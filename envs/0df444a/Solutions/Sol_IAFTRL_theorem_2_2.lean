-- Prove2me | solution 1 for IAFTRL.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-17T06:51:52.391635+00:00
-- url     : https://prove2.me/submissions/761c303f-4e8a-4292-a18d-99112df17f1d

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_LinEnv

-- ===== Env =====

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal

namespace T22

/-! ### Sign laws -/

/-- clamp to `[-1/2, 1/2]` -/
noncomputable def clampH (x : ℝ) : ℝ := max (-(1 / 2) : ℝ) (min (1 / 2 : ℝ) x)

lemma clampH_le (x : ℝ) : |clampH x| ≤ 1 / 2 := by
  unfold clampH; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma clampH_of (x : ℝ) (h : |x| ≤ 1 / 2) : clampH x = x := by
  unfold clampH; rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

lemma clampH_cont : Continuous clampH := by
  unfold clampH; fun_prop

/-- the two-point law on `{1, -1}` with mean `μ` -/
noncomputable def signLaw (μ : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((1 + μ) / 2) • Measure.dirac 1 + ENNReal.ofReal ((1 - μ) / 2) • Measure.dirac (-1)

lemma lintegral_signLaw (μ : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y, g y ∂(signLaw μ) = ENNReal.ofReal ((1 + μ) / 2) * g 1 +
      ENNReal.ofReal ((1 - μ) / 2) * g (-1) := by
  unfold signLaw
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
    lintegral_dirac]
  rfl

lemma signLaw_apply (μ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    signLaw μ s = ENNReal.ofReal ((1 + μ) / 2) * s.indicator 1 1 +
      ENNReal.ofReal ((1 - μ) / 2) * s.indicator 1 (-1) := by
  rw [← lintegral_indicator_one hs, lintegral_signLaw]

lemma signLaw_univ (μ : ℝ) (h : |μ| ≤ 1) : signLaw μ Set.univ = 1 := by
  rw [signLaw_apply _ _ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [abs_le] at h
  rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
  have e : (1 + μ) / 2 + (1 - μ) / 2 = 1 := by ring
  rw [e, ENNReal.ofReal_one]

lemma signLaw_compl (μ : ℝ) : signLaw μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  rw [signLaw_apply _ _ measurableSet_Icc.compl]
  simp [Set.indicator, Set.mem_Icc]

lemma integral_signLaw (μ : ℝ) (h : |μ| ≤ 1) : ∫ y, y ∂(signLaw μ) = μ := by
  rw [abs_le] at h
  unfold signLaw
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
    simp only [smul_eq_mul]; ring
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- the feedback kernel `a ↦ signLaw (clampH (aᵀv))` -/
noncomputable def fbK (v : Fin 2 → ℝ) : Kernel (Fin 2 → ℝ) ℝ where
  toFun a := signLaw (clampH (a ⬝ᵥ v))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hc : Continuous fun a : Fin 2 → ℝ => clampH (a ⬝ᵥ v) :=
      clampH_cont.comp (continuous_id.dotProduct continuous_const)
    have e : (fun a : Fin 2 → ℝ => signLaw (clampH (a ⬝ᵥ v)) s) = fun a =>
        ENNReal.ofReal ((1 + clampH (a ⬝ᵥ v)) / 2) * s.indicator 1 1 +
          ENNReal.ofReal ((1 - clampH (a ⬝ᵥ v)) / 2) * s.indicator 1 (-1) := by
      funext a; exact signLaw_apply _ _ hs
    rw [e]
    refine Measurable.add ?_ ?_
    · exact (ENNReal.measurable_ofReal.comp
        ((continuous_const.add hc).div_const _).measurable).mul_const _
    · exact (ENNReal.measurable_ofReal.comp
        ((continuous_const.sub hc).div_const _).measurable).mul_const _

lemma fbK_apply (v a : Fin 2 → ℝ) : fbK v a = signLaw (clampH (a ⬝ᵥ v)) := rfl

instance (v : Fin 2 → ℝ) : IsMarkovKernel (fbK v) :=
  ⟨fun a => ⟨by
    rw [fbK_apply]
    exact signLaw_univ _ ((clampH_le _).trans (by norm_num))⟩⟩

/-! ### The action set and the instances -/

/-- `arms = (-e₁, e₁, e₂)` -/
def arms : Fin 3 → Fin 2 → ℝ := ![![-1, 0], ![1, 0], ![0, 1]]

lemma dot0 (x y : ℝ) : arms 0 ⬝ᵥ ![x, y] = -x := by
  simp [arms, dotProduct, Fin.sum_univ_two]
lemma dot1 (x y : ℝ) : arms 1 ⬝ᵥ ![x, y] = x := by
  simp [arms, dotProduct, Fin.sum_univ_two]
lemma dot2 (x y : ℝ) : arms 2 ⬝ᵥ ![x, y] = y := by
  simp [arms, dotProduct, Fin.sum_univ_two]

lemma vec2_eq (z : Fin 2 → ℝ) : z = ![z 0, z 1] := by
  funext i; fin_cases i <;> rfl

lemma setNorm_range {K d : ℕ} (a : Fin K → Fin d → ℝ) (z : Fin d → ℝ) :
    setNorm (Set.range a) z = ⨆ j, |a j ⬝ᵥ z| := by
  unfold setNorm
  rw [← Set.range_comp]
  rfl

lemma setNorm_arms (x y : ℝ) : setNorm (Set.range arms) ![x, y] = max |x| |y| := by
  rw [setNorm_range]
  apply le_antisymm
  · apply ciSup_le
    intro j
    fin_cases j
    · show |arms 0 ⬝ᵥ ![x, y]| ≤ _; rw [dot0, abs_neg]; exact le_max_left _ _
    · show |arms 1 ⬝ᵥ ![x, y]| ≤ _; rw [dot1]; exact le_max_left _ _
    · show |arms 2 ⬝ᵥ ![x, y]| ≤ _; rw [dot2]; exact le_max_right _ _
  · have hb : BddAbove (Set.range fun j => |arms j ⬝ᵥ ![x, y]|) := (Set.finite_range _).bddAbove
    apply max_le
    · have := le_ciSup hb 1; rw [dot1] at this; exact this
    · have := le_ciSup hb 2; rw [dot2] at this; exact this

lemma arms_mem (j : Fin 3) : arms j ∈ Set.range arms := ⟨j, rfl⟩

/-- the actual loss vector of round `t` in environment `σ` -/
noncomputable def vv (Δ σ ε : ℝ) (m t : ℕ) : Fin 2 → ℝ :=
  if t < m then ![σ * ε, 1 / 2] else ![σ * Δ / 2, 1 / 2]

/-- the environment of sign `σ` -/
noncomputable def env (Δ σ ε : ℝ) (m : ℕ) : LinEnv 2 where
  θs t := vv Δ σ ε m t
  fb t := fbK (vv Δ σ ε m t)
  markov _ := inferInstance

lemma vv_dot_bound (Δ σ ε : ℝ) (m t : ℕ) (hσ : σ = 1 ∨ σ = -1) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2)
    (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1) (j : Fin 3) : |arms j ⬝ᵥ vv Δ σ ε m t| ≤ 1 / 2 := by
  have hs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  unfold vv
  split_ifs
  · fin_cases j
    · show |arms 0 ⬝ᵥ _| ≤ _; rw [dot0, abs_neg, abs_mul, hs, abs_of_nonneg hε]; linarith
    · show |arms 1 ⬝ᵥ _| ≤ _; rw [dot1, abs_mul, hs, abs_of_nonneg hε]; linarith
    · show |arms 2 ⬝ᵥ _| ≤ _; rw [dot2]; norm_num
  · fin_cases j
    · show |arms 0 ⬝ᵥ _| ≤ _; rw [dot0, abs_neg, mul_div_assoc, abs_mul, hs,
        abs_of_nonneg (by linarith)]; linarith
    · show |arms 1 ⬝ᵥ _| ≤ _; rw [dot1, mul_div_assoc, abs_mul, hs,
        abs_of_nonneg (by linarith)]; linarith
    · show |arms 2 ⬝ᵥ _| ≤ _; rw [dot2]; norm_num

/-- the environment is a corrupted stochastic environment -/
lemma env_corrupted (Δ σ ε C : ℝ) (m T : ℕ) (hσ : σ = 1 ∨ σ = -1) (hε : 0 ≤ ε)
    (hεΔ : ε ≤ Δ) (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 2) (hmT : m ≤ T) (hmC : (m : ℝ) * (Δ / 2) ≤ C) :
    (env Δ σ ε m).IsCorruptedStoch (Set.range arms) ![σ * Δ / 2, 1 / 2] C T := by
  have hs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [setNorm_arms, mul_div_assoc, abs_mul, hs, one_mul, abs_of_nonneg (by linarith)]
    norm_num; linarith
  · intro t _
    show setNorm _ (vv Δ σ ε m t) ≤ 1
    unfold vv
    split_ifs
    · rw [setNorm_arms, abs_mul, hs, one_mul, abs_of_nonneg hε]; norm_num; linarith
    · rw [setNorm_arms, mul_div_assoc, abs_mul, hs, one_mul, abs_of_nonneg (by linarith)]
      norm_num; linarith
  · rintro t _ a ⟨j, rfl⟩
    refine ⟨signLaw_compl _, ?_⟩
    show ∫ y, y ∂(signLaw (clampH (arms j ⬝ᵥ vv Δ σ ε m t))) = arms j ⬝ᵥ vv Δ σ ε m t
    have hb := vv_dot_bound Δ σ ε m t hσ hε (by linarith) hΔ (by linarith) j
    rw [clampH_of _ hb, integral_signLaw _ (hb.trans (by norm_num))]
  · have hterm : ∀ t ∈ Finset.range T, setNorm (Set.range arms)
        ((env Δ σ ε m).θs t - ![σ * Δ / 2, 1 / 2]) ≤ if t < m then Δ / 2 else 0 := by
      intro t _
      show setNorm _ (vv Δ σ ε m t - ![σ * Δ / 2, 1 / 2]) ≤ _
      unfold vv
      split_ifs
      · have e : (![σ * ε, 1 / 2] - ![σ * Δ / 2, 1 / 2] : Fin 2 → ℝ) = ![σ * (ε - Δ / 2), 0] := by
          funext i; fin_cases i <;> simp <;> ring
        rw [e, setNorm_arms, abs_mul, hs, one_mul, abs_zero]
        exact max_le (abs_le.mpr ⟨by linarith, by linarith⟩) (by linarith)
      · rw [sub_self]
        have e : (0 : Fin 2 → ℝ) = ![0, 0] := by funext i; fin_cases i <;> rfl
        rw [e, setNorm_arms]; simp
    refine (Finset.sum_le_sum hterm).trans (le_of_eq_of_le ?_ hmC)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have : (Finset.range T).filter (fun t => t < m) = Finset.range m := by
      ext t; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.card_range]

end T22

-- ===== Hist =====

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal

namespace T22

variable {d : ℕ}

/-- appending a round -/
abbrev snocH {n : ℕ} (h : LinearBanditHistory d n) (a : Fin d → ℝ) (y : ℝ) :
    LinearBanditHistory d (n + 1) :=
  Fin.snoc (α := fun _ => (Fin d → ℝ) × ℝ) h (a, y)

lemma meas_snocH_y {n : ℕ} (h : LinearBanditHistory d n) (a : Fin d → ℝ) :
    Measurable fun y : ℝ => snocH h a y :=
  (measurable_histSnoc (d := d) (n := n)).comp
    ((measurable_const (a := ((h, a) : LinearBanditHistory d n × (Fin d → ℝ)))).prodMk
      measurable_id)

/-- one-step disintegration of the history law -/
lemma lintegral_hist_succ (E : LinEnv d) (π : LinearBanditPolicy d) (n : ℕ)
    {f : LinearBanditHistory d (n + 1) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ h, f h ∂(E.histMeasure π (n + 1)) =
      ∫⁻ h, ∫⁻ a, ∫⁻ y, f (snocH h a y) ∂(E.fb n a) ∂(π.select n h) ∂(E.histMeasure π n) := by
  rw [LinEnv.histMeasure, lintegral_map hf measurable_histSnoc]
  rw [Measure.lintegral_compProd (f := fun p : (LinearBanditHistory d n × (Fin d → ℝ)) × ℝ =>
    f (Fin.snoc (α := fun _ => (Fin d → ℝ) × ℝ) p.1.1 (p.1.2, p.2))) (hf.comp measurable_histSnoc)]
  have hm : Measurable fun q : LinearBanditHistory d n × (Fin d → ℝ) =>
      ∫⁻ y, f (Fin.snoc (α := fun _ => (Fin d → ℝ) × ℝ) q.1 (q.2, y))
        ∂((E.fb n).comap Prod.snd measurable_snd q) :=
    Measurable.lintegral_kernel_prod_right' (κ := (E.fb n).comap Prod.snd measurable_snd)
      (f := fun p : (LinearBanditHistory d n × (Fin d → ℝ)) × ℝ =>
        f (Fin.snoc (α := fun _ => (Fin d → ℝ) × ℝ) p.1.1 (p.1.2, p.2)))
      (hf.comp measurable_histSnoc)
  rw [Measure.lintegral_compProd hm]
  rfl

lemma meas_inner (E : LinEnv d) (n : ℕ) {F : LinearBanditHistory d n × (Fin d → ℝ) × ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    Measurable fun q : LinearBanditHistory d n × (Fin d → ℝ) =>
      ∫⁻ y, F (q.1, q.2, y) ∂(E.fb n q.2) := by
  have := Measurable.lintegral_kernel_prod_right' (κ := (E.fb n).comap Prod.snd measurable_snd)
    (f := fun p : (LinearBanditHistory d n × (Fin d → ℝ)) × ℝ => F (p.1.1, p.1.2, p.2))
    (hF.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  exact this

lemma meas_outer (π : LinearBanditPolicy d) (n : ℕ)
    {G : LinearBanditHistory d n × (Fin d → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    Measurable fun h : LinearBanditHistory d n => ∫⁻ a, G (h, a) ∂(π.select n h) :=
  Measurable.lintegral_kernel_prod_right' (κ := π.select n) hG

/-! ### Support -/

lemma hist_supported (E : LinEnv d) (π : LinearBanditPolicy d) (𝒜 : Set (Fin d → ℝ))
    (h𝒜 : MeasurableSet 𝒜) (hπ : IsSupportedLinearPolicy 𝒜 π) :
    ∀ n (t : Fin n), E.histMeasure π n {h | (h t).1 ∉ 𝒜} = 0 := by
  intro n
  induction n with
  | zero => intro t; exact t.elim0
  | succ n ih =>
    intro t
    have hmeas0 : Measurable fun h' : LinearBanditHistory d (n + 1) => (h' t).1 :=
      (measurable_pi_apply t).fst
    have hS : MeasurableSet {h : LinearBanditHistory d (n + 1) | (h t).1 ∉ 𝒜} :=
      h𝒜.compl.preimage hmeas0
    rw [← lintegral_indicator_one hS, lintegral_hist_succ E π n (measurable_one.indicator hS)]
    cases t using Fin.lastCases with
    | last =>
      have e : ∀ (h : LinearBanditHistory d n) (a : Fin d → ℝ) (y : ℝ),
          ({h' : LinearBanditHistory d (n + 1) | (h' (Fin.last n)).1 ∉ 𝒜}.indicator 1
            (snocH h a y) : ℝ≥0∞) = 𝒜ᶜ.indicator 1 a := by
        intro h a y
        classical
        by_cases ha : a ∈ 𝒜
        · rw [Set.indicator_of_notMem (by simp [snocH, ha]), Set.indicator_of_notMem (by simpa using ha)]
        · rw [Set.indicator_of_mem (by simpa [snocH] using ha), Set.indicator_of_mem (by simpa using ha)]
          rfl
      simp_rw [e, lintegral_const, measure_univ, mul_one]
      simp_rw [lintegral_indicator_one h𝒜.compl, hπ n]
      simp
    | cast t' =>
      have e : ∀ (h : LinearBanditHistory d n) (a : Fin d → ℝ) (y : ℝ),
          ({h' : LinearBanditHistory d (n + 1) | (h' (Fin.castSucc t')).1 ∉ 𝒜}.indicator 1
            (snocH h a y) : ℝ≥0∞) = {h' : LinearBanditHistory d n | (h' t').1 ∉ 𝒜}.indicator 1 h := by
        intro h a y
        classical
        by_cases ha : (h t').1 ∈ 𝒜
        · rw [Set.indicator_of_notMem (by simp [snocH, ha]), Set.indicator_of_notMem (by simpa using ha)]
        · rw [Set.indicator_of_mem (by simpa [snocH] using ha), Set.indicator_of_mem (by simpa using ha)]
          rfl
      simp only [e, lintegral_const, measure_univ, mul_one]
      have hmeas : Measurable fun h' : LinearBanditHistory d n => (h' t').1 :=
        (measurable_pi_apply t').fst
      have hS' : MeasurableSet {h' : LinearBanditHistory d n | (h' t').1 ∉ 𝒜} :=
        h𝒜.compl.preimage hmeas
      rw [lintegral_indicator_one hS', ih t']

lemma hist_ae_supported (E : LinEnv d) (π : LinearBanditPolicy d) (𝒜 : Set (Fin d → ℝ))
    (h𝒜 : MeasurableSet 𝒜) (hπ : IsSupportedLinearPolicy 𝒜 π) (n : ℕ) :
    ∀ᵐ h ∂(E.histMeasure π n), ∀ t : Fin n, (h t).1 ∈ 𝒜 := by
  rw [ae_all_iff]
  intro t
  rw [ae_iff]
  simpa using hist_supported E π 𝒜 h𝒜 hπ n t

/-! ### Marginals -/

/-- restriction of a history to its first `n` rounds -/
def restr {n N : ℕ} (hnN : n ≤ N) (h : LinearBanditHistory d N) : LinearBanditHistory d n :=
  fun i => h (Fin.castLE hnN i)

lemma restr_meas {n N : ℕ} (hnN : n ≤ N) : Measurable (restr (d := d) hnN) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply _

lemma hist_marginal (E : LinEnv d) (π : LinearBanditPolicy d) (n : ℕ) :
    ∀ k, (E.histMeasure π (n + k)).map (restr (Nat.le_add_right n k)) = E.histMeasure π n := by
  intro k
  induction k with
  | zero =>
    have : restr (d := d) (Nat.le_add_right n 0) = id := by funext h i; rfl
    rw [this, Measure.map_id]
    rfl
  | succ k ih =>
    show Measure.map (restr (N := n + k + 1) (by omega)) (E.histMeasure π ((n + k) + 1)) = _
    rw [LinEnv.histMeasure, Measure.map_map (restr_meas _) measurable_histSnoc]
    have e : restr (N := n + k + 1) (by omega) ∘ (fun p : (LinearBanditHistory d (n + k) ×
        (Fin d → ℝ)) × ℝ => Fin.snoc (α := fun _ => (Fin d → ℝ) × ℝ) p.1.1 (p.1.2, p.2)) =
        (restr (Nat.le_add_right n k) ∘ Prod.fst) ∘ Prod.fst := by
      funext p
      funext i
      simp only [restr, Function.comp]
      rw [show (Fin.castLE (by omega : n ≤ n + k + 1) i : Fin (n + k + 1)) =
        Fin.castSucc (Fin.castLE (Nat.le_add_right n k) i) from Fin.ext rfl, Fin.snoc_castSucc]
    rw [e, ← Measure.map_map ((restr_meas _).comp measurable_fst) measurable_fst,
      ← Measure.map_map (restr_meas _) measurable_fst]
    have h1 := Measure.fst_compProd ((E.histMeasure π (n + k)).compProd (π.select (n + k)))
      ((E.fb (n + k)).comap Prod.snd measurable_snd)
    have h2 := Measure.fst_compProd (E.histMeasure π (n + k)) (π.select (n + k))
    rw [Measure.fst] at h1 h2
    rw [h1, h2, ih]

/-! ### Change of measure -/

/-- the likelihood ratio of the first `n` rounds -/
noncomputable def LR (ρ : ℕ → (Fin d → ℝ) → ℝ → ℝ≥0∞) (n : ℕ) (h : LinearBanditHistory d n) :
    ℝ≥0∞ :=
  ∏ t : Fin n, ρ t (h t).1 (h t).2

lemma LR_meas (ρ : ℕ → (Fin d → ℝ) → ℝ → ℝ≥0∞) (hρ : ∀ t, Measurable (Function.uncurry (ρ t)))
    (n : ℕ) : Measurable (LR ρ n) := by
  unfold LR
  refine Finset.measurable_prod _ fun t _ => ?_
  exact (hρ t).comp ((measurable_fst.comp (measurable_pi_apply t)).prodMk
    (measurable_snd.comp (measurable_pi_apply t)))

lemma LR_succ (ρ : ℕ → (Fin d → ℝ) → ℝ → ℝ≥0∞) (n : ℕ) (h : LinearBanditHistory d n)
    (a : Fin d → ℝ) (y : ℝ) : LR ρ (n + 1) (snocH h a y) = LR ρ n h * ρ n a y := by
  unfold LR
  rw [Fin.prod_univ_castSucc]
  simp only [snocH, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]

lemma change_of_measure (E₁ E₂ : LinEnv d) (π : LinearBanditPolicy d) (N : ℕ)
    (ρ : ℕ → (Fin d → ℝ) → ℝ → ℝ≥0∞) (hρ : ∀ t, Measurable (Function.uncurry (ρ t)))
    (hfb : ∀ t < N, ∀ a (g : ℝ → ℝ≥0∞), Measurable g →
      ∫⁻ y, g y ∂(E₂.fb t a) = ∫⁻ y, g y * ρ t a y ∂(E₁.fb t a)) :
    ∀ n ≤ N, ∀ f : LinearBanditHistory d n → ℝ≥0∞, Measurable f →
      ∫⁻ h, f h ∂(E₂.histMeasure π n) = ∫⁻ h, f h * LR ρ n h ∂(E₁.histMeasure π n) := by
  intro n
  induction n with
  | zero =>
    intro _ f _
    simp [LinEnv.histMeasure, LR]
  | succ n ih =>
    intro hn f hf
    have hρn := hρ n
    have hfs : Measurable fun p : LinearBanditHistory d n × (Fin d → ℝ) × ℝ =>
        f (snocH p.1 p.2.1 p.2.2) :=
      hf.comp (measurable_histSnoc.comp ((measurable_fst.prodMk
        (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)))
    have hρs : Measurable fun p : LinearBanditHistory d n × (Fin d → ℝ) × ℝ =>
        ρ n p.2.1 p.2.2 :=
      hρn.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
    rw [lintegral_hist_succ E₂ π n hf,
      lintegral_hist_succ E₁ π n (f := fun h => f h * LR ρ (n + 1) h) (hf.mul (LR_meas ρ hρ _))]
    have step1 : ∀ (h : LinearBanditHistory d n) (a : Fin d → ℝ),
        ∫⁻ y, f (snocH h a y) ∂(E₂.fb n a) = ∫⁻ y, f (snocH h a y) * ρ n a y ∂(E₁.fb n a) :=
      fun h a => hfb n (by omega) a _ (hf.comp (meas_snocH_y h a))
    simp_rw [step1]
    have hG : Measurable fun q : LinearBanditHistory d n × (Fin d → ℝ) =>
        ∫⁻ y, f (snocH q.1 q.2 y) * ρ n q.2 y ∂(E₁.fb n q.2) :=
      meas_inner E₁ n (F := fun p => f (snocH p.1 p.2.1 p.2.2) * ρ n p.2.1 p.2.2) (hfs.mul hρs)
    have hF := meas_outer π n hG
    rw [ih (by omega) _ hF]
    refine lintegral_congr fun h => ?_
    have hGa : Measurable fun a => ∫⁻ y, f (snocH h a y) * ρ n a y ∂(E₁.fb n a) :=
      hG.comp measurable_prodMk_left
    simp only
    rw [← lintegral_mul_const _ hGa]
    refine lintegral_congr fun a => ?_
    have hy : Measurable fun y => f (snocH h a y) * ρ n a y :=
      (hf.comp (meas_snocH_y h a)).mul (hρn.comp (measurable_const.prodMk measurable_id))
    rw [← lintegral_mul_const _ hy]
    refine lintegral_congr fun y => ?_
    rw [LR_succ]
    ring

end T22

-- ===== Chi =====

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal

namespace T22

/-- the density ratio of the feedback laws of the two environments -/
noncomputable def rho (Δ ε : ℝ) (m : ℕ) (t : ℕ) (a : Fin 2 → ℝ) (y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + clampH (a ⬝ᵥ vv Δ (-1) ε m t) * y) / (1 + clampH (a ⬝ᵥ vv Δ 1 ε m t) * y))

lemma rho_meas (Δ ε : ℝ) (m t : ℕ) : Measurable (Function.uncurry (rho Δ ε m t)) := by
  unfold rho Function.uncurry
  have h1 : Continuous fun p : (Fin 2 → ℝ) × ℝ => clampH (p.1 ⬝ᵥ vv Δ (-1) ε m t) :=
    clampH_cont.comp (continuous_fst.dotProduct continuous_const)
  have h2 : Continuous fun p : (Fin 2 → ℝ) × ℝ => clampH (p.1 ⬝ᵥ vv Δ 1 ε m t) :=
    clampH_cont.comp (continuous_fst.dotProduct continuous_const)
  exact ENNReal.measurable_ofReal.comp
    (((continuous_const.add (h1.mul continuous_snd)).measurable).div
      ((continuous_const.add (h2.mul continuous_snd)).measurable))

lemma signLaw_change (μp μm : ℝ) (hp : |μp| ≤ 1 / 2) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y, g y ∂(signLaw μm) =
      ∫⁻ y, g y * ENNReal.ofReal ((1 + μm * y) / (1 + μp * y)) ∂(signLaw μp) := by
  rw [abs_le] at hp
  rw [lintegral_signLaw, lintegral_signLaw]
  have e1 : ENNReal.ofReal ((1 + μp) / 2) * (g 1 * ENNReal.ofReal ((1 + μm * 1) / (1 + μp * 1))) =
      ENNReal.ofReal ((1 + μm) / 2) * g 1 := by
    rw [mul_comm (g 1), ← mul_assoc, ← ENNReal.ofReal_mul (by linarith)]
    congr 2
    rw [mul_one, mul_one]
    have : (1 + μp) ≠ 0 := by intro h; linarith
    field_simp
  have e2 : ENNReal.ofReal ((1 - μp) / 2) *
      (g (-1) * ENNReal.ofReal ((1 + μm * -1) / (1 + μp * -1))) =
      ENNReal.ofReal ((1 - μm) / 2) * g (-1) := by
    rw [mul_comm (g (-1)), ← mul_assoc, ← ENNReal.ofReal_mul (by linarith)]
    congr 2
    rw [mul_neg_one, mul_neg_one, ← sub_eq_add_neg, ← sub_eq_add_neg]
    have : (1 - μp) ≠ 0 := by intro h; linarith
    field_simp
  rw [e1, e2]

lemma fb_change (Δ ε : ℝ) (m t : ℕ) (a : Fin 2 → ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y, g y ∂((env Δ (-1) ε m).fb t a) =
      ∫⁻ y, g y * rho Δ ε m t a y ∂((env Δ 1 ε m).fb t a) :=
  signLaw_change _ _ (clampH_le _) g

lemma signLaw_chi (μp μm : ℝ) (hp : |μp| ≤ 1 / 2) (hm : |μm| ≤ 1 / 2) :
    ∫⁻ y, ENNReal.ofReal ((1 + μm * y) / (1 + μp * y)) ^ 2 ∂(signLaw μp) =
      ENNReal.ofReal ((1 + μm) ^ 2 / (2 * (1 + μp)) + (1 - μm) ^ 2 / (2 * (1 - μp))) := by
  rw [abs_le] at hp hm
  rw [lintegral_signLaw]
  have hp1 : 0 < 1 + μp := by linarith
  have hp2 : 0 < 1 - μp := by linarith
  rw [← ENNReal.ofReal_pow (div_nonneg (by linarith) (by linarith)),
    ← ENNReal.ofReal_pow (div_nonneg (by linarith) (by linarith)),
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  rw [mul_one, mul_one, mul_neg_one, mul_neg_one, ← sub_eq_add_neg, ← sub_eq_add_neg]
  have h1 : (1 + μp) ≠ 0 := by intro h; linarith
  have h2 : (1 - μp) ≠ 0 := by intro h; linarith
  field_simp

/-- the per-round `χ²` factor -/
noncomputable def rbar (ε : ℝ) : ℝ := 1 + 4 * ε ^ 2 / (1 - ε ^ 2)

lemma rbar_eq (ε : ℝ) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 16) :
    (1 + ε) ^ 2 / (2 * (1 - ε)) + (1 - ε) ^ 2 / (2 * (1 + ε)) = rbar ε := by
  unfold rbar
  have h1 : (1 - ε) ≠ 0 := by intro h; linarith
  have h2 : (1 + ε) ≠ 0 := by intro h; linarith
  have h3 : (1 - ε ^ 2) ≠ 0 := by nlinarith
  field_simp
  ring

lemma rbar_ge_one (ε : ℝ) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 16) : 1 ≤ rbar ε := by
  unfold rbar
  have h3 : 0 < 1 - ε ^ 2 := by nlinarith
  have : 0 ≤ 4 * ε ^ 2 / (1 - ε ^ 2) := by positivity
  linarith

lemma round_chi (Δ ε : ℝ) (m t : ℕ) (ht : t < m) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 16) (j : Fin 3) :
    ∫⁻ y, rho Δ ε m t (arms j) y ^ 2 ∂((env Δ 1 ε m).fb t (arms j)) ≤
      ENNReal.ofReal (rbar ε) := by
  show ∫⁻ y, rho Δ ε m t (arms j) y ^ 2 ∂(signLaw (clampH (arms j ⬝ᵥ vv Δ 1 ε m t))) ≤ _
  have hv1 : vv Δ 1 ε m t = ![1 * ε, 1 / 2] := by unfold vv; rw [if_pos ht]
  have hv2 : vv Δ (-1) ε m t = ![-1 * ε, 1 / 2] := by unfold vv; rw [if_pos ht]
  unfold rho
  rw [hv1, hv2]
  have hb1 : |-(1 * ε)| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hb2 : |-(-1 * ε)| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hb3 : |1 * ε| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hb4 : |-1 * ε| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hb5 : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
  fin_cases j
  · show ∫⁻ y, ENNReal.ofReal ((1 + clampH (arms 0 ⬝ᵥ ![-1 * ε, 1 / 2]) * y) /
        (1 + clampH (arms 0 ⬝ᵥ ![1 * ε, 1 / 2]) * y)) ^ 2
        ∂(signLaw (clampH (arms 0 ⬝ᵥ ![1 * ε, 1 / 2]))) ≤ _
    rw [dot0, dot0, clampH_of _ hb1, clampH_of _ hb2, signLaw_chi _ _ hb1 hb2]
    apply ENNReal.ofReal_le_ofReal
    rw [← rbar_eq ε hε hε']
    apply le_of_eq
    ring_nf
  · show ∫⁻ y, ENNReal.ofReal ((1 + clampH (arms 1 ⬝ᵥ ![-1 * ε, 1 / 2]) * y) /
        (1 + clampH (arms 1 ⬝ᵥ ![1 * ε, 1 / 2]) * y)) ^ 2
        ∂(signLaw (clampH (arms 1 ⬝ᵥ ![1 * ε, 1 / 2]))) ≤ _
    rw [dot1, dot1, clampH_of _ hb3, clampH_of _ hb4, signLaw_chi _ _ hb3 hb4]
    apply ENNReal.ofReal_le_ofReal
    rw [← rbar_eq ε hε hε']
    apply le_of_eq
    ring_nf
  · show ∫⁻ y, ENNReal.ofReal ((1 + clampH (arms 2 ⬝ᵥ ![-1 * ε, 1 / 2]) * y) /
        (1 + clampH (arms 2 ⬝ᵥ ![1 * ε, 1 / 2]) * y)) ^ 2
        ∂(signLaw (clampH (arms 2 ⬝ᵥ ![1 * ε, 1 / 2]))) ≤ _
    rw [dot2, dot2, clampH_of _ hb5, signLaw_chi _ _ hb5 hb5]
    apply ENNReal.ofReal_le_ofReal
    have := rbar_ge_one ε hε hε'
    norm_num
    linarith

end T22

-- ===== TV =====

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal

namespace T22

lemma ae_arms (π : LinearBanditPolicy 2) (hπ : IsSupportedLinearPolicy (Set.range arms) π) (n : ℕ)
    (h : LinearBanditHistory 2 n) : ∀ᵐ a ∂(π.select n h), a ∈ Set.range arms := by
  rw [ae_iff]
  exact hπ n h

lemma second_moment (Δ ε : ℝ) (m : ℕ) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 16) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy (Set.range arms) π) :
    ∀ n ≤ m, ∫⁻ h, LR (rho Δ ε m) n h ^ 2 ∂((env Δ 1 ε m).histMeasure π n) ≤
      ENNReal.ofReal (rbar ε) ^ n := by
  intro n
  induction n with
  | zero => intro _; simp [LR, LinEnv.histMeasure]
  | succ n ih =>
    intro hn
    have hLR := LR_meas (rho Δ ε m) (rho_meas Δ ε m)
    have hρn := rho_meas Δ ε m n
    rw [lintegral_hist_succ _ π n ((hLR (n + 1)).pow_const 2)]
    simp_rw [LR_succ, mul_pow]
    have hy : ∀ a, Measurable fun y => rho Δ ε m n a y ^ 2 :=
      fun a => (hρn.comp (measurable_const.prodMk measurable_id)).pow_const 2
    have hinner : ∀ h : LinearBanditHistory 2 n,
        ∫⁻ a, ∫⁻ y, LR (rho Δ ε m) n h ^ 2 * rho Δ ε m n a y ^ 2 ∂((env Δ 1 ε m).fb n a)
          ∂(π.select n h) ≤ LR (rho Δ ε m) n h ^ 2 * ENNReal.ofReal (rbar ε) := by
      intro h
      have hφ : Measurable fun a => ∫⁻ y, rho Δ ε m n a y ^ 2 ∂((env Δ 1 ε m).fb n a) :=
        Measurable.lintegral_kernel_prod_right (κ := (env Δ 1 ε m).fb n)
          (f := fun a y => rho Δ ε m n a y ^ 2) (hρn.pow_const 2)
      simp_rw [lintegral_const_mul _ (hy _)]
      rw [lintegral_const_mul _ hφ]
      gcongr
      calc ∫⁻ a, ∫⁻ y, rho Δ ε m n a y ^ 2 ∂((env Δ 1 ε m).fb n a) ∂(π.select n h)
          ≤ ∫⁻ _a, ENNReal.ofReal (rbar ε) ∂(π.select n h) := by
            refine lintegral_mono_ae ((ae_arms π hπ n h).mono fun a ha => ?_)
            obtain ⟨j, rfl⟩ := ha
            exact round_chi Δ ε m n (by omega) hε hε' j
        _ = ENNReal.ofReal (rbar ε) := by rw [lintegral_const, measure_univ, mul_one]
    calc ∫⁻ h, ∫⁻ a, ∫⁻ y, LR (rho Δ ε m) n h ^ 2 * rho Δ ε m n a y ^ 2
          ∂((env Δ 1 ε m).fb n a) ∂(π.select n h) ∂((env Δ 1 ε m).histMeasure π n)
        ≤ ∫⁻ h, LR (rho Δ ε m) n h ^ 2 * ENNReal.ofReal (rbar ε)
          ∂((env Δ 1 ε m).histMeasure π n) := lintegral_mono hinner
      _ = (∫⁻ h, LR (rho Δ ε m) n h ^ 2 ∂((env Δ 1 ε m).histMeasure π n)) *
          ENNReal.ofReal (rbar ε) := lintegral_mul_const _ ((hLR n).pow_const 2)
      _ ≤ ENNReal.ofReal (rbar ε) ^ n * ENNReal.ofReal (rbar ε) := by
          gcongr; exact ih (by omega)
      _ = ENNReal.ofReal (rbar ε) ^ (n + 1) := by rw [pow_succ]

lemma pt_ineq (i x : ℝ≥0∞) (hi : i = 0 ∨ i = 1) :
    4 * (i * x) + 8 * x ≤ 4 * i + 4 * x ^ 2 + 5 := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · rcases hi with rfl | rfl <;> simp [ENNReal.top_pow]
  lift x to NNReal using hx
  rcases hi with rfl | rfl
  · have : (8 * x : NNReal) ≤ 4 * x ^ 2 + 5 := by
      rw [← NNReal.coe_le_coe]; push_cast; nlinarith [sq_nonneg ((x : ℝ) - 1)]
    simp only [zero_mul, mul_zero, zero_add]
    exact_mod_cast this
  · have : (4 * x + 8 * x : NNReal) ≤ 4 + 4 * x ^ 2 + 5 := by
      rw [← NNReal.coe_le_coe]; push_cast; nlinarith [sq_nonneg ((x : ℝ) - 3 / 2)]
    simp only [one_mul, mul_one]
    exact_mod_cast this

/-- the testing inequality: the two history laws give close probabilities to every event -/
lemma tv_event (Δ ε : ℝ) (m : ℕ) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 16) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy (Set.range arms) π)
    (hR : 4 * ENNReal.ofReal (rbar ε) ^ m ≤ 5) (S : Set (LinearBanditHistory 2 m))
    (hS : MeasurableSet S) :
    ((env Δ (-1) ε m).histMeasure π m S).toReal ≤
      ((env Δ 1 ε m).histMeasure π m S).toReal + 1 / 2 := by
  set P := (env Δ 1 ε m).histMeasure π m with hP
  set Q := (env Δ (-1) ε m).histMeasure π m with hQ
  set L := LR (rho Δ ε m) m with hL
  have hLm : Measurable L := LR_meas (rho Δ ε m) (rho_meas Δ ε m) m
  have hcm := change_of_measure (env Δ 1 ε m) (env Δ (-1) ε m) π m (rho Δ ε m) (rho_meas Δ ε m)
    (fun t _ a g _ => fb_change Δ ε m t a g) m le_rfl
  have hind : Measurable (S.indicator (1 : LinearBanditHistory 2 m → ℝ≥0∞)) :=
    measurable_one.indicator hS
  have hQS : Q S = ∫⁻ h, S.indicator 1 h * L h ∂P := by
    rw [← lintegral_indicator_one hS]; exact hcm _ hind
  have hQ1 : ∫⁻ h, L h ∂P = 1 := by
    have := hcm (fun _ => 1) measurable_const
    simp only [one_mul, lintegral_const, measure_univ, mul_one] at this
    exact this.symm
  have hsq := second_moment Δ ε m hε hε' π hπ m le_rfl
  have hpt : ∀ h, 4 * (S.indicator 1 h * L h) + 8 * L h ≤
      4 * S.indicator 1 h + 4 * L h ^ 2 + 5 := by
    intro h
    apply pt_ineq
    by_cases hh : h ∈ S
    · right; simp [hh]
    · left; simp [hh]
  have hint := lintegral_mono (μ := P) hpt
  have hL1 : ∫⁻ h, 4 * (S.indicator 1 h * L h) + 8 * L h ∂P = 4 * Q S + 8 * 1 := by
    rw [lintegral_add_left (f := fun h => 4 * (S.indicator 1 h * L h))
      ((hind.mul hLm).const_mul 4)]
    rw [lintegral_const_mul (f := fun h => S.indicator 1 h * L h) _ (hind.mul hLm),
      lintegral_const_mul _ hLm, ← hQS, hQ1]
  have hR1 : ∫⁻ h, 4 * S.indicator 1 h + 4 * L h ^ 2 + 5 ∂P =
      4 * P S + 4 * ∫⁻ h, L h ^ 2 ∂P + 5 := by
    rw [lintegral_add_left (f := fun h => 4 * S.indicator 1 h + 4 * L h ^ 2)
      ((hind.const_mul 4).add ((hLm.pow_const 2).const_mul 4))]
    rw [lintegral_add_left (f := fun h => 4 * S.indicator 1 h) (hind.const_mul 4)]
    rw [lintegral_const_mul _ hind, lintegral_const_mul (f := fun h => L h ^ 2) _ (hLm.pow_const 2),
      lintegral_const, measure_univ, mul_one, lintegral_indicator_one hS]
  rw [hL1, hR1] at hint
  -- 4 Q S + 8 ≤ 4 P S + 4 ∫ L² + 5 ≤ 4 P S + 10
  have h2 : 4 * Q S + 8 ≤ (4 * P S + 2) + 8 := by
    calc 4 * Q S + 8 = 4 * Q S + 8 * 1 := by ring
      _ ≤ 4 * P S + 4 * ∫⁻ h, L h ^ 2 ∂P + 5 := hint
      _ ≤ 4 * P S + 5 + 5 := by
          gcongr
          exact (mul_le_mul_right hsq 4).trans hR
      _ = (4 * P S + 2) + 8 := by ring
  have h3 : 4 * Q S ≤ 4 * P S + 2 := (ENNReal.add_le_add_iff_right (by simp)).mp h2
  have hPf : P S ≠ ⊤ := measure_ne_top P S
  have hQf : Q S ≠ ⊤ := measure_ne_top Q S
  have h4 := ENNReal.toReal_mono (by finiteness) h3
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by simp), ENNReal.toReal_mul] at h4
  simp only [ENNReal.toReal_ofNat] at h4
  linarith

end T22

-- ===== Inst =====

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL

namespace T22

lemma alloc_diag (α : Fin 3 → ℝ) :
    linearAllocationMatrix arms α = diagonal ![α 0 + α 1, α 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [linearAllocationMatrix, arms, vecMulVec, Fin.sum_univ_three, Matrix.sum_apply,
      diagonal_apply]

lemma diag_inv (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (diagonal ![a, b])⁻¹ = diagonal ![a⁻¹, b⁻¹] := by
  apply Matrix.inv_eq_left_inv
  rw [diagonal_mul_diagonal]
  have : (fun i => ![a⁻¹, b⁻¹] i * ![a, b] i) = fun _ => (1 : ℝ) := by
    funext i; fin_cases i <;> simp [ha, hb]
  rw [this]
  exact diagonal_one

lemma quad0 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    arms 0 ⬝ᵥ (diagonal ![a, b])⁻¹ *ᵥ arms 0 = a⁻¹ := by
  rw [diag_inv a b ha hb]
  simp [arms, dotProduct, Fin.sum_univ_two, mulVec_diagonal]
lemma quad1 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    arms 1 ⬝ᵥ (diagonal ![a, b])⁻¹ *ᵥ arms 1 = a⁻¹ := by
  rw [diag_inv a b ha hb]
  simp [arms, dotProduct, Fin.sum_univ_two, mulVec_diagonal]
lemma quad2 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    arms 2 ⬝ᵥ (diagonal ![a, b])⁻¹ *ᵥ arms 2 = b⁻¹ := by
  rw [diag_inv a b ha hb]
  simp [arms, dotProduct, Fin.sum_univ_two, mulVec_diagonal]

lemma inst_facts (Δ : ℝ) (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 2) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (∃ jstar : Fin 3, IsUniqueMin arms ![σ * Δ / 2, 1 / 2] jstar ∧
        (∀ j, j ≠ jstar → Δ ≤ (arms j - arms jstar) ⬝ᵥ ![σ * Δ / 2, 1 / 2]) ∧
        ∃ j, j ≠ jstar ∧ (arms j - arms jstar) ⬝ᵥ ![σ * Δ / 2, 1 / 2] = Δ) ∧
      linearBanditAllocationValue arms (-![σ * Δ / 2, 1 / 2]) = 4 / (1 + Δ) := by
  have hneg : (-![σ * Δ / 2, 1 / 2] : Fin 2 → ℝ) = ![-(σ * Δ / 2), -(1 / 2)] := by
    funext i; fin_cases i <;> simp
  set g : ℝ := (1 + Δ) / 2 with hg
  have hgpos : 0 < g := by rw [hg]; linarith
  -- the allocation value
  have hval : ∀ (j0 j1 : Fin 3), (j0 = 0 ∧ j1 = 1 ∨ j0 = 1 ∧ j1 = 0) →
      (∀ j, linearArmGap arms (-![σ * Δ / 2, 1 / 2]) j =
        if j = j0 then 0 else if j = j1 then Δ else g) →
      linearBanditAllocationValue arms (-![σ * Δ / 2, 1 / 2]) = 4 / (1 + Δ) := by
    intro j0 j1 hj hgap
    unfold linearBanditAllocationValue
    have h2 : ∀ j, j ≠ j0 → j ≠ j1 → j = 2 := by
      intro j a b; rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases j <;> simp_all
    have hgap2 : linearArmGap arms (-![σ * Δ / 2, 1 / 2]) 2 = g := by
      rw [hgap]; rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    have hgapj0 : linearArmGap arms (-![σ * Δ / 2, 1 / 2]) j0 = 0 := by rw [hgap]; simp
    have hgapj1 : linearArmGap arms (-![σ * Δ / 2, 1 / 2]) j1 = Δ := by
      rw [hgap]; rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    have h4 : 4 / (1 + Δ) = 2 / g := by rw [hg]; field_simp <;> ring
    rw [h4]
    apply IsLeast.csInf_eq
    constructor
    · -- the optimal allocation
      let α : Fin 3 → ℝ := fun j => if j = j0 then 2 / Δ ^ 2 else if j = j1 then 0 else 2 / g ^ 2
      refine ⟨α, ⟨fun j => ?_, ?_, fun j hj' => ?_⟩, ?_⟩
      · simp only [α]; split_ifs <;> positivity
      · rw [alloc_diag, posDef_diagonal_iff]
        intro i; fin_cases i
        · rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [α] <;> positivity
        · rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [α] <;> positivity
      · have hd : α 0 + α 1 = 2 / Δ ^ 2 := by
          rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [α]
        have hd2 : α 2 = 2 / g ^ 2 := by
          rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [α]
        rw [alloc_diag, hd, hd2]
        have ha : (2 / Δ ^ 2 : ℝ) ≠ 0 := by positivity
        have hb : (2 / g ^ 2 : ℝ) ≠ 0 := by positivity
        by_cases e0 : j = j0
        · subst e0; rw [hgapj0] at hj'; exact absurd hj' (lt_irrefl 0)
        by_cases e1 : j = j1
        · subst e1
          rw [hgapj1]
          rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [quad1 _ _ ha hb]; field_simp; rfl
          · rw [quad0 _ _ ha hb]; field_simp; rfl
        · have := h2 j e0 e1; subst this
          rw [hgap2, quad2 _ _ ha hb]; field_simp; rfl
      · show ∑ j, α j * linearArmGap arms (-![σ * Δ / 2, 1 / 2]) j = 2 / g
        rw [Fin.sum_univ_three]
        have hc : ∀ j, α j * linearArmGap arms (-![σ * Δ / 2, 1 / 2]) j =
            if j = 2 then 2 / g else 0 := by
          intro j
          by_cases e0 : j = j0
          · rw [e0, hgapj0, mul_zero]
            rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
          by_cases e1 : j = j1
          · have : α j = 0 := by simp only [α, if_neg e0, if_pos e1]
            rw [this, zero_mul]
            rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
          · have := h2 j e0 e1; subst this
            rw [hgap2]; simp only [α, if_neg e0, if_neg e1, if_true]
            field_simp
        rw [hc, hc, hc]; simp
    · -- every feasible allocation costs at least `2/g`
      rintro _ ⟨α, ⟨hα0, hpd, hcon⟩, rfl⟩
      rw [alloc_diag, posDef_diagonal_iff] at hpd
      have ha : 0 < α 0 + α 1 := by simpa using hpd 0
      have hb : 0 < α 2 := by simpa using hpd 1
      have hc2 := hcon 2 (by rw [hgap2]; exact hgpos)
      rw [alloc_diag, quad2 _ _ ha.ne' hb.ne', hgap2] at hc2
      have hb2 : 2 / g ^ 2 ≤ α 2 := by
        rw [div_le_iff₀ (by positivity)]
        rw [inv_le_iff_one_le_mul₀ hb] at hc2
        nlinarith
      have hsum : α 2 * g ≤ ∑ j, α j * linearArmGap arms (-![σ * Δ / 2, 1 / 2]) j := by
        rw [Fin.sum_univ_three, hgap2]
        have : ∀ j, 0 ≤ α j * linearArmGap arms (-![σ * Δ / 2, 1 / 2]) j := by
          intro j
          rw [hgap]
          split_ifs <;> nlinarith [hα0 j]
        linarith [this 0, this 1]
      calc 2 / g = 2 / g ^ 2 * g := by field_simp
        _ ≤ α 2 * g := by gcongr
        _ ≤ _ := hsum
  rcases hσ with rfl | rfl
  · refine ⟨⟨0, fun j hj => ?_, fun j hj => ?_, ⟨1, by decide, ?_⟩⟩, ?_⟩
    · fin_cases j
      · exact absurd rfl hj
      · show arms 0 ⬝ᵥ ![1 * Δ / 2, 1 / 2] < arms 1 ⬝ᵥ ![1 * Δ / 2, 1 / 2]
        rw [dot0, dot1]; linarith
      · show arms 0 ⬝ᵥ ![1 * Δ / 2, 1 / 2] < arms 2 ⬝ᵥ ![1 * Δ / 2, 1 / 2]
        rw [dot0, dot2]; linarith
    · rw [sub_dotProduct]
      fin_cases j
      · exact absurd rfl hj
      · show Δ ≤ arms 1 ⬝ᵥ ![1 * Δ / 2, 1 / 2] - arms 0 ⬝ᵥ ![1 * Δ / 2, 1 / 2]
        rw [dot0, dot1]; linarith
      · show Δ ≤ arms 2 ⬝ᵥ ![1 * Δ / 2, 1 / 2] - arms 0 ⬝ᵥ ![1 * Δ / 2, 1 / 2]
        rw [dot0, dot2]; linarith
    · rw [sub_dotProduct, dot0, dot1]; ring
    · apply hval 0 1 (Or.inl ⟨rfl, rfl⟩)
      intro j
      have hsup : (⨆ j', arms j' ⬝ᵥ -![1 * Δ / 2, 1 / 2]) = Δ / 2 := by
        rw [hneg]
        apply le_antisymm
        · apply ciSup_le; intro j'; fin_cases j'
          · show arms 0 ⬝ᵥ ![-(1 * Δ / 2), -(1 / 2)] ≤ _; rw [dot0]; linarith
          · show arms 1 ⬝ᵥ ![-(1 * Δ / 2), -(1 / 2)] ≤ _; rw [dot1]; linarith
          · show arms 2 ⬝ᵥ ![-(1 * Δ / 2), -(1 / 2)] ≤ _; rw [dot2]; linarith
        · have := le_ciSup (Set.finite_range fun j' => arms j' ⬝ᵥ ![-(1 * Δ / 2), -(1 / 2)]).bddAbove 0
          rw [dot0] at this; linarith
      unfold linearArmGap
      rw [hsup, hneg]
      fin_cases j
      · show Δ / 2 - arms 0 ⬝ᵥ ![-(1 * Δ / 2), -(1 / 2)] = _; rw [dot0]; simp <;> ring
      · show Δ / 2 - arms 1 ⬝ᵥ ![-(1 * Δ / 2), -(1 / 2)] = _; rw [dot1]; simp <;> ring
      · show Δ / 2 - arms 2 ⬝ᵥ ![-(1 * Δ / 2), -(1 / 2)] = _; rw [dot2]; simp [hg] <;> ring
  · refine ⟨⟨1, fun j hj => ?_, fun j hj => ?_, ⟨0, by decide, ?_⟩⟩, ?_⟩
    · fin_cases j
      · show arms 1 ⬝ᵥ ![-1 * Δ / 2, 1 / 2] < arms 0 ⬝ᵥ ![-1 * Δ / 2, 1 / 2]
        rw [dot0, dot1]; linarith
      · exact absurd rfl hj
      · show arms 1 ⬝ᵥ ![-1 * Δ / 2, 1 / 2] < arms 2 ⬝ᵥ ![-1 * Δ / 2, 1 / 2]
        rw [dot1, dot2]; linarith
    · rw [sub_dotProduct]
      fin_cases j
      · show Δ ≤ arms 0 ⬝ᵥ ![-1 * Δ / 2, 1 / 2] - arms 1 ⬝ᵥ ![-1 * Δ / 2, 1 / 2]
        rw [dot0, dot1]; linarith
      · exact absurd rfl hj
      · show Δ ≤ arms 2 ⬝ᵥ ![-1 * Δ / 2, 1 / 2] - arms 1 ⬝ᵥ ![-1 * Δ / 2, 1 / 2]
        rw [dot1, dot2]; linarith
    · rw [sub_dotProduct, dot0, dot1]; ring
    · apply hval 1 0 (Or.inr ⟨rfl, rfl⟩)
      intro j
      have hsup : (⨆ j', arms j' ⬝ᵥ -![-1 * Δ / 2, 1 / 2]) = Δ / 2 := by
        rw [hneg]
        apply le_antisymm
        · apply ciSup_le; intro j'; fin_cases j'
          · show arms 0 ⬝ᵥ ![-(-1 * Δ / 2), -(1 / 2)] ≤ _; rw [dot0]; linarith
          · show arms 1 ⬝ᵥ ![-(-1 * Δ / 2), -(1 / 2)] ≤ _; rw [dot1]; linarith
          · show arms 2 ⬝ᵥ ![-(-1 * Δ / 2), -(1 / 2)] ≤ _; rw [dot2]; linarith
        · have := le_ciSup (Set.finite_range fun j' => arms j' ⬝ᵥ ![-(-1 * Δ / 2), -(1 / 2)]).bddAbove 1
          rw [dot1] at this; linarith
      unfold linearArmGap
      rw [hsup, hneg]
      fin_cases j
      · show Δ / 2 - arms 0 ⬝ᵥ ![-(-1 * Δ / 2), -(1 / 2)] = _; rw [dot0]; simp <;> ring
      · show Δ / 2 - arms 1 ⬝ᵥ ![-(-1 * Δ / 2), -(1 / 2)] = _; rw [dot1]; simp <;> ring
      · show Δ / 2 - arms 2 ⬝ᵥ ![-(-1 * Δ / 2), -(1 / 2)] = _; rw [dot2]; simp [hg] <;> ring

end T22

-- ===== Final =====

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal

namespace T22

lemma marg_event (E : LinEnv 2) (π : LinearBanditPolicy 2) (m N : ℕ) (hmN : m ≤ N) (t : ℕ)
    (ht : t < m) (s : Set (Fin 2 → ℝ)) (hs : MeasurableSet s) :
    E.histMeasure π N {h | (h ⟨t, by omega⟩).1 ∈ s} =
      E.histMeasure π m {h | (h ⟨t, ht⟩).1 ∈ s} := by
  obtain ⟨k, rfl⟩ : ∃ k, N = m + k := ⟨N - m, by omega⟩
  have hmeas : Measurable fun h : LinearBanditHistory 2 m => (h ⟨t, ht⟩).1 :=
    (measurable_pi_apply _).fst
  have hS : MeasurableSet {h : LinearBanditHistory 2 m | (h ⟨t, ht⟩).1 ∈ s} := hs.preimage hmeas
  rw [← hist_marginal E π m k, Measure.map_apply (restr_meas _) hS]
  rfl

/-! ### Per-round gaps -/

lemma arms1_ne (j : Fin 3) (hj : arms j ≠ arms 1) : j = 0 ∨ j = 2 := by
  fin_cases j
  · left; rfl
  · exact absurd rfl hj
  · right; rfl

lemma plus_nonneg (Δ ε : ℝ) (m t : ℕ) (hε : 0 ≤ ε) (hΔ : 0 < Δ) (j : Fin 3) :
    0 ≤ (arms j - arms 0) ⬝ᵥ vv Δ 1 ε m t := by
  rw [sub_dotProduct]
  unfold vv
  split_ifs
  · fin_cases j
    · simp
    · show 0 ≤ arms 1 ⬝ᵥ ![1 * ε, 1 / 2] - arms 0 ⬝ᵥ ![1 * ε, 1 / 2]
      rw [dot0, dot1]; linarith
    · show 0 ≤ arms 2 ⬝ᵥ ![1 * ε, 1 / 2] - arms 0 ⬝ᵥ ![1 * ε, 1 / 2]
      rw [dot0, dot2]; linarith
  · fin_cases j
    · simp
    · show 0 ≤ arms 1 ⬝ᵥ ![1 * Δ / 2, 1 / 2] - arms 0 ⬝ᵥ ![1 * Δ / 2, 1 / 2]
      rw [dot0, dot1]; linarith
    · show 0 ≤ arms 2 ⬝ᵥ ![1 * Δ / 2, 1 / 2] - arms 0 ⬝ᵥ ![1 * Δ / 2, 1 / 2]
      rw [dot0, dot2]; linarith

lemma plus_e1 (Δ ε : ℝ) (m t : ℕ) (ht : t < m) :
    2 * ε ≤ (arms 1 - arms 0) ⬝ᵥ vv Δ 1 ε m t := by
  rw [sub_dotProduct]
  unfold vv; rw [if_pos ht, dot0, dot1]; linarith

lemma minus_nonneg (Δ ε : ℝ) (m t : ℕ) (hε : 0 ≤ ε) (hΔ : 0 < Δ) (j : Fin 3) :
    0 ≤ (arms j - arms 1) ⬝ᵥ vv Δ (-1) ε m t := by
  rw [sub_dotProduct]
  unfold vv
  split_ifs
  · fin_cases j
    · show 0 ≤ arms 0 ⬝ᵥ ![-1 * ε, 1 / 2] - arms 1 ⬝ᵥ ![-1 * ε, 1 / 2]
      rw [dot0, dot1]; linarith
    · simp
    · show 0 ≤ arms 2 ⬝ᵥ ![-1 * ε, 1 / 2] - arms 1 ⬝ᵥ ![-1 * ε, 1 / 2]
      rw [dot1, dot2]; linarith
  · fin_cases j
    · show 0 ≤ arms 0 ⬝ᵥ ![-1 * Δ / 2, 1 / 2] - arms 1 ⬝ᵥ ![-1 * Δ / 2, 1 / 2]
      rw [dot0, dot1]; linarith
    · simp
    · show 0 ≤ arms 2 ⬝ᵥ ![-1 * Δ / 2, 1 / 2] - arms 1 ⬝ᵥ ![-1 * Δ / 2, 1 / 2]
      rw [dot1, dot2]; linarith

lemma minus_other (Δ ε : ℝ) (m t : ℕ) (ht : t < m) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 4) (j : Fin 3)
    (hj : arms j ≠ arms 1) : 2 * ε ≤ (arms j - arms 1) ⬝ᵥ vv Δ (-1) ε m t := by
  rw [sub_dotProduct]
  unfold vv; rw [if_pos ht]
  rcases arms1_ne j hj with rfl | rfl
  · rw [dot0, dot1]; linarith
  · rw [dot1, dot2]; linarith

/-! ### Regret lower bounds -/

lemma regret_ge (E : LinEnv 2) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy (Set.range arms) π) (T : ℕ) (u : Fin 2 → ℝ)
    (hu : u ∈ Set.range arms) (hθ : ∀ (t : ℕ) (j : Fin 3), |arms j ⬝ᵥ E.θs t| ≤ 1 / 2)
    (c : Fin T → LinearBanditHistory 2 T → ℝ) (hcm : ∀ t, Measurable (c t)) (B : ℝ)
    (hcb : ∀ t h, |c t h| ≤ B)
    (hle : ∀ h : LinearBanditHistory 2 T, (∀ t, (h t).1 ∈ Set.range arms) →
      ∑ t, c t h ≤ ∑ t : Fin T, ((h t).1 - u) ⬝ᵥ E.θs t) :
    ∑ t, ∫ h, c t h ∂(E.histMeasure π T) ≤ E.regret (Set.range arms) π T := by
  have hA : MeasurableSet (Set.range arms) := (Set.finite_range arms).measurableSet
  have hae := hist_ae_supported E π (Set.range arms) hA hπ T
  have hfm : Measurable fun h : LinearBanditHistory 2 T =>
      ∑ t : Fin T, ((h t).1 - u) ⬝ᵥ E.θs t := by
    refine Finset.measurable_sum _ fun t _ => ?_
    exact (continuous_id.dotProduct continuous_const).measurable.comp
      ((measurable_pi_apply t).fst.sub measurable_const)
  have hf_int : Integrable (fun h : LinearBanditHistory 2 T =>
      ∑ t : Fin T, ((h t).1 - u) ⬝ᵥ E.θs t) (E.histMeasure π T) := by
    refine Integrable.of_bound hfm.aestronglyMeasurable (T : ℝ) (hae.mono fun h hh => ?_)
    rw [Real.norm_eq_abs]
    calc |∑ t : Fin T, ((h t).1 - u) ⬝ᵥ E.θs t| ≤ ∑ t : Fin T, |((h t).1 - u) ⬝ᵥ E.θs t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin T, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro t _
          obtain ⟨j, hj⟩ := hh t
          obtain ⟨j', rfl⟩ := hu
          rw [← hj, sub_dotProduct]
          have h1 := hθ t j; have h2 := hθ t j'
          rw [abs_le] at h1 h2 ⊢; constructor <;> linarith
      _ = T := by simp
  have hc_int : ∀ t, Integrable (c t) (E.histMeasure π T) := fun t =>
    Integrable.of_bound (hcm t).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun h => by rw [Real.norm_eq_abs]; exact hcb t h)
  have hbdd : BddAbove ((fun u => ∫ h, ∑ t : Fin T, ((h t).1 - u) ⬝ᵥ E.θs t
      ∂(E.histMeasure π T)) '' Set.range arms) :=
    ((Set.finite_range arms).image _).bddAbove
  calc ∑ t, ∫ h, c t h ∂(E.histMeasure π T) = ∫ h, ∑ t, c t h ∂(E.histMeasure π T) :=
        (integral_finsetSum _ fun t _ => hc_int t).symm
    _ ≤ ∫ h, ∑ t : Fin T, ((h t).1 - u) ⬝ᵥ E.θs t ∂(E.histMeasure π T) :=
        integral_mono_ae (integrable_finsetSum _ fun t _ => hc_int t) hf_int
          (hae.mono fun h hh => hle h hh)
    _ ≤ E.regret (Set.range arms) π T := le_csSup hbdd ⟨u, hu, rfl⟩

/-- the event `A_t = e₁` -/
def Ev (T : ℕ) (t : Fin T) : Set (LinearBanditHistory 2 T) := {h | (h t).1 ∈ ({arms 1} : Set _)}

lemma Ev_meas (T : ℕ) (t : Fin T) : MeasurableSet (Ev T t) :=
  (measurableSet_singleton _).preimage (measurable_pi_apply t).fst

lemma regret_plus (Δ ε : ℝ) (m T : ℕ) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 16) (hΔ : 0 < Δ)
    (hΔ' : Δ ≤ 1 / 2) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy (Set.range arms) π) :
    ∑ t : Fin T, (if (t : ℕ) < m then
        2 * ε * ((env Δ 1 ε m).histMeasure π T (Ev T t)).toReal else 0) ≤
      (env Δ 1 ε m).regret (Set.range arms) π T := by
  have hθ : ∀ (t : ℕ) (j : Fin 3), |arms j ⬝ᵥ (env Δ 1 ε m).θs t| ≤ 1 / 2 := fun t j =>
    vv_dot_bound Δ 1 ε m t (Or.inl rfl) hε (by linarith) hΔ (by linarith) j
  let c : Fin T → LinearBanditHistory 2 T → ℝ := fun t h =>
    if (t : ℕ) < m then 2 * ε * (Ev T t).indicator 1 h else 0
  have hcm : ∀ t, Measurable (c t) := by
    intro t; simp only [c]; split_ifs
    · exact (measurable_one.indicator (Ev_meas T t)).const_mul _
    · exact measurable_const
  have hcb : ∀ t h, |c t h| ≤ 2 * ε := by
    intro t h; simp only [c]; split_ifs
    · rw [abs_of_nonneg (by unfold Set.indicator; split_ifs <;> simp <;> linarith)]
      unfold Set.indicator; split_ifs <;> simp <;> linarith
    · simp; linarith
  have key := regret_ge (env Δ 1 ε m) π hπ T (arms 0) ⟨0, rfl⟩ hθ c hcm (2 * ε) hcb (by
    intro h hh
    apply Finset.sum_le_sum; intro t _
    obtain ⟨j, hj⟩ := hh t
    show c t h ≤ ((h t).1 - arms 0) ⬝ᵥ vv Δ 1 ε m t
    simp only [c]
    split_ifs with htm
    · by_cases he : (h t).1 = arms 1
      · rw [Set.indicator_of_mem (show h ∈ Ev T t from he), Pi.one_apply, mul_one, he]
        exact plus_e1 Δ ε m t htm
      · rw [Set.indicator_of_notMem (show h ∉ Ev T t from he), mul_zero, ← hj]
        exact plus_nonneg Δ ε m t hε hΔ j
    · rw [← hj]; exact plus_nonneg Δ ε m t hε hΔ j)
  refine le_trans (le_of_eq ?_) key
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [c]
  split_ifs
  · rw [integral_const_mul, integral_indicator_one (Ev_meas T t), measureReal_def]
  · simp

lemma regret_minus (Δ ε : ℝ) (m T : ℕ) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 16) (hΔ : 0 < Δ)
    (hΔ' : Δ ≤ 1 / 2) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy (Set.range arms) π) :
    ∑ t : Fin T, (if (t : ℕ) < m then
        2 * ε * (1 - ((env Δ (-1) ε m).histMeasure π T (Ev T t)).toReal) else 0) ≤
      (env Δ (-1) ε m).regret (Set.range arms) π T := by
  have hθ : ∀ (t : ℕ) (j : Fin 3), |arms j ⬝ᵥ (env Δ (-1) ε m).θs t| ≤ 1 / 2 := fun t j =>
    vv_dot_bound Δ (-1) ε m t (Or.inr rfl) hε (by linarith) hΔ (by linarith) j
  let c : Fin T → LinearBanditHistory 2 T → ℝ := fun t h =>
    if (t : ℕ) < m then 2 * ε * (1 - (Ev T t).indicator 1 h) else 0
  have hcm : ∀ t, Measurable (c t) := by
    intro t; simp only [c]; split_ifs
    · exact (measurable_const.sub (measurable_one.indicator (Ev_meas T t))).const_mul _
    · exact measurable_const
  have hcb : ∀ t h, |c t h| ≤ 2 * ε := by
    intro t h; simp only [c]; split_ifs
    · unfold Set.indicator; split_ifs
      · simp; linarith
      · simp; rw [abs_of_nonneg (by linarith)]
    · simp; linarith
  have key := regret_ge (env Δ (-1) ε m) π hπ T (arms 1) ⟨1, rfl⟩ hθ c hcm (2 * ε) hcb (by
    intro h hh
    apply Finset.sum_le_sum; intro t _
    obtain ⟨j, hj⟩ := hh t
    show c t h ≤ ((h t).1 - arms 1) ⬝ᵥ vv Δ (-1) ε m t
    simp only [c]
    split_ifs with htm
    · by_cases he : (h t).1 = arms 1
      · rw [Set.indicator_of_mem (show h ∈ Ev T t from he), Pi.one_apply, sub_self, mul_zero,
          ← hj]
        exact minus_nonneg Δ ε m t hε hΔ j
      · rw [Set.indicator_of_notMem (show h ∉ Ev T t from he), sub_zero, mul_one, ← hj]
        exact minus_other Δ ε m t htm hε (by linarith) j (by rw [hj]; exact he)
    · rw [← hj]; exact minus_nonneg Δ ε m t hε hΔ j)
  refine le_trans (le_of_eq ?_) key
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [c]
  split_ifs
  · have hi : Integrable ((Ev T t).indicator (1 : LinearBanditHistory 2 T → ℝ))
        ((env Δ (-1) ε m).histMeasure π T) :=
      (integrable_const (1 : ℝ)).indicator (Ev_meas T t)
    rw [integral_const_mul, integral_sub (f := fun _ => (1 : ℝ)) (integrable_const _) hi,
      integral_const, integral_indicator_one (Ev_meas T t)]
    simp [measureReal_def]
  · simp

/-! ### Numerics -/

lemma exp_small : Real.exp (4 / 63) ≤ 5 / 4 := by
  have h := Real.add_one_le_exp (-(4 / 63 : ℝ))
  have hpos := Real.exp_pos (4 / 63 : ℝ)
  have e : Real.exp (4 / 63) * Real.exp (-(4 / 63)) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith

lemma rbar_pow (ε : ℝ) (m : ℕ) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 16) (hm : (m : ℝ) * ε ^ 2 = 1 / 64) :
    rbar ε ^ m ≤ 5 / 4 := by
  unfold rbar
  have h1 : 0 < 1 - ε ^ 2 := by nlinarith
  have h2 : 0 ≤ 4 * ε ^ 2 / (1 - ε ^ 2) := by positivity
  calc (1 + 4 * ε ^ 2 / (1 - ε ^ 2)) ^ m ≤ Real.exp (4 * ε ^ 2 / (1 - ε ^ 2)) ^ m := by
        gcongr; linarith [Real.add_one_le_exp (4 * ε ^ 2 / (1 - ε ^ 2))]
    _ = Real.exp (m * (4 * ε ^ 2 / (1 - ε ^ 2))) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (4 / 63) := by
        apply Real.exp_le_exp.mpr
        rw [← mul_div_assoc, div_le_iff₀ h1]
        nlinarith
    _ ≤ 5 / 4 := exp_small

end T22

-- ===== Main =====

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal

namespace T22

theorem lower_bound (Δ : ℝ) (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 2) (C : ℝ) (hC : Δ⁻¹ ≤ C) (T : ℕ)
    (hT : ⌈(Δ ^ 2)⁻¹⌉₊ ≤ T) :
    ∃ E : ℝ → LinEnv 2,
      (∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
        (E σ).IsCorruptedStoch (Set.range arms) ![σ * Δ / 2, 1 / 2] C T) ∧
      ∀ π : LinearBanditPolicy 2, IsSupportedLinearPolicy (Set.range arms) π →
        (1 / 16) * min (Real.sqrt T) (Real.sqrt (C / Δ)) ≤
          max ((E 1).regret (Set.range arms) π T) ((E (-1)).regret (Set.range arms) π T) := by
  -- the truncation length and the corruption level
  set m : ℕ := min T ⌊2 * C / Δ⌋₊ with hm
  have hΔ2 : 0 < (Δ ^ 2)⁻¹ := by positivity
  have hTr : (Δ ^ 2)⁻¹ ≤ (T : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hT)
  have hCΔ : (Δ ^ 2)⁻¹ ≤ C / Δ := by
    rw [show (Δ ^ 2)⁻¹ = Δ⁻¹ / Δ by field_simp]
    exact div_le_div_of_nonneg_right hC hΔ.le
  have hCΔ1 : 4 ≤ C / Δ := by
    have : (4 : ℝ) ≤ (Δ ^ 2)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by positivity)]; nlinarith
    linarith
  have hfl : C / Δ ≤ (⌊2 * C / Δ⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (2 * C / Δ)
    have e : 2 * C / Δ = 2 * (C / Δ) := by ring
    linarith
  have hCpos : 0 < C := lt_of_lt_of_le (inv_pos.mpr hΔ) hC
  have hfl' : (⌊2 * C / Δ⌋₊ : ℝ) ≤ 2 * C / Δ := Nat.floor_le (by positivity)
  have hmT : m ≤ T := min_le_left _ _
  have hmr : ((m : ℕ) : ℝ) = min (T : ℝ) (⌊2 * C / Δ⌋₊ : ℝ) := by rw [hm]; push_cast; rfl
  have hm_low : (Δ ^ 2)⁻¹ ≤ (m : ℝ) := by rw [hmr]; exact le_min hTr (hCΔ.trans hfl)
  have hm_min : min (T : ℝ) (C / Δ) ≤ (m : ℝ) := by
    rw [hmr]; exact min_le_min le_rfl hfl
  have hmC : (m : ℝ) * (Δ / 2) ≤ C := by
    have : (m : ℝ) ≤ 2 * C / Δ := by rw [hmr]; exact (min_le_right _ _).trans hfl'
    calc (m : ℝ) * (Δ / 2) ≤ 2 * C / Δ * (Δ / 2) := by gcongr
      _ = C := by field_simp
  have hm1 : (1 : ℝ) ≤ m := by
    have : (1 : ℝ) ≤ (Δ ^ 2)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by positivity)]; nlinarith
    linarith
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
  set ε : ℝ := 1 / (8 * Real.sqrt m) with hε
  have hεpos : 0 < ε := by positivity
  have hsqm : Δ⁻¹ ≤ Real.sqrt m := by
    rw [show Δ⁻¹ = Real.sqrt ((Δ ^ 2)⁻¹) by
      rw [Real.sqrt_inv, Real.sqrt_sq hΔ.le]]
    exact Real.sqrt_le_sqrt hm_low
  have hεΔ : ε ≤ Δ / 8 := by
    rw [hε, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 1 ≤ Δ * Real.sqrt m := by
      have := mul_le_mul_of_nonneg_left hsqm hΔ.le
      rwa [mul_inv_cancel₀ hΔ.ne'] at this
    linarith
  have hε16 : ε ≤ 1 / 16 := by linarith
  have hmε : (m : ℝ) * ε ^ 2 = 1 / 64 := by
    rw [hε, div_pow, mul_pow, Real.sq_sqrt (by linarith)]
    field_simp
    ring
  have hR : 4 * ENNReal.ofReal (rbar ε) ^ m ≤ 5 := by
    rw [← ENNReal.ofReal_pow (by linarith [rbar_ge_one ε hεpos.le hε16])]
    have := rbar_pow ε m hεpos.le hε16 hmε
    calc (4 : ℝ≥0∞) * ENNReal.ofReal (rbar ε ^ m) ≤ 4 * ENNReal.ofReal (5 / 4) := by
          gcongr
      _ = 5 := by
          rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
  refine ⟨fun σ => env Δ σ ε m, fun σ hσ => env_corrupted Δ σ ε C m T hσ hεpos.le
    (by linarith) hΔ hΔ' hmT hmC, fun π hπ => ?_⟩
  -- the two regret lower bounds
  have hplus := regret_plus Δ ε m T hεpos.le hε16 hΔ hΔ' π hπ
  have hminus := regret_minus Δ ε m T hεpos.le hε16 hΔ hΔ' π hπ
  -- the testing inequality, transported to the horizon `T`
  have htv : ∀ t : Fin T, (t : ℕ) < m →
      ((env Δ (-1) ε m).histMeasure π T (Ev T t)).toReal ≤
        ((env Δ 1 ε m).histMeasure π T (Ev T t)).toReal + 1 / 2 := by
    intro t ht
    have e1 := marg_event (env Δ (-1) ε m) π m T hmT t ht {arms 1} (measurableSet_singleton _)
    have e2 := marg_event (env Δ 1 ε m) π m T hmT t ht {arms 1} (measurableSet_singleton _)
    have hev : Ev T t = {h | (h ⟨(t : ℕ), by omega⟩).1 ∈ ({arms 1} : Set (Fin 2 → ℝ))} := rfl
    rw [hev, e1, e2]
    exact tv_event Δ ε m hεpos.le hε16 π hπ hR _
      ((measurableSet_singleton _).preimage (measurable_pi_apply _).fst)
  have hsum : ε * m ≤ (env Δ 1 ε m).regret (Set.range arms) π T +
      (env Δ (-1) ε m).regret (Set.range arms) π T := by
    refine le_trans ?_ (add_le_add hplus hminus)
    rw [← Finset.sum_add_distrib]
    have hcount : ∑ t : Fin T, (if (t : ℕ) < m then ε else 0) = ε * m := by
      rw [Fin.sum_univ_eq_sum_range (fun t => if t < m then ε else 0) T, Finset.sum_ite,
        Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
      congr 2
      have : (Finset.range T).filter (fun t => t < m) = Finset.range m := by
        ext t; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [this, Finset.card_range]
    rw [← hcount]
    apply Finset.sum_le_sum
    intro t _
    split_ifs with ht
    · have := htv t ht
      nlinarith
    · simp
  have hεm : ε * m = Real.sqrt m / 8 := by
    rw [hε]
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ m by linarith)
    field_simp
    nlinarith [h2]
  have hsqrt : min (Real.sqrt T) (Real.sqrt (C / Δ)) ≤ Real.sqrt m := by
    have : min (Real.sqrt T) (Real.sqrt (C / Δ)) = Real.sqrt (min (T : ℝ) (C / Δ)) := by
      rcases le_total (T : ℝ) (C / Δ) with h | h
      · rw [min_eq_left h, min_eq_left (Real.sqrt_le_sqrt h)]
      · rw [min_eq_right h, min_eq_right (Real.sqrt_le_sqrt h)]
    rw [this]
    exact Real.sqrt_le_sqrt hm_min
  have hmax := add_le_add (le_max_left ((env Δ 1 ε m).regret (Set.range arms) π T)
    ((env Δ (-1) ε m).regret (Set.range arms) π T))
    (le_max_right ((env Δ 1 ε m).regret (Set.range arms) π T)
    ((env Δ (-1) ε m).regret (Set.range arms) π T))
  show (1 / 16) * min (Real.sqrt T) (Real.sqrt (C / Δ)) ≤
    max ((env Δ 1 ε m).regret (Set.range arms) π T) ((env Δ (-1) ε m).regret (Set.range arms) π T)
  linarith

end T22

namespace IAFTRL

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm

theorem _root_.solution (Δ : ℝ) (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 2) :
    let arms : Fin 3 → Fin 2 → ℝ := ![![-1, 0], ![1, 0], ![0, 1]]
    let θ : ℝ → Fin 2 → ℝ := fun σ => ![σ * Δ / 2, 1 / 2]
    (∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      (∃ jstar : Fin 3, IsUniqueMin arms (θ σ) jstar ∧
        (∀ j, j ≠ jstar → Δ ≤ (arms j - arms jstar) ⬝ᵥ θ σ) ∧
        ∃ j, j ≠ jstar ∧ (arms j - arms jstar) ⬝ᵥ θ σ = Δ) ∧
      linearBanditAllocationValue arms (-θ σ) = 4 / (1 + Δ)) ∧
    ∀ C : ℝ, Δ⁻¹ ≤ C → ∀ T : ℕ, ⌈(Δ ^ 2)⁻¹⌉₊ ≤ T →
      ∃ E : ℝ → LinEnv 2,
        (∀ σ : ℝ, (σ = 1 ∨ σ = -1) → (E σ).IsCorruptedStoch (Set.range arms) (θ σ) C T) ∧
        ∀ π : LinearBanditPolicy 2, IsSupportedLinearPolicy (Set.range arms) π →
          (1 / 16) * min (Real.sqrt T) (Real.sqrt (C / Δ)) ≤
            max ((E 1).regret (Set.range arms) π T) ((E (-1)).regret (Set.range arms) π T) := by
  intro arms θ
  exact ⟨fun σ hσ => T22.inst_facts Δ hΔ hΔ' σ hσ,
    fun C hC T hT => T22.lower_bound Δ hΔ hΔ' C hC T hT⟩

end IAFTRL
