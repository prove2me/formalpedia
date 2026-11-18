-- Prove2me | solution 1 for IAFTRL.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T04:37:44.59918+00:00
-- url     : https://prove2.me/submissions/c52cb561-0857-45bc-842f-16ef643ad169

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_SignModel

-- ===== LB/Common =====

/-! # Common tools for the lower bounds (Theorems 3.2 and 4.1): sign laws, history laws,
change of measure, χ² testing, and regret lower bounds. -/

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal Pointwise

namespace LBC

/-! ### Sign laws -/

lemma clampOne_of {x : ℝ} (h : |x| ≤ 1) : clampOne x = x := by
  unfold clampOne; rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

lemma lintegral_signObs (μ : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y, g y ∂(signObs μ) = ENNReal.ofReal ((1 + clampOne μ) / 2) * g 1 +
      ENNReal.ofReal ((1 - clampOne μ) / 2) * g (-1) := by
  unfold signObs
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
    lintegral_dirac]
  rfl

lemma signObs_compl (μ : ℝ) : signObs μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  rw [signObs_apply _ _ measurableSet_Icc.compl]
  simp [Set.indicator, Set.mem_Icc]

lemma integral_signObs (μ : ℝ) (h : |μ| ≤ 1) : ∫ y, y ∂(signObs μ) = μ := by
  have hc := clampOne_of h
  rw [abs_le] at h
  unfold signObs
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · rw [hc, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
    simp only [smul_eq_mul]; ring
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma signKernel_apply {d : ℕ} (θ a : Fin d → ℝ) : signKernel θ a = signObs (a ⬝ᵥ θ) := rfl

/-- density ratio `dQ_{μm}/dQ_{μp}` at `y ∈ {±1}` -/
noncomputable def ratio (μp μm y : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((1 + μm * y) / (1 + μp * y))

lemma signObs_change (μp μm : ℝ) (hp : |μp| < 1) (hm : |μm| ≤ 1) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y, g y ∂(signObs μm) = ∫⁻ y, g y * ratio μp μm y ∂(signObs μp) := by
  rw [lintegral_signObs, lintegral_signObs, clampOne_of hm, clampOne_of hp.le]
  rw [abs_lt] at hp; rw [abs_le] at hm
  unfold ratio
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

lemma signObs_chi (μp μm : ℝ) (hp : |μp| < 1) (hm : |μm| ≤ 1) :
    ∫⁻ y, ratio μp μm y ^ 2 ∂(signObs μp) =
      ENNReal.ofReal (1 + (μm - μp) ^ 2 / (1 - μp ^ 2)) := by
  rw [lintegral_signObs, clampOne_of hp.le]
  rw [abs_lt] at hp; rw [abs_le] at hm
  unfold ratio
  have hp1 : 0 < 1 + μp := by linarith
  have hp2 : 0 < 1 - μp := by linarith
  simp only [mul_one, mul_neg_one, ← sub_eq_add_neg]
  rw [← ENNReal.ofReal_pow (div_nonneg (by linarith) hp1.le),
    ← ENNReal.ofReal_pow (div_nonneg (by linarith) hp2.le),
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  have h1 : (1 + μp) ≠ 0 := by intro h; linarith
  have h2 : (1 - μp) ≠ 0 := by intro h; linarith
  have h3 : (1 - μp ^ 2) ≠ 0 := by nlinarith
  field_simp
  ring

/-! ### History laws -/

section Hist


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

/-- change of measure for a policy supported on `𝒜`: the feedback densities are only needed on `𝒜` -/
lemma change_of_measure_supp (E₁ E₂ : LinEnv d) (π : LinearBanditPolicy d) (𝒜 : Set (Fin d → ℝ))
    (hπ : IsSupportedLinearPolicy 𝒜 π) (N : ℕ)
    (ρ : ℕ → (Fin d → ℝ) → ℝ → ℝ≥0∞) (hρ : ∀ t, Measurable (Function.uncurry (ρ t)))
    (hfb : ∀ t < N, ∀ a ∈ 𝒜, ∀ (g : ℝ → ℝ≥0∞), Measurable g →
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
    have step1 : ∀ (h : LinearBanditHistory d n),
        ∫⁻ a, ∫⁻ y, f (snocH h a y) ∂(E₂.fb n a) ∂(π.select n h) =
          ∫⁻ a, ∫⁻ y, f (snocH h a y) * ρ n a y ∂(E₁.fb n a) ∂(π.select n h) := by
      intro h
      refine lintegral_congr_ae ?_
      have hae : ∀ᵐ a ∂(π.select n h), a ∈ 𝒜 := by rw [ae_iff]; exact hπ n h
      filter_upwards [hae] with a ha
      exact hfb n (by omega) a ha _ (hf.comp (meas_snocH_y h a))
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

lemma marg_event (E : LinEnv d) (π : LinearBanditPolicy d) (m N : ℕ) (hmN : m ≤ N) (t : ℕ)
    (ht : t < m) (s : Set (Fin d → ℝ)) (hs : MeasurableSet s) :
    E.histMeasure π N {h | (h ⟨t, by omega⟩).1 ∈ s} =
      E.histMeasure π m {h | (h ⟨t, ht⟩).1 ∈ s} := by
  obtain ⟨k, rfl⟩ : ∃ k, N = m + k := ⟨N - m, by omega⟩
  have hmeas : Measurable fun h : LinearBanditHistory d m => (h ⟨t, ht⟩).1 :=
    (measurable_pi_apply _).fst
  have hS : MeasurableSet {h : LinearBanditHistory d m | (h ⟨t, ht⟩).1 ∈ s} := hs.preimage hmeas
  rw [← hist_marginal E π m k, Measure.map_apply (restr_meas _) hS]
  rfl

end Hist

/-! ### Sign environments and χ² testing -/

section Sign

variable {d : ℕ}

/-- the oblivious sign-feedback environment with loss vectors `v t` -/
noncomputable def mkEnv (v : ℕ → Fin d → ℝ) : LinEnv d where
  θs := v
  fb t := signKernel (v t)
  markov _ := inferInstance

lemma mkEnv_fb (v : ℕ → Fin d → ℝ) (t : ℕ) (a : Fin d → ℝ) :
    (mkEnv v).fb t a = signObs (a ⬝ᵥ v t) := rfl

/-- feedback conditions of a corrupted stochastic environment -/
lemma mkEnv_feedback (v : ℕ → Fin d → ℝ) (t : ℕ) (a : Fin d → ℝ) (h : |a ⬝ᵥ v t| ≤ 1) :
    (mkEnv v).fb t a (Set.Icc (-1 : ℝ) 1)ᶜ = 0 ∧ ∫ y, y ∂((mkEnv v).fb t a) = a ⬝ᵥ (mkEnv v).θs t :=
  ⟨signObs_compl _, integral_signObs _ h⟩

/-- the likelihood ratio of `mkEnv v₂` against `mkEnv v₁` -/
noncomputable def rhoS (v₁ v₂ : ℕ → Fin d → ℝ) (t : ℕ) (a : Fin d → ℝ) (y : ℝ) : ℝ≥0∞ :=
  ratio (clampOne (a ⬝ᵥ v₁ t)) (clampOne (a ⬝ᵥ v₂ t)) y

lemma rhoS_meas (v₁ v₂ : ℕ → Fin d → ℝ) (t : ℕ) : Measurable (Function.uncurry (rhoS v₁ v₂ t)) := by
  unfold rhoS ratio Function.uncurry
  have h1 : Continuous fun p : (Fin d → ℝ) × ℝ => clampOne (p.1 ⬝ᵥ v₂ t) :=
    clampOne_continuous.comp (continuous_fst.dotProduct continuous_const)
  have h2 : Continuous fun p : (Fin d → ℝ) × ℝ => clampOne (p.1 ⬝ᵥ v₁ t) :=
    clampOne_continuous.comp (continuous_fst.dotProduct continuous_const)
  exact ENNReal.measurable_ofReal.comp
    (((continuous_const.add (h1.mul continuous_snd)).measurable).div
      ((continuous_const.add (h2.mul continuous_snd)).measurable))

lemma rhoS_change (v₁ v₂ : ℕ → Fin d → ℝ) (t : ℕ) (a : Fin d → ℝ) (h1 : |a ⬝ᵥ v₁ t| < 1)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ y, g y ∂((mkEnv v₂).fb t a) = ∫⁻ y, g y * rhoS v₁ v₂ t a y ∂((mkEnv v₁).fb t a) := by
  rw [mkEnv_fb, mkEnv_fb]
  unfold rhoS
  have hc : clampOne (a ⬝ᵥ v₁ t) = a ⬝ᵥ v₁ t := clampOne_of h1.le
  have e1 : signObs (a ⬝ᵥ v₂ t) = signObs (clampOne (a ⬝ᵥ v₂ t)) := by
    unfold signObs; rw [clampOne_of (clampOne_mem _ |> fun h => abs_le.mpr h)]
  have e2 : signObs (a ⬝ᵥ v₁ t) = signObs (clampOne (a ⬝ᵥ v₁ t)) := by rw [hc]
  rw [e1, e2]
  exact signObs_change _ _ (by rw [hc]; exact h1) (abs_le.mpr (clampOne_mem _)) g

lemma rhoS_chi (v₁ v₂ : ℕ → Fin d → ℝ) (t : ℕ) (a : Fin d → ℝ) (h1 : |a ⬝ᵥ v₁ t| ≤ 1 / 2)
    (h2 : |a ⬝ᵥ v₂ t| ≤ 1) :
    ∫⁻ y, rhoS v₁ v₂ t a y ^ 2 ∂((mkEnv v₁).fb t a) ≤
      ENNReal.ofReal (1 + 4 / 3 * (a ⬝ᵥ v₂ t - a ⬝ᵥ v₁ t) ^ 2) := by
  rw [mkEnv_fb]
  unfold rhoS
  have hc1 : clampOne (a ⬝ᵥ v₁ t) = a ⬝ᵥ v₁ t := clampOne_of (h1.trans (by norm_num))
  have hc2 : clampOne (a ⬝ᵥ v₂ t) = a ⬝ᵥ v₂ t := clampOne_of h2
  rw [hc1, hc2, signObs_chi _ _ (h1.trans_lt (by norm_num)) h2]
  apply ENNReal.ofReal_le_ofReal
  have hb : (a ⬝ᵥ v₁ t) ^ 2 ≤ 1 / 4 := by
    rw [abs_le] at h1; nlinarith
  have hpos : (3 : ℝ) / 4 ≤ 1 - (a ⬝ᵥ v₁ t) ^ 2 := by linarith
  have hq : 0 ≤ (a ⬝ᵥ v₂ t - a ⬝ᵥ v₁ t) ^ 2 := sq_nonneg _
  have : (a ⬝ᵥ v₂ t - a ⬝ᵥ v₁ t) ^ 2 / (1 - (a ⬝ᵥ v₁ t) ^ 2) ≤
      4 / 3 * (a ⬝ᵥ v₂ t - a ⬝ᵥ v₁ t) ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- the second moment of the likelihood ratio -/
lemma second_moment (v₁ v₂ : ℕ → Fin d → ℝ) (𝒜 : Set (Fin d → ℝ)) (π : LinearBanditPolicy d)
    (hπ : IsSupportedLinearPolicy 𝒜 π) (m : ℕ) (r : ℝ)
    (hr : ∀ t < m, ∀ a ∈ 𝒜, ∫⁻ y, rhoS v₁ v₂ t a y ^ 2 ∂((mkEnv v₁).fb t a) ≤ ENNReal.ofReal r) :
    ∀ n ≤ m, ∫⁻ h, LR (rhoS v₁ v₂) n h ^ 2 ∂((mkEnv v₁).histMeasure π n) ≤
      ENNReal.ofReal r ^ n := by
  intro n
  induction n with
  | zero => intro _; simp [LR, LinEnv.histMeasure]
  | succ n ih =>
    intro hn
    have hLR := LR_meas (rhoS v₁ v₂) (rhoS_meas v₁ v₂)
    have hρn := rhoS_meas v₁ v₂ n
    rw [lintegral_hist_succ _ π n ((hLR (n + 1)).pow_const 2)]
    simp_rw [LR_succ, mul_pow]
    have hy : ∀ a, Measurable fun y => rhoS v₁ v₂ n a y ^ 2 :=
      fun a => (hρn.comp (measurable_const.prodMk measurable_id)).pow_const 2
    have hinner : ∀ h : LinearBanditHistory d n,
        ∫⁻ a, ∫⁻ y, LR (rhoS v₁ v₂) n h ^ 2 * rhoS v₁ v₂ n a y ^ 2 ∂((mkEnv v₁).fb n a)
          ∂(π.select n h) ≤ LR (rhoS v₁ v₂) n h ^ 2 * ENNReal.ofReal r := by
      intro h
      have hφ : Measurable fun a => ∫⁻ y, rhoS v₁ v₂ n a y ^ 2 ∂((mkEnv v₁).fb n a) :=
        Measurable.lintegral_kernel_prod_right (κ := (mkEnv v₁).fb n)
          (f := fun a y => rhoS v₁ v₂ n a y ^ 2) (hρn.pow_const 2)
      simp_rw [lintegral_const_mul _ (hy _)]
      rw [lintegral_const_mul _ hφ]
      gcongr
      calc ∫⁻ a, ∫⁻ y, rhoS v₁ v₂ n a y ^ 2 ∂((mkEnv v₁).fb n a) ∂(π.select n h)
          ≤ ∫⁻ _a, ENNReal.ofReal r ∂(π.select n h) := by
            have hae : ∀ᵐ a ∂(π.select n h), a ∈ 𝒜 := by rw [ae_iff]; exact hπ n h
            refine lintegral_mono_ae (hae.mono fun a ha => ?_)
            exact hr n (by omega) a ha
        _ = ENNReal.ofReal r := by rw [lintegral_const, measure_univ, mul_one]
    calc ∫⁻ h, ∫⁻ a, ∫⁻ y, LR (rhoS v₁ v₂) n h ^ 2 * rhoS v₁ v₂ n a y ^ 2
          ∂((mkEnv v₁).fb n a) ∂(π.select n h) ∂((mkEnv v₁).histMeasure π n)
        ≤ ∫⁻ h, LR (rhoS v₁ v₂) n h ^ 2 * ENNReal.ofReal r
          ∂((mkEnv v₁).histMeasure π n) := lintegral_mono hinner
      _ = (∫⁻ h, LR (rhoS v₁ v₂) n h ^ 2 ∂((mkEnv v₁).histMeasure π n)) *
          ENNReal.ofReal r := lintegral_mul_const _ ((hLR n).pow_const 2)
      _ ≤ ENNReal.ofReal r ^ n * ENNReal.ofReal r := by
          gcongr; exact ih (by omega)
      _ = ENNReal.ofReal r ^ (n + 1) := by rw [pow_succ]

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

lemma exp_small : Real.exp (1 / 12) ≤ 5 / 4 := by
  have h := Real.add_one_le_exp (-(1 / 12 : ℝ))
  have hpos := Real.exp_pos (1 / 12 : ℝ)
  have e : Real.exp (1 / 12) * Real.exp (-(1 / 12)) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith

/-- **The testing inequality.** If the two sign environments are `κ`-close on `𝒜` for the first
`m` rounds with `m κ ≤ 1/16`, then every event of the first `m` rounds has close probabilities. -/
lemma tv_event (v₁ v₂ : ℕ → Fin d → ℝ) (𝒜 : Set (Fin d → ℝ)) (π : LinearBanditPolicy d)
    (hπ : IsSupportedLinearPolicy 𝒜 π) (m : ℕ) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (h1 : ∀ t < m, ∀ a ∈ 𝒜, |a ⬝ᵥ v₁ t| ≤ 1 / 2) (h2 : ∀ t < m, ∀ a ∈ 𝒜, |a ⬝ᵥ v₂ t| ≤ 1 / 2)
    (hκ : ∀ t < m, ∀ a ∈ 𝒜, (a ⬝ᵥ v₂ t - a ⬝ᵥ v₁ t) ^ 2 ≤ κ) (hmκ : (m : ℝ) * κ ≤ 1 / 16)
    (S : Set (LinearBanditHistory d m)) (hS : MeasurableSet S) :
    ((mkEnv v₂).histMeasure π m S).toReal ≤ ((mkEnv v₁).histMeasure π m S).toReal + 1 / 2 := by
  set P := (mkEnv v₁).histMeasure π m with hP
  set Q := (mkEnv v₂).histMeasure π m with hQ
  set L := LR (rhoS v₁ v₂) m with hL
  have hLm : Measurable L := LR_meas (rhoS v₁ v₂) (rhoS_meas v₁ v₂) m
  have hcm := change_of_measure_supp (mkEnv v₁) (mkEnv v₂) π 𝒜 hπ m (rhoS v₁ v₂)
    (rhoS_meas v₁ v₂)
    (fun t ht a ha g _ => rhoS_change v₁ v₂ t a ((h1 t ht a ha).trans_lt (by norm_num)) g) m le_rfl
  have hind : Measurable (S.indicator (1 : LinearBanditHistory d m → ℝ≥0∞)) :=
    measurable_one.indicator hS
  have hQS : Q S = ∫⁻ h, S.indicator 1 h * L h ∂P := by
    rw [← lintegral_indicator_one hS]; exact hcm _ hind
  have hQ1 : ∫⁻ h, L h ∂P = 1 := by
    have := hcm (fun _ => 1) measurable_const
    simp only [one_mul, lintegral_const, measure_univ, mul_one] at this
    exact this.symm
  have hr : ∀ t < m, ∀ a ∈ 𝒜, ∫⁻ y, rhoS v₁ v₂ t a y ^ 2 ∂((mkEnv v₁).fb t a) ≤
      ENNReal.ofReal (1 + 4 / 3 * κ) := by
    intro t ht a ha
    refine (rhoS_chi v₁ v₂ t a (h1 t ht a ha) ((h2 t ht a ha).trans (by norm_num))).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have := hκ t ht a ha
    linarith
  have hsq := second_moment v₁ v₂ 𝒜 π hπ m _ hr m le_rfl
  have hRr : (1 + 4 / 3 * κ) ^ m ≤ 5 / 4 := by
    calc (1 + 4 / 3 * κ) ^ m ≤ Real.exp (4 / 3 * κ) ^ m := by
          gcongr; linarith [Real.add_one_le_exp (4 / 3 * κ)]
      _ = Real.exp (m * (4 / 3 * κ)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (1 / 12) := by
          apply Real.exp_le_exp.mpr; nlinarith
      _ ≤ 5 / 4 := exp_small
  have hR : 4 * ENNReal.ofReal (1 + 4 / 3 * κ) ^ m ≤ 5 := by
    rw [← ENNReal.ofReal_pow (by linarith)]
    calc (4 : ℝ≥0∞) * ENNReal.ofReal ((1 + 4 / 3 * κ) ^ m) ≤ 4 * ENNReal.ofReal (5 / 4) := by
          gcongr
      _ = 5 := by
          rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
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
  have h2' : 4 * Q S + 8 ≤ (4 * P S + 2) + 8 := by
    calc 4 * Q S + 8 = 4 * Q S + 8 * 1 := by ring
      _ ≤ 4 * P S + 4 * ∫⁻ h, L h ^ 2 ∂P + 5 := hint
      _ ≤ 4 * P S + 5 + 5 := by
          gcongr
          exact (mul_le_mul_right hsq 4).trans hR
      _ = (4 * P S + 2) + 8 := by ring
  have h3 : 4 * Q S ≤ 4 * P S + 2 := (ENNReal.add_le_add_iff_right (by simp)).mp h2'
  have h4 := ENNReal.toReal_mono (by finiteness) h3
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by simp), ENNReal.toReal_mul] at h4
  simp only [ENNReal.toReal_ofNat] at h4
  linarith

end Sign

/-! ### Regret lower bounds -/

section Regret

variable {d : ℕ}

lemma regret_ge (E : LinEnv d) (π : LinearBanditPolicy d) (𝒜 : Set (Fin d → ℝ))
    (h𝒜 : MeasurableSet 𝒜) (hπ : IsSupportedLinearPolicy 𝒜 π) (T : ℕ) (u : Fin d → ℝ)
    (hu : u ∈ 𝒜) (hθ : ∀ t < T, ∀ a ∈ 𝒜, |a ⬝ᵥ E.θs t| ≤ 1)
    (c : Fin T → LinearBanditHistory d T → ℝ) (hcm : ∀ t, Measurable (c t)) (B : ℝ)
    (hcb : ∀ t h, |c t h| ≤ B)
    (hle : ∀ h : LinearBanditHistory d T, (∀ t, (h t).1 ∈ 𝒜) →
      ∑ t, c t h ≤ ∑ t : Fin T, ((h t).1 - u) ⬝ᵥ E.θs t) :
    ∑ t, ∫ h, c t h ∂(E.histMeasure π T) ≤ E.regret 𝒜 π T := by
  have hae := hist_ae_supported E π 𝒜 h𝒜 hπ T
  have hfm : ∀ u' : Fin d → ℝ, Measurable fun h : LinearBanditHistory d T =>
      ∑ t : Fin T, ((h t).1 - u') ⬝ᵥ E.θs t := by
    intro u'
    refine Finset.measurable_sum _ fun t _ => ?_
    exact (continuous_id.dotProduct continuous_const).measurable.comp
      ((measurable_pi_apply t).fst.sub measurable_const)
  have hbnd : ∀ u' ∈ 𝒜, ∀ h : LinearBanditHistory d T, (∀ t, (h t).1 ∈ 𝒜) →
      |∑ t : Fin T, ((h t).1 - u') ⬝ᵥ E.θs t| ≤ 2 * T := by
    intro u' hu' h hh
    calc |∑ t : Fin T, ((h t).1 - u') ⬝ᵥ E.θs t| ≤ ∑ t : Fin T, |((h t).1 - u') ⬝ᵥ E.θs t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin T, (2 : ℝ) := by
          apply Finset.sum_le_sum; intro t _
          rw [sub_dotProduct]
          have h1 := hθ t t.2 _ (hh t); have h2 := hθ t t.2 u' hu'
          rw [abs_le] at h1 h2 ⊢; constructor <;> linarith
      _ = 2 * T := by simp; ring
  have hf_int : Integrable (fun h : LinearBanditHistory d T =>
      ∑ t : Fin T, ((h t).1 - u) ⬝ᵥ E.θs t) (E.histMeasure π T) := by
    refine Integrable.of_bound (hfm u).aestronglyMeasurable (2 * T) (hae.mono fun h hh => ?_)
    rw [Real.norm_eq_abs]; exact hbnd u hu h hh
  have hc_int : ∀ t, Integrable (c t) (E.histMeasure π T) := fun t =>
    Integrable.of_bound (hcm t).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun h => by rw [Real.norm_eq_abs]; exact hcb t h)
  have hbdd : BddAbove ((fun u => ∫ h, ∑ t : Fin T, ((h t).1 - u) ⬝ᵥ E.θs t
      ∂(E.histMeasure π T)) '' 𝒜) := by
    refine ⟨2 * T, ?_⟩
    rintro _ ⟨u', hu', rfl⟩
    have := norm_integral_le_of_norm_le_const (μ := E.histMeasure π T)
      (f := fun h : LinearBanditHistory d T => ∑ t : Fin T, ((h t).1 - u') ⬝ᵥ E.θs t)
      (C := 2 * T) (hae.mono fun h hh => by rw [Real.norm_eq_abs]; exact hbnd u' hu' h hh)
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  calc ∑ t, ∫ h, c t h ∂(E.histMeasure π T) = ∫ h, ∑ t, c t h ∂(E.histMeasure π T) :=
        (integral_finsetSum _ fun t _ => hc_int t).symm
    _ ≤ ∫ h, ∑ t : Fin T, ((h t).1 - u) ⬝ᵥ E.θs t ∂(E.histMeasure π T) :=
        integral_mono_ae (integrable_finsetSum _ fun t _ => hc_int t) hf_int
          (hae.mono fun h hh => hle h hh)
    _ ≤ E.regret 𝒜 π T := le_csSup hbdd ⟨u, hu, rfl⟩

end Regret

/-! ### Geometry helpers -/

section Geo

variable {d : ℕ}

lemma convexHull_le_of (𝒜 : Set (Fin d → ℝ)) (w : Fin d → ℝ) (c : ℝ)
    (h : ∀ a ∈ 𝒜, w ⬝ᵥ a ≤ c) : ∀ u ∈ convexHull ℝ 𝒜, w ⬝ᵥ u ≤ c := by
  have hconv : Convex ℝ {u : Fin d → ℝ | w ⬝ᵥ u ≤ c} :=
    convex_halfSpace_le (f := fun u => w ⬝ᵥ u)
      ⟨fun x y => dotProduct_add w x y, fun r x => dotProduct_smul r w x⟩ c
  intro u hu
  exact convexHull_min (fun a ha => h a ha) hconv hu

/-- lower bound for a gauge from a bounded linear functional on the set -/
lemma le_gauge_of_bound (S : Set (Fin d → ℝ)) (w x : Fin d → ℝ) (r0 : ℝ) (hr0 : 0 < r0)
    (hx : x ∈ r0 • S) (hS : ∀ s ∈ S, |w ⬝ᵥ s| ≤ 1) : |w ⬝ᵥ x| ≤ gauge S x := by
  rw [gauge_def]
  refine le_csInf ⟨r0, hr0, hx⟩ ?_
  rintro r ⟨hr, s, hs, rfl⟩
  rw [dotProduct_smul, smul_eq_mul, abs_mul, abs_of_pos (Set.mem_Ioi.mp hr)]
  have := hS s hs
  have hr' : 0 < r := hr
  nlinarith

end Geo

end LBC

-- ===== LB/Geo2 =====

/-! # Planar geometry for the lower-bound instances: 2×2 inverses, a Cauchy–Schwarz bound,
explicit design matrices of two-point allocations, and gauge bounds. -/

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal Pointwise NNReal

namespace LBC

/-! ### 2×2 matrices -/

lemma quad_inv_fin_two (M : Matrix (Fin 2) (Fin 2) ℝ) (hsym : M 1 0 = M 0 1)
    (hdet : M 0 0 * M 1 1 - M 0 1 ^ 2 ≠ 0) (v : Fin 2 → ℝ) :
    v ⬝ᵥ M⁻¹ *ᵥ v = (M 1 1 * v 0 ^ 2 - 2 * M 0 1 * v 0 * v 1 + M 0 0 * v 1 ^ 2) /
      (M 0 0 * M 1 1 - M 0 1 ^ 2) := by
  have hd : M.det = M 0 0 * M 1 1 - M 0 1 ^ 2 := by rw [det_fin_two, hsym]; ring
  have hu : IsUnit M.det := by rw [hd]; exact Ne.isUnit hdet
  rw [inv_def, adjugate_fin_two, Ring.inverse_eq_inv', hd]
  simp [dotProduct, mulVec, Fin.sum_univ_two, Matrix.smul_apply]
  rw [hsym]
  field_simp
  ring

lemma posDef_props (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.PosDef) :
    0 < M 0 0 ∧ 0 < M 1 1 ∧ M 1 0 = M 0 1 ∧ 0 < M 0 0 * M 1 1 - M 0 1 ^ 2 := by
  have h0 : 0 < M 0 0 := hM.diag_pos
  have h1 : 0 < M 1 1 := hM.diag_pos
  have hs : M 1 0 = M 0 1 := by
    have := hM.isHermitian.apply 0 1
    simpa using this
  have hdet := hM.det_pos
  rw [det_fin_two, hs] at hdet
  exact ⟨h0, h1, hs, by nlinarith⟩

/-- Cauchy–Schwarz projection bound in the first coordinate -/
lemma cs_fin_two_0 (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.PosDef) (v : Fin 2 → ℝ) :
    v 0 ^ 2 ≤ M 0 0 * (v ⬝ᵥ M⁻¹ *ᵥ v) := by
  obtain ⟨h0, h1, hs, hdet⟩ := posDef_props M hM
  rw [quad_inv_fin_two M hs hdet.ne', mul_div_assoc', le_div_iff₀ hdet]
  nlinarith [sq_nonneg (M 0 1 * v 0 - M 0 0 * v 1)]

/-- Cauchy–Schwarz projection bound in the second coordinate -/
lemma cs_fin_two_1 (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.PosDef) (v : Fin 2 → ℝ) :
    v 1 ^ 2 ≤ M 1 1 * (v ⬝ᵥ M⁻¹ *ᵥ v) := by
  obtain ⟨h0, h1, hs, hdet⟩ := posDef_props M hM
  rw [quad_inv_fin_two M hs hdet.ne', mul_div_assoc', le_div_iff₀ hdet]
  nlinarith [sq_nonneg (M 0 1 * v 1 - M 1 1 * v 0)]

lemma posDef_fin_two_of (M : Matrix (Fin 2) (Fin 2) ℝ) (hsym : M 1 0 = M 0 1) (h0 : 0 < M 0 0)
    (hdet : 0 < M 0 0 * M 1 1 - M 0 1 ^ 2) : M.PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [hsym]
  · simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_two]
    have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h; push Not at h; apply hx; funext i; fin_cases i <;> simp [h.1, h.2]
    rw [hsym]
    have key : M 0 0 * (x 0 * (M 0 0 * x 0 + M 0 1 * x 1) + x 1 * (M 0 1 * x 0 + M 1 1 * x 1)) =
        (M 0 0 * x 0 + M 0 1 * x 1) ^ 2 + (M 0 0 * M 1 1 - M 0 1 ^ 2) * x 1 ^ 2 := by ring
    have hpos : 0 < (M 0 0 * x 0 + M 0 1 * x 1) ^ 2 + (M 0 0 * M 1 1 - M 0 1 ^ 2) * x 1 ^ 2 := by
      rcases hx' with h | h
      · by_cases h1 : x 1 = 0
        · rw [h1]; simp; positivity
        · have := pow_pos (abs_pos.mpr h1) 2; rw [sq_abs] at this
          have := mul_pos hdet this; nlinarith [sq_nonneg (M 0 0 * x 0 + M 0 1 * x 1)]
      · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this
        have := mul_pos hdet this; nlinarith [sq_nonneg (M 0 0 * x 0 + M 0 1 * x 1)]
    have := key ▸ hpos
    exact pos_of_mul_pos_right this h0.le

/-! ### Two-point allocations -/

/-- the allocation `k δ_b + η δ_e` -/
noncomputable def twoPt (k η : ℝ≥0) (b e : Fin 2 → ℝ) : Measure (Fin 2 → ℝ) :=
  k • Measure.dirac b + η • Measure.dirac e

instance (k η : ℝ≥0) (b e : Fin 2 → ℝ) : IsFiniteMeasure (twoPt k η b e) := by
  unfold twoPt; infer_instance

lemma integral_twoPt (k η : ℝ≥0) (b e : Fin 2 → ℝ) (f : (Fin 2 → ℝ) → ℝ) :
    ∫ a, f a ∂(twoPt k η b e) = k * f b + η * f e := by
  unfold twoPt
  rw [integral_add_measure, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_dirac, integral_dirac]
  · simp [NNReal.smul_def]
  · exact (integrable_dirac (by simp)).smul_measure_nnreal
  · exact (integrable_dirac (by simp)).smul_measure_nnreal

lemma designMat_twoPt (k η : ℝ≥0) (b e : Fin 2 → ℝ) (i j : Fin 2) :
    designMat (twoPt k η b e) i j = k * (b i * b j) + η * (e i * e j) := by
  unfold designMat
  rw [of_apply, integral_twoPt]

lemma twoPt_compl (k η : ℝ≥0) (b e : Fin 2 → ℝ) (𝒜 : Set (Fin 2 → ℝ)) (hb : b ∈ 𝒜)
    (he : e ∈ 𝒜) : twoPt k η b e 𝒜ᶜ = 0 := by
  unfold twoPt
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply,
    Measure.dirac_apply]
  simp [Set.indicator, hb, he]

lemma ctrCost_twoPt (k η : ℝ≥0) (b e θ astar : Fin 2 → ℝ) :
    ctrCost θ astar (twoPt k η b e) = k * ((b - astar) ⬝ᵥ θ) + η * ((e - astar) ⬝ᵥ θ) := by
  unfold ctrCost; rw [integral_twoPt]

/-! ### Gauges -/

lemma gauge_le_comb (S : Set (Fin 2 → ℝ)) (hS : Convex ℝ S) (p q : Fin 2 → ℝ) (hp : p ∈ S)
    (hq : q ∈ S) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    gauge S (α • p + β • q) ≤ α + β := by
  rcases eq_or_lt_of_le (add_nonneg hα hβ) with h | h
  · have hα0 : α = 0 := by linarith
    have hβ0 : β = 0 := by linarith
    subst hα0; subst hβ0; simp [gauge_zero]
  · apply gauge_le_of_mem h.le
    refine ⟨(α / (α + β)) • p + (β / (α + β)) • q, ?_, ?_⟩
    · exact hS hp hq (div_nonneg hα h.le) (div_nonneg hβ h.le) (by field_simp)
    · simp only [smul_add, smul_smul]
      congr 1 <;> congr 1 <;> field_simp

lemma Sset_convex {d : ℕ} (ℬ : Set (Fin d → ℝ)) : Convex ℝ (Sset ℬ) := convex_convexHull ℝ _

lemma mem_Sset_of_mem {d : ℕ} (ℬ : Set (Fin d → ℝ)) {a : Fin d → ℝ} (ha : a ∈ ℬ) : a ∈ Sset ℬ :=
  subset_convexHull ℝ _ (Or.inl ha)

lemma neg_mem_Sset_of_mem {d : ℕ} (ℬ : Set (Fin d → ℝ)) {a : Fin d → ℝ} (ha : a ∈ ℬ) :
    -a ∈ Sset ℬ :=
  subset_convexHull ℝ _ (Or.inr (by simpa using ha))

/-- a linear bound valid on `ℬ ∪ −ℬ` holds on `S` -/
lemma Sset_abs_le {d : ℕ} (ℬ : Set (Fin d → ℝ)) (w : Fin d → ℝ)
    (h : ∀ a ∈ ℬ, |w ⬝ᵥ a| ≤ 1) : ∀ s ∈ Sset ℬ, |w ⬝ᵥ s| ≤ 1 := by
  intro s hs
  have h1 := convexHull_le_of (ℬ ∪ -ℬ) w 1 (by
    rintro a (ha | ha)
    · exact (le_abs_self _).trans (h a ha)
    · have := h (-a) ha; rw [dotProduct_neg, abs_neg] at this; exact (le_abs_self _).trans this) s hs
  have h2 := convexHull_le_of (ℬ ∪ -ℬ) (-w) 1 (by
    rintro a (ha | ha)
    · rw [neg_dotProduct]; exact (neg_le_abs _).trans (h a ha)
    · have := h (-a) ha; rw [dotProduct_neg, abs_neg] at this
      rw [neg_dotProduct]; exact (neg_le_abs _).trans this) s hs
  rw [neg_dotProduct] at h2
  rw [abs_le]; constructor <;> linarith

end LBC

-- ===== LB/T41 =====

/-! # Theorem 4.1: impossibility of an `O(√C)` corruption guarantee beyond sharpness -/

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal Pointwise NNReal

namespace LB41

open LBC

/-- the curve point `a(s) = (1/2 + s, s^p)` -/
noncomputable def aP (p : ℕ) (s : ℝ) : Fin 2 → ℝ := ![1 / 2 + s, s ^ p]

/-- the action set `A_p` -/
def Ap (p : ℕ) : Set (Fin 2 → ℝ) :=
  {a | ∃ s ∈ Set.Icc (-(1 / 4) : ℝ) (1 / 4), a = ![1 / 2 + s, s ^ p]}

lemma aP_mem (p : ℕ) {s : ℝ} (hs : s ∈ Set.Icc (-(1 / 4) : ℝ) (1 / 4)) : aP p s ∈ Ap p :=
  ⟨s, hs, rfl⟩

lemma Ap_eq_image (p : ℕ) : Ap p = (aP p) '' Set.Icc (-(1 / 4) : ℝ) (1 / 4) := by
  ext a; constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩

lemma Ap_meas (p : ℕ) : MeasurableSet (Ap p) := by
  rw [Ap_eq_image]
  have hc : Continuous (aP p) := by
    unfold aP
    refine continuous_pi fun i => ?_
    fin_cases i
    · simp; fun_prop
    · simp; fun_prop
  exact ((isCompact_Icc.image hc).isClosed).measurableSet

lemma dot_aP (p : ℕ) (s x y : ℝ) : aP p s ⬝ᵥ ![x, y] = (1 / 2 + s) * x + s ^ p * y := by
  simp [aP, dotProduct, Fin.sum_univ_two]

lemma pow_small (p : ℕ) (hp : 4 ≤ p) {s : ℝ} (hs : s ∈ Set.Icc (-(1 / 4) : ℝ) (1 / 4)) :
    |s ^ p| ≤ 1 / 256 := by
  rw [abs_pow]
  have h1 : |s| ≤ 1 / 4 := abs_le.mpr ⟨hs.1, hs.2⟩
  calc |s| ^ p ≤ (1 / 4) ^ p := pow_le_pow_left₀ (abs_nonneg _) h1 p
    _ ≤ (1 / 4) ^ 4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
    _ = 1 / 256 := by norm_num

lemma even_pow_nonneg {p : ℕ} (hpe : Even p) (s : ℝ) : 0 ≤ s ^ p := hpe.pow_nonneg s

/-- the tangent inequality `p u^{p-1} |s| ≤ s^p + (p-1) u^p` (Bernoulli) -/
lemma tangent (p : ℕ) (hp : 1 ≤ p) (hpe : Even p) (u s : ℝ) (hu : 0 ≤ u) :
    (p : ℝ) * u ^ (p - 1) * |s| ≤ s ^ p + ((p : ℝ) - 1) * u ^ p := by
  have hsp : s ^ p = |s| ^ p := by rw [← hpe.pow_abs]
  rw [hsp]
  rcases eq_or_lt_of_le hu with h0 | hpos
  · subst h0
    have : (0 : ℝ) ^ (p - 1) = 0 ∨ p - 1 = 0 := by
      rcases Nat.eq_zero_or_pos (p - 1) with h | h
      · right; exact h
      · left; exact zero_pow (by omega)
    rcases this with h | h
    · rw [h, mul_zero, zero_mul, zero_pow (by omega : p ≠ 0), mul_zero, add_zero]; positivity
    · have hp1 : p = 1 := by omega
      exact absurd (hp1 ▸ hpe) (by decide)
  · set t := |s| with ht
    have ht0 : 0 ≤ t := abs_nonneg s
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ t / u - 1 by
      have : 0 ≤ t / u := div_nonneg ht0 hpos.le; linarith) p
    have e : 1 + (t / u - 1) = t / u := by ring
    rw [e, div_pow] at hb
    have hup : 0 < u ^ p := pow_pos hpos p
    have := mul_le_mul_of_nonneg_right hb hup.le
    rw [div_mul_cancel₀ _ hup.ne'] at this
    have hpow : u ^ p = u ^ (p - 1) * u := by
      rw [← pow_succ]; congr 1; omega
    have key : (1 + (p : ℝ) * (t / u - 1)) * u ^ p = (p : ℝ) * u ^ (p - 1) * t - ((p : ℝ) - 1) * u ^ p := by
      rw [hpow]; field_simp; ring
    linarith

/-! ### The environments -/

/-- the actual loss vector `(σε, 1)` -/
noncomputable def vσ (σ ε : ℝ) : ℕ → Fin 2 → ℝ := fun _ => ![σ * ε, 1]

lemma setNorm_le (𝒜 : Set (Fin 2 → ℝ)) (z : Fin 2 → ℝ) (B : ℝ) (hne : 𝒜.Nonempty)
    (h : ∀ a ∈ 𝒜, |a ⬝ᵥ z| ≤ B) : setNorm 𝒜 z ≤ B := by
  unfold setNorm
  exact csSup_le (hne.image _) (by rintro _ ⟨a, ha, rfl⟩; exact h a ha)

lemma Ap_nonempty (p : ℕ) : (Ap p).Nonempty := ⟨aP p 0, aP_mem p (by norm_num)⟩

lemma dot_v_bound (p : ℕ) (hp : 4 ≤ p) (σ ε : ℝ) (hσ : σ = 1 ∨ σ = -1) (hε : 0 ≤ ε)
    (hε8 : ε ≤ 1 / 8) (a : Fin 2 → ℝ) (ha : a ∈ Ap p) (t : ℕ) : |a ⬝ᵥ vσ σ ε t| ≤ 1 / 2 := by
  obtain ⟨s, hs, rfl⟩ := ha
  have := dot_aP p s (σ * ε) 1
  unfold aP at this
  show |![1 / 2 + s, s ^ p] ⬝ᵥ ![σ * ε, 1]| ≤ 1 / 2
  rw [this, mul_one]
  have h1 := pow_small p hp hs
  have hsig : |σ * ε| = ε := by rcases hσ with rfl | rfl <;> simp [abs_of_nonneg hε]
  have h2 : |(1 / 2 + s) * (σ * ε)| ≤ 3 / 4 * ε := by
    rw [abs_mul, hsig]
    have : |1 / 2 + s| ≤ 3 / 4 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    nlinarith [abs_nonneg (1 / 2 + s)]
  calc |(1 / 2 + s) * (σ * ε) + s ^ p| ≤ |(1 / 2 + s) * (σ * ε)| + |s ^ p| := abs_add_le _ _
    _ ≤ 1 / 2 := by linarith

lemma env_corrupted (p : ℕ) (hp : 4 ≤ p) (σ ε C : ℝ) (T : ℕ) (hσ : σ = 1 ∨ σ = -1) (hε : 0 ≤ ε)
    (hε8 : ε ≤ 1 / 8) (hC : (T : ℝ) * (3 / 4 * ε) ≤ C) :
    (mkEnv (vσ σ ε)).IsCorruptedStoch (Ap p) ![0, 1] C T := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply setNorm_le _ _ _ (Ap_nonempty p)
    rintro a ⟨s, hs, rfl⟩
    have := dot_aP p s 0 1; unfold aP at this; rw [this]
    simp only [mul_zero, zero_add, mul_one]
    exact (pow_small p hp hs).trans (by norm_num)
  · intro t _
    exact setNorm_le _ _ _ (Ap_nonempty p) fun a ha =>
      (dot_v_bound p hp σ ε hσ hε hε8 a ha t).trans (by norm_num)
  · intro t _ a ha
    exact mkEnv_feedback _ t a ((dot_v_bound p hp σ ε hσ hε hε8 a ha t).trans (by norm_num))
  · have hterm : ∀ t ∈ Finset.range T, setNorm (Ap p) ((mkEnv (vσ σ ε)).θs t - ![0, 1]) ≤
        3 / 4 * ε := by
      intro t _
      apply setNorm_le _ _ _ (Ap_nonempty p)
      rintro a ⟨s, hs, rfl⟩
      have e : ((mkEnv (vσ σ ε)).θs t - ![0, 1] : Fin 2 → ℝ) = ![σ * ε, 0] := by
        funext i; fin_cases i <;> simp [mkEnv, vσ]
      rw [e]
      have := dot_aP p s (σ * ε) 0; unfold aP at this; rw [this]
      simp only [mul_zero, add_zero]
      have hsig : |σ * ε| = ε := by rcases hσ with rfl | rfl <;> simp [abs_of_nonneg hε]
      rw [abs_mul, hsig]
      have : |1 / 2 + s| ≤ 3 / 4 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      nlinarith [abs_nonneg (1 / 2 + s)]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact hC

/-! ### The regret lower bound -/

/-- the event `s_t ≥ 0`, i.e. `(A_t)_1 ≥ 1/2` -/
def Ev (T : ℕ) (t : Fin T) : Set (LinearBanditHistory 2 T) := {h | (h t).1 ∈ {a | 1 / 2 ≤ a 0}}

lemma Ev_meas (T : ℕ) (t : Fin T) : MeasurableSet (Ev T t) :=
  (measurableSet_le measurable_const (measurable_pi_apply 0)).preimage (measurable_pi_apply t).fst

/-- the gap of a curve point against the comparator `a(-σu)` -/
lemma gap_eq (p : ℕ) (hp : 4 ≤ p) (hpe : Even p) (σ ε u s : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hεu : ε * u = (p : ℝ) * u ^ p) :
    (aP p s - aP p (-σ * u)) ⬝ᵥ ![σ * ε, 1] = s ^ p + σ * ε * s + ((p : ℝ) - 1) * u ^ p := by
  rw [sub_dotProduct, dot_aP, dot_aP]
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hpw : (-σ * u) ^ p = u ^ p := by
    rw [neg_mul, hpe.neg_pow, mul_pow]
    rcases hσ with rfl | rfl
    · simp
    · rw [hpe.neg_pow]; simp
  rw [hpw]
  have : (1 / 2 + s) * (σ * ε) + s ^ p * 1 - ((1 / 2 + -σ * u) * (σ * ε) + u ^ p * 1) =
      s ^ p + σ * ε * s + (σ * σ) * (ε * u) - u ^ p := by ring
  rw [this, hσ2, one_mul, hεu]; ring

lemma gap_nonneg (p : ℕ) (hp : 4 ≤ p) (hpe : Even p) (σ ε u s : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hu : 0 ≤ u) (hε : ε = (p : ℝ) * u ^ (p - 1)) :
    0 ≤ s ^ p + σ * ε * s + ((p : ℝ) - 1) * u ^ p := by
  have ht := tangent p (by omega) hpe u s hu
  have hσs : -(ε * |s|) ≤ σ * ε * s := by
    have hε0 : 0 ≤ ε := by rw [hε]; positivity
    rcases hσ with rfl | rfl
    · nlinarith [neg_abs_le s]
    · nlinarith [le_abs_self s]
  rw [hε] at hσs ⊢
  linarith

lemma gap_wrong (p : ℕ) (hpe : Even p) (σ ε u s : ℝ) (hε : 0 ≤ ε) (hs : 0 ≤ σ * s) :
    ((p : ℝ) - 1) * u ^ p ≤ s ^ p + σ * ε * s + ((p : ℝ) - 1) * u ^ p := by
  have h1 : 0 ≤ s ^ p := hpe.pow_nonneg s
  have h2 : 0 ≤ σ * ε * s := by nlinarith
  linarith

/-! ### Geometry of `A_p` -/

lemma a0_mem (p : ℕ) (hp : 1 ≤ p) : (![1 / 2, 0] : Fin 2 → ℝ) ∈ Ap p := by
  refine ⟨0, by norm_num, ?_⟩
  funext i; fin_cases i <;> simp [zero_pow (show p ≠ 0 by omega)]

lemma unique_opt (p : ℕ) (hp : 1 ≤ p) (hpe : Even p) :
    ∀ a ∈ Ap p, a ≠ ![1 / 2, 0] → (![1 / 2, 0] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] < a ⬝ᵥ ![0, 1] := by
  rintro a ⟨s, hs, rfl⟩ hne
  have hs0 : s ≠ 0 := by
    rintro rfl; apply hne; funext i; fin_cases i <;> simp [zero_pow (show p ≠ 0 by omega)]
  have : (![1 / 2 + s, s ^ p] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = s ^ p := by
    simp [dotProduct, Fin.sum_univ_two]
  rw [this]
  simp [dotProduct, Fin.sum_univ_two]
  exact hpe.pow_pos hs0

lemma Sset_bound (p : ℕ) (hp : 4 ≤ p) : ∀ x ∈ Sset (Ap p), |(![4 / 3, 0] : Fin 2 → ℝ) ⬝ᵥ x| ≤ 1 := by
  apply Sset_abs_le
  rintro a ⟨s, hs, rfl⟩
  have e : (![4 / 3, 0] : Fin 2 → ℝ) ⬝ᵥ ![1 / 2 + s, s ^ p] = 4 / 3 * (1 / 2 + s) := by
    simp [dotProduct, Fin.sum_univ_two]
  rw [e, abs_le]; constructor <;> nlinarith [hs.1, hs.2]

lemma diff_mem (p : ℕ) (hp : 1 ≤ p) {s : ℝ} (hs : s ∈ Set.Icc (-(1 / 4) : ℝ) (1 / 4)) :
    (![s, s ^ p] : Fin 2 → ℝ) ∈ (2 : ℝ) • Sset (Ap p) := by
  refine ⟨(1 / 2 : ℝ) • aP p s + (1 / 2 : ℝ) • (-![1 / 2, 0]), ?_, ?_⟩
  · exact Sset_convex _ (mem_Sset_of_mem _ (aP_mem p hs))
      (neg_mem_Sset_of_mem _ (a0_mem p hp)) (by norm_num) (by norm_num) (by norm_num)
  · funext i; fin_cases i <;> simp [aP] <;> ring

lemma not_sharp (p : ℕ) (hp : 4 ≤ p) (hpe : Even p) : ¬ IsSharp (Ap p) ![0, 1] ![1 / 2, 0] := by
  rintro ⟨ς, hς, h⟩
  set s : ℝ := min (1 / 4) ς with hs_def
  have hs0 : 0 < s := lt_min (by norm_num) hς
  have hs1 : s ≤ 1 / 4 := min_le_left _ _
  have hsς : s ≤ ς := min_le_right _ _
  have hsmem : s ∈ Set.Icc (-(1 / 4) : ℝ) (1 / 4) := ⟨by linarith, hs1⟩
  have ha := h (aP p s) (subset_convexHull ℝ _ (aP_mem p hsmem))
  have hv : aP p s - ![1 / 2, 0] = ![s, s ^ p] := by
    funext i; fin_cases i <;> simp [aP]
  rw [hv] at ha
  have hrhs : (![s, s ^ p] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = s ^ p := by
    simp [dotProduct, Fin.sum_univ_two]
  rw [hrhs] at ha
  have hg := le_gauge_of_bound (Sset (Ap p)) ![4 / 3, 0] ![s, s ^ p] 2 two_pos
    (diff_mem p (by omega) hsmem) (Sset_bound p hp)
  have hdot : (![4 / 3, 0] : Fin 2 → ℝ) ⬝ᵥ ![s, s ^ p] = 4 / 3 * s := by
    simp [dotProduct, Fin.sum_univ_two]
  rw [hdot, abs_of_pos (by positivity)] at hg
  have hsn : sNorm (Ap p) ![s, s ^ p] = gauge (Sset (Ap p)) ![s, s ^ p] := rfl
  rw [hsn] at ha
  have h1 : ς * (4 / 3 * s) ≤ s ^ p := (mul_le_mul_of_nonneg_left hg hς.le).trans ha
  have h2 : s ^ p ≤ s ^ 2 := pow_le_pow_of_le_one hs0.le (by linarith) (by omega)
  nlinarith

lemma no_alloc (p : ℕ) (hp : 4 ≤ p) (n : Measure (Fin 2 → ℝ)) :
    ¬ IsCtrAlloc (Ap p) ![0, 1] ![1 / 2, 0] n := by
  rintro ⟨_, _, hpd, hc⟩
  set M := designMat n with hM
  have hM0 := (posDef_props M hpd).1
  set s : ℝ := min (1 / 4) (1 / (M 0 0 + 1)) with hs_def
  have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1 / 4 := min_le_left _ _
  have hsM : s ≤ 1 / (M 0 0 + 1) := min_le_right _ _
  have hsmem : s ∈ Set.Icc (-(1 / 4) : ℝ) (1 / 4) := ⟨by linarith, hs1⟩
  have ha := hc (aP p s) (subset_convexHull ℝ _ (aP_mem p hsmem))
  have hv : aP p s - ![1 / 2, 0] = ![s, s ^ p] := by
    funext i; fin_cases i <;> simp [aP]
  rw [hv] at ha
  have hrhs : (![s, s ^ p] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = s ^ p := by
    simp [dotProduct, Fin.sum_univ_two]
  rw [hrhs] at ha
  have hcs := cs_fin_two_0 M hpd ![s, s ^ p]
  simp only [cons_val_zero] at hcs
  have h1 : s ^ 2 ≤ M 0 0 * ((s ^ p) ^ 2 / 2) :=
    hcs.trans (mul_le_mul_of_nonneg_left ha hM0.le)
  have h2 : (s ^ p) ^ 2 ≤ s ^ 4 := by
    rw [← pow_mul]; exact pow_le_pow_of_le_one hs0.le (by linarith) (by omega)
  have h3 : M 0 0 * s ≤ M 0 0 * (1 / (M 0 0 + 1)) := mul_le_mul_of_nonneg_left hsM hM0.le
  have h4 : M 0 0 * (1 / (M 0 0 + 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  have hs2 : 0 < s ^ 2 := by positivity
  have h5 : M 0 0 * ((s ^ p) ^ 2 / 2) ≤ M 0 0 * (s ^ 4 / 2) := by gcongr
  have h6 : M 0 0 * (s ^ 4 / 2) < s ^ 2 := by
    have : M 0 0 * s ^ 2 < 1 := by nlinarith
    nlinarith
  linarith

/-! ### The main lower bound -/

theorem lower_bound (p : ℕ) (hp : 4 ≤ p) (hpe : Even p) (C : ℝ) (hC : 0 ≤ C) (T : ℕ)
    (hT1 : 1 ≤ T) (hT : ((4 : ℝ) ^ (p - 1) / (8 * p)) ^ 2 ≤ T) :
    ∃ E : ℝ → LinEnv 2,
      (∀ σ : ℝ, (σ = 1 ∨ σ = -1) → (E σ).IsCorruptedStoch (Ap p) ![0, 1] C T) ∧
      ∀ π : LinearBanditPolicy 2, IsSupportedLinearPolicy (Ap p) π →
        ((p : ℝ) - 1) * T / (4 * (p : ℝ) ^ ((p : ℝ) / (p - 1))) *
            (min (4 * C / (3 * T)) (1 / (8 * Real.sqrt T))) ^ ((p : ℝ) / (p - 1)) ≤
          max ((E 1).regret (Ap p) π T) ((E (-1)).regret (Ap p) π T) := by
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hsqT : 1 ≤ Real.sqrt T := by rw [Real.one_le_sqrt]; exact hTr
  set ε : ℝ := min (4 * C / (3 * T)) (1 / (8 * Real.sqrt T)) with hε_def
  have hε0 : 0 ≤ ε := le_min (by positivity) (by positivity)
  have hε8 : ε ≤ 1 / 8 := (min_le_right _ _).trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hεC : (T : ℝ) * (3 / 4 * ε) ≤ C := by
    have h := min_le_left (4 * C / (3 * T)) (1 / (8 * Real.sqrt T))
    have : (T : ℝ) * (3 / 4 * (4 * C / (3 * T))) = C := by field_simp
    nlinarith
  have hεsq : (T : ℝ) * ε ^ 2 ≤ 1 / 64 := by
    have h := min_le_right (4 * C / (3 * T)) (1 / (8 * Real.sqrt T))
    have hsq : Real.sqrt T ^ 2 = T := Real.sq_sqrt (by linarith)
    have : ε ^ 2 ≤ (1 / (8 * Real.sqrt T)) ^ 2 := pow_le_pow_left₀ hε0 h 2
    rw [div_pow, mul_pow, hsq] at this
    calc (T : ℝ) * ε ^ 2 ≤ T * (1 ^ 2 / (8 ^ 2 * T)) := by gcongr
      _ = 1 / 64 := by field_simp; norm_num
  -- the exponent
  set q : ℕ := p - 1 with hq
  have hq0 : q ≠ 0 := by omega
  have hpr : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hqr : ((q : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [hq, Nat.cast_sub (by omega)]; simp
  set u : ℝ := (ε / p) ^ ((q : ℝ)⁻¹) with hu_def
  have hεp : 0 ≤ ε / p := div_nonneg hε0 hpr.le
  have hu0 : 0 ≤ u := Real.rpow_nonneg hεp _
  have huq : u ^ q = ε / p := Real.rpow_inv_natCast_pow hεp hq0
  have hεu1 : ε = (p : ℝ) * u ^ (p - 1) := by rw [← hq, huq]; field_simp
  have hpq : p = q + 1 := by omega
  have hεu : ε * u = (p : ℝ) * u ^ p := by
    rw [hεu1, mul_assoc, ← pow_succ, ← hq, ← hpq]
  -- `u ≤ 1/4`
  have hu4 : u ≤ 1 / 4 := by
    have h1 : (4 : ℝ) ^ q / (8 * p) ≤ Real.sqrt T := by
      apply Real.le_sqrt_of_sq_le; exact hT
    have h2 : ε / p ≤ (1 / 4) ^ q := by
      have h := min_le_right (4 * C / (3 * T)) (1 / (8 * Real.sqrt T))
      rw [div_le_iff₀ hpr]
      have h4q : (0 : ℝ) < 4 ^ q := by positivity
      calc ε ≤ 1 / (8 * Real.sqrt T) := h
        _ ≤ 1 / (8 * ((4 : ℝ) ^ q / (8 * p))) := by
            apply one_div_le_one_div_of_le (by positivity); linarith
        _ = (1 / 4) ^ q * p := by rw [div_pow, one_pow]; field_simp
    calc u ≤ ((1 / 4 : ℝ) ^ q) ^ ((q : ℝ)⁻¹) := Real.rpow_le_rpow hεp h2 (by positivity)
      _ = 1 / 4 := Real.pow_rpow_inv_natCast (by norm_num) hq0
  set g : ℝ := ((p : ℝ) - 1) * u ^ p with hg_def
  have hg0 : 0 ≤ g := by
    have : (0 : ℝ) ≤ (p : ℝ) - 1 := by rw [← hqr]; positivity
    positivity
  refine ⟨fun σ => mkEnv (vσ σ ε), fun σ hσ => env_corrupted p hp σ ε C T hσ hε0 hε8 hεC,
    fun π hπ => ?_⟩
  have hA := Ap_meas p
  -- comparators
  have hcmem : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → aP p (-σ * u) ∈ Ap p := by
    intro σ hσ
    apply aP_mem
    rcases hσ with rfl | rfl <;> constructor <;> linarith
  have hθb : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ t < T, ∀ a ∈ Ap p,
      |a ⬝ᵥ (mkEnv (vσ σ ε)).θs t| ≤ 1 :=
    fun σ hσ t _ a ha => (dot_v_bound p hp σ ε hσ hε0 hε8 a ha t).trans (by norm_num)
  have hgap : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ s : ℝ,
      (aP p s - aP p (-σ * u)) ⬝ᵥ (mkEnv (vσ σ ε)).θs 0 = s ^ p + σ * ε * s + g :=
    fun σ hσ s => gap_eq p hp hpe σ ε u s hσ hεu
  have hθt : ∀ σ t, (mkEnv (vσ σ ε)).θs t = (mkEnv (vσ σ ε)).θs 0 := fun _ _ => rfl
  -- regret of `+`
  have hplus : ∑ t : Fin T, g * ((mkEnv (vσ 1 ε)).histMeasure π T (Ev T t)).toReal ≤
      (mkEnv (vσ 1 ε)).regret (Ap p) π T := by
    let c : Fin T → LinearBanditHistory 2 T → ℝ := fun t h => g * (Ev T t).indicator 1 h
    have hcm : ∀ t, Measurable (c t) := fun t =>
      (measurable_one.indicator (Ev_meas T t)).const_mul _
    have hcb : ∀ t h, |c t h| ≤ g := by
      intro t h; simp only [c]; unfold Set.indicator; split_ifs <;> simp [abs_of_nonneg hg0, hg0]
    have key := regret_ge (mkEnv (vσ 1 ε)) π (Ap p) hA hπ T (aP p (-1 * u)) (hcmem 1 (Or.inl rfl))
      (hθb 1 (Or.inl rfl)) c hcm g hcb (by
        intro h hh
        apply Finset.sum_le_sum; intro t _
        obtain ⟨s, hs, hst⟩ := hh t
        have hst' : (h t).1 = aP p s := hst
        rw [hst', hθt, hgap 1 (Or.inl rfl) s]
        simp only [c]
        by_cases he : h ∈ Ev T t
        · rw [Set.indicator_of_mem he, Pi.one_apply, mul_one]
          have : 0 ≤ s := by
            have h0 : 1 / 2 ≤ (h t).1 0 := he
            rw [hst'] at h0; simp [aP] at h0; linarith
          exact gap_wrong p hpe 1 ε u s hε0 (by linarith)
        · rw [Set.indicator_of_notMem he, mul_zero]
          exact gap_nonneg p hp hpe 1 ε u s (Or.inl rfl) hu0 hεu1)
    refine le_trans (le_of_eq ?_) key
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [c]
    rw [integral_const_mul, integral_indicator_one (Ev_meas T t), measureReal_def]
  -- regret of `-`
  have hminus : ∑ t : Fin T, g * (1 - ((mkEnv (vσ (-1) ε)).histMeasure π T (Ev T t)).toReal) ≤
      (mkEnv (vσ (-1) ε)).regret (Ap p) π T := by
    let c : Fin T → LinearBanditHistory 2 T → ℝ := fun t h => g * (1 - (Ev T t).indicator 1 h)
    have hcm : ∀ t, Measurable (c t) := fun t =>
      (measurable_const.sub (measurable_one.indicator (Ev_meas T t))).const_mul _
    have hcb : ∀ t h, |c t h| ≤ g := by
      intro t h; simp only [c]; unfold Set.indicator; split_ifs <;> simp [abs_of_nonneg hg0, hg0]
    have key := regret_ge (mkEnv (vσ (-1) ε)) π (Ap p) hA hπ T (aP p (-(-1) * u))
      (hcmem (-1) (Or.inr rfl)) (hθb (-1) (Or.inr rfl)) c hcm g hcb (by
        intro h hh
        apply Finset.sum_le_sum; intro t _
        obtain ⟨s, hs, hst⟩ := hh t
        have hst' : (h t).1 = aP p s := hst
        rw [hst', hθt, hgap (-1) (Or.inr rfl) s]
        simp only [c]
        by_cases he : h ∈ Ev T t
        · rw [Set.indicator_of_mem he, Pi.one_apply, sub_self, mul_zero]
          exact gap_nonneg p hp hpe (-1) ε u s (Or.inr rfl) hu0 hεu1
        · rw [Set.indicator_of_notMem he, sub_zero, mul_one]
          have : s < 0 := by
            have h0 : ¬ (1 / 2 ≤ (h t).1 0) := he
            rw [hst'] at h0; simp [aP] at h0; linarith
          exact gap_wrong p hpe (-1) ε u s hε0 (by linarith))
    refine le_trans (le_of_eq ?_) key
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [c]
    have hi : Integrable ((Ev T t).indicator (1 : LinearBanditHistory 2 T → ℝ))
        ((mkEnv (vσ (-1) ε)).histMeasure π T) :=
      (integrable_const (1 : ℝ)).indicator (Ev_meas T t)
    rw [integral_const_mul, integral_sub (f := fun _ => (1 : ℝ)) (integrable_const _) hi,
      integral_const, integral_indicator_one (Ev_meas T t)]
    simp [measureReal_def]
  -- testing
  have htv : ∀ t : Fin T, ((mkEnv (vσ (-1) ε)).histMeasure π T (Ev T t)).toReal ≤
      ((mkEnv (vσ 1 ε)).histMeasure π T (Ev T t)).toReal + 1 / 2 := by
    intro t
    refine tv_event (vσ 1 ε) (vσ (-1) ε) (Ap p) π hπ T (9 / 4 * ε ^ 2) (by positivity)
      (fun t _ a ha => dot_v_bound p hp 1 ε (Or.inl rfl) hε0 hε8 a ha t)
      (fun t _ a ha => dot_v_bound p hp (-1) ε (Or.inr rfl) hε0 hε8 a ha t) ?_ (by nlinarith)
      (Ev T t) (Ev_meas T t)
    intro t _ a ha
    obtain ⟨s, hs, rfl⟩ := ha
    have e1 := dot_aP p s (1 * ε) 1
    have e2 := dot_aP p s (-1 * ε) 1
    unfold aP at e1 e2
    show (![1 / 2 + s, s ^ p] ⬝ᵥ ![-1 * ε, 1] - ![1 / 2 + s, s ^ p] ⬝ᵥ ![1 * ε, 1]) ^ 2 ≤ _
    rw [e1, e2]
    have : (1 / 2 + s) ^ 2 ≤ 9 / 16 := by nlinarith [hs.1, hs.2]
    nlinarith [sq_nonneg ε]
  have hsum : g * T / 2 ≤ (mkEnv (vσ 1 ε)).regret (Ap p) π T +
      (mkEnv (vσ (-1) ε)).regret (Ap p) π T := by
    refine le_trans ?_ (add_le_add hplus hminus)
    rw [← Finset.sum_add_distrib]
    have hcount : ∑ _t : Fin T, g / 2 = g * T / 2 := by simp; ring
    rw [← hcount]
    apply Finset.sum_le_sum
    intro t _
    have := htv t
    nlinarith
  have hmax := add_le_add (le_max_left ((mkEnv (vσ 1 ε)).regret (Ap p) π T)
    ((mkEnv (vσ (-1) ε)).regret (Ap p) π T))
    (le_max_right ((mkEnv (vσ 1 ε)).regret (Ap p) π T)
    ((mkEnv (vσ (-1) ε)).regret (Ap p) π T))
  -- the closed form
  have hclosed : ((p : ℝ) - 1) * T / (4 * (p : ℝ) ^ ((p : ℝ) / (p - 1))) *
      ε ^ ((p : ℝ) / (p - 1)) = g * T / 4 := by
    have hup : u ^ p = ε ^ ((p : ℝ) / (p - 1)) / (p : ℝ) ^ ((p : ℝ) / (p - 1)) := by
      rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hεp, Real.div_rpow hε0 hpr.le, hqr]
      congr 2 <;> field_simp
    rw [hg_def, hup]
    field_simp
  show ((p : ℝ) - 1) * T / (4 * (p : ℝ) ^ ((p : ℝ) / (p - 1))) * ε ^ ((p : ℝ) / (p - 1)) ≤ _
  rw [hclosed]
  linarith

end LB41

namespace IAFTRL

theorem theorem_4_1_proved (p : ℕ) (hp : 4 ≤ p) (hpe : Even p) :
    let Ap : Set (Fin 2 → ℝ) := {a | ∃ s ∈ Set.Icc (-(1 / 4) : ℝ) (1 / 4), a = ![1 / 2 + s, s ^ p]}
    let θ₀ : Fin 2 → ℝ := ![0, 1]
    let a₀ : Fin 2 → ℝ := ![1 / 2, 0]
    (a₀ ∈ Ap ∧ (∀ a ∈ Ap, a ≠ a₀ → a₀ ⬝ᵥ θ₀ < a ⬝ᵥ θ₀) ∧ ¬ IsSharp Ap θ₀ a₀ ∧
      ∀ n : Measure (Fin 2 → ℝ), ¬ IsCtrAlloc Ap θ₀ a₀ n) ∧
    ∀ C : ℝ, 0 ≤ C → ∀ T : ℕ, 1 ≤ T → ((4 : ℝ) ^ (p - 1) / (8 * p)) ^ 2 ≤ T →
      ∃ E : ℝ → LinEnv 2,
        (∀ σ : ℝ, (σ = 1 ∨ σ = -1) → (E σ).IsCorruptedStoch Ap θ₀ C T) ∧
        ∀ π : LinearBanditPolicy 2, IsSupportedLinearPolicy Ap π →
          ((p : ℝ) - 1) * T / (4 * (p : ℝ) ^ ((p : ℝ) / (p - 1))) *
              (min (4 * C / (3 * T)) (1 / (8 * Real.sqrt T))) ^ ((p : ℝ) / (p - 1)) ≤
            max ((E 1).regret Ap π T) ((E (-1)).regret Ap π T) := by
  intro Ap θ₀ a₀
  exact ⟨⟨LB41.a0_mem p (by omega), LB41.unique_opt p (by omega) hpe, LB41.not_sharp p hp hpe,
    LB41.no_alloc p hp⟩, fun C hC T hT1 hT => LB41.lower_bound p hp hpe C hC T hT1 hT⟩

end IAFTRL

theorem _root_.solution : type_of% @IAFTRL.theorem_4_1_proved := @IAFTRL.theorem_4_1_proved
