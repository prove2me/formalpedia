-- Prove2me | solution 1 for IAFTRL.theorem_3_2_i
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T05:20:09.251+00:00
-- url     : https://prove2.me/submissions/06db4693-be2e-4fd5-8b94-d70820dd8b36

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

lemma mem_smul_comb (S : Set (Fin 2 → ℝ)) (hS : Convex ℝ S) (p q : Fin 2 → ℝ) (hp : p ∈ S)
    (hq : q ∈ S) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (h : 0 < α + β) :
    α • p + β • q ∈ (α + β) • S := by
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

-- ===== LB/T32aG =====

/-! # Theorem 3.2(i): geometry of the curve (Appendix H.1) -/

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal Pointwise NNReal

namespace LB32a

open LBC

/-- the curve point `a(s) = (−1/2 + s/4, (s + s²)/4)` -/
noncomputable def aC (s : ℝ) : Fin 2 → ℝ := ![-1 / 2 + s / 4, (s + s ^ 2) / 4]

/-- the curve -/
def Curve : Set (Fin 2 → ℝ) := {a | ∃ s ∈ Set.Icc (0 : ℝ) 1, a = ![-1 / 2 + s / 4, (s + s ^ 2) / 4]}

lemma aC_mem {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : aC s ∈ Curve := ⟨s, hs, rfl⟩

lemma aC0 : aC 0 = ![-1 / 2, 0] := by funext i; fin_cases i <;> simp [aC]

lemma aC1 : aC 1 = ![-1 / 4, 1 / 2] := by funext i; fin_cases i <;> simp [aC] <;> norm_num

lemma a0_mem : (![-1 / 2, 0] : Fin 2 → ℝ) ∈ Curve := by rw [← aC0]; exact aC_mem (by norm_num)

lemma a1_mem : (![-1 / 4, 1 / 2] : Fin 2 → ℝ) ∈ Curve := by rw [← aC1]; exact aC_mem (by norm_num)

lemma Curve_eq_image : Curve = aC '' Set.Icc (0 : ℝ) 1 := by
  ext a; constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩

lemma Curve_meas : MeasurableSet Curve := by
  rw [Curve_eq_image]
  have hc : Continuous aC := by
    unfold aC
    refine continuous_pi fun i => ?_
    fin_cases i
    · simp; fun_prop
    · simp; fun_prop
  exact ((isCompact_Icc.image hc).isClosed).measurableSet

lemma Curve_nonempty : Curve.Nonempty := ⟨_, a0_mem⟩

lemma dot2 (a b x y : ℝ) : (![a, b] : Fin 2 → ℝ) ⬝ᵥ ![x, y] = a * x + b * y := by
  simp [dotProduct, Fin.sum_univ_two]

lemma dotv (a b : ℝ) (z : Fin 2 → ℝ) : (![a, b] : Fin 2 → ℝ) ⬝ᵥ z = a * z 0 + b * z 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- linear facts on the convex hull, relative to `a(0)` -/
lemma hull0 (u : Fin 2 → ℝ) (hu : u ∈ convexHull ℝ Curve) :
    0 ≤ u 0 + 1 / 2 ∧ 0 ≤ u 1 ∧ u 1 ≤ 2 * (u 0 + 1 / 2) := by
  have h1 := convexHull_le_of Curve ![-1, 0] (1 / 2) (by
    rintro a ⟨s, hs, rfl⟩; rw [dot2]; linarith [hs.1]) u hu
  have h2 := convexHull_le_of Curve ![0, -1] 0 (by
    rintro a ⟨s, hs, rfl⟩; rw [dot2]; nlinarith [hs.1, hs.2]) u hu
  have h3 := convexHull_le_of Curve ![-2, 1] 1 (by
    rintro a ⟨s, hs, rfl⟩; rw [dot2]; nlinarith [hs.1, hs.2]) u hu
  rw [dotv] at h1 h2 h3
  exact ⟨by linarith, by linarith, by linarith⟩

/-- linear facts on the convex hull, relative to `a(1)` -/
lemma hull1 (u : Fin 2 → ℝ) (hu : u ∈ convexHull ℝ Curve) :
    u 1 ≤ 1 / 2 ∧ 0 ≤ -u 1 - 2 * u 0 ∧ 9 * (u 1 - 1 / 2) ≤ 14 * (u 0 + 1 / 4) := by
  have h1 := convexHull_le_of Curve ![0, 1] (1 / 2) (by
    rintro a ⟨s, hs, rfl⟩; rw [dot2]; nlinarith [hs.1, hs.2]) u hu
  have h2 := convexHull_le_of Curve ![2, 1] 0 (by
    rintro a ⟨s, hs, rfl⟩; rw [dot2]; nlinarith [hs.1, hs.2]) u hu
  have h3 := convexHull_le_of Curve ![-14, 9] (9 / 2 + 14 / 4) (by
    rintro a ⟨s, hs, rfl⟩; rw [dot2]; nlinarith [hs.1, hs.2]) u hu
  rw [dotv] at h1 h2 h3
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ### The centered complexity `c*_ctr = 8/τ` -/

lemma curve_ae (n : Measure (Fin 2 → ℝ)) (h : n Curveᶜ = 0) : ∀ᵐ a ∂n, a ∈ Curve := by
  rw [ae_iff]; exact h

lemma cstar_lower (τ : ℝ) (hτ : 0 < τ) (n : Measure (Fin 2 → ℝ))
    (hn : IsCtrAlloc Curve ![τ, 0] ![-1 / 2, 0] n) : 8 / τ ≤ ctrCost ![τ, 0] ![-1 / 2, 0] n := by
  obtain ⟨hfin, hsupp, hpd, hc⟩ := hn
  set M := designMat n with hM
  have hu := hc _ (subset_convexHull ℝ _ a1_mem)
  have hv : (![-1 / 4, 1 / 2] : Fin 2 → ℝ) - ![-1 / 2, 0] = ![1 / 4, 1 / 2] := by
    funext i; fin_cases i <;> norm_num
  rw [hv, dot2] at hu
  have hcs := cs_fin_two_1 M hpd ![1 / 4, 1 / 2]
  simp only [cons_val_one, head_cons] at hcs
  have hM11 := (posDef_props M hpd).2.1
  have h1 : (1 / 2 : ℝ) ^ 2 ≤ M 1 1 * ((1 / 4 * τ + 1 / 2 * 0) ^ 2 / 2) :=
    hcs.trans (mul_le_mul_of_nonneg_left hu hM11.le)
  have h2 : 8 / τ ^ 2 ≤ M 1 1 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  -- the cost dominates `τ M₁₁`
  have hae := curve_ae n hsupp
  have hm1 : Continuous fun a : Fin 2 → ℝ => a 1 * a 1 :=
    (continuous_apply 1).mul (continuous_apply 1)
  have hm2 : Continuous fun a : Fin 2 → ℝ => (a - ![-1 / 2, 0]) ⬝ᵥ ![τ, 0] :=
    (continuous_id.sub continuous_const).dotProduct continuous_const
  have hcost : τ * M 1 1 ≤ ctrCost ![τ, 0] ![-1 / 2, 0] n := by
    rw [hM]; unfold designMat ctrCost; simp only [of_apply]
    rw [← integral_const_mul]
    apply integral_mono_ae
    · refine (Integrable.of_bound hm1.measurable.aestronglyMeasurable 1
        (hae.mono fun a ha => ?_)).const_mul τ
      obtain ⟨s, hs, rfl⟩ := ha
      have e : (![-1 / 2 + s / 4, (s + s ^ 2) / 4] : Fin 2 → ℝ) 1 = (s + s ^ 2) / 4 := rfl
      have h0 : 0 ≤ (s + s ^ 2) / 4 := by nlinarith [hs.1, hs.2]
      have h1 : (s + s ^ 2) / 4 ≤ 1 / 2 := by nlinarith [hs.1, hs.2]
      rw [Real.norm_eq_abs, e, abs_le]; constructor <;> nlinarith
    · refine Integrable.of_bound hm2.measurable.aestronglyMeasurable τ (hae.mono fun a ha => ?_)
      obtain ⟨s, hs, rfl⟩ := ha
      have e : (![-1 / 2 + s / 4, (s + s ^ 2) / 4] - ![-1 / 2, 0] : Fin 2 → ℝ) = ![s / 4, (s + s ^ 2) / 4] := by
        funext i; fin_cases i <;> simp
      rw [Real.norm_eq_abs, e, dot2, abs_le]; constructor <;> nlinarith [hs.1, hs.2, hτ]
    · filter_upwards [hae] with a ha
      obtain ⟨s, hs, rfl⟩ := ha
      have e : (![-1 / 2 + s / 4, (s + s ^ 2) / 4] - ![-1 / 2, 0] : Fin 2 → ℝ) = ![s / 4, (s + s ^ 2) / 4] := by
        funext i; fin_cases i <;> simp
      have e1 : (![-1 / 2 + s / 4, (s + s ^ 2) / 4] : Fin 2 → ℝ) 1 = (s + s ^ 2) / 4 := rfl
      rw [e, dot2, e1]
      have : s * (1 + s) ^ 2 ≤ 4 := by nlinarith [hs.1, hs.2]
      have h5 : ((s + s ^ 2) / 4) * ((s + s ^ 2) / 4) ≤ s / 4 := by
        nlinarith [mul_le_mul_of_nonneg_left this hs.1]
      nlinarith [mul_le_mul_of_nonneg_left h5 hτ.le]
  calc 8 / τ = τ * (8 / τ ^ 2) := by field_simp
    _ ≤ τ * M 1 1 := mul_le_mul_of_nonneg_left h2 hτ.le
    _ ≤ _ := hcost

/-- the allocation `k δ_{a(1)} + η δ_{a(0)}` with `k = 32(1+ε)/τ²`, `η = 32(1+ε)/(τ²ε)` -/
noncomputable def nUp (τ ε : ℝ) : Measure (Fin 2 → ℝ) :=
  twoPt (Real.toNNReal (32 * (1 + ε) / τ ^ 2)) (Real.toNNReal (32 * (1 + ε) / (τ ^ 2 * ε)))
    ![-1 / 4, 1 / 2] ![-1 / 2, 0]

lemma nUp_alloc (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    IsCtrAlloc Curve ![τ, 0] ![-1 / 2, 0] (nUp τ ε) ∧
      ctrCost ![τ, 0] ![-1 / 2, 0] (nUp τ ε) = (1 + ε) * (8 / τ) := by
  set k : ℝ := 32 * (1 + ε) / τ ^ 2 with hk
  set η : ℝ := 32 * (1 + ε) / (τ ^ 2 * ε) with hη
  have hk0 : 0 < k := by positivity
  have hη0 : 0 < η := by positivity
  have hkc : ((Real.toNNReal k : ℝ≥0) : ℝ) = k := Real.coe_toNNReal _ hk0.le
  have hηc : ((Real.toNNReal η : ℝ≥0) : ℝ) = η := Real.coe_toNNReal _ hη0.le
  have hM : ∀ i j, designMat (nUp τ ε) i j =
      k * ((![-1 / 4, 1 / 2] : Fin 2 → ℝ) i * (![-1 / 4, 1 / 2] : Fin 2 → ℝ) j) +
        η * ((![-1 / 2, 0] : Fin 2 → ℝ) i * (![-1 / 2, 0] : Fin 2 → ℝ) j) := by
    intro i j; unfold nUp; rw [designMat_twoPt, hkc, hηc]
  have h00 : designMat (nUp τ ε) 0 0 = k / 16 + η / 4 := by rw [hM]; simp; ring
  have h01 : designMat (nUp τ ε) 0 1 = -(k / 8) := by rw [hM]; simp; ring
  have h10 : designMat (nUp τ ε) 1 0 = -(k / 8) := by rw [hM]; simp; ring
  have h11 : designMat (nUp τ ε) 1 1 = k / 4 := by rw [hM]; simp; ring
  have hdet : (k / 16 + η / 4) * (k / 4) - (-(k / 8)) ^ 2 = k * η / 16 := by ring
  have hdetpos : 0 < k * η / 16 := by positivity
  have hpd : (designMat (nUp τ ε)).PosDef := by
    apply posDef_fin_two_of
    · rw [h10, h01]
    · rw [h00]; positivity
    · rw [h00, h01, h11, hdet]; exact hdetpos
  refine ⟨⟨by unfold nUp; infer_instance, ?_, hpd, ?_⟩, ?_⟩
  · unfold nUp; exact twoPt_compl _ _ _ _ _ a1_mem a0_mem
  · intro u hu
    rw [quad_inv_fin_two _ (by rw [h10, h01]) (by rw [h00, h01, h11, hdet]; exact hdetpos.ne'),
      h00, h01, h11, hdet]
    obtain ⟨hv0, hv1, hv2⟩ := hull0 u hu
    have e0 : (u - ![-1 / 2, 0] : Fin 2 → ℝ) 0 = u 0 + 1 / 2 := by simp; ring
    have e1 : (u - ![-1 / 2, 0] : Fin 2 → ℝ) 1 = u 1 := by simp
    have eΔ : (u - ![-1 / 2, 0]) ⬝ᵥ ![τ, 0] = τ * (u 0 + 1 / 2) := by
      rw [dotProduct_comm, dotv, e0, e1]; ring
    rw [e0, e1, eΔ]
    set v0 := u 0 + 1 / 2
    set v1 := u 1
    have key : (k / 4 * v0 ^ 2 - 2 * -(k / 8) * v0 * v1 + (k / 16 + η / 4) * v1 ^ 2) / (k * η / 16) =
        (2 * v0 + v1) ^ 2 / η + 4 * v1 ^ 2 / k := by
      field_simp; ring
    rw [key]
    have hA : (2 * v0 + v1) ^ 2 ≤ 16 * v0 ^ 2 := by nlinarith
    have hB : v1 ^ 2 ≤ 4 * v0 ^ 2 := by nlinarith
    have hsum : 16 / η + 16 / k = τ ^ 2 / 2 := by
      rw [hη, hk]; field_simp; ring
    have hA' : (2 * v0 + v1) ^ 2 / η ≤ 16 * v0 ^ 2 / η := div_le_div_of_nonneg_right hA hη0.le
    have hB' : 4 * v1 ^ 2 / k ≤ 16 * v0 ^ 2 / k := div_le_div_of_nonneg_right (by nlinarith) hk0.le
    calc (2 * v0 + v1) ^ 2 / η + 4 * v1 ^ 2 / k ≤ 16 * v0 ^ 2 / η + 16 * v0 ^ 2 / k := by
          linarith
      _ = (16 / η + 16 / k) * v0 ^ 2 := by ring
      _ = (τ * v0) ^ 2 / 2 := by rw [hsum]; ring
  · unfold nUp
    rw [ctrCost_twoPt, hkc, hηc, sub_self, zero_dotProduct, mul_zero, add_zero]
    have e : (![-1 / 4, 1 / 2] - ![-1 / 2, 0] : Fin 2 → ℝ) = ![1 / 4, 1 / 2] := by
      funext i; fin_cases i <;> norm_num
    rw [e, dot2, hk]; field_simp; ring

lemma cstar_eq (τ : ℝ) (hτ : 0 < τ) : cstarCtr Curve ![τ, 0] ![-1 / 2, 0] = 8 / τ := by
  have hbdd : BddBelow (ctrCost ![τ, 0] ![-1 / 2, 0] '' {n | IsCtrAlloc Curve ![τ, 0] ![-1 / 2, 0] n}) :=
    ⟨8 / τ, by rintro _ ⟨n, hn, rfl⟩; exact cstar_lower τ hτ n hn⟩
  unfold cstarCtr
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨hn, hc⟩ := nUp_alloc τ (δ * τ / 8) hτ (by positivity)
    refine (csInf_le hbdd ⟨_, hn, rfl⟩).trans (le_of_eq ?_)
    rw [hc]; field_simp
  · obtain ⟨hn, _⟩ := nUp_alloc τ 1 hτ one_pos
    exact le_csInf ⟨_, ⟨_, hn, rfl⟩⟩ (by rintro _ ⟨n, hn', rfl⟩; exact cstar_lower τ hτ n hn')

/-! ### Sharpness of the two instances -/

lemma setNorm_le (𝒜 : Set (Fin 2 → ℝ)) (z : Fin 2 → ℝ) (B : ℝ) (hne : 𝒜.Nonempty)
    (h : ∀ a ∈ 𝒜, |a ⬝ᵥ z| ≤ B) : setNorm 𝒜 z ≤ B := by
  unfold setNorm
  exact csSup_le (hne.image _) (by rintro _ ⟨a, ha, rfl⟩; exact h a ha)

lemma theta_sharp (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) : (![τ, 0] : Fin 2 → ℝ) ∈ sharpInstances Curve := by
  refine ⟨?_, ![-1 / 2, 0], a0_mem, ?_, ?_⟩
  · apply setNorm_le _ _ _ Curve_nonempty
    rintro a ⟨s, hs, rfl⟩
    rw [dot2, abs_le]; constructor <;> nlinarith [hs.1, hs.2]
  · rintro a ⟨s, hs, rfl⟩ hne
    have hs0 : s ≠ 0 := by
      rintro rfl; apply hne; funext i; fin_cases i <;> simp
    have hs0' : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    rw [dot2, dot2]; nlinarith
  · refine ⟨τ / 8, by positivity, fun z hz => ?_⟩
    obtain ⟨hv0, hv1, hv2⟩ := hull0 z hz
    have hp : -(![-1 / 2, 0] : Fin 2 → ℝ) ∈ Sset Curve := neg_mem_Sset_of_mem _ a0_mem
    have hq : (![-1 / 4, 1 / 2] : Fin 2 → ℝ) ∈ Sset Curve := mem_Sset_of_mem _ a1_mem
    have hdec : z - ![-1 / 2, 0] = (2 * (z 0 + 1 / 2) + z 1) • (-(![-1 / 2, 0] : Fin 2 → ℝ)) +
        (2 * z 1) • (![-1 / 4, 1 / 2] : Fin 2 → ℝ) := by
      funext i; fin_cases i <;> simp <;> ring
    have hg : sNorm Curve (z - ![-1 / 2, 0]) ≤ (2 * (z 0 + 1 / 2) + z 1) + 2 * z 1 := by
      rw [hdec]
      exact gauge_le_comb _ (Sset_convex _) _ _ hp hq _ _ (by linarith) (by linarith)
    have hΔ : (z - ![-1 / 2, 0]) ⬝ᵥ ![τ, 0] = τ * (z 0 + 1 / 2) := by
      simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply, cons_val_zero, cons_val_one, head_cons]
      ring
    rw [hΔ]
    calc τ / 8 * sNorm Curve (z - ![-1 / 2, 0]) ≤ τ / 8 * ((2 * (z 0 + 1 / 2) + z 1) + 2 * z 1) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ ≤ τ * (z 0 + 1 / 2) := by nlinarith

lemma lambda_sharp (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    (![τ, -τ] : Fin 2 → ℝ) ∈ sharpInstances Curve := by
  refine ⟨?_, ![-1 / 4, 1 / 2], a1_mem, ?_, ?_⟩
  · apply setNorm_le _ _ _ Curve_nonempty
    rintro a ⟨s, hs, rfl⟩
    rw [dot2, abs_le]; constructor <;> nlinarith [hs.1, hs.2]
  · rintro a ⟨s, hs, rfl⟩ hne
    have hs1 : s ≠ 1 := by
      rintro rfl; apply hne; funext i; fin_cases i <;> simp <;> norm_num
    have hs1' : s < 1 := lt_of_le_of_ne hs.2 hs1
    have hsq : s ^ 2 < 1 := by nlinarith [hs.1]
    rw [dot2, dot2]; nlinarith [mul_lt_mul_of_pos_left hsq hτ]
  · refine ⟨τ / 12, by positivity, fun z hz => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hull1 z hz
    have hp : -(![-1 / 4, 1 / 2] : Fin 2 → ℝ) ∈ Sset Curve := neg_mem_Sset_of_mem _ a1_mem
    have hq : (![-1 / 2, 0] : Fin 2 → ℝ) ∈ Sset Curve := mem_Sset_of_mem _ a0_mem
    have hdec : z - ![-1 / 4, 1 / 2] = (-2 * (z 1 - 1 / 2)) • (-(![-1 / 4, 1 / 2] : Fin 2 → ℝ)) +
        (-z 1 - 2 * z 0) • (![-1 / 2, 0] : Fin 2 → ℝ) := by
      funext i; fin_cases i <;> simp <;> ring
    have hg : sNorm Curve (z - ![-1 / 4, 1 / 2]) ≤ (-2 * (z 1 - 1 / 2)) + (-z 1 - 2 * z 0) := by
      rw [hdec]
      exact gauge_le_comb _ (Sset_convex _) _ _ hp hq _ _ (by linarith) h2
    have hΔ : (z - ![-1 / 4, 1 / 2]) ⬝ᵥ ![τ, -τ] = τ * ((z 0 + 1 / 4) - (z 1 - 1 / 2)) := by
      simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply, cons_val_zero, cons_val_one, head_cons]
      ring
    rw [hΔ]
    calc τ / 12 * sNorm Curve (z - ![-1 / 4, 1 / 2]) ≤
          τ / 12 * ((-2 * (z 1 - 1 / 2)) + (-z 1 - 2 * z 0)) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ ≤ τ * ((z 0 + 1 / 4) - (z 1 - 1 / 2)) := by nlinarith

end LB32a

-- ===== LB/T32aP =====

/-! # Theorem 3.2(i): change of measure between the two sign models (Proposition H.1) -/

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal Pointwise NNReal

namespace LBC

variable {d : ℕ}

/-- the round-`t` marginal: integrating a function of round `t` -/
lemma lintegral_round (E : LinEnv d) (π : LinearBanditPolicy d) (T t : ℕ) (ht : t < T)
    (F : (Fin d → ℝ) × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F (h ⟨t, ht⟩) ∂(E.histMeasure π T) =
      ∫⁻ h, ∫⁻ a, ∫⁻ y, F (a, y) ∂(E.fb t a) ∂(π.select t h) ∂(E.histMeasure π t) := by
  obtain ⟨k, rfl⟩ : ∃ k, T = (t + 1) + k := ⟨T - (t + 1), by omega⟩
  have hmeas : Measurable fun h : LinearBanditHistory d (t + 1) => F (h (Fin.last t)) :=
    hF.comp (measurable_pi_apply _)
  calc ∫⁻ h, F (h ⟨t, ht⟩) ∂(E.histMeasure π (t + 1 + k))
      = ∫⁻ h, (fun h' : LinearBanditHistory d (t + 1) => F (h' (Fin.last t)))
          (restr (Nat.le_add_right (t + 1) k) h) ∂(E.histMeasure π (t + 1 + k)) := rfl
    _ = ∫⁻ h', F (h' (Fin.last t))
          ∂((E.histMeasure π (t + 1 + k)).map (restr (Nat.le_add_right (t + 1) k))) :=
        (lintegral_map hmeas (restr_meas _)).symm
    _ = ∫⁻ h', F (h' (Fin.last t)) ∂(E.histMeasure π (t + 1)) := by
        rw [hist_marginal E π (t + 1) k]
    _ = _ := by
        rw [lintegral_hist_succ E π t hmeas]
        simp only [snocH, Fin.snoc_last]

end LBC

namespace LB32a

open LBC

/-- the per-round likelihood ratio `dQ_λ/dQ_θ` at `y` (the values at `y = ±1` matter) -/
noncomputable def rr (τ : ℝ) (a : Fin 2 → ℝ) (y : ℝ) : ℝ :=
  if y = 1 then (1 + a ⬝ᵥ ![τ, -τ]) / (1 + a ⬝ᵥ ![τ, 0])
  else (1 - a ⬝ᵥ ![τ, -τ]) / (1 - a ⬝ᵥ ![τ, 0])

lemma rr_meas (τ : ℝ) : Measurable (Function.uncurry (rr τ)) := by
  unfold rr Function.uncurry
  have hc1 : Continuous fun p : (Fin 2 → ℝ) × ℝ => p.1 ⬝ᵥ ![τ, -τ] :=
    continuous_fst.dotProduct continuous_const
  have hc2 : Continuous fun p : (Fin 2 → ℝ) × ℝ => p.1 ⬝ᵥ ![τ, 0] :=
    continuous_fst.dotProduct continuous_const
  refine Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) ?_ ?_
  · exact ((continuous_const.add hc1).measurable).div ((continuous_const.add hc2).measurable)
  · exact ((continuous_const.sub hc1).measurable).div ((continuous_const.sub hc2).measurable)

/-- the means on the curve -/
lemma means (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (a : Fin 2 → ℝ) (ha : a ∈ Curve) :
    -(1 / 2) ≤ a ⬝ᵥ ![τ, 0] ∧ a ⬝ᵥ ![τ, 0] ≤ 0 ∧ -(3 / 4) ≤ a ⬝ᵥ ![τ, -τ] ∧ a ⬝ᵥ ![τ, -τ] ≤ 0 := by
  obtain ⟨s, hs, rfl⟩ := ha
  rw [dot2, dot2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hs.1, hs.2]

lemma rr_bounds (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (a : Fin 2 → ℝ) (ha : a ∈ Curve) (y : ℝ) :
    1 / 7 ≤ rr τ a y ∧ rr τ a y ≤ 7 := by
  obtain ⟨h1, h2, h3, h4⟩ := means τ hτ hτ1 a ha
  unfold rr
  split_ifs
  · constructor
    · rw [le_div_iff₀ (by linarith)]; linarith
    · rw [div_le_iff₀ (by linarith)]; linarith
  · constructor
    · rw [le_div_iff₀ (by linarith)]; linarith
    · rw [div_le_iff₀ (by linarith)]; linarith

lemma rr_change (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (a : Fin 2 → ℝ) (ha : a ∈ Curve)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ y, g y ∂((signEnv ![τ, -τ]).fb 0 a) =
      ∫⁻ y, g y * ENNReal.ofReal (rr τ a y) ∂((signEnv ![τ, 0]).fb 0 a) := by
  obtain ⟨h1, h2, h3, h4⟩ := means τ hτ hτ1 a ha
  show ∫⁻ y, g y ∂(signObs (a ⬝ᵥ ![τ, -τ])) = ∫⁻ y, g y * ENNReal.ofReal (rr τ a y) ∂(signObs (a ⬝ᵥ ![τ, 0]))
  rw [lintegral_signObs, lintegral_signObs, clampOne_of (abs_le.mpr ⟨by linarith, by linarith⟩),
    clampOne_of (abs_le.mpr ⟨by linarith, by linarith⟩)]
  unfold rr
  rw [if_pos rfl, if_neg (by norm_num)]
  set μp := a ⬝ᵥ ![τ, 0]
  set μm := a ⬝ᵥ ![τ, -τ]
  have e1 : ENNReal.ofReal ((1 + μp) / 2) * (g 1 * ENNReal.ofReal ((1 + μm) / (1 + μp))) =
      ENNReal.ofReal ((1 + μm) / 2) * g 1 := by
    rw [mul_comm (g 1), ← mul_assoc, ← ENNReal.ofReal_mul (by linarith)]
    congr 2
    have : (1 + μp) ≠ 0 := by intro h; linarith
    field_simp
  have e2 : ENNReal.ofReal ((1 - μp) / 2) * (g (-1) * ENNReal.ofReal ((1 - μm) / (1 - μp))) =
      ENNReal.ofReal ((1 - μm) / 2) * g (-1) := by
    rw [mul_comm (g (-1)), ← mul_assoc, ← ENNReal.ofReal_mul (by linarith)]
    congr 2
    have : (1 - μp) ≠ 0 := by intro h; linarith
    field_simp
  rw [e1, e2]

/-- the `χ²`-type identity `E_θ[1/r] = 1 + (μθ − μλ)²/(1 − μλ²)` -/
lemma inv_rr_mean (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (a : Fin 2 → ℝ) (ha : a ∈ Curve) :
    ∫⁻ y, ENNReal.ofReal (1 / rr τ a y) ∂((signEnv ![τ, 0]).fb 0 a) =
      ENNReal.ofReal (1 + (a ⬝ᵥ ![τ, 0] - a ⬝ᵥ ![τ, -τ]) ^ 2 / (1 - (a ⬝ᵥ ![τ, -τ]) ^ 2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := means τ hτ hτ1 a ha
  show ∫⁻ y, ENNReal.ofReal (1 / rr τ a y) ∂(signObs (a ⬝ᵥ ![τ, 0])) = _
  rw [lintegral_signObs, clampOne_of (abs_le.mpr ⟨by linarith, by linarith⟩)]
  unfold rr
  rw [if_pos rfl, if_neg (by norm_num)]
  set μp := a ⬝ᵥ ![τ, 0]
  set μm := a ⬝ᵥ ![τ, -τ]
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_add (by apply mul_nonneg <;> [linarith; (apply div_nonneg <;> [norm_num; apply div_nonneg <;> linarith])])
      (by apply mul_nonneg <;> [linarith; (apply div_nonneg <;> [norm_num; apply div_nonneg <;> linarith])])]
  congr 1
  have hp1 : (1 + μp) ≠ 0 := by intro h; linarith
  have hp2 : (1 - μp) ≠ 0 := by intro h; linarith
  have hm1 : (1 + μm) ≠ 0 := by intro h; linarith
  have hm2 : (1 - μm) ≠ 0 := by intro h; linarith
  have hm3 : (1 - μm ^ 2) ≠ 0 := by nlinarith
  field_simp
  ring

/-! ### The log-likelihood ratio -/

/-- the per-round likelihood ratio as a function on rounds -/
noncomputable def rho' (τ : ℝ) (_t : ℕ) (a : Fin 2 → ℝ) (y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (rr τ a y)

lemma rho'_meas (τ : ℝ) (t : ℕ) : Measurable (Function.uncurry (rho' τ t)) :=
  ENNReal.measurable_ofReal.comp (rr_meas τ)

/-- the log-likelihood ratio of the first `T` rounds -/
noncomputable def ell (τ : ℝ) (T : ℕ) (h : LinearBanditHistory 2 T) : ℝ :=
  ∑ t : Fin T, Real.log (rr τ (h t).1 (h t).2)

lemma ell_meas (τ : ℝ) (T : ℕ) : Measurable (ell τ T) := by
  unfold ell
  refine Finset.measurable_sum _ fun t _ => ?_
  exact Real.measurable_log.comp ((rr_meas τ).comp (measurable_pi_apply t))

lemma ell_bound (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (T : ℕ) (h : LinearBanditHistory 2 T)
    (hh : ∀ t, (h t).1 ∈ Curve) : |ell τ T h| ≤ T * Real.log 7 := by
  unfold ell
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ t : Fin T, |Real.log (rr τ (h t).1 (h t).2)| ≤ Real.log 7 := by
    intro t
    obtain ⟨b1, b2⟩ := rr_bounds τ hτ hτ1 _ (hh t) (h t).2
    have hpos : 0 < rr τ (h t).1 (h t).2 := by linarith
    rw [abs_le]; constructor
    · have := Real.log_le_log (by norm_num) b1
      rw [one_div, Real.log_inv] at this; linarith
    · exact Real.log_le_log hpos b2
  calc ∑ t : Fin T, |Real.log (rr τ (h t).1 (h t).2)| ≤ ∑ _t : Fin T, Real.log 7 :=
        Finset.sum_le_sum fun t _ => this t
    _ = T * Real.log 7 := by simp

lemma LR_eq (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (T : ℕ) (h : LinearBanditHistory 2 T)
    (hh : ∀ t, (h t).1 ∈ Curve) : LR (rho' τ) T h = ENNReal.ofReal (Real.exp (ell τ T h)) := by
  unfold LR rho' ell
  have hpos : ∀ t : Fin T, 0 < rr τ (h t).1 (h t).2 := fun t => by
    obtain ⟨b1, _⟩ := rr_bounds τ hτ hτ1 _ (hh t) (h t).2; linarith
  rw [← ENNReal.ofReal_prod_of_nonneg (fun t _ => (hpos t).le), Real.exp_sum]
  congr 1
  exact Finset.prod_congr rfl fun t _ => (Real.exp_log (hpos t)).symm

/-- the history laws -/
noncomputable abbrev Pth (τ : ℝ) (π : LinearBanditPolicy 2) (T : ℕ) :=
  (signEnv (![τ, 0] : Fin 2 → ℝ)).histMeasure π T

noncomputable abbrev Pla (τ : ℝ) (π : LinearBanditPolicy 2) (T : ℕ) :=
  (signEnv (![τ, -τ] : Fin 2 → ℝ)).histMeasure π T

lemma hist_ae (τ : ℝ) (π : LinearBanditPolicy 2) (hπ : IsSupportedLinearPolicy Curve π) (T : ℕ)
    (θ : Fin 2 → ℝ) : ∀ᵐ h ∂((signEnv θ).histMeasure π T), ∀ t, (h t).1 ∈ Curve :=
  hist_ae_supported _ π Curve Curve_meas hπ T

lemma ell_int (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy Curve π) (T : ℕ) : Integrable (ell τ T) (Pth τ π T) :=
  Integrable.of_bound (ell_meas τ T).aestronglyMeasurable _
    ((hist_ae τ π hπ T _).mono fun h hh => by
      rw [Real.norm_eq_abs]; exact ell_bound τ hτ hτ1 T h hh)

lemma expell_int (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy Curve π) (T : ℕ) :
    Integrable (fun h => Real.exp (ell τ T h)) (Pth τ π T) :=
  Integrable.of_bound ((Real.measurable_exp.comp (ell_meas τ T)).aestronglyMeasurable)
    (Real.exp (T * Real.log 7))
    ((hist_ae τ π hπ T _).mono fun h hh => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (ell_bound τ hτ hτ1 T h hh)))

/-- the change of measure in real form: `Q(S) = E_θ[1_S e^ℓ]` -/
lemma Q_eq (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy Curve π) (T : ℕ) (S : Set (LinearBanditHistory 2 T))
    (hS : MeasurableSet S) :
    (Pla τ π T S).toReal = ∫ h, S.indicator (fun h => Real.exp (ell τ T h)) h ∂(Pth τ π T) := by
  have hcm := change_of_measure_supp (signEnv (![τ, 0] : Fin 2 → ℝ)) (signEnv ![τ, -τ]) π Curve hπ T
    (rho' τ) (rho'_meas τ) (fun t _ a ha g _ => rr_change τ hτ hτ1 a ha g) T le_rfl
  have hind : Measurable (S.indicator (1 : LinearBanditHistory 2 T → ℝ≥0∞)) :=
    measurable_one.indicator hS
  have h1 : Pla τ π T S = ∫⁻ h, S.indicator 1 h * LR (rho' τ) T h ∂(Pth τ π T) := by
    rw [← lintegral_indicator_one hS]; exact hcm _ hind
  have h2 : ∫⁻ h, S.indicator 1 h * LR (rho' τ) T h ∂(Pth τ π T) =
      ∫⁻ h, ENNReal.ofReal (S.indicator (fun h => Real.exp (ell τ T h)) h) ∂(Pth τ π T) := by
    refine lintegral_congr_ae ((hist_ae τ π hπ T _).mono fun h hh => ?_)
    show S.indicator 1 h * LR (rho' τ) T h = ENNReal.ofReal (S.indicator (fun h => Real.exp (ell τ T h)) h)
    rw [LR_eq τ hτ hτ1 T h hh]
    by_cases hS' : h ∈ S
    · simp [Set.indicator_of_mem hS']
    · simp [Set.indicator_of_notMem hS']
  rw [h1, h2, ← ofReal_integral_eq_lintegral_ofReal ((expell_int τ hτ hτ1 π hπ T).indicator hS)
    (Filter.Eventually.of_forall fun h => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) h)]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun h =>
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) h)]

/-- **Change of measure with the tangent bound**: `E_θ[1_S ℓ] ≤ w log(Q(S)/w)` -/
lemma key_set (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy Curve π) (T : ℕ) (S : Set (LinearBanditHistory 2 T))
    (hS : MeasurableSet S) (hw : 0 < (Pth τ π T S).toReal) :
    0 < (Pla τ π T S).toReal ∧ ∫ h, S.indicator (ell τ T) h ∂(Pth τ π T) ≤
      (Pth τ π T S).toReal * Real.log ((Pla τ π T S).toReal / (Pth τ π T S).toReal) := by
  set w := (Pth τ π T S).toReal with hw_def
  set I := ∫ h, S.indicator (ell τ T) h ∂(Pth τ π T) with hI
  set c := I / w with hc
  have hint := ell_int τ hτ hτ1 π hπ T
  have hQ := Q_eq τ hτ hτ1 π hπ T S hS
  -- the tangent bound, integrated
  have hpt : ∀ h, S.indicator (fun h => Real.exp c * (1 - c) + Real.exp c * ell τ T h) h ≤
      S.indicator (fun h => Real.exp (ell τ T h)) h := by
    intro h
    by_cases hh : h ∈ S
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem hh]
      have := Real.add_one_le_exp (ell τ T h - c)
      have e : Real.exp (ell τ T h) = Real.exp c * Real.exp (ell τ T h - c) := by
        rw [← Real.exp_add]; ring_nf
      rw [e]
      nlinarith [Real.exp_pos c]
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hh]
  have hlow : Real.exp c * (1 - c) * w + Real.exp c * I ≤ (Pla τ π T S).toReal := by
    rw [hQ]
    have e : (fun h => S.indicator (fun h => Real.exp c * (1 - c) + Real.exp c * ell τ T h) h) =
        fun h => S.indicator (fun _ => Real.exp c * (1 - c)) h +
          Real.exp c * S.indicator (ell τ T) h := by
      funext h
      by_cases hh : h ∈ S
      · simp [Set.indicator_of_mem hh]
      · simp [Set.indicator_of_notMem hh]
    have h1 : ∫ h, S.indicator (fun h => Real.exp c * (1 - c) + Real.exp c * ell τ T h) h
        ∂(Pth τ π T) = Real.exp c * (1 - c) * w + Real.exp c * I := by
      rw [e, integral_add ((integrable_const _).indicator hS) ((hint.indicator hS).const_mul _),
        integral_indicator_const _ hS, integral_const_mul, smul_eq_mul, measureReal_def]
      ring
    rw [← h1]
    exact integral_mono ((((integrable_const _).add (hint.const_mul _))).indicator hS)
      ((expell_int τ hτ hτ1 π hπ T).indicator hS) hpt
  have hval : Real.exp c * (1 - c) * w + Real.exp c * I = Real.exp c * w := by
    rw [hc]; field_simp; ring
  rw [hval] at hlow
  have hq : 0 < (Pla τ π T S).toReal := lt_of_lt_of_le (by positivity) hlow
  have hlog : c ≤ Real.log ((Pla τ π T S).toReal / w) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hw]
    linarith
  refine ⟨hq, ?_⟩
  calc I = w * c := by rw [hc]; field_simp
    _ ≤ w * Real.log ((Pla τ π T S).toReal / w) := mul_le_mul_of_nonneg_left hlog hw.le

end LB32a

-- ===== LB/T32aQ =====

/-! # Theorem 3.2(i): the information inequality and the regret bounds -/

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal Pointwise NNReal

namespace LB32a

open LBC

lemma xlogx_ge (x : ℝ) (hx : 0 < x) : -1 ≤ x * Real.log x := by
  have := Real.one_sub_inv_le_log_of_pos hx
  have h2 : x * (1 - x⁻¹) ≤ x * Real.log x := mul_le_mul_of_nonneg_left this hx.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hx.ne'] at h2
  linarith

/-- the binary information inequality: `p log(1/q) − 2 ≤ D` -/
lemma D_lower (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy Curve π) (T : ℕ) (S : Set (LinearBanditHistory 2 T))
    (hS : MeasurableSet S) (hp : 0 < (Pth τ π T S).toReal) :
    (Pth τ π T S).toReal * Real.log (1 / (Pla τ π T S).toReal) - 2 ≤
      -∫ h, ell τ T h ∂(Pth τ π T) := by
  have hint := ell_int τ hτ hτ1 π hπ T
  have hsplit : ∫ h, ell τ T h ∂(Pth τ π T) =
      ∫ h, S.indicator (ell τ T) h ∂(Pth τ π T) + ∫ h, Sᶜ.indicator (ell τ T) h ∂(Pth τ π T) := by
    rw [integral_indicator hS, integral_indicator hS.compl, integral_add_compl hS hint]
  obtain ⟨hq, h1⟩ := key_set τ hτ hτ1 π hπ T S hS hp
  set p := (Pth τ π T S).toReal
  set q := (Pla τ π T S).toReal
  have hp1 : p ≤ 1 := by
    simp only [p]; rw [← measureReal_def]; exact measureReal_le_one
  have hq1 : q ≤ 1 := by
    simp only [q]; rw [← measureReal_def]; exact measureReal_le_one
  -- the part on `S`
  have hS1 : ∫ h, S.indicator (ell τ T) h ∂(Pth τ π T) ≤ p * Real.log q + 1 := by
    refine h1.trans ?_
    rw [Real.log_div hq.ne' hp.ne', mul_sub]
    have := xlogx_ge p hp
    linarith
  -- the part on `Sᶜ`
  have hS2 : ∫ h, Sᶜ.indicator (ell τ T) h ∂(Pth τ π T) ≤ 1 := by
    by_cases hw : 0 < (Pth τ π T Sᶜ).toReal
    · obtain ⟨hq', h2⟩ := key_set τ hτ hτ1 π hπ T Sᶜ hS.compl hw
      refine h2.trans ?_
      have hq1' : (Pla τ π T Sᶜ).toReal ≤ 1 := by rw [← measureReal_def]; exact measureReal_le_one
      rw [Real.log_div hq'.ne' hw.ne', mul_sub]
      have := xlogx_ge _ hw
      have hl : Real.log (Pla τ π T Sᶜ).toReal ≤ 0 := Real.log_nonpos hq'.le hq1'
      nlinarith
    · have h0 : (Pth τ π T Sᶜ).toReal = 0 := le_antisymm (not_lt.mp hw) ENNReal.toReal_nonneg
      have hz : Pth τ π T Sᶜ = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
        · exact h
        · exact absurd h (measure_ne_top _ _)
      rw [integral_indicator hS.compl, Measure.restrict_eq_zero.mpr hz, integral_zero_measure]
      norm_num
  rw [hsplit, one_div, Real.log_inv]
  linarith

/-- the clamped curve coordinate `s/4 = a₀ + 1/2` -/
noncomputable def Sf (a : Fin 2 → ℝ) : ℝ := min (max (a 0 + 1 / 2) 0) 1

lemma Sf_meas : Measurable Sf := by
  unfold Sf
  exact (((measurable_pi_apply 0).add measurable_const).max measurable_const).min measurable_const

lemma Sf_bounds (a : Fin 2 → ℝ) : 0 ≤ Sf a ∧ Sf a ≤ 1 := by
  unfold Sf; exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

lemma Sf_curve (a : Fin 2 → ℝ) (ha : a ∈ Curve) :
    Sf a = a 0 + 1 / 2 ∧ 0 ≤ a 0 + 1 / 2 ∧ a 0 + 1 / 2 ≤ 1 / 4 ∧ a 1 ^ 2 ≤ a 0 + 1 / 2 := by
  obtain ⟨s, hs, rfl⟩ := ha
  have e0 : (![-1 / 2 + s / 4, (s + s ^ 2) / 4] : Fin 2 → ℝ) 0 = -1 / 2 + s / 4 := rfl
  have e1 : (![-1 / 2 + s / 4, (s + s ^ 2) / 4] : Fin 2 → ℝ) 1 = (s + s ^ 2) / 4 := rfl
  rw [e0, e1]
  have h0 : 0 ≤ -1 / 2 + s / 4 + 1 / 2 := by linarith [hs.1]
  have h1 : -1 / 2 + s / 4 + 1 / 2 ≤ 1 / 4 := by linarith [hs.2]
  refine ⟨?_, h0, h1, ?_⟩
  · unfold Sf; rw [e0, max_eq_left h0, min_eq_left (by linarith)]
  · have : s * (1 + s) ^ 2 ≤ 4 := by nlinarith [hs.1, hs.2]
    nlinarith [mul_le_mul_of_nonneg_left this hs.1, hs.1]

/-- the per-round `χ²` -/
noncomputable def chi2 (τ : ℝ) (a : Fin 2 → ℝ) : ℝ :=
  (a ⬝ᵥ ![τ, 0] - a ⬝ᵥ ![τ, -τ]) ^ 2 / (1 - (a ⬝ᵥ ![τ, -τ]) ^ 2)

lemma chi2_meas (τ : ℝ) : Measurable (chi2 τ) := by
  unfold chi2
  have h1 : Continuous fun a : Fin 2 → ℝ => a ⬝ᵥ ![τ, 0] := continuous_id.dotProduct continuous_const
  have h2 : Continuous fun a : Fin 2 → ℝ => a ⬝ᵥ ![τ, -τ] := continuous_id.dotProduct continuous_const
  exact ((h1.sub h2).pow 2).measurable.div (continuous_const.sub (h2.pow 2)).measurable

lemma chi2_curve (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (a : Fin 2 → ℝ) (ha : a ∈ Curve) :
    0 ≤ chi2 τ a ∧ chi2 τ a ≤ 16 / 7 * τ ^ 2 * Sf a := by
  obtain ⟨m1, m2, m3, m4⟩ := means τ hτ hτ1 a ha
  obtain ⟨hS, hS0, hS1, hS2⟩ := Sf_curve a ha
  have hden : 7 / 16 ≤ 1 - (a ⬝ᵥ ![τ, -τ]) ^ 2 := by nlinarith
  have hdiff : a ⬝ᵥ ![τ, 0] - a ⬝ᵥ ![τ, -τ] = τ * a 1 := by
    rw [dotProduct_comm a, dotProduct_comm a, dotv, dotv]; ring
  unfold chi2
  rw [hdiff, hS]
  constructor
  · exact div_nonneg (sq_nonneg _) (by linarith)
  · rw [div_le_iff₀ (by linarith)]
    have : (τ * a 1) ^ 2 ≤ τ ^ 2 * (a 0 + 1 / 2) := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hS2 (sq_nonneg τ)
    nlinarith [sq_nonneg τ]

/-! ### The information paid for by regret -/

lemma round_term (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy Curve π) (T : ℕ) (t : Fin T) :
    ∫ h, -Real.log (rr τ (h t).1 (h t).2) ∂(Pth τ π T) ≤ ∫ h, chi2 τ (h t).1 ∂(Pth τ π T) := by
  have hae := hist_ae τ π hπ T ![τ, 0]
  have hm_rr : Measurable fun h : LinearBanditHistory 2 T => rr τ (h t).1 (h t).2 :=
    (rr_meas τ).comp (measurable_pi_apply t)
  have hm_chi : Measurable fun h : LinearBanditHistory 2 T => chi2 τ (h t).1 :=
    (chi2_meas τ).comp (measurable_pi_apply t).fst
  have hb : ∀ h : LinearBanditHistory 2 T, (∀ t, (h t).1 ∈ Curve) →
      1 / 7 ≤ rr τ (h t).1 (h t).2 ∧ rr τ (h t).1 (h t).2 ≤ 7 :=
    fun h hh => rr_bounds τ hτ hτ1 _ (hh t) _
  have hint_inv : Integrable (fun h : LinearBanditHistory 2 T => 1 / rr τ (h t).1 (h t).2)
      (Pth τ π T) := by
    refine Integrable.of_bound (measurable_const.div hm_rr).aestronglyMeasurable 7
      (hae.mono fun h hh => ?_)
    obtain ⟨b1, b2⟩ := hb h hh
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_iff₀ (by linarith)]; linarith
  have hint_log : Integrable (fun h : LinearBanditHistory 2 T => -Real.log (rr τ (h t).1 (h t).2))
      (Pth τ π T) := by
    refine Integrable.of_bound (Real.measurable_log.comp hm_rr).neg.aestronglyMeasurable
      (Real.log 7) (hae.mono fun h hh => ?_)
    obtain ⟨b1, b2⟩ := hb h hh
    rw [Real.norm_eq_abs, abs_neg, abs_le]; constructor
    · have := Real.log_le_log (by norm_num) b1
      rw [one_div, Real.log_inv] at this; linarith
    · exact Real.log_le_log (by linarith) b2
  have hint_chi : Integrable (fun h : LinearBanditHistory 2 T => chi2 τ (h t).1) (Pth τ π T) := by
    refine Integrable.of_bound hm_chi.aestronglyMeasurable (16 / 7 * τ ^ 2)
      (hae.mono fun h hh => ?_)
    obtain ⟨c1, c2⟩ := chi2_curve τ hτ hτ1 _ (hh t)
    have := (Sf_bounds (h t).1).2
    rw [Real.norm_eq_abs, abs_of_nonneg c1]
    nlinarith [sq_nonneg τ, (Sf_bounds (h t).1).1]
  -- `−log x ≤ 1/x − 1`
  have h1 : ∫ h, -Real.log (rr τ (h t).1 (h t).2) ∂(Pth τ π T) ≤
      ∫ h, (1 / rr τ (h t).1 (h t).2 - 1) ∂(Pth τ π T) := by
    refine integral_mono_ae hint_log (hint_inv.sub (integrable_const 1)) (hae.mono fun h hh => ?_)
    obtain ⟨b1, _⟩ := hb h hh
    have hpos : 0 < 1 / rr τ (h t).1 (h t).2 := by positivity
    have := Real.log_le_sub_one_of_pos hpos
    rw [one_div, Real.log_inv] at this
    show -Real.log (rr τ (h t).1 (h t).2) ≤ 1 / rr τ (h t).1 (h t).2 - 1
    rw [one_div]; linarith
  -- `E[1/r] = E[1 + χ²]`
  have h2 : ∫ h, 1 / rr τ (h t).1 (h t).2 ∂(Pth τ π T) = ∫ h, (1 + chi2 τ (h t).1) ∂(Pth τ π T) := by
    have hn1 : 0 ≤ᵐ[Pth τ π T] fun h => 1 / rr τ (h t).1 (h t).2 := hae.mono fun h hh => by
      obtain ⟨b1, _⟩ := hb h hh; show 0 ≤ 1 / rr τ (h t).1 (h t).2; positivity
    have hn2 : 0 ≤ᵐ[Pth τ π T] fun h => 1 + chi2 τ (h t).1 := hae.mono fun h hh => by
      obtain ⟨c1, _⟩ := chi2_curve τ hτ hτ1 _ (hh t); show 0 ≤ 1 + chi2 τ (h t).1; linarith
    rw [integral_eq_lintegral_of_nonneg_ae hn1 (measurable_const.div hm_rr).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae hn2 (measurable_const.add hm_chi).aestronglyMeasurable]
    congr 1
    have hF1 : Measurable fun p : (Fin 2 → ℝ) × ℝ => ENNReal.ofReal (1 / rr τ p.1 p.2) :=
      ENNReal.measurable_ofReal.comp (measurable_const.div (rr_meas τ))
    have hF2 : Measurable fun p : (Fin 2 → ℝ) × ℝ => ENNReal.ofReal (1 + chi2 τ p.1) :=
      ENNReal.measurable_ofReal.comp (measurable_const.add ((chi2_meas τ).comp measurable_fst))
    have L1 : ∫⁻ h, ENNReal.ofReal (1 / rr τ (h t).1 (h t).2) ∂(Pth τ π T) =
        ∫⁻ h, ∫⁻ a, ∫⁻ y, ENNReal.ofReal (1 / rr τ a y) ∂((signEnv (![τ, 0] : Fin 2 → ℝ)).fb t a)
          ∂(π.select t h) ∂(Pth τ π t) :=
      lintegral_round _ π T t t.2 _ hF1
    have L2 : ∫⁻ h, ENNReal.ofReal (1 + chi2 τ (h t).1) ∂(Pth τ π T) =
        ∫⁻ h, ∫⁻ a, ∫⁻ y, ENNReal.ofReal (1 + chi2 τ a) ∂((signEnv (![τ, 0] : Fin 2 → ℝ)).fb t a)
          ∂(π.select t h) ∂(Pth τ π t) :=
      lintegral_round _ π T t t.2 _ hF2
    rw [L1, L2]
    refine lintegral_congr fun h => lintegral_congr_ae ?_
    have hsel : ∀ᵐ a ∂(π.select t h), a ∈ Curve := by rw [ae_iff]; exact hπ t h
    filter_upwards [hsel] with a ha
    rw [lintegral_const, measure_univ, mul_one]
    exact inv_rr_mean τ hτ hτ1 a ha
  calc ∫ h, -Real.log (rr τ (h t).1 (h t).2) ∂(Pth τ π T)
      ≤ ∫ h, (1 / rr τ (h t).1 (h t).2 - 1) ∂(Pth τ π T) := h1
    _ = ∫ h, 1 / rr τ (h t).1 (h t).2 ∂(Pth τ π T) - 1 := by
        rw [integral_sub hint_inv (integrable_const 1), integral_const, probReal_univ, one_smul]
    _ = ∫ h, (1 + chi2 τ (h t).1) ∂(Pth τ π T) - 1 := by rw [h2]
    _ = ∫ h, chi2 τ (h t).1 ∂(Pth τ π T) := by
        rw [integral_add (integrable_const 1) hint_chi, integral_const, probReal_univ, one_smul]
        ring

lemma D_upper (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy Curve π) (T : ℕ) :
    -∫ h, ell τ T h ∂(Pth τ π T) ≤
      16 / 7 * τ ^ 2 * ∑ t : Fin T, ∫ h, Sf (h t).1 ∂(Pth τ π T) := by
  have hae := hist_ae τ π hπ T ![τ, 0]
  have hint : ∀ t : Fin T, Integrable (fun h : LinearBanditHistory 2 T =>
      Real.log (rr τ (h t).1 (h t).2)) (Pth τ π T) := by
    intro t
    refine Integrable.of_bound (Real.measurable_log.comp
      ((rr_meas τ).comp (measurable_pi_apply t))).aestronglyMeasurable (Real.log 7)
      (hae.mono fun h hh => ?_)
    obtain ⟨b1, b2⟩ := rr_bounds τ hτ hτ1 _ (hh t) (h t).2
    rw [Real.norm_eq_abs, abs_le]; constructor
    · have := Real.log_le_log (by norm_num) b1
      rw [one_div, Real.log_inv] at this; linarith
    · exact Real.log_le_log (by linarith) b2
  have hsum : -∫ h, ell τ T h ∂(Pth τ π T) =
      ∑ t : Fin T, ∫ h, -Real.log (rr τ (h t).1 (h t).2) ∂(Pth τ π T) := by
    unfold ell
    rw [integral_finsetSum _ (fun t _ => hint t), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [integral_neg]
  rw [hsum, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => (round_term τ hτ hτ1 π hπ T t).trans ?_
  rw [← integral_const_mul]
  have hSm : Measurable fun h : LinearBanditHistory 2 T => Sf (h t).1 :=
    Sf_meas.comp (measurable_pi_apply t).fst
  refine integral_mono_ae ?_ ?_ (hae.mono fun h hh => (chi2_curve τ hτ hτ1 _ (hh t)).2)
  · refine Integrable.of_bound ((chi2_meas τ).comp (measurable_pi_apply t).fst).aestronglyMeasurable
      (16 / 7 * τ ^ 2) (hae.mono fun h hh => ?_)
    obtain ⟨c1, c2⟩ := chi2_curve τ hτ hτ1 _ (hh t)
    rw [Real.norm_eq_abs, abs_of_nonneg c1]
    nlinarith [sq_nonneg τ, (Sf_bounds (h t).1).1, (Sf_bounds (h t).1).2]
  · exact (Integrable.of_bound hSm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Sf_bounds _).1]; exact (Sf_bounds _).2)).const_mul _

end LB32a

-- ===== LB/T32aR =====

/-! # Theorem 3.2(i): regret bounds, the separating event, and the asymptotics -/

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL Filter Topology
open scoped ENNReal Pointwise NNReal

namespace LB32a

open LBC

lemma dot_le_one (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (θ : Fin 2 → ℝ)
    (hθ : θ = ![τ, 0] ∨ θ = ![τ, -τ]) (a : Fin 2 → ℝ) (ha : a ∈ Curve) : |a ⬝ᵥ θ| ≤ 1 := by
  obtain ⟨m1, m2, m3, m4⟩ := means τ hτ hτ1 a ha
  rcases hθ with rfl | rfl
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

lemma Sf_int {T : ℕ} (P : Measure (LinearBanditHistory 2 T)) [IsProbabilityMeasure P] (t : Fin T) :
    Integrable (fun h : LinearBanditHistory 2 T => Sf (h t).1) P :=
  Integrable.of_bound (Sf_meas.comp (measurable_pi_apply t).fst).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Sf_bounds _).1]; exact (Sf_bounds _).2)

lemma reg_theta (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy Curve π) (T : ℕ) :
    τ * ∑ t : Fin T, ∫ h, Sf (h t).1 ∂(Pth τ π T) ≤ (signEnv (![τ, 0] : Fin 2 → ℝ)).regret Curve π T := by
  let c : Fin T → LinearBanditHistory 2 T → ℝ := fun t h => τ * Sf (h t).1
  have hcm : ∀ t, Measurable (c t) := fun t =>
    (Sf_meas.comp (measurable_pi_apply t).fst).const_mul _
  have hcb : ∀ t h, |c t h| ≤ τ := by
    intro t h; simp only [c]
    rw [abs_of_nonneg (mul_nonneg hτ.le (Sf_bounds _).1)]
    nlinarith [(Sf_bounds (h t).1).2]
  have key := regret_ge (signEnv (![τ, 0] : Fin 2 → ℝ)) π Curve Curve_meas hπ T ![-1 / 2, 0] a0_mem
    (fun t _ a ha => dot_le_one τ hτ hτ1 _ (Or.inl rfl) a ha) c hcm τ hcb (by
      intro h hh
      apply Finset.sum_le_sum; intro t _
      show τ * Sf (h t).1 ≤ ((h t).1 - ![-1 / 2, 0]) ⬝ᵥ ![τ, 0]
      rw [(Sf_curve _ (hh t)).1]
      simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply, cons_val_zero, cons_val_one, head_cons]
      linarith)
  refine le_trans (le_of_eq ?_) key
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [c]; rw [integral_const_mul]

lemma reg_lambda (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy Curve π) (T : ℕ) :
    τ * ∑ t : Fin T, ∫ h, (1 / 4 - Sf (h t).1) ∂(Pla τ π T) ≤
      (signEnv (![τ, -τ] : Fin 2 → ℝ)).regret Curve π T := by
  let c : Fin T → LinearBanditHistory 2 T → ℝ := fun t h => τ * (1 / 4 - Sf (h t).1)
  have hcm : ∀ t, Measurable (c t) := fun t =>
    (measurable_const.sub (Sf_meas.comp (measurable_pi_apply t).fst)).const_mul _
  have hcb : ∀ t h, |c t h| ≤ τ := by
    intro t h; simp only [c]
    rw [abs_mul, abs_of_pos hτ]
    have := Sf_bounds (h t).1
    have : |1 / 4 - Sf (h t).1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith
  have key := regret_ge (signEnv (![τ, -τ] : Fin 2 → ℝ)) π Curve Curve_meas hπ T ![-1 / 4, 1 / 2]
    a1_mem (fun t _ a ha => dot_le_one τ hτ hτ1 _ (Or.inr rfl) a ha) c hcm τ hcb (by
      intro h hh
      apply Finset.sum_le_sum; intro t _
      show τ * (1 / 4 - Sf (h t).1) ≤ ((h t).1 - ![-1 / 4, 1 / 2]) ⬝ᵥ ![τ, -τ]
      have hS := (Sf_curve _ (hh t)).1
      rw [hS]
      obtain ⟨s, hs, hst⟩ := hh t
      rw [hst]
      simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply, cons_val_zero, cons_val_one, head_cons]
      have hss : 0 ≤ s - s ^ 2 := by nlinarith [hs.1, hs.2]
      nlinarith [mul_nonneg hτ.le hss])
  refine le_trans (le_of_eq ?_) key
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [c]; rw [integral_const_mul]

/-- the separating event `Σ s_t ≤ T/2`, i.e. `Σ S_t ≤ T/8` -/
def Ev (T : ℕ) : Set (LinearBanditHistory 2 T) := {h | ∑ t : Fin T, Sf (h t).1 ≤ (T : ℝ) / 8}

lemma Ev_meas (T : ℕ) : MeasurableSet (Ev T) :=
  measurableSet_le (Finset.measurable_sum _ fun t _ => Sf_meas.comp (measurable_pi_apply t).fst)
    measurable_const

lemma pc_bound (τ : ℝ) (π : LinearBanditPolicy 2) (T : ℕ) :
    (T : ℝ) / 8 * (Pth τ π T (Ev T)ᶜ).toReal ≤ ∑ t : Fin T, ∫ h, Sf (h t).1 ∂(Pth τ π T) := by
  rw [← integral_finsetSum _ (fun t _ => Sf_int _ t)]
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := Pth τ π T)
    (f := fun h : LinearBanditHistory 2 T => ∑ t : Fin T, Sf (h t).1)
    (Filter.Eventually.of_forall fun h => Finset.sum_nonneg fun t _ => (Sf_bounds _).1)
    (integrable_finsetSum _ fun t _ => Sf_int _ t) ((T : ℝ) / 8)
  refine le_trans ?_ hm
  have hsub : (Ev T)ᶜ ⊆ {h : LinearBanditHistory 2 T | (T : ℝ) / 8 ≤ ∑ t : Fin T, Sf (h t).1} := by
    intro h hh; simp only [Ev, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hh
    exact hh.le
  rw [measureReal_def]
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub))
    (by positivity)

lemma q_bound (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy Curve π) (T : ℕ) :
    (T : ℝ) / 8 * (Pla τ π T (Ev T)).toReal ≤ ∑ t : Fin T, ∫ h, (1 / 4 - Sf (h t).1) ∂(Pla τ π T) := by
  have hae := hist_ae τ π hπ T ![τ, -τ]
  have hint : ∀ t : Fin T, Integrable (fun h : LinearBanditHistory 2 T => 1 / 4 - Sf (h t).1)
      (Pla τ π T) := fun t => (integrable_const _).sub (Sf_int _ t)
  rw [← integral_finsetSum _ (fun t _ => hint t)]
  have h1 : ∫ h, (Ev T).indicator (fun _ => (T : ℝ) / 8) h ∂(Pla τ π T) =
      (T : ℝ) / 8 * (Pla τ π T (Ev T)).toReal := by
    rw [integral_indicator_const _ (Ev_meas T), smul_eq_mul, measureReal_def, mul_comm]
  rw [← h1]
  refine integral_mono_ae ((integrable_const _).indicator (Ev_meas T))
    (integrable_finsetSum _ fun t _ => hint t) (hae.mono fun h hh => ?_)
  have hle : ∀ t : Fin T, 0 ≤ 1 / 4 - Sf (h t).1 := fun t => by
    have := (Sf_curve _ (hh t)); linarith [this.1, this.2.2.1]
  by_cases he : h ∈ Ev T
  · rw [Set.indicator_of_mem he]
    have : ∑ t : Fin T, Sf (h t).1 ≤ (T : ℝ) / 8 := he
    show (T : ℝ) / 8 ≤ ∑ t : Fin T, (1 / 4 - Sf (h t).1)
    rw [Finset.sum_sub_distrib]; simp; linarith
  · rw [Set.indicator_of_notMem he]
    exact Finset.sum_nonneg fun t _ => hle t

/-- **The finite-horizon information inequality** -/
lemma finite_bound (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy Curve π) (T : ℕ) (hT : 1 ≤ T) :
    1 - (Pth τ π T (Ev T)).toReal ≤ 8 * (signEnv (![τ, 0] : Fin 2 → ℝ)).regret Curve π T / (τ * T) ∧
    (Pla τ π T (Ev T)).toReal ≤ 8 * (signEnv (![τ, -τ] : Fin 2 → ℝ)).regret Curve π T / (τ * T) ∧
    (0 < (Pth τ π T (Ev T)).toReal →
      7 / (16 * τ) * ((Pth τ π T (Ev T)).toReal * Real.log (1 / (Pla τ π T (Ev T)).toReal) - 2) ≤
        (signEnv (![τ, 0] : Fin 2 → ℝ)).regret Curve π T) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hcomp : (Pth τ π T (Ev T)ᶜ).toReal = 1 - (Pth τ π T (Ev T)).toReal := by
    rw [← measureReal_def, ← measureReal_def, probReal_compl_eq_one_sub (Ev_meas T)]
  have hRθ := reg_theta τ hτ hτ1 π hπ T
  have hRl := reg_lambda τ hτ hτ1 π hπ T
  refine ⟨?_, ?_, ?_⟩
  · have := pc_bound τ π T
    rw [hcomp] at this
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · have := q_bound τ hτ hτ1 π hπ T
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · intro hp
    have hlow := D_lower τ hτ hτ1 π hπ T (Ev T) (Ev_meas T) hp
    have hup := D_upper τ hτ hτ1 π hπ T
    have hS0 : 0 ≤ ∑ t : Fin T, ∫ h, Sf (h t).1 ∂(Pth τ π T) :=
      Finset.sum_nonneg fun t _ => integral_nonneg fun h => (Sf_bounds _).1
    have h1 : 7 / (16 * τ) * (16 / 7 * τ ^ 2 * ∑ t : Fin T, ∫ h, Sf (h t).1 ∂(Pth τ π T)) =
        τ * ∑ t : Fin T, ∫ h, Sf (h t).1 ∂(Pth τ π T) := by field_simp
    have h2 := mul_le_mul_of_nonneg_left (hlow.trans hup) (by positivity : (0 : ℝ) ≤ 7 / (16 * τ))
    linarith

/-! ### The asymptotics -/

theorem asymp (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (π : LinearBanditPolicy 2)
    (hπ : IsSupportedLinearPolicy Curve π) (hcons : IsConsistentOn Curve (sharpInstances Curve) π)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop, (7 / (16 * τ) - ε) * Real.log T ≤
      (signEnv (![τ, 0] : Fin 2 → ℝ)).regret Curve π T := by
  set K : ℝ := 7 / (16 * τ) with hK_def
  have hK : 0 < K := by positivity
  set δ : ℝ := min (1 / 2) (ε / (4 * K)) with hδ_def
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδK : δ ≤ ε / (4 * K) := min_le_right _ _
  have hθc := hcons ![τ, 0] (theta_sharp τ hτ hτ1) (1 / 2) (by norm_num)
  have hlc := hcons ![τ, -τ] (lambda_sharp τ hτ hτ1) δ hδ0
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hθc.eventually (eventually_lt_nhds (show (0 : ℝ) < τ * δ / 8 by positivity)),
    hlc.eventually (eventually_lt_nhds (show (0 : ℝ) < τ / 8 by positivity)),
    eventually_ge_atTop 1, hlog.eventually_ge_atTop (4 * K / ε)] with T h1 h2 hT hlogT
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hTr
  obtain ⟨hp, hq, hmain⟩ := finite_bound τ hτ hτ1 π hπ T hT
  set Rθ := (signEnv (![τ, 0] : Fin 2 → ℝ)).regret Curve π T
  set Rl := (signEnv (![τ, -τ] : Fin 2 → ℝ)).regret Curve π T
  set p := (Pth τ π T (Ev T)).toReal
  set q := (Pla τ π T (Ev T)).toReal
  -- `1 − p < δ`
  have hsq : (T : ℝ) ^ ((1 : ℝ) / 2) ≤ T := by
    calc (T : ℝ) ^ ((1 : ℝ) / 2) ≤ (T : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hTr (by norm_num)
      _ = T := Real.rpow_one _
  have hsqpos : 0 < (T : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hT0 _
  have hRθ : Rθ < τ * δ / 8 * T := by
    have := (div_lt_iff₀ hsqpos).mp h1
    calc Rθ < τ * δ / 8 * (T : ℝ) ^ ((1 : ℝ) / 2) := this
      _ ≤ τ * δ / 8 * T := mul_le_mul_of_nonneg_left hsq (by positivity)
  have hp1 : 1 - δ < p := by
    have : 8 * Rθ / (τ * T) < δ := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have hppos : 0 < p := by linarith
  -- `q < T^{δ-1}` and `q > 0`
  have hTδ : 0 < (T : ℝ) ^ δ := Real.rpow_pos_of_pos hT0 _
  have hRl : Rl < τ / 8 * (T : ℝ) ^ δ := (div_lt_iff₀ hTδ).mp h2
  have hqT : q < (T : ℝ) ^ (δ - 1) := by
    have e : (T : ℝ) ^ (δ - 1) = (T : ℝ) ^ δ / T := by
      rw [Real.rpow_sub hT0, Real.rpow_one]
    rw [e]
    calc q ≤ 8 * Rl / (τ * T) := hq
      _ < 8 * (τ / 8 * (T : ℝ) ^ δ) / (τ * T) := by
          apply div_lt_div_of_pos_right _ (by positivity); linarith
      _ = (T : ℝ) ^ δ / T := by field_simp
  have hqpos : 0 < q := (key_set τ hτ hτ1 π hπ T (Ev T) (Ev_meas T) hppos).1
  have hlogq : (1 - δ) * Real.log T ≤ Real.log (1 / q) := by
    have := Real.log_lt_log hqpos hqT
    rw [Real.log_rpow hT0] at this
    rw [one_div, Real.log_inv]; linarith
  have hR := hmain hppos
  -- combine
  have hA : (1 - δ) * ((1 - δ) * Real.log T) ≤ p * Real.log (1 / q) := by
    have h0 : 0 ≤ (1 - δ) * Real.log T := mul_nonneg (by linarith) hlog0
    calc (1 - δ) * ((1 - δ) * Real.log T) ≤ p * ((1 - δ) * Real.log T) :=
          mul_le_mul_of_nonneg_right hp1.le h0
      _ ≤ p * Real.log (1 / q) := mul_le_mul_of_nonneg_left hlogq hppos.le
  have hB : (1 - ε / (2 * K)) * Real.log T ≤ (1 - δ) * ((1 - δ) * Real.log T) := by
    have h2δ : 1 - ε / (2 * K) ≤ (1 - δ) * (1 - δ) := by
      have : ε / (2 * K) = 2 * (ε / (4 * K)) := by field_simp; ring
      nlinarith [sq_nonneg δ]
    nlinarith
  have hC : 2 * K ≤ ε / 2 * Real.log T := by
    have := hlogT
    rw [div_le_iff₀ hε] at this
    nlinarith
  have hD : K * (1 - ε / (2 * K)) = K - ε / 2 := by field_simp
  calc (K - ε) * Real.log T = (K - ε / 2) * Real.log T - ε / 2 * Real.log T := by ring
    _ ≤ K * ((1 - ε / (2 * K)) * Real.log T) - 2 * K := by rw [← mul_assoc, hD]; linarith
    _ ≤ K * (p * Real.log (1 / q)) - 2 * K := by
        have := mul_le_mul_of_nonneg_left (hB.trans hA) hK.le; linarith
    _ = K * (p * Real.log (1 / q) - 2) := by ring
    _ ≤ Rθ := hR

end LB32a

namespace IAFTRL

open Filter Topology

theorem theorem_3_2_i_proved (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    let curve : Set (Fin 2 → ℝ) := {a | ∃ s ∈ Set.Icc (0 : ℝ) 1, a = ![-1 / 2 + s / 4, (s + s ^ 2) / 4]}
    let θ : Fin 2 → ℝ := ![τ, 0]
    cstarCtr curve θ ![-1 / 2, 0] = 8 / τ ∧
    ∀ π : LinearBanditPolicy 2, IsSupportedLinearPolicy curve π →
      IsConsistentOn curve (sharpInstances curve) π →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
        (7 / (16 * τ) - ε) * Real.log T ≤ (signEnv θ).regret curve π T := by
  intro curve θ
  exact ⟨LB32a.cstar_eq τ hτ, fun π hπ hc ε hε => LB32a.asymp τ hτ hτ1 π hπ hc ε hε⟩

end IAFTRL

theorem _root_.solution : type_of% @IAFTRL.theorem_3_2_i_proved := @IAFTRL.theorem_3_2_i_proved
