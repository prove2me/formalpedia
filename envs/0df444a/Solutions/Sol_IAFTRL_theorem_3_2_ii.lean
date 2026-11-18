-- Prove2me | solution 1 for IAFTRL.theorem_3_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T04:49:37.98935+00:00
-- url     : https://prove2.me/submissions/15cb7f3b-402a-4242-a228-d4084ae76070

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

-- ===== LB/T32bG =====

/-! # Theorem 3.2(ii): geometry of the arch (Lemma H.1) -/

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal Pointwise NNReal

namespace LB32b

open LBC

/-- the arch point `a(x) = (x, (1 − x²)/2)` -/
noncomputable def aA (x : ℝ) : Fin 2 → ℝ := ![x, (1 - x ^ 2) / 2]

/-- the arch -/
def Arch : Set (Fin 2 → ℝ) := {a | ∃ x ∈ Set.Icc (-1 : ℝ) 1, a = ![x, (1 - x ^ 2) / 2]}

/-- the loss vector `θ_σ` -/
noncomputable def thS (φ σ : ℝ) : Fin 2 → ℝ := ![σ * φ / 2, 1 / 2]

lemma aA_mem {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : aA x ∈ Arch := ⟨x, hx, rfl⟩

lemma sig_sq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num

lemma sig_mem {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases hσ with rfl | rfl <;> norm_num

lemma astar_eq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : (![-σ, 0] : Fin 2 → ℝ) = aA (-σ) := by
  funext i; fin_cases i <;> simp [aA, neg_sq, sig_sq hσ]

lemma astar_mem {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : (![-σ, 0] : Fin 2 → ℝ) ∈ Arch := by
  rw [astar_eq hσ]; apply aA_mem; rcases hσ with rfl | rfl <;> norm_num

lemma Arch_eq_image : Arch = aA '' Set.Icc (-1 : ℝ) 1 := by
  ext a; constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

lemma Arch_meas : MeasurableSet Arch := by
  rw [Arch_eq_image]
  have hc : Continuous aA := by
    unfold aA
    refine continuous_pi fun i => ?_
    fin_cases i
    · simp; fun_prop
    · simp; fun_prop
  exact ((isCompact_Icc.image hc).isClosed).measurableSet

lemma Arch_nonempty : Arch.Nonempty := ⟨aA 0, aA_mem (by norm_num)⟩

lemma dot2 (a x y : ℝ) (b : ℝ) : (![a, b] : Fin 2 → ℝ) ⬝ᵥ ![x, y] = a * x + b * y := by
  simp [dotProduct, Fin.sum_univ_two]

/-- the gap from `a* = −σe₁` -/
lemma gap_arch (φ σ x : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (aA x - ![-σ, 0]) ⬝ᵥ thS φ σ = φ / 2 * (1 + σ * x) + (1 - x ^ 2) / 4 := by
  unfold aA thS
  rw [sub_dotProduct, dot2, dot2]
  have := sig_sq hσ
  linear_combination (φ / 2) * this

lemma unique_opt (φ : ℝ) (hφ : 0 < φ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∀ a ∈ Arch, a ≠ ![-σ, 0] → (![-σ, 0] : Fin 2 → ℝ) ⬝ᵥ thS φ σ < a ⬝ᵥ thS φ σ := by
  rintro a ⟨x, hx, rfl⟩ hne
  have hg := gap_arch φ σ x hσ
  unfold aA at hg
  rw [sub_dotProduct] at hg
  have h1 : 0 ≤ 1 + σ * x := by rcases hσ with rfl | rfl <;> linarith [hx.1, hx.2]
  have h2 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  suffices 0 < φ / 2 * (1 + σ * x) + (1 - x ^ 2) / 4 by linarith
  by_cases hx1 : x ^ 2 < 1
  · have : 0 < (1 - x ^ 2) / 4 := by linarith
    nlinarith
  · have hx2 : x ^ 2 = 1 := by nlinarith [hx.1, hx.2]
    have : x = 1 ∨ x = -1 := by
      have : (x - 1) * (x + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    have hxs : x ≠ -σ := by
      intro h; apply hne; rw [h]; funext i; fin_cases i <;> simp [neg_sq, sig_sq hσ]
    have : 1 + σ * x = 2 := by
      rcases hσ with rfl | rfl <;> rcases this with rfl | rfl <;> simp_all <;> norm_num
    rw [this, hx2]; linarith

/-! ### The norm `‖·‖_S` -/

lemma Sset_b0 : ∀ s ∈ Sset Arch, |(![1, 0] : Fin 2 → ℝ) ⬝ᵥ s| ≤ 1 := by
  apply Sset_abs_le
  rintro a ⟨x, hx, rfl⟩
  rw [dot2]; simp only [one_mul, zero_mul, add_zero]
  exact abs_le.mpr ⟨hx.1, hx.2⟩

lemma Sset_b1 : ∀ s ∈ Sset Arch, |(![0, 2] : Fin 2 → ℝ) ⬝ᵥ s| ≤ 1 := by
  apply Sset_abs_le
  rintro a ⟨x, hx, rfl⟩
  rw [dot2]; simp only [zero_mul, zero_add]
  rw [abs_le]; constructor <;> nlinarith [hx.1, hx.2]

/-- coordinates of `z − a*` on the hull: `w = 1 + σ z₀ ≥ 0`, `z₁ ≥ 0` -/
lemma hull_coords (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (z : Fin 2 → ℝ) (hz : z ∈ convexHull ℝ Arch) :
    0 ≤ 1 + σ * z 0 ∧ 0 ≤ z 1 ∧ z 1 ≤ 1 / 2 := by
  have h1 := convexHull_le_of Arch ![-σ, 0] 1 (by
    rintro a ⟨x, hx, rfl⟩; rw [dot2]
    rcases hσ with rfl | rfl <;> nlinarith [hx.1, hx.2]) z hz
  have h2 := convexHull_le_of Arch ![0, -1] 0 (by
    rintro a ⟨x, hx, rfl⟩; rw [dot2]; nlinarith [hx.1, hx.2]) z hz
  have h3 := convexHull_le_of Arch ![0, 1] (1 / 2) (by
    rintro a ⟨x, hx, rfl⟩; rw [dot2]; nlinarith [hx.1, hx.2]) z hz
  have e1 : (![-σ, 0] : Fin 2 → ℝ) ⬝ᵥ z = -σ * z 0 := by
    simp [dotProduct, Fin.sum_univ_two]
  have e2 : (![0, -1] : Fin 2 → ℝ) ⬝ᵥ z = -z 1 := by simp [dotProduct, Fin.sum_univ_two]
  have e3 : (![0, 1] : Fin 2 → ℝ) ⬝ᵥ z = z 1 := by simp [dotProduct, Fin.sum_univ_two]
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  exact ⟨by linarith, by linarith, h3⟩

lemma decomp (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (z : Fin 2 → ℝ) :
    z - ![-σ, 0] = (1 + σ * z 0) • (![σ, 0] : Fin 2 → ℝ) + (2 * z 1) • (![0, 1 / 2] : Fin 2 → ℝ) := by
  have := sig_sq hσ
  funext i; fin_cases i
  · simp; linear_combination (-(z 0)) * this
  · simp; ring

lemma sigE_mem {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : (![σ, 0] : Fin 2 → ℝ) ∈ Sset Arch := by
  apply mem_Sset_of_mem
  refine ⟨σ, sig_mem hσ, ?_⟩
  funext i; fin_cases i <;> simp [sig_sq hσ]

lemma halfE_mem : (![0, 1 / 2] : Fin 2 → ℝ) ∈ Sset Arch := by
  apply mem_Sset_of_mem
  exact ⟨0, by norm_num, by funext i; fin_cases i <;> norm_num⟩

lemma sNorm_le (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (z : Fin 2 → ℝ) (hz : z ∈ convexHull ℝ Arch) :
    sNorm Arch (z - ![-σ, 0]) ≤ (1 + σ * z 0) + 2 * z 1 := by
  obtain ⟨h1, h2, _⟩ := hull_coords σ hσ z hz
  rw [decomp σ hσ z]
  exact gauge_le_comb _ (Sset_convex _) _ _ (sigE_mem hσ) halfE_mem _ _ h1 (by linarith)

lemma sNorm_pos (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (z : Fin 2 → ℝ) (hz : z ∈ convexHull ℝ Arch)
    (hne : z ≠ ![-σ, 0]) : 0 < sNorm Arch (z - ![-σ, 0]) := by
  obtain ⟨h1, h2, _⟩ := hull_coords σ hσ z hz
  have hsum : 0 < (1 + σ * z 0) + 2 * z 1 := by
    rcases eq_or_lt_of_le (add_nonneg h1 (by linarith : (0 : ℝ) ≤ 2 * z 1)) with h | h
    · exfalso; apply hne
      have ha : 1 + σ * z 0 = 0 := by linarith
      have hb : z 1 = 0 := by linarith
      have := sig_sq hσ
      funext i; fin_cases i
      · simp; linear_combination σ * ha - z 0 * this
      · simp [hb]
    · exact h
  have hmem : z - ![-σ, 0] ∈ ((1 + σ * z 0) + 2 * z 1) • Sset Arch := by
    rw [decomp σ hσ z]
    exact mem_smul_comb _ (Sset_convex _) _ _ (sigE_mem hσ) halfE_mem _ _ h1 (by linarith) hsum
  have g0 := le_gauge_of_bound _ ![1, 0] _ _ hsum hmem Sset_b0
  have g1 := le_gauge_of_bound _ ![0, 2] _ _ hsum hmem Sset_b1
  have e0 : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ (z - ![-σ, 0]) = z 0 + σ := by
    simp [dotProduct, Fin.sum_univ_two]
  have e1 : (![0, 2] : Fin 2 → ℝ) ⬝ᵥ (z - ![-σ, 0]) = 2 * z 1 := by
    simp [dotProduct, Fin.sum_univ_two]
  rw [e0] at g0; rw [e1] at g1
  show 0 < gauge (Sset Arch) (z - ![-σ, 0])
  by_contra hle; push Not at hle
  have ha : z 0 + σ = 0 := abs_nonpos_iff.mp (g0.trans hle)
  have hb : z 1 = 0 := by
    have := abs_nonpos_iff.mp (g1.trans hle); linarith
  apply hne
  funext i; fin_cases i
  · simp; linarith
  · simp [hb]

lemma gap_hull (φ σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (z : Fin 2 → ℝ) :
    (z - ![-σ, 0]) ⬝ᵥ thS φ σ = φ / 2 * (1 + σ * z 0) + z 1 / 2 := by
  have := sig_sq hσ
  simp [thS, dotProduct, Fin.sum_univ_two]
  linear_combination (φ / 2) * this

/-- the sharpness modulus: `φ/6 ≤ ς ≤ φ/2` -/
lemma sharp_bounds (φ : ℝ) (hφ : 0 < φ) (hφ' : φ ≤ 1 / 8) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    φ / 6 ≤ sharpModulus Arch (thS φ σ) ![-σ, 0] ∧
      sharpModulus Arch (thS φ σ) ![-σ, 0] ≤ φ / 2 := by
  have hσmem : aA σ ∈ Kset Arch \ {![-σ, 0]} := by
    refine ⟨subset_convexHull ℝ _ (aA_mem (sig_mem hσ)), ?_⟩
    intro h
    have := congrFun (h : aA σ = ![-σ, 0]) 0
    simp [aA] at this
    rcases hσ with rfl | rfl <;> norm_num at this
  have hratio : ∀ z ∈ Kset Arch \ {![-σ, 0]},
      φ / 6 ≤ ((z - ![-σ, 0]) ⬝ᵥ thS φ σ) / sNorm Arch (z - ![-σ, 0]) := by
    rintro z ⟨hz, hne⟩
    have hpos := sNorm_pos σ hσ z hz hne
    rw [le_div_iff₀ hpos, gap_hull φ σ hσ z]
    have hle := sNorm_le σ hσ z hz
    obtain ⟨h1, h2, _⟩ := hull_coords σ hσ z hz
    calc φ / 6 * sNorm Arch (z - ![-σ, 0]) ≤ φ / 6 * ((1 + σ * z 0) + 2 * z 1) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ φ / 2 * (1 + σ * z 0) + z 1 / 2 := by nlinarith
  constructor
  · refine le_csInf ⟨_, ⟨aA σ, hσmem, rfl⟩⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hratio z hz
  · have hbdd : BddBelow ((fun a => ((a - ![-σ, 0]) ⬝ᵥ thS φ σ) / sNorm Arch (a - ![-σ, 0])) ''
        (Kset Arch \ {![-σ, 0]})) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact le_trans (by positivity : (0 : ℝ) ≤ φ / 6) (hratio z hz)
    refine (csInf_le hbdd ⟨aA σ, hσmem, rfl⟩).trans (le_of_eq ?_)
    have hv : aA σ - ![-σ, 0] = (2 : ℝ) • (![σ, 0] : Fin 2 → ℝ) := by
      funext i; fin_cases i <;> simp [aA, sig_sq hσ] <;> ring
    have hn : sNorm Arch (aA σ - ![-σ, 0]) = 2 := by
      apply le_antisymm
      · rw [hv]
        have := gauge_le_comb (Sset Arch) (Sset_convex _) ![σ, 0] ![0, 1 / 2] (sigE_mem hσ) halfE_mem
          2 0 (by norm_num) le_rfl
        rw [zero_smul, add_zero, add_zero] at this
        exact this
      · have hmem : aA σ - ![-σ, 0] ∈ (2 : ℝ) • Sset Arch := by rw [hv]; exact ⟨_, sigE_mem hσ, rfl⟩
        have := le_gauge_of_bound _ ![1, 0] _ 2 two_pos hmem Sset_b0
        rw [hv] at this
        have e : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ((2 : ℝ) • ![σ, 0]) = 2 * σ := by
          simp [dotProduct, Fin.sum_univ_two]
        rw [e, abs_mul, abs_two] at this
        have hs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
        rw [hs, mul_one, ← hv] at this
        exact this
    show ((aA σ - ![-σ, 0]) ⬝ᵥ thS φ σ) / sNorm Arch (aA σ - ![-σ, 0]) = φ / 2
    rw [hn, gap_hull φ σ hσ]
    have := sig_sq hσ
    simp [aA]
    linear_combination (φ / 2 - 1 / 4) * this

/-! ### The centered information-acquisition complexity -/

lemma arch_ae (n : Measure (Fin 2 → ℝ)) (h : n Archᶜ = 0) : ∀ᵐ a ∂n, a ∈ Arch := by
  rw [ae_iff]; exact h

lemma cost_ge_M11 (φ σ : ℝ) (hφ : 0 < φ) (hφ' : φ ≤ 1 / 8) (hσ : σ = 1 ∨ σ = -1) (n : Measure (Fin 2 → ℝ))
    [IsFiniteMeasure n] (hsupp : n Archᶜ = 0) :
    designMat n 1 1 ≤ ctrCost (thS φ σ) ![-σ, 0] n := by
  unfold designMat ctrCost
  simp only [of_apply]
  have hae := arch_ae n hsupp
  have hm1 : Continuous fun a : Fin 2 → ℝ => a 1 * a 1 :=
    (continuous_apply 1).mul (continuous_apply 1)
  have hm2 : Continuous fun a : Fin 2 → ℝ => (a - ![-σ, 0]) ⬝ᵥ thS φ σ :=
    (continuous_id.sub continuous_const).dotProduct continuous_const
  have hφ8 : φ ≤ 1 := by linarith
  apply integral_mono_ae
  · refine Integrable.of_bound hm1.measurable.aestronglyMeasurable 1 (hae.mono fun a ha => ?_)
    obtain ⟨x, hx, rfl⟩ := ha
    have e : (![x, (1 - x ^ 2) / 2] : Fin 2 → ℝ) 1 = (1 - x ^ 2) / 2 := rfl
    rw [Real.norm_eq_abs, e]
    have h0 : 0 ≤ (1 - x ^ 2) / 2 := by nlinarith [hx.1, hx.2]
    have h1 : (1 - x ^ 2) / 2 ≤ 1 / 2 := by nlinarith
    rw [abs_le]; constructor <;> nlinarith
  · refine Integrable.of_bound hm2.measurable.aestronglyMeasurable (φ + 1) (hae.mono fun a ha => ?_)
    obtain ⟨x, hx, rfl⟩ := ha
    have := gap_arch φ σ x hσ
    unfold aA at this
    rw [Real.norm_eq_abs, this]
    have h1 : 0 ≤ 1 + σ * x := by rcases hσ with rfl | rfl <;> linarith [hx.1, hx.2]
    have h1' : 1 + σ * x ≤ 2 := by rcases hσ with rfl | rfl <;> linarith [hx.1, hx.2]
    rw [abs_le]; constructor <;> nlinarith [hx.1, hx.2]
  · filter_upwards [hae] with a ha
    obtain ⟨x, hx, rfl⟩ := ha
    have := gap_arch φ σ x hσ
    unfold aA at this
    have e : (![x, (1 - x ^ 2) / 2] : Fin 2 → ℝ) 1 = (1 - x ^ 2) / 2 := rfl
    rw [this, e]
    have h1 : 0 ≤ 1 + σ * x := by rcases hσ with rfl | rfl <;> linarith [hx.1, hx.2]
    have hy0 : 0 ≤ (1 - x ^ 2) / 2 := by nlinarith [hx.1, hx.2]
    have hy1 : (1 - x ^ 2) / 2 ≤ 1 / 2 := by nlinarith
    nlinarith

lemma cstar_lower (φ σ : ℝ) (hφ : 0 < φ) (hφ' : φ ≤ 1 / 8) (hσ : σ = 1 ∨ σ = -1)
    (n : Measure (Fin 2 → ℝ)) (hn : IsCtrAlloc Arch (thS φ σ) ![-σ, 0] n) :
    128 / 25 ≤ ctrCost (thS φ σ) ![-σ, 0] n := by
  obtain ⟨hfin, hsupp, hpd, hc⟩ := hn
  set M := designMat n with hM
  have hu := hc (aA 0) (subset_convexHull ℝ _ (aA_mem (by norm_num)))
  have hg := gap_arch φ σ 0 hσ
  rw [hg] at hu
  have hcs := cs_fin_two_1 M hpd (aA 0 - ![-σ, 0])
  have hv1 : (aA 0 - ![-σ, 0]) 1 = 1 / 2 := by simp [aA]
  rw [hv1] at hcs
  have hM11 := (posDef_props M hpd).2.1
  have h1 : (1 / 2 : ℝ) ^ 2 ≤ M 1 1 * ((φ / 2 * (1 + σ * 0) + (1 - 0 ^ 2) / 4) ^ 2 / 2) :=
    hcs.trans (mul_le_mul_of_nonneg_left hu hM11.le)
  have h2 : (φ / 2 * (1 + σ * 0) + (1 - 0 ^ 2) / 4) ^ 2 ≤ 25 / 256 := by
    simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      mul_one]
    nlinarith
  have h3 : 128 / 25 ≤ M 1 1 := by nlinarith
  exact h3.trans (cost_ge_M11 φ σ hφ hφ' hσ n hsupp)

/-- the explicit allocation `32 δ_{a(0)} + (8/φ²) δ_{a*}` -/
noncomputable def nUp (φ σ : ℝ) : Measure (Fin 2 → ℝ) :=
  twoPt 32 (Real.toNNReal (8 / φ ^ 2)) (aA 0) ![-σ, 0]

lemma nUp_alloc (φ σ : ℝ) (hφ : 0 < φ) (hφ' : φ ≤ 1 / 8) (hσ : σ = 1 ∨ σ = -1) :
    IsCtrAlloc Arch (thS φ σ) ![-σ, 0] (nUp φ σ) ∧ ctrCost (thS φ σ) ![-σ, 0] (nUp φ σ) ≤ 10 := by
  have hη : ((Real.toNNReal (8 / φ ^ 2) : ℝ≥0) : ℝ) = 8 / φ ^ 2 :=
    Real.coe_toNNReal _ (by positivity)
  have h32 : ((32 : ℝ≥0) : ℝ) = 32 := by norm_num
  have hs2 := sig_sq hσ
  have hM : ∀ i j, designMat (nUp φ σ) i j =
      32 * (aA 0 i * aA 0 j) + 8 / φ ^ 2 * ((![-σ, 0] : Fin 2 → ℝ) i * (![-σ, 0] : Fin 2 → ℝ) j) := by
    intro i j; unfold nUp; rw [designMat_twoPt, hη, h32]
  have h00 : designMat (nUp φ σ) 0 0 = 8 / φ ^ 2 := by
    rw [hM]; simp [aA]; rw [show σ * σ = 1 by nlinarith [hs2]]; ring
  have h01 : designMat (nUp φ σ) 0 1 = 0 := by rw [hM]; simp [aA]
  have h10 : designMat (nUp φ σ) 1 0 = 0 := by rw [hM]; simp [aA]
  have h11 : designMat (nUp φ σ) 1 1 = 8 := by rw [hM]; simp [aA]; norm_num
  have hηpos : 0 < 8 / φ ^ 2 := div_pos (by norm_num) (pow_pos hφ 2)
  have hdetpos : 0 < 8 / φ ^ 2 * 8 - (0 : ℝ) ^ 2 := by nlinarith
  have hpd : (designMat (nUp φ σ)).PosDef := by
    apply posDef_fin_two_of
    · rw [h10, h01]
    · rw [h00]; exact hηpos
    · rw [h00, h01, h11]; exact hdetpos
  refine ⟨⟨by unfold nUp; infer_instance, ?_, hpd, ?_⟩, ?_⟩
  · unfold nUp; exact twoPt_compl _ _ _ _ _ (aA_mem (by norm_num)) (astar_mem hσ)
  · intro u hu
    rw [quad_inv_fin_two _ (by rw [h10, h01]) (by rw [h00, h01, h11]; exact hdetpos.ne'), h00, h01, h11,
      gap_hull φ σ hσ u]
    obtain ⟨hw, hy, _⟩ := hull_coords σ hσ u hu
    have e0 : (u - ![-σ, 0]) 0 = u 0 + σ := by simp
    have e1 : (u - ![-σ, 0]) 1 = u 1 := by simp
    rw [e0, e1]
    have hw2 : (u 0 + σ) ^ 2 = (1 + σ * u 0) ^ 2 := by linear_combination (1 - u 0 ^ 2) * hs2
    rw [div_le_div_iff₀ hdetpos (by norm_num)]
    have hφ2 : 0 < φ ^ 2 := by positivity
    rw [hw2]
    field_simp
    nlinarith [mul_nonneg hw hy, mul_nonneg (mul_nonneg hw hy) hφ.le, sq_nonneg (1 + σ * u 0),
      sq_nonneg (u 1)]
  · unfold nUp
    rw [ctrCost_twoPt, hη, h32, sub_self, zero_dotProduct, mul_zero, add_zero]
    have := gap_arch φ σ 0 hσ
    rw [this]; simp; linarith

lemma cstar_bounds (φ : ℝ) (hφ : 0 < φ) (hφ' : φ ≤ 1 / 8) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    128 / 25 ≤ cstarCtr Arch (thS φ σ) ![-σ, 0] ∧ cstarCtr Arch (thS φ σ) ![-σ, 0] ≤ 10 := by
  obtain ⟨hn, hcost⟩ := nUp_alloc φ σ hφ hφ' hσ
  unfold cstarCtr
  constructor
  · exact le_csInf ⟨ctrCost (thS φ σ) ![-σ, 0] (nUp φ σ), nUp φ σ, hn, rfl⟩ (by
      rintro _ ⟨n, hn', rfl⟩
      exact cstar_lower φ σ hφ hφ' hσ n hn')
  · have hbdd : BddBelow (ctrCost (thS φ σ) ![-σ, 0] '' {n | IsCtrAlloc Arch (thS φ σ) ![-σ, 0] n}) :=
      ⟨128 / 25, by rintro _ ⟨n, hn', rfl⟩; exact cstar_lower φ σ hφ hφ' hσ n hn'⟩
    exact (csInf_le hbdd ⟨nUp φ σ, hn, rfl⟩).trans hcost

end LB32b

-- ===== LB/T32bR =====

/-! # Theorem 3.2(ii): the corruption lower bound on the arch (Appendix H.2) -/

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm IAFTRL
open scoped ENNReal Pointwise NNReal

namespace LB32b

open LBC

/-- the actual loss vector of round `t`: `(σε, 1/2)` before `m`, then `θ_σ` -/
noncomputable def vv (φ σ ε : ℝ) (m t : ℕ) : Fin 2 → ℝ :=
  if t < m then ![σ * ε, 1 / 2] else ![σ * φ / 2, 1 / 2]

lemma vv_dot (φ σ ε : ℝ) (m t : ℕ) (x : ℝ) :
    aA x ⬝ᵥ vv φ σ ε m t = (if t < m then σ * ε else σ * φ / 2) * x + (1 - x ^ 2) / 4 := by
  unfold vv aA; split_ifs <;> rw [dot2] <;> ring

lemma vv_bound (φ σ ε : ℝ) (m t : ℕ) (hσ : σ = 1 ∨ σ = -1) (hε : 0 ≤ ε) (hε8 : ε ≤ 1 / 8)
    (hφ : 0 < φ) (hφ' : φ ≤ 1 / 8) (a : Fin 2 → ℝ) (ha : a ∈ Arch) : |a ⬝ᵥ vv φ σ ε m t| ≤ 1 / 2 := by
  obtain ⟨x, hx, rfl⟩ := ha
  have e := vv_dot φ σ ε m t x
  unfold aA at e
  rw [e]
  have hx2 : 0 ≤ (1 - x ^ 2) / 4 ∧ (1 - x ^ 2) / 4 ≤ 1 / 4 := ⟨by nlinarith [hx.1, hx.2], by nlinarith⟩
  have hc : |(if t < m then σ * ε else σ * φ / 2)| ≤ 1 / 8 := by
    have hφ2 : |φ / 2| = φ / 2 := abs_of_pos (by positivity)
    have hφ3 : |-φ / 2| = φ / 2 := by rw [neg_div, abs_neg, hφ2]
    split_ifs <;> rcases hσ with rfl | rfl <;> simp [abs_of_nonneg hε, hφ2, hφ3] <;>
      linarith
  have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
  have h1 : |(if t < m then σ * ε else σ * φ / 2) * x| ≤ 1 / 8 := by
    rw [abs_mul]; nlinarith [abs_nonneg x, abs_nonneg (if t < m then σ * ε else σ * φ / 2)]
  calc |(if t < m then σ * ε else σ * φ / 2) * x + (1 - x ^ 2) / 4|
      ≤ |(if t < m then σ * ε else σ * φ / 2) * x| + |(1 - x ^ 2) / 4| := abs_add_le _ _
    _ ≤ 1 / 2 := by rw [abs_of_nonneg hx2.1]; linarith

lemma setNorm_le (𝒜 : Set (Fin 2 → ℝ)) (z : Fin 2 → ℝ) (B : ℝ) (hne : 𝒜.Nonempty)
    (h : ∀ a ∈ 𝒜, |a ⬝ᵥ z| ≤ B) : setNorm 𝒜 z ≤ B := by
  unfold setNorm
  exact csSup_le (hne.image _) (by rintro _ ⟨a, ha, rfl⟩; exact h a ha)

lemma env_corrupted (φ σ ε C : ℝ) (m T : ℕ) (hσ : σ = 1 ∨ σ = -1) (hε : 0 ≤ ε)
    (hεφ : ε ≤ φ) (hφ : 0 < φ) (hφ' : φ ≤ 1 / 8) (hmT : m ≤ T) (hmC : (m : ℝ) * (φ / 2) ≤ C) :
    (mkEnv (vv φ σ ε m)).IsCorruptedStoch Arch (thS φ σ) C T := by
  have hε8 : ε ≤ 1 / 8 := by linarith
  have hs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply setNorm_le _ _ _ Arch_nonempty
    rintro a ⟨x, hx, rfl⟩
    have e : (![x, (1 - x ^ 2) / 2] : Fin 2 → ℝ) ⬝ᵥ thS φ σ = σ * φ / 2 * x + (1 - x ^ 2) / 4 := by
      unfold thS; rw [dot2]; ring
    rw [e]
    have hx2 : 0 ≤ (1 - x ^ 2) / 4 ∧ (1 - x ^ 2) / 4 ≤ 1 / 4 := ⟨by nlinarith [hx.1, hx.2], by nlinarith⟩
    have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
    have h1 : |σ * φ / 2 * x| ≤ 1 / 16 := by
      rw [abs_mul, mul_div_assoc, abs_mul, hs, one_mul, abs_of_pos (by positivity)]
      nlinarith [abs_nonneg x]
    calc |σ * φ / 2 * x + (1 - x ^ 2) / 4| ≤ |σ * φ / 2 * x| + |(1 - x ^ 2) / 4| := abs_add_le _ _
      _ ≤ 1 := by rw [abs_of_nonneg hx2.1]; linarith
  · intro t _
    exact setNorm_le _ _ _ Arch_nonempty fun a ha =>
      (vv_bound φ σ ε m t hσ hε hε8 hφ hφ' a ha).trans (by norm_num)
  · intro t _ a ha
    exact mkEnv_feedback _ t a ((vv_bound φ σ ε m t hσ hε hε8 hφ hφ' a ha).trans (by norm_num))
  · have hterm : ∀ t ∈ Finset.range T, setNorm Arch ((mkEnv (vv φ σ ε m)).θs t - thS φ σ) ≤
        if t < m then φ / 2 else 0 := by
      intro t _
      show setNorm _ (vv φ σ ε m t - thS φ σ) ≤ _
      apply setNorm_le _ _ _ Arch_nonempty
      rintro a ⟨x, hx, rfl⟩
      have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
      unfold vv thS
      split_ifs
      · have e : (![σ * ε, 1 / 2] - ![σ * φ / 2, 1 / 2] : Fin 2 → ℝ) = ![σ * (ε - φ / 2), 0] := by
          funext i; fin_cases i <;> simp <;> ring
        rw [e, dot2, mul_zero, add_zero, abs_mul, abs_mul, hs, one_mul]
        have : |ε - φ / 2| ≤ φ / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
        nlinarith [abs_nonneg x, abs_nonneg (ε - φ / 2)]
      · rw [sub_self, dotProduct_zero, abs_zero]
    refine (Finset.sum_le_sum hterm).trans (le_of_eq_of_le ?_ hmC)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have : (Finset.range T).filter (fun t => t < m) = Finset.range m := by
      ext t; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.card_range]

/-- the event `x_t ≥ 0` -/
def Ev (T : ℕ) (t : Fin T) : Set (LinearBanditHistory 2 T) := {h | (h t).1 ∈ {a | 0 ≤ a 0}}

lemma Ev_meas (T : ℕ) (t : Fin T) : MeasurableSet (Ev T t) :=
  (measurableSet_le measurable_const (measurable_pi_apply 0)).preimage (measurable_pi_apply t).fst

/-- gaps against `a* = −σe₁` under the actual loss vector -/
lemma gap_vv (φ σ ε : ℝ) (m t : ℕ) (hσ : σ = 1 ∨ σ = -1) (x : ℝ) :
    (aA x - ![-σ, 0]) ⬝ᵥ vv φ σ ε m t =
      (if t < m then ε else φ / 2) * (1 + σ * x) + (1 - x ^ 2) / 4 := by
  have hs2 := sig_sq hσ
  unfold vv aA
  split_ifs with h
  · rw [sub_dotProduct, dot2, dot2]; linear_combination ε * hs2
  · rw [sub_dotProduct, dot2, dot2]; linear_combination (φ / 2) * hs2

lemma gap_vv_nonneg (φ σ ε : ℝ) (m t : ℕ) (hσ : σ = 1 ∨ σ = -1) (hε : 0 ≤ ε) (hφ : 0 < φ)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : 0 ≤ (aA x - ![-σ, 0]) ⬝ᵥ vv φ σ ε m t := by
  rw [gap_vv φ σ ε m t hσ x]
  have h1 : 0 ≤ 1 + σ * x := by rcases hσ with rfl | rfl <;> linarith [hx.1, hx.2]
  have h2 : 0 ≤ (1 - x ^ 2) / 4 := by nlinarith [hx.1, hx.2]
  have h3 : 0 ≤ (if t < m then ε else φ / 2) := by split_ifs <;> linarith
  positivity

lemma gap_vv_wrong (φ σ ε : ℝ) (m t : ℕ) (ht : t < m) (hσ : σ = 1 ∨ σ = -1) (hε : 0 ≤ ε)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hsx : 0 ≤ σ * x) :
    ε ≤ (aA x - ![-σ, 0]) ⬝ᵥ vv φ σ ε m t := by
  rw [gap_vv φ σ ε m t hσ x, if_pos ht]
  have h2 : 0 ≤ (1 - x ^ 2) / 4 := by nlinarith [hx.1, hx.2]
  nlinarith

set_option maxHeartbeats 1000000 in
theorem lower_bound (φ : ℝ) (hφ : 0 < φ) (hφ' : φ ≤ 1 / 8) (C : ℝ) (hC : φ⁻¹ ≤ C) (T : ℕ)
    (hT : ⌈(φ ^ 2)⁻¹⌉₊ ≤ T) :
    ∃ E : ℝ → LinEnv 2,
      (∀ σ : ℝ, (σ = 1 ∨ σ = -1) → (E σ).IsCorruptedStoch Arch (thS φ σ) C T) ∧
      ∀ π : LinearBanditPolicy 2, IsSupportedLinearPolicy Arch π →
        (1 / 32) * min (Real.sqrt T) (Real.sqrt (C / φ)) ≤
          max ((E 1).regret Arch π T) ((E (-1)).regret Arch π T) := by
  set m : ℕ := min T ⌊2 * C / φ⌋₊ with hm
  have hTr : (φ ^ 2)⁻¹ ≤ (T : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hT)
  have hCφ : (φ ^ 2)⁻¹ ≤ C / φ := by
    rw [show (φ ^ 2)⁻¹ = φ⁻¹ / φ by field_simp]
    exact div_le_div_of_nonneg_right hC hφ.le
  have hfl : C / φ ≤ (⌊2 * C / φ⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (2 * C / φ)
    have e : 2 * C / φ = 2 * (C / φ) := by ring
    have h1 : (1 : ℝ) ≤ (φ ^ 2)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by positivity)]; nlinarith
    linarith
  have hCpos : 0 < C := lt_of_lt_of_le (inv_pos.mpr hφ) hC
  have hfl' : (⌊2 * C / φ⌋₊ : ℝ) ≤ 2 * C / φ := Nat.floor_le (by positivity)
  have hmT : m ≤ T := min_le_left _ _
  have hmr : ((m : ℕ) : ℝ) = min (T : ℝ) (⌊2 * C / φ⌋₊ : ℝ) := by rw [hm]; push_cast; rfl
  have hm_low : (φ ^ 2)⁻¹ ≤ (m : ℝ) := by rw [hmr]; exact le_min hTr (hCφ.trans hfl)
  have hm_min : min (T : ℝ) (C / φ) ≤ (m : ℝ) := by
    rw [hmr]; exact min_le_min le_rfl hfl
  have hmC : (m : ℝ) * (φ / 2) ≤ C := by
    have : (m : ℝ) ≤ 2 * C / φ := by rw [hmr]; exact (min_le_right _ _).trans hfl'
    calc (m : ℝ) * (φ / 2) ≤ 2 * C / φ * (φ / 2) := by gcongr
      _ = C := by field_simp
  have hm1 : (1 : ℝ) ≤ m := by
    have : (1 : ℝ) ≤ (φ ^ 2)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by positivity)]; nlinarith
    linarith
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
  set ε : ℝ := 1 / (8 * Real.sqrt m) with hε
  have hεpos : 0 < ε := by positivity
  have hsqm : φ⁻¹ ≤ Real.sqrt m := by
    rw [show φ⁻¹ = Real.sqrt ((φ ^ 2)⁻¹) by
      rw [Real.sqrt_inv, Real.sqrt_sq hφ.le]]
    exact Real.sqrt_le_sqrt hm_low
  have hεφ : ε ≤ φ / 8 := by
    rw [hε, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 1 ≤ φ * Real.sqrt m := by
      have := mul_le_mul_of_nonneg_left hsqm hφ.le
      rwa [mul_inv_cancel₀ hφ.ne'] at this
    linarith
  have hε8 : ε ≤ 1 / 8 := by linarith
  have hmε : (m : ℝ) * ε ^ 2 = 1 / 64 := by
    rw [hε, div_pow, mul_pow, Real.sq_sqrt (by linarith)]
    field_simp
    ring
  refine ⟨fun σ => mkEnv (vv φ σ ε m), fun σ hσ => env_corrupted φ σ ε C m T hσ hεpos.le
    (by linarith) hφ hφ' hmT hmC, fun π hπ => ?_⟩
  have hA := Arch_meas
  have hθb : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ t < T, ∀ a ∈ Arch,
      |a ⬝ᵥ (mkEnv (vv φ σ ε m)).θs t| ≤ 1 :=
    fun σ hσ t _ a ha => (vv_bound φ σ ε m t hσ hεpos.le hε8 hφ hφ' a ha).trans (by norm_num)
  -- regret of `+`
  have hplus : ∑ t : Fin T, (if (t : ℕ) < m then
      ε * ((mkEnv (vv φ 1 ε m)).histMeasure π T (Ev T t)).toReal else 0) ≤
      (mkEnv (vv φ 1 ε m)).regret Arch π T := by
    let c : Fin T → LinearBanditHistory 2 T → ℝ := fun t h =>
      if (t : ℕ) < m then ε * (Ev T t).indicator 1 h else 0
    have hcm : ∀ t, Measurable (c t) := by
      intro t; simp only [c]; split_ifs
      · exact (measurable_one.indicator (Ev_meas T t)).const_mul _
      · exact measurable_const
    have hcb : ∀ t h, |c t h| ≤ ε := by
      intro t h; simp only [c]; split_ifs
      · unfold Set.indicator; split_ifs <;> simp [abs_of_pos hεpos, hεpos.le]
      · simp [hεpos.le]
    have key := regret_ge (mkEnv (vv φ 1 ε m)) π Arch hA hπ T ![-1, 0] (astar_mem (Or.inl rfl))
      (hθb 1 (Or.inl rfl)) c hcm ε hcb (by
        intro h hh
        apply Finset.sum_le_sum; intro t _
        obtain ⟨x, hx, hxt⟩ := hh t
        have hxt' : (h t).1 = aA x := hxt
        show c t h ≤ ((h t).1 - ![-1, 0]) ⬝ᵥ vv φ 1 ε m t
        rw [hxt']
        simp only [c]
        split_ifs with htm
        · by_cases he : h ∈ Ev T t
          · rw [Set.indicator_of_mem he, Pi.one_apply, mul_one]
            have : 0 ≤ x := by
              have h0 : 0 ≤ (h t).1 0 := he
              rw [hxt'] at h0; simpa [aA] using h0
            exact gap_vv_wrong φ 1 ε m t htm (Or.inl rfl) hεpos.le x hx (by linarith)
          · rw [Set.indicator_of_notMem he, mul_zero]
            exact gap_vv_nonneg φ 1 ε m t (Or.inl rfl) hεpos.le hφ x hx
        · exact gap_vv_nonneg φ 1 ε m t (Or.inl rfl) hεpos.le hφ x hx)
    refine le_trans (le_of_eq ?_) key
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [c]
    split_ifs
    · rw [integral_const_mul, integral_indicator_one (Ev_meas T t), measureReal_def]
    · simp
  -- regret of `-`
  have hminus : ∑ t : Fin T, (if (t : ℕ) < m then
      ε * (1 - ((mkEnv (vv φ (-1) ε m)).histMeasure π T (Ev T t)).toReal) else 0) ≤
      (mkEnv (vv φ (-1) ε m)).regret Arch π T := by
    let c : Fin T → LinearBanditHistory 2 T → ℝ := fun t h =>
      if (t : ℕ) < m then ε * (1 - (Ev T t).indicator 1 h) else 0
    have hcm : ∀ t, Measurable (c t) := by
      intro t; simp only [c]; split_ifs
      · exact (measurable_const.sub (measurable_one.indicator (Ev_meas T t))).const_mul _
      · exact measurable_const
    have hcb : ∀ t h, |c t h| ≤ ε := by
      intro t h; simp only [c]; split_ifs
      · unfold Set.indicator; split_ifs <;> simp [abs_of_pos hεpos, hεpos.le]
      · simp [hεpos.le]
    have key := regret_ge (mkEnv (vv φ (-1) ε m)) π Arch hA hπ T ![-(-1), 0]
      (astar_mem (Or.inr rfl)) (hθb (-1) (Or.inr rfl)) c hcm ε hcb (by
        intro h hh
        apply Finset.sum_le_sum; intro t _
        obtain ⟨x, hx, hxt⟩ := hh t
        have hxt' : (h t).1 = aA x := hxt
        show c t h ≤ ((h t).1 - ![-(-1), 0]) ⬝ᵥ vv φ (-1) ε m t
        rw [hxt']
        simp only [c]
        split_ifs with htm
        · by_cases he : h ∈ Ev T t
          · rw [Set.indicator_of_mem he, Pi.one_apply, sub_self, mul_zero]
            exact gap_vv_nonneg φ (-1) ε m t (Or.inr rfl) hεpos.le hφ x hx
          · rw [Set.indicator_of_notMem he, sub_zero, mul_one]
            have : x < 0 := by
              have h0 : ¬ (0 ≤ (h t).1 0) := he
              rw [hxt'] at h0; simp [aA] at h0; linarith
            exact gap_vv_wrong φ (-1) ε m t htm (Or.inr rfl) hεpos.le x hx (by linarith)
        · exact gap_vv_nonneg φ (-1) ε m t (Or.inr rfl) hεpos.le hφ x hx)
    refine le_trans (le_of_eq ?_) key
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [c]
    split_ifs
    · have hi : Integrable ((Ev T t).indicator (1 : LinearBanditHistory 2 T → ℝ))
          ((mkEnv (vv φ (-1) ε m)).histMeasure π T) :=
        (integrable_const (1 : ℝ)).indicator (Ev_meas T t)
      rw [integral_const_mul, integral_sub (f := fun _ => (1 : ℝ)) (integrable_const _) hi,
        integral_const, integral_indicator_one (Ev_meas T t)]
      simp [measureReal_def]
    · simp
  -- testing on the first `m` rounds
  have htv : ∀ t : Fin T, (t : ℕ) < m →
      ((mkEnv (vv φ (-1) ε m)).histMeasure π T (Ev T t)).toReal ≤
        ((mkEnv (vv φ 1 ε m)).histMeasure π T (Ev T t)).toReal + 1 / 2 := by
    intro t ht
    have hW : MeasurableSet {a : Fin 2 → ℝ | 0 ≤ a 0} :=
      measurableSet_le measurable_const (measurable_pi_apply 0)
    have e1 := marg_event (mkEnv (vv φ (-1) ε m)) π m T hmT t ht _ hW
    have e2 := marg_event (mkEnv (vv φ 1 ε m)) π m T hmT t ht _ hW
    have hev : Ev T t = {h | (h ⟨(t : ℕ), by omega⟩).1 ∈ {a : Fin 2 → ℝ | 0 ≤ a 0}} := rfl
    rw [hev, e1, e2]
    refine tv_event (vv φ 1 ε m) (vv φ (-1) ε m) Arch π hπ m (4 * ε ^ 2) (by positivity)
      (fun t _ a ha => vv_bound φ 1 ε m t (Or.inl rfl) hεpos.le hε8 hφ hφ' a ha)
      (fun t _ a ha => vv_bound φ (-1) ε m t (Or.inr rfl) hεpos.le hε8 hφ hφ' a ha) ?_
      (by nlinarith) _ (hW.preimage (measurable_pi_apply _).fst)
    intro t' ht' a ha
    obtain ⟨x, hx, rfl⟩ := ha
    have e1 := vv_dot φ 1 ε m t' x
    have e2 := vv_dot φ (-1) ε m t' x
    unfold aA at e1 e2
    rw [e1, e2, if_pos ht', if_pos ht']
    have : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    nlinarith [sq_nonneg ε]
  have hsum : ε * m / 2 ≤ (mkEnv (vv φ 1 ε m)).regret Arch π T +
      (mkEnv (vv φ (-1) ε m)).regret Arch π T := by
    refine le_trans ?_ (add_le_add hplus hminus)
    rw [← Finset.sum_add_distrib]
    have hcount : ∑ t : Fin T, (if (t : ℕ) < m then ε / 2 else 0) = ε * m / 2 := by
      rw [Fin.sum_univ_eq_sum_range (fun t => if t < m then ε / 2 else 0) T, Finset.sum_ite,
        Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have : (Finset.range T).filter (fun t => t < m) = Finset.range m := by
        ext t; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [this, Finset.card_range]; ring
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
  have hsqrt : min (Real.sqrt T) (Real.sqrt (C / φ)) ≤ Real.sqrt m := by
    have : min (Real.sqrt T) (Real.sqrt (C / φ)) = Real.sqrt (min (T : ℝ) (C / φ)) := by
      rcases le_total (T : ℝ) (C / φ) with h | h
      · rw [min_eq_left h, min_eq_left (Real.sqrt_le_sqrt h)]
      · rw [min_eq_right h, min_eq_right (Real.sqrt_le_sqrt h)]
    rw [this]
    exact Real.sqrt_le_sqrt hm_min
  have hmax := add_le_add (le_max_left ((mkEnv (vv φ 1 ε m)).regret Arch π T)
    ((mkEnv (vv φ (-1) ε m)).regret Arch π T))
    (le_max_right ((mkEnv (vv φ 1 ε m)).regret Arch π T)
    ((mkEnv (vv φ (-1) ε m)).regret Arch π T))
  show (1 / 32) * min (Real.sqrt T) (Real.sqrt (C / φ)) ≤
    max ((mkEnv (vv φ 1 ε m)).regret Arch π T) ((mkEnv (vv φ (-1) ε m)).regret Arch π T)
  linarith

end LB32b

namespace IAFTRL

theorem theorem_3_2_ii_proved (φ : ℝ) (hφ : 0 < φ) (hφ' : φ ≤ 1 / 8) :
    let arch : Set (Fin 2 → ℝ) := {a | ∃ x ∈ Set.Icc (-1 : ℝ) 1, a = ![x, (1 - x ^ 2) / 2]}
    let θ : ℝ → Fin 2 → ℝ := fun σ => ![σ * φ / 2, 1 / 2]
    (∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ![-σ, 0] ∈ arch ∧ (∀ a ∈ arch, a ≠ ![-σ, 0] → ![-σ, 0] ⬝ᵥ θ σ < a ⬝ᵥ θ σ) ∧
      φ / 6 ≤ sharpModulus arch (θ σ) ![-σ, 0] ∧ sharpModulus arch (θ σ) ![-σ, 0] ≤ φ / 2 ∧
      128 / 25 ≤ cstarCtr arch (θ σ) ![-σ, 0] ∧ cstarCtr arch (θ σ) ![-σ, 0] ≤ 10) ∧
    ∀ C : ℝ, φ⁻¹ ≤ C → ∀ T : ℕ, ⌈(φ ^ 2)⁻¹⌉₊ ≤ T →
      ∃ E : ℝ → LinEnv 2,
        (∀ σ : ℝ, (σ = 1 ∨ σ = -1) → (E σ).IsCorruptedStoch arch (θ σ) C T) ∧
        ∀ π : LinearBanditPolicy 2, IsSupportedLinearPolicy arch π →
          (1 / 32) * min (Real.sqrt T) (Real.sqrt (C / φ)) ≤
            max ((E 1).regret arch π T) ((E (-1)).regret arch π T) := by
  intro arch θ
  refine ⟨fun σ hσ => ?_, fun C hC T hT => LB32b.lower_bound φ hφ hφ' C hC T hT⟩
  obtain ⟨h1, h2⟩ := LB32b.sharp_bounds φ hφ hφ' σ hσ
  obtain ⟨h3, h4⟩ := LB32b.cstar_bounds φ hφ hφ' σ hσ
  exact ⟨LB32b.astar_mem hσ, LB32b.unique_opt φ hφ σ hσ, h1, h2, h3, h4⟩

end IAFTRL

theorem _root_.solution : type_of% @IAFTRL.theorem_3_2_ii_proved := @IAFTRL.theorem_3_2_ii_proved
