-- Prove2me | solution 1 for HighDimStat.NonparametricLS.local_gaussian_complexity_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:34:23.203554+00:00
-- url     : https://prove2.me/submissions/97abed16-353f-4e88-bf0f-d2369d715831

import Mathlib
import Definitions.Def_HighDimStat_NonparametricLS_Core
import Definitions.Def_HighDimStat_TailBounds_IsSubGaussian
import Definitions.Def_HighDimStat_TailBounds_IsLLipschitz
import Theorems.Thm_HighDimStat_TailBounds_lipschitz_gaussian_concentration

namespace HighDimStat.NonparametricLS

open MeasureTheory ProbabilityTheory
open HighDimStat.TailBounds

set_option linter.unusedSectionVars false

private lemma prob_real_univ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    P.real Set.univ = 1 := by
  change (P Set.univ).toReal = 1
  rw [measure_univ]
  simp

private lemma mean_eq_zero_of_iid {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    {w : Fin n → Ω → ℝ} (hw : IsIIDStdGaussian P w) (i : Fin n) :
    ∫ ω, w i ω ∂P = 0 := by
  have hm : AEMeasurable (w i) P := (hw.1 i).aemeasurable
  have h_map : ∫ y, y ∂(Measure.map (w i) P) = ∫ ω, w i ω ∂P :=
    integral_map hm stronglyMeasurable_id.aestronglyMeasurable
  rw [← h_map, hw.2.2 i]
  exact integral_id_gaussianReal

private lemma sq_integral_eq_one_of_iid {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    {w : Fin n → Ω → ℝ} (hw : IsIIDStdGaussian P w) (i : Fin n) :
    ∫ ω, (w i ω) ^ 2 ∂P = 1 := by
  have hm : AEMeasurable (w i) P := (hw.1 i).aemeasurable
  have h_map : ∫ y, y ^ 2 ∂(Measure.map (w i) P) = ∫ ω, (w i ω) ^ 2 ∂P :=
    integral_map hm (continuous_pow 2).stronglyMeasurable.aestronglyMeasurable
  rw [← h_map, hw.2.2 i]
  have h_var := variance_eq_integral (aemeasurable_id' (μ := gaussianReal 0 1))
  rw [integral_id_gaussianReal] at h_var
  simp only [sub_zero] at h_var
  rw [← h_var]
  have h_v := variance_id_gaussianReal (μ := 0) (v := 1)
  exact_mod_cast h_v

private lemma cov_eq_zero_of_iid {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    {w : Fin n → Ω → ℝ} (hw : IsIIDStdGaussian P w) {i j : Fin n} (hij : i ≠ j) :
    ∫ ω, w i ω * w j ω ∂P = 0 := by
  have hindep : IndepFun (w i) (w j) P := hw.2.1.indepFun hij
  have h_mul := hindep.integral_mul_eq_mul_integral (hw.1 i).aestronglyMeasurable (hw.1 j).aestronglyMeasurable
  have h_mean_i := mean_eq_zero_of_iid P hw i
  have h_mean_j := mean_eq_zero_of_iid P hw j
  exact (show (fun ω => w i ω * w j ω) = w i * w j from rfl) ▸
    (h_mul.trans (by rw [h_mean_i, h_mean_j, mul_zero]))

private lemma nonempty_slice {X : Type*} {n : ℕ} (x : Fin n → X) (H : Set (X → ℝ))
    (hStar : IsStarShaped H) (hH : H.Nonempty) (δn : ℝ) (hδn : 0 < δn) :
    Nonempty {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn} := by
  rcases hH with ⟨h0, hh0⟩
  have h_zero_mem : (fun _ => (0 : ℝ)) ∈ H := by
    have h_sc := hStar h0 hh0 0 ⟨le_rfl, zero_le_one⟩
    have : (fun z => (0 : ℝ) * h0 z) = fun _ => 0 := by
      ext z; ring
    rwa [this] at h_sc
  have h_norm_zero : empiricalNorm x (fun _ => 0) = 0 := by
    dsimp [empiricalNorm, empiricalNormSq]
    simp
  have h_zero_S : (fun _ => (0 : ℝ)) ∈ H ∧ empiricalNorm x (fun _ => 0) ≤ δn :=
    ⟨h_zero_mem, by rw [h_norm_zero]; exact le_of_lt hδn⟩
  exact ⟨⟨fun _ => 0, h_zero_S⟩⟩

private lemma norm_sq_eq {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) : ∑ i, (z.ofLp i) ^ 2 = ‖z‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  have h_term : ∀ i, ‖z.ofLp i‖ ^ 2 = (z.ofLp i) ^ 2 := by
    intro i
    rw [Real.norm_eq_abs, sq_abs]
  simp_rw [h_term]
  have h_sum_nonneg : 0 ≤ ∑ i, (z.ofLp i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [Real.sq_sqrt h_sum_nonneg]

private lemma abs_inner_div_n_le {X : Type*} {n : ℕ} (hn : 0 < n) (x : Fin n → X) (H : Set (X → ℝ))
    (δn : ℝ) (hδn : 0 ≤ δn) (z : EuclideanSpace ℝ (Fin n))
    (h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn}) :
    |(∑ i, z.ofLp i * h.1 (x i)) / (n : ℝ)| ≤ (δn / Real.sqrt n) * ‖z‖ := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h_norm : empiricalNorm x h.1 ≤ δn := h.2.2
  have h_norm_sq_nonneg : 0 ≤ empiricalNormSq x h.1 := by
    dsimp [empiricalNormSq]
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hn_nonneg
  have h_norm_sq_le : empiricalNormSq x h.1 ≤ δn ^ 2 := by
    have h1 : Real.sqrt (empiricalNormSq x h.1) ≤ δn := h_norm
    have h2 : (Real.sqrt (empiricalNormSq x h.1)) ^ 2 ≤ δn ^ 2 := by
      have : 0 ≤ Real.sqrt (empiricalNormSq x h.1) := Real.sqrt_nonneg _
      nlinarith
    rwa [Real.sq_sqrt h_norm_sq_nonneg] at h2
  have h_sum_sq_le : ∑ i, (h.1 (x i)) ^ 2 ≤ ↑n * δn ^ 2 := by
    calc
      ∑ i, (h.1 (x i)) ^ 2 = ↑n * ((∑ i, (h.1 (x i)) ^ 2) / ↑n) := by
        rw [mul_div_cancel₀ _ (ne_of_gt hn_pos)]
      _ = ↑n * empiricalNormSq x h.1 := rfl
      _ ≤ ↑n * δn ^ 2 := mul_le_mul_of_nonneg_left h_norm_sq_le hn_nonneg
  have h_cs : (∑ i, z.ofLp i * h.1 (x i)) ^ 2 ≤ (∑ i, (z.ofLp i) ^ 2) * (∑ i, (h.1 (x i)) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => z.ofLp i) (fun i => h.1 (x i))
  have h_bound : (∑ i, z.ofLp i * h.1 (x i)) ^ 2 ≤ ‖z‖ ^ 2 * (↑n * δn ^ 2) := by
    rw [norm_sq_eq] at h_cs
    exact le_trans h_cs (mul_le_mul_of_nonneg_left h_sum_sq_le (sq_nonneg ‖z‖))
  have h_abs : |∑ i, z.ofLp i * h.1 (x i)| ≤ Real.sqrt (‖z‖ ^ 2 * (↑n * δn ^ 2)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h_bound
  have h_sqrt_prod : Real.sqrt (‖z‖ ^ 2 * (↑n * δn ^ 2)) = ‖z‖ * (Real.sqrt n * δn) := by
    rw [Real.sqrt_mul (sq_nonneg ‖z‖), Real.sqrt_sq (norm_nonneg z)]
    have h_prod2 : Real.sqrt (↑n * δn ^ 2) = Real.sqrt n * Real.sqrt (δn ^ 2) :=
      Real.sqrt_mul hn_nonneg (δn ^ 2)
    rw [h_prod2, Real.sqrt_sq hδn]
  rw [h_sqrt_prod] at h_abs
  rw [abs_div, abs_of_pos hn_pos]
  have h_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have h1 : Real.sqrt n ≠ 0 := ne_of_gt h_sqrt_pos
  have h_den : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn_nonneg).symm
  have h_num : ‖z‖ * (Real.sqrt n * δn) = (‖z‖ * δn) * Real.sqrt n := by ring
  calc
    |∑ i, z.ofLp i * h.1 (x i)| / ↑n ≤ (‖z‖ * (Real.sqrt n * δn)) / ↑n :=
      div_le_div_of_nonneg_right h_abs hn_nonneg
    _ = (δn / Real.sqrt n) * ‖z‖ := by
      rw [h_num]
      conv_lhs =>
        arg 2
        rw [h_den]
      rw [mul_div_mul_right _ _ h1]
      ring

private lemma bddAbove_slice {X : Type*} {n : ℕ} (hn : 0 < n) (x : Fin n → X) (H : Set (X → ℝ))
    (δn : ℝ) (hδn : 0 ≤ δn) (z : EuclideanSpace ℝ (Fin n)) :
    BddAbove (Set.range (fun h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn} =>
      |(∑ i, z.ofLp i * h.1 (x i)) / (n : ℝ)|)) := by
  refine ⟨(δn / Real.sqrt n) * ‖z‖, ?_⟩
  rintro _ ⟨h, rfl⟩
  exact abs_inner_div_n_le hn x H δn hδn z h

private theorem f_is_lipschitz_slice {X : Type*} {n : ℕ} (hn : 0 < n) (x : Fin n → X)
    (H : Set (X → ℝ)) (hStar : IsStarShaped H) (hH : H.Nonempty) (δn : ℝ) (hδn : 0 < δn) :
    IsLLipschitz (fun z : EuclideanSpace ℝ (Fin n) =>
      ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn}, |(∑ i, z.ofLp i * h.1 (x i)) / (n : ℝ)|)
      (δn / Real.sqrt n) := by
  let S := {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn}
  let f := fun z : EuclideanSpace ℝ (Fin n) => ⨆ h : S, |(∑ i, z.ofLp i * h.1 (x i)) / (n : ℝ)|
  intro z y
  have hS_nonempty : Nonempty S := nonempty_slice x H hStar hH δn hδn
  have hδn_nonneg : 0 ≤ δn := le_of_lt hδn
  have h_bdd_y := bddAbove_slice hn x H δn hδn_nonneg y
  have h_bdd_z := bddAbove_slice hn x H δn hδn_nonneg z
  have h_sub (u v : EuclideanSpace ℝ (Fin n)) (h : S) :
      |(∑ i, u.ofLp i * h.1 (x i)) / (n : ℝ)| ≤
        f v + (δn / Real.sqrt n) * ‖u - v‖ := by
    have h_decomp : (∑ i, u.ofLp i * h.1 (x i)) / (n : ℝ) =
        (∑ i, v.ofLp i * h.1 (x i)) / (n : ℝ) + (∑ i, (u - v).ofLp i * h.1 (x i)) / (n : ℝ) := by
      have : ∀ i, u.ofLp i * h.1 (x i) = v.ofLp i * h.1 (x i) + (u - v).ofLp i * h.1 (x i) := by
        intro i
        rw [show (u - v).ofLp i = u.ofLp i - v.ofLp i from rfl]
        ring
      simp_rw [this, Finset.sum_add_distrib]
      ring
    rw [h_decomp]
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |(∑ i, v.ofLp i * h.1 (x i)) / (n : ℝ)| ≤ f v :=
      le_ciSup (bddAbove_slice hn x H δn hδn_nonneg v) h
    have h2 : |(∑ i, (u - v).ofLp i * h.1 (x i)) / (n : ℝ)| ≤ (δn / Real.sqrt n) * ‖u - v‖ :=
      abs_inner_div_n_le hn x H δn hδn_nonneg (u - v) h
    linarith
  have h_le_uv (u v : EuclideanSpace ℝ (Fin n)) :
      f u ≤ f v + (δn / Real.sqrt n) * ‖u - v‖ := by
    apply ciSup_le
    intro h
    exact h_sub u v h
  have h_diff1 : f z - f y ≤ (δn / Real.sqrt n) * ‖z - y‖ := by
    linarith [h_le_uv z y]
  have h_diff2 : f y - f z ≤ (δn / Real.sqrt n) * ‖z - y‖ := by
    have := h_le_uv y z
    rw [norm_sub_rev] at this
    linarith
  exact abs_sub_le_iff.mpr ⟨h_diff1, h_diff2⟩

private lemma continuous_of_IsLLipschitz {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (hLip : IsLLipschitz f L) : Continuous f := by
  rw [Metric.continuous_iff]
  intro x ε hε
  by_cases hL : 0 < L
  · refine ⟨ε / (2 * L), div_pos hε (mul_pos two_pos hL), ?_⟩
    intro y hy
    have h_le := hLip y x
    rw [Real.dist_eq]
    rw [← dist_eq_norm] at h_le
    calc
      |f y - f x| ≤ L * dist y x := h_le
      _ ≤ L * (ε / (2 * L)) := mul_le_mul_of_nonneg_left (le_of_lt hy) (le_of_lt hL)
      _ = ε / 2 := by
        have : L ≠ 0 := ne_of_gt hL
        field_simp
      _ < ε := half_lt_self hε
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y hy
    have h_le := hLip y x
    have h_nonneg : 0 ≤ ‖y - x‖ := norm_nonneg _
    have hL_nonpos : L ≤ 0 := not_lt.mp hL
    have h_zero : L * ‖y - x‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hL_nonpos h_nonneg
    have h_abs_nonneg : 0 ≤ |f y - f x| := abs_nonneg _
    have h_eq : |f y - f x| = 0 := le_antisymm (le_trans h_le h_zero) h_abs_nonneg
    rw [Real.dist_eq, h_eq]
    exact hε

private lemma subgaussian_one_sided_tail_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} {L : ℝ} (hL : 0 < L) (hSub : IsSubGaussian Y P L)
    (hYmean : ∫ ω, Y ω ∂P = 0) (s : ℝ) (hs : 0 ≤ s) :
    P.real {ω | s ≤ Y ω} ≤ Real.exp (-(s ^ 2) / (2 * L ^ 2)) := by
  let lam := s / L ^ 2
  have hlam_nonneg : 0 ≤ lam := div_nonneg hs (sq_nonneg L)
  let g : Ω → ℝ := fun ω => Real.exp (lam * Y ω)
  have hg_int : Integrable g P := by
    have h_int := hSub.2.1 lam
    dsimp [g]
    simp_rw [hYmean, sub_zero] at h_int
    exact h_int
  have hg_bound : ∫ ω, g ω ∂P ≤ Real.exp (L ^ 2 * lam ^ 2 / 2) := by
    have h_le := hSub.2.2 lam
    dsimp [g]
    simp_rw [hYmean, sub_zero] at h_le
    exact h_le
  have hg_nonneg : 0 ≤ᵐ[P] g := ae_of_all P (fun ω => (Real.exp_pos _).le)
  let c := Real.exp (lam * s)
  have hc_pos : 0 < c := Real.exp_pos _
  have h_subset : {ω | s ≤ Y ω} ⊆ {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (g ω)} := by
    intro ω hω
    dsimp [c, g]
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le]
    exact Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_left hω hlam_nonneg)
  have h_meas_le : P {ω | s ≤ Y ω} ≤ P {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (g ω)} :=
    measure_mono h_subset
  have h_markov : ENNReal.ofReal c * P {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (g ω)} ≤
      ∫⁻ ω, ENNReal.ofReal (g ω) ∂P := by
    have h_ae : AEMeasurable (fun ω => ENNReal.ofReal (g ω)) P :=
      (hg_int.aestronglyMeasurable.aemeasurable).ennreal_ofReal
    exact mul_meas_ge_le_lintegral₀ h_ae (ENNReal.ofReal c)
  have h_gcongr : ENNReal.ofReal c * P {ω | s ≤ Y ω} ≤
      ENNReal.ofReal c * P {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (g ω)} := by
    gcongr
  have h_le1 : ENNReal.ofReal c * P {ω | s ≤ Y ω} ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂P :=
    le_trans h_gcongr h_markov
  have h_lintegral_eq : ∫⁻ ω, ENNReal.ofReal (g ω) ∂P = ENNReal.ofReal (∫ ω, g ω ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hg_int hg_nonneg).symm
  rw [h_lintegral_eq] at h_le1
  have h_le2 : ENNReal.ofReal c * P {ω | s ≤ Y ω} ≤ ENNReal.ofReal (Real.exp (L ^ 2 * lam ^ 2 / 2)) :=
    le_trans h_le1 (ENNReal.ofReal_le_ofReal hg_bound)
  have hc_toReal : (ENNReal.ofReal c).toReal = c := ENNReal.toReal_ofReal hc_pos.le
  have h_step : c * P.real {ω | s ≤ Y ω} ≤ Real.exp (L ^ 2 * lam ^ 2 / 2) := by
    have h_toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_le2
    rw [ENNReal.toReal_mul, hc_toReal] at h_toReal
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at h_toReal
    exact h_toReal
  have h_exp_neg : 0 < Real.exp (- (lam * s)) := Real.exp_pos _
  have h_mult := mul_le_mul_of_nonneg_left h_step h_exp_neg.le
  have h_cancel : Real.exp (- (lam * s)) * (c * P.real {ω | s ≤ Y ω}) = P.real {ω | s ≤ Y ω} := by
    dsimp [c]
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  rw [h_cancel] at h_mult
  refine le_trans h_mult ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp_of_le
  dsimp [lam]
  have hL_sq_pos : 0 < L ^ 2 := sq_pos_of_ne_zero (ne_of_gt hL)
  have : -(s / L ^ 2 * s) + L ^ 2 * (s / L ^ 2) ^ 2 / 2 = -(s ^ 2) / (2 * L ^ 2) := by
    field_simp
    ring
  rw [this]

private lemma exponent_identity {n : ℕ} (hn : 0 < n) (σ δn t : ℝ) (hσ : 0 < σ) (hδn : 0 < δn)
    (ht : 0 ≤ t) :
    let s := 1 / σ * δn * Real.sqrt (t * δn);
    let L := δn / Real.sqrt n;
    -(s ^ 2) / (2 * L ^ 2) = -(↑n * t * δn) / (2 * σ ^ 2) := by
  intro s L
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h_sqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have h_sqrt_n_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_nonneg
  have h_tdn_nonneg : 0 ≤ t * δn := mul_nonneg ht (le_of_lt hδn)
  have h_sqrt_tdn_sq : (Real.sqrt (t * δn)) ^ 2 = t * δn := Real.sq_sqrt h_tdn_nonneg
  have hL_sq : L ^ 2 = δn ^ 2 / (n : ℝ) := by
    dsimp [L]
    rw [div_pow, h_sqrt_n_sq]
  have hs_sq : s ^ 2 = (δn ^ 2 * (t * δn)) / σ ^ 2 := by
    dsimp [s]
    have : (1 / σ * δn * Real.sqrt (t * δn)) ^ 2 = (1 / σ) ^ 2 * δn ^ 2 * (Real.sqrt (t * δn)) ^ 2 := by
      ring
    rw [this, h_sqrt_tdn_sq, one_div_pow]
    ring
  rw [hs_sq, hL_sq]
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have hδn_ne : δn ≠ 0 := ne_of_gt hδn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  field_simp

private lemma crit_ineq_bound {σ δn t μ_f : ℝ} (hσ : 0 < σ) (hδn : 0 < δn) (ht : δn ≤ t)
    (h_crit : μ_f / δn ≤ δn / (2 * σ)) :
    μ_f ≤ 1 / σ * δn * Real.sqrt (t * δn) := by
  have h2σ_pos : 0 < 2 * σ := mul_pos two_pos hσ
  have h_mu : μ_f ≤ δn ^ 2 / (2 * σ) := by
    have := (div_le_iff₀ hδn).mp h_crit
    calc
      μ_f ≤ δn / (2 * σ) * δn := this
      _ = δn ^ 2 / (2 * σ) := by ring
  have h_dn_sq_le : δn ^ 2 ≤ t * δn := by
    calc
      δn ^ 2 = δn * δn := sq δn
      _ ≤ t * δn := mul_le_mul_of_nonneg_right ht (le_of_lt hδn)
  have h_dn_le_sqrt : δn ≤ Real.sqrt (t * δn) := by
    have h := Real.sqrt_le_sqrt h_dn_sq_le
    rwa [Real.sqrt_sq (le_of_lt hδn)] at h
  have h_sq_le_dn_sqrt : δn ^ 2 ≤ δn * Real.sqrt (t * δn) := by
    calc
      δn ^ 2 = δn * δn := sq δn
      _ ≤ δn * Real.sqrt (t * δn) := mul_le_mul_of_nonneg_left h_dn_le_sqrt (le_of_lt hδn)
  have h_mu2 : μ_f ≤ (δn * Real.sqrt (t * δn)) / (2 * σ) := by
    calc
      μ_f ≤ δn ^ 2 / (2 * σ) := h_mu
      _ ≤ (δn * Real.sqrt (t * δn)) / (2 * σ) :=
        div_le_div_of_nonneg_right h_sq_le_dn_sqrt (le_of_lt h2σ_pos)
  have h_le_sigma : (δn * Real.sqrt (t * δn)) / (2 * σ) ≤ 1 / σ * δn * Real.sqrt (t * δn) := by
    have h_prod_nonneg : 0 ≤ δn * Real.sqrt (t * δn) :=
      mul_nonneg (le_of_lt hδn) (Real.sqrt_nonneg _)
    have h_half : 1 / (2 * σ) ≤ 1 / σ := by
      rw [div_le_div_iff₀ h2σ_pos hσ]
      linarith
    calc
      (δn * Real.sqrt (t * δn)) / (2 * σ) = (1 / (2 * σ)) * (δn * Real.sqrt (t * δn)) := by ring
      _ ≤ (1 / σ) * (δn * Real.sqrt (t * δn)) :=
        mul_le_mul_of_nonneg_right h_half h_prod_nonneg
      _ = 1 / σ * δn * Real.sqrt (t * δn) := by ring
  exact le_trans h_mu2 h_le_sigma

theorem local_gaussian_complexity_tail_bound {X Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (x : Fin n → X) (w : Fin n → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hw : IsIIDStdGaussian P w) (H : Set (X → ℝ)) (hStar : IsStarShaped H) (hH : H.Nonempty)
    (σ δn t : ℝ) (hσ : 0 < σ) (hδn : SatisfiesCriticalInequality x w P H σ δn) (ht : δn ≤ t) :
    P.real {ω | 2 / σ * δn * Real.sqrt (t * δn) ≤
        ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn},
          |(∑ i, w i ω * h.1 (x i)) / n|} ≤
      Real.exp (-(↑n * t * δn) / (2 * σ ^ 2)) ∧
    1 - Real.exp (-(↑n * t * δn) / (2 * σ ^ 2)) ≤
      P.real {ω | ⨆ h : {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn},
          |(∑ i, w i ω * h.1 (x i)) / n| ≤
        2 / σ * δn * Real.sqrt (t * δn)} := by
  let S := {h : X → ℝ // h ∈ H ∧ empiricalNorm x h ≤ δn}
  let W : Ω → EuclideanSpace ℝ (Fin n) := fun ω => WithLp.toLp 2 (fun i => w i ω)
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun z => ⨆ h : S, |(∑ i, z.ofLp i * h.1 (x i)) / (n : ℝ)|
  let L := δn / Real.sqrt n
  have hδn_pos : 0 < δn := hδn.1
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hL_pos : 0 < L := div_pos hδn_pos (Real.sqrt_pos.mpr hn_pos)
  have ht_nonneg : 0 ≤ t := le_trans (le_of_lt hδn_pos) ht
  have hLip : IsLLipschitz f L := f_is_lipschitz_slice hn x H hStar hH δn hδn_pos

  have hXGauss : HasGaussianLaw W P := by
    have h1 : ∀ i, HasGaussianLaw (w i) P := by
      intro i
      have : IsGaussian (Measure.map (w i) P) := by
        rw [hw.2.2 i]
        infer_instance
      exact IsGaussian.hasGaussianLaw
    have h2 : HasGaussianLaw (fun ω i => w i ω) P := iIndepFun.hasGaussianLaw h1 hw.2.1
    have fact_two : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
    exact HasGaussianLaw.toLp_pi 2 h2

  have hXmean : ∀ i, ∫ ω, (W ω).ofLp i ∂P = 0 := by
    intro i
    exact mean_eq_zero_of_iid P hw i

  have hXcov : ∀ i j, ∫ ω, (W ω).ofLp i * (W ω).ofLp j ∂P = if i = j then 1 else 0 := by
    intro i j
    dsimp [W]
    change ∫ ω, w i ω * w j ω ∂P = if i = j then 1 else 0
    split_ifs with hij
    · subst hij
      have : (fun ω => w i ω * w i ω) = (fun ω => (w i ω) ^ 2) := by ext; ring
      rw [this]
      exact sq_integral_eq_one_of_iid P hw i
    · exact cov_eq_zero_of_iid P hw hij

  have h_conc := (lipschitz_gaussian_concentration W f L hXGauss hXmean hXcov hLip).1
  let Y := fun ω => f (W ω) - ∫ ω', f (W ω') ∂P
  have hY_int : Integrable (fun ω => f (W ω)) P := hδn.2.1
  have hY_mean : ∫ ω, Y ω ∂P = 0 := by
    dsimp [Y]
    rw [integral_sub hY_int (integrable_const _)]
    rw [integral_const, prob_real_univ, smul_eq_mul, one_mul, sub_self]

  let s := 1 / σ * δn * Real.sqrt (t * δn)
  let c := 2 / σ * δn * Real.sqrt (t * δn)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact mul_nonneg (mul_nonneg (div_nonneg one_pos.le (le_of_lt hσ)) (le_of_lt hδn_pos)) (Real.sqrt_nonneg _)
  have h_tail_Y := subgaussian_one_sided_tail_bound hL_pos h_conc hY_mean s hs_nonneg

  have h_mu_le_s : (∫ ω', f (W ω') ∂P) ≤ s := by
    have h_crit := hδn.2.2
    dsimp [localGaussianComplexity] at h_crit
    exact crit_ineq_bound hσ hδn_pos ht h_crit

  have h_subset1 : {ω | c ≤ f (W ω)} ⊆ {ω | s ≤ Y ω} := by
    intro ω hω
    dsimp [Y]
    have hc_eq : c = s + s := by
      dsimp [c, s]
      ring
    calc
      s = c - s := by rw [hc_eq]; ring
      _ ≤ f (W ω) - (∫ ω', f (W ω') ∂P) := sub_le_sub hω h_mu_le_s

  have h_exp_eq : -(s ^ 2) / (2 * L ^ 2) = -(↑n * t * δn) / (2 * σ ^ 2) :=
    exponent_identity hn σ δn t hσ hδn_pos ht_nonneg

  have h_bound1 : P.real {ω | c ≤ f (W ω)} ≤ Real.exp (-(↑n * t * δn) / (2 * σ ^ 2)) := by
    have h_mono : P.real {ω | c ≤ f (W ω)} ≤ P.real {ω | s ≤ Y ω} :=
      ENNReal.toReal_mono (measure_ne_top P _) (measure_mono h_subset1)
    rw [← h_exp_eq]
    exact le_trans h_mono h_tail_Y

  refine ⟨h_bound1, ?_⟩

  have hW_meas : Measurable W := by
    have h1 : Measurable (fun ω i => w i ω) := measurable_pi_iff.mpr hw.1
    have h2 : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
      WithLp.measurable_toLp 2 (Fin n → ℝ)
    exact h2.comp h1
  have hf_cont : Continuous f := continuous_of_IsLLipschitz hLip
  have h_fW_meas : Measurable (fun ω => f (W ω)) := hf_cont.measurable.comp hW_meas

  let E := {ω | c < f (W ω)}
  have hE_meas : MeasurableSet E := h_fW_meas measurableSet_Ioi
  have hE_sub : E ⊆ {ω | c ≤ f (W ω)} := fun ω (hω : c < f (W ω)) => le_of_lt hω
  have hE_bound : P.real E ≤ Real.exp (-(↑n * t * δn) / (2 * σ ^ 2)) := by
    have : P.real E ≤ P.real {ω | c ≤ f (W ω)} :=
      ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hE_sub)
    exact le_trans this h_bound1

  have hE_compl : Eᶜ = {ω | f (W ω) ≤ c} := by
    ext ω
    change (¬ c < f (W ω)) ↔ f (W ω) ≤ c
    exact not_lt

  have h_prob_compl : P.real Eᶜ = 1 - P.real E := by
    rw [measureReal_compl hE_meas, prob_real_univ]

  rw [hE_compl] at h_prob_compl
  linarith

abbrev solution := @local_gaussian_complexity_tail_bound

end HighDimStat.NonparametricLS

abbrev solution := @HighDimStat.NonparametricLS.local_gaussian_complexity_tail_bound
