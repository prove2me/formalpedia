-- Prove2me | solution 1 for MDPFinance.JumpMarkets.theorem_9_3_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:01:43.147267+00:00
-- url     : https://prove2.me/submissions/6ef15486-17a4-4827-84d8-e6a51ff8d745

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_JumpMarket

open MeasureTheory Filter Topology
open scoped ENNReal
open scoped ENNReal Pointwise

namespace MDPFinance.JumpMarkets

/-! ### Part A: a saturated non-measurable subset of `ℝ`

`vH = ℚ + ℤ√2`; `vSv` = the reals whose `√2`-coefficient relative to the coset representative
is even. Neither `vSv` nor its complement contains a measurable set of positive measure. -/

/-- The additive subgroup `ℚ + ℤ√2`. -/
def vH : AddSubgroup ℝ where
  carrier := {x | ∃ (q : ℚ) (n : ℤ), x = q + n * Real.sqrt 2}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro a b ⟨q, n, rfl⟩ ⟨q', n', rfl⟩
    exact ⟨q + q', n + n', by push_cast; ring⟩
  neg_mem' := by
    rintro a ⟨q, n, rfl⟩
    exact ⟨-q, -n, by push_cast; ring⟩

lemma vH_mem {x : ℝ} : x ∈ vH ↔ ∃ (q : ℚ) (n : ℤ), x = q + n * Real.sqrt 2 := Iff.rfl

lemma vcoef_unique {q q' : ℚ} {n n' : ℤ} (h : (q : ℝ) + n * Real.sqrt 2 = q' + n' * Real.sqrt 2) :
    n = n' := by
  by_contra hne
  have hne' : ((n : ℝ) - n') ≠ 0 := by
    intro h0
    apply hne
    exact_mod_cast sub_eq_zero.mp h0
  have : Real.sqrt 2 = ((q' - q) / (n - n' : ℤ) : ℚ) := by
    push_cast
    field_simp
    linarith
  exact irrational_sqrt_two.ne_rat _ this

/-- The setoid `x ~ y ↔ x - y ∈ vH`. -/
def vSetoid : Setoid ℝ where
  r x y := x - y ∈ vH
  iseqv := by
    refine ⟨fun x => by simp, fun {x y} h => ?_, fun {x y z} h1 h2 => ?_⟩
    · have := vH.neg_mem h; simpa using this
    · have := vH.add_mem h1 h2; simpa using this

noncomputable def vrep (x : ℝ) : ℝ := Quotient.out (Quotient.mk vSetoid x)

lemma vrep_sub_mem (x : ℝ) : vrep x - x ∈ vH := by
  have h := Quotient.out_eq (Quotient.mk vSetoid x)
  exact Quotient.exact h

lemma vrep_eq_of_sub_mem {x y : ℝ} (h : x - y ∈ vH) : vrep x = vrep y := by
  unfold vrep
  congr 1
  exact Quotient.sound h

lemma vcoef_exists (x : ℝ) : ∃ (q : ℚ) (n : ℤ), x - vrep x = q + n * Real.sqrt 2 := by
  have := vH.neg_mem (vrep_sub_mem x)
  rw [neg_sub] at this
  exact this

noncomputable def vcoef (x : ℝ) : ℤ := Classical.choose (Classical.choose_spec (vcoef_exists x))

lemma vcoef_spec (x : ℝ) : ∃ q : ℚ, x - vrep x = q + vcoef x * Real.sqrt 2 :=
  ⟨_, Classical.choose_spec (Classical.choose_spec (vcoef_exists x))⟩

/-- The saturated non-measurable set. -/
def vSv : Set ℝ := {x | Even (vcoef x)}

lemma vSv_diff_aux {x y : ℝ} (hpar : Even (vcoef x - vcoef y)) (q : ℚ) :
    x - y ≠ q + Real.sqrt 2 := by
  intro hxy
  have hmem : x - y ∈ vH := ⟨q, 1, by rw [hxy]; push_cast; ring⟩
  have hrep := vrep_eq_of_sub_mem hmem
  obtain ⟨qx, hx⟩ := vcoef_spec x
  obtain ⟨qy, hy⟩ := vcoef_spec y
  have : ((qx - qy : ℚ) : ℝ) + ((vcoef x - vcoef y : ℤ) : ℝ) * Real.sqrt 2
      = (q : ℝ) + ((1 : ℤ) : ℝ) * Real.sqrt 2 := by
    push_cast
    have : x - y = (x - vrep x) - (y - vrep y) := by rw [hrep]; ring
    rw [this, hx, hy] at hxy
    linarith
  have h1 := vcoef_unique this
  rw [h1] at hpar
  exact (Int.not_even_one) hpar

lemma vSv_diff {x y : ℝ} (hx : x ∈ vSv) (hy : y ∈ vSv) (q : ℚ) : x - y ≠ q + Real.sqrt 2 :=
  vSv_diff_aux (Even.sub hx hy) q

lemma vSv_compl_diff {x y : ℝ} (hx : x ∉ vSv) (hy : y ∉ vSv) (q : ℚ) :
    x - y ≠ q + Real.sqrt 2 := by
  apply vSv_diff_aux _ q
  have hx' : Odd (vcoef x) := Int.not_even_iff_odd.mp hx
  have hy' : Odd (vcoef y) := Int.not_even_iff_odd.mp hy
  exact Odd.sub_odd hx' hy'

/-- Steinhaus: a measurable subset of a set in which no two points differ by `q + √2` is null. -/
lemma volume_eq_zero_of_no_sqrt_diff {S : Set ℝ}
    (hS : ∀ x ∈ S, ∀ y ∈ S, ∀ q : ℚ, x - y ≠ q + Real.sqrt 2)
    {F : Set ℝ} (hF : MeasurableSet F) (hFS : F ⊆ S) : volume F = 0 := by
  by_contra h0
  have hpos : 0 < volume F := pos_iff_ne_zero.mpr h0
  have hnhds : F - F ∈ 𝓝 (0 : ℝ) :=
    MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos volume F hF hpos
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨q, hq⟩ := exists_rat_near (-Real.sqrt 2) hε
  have hmem : (q : ℝ) + Real.sqrt 2 ∈ F - F := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    rw [abs_sub_comm] at hq
    have : (q : ℝ) - -Real.sqrt 2 = q + Real.sqrt 2 := by ring
    rw [this] at hq
    exact hq
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_sub.mp hmem
  exact hS a (hFS ha) b (hFS hb) q hab

lemma vSv_null {F : Set ℝ} (hF : MeasurableSet F) (hFS : F ⊆ vSv) : volume F = 0 :=
  volume_eq_zero_of_no_sqrt_diff (fun x hx y hy q => vSv_diff hx hy q) hF hFS

lemma vSv_compl_null {F : Set ℝ} (hF : MeasurableSet F) (hFS : F ⊆ vSvᶜ) : volume F = 0 :=
  volume_eq_zero_of_no_sqrt_diff (fun x hx y hy q => vSv_compl_diff hx hy q) hF hFS

/-! ### Part B: the lower integral of a saturated set's indicator vanishes. -/

/-- If no measurable subset of `A` has positive `ν`-measure, the (lower) Lebesgue integral of
`c • 1_A` is zero — even though `A` need not be measurable. -/
lemma lintegral_indicator_eq_zero_of_saturated {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (A : Set α) (hA : ∀ M, MeasurableSet M → M ⊆ A → ν M = 0) (c : ℝ≥0∞) :
    ∫⁻ a, A.indicator (fun _ => c) a ∂ν = 0 := by
  rw [lintegral_def]
  refine le_antisymm (iSup₂_le fun g hg => ?_) (by simp)
  rw [← SimpleFunc.lintegral_eq_lintegral, nonpos_iff_eq_zero]
  rw [lintegral_eq_zero_iff g.measurable]
  have hsub : {a | g a ≠ 0} ⊆ A := by
    intro a ha
    by_contra hna
    have := hg a
    simp [Set.indicator_of_notMem hna] at this
    exact ha this
  have hmeas : MeasurableSet {a | g a ≠ 0} :=
    g.measurable (measurableSet_singleton (0 : ℝ≥0∞)).compl
  have := hA _ hmeas hsub
  rw [Filter.EventuallyEq, ae_iff]
  simpa using this

/-- Transport: for `ν = (volume.restrict (Ioi 0)).withDensity w` pushed forward along
`s ↦ (t + s, x * exp (ρ s))`, the set `{q | q.1 ∈ S}` is saturated when `S` is (`S = vSv` or
`vSvᶜ`). -/
lemma saturated_map {S : Set ℝ}
    (hS : ∀ F, MeasurableSet F → F ⊆ S → volume F = 0)
    (w : ℝ → ℝ≥0∞) (t x ρ : ℝ) :
    ∀ M : Set (ℝ × ℝ), MeasurableSet M → M ⊆ {q | q.1 ∈ S} →
      Measure.map (fun s : ℝ => (t + s, x * Real.exp (ρ * s)))
        ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity w) M = 0 := by
  intro M hM hMS
  have hF : Measurable (fun s : ℝ => (t + s, x * Real.exp (ρ * s))) := by fun_prop
  rw [Measure.map_apply hF hM]
  apply (withDensity_absolutelyContinuous _ _)
  apply Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  set P := (fun s : ℝ => (t + s, x * Real.exp (ρ * s))) ⁻¹' M with hP
  have hPm : MeasurableSet P := hF hM
  have hPS : (fun u : ℝ => u + -t) ⁻¹' P ⊆ S := by
    intro u hu
    have := hMS hu
    simpa using this
  have := hS _ ((measurable_add_const (-t)) hPm) hPS
  rwa [measure_preimage_add_right] at this

/-! ### Part C: the market computations and the contradiction. -/

section Market
variable {d : ℕ} (M : JumpMarket d)

/-- The all-bond control `α ≡ 0`. -/
def bondC (d : ℕ) : Control d :=
  ⟨fun _ _ => 0, measurable_const, fun _ => ⟨fun _ => le_rfl, by simp⟩⟩

/-- All-in stock `i`. -/
def stockC (i : Fin d) : Control d :=
  ⟨fun _ => Pi.single i 1, measurable_const, fun _ => ⟨fun j => by
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_apply, h], by simp⟩⟩

lemma bondC_val (s : ℝ) : (bondC d).val s = fun _ => 0 := rfl
lemma stockC_val (i : Fin d) (s : ℝ) : (stockC i).val s = Pi.single i 1 := rfl

lemma phi_bond (s x : ℝ) (hs : 0 ≤ s) :
    M.phi (bondC d) s x = x * Real.exp (M.rho * s) := by
  unfold JumpMarket.phi
  simp only [bondC_val, zero_mul, Finset.sum_const_zero, add_zero]
  rw [setIntegral_const, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, sub_zero, mul_comm s]

lemma stock_rate (i : Fin d) (r : ℝ) :
    M.rho + ∑ j, (stockC i).val r j * (M.mu j - M.rho) = M.mu i := by
  simp [stockC_val, Pi.single_apply]

lemma phi_stock (i : Fin d) (s x : ℝ) (hs : 0 ≤ s) :
    M.phi (stockC i) s x = x * Real.exp (M.mu i * s) := by
  unfold JumpMarket.phi
  simp_rw [stock_rate]
  rw [setIntegral_const, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, sub_zero, mul_comm s]

/-- The inter-jump law `Exp(λ)` as a measure on `ℝ`. -/
noncomputable def dens : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))

lemma step_eq (a : Control d) (p : ℝ × ℝ) :
    M.step a p = (dens M).bind
      (fun s => M.QY.map (fun y => (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i)))) :=
  rfl

lemma dens_ae_pos : ∀ᵐ s ∂(dens M), 0 < s := by
  unfold dens
  rw [ae_withDensity_iff (by fun_prop), ae_restrict_iff' measurableSet_Ioi]
  exact ae_of_all _ (fun s hs _ => hs)

lemma dens_univ : dens M Set.univ = 1 := by
  unfold dens
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h1 := ProbabilityTheory.lintegral_exponentialPDF_eq_one M.lam_pos
  rw [← lintegral_add_compl _ (measurableSet_Iio (a := (0 : ℝ))),
    ProbabilityTheory.lintegral_exponentialPDF_of_nonpos le_rfl, zero_add, Set.compl_Iio] at h1
  rw [← h1, Measure.restrict_congr_set Ioi_ae_eq_Ici]
  apply setLIntegral_congr_fun measurableSet_Ici
  intro s hs
  rw [ProbabilityTheory.exponentialPDF_of_nonneg hs]
  simp only [neg_mul]

/-- The bond flow line through `(0,1)`. -/
def FL : Set (ℝ × ℝ) := {q | q.2 = Real.exp (M.rho * q.1)}

lemma FL_meas : MeasurableSet (FL M) := measurableSet_eq_fun measurable_snd (by fun_prop)

lemma step_bond (q : ℝ × ℝ) :
    M.step (bondC d) q = (dens M).map (fun s => (q.1 + s, q.2 * Real.exp (M.rho * s))) := by
  rw [step_eq, ← Measure.bind_dirac_eq_map _ (by fun_prop)]
  apply Measure.bind_congr_right
  haveI := M.QY_prob
  filter_upwards [dens_ae_pos M] with s hs
  have hfun : (fun y : Fin d → ℝ =>
      (q.1 + s, M.phi (bondC d) s q.2 * (1 + ∑ i, (bondC d).val s i * y i)))
      = fun _ => (q.1 + s, q.2 * Real.exp (M.rho * s)) := by
    funext y; simp [bondC_val, phi_bond M s q.2 hs.le]
  rw [hfun, Measure.map_const, measure_univ, one_smul]

lemma step_stock (i : Fin d) (q : ℝ × ℝ) :
    M.step (stockC i) q = (dens M).bind
      (fun s => M.QY.map (fun y => (q.1 + s, q.2 * Real.exp (M.mu i * s) * (1 + y i)))) := by
  rw [step_eq]
  apply Measure.bind_congr_right
  filter_upwards [dens_ae_pos M] with s hs
  congr 1; funext y
  simp [stockC_val, Pi.single_apply, phi_stock M i s q.2 hs.le]

lemma stock_kernel_meas (i : Fin d) (q : ℝ × ℝ) :
    Measurable (fun s : ℝ =>
      M.QY.map (fun y => (q.1 + s, q.2 * Real.exp (M.mu i * s) * (1 + y i)))) := by
  haveI := M.QY_prob
  have hG : Measurable (fun sy : ℝ × (Fin d → ℝ) =>
      (q.1 + sy.1, q.2 * Real.exp (M.mu i * sy.1) * (1 + sy.2 i))) := by fun_prop
  have : (fun s : ℝ => M.QY.map (fun y => (q.1 + s, q.2 * Real.exp (M.mu i * s) * (1 + y i))))
      = fun s => Measure.map (fun sy : ℝ × (Fin d → ℝ) =>
          (q.1 + sy.1, q.2 * Real.exp (M.mu i * sy.1) * (1 + sy.2 i)))
          (Measure.map (Prod.mk s) M.QY) := by
    funext s
    rw [Measure.map_map hG measurable_prodMk_left]
    rfl
  rw [this]
  exact (Measure.measurable_map _ hG).comp Measurable.map_prodMk_left

lemma step_stock_apply (i : Fin d) (q : ℝ × ℝ) {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) :
    M.step (stockC i) q B =
      ∫⁻ s, M.QY {y | (q.1 + s, q.2 * Real.exp (M.mu i * s) * (1 + y i)) ∈ B} ∂(dens M) := by
  rw [step_stock, Measure.bind_apply hB (stock_kernel_meas M i q).aemeasurable]
  congr 1; funext s
  rw [Measure.map_apply (by fun_prop) hB]
  rfl

/-- `κ`: the chance that the all-in-stock control leaves the bond flow line. -/
noncomputable def kap (i : Fin d) : ℝ≥0∞ :=
  ∫⁻ s, M.QY {y | Real.exp (M.mu i * s) * (1 + y i) ≠ Real.exp (M.rho * s)} ∂(dens M)

lemma step_stock_FLc (i : Fin d) {q : ℝ × ℝ} (hq : q ∈ FL M) :
    M.step (stockC i) q (FL M)ᶜ = kap M i := by
  rw [step_stock_apply M i q (FL_meas M).compl]
  unfold kap
  congr 1; funext s; congr 1; ext y
  simp only [FL, Set.mem_compl_iff, Set.mem_setOf_eq]
  have hq' : q.2 = Real.exp (M.rho * q.1) := hq
  have hpos : 0 < Real.exp (M.rho * q.1) := Real.exp_pos _
  have h2 : Real.exp (M.rho * (q.1 + s)) = Real.exp (M.rho * q.1) * Real.exp (M.rho * s) := by
    rw [mul_add, Real.exp_add]
  rw [hq', h2, mul_assoc]
  exact not_congr (mul_right_inj' hpos.ne')

lemma step_bond_FLc {q : ℝ × ℝ} (hq : q ∈ FL M) : M.step (bondC d) q (FL M)ᶜ = 0 := by
  rw [step_bond, Measure.map_apply (by fun_prop) (FL_meas M).compl]
  have hq' : q.2 = Real.exp (M.rho * q.1) := hq
  have : (fun s : ℝ => (q.1 + s, q.2 * Real.exp (M.rho * s))) ⁻¹' (FL M)ᶜ = ∅ := by
    ext s; simp [FL, hq', mul_add, Real.exp_add]
  rw [this, measure_empty]

lemma step_univ_le (a : Control d) (q : ℝ × ℝ) : M.step a q Set.univ ≤ 1 := by
  rw [step_eq]
  refine (Measure.bind_apply_le _ MeasurableSet.univ).trans ?_
  haveI := M.QY_prob
  calc ∫⁻ s, (M.QY.map (fun y => (q.1 + s, M.phi a s q.2 * (1 + ∑ i, a.val s i * y i))))
        Set.univ ∂(dens M)
      ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(dens M) := by
        apply lintegral_mono; intro s
        haveI : IsProbabilityMeasure
            (M.QY.map (fun y => (q.1 + s, M.phi a s q.2 * (1 + ∑ i, a.val s i * y i)))) :=
          Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
        exact prob_le_one
    _ = 1 := by rw [lintegral_const, dens_univ, mul_one]

lemma kap_le_one (i : Fin d) : kap M i ≤ 1 := by
  have h0 : ((0 : ℝ), (1 : ℝ)) ∈ FL M := by simp [FL]
  rw [← step_stock_FLc M i h0]
  exact (measure_mono (Set.subset_univ _)).trans (step_univ_le M _ _)

lemma step_stock_FL_le (i : Fin d) {q : ℝ × ℝ} (hq : q ∈ FL M) :
    M.step (stockC i) q (FL M) ≤ 1 - kap M i := by
  apply ENNReal.le_sub_of_add_le_right ((kap_le_one M i).trans_lt ENNReal.one_lt_top).ne
  rw [← step_stock_FLc M i hq, measure_add_measure_compl (FL_meas M)]
  exact step_univ_le M _ q

/-- `κ ≠ 0` unless the market is degenerate in direction `i`. -/
lemma kap_ne_zero (i : Fin d) (hnd : ¬ (M.mu i = M.rho ∧ M.QY {y | y i ≠ 0} = 0)) :
    kap M i ≠ 0 := by
  intro h0
  haveI := M.QY_prob
  unfold kap at h0
  have hmeasS : MeasurableSet {sy : ℝ × (Fin d → ℝ) |
      Real.exp (M.mu i * sy.1) * (1 + sy.2 i) ≠ Real.exp (M.rho * sy.1)} :=
    (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
  have hmeas : Measurable fun s : ℝ =>
      M.QY {y | Real.exp (M.mu i * s) * (1 + y i) ≠ Real.exp (M.rho * s)} :=
    measurable_measure_prodMk_left hmeasS
  rw [lintegral_eq_zero_iff hmeas] at h0
  have h0' : ∀ᵐ s ∂(dens M),
      M.QY {y | Real.exp (M.mu i * s) * (1 + y i) ≠ Real.exp (M.rho * s)} = 0 := h0
  unfold dens at h0'
  rw [ae_withDensity_iff (by fun_prop)] at h0'
  have hgood : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      M.QY {y | Real.exp (M.mu i * s) * (1 + y i) ≠ Real.exp (M.rho * s)} = 0 := by
    filter_upwards [h0'] with s hs
    apply hs
    have : 0 < M.lam * Real.exp (-M.lam * s) := mul_pos M.lam_pos (Real.exp_pos _)
    exact (ENNReal.ofReal_pos.mpr this).ne'
  haveI : NeZero (volume.restrict (Set.Ioi (0 : ℝ))) := ⟨by simp⟩
  obtain ⟨s1, hs1, hq1⟩ := ((ae_restrict_mem measurableSet_Ioi).and hgood).exists
  have hne : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))), s ≠ s1 := by
    rw [ae_iff]
    apply measure_mono_null (t := {s1}) (fun x hx => ?_)
    · exact nonpos_iff_eq_zero.mp
        ((Measure.le_iff'.mp Measure.restrict_le_self _).trans_eq Real.volume_singleton)
    · simp only [Set.mem_setOf_eq, not_not] at hx
      exact Set.mem_singleton_iff.mpr hx
  obtain ⟨s2, hs2, hq2, hne12⟩ := ((ae_restrict_mem measurableSet_Ioi).and (hgood.and hne)).exists
  have hae1 : ∀ᵐ y ∂M.QY, Real.exp (M.mu i * s1) * (1 + y i) = Real.exp (M.rho * s1) := by
    rw [ae_iff]; exact hq1
  have hae2 : ∀ᵐ y ∂M.QY, Real.exp (M.mu i * s2) * (1 + y i) = Real.exp (M.rho * s2) := by
    rw [ae_iff]; exact hq2
  obtain ⟨y, hy1, hy2⟩ := (hae1.and hae2).exists
  have hmu : M.mu i = M.rho := by
    have e1 : 1 + y i = Real.exp ((M.rho - M.mu i) * s1) := by
      rw [sub_mul, Real.exp_sub, eq_div_iff (Real.exp_pos _).ne', mul_comm]; exact hy1
    have e2 : 1 + y i = Real.exp ((M.rho - M.mu i) * s2) := by
      rw [sub_mul, Real.exp_sub, eq_div_iff (Real.exp_pos _).ne', mul_comm]; exact hy2
    have := Real.exp_injective (e1.symm.trans e2)
    have h3 : (M.rho - M.mu i) * (s1 - s2) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · exact absurd (sub_eq_zero.mp h).symm hne12
  apply hnd
  refine ⟨hmu, ?_⟩
  rw [← hq1]
  congr 1; ext y
  simp only [Set.mem_setOf_eq, hmu]
  have hpos : 0 < Real.exp (M.rho * s1) := Real.exp_pos _
  rw [ne_eq, ne_eq, mul_eq_left₀ hpos.ne']
  constructor
  · intro h h'; apply h; linarith
  · intro h h'; apply h; rw [h']; ring

/-- The non-measurable policy contradicts the existence of chain laws for all `g`. -/
lemma chain_contra (i : Fin d) (hκ : kap M i ≠ 0)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g)) : False := by
  classical
  let g : HistPolicy d := fun n h =>
    if n = 1 then (if (h (Fin.last n)).1 ∈ vSv then bondC d else stockC i) else bondC d
  let p0 : ℝ × ℝ := (0, 1)
  obtain ⟨hprob, hcyl⟩ := hPr g
  have key : ∀ B : Set (ℝ × ℝ), MeasurableSet B →
      Pr g p0 {w | w 2 ∈ B} =
        ∫⁻ q, M.step (if q.1 ∈ vSv then bondC d else stockC i) q B ∂(M.step (bondC d) p0) := by
    intro B hB
    have := hcyl p0 2 (fun k => if k = 2 then B else Set.univ)
      (fun k => by split_ifs <;> simp [hB])
    have hset : {w : ℕ → ℝ × ℝ | ∀ k ≤ 2, w k ∈ (fun k => if k = 2 then B else Set.univ) k}
        = {w | w 2 ∈ B} := by
      ext w; simp only [Set.mem_setOf_eq]; constructor
      · intro h; simpa using h 2 le_rfl
      · intro h k hk
        by_cases hk2 : k = 2
        · subst hk2; simpa using h
        · simp [hk2]
    rw [hset] at this
    rw [this]
    simp only [JumpMarket.chainCyl, g]
    simp
    have hlast : ∀ q : ℝ × ℝ, (Fin.snoc (fun _ : Fin 1 => p0) q : Fin 2 → ℝ × ℝ) 1 = q :=
      fun q => Fin.snoc_last _ _
    simp only [hlast]
  have hFLc := key (FL M)ᶜ (FL_meas M).compl
  have hFL := key (FL M) (FL_meas M)
  have hae : ∀ᵐ q ∂(M.step (bondC d) p0), q ∈ FL M := by
    rw [step_bond]
    have hF : Measurable (fun s : ℝ => (p0.1 + s, p0.2 * Real.exp (M.rho * s))) := by fun_prop
    exact (ae_map_iff hF.aemeasurable (FL_meas M)).mpr (ae_of_all _ (fun s => by simp [FL, p0]))
  have hsat1 : ∀ N : Set (ℝ × ℝ), MeasurableSet N → N ⊆ {q | q.1 ∈ vSvᶜ} →
      Measure.map (fun s : ℝ => (p0.1 + s, p0.2 * Real.exp (M.rho * s))) (dens M) N = 0 :=
    saturated_map (fun F hF hFS => vSv_compl_null hF hFS)
      (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s))) p0.1 p0.2 M.rho
  have hsat2 : ∀ N : Set (ℝ × ℝ), MeasurableSet N → N ⊆ {q | q.1 ∈ vSv} →
      Measure.map (fun s : ℝ => (p0.1 + s, p0.2 * Real.exp (M.rho * s))) (dens M) N = 0 :=
    saturated_map (fun F hF hFS => vSv_null hF hFS)
      (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s))) p0.1 p0.2 M.rho
  have h1 : ∫⁻ q, M.step (if q.1 ∈ vSv then bondC d else stockC i) q (FL M)ᶜ
      ∂(M.step (bondC d) p0) = 0 := by
    refine le_antisymm ?_ (by simp)
    calc ∫⁻ q, M.step (if q.1 ∈ vSv then bondC d else stockC i) q (FL M)ᶜ
          ∂(M.step (bondC d) p0)
        ≤ ∫⁻ q, {q : ℝ × ℝ | q.1 ∈ vSvᶜ}.indicator (fun _ => kap M i) q
            ∂(M.step (bondC d) p0) := by
          apply lintegral_mono_ae
          filter_upwards [hae] with q hq
          split_ifs with hs
          · rw [step_bond_FLc M hq]; exact zero_le'
          · rw [step_stock_FLc M i hq]
            simp [Set.indicator, hs]
      _ = 0 := by
          rw [step_bond]
          exact lintegral_indicator_eq_zero_of_saturated _ _ hsat1 _
  have h2 : ∫⁻ q, M.step (if q.1 ∈ vSv then bondC d else stockC i) q (FL M)
      ∂(M.step (bondC d) p0) ≤ 1 - kap M i := by
    calc ∫⁻ q, M.step (if q.1 ∈ vSv then bondC d else stockC i) q (FL M)
          ∂(M.step (bondC d) p0)
        ≤ ∫⁻ q, ((1 - kap M i) + {q : ℝ × ℝ | q.1 ∈ vSv}.indicator (fun _ => kap M i) q)
            ∂(M.step (bondC d) p0) := by
          apply lintegral_mono_ae
          filter_upwards [hae] with q hq
          split_ifs with hs
          · calc M.step (bondC d) q (FL M) ≤ 1 :=
                  (measure_mono (Set.subset_univ _)).trans (step_univ_le M _ q)
              _ = _ := by
                  simp only [Set.indicator, Set.mem_setOf_eq, hs, if_true]
                  rw [tsub_add_cancel_of_le (kap_le_one M i)]
          · simp only [Set.indicator, Set.mem_setOf_eq, hs, if_false, add_zero]
            exact step_stock_FL_le M i hq
      _ = (1 - kap M i) * (M.step (bondC d) p0) Set.univ + 0 := by
          rw [lintegral_add_left measurable_const, lintegral_const, step_bond,
            lintegral_indicator_eq_zero_of_saturated _ _ hsat2]
      _ ≤ 1 - kap M i := by
          rw [add_zero]
          exact mul_le_of_le_one_right' (step_univ_le M _ p0)
  have htot : Pr g p0 {w | w 2 ∈ (FL M)ᶜ} + Pr g p0 {w | w 2 ∈ FL M} = 1 := by
    have hm : MeasurableSet {w : ℕ → ℝ × ℝ | w 2 ∈ FL M} := measurable_pi_apply 2 (FL_meas M)
    haveI := hprob p0
    have := measure_add_measure_compl (μ := Pr g p0) hm
    rw [measure_univ, add_comm] at this
    exact this
  rw [hFLc, hFL, h1, zero_add] at htot
  have hle : (1 : ℝ≥0∞) ≤ 1 - kap M i := htot ▸ h2
  have hlt : 1 - kap M i < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hκ
  exact absurd hle (not_le.mpr hlt)

/-- Summary: unless the market is degenerate in every direction, no family of chain laws for
all (including non-measurable) history-dependent policies exists. -/
theorem no_chain_law_of_nondegenerate
    (hnd : ¬ ∀ i : Fin d, M.mu i = M.rho ∧ M.QY {y | y i ≠ 0} = 0)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g)) : False := by
  push_neg at hnd
  obtain ⟨i, hi⟩ := hnd
  exact chain_contra M i (kap_ne_zero M i (fun h => hi h.1 h.2)) Pr hPr

end Market


section Deg
variable {d : ℕ} (M : JumpMarket d)

/-- The degenerate market: every stock has the bond drift and never jumps. -/
def Deg : Prop := ∀ i : Fin d, M.mu i = M.rho ∧ M.QY {y | y i ≠ 0} = 0

noncomputable def densD : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))

noncomputable def densT (p : ℝ × ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo (0 : ℝ) (M.T - p.1))).withDensity
    (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))

/-- The degenerate one-step kernel (untruncated). -/
noncomputable def Kdeg (p : ℝ × ℝ) : Measure (ℝ × ℝ) :=
  (densD M).map (fun s => (p.1 + s, p.2 * Real.exp (M.rho * s)))

/-- The degenerate truncated kernel. -/
noncomputable def Qdeg (p : ℝ × ℝ) : Measure (ℝ × ℝ) :=
  (densT M p).map (fun s => (p.1 + s, p.2 * Real.exp (M.rho * s)))

lemma densD_ae_pos : ∀ᵐ s ∂(densD M), 0 < s := by
  unfold densD
  rw [ae_withDensity_iff (by fun_prop), ae_restrict_iff' measurableSet_Ioi]
  exact ae_of_all _ (fun s hs _ => hs)

lemma densT_ae_pos (p : ℝ × ℝ) : ∀ᵐ s ∂(densT M p), 0 < s := by
  unfold densT
  rw [ae_withDensity_iff (by fun_prop), ae_restrict_iff' measurableSet_Ioo]
  exact ae_of_all _ (fun s hs _ => hs.1)

lemma densD_univ : densD M Set.univ = 1 := by
  unfold densD
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h1 := ProbabilityTheory.lintegral_exponentialPDF_eq_one M.lam_pos
  rw [← lintegral_add_compl _ (measurableSet_Iio (a := (0 : ℝ))),
    ProbabilityTheory.lintegral_exponentialPDF_of_nonpos le_rfl, zero_add, Set.compl_Iio] at h1
  rw [← h1, Measure.restrict_congr_set Ioi_ae_eq_Ici]
  apply setLIntegral_congr_fun measurableSet_Ici
  intro s hs
  rw [ProbabilityTheory.exponentialPDF_of_nonneg hs]
  simp only [neg_mul]

lemma phi_deg (hdeg : Deg M) (a : Control d) (s x : ℝ) (hs : 0 ≤ s) :
    M.phi a s x = x * Real.exp (M.rho * s) := by
  unfold JumpMarket.phi
  have h : ∀ r : ℝ, M.rho + ∑ i, a.val r i * (M.mu i - M.rho) = M.rho := by
    intro r
    rw [Finset.sum_eq_zero (fun i _ => by rw [(hdeg i).1, sub_self, mul_zero]), add_zero]
  simp_rw [h]
  rw [setIntegral_const, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, sub_zero, mul_comm s]

lemma QY_ae_zero (hdeg : Deg M) : ∀ᵐ y ∂M.QY, y = 0 := by
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ i : Fin d, {y : Fin d → ℝ | y i ≠ 0})
  · intro y hy
    simp only [Set.mem_setOf_eq] at hy
    by_contra hcon
    apply hy
    funext i
    by_contra hi
    exact hcon (Set.mem_iUnion.mpr ⟨i, hi⟩)
  · exact measure_iUnion_null (fun i => (hdeg i).2)

lemma step_deg (hdeg : Deg M) (a : Control d) (p : ℝ × ℝ) : M.step a p = Kdeg M p := by
  haveI := M.QY_prob
  unfold Kdeg
  change (densD M).bind _ = _
  rw [← Measure.bind_dirac_eq_map _ (by fun_prop)]
  apply Measure.bind_congr_right
  filter_upwards [densD_ae_pos M] with s hs
  have hfun : (fun y : Fin d → ℝ =>
      (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i)))
      =ᵐ[M.QY] fun _ => (p.1 + s, p.2 * Real.exp (M.rho * s)) := by
    filter_upwards [QY_ae_zero M hdeg] with y hy
    rw [hy, phi_deg M hdeg a s p.2 hs.le]; simp
  rw [Measure.map_congr hfun, Measure.map_const, measure_univ, one_smul]

lemma Q_deg (hdeg : Deg M) (a : Control d) (p : ℝ × ℝ) : M.Q a p = Qdeg M p := by
  haveI := M.QY_prob
  unfold Qdeg
  change (densT M p).bind _ = _
  rw [← Measure.bind_dirac_eq_map _ (by fun_prop)]
  apply Measure.bind_congr_right
  filter_upwards [densT_ae_pos M p] with s hs
  have hfun : (fun y : Fin d → ℝ =>
      (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i)))
      =ᵐ[M.QY] fun _ => (p.1 + s, p.2 * Real.exp (M.rho * s)) := by
    filter_upwards [QY_ae_zero M hdeg] with y hy
    rw [hy, phi_deg M hdeg a s p.2 hs.le]; simp
  rw [Measure.map_congr hfun, Measure.map_const, measure_univ, one_smul]

/-- The `g`-free cylinder recursion. -/
noncomputable def cyl : ℕ → (ℝ × ℝ) → (ℕ → Set (ℝ × ℝ)) → ℝ≥0∞
  | 0, _, _ => 1
  | (m + 1), q, B => ∫⁻ q' in B 0, cyl m q' (fun i => B (i + 1)) ∂(Kdeg M q)

lemma chainCyl_deg (hdeg : Deg M) :
    ∀ (m n : ℕ) (g : HistPolicy d) (h : Fin (n + 1) → ℝ × ℝ) (B : ℕ → Set (ℝ × ℝ)),
      M.chainCyl g n h m B = cyl M m (h (Fin.last n)) B := by
  intro m
  induction m with
  | zero => intro n g h B; rfl
  | succ m ih =>
    intro n g h B
    simp only [JumpMarket.chainCyl, cyl, step_deg M hdeg]
    congr 1
    funext q
    rw [ih, Fin.snoc_last]

/-- The flow line through `p`. -/
def FLp (p : ℝ × ℝ) : Set (ℝ × ℝ) := {q | q.2 = p.2 * Real.exp (M.rho * (q.1 - p.1))}

lemma FLp_meas (p : ℝ × ℝ) : MeasurableSet (FLp M p) :=
  measurableSet_eq_fun measurable_snd (by fun_prop)

lemma self_mem_FLp (p : ℝ × ℝ) : p ∈ FLp M p := by simp [FLp]

lemma Kdeg_FLp {p q : ℝ × ℝ} (hq : q ∈ FLp M p) : Kdeg M q (FLp M p) = 1 := by
  unfold Kdeg
  rw [Measure.map_apply (by fun_prop) (FLp_meas M p)]
  have hq' : q.2 = p.2 * Real.exp (M.rho * (q.1 - p.1)) := hq
  have : (fun s : ℝ => (q.1 + s, q.2 * Real.exp (M.rho * s))) ⁻¹' (FLp M p) = Set.univ := by
    ext s
    simp only [Set.mem_preimage, FLp, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [hq', mul_assoc, ← Real.exp_add]
    congr 2; ring
  rw [this, densD_univ]

lemma cyl_FLp (p : ℝ × ℝ) : ∀ m : ℕ, ∀ q ∈ FLp M p, cyl M m q (fun _ => FLp M p) = 1 := by
  intro m
  induction m with
  | zero => intro q _; rfl
  | succ m ih =>
    intro q hq
    simp only [cyl]
    rw [setLIntegral_congr_fun (FLp_meas M p) (fun q' hq' => ih q' hq'), setLIntegral_one,
      Kdeg_FLp M hq]

lemma cylset_meas (m : ℕ) (B : ℕ → Set (ℝ × ℝ)) (hB : ∀ i, MeasurableSet (B i)) :
    MeasurableSet {w : ℕ → ℝ × ℝ | ∀ i ≤ m, w i ∈ B i} := by
  have : {w : ℕ → ℝ × ℝ | ∀ i ≤ m, w i ∈ B i} = ⋂ i ∈ Finset.range (m + 1), (fun w => w i) ⁻¹' (B i) := by
    ext w; simp [Nat.lt_succ_iff]
  rw [this]
  exact Finset.measurableSet_biInter _ (fun i _ => measurable_pi_apply i (hB i))

lemma Pr_FLp (hdeg : Deg M) (g : HistPolicy d) (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : M.IsChainLaw g Pr) (p : ℝ × ℝ) (m : ℕ) :
    Pr p {w | ∀ i ≤ m, w i ∈ FLp M p} = 1 := by
  rw [hPr.2 p m (fun _ => FLp M p) (fun _ => FLp_meas M p)]
  rw [Set.indicator_of_mem (self_mem_FLp M p), chainCyl_deg M hdeg]
  exact cyl_FLp M p m p (self_mem_FLp M p)

lemma Pr_FLp_all (hdeg : Deg M) (g : HistPolicy d) (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : M.IsChainLaw g Pr) (p : ℝ × ℝ) :
    ∀ᵐ w ∂(Pr p), ∀ i, w i ∈ FLp M p := by
  haveI := hPr.1 p
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ m : ℕ, {w : ℕ → ℝ × ℝ | ∀ i ≤ m, w i ∈ FLp M p}ᶜ)
  · intro w hw
    simp only [Set.mem_setOf_eq, not_forall] at hw
    obtain ⟨i, hi⟩ := hw
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall]
    exact ⟨i, le_rfl, hi⟩
  · apply measure_iUnion_null
    intro m
    rw [prob_compl_eq_one_sub (cylset_meas m _ (fun _ => FLp_meas M p)), Pr_FLp M hdeg g Pr hPr p m,
      tsub_self]

/-- On the flow line, the terminal wealth is `0` or `z = x e^{ρ(T-t)}`. -/
lemma terminalWealth_deg (hdeg : Deg M) (g : HistPolicy d) (p : ℝ × ℝ) (w : ℕ → ℝ × ℝ)
    (hw : ∀ i, w i ∈ FLp M p) :
    M.terminalWealth g w = 0 ∨ M.terminalWealth g w = p.2 * Real.exp (M.rho * (M.T - p.1)) := by
  unfold JumpMarket.terminalWealth
  split_ifs with h
  · right
    set k := h.choose with hk
    have hks := h.choose_spec
    rw [← hk] at hks
    rw [phi_deg M hdeg _ _ _ (by linarith [hks.1])]
    have hwk : (w k).2 = p.2 * Real.exp (M.rho * ((w k).1 - p.1)) := hw k
    rw [hwk, mul_assoc, ← Real.exp_add]
    congr 2; ring
  · left; rfl

lemma E_mem_nonneg {p : ℝ × ℝ} (hp : p ∈ M.E) : 0 ≤ p.2 := hp.2

lemma E_mem_t {p : ℝ × ℝ} (hp : p ∈ M.E) : 0 ≤ p.1 ∧ p.1 ≤ M.T := hp.1

lemma rho_le_mubar : M.rho ≤ M.mubar := le_max_left _ _

/-- Key real inequality: `1 + x e^{ρ(T-t)} ≤ e^{T μ̄}/(1-α) (1 + x)` for `(t,x) ∈ E`. -/
lemma one_add_z_le {p : ℝ × ℝ} (hp : p ∈ M.E) {alpha : ℝ} (h0 : 0 ≤ alpha) (h1 : alpha < 1) :
    1 + p.2 * Real.exp (M.rho * (M.T - p.1)) ≤
      Real.exp (M.T * M.mubar) / (1 - alpha) * (1 + p.2) := by
  have ht := E_mem_t M hp
  have hx := E_mem_nonneg M hp
  have hρ := M.rho_nonneg
  have e1 : 1 ≤ Real.exp (M.rho * (M.T - p.1)) := by
    rw [Real.one_le_exp_iff]; exact mul_nonneg hρ (by linarith)
  have e2 : Real.exp (M.rho * (M.T - p.1)) ≤ Real.exp (M.T * M.mubar) := by
    apply Real.exp_le_exp.mpr
    have := rho_le_mubar M
    nlinarith
  have e3 : Real.exp (M.T * M.mubar) ≤ Real.exp (M.T * M.mubar) / (1 - alpha) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [Real.exp_pos (M.T * M.mubar)]
  calc 1 + p.2 * Real.exp (M.rho * (M.T - p.1))
      ≤ Real.exp (M.rho * (M.T - p.1)) * (1 + p.2) := by nlinarith
    _ ≤ Real.exp (M.T * M.mubar) * (1 + p.2) := by
        apply mul_le_mul_of_nonneg_right e2 (by linarith)
    _ ≤ Real.exp (M.T * M.mubar) / (1 - alpha) * (1 + p.2) := by
        apply mul_le_mul_of_nonneg_right e3 (by linarith)

lemma densT_ae_mem (p : ℝ × ℝ) : ∀ᵐ s ∂(densT M p), s ∈ Set.Ioo (0 : ℝ) (M.T - p.1) := by
  unfold densT
  rw [ae_withDensity_iff (by fun_prop), ae_restrict_iff' measurableSet_Ioo]
  exact ae_of_all _ (fun s hs _ => hs)

lemma densT_univ_pos {p : ℝ × ℝ} (hp : p ∈ M.E) (hpT : p.1 < M.T) :
    0 < densT M p Set.univ := by
  have ht := E_mem_t M hp
  unfold densT
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hlow : ∀ s ∈ Set.Ioo (0 : ℝ) (M.T - p.1),
      ENNReal.ofReal (M.lam * Real.exp (-M.lam * M.T)) ≤
        ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) := by
    intro s hs
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ M.lam_pos.le
    apply Real.exp_le_exp.mpr
    nlinarith [M.lam_pos, hs.2, ht.1]
  calc (0 : ℝ≥0∞)
      < ENNReal.ofReal (M.lam * Real.exp (-M.lam * M.T)) * volume (Set.Ioo (0 : ℝ) (M.T - p.1)) := by
        apply ENNReal.mul_pos
        · exact (ENNReal.ofReal_pos.mpr (mul_pos M.lam_pos (Real.exp_pos _))).ne'
        · rw [Real.volume_Ioo]; exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    _ = ∫⁻ _ in Set.Ioo (0 : ℝ) (M.T - p.1),
          ENNReal.ofReal (M.lam * Real.exp (-M.lam * M.T)) := by rw [setLIntegral_const]
    _ ≤ _ := setLIntegral_mono (by fun_prop) hlow

lemma bfun_lower (gamma : ℝ) {p : ℝ × ℝ} (hp : p ∈ M.E) :
    Real.exp (-(|gamma| * M.T)) ≤ M.bfun gamma p := by
  have ht := E_mem_t M hp
  have hx := E_mem_nonneg M hp
  unfold JumpMarket.bfun
  have h1 : Real.exp (-(|gamma| * M.T)) ≤ Real.exp (gamma * (M.T - p.1)) := by
    apply Real.exp_le_exp.mpr
    have h2 : -|gamma| ≤ gamma := neg_abs_le gamma
    have h3 : 0 ≤ |gamma| := abs_nonneg gamma
    nlinarith
  calc Real.exp (-(|gamma| * M.T)) ≤ Real.exp (gamma * (M.T - p.1)) := h1
    _ = Real.exp (gamma * (M.T - p.1)) * 1 := (mul_one _).symm
    _ ≤ Real.exp (gamma * (M.T - p.1)) * (1 + p.2) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

lemma alpha_nonneg (hdeg : Deg M) {gamma alpha : ℝ}
    (hb : M.IsBoundingFunction (M.bfun gamma) alpha) : 0 ≤ alpha := by
  by_contra hneg
  push_neg at hneg
  have hp0 : ((0 : ℝ), (1 : ℝ)) ∈ M.E := ⟨⟨le_rfl, M.T_pos.le⟩, by simp⟩
  have h := hb.2.2 _ hp0 (bondC d)
  have hz : ENNReal.ofReal (alpha * M.bfun gamma (0, 1)) = 0 :=
    ENNReal.ofReal_eq_zero.mpr (mul_neg_of_neg_of_pos hneg (hb.1 _ hp0)).le
  rw [hz, Q_deg M hdeg, nonpos_iff_eq_zero] at h
  unfold Qdeg at h
  have hbm : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (M.bfun gamma q)) := by
    unfold JumpMarket.bfun; fun_prop
  rw [lintegral_map hbm (by fun_prop)] at h
  have hpos : 0 < ∫⁻ s, ENNReal.ofReal (M.bfun gamma (((0 : ℝ), (1 : ℝ)).1 + s,
      ((0 : ℝ), (1 : ℝ)).2 * Real.exp (M.rho * s))) ∂(densT M (0, 1)) := by
    calc (0 : ℝ≥0∞) < ENNReal.ofReal (Real.exp (-(|gamma| * M.T))) * densT M (0, 1) Set.univ := by
          apply ENNReal.mul_pos
          · exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
          · exact (densT_univ_pos M hp0 M.T_pos).ne'
      _ = ∫⁻ _, ENNReal.ofReal (Real.exp (-(|gamma| * M.T))) ∂(densT M (0, 1)) := by
          rw [lintegral_const]
      _ ≤ _ := by
          apply lintegral_mono_ae
          filter_upwards [densT_ae_mem M (0, 1)] with s hs
          apply ENNReal.ofReal_le_ofReal
          apply bfun_lower M gamma
          refine ⟨⟨by simp; linarith [hs.1], by simp; linarith [hs.2]⟩, ?_⟩
          show (0 : ℝ) ≤ 1 * Real.exp (M.rho * s)
          positivity
  exact lt_irrefl _ (hpos.trans_eq h)

/-- Two jump markets with the same market data (local copy, kept as a plain conjunction). -/
def SameMkt {d : ℕ} (M M' : JumpMarket d) : Prop :=
  M'.rho = M.rho ∧ M'.mu = M.mu ∧ M'.lam = M.lam ∧ M'.QY = M.QY ∧ M'.T = M.T

lemma SameMkt.symm' {M M' : JumpMarket d} (h : SameMkt M M') : SameMkt M' M :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

lemma E_same {M M' : JumpMarket d} (h : SameMkt M M') : M'.E = M.E := by
  unfold JumpMarket.E; rw [h.2.2.2.2]

lemma bfun_same {M M' : JumpMarket d} (h : SameMkt M M') (gamma : ℝ) :
    M'.bfun gamma = M.bfun gamma := by
  funext p; unfold JumpMarket.bfun; rw [h.2.2.2.2]

lemma mubar_same {M M' : JumpMarket d} (h : SameMkt M M') : M'.mubar = M.mubar := by
  unfold JumpMarket.mubar; rw [h.1, h.2.1]

lemma T_same {M M' : JumpMarket d} (h : SameMkt M M') : M'.T = M.T := h.2.2.2.2

lemma FLp_same {M M' : JumpMarket d} (h : SameMkt M M') (p : ℝ × ℝ) : FLp M' p = FLp M p := by
  unfold FLp; rw [h.1]

lemma Deg_same {M M' : JumpMarket d} (h : SameMkt M M') (hdeg : Deg M) : Deg M' := by
  intro i
  rw [h.2.1, h.1, h.2.2.2.1]
  exact hdeg i

lemma terminalWealth_same {M M' : JumpMarket d} (h : SameMkt M M') :
    M'.terminalWealth = M.terminalWealth := by
  funext g w
  have h5 := h.2.2.2.2
  unfold JumpMarket.terminalWealth JumpMarket.phi
  simp only [h.1, h.2.1]
  generalize hT : M'.T = T'
  rw [h5] at hT
  subst hT
  rfl

/-- The value comparison for one strategy, in the degenerate case. -/
lemma Vpi_le_deg (M M' : JumpMarket d) (hdeg : Deg M) (hsame : SameMkt M M')
    (gamma alpha C : ℝ) (h0 : 0 ≤ alpha) (h1 : alpha < 1)
    (hC : ∀ p ∈ M.E, |M.U p.2 - M'.U p.2| ≤ C * M.bfun gamma p)
    (g : HistPolicy d) (Pr : ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    {p : ℝ × ℝ} [IsProbabilityMeasure (Pr p)] (hp : p ∈ M.E)
    (hflow : ∀ᵐ w ∂(Pr p), ∀ i, w i ∈ FLp M p) :
    M.Vpi g Pr p ≤ M'.Vpi g Pr p +
      ENNReal.ofReal (C * Real.exp (M.T * M.mubar) / (1 - alpha) * M.bfun gamma p) := by
  unfold JumpMarket.Vpi
  rw [terminalWealth_same hsame]
  set K := C * Real.exp (M.T * M.mubar) / (1 - alpha) * M.bfun gamma p with hK
  calc ∫⁻ w, ENNReal.ofReal (M.U (M.terminalWealth g w)) ∂(Pr p)
      ≤ ∫⁻ w, (ENNReal.ofReal (M'.U (M.terminalWealth g w)) + ENNReal.ofReal K) ∂(Pr p) := by
        apply lintegral_mono_ae
        filter_upwards [hflow] with w hw
        have hz := terminalWealth_deg M hdeg g p w hw
        set y := M.terminalWealth g w with hy
        have hx := E_mem_nonneg M hp
        have hy0 : 0 ≤ y := by
          rcases hz with h | h
          · rw [h]
          · rw [h]; positivity
        have hyz : y ≤ p.2 * Real.exp (M.rho * (M.T - p.1)) := by
          rcases hz with h | h
          · rw [h]; positivity
          · rw [h]
        have hpy : (p.1, y) ∈ M.E := ⟨hp.1, hy0⟩
        have hb := hC (p.1, y) hpy
        have hbpos : 0 < M.bfun gamma (p.1, y) := by
          unfold JumpMarket.bfun; simp only; positivity
        have hCnn : 0 ≤ C := by
          by_contra hneg
          push_neg at hneg
          have := mul_neg_of_neg_of_pos hneg hbpos
          linarith [abs_nonneg (M.U y - M'.U y)]
        have hkey := one_add_z_le M hp h0 h1
        have h3 : C * M.bfun gamma (p.1, y) ≤ K := by
          rw [hK]
          unfold JumpMarket.bfun
          simp only
          have hE := Real.exp_pos (gamma * (M.T - p.1))
          have h4 : 1 + y ≤ Real.exp (M.T * M.mubar) / (1 - alpha) * (1 + p.2) := by linarith
          calc C * (Real.exp (gamma * (M.T - p.1)) * (1 + y))
              ≤ C * (Real.exp (gamma * (M.T - p.1)) *
                  (Real.exp (M.T * M.mubar) / (1 - alpha) * (1 + p.2))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hE.le) hCnn
            _ = C * Real.exp (M.T * M.mubar) / (1 - alpha) *
                  (Real.exp (gamma * (M.T - p.1)) * (1 + p.2)) := by ring
        calc ENNReal.ofReal (M.U y) ≤ ENNReal.ofReal (M'.U y + |M.U y - M'.U y|) :=
              ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (M.U y - M'.U y)])
          _ ≤ ENNReal.ofReal (M'.U y) + ENNReal.ofReal |M.U y - M'.U y| := ENNReal.ofReal_add_le
          _ ≤ ENNReal.ofReal (M'.U y) + ENNReal.ofReal K :=
              add_le_add le_rfl (ENNReal.ofReal_le_ofReal (hb.trans h3))
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-! ### Relaxed controls in the degenerate case. -/

lemma phiRel_deg (hdeg : Deg M) (α : RelaxedControl d) (s x : ℝ) (hs : 0 ≤ s) :
    M.phiRel α s x = x * Real.exp (M.rho * s) := by
  unfold JumpMarket.phiRel
  have h : ∀ r : ℝ,
      ∫ u, (M.rho + ∑ i, (u : Fin d → ℝ) i * (M.mu i - M.rho)) ∂(α.1 r).toMeasure = M.rho := by
    intro r
    have : (fun u : Ucal d => M.rho + ∑ i, (u : Fin d → ℝ) i * (M.mu i - M.rho))
        = fun _ => M.rho := by
      funext u
      rw [Finset.sum_eq_zero (fun i _ => by rw [(hdeg i).1, sub_self, mul_zero]), add_zero]
    rw [this, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  simp_rw [h]
  rw [setIntegral_const, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, sub_zero, mul_comm s]

lemma QRel_deg (hdeg : Deg M) (α : RelaxedControl d) (p : ℝ × ℝ) : M.QRel α p = Qdeg M p := by
  haveI := M.QY_prob
  unfold Qdeg
  change (densT M p).bind _ = _
  rw [← Measure.bind_dirac_eq_map _ (by fun_prop)]
  apply Measure.bind_congr_right
  filter_upwards [densT_ae_pos M p] with s hs
  have hae : ∀ᵐ uy : Ucal d × (Fin d → ℝ) ∂((α.1 s).toMeasure.prod M.QY), uy.2 = 0 := by
    rw [ae_iff]
    have : {uy : Ucal d × (Fin d → ℝ) | ¬ uy.2 = 0} = Set.univ ×ˢ {y : Fin d → ℝ | ¬ y = 0} := by
      ext uy; simp
    rw [this, Measure.prod_prod, ae_iff.mp (QY_ae_zero M hdeg), mul_zero]
  have hfun : (fun uy : Ucal d × (Fin d → ℝ) =>
      (p.1 + s, M.phiRel α s p.2 * (1 + ∑ i, (uy.1 : Fin d → ℝ) i * uy.2 i)))
      =ᵐ[(α.1 s).toMeasure.prod M.QY] fun _ => (p.1 + s, p.2 * Real.exp (M.rho * s)) := by
    filter_upwards [hae] with uy hy
    rw [hy, phiRel_deg M hdeg α s p.2 hs.le]; simp
  rw [Measure.map_congr hfun, Measure.map_const, measure_univ, one_smul]

lemma LRel_deg (hdeg : Deg M) (v : ℝ × ℝ → ℝ≥0∞) (α : RelaxedControl d) {p : ℝ × ℝ}
    (hp : p ∈ M.E) :
    M.LRel v α p = ENNReal.ofReal (Real.exp (-M.lam * (M.T - p.1)) *
      M.U (p.2 * Real.exp (M.rho * (M.T - p.1)))) + ∫⁻ q, v q ∂(Qdeg M p) := by
  unfold JumpMarket.LRel JumpMarket.rRel
  rw [phiRel_deg M hdeg α _ _ (by linarith [(E_mem_t M hp).2]), QRel_deg M hdeg α p]

lemma AstarRel_deg (hdeg : Deg M) (v : ℝ × ℝ → ℝ≥0∞) {p : ℝ × ℝ} (hp : p ∈ M.E) :
    M.AstarRel v p = Set.univ := by
  ext α
  simp only [Set.mem_univ, iff_true]
  show ∀ α' : RelaxedControl d, M.LRel v α' p ≤ M.LRel v α p
  intro α'
  rw [LRel_deg M hdeg v α hp, LRel_deg M hdeg v α' hp]

end Deg

section Main
variable {d : ℕ}

theorem t937_core (M Mtilde : JumpMarket d)
    (gamma alpha : ℝ) (hb : M.IsBoundingFunction (M.bfun gamma) alpha)
    (hbt : Mtilde.IsBoundingFunction (M.bfun gamma) alpha) (halpha : alpha < 1)
    (hsame : SameMkt M Mtilde)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g))
    (hnd : (¬ ∀ i : Fin d, M.mu i = M.rho ∧ M.QY {y | y i ≠ 0} = 0) → False) :
    (∀ C : ℝ, (∀ p ∈ M.E, |M.U p.2 - Mtilde.U p.2| ≤ C * M.bfun gamma p) →
      ∀ p ∈ M.E,
        M.V Pr p ≤ Mtilde.V Pr p +
            ENNReal.ofReal (C * Real.exp (M.T * M.mubar) / (1 - alpha) * M.bfun gamma p) ∧
          Mtilde.V Pr p ≤ M.V Pr p +
            ENNReal.ofReal (C * Real.exp (M.T * M.mubar) / (1 - alpha) * M.bfun gamma p)) ∧
    (∀ Mn : ℕ → JumpMarket d, (∀ n, SameMkt M (Mn n)) →
      (∀ n, (Mn n).IsBoundingFunction (M.bfun gamma) alpha) →
      (∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ p ∈ M.E,
        |(Mn n).U p.2 - M.U p.2| ≤ ε * M.bfun gamma p) →
      ∀ p ∈ M.E,
        (LsSeq (fun n => (Mn n).AstarRel ((Mn n).V Pr) p)).Nonempty ∧
        LsSeq (fun n => (Mn n).AstarRel ((Mn n).V Pr) p) ⊆ M.AstarRel (M.V Pr) p) := by
  by_cases hdeg : Deg M
  swap
  · exact (hnd hdeg).elim
  have h0 : 0 ≤ alpha := alpha_nonneg M hdeg hb
  have hdeg' : Deg Mtilde := Deg_same hsame hdeg
  refine ⟨fun C hC p hp => ⟨?_, ?_⟩, fun Mn hMn _ _ p hp => ⟨?_, ?_⟩⟩
  · unfold JumpMarket.V
    refine iSup₂_le fun g hg => ?_
    haveI := (hPr g).1 p
    calc M.Vpi g (Pr g) p ≤ Mtilde.Vpi g (Pr g) p + _ :=
          Vpi_le_deg M Mtilde hdeg hsame gamma alpha C h0 halpha hC g (Pr g) hp
            (Pr_FLp_all M hdeg g (Pr g) (hPr g) p)
      _ ≤ _ := add_le_add
          (le_iSup₂ (f := fun g (_ : IsHistPolicy g) => Mtilde.Vpi g (Pr g) p) g hg) le_rfl
  · unfold JumpMarket.V
    refine iSup₂_le fun g hg => ?_
    haveI := (hPr g).1 p
    have hC' : ∀ q ∈ Mtilde.E, |Mtilde.U q.2 - M.U q.2| ≤ C * Mtilde.bfun gamma q := by
      intro q hq
      rw [bfun_same hsame, abs_sub_comm]
      exact hC q (by rwa [E_same hsame] at hq)
    have hp' : p ∈ Mtilde.E := by rwa [E_same hsame]
    have hflow : ∀ᵐ w ∂(Pr g p), ∀ i, w i ∈ FLp Mtilde p := by
      rw [FLp_same hsame]; exact Pr_FLp_all M hdeg g (Pr g) (hPr g) p
    have := Vpi_le_deg Mtilde M hdeg' (SameMkt.symm' hsame) gamma alpha C h0 halpha hC' g
      (Pr g) hp' hflow
    rw [bfun_same hsame, T_same hsame, mubar_same hsame] at this
    calc Mtilde.Vpi g (Pr g) p ≤ M.Vpi g (Pr g) p + _ := this
      _ ≤ _ := add_le_add
          (le_iSup₂ (f := fun g (_ : IsHistPolicy g) => M.Vpi g (Pr g) p) g hg) le_rfl
  · refine ⟨(bondC d).toRelaxed, fun _ => (bondC d).toRelaxed, fun n => ?_,
      tendsto_const_nhds.mapClusterPt⟩
    show (bondC d).toRelaxed ∈ (Mn n).AstarRel ((Mn n).V Pr) p
    rw [AstarRel_deg (Mn n) (Deg_same (hMn n) hdeg) _ (by rwa [E_same (hMn n)])]
    exact Set.mem_univ _
  · rw [AstarRel_deg M hdeg _ hp]
    exact Set.subset_univ _

end Main


/-- Theorem 9.3.7, final form. -/
theorem t937_final {d : ℕ} (M Mtilde : JumpMarket d)
    (gamma alpha : ℝ) (hb : M.IsBoundingFunction (M.bfun gamma) alpha)
    (hbt : Mtilde.IsBoundingFunction (M.bfun gamma) alpha) (halpha : alpha < 1)
    (hsame : Mtilde.rho = M.rho ∧ Mtilde.mu = M.mu ∧ Mtilde.lam = M.lam ∧ Mtilde.QY = M.QY ∧
      Mtilde.T = M.T)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g)) :
    (∀ C : ℝ, (∀ p ∈ M.E, |M.U p.2 - Mtilde.U p.2| ≤ C * M.bfun gamma p) →
      ∀ p ∈ M.E,
        M.V Pr p ≤ Mtilde.V Pr p +
            ENNReal.ofReal (C * Real.exp (M.T * M.mubar) / (1 - alpha) * M.bfun gamma p) ∧
          Mtilde.V Pr p ≤ M.V Pr p +
            ENNReal.ofReal (C * Real.exp (M.T * M.mubar) / (1 - alpha) * M.bfun gamma p)) ∧
    (∀ Mn : ℕ → JumpMarket d, (∀ n, (Mn n).rho = M.rho ∧ (Mn n).mu = M.mu ∧ (Mn n).lam = M.lam ∧
      (Mn n).QY = M.QY ∧ (Mn n).T = M.T) →
      (∀ n, (Mn n).IsBoundingFunction (M.bfun gamma) alpha) →
      (∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ p ∈ M.E,
        |(Mn n).U p.2 - M.U p.2| ≤ ε * M.bfun gamma p) →
      ∀ p ∈ M.E,
        (LsSeq (fun n => (Mn n).AstarRel ((Mn n).V Pr) p)).Nonempty ∧
        LsSeq (fun n => (Mn n).AstarRel ((Mn n).V Pr) p) ⊆ M.AstarRel (M.V Pr) p) :=
  t937_core M Mtilde gamma alpha hb hbt halpha hsame Pr hPr
    (fun hnd => no_chain_law_of_nondegenerate M hnd Pr hPr)

end MDPFinance.JumpMarkets

open MDPFinance.JumpMarkets


theorem solution {d : ℕ} (M Mtilde : JumpMarket d)
    (gamma alpha : ℝ) (hb : M.IsBoundingFunction (M.bfun gamma) alpha)
    (hbt : Mtilde.IsBoundingFunction (M.bfun gamma) alpha) (halpha : alpha < 1)
    (hsame : Mtilde.rho = M.rho ∧ Mtilde.mu = M.mu ∧ Mtilde.lam = M.lam ∧ Mtilde.QY = M.QY ∧
      Mtilde.T = M.T)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g)) :
    (∀ C : ℝ, (∀ p ∈ M.E, |M.U p.2 - Mtilde.U p.2| ≤ C * M.bfun gamma p) →
      ∀ p ∈ M.E,
        M.V Pr p ≤ Mtilde.V Pr p +
            ENNReal.ofReal (C * Real.exp (M.T * M.mubar) / (1 - alpha) * M.bfun gamma p) ∧
          Mtilde.V Pr p ≤ M.V Pr p +
            ENNReal.ofReal (C * Real.exp (M.T * M.mubar) / (1 - alpha) * M.bfun gamma p)) ∧
    (∀ Mn : ℕ → JumpMarket d, (∀ n, (Mn n).rho = M.rho ∧ (Mn n).mu = M.mu ∧ (Mn n).lam = M.lam ∧
      (Mn n).QY = M.QY ∧ (Mn n).T = M.T) →
      (∀ n, (Mn n).IsBoundingFunction (M.bfun gamma) alpha) →
      (∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ p ∈ M.E,
        |(Mn n).U p.2 - M.U p.2| ≤ ε * M.bfun gamma p) →
      ∀ p ∈ M.E,
        (LsSeq (fun n => (Mn n).AstarRel ((Mn n).V Pr) p)).Nonempty ∧
        LsSeq (fun n => (Mn n).AstarRel ((Mn n).V Pr) p) ⊆ M.AstarRel (M.V Pr) p) := by
  exact t937_final M Mtilde gamma alpha hb hbt halpha hsame Pr hPr
