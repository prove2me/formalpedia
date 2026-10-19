-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedLongReference_l1_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:29:56.844044+00:00
-- url     : https://prove2.me/submissions/d0bd6e82-76e5-47e2-b2de-8b8c810582f0

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194
import Definitions.Def_OAIE3v2B196

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalImageDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem density_l1_le_of_bounded_tests {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f μ) (hgi : Integrable g μ) {ε : ℝ}
    (he : ∀ φ : X → ℝ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      |(∫ x, f x*φ x ∂μ)-(∫ x, g x*φ x ∂μ)| ≤ ε) :
    (∫ x, |f x-g x| ∂μ) ≤ ε := by
  let φ := fun x => if 0 ≤ f x-g x then (1 : ℝ) else -1
  have hφ : Measurable φ := Measurable.ite (measurableSet_le measurable_const (hf.sub hg))
    measurable_const measurable_const
  have hbound : ∀ x, ‖φ x‖ ≤ 1 := by
    intro x
    dsimp [φ]
    split_ifs <;> norm_num
  have hif := hfi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hig := hgi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hid : (∫ x, f x*φ x ∂μ)-(∫ x, g x*φ x ∂μ) = ∫ x, |f x-g x| ∂μ := by
    rw [← integral_sub hif hig]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [← sub_mul]
    dsimp [φ]
    split_ifs with hx
    · rw [mul_one, abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      ring
  have h := he φ hφ hbound
  rw [hid, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem selectedCoefficientProfile_lipschitz {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (selectedCoefficientProfile s f) := by
  simpa only [mul_one, selectedCoefficientProfile] using hf.comp (selectedCoefficientEquiv_lipschitz s)

end Erdos3

end

section

namespace Erdos3

variable {I J R : Type*} [Fintype I] (s : I ↪ J)

theorem selectedCoefficientEquiv_on_selected
    (p : (UnselectedColumn s → R) × (I → R)) (i : I) :
    selectedCoefficientEquiv s R p (s i) = p.2 i := by
  have h : selectedFreeFirstEquiv s (Sum.inr i) = s i := rfl
  rw [← h, selectedCoefficientEquiv_apply, Equiv.symm_apply_apply]
  rfl

theorem selectedCoefficientEquiv_on_unselected
    (p : (UnselectedColumn s → R) × (I → R)) (i : UnselectedColumn s) :
    selectedCoefficientEquiv s R p i.val = p.1 i := by
  have h : selectedFreeFirstEquiv s (Sum.inl i) = i.val := rfl
  rw [← h, selectedCoefficientEquiv_apply, Equiv.symm_apply_apply]
  rfl

theorem selectedCoefficientEquiv_eq_of_coordinates
    (f : J → R) (p : (UnselectedColumn s → R) × (I → R))
    (hfree : ∀ i : UnselectedColumn s, f i.val = p.1 i)
    (hselected : ∀ i, f (s i) = p.2 i) :
    f = selectedCoefficientEquiv s R p := by
  classical
  funext j
  by_cases hj : j ∈ Set.range s
  · obtain ⟨i, rfl⟩ := hj
    exact (hselected i).trans (selectedCoefficientEquiv_on_selected s p i).symm
  · exact (hfree ⟨j, hj⟩).trans (selectedCoefficientEquiv_on_unselected s p ⟨j, hj⟩).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SelectedDensityNormalization
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem selectedCoefficientMeasurableEquiv_preserving {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) : MeasurePreserving (selectedCoefficientMeasurableEquiv s) volume volume := by
  have hm := (volume_measurePreserving_piCongrLeft (fun _ : J => ℝ) (selectedFreeFirstEquiv s)).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : UnselectedColumn s ⊕ I => ℝ))
  convert hm using 1
  funext p j
  simp only [Function.comp_def, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft', Equiv.coe_fn_symm_mk, eq_rec_constant]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ENNReal

theorem pi_count_measure {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] [∀ i, Countable (X i)] :
    Measure.pi (fun i => (Measure.count : Measure (X i))) =
      (Measure.count : Measure (∀ i, X i)) := by
  apply Measure.ext_of_singleton
  intro x
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SigmaFiniteProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem sigmaFiniteProductMeasure_flatten {D : Type*} [Fintype D] {I : D → Type*}
    [∀ d, Fintype (I d)] {X : (Σ d, I d) → Type*}
    [∀ s, MeasurableSpace (X s)] (μ : ∀ s, Measure (X s)) [∀ s, SigmaFinite (μ s)] :
    (Measure.pi (fun d => Measure.pi (fun i => μ ⟨d, i⟩))).map
      (fun x (s : Σ d, I d) => x s.1 s.2) = Measure.pi μ := by
  have hm : Measurable (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) :=
    measurable_pi_iff.mpr (fun s => (measurable_pi_apply s.2).comp (measurable_pi_apply s.1))
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi (fun i => s ⟨d, i⟩)) := by
    ext x
    constructor
    · intro hx d _ i _
      exact hx ⟨d, i⟩ (Set.mem_univ _)
    · intro hx t _
      exact hx t.1 (Set.mem_univ _) t.2 (Set.mem_univ _)
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_sigma]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientJetScalar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

theorem coefficientJetScalarEquiv_measurePreserving (O : Fin m → Type*)
    [∀ j, Fintype (O j)] (a : LayerSamplerAxis I n) :
    MeasurePreserving (coefficientJetScalarEquiv O a)
      (coefficientJetAxisReference O a)
      (Measure.pi (fun _ : O a.1 => coefficientJetScalarReference a)) := by
  rcases a with ⟨j, i | i⟩
  · exact MeasurePreserving.id (volume : Measure (O j → ℝ))
  · change MeasurePreserving id (Measure.count : Measure (O j → ℤ))
      (Measure.pi (fun _ : O j => (Measure.count : Measure ℤ)))
    rw [pi_count_measure]
    exact MeasurePreserving.id _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ContinuousOutputBox
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem continuousOutputBoxMeasure_le (I : Type*) [Fintype I] (R : ℝ≥0) :
    continuousOutputBoxMeasure I R ≤ volume := Measure.restrict_le_self

theorem continuousOutputBox_mem_iff {I : Type*} [Fintype I] (R : ℝ≥0) (x : I → ℝ) :
    x ∈ continuousOutputBox I R ↔ ‖x‖ ≤ (R : ℝ) := by
  constructor
  · intro hx
    apply (pi_norm_le_iff_of_nonneg R.coe_nonneg).mpr
    intro i
    exact (Real.norm_eq_abs _).trans_le (abs_le.mpr ⟨hx.1 i, hx.2 i⟩)
  · intro hx
    have hi (i) : |x i| ≤ (R : ℝ) :=
      (Real.norm_eq_abs _).symm.trans_le ((norm_le_pi_norm x i).trans hx)
    exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩

theorem continuousOutputBoxMeasure_mass (I : Type*) [Fintype I] (R : ℝ≥0) :
    (continuousOutputBoxMeasure I R).real Set.univ = (2*(R : ℝ))^Fintype.card I := by
  rw [measureReal_def, continuousOutputBoxMeasure, Measure.restrict_apply_univ]
  have horder : (fun _ : I => -(R : ℝ)) ≤ (fun _ => (R : ℝ)) := fun _ => neg_le_self R.coe_nonneg
  simp only [continuousOutputBox, Real.volume_Icc_pi_toReal horder, sub_neg_eq_add,
    ← two_mul, Finset.prod_const, Finset.card_univ]

theorem continuousOutputBoxMeasure_prod {W I : Type*} [MeasurableSpace W] [Fintype I]
    (μ : Measure W) [SFinite μ] (R : ℝ≥0) :
    μ.prod (continuousOutputBoxMeasure I R) =
      (μ.prod volume).restrict (Set.univ ×ˢ continuousOutputBox I R) := by
  simpa only [Measure.restrict_univ, continuousOutputBoxMeasure] using
    (Measure.prod_restrict (μ := μ) (ν := (volume : Measure (I → ℝ))) Set.univ (continuousOutputBox I R))

theorem continuousOutputBoxMeasure_prod_mass {W I : Type*} [MeasurableSpace W] [Fintype I]
    (μ : Measure W) [IsProbabilityMeasure μ] (R : ℝ≥0) :
    (μ.prod (continuousOutputBoxMeasure I R)).real Set.univ = (2*(R : ℝ))^Fintype.card I := by
  simpa only [Set.univ_prod_univ, probReal_univ, one_mul, continuousOutputBoxMeasure_mass] using
    (measureReal_prod_prod (μ := μ) (ν := continuousOutputBoxMeasure I R) Set.univ Set.univ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedOutputL1
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem selectedOutputSlice_lipschitz {I J : Type*} [Fintype I] [Fintype J]
    (s : J ↪ I) {f : (I → ℝ) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (x : UnselectedColumn s → ℝ) : LipschitzWith K (selectedOutputSlice s f x) := by
  change LipschitzWith K (selectedCoefficientProfile s f ∘ Prod.mk x)
  simpa only [mul_one] using
    (selectedCoefficientProfile_lipschitz s hf).comp (LipschitzWith.prodMk_left x)

theorem selectedOutputSlice_support_right {I J : Type*} [Fintype I] [Fintype J]
    (s : J ↪ I) {f : (I → ℝ) → ℝ} {R : ℝ} (hf : ∀ v, R < ‖v‖ → f v = 0)
    (x : UnselectedColumn s → ℝ) (y : J → ℝ) (hy : R < ‖y‖) :
    selectedOutputSlice s f x y = 0 := by
  apply hf
  rw [selectedCoefficientEquiv_norm]
  exact hy.trans_le (norm_snd_le (x, y))

theorem selectedOutputSlice_support_left {I J : Type*} [Fintype I] [Fintype J]
    (s : J ↪ I) {f : (I → ℝ) → ℝ} {R : ℝ} (hf : ∀ v, R < ‖v‖ → f v = 0)
    (x : UnselectedColumn s → ℝ) (y : J → ℝ) (hx : R < ‖x‖) :
    selectedOutputSlice s f x y = 0 := by
  apply hf
  rw [selectedCoefficientEquiv_norm]
  exact hx.trans_le (norm_fst_le (x, y))

theorem retainedSelectedOutputEquiv_preserving {W I J : Type*} [MeasurableSpace W]
    [Fintype I] [Fintype J] (s : J ↪ I) (μ : Measure W) [SFinite μ] :
    MeasurePreserving (retainedSelectedOutputEquiv (W := W) s)
      ((μ.prod volume).prod volume) (μ.prod volume) :=
  ((MeasurePreserving.id μ).prod (selectedCoefficientMeasurableEquiv_preserving s)).comp
    (measurePreserving_prodAssoc μ volume volume)

theorem retainedSelectedOutput_integrable {W I J : Type*} [MeasurableSpace W]
    [Fintype I] [Fintype J] (s : J ↪ I) (μ : Measure W) [SFinite μ]
    {f : W × (I → ℝ) → ℝ} (hf : Integrable f (μ.prod volume)) :
    Integrable (fun p : (W × (UnselectedColumn s → ℝ)) × (J → ℝ) =>
      f (p.1.1, selectedCoefficientEquiv s ℝ (p.1.2, p.2))) ((μ.prod volume).prod volume) :=
  (retainedSelectedOutputEquiv_preserving s μ).integrable_comp_of_integrable hf

theorem retainedSelectedOutput_integral {W I J : Type*} [MeasurableSpace W]
    [Fintype I] [Fintype J] (s : J ↪ I) (μ : Measure W) [SFinite μ] (f : W × (I → ℝ) → ℝ) :
    (∫ p : (W × (UnselectedColumn s → ℝ)) × (J → ℝ),
      f (p.1.1, selectedCoefficientEquiv s ℝ (p.1.2, p.2)) ∂(μ.prod volume).prod volume) =
      ∫ p, f p ∂μ.prod volume :=
  (retainedSelectedOutputEquiv_preserving s μ).integral_comp
    (retainedSelectedOutputEquiv (W := W) s).measurableEmbedding f

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem selectedOutput_restricted_l1 {W I J : Type*} [MeasurableSpace W]
    [Fintype I] [Fintype J] (s : J ↪ I) (μ : Measure W) [SFinite μ]
    (R : ℝ≥0) (f : W × (I → ℝ) → ℝ) (hf : Integrable f (μ.prod volume))
    {ε : ℝ} (he : (∫ p, |f p| ∂μ.prod volume) ≤ ε) :
    let ν := μ.prod (continuousOutputBoxMeasure (UnselectedColumn s) R)
    let F := fun p : (W × (UnselectedColumn s → ℝ)) × (J → ℝ) =>
      f (p.1.1, selectedCoefficientEquiv s ℝ (p.1.2, p.2))
    Integrable F (ν.prod volume) ∧ (∫ p, |F p| ∂ν.prod volume) ≤ ε := by
  dsimp only
  have hi := retainedSelectedOutput_integrable s μ hf
  have hle : (μ.prod (continuousOutputBoxMeasure (UnselectedColumn s) R)).prod volume ≤
      (μ.prod (volume : Measure (UnselectedColumn s → ℝ))).prod (volume : Measure (J → ℝ)) :=
    Measure.prod_mono (Measure.prod_mono le_rfl (continuousOutputBoxMeasure_le _ R)) le_rfl
  refine ⟨hi.mono_measure hle, ?_⟩
  have ha : Integrable (fun p : (W × (UnselectedColumn s → ℝ)) × (J → ℝ) =>
      |f (p.1.1, selectedCoefficientEquiv s ℝ (p.1.2, p.2))|) ((μ.prod volume).prod volume) := by
    simpa only [Real.norm_eq_abs] using hi.norm
  calc
    _ ≤ ∫ p : (W × (UnselectedColumn s → ℝ)) × (J → ℝ),
        |f (p.1.1, selectedCoefficientEquiv s ℝ (p.1.2, p.2))| ∂(μ.prod volume).prod volume :=
      integral_mono_measure hle (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) ha
    _ = ∫ p, |f p| ∂μ.prod volume := retainedSelectedOutput_integral s μ (fun p => |f p|)
    _ ≤ ε := he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeDensityL1
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem densityDifference_lipschitz {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf+Kg) (fun x => |f x-g x|) := by
  simpa only [one_mul, Function.comp_def, Real.norm_eq_abs] using lipschitzWith_one_norm.comp (hf.sub hg)

theorem rectangular_density_l1_sum_le {J : Type*} [Fintype J]
    (f g : (J → ℝ) → ℝ) {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hfs : ∀ x, R < ‖x‖ → f x = 0) (hgs : ∀ x, R < ‖x‖ → g x = 0) :
    (∑' k : J → ℤ, |f (rectangularLatticePoint a S k)-g (rectangularLatticePoint a S k)|)/(∏ j, S j) ≤
      (∫ x, |f x-g x|)+(2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ := by
  have hs : ∀ x, R < ‖x‖ → |f x-g x| = 0 := by
    intro x hx
    rw [hfs x hx, hgs x hx, sub_self, abs_zero]
  have he := rectangularLattice_quadrature (fun x => |f x-g x|) (densityDifference_lipschitz hf hg)
    a S hS hR hδ hδ1 hmesh hs
  have hu := (le_abs_self _).trans he
  change _ ≤ (2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ at hu
  linarith

theorem rectangular_density_finite_l1_le {J : Type*} [Fintype J]
    (f g : (J → ℝ) → ℝ) {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hfs : ∀ x, R < ‖x‖ → f x = 0) (hgs : ∀ x, R < ‖x‖ → g x = 0)
    (s : Finset (J → ℤ)) :
    (∑ k ∈ s, |f (rectangularLatticePoint a S k)-g (rectangularLatticePoint a S k)|)/(∏ j, S j) ≤
      (∫ x, |f x-g x|)+(2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ := by
  have hs : ∀ x, R < ‖x‖ → |f x-g x| = 0 := by
    intro x hx
    rw [hfs x hx, hgs x hx, sub_self, abs_zero]
  have hsum := rectangularWeight_summable (fun x => |f x-g x|) a S hS hs
  apply le_trans (div_le_div_of_nonneg_right
    (hsum.sum_le_tsum s (fun _ _ => abs_nonneg _)) (Finset.prod_nonneg (fun j _ => (hS j).le)))
  exact rectangular_density_l1_sum_le f g hf hg a S hS hR hδ hδ1 hmesh hfs hgs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MixedOutputGrid
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem norm_masked_density_sum_sub_le {X : Type*} (s : Finset X)
    (a b mask : X → ℝ) (φ : X → ℂ) {G : ℝ} (_hG : 0 ≤ G)
    (hm : ∀ x ∈ s, |mask x| ≤ G) (hφ : ∀ x ∈ s, ‖φ x‖ ≤ 1) :
    ‖(∑ x ∈ s, ((mask x*a x : ℝ) : ℂ)*φ x)-
      (∑ x ∈ s, ((mask x*b x : ℝ) : ℂ)*φ x)‖ ≤ G*(∑ x ∈ s, |a x-b x|) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  have he : ((mask x*a x : ℝ) : ℂ)*φ x-((mask x*b x : ℝ) : ℂ)*φ x =
      ((mask x*(a x-b x) : ℝ) : ℂ)*φ x := by push_cast; ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |mask x| * |a x-b x| * 1 := mul_le_mul_of_nonneg_left (hφ x hx) (by positivity)
    _ ≤ G*|a x-b x| := by rw [mul_one]; exact mul_le_mul_of_nonneg_right (hm x hx) (abs_nonneg _)

theorem gridDensityTest_l1_bound {J : Type*} [Fintype J]
    (f g : (J → ℝ) → ℝ) {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ G : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hfs : ∀ x, R < ‖x‖ → f x = 0) (hgs : ∀ x, R < ‖x‖ → g x = 0)
    (s : Finset (J → ℤ)) (mask : (J → ℤ) → ℝ) (φ : (J → ℤ) → ℂ)
    (hG : 0 ≤ G) (hm : ∀ k ∈ s, |mask k| ≤ G) (hφ : ∀ k ∈ s, ‖φ k‖ ≤ 1) :
    ‖gridDensityTest f a S s mask φ-gridDensityTest g a S s mask φ‖ ≤
      G*((∫ x, |f x-g x|)+(2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ) := by
  have hprod : 0 < ∏ j, S j := Finset.prod_pos (fun j _ => hS j)
  unfold gridDensityTest
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hprod.le]
  calc
    _ ≤ (G*(∑ k ∈ s, |f (rectangularLatticePoint a S k)-g (rectangularLatticePoint a S k)|))/(∏ j, S j) :=
      div_le_div_of_nonneg_right (norm_masked_density_sum_sub_le s _ _ mask φ hG hm hφ) hprod.le
    _ = G*((∑ k ∈ s, |f (rectangularLatticePoint a S k)-g (rectangularLatticePoint a S k)|)/(∏ j, S j)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (rectangular_density_finite_l1_le f g hf hg a S hS hR hδ hδ1 hmesh hfs hgs s) hG

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem partial_gridDensityTest_family_error_ae {Z J : Type*} [MeasurableSpace Z] [Fintype J]
    (μ : Measure Z) [IsFiniteMeasure μ] (f g : Z → (J → ℝ) → ℝ)
    {Kf Kg : ℝ≥0} (a S : Z → J → ℝ) (hS : ∀ z j, 0 < S z j) {R δ G ε : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z j, 1/S z j ≤ δ)
    (hgood : ∀ᵐ z ∂μ, LipschitzWith Kf (f z) ∧ LipschitzWith Kg (g z) ∧
      (∀ x, R < ‖x‖ → f z x = 0) ∧ (∀ x, R < ‖x‖ → g z x = 0))
    (s : Z → Finset (J → ℤ)) (mask : Z → (J → ℤ) → ℝ) (φ : Z → (J → ℤ) → ℂ)
    (hG : 0 ≤ G) (hm : ∀ z k, k ∈ s z → |mask z k| ≤ G) (hφ : ∀ z k, k ∈ s z → ‖φ z k‖ ≤ 1)
    (hfg : Integrable (fun p : Z × (J → ℝ) => f p.1 p.2-g p.1 p.2) (μ.prod volume))
    (he : (∫ p : Z × (J → ℝ), |f p.1 p.2-g p.1 p.2| ∂μ.prod volume) ≤ ε) :
    ‖∫ z, gridDensityTest (f z) (a z) (S z) (s z) (mask z) (φ z)-gridDensityTest (g z) (a z) (S z) (s z) (mask z) (φ z) ∂μ‖ ≤
      G*(ε+μ.real Set.univ*((2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ)) := by
  let E := (2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ
  have habs : Integrable (fun p : Z × (J → ℝ) => |f p.1 p.2-g p.1 p.2|) (μ.prod volume) := by
    simpa only [Real.norm_eq_abs] using hfg.norm
  have hL := habs.integral_prod_left
  have hi : Integrable (fun z => G*((∫ x, |f z x-g z x|)+E)) μ :=
    (hL.add (integrable_const E)).const_mul G
  have hiter : (∫ z, (∫ x, |f z x-g z x|) ∂μ) ≤ ε := by
    rw [← integral_prod _ habs]
    exact he
  calc
    _ ≤ ∫ z, ‖gridDensityTest (f z) (a z) (S z) (s z) (mask z) (φ z)-gridDensityTest (g z) (a z) (S z) (s z) (mask z) (φ z)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, G*((∫ x, |f z x-g z x|)+E) ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hi
      filter_upwards [hgood] with z hz
      exact gridDensityTest_l1_bound (f z) (g z) hz.1 hz.2.1 (a z) (S z) (hS z) hR hδ hδ1 (hmesh z)
        hz.2.2.1 hz.2.2.2 (s z) (mask z) (φ z) hG (hm z) (hφ z)
    _ = G*((∫ z, (∫ x, |f z x-g z x|) ∂μ)+μ.real Set.univ*E) := by
      rw [integral_const_mul, integral_add hL (integrable_const E), integral_const, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hiter le_rfl) hG

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem mixed_output_grid_error {W I J : Type*} [MeasurableSpace W]
    [Fintype I] [Fintype J] (select : J ↪ I) (μ : Measure W) [IsProbabilityMeasure μ]
    (f g : W → (I → ℝ) → ℝ) {Kf Kg : ℝ≥0} (R : ℝ≥0)
    (hgood : ∀ᵐ w ∂μ, LipschitzWith Kf (f w) ∧ LipschitzWith Kg (g w) ∧
      (∀ v, (R : ℝ) < ‖v‖ → f w v = 0) ∧ (∀ v, (R : ℝ) < ‖v‖ → g w v = 0))
    (hfg : Integrable (fun p : W × (I → ℝ) => f p.1 p.2-g p.1 p.2) (μ.prod volume))
    {ε : ℝ} (he : (∫ p : W × (I → ℝ), |f p.1 p.2-g p.1 p.2| ∂μ.prod volume) ≤ ε)
    (a S : W × (UnselectedColumn select → ℝ) → J → ℝ)
    (hS : ∀ p j, 0 < S p j) {mesh M : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ p j, 1/S p j ≤ mesh)
    (grid : W × (UnselectedColumn select → ℝ) → Finset (J → ℤ)) (mask : W × (UnselectedColumn select → ℝ) → (J → ℤ) → ℝ)
    (φ : W × (UnselectedColumn select → ℝ) → (J → ℤ) → ℂ)
    (hM : 0 ≤ M) (hmask : ∀ p k, k ∈ grid p → |mask p k| ≤ M)
    (hφ : ∀ p k, k ∈ grid p → ‖φ p k‖ ≤ 1) :
    ‖∫ p : W × (UnselectedColumn select → ℝ),
      gridDensityTest (selectedOutputSlice select (f p.1) p.2) (a p) (S p) (grid p) (mask p) (φ p)-
      gridDensityTest (selectedOutputSlice select (g p.1) p.2) (a p) (S p) (grid p) (mask p) (φ p) ∂μ.prod volume‖ ≤
      M*(ε+(2*(R : ℝ))^Fintype.card (UnselectedColumn select)*
        ((2*(R : ℝ)+2)^Fintype.card J*((Kf : ℝ)+Kg)*mesh)) := by
  let ν := μ.prod (continuousOutputBoxMeasure (UnselectedColumn select) R)
  let F := fun p : W × (UnselectedColumn select → ℝ) => selectedOutputSlice select (f p.1) p.2
  let G := fun p : W × (UnselectedColumn select → ℝ) => selectedOutputSlice select (g p.1) p.2
  let test := fun p => gridDensityTest (F p) (a p) (S p) (grid p) (mask p) (φ p)-
    gridDensityTest (G p) (a p) (S p) (grid p) (mask p) (φ p)
  have hsplit := selectedOutput_restricted_l1 select μ R
    (fun p => f p.1 p.2-g p.1 p.2) hfg he
  have hs : ∀ᵐ p ∂ν, LipschitzWith Kf (F p) ∧ LipschitzWith Kg (G p) ∧
      (∀ y, (R : ℝ) < ‖y‖ → F p y = 0) ∧ (∀ y, (R : ℝ) < ‖y‖ → G p y = 0) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgood] with p hp
    exact ⟨selectedOutputSlice_lipschitz select hp.1 p.2,
      selectedOutputSlice_lipschitz select hp.2.1 p.2,
      selectedOutputSlice_support_right select hp.2.2.1 p.2,
      selectedOutputSlice_support_right select hp.2.2.2 p.2⟩
  have hbound := partial_gridDensityTest_family_error_ae ν F G a S hS R.coe_nonneg
    hmesh0 hmesh1 hmesh hs grid mask φ hM hmask hφ hsplit.1 hsplit.2
  have hrestrict : (∫ p, test p ∂ν) = ∫ p, test p ∂μ.prod volume := by
    change (∫ p, test p ∂μ.prod (continuousOutputBoxMeasure (UnselectedColumn select) R)) = _
    rw [continuousOutputBoxMeasure_prod]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgood] with p hp
    intro hout
    have hx : (R : ℝ) < ‖p.2‖ := lt_of_not_ge (fun hx => hout
      ⟨Set.mem_univ _, (continuousOutputBox_mem_iff R p.2).mpr hx⟩)
    have hF : F p = 0 := funext (fun y => selectedOutputSlice_support_left select hp.2.2.1 p.2 y hx)
    have hG : G p = 0 := funext (fun y => selectedOutputSlice_support_left select hp.2.2.2 p.2 y hx)
    simp only [test, hF, hG, sub_self]
  change ‖∫ p, test p ∂μ.prod volume‖ ≤ _
  rw [← hrestrict]
  simpa only [ν, continuousOutputBoxMeasure_prod_mass] using hbound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ControlledJointGrid
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem integrable_snd_probability {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f : X → ℝ) (hf : Integrable f ν) :
    Integrable (fun x : Z × X => f x.2) (μ.prod ν) := by
  simpa only [one_mul] using
    (integrable_const (1 : ℝ) : Integrable (fun _ : Z => (1 : ℝ)) μ).mul_prod hf

theorem integral_snd_probability {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f : X → ℝ) (hf : Integrable f ν) :
    (∫ x : Z × X, f x.2 ∂μ.prod ν) = ∫ x, f x ∂ν := by
  rw [integral_prod _ (integrable_snd_probability μ ν f hf)]
  simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem fixed_mixed_output_grid_error {I J : Type*} [Fintype I] [Fintype J]
    (select : J ↪ I) (f g : (I → ℝ) → ℝ) {Kf Kg : ℝ≥0} (R : ℝ≥0)
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfs : ∀ v, (R : ℝ) < ‖v‖ → f v = 0)
    (hgs : ∀ v, (R : ℝ) < ‖v‖ → g v = 0)
    (hfg : Integrable (fun v => f v - g v)) {ε : ℝ}
    (he : (∫ v, |f v - g v|) ≤ ε)
    (a S : (UnselectedColumn select → ℝ) → J → ℝ)
    (hS : ∀ v j, 0 < S v j) {mesh M : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ v j, 1 / S v j ≤ mesh)
    (grid : (UnselectedColumn select → ℝ) → Finset (J → ℤ))
    (mask : (UnselectedColumn select → ℝ) → (J → ℤ) → ℝ)
    (φ : (UnselectedColumn select → ℝ) → (J → ℤ) → ℂ)
    (hM : 0 ≤ M) (hmask : ∀ v k, k ∈ grid v → |mask v k| ≤ M)
    (hφ : ∀ v k, k ∈ grid v → ‖φ v k‖ ≤ 1) :
    ‖∫ v, gridDensityTest (selectedOutputSlice select f v) (a v) (S v)
        (grid v) (mask v) (φ v) -
      gridDensityTest (selectedOutputSlice select g v) (a v) (S v)
        (grid v) (mask v) (φ v)‖ ≤
      M * (ε + (2 * (R : ℝ)) ^ Fintype.card (UnselectedColumn select) *
        ((2 * (R : ℝ) + 2) ^ Fintype.card J * ((Kf : ℝ) + Kg) * mesh)) := by
  have hi := integrable_snd_probability (Measure.dirac ()) volume (fun v => f v - g v) hfg
  have he' : (∫ p : Unit × (I → ℝ), |f p.2 - g p.2| ∂(Measure.dirac ()).prod volume) ≤ ε := by
    rw [integral_snd_probability (Measure.dirac ()) volume (fun v => |f v - g v|) hfg.abs]
    exact he
  have ht := mixed_output_grid_error select (Measure.dirac ()) (fun _ => f) (fun _ => g) R
    (Filter.Eventually.of_forall (fun _ => ⟨hf, hg, hfs, hgs⟩)) hi he'
    (fun p => a p.2) (fun p => S p.2) (fun p => hS p.2)
    hmesh0 hmesh1 (fun p => hmesh p.2) (fun p => grid p.2)
    (fun p => mask p.2) (fun p => φ p.2) hM (fun p => hmask p.2) (fun p => hφ p.2)
  rw [Measure.dirac_prod, (measurableEmbedding_prodMk_left ()).integral_map] at ht
  exact ht

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedAmbientLongBox
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

section Box

variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

theorem allocatedLongJetRowBox_measurable (T : ℝ) (a : {a // ¬grid a}) :
    MeasurableSet (allocatedLongJetRowBox B U basis S O T a) := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    change MeasurableSet (Metric.closedBall (0 : O j → ℝ) T)
    exact measurableSet_closedBall
  | inr i =>
    change MeasurableSet (rectangularWeightIndices (fun _ => 0)
      (fun _ : O j => (basisAxisScale (basis j) i : ℝ)) T : Set (O j → ℤ))
    exact Finset.measurableSet _

theorem allocatedLongJetBox_measurable (T : ℝ) :
    MeasurableSet (allocatedLongJetBox B U basis S O T) :=
  MeasurableSet.univ_pi (allocatedLongJetRowBox_measurable B U basis S O T)

end Box

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical ENNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

theorem allocatedLongJetRowBox_measure_lt_top (T : ℝ) (a : {a // ¬grid a}) :
    coefficientJetAxisReference O a.val (allocatedLongJetRowBox B U basis S O T a) < ∞ := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    change volume (Metric.closedBall (0 : O j → ℝ) T) < ∞
    exact (isCompact_closedBall (0 : O j → ℝ) T).measure_lt_top
  | inr i =>
    change Measure.count (↑(rectangularWeightIndices (fun _ => 0)
      (fun _ : O j => (basisAxisScale (basis j) i : ℝ)) T) : Set (O j → ℤ)) < ∞
    rw [Measure.count_apply_finset]
    simp

theorem allocatedLongJetBox_measure_lt_top (T : ℝ) :
    allocatedLongJetReference B U basis S O (allocatedLongJetBox B U basis S O T) < ∞ := by
  unfold allocatedLongJetReference allocatedLongJetBox
  rw [Measure.pi_pi]
  exact ENNReal.prod_lt_top (fun a _ => allocatedLongJetRowBox_measure_lt_top B U basis S O T a)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedLongGridCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}

theorem allocatedLongRowsFromGrid_realCoordinates
    (v : UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O)) → ℝ)
    (k : integerOutput → ℤ) :
    allocatedLongJetRealCoordinates B U basis S (allocatedLongRowsFromGrid B U basis S v k) =
      selectedCoefficientEquiv (allocatedLongIntegerSelect B U basis S (O := O)) ℝ
        (v, rectangularLatticePoint (fun _ => 0) (allocatedLongLatticeScale B U basis S) k) := by
  apply selectedCoefficientEquiv_eq_of_coordinates
  · intro q
    rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
    · rfl
    · exact False.elim (hq ⟨allocatedLongIntegerIndex B U basis S j i ha o, rfl⟩)
  · intro q
    rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
    · exact False.elim hq
    · change (k (allocatedLongIntegerIndex B U basis S j i ha o) : ℝ) /
        (basisAxisScale (basis j) i : ℝ) =
        ((k (allocatedLongIntegerIndex B U basis S j i ha o) : ℝ) - 0) /
          (basisAxisScale (basis j) i : ℝ)
      rw [sub_zero]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedLongLatticeScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}

omit [∀ j, Fintype (O j)] in
theorem allocatedLongLatticeScale_pos (q : integerOutput) :
    0 < allocatedLongLatticeScale B U basis S q := by
  rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
  · exact False.elim hq
  · exact Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)

theorem allocatedLongLatticeScale_product :
    (∏ q : integerOutput, allocatedLongLatticeScale B U basis S q) =
      ∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U basis S (O := O) a := by
  have hs := Fintype.prod_subtype_mul_prod_subtype
    (allocatedLongIntegerCoordinate B U basis S (O := O))
    (allocatedLongCoordinateScale B U basis S (O := O))
  have hz : (∏ q : {q : output // ¬allocatedLongIntegerCoordinate B U basis S q},
      allocatedLongCoordinateScale B U basis S q.val) = 1 := by
    apply Finset.prod_eq_one
    intro q _
    rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
    · rfl
    · exact False.elim (hq True.intro)
  rw [hz, mul_one] at hs
  change (∏ q : integerOutput, allocatedLongCoordinateScale B U basis S q.val) = _
  rw [hs, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩ <;>
    simp [allocatedLongCoordinateScale, allocatedLongJetOutputScale]

omit [∀ j, Fintype (O j)] in
theorem allocatedLongLatticeScale_mesh (q : integerOutput) :
    1 / allocatedLongLatticeScale B U basis S q ≤
      1 / (S.value : ℝ) ^ (layerTailDegree m + 1) := by
  rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
  · exact False.elim hq
  · change 1 / (basisAxisScale (basis j) i : ℝ) ≤ _
    apply one_div_le_one_div_of_le (pow_pos (Nat.cast_pos.mpr S.positive) _)
    exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge ha)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SelectedDependentMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] (s : I ↪ J)
variable (X : J → Type*) [∀ j, MeasurableSpace (X j)]

theorem selectedDependentEquiv_eq_of_coordinates (f : ∀ j, X j)
    (p : (∀ j : UnselectedColumn s, X j.val) × (∀ i, X (s i)))
    (hfree : ∀ j : UnselectedColumn s, f j.val = p.1 j)
    (hselected : ∀ i, f (s i) = p.2 i) :
    f = selectedDependentEquiv s X p := by
  apply (selectedDependentEquiv s X).symm.injective
  rw [MeasurableEquiv.symm_apply_apply]
  exact Prod.ext (funext hfree) (funext hselected)

theorem selectedDependentEquiv_measurePreserving [Fintype J]
    (μ : ∀ j, Measure (X j)) [∀ j, SigmaFinite (μ j)] :
    MeasurePreserving (selectedDependentEquiv s X)
      ((Measure.pi (fun j : UnselectedColumn s => μ j.val)).prod
        (Measure.pi (fun i => μ (s i)))) (Measure.pi μ) :=
  (measurePreserving_piCongrLeft μ (selectedFreeFirstEquiv s)).comp
    (measurePreserving_sumPiEquivProdPi_symm
      (fun j : UnselectedColumn s ⊕ I => μ (selectedFreeFirstEquiv s j)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedLongGridIntegral
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}
local notation "select" => allocatedLongIntegerSelect B U basis S (O := O)
local notation "realOutput" => UnselectedColumn select

theorem allocatedLongGridEquiv_apply (v : realOutput → ℝ) (k : integerOutput → ℤ) :
    allocatedLongGridEquiv B U basis S (v, k) = allocatedLongRowsFromGrid B U basis S v k := by
  apply (allocatedLongScalarEquiv B U basis S).injective
  simp only [allocatedLongGridEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.apply_symm_apply]
  symm
  apply selectedDependentEquiv_eq_of_coordinates
  · intro q
    rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
    · rfl
    · exact False.elim (hq ⟨allocatedLongIntegerIndex B U basis S j i ha o, rfl⟩)
  · intro q
    rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
    · exact False.elim hq
    · rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

variable [∀ j, DecidableEq (O j)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}
local notation "realOutput" => UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O))

omit [∀ j, DecidableEq (O j)] [Fintype α] in
theorem allocatedLongGridDensityTest_eq (f : (output → ℝ) → ℝ)
    (v : realOutput → ℝ) (qs : Finset (integerOutput → ℤ)) (φ : (integerOutput → ℤ) → ℂ) :
    allocatedLongGridDensityTest B U basis S x rows modulus residue f v qs φ =
      gridDensityTest (selectedOutputSlice (allocatedLongIntegerSelect B U basis S (O := O)) f v)
        (fun _ => 0) (allocatedLongLatticeScale B U basis S) qs
        (allocatedLongGridMask B U basis S x rows modulus residue v) φ := by
  unfold allocatedLongGridDensityTest gridDensityTest selectedOutputSlice
  rw [allocatedLongLatticeScale_product]
  simp only [allocatedLongRowsFromGrid_realCoordinates]

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [Fintype α] in
theorem allocatedLongGridMask_bound {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C)
    (v : realOutput → ℝ) (k : integerOutput → ℤ) :
    |allocatedLongGridMask B U basis S x rows modulus residue v k| ≤
      C ^ Fintype.card (LayerSamplerAxis I n) := by
  have hr (a : {a // ¬grid a}) :
      0 ≤ allocatedLongJetMask B U basis S x rows modulus residue a
        (allocatedLongRowsFromGrid B U basis S v k a) ∧
      allocatedLongJetMask B U basis S x rows modulus residue a
        (allocatedLongRowsFromGrid B U basis S v k a) ≤ C := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact ⟨zero_le_one, hC⟩
    · exact hm j _
  have hnonneg : 0 ≤ allocatedLongGridMask B U basis S x rows modulus residue v k :=
    Finset.prod_nonneg (fun a _ => (hr a).1)
  rw [abs_of_nonneg hnonneg]
  calc
    _ ≤ ∏ _a : {a // ¬grid a}, C :=
      Finset.prod_le_prod (fun a _ => (hr a).1) (fun a _ => (hr a).2)
    _ = C ^ Fintype.card {a // ¬grid a} := by simp
    _ ≤ _ := pow_le_pow_right₀ hC (Fintype.card_subtype_le _)

omit [∀ j, DecidableEq (O j)] [Fintype α] in
theorem allocatedLongGridDensityTest_comparison
    (f g : (output → ℝ) → ℝ) {Kf Kg : ℝ≥0} (Ro : ℝ≥0)
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfs : ∀ v, (Ro : ℝ) < ‖v‖ → f v = 0)
    (hgs : ∀ v, (Ro : ℝ) < ‖v‖ → g v = 0)
    (hfg : Integrable (fun v => f v - g v)) {ε : ℝ}
    (he : (∫ v, |f v - g v|) ≤ ε)
    {mesh C : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C)
    (qs : (realOutput → ℝ) → Finset (integerOutput → ℤ))
    (φ : (realOutput → ℝ) → (integerOutput → ℤ) → ℂ)
    (hφ : ∀ v k, k ∈ qs v → ‖φ v k‖ ≤ 1) :
    ‖∫ v, allocatedLongGridDensityTest B U basis S x rows modulus residue f v (qs v) (φ v) -
      allocatedLongGridDensityTest B U basis S x rows modulus residue g v (qs v) (φ v)‖ ≤
      C ^ Fintype.card (LayerSamplerAxis I n) *
        (ε + (2 * (Ro : ℝ)) ^ Fintype.card realOutput *
          ((2 * (Ro : ℝ) + 2) ^ Fintype.card integerOutput * ((Kf : ℝ) + Kg) * mesh)) := by
  simp_rw [allocatedLongGridDensityTest_eq]
  exact fixed_mixed_output_grid_error (allocatedLongIntegerSelect B U basis S (O := O))
    f g Ro hf hg hfs hgs hfg he (fun _ _ => 0) (fun _ => allocatedLongLatticeScale B U basis S)
    (fun _ => allocatedLongLatticeScale_pos B U basis S) hmesh0 hmesh1
    (fun _ q => (allocatedLongLatticeScale_mesh B U basis S q).trans hmesh) qs
    (allocatedLongGridMask B U basis S x rows modulus residue) φ
    (pow_nonneg (zero_le_one.trans hC) _)
    (fun v k _ => allocatedLongGridMask_bound B U basis S x rows modulus residue hC hm v k) hφ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}
local notation "select" => allocatedLongIntegerSelect B U basis S (O := O)
local notation "realOutput" => UnselectedColumn select
local notation "scalar" => fun q : output => CoefficientJetScalar (Subtype.val (Sigma.fst q))
local notation "law" => fun q : output => coefficientJetScalarReference (Subtype.val (Sigma.fst q))

theorem allocatedLongScalarEquiv_measurePreserving :
    MeasurePreserving (allocatedLongScalarEquiv B U basis S (O := O))
      (allocatedLongJetReference B U basis S O) (Measure.pi law) := by
  have hrows := measurePreserving_pi
    (fun a : {a // ¬grid a} => coefficientJetAxisReference O a.val)
    (fun a : {a // ¬grid a} => Measure.pi (fun _ : O a.val.1 => coefficientJetScalarReference a.val))
    (fun a => coefficientJetScalarEquiv_measurePreserving O a.val)
  have hflat : MeasurePreserving
      (MeasurableEquiv.piCurry (fun (a : {a // ¬grid a}) (_ : O a.val.1) =>
        CoefficientJetScalar a.val)).symm
      (Measure.pi (fun a : {a // ¬grid a} =>
        Measure.pi (fun _ : O a.val.1 => coefficientJetScalarReference a.val)))
      (Measure.pi law) :=
    ⟨(MeasurableEquiv.piCurry (fun (a : {a // ¬grid a}) (_ : O a.val.1) =>
      CoefficientJetScalar a.val)).symm.measurable, sigmaFiniteProductMeasure_flatten law⟩
  exact hflat.comp hrows

omit [∀ j, Fintype (O j)] in
theorem allocatedLongRealScalarEquiv_measurePreserving (q : realOutput) :
    MeasurePreserving (allocatedLongRealScalarEquiv B U basis S q) volume (law q.val) := by
  rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
  · exact MeasurePreserving.id volume
  · exact False.elim (hq ⟨allocatedLongIntegerIndex B U basis S j i ha o, rfl⟩)

omit [∀ j, Fintype (O j)] in
theorem allocatedLongIntegerScalarEquiv_measurePreserving (q : integerOutput) :
    MeasurePreserving (allocatedLongIntegerScalarEquiv B U basis S q) Measure.count
      (law (select q)) := by
  rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
  · exact False.elim hq
  · exact MeasurePreserving.id Measure.count

theorem allocatedLongGridEquiv_measurePreserving :
    MeasurePreserving (allocatedLongGridEquiv B U basis S (O := O))
      ((volume : Measure (realOutput → ℝ)).prod (Measure.count : Measure (integerOutput → ℤ)))
      (allocatedLongJetReference B U basis S O) := by
  have hr := measurePreserving_pi (fun _ : realOutput => (volume : Measure ℝ))
    (fun q => law q.val) (allocatedLongRealScalarEquiv_measurePreserving B U basis S)
  have hi := measurePreserving_pi (fun _ : integerOutput => (Measure.count : Measure ℤ))
    (fun q => law (select q)) (allocatedLongIntegerScalarEquiv_measurePreserving B U basis S)
  have hcoords : MeasurePreserving
      ((MeasurableEquiv.piCongrRight (allocatedLongRealScalarEquiv B U basis S)).prodCongr
        (MeasurableEquiv.piCongrRight (allocatedLongIntegerScalarEquiv B U basis S)))
      ((volume : Measure (realOutput → ℝ)).prod (Measure.count : Measure (integerOutput → ℤ)))
      ((Measure.pi (fun q : realOutput => law q.val)).prod
        (Measure.pi (fun q : integerOutput => law (select q)))) := by
    have h := hr.prod hi
    rw [pi_count_measure] at h
    exact h
  unfold allocatedLongGridEquiv
  rw [MeasurableEquiv.coe_trans, MeasurableEquiv.coe_trans]
  exact (((allocatedLongScalarEquiv_measurePreserving B U basis S (O := O)).symm
    (allocatedLongScalarEquiv B U basis S)).comp
      (selectedDependentEquiv_measurePreserving select scalar law)).comp hcoords

theorem allocatedLongGridEquiv_coe :
    (allocatedLongGridEquiv B U basis S (O := O) :
      ((realOutput → ℝ) × (integerOutput → ℤ)) → AllocatedLongJetRows B U basis S O) =
      fun p => allocatedLongRowsFromGrid B U basis S p.1 p.2 := by
  funext p
  rcases p with ⟨v, k⟩
  exact allocatedLongGridEquiv_apply B U basis S v k

theorem allocatedLongRowsFromGrid_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AllocatedLongJetRows B U basis S O → E) :
    (∫ p : (realOutput → ℝ) × (integerOutput → ℤ),
      f (allocatedLongRowsFromGrid B U basis S p.1 p.2) ∂volume.prod Measure.count) =
      ∫ z, f z ∂allocatedLongJetReference B U basis S O := by
  have h := (allocatedLongGridEquiv_measurePreserving B U basis S (O := O)).integral_comp
    (allocatedLongGridEquiv B U basis S).measurableEmbedding f
  simpa only [allocatedLongGridEquiv_coe] using h

theorem allocatedLongRowsFromGrid_integrable_iff
    {E : Type*} [NormedAddCommGroup E] (f : AllocatedLongJetRows B U basis S O → E) :
    Integrable (fun p : (realOutput → ℝ) × (integerOutput → ℤ) =>
      f (allocatedLongRowsFromGrid B U basis S p.1 p.2)) (volume.prod Measure.count) ↔
      Integrable f (allocatedLongJetReference B U basis S O) := by
  have h := (allocatedLongGridEquiv_measurePreserving B U basis S (O := O)).integrable_comp_emb
    (allocatedLongGridEquiv B U basis S).measurableEmbedding (g := f)
  simpa only [allocatedLongGridEquiv_coe, Function.comp_def] using h

theorem allocatedLongRowsFromGrid_integral_finset
    (f : AllocatedLongJetRows B U basis S O → ℂ)
    (hf : Integrable f (allocatedLongJetReference B U basis S O))
    (qs : (realOutput → ℝ) → Finset (integerOutput → ℤ))
    (hs : ∀ v k, k ∉ qs v → f (allocatedLongRowsFromGrid B U basis S v k) = 0) :
    (∫ z, f z ∂allocatedLongJetReference B U basis S O) =
      ∫ v, ∑ k ∈ qs v, f (allocatedLongRowsFromGrid B U basis S v k) := by
  rw [← allocatedLongRowsFromGrid_integral B U basis S f]
  rw [integral_prod _ ((allocatedLongRowsFromGrid_integrable_iff B U basis S f).mpr hf)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  have hi : Integrable (fun k => f (allocatedLongRowsFromGrid B U basis S v k))
      Measure.count := by
    apply integrable_count_iff.mpr
    exact (hasSum_sum_of_ne_finset_zero (fun k hk => by rw [hs v k hk, norm_zero])).summable
  rw [integral_countable hi]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  exact (hasSum_sum_of_ne_finset_zero (hs v)).tsum_eq

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}
local notation "realOutput" => UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O))

theorem allocatedLongRowsFromGrid_zero_off_indices
    (f : (output → ℝ) → ℝ) {Ro : ℝ} (hs : ∀ z, Ro < ‖z‖ → f z = 0)
    (v : realOutput → ℝ) (k : integerOutput → ℤ)
    (hk : k ∉ rectangularWeightIndices (fun _ => 0) (allocatedLongLatticeScale B U basis S) Ro) :
    f (allocatedLongJetRealCoordinates B U basis S (allocatedLongRowsFromGrid B U basis S v k)) = 0 := by
  rw [allocatedLongRowsFromGrid_realCoordinates]
  change rectangularWeight
    (selectedOutputSlice (allocatedLongIntegerSelect B U basis S (O := O)) f v)
    (fun _ => 0) (allocatedLongLatticeScale B U basis S) k = 0
  exact rectangularWeight_zero_off_indices _ _ _ (allocatedLongLatticeScale_pos B U basis S)
    (selectedOutputSlice_support_right (allocatedLongIntegerSelect B U basis S (O := O)) hs v) k hk

theorem allocatedLongGridDensityTest_integral
    (f : (output → ℝ) → ℝ) (φ : AllocatedLongJetRows B U basis S O → ℂ)
    (qs : (realOutput → ℝ) → Finset (integerOutput → ℤ))
    (hs : ∀ v k, k ∉ qs v →
      f (allocatedLongJetRealCoordinates B U basis S (allocatedLongRowsFromGrid B U basis S v k)) = 0)
    (hi : Integrable (fun z : AllocatedLongJetRows B U basis S O =>
      (((∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        f (allocatedLongJetRealCoordinates B U basis S z) : ℝ) : ℂ) * φ z /
        ((∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U basis S (O := O) a : ℝ) : ℂ))
      (allocatedLongJetReference B U basis S O)) :
    (∫ z : AllocatedLongJetRows B U basis S O,
      (((∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        f (allocatedLongJetRealCoordinates B U basis S z) : ℝ) : ℂ) * φ z /
        ((∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U basis S (O := O) a : ℝ) : ℂ)
      ∂allocatedLongJetReference B U basis S O) =
      ∫ v, allocatedLongGridDensityTest B U basis S x rows modulus residue f v (qs v)
        (fun k => φ (allocatedLongRowsFromGrid B U basis S v k)) := by
  rw [allocatedLongRowsFromGrid_integral_finset B U basis S _ hi qs (by
    intro v k hk
    rw [hs v k hk]
    simp)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  simp only [allocatedLongGridDensityTest, allocatedLongGridMask, Finset.sum_div]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedActualProfileControl
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "reference" => allocatedLongJetReference B U basis S O

theorem allocatedLongJetRealCoordinates_measurable :
    Measurable (allocatedLongJetRealCoordinates B U basis S (O := O)) := by
  apply measurable_pi_iff.mpr
  intro q
  rcases q with ⟨⟨⟨j, i | i⟩, ha⟩, o⟩
  · exact (measurable_pi_apply o).comp
      (show Measurable (fun z : AllocatedLongJetRows B U basis S O =>
        z ⟨⟨j, .inl i⟩, ha⟩) from measurable_pi_apply _)
  · exact (measurable_of_countable
      (fun z : O j → ℤ => (z o : ℝ) / (basisAxisScale (basis j) i : ℝ))).comp
      (show Measurable (fun z : AllocatedLongJetRows B U basis S O =>
        z ⟨⟨j, .inr i⟩, ha⟩) from measurable_pi_apply _)

theorem allocatedLongJetBox_of_realCoordinates {T : ℝ} (hT : 0 ≤ T)
    (z : AllocatedLongJetRows B U basis S O)
    (hz : ‖allocatedLongJetRealCoordinates B U basis S z‖ ≤ T) :
    z ∈ allocatedLongJetBox B U basis S O T := by
  apply Set.mem_univ_pi.mpr
  intro a
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · change ‖(fun o : O j => z ⟨⟨j, .inl i⟩, ha⟩ o) - 0‖ ≤ T
    rw [sub_zero]
    apply (pi_norm_le_iff_of_nonneg hT).mpr
    intro o
    exact (norm_le_pi_norm (allocatedLongJetRealCoordinates B U basis S z)
      ⟨⟨⟨j, .inl i⟩, ha⟩, o⟩).trans hz
  · change z ⟨⟨j, .inr i⟩, ha⟩ ∈ rectangularWeightIndices (fun _ => 0)
      (fun _ : O j => (basisAxisScale (basis j) i : ℝ)) T
    apply Fintype.mem_piFinset.mpr
    intro o
    have ho : |(z ⟨⟨j, .inr i⟩, ha⟩ o : ℝ) / (basisAxisScale (basis j) i : ℝ)| ≤ T :=
      (norm_le_pi_norm (allocatedLongJetRealCoordinates B U basis S z)
        ⟨⟨⟨j, .inr i⟩, ha⟩, o⟩).trans hz
    have hh : (0 : ℝ) < basisAxisScale (basis j) i :=
      Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
    obtain ⟨hlo, hhi⟩ := abs_le.mp ho
    have hlo' := (le_div_iff₀ hh).mp hlo
    have hhi' := (div_le_iff₀ hh).mp hhi
    apply Finset.mem_Icc.mpr
    exact ⟨Int.ceil_le.mpr (by nlinarith), Int.le_floor.mpr (by nlinarith)⟩

theorem allocatedLongProfile_zero_off_box
    (f : (output → ℝ) → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hs : ∀ v, T < ‖v‖ → f v = 0)
    (z : AllocatedLongJetRows B U basis S O)
    (hz : z ∉ allocatedLongJetBox B U basis S O T) :
    f (allocatedLongJetRealCoordinates B U basis S z) = 0 :=
  hs _ (lt_of_not_ge (fun h => hz (allocatedLongJetBox_of_realCoordinates B U basis S hT z h)))

variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

theorem allocatedLongJetMask_measurable (a : {a // ¬grid a}) :
    Measurable (allocatedLongJetMask B U basis S x rows modulus residue a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact measurable_const
  · change Measurable (allocatedIntegerKernelMask B U basis S x rows j modulus (residue j))
    exact measurable_of_countable _

omit [∀ j, Fintype (O j)] in
theorem allocatedLongJetMask_product_bound {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C)
    (z : AllocatedLongJetRows B U basis S O) :
    |∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)| ≤
      C ^ Fintype.card (LayerSamplerAxis I n) := by
  have hr (a : {a // ¬grid a}) :
      0 ≤ allocatedLongJetMask B U basis S x rows modulus residue a (z a) ∧
      allocatedLongJetMask B U basis S x rows modulus residue a (z a) ≤ C := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact ⟨zero_le_one, hC⟩
    · exact hm j _
  rw [abs_of_nonneg (Finset.prod_nonneg (fun a _ => (hr a).1))]
  calc
    _ ≤ ∏ _a : {a // ¬grid a}, C :=
      Finset.prod_le_prod (fun a _ => (hr a).1) (fun a _ => (hr a).2)
    _ = C ^ Fintype.card {a // ¬grid a} := by simp
    _ ≤ _ := pow_le_pow_right₀ hC (Fintype.card_subtype_le _)

theorem allocatedLongMaskedProfile_integrable
    (f : (output → ℝ) → ℝ) (hf : Measurable f)
    {T C Cf : ℝ} (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
    (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hb : ∀ v, |f v| ≤ Cf)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C) :
    Integrable (fun z : AllocatedLongJetRows B U basis S O =>
      (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        f (allocatedLongJetRealCoordinates B U basis S z)) reference := by
  let box := allocatedLongJetBox B U basis S O T
  have hbox : MeasurableSet box := allocatedLongJetBox_measurable B U basis S O T
  have hmajor : Integrable (box.indicator
      (fun _ : AllocatedLongJetRows B U basis S O => C ^ Fintype.card (LayerSamplerAxis I n) * Cf))
      reference :=
    (integrableOn_const (allocatedLongJetBox_measure_lt_top B U basis S O T).ne).integrable_indicator hbox
  have hmask : Measurable (fun z : AllocatedLongJetRows B U basis S O =>
      ∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) :=
    Finset.measurable_prod _ (fun a _ =>
      (allocatedLongJetMask_measurable B U basis S x rows modulus residue a).comp (measurable_pi_apply a))
  apply hmajor.mono' (hmask.mul (hf.comp (allocatedLongJetRealCoordinates_measurable B U basis S))).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  dsimp only [Pi.mul_apply, Function.comp_apply]
  by_cases hz : z ∈ box
  · rw [Set.indicator_of_mem hz, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right
        (allocatedLongJetMask_product_bound B U basis S x rows modulus residue hC hm z) hCf)
  · rw [Set.indicator_of_notMem hz, allocatedLongProfile_zero_off_box B U basis S f hT hs z hz]
    simp

theorem allocatedLongMaskedProfile_test_integrable
    (f : (output → ℝ) → ℝ) (hf : Measurable f)
    {T C Cf : ℝ} (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
    (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hb : ∀ v, |f v| ≤ Cf)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C)
    (φ : AllocatedLongJetRows B U basis S O → ℂ) (hφ : Measurable φ)
    (hφb : ∀ z, ‖φ z‖ ≤ 1) :
    Integrable (fun z : AllocatedLongJetRows B U basis S O =>
      (((∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        f (allocatedLongJetRealCoordinates B U basis S z) : ℝ) : ℂ) * φ z /
        ((∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U basis S (O := O) a : ℝ) : ℂ))
      reference := by
  exact ((allocatedLongMaskedProfile_integrable B U basis S x rows modulus residue
    f hf hT hs hC hCf hb hm).ofReal.mul_bdd hφ.aestronglyMeasurable
      (Filter.Eventually.of_forall hφb)).div_const _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}
local notation "realOutput" => UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O))
local notation "reference" => allocatedLongJetReference B U basis S O
local notation "scale" => ((∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U basis S (O := O) a : ℝ) : ℂ)

theorem allocatedLongGridDensityTest_sub (f g : (output → ℝ) → ℝ)
    (v : realOutput → ℝ) (qs : Finset (integerOutput → ℤ)) (φ : (integerOutput → ℤ) → ℂ) :
    allocatedLongGridDensityTest B U basis S x rows modulus residue (fun z => f z - g z) v qs φ =
      allocatedLongGridDensityTest B U basis S x rows modulus residue f v qs φ -
      allocatedLongGridDensityTest B U basis S x rows modulus residue g v qs φ := by
  simp only [allocatedLongGridDensityTest, mul_sub, Complex.ofReal_sub, sub_mul,
    Finset.sum_sub_distrib, sub_div]

theorem allocatedLongReference_test_comparison
    (f g : (output → ℝ) → ℝ) {Kf Kg : ℝ≥0} (Ro : ℝ≥0)
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfs : ∀ v, (Ro : ℝ) < ‖v‖ → f v = 0)
    (hgs : ∀ v, (Ro : ℝ) < ‖v‖ → g v = 0)
    {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hfb : ∀ v, |f v| ≤ Cf) (hgb : ∀ v, |g v| ≤ Cg)
    (hfg : Integrable (fun v => f v - g v)) {ε : ℝ}
    (he : (∫ v, |f v - g v|) ≤ ε)
    {mesh C : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C)
    (φ : AllocatedLongJetRows B U basis S O → ℂ) (hφ : Measurable φ)
    (hφb : ∀ z, ‖φ z‖ ≤ 1) :
    ‖(∫ z : AllocatedLongJetRows B U basis S O,
        (((∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
          f (allocatedLongJetRealCoordinates B U basis S z) : ℝ) : ℂ) * φ z / scale ∂reference) -
      (∫ z : AllocatedLongJetRows B U basis S O,
        (((∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
          g (allocatedLongJetRealCoordinates B U basis S z) : ℝ) : ℂ) * φ z / scale ∂reference)‖ ≤
      C ^ Fintype.card (LayerSamplerAxis I n) *
        (ε + (2 * (Ro : ℝ)) ^ Fintype.card realOutput *
          ((2 * (Ro : ℝ) + 2) ^ Fintype.card integerOutput * ((Kf : ℝ) + Kg) * mesh)) := by
  have hfi := allocatedLongMaskedProfile_test_integrable B U basis S x rows modulus residue
    f hf.continuous.measurable Ro.coe_nonneg hfs hC hCf hfb hm φ hφ hφb
  have hgi := allocatedLongMaskedProfile_test_integrable B U basis S x rows modulus residue
    g hg.continuous.measurable Ro.coe_nonneg hgs hC hCg hgb hm φ hφ hφb
  have hdi := allocatedLongMaskedProfile_test_integrable B U basis S x rows modulus residue
    (fun v => f v - g v) (hf.continuous.measurable.sub hg.continuous.measurable)
    Ro.coe_nonneg (fun v hv => by rw [hfs v hv, hgs v hv, sub_self])
    hC (add_nonneg hCf hCg)
    (fun v => (abs_sub (f v) (g v)).trans (add_le_add (hfb v) (hgb v))) hm φ hφ hφb
  let qs : Finset (integerOutput → ℤ) := rectangularWeightIndices (fun _ => 0) (allocatedLongLatticeScale B U basis S) (Ro : ℝ)
  have heq := allocatedLongGridDensityTest_integral B U basis S x rows modulus residue
    (fun v => f v - g v) φ (fun _ => qs)
    (fun v k hk => by
      rw [allocatedLongRowsFromGrid_zero_off_indices B U basis S f hfs v k hk,
        allocatedLongRowsFromGrid_zero_off_indices B U basis S g hgs v k hk, sub_self]) hdi
  rw [← integral_sub hfi hgi]
  simp_rw [← sub_div, ← sub_mul, ← Complex.ofReal_sub, ← mul_sub]
  rw [heq]
  simp_rw [allocatedLongGridDensityTest_sub]
  exact allocatedLongGridDensityTest_comparison B U basis S x rows modulus residue
    f g Ro hf hg hfs hgs hfg he hmesh0 hmesh1 hmesh hC hm (fun _ => qs)
    (fun v k => φ (allocatedLongRowsFromGrid B U basis S v k)) (fun v k _ => hφb _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedLongIntegralMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "reference" => allocatedLongJetReference B U b S O

theorem allocatedLongProfileDensity_measurable (f : (output → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (allocatedLongProfileDensity B U b S x rows modulus residue f) := by
  have hm : Measurable (fun z : AllocatedLongJetRows B U b S O =>
      ∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)) :=
    Finset.measurable_prod _ (fun a _ =>
      (allocatedLongJetMask_measurable B U b S x rows modulus residue a).comp (measurable_pi_apply a))
  exact (hm.mul (hf.comp (allocatedLongJetRealCoordinates_measurable B U b S))).div_const _

theorem allocatedLongProfileDensity_integrable
    (f : (output → ℝ) → ℝ) (hf : Measurable f)
    {T C Cf : ℝ} (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
    (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hb : ∀ v, |f v| ≤ Cf)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ≤ C) :
    Integrable (allocatedLongProfileDensity B U b S x rows modulus residue f) reference :=
  (allocatedLongMaskedProfile_integrable B U b S x rows modulus residue
    f hf hT hs hC hCf hb hm).div_const _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityComparisonComposition
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem density_l1_le_of_complex_tests {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f μ) (hgi : Integrable g μ) {ε : ℝ}
    (he : ∀ φ : X → ℂ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      ‖(∫ x, (f x : ℂ) * φ x ∂μ) - (∫ x, (g x : ℂ) * φ x ∂μ)‖ ≤ ε) :
    (∫ x, |f x - g x| ∂μ) ≤ ε := by
  apply density_l1_le_of_bounded_tests μ f g hf hg hfi hgi
  intro φ hφ hb
  have h := he (fun x => (φ x : ℂ)) hφ.complex_ofReal
    (fun x => by simpa only [Complex.norm_real] using hb x)
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedActualHaarComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U b S q}
local notation "realOutput" => UnselectedColumn (allocatedLongIntegerSelect B U b S (O := O))
local notation "reference" => allocatedLongJetReference B U b S O
local notation "density" => allocatedLongProfileDensity B U b S x rows modulus residue

theorem allocatedLongReference_l1_comparison_s2_oai
    (f g : (output → ℝ) → ℝ) {Kf Kg : ℝ≥0} (Ro : ℝ≥0)
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfs : ∀ v, (Ro : ℝ) < ‖v‖ → f v = 0)
    (hgs : ∀ v, (Ro : ℝ) < ‖v‖ → g v = 0)
    {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hfb : ∀ v, |f v| ≤ Cf) (hgb : ∀ v, |g v| ≤ Cg)
    (hfg : Integrable (fun v => f v - g v)) {ε : ℝ}
    (he : (∫ v, |f v - g v|) ≤ ε)
    {mesh C : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ≤ C) :
    (∫ z, |density f z - density g z| ∂reference) ≤
      C ^ Fintype.card (LayerSamplerAxis I n) *
        (ε + (2 * (Ro : ℝ)) ^ Fintype.card realOutput *
          ((2 * (Ro : ℝ) + 2) ^ Fintype.card integerOutput * ((Kf : ℝ) + Kg) * mesh)) := by
  apply density_l1_le_of_complex_tests reference (density f) (density g)
    (allocatedLongProfileDensity_measurable B U b S x rows modulus residue f hf.continuous.measurable)
    (allocatedLongProfileDensity_measurable B U b S x rows modulus residue g hg.continuous.measurable)
    (allocatedLongProfileDensity_integrable B U b S x rows modulus residue f
      hf.continuous.measurable Ro.coe_nonneg hfs hC hCf hfb hm)
    (allocatedLongProfileDensity_integrable B U b S x rows modulus residue g
      hg.continuous.measurable Ro.coe_nonneg hgs hC hCg hgb hm)
  intro φ hφ hφb
  have h := allocatedLongReference_test_comparison B U b S x rows modulus residue
    f g Ro hf hg hfs hgs hCf hCg hfb hgb hfg he hmesh0 hmesh1 hmesh hC hm φ hφ hφb
  simpa only [allocatedLongProfileDensity, Complex.ofReal_div, div_mul_eq_mul_div] using h

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedLongReference_l1_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedLongReference_l1_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
