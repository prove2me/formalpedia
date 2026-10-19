-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.forecastRawSpatialBox_normalized_integral_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:10:59.633974+00:00
-- url     : https://prove2.me/submissions/0a4f3147-45f5-40c6-86b5-638eaa8a4f25

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B126

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalDensityTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

theorem diagonalDensityTransport_det :
    LinearMap.det (coordinateScaleEquiv a ha).toLinearMap = ∏ i, a i := by
  classical
  have hm : LinearMap.toMatrix' (coordinateScaleEquiv a ha).toLinearMap = Matrix.diagonal a := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix'_apply, coordinateScaleEquiv_apply]
    · simp [LinearMap.toMatrix'_apply, coordinateScaleEquiv_apply, hij]
  rw [← LinearMap.det_toMatrix', hm, Matrix.det_diagonal]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexDiagonalVolumeIntegral
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem map_volume_positive_diagonal (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    Measure.map (fun v : ι → ℝ => fun i => a i * v i) volume =
      ENNReal.ofReal (∏ i, a i)⁻¹ • volume := by
  classical
  have hp : 0 < ∏ i, a i := Finset.prod_pos (fun i _ => ha i)
  have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (coordinateScaleEquiv a (fun i => (ha i).ne')).isUnit_det'.ne_zero
  rw [diagonalDensityTransport_det] at h
  change Measure.map (fun v : ι → ℝ => fun i => a i * v i) volume =
    ENNReal.ofReal |(∏ i, a i)⁻¹| • volume at h
  simpa only [abs_of_pos (inv_pos.mpr hp)] using h

theorem complex_integral_comp_positive_diagonal (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (f : (ι → ℝ) → ℂ) :
    (∫ v : ι → ℝ, f (fun i => a i * v i)) =
      ((∏ i, a i : ℝ) : ℂ)⁻¹ * ∫ v : ι → ℝ, f v := by
  classical
  let A := (coordinateScaleEquiv a (fun i => (ha i).ne')).toContinuousLinearEquiv
  have h := A.toHomeomorph.measurableEmbedding.integral_map (μ := volume) f
  change (∫ v : ι → ℝ, f v ∂Measure.map (fun v : ι → ℝ => fun i => a i * v i) volume) =
    ∫ v : ι → ℝ, f (fun i => a i * v i) at h
  rw [map_volume_positive_diagonal a ha, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Finset.prod_nonneg (fun i _ => (ha i).le)))] at h
  simpa only [Complex.real_smul, Complex.ofReal_inv] using h.symm

theorem complex_integral_eq_positive_diagonal (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (f : (ι → ℝ) → ℂ) :
    (∫ v : ι → ℝ, f v) = ((∏ i, a i : ℝ) : ℂ) * ∫ v : ι → ℝ, f (fun i => a i * v i) := by
  classical
  have hp : ((∏ i, a i : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.prod_pos (fun i _ => ha i)).ne'
  rw [complex_integral_comp_positive_diagonal a ha, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPiProduct
namespace OAI

section

namespace Erdos3

open MeasureTheory MeasureTheory.Measure MeasurableSpace

theorem dependentPiProd_measurePreserving {I : Type*} [Fintype I] {X Y : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (X i)) (ν : ∀ i, Measure (Y i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (dependentPiProd I X Y) (Measure.pi (fun i => (μ i).prod (ν i)))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := (dependentPiProd I X Y).measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
        (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn)) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      rw [show (dependentPiProd I X Y) ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
          Set.univ.pi (fun i => s i ×ˢ t i) by
        ext x
        simp [dependentPiProd, Set.mem_pi, forall_and]]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

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

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators ENNReal

theorem mixedArrayRegroup_volume_count (I Z O : Type*) [Fintype I] [Fintype Z] [Fintype O] :
    MeasurePreserving (mixedArrayRegroup I Z O) (mixedArrayReference I Z O)
      (Measure.pi (fun _ : O => (volume : Measure (I → ℝ)).prod (Measure.count : Measure (Z → ℤ)))) := by
  simpa only [mixedArrayReference, volume_pi, pi_count_measure] using
    (mixedArrayRegroup_measurePreserving (fun _ : I => fun _ : O => (volume : Measure ℝ))
      (fun _ : Z => fun _ : O => (Measure.count : Measure ℤ)))

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastIntegerAxisSplit
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

theorem forecastIntegerAxisSplit_measurePreserving :
    MeasurePreserving (forecastIntegerAxisSplit U basis L) Measure.count
      (Measure.count.prod Measure.count) := by
  refine ⟨(forecastIntegerAxisSplit U basis L).measurable, ?_⟩
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (forecastIntegerAxisSplit U basis L).measurable
    (measurableSet_singleton z)]
  have he : (forecastIntegerAxisSplit U basis L) ⁻¹' {z} =
      {(forecastIntegerAxisSplit U basis L).symm z} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      apply (forecastIntegerAxisSplit U basis L).injective
      rw [hx, MeasurableEquiv.apply_symm_apply]
    · intro hx
      rw [hx, MeasurableEquiv.apply_symm_apply]
  rw [he, Measure.count_singleton, ← Set.singleton_prod_singleton,
    Measure.prod_prod, Measure.count_singleton, Measure.count_singleton, one_mul]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastFiniteSpatialFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {K Z : Type*} [Countable K] [MeasurableSpace K]
  [MeasurableSingletonClass K] [MeasurableSpace Z]
  (μ : Measure Z) [SFinite μ]

omit [Countable K] in

theorem forecastFiniteSpatialFamily_integrable
    (F : K → Z → ℂ) (s : Finset K)
    (hf : ∀ k ∈ s, Integrable (F k) μ)
    (hzero : ∀ k ∉ s, ∀ z, F k z = 0) :
    Integrable (fun p : K × Z => F p.1 p.2) (Measure.count.prod μ) := by
  classical
  have hi (k : K) : Integrable (fun j : K => if j = k then (1 : ℂ) else 0)
      Measure.count := by
    apply integrable_count_iff.mpr
    apply summable_of_ne_finset_zero (s := {k})
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [hj]
  have hs := integrable_finsetSum s (fun k hk => (hi k).mul_prod (hf k hk))
  have heq : (fun p : K × Z => F p.1 p.2) =
      (fun p : K × Z => ∑ k ∈ s, (if p.1 = k then (1 : ℂ) else 0) * F k p.2) := by
    funext p
    by_cases hp : p.1 ∈ s
    · rw [Finset.sum_eq_single p.1]
      · simp
      · intro b hb hbp
        simp [Ne.symm hbp]
      · exact fun hn => (hn hp).elim
    · rw [hzero p.1 hp p.2]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      have hpb : p.1 ≠ b := fun h => hp (h ▸ hb)
      simp [hpb]
  rw [heq]
  exact hs

theorem forecastFiniteSpatialFamily_sum_integral
    (F : K → Z → ℂ) (s : Finset K)
    (hf : ∀ k ∈ s, Integrable (F k) μ)
    (hzero : ∀ k ∉ s, ∀ z, F k z = 0) :
    (∑ k ∈ s, ∫ z, F k z ∂μ) =
      ∫ p : K × Z, F p.1 p.2 ∂(Measure.count.prod μ) := by
  classical
  have hi := forecastFiniteSpatialFamily_integrable μ F s hf hzero
  rw [integral_prod _ hi, integral_countable hi.integral_prod_left]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  symm
  apply tsum_eq_sum
  intro k hk
  simp [hzero k hk]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastRawSpatialBoxReorder
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

theorem mixedCoveredJetRawReference_prod {m : ℕ} {I O E : Fin m → Type*}
    [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (N : ℕ) [NeZero N] :
    mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) N =
      (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod
        (mixedCoveredJetDeckReference O E N) := rfl

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable (n : Fin m → ℕ) (N : ℕ) [NeZero N]

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "IntAxis" => (Σ j, Fin (n j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := E) (n := n) N

theorem forecastSingleMixedRawReference_eq :
    raw = (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) Unit)).prod (mixedCoveredJetDeckReference single E N) := by
  exact mixedCoveredJetRawReference_prod (I := I) (O := single) (E := E) (n := n) N

omit [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [NeZero N] in
theorem forecastSingleMixedRawEquiv_coe :
    (forecastSingleMixedRawEquiv I E n N : MixedCoveredJetSource I single E n N →
      (((RealAxis → ℝ) × (IntAxis → ℤ)) × (∀ j, Unit → E j → ZMod N))) =
    Prod.map (fun z : ∀ j, (I j → Unit → ℝ) × (Fin (n j) → Unit → ℤ) =>
      (fun a : RealAxis => (z a.1).1 a.2 (), fun a : IntAxis => (z a.1).2 a.2 ())) id := rfl

omit [∀ j, Fintype (E j)] [NeZero N] in
private theorem forecastSingleRawLayer_preserving (j : Fin m) : MeasurePreserving
    ((mixedArrayRegroup (I j) (Fin (n j)) Unit).trans
      (MeasurableEquiv.funUnique Unit ((I j → ℝ) × (Fin (n j) → ℤ))))
    (mixedArrayReference (I j) (Fin (n j)) Unit)
    ((volume : Measure (I j → ℝ)).prod (Measure.count : Measure (Fin (n j) → ℤ))) :=
  (measurePreserving_funUnique _ Unit).comp
    (mixedArrayRegroup_volume_count (I j) (Fin (n j)) Unit)

omit [∀ j, Fintype (E j)] [NeZero N] in
private theorem forecastSingleRawReal_flatten : MeasurePreserving
    (MeasurableEquiv.piCurry (fun j (_ : I j) => ℝ)).symm
    (Measure.pi (fun j => (volume : Measure (I j → ℝ))))
    (volume : Measure (RealAxis → ℝ)) := by
  refine ⟨(MeasurableEquiv.piCurry (fun j (_ : I j) => ℝ)).symm.measurable, ?_⟩
  exact sigmaFiniteProductMeasure_flatten (fun _ : RealAxis => (volume : Measure ℝ))

omit [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [NeZero N] in
private theorem forecastSingleRawInteger_flatten : MeasurePreserving
    (MeasurableEquiv.piCurry (fun j (_ : Fin (n j)) => ℤ)).symm
    (Measure.pi (fun j => (Measure.count : Measure (Fin (n j) → ℤ))))
    (Measure.count : Measure (IntAxis → ℤ)) := by
  refine ⟨(MeasurableEquiv.piCurry (fun j (_ : Fin (n j)) => ℤ)).symm.measurable, ?_⟩
  change Measure.map (fun (x : ∀ j, Fin (n j) → ℤ) (a : IntAxis) => x a.1 a.2) _ = _
  have h := sigmaFiniteProductMeasure_flatten (fun _ : IntAxis => (Measure.count : Measure ℤ))
  simpa only [pi_count_measure] using h

omit [∀ j, Fintype (E j)] [NeZero N] in
private theorem forecastSingleRawArray_preserving :
    MeasurePreserving
      (fun z : ∀ j, (I j → Unit → ℝ) × (Fin (n j) → Unit → ℤ) =>
        (fun a : RealAxis => (z a.1).1 a.2 (), fun a : IntAxis => (z a.1).2 a.2 ()))
      (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) Unit))
      ((volume : Measure (RealAxis → ℝ)).prod (Measure.count : Measure (IntAxis → ℤ))) := by
  have hlayers := measurePreserving_pi
    (fun j => mixedArrayReference (I j) (Fin (n j)) Unit)
    (fun j => (volume : Measure (I j → ℝ)).prod (Measure.count : Measure (Fin (n j) → ℤ)))
    (forecastSingleRawLayer_preserving I n)
  have hreal := forecastSingleRawReal_flatten I
  have hint := forecastSingleRawInteger_flatten n
  have h := (((hreal.prod hint).comp
    (dependentPiProd_measurePreserving
      (fun j => (volume : Measure (I j → ℝ)))
      (fun j => (Measure.count : Measure (Fin (n j) → ℤ))))).comp hlayers)
  convert h using 1
  rfl

theorem forecastSingleMixedRawEquiv_measurePreserving :
    MeasurePreserving (forecastSingleMixedRawEquiv I E n N) raw
      (((volume : Measure (RealAxis → ℝ)).prod
        (Measure.count : Measure (IntAxis → ℤ))).prod (mixedCoveredJetDeckReference single E N)) := by
  rw [forecastSingleMixedRawEquiv_coe, forecastSingleMixedRawReference_eq]
  have hid : MeasurePreserving (id : (∀ j, Unit → E j → ZMod N) → (∀ j, Unit → E j → ZMod N)) (mixedCoveredJetDeckReference single E N) (mixedCoveredJetDeckReference single E N) := MeasurePreserving.id _
  have hp := (forecastSingleRawArray_preserving I n).prod hid
  exact hp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

private theorem productGridReorder_preserving
    {V S A D : Type*} [MeasurableSpace V] [MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace D]
    (μV : Measure V) (μS : Measure S) (μA : Measure A) (μD : Measure D)
    [SFinite μV] [SFinite μS] [SFinite μA] [SFinite μD] :
    MeasurePreserving (fun p : (V × (S × A)) × D => ((p.1.2.1, p.2), (p.1.1, p.1.2.2)))
      ((μV.prod (μS.prod μA)).prod μD) ((μS.prod μD).prod (μV.prod μA)) := by
  have h₁ := (measurePreserving_prodAssoc μV μS μA).symm MeasurableEquiv.prodAssoc
  have h₂ := (Measure.measurePreserving_swap (μ := μV) (ν := μS)).prod (MeasurePreserving.id μA)
  have h₃ := measurePreserving_prodAssoc μS μV μA
  have hleft := (h₃.comp (h₂.comp h₁)).prod (MeasurePreserving.id μD)
  have h₄ := measurePreserving_prodAssoc μS (μV.prod μA) μD
  have h₅ := (MeasurePreserving.id μS).prod
    (Measure.measurePreserving_swap (μ := μV.prod μA) (ν := μD))
  have h₆ := (measurePreserving_prodAssoc μS μD (μV.prod μA)).symm MeasurableEquiv.prodAssoc
  convert h₆.comp (h₅.comp (h₄.comp hleft)) using 1
  rfl

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (N : ℕ) [NeZero N]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := E) (n := n) N
local notation "deckLaw" => mixedCoveredJetDeckReference single E N
local notation "short" => AllocatedShortIntegerAxis U basis L
local notation "active" => AllocatedActiveIntegerAxis U basis L
local notation "gridMeasure" => Measure.prod
  (Measure.prod (Measure.count : Measure (short → ℤ)) deckLaw)
  (Measure.prod (volume : Measure (RealAxis → ℝ)) (Measure.count : Measure (active → ℤ)))

theorem forecastRawGridEquiv_measurePreserving :
    MeasurePreserving (forecastRawGridEquiv I E N U basis L) raw gridMeasure := by
  let : IsProbabilityMeasure deckLaw := by unfold mixedCoveredJetDeckReference; infer_instance
  have hs := ((MeasurePreserving.id (volume : Measure (RealAxis → ℝ))).prod
    (forecastIntegerAxisSplit_measurePreserving U basis L)).prod (MeasurePreserving.id deckLaw)
  have hr := productGridReorder_preserving (volume : Measure (RealAxis → ℝ))
    (Measure.count : Measure (short → ℤ)) (Measure.count : Measure (active → ℤ)) deckLaw
  convert hr.comp (hs.comp (forecastSingleMixedRawEquiv_measurePreserving I E n N)) using 1
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

private theorem productLeftComm_preserving
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (fun p : A × (B × C) => (p.2.1, (p.1, p.2.2)))
      (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  have h₁ := (measurePreserving_prodAssoc μ ν ρ).symm MeasurableEquiv.prodAssoc
  have h₂ := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id ρ)
  convert (measurePreserving_prodAssoc ν μ ρ).comp (h₂.comp h₁) using 1
  rfl

private theorem spatialGridReorder_preserving
    {K S D V A : Type*} [MeasurableSpace K] [MeasurableSpace S] [MeasurableSpace D]
    [MeasurableSpace V] [MeasurableSpace A]
    (μK : Measure K) (μS : Measure S) (μD : Measure D) (μV : Measure V) (μA : Measure A)
    [SFinite μK] [SFinite μS] [SFinite μD] [SFinite μV] [SFinite μA] :
    MeasurePreserving (fun p : K × ((S × D) × (V × A)) =>
      (p.2.1.2, (p.2.2.1, (p.2.1.1, (p.1, p.2.2.2)))))
      (μK.prod ((μS.prod μD).prod (μV.prod μA)))
      (μD.prod (μV.prod (μS.prod (μK.prod μA)))) := by
  have h₁ := (MeasurePreserving.id μK).prod (measurePreserving_prodAssoc μS μD (μV.prod μA))
  have h₂ := productLeftComm_preserving μK μS (μD.prod (μV.prod μA))
  have h₃ := (MeasurePreserving.id μS).prod (productLeftComm_preserving μK μD (μV.prod μA))
  have h₄ := (MeasurePreserving.id μS).prod
    ((MeasurePreserving.id μD).prod (productLeftComm_preserving μK μV μA))
  have h₅ := productLeftComm_preserving μS μD (μV.prod (μK.prod μA))
  have h₆ := (MeasurePreserving.id μD).prod (productLeftComm_preserving μS μV (μK.prod μA))
  convert h₆.comp (h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))) using 1
  rfl

private theorem integerSumCoordinates_preserving {X A : Type*} [Finite X] [Finite A] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : X ⊕ A => ℤ))
      Measure.count (Measure.count.prod Measure.count) := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : X ⊕ A => ℤ)
  refine ⟨e.measurable, ?_⟩
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply e.measurable (measurableSet_singleton z)]
  have he : e ⁻¹' {z} = {e.symm z} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact e.toEquiv.eq_symm_apply.symm
  rw [he, Measure.count_singleton, ← Set.singleton_prod_singleton,
    Measure.prod_prod, Measure.count_singleton, Measure.count_singleton, one_mul]

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (N : ℕ) [NeZero N]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (X : Type*) [Fintype X]

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "Deck" => ForecastSingleDeckResidues E N
local notation "RawSource" => MixedCoveredJetSource I single E n N
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := E) (n := n) N
local notation "deckLaw" => mixedCoveredJetDeckReference single E N
local notation "short" => AllocatedShortIntegerAxis U basis L
local notation "active" => AllocatedActiveIntegerAxis U basis L
local notation "Target" => Deck × ((RealAxis → ℝ) × ((short → ℤ) × ((X ⊕ active) → ℤ)))
local notation "targetLaw" => Measure.prod deckLaw (Measure.prod (volume : Measure (RealAxis → ℝ))
  (Measure.prod (Measure.count : Measure (short → ℤ)) (Measure.count : Measure ((X ⊕ active) → ℤ))))

theorem forecastRawSpatialEquiv_measurePreserving :
    MeasurePreserving (forecastRawSpatialEquiv I E N U basis L X)
      ((Measure.count : Measure (X → ℤ)).prod raw) targetLaw := by
  let : IsProbabilityMeasure deckLaw := by unfold mixedCoveredJetDeckReference; infer_instance
  let : SigmaFinite raw := by rw [forecastSingleMixedRawReference_eq I E n N]; infer_instance
  have h₁ := (MeasurePreserving.id (Measure.count : Measure (X → ℤ))).prod
    (forecastRawGridEquiv_measurePreserving I E N U basis L)
  have h₂ := spatialGridReorder_preserving (Measure.count : Measure (X → ℤ))
    (Measure.count : Measure (short → ℤ)) deckLaw (volume : Measure (RealAxis → ℝ))
    (Measure.count : Measure (active → ℤ))
  have hjoin := (integerSumCoordinates_preserving (X := X) (A := active)).symm
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : X ⊕ active => ℤ))
  have h₃ := (MeasurePreserving.id deckLaw).prod
    ((MeasurePreserving.id (volume : Measure (RealAxis → ℝ))).prod
      ((MeasurePreserving.id (Measure.count : Measure (short → ℤ))).prod hjoin))
  convert h₃.comp (h₂.comp h₁) using 1
  rfl

theorem forecastRawSpatial_integral
    (F : (X → ℤ) → RawSource → ℂ)
    (hF : Integrable (fun p : (X → ℤ) × RawSource => F p.1 p.2)
      ((Measure.count : Measure (X → ℤ)).prod raw)) :
    (∫ p : (X → ℤ) × RawSource, F p.1 p.2
      ∂(Measure.count : Measure (X → ℤ)).prod raw) =
      ∫ deck : Deck, ∫ v : RealAxis → ℝ,
        ∑' ks : short → ℤ, ∑' k : (X ⊕ active) → ℤ,
          F (fun x => k (Sum.inl x)) (forecastSingleMixedRawPoint I E n N v
            (forecastIntegerAxisMerge U basis L ks (fun a => k (Sum.inr a))) deck)
        ∂volume ∂deckLaw := by
  let : IsProbabilityMeasure deckLaw := by unfold mixedCoveredJetDeckReference; infer_instance
  let e := forecastRawSpatialEquiv I E N U basis L X
  have hp := (forecastRawSpatialEquiv_measurePreserving I E N U basis L X).symm e
  have hi := (hp.integrable_comp_emb e.symm.measurableEmbedding).mpr hF
  have he := hp.integral_comp e.symm.measurableEmbedding (fun p => F p.1 p.2)
  change (∫ p : Target, F (fun x => p.2.2.2 (Sum.inl x))
    (forecastSingleMixedRawPoint I E n N p.2.1
      (forecastIntegerAxisMerge U basis L p.2.2.1 (fun a => p.2.2.2 (Sum.inr a))) p.1)
      ∂targetLaw) = _ at he
  change Integrable (fun p : Target => F (fun x => p.2.2.2 (Sum.inl x))
    (forecastSingleMixedRawPoint I E n N p.2.1
      (forecastIntegerAxisMerge U basis L p.2.2.1 (fun a => p.2.2.2 (Sum.inr a))) p.1))
      targetLaw at hi
  rw [← he, integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with deck hd
  rw [integral_prod _ hd]
  apply integral_congr_ae
  filter_upwards [hd.prod_right_ae] with v hv
  rw [integral_prod _ hv, integral_countable hv.integral_prod_left]
  simp only [count_real_singleton, one_smul]
  apply tsum_congr
  intro ks
  have hrow := Measure.ae_count_iff.mp hv.prod_right_ae ks
  simpa only [count_real_singleton, one_smul] using integral_countable hrow

theorem forecastRawSpatialBox_normalized_integral_s2_oai
    (R : Fin m → ℝ) (hR : ∀ j, 0 < R j)
    (F : (X → ℤ) → RawSource → ℂ) (s : Finset (X → ℤ))
    (hf : ∀ u ∈ s, Integrable (F u) raw)
    (hzero : ∀ u ∉ s, ∀ z, F u z = 0) :
    (∑ u ∈ s, ∫ z, F u z ∂raw) = ((∏ a : RealAxis, R a.1 : ℝ) : ℂ) *
      ∫ deck : Deck, ∫ v : RealAxis → ℝ,
        ∑' ks : short → ℤ, ∑' k : (X ⊕ active) → ℤ,
          F (fun x => k (Sum.inl x))
            (forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
              (forecastIntegerAxisMerge U basis L ks (fun a => k (Sum.inr a))) deck)
        ∂volume ∂deckLaw := by
  let : IsProbabilityMeasure deckLaw := by unfold mixedCoveredJetDeckReference; infer_instance
  let : SigmaFinite raw := by rw [forecastSingleMixedRawReference_eq I E n N]; infer_instance
  have hF := forecastFiniteSpatialFamily_integrable raw F s hf hzero
  rw [forecastFiniteSpatialFamily_sum_integral raw F s hf hzero,
    forecastRawSpatial_integral I E N U basis L X F hF]
  conv_rhs => rw [← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun deck => ?_)
  dsimp only
  exact complex_integral_eq_positive_diagonal (fun a : RealAxis => R a.1)
    (fun a => hR a.1) _

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.forecastRawSpatialBox_normalized_integral_s2_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.forecastRawSpatialBox_normalized_integral_s2_oai.{u_1, u_2, u_3, u_4}
