-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_physical_rational_density_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:40:48.684685+00:00
-- url     : https://prove2.me/submissions/edba767e-ecc6-4c3b-b0cc-98ee052c0b46

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B244
import Definitions.Def_OAIE3v2B247
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_density_residue_comparison_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSlicedPhysicalResidueMean_eq_rationalMean_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3


open scoped BigOperators Classical

theorem integerScalarCubeWeights_root_bounds {α : Type*} [Fintype α] [DecidableEq α]
    {H : ℕ} (hH : 0 < H) (z : IntegerScalarCubeBox α H)
    (hz : (integerScalarCubeWeights α H hH).weight z ≠ 0) :
    0 ≤ (z none : ℤ) ∧ (z none : ℤ) ≤ ((H - 1 : ℕ) : ℤ) := by
  have hmem : z ∈ integerScalarCubeSet α H := by
    by_contra hn
    apply hz
    simp only [integerScalarCubeWeights, FiniteProbabilityWeights.condition,
      hn, ite_false, zero_div]
  have hr := ((mem_integerScalarCubeSet H z).mp hmem) ∅
  simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at hr
  exact ⟨hr.1, by omega⟩

theorem integerScalarCubePi_root_bounds {G : Type*} [Fintype G]
    (H : G → ℕ) (hH : ∀ g, 0 < H g)
    (z : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hz : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight z ≠ 0)
    (g : G) :
    0 ≤ (z g none : ℤ) ∧ (z g none : ℤ) ≤ ((H g - 1 : ℕ) : ℤ) := by
  apply integerScalarCubeWeights_root_bounds (hH g) (z g)
  change (∏ g, (integerScalarCubeWeights Empty (H g) (hH g)).weight (z g)) ≠ 0 at hz
  exact Finset.prod_ne_zero_iff.mp hz g (Finset.mem_univ g)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalizedMonomialTerm {K : Type*} (m : K →₀ ℕ) (scale value : K → ℝ)
    (Q b : ℝ) (hQ : Q ≠ 0) (hscale : ∀ k, scale k ≠ 0) :
    ((Q * b / (∏ k ∈ m.support, scale k ^ m k)) *
      (∏ k ∈ m.support, (scale k * value k) ^ m k)) / Q =
        b * ∏ k ∈ m.support, value k ^ m k := by
  classical
  have hs : (∏ k ∈ m.support, scale k ^ m k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (hscale k))
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MonomialArrayJet
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem monomialArrayPolynomial_rescale {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) (scale x : K → ℝ) (H : ℝ)
    (hH : H ≠ 0) (hscale : ∀ k, scale k ≠ 0) :
    MvPolynomial.eval (fun k => scale k*x k)
      (monomialArrayPolynomial e (fun j => H*a j/monomialScale scale (e j)))/H =
      MvPolynomial.eval x (monomialArrayPolynomial e a) := by
  rw [monomialArrayPolynomial_eval, monomialArrayPolynomial_eval, Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => normalizedMonomialTerm (e j) scale x H (a j) hH hscale)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionTupleSliceSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

theorem condition_weight_pos_iff {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < p.mass S) (x : Ω) :
    0 < (p.condition S hS).weight x ↔ x ∈ S ∧ 0 < p.weight x := by
  change 0 < (if x ∈ S then p.weight x else 0) / p.mass S ↔ _
  rw [lt_div_iff₀ hS, zero_mul]
  by_cases hx : x ∈ S <;> simp [hx]

theorem pi_weight_pos_component {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (x : ∀ j, Ω j) (hx : 0 < (pi p).weight x) (j : J) : 0 < (p j).weight (x j) := by
  apply lt_of_le_of_ne ((p j).nonneg (x j))
  intro he
  have hz : (pi p).weight x = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ j) he.symm
  linarith

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem containedProgressionCubeMap_value (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) (hz : IntegerScalarCube H (fun i => (z i : ℤ)))
    (i : Option I) :
    (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ) =
      (if i = none then c else 0) + (step : ℤ) * (z i : ℤ) := by
  rw [containedProgressionCubeMap, dif_pos hz]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRelativeChildSliceGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

theorem allocatedSampleNormalizedCoefficients_continuous (sample : Sample) (j : Fin m) (i : I j)
    (e : BoundedCoefficientExponent vars (j.val + 1)) :
    allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inl i⟩ e =
      (sample j).1 i e * monomialScale (layerSamplerBox B U basis S) e.val := by
  simp [allocatedSampleNormalizedCoefficients, allocatedContinuousProfileScales]

theorem allocatedSampleNormalizedCoefficients_integer (sample : Sample) (j : Fin m) (i : Fin (n j))
    (e : BoundedCoefficientExponent vars (j.val + 1)) :
    allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inr i⟩ e =
      ((sample j).2 i e : ℝ) * monomialScale (layerSamplerBox B U basis S) e.val /
        (basisAxisScale (basis j) i : ℝ) := by
  simp only [allocatedSampleNormalizedCoefficients, allocatedIntegerProfileScales, div_div_eq_mul_div]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleSliceSubstitution_eval (y : Input → ℝ) (k : vars) :
    MvPolynomial.eval y (allocatedOriginalSampleSliceSubstitution B U basis S x u lower width k) =
      allocatedOriginalSampleSliceInput B U basis S x u lower width y k := by
  rcases k with g | ⟨a, b, i⟩
  · simp only [allocatedOriginalSampleSliceSubstitution, allocatedOriginalSampleSliceInput,
      MvPolynomial.eval_C]
  · by_cases ha : short a <;>
      simp [allocatedOriginalSampleSliceSubstitution, allocatedOriginalSampleSliceInput, ha]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleFullSliceLipschitz
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleFullSliceMap_eq_eval (sample : Sample) (y : Input → ℝ) (o : Output) :
    allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y o =
      MvPolynomial.eval (allocatedOriginalSampleSliceInput B U basis S x u lower width y)
        (monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val)) /
          R o.1.val.1 := by
  simp only [allocatedOriginalSampleFullSliceMap, allocatedOriginalSampleSliceSubstitution_eval]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CanonicalSpatialSupport
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
theorem selectedColumn_sum (s : I ↪ J) (f : J → ℝ) :
    (∑ i, f (s i)) + (∑ j : UnselectedColumn s, f j.val) = ∑ j, f j := by
  calc
    _ = ∑ j : I ⊕ UnselectedColumn s, f (selectedColumnEquiv s j) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = _ := Equiv.sum_comp (selectedColumnEquiv s) f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem boundedCoefficientJetMatrix_empty {α K : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ)
    (e : VectorPolynomial.BoundedCoefficientExponent K h) :
    boundedCoefficientJetMatrix root D h (fun _ : Unit => ∅) () e =
      VectorPolynomial.boundedSiteMatrix h (fun _ : Unit => root) () e := by
  simp [boundedCoefficientJetMatrix, boundedDegreeIntegerJetMatrix,
    boundedCoefficientIntegerExponentEquiv, integerJetMatrix, booleanCoefficient,
    integerAffineCube, VectorPolynomial.boundedSiteMatrix, MvPolynomial.eval_monomial]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

theorem allocatedOriginalSamplePhysicalMixedValue_real (j : Fin m) (i : I j) :
    (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).1 i =
      MvPolynomial.eval (fun v =>
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y v : ℝ))
        (monomialArrayPolynomial Subtype.val ((sample j).1 i)) := by
  rw [monomialArrayPolynomial_eval]
  change (∑ d, (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (j.val + 1) (fun _ : Unit => ∅) () d : ℝ) * (sample j).1 i d) = _
  apply Finset.sum_congr rfl
  intro d _
  rw [boundedCoefficientJetMatrix_empty]
  simp only [boundedSiteMatrix, Finsupp.prod, Int.cast_prod, Int.cast_pow]
  exact mul_comm _ _

theorem allocatedOriginalSamplePhysicalMixedValue_integer (j : Fin m) (i : Fin (n j)) :
    (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).2 i =
      MvPolynomial.eval (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (∑ d, MvPolynomial.monomial d.val ((sample j).2 i d)) := by
  simp only [map_sum, MvPolynomial.eval_monomial, Finsupp.prod]
  change (∑ d, boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (j.val + 1) (fun _ : Unit => ∅) () d * (sample j).2 i d) = _
  apply Finset.sum_congr rfl
  intro d _
  rw [boundedCoefficientJetMatrix_empty]
  exact mul_comm _ _

theorem allocatedOriginalSamplePhysicalMixedValue_integer_cast
    (j : Fin m) (i : Fin (n j)) :
    ((allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).2 i : ℝ) =
      MvPolynomial.eval (fun v =>
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y v : ℝ))
        (monomialArrayPolynomial Subtype.val (fun d => ((sample j).2 i d : ℝ))) := by
  rw [allocatedOriginalSamplePhysicalMixedValue_integer]
  simp only [monomialArrayPolynomial, map_sum, MvPolynomial.eval_monomial,
    Finsupp.prod, Int.cast_sum, Int.cast_mul, Int.cast_prod, Int.cast_pow]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem monomialArrayPolynomial_eval_normalized_input
    {C K : Type*} [Fintype C] (e : C → K →₀ ℕ) (a : C → ℝ)
    (scale x : K → ℝ) (hscale : ∀ k, scale k ≠ 0) :
    MvPolynomial.eval (fun k => x k / scale k)
      (monomialArrayPolynomial e (fun c => a c * monomialScale scale (e c))) =
    MvPolynomial.eval x (monomialArrayPolynomial e a) := by
  have hm (c : C) : monomialScale scale (e c) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (hscale k))
  have h := monomialArrayPolynomial_rescale e
    (fun c => a c * monomialScale scale (e c)) scale (fun k => x k / scale k)
    1 one_ne_zero hscale
  simpa only [one_mul, div_one, mul_div_cancel_right₀ _ (hm _),
    mul_div_cancel₀ _ (hscale _)] using h.symm

theorem monomialArrayPolynomial_eval_div_coefficients
    {C K : Type*} [Fintype C] (e : C → K →₀ ℕ) (a : C → ℝ) (x : K → ℝ) (H : ℝ) :
    MvPolynomial.eval x (monomialArrayPolynomial e (fun c => a c / H)) =
      MvPolynomial.eval x (monomialArrayPolynomial e a) / H := by
  simp only [monomialArrayPolynomial_eval, Finset.sum_div, div_mul_eq_mul_div]

namespace VectorPolynomial
open Module
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "vars" => LayerSamplerVariables G I n B
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "sides" => allocatedPrincipalSides B U basis S

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

local notation "root" => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "physical" => allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y

theorem allocatedSampleNormalizedCoefficients_eval_physical (a : LayerSamplerAxis I n) :
    MvPolynomial.eval (fun k => (root k : ℝ) / layerSamplerBox B U basis S k)
      (monomialArrayPolynomial Subtype.val
        (allocatedSampleNormalizedCoefficients B U basis S sample a)) / R a.1 =
      allocatedFullMixedSiteValue (R := R) U basis physical a := by
  have hscale (k : vars) : layerSamplerBox B U basis S k ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S k)).ne'
  rcases a with ⟨j, i | i⟩
  · have hc : allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inl i⟩ =
        fun d => (sample j).1 i d * monomialScale (layerSamplerBox B U basis S) d.val :=
      funext (allocatedSampleNormalizedCoefficients_continuous B U basis S sample j i)
    rw [hc]
    dsimp only [layerSamplerDegree]
    erw [monomialArrayPolynomial_eval_normalized_input _ _ _ _ hscale]
    change _ = (physical j).1 i / R j
    rw [allocatedOriginalSamplePhysicalMixedValue_real]
    rfl
  · have hc : allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inr i⟩ =
        fun d => ((sample j).2 i d : ℝ) * monomialScale (layerSamplerBox B U basis S) d.val /
          (basisAxisScale (basis j) i : ℝ) :=
      funext (allocatedSampleNormalizedCoefficients_integer B U basis S sample j i)
    rw [hc]
    dsimp only [layerSamplerDegree]
    erw [monomialArrayPolynomial_eval_div_coefficients,
      monomialArrayPolynomial_eval_normalized_input _ _ _ _ hscale]
    change _ = ((physical j).2 i : ℝ) / basisAxisScale (basis j) i / R j
    rw [allocatedOriginalSamplePhysicalMixedValue_integer_cast]
    rfl

theorem allocatedOriginalSampleSliceInput_physical :
    allocatedOriginalSampleSliceInput B U basis S x (principalAxisRestrict short y)
      (fun _ _ => 0) (fun _ _ => 1)
      (fun j : Input => (y ⟨j.1.val,j.2⟩ none : ℝ) / S.value) =
      fun k => (root k : ℝ) / layerSamplerBox B U basis S k := by
  funext k
  rcases k with g | ⟨a,b,i⟩
  · simp [allocatedOriginalSampleSliceInput, allocatedPhysicalCubeRoot, layerSamplerBox,
      layerSamplerSides, heterogeneousSamplerSides]
  · by_cases ha : short a
    · simp only [allocatedOriginalSampleSliceInput, ha, ↓reduceDIte,
        principalAxisRestrict, allocatedPhysicalCubeRoot, zero_add, Sum.elim_inr]
      rfl
    · simp only [allocatedOriginalSampleSliceInput, ha, ↓reduceDIte,
        zero_add, one_mul, allocatedPhysicalCubeRoot, Sum.elim_inr]
      change _ / (S.value : ℝ) = _ / (sides ⟨a,b,i⟩ : ℝ)
      exact congrArg (fun l : ℕ => (y ⟨a,b,i⟩ none : ℝ) / (l : ℝ))
        (allocatedPrincipalSides_not_short B U basis S ⟨a,ha⟩ (b,i)).symm

theorem allocatedOriginalSampleFullSliceMap_physical :
    allocatedOriginalSampleFullSliceMap B U basis S x (principalAxisRestrict short y)
      (fun _ _ => 0) (fun _ _ => 1) sample
      (fun j : Input => (y ⟨j.1.val,j.2⟩ none : ℝ) / S.value) =
      fun o : Output => allocatedFullMixedSiteValue (R := R) U basis physical o.1.val := by
  funext o
  rw [allocatedOriginalSampleFullSliceMap_eq_eval, allocatedOriginalSampleSliceInput_physical]
  exact allocatedSampleNormalizedCoefficients_eval_physical B U basis S sample x y o.1.val

omit y in
theorem allocatedOriginalSampleFullSliceMap_physical_join
    (u : PrincipalAxisTuples (α := Empty) short sides)
    (v : PrincipalAxisTuples (α := Empty) (fun a => ¬short a) sides) :
    allocatedOriginalSampleFullSliceMap B U basis S x u
      (fun _ _ => 0) (fun _ _ => 1) sample
      (fun j : Input => (v j none : ℝ) / S.value) =
      fun o : Output => allocatedFullMixedSiteValue (R := R) U basis
        (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x
          (principalAxisJoin short u v)) o.1.val := by
  have h := allocatedOriginalSampleFullSliceMap_physical B U basis S sample x
    (principalAxisJoin short u v)
  rw [principalAxisRestrict_join_left] at h
  have hv : (fun j : Input =>
      (principalAxisJoin short u v ⟨j.1.val,j.2⟩ none : ℝ) / S.value) =
      (fun j : Input => (v j none : ℝ) / S.value) := by
    funext j
    simp only [principalAxisJoin, j.1.property, ↓reduceDIte]
  rw [hv] at h
  exact h

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedNarrowSpatialCanonicalComparison
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

variable {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ) (W L : ℝ)

omit [Fintype X] in
theorem canonicalZeroSpatialInputMap_apply (hW : 0 ≤ W)
    (u : Option Zsp × X → ℝ) (x : X) :
    canonicalZeroSpatialInputMap s root D W L u ⟨x, Sum.inl ()⟩ =
      u (none, x) + (∑ j, (root j : ℝ) * u (some j, x)) / (1 + W) := by
  have hsum := selectedColumn_sum s (fun j => (root j : ℝ) * u (some j, x))
  simp only [Fintype.sum_empty, zero_add] at hsum
  unfold canonicalZeroSpatialInputMap canonicalSpatialKernelMap
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, normalizedIntegerPivot_entry,
    normalizedIntegerColumns_entry_div, Fintype.sum_sum_type, Fintype.sum_empty,
    add_zero, Fintype.sum_unique, selectedSpatialPivot, rootDifferenceMatrix, Matrix.fromBlocks_apply₁₁, Matrix.one_apply_eq,
    selectedSpatialFreeColumns, Matrix.of_apply, anisotropicSpatialScale,
    physicalSpatialOutputScale, Sum.elim_inl, Int.cast_one, one_mul,
    div_self (by linarith : (1 + W : ℝ) ≠ 0)]
  congr 1
  rw [← hsum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem canonicalZeroSpatialNarrowInput_kernel {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) :
    canonicalZeroSpatialNarrowInput ξ u ∘ canonicalZeroSpatialKernelEmbedding G N X =
      u ∘ canonicalZeroSpatialKernelEmbedding G N X := by
  funext a
  rcases a with ⟨a, x⟩
  cases a <;> rfl

variable {G N X : Type*} [Fintype G] [DecidableEq G]
  [Fintype N] [DecidableEq N] [Fintype X]
variable (s : Empty ↪ G) (sf : Empty ↪ (G ⊕ N))
  (root : G → ℤ) (principal : N → ℤ)
  (D : Matrix Empty G ℤ) (Df : Matrix Empty (G ⊕ N) ℤ) (W L : ℝ)

omit [Fintype X] in
theorem canonicalZeroSpatialPrincipal_difference (hW : 0 ≤ W)
    (u : Option (G ⊕ N) × X → ℝ) (x : X) :
    canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L u ⟨x, .inl ()⟩ -
        canonicalZeroSpatialInputMap s root D W L
          (u ∘ canonicalZeroSpatialKernelEmbedding G N X) ⟨x, .inl ()⟩ =
      (∑ n, (principal n : ℝ) * u (some (.inr n), x)) / (1 + W) := by
  rw [canonicalZeroSpatialInputMap_apply sf _ Df W L hW,
    canonicalZeroSpatialInputMap_apply s root D W L hW]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, canonicalZeroSpatialKernelEmbedding_apply,
    Option.map_none, Option.map_some]
  ring

theorem canonicalZeroSpatialPrincipal_norm_le (hW : 0 ≤ W)
    (u : Option (G ⊕ N) × X → ℝ) (hu : ‖u‖ ≤ 1) :
    ‖canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L u -
        canonicalZeroSpatialInputMap s root D W L
          (u ∘ canonicalZeroSpatialKernelEmbedding G N X)‖ ≤
      (∑ n, |(principal n : ℝ)|) / (1 + W) := by
  have hden : 0 < 1 + W := by linarith
  have hbound : 0 ≤ (∑ n, |(principal n : ℝ)|) / (1 + W) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hden.le
  apply (pi_norm_le_iff_of_nonneg hbound).mpr
  rintro ⟨x, a⟩
  cases a with
  | inr e => exact Empty.elim e
  | inl a =>
    cases a
    rw [Pi.sub_apply, canonicalZeroSpatialPrincipal_difference s sf root principal D Df W L hW,
      Real.norm_eq_abs, abs_div, abs_of_pos hden]
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      _ ≤ ∑ n, |(principal n : ℝ) * u (some (.inr n), x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n, |(principal n : ℝ)| := by
        apply Finset.sum_le_sum
        intro n _
        rw [abs_mul]
        have hn : |u (some (.inr n), x)| ≤ 1 :=
          (Real.norm_eq_abs _).symm ▸ (norm_le_pi_norm u (some (.inr n), x)).trans hu
        exact mul_le_of_le_one_right (abs_nonneg _) hn

omit [Fintype X] in
theorem canonicalZeroSpatialNarrowPrincipal_difference (hW : 0 ≤ W) (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) :
    canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
        (canonicalZeroSpatialNarrowInput ξ u) -
      canonicalZeroSpatialInputMap s root D W L
        (u ∘ canonicalZeroSpatialKernelEmbedding G N X) =
    ξ • (canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L u -
      canonicalZeroSpatialInputMap s root D W L
        (u ∘ canonicalZeroSpatialKernelEmbedding G N X)) := by
  ext ⟨x, a⟩
  cases a with
  | inr e => exact Empty.elim e
  | inl a =>
    cases a
    have h := canonicalZeroSpatialPrincipal_difference s sf root principal D Df W L hW
      (canonicalZeroSpatialNarrowInput ξ u) x
    rw [canonicalZeroSpatialNarrowInput_kernel] at h
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [h, canonicalZeroSpatialPrincipal_difference s sf root principal D Df W L hW]
    simp only [canonicalZeroSpatialNarrowInput_inr]
    rw [← mul_div_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    ring

theorem canonicalZeroSpatialNarrowPrincipal_norm_le (hW : 0 ≤ W) (ξ : ℝ) (hξ0 : 0 ≤ ξ)
    (u : Option (G ⊕ N) × X → ℝ) (hu : ‖u‖ ≤ 1) :
    ‖canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
        (canonicalZeroSpatialNarrowInput ξ u) -
      canonicalZeroSpatialInputMap s root D W L
        (u ∘ canonicalZeroSpatialKernelEmbedding G N X)‖ ≤
      ξ * ((∑ n, |(principal n : ℝ)|) / (1 + W)) := by
  rw [canonicalZeroSpatialNarrowPrincipal_difference s sf root principal D Df W L hW ξ,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hξ0]
  exact mul_le_mul_of_nonneg_left
    (canonicalZeroSpatialPrincipal_norm_le s sf root principal D Df W L hW u hu) hξ0

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem canonicalZeroSpatialInputMap_physicalSite
    {X Zsp : Type*} [Fintype Zsp] [DecidableEq Zsp]
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    {W : ℝ} (hW : 0 ≤ W) (L τ : ℝ) (N : X → ℕ)
    (z : Option Zsp × X → ℤ) (x : X) :
    canonicalZeroSpatialInputMap s root D W L
      (fun k => (z k : ℝ) / trimmedSpatialWidths W τ N k) ⟨x, Sum.inl ()⟩ =
      (integerPhysicalSite root z x : ℝ) / (τ * (N x : ℝ) / 8) := by
  have hb : (1 + W : ℝ) ≠ 0 := by linarith
  have hn : trimmedSpatialWidths (K := Zsp) W τ N (none, x) = τ * (N x : ℝ) / 8 := by
    simp only [trimmedSpatialWidths, centeredSpatialWidths]
    ring
  have hs (j : Zsp) : trimmedSpatialWidths W τ N (some j, x) =
      (τ * (N x : ℝ) / 8) / (1 + W) := by
    simp only [trimmedSpatialWidths, centeredSpatialWidths, one_mul, div_div]
    ring
  rw [canonicalZeroSpatialInputMap_apply s root D W L hW]
  simp only [integerPhysicalSite, Int.cast_add, Int.cast_sum, Int.cast_mul, hn, hs,
    add_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [div_div_eq_mul_div]
  by_cases ht : τ * (N x : ℝ) / 8 = 0
  · simp only [ht, div_zero, mul_zero, zero_div]
  · field_simp

theorem canonicalZeroSpatialNarrowInput_normalized
    {G J X : Type*} {ξ : ℝ} (hξ : ξ ≠ 0) (W τ : ℝ) (N : X → ℕ)
    (z : Option (G ⊕ J) × X → ℤ) :
    canonicalZeroSpatialNarrowInput ξ
      (fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ N k) =
      fun k => (z k : ℝ) / trimmedSpatialWidths W τ N k := by
  funext k
  rcases k with ⟨_ | (g | j), x⟩
  · rfl
  · rfl
  · simp only [canonicalZeroSpatialNarrowInput, narrowTrimmedSpatialWidths]
    by_cases hw : trimmedSpatialWidths (K := G ⊕ J) W τ N (some (Sum.inr j), x) = 0
    · simp only [hw, mul_zero, div_zero]
    · field_simp

theorem canonicalZeroSpatialNarrowInputMap_physicalSite
    {G J X : Type*} [Fintype G] [Fintype J] [DecidableEq G] [DecidableEq J]
    (s : Empty ↪ (G ⊕ J)) (root : G ⊕ J → ℤ) (D : Matrix Empty (G ⊕ J) ℤ)
    {W ξ : ℝ} (hW : 0 ≤ W) (hξ : ξ ≠ 0) (L τ : ℝ) (N : X → ℕ)
    (z : Option (G ⊕ J) × X → ℤ) (x : X) :
    canonicalZeroSpatialInputMap s root D W L
      (canonicalZeroSpatialNarrowInput ξ
        (fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ N k)) ⟨x, Sum.inl ()⟩ =
      (integerPhysicalSite root z x : ℝ) / (τ * (N x : ℝ) / 8) := by
  rw [canonicalZeroSpatialNarrowInput_normalized hξ W τ N z]
  exact canonicalZeroSpatialInputMap_physicalSite s root D hW L τ N z x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {G N X : Type*} [Fintype G] [DecidableEq G]
  [Fintype N] [DecidableEq N] [Fintype X]
variable (s : Empty ↪ G) (sf : Empty ↪ (G ⊕ N))
  (root : G → ℤ) (principal : N → ℤ)
  (D : Matrix Empty G ℤ) (Df : Matrix Empty (G ⊕ N) ℤ) (W L : ℝ)

omit [DecidableEq G] [DecidableEq N] in
theorem canonicalZeroSpatialPrincipal_mass_ratio_le_one (hW : 0 ≤ W)
    (hbudget : (∑ k : G ⊕ N, |((Sum.elim root principal k : ℤ) : ℝ)|) ≤ W) :
    (∑ n, |(principal n : ℝ)|) / (1 + W) ≤ 1 := by
  have hroot0 : 0 ≤ ∑ g, |(root g : ℝ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hbudget
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < 1 + W)).mpr
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical NNReal
variable {G X : Type*} [Fintype G] [Fintype X]

variable [DecidableEq G]

omit [Fintype X] in
theorem fixedSpatialKernelMap_integer (s : Empty ↪ G) (root : G → ℤ)
    (D : Matrix Empty G ℤ) {W L : ℝ} (hW : 0 ≤ W) (hL : L ≠ 0)
    (z : Option G × X → ℝ) :
    fixedSpatialKernelMap W L z (fun g => (root g : ℝ) / L) =
      canonicalZeroSpatialInputMap s root D W L z := by
  funext a
  rcases a with ⟨x, a⟩
  cases a with
  | inr e => exact Empty.elim e
  | inl u =>
    cases u
    rw [canonicalZeroSpatialInputMap_apply s root D W L hW]
    unfold fixedSpatialKernelMap
    simp only
    congr 1
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    field_simp

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem rectangularWeightIndices_normalized_norm_le
    {K : Type*} [Fintype K] (V : K → ℝ) (hV : ∀ k, 0 < V k)
    {z : K → ℤ} (hz : z ∈ rectangularWeightIndices 0 V 1) :
    ‖fun k => (z k : ℝ) / V k‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro k
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hV k), div_le_one (hV k)]
  exact rectangularWeightIndices_zero_bound V hz k

variable {G N X : Type*} [Fintype G] [DecidableEq G]
  [Fintype N] [DecidableEq N] [Fintype X]

theorem fixedSpatialKernelMap_narrow_physical_dist
    (root : G → ℤ) (principal : N → ℤ) {W L τ ξ : ℝ}
    (hW : 0 ≤ W) (hL : L ≠ 0) (hξ : 0 < ξ)
    (hbudget : (∑ k : G ⊕ N, |((Sum.elim root principal k : ℤ) : ℝ)|) ≤ W)
    (box : X → ℕ) (z : Option (G ⊕ N) × X → ℤ)
    (hz : ‖fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ box k‖ ≤ 1) :
    dist (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (Sum.elim root principal) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8))
      (fixedSpatialKernelMap W L
        ((fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G N X)
        (fun g => (root g : ℝ) / L)) ≤ ξ := by
  let s : Empty ↪ G := ⟨Empty.elim, fun e => Empty.elim e⟩
  let sf : Empty ↪ (G ⊕ N) := ⟨Empty.elim, fun e => Empty.elim e⟩
  let D : Matrix Empty G ℤ := fun e => Empty.elim e
  let Df : Matrix Empty (G ⊕ N) ℤ := fun e => Empty.elim e
  have hsite : canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
      (canonicalZeroSpatialNarrowInput ξ
        (fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ box k)) =
      fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (Sum.elim root principal) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8) := by
    funext o
    rcases o with ⟨x, a⟩
    cases a with
    | inr e => exact Empty.elim e
    | inl a =>
      cases a
      exact canonicalZeroSpatialNarrowInputMap_physicalSite sf _ Df hW hξ.ne' L τ box z x
  rw [fixedSpatialKernelMap_integer s root D hW hL, ← hsite, dist_eq_norm]
  exact (canonicalZeroSpatialNarrowPrincipal_norm_le s sf root principal D Df W L
    hW ξ hξ.le _ hz).trans (mul_le_of_le_one_right hξ.le
      (canonicalZeroSpatialPrincipal_mass_ratio_le_one root principal W hW hbudget))

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "principal" => PrincipalTupleIndex B (layerSamplerDegree I n)
local notation "vars" => LayerSamplerVariables G I n B
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

theorem allocatedFixedSpatialKernelMap_narrow_physical_dist
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S))
    {τ ξ : ℝ} (hξ : 0 < ξ) (box : X → ℕ)
    (z : Option vars × X → ℤ)
    (hz : ‖fun k => (z k : ℝ) /
      narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box k‖ ≤ 1) :
    dist (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8))
      (fixedSpatialKernelMap budget (S.value : ℝ)
        ((fun k => (z k : ℝ) / narrowTrimmedSpatialWidths budget τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G principal X)
        (fun g => ((x g none : ℤ) : ℝ) / (S.value : ℝ))) ≤ ξ := by
  have hr : allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y =
      Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) := by
    funext k
    simp only [allocatedPhysicalCubeRoot, zero_add]
  have hbudget : (∑ k : vars,
      |((Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) k : ℤ) : ℝ)|) ≤ budget := by
    simpa only [hr] using allocatedPhysicalCube_root_sum B U basis S (fun _ => 0) x y
  rw [hr]
  exact fixedSpatialKernelMap_narrow_physical_dist _ _
    (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
    (Nat.cast_ne_zero.mpr S.positive.ne') hξ hbudget box z hz

theorem allocatedFixedSpatialKernelMap_supported_narrow_physical_dist
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S))
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ o, 0 < box o)
    (z : Option vars × X → ℤ)
    (hz : z ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box) 1) :
    dist (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8))
      (fixedSpatialKernelMap budget (S.value : ℝ)
        ((fun k => (z k : ℝ) / narrowTrimmedSpatialWidths budget τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G principal X)
        (fun g => ((x g none : ℤ) : ℝ) / (S.value : ℝ))) ≤ ξ := by
  exact allocatedFixedSpatialKernelMap_narrow_physical_dist B U basis S x y hξ box z
    (rectangularWeightIndices_normalized_norm_le _
      (narrowTrimmedSpatialWidths_pos
        (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hτ hξ box hbox) hz)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {G : Type*} [Fintype G]

theorem containedKernelCubeMap_value (S : ℕ) (H step : G → ℕ) (c : G → ℤ)
    (hS : 0 < S) (hH : ∀ g, 0 < H g)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight x ≠ 0)
    (g : G) :
    (containedKernelCubeMap S H step c hS hsubset x g none : ℤ) =
      c g + (step g : ℤ) * (x g none : ℤ) := by
  have hpos := lt_of_le_of_ne ((FiniteProbabilityWeights.pi
    (fun g => integerScalarCubeWeights Empty (H g) (hH g))).nonneg x) hx.symm
  have hg := FiniteProbabilityWeights.pi_weight_pos_component
    (fun g => integerScalarCubeWeights Empty (H g) (hH g)) x hpos g
  have hcube := (mem_integerScalarCubeSet (H g) (x g)).mp
    ((FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ (x g)).mp hg).1
  simpa only [containedKernelCubeMap, ite_true] using
    (containedProgressionCubeMap_value Empty S (H g) (step g) (c g) hS
      (hsubset g) (x g) hcube none)

theorem containedKernelCubeMap_normalized (S : ℕ) (H step : G → ℕ) (c : G → ℤ)
    (hS : 0 < S) (hH : ∀ g, 0 < H g)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight x ≠ 0) :
    (fun g => ((containedKernelCubeMap S H step c hS hsubset x g none : ℤ) : ℝ) / S) =
      fun g => ((c g : ℝ) + (step g : ℝ) * (x g none : ℝ)) / S := by
  funext g
  rw [containedKernelCubeMap_value S H step c hS hH hsubset x hx g]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]

namespace VectorPolynomial

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "principal" => PrincipalTupleIndex B (layerSamplerDegree I n)
local notation "vars" => LayerSamplerVariables G I n B
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

theorem allocatedContainedKernel_supported_narrow_physical_dist
    (H step : G → ℕ) (c : G → ℤ) (hH : ∀ g, 0 < H g)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight x ≠ 0)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S))
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ o, 0 < box o)
    (integerFrame : Option vars × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box) 1) :
    dist (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0)
          (containedKernelCubeMap S.value H step c S.positive hsubset x) y) integerFrame o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8))
      (fixedSpatialKernelMap budget (S.value : ℝ)
        ((fun k => (integerFrame k : ℝ) / narrowTrimmedSpatialWidths budget τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G principal X)
        (fun g => ((c g : ℝ) + (step g : ℝ) * (x g none : ℝ)) / S.value)) ≤ ξ := by
  rw [← containedKernelCubeMap_normalized S.value H step c S.positive hH hsubset x hx]
  exact allocatedFixedSpatialKernelMap_supported_narrow_physical_dist B U basis S
    (containedKernelCubeMap S.value H step c S.positive hsubset x) y
    hτ hξ box hbox integerFrame hframe

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedActiveContainedTupleMap
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedActiveContainedProgression_value
    (step H : Input → ℕ) (c : Input → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (v : ∀ j, IntegerScalarCubeBox Empty (H j))
    (hv : (FiniteProbabilityWeights.pi
      (fun j => integerScalarCubeWeights Empty (H j) (hH j))).weight v ≠ 0) (j : Input) :
    (allocatedActiveContainedProgression B U basis S step H c hsubset v j none : ℤ) =
      c j + (step j : ℤ) * (v j none : ℤ) := by
  have hb := integerScalarCubePi_root_bounds H hH v hv j
  have hc : IntegerScalarCube (H j) (fun i => (v j i : ℤ)) := by
    intro t
    have ht : t = ∅ := Subsingleton.elim _ _
    subst t
    simpa only [integerScalarCubeValue, Finset.sum_empty, add_zero] using
      (show 0 ≤ (v j none : ℤ) ∧ (v j none : ℤ) < (H j : ℤ) from ⟨hb.1, by have := hH j; omega⟩)
  simpa only [allocatedActiveContainedProgression, ite_true] using
    containedProgressionCubeMap_value Empty S.value (H j) (step j) (c j)
      S.positive (hsubset j) (v j) hc none

theorem allocatedOriginalSampleFullSliceMap_contained_physical
    (step H : Input → ℕ) (c : Input → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (v : ∀ j, IntegerScalarCubeBox Empty (H j))
    (hv : (FiniteProbabilityWeights.pi
      (fun j => integerScalarCubeWeights Empty (H j) (hH j))).weight v ≠ 0)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (u : PrincipalAxisTuples (α := Empty) short sides) :
    allocatedOriginalSampleFullSliceMap B U basis S x u
      (fun _ _ => 0) (fun _ _ => 1) sample
      (fun j => ((c j : ℝ) + (step j : ℝ) * (v j none : ℝ)) / S.value) =
      fun o : Output => allocatedFullMixedSiteValue (R := R) U basis
        (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x
          (principalAxisJoin short u
            (allocatedActiveContainedProgression B U basis S step H c hsubset v))) o.1.val := by
  have he (j : Input) :
      (allocatedActiveContainedProgression B U basis S step H c hsubset v j none : ℝ) =
      (c j : ℝ) + (step j : ℝ) * (v j none : ℝ) := by
    exact_mod_cast allocatedActiveContainedProgression_value B U basis S step H c hH hsubset v hv j
  simpa only [he] using allocatedOriginalSampleFullSliceMap_physical_join B U basis S sample x u
    (allocatedActiveContainedProgression B U basis S step H c hsubset v)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFixedPathSlicedPhysicalDensityComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n

variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => Spatial × (Output → ℝ)
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

include hR hσ in
theorem allocatedFixedPath_sliced_physical_density_residue_comparison
    (τ ξ : ℝ) (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ x, 0 < box x)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B degree) budget τ ξ box) 1)
    (HG : G → ℕ) (hHG : ∀ g, 2 ≤ HG g) (cG : G → ℤ)
    (stepG : ℕ) (hstepG : 0 < stepG)
    (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (e : G ≃ X ⊕ (X ⊕ T))
    (h0 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e budget (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (step H : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (q : ℕ) [NeZero q]
    (hsizeG : ∀ g, q ≤ HG g)
    (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1) (hsize : ∀ j, q ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (hδone : δ ≤ 1) (b : ∀ a : Active, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
    (φ : (G → ZMod q) → (Input → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ rG r, LipschitzWith Kφ (φ rG r)) (hφone : ∀ rG r y, ‖φ rG r y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (HG g) (by have := hHG g; omega))
    let active := FiniteProbabilityWeights.pi (fun j : Input => integerScalarCubeWeights Empty (H j)
      (by have := hH j; omega))
    let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) g =>
      containedProgressionCubeMap Empty S.value (HG g) stepG (cG g) S.positive (hcontainedG g) (x g)
    let activeEmbed := allocatedActiveContainedProgression B U basis S step H c hsubset
    let joined := fun v => principalAxisJoin short u (activeEmbed v)
    let density := fixedSpatialKernelSliceOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) (fun g => (cG g : ℝ) / S.value)
      (fun g => (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value) h0 h1
      (fun g => ne_of_gt (fixedSpatialKernelProgression_width_pos S.positive
        (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g))) hB lower width sample
    ‖kernel.complexMean (fun x => active.complexMean (fun v =>
        φ (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
          (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
          ((fun o : Σ _ : X, Unit ⊕ Empty =>
              (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0)
                (embed x) (joined v)) integerFrame o.1 : ℝ) / (τ * (box o.1 : ℝ) / 8)),
            (fun o : Output => allocatedFullMixedSiteValue (R := R) U basis
              (allocatedOriginalSamplePhysicalMixedValue B U basis S sample (embed x) (joined v))
                o.1.val)))) -
      (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun rA =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          ∫ y, φ (fun g => (cG g : ZMod q) + (stepG : ZMod q) * rG g)
            (fun j => (c j : ZMod q) + (step j : ZMod q) * rA j) y
            ∂realDensityMeasure volume density))‖ ≤
      ((∑ j, (q : ℝ) / H j) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) * ∑ g, (q : ℝ) / HG g + (Kφ : ℝ) * ξ := by
  classical
  intro lower width K kernel active embed activeEmbed joined density
  let zK := allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame
  have hnorm := rectangularWeightIndices_normalized_norm_le _
    (narrowTrimmedSpatialWidths_pos
      (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hτ hξ box hbox) hframe
  have hzK : ∀ g x, |zK (some g, x)| ≤ 1 := by
    intro g x
    change |(integerFrame (some (Sum.inl g), x) : ℝ) /
      narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B degree)
        budget τ ξ box (some (Sum.inl g), x)| ≤ 1
    exact (Real.norm_eq_abs _).symm ▸
      (norm_le_pi_norm _ (some (Sum.inl g), x)).trans hnorm
  have hmain := allocatedFixedPath_sliced_density_residue_comparison_s2 B U basis hR hσ S u
    zK hzK HG hHG cG stepG hstepG hcontainedG e h0 h1 hB sample hs ht hσbound
    step H c hstep hH hδ hsubset hdense q hsizeG hsmallG hsize hsmall hε hmesh
    hδone b hη A hA htail φ hφ hφone
  let F := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g))
      (v : ∀ j : Input, IntegerScalarCubeBox Empty (H j)) =>
    φ (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
      (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
      ((fun o : Σ _ : X, Unit ⊕ Empty =>
          (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0)
            (embed x) (joined v)) integerFrame o.1 : ℝ) / (τ * (box o.1 : ℝ) / 8)),
        (fun o : Output => allocatedFullMixedSiteValue (R := R) U basis
          (allocatedOriginalSamplePhysicalMixedValue B U basis S sample (embed x) (joined v)) o.1.val))
  let Fideal := fun (x : ∀ g, IntegerScalarCubeBox Empty (HG g))
      (v : ∀ j : Input, IntegerScalarCubeBox Empty (H j)) =>
    φ (fun g => ((cG g + (stepG : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
      (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q))
      (fixedSpatialKernelMap budget (S.value : ℝ) zK
        (fun g => ((cG g : ℝ) + (stepG : ℝ) * (x g none : ℝ)) / S.value),
        allocatedOriginalSampleFullSliceMap B U basis S (embed x) u (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => ((c j : ℝ) + (step j : ℝ) * (v j none : ℝ)) / S.value))
  have hpoint (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) (hx : kernel.weight x ≠ 0)
      (v : ∀ j : Input, IntegerScalarCubeBox Empty (H j)) (hv : active.weight v ≠ 0) :
      ‖F x v - Fideal x v‖ ≤ (Kφ : ℝ) * ξ := by
    have hid := allocatedOriginalSampleFullSliceMap_contained_physical B U basis S
      step H c (fun j => by have := hH j; omega) hsubset v hv sample (embed x) u
    dsimp only [F, Fideal]
    rw [hid, ← dist_eq_norm]
    apply le_trans ((hφ _ _).dist_le_mul _ _)
    rw [dist_prod_same_right]
    exact mul_le_mul_of_nonneg_left
      (allocatedContainedKernel_supported_narrow_physical_dist B U basis S
        HG (fun _ => stepG) cG (fun g => by have := hHG g; omega) hcontainedG x hx
        (joined v) hτ hξ box hbox integerFrame hframe) Kφ.coe_nonneg
  have hinner (x : ∀ g, IntegerScalarCubeBox Empty (HG g)) (hx : kernel.weight x ≠ 0) :
      ‖active.complexMean (F x) - active.complexMean (Fideal x)‖ ≤ (Kφ : ℝ) * ξ :=
    (active.norm_complexMean_sub_le (F x) (Fideal x) (fun _ => (Kφ : ℝ) * ξ)
      (fun v hv => hpoint x hx v hv)).trans_eq (active.mean_const _)
  have hchange := (kernel.norm_complexMean_sub_le
    (fun x => active.complexMean (F x)) (fun x => active.complexMean (Fideal x))
    (fun _ => (Kφ : ℝ) * ξ) hinner).trans_eq (kernel.mean_const _)
  change ‖kernel.complexMean (fun x => active.complexMean (F x)) - _‖ ≤ _
  have he := (norm_sub_le_norm_sub_add_norm_sub
    (kernel.complexMean (fun x => active.complexMean (F x)))
    (kernel.complexMean (fun x => active.complexMean (Fideal x))) _).trans (add_le_add hchange hmain)
  simpa only [add_comm ((Kφ : ℝ) * ξ)] using he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedPhysicalDensityCRTNeZero
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
variable {Cidx : Type*}
variable (selected : Cidx → Σ j : Fin m, Fin (n j))
variable (hshort : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U basis S.value) j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ}
variable (hV : gridVolume ≠ 0)
variable (test : (Cidx → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      ((Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) → ZMod q) → (((Σ _ : X, Unit ⊕ Empty) → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℂ)
variable {Kφ : ℝ≥0}
variable (htest : ∀ grid residue, LipschitzWith Kφ (test grid residue))
variable (hbound : ∀ grid residue y, ‖test grid residue y‖ ≤ 1)

local notation "actualDensity" => allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box
  integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c
local notation "sourceMean" => allocatedSlicedPhysicalSourceMean B U basis S HP stepP cP hinsideP hHP
  τ box integerFrame HG hHG cG stepG hcontainedG sample H c hH hsubset q selected base deck projection test
local notation "finiteReference" => allocatedSlicedPhysicalResidueMean B U basis S HP stepP cP hinsideP hHP
  integerFrame cG stepG sample c q selected base deck projection test actualDensity
local notation "rationalReference" => allocatedSlicedPhysicalRationalMean B U basis S primes exponent
  HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base deck projection
  hcoprime hqN (gridVolume := gridVolume) test actualDensity
local notation "comparisonError" => allocatedSlicedPhysicalComparisonError B U basis S ξ HG
  (t := t) H q (ε := ε) (η := η) (Kφ := Kφ)

omit [∀ j, Fintype (E j)] in
include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail htest hbound hτ hξ hbox hframe in
theorem allocatedSlicedPhysicalSourceMean_residue_comparison :
    ‖sourceMean - finiteReference‖ ≤ comparisonError := by
  classical
  unfold allocatedSlicedPhysicalSourceMean allocatedSlicedPhysicalResidueMean
  dsimp only
  apply ((allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP).norm_complexMean_sub_le
    _ _ (fun _ => comparisonError) ?_).trans_eq
      ((allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP).mean_const _)
  intro u _
  exact allocatedFixedPath_sliced_physical_density_residue_comparison B U basis hR hσ S u
    τ ξ hτ hξ box hbox integerFrame hframe HG hHG cG
    stepG hstepG hcontainedG e h0 h1 hB sample hs ht hσbound
    (fun _ => stepG) H c (fun _ => hstepG) hH hδ hsubset hdense q hsizeG hsmallG hsize hsmall
    hε hmesh hδone b hη A hA htail
    (fun uG uA => test
      (forecastInactiveShortGrid B U basis S selected (allocatedOriginalSampleInactiveCoefficients B selected sample) u)
      (allocatedJointResidueOutput B U basis S base integerFrame deck projection q uG
        (allocatedPrincipalResidueJoin B U basis S q u uA)))
    (fun rG rA => htest _ _) (fun rG rA y => hbound _ _ y)

include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail hshort hp hV htest hbound hτ hξ hbox hframe in
theorem allocatedFixedPath_sliced_physical_rational_density_comparison_s2_oai :
    ‖sourceMean - rationalReference‖ ≤ comparisonError := by
  rw [← allocatedSlicedPhysicalResidueMean_eq_rationalMean_s2 B U basis hR hσ S primes exponent
    HP stepP cP hinsideP hHP τ ξ box integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample hs
    H c q selected hshort xref base deck projection hp hcoprime hqN hV test]
  exact allocatedSlicedPhysicalSourceMean_residue_comparison B U basis hR hσ S
    HP stepP cP hinsideP hHP τ ξ hτ hξ box hbox integerFrame hframe HG hHG cG stepG hstepG
    hcontainedG e h0 h1 hB sample hs ht hσbound H c hH hδ hsubset hdense q hsizeG hsmallG
    hsize hsmall hε hmesh hδone b hη A hA htail selected base deck projection test htest hbound

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_physical_rational_density_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} := @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_physical_rational_density_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
