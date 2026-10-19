-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_bounds_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:37:11.059278+00:00
-- url     : https://prove2.me/submissions/a3d134ae-b732-4751-b762-0fe3123aba82

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B245
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_fixedSpatialKernelSliceOriginalForecastDensity_bounds_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialSlicedDensityBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

theorem density_bounds_s2_oai
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val)) (hδslice : 0 < δslice) :
    (∀ y, ‖slice.density hBactive y‖ ≤
      (fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) hδslice : ℝ)) ∧
    LipschitzWith (fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
      (slice.slicedBlockEquiv true) hδslice) (slice.density hBactive) := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  have h := fixedSpatialKernelSliceOriginalForecastDensity_bounds_s2 B U b hR hσ S
    spatialEquiv Wsp Lsp slice.path.normalizedNoise slice.kernelLower slice.kernelWidth
    slice.path.detFalse slice.path.detTrue slice.kernelWidth_ne_zero hBactive
    slice.path.lower slice.path.width hδslice slice.path.hwidth slice.path.hlower
    slice.path.sample slice.path.hs
  refine ⟨?_, h.2⟩
  intro y
  change ‖fixedSpatialKernelSliceOriginalForecastDensity B U b S
    spatialEquiv Wsp Lsp slice.path.normalizedNoise slice.kernelLower slice.kernelWidth
    slice.path.detFalse slice.path.detTrue slice.kernelWidth_ne_zero hBactive
    slice.path.lower slice.path.width slice.path.sample y‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (h.1 y).1]
  exact (h.1 y).2

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_bounds_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_bounds_s2_oai
