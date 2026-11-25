-- Prove2me | solution 1 for GlobalTheory.T.exists_complex_embedding_scaling_of_ker_eval_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:14:54.295143+00:00
-- url     : https://prove2.me/submissions/9e1bdec3-f5c5-402c-a860-5e47e50c3934

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEmbeddingOfHomogeneousKerEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEmbeddingOfHomogeneousKerEqStatement
import Theorems.Thm_GlobalTheory_exists_embedding_of_homogeneous_ker_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (o K σ : Type) [CommRing o] [Field K] (β : o →+* K) (em : o →+* ℂ) (u : σ → K) (w : σ → ℂ) (a₀ : σ), u a₀ ≠ 0 → Subfield.closure (Set.range β ∪ Set.range (fun a => u a / u a₀)) = ⊤ → RingHom.ker (MvPolynomial.eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β) (fun a => Polynomial.C (u a) * Polynomial.X)) = RingHom.ker (MvPolynomial.eval₂Hom em w) → ∃ (e : K →+* ℂ) (c : ℂ), c ≠ 0 ∧ e.comp β = em ∧ ∀ a, e (u a) = c * w a := by
  first | exact @GlobalTheory.exists_embedding_of_homogeneous_ker_eq | exact GlobalTheory.exists_embedding_of_homogeneous_ker_eq | (intros; apply GlobalTheory.exists_embedding_of_homogeneous_ker_eq <;> assumption)
end _root_.GlobalTheory.T
