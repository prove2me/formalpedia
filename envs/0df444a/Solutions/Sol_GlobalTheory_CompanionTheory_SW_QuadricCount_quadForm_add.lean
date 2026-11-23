-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadricCount.quadForm_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:02.554337+00:00
-- url     : https://prove2.me/submissions/7a936d42-a71a-4d18-8e71-04d369b9e52b

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricCount
open ComplexConjugate
variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.QuadricCount
theorem _root_.solution (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k} (hB : B.IsSymm) (y z : ι → k) :
    quadForm B (y + z) = quadForm B y + quadForm B z + y ⬝ᵥ (B *ᵥ z) := by
  have hs : z ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq, dotProduct_comm]
  unfold quadForm
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hs]
  field_simp
  ring
end GlobalTheory.CompanionTheory.SW.QuadricCount
