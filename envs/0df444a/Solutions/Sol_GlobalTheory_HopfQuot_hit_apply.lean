-- Prove2me | solution 1 for GlobalTheory.HopfQuot.hit_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:58.232333+00:00
-- url     : https://prove2.me/submissions/c4a1bd97-924c-48ca-b093-bcf9b8b7bf0a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ ι : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Fintype ι]
namespace GlobalTheory.HopfQuot
theorem _root_.solution (f : Λ →ₗ[R] R) (y : Λ) : hit f y = ev Λ f (Coalgebra.comul y) := rfl
end GlobalTheory.HopfQuot
