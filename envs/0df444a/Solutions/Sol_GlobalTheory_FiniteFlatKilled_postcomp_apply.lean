-- Prove2me | solution 1 for GlobalTheory.FiniteFlatKilled.postcomp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:13.804093+00:00
-- url     : https://prove2.me/submissions/b771448e-46ad-477b-93f0-b2176ed85e78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIdPowEqOneOfIsFiniteOfFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FiniteFlatKilled
open TensorProduct WithConv Coalgebra
variable {R B C F : Type*} [CommRing R] [CommRing C] [CommRing F] [Algebra R C] [Algebra R F]
variable [AddCommGroup B] [Module R B] [Coalgebra R B] [IsCocomm R B]
namespace GlobalTheory.FiniteFlatKilled
theorem _root_.solution (h : C →ₐ[R] F) (f : WithConv (B →ₗ[R] C)) (c : B) :
    postcomp B h f c = h (f c) := rfl
end GlobalTheory.FiniteFlatKilled
