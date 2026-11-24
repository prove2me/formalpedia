-- Prove2me | solution 1 for GlobalTheory.FiniteFlatKilled.mul_comp_antipode
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:07:59.976836+00:00
-- url     : https://prove2.me/submissions/843dad50-1d12-46ea-a1a2-aba6e2276b44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIdPowEqOneOfIsFiniteOfFlat
import Theorems.Thm_GlobalTheory_FiniteFlatKilled_postcomp_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FiniteFlatKilled.postcomp_apply

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FiniteFlatKilled
open TensorProduct WithConv Coalgebra
variable {R B C F : Type*} [CommRing R] [CommRing C] [CommRing F] [Algebra R C] [Algebra R F]
variable [CommRing B] [HopfAlgebra R B]
namespace GlobalTheory.FiniteFlatKilled
theorem _root_.solution (u : B →ₐ[R] C) :
    toConv u * toConv (u.comp (HopfAlgebra.antipodeAlgHom R B)) = 1 := by
  have h : toConv (AlgHom.id R B) * toConv (HopfAlgebra.antipodeAlgHom R B) = 1 :=
    mul_inv_cancel (toConv (AlgHom.id R B))
  have h2 := AlgHom.comp_convMul_distrib u (toConv (AlgHom.id R B))
    (toConv (HopfAlgebra.antipodeAlgHom R B))
  rw [h] at h2
  apply ofConv_injective
  refine h2.symm.trans ?_
  ext c
  simp
end GlobalTheory.FiniteFlatKilled
