-- Prove2me | solution 1 for GlobalTheory.FiniteFlatKilled.comp_convPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:07:49.380442+00:00
-- url     : https://prove2.me/submissions/0133be4a-125f-4cb6-a3b6-5dd943e85ab7

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
variable [IsCocomm R B]
namespace GlobalTheory.FiniteFlatKilled
theorem _root_.solution (h : C →ₐ[R] F) (f : WithConv (B →ₐ[R] C)) (n : ℕ) :
    h.comp (f ^ n).ofConv = (toConv (h.comp f.ofConv) ^ n).ofConv := by
  induction n with
  | zero => ext c; simp
  | succ n ih => rw [pow_succ, pow_succ, AlgHom.comp_convMul_distrib, ih]
end GlobalTheory.FiniteFlatKilled
