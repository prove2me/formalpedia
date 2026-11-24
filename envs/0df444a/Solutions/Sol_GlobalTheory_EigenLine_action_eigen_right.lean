-- Prove2me | solution 1 for GlobalTheory.EigenLine.action_eigen_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:25:08.265655+00:00
-- url     : https://prove2.me/submissions/95d06e89-1c8f-46b8-9695-1f6f4646d3d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LineHyperplaneCut
import Theorems.Thm_GlobalTheory_EigenLine_action_one_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.EigenLine
variable {K : Type} [Field K] {O : Type} [CommRing O] {L : Type} [AddCommGroup L] [Module K L]
namespace GlobalTheory.EigenLine
theorem _root_.solution (ρ : O →+* Module.End K L) (χ : O →+* K) (ε : K ⊗[ℤ] O)
    (hε : ∀ a, ε * ((1 : K) ⊗ₜ[ℤ] a) = χ a • ε) (a : O) (x : L) :
    tensorAction ρ ε (ρ a x) = χ a • tensorAction ρ ε x := by
  have h := congrArg (fun t => tensorAction ρ t x) (hε a)
  simpa only [map_mul, Module.End.mul_apply, action_one_tmul, map_smul,
    LinearMap.smul_apply] using h
end GlobalTheory.EigenLine
