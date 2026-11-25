-- Prove2me | solution 1 for GlobalTheory.PDiv.cotBaseChange_hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:35:51.620803+00:00
-- url     : https://prove2.me/submissions/ee788b84-8930-4966-b659-1a086e28a5e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrimitiveSemilinearLiftBaseChangeBijective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange
import Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_succ
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_zero
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
import Theorems.Thm_GlobalTheory_PDivGroup_rigLevel_mk
import Theorems.Thm_GlobalTheory_PDiv_SemiBialgHom_levelRig_mk
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.SemiBialgHom.levelRig_mk
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT
attribute [local simp] GlobalTheory.PDivGroup.resOne_succ
attribute [local simp] GlobalTheory.PDivGroup.resOne_zero
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_id
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_mk
attribute [local simp] GlobalTheory.PDivGroup.rigLevel_mk



set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.PDiv
variable {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A]
  [Module.Projective R A] [IsCocomm R A] [CommRing R'] [Algebra R R']
namespace GlobalTheory.PDiv
theorem _root_.solution {N : Type} [AddCommGroup N] [Module R' N]
    {f g : Cot R' (CartierDual R' (R' ⊗[R] A)) →ₗ[R'] N}
    (h : ∀ φ : CartierDual R A, f (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) =
      g (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ)))) : f = g := by
  refine AugCot.hom_ext fun ψ => ?_
  obtain ⟨x, rfl⟩ := EquivLike.surjective (CartierDual.baseChange R R' A) ψ
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r φ =>
    have e : r ⊗ₜ[R] φ = r • ((1 : R') ⊗ₜ[R] φ) := by simp [smul_tmul']
    rw [e, map_smul, map_smul, map_smul, map_smul]
    exact congrArg (r • ·) (h φ)
end GlobalTheory.PDiv
