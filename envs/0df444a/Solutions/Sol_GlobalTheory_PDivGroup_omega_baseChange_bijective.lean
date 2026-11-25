-- Prove2me | solution 1 for GlobalTheory.PDivGroup.omega_baseChange_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:35:54.027844+00:00
-- url     : https://prove2.me/submissions/148c155b-94f8-4a06-99db-741f5e6c4f30

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmegaBaseChangeBijectiveOfPEqZero
import Theorems.Thm_GlobalTheory_PDiv_liftSemi_toBaseChange_cot_bijective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange
import Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_omegaLevel_one_bijective
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
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory
open GlobalTheory.PDivGroup
namespace GlobalTheory.PDivGroup
theorem _root_.solution {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (R' : Type)
    [CommRing R'] [Algebra R R'] (hp : (p : R) = 0) :
    Function.Bijective (liftSemi (G.toBase R').omega) := by
  have hp' : (p : R') = 0 := by rw [← map_natCast (algebraMap R R'), hp, map_zero]
  have hL := G.omegaLevel_one_bijective hp
  have hL' := (G.baseChange R').omegaLevel_one_bijective hp'
  have hg := liftSemi_toBaseChange_cot_bijective R R' (G.A 1)
  let e : R' ⊗[R] G.omega ≃ₗ[R'] R' ⊗[R] Cot R (G.A 1) :=
    LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofBijective (G.omegaLevel 1) hL)
  have key : ∀ x, (G.baseChange R').omegaLevel 1 (liftSemi (G.toBase R').omega x) =
      liftSemi (toBaseChange R R' (G.A 1)).cot (e x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul r w =>
      simp only [liftSemi_tmul, map_smul, e, LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
      congr 1
  have hcomp : ⇑((G.baseChange R').omegaLevel 1) ∘ ⇑(liftSemi (G.toBase R').omega) =
      ⇑(liftSemi (toBaseChange R R' (G.A 1)).cot) ∘ ⇑e := funext key
  exact (Function.Bijective.of_comp_iff' hL' _).1 (hcomp ▸ hg.comp e.bijective)
end GlobalTheory.PDivGroup
