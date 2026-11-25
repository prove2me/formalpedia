-- Prove2me | solution 1 for GlobalTheory.PDivGroup.ker_resOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:16.668802+00:00
-- url     : https://prove2.me/submissions/f70434d5-fc04-44ea-bc46-b91e4606b591

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupMulPUnitFibreEqLevelOne
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_succ
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_zero
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
import Theorems.Thm_GlobalTheory_PDivGroup_rigLevel_mk
import Theorems.Thm_GlobalTheory_PDiv_SemiBialgHom_levelRig_mk
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_map_torsionIdeal
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
import Theorems.Thm_GlobalTheory_PDiv_torsionIdeal_le_ker_iff
import Theorems.Thm_GlobalTheory_PDiv_torsionIdeal_le_of_dvd
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
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv
open GlobalTheory
open GlobalTheory.PDivGroup
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
open scoped TensorProduct
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R)
namespace GlobalTheory.PDivGroup
namespace _root_.GlobalTheory.PDivGroup
theorem _root_.solution (n : ℕ) :
    RingHom.ker (G.resOne n :
      G.A (n + 1) →ₐ[R] G.A 1) =
      _root_.GlobalTheory.PDiv.torsionIdeal R (G.A (n + 1)) p := by
  induction n with
  | zero =>
    have hid : (G.resOne 0 :
        G.A 1 →ₐ[R] G.A 1) = AlgHom.id R _ := by
      ext a; exact G.resOne_zero a
    rw [hid]
    refine le_antisymm ?_ ?_
    · intro a ha
      have : a = 0 := ha
      simp [this]
    · refine (_root_.GlobalTheory.PDiv.torsionIdeal_le_ker_iff p
        (AlgHom.id R (G.A (0 + 1)))).2 ?_
      simpa using G.pts_pow_self 1 (WithConv.toConv (AlgHom.id R (G.A 1)))
  | succ n ih =>
    have hcomp : (G.resOne (n + 1) :
        G.A (n + 2) →ₐ[R] G.A 1) =
        (G.resOne n :
          G.A (n + 1) →ₐ[R] G.A 1).comp
          (G.res (n + 1) :
            G.A (n + 2) →ₐ[R] G.A (n + 1)) := by
      ext a; exact G.resOne_succ n a
    have hsurj : Function.Surjective (G.res (n + 1) :
        G.A (n + 2) →ₐ[R] G.A (n + 1)) :=
      G.res_surjective (n + 1)
    have hker : RingHom.ker ((G.resOne n :
        G.A (n + 1) →ₐ[R] G.A 1).comp
          (G.res (n + 1) :
            G.A (n + 2) →ₐ[R] G.A (n + 1))) =
        Ideal.comap (G.res (n + 1) :
          G.A (n + 2) →ₐ[R] G.A (n + 1))
          (RingHom.ker (G.resOne n :
            G.A (n + 1) →ₐ[R] G.A 1)) := by
      ext a; exact Iff.rfl
    rw [hcomp, hker, ih, ← _root_.GlobalTheory.PDiv.map_torsionIdeal
      (G.res_surjective (n + 1)) p]
    erw [Ideal.comap_map_of_surjective _ hsurj]
    refine sup_eq_left.mpr ?_
    have h0 : Ideal.comap (G.res (n + 1) :
        G.A (n + 2) →ₐ[R] G.A (n + 1)) ⊥ =
        _root_.GlobalTheory.PDiv.torsionIdeal R (G.A (n + 2)) (p ^ (n + 1)) := by
      rw [← G.ker_res (n + 1)]
      ext a; exact Iff.rfl
    rw [h0]
    exact _root_.GlobalTheory.PDiv.torsionIdeal_le_of_dvd (dvd_pow_self p (Nat.succ_ne_zero n))
end _root_.GlobalTheory.PDivGroup
end GlobalTheory.PDivGroup
