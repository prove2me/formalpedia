-- Prove2me | solution 1 for GlobalTheory.CuspGL.mass_card_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:41:02.33284+00:00
-- url     : https://prove2.me/submissions/b357390e-4b7e-4c4b-868d-ce8e7c9c292e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassOfCharpolyCardCyclicVectors
import Theorems.Thm_GlobalTheory_CuspGL_CyclicMass_card_pairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F] (D : F[X]) (hD : D.Monic) :
    mass (fun g : Module.End F (Fin D.natDegree → F) =>
      (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F),
        (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D = glCard F D.natDegree := by
  classical
  haveI : FiniteDimensional F (AdjoinRoot D) := (AdjoinRoot.powerBasis' hD).finite
  have hA : Module.finrank F (AdjoinRoot D) = D.natDegree := (AdjoinRoot.powerBasis' hD).finrank
  have h := CyclicMass.card_pairs (V := Fin D.natDegree → F) D hD (by simp)
  haveI : Finite (Module.End F (Fin D.natDegree → F)) :=
    Finite.of_injective _ DFunLike.coe_injective
  haveI := Fintype.ofFinite {g : Module.End F (Fin D.natDegree → F) // LinearMap.charpoly g = D}
  rw [Nat.card_sigma] at h
  let e0 : AdjoinRoot D ≃ₗ[F] (Fin D.natDegree → F) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hA])
  have h2 : Nat.card (AdjoinRoot D ≃ₗ[F] (Fin D.natDegree → F)) = Nat.card (GL (Fin D.natDegree) F) := by
    refine Nat.card_congr (Equiv.trans ?_ (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F _)).toEquiv.symm)
    exact ⟨fun e => e0.symm.trans e, fun e => e0.trans e, fun e => by ext; simp, fun e => by ext; simp⟩
  rw [glCard, ← h2, h, mass, ← finsum_set_coe_eq_finsum_mem, Nat.cast_sum]
  exact finsum_eq_sum_of_fintype (α := {g : Module.End F (Fin D.natDegree → F) // LinearMap.charpoly g = D}) _
end GlobalTheory.CuspGL
