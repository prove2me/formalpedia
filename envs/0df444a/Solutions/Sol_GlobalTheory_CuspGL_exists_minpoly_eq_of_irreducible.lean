-- Prove2me | solution 1 for GlobalTheory.CuspGL.exists_minpoly_eq_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:03:59.185796+00:00
-- url     : https://prove2.me/submissions/72437820-42fb-41bd-99cd-55111fa2f0fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumMobiusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumEqTorusSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveEndClassFunctionZeroOfCharpolyMassZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfFinsumMulStarPowEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimitiveClassFunctionExpansionRootSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F] (f : F[X]) (hm : f.Monic)
    (hf : Irreducible f) (h0 : f.coeff 0 ≠ 0) (m : ℕ) :
    ∃ α : AlgebraicClosure F, α ^ (Nat.card F ^ (f.natDegree * m) - 1) = 1 ∧ minpoly F α = f := by
  obtain ⟨α, hα⟩ : ∃ α : AlgebraicClosure F, aeval α f = 0 :=
    IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure F) f (degree_pos_of_irreducible hf).ne'
  have hmin : minpoly F α = f := (minpoly.eq_of_irreducible_of_monic hf hα hm).symm
  refine ⟨α, ?_, hmin⟩
  have hα0 : α ≠ 0 := by
    rintro rfl
    apply h0
    have h := coeff_zero_eq_aeval_zero' (R := F) (A := AlgebraicClosure F) f
    rw [hα] at h
    exact (algebraMap F (AlgebraicClosure F)).injective (by rw [h, map_zero])
  have hint : IsIntegral F α := ⟨f, hm, by rwa [← aeval_def]⟩
  have : FiniteDimensional F (IntermediateField.adjoin F ({α} : Set (AlgebraicClosure F))) := IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin F ({α} : Set (AlgebraicClosure F))) := Module.finite_of_finite F
  let _ : Fintype (IntermediateField.adjoin F ({α} : Set (AlgebraicClosure F))) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin F ({α} : Set (AlgebraicClosure F))) = Nat.card F ^ f.natDegree := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := F),
      IntermediateField.adjoin.finrank hint, hmin]
  have hβ : (⟨α, IntermediateField.mem_adjoin_simple_self F α⟩ : (IntermediateField.adjoin F ({α} : Set (AlgebraicClosure F)))) ≠ 0 := by
    intro h; apply hα0; exact congrArg Subtype.val h
  have h1 := FiniteField.pow_card_sub_one_eq_one _ hβ
  rw [hcard] at h1
  have h2 : α ^ (Nat.card F ^ f.natDegree - 1) = 1 := by
    have := congrArg Subtype.val h1
    simpa using this
  obtain ⟨r, hr⟩ : Nat.card F ^ f.natDegree - 1 ∣ Nat.card F ^ (f.natDegree * m) - 1 := by
    exact Nat.pow_sub_one_dvd_pow_sub_one (Nat.card F) (dvd_mul_right _ _)
  rw [hr, pow_mul, h2, one_pow]
end GlobalTheory.CuspGL
