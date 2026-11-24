-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormBaseChange.normsEscape_of_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:16:07.549304+00:00
-- url     : https://prove2.me/submissions/268bf1d0-78bf-4aca-a898-7d4325db787f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndexTwoOfFiniteReal
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_NormsEscape_trans
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_normsEscape_of_odd
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_normsEscape_of_two
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_even_or_odd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormBaseChange
open NormIndex
variable {A : Type} [Field A] [CharZero A]
  (hA : ∀ (B : Type) [Field B] [Algebra A B] [FiniteDimensional A B], IndexTwo B)
include hA
namespace GlobalTheory.QuadSymbol.NormBaseChange
theorem _root_.solution (M : Type) [Field M] [Algebra A M] [FiniteDimensional A M]
    [IsGalois A M] : ∀ (m : ℕ) (K : IntermediateField A M) (n : ℕ), Module.finrank A K = m →
      Module.finrank K M = 2 ^ n → NormsEscape A K := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro K n hm hn
    rcases Nat.even_or_odd (Module.finrank A K) with hev | hodd
    swap
    · exact normsEscape_of_odd (hA A) hodd
    have hdvd : 2 ^ (n + 1) ∣ Nat.card (M ≃ₐ[A] M) := by
      rw [IsGalois.card_aut_eq_finrank, ← Module.finrank_mul_finrank A K M, hn, pow_succ']
      exact Nat.mul_dvd_mul_right hev.two_dvd _
    obtain ⟨H, hH, hle⟩ := Sylow.exists_subgroup_card_pow_succ (H := K.fixingSubgroup) hdvd
      (by rw [IsGalois.card_fixingSubgroup_eq_finrank, hn])
    let K' := IntermediateField.fixedField H
    have hK' : K' ≤ K := by
      rw [← IsGalois.fixedField_fixingSubgroup K]
      exact IntermediateField.fixedField_le hle
    have hn' : Module.finrank K' M = 2 ^ (n + 1) := by
      rw [IntermediateField.finrank_fixedField_eq_card, hH]
    letI : Algebra K' K := (IntermediateField.inclusion hK').toRingHom.toAlgebra
    haveI : IsScalarTower A K' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower K' K M := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : FiniteDimensional K' K := Module.Finite.of_restrictScalars_finite A K' K
    have h2 : Module.finrank K' K = 2 := by
      have := Module.finrank_mul_finrank K' K M
      rw [hn, hn', pow_succ'] at this
      exact Nat.eq_of_mul_eq_mul_right (by positivity) this
    have hlt : Module.finrank A K' < m := by
      have := Module.finrank_mul_finrank A K' K
      have hpos : 0 < Module.finrank A K' := Module.finrank_pos
      rw [h2, hm] at this
      omega
    haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap A K').injective
    exact NormsEscape.trans (hA K') (ih _ hlt K' _ rfl hn') (normsEscape_of_two (hA K') h2)
end GlobalTheory.QuadSymbol.NormBaseChange
