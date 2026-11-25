-- Prove2me | solution 1 for GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:55:43.206854+00:00
-- url     : https://prove2.me/submissions/8776f3f9-aa7a-4040-a712-9dd42eac4955

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Theorems.Thm_GlobalTheory_FiniteModuleOrder_exists_card_eq_pow
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FiniteModuleOrder
namespace GlobalTheory.FiniteModuleOrder
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D], (∃ i : ℕ, Nat.card D = resQ ϖ ^ i) ∧ ∀ I : Submodule L.O D, I ≠ ⊤ → resQ ϖ * Nat.card I ≤ Nat.card D := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a =>
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  have key : ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D],
      ∃ i : ℕ, Nat.card D = resQ ϖ ^ i := by
    intro D _ _ _
    let : Module 𝒪[F] D := Module.compHom D i
    rw [resQ, ← hϖ.maximalIdeal_eq]
    exact exists_card_eq_pow 𝒪[F] _ D rfl
  intro D _ _ _
  refine ⟨key D, fun I hI => ?_⟩
  have hnt : Nontrivial (D ⧸ I) := Submodule.Quotient.nontrivial_iff.2 hI
  have hf : Finite (D ⧸ I) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective I)
  have h2 : 1 < Nat.card (D ⧸ I) := Finite.one_lt_card
  obtain ⟨j, hj⟩ := key (D ⧸ I)
  have hj0 : j ≠ 0 := by rintro rfl; rw [pow_zero] at hj; omega
  rw [Submodule.card_eq_card_quotient_mul_card I, hj, mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.le_self_pow hj0 _)
end GlobalTheory.FiniteModuleOrder
