-- Prove2me | solution 1 for GlobalTheory.FiniteModuleOrder.exists_card_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:15:15.409922+00:00
-- url     : https://prove2.me/submissions/39d50598-2c2d-4e86-8beb-d2762371ea6f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FiniteModuleOrder
namespace GlobalTheory.FiniteModuleOrder
theorem _root_.solution (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) :
    ∀ (D : Type) [AddCommGroup D] [Module R D] [Finite D], Nat.card D = n →
      ∃ i : ℕ, Nat.card D = Nat.card (R ⧸ IsLocalRing.maximalIdeal R) ^ i := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D _ _ _ hn
    rcases subsingleton_or_nontrivial D with h | h
    · exact ⟨0, by simp⟩
    have hfin : Finite (Submodule R D) := Finite.of_injective _ SetLike.coe_injective
    obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R D)).resolve_left bot_ne_top
    have hs : IsSimpleModule R (D ⧸ M) := isSimpleModule_iff_isCoatom.2 hM
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
    have hI' : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
    subst hI'
    have hc := Submodule.card_eq_card_quotient_mul_card M
    have hnt : Nontrivial (D ⧸ M) := IsSimpleModule.nontrivial R _
    have hf : Finite (D ⧸ M) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective M)
    have h2 : 1 < Nat.card (D ⧸ M) := Finite.one_lt_card
    have hpos : 0 < Nat.card M := Nat.card_pos
    obtain ⟨i, hi⟩ := ih (Nat.card M) (by rw [← hn, hc]; nlinarith) M rfl
    exact ⟨i + 1, by rw [hc, hi, Nat.card_congr e.toEquiv, pow_succ]⟩
end GlobalTheory.FiniteModuleOrder
