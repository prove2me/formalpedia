-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.exists_unit_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:47:07.4099+00:00
-- url     : https://prove2.me/submissions/891550c3-978b-444e-a3ce-2d7cbce81497

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mono
import Theorems.Thm_GlobalTheory_RootEx_Supp_exists_bd_of_isCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {S : Set (GL ι k)} (hS : S.Finite) :
    ∃ s : kˣ, ∀ g ∈ S, Bd (valuation k (s : k)) g.val ∧ Bd (valuation k (s : k)) (g⁻¹).val := by
  obtain ⟨γ, hγ⟩ := exists_bd_of_isCompact
    ((hS.image fun g => g.val).union (hS.image fun g => (g⁻¹).val)).isCompact
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (max 1 γ)
  have h0 : t ≠ 0 := by
    rintro rfl
    have : (1 : ValueGroupWithZero k) ≤ 0 := by simpa using (le_max_left 1 γ).trans ht.ge
    simp at this
  have h1 : γ ≤ valuation k t := ht ▸ le_max_right _ _
  exact ⟨Units.mk0 t h0, fun g hg => ⟨(hγ _ (Or.inl ⟨g, hg, rfl⟩)).mono h1, (hγ _ (Or.inr ⟨g, hg, rfl⟩)).mono h1⟩⟩
end GlobalTheory.FunObj.FiniteSupport
