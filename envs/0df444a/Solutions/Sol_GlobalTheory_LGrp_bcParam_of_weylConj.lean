-- Prove2me | solution 1 for GlobalTheory.LGrp.bcParam_of_weylConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:00:10.818352+00:00
-- url     : https://prove2.me/submissions/52df5864-aeb0-4260-927f-5fc2f6cd9e14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
open Formalism.UG
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {α : Type} [LinearOrder α]
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
namespace GlobalTheory.LGrp
theorem _root_.solution {n : ℕ} {α β : Fin (n / 2) → ℂˣ} (h : WeylConjU α β) : bcParam n α = bcParam n β := by
  obtain ⟨w, hw⟩ := h
  have key : ∀ γ : Fin (n / 2) → ℂˣ, Finset.univ.val.map γ + Finset.univ.val.map (fun i => (γ i)⁻¹) =
      ∑ i, ({γ i, (γ i)⁻¹} : Multiset ℂˣ) := by
    intro γ
    have : ∀ f : Fin (n / 2) → ℂˣ, ∑ i, ({f i} : Multiset ℂˣ) = Finset.univ.val.map f := fun f => by
      rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (Finset.univ.val.map f), Multiset.map_map]; rfl
    simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add, Finset.sum_add_distrib, this]
  unfold bcParam
  rw [key, key, ← Equiv.sum_comp w]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hw i with e | e
  · rw [e]
  · rw [e, inv_inv, Multiset.pair_comm]
end GlobalTheory.LGrp
