-- Prove2me | solution 1 for GlobalTheory.LGrp.bcParam_consParam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:35:04.533807+00:00
-- url     : https://prove2.me/submissions/06b9056d-0d7b-4917-b5ba-b70fd2f4740c

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
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
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
variable {n : ℕ}
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)
omit σ hσ hc
namespace GlobalTheory.LGrp
theorem _root_.solution (z : ℂˣ) (α : Fin (n / 2) → ℂˣ) :
    bcParam (n + 2) (consParam z α) = bcParam n α + {z, z⁻¹} := by
  have key : ∀ f : ℂˣ → ℂˣ, Finset.univ.val.map (fun i => f (consParam z α i)) =
      f z ::ₘ Finset.univ.val.map fun i => f (α i) := fun f => by
    have h := congrArg (Multiset.map fun i => f ((Fin.cons z α : Fin (n / 2 + 1) → ℂˣ) i))
      (congrArg Finset.val (Finset.map_univ_equiv (finCongr (Nat.add_div_right n two_pos))))
    rw [Finset.map_val, Multiset.map_map, Fin.univ_succ] at h
    refine h.trans ?_
    simp [Function.comp_def]
  have h1 := key id
  have h2 := key (·⁻¹)
  simp only [id] at h1
  unfold bcParam
  rw [h1, h2, Nat.add_mod_right]
  simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
  abel
end GlobalTheory.LGrp
