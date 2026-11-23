-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.mem_of_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:22.266188+00:00
-- url     : https://prove2.me/submissions/758cf5d7-635c-4a3d-aa42-313662016ee9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_Deep_neg
import Theorems.Thm_GlobalTheory_IwahoriInj_deep_inv
import Theorems.Thm_GlobalTheory_IwahoriInj_diag_unit
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable {g f f' : n → n → ℤ} {i j : n}
namespace GlobalTheory.IwahoriInj
theorem _root_.solution (hg : Conc g) (hf : Chamber f) (hij : i ≠ j)
    (hfg : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b) {p : GL n k} (hp : p ∈ grp k hg)
    (h : Deep (f i j) (p.val i j)) : p ∈ grp k hf.1 := by
  have h1 : ∀ a b, Deep (f a b) (p.val a b) := fun a b => by
    by_cases c : a = i ∧ b = j
    · rw [c.1, c.2]; exact h
    · rw [hfg a b c]; exact hp.1 a b
  have h2 : ∀ a b, ¬ (a = i ∧ b = j) → Deep (f a b) ((p⁻¹).val a b) := fun a b c => by
    rw [hfg a b c]; exact hp.2 a b
  refine ⟨h1, fun a b => ?_⟩
  by_cases c : a = i ∧ b = j
  swap
  · exact h2 a b c
  rw [c.1, c.2]
  obtain ⟨hu0, hu⟩ := deep_inv (diag_unit hf (h1 i) fun l => h2 l i (by grind))
  have h3 : (p.val * (p⁻¹).val) i j = 0 := by simp [one_apply_ne hij]
  rw [mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_eq_zero_iff_eq_neg] at h3
  have h4 : Deep (f i j) (p.val i i * (p⁻¹).val i j) := by
    rw [h3]
    exact (Deep.sum fun l hl => ((h1 i l).mul (h2 l j (by grind))).mono (hf.1.2 i j l)).neg
  simpa only [zero_add, inv_mul_cancel_left₀ hu0] using hu.mul h4
end GlobalTheory.IwahoriInj
