-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:29.643822+00:00
-- url     : https://prove2.me/submissions/0d8fa01d-1938-42f1-ad86-9d5fa1c3395c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_deep_inv
import Theorems.Thm_GlobalTheory_IwahoriInj_elem_mem
import Theorems.Thm_GlobalTheory_IwahoriInj_mem_of_entry
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
    (h : ¬ Deep 1 (p.val j j)) : ∃ y : k, Deep (g i j) y ∧ ∃ b ∈ grp k hf.1, p = elem hij y * b := by
  obtain ⟨hu0, hu⟩ := deep_inv h
  have hy : Deep (g i j) (p.val i j * (p.val j j)⁻¹) := by simpa using (hp.1 i j).mul hu
  refine ⟨_, hy, (elem hij _)⁻¹ * p, mem_of_entry hg hf hij hfg
    (mul_mem (inv_mem (elem_mem hg hij hy)) hp) ?_, (mul_inv_cancel_left _ _).symm⟩
  have : ((elem hij (p.val i j * (p.val j j)⁻¹))⁻¹ * p).val i j = 0 := by
    show (transvection i j (-(p.val i j * (p.val j j)⁻¹)) * p.val) i j = 0
    rw [transvection_mul_apply_same]
    field_simp
    ring
  rw [this]
  exact deep_zero _
end GlobalTheory.IwahoriInj
