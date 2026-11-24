-- Prove2me | solution 1 for GlobalTheory.Klein.exists_hasDerivAt_intFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:07:24.937351+00:00
-- url     : https://prove2.me/submissions/f8660aa3-bc9e-41c6-a0c2-3efed1f88542

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormIteratedDerivWeierstrassPLeOne
import Theorems.Thm_GlobalTheory_Klein_mem_intAt
import Theorems.Thm_GlobalTheory_Klein_half_mem_intAt
import Theorems.Thm_GlobalTheory_Klein_const_mem_intFun
import Theorems.Thm_GlobalTheory_Klein_x_mem_intFun
import Theorems.Thm_GlobalTheory_Klein_y_mem_intFun
import Theorems.Thm_GlobalTheory_hasDerivAt_derivWeierstrassP
import Theorems.Thm_GlobalTheory_hasDerivAt_weierstrassP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Klein
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.Klein
theorem _root_.solution {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r : ℂ} (hg : Good ι L r)
    {f : ℂ → ℂ} (hf : f ∈ intFun ι L r) :
    ∃ g ∈ intFun ι L r, ∀ w ∉ L.lattice, HasDerivAt f (g w) w := by
  induction hf using Subring.closure_induction with
  | mem f hf =>
    rcases hf with (rfl | rfl) | ⟨c, hc, rfl⟩
    · exact ⟨_, y_mem_intFun ι L r, fun w hw => (GlobalTheory.hasDerivAt_weierstrassP L hw).sub_const r⟩
    · obtain ⟨hp, h1, h2, -, -⟩ := hg
      rw [← mem_intAt] at h1 h2
      have hx := x_mem_intFun ι L r
      refine ⟨_, add_mem (add_mem (mul_mem (const_mem_intFun ι L r (natCast_mem _ 6)) (mul_mem hx hx))
        (mul_mem (const_mem_intFun ι L r h1) hx))
        (const_mem_intFun ι L r (mul_mem h2 (half_mem_intAt ι hp))), fun w hw => ?_⟩
      convert GlobalTheory.hasDerivAt_derivWeierstrassP L hw using 1
      simp only [Pi.add_apply, Pi.mul_apply]
      push_cast; ring
    · exact ⟨0, zero_mem _, fun w _ => hasDerivAt_const w c⟩
  | zero => exact ⟨0, zero_mem _, fun w _ => hasDerivAt_const w 0⟩
  | one => exact ⟨0, zero_mem _, fun w _ => hasDerivAt_const w 1⟩
  | add f f' _ _ h h' =>
    obtain ⟨g, hg1, hg2⟩ := h
    obtain ⟨g', hg1', hg2'⟩ := h'
    exact ⟨g + g', add_mem hg1 hg1', fun w hw => (hg2 w hw).add (hg2' w hw)⟩
  | neg f _ h =>
    obtain ⟨g, hg1, hg2⟩ := h
    exact ⟨-g, neg_mem hg1, fun w hw => (hg2 w hw).neg⟩
  | mul f f' hf hf' h h' =>
    obtain ⟨g, hg1, hg2⟩ := h
    obtain ⟨g', hg1', hg2'⟩ := h'
    exact ⟨g * f' + f * g', add_mem (mul_mem hg1 hf') (mul_mem hf hg1'),
      fun w hw => (hg2 w hw).mul (hg2' w hw)⟩
end GlobalTheory.Klein
