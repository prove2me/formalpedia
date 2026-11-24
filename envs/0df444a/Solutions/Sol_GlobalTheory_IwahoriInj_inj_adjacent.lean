-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.inj_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:12:48.058413+00:00
-- url     : https://prove2.me/submissions/cffa29e2-1f61-46d2-b534-645dc52c2082

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_inj_of_rank_one
import Theorems.Thm_GlobalTheory_IwahoriInj_Deep_neg
import Theorems.Thm_GlobalTheory_IwahoriInj_exists_deep
import Theorems.Thm_GlobalTheory_IwahoriInj_grp_mono
import Theorems.Thm_GlobalTheory_IwahoriInj_isCompact_grp
import Theorems.Thm_GlobalTheory_IwahoriInj_elem_mem
import Theorems.Thm_GlobalTheory_IwahoriInj_mem_of_entry
import Theorems.Thm_GlobalTheory_IwahoriInj_exists_factor
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
variable {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL n k) V}
namespace GlobalTheory.IwahoriInj
theorem _root_.solution (hπ : IsSmooth π) (hg : Conc g) (hf : Chamber f) (hf' : Chamber f') (hij : i ≠ j)
    (h1 : f i j = g i j + 1) (h2 : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b)
    (h3 : f' j i = g j i + 1) (h4 : ∀ a b, ¬ (a = j ∧ b = i) → f' a b = g a b) :
    Inj π (grp k hf.1) (grp k hf'.1) := by
  have hle : grp k hf'.1 ≤ grp k hg := grp_mono _ _ fun a b => by
    by_cases c : a = j ∧ b = i
    · rw [c.1, c.2]; omega
    · exact (h4 a b c).ge
  have h5 := h2 j i (by grind)
  have h6 := hf.2 i j hij
  have h7 := h4 i j (by grind)
  obtain ⟨c, hc0, hc, hc'⟩ := exists_deep (k := k) (g i j)
  let s : GL n k := elem hij.symm c⁻¹ * elem hij (-c)
  have hs : s ∈ grp k hg :=
    mul_mem (elem_mem hg _ (hc'.mono (by omega))) (elem_mem hg _ hc.neg)
  have hl : ∀ (p : GL n k) (b : n), (s⁻¹ * p).val i b = c * p.val j b := fun p b => by
    rw [_root_.mul_inv_rev, mul_assoc]
    show (transvection i j (-(-c)) * (transvection j i (-c⁻¹) * p.val)) i b = _
    rw [transvection_mul_apply_same, transvection_mul_apply_same, transvection_mul_apply_of_ne _ _ _ _ hij]
    field_simp
    ring
  have hr : ∀ (p : GL n k) (a : n), (p * s).val a j = -c * p.val a i := fun p a => by
    rw [← mul_assoc]
    show (p.val * transvection j i c⁻¹ * transvection i j (-c)) a j = _
    rw [mul_transvection_apply_same, mul_transvection_apply_same,
      mul_transvection_apply_of_ne _ _ _ _ hij.symm]
    field_simp
    ring
  refine inj_of_rank_one hπ (isCompact_grp _) (isCompact_grp hg) hle hs (fun x hx => ?_) fun p hp => ?_
  · refine mem_of_entry hg hf hij h2 (mul_mem (mul_mem (inv_mem hs) (hle hx)) hs) ?_
    rw [mul_assoc, hl, hr]
    exact (hc.mul (hc.neg.mul (hx.1 j i))).mono (by omega)
  · by_cases hu : Deep 1 (p.val j j)
    · refine Or.inr (mem_of_entry hg hf hij h2 (mul_mem (inv_mem hs) hp) ?_)
      rw [hl]
      exact (hc.mul hu).mono (by omega)
    · obtain ⟨y, hy, b, hb, e⟩ := exists_factor hg hf hij h2 hp hu
      exact Or.inl ⟨_, elem_mem hf'.1 hij (by rwa [h7]), b, hb, e⟩
end GlobalTheory.IwahoriInj
