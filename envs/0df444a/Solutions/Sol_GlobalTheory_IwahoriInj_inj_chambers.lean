-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.inj_chambers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:33:43.937801+00:00
-- url     : https://prove2.me/submissions/eb4949a1-78c4-4f91-842b-0d55a018db02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_eq_zero_of_fixed
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_IwahoriInj_exists_wall
import Theorems.Thm_GlobalTheory_IwahoriInj_exists_flip
import Theorems.Thm_GlobalTheory_IwahoriInj_grp_mono
import Theorems.Thm_GlobalTheory_IwahoriInj_isCompact_grp
import Theorems.Thm_GlobalTheory_IwahoriInj_elem_mem
import Theorems.Thm_GlobalTheory_IwahoriInj_diag_unit
import Theorems.Thm_GlobalTheory_IwahoriInj_exists_factor
import Theorems.Thm_GlobalTheory_IwahoriInj_inj_adjacent
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_UpperTheory_Reformulated_B_TwistedKernelFixed_eq_zero_of_fixed


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
theorem _root_.solution (hπ : IsSmooth π) {f F : n → n → ℤ} (hf : Chamber f) (hF : Chamber F) :
    Inj π (grp k hf.1) (grp k hF.1) := by
  generalize hd : ∑ p : n × n, (f p.1 p.2 - F p.1 p.2).toNat = d
  induction d using Nat.strong_induction_on generalizing f with
  | _ d ih =>
  by_cases hne : f = F
  · subst hne
    exact fun v hv hv' => eq_zero_of_fixed hπ (isCompact_grp _) hv hv'
  obtain ⟨i, j, hij, hlt, hw⟩ := exists_wall hf hF hne
  obtain ⟨g, f', hg, hf', h1, h2, h3, h4⟩ := exists_flip hf hij hw
  have h5 := h2 j i (by grind)
  have h6 := hf.2 i j hij
  have h7 := h4 i j (by grind)
  have h8 := hF.2 i j hij
  refine (inj_adjacent hπ hg hf hf' hij h1 h2 h3 h4).trans hπ (isCompact_grp _) (fun x hx => ?_)
    (ih _ ?_ hf' rfl)
  · have hle : grp k hf'.1 ≤ grp k hg := grp_mono _ _ fun a b => by
      by_cases c : a = j ∧ b = i
      · rw [c.1, c.2]; omega
      · exact (h4 a b c).ge
    obtain ⟨y, hy, b, hb, e⟩ := exists_factor hg hf hij h2 (hle hx)
      (diag_unit hf' (hx.1 j) fun l => hx.2 l j)
    exact ⟨_, elem_mem hF.1 hij (hy.mono (by omega)), b, hb, e⟩
  · rw [← hd]
    refine Finset.sum_lt_sum (fun p _ => ?_) ⟨(i, j), Finset.mem_univ _, by simp only; omega⟩
    obtain ⟨a, b⟩ := p
    simp only
    by_cases c : a = j ∧ b = i
    · rw [c.1, c.2]; omega
    by_cases c' : a = i ∧ b = j
    · rw [c'.1, c'.2]; omega
    rw [h4 a b c, h2 a b c']
end GlobalTheory.IwahoriInj
