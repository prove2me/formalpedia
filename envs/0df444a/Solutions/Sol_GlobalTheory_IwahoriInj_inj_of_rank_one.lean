-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.inj_of_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:29.647807+00:00
-- url     : https://prove2.me/submissions/69b9a32b-7b85-4cc5-a0a4-338573b05344

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_mem_fixed
import Theorems.Thm_GlobalTheory_IwahoriInj_twKer_mono
import Theorems.Thm_GlobalTheory_IwahoriInj_apply_mem_twKer
import Theorems.Thm_GlobalTheory_IwahoriInj_eq_zero_of_fixed
import Theorems.Thm_GlobalTheory_IwahoriInj_exists_orbit
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
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.IwahoriInj
theorem _root_.solution (hπ : IsSmooth π) {I J P : Subgroup G} (hJ : IsCompact (J : Set G))
    (hP : IsCompact (P : Set G)) (hJP : J ≤ P) {s : G} (hs : s ∈ P) (hconj : ∀ x ∈ J, s⁻¹ * x * s ∈ I)
    (hdec : ∀ p ∈ P, (∃ a ∈ J, ∃ b ∈ I, p = a * b) ∨ s⁻¹ * p ∈ I) : Inj π I J := by
  classical
  intro v hv hv'
  obtain ⟨S, hS, hz⟩ := exists_orbit hπ hP v
  have hz0 : ∑ u ∈ S, u = 0 := eq_zero_of_fixed hπ hP hz (Submodule.sum_mem _ fun u hu => by
    obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
    exact apply_mem_twKer hx (twKer_mono hJP hv'))
  have hw : π s v ∈ S := (hS _).2 ⟨s, hs, rfl⟩
  have h3 : ∑ u ∈ S.erase (π s v), u ∈ twKer π J 1 := Submodule.sum_mem _ fun u hu => by
    obtain ⟨hne, hu⟩ := Finset.mem_erase.1 hu
    obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
    rcases hdec x hx with ⟨a, ha, b, hb, rfl⟩ | h
    · rw [map_mul, Module.End.mul_apply, mem_fixed.1 hv b hb]
      exact apply_mem_twKer ha hv'
    · refine absurd ?_ hne
      conv_rhs => rw [← mem_fixed.1 hv _ h]
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  rw [← Finset.add_sum_erase _ _ hw, add_eq_zero_iff_eq_neg] at hz0
  have h4 : π s v = 0 := eq_zero_of_fixed hπ hJ (mem_fixed.2 fun x hx => by
    conv_rhs => rw [← mem_fixed.1 hv _ (hconj x hx)]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group) (by rw [hz0]; exact neg_mem h3)
  have := congrArg (π s⁻¹) h4
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at this
end GlobalTheory.IwahoriInj
