-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.Inj.trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:27.706844+00:00
-- url     : https://prove2.me/submissions/275d07b3-ce20-4859-96e2-ed177d91f122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_mem_fixed
import Theorems.Thm_GlobalTheory_IwahoriInj_sub_mem_twKer
import Theorems.Thm_GlobalTheory_IwahoriInj_apply_mem_twKer
import Theorems.Thm_GlobalTheory_IwahoriInj_exists_orbit

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
namespace Inj
theorem _root_.solution (hπ : IsSmooth π) {I J K : Subgroup G} (hJ : IsCompact (J : Set G))
    (hfac : ∀ x ∈ J, ∃ a ∈ K, ∃ b ∈ I, x = a * b) (h1 : Inj π I J) (h2 : Inj π J K) : Inj π I K := by
  intro v hv hv'
  obtain ⟨S, hS, hz⟩ := exists_orbit hπ hJ v
  have hz0 : ∑ u ∈ S, u = 0 := h2 _ hz (Submodule.sum_mem _ fun u hu => by
    obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
    obtain ⟨a, ha, b, hb, rfl⟩ := hfac x hx
    rw [map_mul, Module.End.mul_apply, mem_fixed.1 hv b hb]
    exact apply_mem_twKer ha hv')
  have h3 : ∑ u ∈ S, (u - v) ∈ twKer π J 1 := Submodule.sum_mem _ fun u hu => by
    obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
    exact sub_mem_twKer hx v
  rw [Finset.sum_sub_distrib, hz0, zero_sub, neg_mem_iff, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h3
  have hne : (S.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨v, (hS v).2 ⟨1, one_mem _, by simp⟩⟩)
  exact h1 v hv ((Submodule.smul_mem_iff _ hne).1 h3)
end Inj
end GlobalTheory.IwahoriInj
