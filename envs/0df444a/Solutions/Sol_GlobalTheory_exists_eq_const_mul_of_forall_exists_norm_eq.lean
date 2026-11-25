-- Prove2me | solution 1 for GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:38:23.730054+00:00
-- url     : https://prove2.me/submissions/e067ab28-91b9-4c36-86b6-17a6ee522484

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EqZeroOfMulEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsEqConstMulOfForallExistsNormEq
import Theorems.Thm_GlobalTheory_exists_eventually_eq_mul_of_norm_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_eq_zero_of_eventually


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Metric Set Filter Topology
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (ι : Type) [Countable ι]
      (O : Set V), IsOpen O → IsPreconnected O → O.Nonempty → ∀ (P : V → ℂ) (Q : ι → V → ℂ),
      DifferentiableOn ℂ P O → (∀ i, DifferentiableOn ℂ (Q i) O) → (∀ x ∈ O, ∃ i, ‖P x‖ = ‖Q i x‖) →
      ∃ (i : ι) (c : ℂ), ∀ x ∈ O, P x = c * Q i x := by
  intro V _ _ _ ι _ O hO hc hne P Q hP hQ h
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  haveI : BaireSpace O := hO.baireSpace
  haveI : Nonempty O := hne.to_subtype
  have hcl : ∀ i, IsClosed {x : O | ‖P x‖ = ‖Q i x‖} := fun i =>
    isClosed_eq (hP.continuousOn.restrict.norm) ((hQ i).continuousOn.restrict.norm)
  have hcov : ⋃ i, {x : O | ‖P x‖ = ‖Q i x‖} = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi⟩ := h x x.2
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hcov
  have hx1 : ∀ᶠ y : O in 𝓝 x, ‖P y‖ = ‖Q i y‖ := mem_interior_iff_mem_nhds.mp hx
  have hx2 : ∀ᶠ y in 𝓝 (x : V), ‖P y‖ = ‖Q i y‖ := by
    rw [← hO.isOpenEmbedding_subtypeVal.map_nhds_eq x]
    exact hx1
  obtain ⟨z, hz, c, hzc⟩ := exists_eventually_eq_mul_of_norm_eq hO hP (hQ i) x.2 hx2
  refine ⟨i, c, fun y hy => ?_⟩
  have hd : DifferentiableOn ℂ (fun y => P y - c * Q i y) O := hP.sub ((hQ i).const_mul c)
  have := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually hO hc hd hz
    (by filter_upwards [hzc] with y hy; simp [hy]) y hy
  exact sub_eq_zero.mp this
end GlobalTheory
