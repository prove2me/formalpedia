-- Prove2me | solution 1 for NCPSeqOpt.AugLag.nonexpansive_proj
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:20:33.910474+00:00
-- url     : https://prove2.me/submissions/36962652-3703-4c53-b89d-264922b143a6

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting

open MoreauProx.Decomposition
open scoped InnerProductSpace
open Filter Topology

namespace Aux_NCPSeqOpt_AugLag_nonexpansive_proj

open NCPSeqOpt.AugLag

lemma proj_spec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) (hK : IsClosedConvexCone K) (w : E) :
    IsProj K w (proj K w) := by
  have hex : ∃ v, IsProj K w v := by
    obtain ⟨v, hv, heq⟩ := exists_norm_eq_iInf_of_complete_convex hK.1
      hK.2.1.isComplete hK.2.2.1 w
    refine ⟨v, hv, fun u hu => ?_⟩
    rw [heq]
    exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨u, hu⟩ : K)
  unfold proj
  rw [dif_pos hex]
  exact hex.choose_spec

lemma var_ineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) (hK : IsClosedConvexCone K) (w : E) :
    ∀ u ∈ K, ⟪w - proj K w, u - proj K w⟫_ℝ ≤ 0 := by
  have h := proj_spec K hK w
  have hne : Nonempty K := ⟨⟨_, h.1⟩⟩
  have heq : ‖w - proj K w‖ = ⨅ u : K, ‖w - u‖ := by
    apply le_antisymm
    · exact le_ciInf (fun u => h.2 u u.2)
    · exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨_, h.1⟩ : K)
  exact (norm_eq_iInf_iff_real_inner_le_zero hK.2.2.1 h.1).1 heq

end Aux_NCPSeqOpt_AugLag_nonexpansive_proj

open Aux_NCPSeqOpt_AugLag_nonexpansive_proj in
open NCPSeqOpt.AugLag in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E) (hK : IsClosedConvexCone K) (v w : E) :
    ‖proj K w - proj K v‖ ≤ ‖w - v‖ := by
  set P := proj K w with hP
  set Q := proj K v with hQ
  have h1 : ⟪w - P, Q - P⟫_ℝ ≤ 0 := var_ineq K hK w Q (proj_spec K hK v).1
  have h2 : ⟪v - Q, P - Q⟫_ℝ ≤ 0 := var_ineq K hK v P (proj_spec K hK w).1
  have hQP : Q - P = -(P - Q) := by abel
  rw [hQP, inner_neg_right] at h1
  have hwv : w - v = (w - P) - (v - Q) + (P - Q) := by abel
  have key : ‖P - Q‖ ^ 2 ≤ ⟪w - v, P - Q⟫_ℝ := by
    rw [hwv, inner_add_left, inner_sub_left, real_inner_self_eq_norm_sq]
    linarith
  have hcs : ⟪w - v, P - Q⟫_ℝ ≤ ‖w - v‖ * ‖P - Q‖ := real_inner_le_norm _ _
  have hn := norm_nonneg (P - Q)
  have hn2 := norm_nonneg (w - v)
  nlinarith
