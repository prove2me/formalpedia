-- Prove2me | solution 1 for MME.StothersFourth.fixedHash_budget_of_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:54:35.276103+00:00
-- url     : https://prove2.me/submissions/1f1fedef-2931-4614-96e7-7331d74e7f91

import Definitions.Def_mme_stothers_fixed_affine_hash
import Theorems.Thm_MME_StothersFourth_fixedHash_incidence_sums
import Theorems.Thm_MME_StothersFourth_fixedHash_retained_vertex_closed
import Theorems.Thm_mme_finite_collision_budget_averaging_real
import Theorems.Thm_mme_CW_2376_aggregate_budget_of_normalized_margin

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000


namespace MME.StothersFourth

private theorem fixedHash_state_universe_card
    (m p : ℕ) [Fact p.Prime] :
    (fixedHashStateUniverse m p).card =
      p ^ (fixedOuterLength m + 2) := by
  classical
  simp only [fixedHashStateUniverse, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [show fixedOuterLength m + 2 =
      (fixedOuterLength m + 1) + 1 by omega]
  exact (pow_succ p (fixedOuterLength m + 1)).symm


/-- A uniform per-mode completion-degree bound controls all directed
target--ambient collisions by `3 * |T| * D`. -/
private theorem fixedHash_collision_universe_card_of_degree
    (m D : ℕ)
    (hdeg : ∀ i : Fin 3, ∀ a ∈ fixedHashAllTargetEdges m,
      ((fixedHashMarginalUniverse m).filter
        (fun b ↦ b.1 i = a.1 i)).card ≤ D) :
    (fixedHashAllTargetAmbientCollisions m).card ≤
      3 * (fixedHashAllTargetEdges m).card * D := by
  classical
  let U := fixedHashMarginalUniverse m
  let T := fixedHashAllTargetEdges m
  let C := fixedHashAllTargetAmbientCollisions m
  let star (i : Fin 3) (a : FixedMarginalSupportedAddress m) :=
    U.filter (fun b ↦ b.1 i = a.1 i)
  let Ci (i : Fin 3) := T.biUnion (fun a ↦
    (star i a).image (fun b ↦ (a, b)))
  let CU := (Finset.univ : Finset (Fin 3)).biUnion Ci
  have hsubset : C ⊆ CU := by
    intro ab hab
    have hfull := hab
    simp only [C, fixedHashAllTargetAmbientCollisions,
      fixedTargetAmbientCollisions, Finset.mem_filter,
      Finset.mem_product] at hfull
    obtain ⟨⟨haT, hbU⟩, _hne, i, hi⟩ := hfull
    simp only [CU, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨i, ?_⟩
    simp only [Ci, Finset.mem_biUnion]
    refine ⟨ab.1, haT, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨ab.2, ?_, rfl⟩
    simp only [star, Finset.mem_filter]
    exact ⟨hbU, hi.symm⟩
  calc
    C.card ≤ CU.card := Finset.card_le_card hsubset
    _ ≤ ∑ i : Fin 3, (Ci i).card := by
      simpa only [CU]
        using (Finset.card_biUnion_le :
          CU.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin 3)), (Ci i).card)
    _ ≤ ∑ i : Fin 3, ∑ a ∈ T, (star i a).card := by
      apply Finset.sum_le_sum
      intro i _hi
      calc
        (Ci i).card ≤ ∑ a ∈ T,
            ((star i a).image (fun b ↦ (a, b))).card := by
          simpa only [Ci] using (Finset.card_biUnion_le :
            (T.biUnion (fun a ↦
              (star i a).image (fun b ↦ (a, b)))).card ≤
              ∑ a ∈ T, ((star i a).image (fun b ↦ (a, b))).card)
        _ ≤ ∑ a ∈ T, (star i a).card := by
          apply Finset.sum_le_sum
          intro a _ha
          exact Finset.card_image_le
    _ ≤ ∑ i : Fin 3, ∑ a ∈ T, D := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro a ha
      exact hdeg i a ha
    _ = 3 * T.card * D := by simp [mul_assoc]

/-- Aggregate incidence bounds select one vertex-closed hash state with the
requested real target surplus. -/
private theorem fixedHash_budget_select
    (m p : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hp9 : 9 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (L : ℝ)
    (hbudget :
      (p : ℝ) ^ (fixedOuterLength m + 2) * L +
          ((fixedHashAllTargetAmbientCollisions m).card : ℝ) *
            (p : ℝ) ^ fixedOuterLength m ≤
        ((fixedHashAllTargetEdges m).card : ℝ) *
          (S.card : ℝ) * (p : ℝ) ^ fixedOuterLength m) :
    ∃ q : (Fin (fixedOuterLength m + 1) → ZMod p) × ZMod p,
      let E := fixedHashEdgesAtState m p S q
      FixedMarginalVertexClosed E ∧
        ((fixedTargetAmbientCollisions E).card : ℝ) + L ≤
          ((fixedExactTargetEdges E).card : ℝ) := by
  classical
  let good :
      ((Fin (fixedOuterLength m + 1) → ZMod p) × ZMod p) → ℕ :=
    fun q ↦ (fixedExactTargetEdges
      (fixedHashEdgesAtState m p S q)).card
  let bad :
      ((Fin (fixedOuterLength m + 1) → ZMod p) × ZMod p) → ℕ :=
    fun q ↦ (fixedTargetAmbientCollisions
      (fixedHashEdgesAtState m p S q)).card
  have hinc := fixedHash_incidence_sums
    m p hm hp9 hpodd S hSrange
  have hgoodNat :
      (∑ q, good q) =
        (fixedHashAllTargetEdges m).card * S.card *
          p ^ fixedOuterLength m := by
    simpa only [good, fixedHashStateUniverse,
      Finset.sum_const_zero] using hinc.1
  have hbadNat :
      (∑ q, bad q) ≤
        (fixedHashAllTargetAmbientCollisions m).card *
          p ^ fixedOuterLength m := by
    simpa only [bad, fixedHashStateUniverse,
      Finset.sum_const_zero] using hinc.2
  have hgoodReal :
      (∑ q, (good q : ℝ)) =
        ((fixedHashAllTargetEdges m).card : ℝ) *
          (S.card : ℝ) * (p : ℝ) ^ fixedOuterLength m := by
    exact_mod_cast hgoodNat
  have hbadReal :
      (∑ q, (bad q : ℝ)) ≤
        ((fixedHashAllTargetAmbientCollisions m).card : ℝ) *
          (p : ℝ) ^ fixedOuterLength m := by
    exact_mod_cast hbadNat
  have hcard :
      Fintype.card
          ((Fin (fixedOuterLength m + 1) → ZMod p) × ZMod p) =
        p ^ (fixedOuterLength m + 2) := by
    simpa only [fixedHashStateUniverse, Finset.card_univ] using
      fixedHash_state_universe_card m p
  have havgBudget :
      (Fintype.card
          ((Fin (fixedOuterLength m + 1) → ZMod p) × ZMod p) : ℝ) * L +
          ∑ q, (bad q : ℝ) ≤
        ∑ q, (good q : ℝ) := by
    calc
      (Fintype.card
          ((Fin (fixedOuterLength m + 1) → ZMod p) × ZMod p) : ℝ) * L +
          ∑ q, (bad q : ℝ) ≤
          (p : ℝ) ^ (fixedOuterLength m + 2) * L +
            ((fixedHashAllTargetAmbientCollisions m).card : ℝ) *
              (p : ℝ) ^ fixedOuterLength m := by
        rw [hcard]
        push_cast
        simpa only [add_comm] using add_le_add_left hbadReal
          ((p : ℝ) ^ (fixedOuterLength m + 2) * L)
      _ ≤ ((fixedHashAllTargetEdges m).card : ℝ) *
            (S.card : ℝ) * (p : ℝ) ^ fixedOuterLength m := hbudget
      _ = ∑ q, (good q : ℝ) := hgoodReal.symm
  obtain ⟨q, hq⟩ :=
    mme_finite_collision_budget_averaging_real good bad L havgBudget
  refine ⟨q, ?_, ?_⟩
  · exact fixedHash_retained_vertex_closed
      m p S q.2 (fun k ↦ q.1 k.castSucc) hpodd hSrange hSfree
  · exact hq

/- The reusable interface between a target-star factorization, a uniform
ambient degree bound, and the concrete affine-hash implementation. -/
end MME.StothersFourth

open MME.StothersFourth

theorem solution
    (m p D Dstar : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hp9 : 9 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (V loss : ℝ) (hV : 0 ≤ V)
    (hT : ((fixedHashAllTargetEdges m).card : ℝ) =
      V * (Dstar : ℝ))
    (hdeg : ∀ i : Fin 3, ∀ a ∈ fixedHashAllTargetEdges m,
      ((fixedHashMarginalUniverse m).filter
        (fun b ↦ b.1 i = a.1 i)).card ≤ D)
    (hmargin :
      (p : ℝ) ^ 2 * loss + 3 * (Dstar : ℝ) * (D : ℝ) ≤
        (Dstar : ℝ) * (S.card : ℝ)) :
    ∃ E : Finset (FixedMarginalSupportedAddress m),
      FixedMarginalVertexClosed E ∧
        ((fixedTargetAmbientCollisions E).card : ℝ) + V * loss ≤
          ((fixedExactTargetEdges E).card : ℝ) := by
  let N := fixedOuterLength m
  have hCnat : (fixedHashAllTargetAmbientCollisions m).card ≤
      3 * (fixedHashAllTargetEdges m).card * D :=
    fixedHash_collision_universe_card_of_degree m D hdeg
  have hC :
      ((fixedHashAllTargetAmbientCollisions m).card : ℝ) * (p : ℝ) ^ N ≤
        3 * ((fixedHashAllTargetEdges m).card : ℝ) * (D : ℝ) *
          (p : ℝ) ^ N := by
    have hc' :
        ((fixedHashAllTargetAmbientCollisions m).card : ℝ) ≤
          3 * ((fixedHashAllTargetEdges m).card : ℝ) * (D : ℝ) := by
      exact_mod_cast hCnat
    exact mul_le_mul_of_nonneg_right hc' (by positivity)
  have haggregate :=
    mme_CW_2376_aggregate_budget_of_normalized_margin
      (N + 1) p (fixedHashAllTargetEdges m).card S.card D Dstar
      V loss (by omega) hV hT hmargin
  have haggregate' :
      (p : ℝ) ^ (N + 2) * (V * loss) +
          3 * ((fixedHashAllTargetEdges m).card : ℝ) * (D : ℝ) *
            (p : ℝ) ^ N ≤
        ((fixedHashAllTargetEdges m).card : ℝ) * (S.card : ℝ) *
          (p : ℝ) ^ N := by
    simpa only [Nat.add_assoc, Nat.add_sub_cancel] using haggregate
  have hbudget :
      (p : ℝ) ^ (N + 2) * (V * loss) +
          ((fixedHashAllTargetAmbientCollisions m).card : ℝ) *
            (p : ℝ) ^ N ≤
        ((fixedHashAllTargetEdges m).card : ℝ) * (S.card : ℝ) *
          (p : ℝ) ^ N := by
    have hcadd := add_le_add_left hC
      ((p : ℝ) ^ (N + 2) * (V * loss))
    have hcadd' :
        (p : ℝ) ^ (N + 2) * (V * loss) +
            ((fixedHashAllTargetAmbientCollisions m).card : ℝ) *
              (p : ℝ) ^ N ≤
          (p : ℝ) ^ (N + 2) * (V * loss) +
            3 * ((fixedHashAllTargetEdges m).card : ℝ) * (D : ℝ) *
              (p : ℝ) ^ N := by
      simpa only [add_comm] using hcadd
    exact hcadd'.trans haggregate'
  obtain ⟨q, hclosed, hsurplus⟩ :=
    fixedHash_budget_select m p hm hp9 hpodd S hSrange hSfree
      (V * loss) (by simpa only [N] using hbudget)
  exact ⟨fixedHashEdgesAtState m p S q, hclosed, hsurplus⟩
