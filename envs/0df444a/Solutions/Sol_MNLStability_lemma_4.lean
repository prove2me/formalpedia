-- Prove2me | solution 1 for MNLStability.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:58:43.388181+00:00
-- url     : https://prove2.me/submissions/1e2042c8-6f98-4031-af6b-71cb5b90d9a7

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_swap
import Definitions.Def_MNLStability_IsUniversal

namespace Aux_MNL4
open MNLStability

variable {n : ℕ}

lemma expX_nonneg (wt : Weights n) (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (U : Fin n → ℕ) (i : Fin n) :
    0 ≤ expX wt pM U i :=
  Finset.sum_nonneg (fun m _ => mul_nonneg (hM.1 m) ENNReal.toReal_nonneg)

lemma mem_foldr_union (x : Fin n) : ∀ L : List (Finset (Fin n)),
    x ∈ L.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ L, x ∈ s
  | [] => by simp
  | s :: L => by simp [Finset.mem_union, mem_foldr_union x L]

lemma sum_partition (f : Fin n → ℝ) : ∀ L : List (Finset (Fin n)), L.Pairwise Disjoint →
    (L.map (fun s => ∑ i ∈ s, f i)).sum = ∑ i ∈ L.foldr (· ∪ ·) ∅, f i
  | [], _ => by simp
  | s :: L, h => by
    rw [List.pairwise_cons] at h
    have hd : Disjoint s (L.foldr (· ∪ ·) ∅) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨t, ht, hxt⟩ := (mem_foldr_union x L).1 hx'
      exact Finset.disjoint_left.1 (h.1 t ht) hx hxt
    rw [List.map_cons, List.sum_cons, sum_partition f L h.2, List.foldr_cons,
      Finset.sum_union hd]

theorem main_ind (wts : Weights n) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (pM : ℕ →₀ ℝ) (C : ℕ)
    (ε : ℝ) : ∀ (cls : List (Finset (Fin n) × List (Fin n → ℕ))),
    (cls.map Prod.fst).Pairwise Disjoint →
    (∀ p ∈ cls, IsUniversal wts r pM C ε p.1 p.2) →
    ∀ U : Fin n → ℕ, norm1 U ≤ C →
    ∃ Vs : List (Fin n → ℕ), List.Forall₂ (fun p V => V ∈ p.2) cls Vs ∧
      (∀ i, (∀ q ∈ cls, i ∉ q.1) →
        expX wts pM U i ≤
          expX wts pM ((cls.zip Vs).foldl (fun U' q => swap q.1.1 U' q.2) U) i) ∧
      (ε ≤ 1 → ∀ q ∈ cls, (1 - ε) * ∑ i ∈ q.1, r i * expX wts pM U i ≤
        ∑ i ∈ q.1, r i * expX wts pM ((cls.zip Vs).foldl (fun U' q => swap q.1.1 U' q.2) U) i) ∧
      norm1 ((cls.zip Vs).foldl (fun U' q => swap q.1.1 U' q.2) U) ≤ norm1 U
  | [], _, _, U, _ => ⟨[], List.Forall₂.nil, fun i _ => le_rfl, fun _ q hq => by simp at hq,
      le_rfl⟩
  | p :: cls, hdisj, huniv, U, hU => by
    rw [List.map_cons, List.pairwise_cons] at hdisj
    obtain ⟨V, hV, hu1, hu2, hu3⟩ := huniv p (by simp) U hU
    obtain ⟨Vs, hF, ha, hb, hc⟩ := main_ind wts r hr pM C ε cls hdisj.2
      (fun q hq => huniv q (by simp [hq])) (swap p.1 U V) (hu3.trans hU)
    refine ⟨V :: Vs, List.Forall₂.cons hV hF, ?_, ?_, ?_⟩
    · intro i hi
      show expX wts pM U i ≤
        expX wts pM ((cls.zip Vs).foldl (fun U' q => swap q.1.1 U' q.2) (swap p.1 U V)) i
      exact (hu1 i (hi p (by simp))).trans (ha i (fun q hq => hi q (by simp [hq])))
    · intro hε q hq
      show (1 - ε) * ∑ i ∈ q.1, r i * expX wts pM U i ≤ ∑ i ∈ q.1, r i *
        expX wts pM ((cls.zip Vs).foldl (fun U' q => swap q.1.1 U' q.2) (swap p.1 U V)) i
      have hε' : 0 ≤ 1 - ε := by linarith
      rcases List.mem_cons.1 hq with rfl | hq'
      · refine hu2.trans (Finset.sum_le_sum (fun i hi =>
          mul_le_mul_of_nonneg_left (ha i ?_) (hr i)))
        intro q' hq'
        exact Finset.disjoint_left.1 (hdisj.1 q'.1 (List.mem_map.2 ⟨q', hq', rfl⟩)) hi
      · refine le_trans ?_ (hb hε q hq')
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi =>
          mul_le_mul_of_nonneg_left (hu1 i ?_) (hr i))) hε'
        intro hip
        exact Finset.disjoint_left.1 (hdisj.1 q.1 (List.mem_map.2 ⟨q, hq', rfl⟩)) hip hi
    · exact hc.trans hu3

end Aux_MNL4

open MNLStability Aux_MNL4 in
theorem solution {n : ℕ} (wts : Weights n) (hw : wts.Pos) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (C : ℕ) (ε : ℝ) (hε : 0 < ε)
    (cls : List (Finset (Fin n) × List (Fin n → ℕ)))
    (hdisj : (cls.map Prod.fst).Pairwise Disjoint) (hcover : ∀ i, ∃ p ∈ cls, i ∈ p.1)
    (hunif : ∀ p ∈ cls, wts.UniformOn p.1)
    (huniv : ∀ p ∈ cls, IsUniversal wts r pM C ε p.1 p.2)
    (U : Fin n → ℕ) (hU : norm1 U ≤ C) :
    ∃ Vs : List (Fin n → ℕ), List.Forall₂ (fun p V => V ∈ p.2) cls Vs ∧
      (1 - ε) * expR wts r pM U ≤
        expR wts r pM ((cls.zip Vs).foldl (fun U' q => swap q.1.1 U' q.2) U) ∧
      norm1 ((cls.zip Vs).foldl (fun U' q => swap q.1.1 U' q.2) U) ≤ C := by
  obtain ⟨Vs, hF, _, hb, hc⟩ := main_ind wts r hr pM C ε cls hdisj huniv U hU
  refine ⟨Vs, hF, ?_, hc.trans hU⟩
  have huniv' : (cls.map Prod.fst).foldr (· ∪ ·) ∅ = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    obtain ⟨p, hp, hip⟩ := hcover i
    exact (mem_foldr_union i _).2 ⟨p.1, List.mem_map.2 ⟨p, hp, rfl⟩, hip⟩
  have hpart : ∀ W : Fin n → ℕ, expR wts r pM W =
      (cls.map (fun p => ∑ i ∈ p.1, r i * expX wts pM W i)).sum := by
    intro W
    unfold expR
    have := sum_partition (fun i => r i * expX wts pM W i) (cls.map Prod.fst) hdisj
    rw [huniv', List.map_map] at this
    exact this.symm
  have h0 : ∀ W : Fin n → ℕ, 0 ≤ expR wts r pM W := fun W =>
    Finset.sum_nonneg (fun i _ => mul_nonneg (hr i) (expX_nonneg wts pM hM W i))
  by_cases hε1 : ε ≤ 1
  · rw [hpart U, hpart ((cls.zip Vs).foldl (fun U' q => swap q.1.1 U' q.2) U),
      ← List.sum_map_mul_left]
    exact List.sum_le_sum (fun p hp => hb hε1 p hp)
  · push_neg at hε1
    have := h0 U
    have := h0 ((cls.zip Vs).foldl (fun U' q => swap q.1.1 U' q.2) U)
    nlinarith
