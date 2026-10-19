-- Prove2me | solution 1 for OAI.EuclideanSteinitzBergstrom.signing_implies_ordering
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:20:31.283105+00:00
-- url     : https://prove2.me/submissions/20465764-de0d-438a-ae6b-632bf63ebdd2

import Mathlib
import Definitions.Def_SteinitzBergstrom
import Definitions.Def_OAIQWESB000

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Transference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive-forward and negative-reverse permutation transference. -/

section

namespace EuclideanSteinitzBergstrom

section Lists

variable {α E : Type*}

lemma sum_take_ofFn [AddCommMonoid E] {N : ℕ} (v : Fin N → E) (k : ℕ) :
    ((List.ofFn v).take k).sum =
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), v i := by
  induction N generalizing k with
  | zero => simp
  | succ N ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.ofFn_succ, List.take_succ_cons, List.sum_cons,
        Finset.sum_filter, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.zero_lt_succ, ite_true, Fin.val_succ,
        Nat.succ_lt_succ_iff]
      rw [ih]
      rw [Finset.sum_filter]

lemma take_filter_eq_filter_take (p : α → Bool) (l : List α) (k : ℕ) :
    ∃ j ≤ l.length, (l.filter p).take k = (l.take j).filter p := by
  induction l generalizing k with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons a l ih =>
    by_cases ha : p a = true
    · cases k with
      | zero => exact ⟨0, by simp, by simp⟩
      | succ k =>
        obtain ⟨j, hj, he⟩ := ih k
        exact ⟨j + 1, by simpa using hj, by simp [ha, he]⟩
    · obtain ⟨j, hj, he⟩ := ih k
      exact ⟨j + 1, by simpa using hj, by simp [ha, he]⟩

lemma signedOrder_perm (p : α → Bool) (l : List α) :
    (signedOrder p l).Perm l := by
  exact ((List.Perm.refl (l.filter p)).append (List.reverse_perm _)).trans
    (List.filter_append_perm p l)

lemma signedOrder_prefix [AddCommGroup E] (p : α → Bool) (l : List α)
    (v : α → E) (hzero : (l.map v).sum = 0) (k : ℕ) :
    (∃ j ≤ l.length,
      (((signedOrder p l).take k).map v).sum = (((l.take j).filter p).map v).sum) ∨
    (∃ j ≤ l.length,
      (((signedOrder p l).take k).map v).sum =
        -((((l.take j).filter fun a => !p a).map v).sum)) := by
  by_cases hk : k ≤ (l.filter p).length
  · left
    obtain ⟨j, hj, he⟩ := take_filter_eq_filter_take p l k
    refine ⟨j, hj, ?_⟩
    simp only [signedOrder, List.take_append_of_le_length hk, he]
  · right
    let q : α → Bool := fun a => !p a
    have hz : ((signedOrder p l).map v).sum = 0 := by
      rw [((signedOrder_perm p l).map v).sum_eq, hzero]
    have hd :
        (((signedOrder p l).drop k).map v).sum =
          ((((l.filter q).take ((l.filter q).length - (k - (l.filter p).length)))).map v).sum := by
      simp [signedOrder, List.drop_append, List.drop_eq_nil_of_le (Nat.le_of_not_ge hk),
        List.drop_reverse, q]
    obtain ⟨j, hj, he⟩ := take_filter_eq_filter_take q l
      ((l.filter q).length - (k - (l.filter p).length))
    refine ⟨j, hj, ?_⟩
    have hs := List.sum_take_add_sum_drop ((signedOrder p l).map v) k
    rw [← List.map_take, ← List.map_drop, hz, hd, he] at hs
    exact eq_neg_of_add_eq_zero_left hs

lemma signed_parts [AddCommGroup E] (p : α → Bool) (l : List α) (v : α → E) :
    2 • (((l.filter p).map v).sum) =
      (l.map v).sum + (l.map fun a => if p a then v a else -v a).sum ∧
    2 • (((l.filter fun a => !p a).map v).sum) =
      (l.map v).sum - (l.map fun a => if p a then v a else -v a).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rcases ih with ⟨ihp, ihn⟩
    cases ha : p a <;> simp_all [two_nsmul, sub_eq_add_neg] <;> abel_nf <;> simp

lemma signedOrder_prefix_bound [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : α → Bool) (l : List α) (v : α → E) (B D : ℝ)
    (hzero : (l.map v).sum = 0)
    (hprefix : ∀ j ≤ l.length, ‖((l.take j).map v).sum‖ ≤ B)
    (hsigned : ∀ j ≤ l.length,
      ‖((l.take j).map fun a => if p a then v a else -v a).sum‖ ≤ D)
    (k : ℕ) : ‖(((signedOrder p l).take k).map v).sum‖ ≤ (B + D) / 2 := by
  rcases signedOrder_prefix p l v hzero k with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
  · rw [he]
    have hparts := (signed_parts p (l.take j) v).1
    have htwice : ‖(2 : ℝ) • (((l.take j).filter p).map v).sum‖ ≤ B + D := by
      rw [two_smul, ← two_nsmul, hparts]
      exact (norm_add_le _ _).trans (add_le_add (hprefix j hj) (hsigned j hj))
    rw [norm_smul] at htwice
    norm_num at htwice
    linarith
  · rw [he, norm_neg]
    have hparts := (signed_parts p (l.take j) v).2
    have htwice : ‖(2 : ℝ) • (((l.take j).filter fun a => !p a).map v).sum‖ ≤ B + D := by
      rw [two_smul, ← two_nsmul, hparts]
      exact (norm_sub_le _ _).trans (add_le_add (hprefix j hj) (hsigned j hj))
    rw [norm_smul] at htwice
    norm_num at htwice
    linarith

lemma exists_perm_of_list_perm {N : ℕ} (l : List (Fin N))
    (hl : l.Perm (List.ofFn (id : Fin N → Fin N))) :
    ∃ π : Equiv.Perm (Fin N), List.ofFn π = l := by
  have hlen : l.length = N := by simpa using hl.length_eq
  have hnodup : l.Nodup := hl.nodup_iff.mpr (List.nodup_ofFn.mpr Function.injective_id)
  have hmem : ∀ i, i ∈ l := fun i => hl.mem_iff.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)
  let π := (finCongr hlen.symm).trans (List.Nodup.getEquivOfForallMemList l hnodup hmem)
  refine ⟨π, List.ext_getElem (by simp [hlen]) ?_⟩
  intro i hi hj
  simp [π, List.Nodup.getEquivOfForallMemList]

end Lists

theorem signing_implies_ordering_oai (C : ℝ) (h : SignedPrefixBound C) :
    OrderingPrefixBound C := by
  classical
  intro d N hd hN v hv hzero
  let peak : Equiv.Perm (Fin N) → ℝ := fun π =>
    Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (N + 1) =>
      ‖walkPrefix (fun i => v (π i)) k.val‖)
  obtain ⟨π, _, hmin⟩ := Finset.exists_min_image Finset.univ peak Finset.univ_nonempty
  have hpeak (σ : Equiv.Perm (Fin N)) (k : ℕ) (hk : k ≤ N) :
      ‖walkPrefix (fun i => v (σ i)) k‖ ≤ peak σ :=
    Finset.le_sup' (fun k : Fin (N + 1) => ‖walkPrefix (fun i => v (σ i)) k.val‖)
      (Finset.mem_univ (⟨k, by omega⟩ : Fin (N + 1)))
  obtain ⟨ε, hε, hsign⟩ := h d N hd hN (fun i => v (π i)) (fun i => hv (π i))
  let p : Fin N → Bool := fun i => decide (ε i = 1)
  let l : List (Fin N) := List.ofFn id
  have heps (i : Fin N) : (if p i then v (π i) else -v (π i)) = ε i • v (π i) := by
    rcases hε i with hi | hi <;> norm_num [p, hi]
  have hz : (l.map fun i => v (π i)).sum = 0 := by
    simpa [l, List.map_ofFn, List.sum_ofFn, Equiv.sum_comp] using hzero
  obtain ⟨σ, hσ⟩ := exists_perm_of_list_perm (signedOrder p l) (signedOrder_perm p l)
  have hpref : ∀ k ≤ l.length, ‖((l.take k).map fun i => v (π i)).sum‖ ≤ peak π := by
    intro k hk
    simpa [l, List.map_take, List.map_ofFn, sum_take_ofFn, walkPrefix] using
      hpeak π k (by simpa [l] using hk)
  have hsig : ∀ k ≤ l.length,
      ‖((l.take k).map fun i => if p i then v (π i) else -v (π i)).sum‖ ≤ C * Real.sqrt d := by
    intro k hk
    simp_rw [heps]
    simpa [l, List.map_take, List.map_ofFn, sum_take_ofFn, walkPrefix] using
      hsign k (by simpa [l] using hk)
  have hnew : peak (σ.trans π) ≤ (peak π + C * Real.sqrt d) / 2 := by
    apply (Finset.sup'_le_iff _ _).mpr
    intro k _
    have hh := signedOrder_prefix_bound p l (fun i => v (π i))
      (peak π) (C * Real.sqrt d) hz hpref hsig k.val
    rw [← hσ, List.map_take, List.map_ofFn, sum_take_ofFn] at hh
    exact hh
  have hβ : peak π ≤ C * Real.sqrt d := by
    have := hmin (σ.trans π) (Finset.mem_univ _)
    linarith
  exact ⟨π, fun k hk => (hpeak π k hk).trans hβ⟩

end EuclideanSteinitzBergstrom

end

end OAI
end

theorem solution : type_of% @OAI.EuclideanSteinitzBergstrom.signing_implies_ordering_oai := @OAI.EuclideanSteinitzBergstrom.signing_implies_ordering_oai
