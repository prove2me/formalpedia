-- Prove2me | solution 1 for KVVMatching.UpperBound.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T19:56:59.789689+00:00
-- url     : https://prove2.me/submissions/cbd137a7-ad6b-4991-8e63-0fdf67e5a4b2

import Init
import Definitions.Def_KVVMatching_UpperBound_RandomValue
import Definitions.Def_KVVMatching_UpperBound_Triangular
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPerfectMatchingBij
import Mathlib

open Finset
namespace KVVMatching.UpperBound.Exposure

def SameThrough {n : ℕ} (G H : Graph n) (k : ℕ) : Prop :=
  ∀ j : Fin n, j.val < k → ∀ r, (r, Fin.rev j) ∈ G ↔ (r, Fin.rev j) ∈ H

theorem history_eq {n : ℕ} {G H : Graph n} {k : ℕ}
    (h : SameThrough G H k) (j : Fin n) (hj : j.val < k) :
    revealedHistory G j = revealedHistory H j := by
  classical
  funext i
  unfold revealedHistory
  split_ifs with hi
  · congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h i (lt_of_le_of_lt hi hj) r
  · rfl

theorem eligible_eq {n : ℕ} {G H : Graph n} {k : ℕ}
    (h : SameThrough G H k) (j : Fin n) (hj : j.val < k) (S : Finset (Fin n)) :
    eligibleRows G S (Fin.rev j) = eligibleRows H S (Fin.rev j) := by
  classical
  ext r
  simp only [eligibleRows, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h j hj r]

theorem matched_eq {n : ℕ} (a : DetAlg n) {G H : Graph n} (k : ℕ)
    (h : SameThrough G H k) : matchedRows G a k = matchedRows H a k := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
    have hi := ih (fun j hj r => h j (Nat.lt_succ_of_lt hj) r)
    simp only [matchedRows, hi]
    split_ifs with hk
    · rw [history_eq h ⟨k,hk⟩ (show k < k+1 from Nat.lt_succ_self k)]
      cases he : a ⟨k,hk⟩ (revealedHistory H ⟨k,hk⟩) with
      | none => rfl
      | some r => rw [eligible_eq h ⟨k,hk⟩ (show k < k+1 from Nat.lt_succ_self k)]
    · rfl

/-- Swap two row labels, without assuming that the algorithm is equivariant. -/
def rowSwap {n : ℕ} (G : Graph n) (u v : Fin n) : Graph n :=
  {e | (Equiv.swap u v e.1,e.2) ∈ G}

theorem sameThrough_rowSwap {n : ℕ} (G : Graph n) (u v : Fin n) (k : ℕ)
    (huv : ∀ j : Fin n, j.val < k → ((u,Fin.rev j) ∈ G ↔ (v,Fin.rev j) ∈ G)) :
    SameThrough (rowSwap G u v) G k := by
  intro j hj r
  change (Equiv.swap u v r,Fin.rev j) ∈ G ↔ (r,Fin.rev j) ∈ G
  by_cases hru : r = u
  · subst r
    simpa using (huv j hj).symm
  by_cases hrv : r = v
  · subst r
    simpa using huv j hj
  simp [Equiv.swap_apply_of_ne_of_ne hru hrv]

theorem permuted_rowSwap {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    permutedTriangular (π.trans (Equiv.swap u v)) = rowSwap (permutedTriangular π) u v := by
  ext e
  simp [permutedTriangular,rowSwap]

/-- Two rows still present at arrival k have identical revealed neighborhoods. -/
theorem triangular_sameThrough_swap {n : ℕ} (π : Equiv.Perm (Fin n))
    (k : Fin n) (u v : Fin n)
    (hu : π.symm u ≤ Fin.rev k) (hv : π.symm v ≤ Fin.rev k) :
    SameThrough (permutedTriangular (π.trans (Equiv.swap u v)))
      (permutedTriangular π) (k.val+1) := by
  rw [permuted_rowSwap]
  apply sameThrough_rowSwap
  intro j hj
  have hjk : j ≤ k := by exact Nat.le_of_lt_succ hj
  have hrev : Fin.rev k ≤ Fin.rev j := by simpa using hjk
  change (π.symm u ≤ Fin.rev j) ↔ (π.symm v ≤ Fin.rev j)
  exact iff_of_true (hu.trans hrev) (hv.trans hrev)

theorem triangular_swap_history {n : ℕ} (π : Equiv.Perm (Fin n))
    (a : DetAlg n) (k : Fin n) (u v : Fin n)
    (hu : π.symm u ≤ Fin.rev k) (hv : π.symm v ≤ Fin.rev k) :
    revealedHistory (permutedTriangular (π.trans (Equiv.swap u v))) k =
      revealedHistory (permutedTriangular π) k ∧
    matchedRows (permutedTriangular (π.trans (Equiv.swap u v))) a k.val =
      matchedRows (permutedTriangular π) a k.val := by
  have h := triangular_sameThrough_swap π k u v hu hv
  exact ⟨history_eq h k (by omega),matched_eq a k.val (fun j hj r => h j (by omega) r)⟩

#print axioms triangular_swap_history
end KVVMatching.UpperBound.Exposure

open Finset
namespace KVVMatching.UpperBound.Exposure

/-- Relabel all rows by a bijection. -/
def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : Graph n) : Graph n :=
  {e | (σ.symm e.1,e.2) ∈ G}

theorem eligible_relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : Graph n)
    (S : Finset (Fin n)) (c : Fin n) :
    eligibleRows (relabel σ G) (S.image σ) c = (eligibleRows G S c).image σ := by
  classical
  ext r
  simp only [eligibleRows, mem_filter, mem_univ, true_and, mem_image, relabel, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hg,hs⟩
    refine ⟨σ.symm r,⟨hg,?_⟩,σ.apply_symm_apply r⟩
    intro hm
    exact hs ⟨σ.symm r,hm,σ.apply_symm_apply r⟩
  · rintro ⟨u,⟨hg,hs⟩,rfl⟩
    simp only [σ.symm_apply_apply]
    refine ⟨hg,?_⟩
    rintro ⟨v,hv,heq⟩
    exact hs (σ.injective heq ▸ hv)

theorem random_relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : Graph n)
    (t : ℕ) (S : Finset (Fin n)) :
    randomValueAux (relabel σ G) t (S.image σ) = randomValueAux G t S := by
  classical
  induction t generalizing S with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t < n
    · simp only [randomValueAux, dif_pos ht]
      rw [eligible_relabel]
      simp only [Finset.image_nonempty, Finset.card_image_of_injective _ σ.injective]
      split_ifs with he
      · congr 1
        congr 1
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro r hr
          simpa only [Finset.image_insert] using ih (insert r S)
        · intro a ha b hb heq
          exact σ.injective heq
      · exact ih S
    · simp only [randomValueAux, dif_neg ht]

theorem relabel_triangular {n : ℕ} (π : Equiv.Perm (Fin n)) :
    relabel π (upperTriangular n) = permutedTriangular π := rfl

theorem random_triangular {n : ℕ} (π : Equiv.Perm (Fin n)) :
    randomValue (permutedTriangular π) = randomValue (upperTriangular n) := by
  simpa only [randomValue,Finset.image_empty,relabel_triangular] using
    random_relabel π (upperTriangular n) n ∅

#print axioms random_relabel
#print axioms random_triangular
end KVVMatching.UpperBound.Exposure

open Finset
namespace KVVMatching.UpperBound.Exposure

noncomputable def available {n : ℕ} (a : DetAlg n) (k : Fin n)
    (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  eligibleRows (permutedTriangular π) (matchedRows (permutedTriangular π) a k.val) (Fin.rev k)

noncomputable def choice {n : ℕ} (a : DetAlg n) (k : Fin n)
    (π : Equiv.Perm (Fin n)) : Option (Fin n) := a k (revealedHistory (permutedTriangular π) k)

theorem swap_data {n : ℕ} (a : DetAlg n) (k : Fin n) (π : Equiv.Perm (Fin n))
    (r s : Fin n) (hr : r ∈ available a k π) (hs : s ∈ available a k π) :
    choice a k (π.trans (Equiv.swap r s)) = choice a k π ∧
    matchedRows (permutedTriangular (π.trans (Equiv.swap r s))) a k.val =
      matchedRows (permutedTriangular π) a k.val ∧
    available a k (π.trans (Equiv.swap r s)) = available a k π := by
  classical
  have hr' : π.symm r ≤ Fin.rev k := (Finset.mem_filter.mp hr).2.1
  have hs' : π.symm s ≤ Fin.rev k := (Finset.mem_filter.mp hs).2.1
  have h := triangular_swap_history π a k r s hr' hs'
  refine ⟨congrArg (a k) h.1,h.2,?_⟩
  unfold available
  rw [h.2]
  exact eligible_eq (triangular_sameThrough_swap π k r s hr' hs') k (by omega) _

noncomputable def adaptiveSwap {n : ℕ} (a : DetAlg n) (k : Fin n) (s : Fin n)
    (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) := by
  classical
  exact match choice a k π with
    | none => π
    | some r => if r ∈ available a k π ∧ s ∈ available a k π then π.trans (Equiv.swap r s) else π

theorem adaptiveSwap_apply {n : ℕ} (a : DetAlg n) (k : Fin n) (s : Fin n)
    (π : Equiv.Perm (Fin n)) (r : Fin n) (hc : choice a k π = some r)
    (hr : r ∈ available a k π) (hs : s ∈ available a k π) :
    adaptiveSwap a k s π = π.trans (Equiv.swap r s) := by
  simp [adaptiveSwap,hc,hr,hs]

theorem adaptiveSwap_involutive {n : ℕ} (a : DetAlg n) (k : Fin n) (s : Fin n) :
    Function.Involutive (adaptiveSwap a k s) := by
  classical
  intro π
  cases hc : choice a k π with
  | none => simp [adaptiveSwap,hc]
  | some r =>
    by_cases h : r ∈ available a k π ∧ s ∈ available a k π
    · have hd := swap_data a k π r s h.1 h.2
      rw [adaptiveSwap_apply a k s π r hc h.1 h.2]
      rw [adaptiveSwap_apply a k s (π.trans (Equiv.swap r s)) r (hd.1.trans hc)
        (hd.2.2 ▸ h.1) (hd.2.2 ▸ h.2)]
      ext x
      simp
    · simp [adaptiveSwap,hc,h]

noncomputable def adaptiveEquiv {n : ℕ} (a : DetAlg n) (k : Fin n) (s : Fin n) :
    Equiv.Perm (Equiv.Perm (Fin n)) :=
  (adaptiveSwap_involutive a k s).toPerm

theorem image_swap_fixed {n : ℕ} (S : Finset (Fin n)) (r s : Fin n)
    (hr : r ∉ S) (hs : s ∉ S) : S.image (Equiv.swap r s) = S := by
  classical
  calc
    S.image (Equiv.swap r s) = S.image id := by
      apply Finset.image_congr
      intro x hx
      exact Equiv.swap_apply_of_ne_of_ne (fun he => hr (he ▸ hx)) (fun he => hs (he ▸ hx))
    _ = S := Finset.image_id

theorem random_swap_unused {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (r s : Fin n) (hr : r ∉ S) (hs : s ∉ S) (t : ℕ) :
    randomValueAux (permutedTriangular (π.trans (Equiv.swap r s))) t (insert r S) =
      randomValueAux (permutedTriangular π) t (insert s S) := by
  have h := random_relabel (Equiv.swap r s) (permutedTriangular π) t (insert s S)
  have heq : relabel (Equiv.swap r s) (permutedTriangular π) =
      permutedTriangular (π.trans (Equiv.swap r s)) := by
    ext e
    simp [relabel,permutedTriangular]
  rw [heq] at h
  simpa only [Finset.image_insert,Equiv.swap_apply_right,image_swap_fixed S r s hr hs] using h

#print axioms adaptiveSwap_involutive
#print axioms random_swap_unused
end KVVMatching.UpperBound.Exposure

open Finset
namespace KVVMatching.UpperBound.Exposure

noncomputable def future {n : ℕ} (a : DetAlg n) (k : Fin n) (t : ℕ)
    (π : Equiv.Perm (Fin n)) (s : Fin n) : ℝ :=
  randomValueAux (permutedTriangular π) t (insert s (matchedRows (permutedTriangular π) a k.val))

noncomputable def chosenFuture {n : ℕ} (a : DetAlg n) (k : Fin n) (t : ℕ)
    (π : Equiv.Perm (Fin n)) : ℝ :=
  match choice a k π with
  | none => 0
  | some r => future a k t π r

theorem greedy_choice {n : ℕ} (a : DetAlg n) (ha : IsGreedy a)
    (k : Fin n) (π : Equiv.Perm (Fin n)) (h : (available a k π).Nonempty) :
    ∃ r ∈ available a k π, choice a k π = some r := ha _ k h

theorem weighted_swap {n : ℕ} (a : DetAlg n) (ha : IsGreedy a) (k : Fin n)
    (t : ℕ) (s : Fin n) (π : Equiv.Perm (Fin n)) :
    (if s ∈ available a k (adaptiveSwap a k s π) then
      chosenFuture a k t (adaptiveSwap a k s π) / ((available a k (adaptiveSwap a k s π)).card : ℝ)
     else 0) =
    (if s ∈ available a k π then future a k t π s / ((available a k π).card : ℝ) else 0) := by
  classical
  by_cases hs : s ∈ available a k π
  · obtain ⟨r,hr,hc⟩ := greedy_choice a ha k π ⟨s,hs⟩
    have hd := swap_data a k π r s hr hs
    rw [adaptiveSwap_apply a k s π r hc hr hs,hd.2.2]
    simp only [if_pos hs,chosenFuture,hd.1,hc]
    congr 1
    unfold future
    rw [hd.2.1]
    exact random_swap_unused π _ r s (Finset.mem_filter.mp hr).2.2
      (Finset.mem_filter.mp hs).2.2 t
  · have he : adaptiveSwap a k s π = π := by
      cases hc : choice a k π <;> simp [adaptiveSwap,hc,hs]
    simp [he,hs]

theorem weighted_sum {n : ℕ} (a : DetAlg n) (ha : IsGreedy a) (k : Fin n)
    (t : ℕ) (s : Fin n) :
    (∑ π : Equiv.Perm (Fin n), if s ∈ available a k π then
      chosenFuture a k t π / ((available a k π).card : ℝ) else 0) =
    ∑ π : Equiv.Perm (Fin n), if s ∈ available a k π then
      future a k t π s / ((available a k π).card : ℝ) else 0 := by
  classical
  let f := fun π : Equiv.Perm (Fin n) => if s ∈ available a k π then
      chosenFuture a k t π / ((available a k π).card : ℝ) else 0
  calc
    (∑ π, f π) = ∑ π, f (adaptiveEquiv a k s π) := (Equiv.sum_comp (adaptiveEquiv a k s) f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro π hπ
      exact weighted_swap a ha k t s π

theorem sum_weights {n : ℕ} (E : Finset (Fin n)) (c : ℝ) :
    (∑ s : Fin n, if s ∈ E then c / (E.card : ℝ) else 0) =
      if E.Nonempty then c else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  by_cases h : E.Nonempty
  · rw [if_pos h]
    have hn : (E.card : ℝ) ≠ 0 := by exact_mod_cast h.card_pos.ne'
    field_simp
  · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he]

theorem choice_average {n : ℕ} (a : DetAlg n) (ha : IsGreedy a) (k : Fin n)
    (t : ℕ) :
    (∑ π : Equiv.Perm (Fin n), if (available a k π).Nonempty then chosenFuture a k t π else 0) =
    ∑ π : Equiv.Perm (Fin n), (∑ s ∈ available a k π, future a k t π s) /
      ((available a k π).card : ℝ) := by
  classical
  calc
    _ = ∑ π : Equiv.Perm (Fin n), ∑ s : Fin n, if s ∈ available a k π then
        chosenFuture a k t π / ((available a k π).card : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro π hπ
      exact (sum_weights _ _).symm
    _ = ∑ s : Fin n, ∑ π : Equiv.Perm (Fin n), if s ∈ available a k π then
        chosenFuture a k t π / ((available a k π).card : ℝ) else 0 := Finset.sum_comm
    _ = ∑ s : Fin n, ∑ π : Equiv.Perm (Fin n), if s ∈ available a k π then
        future a k t π s / ((available a k π).card : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact weighted_sum a ha k t s
    _ = ∑ π : Equiv.Perm (Fin n), ∑ s : Fin n, if s ∈ available a k π then
        future a k t π s / ((available a k π).card : ℝ) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro π hπ
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_div]

#print axioms choice_average
end KVVMatching.UpperBound.Exposure

open Finset
namespace KVVMatching.UpperBound.Exposure

noncomputable def potential {n : ℕ} (a : DetAlg n) (π : Equiv.Perm (Fin n)) (k : ℕ) : ℝ :=
  ((matchedRows (permutedTriangular π) a k).card : ℝ) +
    randomValueAux (permutedTriangular π) (n-k) (matchedRows (permutedTriangular π) a k)

noncomputable def basePotential {n : ℕ} (a : DetAlg n) (π : Equiv.Perm (Fin n)) (k : Fin n) : ℝ :=
  ((matchedRows (permutedTriangular π) a k.val).card : ℝ) +
    if (available a k π).Nonempty then 1 else
      randomValueAux (permutedTriangular π) (n-(k.val+1)) (matchedRows (permutedTriangular π) a k.val)

theorem potential_next {n : ℕ} (a : DetAlg n) (ha : IsGreedy a)
    (π : Equiv.Perm (Fin n)) (k : Fin n) :
    potential a π (k.val+1) = basePotential a π k +
      if (available a k π).Nonempty then chosenFuture a k (n-(k.val+1)) π else 0 := by
  classical
  by_cases he : (available a k π).Nonempty
  · obtain ⟨r,hr,hc⟩ := greedy_choice a ha k π he
    have hstep : matchedRows (permutedTriangular π) a (k.val+1) =
        insert r (matchedRows (permutedTriangular π) a k.val) := by
      simp only [matchedRows,dif_pos k.isLt]
      change (match choice a k π with
        | none => matchedRows (permutedTriangular π) a k.val
        | some r => if r ∈ available a k π then insert r (matchedRows (permutedTriangular π) a k.val)
                    else matchedRows (permutedTriangular π) a k.val) =
          insert r (matchedRows (permutedTriangular π) a k.val)
      simp only [hc,if_pos hr]
    have hn := (Finset.mem_filter.mp hr).2.2
    simp [potential,hstep,Finset.card_insert_of_notMem hn,basePotential,he,chosenFuture,hc,future,
      Nat.cast_add,Nat.cast_one,add_assoc]
  · have hempty : available a k π = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have hstep : matchedRows (permutedTriangular π) a (k.val+1) =
        matchedRows (permutedTriangular π) a k.val := by
      simp only [matchedRows,dif_pos k.isLt]
      change (match choice a k π with
        | none => matchedRows (permutedTriangular π) a k.val
        | some r => if r ∈ available a k π then insert r (matchedRows (permutedTriangular π) a k.val)
                    else matchedRows (permutedTriangular π) a k.val) = _
      cases hc : choice a k π <;> simp [hempty]
    simp [potential,hstep,basePotential,he]

theorem potential_current {n : ℕ} (a : DetAlg n)
    (π : Equiv.Perm (Fin n)) (k : Fin n) :
    potential a π k.val = basePotential a π k +
      (∑ s ∈ available a k π, future a k (n-(k.val+1)) π s) /
        ((available a k π).card : ℝ) := by
  classical
  have hn : n-k.val = (n-(k.val+1))+1 := by omega
  have ht : n-(k.val+1) < n := by omega
  have hk : (⟨n-(k.val+1),ht⟩ : Fin n) = Fin.rev k := by
    apply Fin.ext
    simp only [Fin.val_rev]
  unfold potential
  rw [hn,randomValueAux,dif_pos ht,hk]
  change _ + (if (available a k π).Nonempty then
    1 + (∑ s ∈ available a k π, future a k (n-(k.val+1)) π s) / ((available a k π).card : ℝ)
    else _) = _
  by_cases he : (available a k π).Nonempty
  · simp only [he,if_true,basePotential,future]
    ring
  · have hempty : available a k π = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp [basePotential,hempty]

theorem potential_sum_step {n : ℕ} (a : DetAlg n) (ha : IsGreedy a) (k : Fin n) :
    (∑ π : Equiv.Perm (Fin n), potential a π (k.val+1)) =
      ∑ π : Equiv.Perm (Fin n), potential a π k.val := by
  classical
  simp_rw [potential_next a ha, potential_current]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,choice_average a ha]

theorem potential_sum_const {n : ℕ} (a : DetAlg n) (ha : IsGreedy a) (k : ℕ) (hk : k ≤ n) :
    (∑ π : Equiv.Perm (Fin n), potential a π k) =
      ∑ π : Equiv.Perm (Fin n), potential a π 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (potential_sum_step a ha ⟨k,by omega⟩).trans (ih (by omega))

#print axioms potential_sum_const
end KVVMatching.UpperBound.Exposure

open Finset KVVMatching.UpperBound KVVMatching.UpperBound.Exposure

theorem lemma13 (n : ℕ) (a : DetAlg n) (ha : IsGreedy a) :
    (1 / (n.factorial : ℝ)) *
      (∑ π : Equiv.Perm (Fin n),
        (matchingSize (permutedTriangular π) a : ℝ)) =
      randomValue (upperTriangular n) := by
  classical
  have h := potential_sum_const a ha n (le_refl n)
  have hz : ∀ π : Equiv.Perm (Fin n), potential a π 0 = randomValue (upperTriangular n) := by
    intro π
    simpa [potential,matchedRows,randomValue] using random_triangular π
  have hn : ∀ π : Equiv.Perm (Fin n), potential a π n = (matchingSize (permutedTriangular π) a : ℝ) := by
    intro π
    simp [potential,matchingSize,randomValueAux]
  simp_rw [hz,hn] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul] at h
  rw [h]
  have hpos : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

#print axioms lemma13

open Finset
namespace KVVMatching.UpperBound.Exposure

noncomputable def pick {n : ℕ} (E : Finset (Fin n)) (o : Option (Fin n)) : Option (Fin n) := by
  classical
  exact match o with
  | some r => if r ∈ E then some r else if h : E.Nonempty then some (E.min' h) else none
  | none => if h : E.Nonempty then some (E.min' h) else none

theorem pick_valid {n : ℕ} (E : Finset (Fin n)) (o : Option (Fin n)) (r : Fin n)
    (h : pick E o = some r) : r ∈ E := by
  classical
  cases o with
  | none =>
    by_cases he : E.Nonempty
    · simp only [pick,dif_pos he,Option.some.injEq] at h
      exact h ▸ E.min'_mem he
    · simp [pick,he] at h
  | some u =>
    by_cases hu : u ∈ E
    · simp only [pick,if_pos hu,Option.some.injEq] at h
      exact h ▸ hu
    · by_cases he : E.Nonempty
      · simp only [pick,if_neg hu,dif_pos he,Option.some.injEq] at h
        exact h ▸ E.min'_mem he
      · simp [pick,hu,he] at h

theorem pick_greedy {n : ℕ} (E : Finset (Fin n)) (o : Option (Fin n)) (h : E.Nonempty) :
    ∃ r ∈ E, pick E o = some r := by
  classical
  cases o with
  | none => exact ⟨E.min' h,E.min'_mem h,by simp [pick,h]⟩
  | some u =>
    by_cases hu : u ∈ E
    · exact ⟨u,hu,by simp [pick,hu]⟩
    · exact ⟨E.min' h,E.min'_mem h,by simp [pick,hu,h]⟩

noncomputable def completedRows {n : ℕ} (G : Graph n) (a : DetAlg n) : ℕ → Finset (Fin n)
  | 0 => ∅
  | k+1 =>
    let S := completedRows G a k
    if hk : k < n then
      match pick (eligibleRows G S (Fin.rev ⟨k,hk⟩)) (a ⟨k,hk⟩ (revealedHistory G ⟨k,hk⟩)) with
      | none => S
      | some r => insert r S
    else S

theorem completed_eq {n : ℕ} (a : DetAlg n) {G H : Graph n} (k : ℕ)
    (h : SameThrough G H k) : completedRows G a k = completedRows H a k := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
    have hi := ih (fun j hj r => h j (Nat.lt_succ_of_lt hj) r)
    simp only [completedRows,hi]
    split_ifs with hk
    · rw [history_eq h ⟨k,hk⟩ (show k<k+1 from Nat.lt_succ_self k),
        eligible_eq h ⟨k,hk⟩ (show k<k+1 from Nat.lt_succ_self k)]
    · rfl

noncomputable def graphOf {n : ℕ} (H : History n) : Graph n :=
  {e | ∃ S, H (Fin.rev e.2) = some S ∧ e.1 ∈ S}

theorem graphOf_same {n : ℕ} (G : Graph n) (k : Fin n) :
    SameThrough (graphOf (revealedHistory G k)) G (k.val+1) := by
  classical
  intro j hj r
  have hjk : j ≤ k := Nat.le_of_lt_succ hj
  simp [graphOf,revealedHistory,hjk]

noncomputable def greedify {n : ℕ} (a : DetAlg n) : DetAlg n := fun k H =>
  pick (eligibleRows (graphOf H) (completedRows (graphOf H) a k.val) (Fin.rev k)) (a k H)

theorem greedify_choice {n : ℕ} (a : DetAlg n) (G : Graph n) (k : Fin n) :
    greedify a k (revealedHistory G k) =
      pick (eligibleRows G (completedRows G a k.val) (Fin.rev k)) (a k (revealedHistory G k)) := by
  unfold greedify
  have h := graphOf_same G k
  rw [completed_eq a k.val (fun j hj r => h j (Nat.lt_succ_of_lt hj) r),
    eligible_eq h k (Nat.lt_succ_self k.val)]

theorem greedify_rows {n : ℕ} (a : DetAlg n) (G : Graph n) (k : ℕ) :
    matchedRows G (greedify a) k = completedRows G a k := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [matchedRows,completedRows,ih]
    split_ifs with hk
    · rw [greedify_choice]
      cases he : pick (eligibleRows G (completedRows G a k) (Fin.rev ⟨k,hk⟩))
          (a ⟨k,hk⟩ (revealedHistory G ⟨k,hk⟩)) with
      | none => rfl
      | some r => exact if_pos (pick_valid _ _ r he)
    · rfl

theorem greedify_greedy {n : ℕ} (a : DetAlg n) : IsGreedy (greedify a) := by
  intro G k h
  rw [greedify_rows] at h
  obtain ⟨r,hr,hp⟩ := pick_greedy _ (a k (revealedHistory G k)) h
  refine ⟨r,?_,?_⟩
  · simpa only [greedify_rows] using hr
  · rw [greedify_choice]
    exact hp

theorem completed_grows {n : ℕ} (a : DetAlg n) (G : Graph n) (k : ℕ) :
    completedRows G a k ⊆ completedRows G a (k+1) := by
  classical
  simp only [completedRows]
  split_ifs with hk
  · cases pick (eligibleRows G (completedRows G a k) (Fin.rev ⟨k,hk⟩))
      (a ⟨k,hk⟩ (revealedHistory G ⟨k,hk⟩)) with
    | none => exact Finset.Subset.refl _
    | some r => exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem matched_subset_completed {n : ℕ} (a : DetAlg n) (G : Graph n) (k : ℕ) :
    matchedRows G a k ⊆ completedRows G a k := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
    have hg := completed_grows a G k
    simp only [matchedRows]
    split_ifs with hk
    · cases he : a ⟨k,hk⟩ (revealedHistory G ⟨k,hk⟩) with
      | none => exact ih.trans hg
      | some r =>
        by_cases hr : r ∈ eligibleRows G (matchedRows G a k) (Fin.rev ⟨k,hk⟩)
        · simp only [if_pos hr]
          refine Finset.insert_subset_iff.mpr ⟨?_,ih.trans hg⟩
          by_cases hrc : r ∈ completedRows G a k
          · exact hg hrc
          · have hre : r ∈ eligibleRows G (completedRows G a k) (Fin.rev ⟨k,hk⟩) := by
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hr).2.1,hrc⟩
            simp only [completedRows,dif_pos hk,he,pick,if_pos hre,Finset.mem_insert_self]
        · simp only [if_neg hr]
          exact ih.trans hg
    · simpa only [completedRows,dif_neg hk] using ih

theorem greedify_dominates {n : ℕ} (a : DetAlg n) (G : Graph n) :
    matchingSize G a ≤ matchingSize G (greedify a) := by
  apply Finset.card_le_card
  rw [greedify_rows]
  exact matched_subset_completed a G n

#print axioms greedify_greedy
#print axioms greedify_dominates
end KVVMatching.UpperBound.Exposure

open Finset KVVMatching.UpperBound KVVMatching.UpperBound.Exposure

namespace UniversalMatching

theorem deterministic_bound (n : ℕ) (a : DetAlg n) :
    (∑ π : Equiv.Perm (Fin n), (matchingSize (permutedTriangular π) a : ℝ)) ≤
      (n.factorial : ℝ)*randomValue (upperTriangular n) := by
  classical
  have h := lemma13 n (greedify a) (greedify_greedy a)
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have heq : (∑ π : Equiv.Perm (Fin n), (matchingSize (permutedTriangular π) (greedify a) : ℝ)) =
      (n.factorial : ℝ)*randomValue (upperTriangular n) := by
    field_simp at h
    nlinarith
  rw [← heq]
  apply Finset.sum_le_sum
  intro π hπ
  exact_mod_cast greedify_dominates a (permutedTriangular π)

theorem randomized_sum_bound (n : ℕ) (A : RandomAlg n) :
    (∑ π : Equiv.Perm (Fin n), expectedSize (permutedTriangular π) A) ≤
      (n.factorial : ℝ)*randomValue (upperTriangular n) := by
  classical
  have hm : (∑ a : DetAlg n, (A a).toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ => A.apply_ne_top a)]
    simpa only [tsum_fintype,ENNReal.toReal_one] using congrArg ENNReal.toReal A.tsum_coe
  calc
    _ = ∑ a : DetAlg n, (A a).toReal * ∑ π : Equiv.Perm (Fin n),
        (matchingSize (permutedTriangular π) a : ℝ) := by
      unfold expectedSize
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ a : DetAlg n, (A a).toReal * ((n.factorial : ℝ)*randomValue (upperTriangular n)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (deterministic_bound n a) ENNReal.toReal_nonneg
    _ = _ := by rw [← Finset.sum_mul,hm,one_mul]
end UniversalMatching

theorem prior_finite (n : ℕ) (A : RandomAlg n) :
    ∃ G : Graph n,
      (∃ σ : Fin n ≃ Fin n,
        DiscreteConvex.IntegralConvexityB.IsPerfectMatchingBij G σ) ∧
      expectedSize G A ≤ randomValue (upperTriangular n) := by
  classical
  have h := UniversalMatching.randomized_sum_bound n A
  have hex : ∃ π : Equiv.Perm (Fin n), expectedSize (permutedTriangular π) A ≤
      randomValue (upperTriangular n) := by
    by_contra hn
    push_neg at hn
    have hlt : (∑ _π : Equiv.Perm (Fin n), randomValue (upperTriangular n)) <
        ∑ π : Equiv.Perm (Fin n), expectedSize (permutedTriangular π) A := by
      exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun π _ => hn π)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul] at hlt
    linarith
  obtain ⟨π,hπ⟩ := hex
  refine ⟨permutedTriangular π,⟨π.symm,?_⟩,hπ⟩
  intro u
  exact le_refl (π.symm u)

#print axioms prior_finite

open Finset
noncomputable section
namespace UniformDeletion
variable {X : Type*} [DecidableEq X]
lemma erase_counting (s : Finset X) (k : ℕ) (f : Finset X → ℝ) :
    (∑ E ∈ s.powersetCard (k+1), ∑ r ∈ E, f (E.erase r)) =
      (s.card-k : ℕ) * ∑ T ∈ s.powersetCard k, f T := by
  classical
  rw [Finset.sum_sigma']
  have hbij : (∑ p ∈ (s.powersetCard (k+1)).sigma (fun E => E), f (p.1.erase p.2)) =
      ∑ q ∈ (s.powersetCard k).sigma (fun T => s \ T), f q.1 := by
    apply Finset.sum_bij (fun p _ => ⟨p.1.erase p.2,p.2⟩)
    · intro p hp
      obtain ⟨hE,hr⟩ := mem_sigma.mp hp
      obtain ⟨hEs,hEc⟩ := mem_powersetCard.mp hE
      apply mem_sigma.mpr
      refine ⟨mem_powersetCard.mpr ⟨(erase_subset _ _).trans hEs,?_⟩,?_⟩
      · rw [card_erase_of_mem hr,hEc]; omega
      · exact mem_sdiff.mpr ⟨hEs hr,notMem_erase _ _⟩
    · intro p hp q hq heq
      have h1 : p.1.erase p.2 = q.1.erase q.2 := congrArg Sigma.fst heq
      have h2 : p.2 = q.2 := eq_of_heq (Sigma.mk.inj heq).2
      have hp2 := (mem_sigma.mp hp).2
      have hq2 := (mem_sigma.mp hq).2
      have hE : p.1 = q.1 := by
        rw [← insert_erase hp2,← insert_erase hq2,h1,h2]
      cases p; cases q; simp_all
    · intro q hq
      obtain ⟨hT,hr⟩ := mem_sigma.mp hq
      obtain ⟨hTs,hTc⟩ := mem_powersetCard.mp hT
      obtain ⟨hrs,hrT⟩ := mem_sdiff.mp hr
      refine ⟨⟨insert q.2 q.1,q.2⟩,mem_sigma.mpr ⟨?_,mem_insert_self _ _⟩,?_⟩
      · exact mem_powersetCard.mpr ⟨insert_subset hrs hTs,by rw [card_insert_of_notMem hrT,hTc]⟩
      · simp [erase_insert hrT]
    · intro p hp
      rfl
  rw [hbij, Finset.sum_sigma]
  simp only [sum_const, nsmul_eq_mul]
  rw [mul_sum]
  apply sum_congr rfl
  intro T hT
  rw [card_sdiff_of_subset (mem_powersetCard.mp hT).1,(mem_powersetCard.mp hT).2]
end UniformDeletion

open Finset
noncomputable section
namespace UniformDeletion
variable {X : Type*} [DecidableEq X]
lemma boundary_counting (s : Finset X) (z : X) (hz : z ∈ s) (k : ℕ)
    (f : Finset X → ℝ) :
    (∑ T ∈ s.powersetCard (k+1), f (T.erase z)) =
      (∑ T ∈ (s.erase z).powersetCard (k+1), f T) +
      ∑ T ∈ (s.erase z).powersetCard k, f T := by
  classical
  conv_lhs => rw [← insert_erase hz, powersetCard_succ_insert (notMem_erase z s)]
  rw [sum_union]
  · congr 1
    · apply sum_congr rfl
      intro T hT
      rw [erase_eq_of_notMem]
      exact fun h => (notMem_erase z s) ((mem_powersetCard.mp hT).1 h)
    · rw [sum_image]
      · apply sum_congr rfl
        intro T hT
        rw [erase_insert]
        exact fun h => (notMem_erase z s) ((mem_powersetCard.mp hT).1 h)
      · intro T hT U hU heq
        have hTz : z ∉ T := fun h => (notMem_erase z s) ((mem_powersetCard.mp hT).1 h)
        have hUz : z ∉ U := fun h => (notMem_erase z s) ((mem_powersetCard.mp hU).1 h)
        simpa [erase_insert hTz, erase_insert hUz] using congrArg (fun E => E.erase z) heq
  · apply disjoint_left.mpr
    intro T hT hT'
    obtain ⟨U,hU,rfl⟩ := mem_image.mp hT'
    exact (notMem_erase z s) ((mem_powersetCard.mp hT).1 (mem_insert_self _ _))
end UniformDeletion

open Finset
noncomputable section
namespace KVVMatching.UpperBound.CountProcess
lemma locality {n : ℕ} (t : ℕ) (S T : Finset (Fin n))
    (h : ∀ r : Fin n, r.val < t → (r ∈ S ↔ r ∈ T)) :
    randomValueAux (upperTriangular n) t S = randomValueAux (upperTriangular n) t T := by
  classical
  induction t generalizing S T with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t < n
    · have he : eligibleRows (upperTriangular n) S ⟨t,ht⟩ =
          eligibleRows (upperTriangular n) T ⟨t,ht⟩ := by
        ext r
        simp only [eligibleRows,mem_filter,mem_univ,true_and,upperTriangular,Set.mem_setOf_eq]
        constructor <;> rintro ⟨hr,hs⟩
        · exact ⟨hr,fun hh => hs ((h r (by change r.val ≤ t at hr; omega)).mpr hh)⟩
        · exact ⟨hr,fun hh => hs ((h r (by change r.val ≤ t at hr; omega)).mp hh)⟩
      simp only [randomValueAux,dif_pos ht,he]
      split_ifs
      · congr 1
        congr 1
        apply sum_congr rfl
        intro r hr
        apply ih
        intro q hq
        simp only [mem_insert]
        rw [h q (by omega)]
      · apply ih
        intro r hr
        exact h r (by omega)
    · simp only [randomValueAux,dif_neg ht]

def activeRows (n t : ℕ) : Finset (Fin n) := univ.filter (fun r => r.val < t)
def remainingValue {n : ℕ} (t : ℕ) (E : Finset (Fin n)) : ℝ :=
  randomValueAux (upperTriangular n) t (univ \ E)

lemma eligible_complement {n t : ℕ} (ht : t < n) (E : Finset (Fin n))
    (hE : E ⊆ activeRows n (t+1)) :
    eligibleRows (upperTriangular n) (univ \ E) ⟨t,ht⟩ = E := by
  classical
  ext r
  simp only [eligibleRows,mem_filter,mem_univ,true_and,upperTriangular,Set.mem_setOf_eq,
    mem_sdiff,not_and,true_implies,not_not]
  constructor
  · exact And.right
  · intro hr
    exact ⟨by have := (mem_filter.mp (hE hr)).2; change r.val ≤ t; omega,hr⟩

lemma remaining_next {n t : ℕ} (ht : t < n) (E : Finset (Fin n))
    (hE : E ⊆ activeRows n (t+1)) (hne : E.Nonempty) :
    remainingValue (t+1) E = 1 + (∑ r ∈ E,
      remainingValue t ((E.erase r).erase ⟨t,ht⟩)) / (E.card : ℝ) := by
  classical
  unfold remainingValue
  rw [randomValueAux,dif_pos ht,eligible_complement ht E hE,if_pos hne]
  congr 1
  congr 1
  apply sum_congr rfl
  intro r hr
  apply locality
  intro q hq
  have hqt : q ≠ ⟨t,ht⟩ := by intro he; subst q; simp at hq
  simp only [mem_sdiff,mem_erase,mem_insert,mem_univ,true_and,hqt,true_and]
  tauto

lemma remaining_empty {n : ℕ} (t : ℕ) : remainingValue (n:=n) t ∅ = 0 := by
  classical
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t < n
    · have he : eligibleRows (upperTriangular n) (univ : Finset (Fin n)) ⟨t,ht⟩ = ∅ := by
        ext r; simp [eligibleRows]
      simpa [remainingValue,randomValueAux,ht,he] using ih
    · simp [remainingValue,randomValueAux,ht]
end KVVMatching.UpperBound.CountProcess

open Finset
noncomputable section
namespace KVVMatching.UpperBound.CountProcess
lemma active_erase {n t : ℕ} (ht : t < n) :
    (activeRows n (t+1)).erase ⟨t,ht⟩ = activeRows n t := by
  classical
  ext r
  simp only [activeRows,mem_erase,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨hne,hr⟩
    have : r.val ≠ t := by intro he; apply hne; exact Fin.ext he
    omega
  · intro hr
    exact ⟨by intro he; subst r; simp at hr,by omega⟩
lemma active_card {n t : ℕ} (ht : t ≤ n) : (activeRows n t).card = t := by
  classical
  have he : activeRows n t = (Finset.univ : Finset (Fin t)).image
      (fun r => (⟨r.val,lt_of_lt_of_le r.isLt ht⟩ : Fin n)) := by
    ext r
    simp only [activeRows,mem_filter,mem_univ,true_and,mem_image]
    constructor
    · intro hr
      exact ⟨⟨r.val,hr⟩,rfl⟩
    · rintro ⟨s,hs⟩
      have := congrArg Fin.val hs
      simpa [← this] using s.isLt
  rw [he,card_image_of_injective]
  · simp
  · intro a b heq
    exact Fin.ext (congrArg (Fin.val (n:=n)) heq)

def aggregate (n t k : ℕ) : ℝ :=
  ∑ E ∈ (activeRows n t).powersetCard k, remainingValue t E

lemma aggregate_zero (n t : ℕ) : aggregate n t 0 = 0 := by
  simp [aggregate,remaining_empty]
lemma aggregate_time_zero (n k : ℕ) : aggregate n 0 k = 0 := by
  simp [aggregate,remainingValue,randomValueAux]

lemma aggregate_step {n t k : ℕ} (ht : t < n) :
    aggregate n (t+1) (k+1) = ((t+1).choose (k+1) : ℝ) +
      ((t+1-k : ℕ) : ℝ) / (k+1) *
        (∑ T ∈ (activeRows n (t+1)).powersetCard k,
          remainingValue t (T.erase ⟨t,ht⟩)) := by
  classical
  unfold aggregate
  have hs : (∑ E ∈ (activeRows n (t+1)).powersetCard (k+1), remainingValue (t+1) E) =
      ∑ E ∈ (activeRows n (t+1)).powersetCard (k+1),
        (1 + (∑ r ∈ E, remainingValue t ((E.erase r).erase ⟨t,ht⟩)) / (k+1)) := by
    apply sum_congr rfl
    intro E hE
    obtain ⟨hEs,hEc⟩ := mem_powersetCard.mp hE
    have hne : E.Nonempty := card_pos.mp (by omega)
    rw [remaining_next ht E hEs hne,hEc]
    simp
  rw [hs,sum_add_distrib,← sum_div,UniformDeletion.erase_counting
    (activeRows n (t+1)) k (fun T => remainingValue t (T.erase ⟨t,ht⟩))]
  simp only [sum_const,card_powersetCard,nsmul_eq_mul,mul_one,active_card (by omega : t+1 ≤ n)]
  ring

lemma aggregate_one {n t : ℕ} (ht : t < n) : aggregate n (t+1) 1 = t+1 := by
  rw [show 1=0+1 from rfl,aggregate_step ht]
  simp [remaining_empty]

lemma aggregate_two_step {n t k : ℕ} (ht : t < n) :
    aggregate n (t+1) (k+2) = ((t+1).choose (k+2) : ℝ) +
      ((t-k : ℕ) : ℝ) / (k+2) * (aggregate n t (k+1) + aggregate n t k) := by
  have hz : (⟨t,ht⟩ : Fin n) ∈ activeRows n (t+1) := by simp [activeRows]
  rw [show k+2=(k+1)+1 by omega,aggregate_step ht,
    UniformDeletion.boundary_counting _ _ hz k (remainingValue t),active_erase ht]
  simp only [aggregate,Nat.add_sub_add_right,Nat.cast_add,Nat.cast_one]
  congr 2 <;> ring

end KVVMatching.UpperBound.CountProcess

open Finset
noncomputable section
namespace KVVMatching.UpperBound.CountProcess
/-- The sum of expected matching sizes over all k-subsets of the active t rows.
    Dividing by t.choose k gives the uniform-subset expectation when k≤t. -/
def countTotal : ℕ → ℕ → ℝ
  | 0, _ => 0
  | t+1, 0 => 0
  | t+1, 1 => t+1
  | t+1, k+2 => ((t+1).choose (k+2) : ℝ) +
      ((t-k : ℕ) : ℝ) / (k+2) * (countTotal t (k+1) + countTotal t k)

lemma aggregate_eq_total (n t k : ℕ) (ht : t ≤ n) : aggregate n t k = countTotal t k := by
  induction t generalizing k with
  | zero => exact aggregate_time_zero n k
  | succ t ih =>
    cases k with
    | zero => exact aggregate_zero n (t+1)
    | succ k =>
      cases k with
      | zero => exact aggregate_one (by omega)
      | succ k =>
        rw [show k+1+1=k+2 by omega,aggregate_two_step (by omega),countTotal,
          ih (k+1) (by omega),ih k (by omega)]

/-- Exact finite recurrence for the platform's RANDOM value on the complete
    upper-triangular graph. The asymptotic limit is a separate obligation. -/
theorem randomValue_eq_countTotal (n : ℕ) :
    randomValue (upperTriangular n) = countTotal n n := by
  have h := aggregate_eq_total n n n le_rfl
  have he : activeRows n n = univ := by ext r; simp [activeRows]
  have hc : (univ : Finset (Fin n)).card = n := by simp
  have hp : (univ : Finset (Fin n)).powersetCard n = {univ} := by
    simpa only [hc] using powersetCard_self (univ : Finset (Fin n))
  simpa only [aggregate,he,hp,sum_singleton,remainingValue,sdiff_self,Finset.bot_eq_empty,randomValue] using h
end KVVMatching.UpperBound.CountProcess

namespace KVVMatching.UpperBound.CountProcess
/-- Expected number of future matches when the k eligible rows are uniform
    among t currently active rows. -/
noncomputable def countValue : ℕ → ℕ → ℝ
  | 0, _ => 0
  | t+1, 0 => 0
  | t+1, 1 => 1
  | t+1, k+2 => 1 + ((k+1 : ℕ) : ℝ) / (t+1) * countValue t k +
      ((t-k : ℕ) : ℝ) / (t+1) * countValue t (k+1)

lemma total_eq_countValue (t k : ℕ) (hk : k ≤ t) :
    countTotal t k = (t.choose k : ℝ) * countValue t k := by
  induction t generalizing k with
  | zero => simp [countTotal,countValue]
  | succ t ih =>
    cases k with
    | zero => simp [countTotal,countValue]
    | succ k =>
      cases k with
      | zero => simp [countTotal,countValue]
      | succ k =>
        have hk1 : k+1 ≤ t := by omega
        have hk0 : k ≤ t := by omega
        have hchoose1 : ((t+1 : ℕ) : ℝ) * (t.choose (k+1) : ℝ) =
            ((t+1).choose (k+2) : ℝ) * (k+2) := by
          exact_mod_cast Nat.add_one_mul_choose_eq t (k+1)
        have hchoose2 : (t.choose (k+1) : ℝ) * (k+1) =
            (t.choose k : ℝ) * ((t-k : ℕ) : ℝ) := by
          exact_mod_cast Nat.choose_succ_right_eq t k
        push_cast at hchoose1
        have htpos : (t+1 : ℝ) ≠ 0 := by positivity
        have hkpos : (k+2 : ℝ) ≠ 0 := by positivity
        have hcoef1 : ((t-k : ℕ) : ℝ) / (k+2) * (t.choose (k+1) : ℝ) =
            ((t+1).choose (k+2) : ℝ) * (((t-k : ℕ) : ℝ) / (t+1)) := by
          field_simp [htpos,hkpos]
          nlinarith [congrArg (fun z : ℝ => z * ((t-k : ℕ) : ℝ)) hchoose1]
        have hcoef2 : ((t-k : ℕ) : ℝ) / (k+2) * (t.choose k : ℝ) =
            ((t+1).choose (k+2) : ℝ) * ((k+1 : ℝ) / (t+1)) := by
          field_simp [htpos,hkpos]
          nlinarith [congrArg (fun z : ℝ => z * (k+1)) hchoose1,
            congrArg (fun z : ℝ => z * (t+1)) hchoose2]
        simp only [countTotal,countValue,ih (k+1) hk1,ih k hk0]
        rw [mul_add,← mul_assoc,← mul_assoc,hcoef1,hcoef2]
        push_cast
        ring

 theorem randomValue_eq_countValue (n : ℕ) :
    randomValue (upperTriangular n) = countValue n n := by
  rw [randomValue_eq_countTotal,total_eq_countValue n n le_rfl]
  simp
end KVVMatching.UpperBound.CountProcess

open Finset
namespace KVVMatching.UpperBound.CountProcess
noncomputable def countStep (v : ℕ → ℝ) (t : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | k+2 => 1 + ((k+1 : ℕ) : ℝ) / (t+1) * v k +
      ((t-k : ℕ) : ℝ) / (t+1) * v (k+1)
lemma countValue_step (t k : ℕ) : countValue (t+1) k = countStep (countValue t) t k := by
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

lemma countStep_nonexpansive (v w : ℕ → ℝ) (t k : ℕ) (hk : k ≤ t+1)
    (B : ℝ) (hB : 0 ≤ B) (h : ∀ j ≤ t, |v j-w j| ≤ B) :
    |countStep v t k-countStep w t k| ≤ B := by
  cases k with
  | zero => simpa [countStep] using hB
  | succ k =>
    cases k with
    | zero => simpa [countStep] using hB
    | succ k =>
      have hk1 : k+1 ≤ t := by omega
      have hcast : ((t-k : ℕ) : ℝ) = (t:ℝ)-k := by rw [Nat.cast_sub (by omega)]
      have hp : 0 ≤ ((k+1 : ℕ) : ℝ) / (t+1) := by positivity
      have hq : 0 ≤ ((t-k : ℕ) : ℝ) / (t+1) := by positivity
      have hpq : ((k+1 : ℕ) : ℝ) / (t+1) + ((t-k : ℕ) : ℝ) / (t+1) = 1 := by
        rw [hcast]
        push_cast
        field_simp
        ring
      change |(1 + ((k+1 : ℕ) : ℝ) / (t+1) * v k + ((t-k : ℕ) : ℝ) / (t+1) * v (k+1)) -
        (1 + ((k+1 : ℕ) : ℝ) / (t+1) * w k + ((t-k : ℕ) : ℝ) / (t+1) * w (k+1))| ≤ B
      have heq : (1 + ((k+1 : ℕ) : ℝ) / (t+1) * v k + ((t-k : ℕ) : ℝ) / (t+1) * v (k+1)) -
        (1 + ((k+1 : ℕ) : ℝ) / (t+1) * w k + ((t-k : ℕ) : ℝ) / (t+1) * w (k+1)) =
        ((k+1 : ℕ) : ℝ) / (t+1) * (v k-w k) + ((t-k : ℕ) : ℝ) / (t+1) * (v (k+1)-w (k+1)) := by ring
      rw [heq]
      calc
        _ ≤ |((k+1 : ℕ) : ℝ) / (t+1) * (v k-w k)| +
          |((t-k : ℕ) : ℝ) / (t+1) * (v (k+1)-w (k+1))| := abs_add_le _ _
        _ = ((k+1 : ℕ) : ℝ) / (t+1) * |v k-w k| +
          ((t-k : ℕ) : ℝ) / (t+1) * |v (k+1)-w (k+1)| := by rw [abs_mul,abs_mul,abs_of_nonneg hp,abs_of_nonneg hq]
        _ ≤ ((k+1 : ℕ) : ℝ) / (t+1) * B + ((t-k : ℕ) : ℝ) / (t+1) * B :=
          add_le_add (mul_le_mul_of_nonneg_left (h k (by omega)) hp)
            (mul_le_mul_of_nonneg_left (h (k+1) hk1) hq)
        _ = B := by rw [← add_mul,hpq,one_mul]

/-- Accumulated one-step residuals control the exact finite RANDOM value. -/
theorem approximation_bound (v : ℕ → ℕ → ℝ) (ε : ℕ → ℝ)
    (hε : ∀ t, 0 ≤ ε t) (hv : v 0 0 = 0)
    (hr : ∀ t k, k ≤ t+1 → |countStep (v t) t k-v (t+1) k| ≤ ε t)
    (t k : ℕ) (hk : k ≤ t) :
    |countValue t k-v t k| ≤ ∑ j ∈ range t, ε j := by
  induction t generalizing k with
  | zero =>
    have : k=0 := by omega
    subst k
    simp [countValue,hv]
  | succ t ih =>
    rw [countValue_step,sum_range_succ]
    calc
      _ ≤ |countStep (countValue t) t k-countStep (v t) t k| +
        |countStep (v t) t k-v (t+1) k| := abs_sub_le _ _ _
      _ ≤ (∑ j ∈ range t, ε j) + ε t := add_le_add
        (countStep_nonexpansive _ _ t k hk _ (sum_nonneg (fun j _ => hε j))
          (fun j hj => ih j hj)) (hr t k hk)
end KVVMatching.UpperBound.CountProcess

open Finset
namespace KVVMatching.UpperBound.CountProcess
lemma exp_mix (p y : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    |(1-p)*Real.exp (-p*y)+p*Real.exp ((1-p)*y)-1| ≤ y^2 := by
  have hu : |-p*y| ≤ y := by rw [abs_mul,abs_neg,abs_of_nonneg hp,abs_of_nonneg hy]; nlinarith
  have hv : |(1-p)*y| ≤ y := by rw [abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1-p),abs_of_nonneg hy]; nlinarith
  have h1 := Real.abs_exp_sub_one_sub_id_le (hu.trans hy1)
  have h2 := Real.abs_exp_sub_one_sub_id_le (hv.trans hy1)
  have hs1 : (-p*y)^2 ≤ y^2 := by nlinarith [sq_abs (-p*y)]
  have hs2 : ((1-p)*y)^2 ≤ y^2 := by nlinarith [sq_abs ((1-p)*y)]
  have heq : (1-p)*Real.exp (-p*y)+p*Real.exp ((1-p)*y)-1 =
      (1-p)*(Real.exp (-p*y)-1-(-p*y))+p*(Real.exp ((1-p)*y)-1-(1-p)*y) := by ring
  rw [heq]
  calc
    _ ≤ |(1-p)*(Real.exp (-p*y)-1-(-p*y))|+|p*(Real.exp ((1-p)*y)-1-(1-p)*y)| := abs_add_le _ _
    _ = (1-p)*|Real.exp (-p*y)-1-(-p*y)|+p*|Real.exp ((1-p)*y)-1-(1-p)*y| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hp,abs_of_nonneg (by linarith : 0 ≤ 1-p)]
    _ ≤ (1-p)*y^2+p*y^2 := add_le_add
      (mul_le_mul_of_nonneg_left (h1.trans hs1) (by linarith)) (mul_le_mul_of_nonneg_left (h2.trans hs2) hp)
    _ = y^2 := by ring

lemma exp_scalar_error (t p : ℝ) (ht : 1 ≤ t) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    |Real.exp (-p) * ((t+1)*Real.exp (-(1/(t+1))) -
      t*((1-p)*Real.exp (-p*(1/t))+p*Real.exp ((1-p)*(1/t))))| ≤ 1/(t+1)+1/t := by
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < t+1 := by linarith
  have hy : 0 ≤ 1/t := by positivity
  have hy1 : 1/t ≤ 1 := (div_le_one ht0).mpr ht
  have hx : |-(1/(t+1))| ≤ 1 := by
    rw [abs_neg,abs_of_nonneg (by positivity : 0 ≤ 1/(t+1))]
    exact (div_le_one hx0).mpr (by linarith)
  have hmix := exp_mix p (1/t) hp hp1 hy hy1
  have he := Real.abs_exp_sub_one_sub_id_le hx
  have hT : |(t+1)*Real.exp (-(1/(t+1)))-t| ≤ 1/(t+1) := by
    have heq : (t+1)*Real.exp (-(1/(t+1)))-t =
      (t+1)*(Real.exp (-(1/(t+1)))-1-(-(1/(t+1)))) := by field_simp <;> ring
    rw [heq,abs_mul,abs_of_pos hx0]
    calc
      _ ≤ (t+1)*(-(1/(t+1)))^2 := mul_le_mul_of_nonneg_left he hx0.le
      _ = 1/(t+1) := by field_simp <;> ring
  have hM : |t*((1-p)*Real.exp (-p*(1/t))+p*Real.exp ((1-p)*(1/t)))-t| ≤ 1/t := by
    rw [← mul_sub_one,abs_mul,abs_of_pos ht0]
    calc
      _ ≤ t*(1/t)^2 := mul_le_mul_of_nonneg_left hmix ht0.le
      _ = 1/t := by field_simp <;> ring
  have hexp : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ |(t+1)*Real.exp (-(1/(t+1))) -
      t*((1-p)*Real.exp (-p*(1/t))+p*Real.exp ((1-p)*(1/t)))| := mul_le_of_le_one_left (abs_nonneg _) hexp
    _ ≤ |(t+1)*Real.exp (-(1/(t+1)))-t| +
      |t-t*((1-p)*Real.exp (-p*(1/t))+p*Real.exp ((1-p)*(1/t)))| := abs_sub_le _ _ _
    _ ≤ 1/(t+1)+1/t := by rw [abs_sub_comm t]; exact add_le_add hT hM
end KVVMatching.UpperBound.CountProcess

namespace KVVMatching.UpperBound.CountProcess
noncomputable def fluidValue (t k : ℕ) : ℝ :=
  (t:ℝ)*(1-Real.exp (-(k:ℝ)/(t:ℝ)))
lemma fluid_zero (t : ℕ) : fluidValue t 0 = 0 := by simp [fluidValue]

lemma fluid_step_error (t k : ℕ) (ht : 1 ≤ t) (hk : k ≤ t+1) :
    |countStep (fluidValue t) t k-fluidValue (t+1) k| ≤
      1/((t:ℝ)+1)+1/(t:ℝ) := by
  have htR : (1:ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0:ℝ) < t := by linarith
  have hxpos : (0:ℝ) < (t:ℝ)+1 := by linarith
  cases k with
  | zero => simp [countStep,fluid_zero]; positivity
  | succ k =>
    cases k with
    | zero =>
      have h := exp_scalar_error (t:ℝ) 0 htR le_rfl (by norm_num)
      simp only [neg_zero,zero_mul,Real.exp_zero,one_mul,sub_zero,mul_zero,add_zero] at h
      convert h using 1 <;> simp only [countStep,fluidValue,Nat.cast_add,Nat.cast_one]
      congr 1
      ring
    | succ k =>
      have hkt : k ≤ t := by omega
      let p : ℝ := ((k:ℝ)+1)/((t:ℝ)+1)
      have hp : 0 ≤ p := by dsimp [p]; positivity
      have hp1 : p ≤ 1 := by
        apply (div_le_one hxpos).mpr
        have : (k:ℝ) ≤ t := by exact_mod_cast hkt
        linarith
      have e0 : -(k:ℝ)/(t:ℝ) = -p+(1-p)*(1/(t:ℝ)) := by
        dsimp [p]; field_simp [htpos.ne',hxpos.ne'] <;> ring
      have e1 : -((k:ℝ)+1)/(t:ℝ) = -p+ -p*(1/(t:ℝ)) := by
        dsimp [p]; field_simp [htpos.ne',hxpos.ne'] <;> ring
      have e2 : -((k:ℝ)+1+1)/((t:ℝ)+1) = -p+ -(1/((t:ℝ)+1)) := by
        dsimp [p]; field_simp [hxpos.ne'] <;> ring
      have hc : ((t-k:ℕ):ℝ)/((t:ℝ)+1) = 1-p := by
        rw [Nat.cast_sub hkt]
        dsimp [p]; field_simp [hxpos.ne'] <;> ring
      have heq : countStep (fluidValue t) t (k+1+1)-fluidValue (t+1) (k+1+1) =
          Real.exp (-p) * (((t:ℝ)+1)*Real.exp (-(1/((t:ℝ)+1))) -
          (t:ℝ)*((1-p)*Real.exp (-p*(1/(t:ℝ)))+p*Real.exp ((1-p)*(1/(t:ℝ))))) := by
        simp only [countStep,fluidValue,Nat.cast_add,Nat.cast_one]
        rw [e0,e1,e2,hc]
        simp only [Real.exp_add]
        change 1+p*((t:ℝ)*(1-Real.exp (-p)*Real.exp ((1-p)*(1/(t:ℝ)))))+
          (1-p)*((t:ℝ)*(1-Real.exp (-p)*Real.exp (-p*(1/(t:ℝ)))))-
          ((t:ℝ)+1)*(1-Real.exp (-p)*Real.exp (-(1/((t:ℝ)+1)))) = _
        ring
      rw [heq]
      exact exp_scalar_error (t:ℝ) p htR hp hp1
end KVVMatching.UpperBound.CountProcess

open Filter Topology Finset
noncomputable section
namespace KVVMatching.UpperBound.CountProcess
def errorBudget (t : ℕ) : ℝ := if t=0 then 1 else 1/((t:ℝ)+1)+1/(t:ℝ)
lemma errorBudget_nonneg (t : ℕ) : 0 ≤ errorBudget t := by
  unfold errorBudget
  split_ifs <;> positivity
lemma fluid_residual (t k : ℕ) (hk : k ≤ t+1) :
    |countStep (fluidValue t) t k-fluidValue (t+1) k| ≤ errorBudget t := by
  by_cases ht : t=0
  · subst t
    have hk01 : k=0 ∨ k=1 := by omega
    rcases hk01 with rfl | rfl
    · simp [errorBudget,countStep,fluid_zero]
    · simpa [countStep,fluidValue,errorBudget,abs_of_pos (Real.exp_pos (-1))] using
        (Real.exp_le_one_iff.mpr (show (-1:ℝ) ≤ 0 by norm_num))
  · simpa [errorBudget,ht] using fluid_step_error t k (by omega) hk

lemma value_error (n : ℕ) :
    |randomValue (upperTriangular n)-fluidValue n n| ≤ ∑ j ∈ range n, errorBudget j := by
  rw [randomValue_eq_countValue]
  exact approximation_bound fluidValue errorBudget errorBudget_nonneg (by simp [fluidValue])
    fluid_residual n n le_rfl

lemma errorBudget_tendsto : Tendsto errorBudget atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs := hi.comp (tendsto_add_atTop_nat 1)
  have hh := hi.add hs
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp [errorBudget,show n ≠ 0 by omega,Nat.cast_add,Nat.cast_one,one_div,add_comm]
end KVVMatching.UpperBound.CountProcess

open KVVMatching.UpperBound KVVMatching.UpperBound.CountProcess
 theorem triangular_limit :
    Tendsto (fun n : ℕ => randomValue (upperTriangular n)/(n:ℝ)) atTop (𝓝 (1-Real.exp (-1))) := by
  have hb : Tendsto (fun n : ℕ => (∑ j ∈ range n, errorBudget j)/(n:ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv,mul_comm] using errorBudget_tendsto.cesaro
  have he : Tendsto (fun n : ℕ => |randomValue (upperTriangular n)/(n:ℝ)-(1-Real.exp (-1))|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun n => abs_nonneg _)) ?_ hb
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have hfluid : fluidValue n n = (n:ℝ)*(1-Real.exp (-1)) := by
      unfold fluidValue
      rw [neg_div,div_self hn0.ne']
    have hh := div_le_div_of_nonneg_right (value_error n) hn0.le
    rw [hfluid] at hh
    have heq : randomValue (upperTriangular n)/(n:ℝ)-(1-Real.exp (-1)) =
        (randomValue (upperTriangular n)-(n:ℝ)*(1-Real.exp (-1)))/(n:ℝ) := by
      field_simp
    rw [heq,abs_div,abs_of_pos hn0]
    exact hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using he)

open Filter Topology
open KVVMatching.UpperBound
 theorem solution :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : RandomAlg n, ∃ G : Graph n,
        (∃ σ : Fin n ≃ Fin n,
          DiscreteConvex.IntegralConvexityB.IsPerfectMatchingBij G σ) ∧
        expectedSize G A ≤ (1 - Real.exp (-1) + ε) * (n : ℝ) := by
  intro ε hε
  have he := (tendsto_order.mp triangular_limit).2 (1-Real.exp (-1)+ε) (by linarith)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨max N 1,fun n hn A => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  obtain ⟨G,hG,hbound⟩ := prior_finite n A
  exact ⟨G,hG,hbound.trans (le_of_lt ((div_lt_iff₀ hnpos).mp (hN n hnN)))⟩
