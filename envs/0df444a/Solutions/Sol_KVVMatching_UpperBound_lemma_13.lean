-- Prove2me | solution 1 for KVVMatching.UpperBound.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T18:35:16.79999+00:00
-- url     : https://prove2.me/submissions/93729b85-8ed1-4387-9324-245f1fd68a80

import Init
import Definitions.Def_KVVMatching_UpperBound_RandomValue
import Definitions.Def_KVVMatching_UpperBound_Triangular

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

theorem solution (n : ℕ) (a : DetAlg n) (ha : IsGreedy a) :
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

#print axioms solution
