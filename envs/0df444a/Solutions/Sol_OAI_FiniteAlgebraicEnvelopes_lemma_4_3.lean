-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T15:55:44.839695+00:00
-- url     : https://prove2.me/submissions/80e556b1-8b23-446b-93ee-1751ce3ec68f

import Mathlib
import Definitions.Def_BooneHigman_Steinberg
import Definitions.Def_BooneHigman_cornerSub
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_4_2
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_4_2_corollary

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

variable {n : ℕ} {R : Type u} [Ring R]

-- Small helpers reproduced from the Lemma 4.2 solution (not published separately).

theorem steinberg_x_add (i j : Fin n) (hij : i ≠ j) (a b : R) :
    SteinbergGroup.x i j hij a * SteinbergGroup.x i j hij b = SteinbergGroup.x i j hij (a + b) := by
  have hmem : steinAddRelator (⟨i, j, hij, a, b⟩ : SteinAddParam n R) ∈ steinRelations n R :=
    Or.inl (Or.inl (Set.mem_range_self _))
  have h1 := PresentedGroup.one_of_mem hmem
  unfold steinAddRelator at h1
  simp only [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

theorem steinberg_x_chain (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    SteinbergGroup.x i j hij a * SteinbergGroup.x j k hjk b *
        (SteinbergGroup.x i j hij a)⁻¹ * (SteinbergGroup.x j k hjk b)⁻¹ =
      SteinbergGroup.x i k hik (a * b) := by
  have hmem : steinChainRelator (⟨i, j, k, hij, hjk, hik, a, b⟩ : SteinChainParam n R) ∈
      steinRelations n R := Or.inl (Or.inr (Set.mem_range_self _))
  have h1 := PresentedGroup.one_of_mem hmem
  unfold steinChainRelator at h1
  simp only [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

theorem steinberg_x_zero (i j : Fin n) (hij : i ≠ j) :
    SteinbergGroup.x i j hij (0 : R) = 1 := by
  have h := steinberg_x_add i j hij (0 : R) (0 : R)
  rw [add_zero] at h
  calc SteinbergGroup.x i j hij (0 : R)
      = (SteinbergGroup.x i j hij (0 : R))⁻¹ *
        (SteinbergGroup.x i j hij (0 : R) * SteinbergGroup.x i j hij (0 : R)) := by group
    _ = (SteinbergGroup.x i j hij (0 : R))⁻¹ * SteinbergGroup.x i j hij (0 : R) := by rw [h]
    _ = 1 := by group

theorem steinberg_x_inv (i j : Fin n) (hij : i ≠ j) (a : R) :
    (SteinbergGroup.x i j hij a)⁻¹ = SteinbergGroup.x i j hij (-a) := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, steinberg_x_add, neg_add_cancel, steinberg_x_zero]

theorem columnElem_congr (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (c1 c2 : Fin n → R) (h : ∀ i ∈ J, c1 i = c2 i) :
    columnElem J k hk c1 = columnElem J k hk c2 := by
  unfold columnElem
  refine Finset.noncommProd_congr rfl (fun i hi => ?_) _
  simp only [dif_pos (hk i hi), h i hi]

theorem rowElem_congr (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (r1 r2 : Fin n → R) (h : ∀ i ∈ J, r1 i = r2 i) :
    rowElem J k hk r1 = rowElem J k hk r2 := by
  unfold rowElem
  refine Finset.noncommProd_congr rfl (fun i hi => ?_) _
  simp only [dif_pos (hk i hi), h i hi]

theorem columnElem_single (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (i : Fin n) (hi : i ∈ J) (a : R) :
    columnElem J k hk (Function.update (0 : Fin n → R) i a) =
      SteinbergGroup.x i k (hk i hi) a := by
  classical
  set f : Fin n → SteinbergGroup n R := fun i' => if h : i' ≠ k then SteinbergGroup.x i' k h
      ((Function.update (0 : Fin n → R) i a) i') else 1 with hf_def
  have comm : (↑J : Set (Fin n)).Pairwise (Function.onFun Commute f) := by
    intro i' hi' j' hj' hij'
    simp only [Function.onFun, hf_def, dif_pos (hk i' hi'), dif_pos (hk j' hj')]
    exact steinberg_col_commute k (hk i' hi') (hk j' hj') hij' _ _
  show J.noncommProd f comm = SteinbergGroup.x i k (hk i hi) a
  rw [← Finset.mul_noncommProd_erase J hi f comm]
  have hrest : (J.erase i).noncommProd f
      (fun _ hx _ hy hxy => comm (J.mem_of_mem_erase hx) (J.mem_of_mem_erase hy) hxy) = 1 := by
    refine (Finset.noncommProd_eq_pow_card _ _ _ 1 (fun x hx => ?_)).trans (one_pow _)
    have hxne : x ≠ i := (Finset.mem_erase.mp hx).1
    have hx0 : (Function.update (0 : Fin n → R) i a) x = 0 := by
      rw [Function.update_of_ne hxne]; rfl
    show (if h : x ≠ k then SteinbergGroup.x x k h
      ((Function.update (0 : Fin n → R) i a) x) else 1) = 1
    rw [hx0]
    by_cases h : x ≠ k
    · rw [dif_pos h, steinberg_x_zero]
    · rw [dif_neg h]
  rw [hrest, mul_one]
  show (if h : i ≠ k then SteinbergGroup.x i k h ((Function.update (0 : Fin n → R) i a) i)
    else 1) = SteinbergGroup.x i k (hk i hi) a
  rw [dif_pos (hk i hi), Function.update_self]

theorem rowElem_single (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (i : Fin n) (hi : i ∈ J) (a : R) :
    rowElem J k hk (Function.update (0 : Fin n → R) i a) =
      SteinbergGroup.x k i (hk i hi).symm a := by
  classical
  set f : Fin n → SteinbergGroup n R := fun i' => if h : i' ≠ k then SteinbergGroup.x k i' h.symm
      ((Function.update (0 : Fin n → R) i a) i') else 1 with hf_def
  have comm : (↑J : Set (Fin n)).Pairwise (Function.onFun Commute f) := by
    intro i' hi' j' hj' hij'
    simp only [Function.onFun, hf_def, dif_pos (hk i' hi'), dif_pos (hk j' hj')]
    exact steinberg_row_commute k (hk i' hi') (hk j' hj') hij' _ _
  show J.noncommProd f comm = SteinbergGroup.x k i (hk i hi).symm a
  rw [← Finset.mul_noncommProd_erase J hi f comm]
  have hrest : (J.erase i).noncommProd f
      (fun _ hx _ hy hxy => comm (J.mem_of_mem_erase hx) (J.mem_of_mem_erase hy) hxy) = 1 := by
    refine (Finset.noncommProd_eq_pow_card _ _ _ 1 (fun x hx => ?_)).trans (one_pow _)
    have hxne : x ≠ i := (Finset.mem_erase.mp hx).1
    have hx0 : (Function.update (0 : Fin n → R) i a) x = 0 := by
      rw [Function.update_of_ne hxne]; rfl
    show (if h : x ≠ k then SteinbergGroup.x k x h.symm
      ((Function.update (0 : Fin n → R) i a) x) else 1) = 1
    rw [hx0]
    by_cases h : x ≠ k
    · rw [dif_pos h, steinberg_x_zero]
    · rw [dif_neg h]
  rw [hrest, mul_one]
  show (if h : i ≠ k then SteinbergGroup.x k i h.symm ((Function.update (0 : Fin n → R) i a) i)
    else 1) = SteinbergGroup.x k i (hk i hi).symm a
  rw [dif_pos (hk i hi), Function.update_self]

theorem commute_of_conj_self {G : Type*} [Group G] {w g : G} (h : w * g * w⁻¹ = g) :
    Commute w g := by
  show w * g = g * w
  calc w * g = w * g * w⁻¹ * w := by group
    _ = g * w := by rw [h]

section Lemma43Setup

variable (E F d dstar : R) {p q : Fin n} (hpq : p ≠ q)

theorem single_neg (i j : Fin n) (a : R) :
    Matrix.single i j (-a) = -Matrix.single i j a := by
  have h0 : Matrix.single i j a + Matrix.single i j (-a) = 0 := by
    rw [← Matrix.single_add, add_neg_cancel, Matrix.single_zero]
  exact eq_neg_of_add_eq_zero_right h0

/-- The matrix of `W = x_pq(d) x_qp(-d*) x_pq(d)` from the proof of Lemma 4.3. -/
theorem W_matrix (hF : F * F = F) (hd : d = F * d * E)
    (hdstard : dstar * d = E) (hddstar : d * dstar = F) :
    (steinPi (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) : Matrix (Fin n) (Fin n) R) =
      1 - Matrix.single p p F - Matrix.single q q E +
        Matrix.single p q d - Matrix.single q p dstar := by
  have hFd : F * d = d := by rw [hd]; rw [← mul_assoc, ← mul_assoc, hF]
  rw [map_mul, map_mul, steinPi_x, steinPi_x, Units.val_mul, Units.val_mul]
  show (1 + Matrix.single p q d) * (1 + Matrix.single q p (-dstar)) *
      (1 + Matrix.single p q d) =
    1 - Matrix.single p p F - Matrix.single q q E +
      Matrix.single p q d - Matrix.single q p dstar
  rw [single_neg]
  have step1 : (1 + Matrix.single p q d) * (1 + (-Matrix.single q p dstar)) =
      1 + (-Matrix.single q p dstar) + Matrix.single p q d - Matrix.single p p F := by
    rw [mul_add, mul_one, mul_neg, add_mul, one_mul,
      Matrix.single_mul_single_same]
    rw [hddstar]
    abel
  rw [step1]
  have hcross : (1 + (-Matrix.single q p dstar) + Matrix.single p q d - Matrix.single p p F) *
      Matrix.single p q d = - Matrix.single q q E := by
    rw [sub_mul, add_mul, add_mul, one_mul, neg_mul,
      Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne (h := hpq.symm),
      Matrix.single_mul_single_same, hdstard, hFd]
    abel
  calc (1 + (-Matrix.single q p dstar) + Matrix.single p q d - Matrix.single p p F) *
      (1 + Matrix.single p q d)
      = (1 + (-Matrix.single q p dstar) + Matrix.single p q d - Matrix.single p p F) +
        (1 + (-Matrix.single q p dstar) + Matrix.single p q d - Matrix.single p p F) *
          Matrix.single p q d := by rw [mul_add, mul_one]
    _ = (1 + (-Matrix.single q p dstar) + Matrix.single p q d - Matrix.single p p F) +
        (- Matrix.single q q E) := by rw [hcross]
    _ = 1 - Matrix.single p p F - Matrix.single q q E +
        Matrix.single p q d - Matrix.single q p dstar := by abel

/-- The matrix of `W⁻¹`. -/
theorem W_matrix_inv (hF : F * F = F) (hd : d = F * d * E)
    (hdstard : dstar * d = E) (hddstar : d * dstar = F) :
    (steinPi (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d)⁻¹ : Matrix (Fin n) (Fin n) R) =
      1 - Matrix.single p p F - Matrix.single q q E -
        Matrix.single p q d + Matrix.single q p dstar := by
  have hd' : -d = F * (-d) * E := by rw [mul_neg, neg_mul, ← hd]
  have hdstard' : (-dstar) * (-d) = E := by rw [neg_mul_neg, hdstard]
  have hddstar' : (-d) * (-dstar) = F := by rw [neg_mul_neg, hddstar]
  have key := W_matrix E F (-d) (-dstar) hpq hF hd' hdstard' hddstar'
  rw [neg_neg] at key
  have h1 : (SteinbergGroup.x p q hpq d)⁻¹ = SteinbergGroup.x p q hpq (-d) :=
    steinberg_x_inv p q hpq d
  have h2 : (SteinbergGroup.x q p hpq.symm (-dstar))⁻¹ = SteinbergGroup.x q p hpq.symm dstar := by
    rw [steinberg_x_inv, neg_neg]
  have hWeq : (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
      SteinbergGroup.x p q hpq d)⁻¹ =
      SteinbergGroup.x p q hpq (-d) * SteinbergGroup.x q p hpq.symm dstar *
        SteinbergGroup.x p q hpq (-d) := by
    rw [mul_inv_rev, mul_inv_rev, h1, h2, mul_assoc]
  rw [hWeq, key, single_neg, single_neg]
  abel

theorem W_mem_steinSub :
    SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d ∈
      steinSub ({p, q} : Finset (Fin n)) := by
  have hp : p ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_self p {q}
  have hq : q ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  have hmem1 : SteinbergGroup.x p q hpq d ∈ steinSub ({p, q} : Finset (Fin n)) :=
    Subgroup.subset_closure ⟨p, q, hpq, d, hp, hq, rfl⟩
  have hmem2 : SteinbergGroup.x q p hpq.symm (-dstar) ∈ steinSub ({p, q} : Finset (Fin n)) :=
    Subgroup.subset_closure ⟨q, p, hpq.symm, -dstar, hq, hp, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmem1 hmem2) hmem1

-- The four single-generator conjugation formulas (19) from the proof of Lemma 4.3, for a
-- column/row generator at an auxiliary index `k ∉ {p, q}`, with `y = EyE`.
section Formulas19

variable (k : Fin n) (hkp : k ≠ p) (hkq : k ≠ q) (y : R) (hy : y = E * y * E)
  (hE : E * E = E) (hEF : E * F = 0) (hFE : F * E = 0)
  (hF : F * F = F) (hd : d = F * d * E)
  (hdstar : dstar = E * dstar * F) (hdstard : dstar * d = E) (hddstar : d * dstar = F)

include hy hE in
theorem yE_eq_y : y * E = y := by
  calc y * E = E * y * E * E := congrArg (· * E) hy
    _ = E * y * (E * E) := by rw [mul_assoc]
    _ = E * y * E := by rw [hE]
    _ = y := hy.symm

include hkp hkq in
private theorem hJmem :
    ∀ i ∈ ({p, q} : Finset (Fin n)), i ≠ k := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact hkp.symm
  · exact hkq.symm

include hF hd hdstard hddstar in
theorem W_col_p_entry (i' : Fin n) :
    (steinPi (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) : Matrix (Fin n) (Fin n) R) i' p =
      if i' = p then 1 - F else if i' = q then -dstar else 0 := by
  have hmat := W_matrix E F d dstar hpq hF hd hdstard hddstar
  have hent := congrFun (congrFun hmat i') p
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at hent
  rw [hent]
  by_cases h1 : i' = p
  · subst h1; simp [hpq.symm, hpq]
  · by_cases h2 : i' = q
    · subst h2; simp [hpq, Ne.symm hpq, h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

include hF hd hdstard hddstar in
theorem W_col_q_entry (i' : Fin n) :
    (steinPi (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) : Matrix (Fin n) (Fin n) R) i' q =
      if i' = p then d else if i' = q then 1 - E else 0 := by
  have hmat := W_matrix E F d dstar hpq hF hd hdstard hddstar
  have hent := congrFun (congrFun hmat i') q
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at hent
  rw [hent]
  by_cases h1 : i' = p
  · subst h1; simp [hpq, Ne.symm hpq]
  · by_cases h2 : i' = q
    · subst h2; simp [hpq, h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

include hF hd hdstard hddstar in
theorem Winv_row_p_entry (j' : Fin n) :
    (steinPi (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d)⁻¹ : Matrix (Fin n) (Fin n) R) p j' =
      if j' = p then 1 - F else if j' = q then -d else 0 := by
  have hmat := W_matrix_inv E F d dstar hpq hF hd hdstard hddstar
  have hent := congrFun (congrFun hmat p) j'
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at hent
  rw [hent]
  by_cases h1 : j' = p
  · subst h1; simp [hpq.symm, hpq]
  · by_cases h2 : j' = q
    · subst h2; simp [hpq, Ne.symm hpq, h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

include hF hd hdstard hddstar in
theorem Winv_row_q_entry (j' : Fin n) :
    (steinPi (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d)⁻¹ : Matrix (Fin n) (Fin n) R) q j' =
      if j' = p then dstar else if j' = q then 1 - E else 0 := by
  have hmat := W_matrix_inv E F d dstar hpq hF hd hdstard hddstar
  have hent := congrFun (congrFun hmat q) j'
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at hent
  rw [hent]
  by_cases h1 : j' = p
  · subst h1; simp [hpq, Ne.symm hpq]
  · by_cases h2 : j' = q
    · subst h2; simp [hpq, h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

include hy hFE hdstar hF hd hdstard hddstar hkq in
theorem formula19_col_p :
    (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) * SteinbergGroup.x p k hkp.symm y *
      (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d)⁻¹ =
      SteinbergGroup.x p k hkp.symm y := by
  have hp : p ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_self p {q}
  have hq : q ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  set W := SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
    SteinbergGroup.x p q hpq d with hW_def
  have hW : W ∈ steinSub ({p, q} : Finset (Fin n)) := W_mem_steinSub d dstar hpq
  set c : Fin n → R := Function.update (0 : Fin n → R) p y with hc_def
  have heq := (lemma_4_2 ({p, q} : Finset (Fin n)) k (hJmem k hkp hkq) W hW c
    (0 : Fin n → R)).1
  rw [columnElem_single _ k _ p hp y] at heq
  have hFy : F * y = 0 := by
    rw [hy, ← mul_assoc F (E * y) E, ← mul_assoc F E y, hFE, zero_mul, zero_mul]
  have hdstary : dstar * y = 0 := by
    rw [hdstar, hy, mul_assoc (E * dstar) F (E * y * E), ← mul_assoc F (E * y) E,
      ← mul_assoc F E y, hFE, zero_mul, zero_mul, mul_zero]
  have hcp : c p = y := by simp [hc_def]
  have hcq : c q = 0 := by simp [hc_def, Function.update_of_ne hpq.symm]
  have heq2 : (fun i' => ∑ j ∈ ({p, q} : Finset (Fin n)),
      (steinPi W : Matrix (Fin n) (Fin n) R) i' j * c j) = c := by
    funext i'
    rw [Finset.sum_pair hpq, hcp, hcq, mul_zero, add_zero]
    rw [hW_def, W_col_p_entry E F d dstar hpq hF hd hdstard hddstar i']
    rcases eq_or_ne i' p with rfl | hip
    · rw [if_pos rfl, sub_mul, one_mul, hFy, sub_zero, hcp]
    · rcases eq_or_ne i' q with rfl | hiq
      · rw [if_neg hip, if_pos rfl, neg_mul, hdstary, neg_zero, hcq]
      · rw [if_neg hip, if_neg hiq, zero_mul]
        simp [hc_def, Function.update_of_ne hip]
  rw [heq2, columnElem_single _ k _ p hp y] at heq
  exact heq

include hy hE hFE hF hd hdstard hddstar hkq in
theorem formula19_col_q :
    (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) * SteinbergGroup.x q k hkq.symm y *
      (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d)⁻¹ =
      SteinbergGroup.x p k hkp.symm (d * y) := by
  have hp : p ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_self p {q}
  have hq : q ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  set W := SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
    SteinbergGroup.x p q hpq d with hW_def
  have hW : W ∈ steinSub ({p, q} : Finset (Fin n)) := W_mem_steinSub d dstar hpq
  set c : Fin n → R := Function.update (0 : Fin n → R) q y with hc_def
  have heq := (lemma_4_2 ({p, q} : Finset (Fin n)) k (hJmem k hkp hkq) W hW c
    (0 : Fin n → R)).1
  rw [columnElem_single _ k _ q hq y] at heq
  have hEy_eq : E * y = y := by
    calc E * y = E * (E * y * E) := congrArg (E * ·) hy
      _ = E * E * y * E := by rw [← mul_assoc, ← mul_assoc]
      _ = E * y * E := by rw [hE]
      _ = y := hy.symm
  have hEy : (1 - E) * y = 0 := by rw [sub_mul, one_mul, hEy_eq, sub_self]
  have hcp : c p = 0 := by simp [hc_def, Function.update_of_ne hpq]
  have hcq : c q = y := by simp [hc_def]
  have heq2 : (fun i' => ∑ j ∈ ({p, q} : Finset (Fin n)),
      (steinPi W : Matrix (Fin n) (Fin n) R) i' j * c j) =
      Function.update (0 : Fin n → R) p (d * y) := by
    funext i'
    rw [Finset.sum_pair hpq, hcp, hcq, mul_zero, zero_add]
    rw [hW_def, W_col_q_entry E F d dstar hpq hF hd hdstard hddstar i']
    rcases eq_or_ne i' p with rfl | hip
    · rw [if_pos rfl]
      simp [Function.update_self]
    · rcases eq_or_ne i' q with rfl | hiq
      · rw [if_neg hip, if_pos rfl, hEy]
        simp [Function.update_of_ne hpq.symm]
      · rw [if_neg hip, if_neg hiq, zero_mul]
        simp [Function.update_of_ne hip]
  rw [heq2, columnElem_single _ k _ p hp (d * y)] at heq
  exact heq

include hy hEF hF hd hdstard hddstar hkq in
theorem formula19_row_p :
    (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) * SteinbergGroup.x k p hkp y *
      (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d)⁻¹ =
      SteinbergGroup.x k p hkp y := by
  have hp : p ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_self p {q}
  have hq : q ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  set W := SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
    SteinbergGroup.x p q hpq d with hW_def
  have hW : W ∈ steinSub ({p, q} : Finset (Fin n)) := W_mem_steinSub d dstar hpq
  set r : Fin n → R := Function.update (0 : Fin n → R) p y with hr_def
  have heq := (lemma_4_2 ({p, q} : Finset (Fin n)) k (hJmem k hkp hkq) W hW
    (0 : Fin n → R) r).2
  rw [rowElem_single _ k _ p hp y] at heq
  have hyF : y * F = 0 := by
    rw [hy, mul_assoc (E * y) E F, hEF, mul_zero]
  have hyd : y * d = 0 := by
    rw [hd, ← mul_assoc, ← mul_assoc, hyF, zero_mul, zero_mul]
  have hrp : r p = y := by simp [hr_def]
  have hrq : r q = 0 := by simp [hr_def, Function.update_of_ne hpq.symm]
  have heq2 : (fun j => ∑ i' ∈ ({p, q} : Finset (Fin n)),
      r i' * (steinPi W⁻¹ : Matrix (Fin n) (Fin n) R) i' j) = r := by
    funext j
    rw [Finset.sum_pair hpq, hrp, hrq, zero_mul, add_zero]
    rw [hW_def, Winv_row_p_entry E F d dstar hpq hF hd hdstard hddstar j]
    rcases eq_or_ne j p with rfl | hjp
    · rw [if_pos rfl, mul_sub, mul_one, hyF, sub_zero, hrp]
    · rcases eq_or_ne j q with rfl | hjq
      · rw [if_neg hjp, if_pos rfl, mul_neg, hyd, neg_zero, hrq]
      · rw [if_neg hjp, if_neg hjq, mul_zero]
        simp [hr_def, Function.update_of_ne hjp]
  rw [heq2, rowElem_single _ k _ p hp y] at heq
  exact heq

include hy hE hF hd hdstard hddstar hkq in
theorem formula19_row_q :
    (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) * SteinbergGroup.x k q hkq y *
      (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d)⁻¹ =
      SteinbergGroup.x k p hkp (y * dstar) := by
  have hp : p ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_self p {q}
  have hq : q ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  set W := SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
    SteinbergGroup.x p q hpq d with hW_def
  have hW : W ∈ steinSub ({p, q} : Finset (Fin n)) := W_mem_steinSub d dstar hpq
  set r : Fin n → R := Function.update (0 : Fin n → R) q y with hr_def
  have heq := (lemma_4_2 ({p, q} : Finset (Fin n)) k (hJmem k hkp hkq) W hW
    (0 : Fin n → R) r).2
  rw [rowElem_single _ k _ q hq y] at heq
  have hyE_eq : y * E = y := by
    calc y * E = E * y * E * E := congrArg (· * E) hy
      _ = E * y * (E * E) := by rw [mul_assoc]
      _ = E * y * E := by rw [hE]
      _ = y := hy.symm
  have hyE : y * (1 - E) = 0 := by rw [mul_sub, mul_one, hyE_eq, sub_self]
  have hrp : r p = 0 := by simp [hr_def, Function.update_of_ne hpq]
  have hrq : r q = y := by simp [hr_def]
  have heq2 : (fun j => ∑ i' ∈ ({p, q} : Finset (Fin n)),
      r i' * (steinPi W⁻¹ : Matrix (Fin n) (Fin n) R) i' j) =
      Function.update (0 : Fin n → R) p (y * dstar) := by
    funext j
    rw [Finset.sum_pair hpq, hrp, hrq, zero_mul, zero_add]
    rw [hW_def, Winv_row_q_entry E F d dstar hpq hF hd hdstard hddstar j]
    rcases eq_or_ne j p with rfl | hjp
    · rw [if_pos rfl]
      simp [Function.update_self]
    · rcases eq_or_ne j q with rfl | hjq
      · rw [if_neg hjp, if_pos rfl, hyE]
        simp [Function.update_of_ne hpq.symm]
      · rw [if_neg hjp, if_neg hjq, mul_zero]
        simp [Function.update_of_ne hjp]
  rw [heq2, rowElem_single _ k _ p hp (y * dstar)] at heq
  exact heq

include hy hE hEF hFE hF hd hdstar hdstard hddstar hkp hkq in
theorem W_conj_pq_mem :
    (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) * SteinbergGroup.x p q hpq y *
      (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d)⁻¹ ∈
      steinSub (Finset.univ.erase q) := by
  have hyE : y * E = y := yE_eq_y E y hy hE
  have hEE : E = E * E * E := by rw [hE, hE]
  have hchain : SteinbergGroup.x p k hkp.symm y * SteinbergGroup.x k q hkq E *
      (SteinbergGroup.x p k hkp.symm y)⁻¹ * (SteinbergGroup.x k q hkq E)⁻¹ =
      SteinbergGroup.x p q hpq y := by
    have hc := steinberg_x_chain p k q hkp.symm hkq hpq y E
    rwa [hyE] at hc
  rw [← hchain]
  have hc1 := formula19_col_p E F d dstar hpq k hkp hkq y hy hFE hF hd hdstar hdstard hddstar
  have hc2 := formula19_row_q E F d dstar hpq k hkp hkq E hEE hE hF hd hdstard hddstar
  have hEdstar : E * dstar = dstar := by
    calc E * dstar = E * (E * dstar * F) := congrArg (E * ·) hdstar
      _ = E * E * dstar * F := by rw [← mul_assoc, ← mul_assoc]
      _ = E * dstar * F := by rw [hE]
      _ = dstar := hdstar.symm
  rw [hEdstar] at hc2
  have hfinal := calc (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) *
      (SteinbergGroup.x p k hkp.symm y * SteinbergGroup.x k q hkq E *
        (SteinbergGroup.x p k hkp.symm y)⁻¹ * (SteinbergGroup.x k q hkq E)⁻¹) *
      (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d)⁻¹
      = (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d) * SteinbergGroup.x p k hkp.symm y *
        (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d)⁻¹ *
        ((SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d) * SteinbergGroup.x k q hkq E *
        (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d)⁻¹) *
        ((SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d) * SteinbergGroup.x p k hkp.symm y *
        (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d)⁻¹)⁻¹ *
        ((SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d) * SteinbergGroup.x k q hkq E *
        (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d)⁻¹)⁻¹ := by group
    _ = SteinbergGroup.x p k hkp.symm y * SteinbergGroup.x k p hkp dstar *
        (SteinbergGroup.x p k hkp.symm y)⁻¹ * (SteinbergGroup.x k p hkp dstar)⁻¹ := by
        rw [hc1, hc2]
  rw [hfinal]
  apply Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · exact Subgroup.subset_closure ⟨p, k, hkp.symm, y, Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ p⟩,
      Finset.mem_erase.mpr ⟨hkq, Finset.mem_univ k⟩, rfl⟩
  · exact Subgroup.subset_closure ⟨k, p, hkp, dstar,
      Finset.mem_erase.mpr ⟨hkq, Finset.mem_univ k⟩, Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ p⟩, rfl⟩
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨p, k, hkp.symm, y,
      Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ p⟩, Finset.mem_erase.mpr ⟨hkq, Finset.mem_univ k⟩, rfl⟩)
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨k, p, hkp, dstar,
      Finset.mem_erase.mpr ⟨hkq, Finset.mem_univ k⟩, Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ p⟩, rfl⟩)

include hy hE hEF hFE hF hd hdstar hdstard hddstar hkp hkq in
theorem W_conj_qp_mem :
    (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) * SteinbergGroup.x q p hpq.symm y *
      (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d)⁻¹ ∈
      steinSub (Finset.univ.erase q) := by
  have hyE : y * E = y := yE_eq_y E y hy hE
  have hEE : E = E * E * E := by rw [hE, hE]
  have hchain : SteinbergGroup.x q k hkq.symm y * SteinbergGroup.x k p hkp E *
      (SteinbergGroup.x q k hkq.symm y)⁻¹ * (SteinbergGroup.x k p hkp E)⁻¹ =
      SteinbergGroup.x q p hpq.symm y := by
    have hc := steinberg_x_chain q k p hkq.symm hkp hpq.symm y E
    rwa [hyE] at hc
  rw [← hchain]
  have hc1 := formula19_col_q E F d dstar hpq k hkp hkq y hy hE hFE hF hd hdstard hddstar
  have hc2 := formula19_row_p E F d dstar hpq k hkp hkq E hEE hEF hF hd hdstard hddstar
  have hfinal := calc (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) *
      (SteinbergGroup.x q k hkq.symm y * SteinbergGroup.x k p hkp E *
        (SteinbergGroup.x q k hkq.symm y)⁻¹ * (SteinbergGroup.x k p hkp E)⁻¹) *
      (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d)⁻¹
      = (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d) * SteinbergGroup.x q k hkq.symm y *
        (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d)⁻¹ *
        ((SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d) * SteinbergGroup.x k p hkp E *
        (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d)⁻¹) *
        ((SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d) * SteinbergGroup.x q k hkq.symm y *
        (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d)⁻¹)⁻¹ *
        ((SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d) * SteinbergGroup.x k p hkp E *
        (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d)⁻¹)⁻¹ := by group
    _ = SteinbergGroup.x p k hkp.symm (d * y) * SteinbergGroup.x k p hkp E *
        (SteinbergGroup.x p k hkp.symm (d * y))⁻¹ * (SteinbergGroup.x k p hkp E)⁻¹ := by
        rw [hc1, hc2]
  rw [hfinal]
  apply Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · exact Subgroup.subset_closure ⟨p, k, hkp.symm, d * y,
      Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ p⟩, Finset.mem_erase.mpr ⟨hkq, Finset.mem_univ k⟩, rfl⟩
  · exact Subgroup.subset_closure ⟨k, p, hkp, E,
      Finset.mem_erase.mpr ⟨hkq, Finset.mem_univ k⟩, Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ p⟩, rfl⟩
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨p, k, hkp.symm, d * y,
      Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ p⟩, Finset.mem_erase.mpr ⟨hkq, Finset.mem_univ k⟩, rfl⟩)
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨k, p, hkp, E,
      Finset.mem_erase.mpr ⟨hkq, Finset.mem_univ k⟩, Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ p⟩, rfl⟩)

end Formulas19

theorem conj_eq_of_commute {G : Type*} [Group G] {w g : G} (h : Commute w g) :
    w * g * w⁻¹ = g := by
  rw [h.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem W_commute_disjoint (i j : Fin n) (hij : i ≠ j) (hip : i ≠ p) (hiq : i ≠ q)
    (hjp : j ≠ p) (hjq : j ≠ q) (a : R) :
    Commute (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) (SteinbergGroup.x i j hij a) := by
  have h1 : Commute (SteinbergGroup.x p q hpq d) (SteinbergGroup.x i j hij a) :=
    steinberg_x_commute p q i j hpq hij hjp.symm hiq.symm d a
  have h2 : Commute (SteinbergGroup.x q p hpq.symm (-dstar)) (SteinbergGroup.x i j hij a) :=
    steinberg_x_commute q p i j hpq.symm hij hjq.symm hip.symm (-dstar) a
  exact (h1.mul_left h2).mul_left h1

theorem W_conj_corner_gen (hex : ∃ k0 : Fin n, k0 ≠ p ∧ k0 ≠ q)
    (hE : E * E = E) (hEF : E * F = 0) (hFE : F * E = 0) (hF : F * F = F)
    (hd : d = F * d * E) (hdstar : dstar = E * dstar * F)
    (hdstard : dstar * d = E) (hddstar : d * dstar = F)
    (i j : Fin n) (hij : i ≠ j) (s : R) :
    (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) * SteinbergGroup.x i j hij (E * s * E) *
      (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d)⁻¹ ∈
      steinSub (Finset.univ.erase q) := by
  obtain ⟨k0, hk0p, hk0q⟩ := hex
  set y := E * s * E with hy_def
  have step1 : E * (E * s * E) = E * s * E := by
    have assoc1 : E * (E * s * E) = E * E * s * E := by noncomm_ring
    rw [assoc1, hE]
  have step2 : E * s * E * E = E * s * E := by
    have assoc2 : E * s * E * E = E * s * (E * E) := by noncomm_ring
    rw [assoc2, hE]
  have hy : y = E * y * E := by
    show E * s * E = E * (E * s * E) * E
    rw [step1, step2]
  obtain hip | hip := eq_or_ne i p
  · subst hip
    obtain hjq | hjq := eq_or_ne j q
    · subst hjq
      exact W_conj_pq_mem E F d dstar hpq k0 hk0p hk0q y hy hE hEF hFE hF hd hdstar hdstard hddstar
    · have hjp : j ≠ i := hij.symm
      rw [formula19_col_p E F d dstar hpq j hjp hjq y hy hFE hF hd hdstar hdstard hddstar]
      exact Subgroup.subset_closure ⟨i, j, hij, y,
        Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ i⟩, Finset.mem_erase.mpr ⟨hjq, Finset.mem_univ j⟩, rfl⟩
  · obtain hiq | hiq := eq_or_ne i q
    · subst hiq
      obtain hjp | hjp := eq_or_ne j p
      · subst hjp
        exact W_conj_qp_mem E F d dstar hpq k0 hk0p hk0q y hy hE hEF hFE hF hd hdstar hdstard hddstar
      · rw [formula19_col_q E F d dstar hpq j hjp hij.symm y hy hE hFE hF hd hdstard hddstar]
        exact Subgroup.subset_closure ⟨p, j, hjp.symm, d * y,
          Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ p⟩,
          Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩, rfl⟩
    · obtain hjp | hjp := eq_or_ne j p
      · subst hjp
        rw [formula19_row_p E F d dstar hpq i hij hiq y hy hEF hF hd hdstard hddstar]
        exact Subgroup.subset_closure ⟨i, j, hij, y,
          Finset.mem_erase.mpr ⟨hiq, Finset.mem_univ i⟩, Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ j⟩, rfl⟩
      · obtain hjq | hjq := eq_or_ne j q
        · subst hjq
          rw [formula19_row_q E F d dstar hpq i hip hiq y hy hE hF hd hdstard hddstar]
          exact Subgroup.subset_closure ⟨i, p, hip, y * dstar,
            Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩,
            Finset.mem_erase.mpr ⟨hjp.symm, Finset.mem_univ p⟩, rfl⟩
        · rw [conj_eq_of_commute (W_commute_disjoint (d := d) (dstar := dstar)
            (hpq := hpq) (i := i) (j := j) (hij := hij) (hip := hip) (hiq := hiq) (hjp := hjp)
            (hjq := hjq) (a := y))]
          exact Subgroup.subset_closure ⟨i, j, hij, y,
            Finset.mem_erase.mpr ⟨hiq, Finset.mem_univ i⟩, Finset.mem_erase.mpr ⟨hjq, Finset.mem_univ j⟩, rfl⟩

theorem W_conj_cornerSub (hex : ∃ k0 : Fin n, k0 ≠ p ∧ k0 ≠ q)
    (hE : E * E = E) (hEF : E * F = 0) (hFE : F * E = 0) (hF : F * F = F)
    (hd : d = F * d * E) (hdstar : dstar = E * dstar * F)
    (hdstard : dstar * d = E) (hddstar : d * dstar = F)
    (w0 : SteinbergGroup n R) (hw0 : w0 ∈ cornerSub E) :
    (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d) * w0 *
      (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
        SteinbergGroup.x p q hpq d)⁻¹ ∈
      steinSub (Finset.univ.erase q) := by
  induction hw0 using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, s, rfl⟩ := hx
      exact W_conj_corner_gen E F d dstar hpq hex hE hEF hFE hF hd hdstar hdstard hddstar i j hij s
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ ihx ihy =>
      have heq : (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d) * (x * y) *
        (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d)⁻¹ =
        ((SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d) * x *
        (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d)⁻¹) *
        ((SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d) * y *
        (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d)⁻¹) := by group
      rw [heq]
      exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ih =>
      have heq : (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d) * x⁻¹ *
        (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d)⁻¹ =
        ((SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d) * x *
        (SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
          SteinbergGroup.x p q hpq d)⁻¹)⁻¹ := by group
      rw [heq]
      exact Subgroup.inv_mem _ ih

include hpq in
theorem lemma_4_3 (hex : ∃ k0 : Fin n, k0 ≠ p ∧ k0 ≠ q)
    (hE : E * E = E) (hEF : E * F = 0) (hFE : F * E = 0) (hF : F * F = F)
    (hd : d = F * d * E) (hdstar : dstar = E * dstar * F)
    (hdstard : dstar * d = E) (hddstar : d * dstar = F)
    (w0 : SteinbergGroup n R) (hw0 : w0 ∈ cornerSub E) (hid : steinPi w0 = 1)
    (v : SteinbergGroup n R) :
    w0 * v = v * w0 := by
  set W := SteinbergGroup.x p q hpq d * SteinbergGroup.x q p hpq.symm (-dstar) *
    SteinbergGroup.x p q hpq d with hW_def
  have hWmem : W * w0 * W⁻¹ ∈ steinSub (Finset.univ.erase q) := by
    rw [hW_def]
    exact W_conj_cornerSub E F d dstar hpq hex hE hEF hFE hF hd hdstar hdstard hddstar w0 hw0
  have hWid : steinPi (W * w0 * W⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hid, mul_one, mul_inv_cancel]
  have hWcentral := OAI.FiniteAlgebraicEnvelopes.lemma_4_2_corollary q (W * w0 * W⁻¹)
    (Finset.univ.erase q) rfl hWmem hWid
  have hcentral : ∀ u : SteinbergGroup n R, w0 * u = u * w0 := by
    intro u
    have h1 := hWcentral (W * u * W⁻¹)
    have h2 : W * (w0 * u) * W⁻¹ = W * (u * w0) * W⁻¹ := by
      have expand1 : W * (w0 * u) * W⁻¹ = (W * w0 * W⁻¹) * (W * u * W⁻¹) := by group
      have expand2 : W * (u * w0) * W⁻¹ = (W * u * W⁻¹) * (W * w0 * W⁻¹) := by group
      rw [expand1, expand2, h1]
    have hWinj : Function.Injective (fun x : SteinbergGroup n R => W * x * W⁻¹) := by
      intro a b hab
      simpa using congrArg (fun y => W⁻¹ * y * W) hab
    exact hWinj h2
  exact hcentral v

end Lemma43Setup

end FiniteAlgebraicEnvelopes
end OAI

open OAI.FiniteAlgebraicEnvelopes

universe u

theorem solution {n : ℕ} {R : Type u} [Ring R] (E F d dstar : R) {p q : Fin n} (hpq : p ≠ q)
    (hex : ∃ k0 : Fin n, k0 ≠ p ∧ k0 ≠ q)
    (hE : E * E = E) (hEF : E * F = 0) (hFE : F * E = 0) (hF : F * F = F)
    (hd : d = F * d * E) (hdstar : dstar = E * dstar * F)
    (hdstard : dstar * d = E) (hddstar : d * dstar = F)
    (w0 : SteinbergGroup n R) (hw0 : w0 ∈ cornerSub E) (hid : steinPi w0 = 1)
    (v : SteinbergGroup n R) :
    w0 * v = v * w0 :=
  OAI.FiniteAlgebraicEnvelopes.lemma_4_3 E F d dstar hpq hex hE hEF hFE hF hd hdstar hdstard
    hddstar w0 hw0 hid v
