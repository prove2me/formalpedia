-- Prove2me | solution 1 for HararySachs.Hyper.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T03:25:35.891198+00:00
-- url     : https://prove2.me/submissions/3ec54afc-43a7-44ab-88e9-6b47b3c2f594

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_Veblen
import Theorems.Thm_HararySachs_Hyper_operator_expansion
import Theorems.Thm_HararySachs_Hyper_best_theorem
import Theorems.Thm_HararySachs_Hyper_lemma_4
import Theorems.Thm_HararySachs_Hyper_lemma_9

open HararySachs.Hyper
open Classical

namespace Lemma13Aux

variable {n : ℕ}

/-! ### Membership in `allMultisets` -/

lemma mem_allMultisets (E : Finset (Finset (Fin n))) (j : ℕ) (S : MultiGraph n) :
    S ∈ allMultisets E j ↔ S.card = j ∧ ∀ e ∈ S, e ∈ E := by
  unfold allMultisets
  rw [Finset.mem_image]
  constructor
  · rintro ⟨f, -, rfl⟩
    refine ⟨by simp, ?_⟩
    intro e he
    rw [Multiset.mem_coe, List.mem_ofFn] at he
    obtain ⟨i, rfl⟩ := he
    exact (f i).2
  · rintro ⟨rfl, hS⟩
    refine ⟨fun i => ⟨S.toList.get ⟨i, by simp⟩,
      hS _ (Multiset.mem_toList.mp (List.get_mem _ _))⟩, Finset.mem_univ _, ?_⟩
    conv_rhs => rw [← Multiset.coe_toList S]
    congr 1
    apply List.ext_get (by simp)
    intro p h1 h2
    simp

/-! ### Degrees of the rooted digraph -/

/-- number of positions of `R` rooted at `v` -/
def rc {S : MultiGraph n} (R : Fin S.card → Fin n × Finset (Fin n)) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => (R i).1 = v)).card

lemma edge_mem {S : MultiGraph n} {R : Fin S.card → Fin n × Finset (Fin n)}
    (hR : IsRooting S R) (i : Fin S.card) : (R i).2 ∈ S := by
  rw [← hR.2.2]
  simp

lemma outDeg_eq {k : ℕ} {S : MultiGraph n} (hS : IsUniform S k)
    {R : Fin S.card → Fin n × Finset (Fin n)} (hR : IsRooting S R) (u : Fin n) :
    outDeg (rootedArcs R) u = (k - 1) * rc R u := by
  unfold outDeg rootedArcs rc
  simp only [Finset.card_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : (R i).1 = u
  · simp only [h, true_and, if_true, mul_one]
    rw [← Finset.card_filter, ← hS _ (edge_mem hR i)]
    have hu : u ∈ (R i).2 := h ▸ hR.1 i
    rw [← Finset.card_erase_of_mem hu]
    congr 1
    ext v
    simp [Finset.mem_erase, and_comm]
  · simp [h]

lemma sum_rc {S : MultiGraph n} (R : Fin S.card → Fin n × Finset (Fin n)) :
    ∑ v, rc R v = S.card := by
  unfold rc
  rw [← Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ ((R i).1))]
  simp

lemma total_arcs {k : ℕ} {S : MultiGraph n} (hS : IsUniform S k)
    {R : Fin S.card → Fin n × Finset (Fin n)} (hR : IsRooting S R) :
    (∑ u : Fin n, ∑ v : Fin n, rootedArcs R u v) = S.card * (k - 1) := by
  have : ∀ u, (∑ v : Fin n, rootedArcs R u v) = (k - 1) * rc R u :=
    fun u => outDeg_eq hS hR u
  rw [Finset.sum_congr rfl (fun u _ => this u), ← Finset.mul_sum, sum_rc, mul_comm]

/-- For an Euler rooting, the in-degree at `v` is `(k-1)` times the number of roots at `v`. -/
lemma inDeg_eq_of_euler {k : ℕ} {S : MultiGraph n} (hS : IsUniform S k)
    {R : Fin S.card → Fin n × Finset (Fin n)} (hR : IsEulerRooting S R) (v : Fin n) :
    inDeg (rootedArcs R) v = (k - 1) * rc R v := by
  rw [← hR.2.2.1 v, outDeg_eq hS hR.1]

lemma inDeg_pos_of_active {m : ArcMult n} (hm : IsEulerian m) {v : Fin n}
    (hv : v ∈ active m) : 0 < inDeg m v := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have := hm.2.1 v
  omega

lemma inDeg_zero_of_not_active {m : ArcMult n} {v : Fin n} (hv : v ∉ active m) :
    inDeg m v = 0 := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv
  omega

/-! ### The associated coefficient of a connected multigraph -/

lemma mem_covered {S : MultiGraph n} {e : Finset (Fin n)} {u : Fin n} (he : e ∈ S)
    (hu : u ∈ e) : u ∈ covered S := by
  unfold covered vertexDegree
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨e, Multiset.mem_filter.mpr ⟨he, hu⟩⟩

lemma components_of_connected {k : ℕ} (hk : 1 ≤ k) {S : MultiGraph n} (hS : IsUniform S k)
    (hC : HararySachs.Hyper.IsConnected S) : components S = {S} := by
  have hne : ∀ e ∈ S, e.Nonempty := by
    intro e he
    rw [← Finset.card_pos, hS e he]
    omega
  have hcomp : ∀ v ∈ covered S, componentAt S v = S := by
    intro v hv
    unfold componentAt
    rw [Multiset.filter_eq_self]
    intro e he
    obtain ⟨u, hu⟩ := hne e he
    exact ⟨u, hu, hC.2 v hv u (mem_covered he hu)⟩
  have hcov : (covered S).Nonempty := by
    obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero hC.1
    obtain ⟨u, hu⟩ := hne e he
    exact ⟨u, mem_covered he hu⟩
  unfold components
  ext C
  rw [Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hcomp v hv
  · rintro rfl
    obtain ⟨v, hv⟩ := hcov
    exact ⟨v, hv, hcomp v hv⟩

/-- The weight of a rooting in the expansion of `Tr_d`. -/
noncomputable def wt (k d : ℕ) {S : MultiGraph n} (R : Fin S.card → Fin n × Finset (Fin n)) : ℚ :=
  MvPolynomial.coeff 0 (diffMonomial (rootedArcs R) (trPow n (d * (k - 1)))) /
    ∏ i, (Nat.factorial (rc R i * (k - 1)) : ℚ)

end Lemma13Aux

open Lemma13Aux in
theorem solution (n k d : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = k)
    (hd : 1 ≤ d) :
    Tr (k := k) E d =
      (d : ℚ) * ((k : ℚ) - 1) ^ n *
        ∑ S ∈ (allMultisets E d).filter
            (fun S => IsVeblen S k ∧ HararySachs.Hyper.IsConnected S),
          assocCoeff S := by
  have hL : 0 < d * (k - 1) := Nat.mul_pos (by omega) (by omega)
  have hunif : ∀ S ∈ allMultisets E d, IsUniform S k := fun S hS e he =>
    hE e (((mem_allMultisets E d S).mp hS).2 e he)
  have hcardS : ∀ S ∈ allMultisets E d, S.card = d := fun S hS =>
    ((mem_allMultisets E d S).mp hS).1
  -- Step 1 (operator expansion): the sum over arrangements becomes a sum over rootings.
  have step1 : (∑ a : Fin n → Fin (d + 1),
      if (∑ i, (a i).val) = d then
        MvPolynomial.coeff 0 (applyAll (k := k) E a (trPow n (d * (k - 1)))) /
          ∏ i, (Nat.factorial ((a i).val * (k - 1)) : ℚ)
      else 0) =
      ∑ S ∈ allMultisets E d, ∑ R : Fin S.card → Fin n × Finset (Fin n),
        if IsRooting S R then wt k d R else 0 := by
    have hA : ∀ a : Fin n → Fin (d + 1), (if (∑ i, (a i).val) = d then
        MvPolynomial.coeff 0 (applyAll (k := k) E a (trPow n (d * (k - 1)))) /
          ∏ i, (Nat.factorial ((a i).val * (k - 1)) : ℚ) else 0) =
        ∑ S ∈ allMultisets E d, ∑ R : Fin S.card → Fin n × Finset (Fin n),
          if (∑ i, (a i).val) = d ∧ IsRooting S R ∧ ∀ v, rc R v = (a v).val
          then wt k d R else 0 := by
      intro a
      split_ifs with ha
      · rw [operator_expansion hk E hE a ha, MvPolynomial.coeff_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [MvPolynomial.coeff_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun R _ => ?_)
        by_cases h : IsRooting S R ∧
            ∀ v, (Finset.univ.filter (fun i => (R i).1 = v)).card = (a v).val
        · rw [if_pos h, if_pos ⟨ha, h.1, h.2⟩]
          have hra : ∀ i, (a i).val = rc R i := fun i => (h.2 i).symm
          simp only [wt, hra]
        · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.1, h'.2.2⟩), MvPolynomial.coeff_zero,
            zero_div]
      · symm
        apply Finset.sum_eq_zero
        intro S _
        apply Finset.sum_eq_zero
        intro R _
        rw [if_neg (fun h => ha h.1)]
    rw [Finset.sum_congr rfl (fun a _ => hA a), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    have hrc_le : ∀ v, rc R v < d + 1 := by
      intro v
      have := Finset.single_le_sum (f := fun v => rc R v) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ v)
      rw [sum_rc, hcardS S hS] at this
      omega
    rw [Finset.sum_eq_single (fun v => (⟨rc R v, hrc_le v⟩ : Fin (d + 1)))]
    · by_cases hR : IsRooting S R
      · rw [if_pos ⟨by simp only; rw [sum_rc, hcardS S hS], hR, fun v => rfl⟩, if_pos hR]
      · rw [if_neg (fun h => hR h.2.1), if_neg hR]
    · intro b _ hb
      rw [if_neg]
      rintro ⟨-, -, hbv⟩
      apply hb
      funext v
      exact Fin.ext (hbv v).symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  -- Step 2 (Lemma 4 and BEST): the weight of an Euler rooting.
  have step2 : ∀ S ∈ allMultisets E d, ∀ R : Fin S.card → Fin n × Finset (Fin n),
      IsRooting S R →
      wt k d R = if IsEulerian (rootedArcs R) then
        ((d * (k - 1) : ℕ) : ℚ) * (numArb (rootedArcs R) : ℚ) /
          ∏ v ∈ active (rootedArcs R), (inDeg (rootedArcs R) v : ℚ) else 0 := by
    intro S hS R hR
    have hsum : (∑ u : Fin n, ∑ v : Fin n, rootedArcs R u v) = d * (k - 1) := by
      rw [total_arcs (hunif S hS) hR, hcardS S hS]
    obtain ⟨h4a, h4b⟩ := lemma_4 hL (rootedArcs R) hsum
    unfold wt
    split_ifs with hEu
    · have hER : IsEulerRooting S R := ⟨hR, hEu⟩
      rw [h4b hEu, best_theorem hL _ hsum hEu]
      have hprod : ∏ i, (Nat.factorial (rc R i * (k - 1)) : ℚ) =
          ∏ v ∈ active (rootedArcs R), (Nat.factorial (inDeg (rootedArcs R) v) : ℚ) := by
        have h' : ∀ i, rc R i * (k - 1) = inDeg (rootedArcs R) i := fun i => by
          rw [inDeg_eq_of_euler (hunif S hS) hER i, mul_comm]
        simp only [h']
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro v _ hv
        rw [inDeg_zero_of_not_active hv]
        simp
      rw [hprod]
      have hfact : ∀ v ∈ active (rootedArcs R),
          (Nat.factorial (inDeg (rootedArcs R) v) : ℚ) =
            (inDeg (rootedArcs R) v : ℚ) *
              (Nat.factorial (inDeg (rootedArcs R) v - 1) : ℚ) := by
        intro v hv
        have hpos := inDeg_pos_of_active hEu hv
        rw [← Nat.cast_mul, Nat.mul_factorial_pred hpos.ne']
      rw [Finset.prod_congr rfl hfact, Finset.prod_mul_distrib]
      have h1 : (∏ v ∈ active (rootedArcs R), (inDeg (rootedArcs R) v : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun v hv => by
          exact_mod_cast (inDeg_pos_of_active hEu hv).ne')
      have h2 : (∏ v ∈ active (rootedArcs R),
          (Nat.factorial (inDeg (rootedArcs R) v - 1) : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun v _ => by
          exact_mod_cast (Nat.factorial_pos _).ne')
      push_cast
      field_simp
    · have h0 : MvPolynomial.coeff 0 (diffMonomial (rootedArcs R) (trPow n (d * (k - 1)))) = 0 := by
        by_contra h
        exact hEu (h4a.mp h)
      rw [h0, zero_div]
  -- Step 3: summing over rootings of a fixed multiset gives the connected coefficient.
  have step3 : ∀ S ∈ allMultisets E d,
      (∑ R : Fin S.card → Fin n × Finset (Fin n), if IsRooting S R then wt k d R else 0) =
        ((d * (k - 1) : ℕ) : ℚ) * connectedCoeff S := by
    intro S hS
    unfold connectedCoeff
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    by_cases hR : IsRooting S R
    · rw [if_pos hR, step2 S hS R hR]
      by_cases hEu : IsEulerian (rootedArcs R)
      · rw [if_pos hEu, if_pos ⟨hR, hEu⟩]
        ring
      · rw [if_neg hEu, if_neg (fun h => hEu h.2)]
        ring
    · rw [if_neg hR, if_neg (fun h => hR h.1)]
      ring
  -- Step 4 (Lemma 9): only connected Veblen multisets carry Euler rootings.
  have step4 : ∑ S ∈ allMultisets E d, connectedCoeff S =
      ∑ S ∈ (allMultisets E d).filter
          (fun S => IsVeblen S k ∧ HararySachs.Hyper.IsConnected S), assocCoeff S := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    split_ifs with hVC
    · unfold assocCoeff
      rw [components_of_connected (by omega) (hunif S hS) hVC.2, Finset.prod_singleton]
    · unfold connectedCoeff
      apply Finset.sum_eq_zero
      intro R _
      rw [if_neg]
      intro hER
      obtain ⟨hV, hC, -⟩ := lemma_9 hk S (hunif S hS) R hER
      exact hVC ⟨hV, hC⟩
  -- Assembly.
  unfold Tr
  rw [step1, Finset.sum_congr rfl step3, ← Finset.mul_sum, step4]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
  ring
