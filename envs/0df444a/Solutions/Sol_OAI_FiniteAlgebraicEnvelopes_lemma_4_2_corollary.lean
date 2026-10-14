-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.lemma_4_2_corollary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T15:07:24.525866+00:00
-- url     : https://prove2.me/submissions/0f9fa738-61ac-47af-a32b-af3a12c90f7e

import Mathlib
import Definitions.Def_BooneHigman_Steinberg
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_4_2

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

variable {n : ℕ} {R : Type u} [Ring R]

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


/-- `columnElem` at a single-slot vector is exactly that one generator. -/
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

/-- `rowElem` at a single-slot vector is exactly that one generator. -/
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

theorem commute_of_conj_self {G : Type*} [Group G] {w g : G} (h : w * g * w⁻¹ = g) :
    Commute w g := by
  show w * g = g * w
  calc w * g = w * g * w⁻¹ * w := by group
    _ = g * w := by rw [h]

/-- The corollary at the end of Lemma 4.2's proof: a root word omitting a single index `k`,
whose matrix is the identity, is central. -/
theorem central_of_omit_and_identity (k : Fin n) (w : SteinbergGroup n R)
    (J : Finset (Fin n)) (hJ : J = Finset.univ.erase k) (hw : w ∈ steinSub J)
    (hid : steinPi w = 1) (v : SteinbergGroup n R) :
    w * v = v * w := by
  classical
  have hk : ∀ i ∈ J, i ≠ k := by subst hJ; intro i hi; exact (Finset.mem_erase.mp hi).1
  have hcol : ∀ i (hi' : i ≠ k) (a : R), Commute w (SteinbergGroup.x i k hi' a) := by
    intro i hi' a
    have hiJ : i ∈ J := by subst hJ; exact Finset.mem_erase.mpr ⟨hi', Finset.mem_univ i⟩
    set c := Function.update (0 : Fin n → R) i a with hc_def
    have heq := (lemma_4_2 J k hk w hw c (0 : Fin n → R)).1
    rw [hid, Units.val_one] at heq
    have heq2 : columnElem J k hk
        (fun i' => ∑ j ∈ J, (1 : Matrix (Fin n) (Fin n) R) i' j * c j) =
        columnElem J k hk c := by
      apply columnElem_congr
      intro i' hi'2
      show (∑ j ∈ J, (1 : Matrix (Fin n) (Fin n) R) i' j * c j) = c i'
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq J i' c, if_pos hi'2]
    rw [heq2, columnElem_single J k hk i hiJ a] at heq
    exact commute_of_conj_self heq
  have hrow : ∀ i (hi' : i ≠ k) (a : R), Commute w (SteinbergGroup.x k i hi'.symm a) := by
    intro i hi' a
    have hiJ : i ∈ J := by subst hJ; exact Finset.mem_erase.mpr ⟨hi', Finset.mem_univ i⟩
    set r := Function.update (0 : Fin n → R) i a with hr_def
    have heq := (lemma_4_2 J k hk w hw (0 : Fin n → R) r).2
    rw [map_inv, hid, inv_one, Units.val_one] at heq
    have heq2 : rowElem J k hk
        (fun j => ∑ i' ∈ J, r i' * (1 : Matrix (Fin n) (Fin n) R) i' j) =
        rowElem J k hk r := by
      apply rowElem_congr
      intro i' hi'2
      show (∑ j ∈ J, r j * (1 : Matrix (Fin n) (Fin n) R) j i') = r i'
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' J i' r, if_pos hi'2]
    rw [heq2, rowElem_single J k hk i hiJ a] at heq
    exact commute_of_conj_self heq
  have hcenter : ∀ g : SteinbergGroup n R, Commute w g := by
    intro g
    have hcentralizer : g ∈ Subgroup.centralizer ({w} : Set (SteinbergGroup n R)) := by
      refine PresentedGroup.generated_by (steinRelations n R)
        (Subgroup.centralizer ({w} : Set (SteinbergGroup n R))) ?_ g
      rintro ⟨i, j, hij, a⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rcases eq_or_ne j k with hjk | hjk
      · subst hjk; exact (hcol i hij a).symm
      · rcases eq_or_ne i k with hik | hik
        · subst hik; exact (hrow j hjk a).symm
        · have hchain := steinberg_x_chain i k j hik hjk.symm hij a 1
          rw [mul_one] at hchain
          have hc1 : Commute w (SteinbergGroup.x i k hik a) := hcol i hik a
          have hc2 : Commute w (SteinbergGroup.x k j hjk.symm (1 : R)) := hrow j hjk 1
          have hcomm4 := ((hc1.mul_right hc2).mul_right hc1.inv_right).mul_right hc2.inv_right
          rw [hchain] at hcomm4
          exact hcomm4.symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp hcentralizer).symm
  exact hcenter v

end FiniteAlgebraicEnvelopes
end OAI

open OAI.FiniteAlgebraicEnvelopes

universe u

theorem solution {n : ℕ} {R : Type u} [Ring R] (k : Fin n) (w : SteinbergGroup n R)
    (J : Finset (Fin n)) (hJ : J = Finset.univ.erase k) (hw : w ∈ steinSub J)
    (hid : steinPi w = 1) (v : SteinbergGroup n R) :
    w * v = v * w :=
  OAI.FiniteAlgebraicEnvelopes.central_of_omit_and_identity k w J hJ hw hid v
