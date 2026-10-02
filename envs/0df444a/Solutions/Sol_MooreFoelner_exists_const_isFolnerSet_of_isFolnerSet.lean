-- Prove2me | solution 1 for MooreFoelner.exists_const_isFolnerSet_of_isFolnerSet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T04:29:31.736534+00:00
-- url     : https://prove2.me/submissions/860b501b-c3a8-43ab-8d8b-0c03769396f9

import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib

section
namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

section
/-!
# Moore 2013, group GenTrees: #7, #17, #18, #27
-/

namespace MooreFoelner.Dev.GenTrees

open Classical MooreFoelner CannonFloydParry
open scoped symmDiff

section Folner

variable {G : Type*} [Group G]

/-- `|A·g Δ A|`. -/
noncomputable def dcard (A : Finset G) (g : G) : ℕ := ((A.image (· * g)) ∆ A).card

lemma image_mul_mul (A : Finset G) (g h : G) :
    A.image (· * (g * h)) = (A.image (· * g)).image (· * h) := by
  rw [Finset.image_image]; congr 1; funext x; simp [mul_assoc]

lemma dcard_mul_le (A : Finset G) (g h : G) : dcard A (g * h) ≤ dcard A g + dcard A h := by
  unfold dcard
  rw [image_mul_mul]
  have hinj : Function.Injective (· * h : G → G) := mul_left_injective h
  have h1 : ((A.image (· * g)).image (· * h)) ∆ (A.image (· * h)) =
      ((A.image (· * g)) ∆ A).image (· * h) := (Finset.image_symmDiff _ _ hinj).symm
  calc _ ≤ (((A.image (· * g)).image (· * h)) ∆ (A.image (· * h)) ∪
          (A.image (· * h)) ∆ A).card := Finset.card_le_card (symmDiff_triangle _ _ _)
    _ ≤ _ := Finset.card_union_le _ _
    _ = _ := by rw [h1, Finset.card_image_of_injective _ hinj]

lemma dcard_inv (A : Finset G) (g : G) : dcard A g⁻¹ = dcard A g := by
  unfold dcard
  have hinj : Function.Injective (· * g : G → G) := mul_left_injective g
  rw [← Finset.card_image_of_injective _ hinj, Finset.image_symmDiff _ _ hinj,
    ← image_mul_mul, inv_mul_cancel, symmDiff_comm]
  congr 2
  ext x; simp

lemma dcard_one (A : Finset G) : dcard A 1 = 0 := by
  unfold dcard; simp

lemma exists_dcard_le (Γ' : Finset G) (g : G) (hg : g ∈ Subgroup.closure (Γ' : Set G)) :
    ∃ N : ℕ, ∀ A : Finset G, dcard A g ≤ N * ∑ γ ∈ Γ', dcard A γ := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    exact ⟨1, fun A => by
      rw [one_mul]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx⟩
  | one => exact ⟨0, fun A => by rw [dcard_one]; exact Nat.zero_le _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨N₁, h₁⟩ := hx
    obtain ⟨N₂, h₂⟩ := hy
    exact ⟨N₁ + N₂, fun A => (dcard_mul_le A x y).trans (by
      rw [add_mul]; exact add_le_add (h₁ A) (h₂ A))⟩
  | inv x _ hx =>
    obtain ⟨N, h⟩ := hx
    exact ⟨N, fun A => by rw [dcard_inv]; exact h A⟩

lemma isFolnerSet_iff_dcard (Γ A : Finset G) (ε : ℝ) :
    IsFolnerSet Γ A ε ↔ ((∑ γ ∈ Γ, dcard A γ : ℕ) : ℝ) < ε * A.card := by
  unfold IsFolnerSet dcard; push_cast; rfl

lemma exists_const_isFolnerSet_of_closure (Γ Γ' : Finset G)
    (hgen : Subgroup.closure (Γ' : Set G) = ⊤) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : Finset G) (ε : ℝ), IsFolnerSet Γ' A ε → IsFolnerSet Γ A (K * ε) := by
  have hN : ∀ g : G, ∃ N : ℕ, ∀ A : Finset G, dcard A g ≤ N * ∑ γ ∈ Γ', dcard A γ :=
    fun g => exists_dcard_le Γ' g (by rw [hgen]; exact Subgroup.mem_top g)
  choose N hN using hN
  refine ⟨(∑ γ ∈ Γ, N γ : ℕ) + 1, by positivity, fun A ε hA => ?_⟩
  rw [isFolnerSet_iff_dcard] at hA ⊢
  set S := ∑ γ ∈ Γ', dcard A γ
  have h1 : ∑ γ ∈ Γ, dcard A γ ≤ (∑ γ ∈ Γ, N γ) * S := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum fun γ _ => hN γ A
  have h1' : ((∑ γ ∈ Γ, dcard A γ : ℕ) : ℝ) ≤ ((∑ γ ∈ Γ, N γ : ℕ) : ℝ) * (S : ℝ) := by
    exact_mod_cast h1
  have hS : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  calc ((∑ γ ∈ Γ, dcard A γ : ℕ) : ℝ) ≤ ((∑ γ ∈ Γ, N γ : ℕ) : ℝ) * (S : ℝ) := h1'
    _ ≤ (((∑ γ ∈ Γ, N γ : ℕ) : ℝ) + 1) * (S : ℝ) := by nlinarith
    _ < (((∑ γ ∈ Γ, N γ : ℕ) : ℝ) + 1) * (ε * A.card) := by
        apply mul_lt_mul_of_pos_left hA; positivity
    _ = _ := by ring

end Folner

section Seqs

/-- The infinite sequence `s⁀y`. -/
def appS (s : Seq) (y : ℕ → Bool) : ℕ → Bool :=
  fun n => if h : n < s.length then s.get ⟨n, h⟩ else y (n - s.length)

/-- `x` with its first `k` digits removed. -/
def shift (x : ℕ → Bool) (k : ℕ) : ℕ → Bool := fun n => x (n + k)

@[simp] lemma appS_nil (y : ℕ → Bool) : appS [] y = y := by funext n; simp [appS]

@[simp] lemma shift_zero (x : ℕ → Bool) : shift x 0 = x := by funext n; simp [shift]

end Seqs

section Trees

end Trees

section Sorted

end Sorted

section DiagramMap

end DiagramMap

section DiagramAct

end DiagramAct

section Five

end Five

section PartialAction

end PartialAction

section StrictSort

variable {α : Type*}

end StrictSort

section SortedOrder

end SortedOrder

section Val

end Val

section Concrete

@[simp] lemma seqVal_nil : seqVal [] = 0 := by simp [seqVal]

@[simp] lemma seqVal_cons (b : Bool) (s : Seq) :
    seqVal (b :: s) = (if b then 1/2 else 0) + (1/2) * seqVal s := by
  unfold seqVal
  change (∑ i : Fin (s.length + 1), _) = _
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i _
    simp only [List.length_cons, Fin.val_succ, List.get_eq_getElem, List.getElem_cons_succ]
    split_ifs <;> ring

end Concrete

section GMap

/-! ### The element `g_u`: `x₀` acting inside the dyadic interval of `u` -/

end GMap

section Concrete2

end Concrete2

section WordLength

end WordLength

section LocalX0

end LocalX0

section Lemma41


end Lemma41

section Lemma42


end Lemma42

end MooreFoelner.Dev.GenTrees

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

open MooreFoelner in
open Classical MooreFoelner CannonFloydParry in
open scoped symmDiff in
open Classical CannonFloydParry in
theorem solution (Γ' : Finset MooreF)
    (hgen : Subgroup.closure (Γ' : Set MooreF) = ⊤) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : Finset MooreF) (ε : ℝ), IsFolnerSet Γ' A ε → IsFolnerSet gens A (K * ε) :=
  Dev.GenTrees.exists_const_isFolnerSet_of_closure gens Γ' hgen
