-- Prove2me | solution 1 for NearEnemy.bisectorEnergy_eq_of_bisectorInjective
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T14:56:32.99377+00:00
-- url     : https://prove2.me/submissions/8c4cd2fc-3296-4d26-93c5-850dbe5fb87a

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy
namespace NearEnemy

 theorem mem_image_trivialQuad_of_injective
    {P : Finset (EuclideanSpace ℝ (Fin 2))} (hP : BisectorInjectiveOnPairs P)
    (q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hmem : q ∈ (P ×ˢ P) ×ˢ (P ×ˢ P)) (hne1 : q.1.1 ≠ q.1.2)
    (hne2 : q.2.1 ≠ q.2.2)
    (hbis : perpBisector q.1.1 q.1.2 = perpBisector q.2.1 q.2.2) :
    q ∈ (P.offDiag ×ˢ (Finset.univ : Finset Bool)).image trivialQuad := by
  obtain ⟨⟨x, y⟩, z, w⟩ := q
  rw [Finset.mem_product] at hmem
  obtain ⟨h1, h2⟩ := hmem
  rw [Finset.mem_product] at h1 h2
  have hpair := hP x h1.1 y h1.2 z h2.1 w h2.2 hne1 hne2 hbis
  rw [Finset.mem_image]
  rcases Set.pair_eq_pair_iff.mp hpair with ⟨hz, hw⟩ | ⟨hz, hw⟩
  · exact ⟨((x, y), true), by
      rw [Finset.mem_product, Finset.mem_offDiag]
      exact ⟨⟨h1.1, h1.2, hne1⟩, Finset.mem_univ _⟩,
      by simp [trivialQuad, hz, hw]⟩
  · exact ⟨((x, y), false), by
      rw [Finset.mem_product, Finset.mem_offDiag]
      exact ⟨⟨h1.1, h1.2, hne1⟩, Finset.mem_univ _⟩,
      by simp [trivialQuad, ← hz, ← hw]⟩

 theorem card_arith (n : ℕ) : n * n - n = n * (n - 1) := by
  cases n with
  | zero => rfl
  | succ m => rw [Nat.succ_sub_one, Nat.mul_succ, Nat.add_sub_cancel]

 theorem trivialQuad_injOn (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    Set.InjOn trivialQuad ↑(P.offDiag ×ˢ (Finset.univ : Finset Bool)) := by
  rintro ⟨⟨x, y⟩, b⟩ h1 ⟨⟨x', y'⟩, b'⟩ h2 heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
    Finset.mem_offDiag] at h1 h2
  obtain ⟨⟨-, -, hxy⟩, -⟩ := h1
  have hfst : (x, y) = (x', y') := congrArg Prod.fst heq
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hfst
  have hsnd : (if b then (x, y) else (y, x)) =
      (if b' then (x, y) else (y, x)) := congrArg Prod.snd heq
  cases b <;> cases b'
  · rfl
  · exfalso
    simp only [Bool.false_eq_true, if_false, if_true] at hsnd
    exact hxy (Prod.ext_iff.mp hsnd).2
  · exfalso
    simp only [Bool.false_eq_true, if_false, if_true] at hsnd
    exact hxy (Prod.ext_iff.mp hsnd).1
  · rfl

/-- Perpendicular bisectors are symmetric in their two endpoints. -/
@[simp] theorem perpBisector_comm (p q : EuclideanSpace ℝ (Fin 2)) :
    perpBisector p q = perpBisector q p := by
  ext x
  constructor <;> intro h <;> exact h.symm

 theorem trivialQuad_mem_and_cond (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (q : (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hq : q ∈ (P.offDiag ×ˢ (Finset.univ : Finset Bool)).image trivialQuad) :
    q ∈ (P ×ˢ P) ×ˢ (P ×ˢ P) ∧ q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
      perpBisector q.1.1 q.1.2 = perpBisector q.2.1 q.2.2 := by
  rw [Finset.mem_image] at hq
  obtain ⟨⟨⟨x, y⟩, b⟩, hmem, rfl⟩ := hq
  rw [Finset.mem_product, Finset.mem_offDiag] at hmem
  obtain ⟨⟨hx, hy, hxy⟩, -⟩ := hmem
  cases b <;>
    simp only [trivialQuad, ite_true, ite_false, Bool.false_eq_true,
      Finset.mem_product] <;>
    exact ⟨⟨⟨hx, hy⟩, by aesop⟩, hxy, by aesop, by simp [perpBisector_comm]⟩

end NearEnemy

open NearEnemy in
theorem solution {P : Finset (EuclideanSpace ℝ (Fin 2))}
    (hP : BisectorInjectiveOnPairs P) :
    bisectorEnergy P = 2 * P.card * (P.card - 1) := by
  have heq : (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter fun q ↦
      q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
        perpBisector q.1.1 q.1.2 = perpBisector q.2.1 q.2.2) =
      (P.offDiag ×ˢ (Finset.univ : Finset Bool)).image trivialQuad := by
    apply Finset.Subset.antisymm
    · intro q hq
      rw [Finset.mem_filter] at hq
      exact mem_image_trivialQuad_of_injective hP q hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
    · intro q hq
      rw [Finset.mem_filter]
      obtain ⟨hmem, hcond⟩ := trivialQuad_mem_and_cond P q hq
      exact ⟨hmem, hcond⟩
  have hcard : bisectorEnergy P =
      ((P.offDiag ×ˢ (Finset.univ : Finset Bool)).image trivialQuad).card :=
    congrArg Finset.card heq
  rw [hcard, Finset.card_image_of_injOn (trivialQuad_injOn P),
    Finset.card_product, Finset.offDiag_card, Finset.card_univ,
    Fintype.card_bool, card_arith]
  ring
