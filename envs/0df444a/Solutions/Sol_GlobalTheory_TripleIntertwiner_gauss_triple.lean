-- Prove2me | solution 1 for GlobalTheory.TripleIntertwiner.gauss_triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:43.8347+00:00
-- url     : https://prove2.me/submissions/b6b2fd6f-0ac4-403b-8432-1b34006d7db7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
import Theorems.Thm_GlobalTheory_TripleIntertwiner_gauss_pow_four
import Theorems.Thm_GlobalTheory_TripleIntertwiner_rep_mem
import Theorems.Thm_GlobalTheory_TripleIntertwiner_rep_mk
import Theorems.Thm_GlobalTheory_TripleIntertwiner_rep_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical
variable {V : Type*} [AddCommGroup V] {F : Type} [AddCommGroup F] [Module ℂ F]
variable {W : V → F →ₗ[ℂ] F} {c : V → V → ℂ}
namespace GlobalTheory.TripleIntertwiner
theorem _root_.solution (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0)
    {A₀ A B C : AddSubgroup V} (hA : A₀ ≤ A) (hB : A₀ ≤ B) (hC : A₀ ≤ C)
    [Fintype (B ⧸ A₀.addSubgroupOf B)] [Fintype (C ⧸ A₀.addSubgroupOf C)]
    (cA : ∀ x ∈ A, ∀ y ∈ A, c x y = 1) (cB : ∀ x ∈ B, ∀ y ∈ B, c x y = 1)
    (cC : ∀ x ∈ C, ∀ y ∈ C, c x y = 1) :
    (∑ z : C ⧸ A₀.addSubgroupOf C, ∑ y : B ⧸ A₀.addSubgroupOf B,
        if rep z + rep y ∈ A then c (rep z) (rep y) else 0) ^ 4 =
    (∑ y : B ⧸ A₀.addSubgroupOf B, ∑ z : C ⧸ A₀.addSubgroupOf C,
        if rep y + rep z ∈ A then c (rep y) (rep z) else 0) ^ 4 := by
  let M : AddSubgroup ((C ⧸ A₀.addSubgroupOf C) × (B ⧸ A₀.addSubgroupOf B)) :=
    AddSubgroup.map ((QuotientAddGroup.mk' _).prodMap (QuotientAddGroup.mk' _))
      (A.comap (C.subtype.coprod B.subtype))
  have hM : ∀ p, p ∈ M ↔ rep p.1 + rep p.2 ∈ A := by
    rintro ⟨z, y⟩
    constructor
    · rintro ⟨⟨z', y'⟩, h1, h2⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      obtain ⟨l, -, hl, h3⟩ := rep_mk (B := A₀) z'
      obtain ⟨l', -, hl', h4⟩ := rep_mk (B := A₀) y'
      have h1' : (z' : V) + y' ∈ A := h1
      show rep (QuotientAddGroup.mk z') + rep (QuotientAddGroup.mk y') ∈ A
      rw [h3, h4, add_add_add_comm]
      exact A.add_mem h1' (A.add_mem (hA hl) (hA hl'))
    · intro h
      exact ⟨(Quotient.out z, Quotient.out y), h, Prod.ext (QuotientAddGroup.out_eq' z)
        (QuotientAddGroup.out_eq' y)⟩
  have key := gauss_pow_four (M := M) (fun m m' => c (rep m.1.1) (rep m'.1.2))
    (fun x x' y => by
      obtain ⟨l, -, hl, h3⟩ := rep_add x.1.1 x'.1.1
      show c (rep (x.1.1 + x'.1.1)) _ = _
      rw [h3, H.2.1, H.2.1, cB _ (hB hl) _ (rep_mem _), mul_one])
    (fun x y y' => by
      obtain ⟨l, -, hl, h3⟩ := rep_add y.1.2 y'.1.2
      show c _ (rep (y.1.2 + y'.1.2)) = _
      rw [h3, H.2.2.1, H.2.2.1, cC _ (rep_mem _) _ (hC hl), mul_one])
    (fun x y => H.2.2.2 _ _)
  have conv : ∀ g : (C ⧸ A₀.addSubgroupOf C) × (B ⧸ A₀.addSubgroupOf B) → ℂ,
      ∑ m : M, g m = ∑ z, ∑ y, if rep z + rep y ∈ A then g (z, y) else 0 := by
    intro g
    rw [← Finset.sum_subtype (Finset.univ.filter fun p => rep p.1 + rep p.2 ∈ A) (p := fun p => p ∈ M)
      (by intro p; simp [hM]), Finset.sum_filter, Fintype.sum_prod_type]
  rw [conv (fun p => c (rep p.1) (rep p.2)), conv (fun p => (c (rep p.1) (rep p.2))⁻¹)] at key
  rw [key, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  rw [add_comm (rep y)]
  split_ifs with h
  · have := cA _ h _ h
    rw [H.2.1, H.2.2.1, H.2.2.1, cB _ (rep_mem y) _ (rep_mem y), cC _ (rep_mem z) _ (rep_mem z),
      one_mul, mul_one] at this
    exact (eq_inv_of_mul_eq_one_right this).symm
  · rfl
end GlobalTheory.TripleIntertwiner
