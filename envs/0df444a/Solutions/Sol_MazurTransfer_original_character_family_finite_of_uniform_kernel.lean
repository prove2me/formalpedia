-- Prove2me | solution 1 for MazurTransfer.original_character_family_finite_of_uniform_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T21:44:22.041169+00:00
-- url     : https://prove2.me/submissions/93063af1-6dc6-49ba-8808-9da378e6737c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an injectively represented family of genuine subgroup characters is finite when every character kills the same ambient finite-index subgroup.
Named downstream consumer: unconditional finiteness of the original arithmetic kernel character conditions.
-/
import Mathlib
noncomputable section
namespace MazurTransfer.OriginalCharacterFamilyFiniteUniformKernelProofBoundary20261019
end MazurTransfer.OriginalCharacterFamilyFiniteUniformKernelProofBoundary20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a family of genuine characters on a GIVEN subgroup is
finite if every character kills one SAME ambient finite-index subgroup.
The family need only inject into the character set; no replacement map.
Named downstream consumer: actual unramified reflected-character spaces
using the uniform finite field level from the checked official FLT proof.
-/

noncomputable section
namespace MazurTransfer.FiniteCharacterQuotientDetection
variable {G M W : Type} [Group G] [Group M] [Finite M]

theorem finite_of_uniform_kernel (S T : Subgroup G) [T.FiniteIndex]
    (hTS : T ≤ S) (i : W → (S →* M)) (hi : Function.Injective i)
    (hvan : ∀ (w : W) (t : T), i w ⟨t.val, hTS t.property⟩ = 1) : Finite W := by
  classical
  let Ψ : W → (G ⧸ T) → M := fun w q => if hq : q.out ∈ S then i w ⟨q.out, hq⟩ else 1
  have hΨ : Function.Injective Ψ := by
    intro x y he
    apply hi
    apply MonoidHom.ext
    intro s
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul T s.val
    let q : G ⧸ T := QuotientGroup.mk s.val
    have hout : q.out ∈ S := by
      rw [hu]
      exact S.mul_mem s.property (hTS u.property)
    have helem : (⟨q.out, hout⟩ : S) = s * ⟨u.val, hTS u.property⟩ := Subtype.ext hu
    have ht := congrFun he q
    change (if hq : q.out ∈ S then i x ⟨q.out, hq⟩ else 1) =
      (if hq : q.out ∈ S then i y ⟨q.out, hq⟩ else 1) at ht
    simp only [dif_pos hout] at ht
    rw [helem, map_mul (i x), map_mul (i y), hvan x u, hvan y u, mul_one, mul_one] at ht
    exact ht
  exact Finite.of_injective Ψ hΨ

end MazurTransfer.FiniteCharacterQuotientDetection

theorem solution : ∀ {G M W : Type} [Group G] [Group M] [Finite M] (S T : Subgroup G) [T.FiniteIndex] (hTS : T ≤ S) (i : W → (S →* M)) (hi : Function.Injective i) (hvan : ∀ (w : W) (t : T), i w ⟨t.val, hTS t.property⟩ = 1), Finite W := by
  exact MazurTransfer.FiniteCharacterQuotientDetection.finite_of_uniform_kernel
#print axioms solution
