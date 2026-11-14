-- Prove2me | solution 1 for IsRegularLocalRing.tfae_hasProjectiveDimensionLT
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:10:17.885522+00:00
-- url     : https://prove2.me/submissions/e36f2d1f-e898-4691-bff3-b1f6daa0d41e

import Mathlib
import Definitions.Def_RPLib_S4_JacDivisorsD

set_option autoImplicit false

universe u

theorem solution (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    List.TFAE [IsRegularLocalRing R,
      ∀ M : ModuleCat.{u} R, Module.Finite R M → ∃ n : ℕ, CategoryTheory.HasProjectiveDimensionLT M n,
      ∃ n : ℕ, CategoryTheory.HasProjectiveDimensionLT (ModuleCat.of R (IsLocalRing.ResidueField R)) n] := by
  tfae_have 1 → 2 := by
    intro h M hM
    exact RamanujanPetersson.JacDivisors.exists_hasPDLT_of_isRegularLocalRing M
  tfae_have 2 → 3 := by
    intro h
    have hfin : Module.Finite R (IsLocalRing.ResidueField R) :=
      Module.Finite.of_surjective (Algebra.linearMap R (IsLocalRing.ResidueField R))
        IsLocalRing.residue_surjective
    exact h (ModuleCat.of R (IsLocalRing.ResidueField R)) hfin
  tfae_have 3 → 1 := by
    rintro ⟨n, hn⟩
    let e : IsLocalRing.ResidueField R ≃ₗ[R] R ⧸ IsLocalRing.maximalIdeal R :=
      { toFun := fun x => x
        invFun := fun x => x
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => by
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
          rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact RamanujanPetersson.JacDivisors.isRegularLocalRing_of_hasPDLT n
      (CategoryTheory.hasProjectiveDimensionLT_of_iso e.toModuleIso n)
  tfae_finish
