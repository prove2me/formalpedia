-- Prove2me | solution 1 for IntermediateField.exists_algEquiv_adjoin_rootsOfUnity_apply_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/819660c9-fb43-57ef-a718-2b4daf736858

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_algEquiv_adjoin_rootsOfUnity_apply_eq_pow

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField
open Polynomial

theorem solution {F E : Type} [Field F] [Field E] [Algebra F E] (m : ℕ) (hm : 0 < m) (ζ₀ : E) (hζ₀ : IsPrimitiveRoot ζ₀ m)
    (a : ℕ) (ha : a.Coprime m) (hroot : Polynomial.aeval (ζ₀ ^ a) (minpoly F ζ₀) = 0) :
    ∃ φ : (IntermediateField.adjoin F {ζ : E | ζ ^ m = 1}) ≃ₐ[F] (IntermediateField.adjoin F {ζ : E | ζ ^ m = 1}),
      ∀ ζ : IntermediateField.adjoin F {ζ : E | ζ ^ m = 1}, (ζ : E) ^ m = 1 → (φ ζ : E) = (ζ : E) ^ a := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  have hint : IsIntegral F ζ₀ := IsIntegral.of_pow hm (by rw [hζ₀.pow_eq_one]; exact isIntegral_one)
  have hζa : IsPrimitiveRoot (ζ₀ ^ a) m := hζ₀.pow_of_coprime a ha
  have hinta : IsIntegral F (ζ₀ ^ a) := hint.pow a
  set L := IntermediateField.adjoin F {ζ : E | ζ ^ m = 1} with hLdef

  have hgen : ∀ (η : E), IsPrimitiveRoot η m → L = F⟮η⟯ := by
    intro η hη
    apply le_antisymm
    · rw [hLdef, IntermediateField.adjoin_le_iff]
      intro ζ hζ
      obtain ⟨i, -, rfl⟩ := hη.eq_pow_of_pow_eq_one hζ
      exact pow_mem (IntermediateField.mem_adjoin_simple_self F η) i
    · rw [IntermediateField.adjoin_simple_le_iff, hLdef]
      exact IntermediateField.subset_adjoin F _ hη.pow_eq_one
  have h1 : L = F⟮ζ₀⟯ := hgen ζ₀ hζ₀
  have h2 : L = F⟮ζ₀ ^ a⟯ := hgen _ hζa

  have hmin : minpoly F ζ₀ = minpoly F (ζ₀ ^ a) :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hroot (minpoly.monic hint)
  let pb₁ := IntermediateField.adjoin.powerBasis hint
  let pb₂ := IntermediateField.adjoin.powerBasis hinta
  have hpb : minpoly F pb₁.gen = minpoly F pb₂.gen := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.minpoly_gen, IntermediateField.minpoly_gen, hmin]
  let e₁ : F⟮ζ₀⟯ ≃ₐ[F] F⟮ζ₀ ^ a⟯ := pb₁.equivOfMinpoly pb₂ hpb
  have he₁ : e₁ (IntermediateField.AdjoinSimple.gen F ζ₀) = IntermediateField.AdjoinSimple.gen F (ζ₀ ^ a) := by
    have := pb₁.equivOfMinpoly_gen pb₂ hpb
    rwa [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_gen] at this
  let φ : L ≃ₐ[F] L :=
    (IntermediateField.equivOfEq h1).trans (e₁.trans (IntermediateField.equivOfEq h2.symm))
  refine ⟨φ, fun ζ hζ => ?_⟩
  obtain ⟨i, -, hi⟩ := hζ₀.eq_pow_of_pow_eq_one hζ

  have hx : IntermediateField.equivOfEq h1 ζ = (IntermediateField.AdjoinSimple.gen F ζ₀) ^ i :=
    Subtype.ext (by
      rw [IntermediateField.equivOfEq_apply]
      change (ζ : E) = ((IntermediateField.AdjoinSimple.gen F ζ₀ ^ i : F⟮ζ₀⟯) : E)
      rw [SubmonoidClass.coe_pow, IntermediateField.AdjoinSimple.coe_gen, hi])
  change (((IntermediateField.equivOfEq h2.symm) (e₁ ((IntermediateField.equivOfEq h1) ζ)) : L) : E) = _
  rw [IntermediateField.equivOfEq_apply, hx, map_pow, he₁]
  change (((IntermediateField.AdjoinSimple.gen F (ζ₀ ^ a)) ^ i : F⟮ζ₀ ^ a⟯) : E) = _
  rw [SubmonoidClass.coe_pow, IntermediateField.AdjoinSimple.coe_gen, ← hi, ← pow_mul, ← pow_mul, mul_comm]

end S_IntermediateField_exists_algEquiv_adjoin_rootsOfUnity_apply_eq_pow
end P2MW
export P2MW.S_IntermediateField_exists_algEquiv_adjoin_rootsOfUnity_apply_eq_pow (solution)
