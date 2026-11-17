-- Prove2me | solution 1 for N25.characterField_degree_and_totallyReal
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:46.321351+00:00
-- url     : https://prove2.me/submissions/fce21258-1033-42b0-93a5-f96e2f2a4d50

import Mathlib
import Definitions.Def_N25_CharacterField
import Theorems.Thm_N25_level25_subgroup_card
import Definitions.Def_N25
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

namespace N25

/-- The literal H25-fixed cyclotomic field has degree five, relative degree
four in Q(zeta25), and only real embeddings. -/
theorem _root_.solution :
    Module.finrank ℚ characterField = 5 ∧
    Module.finrank characterField cyclotomicField = 4 ∧
    NumberField.IsTotallyReal characterField := by
  haveI : FiniteDimensional ℚ cyclotomicField :=
    IsCyclotomicExtension.finiteDimensional {25} ℚ cyclotomicField
  let e : characterSubgroup ≃ H25 :=
    { toFun := fun x => ⟨cyclotomicAutEquiv x, x.2⟩
      invFun := fun x => ⟨cyclotomicAutEquiv.symm x, by
        change cyclotomicAutEquiv (cyclotomicAutEquiv.symm x) ∈ H25
        simpa only [MulEquiv.apply_symm_apply] using x.2⟩
      left_inv := fun x => Subtype.ext (MulEquiv.symm_apply_apply cyclotomicAutEquiv x)
      right_inv := fun x => Subtype.ext (MulEquiv.apply_symm_apply cyclotomicAutEquiv x) }
  have hc : Nat.card characterSubgroup = 4 :=
    (Nat.card_congr e).trans level25_subgroup_card
  have hrel : Module.finrank characterField cyclotomicField = 4 := by
    exact (IntermediateField.finrank_fixedField_eq_card characterSubgroup).trans hc
  have hfull : Module.finrank ℚ cyclotomicField = 20 := by
    have hf := IsCyclotomicExtension.finrank cyclotomicField
      (Polynomial.cyclotomic.irreducible_rat (by decide : 0 < 25))
    norm_num [show 25 = 5 ^ 2 by decide, Nat.totient_prime_pow (by decide : Nat.Prime 5)] at hf
    exact hf
  have hdeg : Module.finrank ℚ characterField = 5 := by
    have ht := Module.finrank_mul_finrank ℚ characterField cyclotomicField
    rw [hrel, hfull] at ht
    omega
  haveI : characterSubgroup.Normal := ⟨by
    intro n hn g
    change cyclotomicAutEquiv (g * n * g⁻¹) ∈ H25
    have heq : cyclotomicAutEquiv (g * n * g⁻¹) = cyclotomicAutEquiv n := by
      simp only [map_mul, map_inv]
      simp [mul_comm, mul_left_comm, mul_assoc]
    rw [heq]
    exact hn⟩
  haveI : IsGalois ℚ cyclotomicField :=
    IsCyclotomicExtension.isGalois {25} ℚ cyclotomicField
  haveI : IsGalois ℚ characterField :=
    IsGalois.of_fixedField_normal_subgroup characterSubgroup
  haveI : IsUnramifiedAtInfinitePlaces ℚ characterField :=
    IsUnramifiedAtInfinitePlaces_of_odd_finrank (by rw [hdeg]; decide)
  refine ⟨hdeg, hrel, ⟨?_⟩⟩
  intro w
  have hw := NumberField.InfinitePlace.isUnramified ℚ w
  exact (NumberField.InfinitePlace.isUnramified_iff.mp hw).resolve_right
    (NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr
      (NumberField.IsTotallyReal.isReal (w.comap (algebraMap ℚ characterField))))

end N25
