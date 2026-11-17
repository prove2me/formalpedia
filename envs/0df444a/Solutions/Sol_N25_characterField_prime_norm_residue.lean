-- Prove2me | solution 1 for N25.characterField_prime_norm_residue
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:01.449756+00:00
-- url     : https://prove2.me/submissions/cc845965-0409-4449-a3cb-53a43d1abfc8

import Mathlib
import Definitions.Def_N25_CharacterField
import Theorems.Thm_N25_level25_subgroup_membership
import Definitions.Def_N25
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic

set_option autoImplicit false

noncomputable section

open scoped NumberField

namespace N25

/-- A prime upstairs with small prime-to-25 norm downstairs has its norm
in the literal H25 residue set. -/
theorem _root_.solution
    (Q : Ideal (𝓞 cyclotomicField)) [Q.IsPrime]
    [Finite ((𝓞 cyclotomicField) ⧸ Q)]
    (h25 : (25 : 𝓞 cyclotomicField) ∉ Q)
    (hbound : (Q.under (𝓞 characterField)).absNorm ≤ 24) :
    ((Q.under (𝓞 characterField)).absNorm : ZMod 25) = 1 ∨
    ((Q.under (𝓞 characterField)).absNorm : ZMod 25) = 7 ∨
    ((Q.under (𝓞 characterField)).absNorm : ZMod 25) = 18 ∨
    ((Q.under (𝓞 characterField)).absNorm : ZMod 25) = 24 := by
  haveI : FiniteDimensional ℚ cyclotomicField :=
    IsCyclotomicExtension.finiteDimensional {25} ℚ cyclotomicField
  haveI : IsGalois characterField cyclotomicField :=
    IsGalois.of_fixed_field cyclotomicField characterSubgroup
  let E := galRestrict (𝓞 characterField) characterField
    cyclotomicField (𝓞 cyclotomicField)
  haveI : Finite ((𝓞 cyclotomicField) ≃ₐ[𝓞 characterField] 𝓞 cyclotomicField) :=
    Finite.of_equiv (cyclotomicField ≃ₐ[characterField] cyclotomicField) E.toEquiv
  haveI : Algebra.IsInvariant (𝓞 characterField) (𝓞 cyclotomicField)
      ((𝓞 cyclotomicField) ≃ₐ[𝓞 characterField] 𝓞 cyclotomicField) :=
    Algebra.isInvariant_of_isGalois' (𝓞 characterField) characterField
      cyclotomicField (𝓞 cyclotomicField)
  obtain ⟨f, hf⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 characterField)
    ((𝓞 cyclotomicField) ≃ₐ[𝓞 characterField] 𝓞 cyclotomicField) Q
  let σ : cyclotomicField ≃ₐ[characterField] cyclotomicField := E.symm f
  have hfix : σ.restrictScalars ℚ ∈ characterField.fixingSubgroup := by
    intro x
    exact σ.commutes x
  have hsH : cyclotomicAutEquiv (σ.restrictScalars ℚ) ∈ H25 := by
    change σ.restrictScalars ℚ ∈ characterSubgroup
    have hx := hfix
    change σ.restrictScalars ℚ ∈
      (IntermediateField.fixedField characterSubgroup).fixingSubgroup at hx
    rwa [IntermediateField.fixingSubgroup_fixedField] at hx
  let ζ : 𝓞 cyclotomicField :=
    ⟨IsCyclotomicExtension.zeta 25 ℚ cyclotomicField,
      (IsCyclotomicExtension.zeta_spec 25 ℚ cyclotomicField).isIntegral (by decide)⟩
  have hζpow : ζ ^ 25 = 1 := by
    apply Subtype.ext
    exact (IsCyclotomicExtension.zeta_spec 25 ℚ cyclotomicField).pow_eq_one
  have hF := hf.apply_of_pow_eq_one hζpow h25
  have hσpow : σ (ζ : cyclotomicField) =
      (ζ : cyclotomicField) ^ (Q.under (𝓞 characterField)).absNorm := by
    rw [show σ (ζ : cyclotomicField) = (f ζ : cyclotomicField) from
      galRestrict_symm_algebraMap_apply
        (𝓞 characterField) characterField f ζ]
    exact congrArg (fun x : 𝓞 cyclotomicField => (x : cyclotomicField)) hF
  have hAut := (IsCyclotomicExtension.zeta_spec 25 ℚ cyclotomicField).autToPow_spec
    ℚ (σ.restrictScalars ℚ)
  change (ζ : cyclotomicField) ^
    (cyclotomicAutEquiv (σ.restrictScalars ℚ) : ZMod 25).val = σ (ζ : cyclotomicField) at hAut
  have hv := (IsCyclotomicExtension.zeta_spec 25 ℚ cyclotomicField).pow_inj
    (ZMod.val_lt _) (by omega : (Q.under (𝓞 characterField)).absNorm < 25)
    (hAut.trans hσpow)
  have he : (cyclotomicAutEquiv (σ.restrictScalars ℚ) : ZMod 25) =
      ((Q.under (𝓞 characterField)).absNorm : ZMod 25) := by
    rw [← hv, ZMod.natCast_zmod_val]
  simpa only [he] using (level25_subgroup_membership _).mp hsH

end N25
