-- Prove2me | solution 1 for N25.characterField_comparison
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:10.803459+00:00
-- url     : https://prove2.me/submissions/ec55f74c-4e95-4bf3-a725-bb9d935f2107

import Mathlib
import Definitions.Def_N25_CharacterField
import Theorems.Thm_N25_psiBar_ker
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

namespace N25

/-- The literal quintic cyclotomic fixed field is isomorphic to the field
in the algebraic closure cut out by the actual character psi. -/
theorem _root_.solution :
    (IntermediateField.fixedField psi.ker).fixingSubgroup = psi.ker ∧
    Nonempty (characterField ≃ₐ[ℚ] IntermediateField.fixedField psi.ker) := by
  let j : cyclotomicField →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  letI : Algebra cyclotomicField (AlgebraicClosure ℚ) := j.toRingHom.toAlgebra
  letI : IsScalarTower ℚ cyclotomicField (AlgebraicClosure ℚ) := IsScalarTower.of_algHom j
  haveI : IsGalois ℚ cyclotomicField :=
    IsCyclotomicExtension.isGalois {25} ℚ cyclotomicField
  let ζ : cyclotomicField := IsCyclotomicExtension.zeta 25 ℚ cyclotomicField
  have hζ : IsPrimitiveRoot ζ 25 := IsCyclotomicExtension.zeta_spec 25 ℚ cyclotomicField
  have hμ : IsPrimitiveRoot (j ζ) 25 := hζ.map_of_injective j.injective
  have hchi (σ : Gal) : cyclotomicAutEquiv (σ.restrictNormal cyclotomicField) = chi25 σ := by
    have hglobal : (j ζ) ^ (chi25 σ : ZMod 25).val = σ (j ζ) := by
      have hv := hμ.autToPow_spec ℚ σ
      rw [hμ.autToPow_eq_modularCyclotomicCharacter 25 ℚ σ] at hv
      exact hv
    have hlocal : (j ζ) ^ (cyclotomicAutEquiv (σ.restrictNormal cyclotomicField) : ZMod 25).val =
        σ (j ζ) := by
      have hv := hζ.autToPow_spec ℚ (σ.restrictNormal cyclotomicField)
      calc
        (j ζ) ^ (cyclotomicAutEquiv (σ.restrictNormal cyclotomicField) : ZMod 25).val =
            j (ζ ^ (cyclotomicAutEquiv (σ.restrictNormal cyclotomicField) : ZMod 25).val) :=
          (map_pow j ζ _).symm
        _ = j (σ.restrictNormal cyclotomicField ζ) := congrArg j hv
        _ = σ (j ζ) := σ.restrictNormal_commutes cyclotomicField ζ
    apply Units.ext
    apply ZMod.val_injective
    exact hμ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hlocal.trans hglobal.symm)
  let i : characterField →ₐ[ℚ] AlgebraicClosure ℚ := j.comp characterField.val
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := i.fieldRange
  have hfix (σ : Gal) : σ ∈ F.fixingSubgroup ↔
      σ.restrictNormal cyclotomicField ∈ characterSubgroup := by
    rw [← IntermediateField.fixingSubgroup_fixedField characterSubgroup]
    change σ ∈ F.fixingSubgroup ↔ σ.restrictNormal cyclotomicField ∈ characterField.fixingSubgroup
    constructor
    · intro h x
      apply j.injective
      change j (σ.restrictNormal cyclotomicField (x : cyclotomicField)) = j (x : cyclotomicField)
      exact (σ.restrictNormal_commutes cyclotomicField (x : cyclotomicField)).trans
        (h ⟨i x, ⟨x, rfl⟩⟩)
    · intro h y
      obtain ⟨x, hx⟩ := y.property
      change σ (y : AlgebraicClosure ℚ) = (y : AlgebraicClosure ℚ)
      rw [← hx]
      change σ (j (x : cyclotomicField)) = j (x : cyclotomicField)
      exact (σ.restrictNormal_commutes cyclotomicField (x : cyclotomicField)).symm.trans
        (congrArg j (h x))
  have hpsi (σ : Gal) : σ ∈ psi.ker ↔ chi25 σ ∈ H25 := by
    rw [← psiBar_ker]
    rfl
  have hker : F.fixingSubgroup = psi.ker := by
    ext σ
    rw [hfix, hpsi]
    change cyclotomicAutEquiv (σ.restrictNormal cyclotomicField) ∈ H25 ↔ chi25 σ ∈ H25
    rw [hchi]
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    (isAlgClosure_iff ℚ (AlgebraicClosure ℚ)).mpr ⟨inferInstance, AlgebraicClosure.isAlgebraic ℚ⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  have heq : F = IntermediateField.fixedField psi.ker := by
    rw [← hker]
    exact (InfiniteGalois.fixedField_fixingSubgroup F).symm
  constructor
  · rw [← heq]
    exact hker
  · rw [← heq]
    exact ⟨AlgEquiv.ofInjectiveField i⟩

end N25
