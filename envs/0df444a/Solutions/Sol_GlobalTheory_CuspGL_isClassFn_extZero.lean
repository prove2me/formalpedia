-- Prove2me | solution 1 for GlobalTheory.CuspGL.isClassFn_extZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:05:35.657996+00:00
-- url     : https://prove2.me/submissions/ff0ee6c1-e258-4a81-b22f-5b288203751f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndProperties
import Theorems.Thm_GlobalTheory_CuspGL_extZero_isUnit_iff
import Theorems.Thm_GlobalTheory_CuspGL_extZero_toLin
import Theorems.Thm_GlobalTheory_CuspGL_extZero_of_not_isUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F] {d : ℕ}
namespace GlobalTheory.CuspGL
theorem _root_.solution (χ : GL (Fin d) F → ℂ)
    (hχ : ∀ g x : GL (Fin d) F, χ (x⁻¹ * g * x) = χ g) : IsClassFn (extZero χ) := by
  intro e g

  let Φ : GL (Fin d) F ≃* (Module.End F (Fin d → F))ˣ :=
    Units.mapEquiv (Matrix.toLinAlgEquiv' (R := F) (n := Fin d)).toMulEquiv
  have hcoe : ∀ x : GL (Fin d) F, ((Φ x : (Module.End F (Fin d → F))ˣ) : Module.End F (Fin d → F)) =
      Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := by
    intro x
    refine LinearMap.ext fun v => ?_
    change Matrix.toLinAlgEquiv' (x : Matrix (Fin d) (Fin d) F) v = _
    rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

  let E : (Module.End F (Fin d → F))ˣ :=
    ⟨e.toLinearMap, e.symm.toLinearMap, LinearMap.ext fun v => e.apply_symm_apply v,
      LinearMap.ext fun v => e.symm_apply_apply v⟩
  have hconj : ∀ f : Module.End F (Fin d → F),
      e.conj f = (E : Module.End F (Fin d → F)) * f * ((E⁻¹ : (Module.End F (Fin d → F))ˣ) :
        Module.End F (Fin d → F)) := by
    intro f
    exact LinearMap.ext fun v => rfl
  by_cases hg : IsUnit g
  · obtain ⟨y, rfl⟩ := (extZero_isUnit_iff g).mp hg
    have hy : e.conj (Matrix.toLin' (y : Matrix (Fin d) (Fin d) F)) =
        Matrix.toLin' ((Φ.symm E * y * (Φ.symm E)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
      rw [← hcoe (Φ.symm E * y * (Φ.symm E)⁻¹), map_mul, map_mul, map_inv, Φ.apply_symm_apply, Units.val_mul, Units.val_mul,
        hcoe y, hconj]
    rw [hy, extZero_toLin, extZero_toLin]
    simpa using hχ y (Φ.symm E)⁻¹
  · have hg' : ¬ IsUnit (e.conj g) := by
      rw [hconj, Units.isUnit_mul_units, Units.isUnit_units_mul]
      exact hg
    rw [extZero_of_not_isUnit χ _ hg', extZero_of_not_isUnit χ _ hg]
end GlobalTheory.CuspGL
