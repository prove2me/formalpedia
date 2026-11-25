-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.det_adLeviPar_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:36.004241+00:00
-- url     : https://prove2.me/submissions/d596fa48-444c-49d8-a40a-dbf0c285e2d5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_coe_leviParCoord_symm_single
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_inv_apply_of_diagonal
import Theorems.Thm_GroundTheory_Automorphic_Measures_mul_single_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa MeasureTheory Measure Topology Set ValuativeRel Measures
open scoped NNReal
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α α' : Type*} [LinearOrder α] [LinearOrder α'] {γ : Fin n → α} {δ : Fin n → α'}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (l : leviPar F n γ δ)
    (hl : ∀ i j, i ≠ j → ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :
    (LinearEquiv.det (adLeviPar F n γ δ l) : F) = ∏ s : LeviParIndex n γ δ,
      ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1 *
        (((l : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2 := by
  classical
  have hQ : ∀ i j, i ≠ j →
      (((l : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 :=
    fun i j hij => by rw [inv_apply_of_diagonal hl, if_neg hij]
  set P : Matrix (Fin n) (Fin n) F := ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Q : Matrix (Fin n) (Fin n) F :=
    (((l : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  let A : (LeviParIndex n γ δ → F) →ₗ[F] (LeviParIndex n γ δ → F) :=
    (((leviParCoord F n γ δ).symm.trans ((adLeviPar F n γ δ l).trans (leviParCoord F n γ δ))) :
      (LeviParIndex n γ δ → F) →ₗ[F] (LeviParIndex n γ δ → F))
  have hdet : (LinearEquiv.det (adLeviPar F n γ δ l) : F) = LinearMap.det A := by
    rw [← LinearEquiv.det_conj (adLeviPar F n γ δ l) (leviParCoord F n γ δ), LinearEquiv.coe_det]
    rfl
  have hM : ∀ s t, LinearMap.toMatrix' A s t = P s.1.1 t.1.1 * Q t.1.2 s.1.2 := by
    intro s t
    rw [LinearMap.toMatrix'_apply]
    show ((adLeviPar F n γ δ l ((leviParCoord F n γ δ).symm (Pi.single t 1)) : lieLeviPar F n γ δ) :
      Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 = _
    rw [coe_adLeviPar, coe_leviParCoord_symm_single, mul_single_mul_apply]
  have hD : LinearMap.toMatrix' A = diagonal fun s : LeviParIndex n γ δ => P s.1.1 s.1.1 * Q s.1.2 s.1.2 := by
    ext s t
    rw [hM]
    by_cases hst : s = t
    · subst hst
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hst]
      by_cases h1 : s.1.1 = t.1.1
      · have h2 : t.1.2 ≠ s.1.2 := fun h2 => hst (Subtype.ext (Prod.ext h1 h2.symm))
        rw [hQ _ _ h2, mul_zero]
      · rw [hl _ _ h1, zero_mul]
  rw [hdet, ← LinearMap.det_toMatrix', hD, det_diagonal]
end GroundTheory.Automorphic.Parabolic
