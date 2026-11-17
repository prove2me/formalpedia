-- Prove2me | solution 1 for N25.exists_northcott_boundedDefect_height_on_M
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:48.309765+00:00
-- url     : https://prove2.me/submissions/5e44612b-dfca-4a02-b817-8cc154dfebab

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_exists_ratModel_pointEquiv
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
import Theorems.Thm_ModularCurve_exists_abelianSchemePropertyBundle_model_jH
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_numberField_symmetricFiniteFrame
import Theorems.Thm_AlgebraicGeometry_SymmetricFiniteFrame_exists_bounded_double
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_SymmetricFiniteFrame_exists_bounded_parallelogram
import Theorems.Thm_AlgebraicGeometry_SymmetricFiniteFrame_northcott_height
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pointLogHeight_nonneg

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace N25

/-- A symmetric frame over a number field induces a Northcott height on rational points. -/
theorem _root_.solution :
    ∃ (h₀ : ↥N25.M → ℝ) (C₂ Cp : ℝ), (∀ x, 0 ≤ h₀ x) ∧ (∀ B : ℝ, {x | h₀ x ≤ B}.Finite) ∧
      (∀ x, |h₀ (x + x) - 4 * h₀ x| ≤ C₂) ∧
      ∀ x y, |h₀ (x + y) + h₀ (x - y) - 2 * h₀ x - 2 * h₀ y| ≤ Cp := by
  classical
  obtain ⟨A, f, G, e, hc, hA, he⟩ := exists_ratModel_pointEquiv
  obtain ⟨F, hF, hNF, ⟨P⟩⟩ := hA.exists_numberField_symmetricFiniteFrame f G hc
  let : Field F := hF
  let : NumberField F := hNF
  let b := Spec.map (CommRingCat.ofHom (algebraMap ℚ F))
  let : Epi b := Flat.epi_of_flat_of_surjective b
  let extend : Scheme.KPoint f → Scheme.KPoint (RelativeGroupLaw.baseChangeStr b f) :=
    fun x => RelativeGroupLaw.baseChangePointOfBase b
      (GoodReductionJacobian.schemeHomOverComp b (Category.comp_id _) x)
  let j : ↥M → Scheme.KPoint (RelativeGroupLaw.baseChangeStr b f) := fun x => extend (e x)
  have hj : Function.Injective j := by
    intro x y h
    apply e.injective
    apply Subtype.ext
    apply (cancel_epi b).mp
    have h' := congrArg (fun z => (RelativeGroupLaw.baseChangePointToBase b z).1) h
    simpa only [j, extend, RelativeGroupLaw.baseChangePointToBase_ofBase,
      GoodReductionJacobian.schemeHomOverComp] using h'
  have hm (x y : ↥M) : j (x + y) = (G.baseChange b).mul (𝟙 _) (j x) (j y) := by
    apply (RelativeGroupLaw.baseChangePointEquiv b (𝟙 _)).injective
    simp only [j, extend, RelativeGroupLaw.baseChangePointEquiv,
      Equiv.coe_fn_mk, RelativeGroupLaw.baseChangePointToBase_ofBase,
      RelativeGroupLaw.baseChangePointToBase_mul]
    rw [he]
    exact G.mul_natural (𝟙 _) (𝟙 _ ≫ b) b (Category.comp_id _)
      (e x) (e y)
  have hz : j 0 = (G.baseChange b).one (𝟙 _) := by
    let := (G.baseChange b).pointGroup (𝟙 _)
    have h := hm 0 0
    change j (0 + 0) = j 0 * j 0 at h
    have hz' : j 0 * 1 = j 0 * j 0 := by simpa using h
    exact (mul_left_cancel hz').symm
  have hn (y : ↥M) : j (-y) = (G.baseChange b).inv (𝟙 _) (j y) := by
    let := (G.baseChange b).pointGroup (𝟙 _)
    apply mul_left_cancel (a := j y)
    change (G.baseChange b).mul (𝟙 _) (j y) (j (-y)) =
      (G.baseChange b).mul (𝟙 _) (j y) ((G.baseChange b).inv (𝟙 _) (j y))
    rw [← hm, add_neg_cancel, hz, (G.baseChange b).mul_inv_cancel]
  obtain ⟨C₂, _, hd⟩ := P.exists_bounded_double
  obtain ⟨Cp, _, hp⟩ := P.exists_bounded_parallelogram
  refine ⟨fun x => P.height (j x), C₂, Cp, ?_, ?_, ?_, ?_⟩
  · intro x
    exact P.presentation.pointLogHeight_nonneg (j x)
  · intro B
    exact (P.northcott_height B).preimage hj.injOn
  · intro x
    simpa only [hm] using hd (j x)
  · intro x y
    simpa only [sub_eq_add_neg, hm, hn] using hp (j x) (j y)

end N25
