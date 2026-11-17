-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_numberField_symmetricFiniteFrame
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:51.724193+00:00
-- url     : https://prove2.me/submissions/b54994c6-e379-4edd-be86-b3cb3f57333a

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_numberField_finiteFrame_descent
import Theorems.Thm_AlgebraicGeometry_Polarisation_exists_symmetric_finiteBySections
import Theorems.Thm_AlgebraicGeometry_Polarisation_isSymmetric_tensor_pullback_negMor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_pullback_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_quadratic_isos_of_isSymmetric
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso_monoidalV2
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_iso_tensorPow_sq_of_isSymmetric_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  NeronModelInfra GoodReductionJacobian

namespace GoodReductionJacobian.AbelianSchemePropertyBundle

/-- A finite frame descends to a number field and can be symmetrized there. -/
theorem _root_.solution {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of ℚ))
    (G : RelativeGroupLaw ℚ f) (hc : G.IsCommutative) (hA : AbelianSchemePropertyBundle ℚ f) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F),
      Nonempty (SymmetricFiniteFrame F
        (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℚ F))) f)
        (G.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℚ F))))) := by
  obtain ⟨F, hF, M, N, P, hM, hP⟩ :=
    Scheme.Modules.exists_numberField_finiteFrame_descent f hA
  letI : FiniteDimensional ℚ F := hF
  letI : NumberField F := {}
  let b := Spec.map (CommRingCat.ofHom (algebraMap ℚ F))
  have hAF : AbelianSchemePropertyBundle F (pullback.snd f b) :=
    hA.of_isPullback (IsPullback.of_hasPullback f b)
  obtain ⟨L, hL, hfinite, hsym⟩ := Polarisation.exists_symmetric_finiteBySections
    (pullback.snd f b) (G.baseChange b) M hM ⟨N, P, hP⟩
  obtain ⟨n, Q, hQ⟩ := hfinite
  obtain ⟨hdouble, hparallelogram⟩ := Polarisation.nonempty_quadratic_isos_of_isSymmetric
    F (pullback.snd f b) (G.baseChange b) (RelativeGroupLaw.IsCommutative.baseChange b hc) hAF L hL hsym
  exact ⟨F, inferInstance, inferInstance, ⟨{
    line := L
    line_isInvertible := hL
    N := n
    presentation := Q
    presentation_finite := hQ
    symmetric := hsym
    doubleIso := hdouble
    parallelogramIso := hparallelogram }⟩⟩

end GoodReductionJacobian.AbelianSchemePropertyBundle
