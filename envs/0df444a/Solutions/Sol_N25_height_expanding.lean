-- Prove2me | solution 1 for N25.height_expanding
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:44.615439+00:00
-- url     : https://prove2.me/submissions/95b9e403-c59c-4c93-82f3-97ed06866396

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_piEnd_mem_M
import Theorems.Thm_ModularCurve_galois_smul_genOpH_comm
import Theorems.Thm_N25_exists_northcott_boundedDefect_height_on_M
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
import Theorems.Thm_ModularCurve_exists_abelianSchemePropertyBundle_model_jH
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_N25_gamma_mem_M
import Definitions.Def_N25_LocalKummerEquivariance
import Theorems.Thm_N25_gamma_pow_five
import Theorems.Thm_N25_cyclotomic_gamma
import Theorems.Thm_N25_Alg_exists_canonicalQuadratic_of_boundedDefects
import Theorems.Thm_N25_Alg_exists_invariant_quadratic_of_pow_five
import Theorems.Thm_N25_Alg_quadratic_norm71_expansion

set_option autoImplicit false

noncomputable section

namespace N25

/-- Averaging a canonical height over the order-five diamond action gives expansion. -/
theorem _root_.solution :
    ∃ q : ↥N25.M → ℝ, (∀ B : ℝ, {x | q x ≤ B}.Finite) ∧
      ∀ x : ↥N25.M, (7 / 3 : ℝ) * q x ≤ q ⟨N25.piEnd x, N25.piEnd_mem_M x.2⟩ := by
  obtain ⟨h₀, C₂, Cp, hnn, hN, hd, hp⟩ := exists_northcott_boundedDefect_height_on_M
  obtain ⟨q₀, hqnn, hpar, _, hqN⟩ :=
    Alg.exists_canonicalQuadratic_of_boundedDefects h₀ hnn hN C₂ Cp hd hp
  let d : ↥M →+ ↥M :=
    { toFun := fun x => ⟨gamma x, gamma_mem_M x.2⟩
      map_zero' := Subtype.ext gamma.map_zero
      map_add' := fun x y => Subtype.ext (gamma.map_add x y) }
  have hd5 (x : ↥M) : d (d (d (d (d x)))) = x := Subtype.ext (gamma_pow_five x)
  obtain ⟨q, hnn, hpar, hinv, hN⟩ :=
    Alg.exists_invariant_quadratic_of_pow_five d hd5 q₀ hqnn hpar hqN
  refine ⟨q, hN, ?_⟩
  intro x
  have hphi (y : ↥M) : y + d y + d (d y) + d (d (d y)) + d (d (d (d y))) = 0 :=
    Subtype.ext (cyclotomic_gamma y)
  have h := Alg.quadratic_norm71_expansion d hphi q hpar hinv hnn x
  have heq : 2 • x + 4 • d x + d (d x) = ⟨piEnd x, piEnd_mem_M x.2⟩ := by
    apply Subtype.ext
    rfl
  rw [heq] at h
  exact h

end N25
