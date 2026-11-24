-- Prove2me | solution 1 for GlobalTheory.UnifTransport.hermForm_eq_of_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:13:19.223302+00:00
-- url     : https://prove2.me/submissions/9d720894-88fe-4ef0-a342-0e333e2548eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolUnifReparam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TransportThetaLevelUniformisationCoordinates
import Theorems.Thm_GlobalTheory_UnifTransport_hermForm_smul_left
import Theorems.Thm_GlobalTheory_UnifTransport_hermForm_add_left
import Theorems.Thm_GlobalTheory_UnifTransport_hermForm_add_right
import Theorems.Thm_GlobalTheory_UnifTransport_hermForm_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.UnifTransport
namespace GlobalTheory.UnifTransport
theorem _root_.solution {g : ℕ} (H H' : Matrix (Fin g) (Fin g) ℂ)
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (him : ∀ x ∈ S, ∀ y ∈ S, (hermForm H' (h x) (h y)).im = (hermForm H x y).im) (z w : Fin g → ℂ) :
    hermForm H' (h z) (h w) = hermForm H z w := by
  have first : ∀ y ∈ S, ∀ x, (hermForm H' (h x) (h y)).im = (hermForm H x y).im := by
    intro y hy
    let f₁ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => (hermForm H' (h x) (h y)).im
        map_add' := fun a c => by simp only [map_add, hermForm_add_left, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, map_smul, hermForm_smul_left, Complex.im_ofReal_mul] }
    let f₂ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => (hermForm H x y).im
        map_add' := fun a c => by simp only [hermForm_add_left, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, hermForm_smul_left, Complex.im_ofReal_mul] }
    have hf : f₁ = f₂ := LinearMap.ext_on hS (fun x hx => him x hx y hy)
    exact fun x => LinearMap.congr_fun hf x
  have both : ∀ x y, (hermForm H' (h x) (h y)).im = (hermForm H x y).im := by
    intro x
    let f₁ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => (hermForm H' (h x) (h y)).im
        map_add' := fun a c => by simp only [map_add, hermForm_add_right, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, map_smul, hermForm_smul_right, Complex.star_def, Complex.conj_ofReal,
            Complex.im_ofReal_mul] }
    let f₂ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => (hermForm H x y).im
        map_add' := fun a c => by simp only [hermForm_add_right, Complex.add_im]
        map_smul' := fun r a => by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← Complex.coe_smul, hermForm_smul_right, Complex.star_def, Complex.conj_ofReal,
            Complex.im_ofReal_mul] }
    have hf : f₁ = f₂ := LinearMap.ext_on hS (fun y hy => first y hy x)
    exact fun y => LinearMap.congr_fun hf y
  apply Complex.ext
  ·
    have hI := both (Complex.I • z) w
    rw [map_smul, hermForm_smul_left, hermForm_smul_left, Complex.I_mul_im, Complex.I_mul_im] at hI
    exact hI
  · exact both z w
end GlobalTheory.UnifTransport
