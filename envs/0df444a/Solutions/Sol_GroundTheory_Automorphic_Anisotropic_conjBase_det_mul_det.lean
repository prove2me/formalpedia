-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.conjBase_det_mul_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:56:07.044852+00:00
-- url     : https://prove2.me/submissions/e4a98da0-cbcc-4e43-8fb5-7c95ca67eb58

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicUnitaryRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Module Matrix TensorProduct
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Anisotropic
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
local notation "𝒩" => Fintype.card (ι × κ)
variable {R}
variable (R)
variable {R}
variable (R)
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution (H : Matrix ι ι E) (hH : IsUnit H.det) (g : unitaryPoints K E H R) :
    conjBase K E R ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).det * ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).det = 1 := by
  have hg : (((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).map (conjBase K E R))ᵀ * baseMatrix K H R *
      ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) = baseMatrix K H R := g.2
  have h := congrArg Matrix.det hg
  have hd : (((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).map (conjBase K E R)).det =
      conjBase K E R ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).det :=
    (RingHom.map_det (conjBase K E R) _).symm
  rw [det_mul, det_mul, det_transpose, hd] at h
  have hu : IsUnit (baseMatrix K H R).det := isUnit_det_baseMatrix H R hH
  have : conjBase K E R ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).det * ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).det *
      (baseMatrix K H R).det = 1 * (baseMatrix K H R).det := by
    linear_combination h
  exact hu.mul_right_cancel this
end GroundTheory.Automorphic.Anisotropic
