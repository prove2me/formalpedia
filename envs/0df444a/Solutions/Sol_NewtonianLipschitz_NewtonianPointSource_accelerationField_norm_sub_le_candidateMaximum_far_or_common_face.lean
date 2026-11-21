-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_far_or_common_face
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:15:56.182176+00:00
-- url     : https://prove2.me/submissions/5efffaea-1683-4b7f-b5c4-c2de1a5b8190

module
public import Definitions.Def_NewtonianLipschitz_LongSeparation
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_common_face
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_long


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x y : Vec3) (d : ℝ)
    (hd : 0 < d)
    (hx : d ≤ ‖x‖) (hy : d ≤ ‖y‖)
    (hcases : d ≤ ‖x - y‖ ∨
      ∃ i : Fin 3,
        (d ≤ x i ∧ d ≤ y i) ∨
        (x i ≤ -d ∧ y i ≤ -d)) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) * (c.gravitationalParameter * candidateMaximum)) *
        ‖x - y‖ := by
  rcases hcases with hfar | hface
  · exact c.accelerationField_norm_sub_le_candidateMaximum_long
      x y d hd hx hy hfar
  · exact c.accelerationField_norm_sub_le_candidateMaximum_common_face
      x y d hd hface
end NewtonianPointSource
end NewtonianLipschitz
