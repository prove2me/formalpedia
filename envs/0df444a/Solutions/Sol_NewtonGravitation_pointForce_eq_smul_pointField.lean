-- Prove2me | solution 1 for NewtonGravitation.pointForce_eq_smul_pointField
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:14:44.090726+00:00
-- url     : https://prove2.me/submissions/96601b8e-01b4-44f3-ace0-c15bae0c45d9

import Definitions.Def_NewtonGravitation_Defs

theorem solution (m₁ m₂ : ℝ) (r₁ r₂ : NewtonGravitation.Space) :
    NewtonGravitation.pointForce m₁ m₂ r₁ r₂ =
      m₂ • NewtonGravitation.pointField m₁ r₁ r₂ := by
  unfold NewtonGravitation.pointForce NewtonGravitation.pointField
  simp only [smul_smul]
  congr 1
  simp only [div_eq_mul_inv]
  ring

#print axioms solution
