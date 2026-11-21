-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.inverse_fifth_derivative_coefficient_le
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:48:28.875913+00:00
-- url     : https://prove2.me/submissions/efeb8c93-81d3-42df-b7ea-d5981426d175

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz


theorem solution
    (c : NewtonianPointSource) (x : Vec3) (d M : ℝ)
    (hd : 0 < d)
    (hclear : d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ M) :
    3 * c.gravitationalParameter / euclideanRadius x ^ 5 ≤
      3 * M / d ^ 5 := by
  have hp : 0 < d ^ 5 := pow_pos hd _
  have hpow : d ^ 5 ≤ euclideanRadius x ^ 5 := by gcongr
  have hden : 0 ≤ euclideanRadius x ^ 5 := (hp.le.trans hpow)
  have hM0 : 0 ≤ M := c.gravitationalParameter_nonneg.trans hM
  calc
    3 * c.gravitationalParameter / euclideanRadius x ^ 5 ≤
        3 * M / euclideanRadius x ^ 5 :=
      div_le_div_of_nonneg_right (by linarith) hden
    _ ≤ 3 * M / d ^ 5 := div_le_div_of_nonneg_left (by positivity) hp hpow
