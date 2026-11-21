-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.inverse_power_parameter_le_of_clearance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:03.835038+00:00
-- url     : https://prove2.me/submissions/ad2c28c3-34a5-4ec9-ad5e-e585e2074e9f

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_BaselineBounds

set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x : Vec3) (d M : ℝ) (n : ℕ)
    (hd : 0 < d)
    (hclear : d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ M) :
    c.gravitationalParameter / euclideanRadius x ^ n ≤
      M / d ^ n := by
  have hr : 0 < euclideanRadius x := lt_of_lt_of_le hd hclear
  have hdpow : 0 < d ^ n := pow_pos hd n
  have hrpow : 0 < euclideanRadius x ^ n := pow_pos hr n
  have hpow : d ^ n ≤ euclideanRadius x ^ n :=
    pow_le_pow_left₀ (le_of_lt hd) hclear n
  have hMnonneg : 0 ≤ M :=
    le_trans c.gravitationalParameter_nonneg hM
  apply (div_le_div_iff₀ hrpow hdpow).2
  exact (mul_le_mul_of_nonneg_right hM (le_of_lt hdpow)).trans
    (mul_le_mul_of_nonneg_left hpow hMnonneg)
end NewtonianPointSource
end NewtonianLipschitz
