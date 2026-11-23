-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Gt.pow_s
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:10.283146+00:00
-- url     : https://prove2.me/submissions/8c565084-8734-4c11-932d-eaae3f7d2f7d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
attribute [instance] NumB.grp
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.NumD
variable (N : NumD O)
open GlobalTheory.Ex.NumD.Gt
variable {N}
namespace GlobalTheory.Ex.NumD.Gt
theorem _root_.solution (g : N.Gt) (k : ℕ) (χ : N.X) : (g ^ k).s χ * cubN N.θ k 1 g.b (N.c χ) = g.s χ ^ k := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    rw [cubN] at ih
    rw [pow_succ, pow_succ, mul_s, cubN, Finset.prod_range_succ, ← ih, pow_b, one_mul, N.cub.s12 (g.b ^ k),
      N.cub.s01 (g.b ^ k), ← mul_assoc, mul_right_comm, div_mul_cancel, mul_right_comm]
end GlobalTheory.Ex.NumD.Gt
