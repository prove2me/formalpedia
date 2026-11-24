-- Prove2me | solution 1 for GlobalTheory.UT.CoefPhi.cubN_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:42:31.152423+00:00
-- url     : https://prove2.me/submissions/778ffa31-cbd5-4d29-a2bf-17c90945df88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFrameRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubNMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.CoefPhi
open GlobalTheory.UT.CoefBasic
namespace GlobalTheory.UT.CoefPhi
theorem _root_.solution {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k n : ℕ) (a m x : A) :
    cubN θ (k * n) a m x = cubN θ n a (m ^ k) x * cubN θ k 1 m x ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have e : cubN θ (k * (n + 1)) a m x = cubN θ (k * n) a m x * cubN θ k (a * (m ^ k) ^ n) m x := by
      rw [Nat.mul_succ, cubN, Finset.prod_range_add, cubN, cubN]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [pow_add, pow_mul, _root_.mul_assoc]
    have e' : cubN θ (n + 1) a (m ^ k) x = cubN θ n a (m ^ k) x * θ (a * (m ^ k) ^ n) (m ^ k) x :=
      Finset.prod_range_succ _ _
    rw [e, e', ih, h.N_split k (a * (m ^ k) ^ n), pow_succ (cubN θ k 1 m x)]
    ac_rfl
end GlobalTheory.UT.CoefPhi
