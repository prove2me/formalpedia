-- Prove2me | solution 1 for GlobalTheory.WeilCube.comm_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:34.409515+00:00
-- url     : https://prove2.me/submissions/74c6f2c3-98be-44df-a0e3-fd501219f766

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory.WeilCube
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)
namespace GlobalTheory.WeilCube
theorem _root_.solution {G U : Type} [CommGroup G] [CommGroup U] {θ : G → G → G → U} (h : IsCub θ) {k : ℕ} {a b : G}
    (ha : a ^ k = 1) (hb : b ^ k = 1) (s : G) (p q e : U) (he : e * cubN θ k 1 a b = cubN θ k 1 b a) :
    cubN θ k 1 a s * p * (cubN θ k 1 b (a * s) * q) = cubN θ k 1 b s * q * (cubN θ k 1 a (b * s) * p) * e := by
  have e₁ := h.N_add k 1 a b s
  have e₂ := h.N_add k 1 b a s
  rw [ha, _root_.one_mul, h.face] at e₁
  rw [hb, _root_.one_mul, h.face, h.s01 b a] at e₂
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul he
  simp only [ofMul_mul, ofMul_one] at *
  linear_combination (norm := abel) a₂ - a₁ - a₃
end GlobalTheory.WeilCube
