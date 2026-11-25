-- Prove2me | solution 1 for GlobalTheory.WeilCube.exists_gen_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:10.884624+00:00
-- url     : https://prove2.me/submissions/91a76a47-d82e-4228-b5e6-2cf329727791

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen


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
theorem _root_.solution {T : Over S} (k : ℕ) (x y : T ⟶ A) (hx : x ^ k = 1) :
    ∃ t : LB.Gen (LB.LinComb Lr.L (K := Fin 4) ![(x * y).left, x.left, y.left, (1 : T ⟶ A).left] ![-k, k, k, -k]),
      t.IsGen ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good Lr.L z J →
        val t ρ.left z J = cubN (cubV c z J) k 1 (ρ ≫ x) (ρ ≫ y) := by
  obtain ⟨t, ht, hv⟩ := exists_cubN c (1 : T ⟶ A) x y k
  obtain ⟨t', ht', hv'⟩ := exists_gen Lr.isLB (φ' := ![(x * y).left, x.left, y.left, (1 : T ⟶ A).left])
    (ε' := ![-k, k, k, -k]) (fun U _ h => by
      rw [hx]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_pow]
      abel) t ht
  refine ⟨t', ht', fun T' ρ z J hJ => (hv' _ _ z J hJ).trans ((hv T' ρ z J hJ).trans ?_)⟩
  rw [MonObj.comp_one]
end GlobalTheory.WeilCube
