-- Prove2me | solution 1 for GlobalTheory.WeilCube.exists_isRatio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:12:09.297865+00:00
-- url     : https://prove2.me/submissions/897bc8c7-e28c-46da-b0e0-9c297488c55b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Theorems.Thm_GlobalTheory_WeilCube_exists_gen_torsion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


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
theorem _root_.solution (k : ℕ) {T : Over S} (x y : T ⟶ A) (hx : x ^ k = 1) (hy : y ^ k = 1) :
    ∃ e, IsRatio c k x y e := by
  obtain ⟨t₁, h₁, v₁⟩ := exists_gen_torsion c k x y hx
  obtain ⟨t₂, h₂, v₂⟩ := exists_gen_torsion c k y x hy
  obtain ⟨t, -, hv⟩ := exists_gen Lr.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      rw [mul_comm y x]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_pow]
      abel)
    (LB.mulGen Lr.L _ _ _ _ t₂ (LB.invGen Lr.L _ _ t₁))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₂ (DVR.invGen_isGen _ _ _ _ h₁))
  have le : (⊤ : T.left.Opens) ≤ LB.wchart Lr.L (PEmpty.elim : PEmpty → (T.left ⟶ A.left)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun T' ρ z J hJ => ?_⟩
  have e := hv _ ρ.left z J hJ
  rw [val_mul hJ, val_inv, v₁ T' ρ z J hJ, v₂ T' ρ z J hJ, val_of t ρ.left z J PEmpty.elim (fun k => k.elim)] at e
  exact (congrArg (· * _) ((gm_res ρ.left z le trivial _).trans e)).trans (inv_mul_cancel_right _ _)
end GlobalTheory.WeilCube
