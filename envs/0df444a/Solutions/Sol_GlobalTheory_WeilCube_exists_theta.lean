-- Prove2me | solution 1 for GlobalTheory.WeilCube.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:27:09.77572+00:00
-- url     : https://prove2.me/submissions/8559012e-bef1-4169-98ca-b01f47ff722f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Theorems.Thm_GlobalTheory_WeilCube_exists_gen_of_chart
import Theorems.Thm_GlobalTheory_WeilCube_exists_gen_torsion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
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
include c
namespace GlobalTheory.WeilCube
theorem _root_.solution {k : ℕ} {T : Over S} (x : T ⟶ A) (hx : x ^ k = 1) (i j : Lr.L.ι)
    (hi : ∀ p, x.left p ∈ Lr.L.U i) (hj : ∀ p, (1 : T ⟶ A).left p ∈ Lr.L.U j) :
    ∃ θ : ThetaGrp A Lr.L k T, θ.pt = x := by
  have hx' : (fst T A ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨t, ht, -⟩ := exists_gen_torsion c k (fst T A ≫ x) (snd T A) hx'
  have o : (1 : T ⊗ A ⟶ A) = fst T A ≫ 1 := (MonObj.comp_one _).symm
  obtain ⟨s, hs⟩ := exists_gen_of_chart Lr.isLB (K := Fin 2) ![(fst T A ≫ x).left, (1 : T ⊗ A ⟶ A).left] ![-k, k] ![i, j]
    (fun y => Set.mem_iInter.2 fun a => by
      fin_cases a
      · exact hi _
      · show (1 : T ⊗ A ⟶ A).left y ∈ Lr.L.U j
        rw [o]; exact hj _)
  obtain ⟨u, hu, -⟩ := exists_gen Lr.isLB (K' := Fin 2) (φ' := ![(snd T A).left, (translPt A x).left]) (ε' := ![k, -k])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      have e₁ : ((fst T A ≫ x) * snd T A).left = (translPt A x).left := rfl
      simp only [Fin.prod_univ_succ, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_succ, e₁,
        Fin.prod_univ_zero]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (LB.mulGen Lr.L _ _ _ _ t s) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht hs)
  exact ⟨⟨x, u, hu⟩, rfl⟩
end GlobalTheory.WeilCube
