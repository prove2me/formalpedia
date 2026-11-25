-- Prove2me | solution 1 for GlobalTheory.UU.exists_isProdB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:15:37.085244+00:00
-- url     : https://prove2.me/submissions/4adabb47-a49b-46c7-aed7-c2266424a984

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsProdB
import Theorems.Thm_GlobalTheory_UU_prod_famT
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_genSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_mulSec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (k l : ℕ) (β ga α : D.X), β + ga = α → ∀ (f : SecBT D T k β) (g : SecBT D T l ga),
    ∃ h : SecBT D T (k + l) α, IsProdB f g h := by
  intro R _ _ D T k l β ga α hα f g
  subst hα
  let a : T ⊗ D.P.A ⟶ D.P.A := DVR.cP D _ β
  let b : T ⊗ D.P.A ⟶ D.P.A := DVR.cP D _ ga
  let x : T ⊗ D.P.A ⟶ D.P.A := snd T D.P.A
  have hu := DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift a (lift b x)).left
  obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := famφT D T (β + ga)) (ε' := DegPre.famε (k + l)) (fun U _ h => by
      have p₁ := prod_cub a b x h
      have p₂ := prod_famT D T β k h
      have p₃ := prod_famT D T ga l h
      have p₄ := prod_famT D T (β + ga) (k + l) h
      rw [DVR.cPoint_add] at p₄
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₂ p₃) p₁) (Eq.trans ?_ p₄.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, a, b, x]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec f g) (genSec (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift a (lift b x)).left) hu))
  refine ⟨t, fun Z r z J hJ => ?_⟩
  refine (ht _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ) ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val
      ((val_cub D.cub r hJ a b x).trans ?_)))))
  rw [DVR.comp_cP, DVR.comp_cP]; rfl
end GlobalTheory.UU
