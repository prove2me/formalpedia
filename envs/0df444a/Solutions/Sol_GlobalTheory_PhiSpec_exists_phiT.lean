-- Prove2me | solution 1 for GlobalTheory.PhiSpec.exists_phiT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:18:01.179+00:00
-- url     : https://prove2.me/submissions/156a0b59-c1b2-4719-8954-3a25c4c82452

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiSpecialises
import Theorems.Thm_GlobalTheory_PhiSpec_gen_uT
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PhiSpec
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
variable {D}
namespace GlobalTheory.PhiSpec
theorem _root_.solution {k : ℕ} (y : D.X) (gp : GtPt D T) (hy : cP D T y = gp.b ^ k)
    (w : LB.Gen (LB.LinComb D.P.L (lineT D gp.b) (DegPre.lineε k))) (hw : w.IsGen) (g : ∀ α, SecT D T k α) :
    ∃ g₂ : ∀ α, SecT D T k α, PhiT y gp w g g₂ := by
  have ex : ∀ β, ∃ t : SecT D T k β, ∀ α, α + y = β →
      ∀ (T₁ : Over (Spec (CommRingCat.of R))) (ρ : T₁ ⟶ T ⊗ D.P.A) (z : T₁.left) (J),
      Good D.P.L z J → sval t ρ.left z J = sval (g α) (ρ ≫ trT D gp.b).left z J *
        (uT D k α gp.b ρ z J * (val (gp.s α) (ρ ≫ fst _ _).left z J * val w (ρ ≫ fst _ _).left z J)).val := by
    intro β
    obtain ⟨α₀, rfl⟩ : ∃ α₀, α₀ + y = β := ⟨β - y, sub_add_cancel _ _⟩
    obtain ⟨u, hu, hv⟩ := gen_uT D k α₀ (α₀ + y) gp.b (by rw [cPoint_add, hy]) _
      (mulGen_isGen _ _ _ _ _ _ _ (gp.isGen α₀) hw) (fun U _ h => by
        refine (Fintype.prod_sum_type _).trans ?_
        rw [Fin.prod_univ_four, Fin.prod_univ_two]
        show h (cP D _ α₀ * gp.b).left ^ (-1 : ℤ) * h (cP D _ α₀).left ^ (1 : ℤ) * h gp.b.left ^ (1 : ℤ) *
          h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) *
          (h (1 : T ⟶ D.P.A).left ^ (k : ℤ) * h gp.b.left ^ (-(k : ℤ))) = _
        simp only [zpow_neg, zpow_one, zpow_natCast]
        ac_rfl)
    obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := fun i => (snd T D.P.A).left ≫ D.famφB (α₀ + y) i)
      (ε' := DegPre.famε k) (fun U _ h => by
        refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
          (c := ∏ i, h ((trT D gp.b ≫ snd _ _).left ≫ D.famφB α₀ i) ^ DegPre.famε k i)
          (Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.famε k i) (Category.assoc _ _ _).symm)
          (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
            (c := ∏ i, h ((snd T D.P.A).left ≫ D.famφB (α₀ + y) i) ^ DegPre.famε k i) rfl (prod_neg _ _ rfl))) ?_
        exact (mul_comm _ _).trans (inv_mul_cancel_right _ _)) (pullMulSec (g α₀) (trT D gp.b).left u hu)
    refine ⟨t, fun α hα T₁ ρ z J hJ => ?_⟩
    obtain rfl : α = α₀ := add_right_cancel hα
    exact (ht _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans
      (congrArg₂ (· * ·) rfl (congrArg Units.val ((hv T₁ ρ z J hJ).trans
        (congrArg₂ (· * ·) rfl (val_mul hJ _ _ _))))))
  choose t ht using ex
  exact ⟨t, fun α β h => ht β α h⟩
end GlobalTheory.PhiSpec
