-- Prove2me | solution 1 for GlobalTheory.ConvOfProd.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:48:48.609919+00:00
-- url     : https://prove2.me/submissions/9e714c26-bbdc-42ac-ab8e-e30a946a0de1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsProdB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSubSum
import Theorems.Thm_GlobalTheory_ConvOfProd_sum_conv
import Theorems.Thm_GlobalTheory_ConvOfProd_exists_sub_sum
import Theorems.Thm_GlobalTheory_ConvOfProd_over_eq
import Theorems.Thm_GlobalTheory_ConvOfProd_prod_mul_coord
import Theorems.Thm_GlobalTheory_LiftTest_main
import Theorems.Thm_GlobalTheory_UU_exists_isProdB
import Theorems.Thm_GlobalTheory_sval_eq_zero_of_sum_mul_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
open GlobalTheory GlobalTheory.ConvOfProd
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.ConvOfProd
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k l : ℕ) (f : ∀ α, SecBT D T k α) (g : ∀ α, SecBT D T l α) (h : ∀ α, SecBT D T (k + l) α) (σ : U.SecGT T (k + l)), U.ProdExp T f g σ → U.ExpT T (k + l) σ h → ConvT I f g h := by
  intro R _ _ I D A G _ _ U T k l f g h σ hP hE α₀
  classical
  choose p hp using fun α β => exists_isProdB R D T k l β (α - β) α (add_sub_cancel β α) (f β) (g (α - β))
  refine ⟨p α₀, hp α₀, fun e => ?_⟩
  obtain ⟨s, s', hP⟩ := hP e
  obtain ⟨s'', hE⟩ := hE e
  have key : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left),
      r ≫ (snd T D.P.A).left = x ≫ (U.gt e).pG.left → ∀ (z : Z) (J), Good D.P.L z J →
      (∀ α ∉ s, sval (f α) r z J = 0) ∧ (∀ α ∉ s', sval (g α) r z J = 0) ∧ (∀ α ∉ s'', sval (h α) r z J = 0) ∧
      ∑ α ∈ s'', sval (h α) r z J * (val ((U.gt e).t α) x z J).val =
        (∑ α ∈ s, sval (f α) r z J * (val ((U.gt e).t α) x z J).val) *
          ∑ α ∈ s', sval (g α) r z J * (val ((U.gt e).t α) x z J).val := by
    intro Z x r hr z J hJ
    let FinalForm : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (T ⊗ D.P.A).hom)
    let ro : FinalForm ⟶ T ⊗ D.P.A := Over.homMk r rfl
    let xo : FinalForm ⟶ (Over.map (thick R I e)).obj (thickObj R I e G) := Over.homMk x (over_eq (U.gt e) x r hr)
    let rG : FinalForm ⟶ T ⊗ G := lift (ro ≫ fst _ _) (xo ≫ fstG I e G)
    have e₁ : rG.left ≫ (snd T G).left = x ≫ (fstG I e G).left := congrArg (fun q : FinalForm ⟶ G => q.left) (lift_snd _ _)
    have e₂ : r ≫ (fst T D.P.A).left = rG.left ≫ (fst T G).left :=
      congrArg (fun q : FinalForm ⟶ T => q.left) (lift_fst (ro ≫ fst _ _) (xo ≫ fstG I e G)).symm
    choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
    obtain ⟨a₁, a₂, a₃⟩ := hP Z x rG.left r e₁ hr e₂ z JG J hJG hJ
    obtain ⟨b₁, b₂⟩ := hE Z x rG.left r e₁ hr e₂ z JG J hJG hJ
    exact ⟨a₁, a₂, b₁, b₂.symm.trans a₃⟩
  choose d hd using fun α => exists_sub_sum (h α) (p α) s
  let S : Finset D.X := insert α₀ (s'' ∪ Finset.image₂ (· + ·) s s')
  have hd0 := GlobalTheory.sval_eq_zero_of_sum_mul_coord R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) (Fin 4)
    (famφT D T) (DegPre.famε (k + l)) d S (fun Z x r hr z J hJ => by
      obtain ⟨-, k₂, k₃, k₄⟩ := key Z x r hr z J hJ
      have c := sum_conv s s' S (fun β => sval (f β) r z J * (val ((U.gt e).t β) x z J).val)
        (fun β => sval (g β) r z J * (val ((U.gt e).t β) x z J).val)
        (fun v hv => by rw [k₂ v hv, zero_mul])
        (fun β hβ v hv => Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hβ hv)))
      have c' : ∑ α ∈ s'', sval (h α) r z J * (val ((U.gt e).t α) x z J).val =
          ∑ α ∈ S, sval (h α) r z J * (val ((U.gt e).t α) x z J).val :=
        Finset.sum_subset (fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ ha))
          (fun a _ ha => by rw [k₃ a ha, zero_mul])
      rw [← sub_eq_zero.2 (c'.symm.trans (k₄.trans c.symm)), ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hd α Z r z J hJ, sub_mul, Finset.sum_mul]
      exact congrArg _ (Finset.sum_congr rfl fun β _ =>
        prod_mul_coord (U.gt e) (add_sub_cancel β α) (hp α β) x r hr z J hJ)) α₀ (Finset.mem_insert_self _ _)
  refine ⟨s, fun Z r hl z J hJ => ⟨fun β hβ => ?_, ?_⟩⟩
  · refine GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (p α₀ β)
      (fun Z x r hr z J hJ => ?_) Z r hl z J hJ
    have c := prod_mul_coord (U.gt e) (add_sub_cancel β α₀) (hp α₀ β) x r hr z J hJ
    rw [(key Z x r hr z J hJ).1 β hβ, zero_mul, zero_mul] at c
    exact (Units.mul_left_eq_zero _).1 c
  · have c := GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (d α₀) hd0 Z r hl z J hJ
    rw [hd α₀ Z r z J hJ] at c
    exact sub_eq_zero.1 c
end GlobalTheory.ConvOfProd
