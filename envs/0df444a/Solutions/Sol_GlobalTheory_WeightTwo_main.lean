-- Prove2me | solution 1 for GlobalTheory.WeightTwo.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:24:50.162101+00:00
-- url     : https://prove2.me/submissions/4817544f-9988-4586-a9a3-8b010419c89b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecFinsum
import Theorems.Thm_GlobalTheory_WeightTwo_level
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_GlobalTheory_app_sec_eq_zero_of_sval
import Theorems.Thm_GlobalTheory_sec_eq_zero_of_thickenings_of_section
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.WeightTwo
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
namespace GlobalTheory.WeightTwo
theorem _root_.solution : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (k l : ℕ) (d : ∀ p : D.X × D.X, LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB p.1 i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB p.2 i)) (Sum.elim (DegPre.famε k) (DegPre.famε l)))), (∀ e : ℕ, ∃ s₀ : Finset D.X, ∀ s : Finset D.X, s₀ ⊆ s → ∀ (T : Over (Spec (CommRingCat.of V))) (x y : T ⟶ D.P.A) (xe ye : T.left ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (U.gt e).pG.left = x.left → ye ≫ (U.gt e).pG.left = y.left → xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom = ye ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom → ∀ (z : T.left) (J), Good D.P.L z J → ∑ α ∈ s, ∑ β ∈ s, sval (d (α, β)) (lift x y).left z J * ((val ((U.gt e).t α) xe z J).val * (val ((U.gt e).t β) ye z J).val) = 0) → ∀ p j, (d p).f j = 0) := by
  classical
  intro V _ _ _ hV D A G _ _ U k l d H p j
  have := hV.1
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : Smooth (D.P.A ⊗ D.P.A).hom := inferInstanceAs (Smooth (pullback.fst D.P.A.hom D.P.A.hom ≫ D.P.A.hom))
  have : GeometricallyConnected (D.P.A ⊗ D.P.A).hom := by
    change GeometricallyConnected (pullback.fst D.P.A.hom D.P.A.hom ≫ D.P.A.hom)
    exact GeometricallyConnected.comp _ _
  refine sec_eq_zero_of_thickenings_of_section V (IsLocalRing.maximalIdeal V)
    (IsLocalRing.maximalIdeal_le_jacobson _) (D.P.A ⊗ D.P.A) (lift η[D.P.A] η[D.P.A]) _
    (DVR.linComb_isLB D.P.L D.P.isLB _ _) (d p) (fun e j => app_sec_eq_zero_of_sval D.P.isLB (d p) _ ?_ j) j
  obtain ⟨s₀, hs⟩ := H e
  exact level (U.gt e) k l d (insert p.1 (insert p.2 s₀))
    (hs _ ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))) p.1 (Finset.mem_insert_self _ _) p.2
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) _ _
    ⟨pullback.snd _ _, pullback.condition.symm⟩
end GlobalTheory.WeightTwo
