-- Prove2me | solution 1 for GlobalTheory.LN.Cmp.exists_comp_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:20:30.709574+00:00
-- url     : https://prove2.me/submissions/4b7c5754-8247-4e87-9268-3249efc1c35e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsComparisonCompAlongIdentity
import Theorems.Thm_P2M_GlobalTheory_LN_Cmp_O__baseChange_149e51dc56c0
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_exists_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pgen_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
open GlobalTheory GlobalTheory.LN GlobalTheory.LN.Cmp
namespace GlobalTheory.LN.Cmp
theorem _root_.solution : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D₁ D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A₁ A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U₁ : PreU I' D₁ A₁ G') (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C₁ : Cmp φ U U₁ F) (C₂ : Cmp (RingHom.id V) U₁ U' (𝟙 G'.left)) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F C₁.pb.1.w wL → (∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (j : U.P.L.L.ι) (i : U₁.P.L.L.ι) (k : U'.P.L.L.ι), F (r z) ∈ U.P.L.L.U j → r z ∈ U₁.P.L.L.U i → r z ∈ U'.P.L.L.U k → gw wL r z j k = gw C₁.wL r z j i * gw C₂.wL r z i k) → ∃ C : Cmp φ U U' F, C.wL = wL := by
  intro R V _ _ _ _ I I' φ D D₁ D' A A₁ A' G _ _ G' _ _ U U₁ U' F C₁ C₂ wL hmap hw
  have g₁ := (isGen_iff _).1 C₁.v_gen
  have g₂ := (isGen_iff _).1 C₂.v_gen
  obtain ⟨v, T⟩ := exists_comp D₁.P.isLB C₁.v C₂.v g₁ g₂ D.P.isLB D'.P.isLB
  have pbB : IsGrpPullback D'.P.A D.P.A (spMap φ) (C₂.β ≫ C₁.β) := by
    have h := C₂.pbB.comp C₁.pbB
    rwa [spMap_ringHom_id, Category.id_comp] at h
  refine ⟨{
    pb := C₁.pb
    wL := wL
    wL_map := hmap
    β := C₂.β ≫ C₁.β
    pbB := pbB
    v := v
    v_gen := (isGen_iff _).2 (T.pgen_comp D₁.P.isLB g₁ g₂)
    xe := C₂.xe.trans C₁.xe
    c_pr := fun x => by
      rw [← Category.assoc, C₂.c_pr, spMap_ringHom_id, Category.id_comp, C₁.c_pr]
      rfl
    lev := fun e Z x' x hx => ?_
    map_le := C₁.map_le }, rfl⟩
  obtain ⟨a₁, b₁⟩ := C₁.lev e Z x' x hx
  obtain ⟨a₂, b₂⟩ := C₂.lev e Z x' x' (by rw [Category.comp_id])
  refine ⟨by rw [← a₁, reassoc_of% a₂], fun z J J' hJ hJ' => ?_⟩
  obtain ⟨J₁, hJ₁⟩ := exists_good_pt D₁.P.isLB z
  obtain ⟨c₁, d₁⟩ := b₁ z J J₁ hJ hJ₁
  obtain ⟨c₂, d₂⟩ := b₂ z J₁ J' hJ₁ hJ'
  have tri : ∀ f : Z ⟶ D'.P.A.left, gw v f z (J (f ≫ C₂.β ≫ C₁.β)) (J' f) =
      gw C₁.v (f ≫ C₂.β) z (J (f ≫ C₂.β ≫ C₁.β)) (J₁ (f ≫ C₂.β)) * gw C₂.v f z (J₁ (f ≫ C₂.β)) (J' f) :=
    fun f => T Z f z _ _ _ (hJ (f ≫ C₂.β ≫ C₁.β)) (hJ₁ (f ≫ C₂.β)) (hJ' f)
  refine ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩
  · have hp : (U'.gt e).pG.left ≫ C₂.β = 𝟙 _ ≫ (U₁.gt e).pG.left := by
      have := (C₂.lev e _ (𝟙 _) (𝟙 _) (by rw [Category.comp_id])).1
      rwa [Category.id_comp] at this
    have o : ∀ κ, D'.Oφ (U'.gt e).pG χ κ ≫ C₂.β = D₁.Oφ (U₁.gt e).pG (C₂.xe χ) κ := fun κ =>
      (Oφ_baseChange C₂.pbB (C₂.c_pr χ) _ _ _ hp κ).trans (Category.id_comp _)
    refine (c₁ (C₂.xe χ)).trans ?_
    rw [c₂ χ, _root_.mul_assoc, ← Finset.prod_mul_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun κ _ => ?_)
    have t := tri (x' ≫ D'.Oφ (U'.gt e).pG χ κ)
    simp only [Category.assoc] at t
    rw [t, mul_zpow, mul_comm, ← o κ]
    simp only [Category.assoc]
  · obtain ⟨i, hi⟩ := exists_chart U₁.P.L.isLB ((fstG I' e G').left (x' z))
    have t := tri (x' ≫ (U'.gt e).pG.left)
    simp only [Category.assoc] at t
    have a : x' ≫ (U'.gt e).pG.left ≫ C₂.β ≫ C₁.β = x ≫ (U.gt e).pG.left := by rw [← a₁, reassoc_of% a₂]
    rw [a, a₂] at t
    have hk₂ : F ((x' ≫ (fstG I' e G').left) z) ∈ U.P.L.L.U k := by
      have : F ((x' ≫ (fstG I' e G').left) z) = (fstG I e G).left (x z) :=
        (congrArg (fun q : Z ⟶ G.left => q z) hx).symm
      rw [this]; exact hk
    rw [t, hw Z (x' ≫ (fstG I' e G').left) z k i k' hk₂ hi hk', _root_.mul_assoc, d₂ i k' hi hk',
      ← _root_.mul_assoc, d₁ k i hk hi, _root_.mul_assoc]
end GlobalTheory.LN.Cmp
