-- Prove2me | solution 1 for GlobalTheory.TorsionCharacter.exists_lie_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:25:40.947958+00:00
-- url     : https://prove2.me/submissions/449a2377-ee21-4b8f-831a-24530f8e0a89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LieEig
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Theorems.Thm_GlobalTheory_TorsionCharacter_isMapOf_baseChange
import Theorems.Thm_GlobalTheory_TorsionCharacter_isTan_iff
import Theorems.Thm_GlobalTheory_ChartBaseChange_isUnivChart_baseChange
import Theorems.Thm_GlobalTheory_ChartBaseChange_jetCoeff_zR
import Theorems.Thm_GlobalTheory_ChartBaseChange_push_injective
import Theorems.Thm_GlobalTheory_ChartBaseChange_push_left
import Theorems.Thm_GlobalTheory_ChartBaseChange_push_mul
import Theorems.Thm_GlobalTheory_ChartBaseChange_push_one
import Theorems.Thm_GlobalTheory_ChartBaseChange_push_surjective
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_dualLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCharacter
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.JetSer GlobalTheory.ChartBaseChange ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback isGrpPullback_pullback)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (Pt comp1)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
namespace GlobalTheory.TorsionCharacter
theorem _root_.solution (hJ : JetAlgSt) (hD : DLinSt) {V O : Type} [CommRing V] [IsLocalRing V] [CommRing O]
    (f : V →+* O) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] {d : ℕ} (x : JetSer.Fam G (Fin d))
    (hx : IsUnivChart G d x) (Gt : Over (Spec (CommRingCat.of O))) [GrpObj Gt]
    (J : (specO O (DualNumber O) ⟶ Gt) → (specV f (DualNumber O) ⟶ G))
    (hmul : ∀ w w', J (w * w') = J w * J w') (hinj : Function.Injective J)
    (hnat : ∀ (φ : DualNumber O →ₐ[O] DualNumber O) w,
      (J (ptMap φ ≫ w)).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (J w).left)
    (hsurj : ∀ g : specV f (DualNumber O) ⟶ G, Spec.map (CommRingCat.ofHom (fstD O).toRingHom) ≫ g.left =
      Spec.map (CommRingCat.ofHom (fstD O).toRingHom) ≫ (1 : specV f (DualNumber O) ⟶ G).left → ∃ w, J w = g) :
    ∃ (co : LieG Gt → Fin d → O) (tv : (Fin d → O) → LieG Gt), (∀ s, (fun w => co w s) ∈ omega Gt) ∧
      (∀ b, co (tv b) = b) ∧
      (∀ b, ∃ φ : JetR V (Fin d) 1 →+* DualNumber O, (∀ i, φ (zR 1 i) = TrivSqZeroExt.inr (b i)) ∧
        (J (tv b).1).left = Spec.map (CommRingCat.ofHom φ) ≫ (x 1).left) ∧
      ∀ (u : G ⟶ G) [IsMonHom u] (ut : Gt ⟶ Gt) (α : Pt V 1 d), IsMapOf x x u α → (∀ w, J (w ≫ ut) = J w ≫ u) →
        ∀ (b : Fin d → O) (a : O), ((dLin α).map f).mulVec b = a • b →
          (tv b).1 ≫ ut = ptMap (dualScale a) ≫ (tv b).1 := by
  letI : Algebra V O := f.toAlgebra
  letI alg : Algebra V (DualNumber O) := ((algebraMap O (DualNumber O)).comp f).toAlgebra
  haveI tow : @IsScalarTower V O (DualNumber O) _ _ alg.toSMul :=
    IsScalarTower.of_algebraMap_eq (R := V) (S := O) (A := DualNumber O) fun _ => rfl
  let j := Spec.map (CommRingCat.ofHom (algebraMap V O))
  let G' := (Over.pullback j).obj G
  have hπ : IsGrpPullback G' G j (pullback.fst G.hom j) := isGrpPullback_pullback G j
  choose x' hx' using fun m => push_surjective hπ (Chart.spMap (jetCoeff V O (Fin d) m) ≫ x m)
  have hu := isUnivChart_baseChange hπ hx hx'
  choose K hK using fun w => push_surjective (A := DualNumber O) hπ (J w)
  have hK' : ∀ w, (K w).left ≫ pullback.fst G.hom j = (J w).left := fun w => congrArg (·.left) (hK w)
  have Kmul : ∀ w w', K (w * w') = K w * K w' := fun w w' =>
    push_injective hπ (by rw [push_mul, hK, hK, hK]; exact hmul w w')
  have Kinj : Function.Injective K := fun w w' h => hinj (by rw [← hK, ← hK, h])
  have Knat : ∀ (φ : DualNumber O →ₐ[O] DualNumber O) w, K (ptMap φ ≫ w) = ptMap φ ≫ K w := fun φ w =>
    push_injective hπ (Over.OverMorphism.ext (by
      rw [push_left, push_left, hK', hnat, Over.comp_left, Category.assoc, hK']; rfl))
  have htan := isTan_iff K Kmul Kinj Knat
  have lie : ∀ w : specO O (DualNumber O) ⟶ Gt,
      (ptMap (TrivSqZeroExt.fstHom O O O) ≫ w = toUnit (specO O O) ≫ η[Gt]) ↔ IsTan w := fun w => Iff.rfl
  have ex : ∀ b : Fin d → O, ∃ w : LieG Gt, K w.1 = Chart.spMap (dualLift b) ≫ x' 1 := fun b => by
    obtain ⟨w, hw⟩ := hsurj (push hπ (Chart.spMap (dualLift b) ≫ x' 1)) (by
      have h := congrArg (·.left ≫ pullback.fst G.hom j) (isTan_dualLift hu b)
      have h1 := congrArg (·.left) (push_one (A := DualNumber O) hπ)
      have h2 : Chart.spMap (fstD O) ≫ (1 : sp (R₀ := O) (DualNumber O) ⟶ G') = 1 := MonObj.comp_one _
      rw [← h2] at h
      simp only [Over.comp_left, Category.assoc] at h
      rw [push_left] at h1
      rw [h1] at h
      exact h)
    have e : K w = Chart.spMap (dualLift b) ≫ x' 1 := push_injective hπ ((hK w).trans hw)
    exact ⟨⟨w, (lie w).2 ((htan w).2 (e ▸ isTan_dualLift hu b))⟩, e⟩
  choose tv htv using ex
  let co : LieG Gt → Fin d → O := fun w => tcoord hu (K w.1) ((htan _).1 ((lie _).1 w.2))
  have hco : ∀ b, co (tv b) = b := fun b => tcoord_eq hu _ _ b (htv b)
  refine ⟨co, tv, fun s => ⟨fun w w' h => ?_, fun a w h => ?_⟩, hco, fun b => ?_, ?_⟩
  · have := tcoord_mul hu ((htan _).1 ((lie _).1 w.2)) ((htan _).1 ((lie _).1 w'.2))
    exact (congrFun (Chart.tcoord_congr hu (Kmul _ _) _ _) s).trans (congrFun this s)
  · have := tcoord_scale hu a ((htan _).1 ((lie _).1 w.2))
    exact (congrFun (Chart.tcoord_congr hu (Knat _ _) _ _) s).trans (congrFun this s)
  · refine ⟨(dualLift b).toRingHom.comp (jetCoeff V O (Fin d) 1).toRingHom, fun i => ?_, ?_⟩
    · show dualLift b (jetCoeff V O (Fin d) 1 (zR 1 i)) = _
      rw [jetCoeff_zR, dualLift_zR]
    · have h : (x' 1).left ≫ pullback.fst G.hom j = _ := congrArg (·.left) (hx' 1)
      rw [← hK', htv, Over.comp_left, Category.assoc, h, Over.comp_left, ← Category.assoc, Chart.spMap_left, Chart.spMap_left, ← Spec.map_comp]
      rfl
  · intro u _ ut α hα hut b a hb
    let u' : G' ⟶ G' := (Over.pullback j).map u
    have hu' : u'.left ≫ pullback.fst G.hom j = pullback.fst G.hom j ≫ u.left := pullback.lift_fst _ _ _
    have hm := isMapOf_baseChange hπ hJ hx' u u' α hu' hα
    have ht := (htan _).1 ((lie _).1 (tv b).2)
    have h := hD O G' G' d x' x' hu hu u' _ hm (K (tv b).1) ht (Chart.isTan_comp ht u')
    have h2 : dLin (fun i => MvPowerSeries.map (algebraMap V O) (α i)) = (dLin α).map f := by
      ext i k
      simp [dLin, RingHom.algebraMap_toAlgebra]
    have h3 : tcoord hu (K (tv b).1) ht = b := hco b
    rw [h2, h3, hb] at h
    have h4 := tcoord_scale hu a ht
    rw [h3] at h4
    apply Kinj
    rw [Knat]
    have e1 : K ((tv b).1 ≫ ut) = K (tv b).1 ≫ u' := push_injective hπ (Over.OverMorphism.ext (by
      rw [push_left, push_left, hK', hut, Over.comp_left, Over.comp_left, Category.assoc, hu', ← Category.assoc, hK']))
    rw [e1, tcoord_spec hu _ (Chart.isTan_comp ht u'), h, ← h4]
    exact (tcoord_spec hu _ _).symm
end GlobalTheory.TorsionCharacter
