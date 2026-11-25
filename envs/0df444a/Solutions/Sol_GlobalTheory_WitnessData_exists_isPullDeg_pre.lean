-- Prove2me | solution 1 for GlobalTheory.WitnessData.exists_isPullDeg_pre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:01:34.436269+00:00
-- url     : https://prove2.me/submissions/8f8781c1-cd72-42ce-b4ce-6539573952d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataIsoOfTwoWitnesses
import Theorems.Thm_GlobalTheory_WitnessData_value_of_genRel
import Theorems.Thm_GlobalTheory_WitnessData_exists_psi_pull
import Theorems.Thm_GlobalTheory_WitnessData_exists_generic_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pgen_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pmaps_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_of_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_specOf_id


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
noncomputable section
open GlobalTheory GlobalTheory.WitnessData
namespace GlobalTheory.WitnessData
theorem _root_.solution {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R] {f : O' →+* R}
    {D₀ : DegPre O'} {D D' : DegPre R} {φ : D.P.A.left ⟶ D₀.P.A.left} {φ' : D'.P.A.left ⟶ D₀.P.A.left}
    (he : eSec D.P.A ≫ φ = spMap f ≫ eSec D₀.P.A) (he' : eSec D'.P.A ≫ φ' = spMap f ≫ eSec D₀.P.A)
    {w : LB.Iso D.P.L (D₀.P.L.pull φ)} {w' : LB.Iso D'.P.L (D₀.P.L.pull φ')} (ε : D₀.X ≃+ D.X) (ε' : D₀.X ≃+ D'.X)
    (s1 : IsGrpPullback D.P.A D₀.P.A (spMap f) φ) (s1' : IsGrpPullback D'.P.A D₀.P.A (spMap f) φ')
    (s2 : w.IsGen) (s2' : w'.IsGen)
    (s3 : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1)) D.rig
      (rigPullOf φ (spMap f) he D₀.P.L D₀.rig))
    (s3' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf φ' (spMap f) he' D₀.P.L D₀.rig))
    (s5 : ∀ y, (D.c (ε y)).left ≫ φ = spMap f ≫ (D₀.c y).left)
    (s5' : ∀ y, (D'.c (ε' y)).left ≫ φ' = spMap f ≫ (D₀.c y).left)
    (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] (v : D₀.X → F)
    (k : ∀ y, GenRel w (LB.pullGen _ _ _ (D.psi (ε y)) (jFK (R := R) F))
      (LB.pullGen _ _ _ (D₀.psi y) (jFK (R := O') F)) (v y))
    (k' : ∀ y, GenRel w' (LB.pullGen _ _ _ (D'.psi (ε' y)) (jFK (R := R) F))
      (LB.pullGen _ _ _ (D₀.psi y) (jFK (R := O') F)) (v y))
    {Wo : (Spec (CommRingCat.of R)).Opens} (hWo : genericPoint (Spec (CommRingCat.of R)) ∈ Wo) (ψW : PsiOn D Wo) :
    ∃ hD : IsPullDeg (RingHom.id R) D D', (∀ y, hD.xe (ε' y) = ε y) ∧
      ∃ w'' : LB.Iso D'.P.L (D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ)),
        φ' = (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ ∧ HEq w' w'' ∧ Tri w hD.w w'' := by
  have hs := specOf_id R
  have hsf : specOf (RingHom.id R) ≫ spMap f = spMap f := by rw [hs, Category.id_comp]
  obtain ⟨e, e_hom, hφ⟩ := grpPullback_iso s1'
    (((isGrpPullback_pullback D.P.A (specOf (RingHom.id R))).comp s1).congr hsf rfl)
  let Φ := e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))
  replace hφ : Φ ≫ φ = φ' := (Category.assoc _ _ _).trans hφ
  subst hφ
  have gp : IsGrpPullback D'.P.A D.P.A (specOf (RingHom.id R)) Φ :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback D.P.A (specOf (RingHom.id R)))).congr
      (Category.id_comp _) rfl
  have hE : eSec D'.P.A ≫ Φ = specOf (RingHom.id R) ≫ eSec D.P.A := (cubeMapOf gp).e_comm
  have hw : Φ ≫ D.P.A.hom = D'.P.A.hom := by rw [gp.1.w, hs, Category.comp_id]
  have g0 := (isGen_iff w).1 s2
  have g' := (isGen_iff w').1 s2'
  obtain ⟨wD, T⟩ := exists_cancel D₀.P.isLB w w' g0 g' D.P.isLB D'.P.isLB
  let xe : D'.X ≃+ D.X := ε'.symm.trans ε
  have hxe : ∀ y, xe (ε' y) = ε y := fun y => congrArg ε (ε'.symm_apply_apply y)
  have hc : ∀ y, (D'.c (ε' y)).left ≫ Φ = (D.c (ε y)).left := fun y => by
    apply s1.1.hom_ext
    · rw [Category.assoc, s5' y, s5 y]
    · rw [Category.assoc, hw, Over.w, Over.w]
  obtain ⟨g, hg⟩ := exists_generic_lift hWo
  refine ⟨⟨e, e_hom, wD, (isGen_iff wD).2 (T.pgen_cancel D₀.P.isLB g0 g'), hE, ?_, xe, fun x => ?_, Wo, ψW, g,
    by rw [hg, hs, Category.comp_id], fun x => ?_⟩, hxe, w', rfl, HEq.rfl, T⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec D₀.P.A) _ D.rig D₀.rig (spMap f) _
      (rigPull_le φ (spMap f) he D₀.P.L) (fun _ => rfl)).1 s3
    have r₁ := (maps_iff w' _ (fun _ => eSec D₀.P.A) _ D'.rig D₀.rig (spMap f) _
      (rigPull_le (Φ ≫ φ) (spMap f) he' D₀.P.L) (fun _ => rfl)).1 s3'
    rw [← hsf] at r₁
    exact (maps_iff wD _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf (RingHom.id R)) _
      (rigPull_le Φ (specOf (RingHom.id R)) hE D.P.L) (fun _ => rfl)).2
      (T.pmaps_cancel D₀.P.isLB (fun _ => hE) r₀ r₁)
  · obtain ⟨y, rfl⟩ := ε'.surjective x
    rw [hxe]
    exact (hc y).trans ((Category.id_comp _).symm.trans (congrArg (· ≫ _) hs.symm))
  · obtain ⟨y, rfl⟩ := ε'.surjective x
    rw [hxe]
    have hx : D'.xK (ε' y) ≫ Φ = D.xK (ε y) :=
      (Category.assoc _ _ _).trans (congrArg (jK R ≫ ·) (hc y))
    refine exists_psi_pull wD ψW hg hx F fun z p q hp hq => ?_
    have v := value_of_genRel T D₀.P.isLB (fun _ => (Category.assoc _ _ _).trans (congrArg (jFK (R := R) F ≫ ·) hx))
      (k y) (k' y) z (fun _ => p) (fun _ => q) (fun _ => hp) (fun _ => hq)
    have hp' : D.xK (ε y) (jFK (R := R) F z) ∈ D.P.L.U p :=
      (congrArg (fun h => h (jFK (R := R) F z) ∈ D.P.L.U p) hx).mp hp
    have a₁ := gm_pullGen D.P.L _ _ (D.psi (ε y)) (jFK (R := R) F) (𝟙 _) z (fun _ => p) (Set.mem_iInter.2 fun _ => hp')
    have a₂ := gm_pullGen D'.P.L _ _ (D'.psi (ε' y)) (jFK (R := R) F) (𝟙 _) z (fun _ => q)
      (Set.mem_iInter.2 fun _ => hq)
    rw [Category.id_comp] at a₁ a₂
    rw [Fintype.prod_unique] at v
    exact a₁.symm.trans (v.trans (congrArg _ a₂))
end GlobalTheory.WitnessData
