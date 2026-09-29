-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.LevelModel.nonempty_poincare_baseChange_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/66cd5cc3-30fc-5d80-a1f4-dfb32cc4c6e5

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_baseChange_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel"

noncomputable section

namespace TwistBC

section foldr
variable {X : Scheme.{u}} {ι : Type*}

abbrev twistStep (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (M : X.Modules) : X.Modules :=
  (K i ^ pos i).invModule ⊗ (K i ^ neg i).module ⊗ M

def foldrTwistCongr (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) :
    ∀ (l : List ι) {M M' : X.Modules} (_ : M ≅ M'),
      l.foldr (twistStep K pos neg) M ≅ l.foldr (twistStep K pos neg) M'
  | [], _, _, e => e
  | (i :: l), _, _, e => whiskerLeftIso _ (whiskerLeftIso _ (foldrTwistCongr K pos neg l e))

theorem isInvertible_pow {I : X.IdealSheafData} (hI : I.IsInvertible) : ∀ n : ℕ, (I ^ n).IsInvertible
  | 0 => by
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
    exact Scheme.IdealSheafData.isInvertible_top
  | (n + 1) => by
    rw [pow_succ]
    exact (isInvertible_pow hI n).mul hI

theorem isInvertible_foldrTwist (K : ι → X.IdealSheafData) (pos neg : ι → ℕ)
    (hK : ∀ i, (K i).IsInvertible) :
    ∀ (l : List ι) {M : X.Modules} (_ : Scheme.Modules.IsInvertible M),
      Scheme.Modules.IsInvertible (l.foldr (twistStep K pos neg) M)
  | [], _, hM => hM
  | (i :: l), _, hM =>
    (isInvertible_pow (hK i) (pos i)).isInvertible_invModule.tensor
      ((isInvertible_pow (hK i) (neg i)).isInvertible_module.tensor (isInvertible_foldrTwist K pos neg hK l hM))

end foldr

section core
variable {X Y : Scheme.{u}}

theorem nonempty_pullback_foldrTwist_iso (f : X ⟶ Y) {n : ℕ} (K : Fin n → Y.IdealSheafData)
    (K' : Fin n → X.IdealSheafData) (pos neg : Fin n → ℕ)
    (hK : ∀ i, (K i).IsInvertible) (hK' : ∀ i, (K' i).IsInvertible) (hcomap : ∀ i, (K i).comap f = K' i) :
    Nonempty ((Scheme.Modules.pullback f).obj ((List.finRange n).foldr (twistStep K pos neg) (𝟙_ Y.Modules)) ≅
      (List.finRange n).foldr (twistStep K' pos neg) (𝟙_ X.Modules)) := by
  have hKf : ∀ i, ((K i).comap f).IsInvertible := fun i => by rw [hcomap i]; exact hK' i
  have h1inv : ∀ (Z : Scheme.{u}), (1 : Z.IdealSheafData).IsInvertible := fun Z => by
    rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  let C0 : Fin 0 → Y.IdealSheafData := fun _ => ⊤
  let a0 : Fin 0 → ℕ := fun _ => 0
  have hprod : (∏ F, C0 F ^ a0 F) = 1 := Fintype.prod_empty _
  have hprod' : (∏ F, (C0 F).comap f ^ a0 F) = 1 := Fintype.prod_empty _
  obtain ⟨eB⟩ : Nonempty ((∏ F, C0 F ^ a0 F).invModule ⊗ (∏ F, C0 F ^ a0 F).module ≅ 𝟙_ _) := by
    rw [hprod]; exact (h1inv _).nonempty_module_tensor_invModule_iso.2
  obtain ⟨eB'⟩ : Nonempty ((∏ F, (C0 F).comap f ^ a0 F).invModule ⊗ (∏ F, (C0 F).comap f ^ a0 F).module ≅ 𝟙_ _) := by
    rw [hprod']; exact (h1inv _).nonempty_module_tensor_invModule_iso.2
  obtain ⟨e4⟩ := Scheme.Modules.nonempty_pullback_foldr_twist_iso f K pos neg C0 a0 a0 hK
    (fun F => F.elim0) hKf (fun F => F.elim0)
  have hKK : (fun i => (K i).comap f) = K' := funext hcomap
  refine ⟨(Scheme.Modules.pullback f).mapIso (foldrTwistCongr K pos neg _ eB.symm) ≪≫ e4 ≪≫
    foldrTwistCongr _ pos neg _ eB' ≪≫ eqToIso ?_⟩
  rw [← hKK]

end core

section rigid
variable {A : Type u} [CommRing A] [IsLocalRing A] {P : Scheme.{u}}

theorem nonempty_rigidify_iso_self (σ : Spec (CommRingCat.of A) ⟶ P) (q : P ⟶ Spec (CommRingCat.of A))
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  obtain ⟨eD⟩ := ((hL.pullback σ).dual).1.nonempty_iso_tensorUnit_of_isLocalRing
  exact ⟨whiskerLeftIso L ((Scheme.Modules.pullback q).mapIso eD ≪≫ Scheme.Modules.pullbackTensorUnitObjIso q) ≪≫ ρ_ L⟩

end rigid

section geom
variable {X₀ X T : Scheme.{u}}

theorem comap_ker_eq_ker_of_isPullback {Z : Scheme.{u}} {iX : Z ⟶ X₀} {g : Z ⟶ T} {f : X₀ ⟶ X}
    {iY : T ⟶ X} [IsClosedImmersion iY] (H : IsPullback iX g f iY) : iY.ker.comap f = iX.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← H.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

theorem comap_ker_hom_of_iso (e : X₀ ≅ X) (y : T ⟶ X) [IsClosedImmersion y] :
    y.ker.comap e.hom = (y ≫ e.inv).ker :=
  comap_ker_eq_ker_of_isPullback (iX := y ≫ e.inv) (g := 𝟙 T) (IsPullback.of_vert_isIso ⟨by simp⟩)

end geom

end TwistBC

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (A : ValuationSubring (AlgebraicClosure ℚ))
    (M : JZeroNeronObjectAtP.LevelModel N₀ p A)

    [IsProper (toBase0 N₀ p)] [SmoothOfRelativeDimension 1 (toBase0 N₀ p)]
    (hA : A.LiesOverPrime p) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp M.ρ).toAlgebra
    ∀ [IsProper (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)
        (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)) (M.D₀.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) M.ε₀ (ResidueField ↥A)
        (M.rep.poincare.pullbackAlong ⟨pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))

      {n : ℕ} (σ : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase0 N₀ p)) (pos neg : Fin n → ℕ)
      (b : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) M.D₀.toBase)
      (hb : Nonempty ((M.rep.poincare.pullbackAlong b).L ≅
          Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom M.ρ)) M.ε₀)
            (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom M.ρ)))
            ((List.finRange n).foldr
              (fun i N => ((RelEffCartierDiv.ofPoint (toBase0 N₀ p) (σ i).1 (σ i).2).I ^ (pos i)).invModule ⊗
                ((RelEffCartierDiv.ofPoint (toBase0 N₀ p) (σ i).1 (σ i).2).I ^ (neg i)).module ⊗ N)
              (𝟙_ (pullback (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom M.ρ))).Modules))))

      (z : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))))
      (hz : ∀ i, z i ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _)
      (_ : ∀ i, z i ≫ pullback.fst (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A)) = resPt A ≫ (σ i).1)

      (bκ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (M.D₀.baseChange (ResidueField ↥A)).toBase)
      (_ : bκ.1 ≫ pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A)) = resPt A ≫ b.1),
      Nonempty ((hD₀κ.poincare.pullbackAlong bκ).L ≅
        ((List.finRange n).foldr
          (fun i N => ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (neg i)).module ⊗ N)
          (𝟙_ _))) := by
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  letI := instDecidableEqResidueFieldSemistable A
  letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp M.ρ).toAlgebra
  intro _iP hD₀κ hPκ n σ pos neg b hb z hz hzσ bκ hbκ

  let ψ : SchemeHomOver (𝟙 _ ≫ specMap (R p) (ResidueField ↥A)) (Spec.map (CommRingCat.ofHom M.ρ)) :=
    ⟨resPt A, by
      rw [Category.id_comp]
      show Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ Spec.map (CommRingCat.ofHom M.ρ) =
        Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩

  have hpost : postComp ⟨pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩ (BaseChange.overR (ResidueField ↥A) bκ) =
      postComp b ψ := Subtype.ext hbκ

  let K : Fin n → (pullback (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom M.ρ))).IdealSheafData := fun i =>
    (RelEffCartierDiv.ofPoint (toBase0 N₀ p) (σ i).1 (σ i).2).I
  let K' : Fin n → (pullback (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))).IdealSheafData := fun i =>
    (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I
  have hK : ∀ i, (K i).IsInvertible := fun i => RelEffCartierDiv.isInvertible_I _
  have hK' : ∀ i, (K' i).IsInvertible := fun i => RelEffCartierDiv.isInvertible_I _

  let eκ := BaseChange.κ (toBase0 N₀ p) (ResidueField ↥A) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  let Φ := eκ.hom ≫ baseChangeSnd (toBase0 N₀ p) ψ
  have hcomap : ∀ i, (K i).comap Φ = K' i := by
    intro i
    have ha : (K i).comap (baseChangeSnd (toBase0 N₀ p) ψ) =
        (graphOver (toBase0 N₀ p) (ψ.1 ≫ (σ i).1) (by rw [Category.assoc, (σ i).2, ψ.2])).ker :=
      congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_ofPoint (toBase0 N₀ p) (σ i).1 (σ i).2 ψ.1 ψ.2)
    rw [Scheme.IdealSheafData.comap_comp, ha, TwistBC.comap_ker_hom_of_iso]
    change _ = (graphOver (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).ker
    congr 1
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc, BaseChange.κ_hom_fst, graphOver_fst_assoc, hzσ i]
    · rw [graphOver_snd, Category.assoc, BaseChange.κ_hom_snd, graphOver_snd]

  have hL := TwistBC.isInvertible_foldrTwist K pos neg hK (List.finRange n) (Scheme.Modules.isInvertible_unit _)
  obtain ⟨erig⟩ := TwistBC.nonempty_rigidify_iso_self (rigSection (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom M.ρ)) M.ε₀)
    (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom M.ρ))) hL
  obtain ⟨ecore⟩ := TwistBC.nonempty_pullback_foldrTwist_iso Φ K K' pos neg hK hK' hcomap

  refine ⟨(Scheme.Modules.pullback _).mapIso hPκ.some ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (BaseChange.baseChangeSnd_κ_hom (toBase0 N₀ p) (ResidueField ↥A) bκ)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback eκ.hom).mapIso
      ((M.rep.poincare.pullbackAlongPullbackAlongIso' _ (BaseChange.overR (ResidueField ↥A) bκ)) ≪≫ eqToIso (by rw [hpost]) ≪≫
        (M.rep.poincare.pullbackAlongPullbackAlongIso' b ψ).symm ≪≫
        (Scheme.Modules.pullback _).mapIso (hb.some ≪≫ erig)) ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫ ecore⟩

end

#print axioms solution

end S_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_baseChange_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_baseChange_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist (solution)
