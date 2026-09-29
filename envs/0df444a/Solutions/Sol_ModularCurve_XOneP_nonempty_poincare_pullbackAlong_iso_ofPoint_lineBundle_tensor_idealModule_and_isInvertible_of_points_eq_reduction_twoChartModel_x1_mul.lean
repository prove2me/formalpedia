-- Prove2me | solution 1 for ModularCurve.XOneP.nonempty_poincare_pullbackAlong_iso_ofPoint_lineBundle_tensor_idealModule_and_isInvertible_of_points_eq_reduction_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/ebe6e30d-487f-5100-afe6-6a02bc702484

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicCurve_RelCartier

import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_supportedIn_ofPoint
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_iso_ofPoint_lineBundle_tensor_idealModule_and_isInvertible_of_points_eq_reduction_twoChartModel_x1_mul
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

universe u

namespace Ws50SFR

theorem comap_ker_eq_ker_of_isPullback {X₀ X T Z : Scheme.{u}} {iX : Z ⟶ X₀} {g : Z ⟶ T} {f : X₀ ⟶ X}
    {iY : T ⟶ X} [IsClosedImmersion iY] (H : IsPullback iX g f iY) : iY.ker.comap f = iX.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← H.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

noncomputable def pbComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N) ≅ (Scheme.Modules.pullback (f ≫ g)).obj N :=
  (Scheme.Modules.pullbackComp f g).app N

noncomputable def pbCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (N : Y.Modules) :
    (Scheme.Modules.pullback f).obj N ≅ (Scheme.Modules.pullback g).obj N :=
  (Scheme.Modules.pullbackCongr h).app N

noncomputable def pbTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (M ⊗ N) ≅ (Scheme.Modules.pullback f).obj M ⊗ (Scheme.Modules.pullback f).obj N :=
  (Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N).symm

end Ws50SFR

open Ws50SFR in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)

    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective πk) :
    ∀ (ξ₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j)) (ξ₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
      (u₁ u₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)),
      Set.range ξ₁.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) → Set.range ξ₂.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) →
      u₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₁.1 →
      u₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₂.1 →
      ∀ (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
        Nonempty ((hrep.some.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₁.1 ξ₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₂.1 ξ₂.2).idealModule) →
        ∀ (y : G.J0s),
          (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ s.1 →
          Nonempty ((hreps.poincare.pullbackAlong (pts y)).L ≅
            (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u₁.1 u₁.2).lineBundle ⊗
              (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u₂.1 u₂.2).idealModule) ∧
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u₁.1 u₁.2).I.IsInvertible ∧
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u₂.1 u₂.2).I.IsInvertible := by
  intro ξ₁ ξ₂ u₁ u₂ hξ₁U hξ₂U hu₁ hu₂ s hs y hy
  classical

  have hψ : Spec.map (CommRingCat.ofHom πk) ≫ Spec.map (CommRingCat.ofHom ρ) = specMap A k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hAlgk]

  set t1 : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A) := 𝟙 (Spec (CommRingCat.of k)) ≫ specMap A k with ht1
  have ht1' : t1 = specMap A k := Category.id_comp _
  let ψ' : SchemeHomOver t1 (Spec.map (CommRingCat.ofHom ρ)) := ⟨Spec.map (CommRingCat.ofHom πk), by rw [hψ, ht1']⟩

  have hover : ∀ ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j), (ψ'.1 ≫ ξ.1) ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = t1 :=
    fun ξ => (Category.assoc _ _ _).trans ((congrArg (ψ'.1 ≫ ·) ξ.2).trans ψ'.2)

  let sψ : SchemeHomOver t1 D.toBase := postComp s ψ'

  obtain ⟨⟨eL₁⟩, -⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
    A (ModularCurve.TwoChart.modelTo A (↥K) j) U ξ₁ hξ₁U ψ' (hover ξ₁)
  obtain ⟨-, ⟨eI₂⟩⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
    A (ModularCurve.TwoChart.modelTo A (↥K) j) U ξ₂ hξ₂U ψ' (hover ξ₂)

  have hcomp : baseChangeSnd (ModularCurve.TwoChart.modelTo A (↥K) j) ψ' ≫ baseChangeSnd (ModularCurve.TwoChart.modelTo A (↥K) j) s = baseChangeSnd (ModularCurve.TwoChart.modelTo A (↥K) j) sψ :=
    baseChangeSnd_comp _ s ψ'
  obtain ⟨es⟩ := hs
  let E2 : (Scheme.Modules.pullback (baseChangeSnd (ModularCurve.TwoChart.modelTo A (↥K) j) sψ)).obj hrep.some.poincare.L ≅
      (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ₁.1) (hover ξ₁)).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ₂.1) (hover ξ₂)).idealModule :=
    (pbCongr hcomp _).symm ≪≫ (pbComp _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso es ≪≫ pbTensor _ _ _ ≪≫ (eL₁ ⊗ᵢ eI₂)

  let κ1 := BaseChange.κ (ModularCurve.TwoChart.modelTo A (↥K) j) k (𝟙 (Spec (CommRingCat.of k)))
  let κD := BaseChange.κ (ModularCurve.TwoChart.modelTo A (↥K) j) k (D.baseChange k).toBase
  let σ₀ : SchemeHomOver ((D.baseChange k).toBase ≫ specMap A k) D.toBase := ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩
  have hFG : baseChangeSnd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (pts y) ≫ κD.hom ≫ baseChangeSnd (ModularCurve.TwoChart.modelTo A (↥K) j) σ₀ = κ1.hom ≫ baseChangeSnd (ModularCurve.TwoChart.modelTo A (↥K) j) sψ := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [BaseChange.baseChangeSnd_fst', BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst, BaseChange.κ_hom_fst,
        ← Category.assoc, BaseChange.baseChangeSnd_fst']
    · have L : (baseChangeSnd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (pts y) ≫ κD.hom ≫ baseChangeSnd (ModularCurve.TwoChart.modelTo A (↥K) j) σ₀) ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase =
          pullback.snd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (𝟙 _) ≫ (pts y).1 ≫ pullback.fst D.toBase (specMap A k) := by
        rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc κD.hom (pullback.snd _ _) σ₀.1,
          BaseChange.κ_hom_snd, ← Category.assoc (baseChangeSnd _ (pts y)) (pullback.snd _ _) σ₀.1, BaseChange.baseChangeSnd_snd',
          Category.assoc]
      have R' : (κ1.hom ≫ baseChangeSnd (ModularCurve.TwoChart.modelTo A (↥K) j) sψ) ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase =
          pullback.snd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (𝟙 _) ≫ ψ'.1 ≫ s.1 := by
        rw [Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc κ1.hom (pullback.snd _ _) sψ.1, BaseChange.κ_hom_snd]
        rfl
      rw [L, R', hy]

  obtain ⟨eP⟩ := hPk
  have E4 : Nonempty ((hreps.poincare.pullbackAlong (pts y)).L ≅
      (Scheme.Modules.pullback κ1.hom).obj ((Scheme.Modules.pullback (baseChangeSnd (ModularCurve.TwoChart.modelTo A (↥K) j) sψ)).obj hrep.some.poincare.L)) := by
    refine ⟨(Scheme.Modules.pullback (baseChangeSnd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (pts y))).mapIso eP ≪≫ ?_⟩

    refine (Scheme.Modules.pullback (baseChangeSnd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (pts y))).mapIso (pbComp _ _ _) ≪≫ pbComp _ _ _ ≪≫ pbCongr hFG _ ≪≫ (pbComp _ _ _).symm

  have hgraph : ∀ (u : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
      (hu : u.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ.1),
      graphOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u.1 u.2 ≫ κ1.hom = graphOver (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ.1) (hover ξ) := by
    intro u ξ hu
    apply pullback.hom_ext
    · rw [Category.assoc, BaseChange.κ_hom_fst, graphOver_fst_assoc, graphOver_fst]
      try exact hu
    · rw [Category.assoc, BaseChange.κ_hom_snd, graphOver_snd, graphOver_snd]

  have hinvX : ∀ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j)) (hξU : Set.range ξ.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j))),
      (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ.1) (hover ξ)).I.IsInvertible := by
    intro ξ hξU
    refine AlgebraicGeometry.RelEffCartierDiv.isInvertible_I_of_supportedIn U _ ?_
    exact AlgebraicGeometry.RelEffCartierDiv.supportedIn_ofPoint _ _ U fun z => hξU ⟨ψ'.1.base z, rfl⟩

  have htrans : ∀ (u : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
      (hξU : Set.range ξ.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)))
      (hu : u.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ.1),
      (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u.1 u.2).I.IsInvertible ∧
      Nonempty ((Scheme.Modules.pullback κ1.hom).obj
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ.1) (hover ξ)).lineBundle ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u.1 u.2).lineBundle) ∧
      Nonempty ((Scheme.Modules.pullback κ1.hom).obj
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ.1) (hover ξ)).idealModule ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u.1 u.2).idealModule) := by
    intro u ξ hξU hu
    have hsq : IsPullback (graphOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u.1 u.2) (𝟙 _) κ1.hom
        (graphOver (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ.1) (hover ξ)) :=
      IsPullback.of_vert_isIso ⟨(hgraph u ξ hu).trans (Category.id_comp _).symm⟩
    have hcomapI : (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ.1) (hover ξ)).I.comap κ1.hom =
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u.1 u.2).I := by
      rw [RelEffCartierDiv.ofPoint_I, RelEffCartierDiv.ofPoint_I]
      exact comap_ker_eq_ker_of_isPullback hsq
    have hinv' : (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u.1 u.2).I.IsInvertible := by
      have h0 := (hinvX ξ hξU).comap_of_isOpenImmersion κ1.hom
      rwa [hcomapI] at h0
    have hk1 : (graphOver (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ.1) (hover ξ)).ker.IsInvertible := by
      have h0 := hinvX ξ hξU
      rwa [RelEffCartierDiv.ofPoint_I] at h0
    have hk2 : (graphOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u.1 u.2).ker.IsInvertible := by
      have h0 := hinv'
      rwa [RelEffCartierDiv.ofPoint_I] at h0
    obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := AlgebraicGeometry.Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso κ1.hom
      (graphOver (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ.1) (hover ξ)) (graphOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u.1 u.2) (hgraph u ξ hu)
      hk1 hk2 1
    have q1 : (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ.1) (hover ξ)).lineBundle =
        ((graphOver (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ.1) (hover ξ)).ker ^ 1).invModule := by
      show (RelEffCartierDiv.ofPoint _ _ _).I.invModule = _
      rw [RelEffCartierDiv.ofPoint_I, pow_one]
    have q2 : ((graphOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u.1 u.2).ker ^ 1).invModule = (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u.1 u.2).lineBundle := by
      show _ = (RelEffCartierDiv.ofPoint _ _ _).I.invModule
      rw [RelEffCartierDiv.ofPoint_I, pow_one]
    have q3 : (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ.1) (hover ξ)).idealModule =
        ((graphOver (ModularCurve.TwoChart.modelTo A (↥K) j) (ψ'.1 ≫ ξ.1) (hover ξ)).ker ^ 1).module := by
      show (RelEffCartierDiv.ofPoint _ _ _).I.module = _
      rw [RelEffCartierDiv.ofPoint_I, pow_one]
    have q4 : ((graphOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u.1 u.2).ker ^ 1).module = (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) u.1 u.2).idealModule := by
      show _ = (RelEffCartierDiv.ofPoint _ _ _).I.module
      rw [RelEffCartierDiv.ofPoint_I, pow_one]
    refine ⟨hinv', ⟨?_⟩, ⟨?_⟩⟩
    · exact (Scheme.Modules.pullback κ1.hom).mapIso (eqToIso q1) ≪≫ e1 ≪≫ eqToIso q2
    · exact (Scheme.Modules.pullback κ1.hom).mapIso (eqToIso q3) ≪≫ e2 ≪≫ eqToIso q4
  obtain ⟨hinv₁, ⟨f1⟩, -⟩ := htrans u₁ ξ₁ hξ₁U hu₁
  obtain ⟨hinv₂, -, ⟨f2⟩⟩ := htrans u₂ ξ₂ hξ₂U hu₂
  obtain ⟨e4⟩ := E4
  exact ⟨⟨e4 ≪≫ (Scheme.Modules.pullback κ1.hom).mapIso E2 ≪≫ pbTensor _ _ _ ≪≫ (f1 ⊗ᵢ f2)⟩, hinv₁, hinv₂⟩

end S_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_iso_ofPoint_lineBundle_tensor_idealModule_and_isInvertible_of_points_eq_reduction_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_iso_ofPoint_lineBundle_tensor_idealModule_and_isInvertible_of_points_eq_reduction_twoChartModel_x1_mul (solution)
