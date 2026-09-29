-- Prove2me | solution 1 for ModularCurve.XOneP.exists_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_classifies_fibre_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/428e6131-669e-5ecc-ac6a-7bfc3449c60c

import Mathlib
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_iso_of_sections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_classifies_fibre_twoChartModel_x1_mul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

universe u

namespace SFAux

open AlgebraicGeometry.RelPicard.BaseChange

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

theorem main
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (k : Type u) [CommRing k] [Algebra R k]
    (hk : RepresentsRelSubPic (baseChange R c k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange R c k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hk.poincare.L ≅ (BaseChange.ofR c ε k
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩)).L))
    (β β' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
    (hββ' : β ≫ β' = 𝟙 _)
    (hσ : specMap R k ≫ β = specMap R k)
    (u : C ⟶ C) (hu : u ≫ c = c ≫ β')
    (uk : pullback c (specMap R k) ≅ pullback c (specMap R k))
    (huk₁ : uk.hom ≫ pullback.fst c (specMap R k) = pullback.fst c (specMap R k) ≫ u)
    (huk₂ : uk.hom ≫ pullback.snd c (specMap R k) = pullback.snd c (specMap R k))
    (N : SchemeHomOver (D.toBase ≫ β) D.toBase)
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
      Nonempty ((h.poincare.pullbackAlong
          (⟨a.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, a.2]⟩ : SchemeHomOver (t ≫ β) D.toBase)).L ≅
        Scheme.Modules.rigidify (rigSection c (t ≫ β) ε) (pullback.snd c (t ≫ β))
          ((Scheme.Modules.pullback
              (pullback.map c (t ≫ β) c t u (𝟙 T) β' hu.symm
                (by rw [Category.assoc, hββ', Category.comp_id, Category.id_comp]))).obj
            (h.poincare.pullbackAlong a).L))) :
    ∃ θk : SchemeHomOver (D.baseChange k).toBase (D.baseChange k).toBase,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
          (P₁ : RigidifiedLineBundle (baseChange R c k) (sectionBaseChange k ε) t) (hP₁ : FibrewiseAlgEquivZero P₁)
          (P₂ : RigidifiedLineBundle (baseChange R c k) (sectionBaseChange k ε) t) (hP₂ : FibrewiseAlgEquivZero P₂)
          (Q : T.Modules), Scheme.Modules.IsInvertible Q →
          Nonempty (P₂.L ≅ (Scheme.Modules.pullback
              (curveChange (c := baseChange R c k) (c' := baseChange R c k) uk.hom huk₂ t)).obj P₁.L ⊗
            (Scheme.Modules.pullback (pullback.snd (baseChange R c k) t)).obj Q) →
          postComp θk (hk.classify t P₁ hP₁) = hk.classify t P₂ hP₂) ∧
      (∀ (a a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase),
          a'.1 ≫ pullback.fst D.toBase (specMap R k) = (a.1 ≫ pullback.fst D.toBase (specMap R k)) ≫ N.1 →
          a' = postComp θk a) := by
  classical

  have he' : uk.hom ≫ baseChange R c k = baseChange R c k := huk₂
  have he : uk.inv ≫ baseChange R c k = baseChange R c k := (Iso.inv_comp_eq _).2 he'.symm
  obtain ⟨θ, -, -, -, hθ⟩ := RepresentsRelSubPic.exists_inverse_pair_of_iso_of_sections
    (sectionBaseChange k ε) (sectionBaseChange k ε) uk.symm he he' hk hk
  refine ⟨θ, fun t P₁ hP₁ P₂ hP₂ Q hQ hiso => hθ t P₁ hP₁ P₂ hP₂ Q hQ hiso, ?_⟩

  intro a a' haa'

  have hbase : (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ β = (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) := by
    rw [Category.assoc, hσ]

  let π : SchemeHomOver ((D.baseChange k).toBase ≫ specMap R k) D.toBase :=
    ⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩

  let α : SchemeHomOver (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) D.toBase := postComp π (overR k a)
  let α' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) D.toBase := postComp π (overR k a')
  let αN : SchemeHomOver ((𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ β) D.toBase :=
    ⟨α.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, α.2]⟩

  let κ₁ := κ c k (𝟙 (Spec (CommRingCat.of k)))
  let κD := κ c k (D.baseChange k).toBase
  have hκ₁fst : κ₁.hom ≫ pullback.fst c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) =
      pullback.fst (baseChange R c k) (𝟙 _) ≫ pullback.fst c (specMap R k) := κ_hom_fst c k (𝟙 _)
  have hκ₁snd : κ₁.hom ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) = pullback.snd (baseChange R c k) (𝟙 _) :=
    κ_hom_snd c k (𝟙 _)

  obtain ⟨ι, hι₁, hι₂⟩ : ∃ ι : pullback c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ⟶ pullback c ((𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ β),
      ι ≫ pullback.fst c ((𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ β) = pullback.fst c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ∧
      ι ≫ pullback.snd c ((𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ β) = pullback.snd c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) :=
    ⟨pullback.lift (pullback.fst c _) (pullback.snd c _) (by rw [hbase]; exact pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  obtain ⟨pm, hpm₁, hpm₂, hNα⟩ : ∃ pm : pullback c ((𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ β) ⟶ pullback c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k),
      pm ≫ pullback.fst c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) = pullback.fst c ((𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ β) ≫ u ∧
      pm ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) = pullback.snd c ((𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ β) ∧
      Nonempty ((h.poincare.pullbackAlong αN).L ≅
        Scheme.Modules.rigidify (rigSection c ((𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ β) ε) (pullback.snd c ((𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ β))
          ((Scheme.Modules.pullback pm).obj (h.poincare.pullbackAlong α).L)) :=
    ⟨pullback.map c ((𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ β) c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) u (𝟙 _) β' hu.symm
        (by rw [Category.assoc, hββ', Category.comp_id]; exact (Category.id_comp _).symm),
      pullback.lift_fst _ _ _, by simp only [pullback.lift_snd, Category.comp_id], hN _ α⟩

  have hB : ∀ b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase,
      Nonempty ((hk.poincare.pullbackAlong b).L ≅
        (Scheme.Modules.pullback κ₁.hom).obj (h.poincare.pullbackAlong (postComp π (overR k b))).L) := by
    intro b
    have h1 : baseChangeSnd (baseChange R c k) b ≫ κD.hom = κ₁.hom ≫ baseChangeSnd c (overR k b) :=
      baseChangeSnd_κ_hom c k b
    have hcomp : (baseChangeSnd (baseChange R c k) b ≫ κD.hom) ≫ baseChangeSnd c π =
        κ₁.hom ≫ baseChangeSnd c (postComp π (overR k b)) := by
      rw [h1, Category.assoc, baseChangeSnd_comp]
    exact ⟨(Scheme.Modules.pullback (baseChangeSnd (baseChange R c k) b)).mapIso hPk.some ≪≫
      (Scheme.Modules.pullbackComp (baseChangeSnd (baseChange R c k) b) κD.hom).app _ ≪≫
      (Scheme.Modules.pullbackComp (baseChangeSnd (baseChange R c k) b ≫ κD.hom) (baseChangeSnd c π)).app
        h.poincare.L ≪≫
      (Scheme.Modules.pullbackCongr hcomp).app h.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp κ₁.hom (baseChangeSnd c (postComp π (overR k b)))).app h.poincare.L).symm⟩

  have hA : Nonempty ((h.poincare.pullbackAlong α').L ≅
      (Scheme.Modules.pullback ι).obj (h.poincare.pullbackAlong αN).L) := by
    have hιN : ι ≫ baseChangeSnd c αN = baseChangeSnd c α' := by
      apply pullback.hom_ext
      · rw [Category.assoc, baseChangeSnd_fst', hι₁, baseChangeSnd_fst']
      · rw [Category.assoc, baseChangeSnd_snd', ← Category.assoc, hι₂, baseChangeSnd_snd']
        show pullback.snd c _ ≫ (a.1 ≫ pullback.fst D.toBase (specMap R k)) ≫ N.1 =
          pullback.snd c _ ≫ a'.1 ≫ pullback.fst D.toBase (specMap R k)
        rw [← haa']
    exact ⟨(Scheme.Modules.pullbackCongr hιN.symm).app h.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp ι (baseChangeSnd c αN)).app h.poincare.L).symm⟩

  let cc := curveChange (c := baseChange R c k) (c' := baseChange R c k) uk.hom huk₂ (𝟙 (Spec (CommRingCat.of k)))
  have hcc₁ : cc ≫ pullback.fst (baseChange R c k) (𝟙 _) = pullback.fst (baseChange R c k) (𝟙 _) ≫ uk.hom :=
    pullback.lift_fst _ _ _
  have hcc₂ : cc ≫ pullback.snd (baseChange R c k) (𝟙 _) = pullback.snd (baseChange R c k) (𝟙 _) :=
    curveChange_snd _ _ _
  have hmap : cc ≫ κ₁.hom = (κ₁.hom ≫ ι) ≫ pm := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hκ₁fst, reassoc_of% hκ₁fst, hpm₁, reassoc_of% hι₁, reassoc_of% hcc₁, huk₁]
    · simp only [Category.assoc, hκ₁snd, hcc₂, hpm₂, hι₂]
  have hC : Nonempty ((Scheme.Modules.pullback (κ₁.hom ≫ ι)).obj
      ((Scheme.Modules.pullback pm).obj (h.poincare.pullbackAlong α).L) ≅
      (Scheme.Modules.pullback cc).obj (hk.poincare.pullbackAlong a).L) :=
    ⟨(Scheme.Modules.pullbackComp (κ₁.hom ≫ ι) pm).app _ ≪≫
      (Scheme.Modules.pullbackCongr hmap.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp cc κ₁.hom).app _).symm ≪≫
      ((Scheme.Modules.pullback cc).mapIso (hB a).some).symm⟩

  have hrs₁ : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)), rigSection c t ε ≫ pullback.fst c t = t ≫ ε.1 :=
    fun t => pullback.lift_fst _ _ _
  have hrs₂ : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)), rigSection c t ε ≫ pullback.snd c t = 𝟙 _ :=
    fun t => pullback.lift_snd _ _ _
  have hrκ : rigSection (baseChange R c k) (𝟙 _) (sectionBaseChange k ε) ≫ κ₁.hom = rigSection c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ε :=
    rigSection_κ_hom c ε k (𝟙 _)
  have hσ' : rigSection (baseChange R c k) (𝟙 _) (sectionBaseChange k ε) ≫ (κ₁.hom ≫ ι) =
      rigSection c ((𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ β) ε := by
    rw [← Category.assoc, hrκ]
    apply pullback.hom_ext
    · rw [Category.assoc, hι₁, hrs₁, hrs₁, hbase]
    · rw [Category.assoc, hι₂, hrs₂, hrs₂]
  have hq' : (κ₁.hom ≫ ι) ≫ pullback.snd c ((𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ β) = pullback.snd (baseChange R c k) (𝟙 _) := by
    rw [Category.assoc, hι₂, hκ₁snd]
  have hR := Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso (𝟙 _) (κ₁.hom ≫ ι)
    (hσ'.trans (Category.id_comp _).symm) (hq'.trans (Category.comp_id _).symm)
    ((h.poincare.pullbackAlong α).isInvertible.pullback pm)

  let Q : (Spec (CommRingCat.of k)).Modules := Scheme.Modules.dual
    ((Scheme.Modules.pullback (rigSection (baseChange R c k) (𝟙 _) (sectionBaseChange k ε))).obj
      ((Scheme.Modules.pullback cc).obj (hk.poincare.pullbackAlong a).L))
  have hQ : Scheme.Modules.IsInvertible Q :=
    (Scheme.Modules.IsInvertible.dual (((hk.poincare.pullbackAlong a).isInvertible.pullback cc).pullback _)).1

  have mem : ∀ b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase,
      (algEquivZeroCut (baseChange R c k) (sectionBaseChange k ε)).P (𝟙 _) (hk.poincare.pullbackAlong b) :=
    fun b => (algEquivZeroCut _ _).pullback_mem _ _ b _ hk.poincare_mem
  have hcl : ∀ b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase,
      b = hk.classify (𝟙 _) (hk.poincare.pullbackAlong b) (mem b) :=
    fun b => hk.classify_unique _ _ _ b ⟨Iso.refl _⟩
  rw [hcl a, hcl a']
  refine (hθ (𝟙 _) _ (mem a) _ (mem a') Q hQ ⟨?_⟩).symm

  exact (hB a').some ≪≫ (Scheme.Modules.pullback κ₁.hom).mapIso hA.some ≪≫
    (Scheme.Modules.pullbackComp κ₁.hom ι).app _ ≪≫
    (Scheme.Modules.pullback (κ₁.hom ≫ ι)).mapIso hNα.some ≪≫ hR.some ≪≫
    Scheme.Modules.rigidifyMapIso _ _ hC.some

end SFAux

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

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (hsk : ∀ (s' : L ≃ₐ[ℚ] L) (a : A), algebraMap A k (s' • a) = algebraMap A k a)
    (s : L ≃ₐ[ℚ] L)
    (u : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j)
    (hu : u ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = (ModularCurve.TwoChart.modelTo A (↥K) j) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))))
    (uk : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≅ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (huk₁ : uk.hom ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ u)
    (huk₂ : uk.hom ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))

    (hsinv : (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))) = 𝟙 (Spec (CommRingCat.of A)))

    (N : SchemeHomOver (D.toBase ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))) D.toBase)
    (hN : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (a : SchemeHomOver t D.toBase),
      Nonempty ((hrep.some.poincare.pullbackAlong
          (⟨a.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, a.2]⟩ : SchemeHomOver (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))) D.toBase)).L ≅
        Scheme.Modules.rigidify (rigSection (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))) ε) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))))
          ((Scheme.Modules.pullback
              (pullback.map (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))) (ModularCurve.TwoChart.modelTo A (↥K) j) t u (𝟙 T) (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))
                hu.symm (by rw [Category.assoc, hsinv, Category.comp_id, Category.id_comp]))).obj
            (hrep.some.poincare.pullbackAlong a).L)))
    :
    ∃ θk : SchemeHomOver (D.baseChange k).toBase (D.baseChange k).toBase,

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k))
          (P₁ : RigidifiedLineBundle (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε) t) (hP₁ : FibrewiseAlgEquivZero P₁)
          (P₂ : RigidifiedLineBundle (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε) t) (hP₂ : FibrewiseAlgEquivZero P₂)
          (Q : T.Modules), Scheme.Modules.IsInvertible Q →
          Nonempty (P₂.L ≅ (Scheme.Modules.pullback (curveChange (c := (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (c' := (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) uk.hom huk₂ t)).obj P₁.L ⊗
            (Scheme.Modules.pullback (pullback.snd (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) t)).obj Q) →
          postComp θk (hreps.classify t P₁ hP₁) = hreps.classify t P₂ hP₂) ∧

      (∀ (a a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase),
          a'.1 ≫ pullback.fst D.toBase (specMap A k) = (a.1 ≫ pullback.fst D.toBase (specMap A k)) ≫ N.1 →
          a' = postComp θk a) := by
  classical
  exact SFAux.main ε hrep.some k hreps hPk
    (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))
    (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))
    hsinv
    (by
      show Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ _ = Spec.map (CommRingCat.ofHom (algebraMap A k))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a
      exact hsk s a)
    u hu uk huk₁ huk₂ N hN

end S_ModularCurve_XOneP_exists_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_classifies_fibre_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_classifies_fibre_twoChartModel_x1_mul (solution)
