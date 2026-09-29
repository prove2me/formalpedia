-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackageLevel.exists_pullback_toDR_iso_foldr_ker_tensor_invModule_prod_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b9af4a6e-0639-55c2-8a3d-b645de610969

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_prod_pow_of_zeroSchemeIdeal_support_disjoint
import Theorems.Thm_IsRegularLocalRing_isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial_of_qcqs
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
import Theorems.Thm_ModularCurve_DRResolvedModelPackageLevel_ne_edgePt_and_mem_smoothOffEdges_and_existsUnique_mem_comp_support_of_section
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackageLevel_exists_pullback_toDR_iso_foldr_ker_tensor_invModule_prod_comp
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian ModularCurve MazurRapoportAppendix"

open scoped BigOperators
open Opposite

universe u

namespace E5W2aGs

private noncomputable def foldrTensorIso {C : Type*} [Category C] [MonoidalCategory C] {ι : Type*} (A B : ι → C) (V : C) :
    ∀ l : List ι, l.foldr (fun j N => A j ⊗ B j ⊗ N) V ≅ (l.foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ C)) ⊗ V
  | [] => (λ_ V).symm
  | j :: l => whiskerLeftIso (A j) (whiskerLeftIso (B j) (foldrTensorIso A B V l)) ≪≫
      (α_ (A j) (B j) _).symm ≪≫ (α_ (A j ⊗ B j) _ V).symm

private noncomputable def pullbackFoldrIso {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (A B : ι → Y.Modules) (A' B' : ι → X.Modules)
    (eA : ∀ j, (Scheme.Modules.pullback f).obj (A j) ≅ A' j) (eB : ∀ j, (Scheme.Modules.pullback f).obj (B j) ≅ B' j) :
    ∀ l : List ι, (Scheme.Modules.pullback f).obj (l.foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ Y.Modules)) ≅
      l.foldr (fun j M => (A' j ⊗ B' j) ⊗ M) (𝟙_ X.Modules)
  | [] => Scheme.Modules.pullbackTensorUnitObjIso f
  | j :: l => Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
      tensorIso (Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ tensorIso (eA j) (eB j)) (pullbackFoldrIso f A B A' B' eA eB l)

private theorem isInvertible_prod_pow {X : Scheme.{u}} {ι : Type*} [Fintype ι] [DecidableEq ι] (I : ι → X.IdealSheafData)
    (hI : ∀ i, (I i).IsInvertible) (n : ι → ℕ) : (∏ i, I i ^ n i).IsInvertible := by
  classical
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  · intro i s hi ih
    rw [Finset.prod_insert hi]
    exact ((hI i).pow (n i)).mul ih

private theorem isInvertible_foldr {X : Scheme.{u}} {m : ℕ} (A B : Fin m → X.Modules)
    (hA : ∀ j, Scheme.Modules.IsInvertible (A j)) (hB : ∀ j, Scheme.Modules.IsInvertible (B j))
    (V : X.Modules) (hV : Scheme.Modules.IsInvertible V) (l : List (Fin m)) :
    Scheme.Modules.IsInvertible (l.foldr (fun j N => A j ⊗ B j ⊗ N) V) := by
  induction l with
  | nil => exact hV
  | cons j l ih => exact (hA j).tensor ((hB j).tensor ih)

private theorem range_subset_of_closedPoint_mem {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}}
    (W : Y.Opens) (σ : Spec (CommRingCat.of O) ⟶ Y) (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
    Set.range σ.base ⊆ (W : Set Y) := by
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map σ.continuous).mem_open W.2 hW

private theorem specMap_base_mem_basicOpen {O K : Type u} [CommRing O] [Field K] (φ : O →+* K) (r : O) (hr : φ r ≠ 0)
    (q : Spec (CommRingCat.of K)) :
    (Spec.map (CommRingCat.ofHom φ)).base q ∈ PrimeSpectrum.basicOpen r := by
  have h1 : ((Spec.map (CommRingCat.ofHom φ)).base q).asIdeal = Ideal.comap φ q.asIdeal := rfl
  have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
  show r ∉ ((Spec.map (CommRingCat.ofHom φ)).base q).asIdeal
  rw [h1, Ideal.mem_comap, hq, Ideal.mem_bot]
  exact hr

private theorem isClosedImmersion_of_comp_eq_id {Y S : Scheme.{u}} (π : Y ⟶ S) [IsSeparated π] (σ : S ⟶ Y) (hσ : σ ≫ π = 𝟙 _) :
    IsClosedImmersion σ := by
  have : IsClosedImmersion (σ ≫ π) := by rw [hσ]; infer_instance
  exact .of_comp σ π

set_option maxHeartbeats 6400000 in
private theorem nonempty_generic_iso
    {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {Y : Scheme.{0}} (c : Y ⟶ Spec (CommRingCat.of O)) [IsSeparated c]
    (U : Y.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {m : ℕ} (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) c) (pos neg : Fin m → ℕ)
    (hσU : ∀ j, Set.range (σ j).1 ⊆ (U : Set Y))
    (hker : ∀ j, ((σ j).1).ker.IsInvertible)
    (V : Y.Modules)
    (hV : Nonempty ((Scheme.Modules.pullback (pullback.fst c
        (Spec.map (CommRingCat.ofHom (algebraMap O K))))).obj V ≅ 𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst c
          (Spec.map (CommRingCat.ofHom (algebraMap O K))))).obj
            ((List.finRange m).foldr
          (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N) V) ≅
        (List.finRange m).foldr
          (fun j N => (sectionTwist c (σ j) (Spec.map (CommRingCat.ofHom (algebraMap O K))) (pos j) ⊗
              ((sectionIdeal c (σ j) (Spec.map (CommRingCat.ofHom (algebraMap O K)))) ^ (neg j)).module) ⊗ N)
          (𝟙_ (pullback c (Spec.map (CommRingCat.ofHom (algebraMap O K)))).Modules)) := by
  classical
  let t' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom (algebraMap O K))
  let jη := pullback.fst c t'
  let fst₁ := pullback.fst c (𝟙 (Spec (CommRingCat.of O)))
  haveI : IsIso fst₁ := inferInstance
  let ψ : SchemeHomOver t' (𝟙 (Spec (CommRingCat.of O))) := ⟨t', Category.comp_id _⟩
  have hcomp : baseChangeSnd c ψ ≫ fst₁ = jη := by
    simp only [baseChangeSnd, fst₁, jη, pullback.lift_fst, Category.comp_id]
  let A : Fin m → Y.Modules := fun j => ((σ j).1.ker ^ (pos j)).invModule
  let B : Fin m → Y.Modules := fun j => ((σ j).1.ker ^ (neg j)).module
  let A₁ : Fin m → (pullback c (𝟙 (Spec (CommRingCat.of O)))).Modules := fun j =>
    sectionTwist c (σ j) (𝟙 _) (pos j)
  let B₁ : Fin m → (pullback c (𝟙 (Spec (CommRingCat.of O)))).Modules := fun j =>
    ((sectionIdeal c (σ j) (𝟙 _)) ^ (neg j)).module
  have hsec : ∀ j, (sectionIdeal c (σ j) (𝟙 (Spec (CommRingCat.of O)))).IsInvertible := fun j =>
    isInvertible_sectionIdeal_of_range_subset c (σ j) U (hσU j) (𝟙 _)
  haveI : ∀ j, IsClosedImmersion (σ j).1 := fun j => isClosedImmersion_of_comp_eq_id c (σ j).1 (σ j).2
  have hrig : ∀ j, rigSection c (𝟙 (Spec (CommRingCat.of O))) (σ j) ≫ fst₁ = (σ j).1 := fun j => by
    show pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    rw [pullback.lift_fst, Category.id_comp]
  have eAB := fun j => Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso fst₁ (σ j).1
    (rigSection c (𝟙 _) (σ j)) (hrig j) (hker j) (hsec j)
  let eA : ∀ j, (Scheme.Modules.pullback fst₁).obj (A j) ≅ A₁ j := fun j => ((eAB j (pos j)).1).some
  let eB : ∀ j, (Scheme.Modules.pullback fst₁).obj (B j) ≅ B₁ j := fun j => ((eAB j (neg j)).2).some
  let S'' : Y.Modules := (List.finRange m).foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ Y.Modules)
  let i0 : (List.finRange m).foldr (fun j N => A j ⊗ B j ⊗ N) V ≅ S'' ⊗ V := foldrTensorIso A B V _
  let i1 : (Scheme.Modules.pullback jη).obj (S'' ⊗ V) ≅
      (Scheme.Modules.pullback jη).obj S'' ⊗ (Scheme.Modules.pullback jη).obj V := Scheme.Modules.pullbackTensorObjIso jη _ _
  let i2 : (Scheme.Modules.pullback jη).obj S'' ⊗ (Scheme.Modules.pullback jη).obj V ≅
      (Scheme.Modules.pullback jη).obj S'' := tensorIso (Iso.refl _) hV.some ≪≫ ρ_ _
  let i3 : (Scheme.Modules.pullback jη).obj S'' ≅
      (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj ((Scheme.Modules.pullback fst₁).obj S'') :=
    ((Scheme.Modules.pullbackCongr hcomp).symm ≪≫ (Scheme.Modules.pullbackComp (baseChangeSnd c ψ) fst₁).symm).app S''
  let i4 : (Scheme.Modules.pullback fst₁).obj S'' ≅
      (List.finRange m).foldr (fun j M => (A₁ j ⊗ B₁ j) ⊗ M) (𝟙_ _) := pullbackFoldrIso fst₁ A B A₁ B₁ eA eB _
  obtain ⟨-, ⟨i5⟩⟩ := isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset c U σ hσU pos neg ψ
  exact ⟨(Scheme.Modules.pullback jη).mapIso i0 ≪≫ i1 ≪≫ i2 ≪≫ i3 ≪≫
    (Scheme.Modules.pullback (baseChangeSnd c ψ)).mapIso i4 ≪≫ i5⟩

end E5W2aGs

namespace E5W2aGs

private theorem away_of_maximalIdeal_eq_span {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : O}
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {p})
    (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K] : IsLocalization.Away p K := by
  have hp0 : p ≠ 0 := fun h => by
    apply IsDiscreteValuationRing.not_a_field O
    rw [hϖ, h, Ideal.span_singleton_eq_bot]
  have hirr : Irreducible p := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal p hp0 hϖ
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    rw [map_pow]
    exact pow_ne_zero _ (fun h => hp0 (hinj (by rw [h, map_zero])))
  · intro k
    obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors O) k
    have hb0 : (b : O) ≠ 0 := nonZeroDivisors.ne_zero b.2
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hirr
    refine ⟨⟨a * ↑v⁻¹, ⟨p ^ n, n, rfl⟩⟩, ?_⟩

    dsimp only at h ⊢
    rw [map_mul]
    have hvK : algebraMap O K (↑v⁻¹ : O) * algebraMap O K (v : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc k * algebraMap O K (p ^ n)
        = k * algebraMap O K (b : O) * algebraMap O K (↑v⁻¹ : O) := by
          rw [hv, map_mul, mul_assoc, mul_assoc, mul_comm (algebraMap O K (v : O)),  mul_assoc, hvK, mul_one]
      _ = algebraMap O K a * algebraMap O K (↑v⁻¹ : O) := by rw [h]
  · intro a b h
    exact ⟨1, by rw [hinj h]⟩

private theorem exists_hom_app_toUnitSection_eq {Y : Scheme.{u}} (M : Y.Modules) (y : Γ(M, ⊤)) :
    ∃ s : 𝟙_ Y.Modules ⟶ M, ∀ W : Y.Opens,
      s.app W (Scheme.Modules.toUnitSection W 1) = M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op y := by
  let sec : SheafOfModules.sections (R := Y.ringCatSheaf) M :=
    PresheafOfModules.sectionsMk (M := M.val)
      (fun W => M.presheaf.map (homOfLE (le_top : W.unop ≤ ⊤)).op y)
      (by
        intro W W' i
        change M.presheaf.map i (M.presheaf.map (homOfLE le_top).op y) = _
        rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
        rfl)
  refine ⟨(SheafOfModules.unitHomEquiv M).symm sec, fun W => ?_⟩
  have := SheafOfModules.unitHomEquiv_apply_coe M ((SheafOfModules.unitHomEquiv M).symm sec) (op W)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

end E5W2aGs

namespace E5W2aGs

set_option maxHeartbeats 3200000 in

private theorem exists_section_support_subset
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : O}
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {p})
    {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
    {Y : Scheme.{0}} (c : Y ⟶ Spec (CommRingCat.of O)) [IsProper c]
    {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    (eMK : Nonempty ((Scheme.Modules.pullback (pullback.fst c
        (Spec.map (CommRingCat.ofHom (algebraMap O K))))).obj M ≅ 𝟙_ _)) :
    ∃ s : 𝟙_ Y.Modules ⟶ M, ∀ y : Y, y ∈ (Scheme.Modules.zeroSchemeIdeal s).support →
      y ∉ c ⁻¹ᵁ (PrimeSpectrum.basicOpen p : (Spec (CommRingCat.of O)).Opens) := by
  classical
  haveI hAway := away_of_maximalIdeal_eq_span hϖ K
  let tK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom (algebraMap O K))
  haveI : IsOpenImmersion tK := IsOpenImmersion.of_isLocalization p
  let jη := pullback.fst c tK
  haveI : IsOpenImmersion jη := inferInstance
  let U : Y.Opens := c ⁻¹ᵁ (PrimeSpectrum.basicOpen p : (Spec (CommRingCat.of O)).Opens)

  have htK : Set.range tK.base = (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum O)) :=
    PrimeSpectrum.localization_away_comap_range K p
  have hrange : Set.range jη.base = Set.range U.ι.base := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι, htK]
    rfl
  let e := IsOpenImmersion.isoOfRangeEq jη U.ι hrange
  have he : e.inv ≫ jη = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have eU : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{0}).ringCatSheaf :=
    (Scheme.Modules.pullbackCongr he.symm).app M ≪≫ ((Scheme.Modules.pullbackComp e.inv jη).app M).symm ≪≫
      (Scheme.Modules.pullback e.inv).mapIso eMK.some ≪≫ Scheme.Modules.pullbackTensorUnitObjIso e.inv

  obtain ⟨Ω, hΩ⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit U eU

  let f : Γ(Y, ⊤) := c.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv p)
  have hUf : U = Y.basicOpen f := by
    have hb : (PrimeSpectrum.basicOpen p : (Spec (CommRingCat.of O)).Opens) =
        (Spec (CommRingCat.of O)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv p) :=
      (basicOpen_eq_of_affine (R := CommRingCat.of O) p).symm
    show c ⁻¹ᵁ _ = _
    rw [hb, Scheme.preimage_basicOpen_top]
  have hle : Y.basicOpen f ≤ U := hUf ▸ le_rfl
  let x : Γ(M, Y.basicOpen f) := M.presheaf.map (homOfLE hle).op Ω
  have hx : Scheme.Modules.IsFrameOn x (Y.basicOpen f) := (hΩ.map (homOfLE hle)).mono hle

  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace c
  haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated c
  have hqc : IsCompact ((⊤ : Y.Opens) : Set Y) := by
    rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ
  have hqs : IsQuasiSeparated ((⊤ : Y.Opens) : Set Y) := by
    rw [TopologicalSpace.Opens.coe_top]; exact isQuasiSeparated_univ
  obtain ⟨hloc, -⟩ := Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial_of_qcqs M hM.1 hqc hqs f
  obtain ⟨nn, y, hy⟩ := hloc x

  obtain ⟨s, hs⟩ := exists_hom_app_toUnitSection_eq M y
  refine ⟨s, ?_⟩

  have hsx : s.app (Y.basicOpen f) (Scheme.Modules.toUnitSection (Y.basicOpen f) 1) =
      Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (f ^ nn) • x := by
    rw [hs]; exact hy
  intro y₀ hy₀ hyU
  have hyW : y₀ ∈ Y.basicOpen f := hUf ▸ hyU
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW', hWle⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyW (Y.basicOpen f).isOpen
  have hideal := hM.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul x hx s _ hsx ⟨W, hW⟩ hWle
  have hunit : IsUnit (Y.presheaf.map (homOfLE hWle).op (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (f ^ nn))) := by
    rw [map_pow]
    exact ((RingedSpace.isUnit_res_basicOpen Y.toRingedSpace f).pow nn).map _
  have htop : (Scheme.Modules.zeroSchemeIdeal s).ideal ⟨W, hW⟩ = ⊤ := by
    rw [hideal, Ideal.span_singleton_eq_top]; exact hunit
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨W, hW⟩) hyW', htop] at hy₀
  have := (Scheme.mem_zeroLocus_iff Y _ y₀).mp hy₀ 1 trivial
  rw [Scheme.basicOpen_one] at this
  exact this hyW'

end E5W2aGs

namespace E5W2aGs

private theorem exists_iso_invModule_prod_comp
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R p →+* O)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    {M : 𝔛reg.Y.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ 𝔛reg.Y.Modules ⟶ M)
    (hs : ∀ y : 𝔛reg.Y, y ∈ (Scheme.Modules.zeroSchemeIdeal s).support →
      y ∉ 𝔛reg.toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ∃ n : X0MqComponents 𝔛reg.width → ℕ, Nonempty (M ≅ (∏ F, 𝔛reg.comp F ^ n F).invModule) := by
  classical
  refine Scheme.Modules.IsInvertible.exists_iso_invModule_prod_pow_of_zeroSchemeIdeal_support_disjoint
    (𝔛reg.toBase ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    𝔛reg.comp 𝔛reg.comp_isInvertible 𝔛reg.comp_support 𝔛reg.η 𝔛reg.η_not_mem 𝔛reg.η_stalk 𝔛reg.codim
    ?_ hM s hs
  intro x hx P hP hP1
  haveI := 𝔛reg.regular x hx
  exact IsRegularLocalRing.isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two
    (𝔛reg.stalk_dim_le_two x hx) P hP hP1

end E5W2aGs

namespace E5W2aGs

private theorem nonempty_invModule_prod_pow_iso_vert {X : Scheme.{u}} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → X.IdealSheafData) (hC : ∀ i, (C i).IsInvertible) (n : ι → ℕ) :
    Nonempty ((∏ i, C i ^ n i).invModule ≅
      (∏ i, C i ^ (n i + 1)).invModule ⊗ (∏ i, C i ^ (1 : ℕ)).module) := by
  classical
  have hprod : (∏ i, C i ^ n i) * (∏ i, C i ^ (1 : ℕ)) = ∏ i, C i ^ (n i + 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_one, pow_succ]
  have h1 := isInvertible_prod_pow C hC n
  have h2 := isInvertible_prod_pow C hC (fun _ => 1)
  obtain ⟨e1⟩ := h1.nonempty_mul_invModule_iso_tensor h2
  obtain ⟨-, ⟨e2⟩⟩ := h2.nonempty_module_tensor_invModule_iso
  have e3 : ((∏ i, C i ^ n i) * (∏ i, C i ^ (1 : ℕ))).invModule ≅ (∏ i, C i ^ (n i + 1)).invModule :=
    eqToIso (by rw [hprod])
  exact ⟨(ρ_ _).symm ≪≫ whiskerLeftIso _ e2.symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso (e1.symm ≪≫ e3) _⟩

end E5W2aGs

open E5W2aGs in
set_option maxHeartbeats 3200000 in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (D : RelativePic0Designation (DRLevel.R p) (DRLevel.toBase N₀ p))
    (hD : RepresentsRelSubPic (DRLevel.toBase N₀ p) 𝔓.εinf (algEquivZeroCut (DRLevel.toBase N₀ p) 𝔓.εinf) D)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) D.toBase)
    {m : ℕ} (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    (pos neg : Fin m → ℕ)
    (v : Fin m → X0MqComponents 𝔛reg.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (v j)).support ∧
      ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support)
    (hgen : Nonempty (
      (Scheme.Modules.pullback (pullback.fst 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap O K))))).obj
          ((Scheme.Modules.pullback 𝔛reg.toDR).obj (hD.poincare.pullbackAlong z).L) ≅
        (List.finRange m).foldr
          (fun j M => (sectionTwist 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap O K))) (pos j) ⊗
              ((sectionIdeal 𝔛reg.toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap O K)))) ^ (neg j)).module) ⊗ M)
          (𝟙_ (pullback 𝔛reg.toBase (Spec.map (CommRingCat.ofHom (algebraMap O K)))).Modules))) :
    ∃ (aplus aminus : X0MqComponents 𝔛reg.width → ℕ),
      Nonempty ((Scheme.Modules.pullback 𝔛reg.toDR).obj (hD.poincare.pullbackAlong z).L ≅
        (List.finRange m).foldr
          (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N)
          ((∏ F, (𝔛reg.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (𝔛reg.comp F) ^ (aminus F)).module)) := by
  classical

  let tK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom (algebraMap O K))
  let jη := pullback.fst 𝔛reg.toBase tK
  let L : 𝔛reg.Y.Modules := (Scheme.Modules.pullback 𝔛reg.toDR).obj (hD.poincare.pullbackAlong z).L
  have hL : Scheme.Modules.IsInvertible L := (hD.poincare.pullbackAlong z).isInvertible.pullback _
  let A : Fin m → 𝔛reg.Y.Modules := fun j => ((σ j).1.ker ^ (pos j)).invModule
  let B : Fin m → 𝔛reg.Y.Modules := fun j => ((σ j).1.ker ^ (neg j)).module
  let E : 𝔛reg.Y.Modules := (List.finRange m).foldr (fun j N => A j ⊗ B j ⊗ N) (𝟙_ _)

  have hoff : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges := fun j =>
    (ModularCurve.DRResolvedModelPackageLevel.ne_edgePt_and_mem_smoothOffEdges_and_existsUnique_mem_comp_support_of_section
      N₀ p hpN₀ 𝔓 O ρO hϖ κ toκ 𝔛reg (σ j)).2.1
  have hσU : ∀ j, Set.range (σ j).1 ⊆ (𝔛reg.smoothOffEdges : Set 𝔛reg.Y) := fun j =>
    range_subset_of_closedPoint_mem 𝔛reg.smoothOffEdges (σ j).1 (hoff j)
  have hker : ∀ j, ((σ j).1).ker.IsInvertible := fun j =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens 𝔛reg.toBase 𝔛reg.smoothOffEdges (σ j).1 (σ j).2 (hoff j)

  have hE : Scheme.Modules.IsInvertible E :=
    isInvertible_foldr A B (fun j => ((hker j).pow (pos j)).isInvertible_invModule)
      (fun j => ((hker j).pow (neg j)).isInvertible_module) _ (Scheme.Modules.isInvertible_unit _) (List.finRange m)
  have eEK := nonempty_generic_iso (K := K) 𝔛reg.toBase 𝔛reg.smoothOffEdges σ pos neg hσU hker (𝟙_ _)
    ⟨Scheme.Modules.pullbackTensorUnitObjIso _⟩

  let M : 𝔛reg.Y.Modules := L ⊗ Scheme.Modules.dual E
  have hM : Scheme.Modules.IsInvertible M := hL.tensor hE.dual.1
  have eMK : Nonempty ((Scheme.Modules.pullback jη).obj M ≅ 𝟙_ _) :=
    ⟨Scheme.Modules.pullbackTensorObjIso jη L (Scheme.Modules.dual E) ≪≫
      tensorIso (hgen.some ≪≫ eEK.some.symm) (Scheme.Modules.IsInvertible.pullback_dual jη hE).some ≪≫
      (hE.pullback jη).dual.2.some⟩

  obtain ⟨s, hs⟩ := exists_section_support_subset (p := ((p : ℕ) : O)) hϖ (K := K) 𝔛reg.toBase hM eMK

  obtain ⟨n, ⟨eMn⟩⟩ := exists_iso_invModule_prod_comp N₀ p hpN₀ 𝔓 O ρO κ toκ 𝔛reg hM s hs

  refine ⟨fun F => n F + 1, fun _ => 1, ⟨?_⟩⟩
  let V : 𝔛reg.Y.Modules :=
    (∏ F, (𝔛reg.comp F) ^ (n F + 1)).invModule ⊗ (∏ F, (𝔛reg.comp F) ^ (1 : ℕ)).module
  have eV : (∏ F, 𝔛reg.comp F ^ n F).invModule ≅ V :=
    (nonempty_invModule_prod_pow_iso_vert 𝔛reg.comp 𝔛reg.comp_isInvertible n).some

  have eEdual : Scheme.Modules.dual E ⊗ E ≅ 𝟙_ _ := (β_ _ _) ≪≫ hE.dual.2.some
  let S'' : 𝔛reg.Y.Modules := (List.finRange m).foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ _)
  have eES : E ≅ S'' := foldrTensorIso A B (𝟙_ _) _ ≪≫ ρ_ _
  exact (ρ_ L).symm ≪≫ whiskerLeftIso L eEdual.symm ≪≫ (α_ _ _ _).symm ≪≫ (β_ _ _) ≪≫
    tensorIso eES (eMn ≪≫ eV) ≪≫ (foldrTensorIso A B V _).symm

#print axioms solution

end S_ModularCurve_DRResolvedModelPackageLevel_exists_pullback_toDR_iso_foldr_ker_tensor_invModule_prod_comp
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackageLevel_exists_pullback_toDR_iso_foldr_ker_tensor_invModule_prod_comp (solution)
