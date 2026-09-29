-- Prove2me | solution 1 for NeronModelInfra.exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3f6d18b0-6b53-57c0-b19b-98eb51e8999a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import Theorems.Thm_NeronModelInfra_exists_componentReading_data_of_smooth_of_forall_specializes
import Theorems.Thm_NeronModelInfra_finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
import Theorems.Thm_NeronModelInfra_ComponentReading_n_le_n_and_isOpenImmersion_of_n_eq_of_specializes
import Theorems.Thm_NeronModelInfra_exists_nhds_extension_chart_of_catchesIndexOnePoints
import Theorems.Thm_NeronModelInfra_exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints
p2m_attr_erase "instance" "NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace Topology

universe u

noncomputable section

namespace S24Asm

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
  [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]

local notation "ιK" => specGenericFibreInclusion R K

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Smooth gK] [IsSeparated gK]
  [LocallyOfFiniteType gK] [QuasiCompact gK] in
theorem genericFibreRestrict_incl_val {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) :
    (genericFibreRestrict R K f (W.ι ≫ f) ⟨W.ι, rfl⟩).1 =
      pullback.map (W.ι ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) W.ι (𝟙 _)
        (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) := by
  apply pullback.hom_ext
  · simp only [genericFibreRestrict, pullback.map, pullback.lift_fst, Category.comp_id]
  · simp only [genericFibreRestrict, pullback.map, pullback.lift_snd, Category.comp_id]

structure Completion (M : ModelFamily R K gK) (i : M.ι) where
  Y' : Scheme.{u}
  f' : Y' ⟶ Spec (CommRingCat.of R)
  j : M.X i ⟶ Y'
  hj : j ≫ f' = M.str i
  e' : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K)) gK
  hjo : IsOpenImmersion j
  sep : IsSeparated f'
  lft : LocallyOfFiniteType f'
  qc : QuasiCompact f'
  iso : IsIso e'.1
  hsurj : ∀ y' : Y', f'.base y' = IsLocalRing.closedPoint R → y' ∈ Set.range j.base
  hchart : schemeHomOverComp (genericFibreRestrict R K f' (M.str i) ⟨j, hj⟩) e' = M.chart i
  smooth : Smooth f'

theorem nonempty_completion (M : ModelFamily R K gK)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i)) (i : M.ι) : Nonempty (Completion K M i) := by
  haveI := (hM i).1; haveI := (hM i).2.1; haveI := (hM i).2.2.1; haveI := (hM i).2.2.2
  obtain ⟨Y', f', j, hj, e', hjo, hsep, hlft, hqc, hiso, hsurj, hchart, hsm⟩ :=
    NeronModelInfra.exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart K gK (M.str i)
      (M.chart i)
  exact ⟨⟨Y', f', j, hj, e', hjo, hsep, hlft, hqc, hiso, hsurj, hchart, hsm ‹_› ‹_›⟩⟩

section Main

variable (M : ModelFamily R K gK) (hfin : Finite M.ι)
  (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
    QuasiCompact (M.str i))

def Cpl (i : M.ι) : Completion K M i := (nonempty_completion K M hM i).some

scoped instance (i : M.ι) : Smooth (Cpl K M hM i).f' := (Cpl K M hM i).smooth
scoped instance (i : M.ι) : IsSeparated (Cpl K M hM i).f' := (Cpl K M hM i).sep
scoped instance (i : M.ι) : LocallyOfFiniteType (Cpl K M hM i).f' := (Cpl K M hM i).lft
scoped instance (i : M.ι) : QuasiCompact (Cpl K M hM i).f' := (Cpl K M hM i).qc
scoped instance (i : M.ι) : IsOpenImmersion (Cpl K M hM i).j := (Cpl K M hM i).hjo
scoped instance (i : M.ι) : IsIso (Cpl K M hM i).e'.1 := (Cpl K M hM i).iso

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Smooth gK] [IsSeparated gK]
  [LocallyOfFiniteType gK] [QuasiCompact gK] in
theorem noetherianSpace_of {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R]
    [LocallyOfFiniteType f] [QuasiCompact f] : NoetherianSpace Y := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian Y := {}
  infer_instance

def IsMaxSpecial {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) (ξ : Y) : Prop :=
  f.base ξ = IsLocalRing.closedPoint R ∧
    ∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ

def Idx : Type u := Σ i : M.ι, {ξ : ↥(Cpl K M hM i).Y' // IsMaxSpecial (Cpl K M hM i).f' ξ}

include hfin in
theorem finite_idx : Finite (Idx K M hM) := by
  haveI := hfin
  haveI : ∀ i : M.ι, Finite {ξ : ↥(Cpl K M hM i).Y' // IsMaxSpecial (Cpl K M hM i).f' ξ} := fun i =>
    (NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
      (Cpl K M hM i).f').1.to_subtype
  exact Finite.instSigma

variable {d : ℕ} [SmoothOfRelativeDimension d gK] {ω : Γ(gK.topDifferentials d, ⊤)}
  (hω : Scheme.Modules.IsFrameOn ω ⊤)

structure RTail {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) (y : Y) where
  isDomain : IsDomain (Y.presheaf.stalk y)
  isDiscreteValuationRing : IsDiscreteValuationRing (Y.presheaf.stalk y)
  algebra : Algebra R (Y.presheaf.stalk y)
  halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))
  algebraK : Algebra K (FractionRing (Y.presheaf.stalk y))
  isScalarTower : IsScalarTower R K (FractionRing (Y.presheaf.stalk y))
  b : Module.Basis (Fin d) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R])
  U : XK.Opens
  hU : IsAffineOpen U
  algebraU : Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y))
  isScalarTowerU : letI := gK.sectionsAlgebra U
    IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y))
  hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))) ≫ hU.fromSpec =
    (schemeHomOverComp
      (pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
        (⟨Y.fromSpecStalk y, halg⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f))
      e).1
  ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U))
  hωU : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω
  a : FractionRing (Y.presheaf.stalk y)
  ha : letI := gK.sectionsAlgebra U
    TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU =
      a • TopFormOrder.topFormMap R K (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)) d
        (exteriorPower.ιMulti (Y.presheaf.stalk y) d b)
  ha0 : a ≠ 0

include hω in
omit [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK] [Smooth gK] in
theorem nonempty_rtail {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
    (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
    (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y) :
    Nonempty (RTail K (gK := gK) (d := d) (ω := ω) f e y) := by
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, h16, h17⟩ :=
    NeronModelInfra.exists_componentReading_data_of_smooth_of_forall_specializes K gK d ω hω f e y hy hmax
  exact ⟨⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, h16, h17⟩⟩

def tail {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
    (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
    (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y) :
    RTail K (gK := gK) (d := d) (ω := ω) f e y :=
  Classical.choice (nonempty_rtail K hω f e y hy hmax)

@[reducible] def mkReading {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [hs : Smooth f]
    [hl : LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [ho : IsOpenImmersion e.1]
    (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
    (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y) :
    ComponentReading R K gK d ω :=
  let t := tail K hω f e y hy hmax
  { Y := Y, f := f, smooth := hs, locallyOfFiniteType := hl, e := e, isOpenImmersion := ho, y := y,
    hy := hy, hmax := hmax,
    isDomain := t.isDomain, isDiscreteValuationRing := t.isDiscreteValuationRing, algebra := t.algebra,
    halg := t.halg, algebraK := t.algebraK, isScalarTower := t.isScalarTower, b := t.b, U := t.U, hU := t.hU,
    algebraU := t.algebraU, isScalarTowerU := t.isScalarTowerU, hx := t.hx, ωU := t.ωU, hωU := t.hωU,
    a := t.a, ha := t.ha, ha0 := t.ha0 }

omit [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK] [Smooth gK] in
@[scoped simp] theorem mkReading_Y {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
    (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
    (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y) :
    (mkReading K hω f e y hy hmax).Y = Y := rfl

section Members

variable (c : Idx K M hM)

abbrev Yp : Scheme.{u} := (Cpl K M hM c.1).Y'

abbrev fp : Yp K M hM c ⟶ Spec (CommRingCat.of R) := (Cpl K M hM c.1).f'

scoped instance : NoetherianSpace ↥(Yp K M hM c) := noetherianSpace_of (fp K M hM c)

theorem exists_V : ∃ V : (Yp K M hM c).Opens, c.2.1 ∈ V ∧
    (∀ y', (fp K M hM c).base y' ≠ IsLocalRing.closedPoint R → y' ∈ V) ∧
    (∀ y', y' ∈ V → (fp K M hM c).base y' = IsLocalRing.closedPoint R → c.2.1 ⤳ y') ∧
    (∀ y', (fp K M hM c).base y' = IsLocalRing.closedPoint R → c.2.1 ⤳ y' → y' ∈ V) :=
  (NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
    (fp K M hM c)).2.2 c.2.1 c.2.2.1 c.2.2.2

def V : (Yp K M hM c).Opens := (exists_V K M hM c).choose

theorem mem_V : c.2.1 ∈ V K M hM c := (exists_V K M hM c).choose_spec.1
theorem mem_V_of_ne (y' : ↥(Yp K M hM c)) (h : (fp K M hM c).base y' ≠ IsLocalRing.closedPoint R) :
    y' ∈ V K M hM c := (exists_V K M hM c).choose_spec.2.1 y' h
theorem gen_V (y' : ↥(Yp K M hM c)) (h : y' ∈ V K M hM c)
    (h' : (fp K M hM c).base y' = IsLocalRing.closedPoint R) : c.2.1 ⤳ y' :=
  (exists_V K M hM c).choose_spec.2.2.1 y' h h'
theorem mem_V_of_specializes (y' : ↥(Yp K M hM c)) (h' : (fp K M hM c).base y' = IsLocalRing.closedPoint R)
    (h : c.2.1 ⤳ y') : y' ∈ V K M hM c :=
  (exists_V K M hM c).choose_spec.2.2.2 y' h' h

abbrev Yc : Scheme.{u} := ↑(V K M hM c)

abbrev fc : Yc K M hM c ⟶ Spec (CommRingCat.of R) := (V K M hM c).ι ≫ fp K M hM c

def ec : SchemeHomOver (pullback.snd (fc K M hM c) (specGenericFibreInclusion R K)) gK :=
  schemeHomOverComp (genericFibreRestrict R K (fp K M hM c) (fc K M hM c) ⟨(V K M hM c).ι, rfl⟩)
    (Cpl K M hM c.1).e'

def yc : ↥(Yc K M hM c) := ⟨c.2.1, mem_V K M hM c⟩

theorem yc_val : ((V K M hM c).ι).base (yc K M hM c) = c.2.1 := rfl

theorem fc_base (y' : ↥(Yc K M hM c)) : (fc K M hM c).base y' = (fp K M hM c).base y'.1 := rfl

theorem hy_c : (fc K M hM c).base (yc K M hM c) = IsLocalRing.closedPoint R := c.2.2.1

theorem hmax_c (y' : ↥(Yc K M hM c)) (h : y' ⤳ yc K M hM c)
    (h' : (fc K M hM c).base y' = IsLocalRing.closedPoint R) : y' = yc K M hM c := by
  apply Subtype.ext
  have h1 : y'.1 ⤳ c.2.1 := h.map (V K M hM c).ι.continuous
  exact c.2.2.2 y'.1 h1 h'

theorem hgen_c (y' : ↥(Yc K M hM c)) (h' : (fc K M hM c).base y' = IsLocalRing.closedPoint R) :
    yc K M hM c ⤳ y' := by
  have h1 : (V K M hM c).ι.base (yc K M hM c) ⤳ (V K M hM c).ι.base y' := gen_V K M hM c y'.1 y'.2 h'
  exact ((V K M hM c).ι.isOpenEmbedding.isInducing.specializes_iff).mp h1

scoped instance : IsOpenImmersion (ec K M hM c).1 := by
  change IsOpenImmersion ((genericFibreRestrict R K (fp K M hM c) (fc K M hM c) ⟨(V K M hM c).ι, rfl⟩).1 ≫
    (Cpl K M hM c.1).e'.1)
  rw [genericFibreRestrict_incl_val]
  infer_instance

end Members

omit [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK] in

theorem specGenericFibreInclusion_base_ne (s : ↥(Spec (CommRingCat.of K))) :
    (specGenericFibreInclusion R K).base s ≠ IsLocalRing.closedPoint R := by
  intro h
  have h1 : ((specGenericFibreInclusion R K).base s).asIdeal = (IsLocalRing.closedPoint R).asIdeal := by rw [h]
  rw [specGenericFibreInclusion_eq, Spec.map_base] at h1
  change (PrimeSpectrum.comap (algebraMap R K) s).asIdeal = _ at h1
  rw [PrimeSpectrum.comap_asIdeal] at h1
  have h2 : s.asIdeal = ⊥ := by
    haveI : s.asIdeal.IsPrime := s.2
    exact (Ideal.eq_bot_of_prime s.asIdeal)
  rw [h2, Ideal.comap_bot_of_injective (algebraMap R K) (IsFractionRing.injective R K)] at h1
  exact IsDiscreteValuationRing.not_a_field R (by
    change IsLocalRing.maximalIdeal R = ⊥
    have : (IsLocalRing.closedPoint R).asIdeal = IsLocalRing.maximalIdeal R := rfl
    rw [← this, ← h1])

section Members2

variable (c : Idx K M hM)

scoped instance : IsIso (ec K M hM c).1 := by
  change IsIso ((genericFibreRestrict R K (fp K M hM c) (fc K M hM c) ⟨(V K M hM c).ι, rfl⟩).1 ≫
    (Cpl K M hM c.1).e'.1)
  rw [genericFibreRestrict_incl_val]
  haveI : IsIso (pullback.map ((V K M hM c).ι ≫ fp K M hM c) (specGenericFibreInclusion R K) (fp K M hM c)
      (specGenericFibreInclusion R K) (V K M hM c).ι (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨?_⟩⟩
    rw [← Set.range_eq_univ, Scheme.Pullback.range_map]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ, iff_true]
    refine ⟨?_, ?_⟩
    · rw [Scheme.Opens.range_ι]
      apply mem_V_of_ne
      intro hp
      refine specGenericFibreInclusion_base_ne (R := R) K
        ((pullback.snd (fp K M hM c) (specGenericFibreInclusion R K)).base p) ?_
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
      exact hp
    · exact ⟨(pullback.snd (fp K M hM c) (specGenericFibreInclusion R K)).base p, rfl⟩
  infer_instance

@[reducible] def Tc : ComponentReading R K gK d ω :=
  mkReading K hω (fc K M hM c) (ec K M hM c) (yc K M hM c) (hy_c K M hM c) (hmax_c K M hM c)

theorem Tc_Y : (Tc K M hM hω c).Y = Yc K M hM c := rfl
theorem Tc_f : (Tc K M hM hω c).f = fc K M hM c := rfl
theorem Tc_e : (Tc K M hM hω c).e = ec K M hM c := rfl
theorem Tc_y : (Tc K M hM hω c).y = yc K M hM c := rfl

end Members2

section Reach

variable (hpts : M.CatchesIndexOnePoints)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Smooth gK] [IsSeparated gK]
  [LocallyOfFiniteType gK] [QuasiCompact gK] in

theorem gFR_incl_comp {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) {W' : Scheme.{u}}
    (k : W' ⟶ ↑U) :
    (genericFibreRestrict R K (U.ι ≫ f) ((k ≫ U.ι) ≫ f) ⟨k, (Category.assoc _ _ _).symm⟩).1 ≫
      pullback.map (U.ι ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) =
    pullback.map ((k ≫ U.ι) ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) (k ≫ U.ι)
        (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) := by
  apply pullback.hom_ext
  · simp only [genericFibreRestrict, Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.comp_id]
  · simp only [genericFibreRestrict, Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc,
      Category.comp_id]

include hpts in
theorem reach (T : ComponentReading R K gK d ω) :
    ∃ (c : Idx K M hM) (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) (fc K M hM c)),
      (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ T.f) u).1 ≫ (ec K M hM c).1 =
        (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1 ∧
      yc K M hM c ⤳ u.1.base ⟨T.y, hyW⟩ := by
  obtain ⟨i, U, hU, u₀, hc₀⟩ := NeronModelInfra.exists_nhds_extension_chart_of_catchesIndexOnePoints K M
    (fun i => (hM i).2.2.1) hpts T.f T.e T.y T.hy T.hmax
  set Cp := Cpl K M hM i
  set u₁ : (U : Scheme.{u}) ⟶ Cp.Y' := u₀.1 ≫ Cp.j with hu₁
  have hu₁f : u₁ ≫ Cp.f' = U.ι ≫ T.f := by rw [hu₁, Category.assoc, Cp.hj, u₀.2]
  set p : ↥Cp.Y' := u₁.base ⟨T.y, hU⟩ with hp
  have hps : Cp.f'.base p = IsLocalRing.closedPoint R := by
    rw [hp, ← Scheme.Hom.comp_apply, hu₁f, Scheme.Hom.comp_apply]
    exact T.hy
  obtain ⟨ξ, ⟨⟨hξs, hξmax⟩, hξp⟩, -⟩ :=
    (NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens Cp.f').2.1 p hps
  let c : Idx K M hM := ⟨i, ⟨ξ, hξs, hξmax⟩⟩
  have hpV : p ∈ V K M hM c := mem_V_of_specializes K M hM c p hps hξp
  let W₀ : (U : Scheme.{u}).Opens := u₁ ⁻¹ᵁ (V K M hM c)
  let W : T.Y.Opens := U.ι ''ᵁ W₀
  have hyW : T.y ∈ W := by
    refine ⟨⟨T.y, hU⟩, hpV, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : (W : Scheme.{u}) ⟶ ↑U, k = (U.ι.isoImage W₀).inv ≫ W₀.ι := ⟨_, rfl⟩
  have hk : k ≫ U.ι = W.ι := by rw [hkdef, Category.assoc]; exact Scheme.Hom.isoImage_inv_ι _ _
  obtain ⟨uu, huudef⟩ : ∃ uu : (W : Scheme.{u}) ⟶ Yc K M hM c, uu = (U.ι.isoImage W₀).inv ≫ (u₁ ∣_ V K M hM c) :=
    ⟨_, rfl⟩
  have huuV : uu ≫ (V K M hM c).ι = k ≫ u₁ := by
    rw [huudef, hkdef, Category.assoc, Category.assoc, morphismRestrict_ι]
  have huu : uu ≫ fc K M hM c = W.ι ≫ T.f := by
    change uu ≫ (V K M hM c).ι ≫ Cp.f' = W.ι ≫ T.f
    rw [← Category.assoc, huuV, Category.assoc, hu₁f, ← hk, Category.assoc]
  refine ⟨c, W, hyW, ⟨uu, huu⟩, ?_, ?_⟩
  ·

    let w : SchemeHomOver (W.ι ≫ T.f) (U.ι ≫ T.f) := ⟨k, by rw [← hk, Category.assoc]⟩
    have hcomp : schemeHomOverComp (⟨uu, huu⟩ : SchemeHomOver (W.ι ≫ T.f) (fc K M hM c))
        (⟨(V K M hM c).ι, rfl⟩ : SchemeHomOver (fc K M hM c) Cp.f') =
        schemeHomOverComp (schemeHomOverComp w u₀) ⟨Cp.j, Cp.hj⟩ := by
      apply Subtype.ext
      change uu ≫ (V K M hM c).ι = (k ≫ u₀.1) ≫ Cp.j
      rw [huuV, hu₁, Category.assoc]
    change (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ T.f) ⟨uu, huu⟩).1 ≫
      ((genericFibreRestrict R K Cp.f' (fc K M hM c) ⟨(V K M hM c).ι, rfl⟩).1 ≫ Cp.e'.1) = _
    rw [← Category.assoc, ← NeronModelInfra.schemeHomOverComp_coe (genericFibreRestrict R K (fc K M hM c) _ _),
      ← genericFibreRestrict_schemeHomOverComp, hcomp, genericFibreRestrict_schemeHomOverComp,
      genericFibreRestrict_schemeHomOverComp]
    simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
    have h2 : (genericFibreRestrict R K Cp.f' (M.str i) ⟨Cp.j, Cp.hj⟩).1 ≫ Cp.e'.1 = (M.chart i).1 := by
      rw [← NeronModelInfra.schemeHomOverComp_coe, Cp.hchart]
    rw [h2]
    have h3 : (genericFibreRestrict R K (M.str i) (U.ι ≫ T.f) u₀).1 ≫ (M.chart i).1 =
        pullback.map (U.ι ≫ T.f) (specGenericFibreInclusion R K) T.f (specGenericFibreInclusion R K) U.ι (𝟙 _)
          (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ T.e.1 := by
      rw [← NeronModelInfra.schemeHomOverComp_coe]; exact hc₀
    rw [h3, genericFibreRestrict_incl_val, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [genericFibreRestrict, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.comp_id]
      change pullback.fst (W.ι ≫ T.f) (specGenericFibreInclusion R K) ≫ k ≫ U.ι = _
      rw [hk]
    · simp only [genericFibreRestrict, pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]
  · apply hgen_c
    change ((uu ≫ fc K M hM c).base ⟨T.y, hyW⟩) = _
    rw [huu, Scheme.Hom.comp_apply]
    exact T.hy

end Reach

section Rel

def Rel' (T : ComponentReading R K gK d ω) (c : Idx K M hM) : Prop :=
  ∃ (W : T.Y.Opens) (hyW : T.y ∈ W) (ε : SchemeHomOver (W.ι ≫ T.f) (fc K M hM c)),
    IsOpenImmersion ε.1 ∧ ε.1.base ⟨T.y, hyW⟩ = yc K M hM c ∧
    (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ T.f) ε).1 ≫ (ec K M hM c).1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1

def Rel (c c' : Idx K M hM) : Prop := Rel' K M hM (Tc K M hM hω c) c'

theorem rel_refl (c : Idx K M hM) : Rel K M hM hω c c := by
  refine ⟨⊤, trivial, ⟨(⊤ : (Yc K M hM c).Opens).ι, rfl⟩, ?_, rfl, rfl⟩
  exact (inferInstance : IsOpenImmersion (⊤ : (Yc K M hM c).Opens).ι)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Smooth gK] [IsSeparated gK]
  [LocallyOfFiniteType gK] [QuasiCompact gK] in
theorem gFR_val_congr {Y X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) {g : Y ⟶ Spec (CommRingCat.of R)}
    (φ ψ : SchemeHomOver g f) (h : φ.1 = ψ.1) :
    (genericFibreRestrict R K f g φ).1 = (genericFibreRestrict R K f g ψ).1 := by
  have : φ = ψ := Subtype.ext h
  rw [this]

theorem rel'_comp (T : ComponentReading R K gK d ω) (c c' : Idx K M hM)
    (h1 : Rel' K M hM T c) (h2 : Rel K M hM hω c c') : Rel' K M hM T c' := by
  obtain ⟨W, hyW, ε, hεo, hεy, hεc⟩ := h1
  obtain ⟨W₂, hy₂, ε₂, hε₂o, hε₂y, hε₂c⟩ := h2
  change (Yc K M hM c).Opens at W₂
  change yc K M hM c ∈ W₂ at hy₂
  change SchemeHomOver (W₂.ι ≫ fc K M hM c) (fc K M hM c') at ε₂
  change ε₂.1.base ⟨yc K M hM c, hy₂⟩ = yc K M hM c' at hε₂y
  change (genericFibreRestrict R K (fc K M hM c') (W₂.ι ≫ fc K M hM c) ε₂).1 ≫ (ec K M hM c').1 =
      (genericFibreRestrict R K (fc K M hM c) (W₂.ι ≫ fc K M hM c) ⟨W₂.ι, rfl⟩).1 ≫ (ec K M hM c).1 at hε₂c
  haveI : IsOpenImmersion ε.1 := hεo
  haveI : IsOpenImmersion ε₂.1 := hε₂o
  let W₀ : (W : Scheme.{u}).Opens := ε.1 ⁻¹ᵁ W₂
  let W₃ : T.Y.Opens := W.ι ''ᵁ W₀
  have hy₀ : (⟨T.y, hyW⟩ : ↥W) ∈ W₀ := by
    change ε.1.base ⟨T.y, hyW⟩ ∈ W₂
    rw [hεy]; exact hy₂
  have hy₃ : T.y ∈ W₃ := ⟨⟨T.y, hyW⟩, hy₀, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : (W₃ : Scheme.{u}) ⟶ ↑W, k = (W.ι.isoImage W₀).inv ≫ W₀.ι := ⟨_, rfl⟩
  have hk : k ≫ W.ι = W₃.ι := by rw [hkdef, Category.assoc]; exact Scheme.Hom.isoImage_inv_ι _ _
  obtain ⟨m, hmdef⟩ : ∃ m : (W₃ : Scheme.{u}) ⟶ ↑W₂, m = (W.ι.isoImage W₀).inv ≫ (ε.1 ∣_ W₂) := ⟨_, rfl⟩
  have hmW₂ : m ≫ W₂.ι = k ≫ ε.1 := by
    rw [hmdef, hkdef, Category.assoc, Category.assoc, morphismRestrict_ι]
  haveI : IsOpenImmersion m := by rw [hmdef]; infer_instance
  have hm_over : m ≫ W₂.ι ≫ fc K M hM c = W₃.ι ≫ T.f := by
    rw [← Category.assoc, hmW₂, Category.assoc, ε.2, ← hk, Category.assoc]
  let ε₃ : SchemeHomOver (W₃.ι ≫ T.f) (fc K M hM c') := ⟨m ≫ ε₂.1, by rw [Category.assoc, ε₂.2, hm_over]⟩
  refine ⟨W₃, hy₃, ε₃, ?_, ?_, ?_⟩
  · change IsOpenImmersion (m ≫ ε₂.1); infer_instance
  ·
    change (m ≫ ε₂.1).base ⟨T.y, hy₃⟩ = yc K M hM c'
    rw [Scheme.Hom.comp_apply]
    have hk₀ : k.base ⟨T.y, hy₃⟩ = ⟨T.y, hyW⟩ := by
      apply W.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hk]; rfl
    have hm₀ : m.base ⟨T.y, hy₃⟩ = ⟨yc K M hM c, hy₂⟩ := by
      apply W₂.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hmW₂, Scheme.Hom.comp_apply, hk₀, hεy]; rfl
    rw [hm₀, hε₂y]
  ·
    have e1 : ε₃ = schemeHomOverComp (⟨m, hm_over⟩ : SchemeHomOver (W₃.ι ≫ T.f) (W₂.ι ≫ fc K M hM c)) ε₂ :=
      Subtype.ext rfl
    rw [e1, genericFibreRestrict_schemeHomOverComp, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hε₂c,
      ← Category.assoc, ← NeronModelInfra.schemeHomOverComp_coe (genericFibreRestrict R K _ _ _),
      ← genericFibreRestrict_schemeHomOverComp]
    have e2 : (genericFibreRestrict R K (fc K M hM c) (W₃.ι ≫ T.f)
        (schemeHomOverComp (⟨m, hm_over⟩ : SchemeHomOver (W₃.ι ≫ T.f) (W₂.ι ≫ fc K M hM c)) ⟨W₂.ι, rfl⟩)).1 =
        (genericFibreRestrict R K (fc K M hM c) (W₃.ι ≫ T.f)
          (schemeHomOverComp (⟨k, by rw [← hk, Category.assoc]⟩ : SchemeHomOver (W₃.ι ≫ T.f) (W.ι ≫ T.f)) ε)).1 := by
      apply gFR_val_congr
      simp only [NeronModelInfra.schemeHomOverComp_coe]
      exact hmW₂
    rw [e2, genericFibreRestrict_schemeHomOverComp, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hεc,
      ← Category.assoc, ← NeronModelInfra.schemeHomOverComp_coe (genericFibreRestrict R K _ _ _),
      ← genericFibreRestrict_schemeHomOverComp]
    congr 1
    apply gFR_val_congr
    simp only [NeronModelInfra.schemeHomOverComp_coe]
    exact hk

end Rel

section Rel2

theorem rel'_of_n_eq (T : ComponentReading R K gK d ω) (c : Idx K M hM)
    (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) (fc K M hM c))
    (hu : (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ T.f) u).1 ≫ (ec K M hM c).1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1)
    (hgen : yc K M hM c ⤳ u.1.base ⟨T.y, hyW⟩) (heq : T.n = (Tc K M hM hω c).n) :
    Rel' K M hM T c := by
  obtain ⟨-, h2⟩ := NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes K hω T
    (Tc K M hM hω c) W hyW u hu hgen
  obtain ⟨hpt, W', hW', hyW', hoi⟩ := h2 heq
  refine ⟨W', hyW', ⟨T.Y.homOfLE hW' ≫ u.1, by rw [Category.assoc, u.2, ← Category.assoc, Scheme.homOfLE_ι]⟩,
    hoi, ?_, ?_⟩
  · change (T.Y.homOfLE hW' ≫ u.1).base ⟨T.y, hyW'⟩ = yc K M hM c
    rw [Scheme.Hom.comp_apply, Scheme.homOfLE_apply']
    exact hpt
  · have e1 : (⟨T.Y.homOfLE hW' ≫ u.1, by rw [Category.assoc, u.2, ← Category.assoc, Scheme.homOfLE_ι]⟩ :
        SchemeHomOver (W'.ι ≫ T.f) (fc K M hM c)) =
        schemeHomOverComp (⟨T.Y.homOfLE hW', by rw [← Category.assoc, Scheme.homOfLE_ι]⟩ :
          SchemeHomOver (W'.ι ≫ T.f) (W.ι ≫ T.f)) u := Subtype.ext rfl
    rw [e1, genericFibreRestrict_schemeHomOverComp, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hu,
      ← Category.assoc, ← NeronModelInfra.schemeHomOverComp_coe (genericFibreRestrict R K _ _ _),
      ← genericFibreRestrict_schemeHomOverComp]
    congr 1
    apply gFR_val_congr
    simp only [NeronModelInfra.schemeHomOverComp_coe]
    exact Scheme.homOfLE_ι _ _

theorem rel_symm (c c' : Idx K M hM) (h : Rel K M hM hω c c') : Rel K M hM hω c' c := by
  obtain ⟨W, hyW, ε, hεo, hεy, hεc⟩ := h
  change (Yc K M hM c).Opens at W
  change yc K M hM c ∈ W at hyW
  change SchemeHomOver (W.ι ≫ fc K M hM c) (fc K M hM c') at ε
  change ε.1.base ⟨yc K M hM c, hyW⟩ = yc K M hM c' at hεy
  change (genericFibreRestrict R K (fc K M hM c') (W.ι ≫ fc K M hM c) ε).1 ≫ (ec K M hM c').1 =
      (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ fc K M hM c) ⟨W.ι, rfl⟩).1 ≫ (ec K M hM c).1 at hεc
  haveI : IsOpenImmersion ε.1 := hεo
  let W' : (Yc K M hM c').Opens := ε.1.opensRange
  have hy' : yc K M hM c' ∈ W' := by rw [← hεy]; exact ⟨_, rfl⟩
  let ι' := ε.1.isoOpensRange

  have h2 : W.ι ≫ fc K M hM c = ε.1 ≫ fc K M hM c' := ε.2.symm
  have h3 : ι'.inv ≫ ε.1 = W'.ι := Scheme.Hom.isoOpensRange_inv_comp _
  have hε'over : (ι'.inv ≫ W.ι) ≫ fc K M hM c = W'.ι ≫ fc K M hM c' :=
    calc (ι'.inv ≫ W.ι) ≫ fc K M hM c = ι'.inv ≫ (W.ι ≫ fc K M hM c) := Category.assoc _ _ _
      _ = ι'.inv ≫ (ε.1 ≫ fc K M hM c') := congrArg (ι'.inv ≫ ·) h2
      _ = (ι'.inv ≫ ε.1) ≫ fc K M hM c' := (Category.assoc _ _ _).symm
      _ = W'.ι ≫ fc K M hM c' := congrArg (· ≫ fc K M hM c') h3
  let ε' : SchemeHomOver (W'.ι ≫ fc K M hM c') (fc K M hM c) := ⟨ι'.inv ≫ W.ι, hε'over⟩
  refine ⟨W', hy', ε', ?_, ?_, ?_⟩
  · change IsOpenImmersion (ι'.inv ≫ W.ι); infer_instance
  · change (ι'.inv ≫ W.ι).base ⟨yc K M hM c', hy'⟩ = yc K M hM c
    have h1 : (⟨yc K M hM c', hy'⟩ : ↥W') = ι'.hom.base ⟨yc K M hM c, hyW⟩ := by
      apply W'.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_hom_ι, hεy]; rfl
    rw [h1, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]; rfl
  ·
    change (genericFibreRestrict R K (fc K M hM c) (W'.ι ≫ fc K M hM c') ε').1 ≫ (ec K M hM c).1 =
      (genericFibreRestrict R K (fc K M hM c') (W'.ι ≫ fc K M hM c') ⟨W'.ι, rfl⟩).1 ≫ (ec K M hM c').1
    let h : SchemeHomOver (W.ι ≫ fc K M hM c) (W'.ι ≫ fc K M hM c') :=
      ⟨ι'.hom, by rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ε.2]⟩
    haveI : IsIso (genericFibreRestrict R K (W'.ι ≫ fc K M hM c') (W.ι ≫ fc K M hM c) h).1 := by
      change IsIso (pullback.lift (pullback.fst (W.ι ≫ fc K M hM c) (specGenericFibreInclusion R K) ≫ ι'.hom)
        (pullback.snd _ _) _)
      have : pullback.lift (pullback.fst (W.ι ≫ fc K M hM c) (specGenericFibreInclusion R K) ≫ ι'.hom)
          (pullback.snd (W.ι ≫ fc K M hM c) (specGenericFibreInclusion R K)) (by rw [Category.assoc, h.2, pullback.condition]) =
          pullback.map (W.ι ≫ fc K M hM c) (specGenericFibreInclusion R K) (W'.ι ≫ fc K M hM c')
            (specGenericFibreInclusion R K) ι'.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h.2])
            ((Category.comp_id _).trans (Category.id_comp _).symm) := by
        apply pullback.hom_ext <;> simp [pullback.map]
      rw [this]; infer_instance
    have eA : (genericFibreRestrict R K (W'.ι ≫ fc K M hM c') (W.ι ≫ fc K M hM c) h).1 ≫
        (genericFibreRestrict R K (fc K M hM c) (W'.ι ≫ fc K M hM c') ε').1 =
        (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ fc K M hM c) (schemeHomOverComp h ε')).1 := by
      rw [genericFibreRestrict_schemeHomOverComp]; rfl
    have eB : (genericFibreRestrict R K (W'.ι ≫ fc K M hM c') (W.ι ≫ fc K M hM c) h).1 ≫
        (genericFibreRestrict R K (fc K M hM c') (W'.ι ≫ fc K M hM c') ⟨W'.ι, rfl⟩).1 =
        (genericFibreRestrict R K (fc K M hM c') (W.ι ≫ fc K M hM c) (schemeHomOverComp h ⟨W'.ι, rfl⟩)).1 := by
      rw [genericFibreRestrict_schemeHomOverComp]; rfl
    have e1 : (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ fc K M hM c) (schemeHomOverComp h ε')).1 =
        (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ fc K M hM c) ⟨W.ι, rfl⟩).1 := by
      apply gFR_val_congr
      simp only [NeronModelInfra.schemeHomOverComp_coe]
      change ι'.hom ≫ ι'.inv ≫ W.ι = W.ι
      rw [Iso.hom_inv_id_assoc]
    have e2 : (genericFibreRestrict R K (fc K M hM c') (W.ι ≫ fc K M hM c) (schemeHomOverComp h ⟨W'.ι, rfl⟩)).1 =
        (genericFibreRestrict R K (fc K M hM c') (W.ι ≫ fc K M hM c) ε).1 := by
      apply gFR_val_congr
      simp only [NeronModelInfra.schemeHomOverComp_coe]
      exact Scheme.Hom.isoOpensRange_hom_ι _
    refine (cancel_epi (genericFibreRestrict R K (W'.ι ≫ fc K M hM c') (W.ι ≫ fc K M hM c) h).1).mp ?_
    set X := (genericFibreRestrict R K (W'.ι ≫ fc K M hM c') (W.ι ≫ fc K M hM c) h).1 with hX
    calc X ≫ (genericFibreRestrict R K (fc K M hM c) (W'.ι ≫ fc K M hM c') ε').1 ≫ (ec K M hM c).1
        = (X ≫ (genericFibreRestrict R K (fc K M hM c) (W'.ι ≫ fc K M hM c') ε').1) ≫ (ec K M hM c).1 :=
          (Category.assoc _ _ _).symm
      _ = (genericFibreRestrict R K (fc K M hM c) (W.ι ≫ fc K M hM c) ⟨W.ι, rfl⟩).1 ≫ (ec K M hM c).1 := by
          rw [eA, e1]
      _ = (genericFibreRestrict R K (fc K M hM c') (W.ι ≫ fc K M hM c) ε).1 ≫ (ec K M hM c').1 := hεc.symm
      _ = (X ≫ (genericFibreRestrict R K (fc K M hM c') (W'.ι ≫ fc K M hM c') ⟨W'.ι, rfl⟩).1) ≫
            (ec K M hM c').1 := by rw [eB, e2]
      _ = X ≫ (genericFibreRestrict R K (fc K M hM c') (W'.ι ≫ fc K M hM c') ⟨W'.ι, rfl⟩).1 ≫ (ec K M hM c').1 :=
          Category.assoc _ _ _

end Rel2

section Final

variable (LXK : RelativeGroupLaw K gK) (hpts : M.CatchesIndexOnePoints)

include LXK hpts in
theorem nonempty_idx : Nonempty (Idx K M hM) := by
  obtain ⟨i, U, hU, u₀, -⟩ := NeronModelInfra.exists_nhds_extension_chart_of_catchesIndexOnePoints K M
    (fun i => (hM i).2.2.1) hpts (𝟙 (Spec (CommRingCat.of R)))
    (LXK.one (pullback.snd (𝟙 _) (specGenericFibreInclusion R K))) (IsLocalRing.closedPoint R) rfl
    (fun y _ h => h)
  set Cp := Cpl K M hM i
  set p : ↥Cp.Y' := (u₀.1 ≫ Cp.j).base ⟨IsLocalRing.closedPoint R, hU⟩ with hp
  have hps : Cp.f'.base p = IsLocalRing.closedPoint R := by
    rw [hp, ← Scheme.Hom.comp_apply, Category.assoc, Cp.hj, u₀.2, Scheme.Hom.comp_apply]
    rfl
  obtain ⟨ξ, ⟨⟨hξs, hξmax⟩, -⟩, -⟩ :=
    (NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens Cp.f').2.1 p hps
  exact ⟨⟨i, ⟨ξ, hξs, hξmax⟩⟩⟩

include hfin hM hω LXK hpts in

theorem exists_D : ∃ D : MinimalComponentData R K gK d ω, D.IsOmegaMinimal := by
  classical
  haveI : Finite (Idx K M hM) := finite_idx K M hfin hM
  haveI : Nonempty (Idx K M hM) := nonempty_idx K M hM LXK hpts

  obtain ⟨c₀, hc₀⟩ := Finite.exists_min (fun c : Idx K M hM => (Tc K M hM hω c).n)
  set n₀ := (Tc K M hM hω c₀).n with hn₀

  let I₁ := {c : Idx K M hM // (Tc K M hM hω c).n = n₀}
  haveI : Nonempty I₁ := ⟨⟨c₀, rfl⟩⟩
  let s : Setoid I₁ :=
    { r := fun a b => Rel K M hM hω a.1 b.1
      iseqv :=
        { refl := fun a => rel_refl K M hM hω a.1
          symm := fun h => rel_symm K M hM hω _ _ h
          trans := fun h h' => rel'_comp K M hM hω _ _ _ h h' } }
  let Q := Quotient s
  haveI : Finite Q := Quotient.finite s
  haveI : Nonempty Q := ⟨Quotient.mk s (Classical.arbitrary I₁)⟩
  let rep : Q → I₁ := fun q => q.out
  have hrep : ∀ q : Q, Quotient.mk s (rep q) = q := fun q => Quotient.out_eq q
  have hrel_of_mk_eq : ∀ a b : I₁, Quotient.mk s a = Quotient.mk s b → Rel K M hM hω a.1 b.1 :=
    fun a b h => Quotient.exact h

  haveI : ∀ c : Idx K M hM, QuasiCompact (fc K M hM c) := fun c => by
    haveI : NoetherianSpace ↥(Yc K M hM c) := NoetherianSpace.set _
    infer_instance
  refine ⟨{ ι := Q, finite := inferInstance, nonempty := inferInstance, C := fun q => Tc K M hM hω (rep q).1,
            isSeparated := fun q => inferInstance, quasiCompact := fun q => inferInstance,
            isIso := fun q => inferInstance, hgen := fun q => hgen_c K M hM (rep q).1, inequiv := ?_ }, ?_, ?_⟩
  ·
    intro q q' hne U hyU u heq
    apply hne
    have hsp : (fc K M hM (rep q').1).base (u.1.base ⟨yc K M hM (rep q).1, hyU⟩) = IsLocalRing.closedPoint R := by
      rw [← Scheme.Hom.comp_apply, u.2, Scheme.Hom.comp_apply]
      exact hy_c K M hM (rep q).1
    have hg : yc K M hM (rep q').1 ⤳ u.1.base ⟨yc K M hM (rep q).1, hyU⟩ := hgen_c K M hM (rep q').1 _ hsp
    have hn : (Tc K M hM hω (rep q).1).n = (Tc K M hM hω (rep q').1).n := (rep q).2.trans (rep q').2.symm
    have r : Rel K M hM hω (rep q).1 (rep q').1 :=
      rel'_of_n_eq K M hM hω (Tc K M hM hω (rep q).1) (rep q').1 U hyU u heq hg hn
    rw [← hrep q, ← hrep q']
    exact Quotient.sound r
  ·
    intro q T
    obtain ⟨c, W, hyW, u, hu, hg⟩ := reach K M hM hpts T
    have h1 := (NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes K hω T
      (Tc K M hM hω c) W hyW u hu hg).1
    have h0 : (Tc K M hM hω (rep q).1).n ≤ (Tc K M hM hω c).n := by rw [(rep q).2]; exact hc₀ c
    exact h0.trans h1
  ·
    rintro T ⟨q₀, hT⟩
    obtain ⟨c, W, hyW, u, hu, hg⟩ := reach K M hM hpts T
    have h1 := (NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes K hω T
      (Tc K M hM hω c) W hyW u hu hg).1
    have hTn : T.n = n₀ := hT.trans (rep q₀).2
    have hc : (Tc K M hM hω c).n = n₀ := le_antisymm (h1.trans hTn.le) (hc₀ c)
    have heq : T.n = (Tc K M hM hω c).n := hTn.trans hc.symm
    have r1 : Rel' K M hM T c := rel'_of_n_eq K M hM hω T c W hyW u hu hg heq
    let c1 : I₁ := ⟨c, hc⟩
    let q := Quotient.mk s c1
    have r2 : Rel K M hM hω c (rep q).1 := by
      apply rel_symm
      exact hrel_of_mk_eq (rep q) c1 (hrep q)
    exact ⟨q, rel'_comp K M hM hω T c (rep q).1 r1 r2⟩

end Final

end Main

end S24Asm
p2m_reactivate "P2MW.S_NeronModelInfra_exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints.S24Asm"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (M : ModelFamily R K gK) (hfin : Finite M.ι)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤) :
    ∃ D : MinimalComponentData R K gK d ω, D.IsOmegaMinimal :=
  S24Asm.exists_D K M hfin hM hω LXK hpts

end
p2m_reactivate "P2MW.S_NeronModelInfra_exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints.S24Asm"

end S_NeronModelInfra_exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints
end P2MW
export P2MW.S_NeronModelInfra_exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints (solution)
