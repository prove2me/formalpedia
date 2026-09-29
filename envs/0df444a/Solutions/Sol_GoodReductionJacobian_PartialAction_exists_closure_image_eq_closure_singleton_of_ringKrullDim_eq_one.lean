-- Prove2me | solution 1 for GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/dbd35e54-b7c6-58c0-a5c3-b4556cf56fa5

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_partialAction_compatible_maximal_of_isProper
import Theorems.Thm_AlgebraicGeometry_exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
import Theorems.Thm_AlgebraicGeometry_exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
import Theorems.Thm_GoodReductionJacobian_PartialAction_hom_base_notMem_of_snd_notMem_of_isProper
import Theorems.Thm_AlgebraicGeometry_exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_eq_of_iso_opens
import Theorems.Thm_GoodReductionJacobian_PartialAction_base_hom_eq_of_compatible_of_isIso_stalkMap
import Theorems.Thm_GoodReductionJacobian_PartialAction_closure_image_preimage_closure_eq_closure_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_PartialAction_exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace

universe u

namespace B1dGlue

theorem isIntegrallyClosed_stalk_of_isIso_stalkMap
    {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X) [IsIso (g.stalkMap x)]
    (h : IsIntegrallyClosed (Y.presheaf.stalk (g.base x))) : IsIntegrallyClosed (X.presheaf.stalk x) := by
  haveI := h
  exact IsIntegrallyClosed.of_equiv (asIso (g.stalkMap x)).commRingCatIsoToRingEquiv

theorem isProper_of_comp_eq {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [IsProper fX] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = fX) : IsProper g := by
  haveI : IsProper (g ≫ fY) := by rw [hg]; infer_instance
  exact IsProper.of_comp g fY

theorem eq_genericPoint_of_ringKrullDim_stalk_eq_zero
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsIntegral X]
    (x : X) (hx : ringKrullDim (X.presheaf.stalk x) = 0) : x = genericPoint X := by

  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  letI := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  haveI := hU.isLocalization_stalk ⟨x, hxU⟩
  have hh : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.height = 0 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
      (X.presheaf.stalk x)
    rw [hx] at this
    exact_mod_cast this.symm
  have hmin : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal = ⊥ := by
    have h0 := Ideal.height_eq_zero_iff.mp hh
    rw [IsDomain.minimalPrimes_eq_singleton_bot] at h0
    exact h0
  have hgen : hU.primeIdealOf ⟨x, hxU⟩ = genericPoint (Spec Γ(X, U)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hmin
  calc x = hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) := (hU.fromSpec_primeIdealOf ⟨x, hxU⟩).symm
    _ = hU.fromSpec (genericPoint (Spec Γ(X, U))) := by rw [hgen]
    _ = genericPoint X := genericPoint_eq_of_isOpenImmersion hU.fromSpec

theorem isIntegral_pullback_of_geometricallyIrreducible_of_smooth
    {k : Type u} [Field k] {G P : Scheme.{u}} (f : G ⟶ Spec (.of k)) (p : P ⟶ Spec (.of k))
    [GeometricallyIrreducible f] [Smooth f] [LocallyOfFiniteType p] [IsIntegral P] :
    IsIntegral (pullback f p) := by
  haveI : IrreducibleSpace ↥(pullback f p) := inferInstance
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : IsReduced (pullback f p) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.snd f p)
  haveI : Nonempty ↥(pullback f p) := inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end B1dGlue

namespace B1dGlue

theorem isIntegrallyClosed_sections_of_stalk {X : Scheme.{u}} [IsIntegral X] {W : X.Opens}
    (hW : IsAffineOpen W) [Nonempty W] (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(X, W) := by
  refine IsIntegrallyClosed.of_localization_maximal (fun p _ hp => ?_)
  haveI : p.IsPrime := hp.isPrime
  have hmem : hW.fromSpec ⟨p, hp.isPrime⟩ ∈ W := by
    have h : (hW.fromSpec ⟨p, hp.isPrime⟩ : X) ∈ Set.range hW.fromSpec := ⟨_, rfl⟩
    rwa [hW.range_fromSpec] at h
  let x : W := ⟨hW.fromSpec ⟨p, hp.isPrime⟩, hmem⟩
  letI := X.presheaf.algebra_section_stalk x
  have hx : hW.primeIdealOf x = ⟨p, hp.isPrime⟩ := by
    apply hW.fromSpec.injective
    rw [hW.fromSpec_primeIdealOf]
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk (x : X)) p := by
    have := hW.isLocalization_stalk x
    rw [hx] at this
    exact this
  haveI := hn (x : X)
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (x : X))
      (Localization.AtPrime p)).toRingEquiv

theorem isIntegrallyClosed_stalk_pullback_of_smooth
    {k : Type u} [Field k] {G P : Scheme.{u}} (f : G ⟶ Spec (.of k)) (p : P ⟶ Spec (.of k))
    [Smooth f] [IsIntegral P] (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y))
    (ζ : ↥(pullback f p)) : IsIntegrallyClosed ((pullback f p).presheaf.stalk ζ) := by

  obtain ⟨_, ⟨S, hS, rfl⟩, hyS, -⟩ :=
    P.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (pullback.snd f p ζ)) isOpen_univ
  haveI : Nonempty S := ⟨⟨_, hyS⟩⟩
  haveI : IsAffine (S : Scheme.{u}) := hS
  haveI : IsIntegrallyClosed Γ(P, S) := isIntegrallyClosed_sections_of_stalk hS hn
  haveI : IsIntegrallyClosed Γ((S : Scheme.{u}), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.Opens.topIso S).symm.commRingCatIsoToRingEquiv

  set V : (pullback f p).Opens := pullback.snd f p ⁻¹ᵁ S with hV
  have hζV : ζ ∈ V := hyS
  obtain ⟨-, hic⟩ := AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk
    (pullback.snd f p ∣_ S) (⟨ζ, hζV⟩ : ↥V)
  haveI := hic
  exact IsIntegrallyClosed.of_equiv (asIso (V.ι.stalkMap ⟨ζ, hζV⟩)).symm.commRingCatIsoToRingEquiv

theorem geometricallyIrreducible_of_connectedSpace_of_smooth'
    {k : Type u} [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k))
    [QuasiCompact f] [ConnectedSpace G] [Smooth f] (L : GoodReductionJacobian.RelativeGroupLaw k f) :
    GeometricallyIrreducible f := by
  obtain ⟨G₀, i, L₀, hi, -, hirr, hrange, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
      k L
  have hsurj : Function.Surjective i.base := by
    rw [← Set.range_eq_univ]
    show Set.range i = Set.univ
    rw [hrange]
    exact PreconnectedSpace.connectedComponent_eq_univ _
  have h : IsIrreducible (Set.univ : Set G) := by
    have := (IrreducibleSpace.isIrreducible_univ G₀).image i.base i.base.hom.continuous.continuousOn
    rwa [Set.image_univ, Set.range_eq_univ.mpr hsurj] at this
  haveI : IrreducibleSpace G := (irreducibleSpace_def G).2 h
  exact AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed f

theorem isIntegral_of_geometricallyIrreducible_of_smooth
    {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k)) [GeometricallyIrreducible f] [Smooth f] :
    IsIntegral G := by
  haveI : IrreducibleSpace G := GeometricallyIrreducible.irreducibleSpace_of_subsingleton f
  haveI : IsReduced G := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian f
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem isIso_stalkMap_of_isIso_morphismRestrict {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens) [IsIso (g ∣_ U)]
    (x : X) (hx : g.base x ∈ U) : IsIso (g.stalkMap x) := by
  have e := morphismRestrictStalkMap g U ⟨x, hx⟩
  haveI h0 : IsIso ((g ∣_ U).stalkMap ⟨x, hx⟩) := inferInstance
  have h : g.stalkMap x = e.inv.left ≫ (g ∣_ U).stalkMap ⟨x, hx⟩ ≫ e.hom.right := Arrow.iso_w' e
  haveI h1 : IsIso e.inv.left := Arrow.isIso_left (sq := e.inv)
  haveI h2 : IsIso e.hom.right := Arrow.isIso_right (sq := e.hom)
  rw [h]; exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h0 h2)

theorem denseRange_hom_of_compatible
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f] (L : GoodReductionJacobian.RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι₀ : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι₀] (hι₀ : ι₀ ≫ p = V.ι ≫ f)
    (a : GoodReductionJacobian.PartialAction k f p) (hc : a.Compatible L V ι₀ hι₀) : DenseRange a.hom.base := by

  let t : (V : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := V.ι ≫ f
  let v : NeronModelInfra.SchemeHomOver t (V.ι ≫ f) := ⟨𝟙 _, Category.id_comp _⟩
  have hmul : NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : NeronModelInfra.SchemeHomOver (V.ι ≫ f) f) =
      L.mul t (L.one t) (NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : NeronModelInfra.SchemeHomOver (V.ι ≫ f) f)) :=
    (L.one_mul t _).symm
  obtain ⟨hd, hact⟩ := hc t (L.one t) v v hmul
  have hfac : a.liftDom (L.one t) (GoodReductionJacobian.PartialAction.modelPoint ι₀ hι₀ v) hd ≫ a.hom = ι₀ := by
    have := congrArg Subtype.val hact
    simpa [GoodReductionJacobian.PartialAction.act, GoodReductionJacobian.PartialAction.modelPoint, v] using this
  have hsub : Set.range ι₀.base ⊆ Set.range a.hom.base := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(a.liftDom (L.one t) (GoodReductionJacobian.PartialAction.modelPoint ι₀ hι₀ v) hd).base y, by
      rw [← Scheme.Hom.comp_apply, hfac]⟩
  have hdense : Dense (Set.range ι₀.base) :=
    ι₀.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  exact hdense.mono hsub

end B1dGlue

open B1dGlue in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y))
    (D : P.Opens) (τ : (D : Scheme.{u}) ⟶ G) [IsProper τ] (hτ : τ ≫ f = D.ι ≫ p)
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u}))
    [IsOpenImmersion ι] (hτι : ι ≫ τ = V.ι)
    (w : P) (hw : w ∉ (D : Set P)) (hw₁ : ringKrullDim (P.presheaf.stalk w) = 1) :
    ∃ (P' : Scheme.{u}) (π : P' ⟶ P) (V' : G.Opens)
      (ι' : (V' : Scheme.{u}) ⟶ P') (hι' : ι' ≫ π ≫ p = V'.ι ≫ f) (a' : PartialAction k f (π ≫ p))
      (w' w'' : P'),
      IsIntegral P' ∧ (∀ y : P', IsIntegrallyClosed (P'.presheaf.stalk y)) ∧ IsProper π ∧
      topologicalKrullDim ↥P' = topologicalKrullDim ↥G ∧
      Nonempty (V' : Scheme.{u}) ∧ IsOpenImmersion ι' ∧
      a'.Compatible L V' ι' hι' ∧ a'.Maximal ∧
      (∀ z : ↥(pullback f (π ≫ p)),
        ringKrullDim ((pullback f (π ≫ p)).presheaf.stalk z) ≤ 1 → z ∈ a'.dom) ∧
      π.base w' = w ∧
      ringKrullDim (P'.presheaf.stalk w') = 1 ∧ ringKrullDim (P'.presheaf.stalk w'') = 1 ∧
      closure (a'.hom.base '' ((a'.dom.ι ≫ pullback.snd f (π ≫ p)).base ⁻¹' closure {w'})) =
        closure {w''} := by

  have hι₀ : (ι ≫ D.ι) ≫ p = V.ι ≫ f := by rw [Category.assoc, ← hτ, ← Category.assoc, hτι]
  haveI : IsOpenImmersion (ι ≫ D.ι) := inferInstance
  obtain ⟨a, hc, hm, hcod⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_partialAction_compatible_maximal_of_isProper k f L p hn V (ι ≫ D.ι) hι₀

  haveI : GeometricallyIrreducible f := geometricallyIrreducible_of_connectedSpace_of_smooth' f L
  haveI : LocallyOfFiniteType f := inferInstance
  obtain ⟨ζ, hζcl, hζw, hζdim⟩ :=
    AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat f p w
  have hζ₁ : ringKrullDim ((pullback f p).presheaf.stalk ζ) = 1 := by rw [hζdim, hw₁]
  have hζdom : ζ ∈ a.dom := hcod ζ (by rw [hζ₁])
  have hζn : IsIntegrallyClosed ((pullback f p).presheaf.stalk ζ) := isIntegrallyClosed_stalk_pullback_of_smooth f p hn ζ

  haveI : IsIntegral (pullback f p) := isIntegral_pullback_of_geometricallyIrreducible_of_smooth f p
  haveI : Nonempty ↥(a.dom : Scheme.{u}) := ⟨⟨ζ, hζdom⟩⟩
  haveI : IsIntegral (a.dom : Scheme.{u}) := inferInstance
  haveI : LocallyOfFiniteType p := inferInstance
  have hdomα : DenseRange a.hom.base := denseRange_hom_of_compatible k f L p V (ι ≫ D.ι) hι₀ a hc
  have hbd : a.hom.base ⟨ζ, hζdom⟩ ∉ (D : Set P) :=
    GoodReductionJacobian.PartialAction.hom_base_notMem_of_snd_notMem_of_isProper k f L p D τ hτ V ι hτι a hc ⟨ζ, hζdom⟩ (by
      change (pullback.snd f p).base ζ ∉ (D : Set P); rw [hζw]; exact hw)
  have hnd : ringKrullDim (P.presheaf.stalk (a.hom.base ⟨ζ, hζdom⟩)) ≠ 0 := by
    intro h0
    apply hbd
    rw [eq_genericPoint_of_ringKrullDim_stalk_eq_zero p _ h0]

    obtain ⟨v⟩ := (inferInstance : Nonempty (V : Scheme.{u}))
    exact ((genericPoint_spec P).mem_open_set_iff D.isOpen).mpr ⟨_, Set.mem_univ _, (ι.base v).2⟩

  obtain ⟨P'', p'', hP''i, hP''p, β, hβ, W, hWd, hβW, U', hU', hζU', α', hα', hα'ζ⟩ :=
    AlgebraicGeometry.exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one
      (pullback.fst f p ≫ f) p a.dom a.hom (by rw [a.hom_comp, pullback.condition]) hdomα ζ hζdom hζ₁ hζn hnd

  haveI := hP''i; haveI := hP''p
  haveI : LocallyOfFiniteType p'' := inferInstance
  haveI : QuasiCompact p'' := inferInstance
  obtain ⟨P', ν, hP'i, hP'n, hνfin, hνsurj, hνdim, hνiso⟩ :=
    AlgebraicGeometry.exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral k p''
  haveI := hP'i; haveI := hνfin
  refine ⟨P', ν ≫ β, ?_⟩

  haveI hβWn : IsIso (ν ∣_ (β ⁻¹ᵁ W)) := hνiso _ (fun y hy => by
    haveI := isIso_stalkMap_of_isIso_morphismRestrict β W y hy
    exact isIntegrallyClosed_stalk_of_isIso_stalkMap β y (hn _))
  haveI hπW : IsIso ((ν ≫ β) ∣_ W) := by
    rw [morphismRestrict_comp]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ hβWn hβW

  let ι₀ : (V : Scheme.{u}) ⟶ P := ι ≫ D.ι
  let V' : G.Opens := V.ι ''ᵁ (ι₀ ⁻¹ᵁ W)
  let ι' : (V' : Scheme.{u}) ⟶ P' :=
    (V.ι.isoImage (ι₀ ⁻¹ᵁ W)).inv ≫ (ι₀ ∣_ W) ≫ inv ((ν ≫ β) ∣_ W) ≫ ((ν ≫ β) ⁻¹ᵁ W).ι
  have hι'π : ι' ≫ (ν ≫ β) = (V.ι.isoImage (ι₀ ⁻¹ᵁ W)).inv ≫ (ι₀ ⁻¹ᵁ W).ι ≫ ι₀ := by
    simp only [ι', Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, morphismRestrict_ι]
  have hι' : ι' ≫ (ν ≫ β) ≫ p = V'.ι ≫ f := by
    rw [← Category.assoc, hι'π, Category.assoc, Category.assoc, hι₀, ← Category.assoc ((ι₀ ⁻¹ᵁ W).ι),
      ← Category.assoc, Scheme.Hom.isoImage_inv_ι]
  haveI : IsOpenImmersion ι' := by
    simp only [ι']; infer_instance
  haveI : Nonempty (V' : Scheme.{u}) := by
    obtain ⟨x, ⟨v, rfl⟩, hxW⟩ := hWd.inter_open_nonempty _ ι₀.isOpenEmbedding.isOpen_range
      (Set.range_nonempty _)
    exact ⟨⟨V.ι.base v, (Scheme.Opens.mem_ι_image_iff V).mpr hxW⟩⟩

  haveI : IsProper β := isProper_of_comp_eq p'' p β hβ
  haveI : IsProper (ν ≫ β) := inferInstance
  haveI : IsProper ((ν ≫ β) ≫ p) := inferInstance
  obtain ⟨a', hc', hm', hcod'⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_partialAction_compatible_maximal_of_isProper k f L ((ν ≫ β) ≫ p)
      hP'n V' ι' hι'

  haveI : LocallyOfFiniteType p := inferInstance
  haveI : QuasiCompact p := inferInstance
  have hWne : (W : Set P).Nonempty := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (V : Scheme.{u}))
    exact hWd.nonempty_iff.mpr ⟨ι₀.base v⟩
  obtain ⟨w', hπw', hisow'⟩ := AlgebraicGeometry.exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one p (ν ≫ β) W
    hWne w hw₁ (hn w)
  have hw'₁ : ringKrullDim (P'.presheaf.stalk w') = 1 := by
    rw [← hw₁, ← hπw']
    exact (ringKrullDim_eq_of_ringEquiv (asIso ((ν ≫ β).stalkMap w')).commRingCatIsoToRingEquiv).symm
  haveI : LocallyOfFiniteType ((ν ≫ β) ≫ p) := inferInstance
  obtain ⟨ζ', hζ'cl, hζ'w, hζ'dim⟩ :=
    AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat f ((ν ≫ β) ≫ p) w'
  have hζ'dom : ζ' ∈ a'.dom := hcod' ζ' (by rw [hζ'dim, hw'₁])

  let w'' : P' := a'.hom.base ⟨ζ', hζ'dom⟩
  have hV'V : V' ≤ V := Scheme.Opens.ι_image_le _ _
  have hV'W : Set.range (G.homOfLE hV'V ≫ ι₀).base ⊆ (W : Set P) := by
    rintro _ ⟨x, rfl⟩
    change ι₀.base ((G.homOfLE hV'V).base x) ∈ (W : Set P)
    have hx : ((G.homOfLE hV'V).base x).1 ∈ (V' : Set G) := by
      rw [Scheme.homOfLE_apply]; exact x.2
    have : (G.homOfLE hV'V).base x ∈ ι₀ ⁻¹ᵁ W := (Scheme.Opens.mem_ι_image_iff V).mp hx
    exact this
  have hι'ι₀ : ι' ≫ ν ≫ β = G.homOfLE hV'V ≫ ι₀ := by
    rw [hι'π, ← Category.assoc]
    congr 1
    rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι]
    exact (Scheme.Hom.isoImage_inv_ι V.ι (ι₀ ⁻¹ᵁ W))
  haveI : IsSeparated p'' := inferInstance
  have hνw'' : ν.base w'' = α'.base ⟨ζ, hζU'⟩ :=
    GoodReductionJacobian.PartialAction.base_hom_eq_of_compatible_of_isIso_stalkMap k f L p V ι₀ hι₀ a hc w ζ hζdom
      hζcl p'' β hβ W U' hU' hζU' α' hα' ν V' hV'V hV'W ι' hι'ι₀ hι' a' hc' w' hπw' hisow' ζ' hζ'dom hζ'cl
  have hw''₁ : ringKrullDim (P'.presheaf.stalk w'') = 1 := by rw [hνdim, hνw'', hα'ζ]
  have hsweep : closure (a'.hom.base '' ((a'.dom.ι ≫ pullback.snd f ((ν ≫ β) ≫ p)).base ⁻¹' closure {w'})) =
      closure {w''} :=
    GoodReductionJacobian.PartialAction.closure_image_preimage_closure_eq_closure_singleton a' {w'} ζ' hζ'dom hζ'cl
  haveI : LocallyOfFiniteType ((ν ≫ β) ≫ p) := inferInstance
  have hdimP' : topologicalKrullDim ↥P' = topologicalKrullDim ↥G := by
    have h1 := AlgebraicGeometry.topologicalKrullDim_eq_of_iso_opens ((ν ≫ β) ≫ p) p ((ν ≫ β) ⁻¹ᵁ W) W
      (by obtain ⟨y, hy⟩ := hWne
          exact ⟨((inv ((ν ≫ β) ∣_ W)).base ⟨y, hy⟩).1, ((inv ((ν ≫ β) ∣_ W)).base ⟨y, hy⟩).2⟩)
      (asIso ((ν ≫ β) ∣_ W))
    haveI : IsIntegral G := isIntegral_of_geometricallyIrreducible_of_smooth f
    have h2 := AlgebraicGeometry.topologicalKrullDim_eq_of_iso_opens f p V ι₀.opensRange
      ((Scheme.Opens.nonempty_iff _).mp inferInstance) ι₀.isoOpensRange
    exact h1.trans h2.symm
  exact ⟨V', ι', hι', a', w', w'', hP'i, hP'n, inferInstance, hdimP', inferInstance, inferInstance, hc', hm', hcod',
    hπw', hw'₁, hw''₁, hsweep⟩

end S_GoodReductionJacobian_PartialAction_exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one
end P2MW
export P2MW.S_GoodReductionJacobian_PartialAction_exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one (solution)
