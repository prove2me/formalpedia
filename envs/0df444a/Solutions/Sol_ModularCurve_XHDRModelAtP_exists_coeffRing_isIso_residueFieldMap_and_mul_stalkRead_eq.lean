-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c41db449-6aab-5f25-90a2-cd4dd21e68ad

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_AlgebraicGeometry_isIso_residueFieldMap_of_comp_eq_fromSpecResidueField
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_exists_sum_smul_coeffEmb_mul_eq_of_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_coeffEmb_mul_stalkRead_eq_stalkRead_of_point
import Theorems.Thm_ModularCurve_exists_coeffRing_forall_exists_mul_eq_and_forall_mem_range_residue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA MvPolynomial.CrossingQuotient.Resolution.instIsAffineXSchemeOpenCover MvPolynomial.CrossingQuotient.isOpenImmersion_overlapToChartRight MvPolynomial.CrossingQuotient.isOpenImmersion_torusToOverlap MvPolynomial.CrossingQuotient.isLocallyDirected_glueDiagram MvPolynomial.CrossingQuotient.GlueIndex.instPreorder MvPolynomial.CrossingQuotient.isOpenImmersion_torusToChart MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ιTorus MvPolynomial.CrossingQuotient.isOpenImmersion_glueMap MvPolynomial.CrossingQuotient.GlueIndex.instLE MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ιOverlap MvPolynomial.CrossingQuotient.isLocalization_away_torusRing MvPolynomial.CrossingQuotient.isOpenImmersion_glueDiagram_map MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ι"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ MvPolynomial.CrossingQuotient.GlueIndex.chart_le_overlap MvPolynomial.CrossingQuotient.GlueIndex.torus.sizeOf_spec MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_torus MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_chart MvPolynomial.CrossingQuotient.GlueIndex.overlap.sizeOf_spec MvPolynomial.CrossingQuotient.Resolution.ι_toSpec MvPolynomial.CrossingQuotient.Resolution.ι_toCrossing_assoc MvPolynomial.CrossingQuotient.glueMap_torus_overlap MvPolynomial.CrossingQuotient.GlueIndex.chart_le_torus MvPolynomial.CrossingQuotient.glueMap_overlap_overlap MvPolynomial.CrossingQuotient.GlueIndex.torus_le MvPolynomial.CrossingQuotient.Resolution.openCover_f MvPolynomial.CrossingQuotient.Resolution.ι_toCrossing MvPolynomial.CrossingQuotient.glueMap_torus_chart MvPolynomial.CrossingQuotient.glueMap_torus_torus MvPolynomial.CrossingQuotient.glueDiagram_obj MvPolynomial.CrossingQuotient.GlueIndex.chart.injEq MvPolynomial.CrossingQuotient.GlueIndex.chart_le_chart MvPolynomial.CrossingQuotient.GlueIndex.chart.sizeOf_spec MvPolynomial.CrossingQuotient.Resolution.openCover_X MvPolynomial.CrossingQuotient.Resolution.openCover_I₀ MvPolynomial.CrossingQuotient.GlueIndex.overlap.injEq"
p2m_attr_erase "simp" "MvPolynomial.CrossingQuotient.glueMap_chart_chart MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_overlap MvPolynomial.CrossingQuotient.Resolution.ι_toSpec_assoc MvPolynomial.CrossingQuotient.lift_V MvPolynomial.CrossingQuotient.lift_U MvPolynomial.CrossingQuotient.monomial_neg_natCast MvPolynomial.CrossingQuotient.monomial_zero MvPolynomial.CrossingQuotient.monomial_natCast MvPolynomial.CrossingQuotient.powMap_mk_X AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace H1R

theorem ext_of_specMap_comp_eq {k' K : Type} [Field k'] [Field K] {S : Scheme.{0}}
    (ι : CommRingCat.of k' ⟶ CommRingCat.of K) (hι : Function.Injective ι.hom)
    (m₁ m₂ : Spec (CommRingCat.of k') ⟶ S) (h : Spec.map ι ≫ m₁ = Spec.map ι ≫ m₂) : m₁ = m₂ := by
  haveI : Mono ι := ConcreteCategory.mono_of_injective ι hι
  have e₁ := (Scheme.SpecToEquivOfField k' S).symm_apply_apply m₁
  have e₂ := (Scheme.SpecToEquivOfField k' S).symm_apply_apply m₂

  have key : (Scheme.SpecToEquivOfField K S).symm ⟨(Scheme.SpecToEquivOfField k' S m₁).1, (Scheme.SpecToEquivOfField k' S m₁).2 ≫ ι⟩ =
      (Scheme.SpecToEquivOfField K S).symm ⟨(Scheme.SpecToEquivOfField k' S m₂).1, (Scheme.SpecToEquivOfField k' S m₂).2 ≫ ι⟩ := by
    simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk, Spec.map_comp, Category.assoc]
    simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at e₁ e₂
    rw [e₁, e₂, h]
  have key2 := (Scheme.SpecToEquivOfField K S).symm.injective key
  rw [Scheme.SpecToEquivOfField_eq_iff] at key2
  obtain ⟨e, he⟩ := key2
  simp only at e he
  rw [← Category.assoc, cancel_mono] at he
  rw [← e₁, ← e₂]
  congr 1
  rw [Scheme.SpecToEquivOfField_eq_iff]
  exact ⟨e, he⟩

theorem isIso_residueFieldMap_snd_lift_of_fieldRange_le
    {X S S' : Scheme.{0}} (f : X ⟶ S) (g : S' ⟶ S) {K : Type} [Field K]
    (v : Spec (CommRingCat.of K) ⟶ X) (w : Spec (CommRingCat.of K) ⟶ S') (h : v ≫ f = w ≫ g)
    (hk : (Scheme.SpecToEquivOfField K X v).2.hom.fieldRange ≤ (Scheme.SpecToEquivOfField K S' w).2.hom.fieldRange) :
    IsIso ((pullback.snd f g).residueFieldMap ((pullback.lift v w h).base (closedPoint K))) := by
  classical
  set x := v.base (closedPoint K) with hx
  set s' := w.base (closedPoint K) with hs'
  set ev : X.residueField x ⟶ CommRingCat.of K := (Scheme.SpecToEquivOfField K X v).2 with hev
  set ew : S'.residueField s' ⟶ CommRingCat.of K := (Scheme.SpecToEquivOfField K S' w).2 with hew
  have hv : Spec.map ev ≫ X.fromSpecResidueField x = v := (Scheme.SpecToEquivOfField K X).symm_apply_apply v
  have hw : Spec.map ew ≫ S'.fromSpecResidueField s' = w := (Scheme.SpecToEquivOfField K S').symm_apply_apply w
  have hewinj : Function.Injective ew.hom := ew.hom.injective

  have hfac : ∀ t : X.residueField x, ∃! u : S'.residueField s', ew.hom u = ev.hom t := by
    intro t
    obtain ⟨u, hu⟩ : ev.hom t ∈ ew.hom.fieldRange := hk ⟨t, rfl⟩
    exact ⟨u, hu, fun u' hu' => hewinj (hu'.trans hu.symm)⟩
  choose g₀f hg₀f _hg₀u using hfac
  let g₀ : X.residueField x →+* S'.residueField s' :=
    { toFun := g₀f
      map_one' := hewinj (by rw [hg₀f, map_one, map_one])
      map_mul' := fun a b => hewinj (by rw [hg₀f, map_mul, map_mul, hg₀f, hg₀f])
      map_zero' := hewinj (by rw [hg₀f, map_zero, map_zero])
      map_add' := fun a b => hewinj (by rw [hg₀f, map_add, map_add, hg₀f, hg₀f]) }
  have hg₀ : CommRingCat.ofHom g₀ ≫ ew = ev := by
    ext t; exact hg₀f t

  let a : Spec (S'.residueField s') ⟶ X := Spec.map (CommRingCat.ofHom g₀) ≫ X.fromSpecResidueField x
  have ha : Spec.map ew ≫ a = v := by
    simp only [a, ← Category.assoc, ← Spec.map_comp]
    erw [hg₀]
    exact hv
  have hcompat : a ≫ f = S'.fromSpecResidueField s' ≫ g := by
    refine ext_of_specMap_comp_eq (k' := S'.residueField s') (K := K) ew hewinj _ _ ?_
    rw [← Category.assoc, ha, h, ← Category.assoc, hw]

  let u₀ : Spec (S'.residueField s') ⟶ pullback f g := pullback.lift a (S'.fromSpecResidueField s') hcompat
  have hu₀ : u₀ ≫ pullback.snd f g = S'.fromSpecResidueField s' := pullback.lift_snd _ _ _
  have H := AlgebraicGeometry.isIso_residueFieldMap_of_comp_eq_fromSpecResidueField (pullback.snd f g) s' u₀ hu₀

  have hz : pullback.lift v w h = Spec.map ew ≫ u₀ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ha]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, hw]
  have hpt : (pullback.lift v w h).base (closedPoint K) = u₀.base (closedPoint (S'.residueField s')) := by
    rw [hz, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  have : ∀ q, q = u₀.base (closedPoint (S'.residueField s')) → IsIso ((pullback.snd f g).residueFieldMap q) := by
    rintro q rfl; exact H
  exact this _ hpt

theorem range_subset_fieldRange_specMap {O' κ : Type} [CommRing O'] [Field κ] (toκ' : O' →+* κ) :
    Set.range toκ' ⊆ ((Scheme.SpecToEquivOfField κ (Spec (CommRingCat.of O')) (Spec.map (CommRingCat.ofHom toκ'))).2).hom.fieldRange := by
  classical
  have hw := (Scheme.SpecToEquivOfField κ (Spec (CommRingCat.of O'))).symm_apply_apply (Spec.map (CommRingCat.ofHom toκ'))
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk] at hw ⊢
  have hfrom := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (CommRingCat.of O')
    ((Spec.map (CommRingCat.ofHom toκ')).base (closedPoint κ))
  rw [← hfrom, ← Spec.map_comp] at hw
  erw [← Spec.map_comp] at hw
  have hring := Spec.map_injective hw
  rintro _ ⟨o, rfl⟩
  refine ⟨((CommRingCat.ofHom (algebraMap O' _)) ≫ (Scheme.Spec.residueFieldIso (CommRingCat.of O') _).inv).hom o, ?_⟩
  have := congrArg (fun φ => φ.hom o) hring
  first | exact this | simpa using this | simpa +zetaDelta using this

theorem isIso_residueFieldMap_toBase_of_fieldRange_subset
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (ρO' : R p →+* O')
    (ιA' : O' →+* ↥A) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA') (hιA'ρ : ιA'.comp ρO' = ρ)
    (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp ρO' = (IsLocalRing.residue ↥A).comp ρ)
    (hk : ∀ ξ : ResidueField ↥A,
      ξ ∈ (Scheme.SpecToEquivOfField (ResidueField ↥A) (XHDRLevel.X p (ΓM M H) hj) (uκ ≫ pullback.fst _ _)).2.hom.fieldRange →
      ξ ∈ Set.range ((IsLocalRing.residue ↥A).comp ιA')) :
    IsIso ((XO.toBase (ΓM M H) hj ρO').residueFieldMap
      ((bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ').base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))))) := by
  classical

  have hvw : (uκ ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ιA')) ≫ Spec.map (CommRingCat.ofHom ρO') := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, huκ₂, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, htoκ']
  have hlift : uκ ≫ bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ' =
      pullback.lift (uκ ≫ pullback.fst _ _) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ιA'))) hvw := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, XHDRLevel.bcMap_fst]
    · rw [pullback.lift_snd, Category.assoc, XHDRLevel.bcMap_snd, ← Category.assoc, huκ₂, Category.id_comp]
  have hpt : (bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ').base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) =
      (pullback.lift (uκ ≫ pullback.fst _ _) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ιA'))) hvw).base
        (IsLocalRing.closedPoint (ResidueField ↥A)) := by
    rw [← hlift]; rfl
  have H := H1R.isIso_residueFieldMap_snd_lift_of_fieldRange_le (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO'))
    (uκ ≫ pullback.fst _ _) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ιA'))) hvw
    (fun ξ hξ => range_subset_fieldRange_specMap ((IsLocalRing.residue ↥A).comp ιA') (hk ξ hξ))
  rw [hpt]
  exact H

end H1R

namespace H1R

theorem ringHom_ext_R {p : ℕ} [Fact p.Prime] {T : Type*} [CommRing T] (f g : R p →+* T) : f = g := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

theorem T_mem_ΓM (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ ΓM M H := by
  rw [XHDRLevel.ΓM, CohCarrier.mem_GammaH_iff]
  have hT0 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  refine ⟨hT0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨ModularGroup.T, hT0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    simp [CongruenceSubgroup.Gamma0Map, ModularGroup.T]
  rw [this]; exact one_mem H

theorem finite_fieldRange_of_residueField_hom
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (IsLocalRing.ResidueField ↥A) p]
    (xb : ↥(XHDRLevel.X p (ΓM M H) hj)) (e : (XHDRLevel.X p (ΓM M H) hj).residueField xb ⟶ CommRingCat.of (ResidueField ↥A)) :
    Finite ↥(e.hom.fieldRange) := by
  classical
  have hT := T_mem_ΓM M H
  haveI := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI : IsNoetherianRing (R p) := inferInstance
  have heinj : Function.Injective e.hom := e.hom.injective

  letI algSt : Algebra (R p) ((XHDRLevel.X p (ΓM M H) hj).presheaf.stalk xb) :=
    RingHom.toAlgebra ((((XHDRLevel.X p (ΓM M H) hj).presheaf.germ ⊤ xb trivial).hom.comp
      (((toBase p (ΓM M H) hj).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (R p))).inv.hom)))
  obtain ⟨hFT, hFT'⟩ := ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p (ΓM M H) hT
    (jAt (ΓM M H) hj) (coe_jAt _ _)
  have hinjR : Function.Injective (algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by
    rw [IsScalarTower.algebraMap_eq (R p) ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H))]
    exact (algebraMap ℚ _).injective.comp Subtype.val_injective
  obtain ⟨-, hess, -, -⟩ := AlgebraicCurve.TwoChartIntegralModel.isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
    (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) hinjR (jAt (ΓM M H) hj) hFT hFT' xb (fun _ => rfl)

  letI algKZ : Algebra (R p) ↑((XHDRLevel.X p (ΓM M H) hj).residueField xb) :=
    @Ideal.Quotient.algebra (R p) _ _ _ algSt (maximalIdeal _) _
  haveI : Algebra.EssFiniteType (R p) ↑((XHDRLevel.X p (ΓM M H) hj).residueField xb) :=
    @Algebra.instEssFiniteTypeQuotientIdeal (R p) _ _ _ algSt hess (maximalIdeal _)
  haveI hchar : CharP ↑((XHDRLevel.X p (ΓM M H) hj).residueField xb) p := (RingHom.charP_iff e.hom heinj p).mpr inferInstance
  letI algZ : Algebra (ZMod p) ↑((XHDRLevel.X p (ΓM M H) hj).residueField xb) := ZMod.algebra _ p
  haveI : IsScalarTower (R p) (ZMod p) ↑((XHDRLevel.X p (ΓM M H) hj).residueField xb) :=
    IsScalarTower.of_algebraMap_eq (fun r => RingHom.congr_fun
      (ringHom_ext_R (algebraMap (R p) _) ((algebraMap (ZMod p) ↑((XHDRLevel.X p (ΓM M H) hj).residueField xb)).comp (algebraMap (R p) (ZMod p)))) r)
  haveI : Algebra.EssFiniteType (ZMod p) ↑((XHDRLevel.X p (ΓM M H) hj).residueField xb) := Algebra.EssFiniteType.of_comp (R p) _ _

  letI algκ : Algebra (ZMod p) (ResidueField ↥A) := ZMod.algebra _ p
  haveI : Algebra.IsAlgebraic (ZMod p) (ResidueField ↥A) :=
    ValuationSubring.algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat (AlgebraicClosure ℚ) A p
  let e' : ↑((XHDRLevel.X p (ΓM M H) hj).residueField xb) →ₐ[ZMod p] ResidueField ↥A :=
    { e.hom with commutes' := fun r => RingHom.congr_fun (RingHom.ext_zmod (e.hom.comp (algebraMap (ZMod p) _)) (algebraMap (ZMod p) _)) r }
  haveI : Algebra.IsAlgebraic (ZMod p) ↑((XHDRLevel.X p (ΓM M H) hj).residueField xb) := Algebra.IsAlgebraic.of_injective e' heinj
  haveI : Module.Finite (ZMod p) ↑((XHDRLevel.X p (ΓM M H) hj).residueField xb) := Algebra.finite_of_essFiniteType_of_isAlgebraic
  haveI hfin : Finite ↑((XHDRLevel.X p (ΓM M H) hj).residueField xb) := Module.finite_of_finite (ZMod p)
  exact Finite.of_surjective (fun y => (⟨e.hom y, ⟨y, rfl⟩⟩ : ↥(e.hom.fieldRange))) (fun ⟨x, y, hy⟩ => ⟨y, Subtype.ext hy⟩)

theorem finite_fieldRange_residue_of_section
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _) :
    Finite ↥((Scheme.SpecToEquivOfField (ResidueField ↥A) (XHDRLevel.X p (ΓM M H) hj)
      (uκ ≫ pullback.fst _ _)).2.hom.fieldRange) :=
  finite_fieldRange_of_residueField_hom p M H hj A _ _

end H1R

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    :
    ∀ f : ↥(xHFunctionFieldBar M H),
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (ρO' : R p →+* O')
        (ιA' : O' →+* ↥A) (_ : Function.Injective ιA') (_ : IsLocalHom ιA') (_ : ιA'.comp ρO' = ρ)
        (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp ρO' = algebraMap (R p) (AlgebraicClosure ℚ)) (_ : A.subtype.comp ιA' = jO')
        (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp ρO' = (IsLocalRing.residue ↥A).comp ρ),
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ' : XQ ⟶ XO (ΓM M H) hj ρO' :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI bc' := bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ'
    letI x' : ↥(XO (ΓM M H) hj ρO') := bc'.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    letI B := (XO (ΓM M H) hj ρO').presheaf.stalk x'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
      ∃ (hsp : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x'),
      letI emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp).hom))
      (XO.toBase (ΓM M H) hj ρO').base x' = IsLocalRing.closedPoint O' ∧
      IsIso ((XO.toBase (ΓM M H) hj ρO').residueFieldMap x') ∧
      ∃ r s₀ : ↥B, s₀ ≠ 0 ∧ f * emb s₀ = emb r := by
  intro f
  classical

  obtain ⟨ι, _iι, c, g, κι, _iκ, d, h, hden, hfrac⟩ :=
    ModularCurve.exists_sum_smul_coeffEmb_mul_eq_of_mem_laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (ΓM M H)) (f : LaurentSeries (AlgebraicClosure ℚ)) f.2

  let k₀ : Subfield (ResidueField ↥A) :=
    (Scheme.SpecToEquivOfField (ResidueField ↥A) (XHDRLevel.X p (ΓM M H) hj) (uκ ≫ pullback.fst _ _)).2.hom.fieldRange
  haveI _ik₀ : Finite ↥k₀ := H1R.finite_fieldRange_residue_of_section p M H hj A hA ρ hρ uκ huκ₂

  obtain ⟨O', _iCR, _iDom, _iDVR, ρO', ιA', hinj, hloc, hιA'ρ, jO', hjO', hιA'j, htoκ', hS, hk⟩ :=
    ModularCurve.exists_coeffRing_forall_exists_mul_eq_and_forall_mem_range_residue p A hA ρ hρ (Finset.univ.image c ∪ Finset.univ.image d) k₀
  have hsp : (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO']) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO').base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ ((bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ').base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) := by

    let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    let prJ' : XQ ⟶ XO (ΓM M H) hj ρO' :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    let x' : ↥(XO (ΓM M H) hj ρO') := (bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ').base
      (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    show prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x'
    haveI := 𝔛.eeta_iso
    haveI := 𝔛.flat
    have hjinj' : Function.Injective jO' := by
      rw [← hιA'j]; exact Subtype.coe_injective.comp hinj
    have hprJ₁ : prJ' ≫ pullback.fst _ _ = pullback.fst _ _ := by
      simp only [prJ', pullback.lift_fst, Category.comp_id]
    have hprJ₂ : prJ' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom jO') := by
      simp only [prJ', pullback.lift_snd]
    have hprPB : IsPullback prJ' (pullback.snd (toBase p (ΓM M H) hj) _) (XO.toBase (ΓM M H) hj ρO') (Spec.map (CommRingCat.ofHom jO')) := by
      have key : IsPullback (prJ' ≫ pullback.fst (toBase p (ΓM M H) hj) _)
          (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) (toBase p (ΓM M H) hj)
          (Spec.map (CommRingCat.ofHom jO') ≫ Spec.map (CommRingCat.ofHom ρO')) := by
        rw [hprJ₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO']; exact IsPullback.of_hasPullback _ _
      exact IsPullback.of_right key hprJ₂ (IsPullback.of_hasPullback _ _)
    have hflat : GeneralizingMap (XO.toBase (ΓM M H) hj ρO').base := Flat.generalizingMap _
    have hsp0 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O') ⤳ (XO.toBase (ΓM M H) hj ρO').base x' :=
      (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
    obtain ⟨x'', hx'', hx''b⟩ := hflat hsp0
    obtain ⟨ζ, hζ, -⟩ := Scheme.exists_preimage_of_isPullback hprPB x'' (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) (by
      rw [hx''b]
      apply PrimeSpectrum.ext
      show (⊥ : Ideal O') = Ideal.comap jO' (IsLocalRing.closedPoint (AlgebraicClosure ℚ)).asIdeal
      rw [show (IsLocalRing.closedPoint (AlgebraicClosure ℚ)).asIdeal = ⊥ from Ideal.eq_bot_of_prime _, ← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot jO').mp hjinj'])
    have h1 : genericPoint (𝔛.Meta).C ⤳ (inv 𝔛.eeta).base ζ := genericPoint_specializes _
    have h2 := h1.map (𝔛.eeta ≫ prJ').base.hom.continuous
    have h3 : (𝔛.eeta ≫ prJ').base ((inv 𝔛.eeta).base ζ) = x'' := by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc, hζ]
    rw [h3] at h2
    rw [← Scheme.Hom.comp_apply]
    exact h2.trans hx''
  refine ⟨O', _iCR, _iDom, _iDVR, ρO', ιA', hinj, hloc, hιA'ρ, jO', hjO', hιA'j, htoκ', hsp, ?_, ?_, ?_⟩
  ·
    have e1 : bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ' ≫ XO.toBase (ΓM M H) hj ρO' =
        pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ιA')) := by
      simp only [XO.toBase, bcMap_snd]
    show (XO.toBase (ΓM M H) hj ρO').base ((bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ').base
      (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) = _
    rw [← Scheme.Hom.comp_apply, e1, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (pullback.snd _ _), huκ₂]
    haveI : IsLocalHom (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ιA')).hom := by
      rw [CommRingCat.hom_ofHom]; haveI := hloc; exact RingHom.isLocalHom_comp _ _
    exact Spec_closedPoint
  ·
    exact H1R.isIso_residueFieldMap_toBase_of_fieldRange_subset p M H hj A hA ρ hρ uκ huκ₂ O' ρO' ιA' hinj hloc hιA'ρ htoκ' hk
  ·
    obtain ⟨hinjE, hconst, hgen⟩ := ModularCurve.XHDRModelAtP.exists_coeffEmb_mul_stalkRead_eq_stalkRead_of_point p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O' ρO' ιA' hinj hloc hιA'ρ jO' hjO' hιA'j htoκ' _ hsp

    let x' : ↥(XO (ΓM M H) hj ρO') := (bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ').base
      (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    let B := (XO (ΓM M H) hj ρO').presheaf.stalk x'
    let σB : O' →+* ↥B := ((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
    let emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
        (((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO']) :
          pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO').stalkMap
            (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
          ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp).hom))
    show ∃ r s₀ : ↥B, s₀ ≠ 0 ∧ f * emb s₀ = emb r
    change Function.Injective emb at hinjE
    change emb.comp σB = (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).comp jO' at hconst
    let P : ↥(xHFunctionFieldBar M H) → Prop := fun x => ∃ r s : ↥B, emb s ≠ 0 ∧ x * emb s = emb r
    have hP0 : P 0 := ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [map_zero, zero_mul]⟩
    have hPmul : ∀ x y, P x → P y → P (x * y) := by
      rintro x y ⟨r, s, hs, hx⟩ ⟨r', s', hs', hy⟩
      refine ⟨r * r', s * s', by rw [map_mul]; exact mul_ne_zero hs hs', ?_⟩
      rw [map_mul, map_mul]
      linear_combination (y * emb s') * hx + (emb r) * hy
    have hPadd : ∀ x y, P x → P y → P (x + y) := by
      rintro x y ⟨r, s, hs, hx⟩ ⟨r', s', hs', hy⟩
      refine ⟨r * s' + r' * s, s * s', by rw [map_mul]; exact mul_ne_zero hs hs', ?_⟩
      rw [map_mul, map_add, map_mul, map_mul]
      linear_combination (emb s') * hx + (emb s) * hy
    have hPsum : ∀ {α : Type} [Fintype α] (u : α → ↥(xHFunctionFieldBar M H)), (∀ a, P (u a)) → P (∑ a, u a) := by
      intro α _ u hu
      classical
      have key : ∀ t : Finset α, P (∑ a ∈ t, u a) := by
        intro t
        induction t using Finset.induction_on with
        | empty => simpa using hP0
        | insert a t ha ih => rw [Finset.sum_insert ha]; exact hPadd _ _ (hu a) ih
      exact key _
    have hPconst : ∀ cc : AlgebraicClosure ℚ, cc ∈ (Finset.univ.image c ∪ Finset.univ.image d) →
        P (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) cc) := by
      intro cc hcc
      obtain ⟨a, b, hb, hcab⟩ := hS cc hcc
      have hea : emb (σB a) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (jO' a) := RingHom.congr_fun hconst a
      have heb : emb (σB b) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (jO' b) := RingHom.congr_fun hconst b
      refine ⟨σB a, σB b, ?_, ?_⟩
      · rw [heb, map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).injective]
        exact hb
      · rw [heb, hea, ← map_mul, hcab]
    have hPemb : ∀ a : ↥(qExpFunctionFieldC ℚ (ΓM M H)),
        P ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (a : LaurentSeries ℚ), ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) a.2⟩ := by
      intro a
      obtain ⟨r, s, hs, h⟩ := hgen a
      exact ⟨r, s, (map_ne_zero_iff emb hinjE).mpr hs, h⟩

    let q : ↥(qExpFunctionFieldC ℚ (ΓM M H)) → ↥(xHFunctionFieldBar M H) := fun a =>
      ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (a : LaurentSeries ℚ), ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) a.2⟩
    let Df : ↥(xHFunctionFieldBar M H) := ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (d j) * q (h j)
    let Nf : ↥(xHFunctionFieldBar M H) := ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c i) * q (g i)
    have hval : ∀ x : ↥(xHFunctionFieldBar M H), (x : LaurentSeries (AlgebraicClosure ℚ)) = (xHFunctionFieldBar M H).val x := fun x => rfl
    have hDf : (Df : LaurentSeries (AlgebraicClosure ℚ)) = ∑ j, algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (d j) *
        ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((h j : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by
      rw [hval]; simp only [Df, q, map_sum, map_mul, AlgHom.commutes]; rfl
    have hNf : (Nf : LaurentSeries (AlgebraicClosure ℚ)) = ∑ i, algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c i) *
        ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((g i : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by
      rw [hval]; simp only [Nf, q, map_sum, map_mul, AlgHom.commutes]; rfl
    have hDne : Df ≠ 0 := fun h0 => hden (by rw [← hDf, h0]; rfl)
    have hgDf : f * Df = Nf := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, hDf, hNf]
      exact hfrac
    have hcmem : ∀ i, c i ∈ (Finset.univ.image c ∪ Finset.univ.image d) := fun i =>
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hdmem : ∀ j, d j ∈ (Finset.univ.image c ∪ Finset.univ.image d) := fun j =>
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    have hPD : P Df := hPsum _ (fun j => hPmul _ _ (hPconst _ (hdmem j)) (hPemb _))
    have hPN : P Nf := hPsum _ (fun i => hPmul _ _ (hPconst _ (hcmem i)) (hPemb _))
    obtain ⟨rD, sD, hsD, hxD⟩ := hPD
    obtain ⟨rN, sN, hsN, hxN⟩ := hPN
    have hrD : emb rD ≠ 0 := by rw [← hxD]; exact mul_ne_zero hDne hsD
    refine ⟨rN * sD, rD * sN, ?_, ?_⟩
    · intro h0; apply mul_ne_zero hrD hsN; rw [← map_mul, h0, map_zero]
    · rw [map_mul, map_mul]
      linear_combination (emb sD * emb sN) * hgDf - (f * emb sN) * hxD + (emb sD) * hxN

end S_ModularCurve_XHDRModelAtP_exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq (solution)
