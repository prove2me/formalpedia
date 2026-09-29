-- Prove2me | solution 1 for ModularCurve.exists_integralPoints_through_of_torsion_over_p
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9729d271-4d9c-584a-9939-eb6e70ea2b71

import Mathlib
import Definitions.Def_ModularCurve_JZeroToricTorsion
import Definitions.Def_ModularCurve_JZeroNeronDataPrime
import Definitions.Def_ModularCurve_JZeroNeronData
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Theorems.Thm_ModularCurve_smul_mem_jZeroToricTorsion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_integralPoints_through_of_torsion_over_p
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀"
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve

namespace PointSupply

section Helpers

universe u

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
  (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem comp_schemeNsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    x.1 ≫ L.schemeNsmul n = (L.nsmul t n x).1 := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  have e := congrArg Subtype.val (L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint)
  rw [hx] at e
  exact e

theorem eq_one_of_mul_self (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t f) (h : L.mul t a a = a) :
    a = L.one t := by
  calc a = L.mul t (L.one t) a := (L.one_mul t a).symm
    _ = L.mul t (L.mul t (L.inv t a) a) a := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t a) (L.mul t a a) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t a) a := by rw [h]
    _ = L.one t := L.inv_mul_cancel t a

theorem one_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t t' : T ⟶ Spec (CommRingCat.of R)} (he : t = t') : (L.one t).1 = (L.one t').1 := by
  subst he; rfl

theorem mul_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t t' : T ⟶ Spec (CommRingCat.of R)} (he : t = t')
    (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t' x' y').1 := by
  subst he
  obtain rfl : x = x' := Subtype.ext hx
  obtain rfl : y = y' := Subtype.ext hy
  rfl

theorem eq_of_isSeparated_of_generic_eq {K : Type u} [Field K] (O : ValuationSubring K)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] (σ : Spec (CommRingCat.of ↥O) ⟶ Y)
    (x y : SchemeHomOver σ f)
    (h : Spec.map (CommRingCat.ofHom O.subtype) ≫ x.1 = Spec.map (CommRingCat.ofHom O.subtype) ≫ y.1) :
    x = y := by
  let S : ValuativeCommSq f :=
    ValuativeCommSq.mk (↥O) K (Spec.map (CommRingCat.ofHom O.subtype) ≫ x.1) σ
      ⟨by rw [Category.assoc, x.2]; rfl⟩
  have hU : ValuativeCriterion.Uniqueness f := IsSeparated.valuativeCriterion f
  have hsub : Subsingleton S.commSq.LiftStruct := hU S
  let l₁ : S.commSq.LiftStruct := ⟨x.1, rfl, x.2⟩
  let l₂ : S.commSq.LiftStruct := ⟨y.1, h.symm, y.2⟩
  haveI := hsub
  have e : l₁ = l₂ := Subsingleton.elim l₁ l₂
  exact Subtype.ext (congrArg CommSq.LiftStruct.l e)

theorem baseChangePointToBase_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ) (x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f)) :
    RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).nsmul t' n x) =
      L.nsmul _ n (RelativeGroupLaw.baseChangePointToBase ι x) := by
  induction n with
  | zero => exact RelativeGroupLaw.baseChangePointToBase_one ι L t'
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.baseChangePointToBase_mul, ih]

theorem schemeNsmul_baseChange_fst (L : RelativeGroupLaw R f) (n : ℕ) :
    (L.baseChange ι).schemeNsmul n ≫ pullback.fst f ι = pullback.fst f ι ≫ L.schemeNsmul n := by
  have h1 : (L.baseChange ι).schemeNsmul n ≫ pullback.fst f ι =
      (RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).nsmul _ n RelativeGroupLaw.idPoint)).1 := rfl
  rw [h1, baseChangePointToBase_nsmul, ← comp_schemeNsmul]
  rfl

theorem schemeNsmul_baseChange_eq_map (L : RelativeGroupLaw R f) (n : ℕ) :
    (L.baseChange ι).schemeNsmul n =
      pullback.map f ι f ι (L.schemeNsmul n) (𝟙 _) (𝟙 _)
        ((Category.comp_id _).trans (L.schemeNsmul_over n).symm) ((Category.comp_id _).trans rfl) := by
  apply pullback.hom_ext
  · rw [schemeNsmul_baseChange_fst, pullback.lift_fst]
  · rw [pullback.lift_snd, Category.comp_id]
    exact (L.baseChange ι).schemeNsmul_over n

end Helpers

theorem isUnit_natCast_of_liesOverPrime {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) (k : ℕ) (hk : ¬ p ∣ k) : IsUnit (k : ↥A) := by
  by_contra hku
  have hcop : IsCoprime (k : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_comm).1 ((hp.coprime_iff_not_dvd).2 hk))
  obtain ⟨a, b, hab⟩ := hcop
  have hkm : (k : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := hku
  have hpm : (p : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    have h : ((p : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits := by first | exact hA | simpa [ValuationSubring.LiesOverPrime] using hA
    exact (A.coe_mem_nonunits_iff).1 h
  have h1 : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    have := Ideal.add_mem _ (Ideal.mul_mem_left _ (a : ↥A) hkm) (Ideal.mul_mem_left _ (b : ↥A) hpm)
    have e : ((a : ℤ) : ↥A) * (k : ↥A) + ((b : ℤ) : ↥A) * (p : ↥A) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ↥A) hab |>.trans Int.cast_one
    rwa [e] at this
  exact (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top ((Ideal.eq_top_iff_one _).2 h1)

end PointSupply

open PointSupply

set_option maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [IsSeparated g] [LocallyOfFiniteType g]
    (L : RelativeGroupLaw ℤ g) (hcomm : L.IsCommutative)
    (hflat : ∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n))
    (hlfp : ∀ n : ℕ, 0 < n → LocallyOfFinitePresentation (L.schemeNsmul n))
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) g)
    (pts_add : ∀ x y : JZero p, pts (x + y) = L.mul _ (pts x) (pts y))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

    (hvi : ∀ m : ℕ, ¬ p ∣ m →
      {x : JZero p | x ∈ jZeroTorsion p m ∧
          ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g,
            (pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1}
        = (jZeroToricTorsion p A m : Set (JZero p)))

    (hptors : ∀ ζ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ G,
      ζ ≫ g = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap ℤ ↥A))) →
      ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧
        ζ ≫ L.schemeNsmul m = ζ ≫ g ≫ (L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1)
    (t : HeckeAlg)
    (ζ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ G)
    (hζ : ζ ≫ g = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap ℤ ↥A)))) :
    letI := heckeModuleBar p
    ∃ (x : JZero p) (s e : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g),
      s.1.base (IsLocalRing.closedPoint ↥A) =
        ζ.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) ∧
      (pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 ∧
      (pts (t • x)).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ e.1 := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨m, hm0, hpm, hζm⟩ := hptors ζ hζ

  have h1 : pts 0 = L.one _ :=
    eq_one_of_mul_self L _ _ (by have e := pts_add 0 0; rw [add_zero] at e; exact e.symm)
  have hpow : ∀ (c : ℕ) (z : JZero p), pts (c • z) = L.nsmul _ c (pts z) := by
    intro c z
    induction c with
    | zero => rw [zero_nsmul, RelativeGroupLaw.nsmul_zero]; exact h1
    | succ c ih => rw [succ_nsmul, pts_add, ih, RelativeGroupLaw.nsmul_succ]
  have hjι : (Spec.map (CommRingCat.ofHom A.subtype)) ≫ (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) := by
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1

  have hres : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap ℤ ↥A))) =
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hζ' : ζ ≫ g = (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) := by rw [hζ, hres]

  let L' := L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))
  have hmap := schemeNsmul_baseChange_eq_map (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) L m
  haveI : Flat (L'.schemeNsmul m) := by
    haveI := hflat m hm0
    rw [show L'.schemeNsmul m = _ from hmap]
    exact MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance
      (L.schemeNsmul_over m).symm (Category.id_comp _).symm
  haveI : LocallyOfFinitePresentation (L'.schemeNsmul m) := by
    haveI := hlfp m hm0
    rw [show L'.schemeNsmul m = _ from hmap]
    exact MorphismProperty.pullbackMap (P := @LocallyOfFinitePresentation) inferInstance inferInstance
      (L.schemeNsmul_over m).symm (Category.id_comp _).symm
  haveI : FormallyUnramified (L'.schemeNsmul m) :=
    RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing L'
      (fun t x y => (RelativeGroupLaw.IsCommutative.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) hcomm) t x y) m
      (isUnit_natCast_of_liesOverPrime hp A hA m hpm)

  let u : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g) := L'.one (𝟙 _)
  let fY := pullback.snd (L'.schemeNsmul m) u.1
  haveI : Flat fY := MorphismProperty.pullback_snd (P := @Flat) _ _ inferInstance
  haveI : FormallyUnramified fY := MorphismProperty.pullback_snd (P := @FormallyUnramified) _ _ inferInstance
  haveI : LocallyOfFinitePresentation fY :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  haveI : AlgebraicGeometry.Etale fY := Etale.of_formallyUnramified_of_flat (f := fY)

  have hu2 : u.1 ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) = 𝟙 _ := u.2
  have hu1 : u.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) = (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) ≫ (L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by
    have e1 : u.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) =
        (RelativeGroupLaw.baseChangePointToBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) (L'.one (𝟙 _))).1 := rfl
    have e2 : RelativeGroupLaw.baseChangePointToBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) (L'.one (𝟙 _)) = L.one (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))) :=
      RelativeGroupLaw.baseChangePointToBase_one (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) L (𝟙 _)
    have e3 : (L.one (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))))).1 = (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) ≫ (L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 :=
      (congrArg Subtype.val (L.one_natural (𝟙 _) (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))) (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))
        ((Category.comp_id _).trans (Category.id_comp _).symm))).symm
    rw [e1, e2, e3]
  have hfst : L'.schemeNsmul m ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) ≫ L.schemeNsmul m :=
    schemeNsmul_baseChange_fst (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) L m
  have hsnd : L'.schemeNsmul m ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) = pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) := L'.schemeNsmul_over m

  obtain ⟨ζA, hζA1, hζA2⟩ : ∃ ζA : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))),
      ζA ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) = ζ ∧ ζA ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) = (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) :=
    ⟨pullback.lift ζ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) hζ', pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hζAm : ζA ≫ L'.schemeNsmul m = (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) ≫ u.1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, hfst, ← Category.assoc, hζA1, hζm, Category.assoc, hu1, ← Category.assoc ζ g,
        hζ', Category.assoc]
    · rw [Category.assoc, hsnd, hζA2, Category.assoc, hu2, Category.comp_id]
  obtain ⟨ζY, hζY1, hζY2⟩ : ∃ ζY : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶
      pullback (L'.schemeNsmul m) u.1,
      ζY ≫ pullback.fst (L'.schemeNsmul m) u.1 = ζA ∧ ζY ≫ pullback.snd (L'.schemeNsmul m) u.1 = (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) :=
    ⟨pullback.lift ζA (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) hζAm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue ↥A)).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue ↥A))
  have hρpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) =
      IsLocalRing.closedPoint ↥A := Spec_closedPoint
  have hy₀ : fY.base (ζY.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A))) =
      IsLocalRing.closedPoint ↥A := by
    show (ζY ≫ pullback.snd (L'.schemeNsmul m) u.1).base _ = _
    rw [hζY2]
    exact hρpt

  haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨sec, hsec, hsecy⟩ :=
    AlgebraicGeometry.exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing fY _ hy₀

  have hover : (sec ≫ pullback.fst (L'.schemeNsmul m) u.1) ≫ (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g) = 𝟙 _ := by
    calc (sec ≫ pullback.fst (L'.schemeNsmul m) u.1) ≫ (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g)
        = sec ≫ pullback.fst (L'.schemeNsmul m) u.1 ≫ (L'.schemeNsmul m ≫ (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g)) := by
          rw [L'.schemeNsmul_over m, Category.assoc]
      _ = sec ≫ (pullback.fst (L'.schemeNsmul m) u.1 ≫ L'.schemeNsmul m) ≫ (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g) := by
          simp only [Category.assoc]
      _ = sec ≫ (pullback.snd (L'.schemeNsmul m) u.1 ≫ u.1) ≫ (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g) := by rw [pullback.condition]
      _ = (sec ≫ pullback.snd (L'.schemeNsmul m) u.1) ≫ (u.1 ≫ (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g)) := by simp only [Category.assoc]
      _ = 𝟙 _ := by rw [hsec, u.2, Category.id_comp]
  let tpt : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g) := ⟨sec ≫ pullback.fst (L'.schemeNsmul m) u.1, hover⟩
  have hnt : L'.nsmul (𝟙 _) m tpt = u := by
    apply Subtype.ext
    rw [← comp_schemeNsmul]
    show (sec ≫ pullback.fst (L'.schemeNsmul m) u.1) ≫ L'.schemeNsmul m = u.1
    rw [Category.assoc, pullback.condition, ← Category.assoc, hsec, Category.id_comp]
  let tA := RelativeGroupLaw.baseChangePointToBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) tpt
  have hnt' : L.nsmul _ m tA = L.one _ := by
    rw [← baseChangePointToBase_nsmul, hnt]
    exact RelativeGroupLaw.baseChangePointToBase_one (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) L (𝟙 _)

  let s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g := ⟨tA.1, tA.2.trans (Category.id_comp _)⟩
  let x : JZero p := pts.symm (schemeHomOverComp (Spec.map (CommRingCat.ofHom A.subtype)) hjι tA)
  have hptsx : pts x = schemeHomOverComp (Spec.map (CommRingCat.ofHom A.subtype)) hjι tA := Equiv.apply_symm_apply _ _
  have hxs : (pts x).1 = (Spec.map (CommRingCat.ofHom A.subtype)) ≫ s.1 := by rw [hptsx]; rfl

  have hmx : m • x = 0 := by
    apply pts.injective
    rw [hpow, hptsx, ← L.nsmul_natural, hnt', h1]
    exact L.one_natural _ _ _ _
  have hxm : x ∈ jZeroTorsion p m :=
    (Submodule.mem_torsionBy_iff (R := ℤ) _ _).2 (by rw [natCast_zsmul]; exact hmx)

  have hxT : x ∈ (jZeroToricTorsion p A m : Set (JZero p)) := by
    rw [← hvi m hpm]; exact ⟨hxm, s, hxs⟩
  have htxT := ModularCurve.smul_mem_jZeroToricTorsion p A m t hxT
  have htx' : _ ∈ (jZeroToricTorsion p A m : Set (JZero p)) := htxT
  rw [← hvi m hpm] at htx'
  obtain ⟨-, e, he⟩ := htx'
  refine ⟨x, s, e, ?_, hxs, he⟩

  have e3 : ζY ≫ pullback.fst (L'.schemeNsmul m) u.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) = ζ := by
    rw [← Category.assoc, hζY1, hζA1]
  calc s.1.base (IsLocalRing.closedPoint ↥A)
      = (pullback.fst (L'.schemeNsmul m) u.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))).base
          (sec.base (IsLocalRing.closedPoint ↥A)) := rfl
    _ = (pullback.fst (L'.schemeNsmul m) u.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))).base
          (ζY.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A))) := by rw [hsecy]
    _ = (ζY ≫ pullback.fst (L'.schemeNsmul m) u.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))).base
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) := rfl
    _ = ζ.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) := by rw [e3]

end S_ModularCurve_exists_integralPoints_through_of_torsion_over_p
end P2MW
export P2MW.S_ModularCurve_exists_integralPoints_through_of_torsion_over_p (solution)
