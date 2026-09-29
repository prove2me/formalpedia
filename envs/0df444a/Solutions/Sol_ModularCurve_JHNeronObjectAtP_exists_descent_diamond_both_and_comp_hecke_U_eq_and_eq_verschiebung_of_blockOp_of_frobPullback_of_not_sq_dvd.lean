-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_descent_diamond_both_and_comp_hecke_U_eq_and_eq_verschiebung_of_blockOp_of_frobPullback_of_not_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/facaa5ef-8ac4-5be6-883c-358cda9e8f89

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_levelData_ptsSp_frobeniusPushforward_eq_schemeHomOverComp_frobenius_ptsSp_of_hsp
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap
import Theorems.Thm_ModularCurve_XHDRModelAtP_smul_frob_mem_ssPlacesQExp_and_frob_smul_frob_eq_of_mem_ssPlacesQExp
import Theorems.Thm_AlgebraicGeometry_ext_of_forall_geometricPoint_comp_eq_of_flat
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_GluedPic0_toPic0Pair_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_descent_diamond_both_and_comp_hecke_U_eq_and_eq_verschiebung_of_blockOp_of_frobPullback_of_not_sq_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

p2m_open "ModularCurve.XHDRLevel~ΓN"
open ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace R1AB48

section Points

variable {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂]
variable {σ : Spec (CommRingCat.of R₁) ⟶ Spec (CommRingCat.of R)}
variable {ι : Spec (CommRingCat.of R₂) ⟶ Spec (CommRingCat.of R₁)}
variable {s : Spec (CommRingCat.of R₂) ⟶ Spec (CommRingCat.of R)}

def liftPt (hfac : ι ≫ σ = s) {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver s g) : Spec (CommRingCat.of R₂) ⟶ pullback g σ :=
  pullback.lift P.1 ι (by rw [P.2, hfac])

@[scoped simp]
theorem liftPt_fst (hfac : ι ≫ σ = s) {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver s g) : liftPt hfac P ≫ pullback.fst g σ = P.1 :=
  pullback.lift_fst _ _ _

@[scoped simp]
theorem liftPt_snd (hfac : ι ≫ σ = s) {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver s g) : liftPt hfac P ≫ pullback.snd g σ = ι :=
  pullback.lift_snd _ _ _

def ofPt (hfac : ι ≫ σ = s) {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (x : Spec (CommRingCat.of R₂) ⟶ pullback g σ) (hx : x ≫ pullback.snd g σ = ι) : SchemeHomOver s g :=
  ⟨x ≫ pullback.fst g σ, by rw [Category.assoc, pullback.condition, ← Category.assoc, hx, hfac]⟩

@[scoped simp]
theorem ofPt_coe (hfac : ι ≫ σ = s) {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (x : Spec (CommRingCat.of R₂) ⟶ pullback g σ) (hx : x ≫ pullback.snd g σ = ι) :
    (ofPt hfac x hx).1 = x ≫ pullback.fst g σ := rfl

theorem liftPt_ofPt (hfac : ι ≫ σ = s) {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (x : Spec (CommRingCat.of R₂) ⟶ pullback g σ) (hx : x ≫ pullback.snd g σ = ι) :
    liftPt hfac (ofPt hfac x hx) = x := by
  apply pullback.hom_ext
  · rw [liftPt_fst, ofPt_coe]
  · rw [liftPt_snd, hx]

theorem liftPt_injective (hfac : ι ≫ σ = s) {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    {P P' : SchemeHomOver s g} (h : liftPt hfac P = liftPt hfac P') : P = P' := by
  apply Subtype.ext
  rw [← liftPt_fst hfac P, h, liftPt_fst]

def pushPt (hfac : ι ≫ σ = s) {G G' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    {g' : G' ⟶ Spec (CommRingCat.of R)}
    (E : SchemeHomOver (pullback.snd g σ) (pullback.snd g' σ)) (P : SchemeHomOver s g) : SchemeHomOver s g' :=
  ofPt hfac (liftPt hfac P ≫ E.1) (by rw [Category.assoc, E.2, liftPt_snd])

theorem pushPt_coe (hfac : ι ≫ σ = s) {G G' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    {g' : G' ⟶ Spec (CommRingCat.of R)}
    (E : SchemeHomOver (pullback.snd g σ) (pullback.snd g' σ)) (P : SchemeHomOver s g) :
    (pushPt hfac E P).1 = liftPt hfac P ≫ E.1 ≫ pullback.fst g' σ := by
  rw [pushPt, ofPt_coe, Category.assoc]

@[scoped simp]
theorem liftPt_pushPt (hfac : ι ≫ σ = s) {G G' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    {g' : G' ⟶ Spec (CommRingCat.of R)}
    (E : SchemeHomOver (pullback.snd g σ) (pullback.snd g' σ)) (P : SchemeHomOver s g) :
    liftPt hfac (pushPt hfac E P) = liftPt hfac P ≫ E.1 :=
  liftPt_ofPt _ _ _

theorem pushPt_comp (hfac : ι ≫ σ = s) {G G' G'' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    {g' : G' ⟶ Spec (CommRingCat.of R)} {g'' : G'' ⟶ Spec (CommRingCat.of R)}
    (E : SchemeHomOver (pullback.snd g σ) (pullback.snd g' σ))
    (E' : SchemeHomOver (pullback.snd g' σ) (pullback.snd g'' σ)) (P : SchemeHomOver s g) :
    pushPt hfac (NeronModelInfra.schemeHomOverComp E E') P = pushPt hfac E' (pushPt hfac E P) := by
  apply liftPt_injective hfac
  rw [liftPt_pushPt, liftPt_pushPt, liftPt_pushPt, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

theorem pushPt_eq_comp_of_fst (hfac : ι ≫ σ = s) {G G' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    {g' : G' ⟶ Spec (CommRingCat.of R)}
    (E : SchemeHomOver (pullback.snd g σ) (pullback.snd g' σ)) (h : SchemeHomOver g g')
    (hE : E.1 ≫ pullback.fst g' σ = pullback.fst g σ ≫ h.1) (P : SchemeHomOver s g) :
    pushPt hfac E P = NeronModelInfra.schemeHomOverComp P h := by
  apply Subtype.ext
  rw [pushPt_coe, hE, ← Category.assoc, liftPt_fst, NeronModelInfra.schemeHomOverComp_coe]

theorem pushPt_fibreRestrictAlong (hfac : ι ≫ σ = s) {G G' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    {g' : G' ⟶ Spec (CommRingCat.of R)} (h : SchemeHomOver g g') (P : SchemeHomOver s g) :
    pushPt hfac (NeronSpecialFibreInfra.fibreRestrictAlong σ g' g h) P = NeronModelInfra.schemeHomOverComp P h :=
  pushPt_eq_comp_of_fst hfac _ h (NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst σ g' g h) P

theorem toFibrePt_coe_comp_map (hfac : ι ≫ σ = s) {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver s g)
    (e₁ : g ≫ 𝟙 _ = 𝟙 _ ≫ g) (e₂ : s ≫ 𝟙 _ = ι ≫ σ) :
    (toFibrePt P).1 ≫ pullback.map g s g σ (𝟙 _) ι (𝟙 _) e₁ e₂ = liftPt hfac P := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, liftPt_fst]
    show (RelativeGroupLaw.baseChangePointOfBase s (overId P)).1 ≫ pullback.fst g s ≫ 𝟙 G = P.1
    rw [Category.comp_id, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
    rfl
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, liftPt_snd]
    show (RelativeGroupLaw.baseChangePointOfBase s (overId P)).1 ≫ pullback.snd g s ≫ ι = ι
    rw [RelativeGroupLaw.baseChangePointOfBase_coe, ← Category.assoc, pullback.lift_snd, Category.id_comp]

theorem fibreMap_coe {G G' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} {g' : G' ⟶ Spec (CommRingCat.of R)}
    (a : SchemeHomOver (RelativeGroupLaw.baseChangeStr s g) (RelativeGroupLaw.baseChangeStr s g'))
    (P : SchemeHomOver s g) :
    (fibreMap a P).1 = (toFibrePt P).1 ≫ a.1 ≫ pullback.fst g' s := by
  show (RelativeGroupLaw.baseChangePointToBase s (NeronModelInfra.schemeHomOverComp (toFibrePt P) a)).1 = _
  rw [RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

theorem pushPt_eq_fibreMap (hfac : ι ≫ σ = s) {G G' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    {g' : G' ⟶ Spec (CommRingCat.of R)}
    (a : SchemeHomOver (RelativeGroupLaw.baseChangeStr s g) (RelativeGroupLaw.baseChangeStr s g'))
    (qq : SchemeHomOver (pullback.snd g σ) (pullback.snd g' σ))
    (e₁ : g ≫ 𝟙 _ = 𝟙 _ ≫ g) (e₂ : s ≫ 𝟙 _ = ι ≫ σ) (e₁' : g' ≫ 𝟙 _ = 𝟙 _ ≫ g')
    (h : a.1 ≫ pullback.map g' s g' σ (𝟙 _) ι (𝟙 _) e₁' e₂ =
      pullback.map g s g σ (𝟙 _) ι (𝟙 _) e₁ e₂ ≫ qq.1)
    (P : SchemeHomOver s g) :
    pushPt hfac qq P = fibreMap a P := by
  apply Subtype.ext
  rw [pushPt_coe, fibreMap_coe, ← toFibrePt_coe_comp_map hfac P e₁ e₂, Category.assoc,
    ← reassoc_of% h, pullback.lift_fst, Category.comp_id]

end Points

section Ext

variable {p : ℕ} [Fact p.Prime] {κ : Type} [Field κ] [IsAlgClosed κ] [Algebra (ZMod p) κ]
variable {R : Type} [CommRing R]
variable {σ : Spec (CommRingCat.of (ZMod p)) ⟶ Spec (CommRingCat.of R)}
variable {s : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R)}

theorem hom_ext_of_pushPt
    (hfac : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) κ)) ≫ σ = s)
    {G G' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} {g' : G' ⟶ Spec (CommRingCat.of R)}
    [Smooth g] [IsSeparated g']
    (φ ψ : SchemeHomOver (pullback.snd g σ) (pullback.snd g' σ))
    (h : ∀ P : SchemeHomOver s g, pushPt hfac φ P = pushPt hfac ψ P) : φ = ψ := by
  apply Subtype.ext
  haveI : IsReduced (pullback g σ) := AlgebraicGeometry.isReduced_of_smooth_of_field (pullback.snd g σ)
  refine AlgebraicGeometry.ext_of_forall_geometricPoint_comp_eq_of_flat (algebraMap (ZMod p) κ)
    (algebraMap (ZMod p) κ).injective (pullback.snd g σ) (pullback.snd g' σ) φ.2 ψ.2 ?_
  intro x hx
  have hP := h (ofPt hfac x hx)
  have h1 := congrArg (liftPt hfac) hP
  rw [liftPt_pushPt, liftPt_pushPt, liftPt_ofPt] at h1
  exact h1

end Ext

section Laws

variable {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂]
variable {σ : Spec (CommRingCat.of R₁) ⟶ Spec (CommRingCat.of R)}
variable {ι : Spec (CommRingCat.of R₂) ⟶ Spec (CommRingCat.of R₁)}
variable {s : Spec (CommRingCat.of R₂) ⟶ Spec (CommRingCat.of R)}

def liftOver (hfac : ι ≫ σ = s) {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver s g) : SchemeHomOver ι (pullback.snd g σ) :=
  ⟨liftPt hfac P, liftPt_snd hfac P⟩

theorem baseChangePointToBase_liftOver {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver (ι ≫ σ) g) :
    RelativeGroupLaw.baseChangePointToBase σ (liftOver rfl P) = P :=
  Subtype.ext (liftPt_fst rfl P)

theorem comp_liftPt_eq {G G' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    {g' : G' ⟶ Spec (CommRingCat.of R)} (hfac : ι ≫ σ = s)
    (P : SchemeHomOver s g) (a : SchemeHomOver (pullback.snd g σ) (pullback.snd g' σ)) :
    GoodReductionJacobian.schemeHomOverComp (liftPt hfac P) (liftPt_snd hfac P) a =
      liftOver hfac (pushPt hfac a P) :=
  Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe]; exact (liftPt_pushPt hfac a P).symm)

theorem fibreRestrictAlong_mul {G G' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    {g' : G' ⟶ Spec (CommRingCat.of R)} (Lg : RelativeGroupLaw R g) (Lg' : RelativeGroupLaw R g')
    (h : SchemeHomOver g g')
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (Lg.mul t x y) h =
        Lg'.mul t (NeronModelInfra.schemeHomOverComp x h) (NeronModelInfra.schemeHomOverComp y h))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R₁)) (x y : SchemeHomOver t (pullback.snd g σ)) :
    NeronModelInfra.schemeHomOverComp ((Lg.baseChange σ).mul t x y)
        (NeronSpecialFibreInfra.fibreRestrictAlong σ g' g h) =
      (Lg'.baseChange σ).mul t
        (NeronModelInfra.schemeHomOverComp x (NeronSpecialFibreInfra.fibreRestrictAlong σ g' g h))
        (NeronModelInfra.schemeHomOverComp y (NeronSpecialFibreInfra.fibreRestrictAlong σ g' g h)) := by
  apply (RelativeGroupLaw.baseChangePointEquiv σ t).injective
  show RelativeGroupLaw.baseChangePointToBase σ _ = RelativeGroupLaw.baseChangePointToBase σ _
  rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, RelativeGroupLaw.baseChangePointToBase_mul,
    hmul, RelativeGroupLaw.baseChangePointToBase_mul, RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
    RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong]

theorem pushPt_mul (hfac : ι ≫ σ = s) {G G' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    {g' : G' ⟶ Spec (CommRingCat.of R)} (Lg' : RelativeGroupLaw R g')
    (a b : SchemeHomOver (pullback.snd g σ) (pullback.snd g' σ)) (P : SchemeHomOver s g) :
    pushPt hfac ((Lg'.baseChange σ).mul (pullback.snd g σ) a b) P =
      Lg'.mul s (pushPt hfac a P) (pushPt hfac b P) := by
  subst hfac
  have hnat := (Lg'.baseChange σ).mul_natural (pullback.snd g σ) ι (liftPt rfl P) (liftPt_snd rfl P) a b
  rw [comp_liftPt_eq, comp_liftPt_eq, comp_liftPt_eq] at hnat
  have h2 := congrArg (RelativeGroupLaw.baseChangePointToBase σ) hnat
  rw [RelativeGroupLaw.baseChangePointToBase_mul, baseChangePointToBase_liftOver, baseChangePointToBase_liftOver,
    baseChangePointToBase_liftOver] at h2
  exact h2

theorem pushPt_one (hfac : ι ≫ σ = s) {G G' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    {g' : G' ⟶ Spec (CommRingCat.of R)} (Lg' : RelativeGroupLaw R g') (P : SchemeHomOver s g) :
    pushPt hfac ((Lg'.baseChange σ).one (pullback.snd g σ)) P = Lg'.one s := by
  subst hfac
  have hnat := (Lg'.baseChange σ).one_natural (pullback.snd g σ) ι (liftPt rfl P) (liftPt_snd rfl P)
  rw [comp_liftPt_eq] at hnat
  have h2 := congrArg (RelativeGroupLaw.baseChangePointToBase σ) hnat
  rw [RelativeGroupLaw.baseChangePointToBase_one, baseChangePointToBase_liftOver] at h2
  exact h2

theorem pushPt_idPoint (hfac : ι ≫ σ = s) {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver s g) :
    pushPt hfac (RelativeGroupLaw.idPoint (f := pullback.snd g σ)) P = P := by
  apply liftPt_injective hfac
  rw [liftPt_pushPt]
  exact Category.comp_id _

theorem pushPt_nsmul_idPoint (hfac : ι ≫ σ = s) {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (Lg : RelativeGroupLaw R g) (n : ℕ) (P : SchemeHomOver s g) :
    pushPt hfac ((Lg.baseChange σ).nsmul (pullback.snd g σ) n RelativeGroupLaw.idPoint) P = Lg.nsmul s n P := by
  induction n with
  | zero => exact pushPt_one hfac Lg P
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, pushPt_mul, ih, pushPt_idPoint]

theorem pushPt_schemeNsmul (hfac : ι ≫ σ = s) {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}
    (Lg : RelativeGroupLaw R g) (n : ℕ) (P : SchemeHomOver s g)
    (E : SchemeHomOver (pullback.snd g σ) (pullback.snd g σ)) (hE : E.1 = (Lg.baseChange σ).schemeNsmul n) :
    pushPt hfac E P = Lg.nsmul s n P := by
  have : E = (Lg.baseChange σ).nsmul (pullback.snd g σ) n RelativeGroupLaw.idPoint := Subtype.ext hE
  rw [this, pushPt_nsmul_idPoint]

theorem one_comp_schemeNsmul {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R₁)} (L : RelativeGroupLaw R₁ g)
    (n : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R₁))
    (E : SchemeHomOver g g) (hE : E.1 = L.schemeNsmul n) :
    NeronModelInfra.schemeHomOverComp (L.one t) E = L.one t := by
  have hE' : E = L.nsmul g n RelativeGroupLaw.idPoint := Subtype.ext hE
  rw [hE']
  have h1 : NeronModelInfra.schemeHomOverComp (L.one t) (L.nsmul g n RelativeGroupLaw.idPoint) =
      GoodReductionJacobian.schemeHomOverComp (L.one t).1 (L.one t).2 (L.nsmul g n RelativeGroupLaw.idPoint) :=
    Subtype.ext rfl
  rw [h1, RelativeGroupLaw.nsmul_natural]
  have h2 : GoodReductionJacobian.schemeHomOverComp (L.one t).1 (L.one t).2
      (RelativeGroupLaw.idPoint (f := g)) = L.one t :=
    Subtype.ext (Category.comp_id _)
  rw [h2, RelativeGroupLaw.nsmul_unit]

theorem comp_mul_eq {G G' : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R₁)} {g' : G' ⟶ Spec (CommRingCat.of R₁)}
    (L' : RelativeGroupLaw R₁ g') {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R₁)}
    (x : SchemeHomOver t g) (a b : SchemeHomOver g g') :
    NeronModelInfra.schemeHomOverComp x (L'.mul g a b) =
      L'.mul t (NeronModelInfra.schemeHomOverComp x a) (NeronModelInfra.schemeHomOverComp x b) := by
  have h := L'.mul_natural g t x.1 x.2 a b
  exact h

end Laws

section FunctionField

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
  (κ : Type) [Field κ] [IsAlgClosed κ]

theorem isCurveOver_fbar : IsCurveOver κ (Fbar p M H hpM κ) := by
  obtain ⟨x, -, hxt, hfin⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed κ (ΓN p M H hpM)
      (ModularCurve.translation_mem_GammaH _ _)
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxt hfin

theorem hasPrincipalDivisors_fbar : HasPrincipalDivisors κ (Fbar p M H hpM κ) :=
  (isCurveOver_fbar p M H hpM κ).hasPrincipalDivisors

end FunctionField

section NodeStable

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

theorem isNodeStable_of_frob (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (Φ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃
      Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hΦ : ∀ v, Φ v = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v)
    (g : SemilinearAut (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hss : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      g • Φ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p ∧ Φ (g • Φ y) = y) :
    SemilinearAut.IsNodeStable O.ssFinset g := by

  have key : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      Φ.symm y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p ∧ g • Φ y = Φ.symm y := by
    intro y hy
    have h2 : g • Φ y = Φ.symm y := by
      rw [Equiv.eq_symm_apply]; exact (hss y hy).2
    exact ⟨h2 ▸ (hss y hy).1, h2⟩
  intro s hs
  rw [O.mem_ssFinset_iff, mem_ssNodePairsQExp_iff] at hs ⊢
  obtain ⟨hy, h1⟩ := hs
  rw [← hΦ] at h1 ⊢

  set y' := Φ.symm s.2 with hy'
  have hy's : y' ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := (key _ hy).1
  have hs2 : s.2 = Φ y' := (Equiv.apply_symm_apply Φ s.2).symm
  refine ⟨?_, ?_⟩
  · rw [hs2, (key _ hy's).2]; exact (key _ hy's).1
  · rw [h1, (key _ hy).2, hs2, (key _ hy's).2, ← hs2]
    show Φ.symm s.2 = Φ (Φ.symm (Φ.symm s.2))
    rw [Equiv.apply_symm_apply]

end NodeStable

section Additive

variable {R R' : Type} [CommRing R] [CommRing R']

theorem toFibrePt_ofFibrePt {X : Scheme.{0}} {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)}
    {f : X ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) :
    toFibrePt (ofFibrePt y) = y := by
  have h : overId (ofFibrePt y) = RelativeGroupLaw.baseChangePointToBase ι y := Subtype.ext rfl
  show RelativeGroupLaw.baseChangePointOfBase ι (overId (ofFibrePt y)) = y
  rw [h, RelativeGroupLaw.baseChangePointOfBase_toBase]

theorem ofFibrePt_mul {X : Scheme.{0}} {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)}
    {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (u v : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) :
    ofFibrePt ((L.baseChange ι).mul (𝟙 _) u v) = L.mul ι (ofFibrePt u) (ofFibrePt v) := by
  apply Subtype.ext
  have hnat := L.mul_natural ι (𝟙 _ ≫ ι) (𝟙 _) rfl (ofFibrePt u) (ofFibrePt v)
  have hu : GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl (ofFibrePt u) =
      RelativeGroupLaw.baseChangePointToBase ι u := Subtype.ext (Category.id_comp _)
  have hv : GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl (ofFibrePt v) =
      RelativeGroupLaw.baseChangePointToBase ι v := Subtype.ext (Category.id_comp _)
  rw [hu, hv] at hnat
  have h2 := congrArg Subtype.val hnat
  rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp] at h2
  rw [h2]
  show (RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).mul (𝟙 _) u v)).1 = _
  rw [RelativeGroupLaw.baseChangePointToBase_mul]

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

def aq (O : JHNeronObjectAtP p M H hpM A hA Λ) (i : Fin 2)
    (ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) :
    SchemeHomOver (resPt A ≫ Λ.σA) Λ.f :=
  fibreMap (O.abqFibre i) (O.ptsSp ξ)

theorem ptsSp_symm_aq (O : JHNeronObjectAtP p M H hpM A hA Λ) (i : Fin 2)
    (ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) :
    Λ.ptsSp.symm (aq O i ξ) =
      if i = 0 then (GluedPic0.toPic0Pair O.ssFinset ξ).1 else (GluedPic0.toPic0Pair O.ssFinset ξ).2 :=
  O.abqFibre_ptsSp ξ i

theorem aq_zero_eq (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) :
    aq O 0 ξ = Λ.ptsSp (GluedPic0.toPic0Pair O.ssFinset ξ).1 := by
  rw [← Equiv.symm_apply_eq]; exact ptsSp_symm_aq O 0 ξ

theorem aq_one_eq (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) :
    aq O 1 ξ = Λ.ptsSp (GluedPic0.toPic0Pair O.ssFinset ξ).2 := by
  rw [← Equiv.symm_apply_eq]; exact ptsSp_symm_aq O 1 ξ

theorem aq_add (O : JHNeronObjectAtP p M H hpM A hA Λ) (i : Fin 2)
    (ξ η : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) :
    aq O i (ξ + η) = Λ.L.mul (resPt A ≫ Λ.σA) (aq O i ξ) (aq O i η) := by
  unfold aq
  rw [O.ptsSp_add]
  show ofFibrePt (NeronModelInfra.schemeHomOverComp (toFibrePt (ofFibrePt _)) (O.abqFibre i)) = _
  rw [toFibrePt_ofFibrePt, O.abqFibre_mul, ofFibrePt_mul]
  rfl

variable [HasPrincipalDivisors (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))]

theorem exists_aq_zero_eq (O : JHNeronObjectAtP p M H hpM A hA Λ) (u : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f) :
    ∃ ξ, aq O 0 ξ = u := by
  obtain ⟨ξ, hξ⟩ := GluedPic0.toPic0Pair_surjective O.ssFinset (Λ.ptsSp.symm u, 0)
  exact ⟨ξ, by rw [aq_zero_eq, hξ, Equiv.apply_symm_apply]⟩

theorem ptsSp_symm_mul (O : JHNeronObjectAtP p M H hpM A hA Λ) (u v : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f) :
    Λ.ptsSp.symm (Λ.L.mul (resPt A ≫ Λ.σA) u v) = Λ.ptsSp.symm u + Λ.ptsSp.symm v := by
  obtain ⟨ξ, rfl⟩ := exists_aq_zero_eq O u
  obtain ⟨η, rfl⟩ := exists_aq_zero_eq O v
  rw [← aq_add, ptsSp_symm_aq, ptsSp_symm_aq, ptsSp_symm_aq]
  simp only [↓reduceIte, map_add, Prod.fst_add]

theorem ptsSp_symm_one (O : JHNeronObjectAtP p M H hpM A hA Λ) :
    Λ.ptsSp.symm (Λ.L.one (resPt A ≫ Λ.σA)) = 0 := by
  have h := ptsSp_symm_mul O (Λ.L.one (resPt A ≫ Λ.σA)) (Λ.L.one (resPt A ≫ Λ.σA))
  rw [Λ.L.one_mul] at h
  simpa using h

theorem ptsSp_symm_nsmul (O : JHNeronObjectAtP p M H hpM A hA Λ) (n : ℕ)
    (u : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f) :
    Λ.ptsSp.symm (Λ.L.nsmul (resPt A ≫ Λ.σA) n u) = n • Λ.ptsSp.symm u := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, ptsSp_symm_one O, zero_nsmul]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ptsSp_symm_mul O, ih, succ_nsmul]

end Additive

end R1AB48
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_descent_diamond_both_and_comp_hecke_U_eq_and_eq_verschiebung_of_blockOp_of_frobPullback_of_not_sq_dvd.R1AB48"

end
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_descent_diamond_both_and_comp_hecke_U_eq_and_eq_verschiebung_of_blockOp_of_frobPullback_of_not_sq_dvd.R1AB48"

open R1AB48 in
set_option maxHeartbeats 16000000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hpM2 : ¬ p ^ 2 ∣ M) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    [IsSeparated Λ.f] [LocallyOfFiniteType Λ.f]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt A ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (S : Set ℕ)
    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))
    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (σ : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσ : ∀ n : ↥O.ssFinset, (σ n).1.2 = n.1.1)

    (Φ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃ Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hΦ : ∀ v, Φ v = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v)
    (hFdiv : ∀ (D D' : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A))),
      (D' : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.mapDomain Φ (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) →
      F (Pic0.mk D) = Pic0.mk D')

    (hpull1sp : ∀ (D : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (x₁ : ↥(GluingData.admissible O.ssFinset)),
      (∀ s ∈ O.ssFinset, (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) s.1 = 0 ∧
        (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (Φ s.1) = 0) →
      (x₁ : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (p : ℤ) • Finsupp.mapDomain Φ.symm (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) →
      (x₁ : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb)) • (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) →
      (x₁ : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0 →
      O.ptsSp.symm (schemeHomOverComp (Λ.ptsSp (Pic0.mk D)) (degPull 1)) = GluedPic0.mk O.ssFinset x₁)

    (hUPABQ : (      ∀ ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
        GluedPic0.toPic0Pair O.ssFinset
            (O.ptsSp.symm (schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))) =
          AlgebraicCurve.Pic0Pair.blockOp Fstar (((p : ℤ) - 1) • AddMonoidHom.id _) 0 (δ.comp F)
            (GluedPic0.toPic0Pair O.ssFinset ξ)))

    (hUPKER : (∀ (x x' : ↥(GluingData.admissible O.ssFinset)),

      (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 = 0 →
      (∀ s ∈ O.ssFinset, (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 (Φ s.1) = 0) →

      (x' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (p : ℤ) • Finsupp.mapDomain Φ.symm
          (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 →
      (x' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 = 0 →
      (x' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 =
        (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 ∘ σ →
      O.ptsSp.symm (schemeHomOverComp (O.ptsSp (GluedPic0.mk O.ssFinset x))
          (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) =
        GluedPic0.mk O.ssFinset x') ∧

    (∀ ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
      (GluedPic0.toPic0Pair O.ssFinset ξ).2 = 0 →
      ∃ x : ↥(GluingData.admissible O.ssFinset),
        (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 = 0 ∧
        (∀ s ∈ O.ssFinset, (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 (Φ s.1) = 0) ∧
        GluedPic0.mk O.ssFinset x = ξ))

    [Algebra (ZMod p) (ResidueField ↥A)]
    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ base p)
    (hfac : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A))) ≫ σp = resPt A ≫ Λ.σA)
    (d : (ZMod M)ˣ)
    (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))

    (q : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr σp O.g) (RelativeGroupLaw.baseChangeStr σp Λ.f))
    (hqmul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp O.g)),
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange σp).mul s x y) (q i) =
          (Λ.L.baseChange σp).mul s (NeronModelInfra.schemeHomOverComp x (q i)) (NeronModelInfra.schemeHomOverComp y (q i)))
    (hqbc : ∀ i : Fin 2,
        (O.abqFibre i).1 ≫ pullback.map Λ.f (resPt A ≫ Λ.σA) Λ.f σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) =
          pullback.map O.g (resPt A ≫ Λ.σA) O.g σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) ≫ (q i).1)

    (U D : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp O.g) (RelativeGroupLaw.baseChangeStr σp O.g))
    (hU : U.1 ≫ pullback.fst O.g σp = pullback.fst O.g σp ≫ (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1)
    (hD : D.1 ≫ pullback.fst O.g σp = pullback.fst O.g σp ≫ (O.hecke S (CohCarrier.Gen.dia d)).1)

    (Fsch Vsch : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f))
    (hFsch : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p]
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) (RelativeGroupLaw.baseChangeStr σp Λ.f)),
      (schemeHomOverComp x Fsch).1 = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x.1)
    (hVF : Vsch.1 ≫ Fsch.1 = (Λ.L.baseChange σp).schemeNsmul p)
    :

    (∃ DΛ : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f),

      (∀ {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp Λ.f)),
        schemeHomOverComp ((Λ.L.baseChange σp).mul s x y) DΛ =
          (Λ.L.baseChange σp).mul s (schemeHomOverComp x DΛ) (schemeHomOverComp y DΛ)) ∧
      schemeHomOverComp D (q 1) = schemeHomOverComp (q 1) DΛ ∧
      schemeHomOverComp D (q 0) = schemeHomOverComp (q 0) DΛ ∧
      schemeHomOverComp U (q 1) = schemeHomOverComp (schemeHomOverComp (q 1) Fsch) DΛ) ∧

    (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp O.g)),
      NeronModelInfra.schemeHomOverComp x (q 1) = (Λ.L.baseChange σp).one s →
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x U) (q 0) =
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x (q 0)) Vsch) := by
  classical

  have hdpb : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d = pb := Units.ext (hd.trans hpb.symm)
  subst hdpb
  haveI hPD : HasPrincipalDivisors (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
    R1AB48.hasPrincipalDivisors_fbar p M H hpM (ResidueField ↥A)
  haveI : Smooth O.g := O.smooth
  have hp0 : 0 < p := (Fact.out : p.Prime).pos

  set gδ : SemilinearAut (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
    SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d))) with hgδ
  have hδ' : ∀ z, δ z = gδ • z := hδ

  have hstab : SemilinearAut.IsNodeStable O.ssFinset gδ := by
    refine R1AB48.isNodeStable_of_frob O Φ hΦ gδ fun y hy => ?_
    rw [hΦ, hΦ]
    exact ModularCurve.XHDRModelAtP.smul_frob_mem_ssPlacesQExp_and_frob_smul_frob_eq_of_mem_ssPlacesQExp p M H hpM
      hj 𝔛 A hA ρ hρ hdia0 _ hpb y hy
  have hDIA : ∀ ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
      NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.dia d)) =
        O.ptsSp (GluedPic0.glueMap O.ssFinset gδ hstab ξ) := by
    intro ξ
    rw [← Equiv.symm_apply_eq]
    exact ModularCurve.JHNeronObjectAtP.ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap p M H hpM hj 𝔛 A hA Λ O
      ρ hρ hσA hsp hdia0 S d hstab ξ

  have hfrobι : (frobenius (ResidueField ↥A) p).comp (algebraMap (ZMod p) (ResidueField ↥A)) =
      algebraMap (ZMod p) (ResidueField ↥A) := Subsingleton.elim _ _
  have hSpecF : Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A))) =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hfrobι]
  let τF : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA) :=
    ⟨Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)), by
      rw [← hfac, ← Category.assoc, hSpecF]⟩
  have hτF : τF.1 = Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) := rfl

  let frobPt : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f → SchemeHomOver (resPt A ≫ Λ.σA) Λ.f :=
    fun Q => GoodReductionJacobian.schemeHomOverComp τF.1 τF.2 Q

  have hFpush : ∀ Q : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f, R1AB48.pushPt hfac Fsch Q = frobPt Q := by
    intro Q
    apply R1AB48.liftPt_injective hfac
    rw [R1AB48.liftPt_pushPt]
    have h1 := hFsch (ResidueField ↥A) (R1AB48.liftOver hfac Q)
    rw [NeronModelInfra.schemeHomOverComp_coe] at h1
    change R1AB48.liftPt hfac Q ≫ Fsch.1 = _ at h1
    rw [h1]
    apply pullback.hom_ext
    · change Spec.map _ ≫ R1AB48.liftPt hfac Q ≫ _ = _
      rw [R1AB48.liftPt_fst, R1AB48.liftPt_fst]
      rfl
    · change Spec.map _ ≫ R1AB48.liftPt hfac Q ≫ _ = _
      rw [R1AB48.liftPt_snd, R1AB48.liftPt_snd, hSpecF]

  have hFpts : ∀ Q : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f, Λ.ptsSp.symm (frobPt Q) = F (Λ.ptsSp.symm Q) := by
    intro Q
    have h1 :=
      ModularCurve.JHNeronObjectAtP.levelData_ptsSp_frobeniusPushforward_eq_schemeHomOverComp_frobenius_ptsSp_of_hsp
        p M H hpM hpM2 hHp hj 𝔛 A hA Λ O ρ hρ hσA hsp F hF τF hτF (Λ.ptsSp.symm Q)
    rw [Equiv.apply_symm_apply] at h1
    show Λ.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp τF.1 τF.2 Q) = _
    rw [← h1, Equiv.symm_apply_apply]

  have hFinvF : ∀ w, Finv (F w) = w := fun w => by
    have := congrArg (fun φ => φ w) hFinv.2
    simpa using this
  have hVpts : ∀ Q : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f,
      Λ.ptsSp.symm (R1AB48.pushPt hfac Vsch Q) = Fstar (Λ.ptsSp.symm Q) := by
    intro Q
    have h1 : R1AB48.pushPt hfac (NeronModelInfra.schemeHomOverComp Vsch Fsch) Q =
        Λ.L.nsmul (resPt A ≫ Λ.σA) p Q :=
      R1AB48.pushPt_schemeNsmul hfac Λ.L p Q _ hVF
    rw [R1AB48.pushPt_comp, hFpush] at h1
    have h2 := congrArg Λ.ptsSp.symm h1
    rw [hFpts, R1AB48.ptsSp_symm_nsmul O] at h2
    have h3 := congrArg Finv h2
    rw [hFinvF, map_nsmul] at h3
    rw [h3, hFstar, natCast_zsmul]

  have hqpush : ∀ (i : Fin 2) (ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset),
      R1AB48.pushPt hfac (q i) (O.ptsSp ξ) = R1AB48.aq O i ξ := fun i ξ =>
    R1AB48.pushPt_eq_fibreMap hfac (O.abqFibre i) (q i) _ _ _ (hqbc i) (O.ptsSp ξ)
  have hUpush : ∀ P : SchemeHomOver (resPt A ≫ Λ.σA) O.g, R1AB48.pushPt hfac U P =
      NeronModelInfra.schemeHomOverComp P (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)) := fun P =>
    R1AB48.pushPt_eq_comp_of_fst hfac U _ hU P
  have hDpush : ∀ P : SchemeHomOver (resPt A ≫ Λ.σA) O.g, R1AB48.pushPt hfac D P =
      NeronModelInfra.schemeHomOverComp P (O.hecke S (CohCarrier.Gen.dia d)) := fun P =>
    R1AB48.pushPt_eq_comp_of_fst hfac D _ hD P

  let FRpull : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp O.g) :=
    NeronSpecialFibreInfra.fibreRestrictAlong σp O.g Λ.f (degPull 1)
  let DΛ : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f) :=
    NeronModelInfra.schemeHomOverComp FRpull (q 1)
  have hone : (1 : Fin 2) ≠ 0 := by decide

  have hDΛpts : ∀ Q : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f,
      Λ.ptsSp.symm (R1AB48.pushPt hfac DΛ Q) = gδ • Λ.ptsSp.symm Q := by
    intro Q
    change Λ.ptsSp.symm (R1AB48.pushPt hfac (NeronModelInfra.schemeHomOverComp FRpull (q 1)) Q) = _
    rw [R1AB48.pushPt_comp, R1AB48.pushPt_fibreRestrictAlong]
    obtain ⟨ξ', hξ'⟩ := O.ptsSp.surjective (NeronModelInfra.schemeHomOverComp Q (degPull 1))
    rw [← hξ', hqpush, R1AB48.ptsSp_symm_aq, if_neg hone]
    have h1 := hpullsp 1 Q
    rw [← hξ', Equiv.symm_apply_apply, if_neg hone] at h1
    rw [h1, hδ']

  have hDΛmul : ∀ {T' : Scheme.{0}} (s' : T' ⟶ Spec (CommRingCat.of (ZMod p)))
      (x y : SchemeHomOver s' (RelativeGroupLaw.baseChangeStr σp Λ.f)),
      NeronModelInfra.schemeHomOverComp ((Λ.L.baseChange σp).mul s' x y) DΛ =
        (Λ.L.baseChange σp).mul s' (NeronModelInfra.schemeHomOverComp x DΛ)
          (NeronModelInfra.schemeHomOverComp y DΛ) := by
    intro T' s' x y
    change NeronModelInfra.schemeHomOverComp _ (NeronModelInfra.schemeHomOverComp FRpull (q 1)) =
      (Λ.L.baseChange σp).mul s' (NeronModelInfra.schemeHomOverComp x (NeronModelInfra.schemeHomOverComp FRpull (q 1)))
        (NeronModelInfra.schemeHomOverComp y (NeronModelInfra.schemeHomOverComp FRpull (q 1)))
    rw [← NeronModelInfra.schemeHomOverComp_assoc, ← NeronModelInfra.schemeHomOverComp_assoc,
      ← NeronModelInfra.schemeHomOverComp_assoc,
      R1AB48.fibreRestrictAlong_mul Λ.L O.L (degPull 1) (fun s x y => hpull_mul 1 s x y) s' x y, hqmul 1]
  clear_value frobPt τF DΛ FRpull

  have hblock1 : ∀ z : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      (AlgebraicCurve.Pic0Pair.blockOp Fstar (((p : ℤ) - 1) • AddMonoidHom.id _) 0 (δ.comp F) z).1 =
        Fstar z.1 + (p - 1) • z.2 := by
    rintro ⟨z₁, z₂⟩
    rw [AlgebraicCurve.Pic0Pair.blockOp_apply]
    show Fstar z₁ + ((p : ℤ) - 1) • z₂ = Fstar z₁ + (p - 1) • z₂
    rw [← natCast_zsmul, Nat.cast_pred hp0]
  have hblock2 : ∀ z : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      (AlgebraicCurve.Pic0Pair.blockOp Fstar (((p : ℤ) - 1) • AddMonoidHom.id _) 0 (δ.comp F) z).2 =
        δ (F z.2) := by
    rintro ⟨z₁, z₂⟩
    rw [AlgebraicCurve.Pic0Pair.blockOp_apply]
    show (0 : Pic0 _ _ →+ Pic0 _ _) z₁ + δ (F z₂) = δ (F z₂)
    rw [AddMonoidHom.zero_apply, zero_add]

  refine ⟨⟨DΛ, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact fun s' x y => hDΛmul s' x y
  ·
    apply R1AB48.hom_ext_of_pushPt hfac
    intro P
    obtain ⟨ξ, rfl⟩ := O.ptsSp.surjective P
    apply Λ.ptsSp.symm.injective
    rw [R1AB48.pushPt_comp, R1AB48.pushPt_comp, hDpush, hDIA, hqpush, hqpush, hDΛpts, R1AB48.ptsSp_symm_aq,
      R1AB48.ptsSp_symm_aq, if_neg hone, if_neg hone, GluedPic0.toPic0Pair_glueMap]
  ·
    apply R1AB48.hom_ext_of_pushPt hfac
    intro P
    obtain ⟨ξ, rfl⟩ := O.ptsSp.surjective P
    apply Λ.ptsSp.symm.injective
    rw [R1AB48.pushPt_comp, R1AB48.pushPt_comp, hDpush, hDIA, hqpush, hqpush, hDΛpts, R1AB48.ptsSp_symm_aq,
      R1AB48.ptsSp_symm_aq, if_pos rfl, if_pos rfl, GluedPic0.toPic0Pair_glueMap]
  ·
    apply R1AB48.hom_ext_of_pushPt hfac
    intro P
    obtain ⟨ξ, rfl⟩ := O.ptsSp.surjective P
    apply Λ.ptsSp.symm.injective
    rw [R1AB48.pushPt_comp, R1AB48.pushPt_comp, R1AB48.pushPt_comp, hUpush, hqpush, hFpush, hDΛpts, hFpts,
      R1AB48.ptsSp_symm_aq, if_neg hone]
    obtain ⟨ξ', hξ'⟩ := O.ptsSp.surjective
      (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)))
    rw [← hξ', hqpush, R1AB48.ptsSp_symm_aq, if_neg hone]
    have h1 := hUPABQ ξ
    rw [← hξ', Equiv.symm_apply_apply] at h1
    rw [h1, hblock2, hδ']

  · let Np : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f) :=
      ⟨(Λ.L.baseChange σp).schemeNsmul (p - 1), (Λ.L.baseChange σp).schemeNsmul_over (p - 1)⟩
    have hglob : NeronModelInfra.schemeHomOverComp U (q 0) =
        (Λ.L.baseChange σp).mul (RelativeGroupLaw.baseChangeStr σp O.g)
          (NeronModelInfra.schemeHomOverComp (q 0) Vsch) (NeronModelInfra.schemeHomOverComp (q 1) Np) := by
      apply R1AB48.hom_ext_of_pushPt hfac
      intro P
      obtain ⟨ξ, rfl⟩ := O.ptsSp.surjective P
      apply Λ.ptsSp.symm.injective
      rw [R1AB48.pushPt_comp, hUpush, R1AB48.pushPt_mul, R1AB48.ptsSp_symm_mul O, R1AB48.pushPt_comp,
        R1AB48.pushPt_comp, hqpush, hqpush, hVpts, R1AB48.pushPt_schemeNsmul hfac Λ.L (p - 1) _ Np rfl,
        R1AB48.ptsSp_symm_nsmul O, R1AB48.ptsSp_symm_aq, R1AB48.ptsSp_symm_aq, if_pos rfl, if_neg hone]
      obtain ⟨ξ', hξ'⟩ := O.ptsSp.surjective
        (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)))
      rw [← hξ', hqpush, R1AB48.ptsSp_symm_aq, if_pos rfl]
      have h1 := hUPABQ ξ
      rw [← hξ', Equiv.symm_apply_apply] at h1
      rw [h1, hblock1]
    intro T s x hx
    have h := congrArg (fun E => NeronModelInfra.schemeHomOverComp x E) hglob
    try simp only at h
    rw [← NeronModelInfra.schemeHomOverComp_assoc, R1AB48.comp_mul_eq, ← NeronModelInfra.schemeHomOverComp_assoc,
      ← NeronModelInfra.schemeHomOverComp_assoc, hx,
      R1AB48.one_comp_schemeNsmul (Λ.L.baseChange σp) (p - 1) s Np rfl, (Λ.L.baseChange σp).mul_one] at h
    exact h

end S_ModularCurve_JHNeronObjectAtP_exists_descent_diamond_both_and_comp_hecke_U_eq_and_eq_verschiebung_of_blockOp_of_frobPullback_of_not_sq_dvd
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_descent_diamond_both_and_comp_hecke_U_eq_and_eq_verschiebung_of_blockOp_of_frobPullback_of_not_sq_dvd (solution)
