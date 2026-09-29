-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/851066d0-2e63-54f9-83da-f6326eb28589

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_NodeLocalizedPresentation
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

namespace FltWs29
namespace T27

open ModularCurve ModularCurve.NodeLocalized ModularCurve.CharPReduction MvPolynomial

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

section Swap

theorem comp_swap_eq {k : Type*} (a b : k) : ((![a, b] : Fin 2 → k) ∘ (Equiv.swap (0 : Fin 2) 1)) = ![b, a] := by
  funext i
  fin_cases i <;> simp

variable {L : Type*} [CommRing L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k)

theorem pointEval_rename_swap (p : MvPolynomial (Fin 2) A) :
    pointEval A red a b (rename (Equiv.swap 0 1) p) = pointEval A red b a p := by
  rw [pointEval, pointEval, coe_eval₂Hom, coe_eval₂Hom, eval₂_rename, comp_swap_eq]

end Swap

section QExpand
variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeffMap_qExpand' (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

end QExpand

section Gens
variable (q : ℕ) [Fact q.Prime]

noncomputable def J1 : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (Dvd.intro (1 * q) (one_mul _)))⟩

noncomputable def JN : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (Dvd.intro 1 (mul_one _)))⟩

theorem coe_J1 : ((J1 q : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
    = jqModC (AlgebraicClosure ℚ) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ 1 (jqModC ℚ)) = _
  rw [qExpand_one_apply]
  exact map_jqModC _

theorem coe_JN : ((JN q : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
    = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ (1 * q) (jqModC ℚ))
    = qExpand (AlgebraicClosure ℚ) (1 * q) (jqModC (AlgebraicClosure ℚ))
  rw [coeffMap_qExpand']
  exact congrArg _ (map_jqModC _)

theorem isFrickeAutFull_one_mul : IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have key : ∀ (n : ℕ) [NeZero n], n = q → IsFrickeAutFull n (frickeInvolutionFull n) := by
    rintro n _ rfl
    exact isFrickeAutFull_frickeInvolutionFull_prime _
  exact key (1 * q) (one_mul q)

theorem w_J1 : frickeInvolutionBar (1 * q) (J1 q) = JN q :=
  frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) 1 (1 * q) (one_mul _)

theorem w_JN : frickeInvolutionBar (1 * q) (JN q) = J1 q :=
  frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) (1 * q) 1 (mul_one _)

end Gens

section EvalF
variable (q : ℕ) [Fact q.Prime] (A₀ : Subring (AlgebraicClosure ℚ))

noncomputable def EF : MvPolynomial (Fin 2) A₀ →+* modularFunctionFieldBar (1 * q) :=
  eval₂Hom ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).comp A₀.subtype) ![J1 q, JN q]

theorem algebraMap_comp_EF :
    (algebraMap (modularFunctionFieldBar (1 * q)) (LaurentSeries (AlgebraicClosure ℚ))).comp (EF q A₀)
      = modularEval (1 * q) A₀ := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
  · simp only [RingHom.comp_apply, EF, modularEval, eval₂Hom_C]
    rfl
  · fin_cases i
    · simp only [RingHom.comp_apply, EF, modularEval, eval₂Hom_X']
      exact coe_J1 q
    · simp only [RingHom.comp_apply, EF, modularEval, eval₂Hom_X']
      exact coe_JN q

theorem coe_EF (p : MvPolynomial (Fin 2) A₀) :
    ((EF q A₀ p : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) A₀ p :=
  RingHom.congr_fun (algebraMap_comp_EF q A₀) p

set_option maxHeartbeats 4000000 in

theorem frickeInvolutionBar_EF (p : MvPolynomial (Fin 2) A₀) :
    frickeInvolutionBar (1 * q) (EF q A₀ p) = EF q A₀ (rename (Equiv.swap 0 1) p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [rename_C]
    simp only [EF, eval₂Hom_C, RingHom.comp_apply]
    exact AlgEquiv.commutes _ _
  | add p r hp hr => rw [map_add, map_add, hp, hr, ← map_add, ← map_add]
  | mul_X p i hp =>
    have hX : frickeInvolutionBar (1 * q) (EF q A₀ (X i)) = EF q A₀ (X (Equiv.swap 0 1 i)) := by
      fin_cases i
      · simp only [EF, eval₂Hom_X', Fin.isValue]
        exact w_J1 q
      · simp only [EF, eval₂Hom_X', Fin.isValue]
        exact w_JN q
    rw [map_mul, map_mul, map_mul, rename_X, map_mul, hp, hX]

end EvalF

section Transport
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem modularEval_ne_zero (c : k) {s : MvPolynomial (Fin 2) (coeffSubring A K)}
    (hs : pointEval (coeffSubring A K) (redRestrict red K) c (c ^ q) s ≠ 0) :
    modularEval (1 * q) (coeffSubring A K) s ≠ 0 :=
  fun h => hs (pointEval_eq_zero_of_modularEval_eq_zero red c K s h)

theorem mem_bar_of_mem (c : k) {g : LaurentSeries (AlgebraicClosure ℚ)}
    (hg : g ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) c (c ^ q)) :
    g ∈ modularFunctionFieldBar (1 * q) := by
  obtain ⟨r, s, hs, h⟩ := hg
  have hs0 := modularEval_ne_zero red K c hs
  have hg' : g = modularEval (1 * q) (coeffSubring A K) r / modularEval (1 * q) (coeffSubring A K) s := by
    rw [eq_div_iff hs0, h]
  rw [hg', ← coe_EF q (coeffSubring A K) r, ← coe_EF q (coeffSubring A K) s]
  exact (modularFunctionFieldBar (1 * q)).div_mem (SetLike.coe_mem _) (SetLike.coe_mem _)

noncomputable def toBar (c : k) :
    modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) c (c ^ q)
      →+* modularFunctionFieldBar (1 * q) where
  toFun g := ⟨(g : LaurentSeries (AlgebraicClosure ℚ)), mem_bar_of_mem red K c g.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem coe_toBar (c : k) (g : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) c (c ^ q)) :
    ((toBar red K c g : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) = g := rfl

theorem toBar_modularEvalAt (c : k) (p : MvPolynomial (Fin 2) (coeffSubring A K)) :
    toBar red K c (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) c (c ^ q) p)
      = EF q (coeffSubring A K) p :=
  Subtype.ext (coe_EF q (coeffSubring A K) p).symm

set_option maxHeartbeats 4000000 in

theorem fricke_presentation (c : k)
    (g : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) c (c ^ q))
    {r s : MvPolynomial (Fin 2) (coeffSubring A K)}
    (h : (g : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K) s
      = modularEval (1 * q) (coeffSubring A K) r) :
    ((frickeInvolutionBar (1 * q) (toBar red K c g) : modularFunctionFieldBar (1 * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K) (rename (Equiv.swap 0 1) s)
      = modularEval (1 * q) (coeffSubring A K) (rename (Equiv.swap 0 1) r) := by
  have h' : toBar red K c g * EF q (coeffSubring A K) s = EF q (coeffSubring A K) r := by
    apply Subtype.ext
    show (g : LaurentSeries (AlgebraicClosure ℚ))
        * ((EF q (coeffSubring A K) s : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = ((EF q (coeffSubring A K) r : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
    rw [coe_EF, coe_EF]
    exact h
  have h2 := congrArg (frickeInvolutionBar (1 * q)) h'
  rw [map_mul, frickeInvolutionBar_EF, frickeInvolutionBar_EF] at h2
  have h3 : ((frickeInvolutionBar (1 * q) (toBar red K c g) : modularFunctionFieldBar (1 * q)) :
        LaurentSeries (AlgebraicClosure ℚ))
      * ((EF q (coeffSubring A K) (rename (Equiv.swap 0 1) s) : modularFunctionFieldBar (1 * q)) :
        LaurentSeries (AlgebraicClosure ℚ))
      = ((EF q (coeffSubring A K) (rename (Equiv.swap 0 1) r) : modularFunctionFieldBar (1 * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) :=
    congrArg Subtype.val h2
  rwa [coe_EF, coe_EF] at h3

set_option maxHeartbeats 4000000 in

noncomputable def frickeMap (c c' d' : k) (hc : c ^ q = c') (hd : c = d') :
    modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) c (c ^ q)
      →+* modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) c' d' :=
  ((algebraMap (modularFunctionFieldBar (1 * q)) (LaurentSeries (AlgebraicClosure ℚ))).comp
      (((frickeInvolutionBar (1 * q) : modularFunctionFieldBar (1 * q) ≃ₐ[AlgebraicClosure ℚ]
          modularFunctionFieldBar (1 * q)) : modularFunctionFieldBar (1 * q) →+* modularFunctionFieldBar (1 * q)).comp
        (toBar red K c))).codRestrict
    (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) c' d') (by
      intro g
      obtain ⟨r, s, hs, h⟩ := g.2
      refine ⟨rename (Equiv.swap 0 1) r, rename (Equiv.swap 0 1) s, ?_, fricke_presentation red K c g h⟩
      rw [pointEval_rename_swap, ← hd, ← hc]
      exact hs)

theorem coe_frickeMap (c c' d' : k) (hc : c ^ q = c') (hd : c = d')
    (g : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) c (c ^ q)) :
    ((frickeMap red K c c' d' hc hd g :
        modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) c' d') :
        LaurentSeries (AlgebraicClosure ℚ))
      = ((frickeInvolutionBar (1 * q) (toBar red K c g) : modularFunctionFieldBar (1 * q)) :
          LaurentSeries (AlgebraicClosure ℚ)) := rfl

theorem toBar_frickeMap (c c' : k) (hc : c ^ q = c') (hd : c = c' ^ q)
    (g : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) c (c ^ q)) :
    toBar red K c' (frickeMap red K c c' (c' ^ q) hc hd g) = frickeInvolutionBar (1 * q) (toBar red K c g) :=
  Subtype.ext rfl

theorem frickeMap_modularEvalAt (c c' d' : k) (hc : c ^ q = c') (hd : c = d')
    (p : MvPolynomial (Fin 2) (coeffSubring A K)) :
    frickeMap red K c c' d' hc hd (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) c (c ^ q) p)
      = modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) c' d' (rename (Equiv.swap 0 1) p) := by
  apply Subtype.ext
  rw [coe_frickeMap, toBar_modularEvalAt, frickeInvolutionBar_EF, coe_EF]
  rfl

end Transport

end FltWs29.T27

set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

set_option maxHeartbeats 4000000 in
theorem FltWs29.T27.main
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ∃ σ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ≃+* ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q)),
      (∀ (g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) (hgF : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q)),
          ((σ g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q))) : LaurentSeries (AlgebraicClosure ℚ))
            = ((frickeInvolutionBar (1 * q) ⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ : modularFunctionFieldBar (1 * q)) :
                LaurentSeries (AlgebraicClosure ℚ))) ∧
      (∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
          σ (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) p)
            = modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q)
                (MvPolynomial.rename (Equiv.swap 0 1) p)) := by
  have hqq : (a ^ q) ^ q = a := by rw [← pow_mul, ← sq, ha2]
  have h1 : ∀ g, FltWs29.T27.frickeMap red K (a ^ q) a (a ^ q) hqq rfl
      (FltWs29.T27.frickeMap red K a (a ^ q) ((a ^ q) ^ q) rfl hqq.symm g) = g := fun g => by
    apply Subtype.ext
    rw [FltWs29.T27.coe_frickeMap, FltWs29.T27.toBar_frickeMap,
      frickeInvolutionBar_frickeInvolutionBar]
    rfl
  have h2 : ∀ g, FltWs29.T27.frickeMap red K a (a ^ q) ((a ^ q) ^ q) rfl hqq.symm
      (FltWs29.T27.frickeMap red K (a ^ q) a (a ^ q) hqq rfl g) = g := fun g => by
    apply Subtype.ext
    rw [FltWs29.T27.coe_frickeMap, FltWs29.T27.toBar_frickeMap,
      frickeInvolutionBar_frickeInvolutionBar]
    rfl
  refine ⟨{ toFun := FltWs29.T27.frickeMap red K a (a ^ q) ((a ^ q) ^ q) rfl hqq.symm,
            invFun := FltWs29.T27.frickeMap red K (a ^ q) a (a ^ q) hqq rfl,
            left_inv := h1, right_inv := h2,
            map_mul' := fun x y => map_mul _ x y, map_add' := fun x y => map_add _ x y }, ?_, ?_⟩
  · intro g hgF
    rfl
  · intro p
    exact FltWs29.T27.frickeMap_modularEvalAt red K a (a ^ q) ((a ^ q) ^ q) rfl hqq.symm p

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ∃ σ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) ≃+* ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q)),
      (∀ (g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) (hgF : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q)),
          ((σ g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q))) : LaurentSeries (AlgebraicClosure ℚ))
            = ((frickeInvolutionBar (1 * q) ⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ : modularFunctionFieldBar (1 * q)) :
                LaurentSeries (AlgebraicClosure ℚ))) ∧
      (∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
          σ (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) p)
            = modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q)
                (MvPolynomial.rename (Equiv.swap 0 1) p)) :=
  FltWs29.T27.main red a ha2 K

end S_ModularCurve_NodeLocalized_exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar (solution)
