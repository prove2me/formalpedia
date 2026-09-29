-- Prove2me | solution 1 for ModularCurve.exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/0e3e25dd-c717-571f-8634-5467a48b83bf

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Theorems.Thm_ModularCurve_heckeOperatorHAlong_comm
import Theorems.Thm_ModularCurve_heckeOperatorHAlong_diamondHBar_comm
import Theorems.Thm_ModularCurve_diamondHBar_mul
import Definitions.Def_PDivisibleGroup_Points
import Theorems.Thm_PDivisibleGroup_exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq
import Theorems.Thm_PDivisibleGroup_finite_point_and_natCard_point_eq_pow
import Theorems.Thm_PDivisibleGroup_eq_of_forall_point_toAlgHom_apply_eq
import Theorems.Thm_Bialgebra_exists_bialgHom_coe_eq_of_comp_convMul
import Theorems.Thm_PDivisibleGroup_exists_moduleEnd_tateModule_apply_eq_pointsMkAdd_comp_of_comp_transition_eq
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdProj

open ModularCurve

section ConvAlgebra
open WithConv

variable {O : Type} [CommRing O] {p h : ℕ} (𝒢 : PDivisibleGroup O p h)

abbrev E (v : ℕ) : Type := WithConv (𝒢.level v →ₐ[O] 𝒢.level v)

def ccomp {v : ℕ} (f g : E 𝒢 v) : E 𝒢 v := toConv (f.ofConv.comp g.ofConv)

theorem point_comp_mul {v : ℕ} {L : Type} [CommRing L] [Algebra O L] (χ : 𝒢.level v →ₐ[O] L) (f g : E 𝒢 v) :
    toConv (χ.comp (f * g).ofConv) = toConv (χ.comp f.ofConv) * toConv (χ.comp g.ofConv) := by
  rw [AlgHom.comp_convMul_distrib]

theorem point_comp_one {v : ℕ} {L : Type} [CommRing L] [Algebra O L] (χ : 𝒢.level v →ₐ[O] L) :
    toConv (χ.comp (1 : E 𝒢 v).ofConv) = (1 : WithConv (𝒢.level v →ₐ[O] L)) := by
  rw [AlgHom.convOne_def, AlgHom.convOne_def]
  congr 1
  ext a
  simp [AlgHom.comp_apply]

noncomputable def evalAt {v : ℕ} {L : Type} [CommRing L] [Algebra O L] (χ : 𝒢.level v →ₐ[O] L) :
    E 𝒢 v →* WithConv (𝒢.level v →ₐ[O] L) where
  toFun f := toConv (χ.comp f.ofConv)
  map_one' := point_comp_one 𝒢 χ
  map_mul' f g := point_comp_mul 𝒢 χ f g

theorem point_comp_nsmul_comp {v : ℕ} {L : Type} [CommRing L] [Algebra O L] (χ : 𝒢.level v →ₐ[O] L)
    (n : ℕ) (f : 𝒢.level v →ₐc[O] 𝒢.level v) :
    toConv (χ.comp ((PDivisibleGroup.Hopf.nsmulAlgHom O (𝒢.level v) n).comp (f : 𝒢.level v →ₐ[O] 𝒢.level v))) =
      toConv (χ.comp (f : 𝒢.level v →ₐ[O] 𝒢.level v)) ^ n := by
  rw [PDivisibleGroup.Hopf.nsmulAlgHom_comp_bialgHom, ← AlgHom.comp_assoc,
    PDivisibleGroup.Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom]

theorem exists_tate_apply_eq [Fact p.Prime] [Algebra O (AlgebraicClosure ℚ)] (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v) :
    ∃ y : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
      (y : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) v = 𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x) :=
  (PDivisibleGroup.exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq p 𝒢
    (AlgebraicClosure ℚ) (fun w => PDivisibleGroup.finite_point_and_natCard_point_eq_pow p 𝒢 (AlgebraicClosure ℚ) w)).1 v x

end ConvAlgebra

section JSide

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (p : ℕ) [Fact p.Prime]

theorem genOpH_comm (g g' : CohCarrier.Gen M S) (x : JH M H) :
    genOpH M H S g (genOpH M H S g' x) = genOpH M H S g' (genOpH M H S g x) := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    cases g' with
    | T ℓ' hℓ' _ _ => haveI : Fact ℓ'.Prime := ⟨hℓ'⟩; exact heckeOperatorHAlong_comm M H ℓ ℓ' x
    | U q hq _ => haveI : Fact q.Prime := ⟨hq⟩; exact heckeOperatorHAlong_comm M H ℓ q x
    | dia d => exact heckeOperatorHAlong_diamondHBar_comm M H ℓ d x
  | U q hq hqM =>
    haveI : Fact q.Prime := ⟨hq⟩
    cases g' with
    | T ℓ' hℓ' _ _ => haveI : Fact ℓ'.Prime := ⟨hℓ'⟩; exact heckeOperatorHAlong_comm M H q ℓ' x
    | U q' hq' _ => haveI : Fact q'.Prime := ⟨hq'⟩; exact heckeOperatorHAlong_comm M H q q' x
    | dia d => exact heckeOperatorHAlong_diamondHBar_comm M H q d x
  | dia d =>
    cases g' with
    | T ℓ' hℓ' _ _ => haveI : Fact ℓ'.Prime := ⟨hℓ'⟩; exact (heckeOperatorHAlong_diamondHBar_comm M H ℓ' d x).symm
    | U q' hq' _ => haveI : Fact q'.Prime := ⟨hq'⟩; exact (heckeOperatorHAlong_diamondHBar_comm M H q' d x).symm
    | dia d' =>
      show diamondHBar M H d (diamondHBar M H d' x) = diamondHBar M H d' (diamondHBar M H d x)
      rw [← diamondHBar_mul, ← diamondHBar_mul, mul_comm]

noncomputable def Jtor (n : ℕ) : AddSubgroup (JH M H) :=
  (Submodule.torsionBy ℤ (JH M H) ((p ^ n : ℕ) : ℤ)).toAddSubgroup

theorem mem_Jtor {n : ℕ} (x : JH M H) : x ∈ Jtor M H p n ↔ ((p ^ n : ℕ) : ℤ) • x = 0 :=
  Submodule.mem_torsionBy_iff _ _

noncomputable scoped instance instModuleJtor (n : ℕ) : Module (ZMod (p ^ n)) ↥(Jtor M H p n) :=
  AddCommGroup.zmodModule fun x => Subtype.ext (by
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, ← natCast_zsmul]
    exact (mem_Jtor M H p x.1).mp x.2)

variable {M H}

noncomputable def resTor (n : ℕ) (f : JH M H →+ JH M H) : ↥(Jtor M H p n) →ₗ[ZMod (p ^ n)] ↥(Jtor M H p n) :=
  AddMonoidHom.toZModLinearMap (p ^ n)
    ((f.comp (Jtor M H p n).subtype).codRestrict (Jtor M H p n) fun x => by
      show f x ∈ Jtor M H p n
      rw [mem_Jtor, ← map_zsmul, (mem_Jtor M H p x.1).mp x.2, map_zero])

@[scoped simp] theorem resTor_apply_coe (n : ℕ) (f : JH M H →+ JH M H) (x : ↥(Jtor M H p n)) :
    ((resTor p n f x : ↥(Jtor M H p n)) : JH M H) = f x := rfl

variable (M H)

noncomputable def genAlg (n : ℕ) : Subalgebra (ZMod (p ^ n)) (Module.End (ZMod (p ^ n)) ↥(Jtor M H p n)) :=
  Algebra.adjoin (ZMod (p ^ n)) (Set.range fun g : CohCarrier.Gen M S => resTor p n (genOpH M H S g))

theorem isMulCommutative_genAlg (n : ℕ) : IsMulCommutative ↥(genAlg M H S p n) :=
  Algebra.isMulCommutative_adjoin _ (by
    rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact genOpH_comm M H S g g' x)

def GA (n : ℕ) : Type := ↥(genAlg M H S p n)

noncomputable scoped instance GA.instCommRing (n : ℕ) : CommRing (GA M H S p n) :=
  { (inferInstance : Ring ↥(genAlg M H S p n)) with
    mul_comm := fun a b => (isMulCommutative_genAlg M H S p n).is_comm.comm a b }

p2m_reactivate "P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.GA"
noncomputable scoped instance GA.instAlgebra (n : ℕ) : Algebra (ZMod (p ^ n)) (GA M H S p n) :=
  show Algebra (ZMod (p ^ n)) ↥(genAlg M H S p n) from inferInstance

p2m_reactivate "P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.GA"

def GA.toEnd {n : ℕ} (a : GA M H S p n) : Module.End (ZMod (p ^ n)) ↥(Jtor M H p n) :=
  (show ↥(genAlg M H S p n) from a).1

noncomputable def gaGen (n : ℕ) (g : CohCarrier.Gen M S) : GA M H S p n :=
  (⟨resTor p n (genOpH M H S g), Algebra.subset_adjoin ⟨g, rfl⟩⟩ : ↥(genAlg M H S p n))

noncomputable def evalJ (n : ℕ) : MvPolynomial (CohCarrier.Gen M S) ℤ_[p] →+* GA M H S p n :=
  (MvPolynomial.aeval (gaGen M H S p n)).toRingHom.comp (MvPolynomial.map (PadicInt.toZModPow n))

theorem evalJ_X (n : ℕ) (g : CohCarrier.Gen M S) :
    evalJ M H S p n (MvPolynomial.X g) = gaGen M H S p n g := by
  show MvPolynomial.aeval (gaGen M H S p n) (MvPolynomial.map (PadicInt.toZModPow n) (MvPolynomial.X g)) = _
  rw [MvPolynomial.map_X, MvPolynomial.aeval_X]

theorem evalJ_C (n : ℕ) (c : ℤ_[p]) :
    evalJ M H S p n (MvPolynomial.C c) = algebraMap (ZMod (p ^ n)) (GA M H S p n) (PadicInt.toZModPow n c) := by
  show MvPolynomial.aeval (gaGen M H S p n) (MvPolynomial.map (PadicInt.toZModPow n) (MvPolynomial.C c)) = _
  rw [MvPolynomial.map_C, MvPolynomial.aeval_C]

end JSide
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.GA"

section Link

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (p : ℕ) [Fact p.Prime]

theorem tate_apply_mem (x : TateModule p (JH M H)) (n : ℕ) : (x : ℕ → JH M H) n ∈ Jtor M H p n :=
  (mem_Jtor M H p _).mpr (TateModule.torsion x n)

theorem coe_zmod_smul (n : ℕ) (k : ZMod (p ^ n)) (y : ↥(Jtor M H p n)) :
    ((k • y : ↥(Jtor M H p n)) : JH M H) = ((k.val : ℕ) : ℤ) • (y : JH M H) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val k, Nat.cast_smul_eq_nsmul]
  rw [AddSubgroup.coe_nsmul, natCast_zsmul]

theorem GA.toEnd_algebraMap_apply (n : ℕ) (r : ZMod (p ^ n)) (y : ↥(Jtor M H p n)) :
    GA.toEnd M H S p (algebraMap (ZMod (p ^ n)) (GA M H S p n) r) y = r • y := by
  show (algebraMap (ZMod (p ^ n)) (Module.End (ZMod (p ^ n)) ↥(Jtor M H p n)) r) y = r • y
  simp [Module.algebraMap_end_apply]

theorem coe_aeval_smul_apply
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (JH M H))] [IsScalarTower ℤ_[p] 𝕋 (TateModule p (JH M H))]
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (JH M H)), op g • x = tateGenOpH M H S p g x)
    (P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) (x : TateModule p (JH M H)) (n : ℕ) :
    ((MvPolynomial.aeval op P • x : TateModule p (JH M H)) : ℕ → JH M H) n =
      ((GA.toEnd M H S p (evalJ M H S p n P) ⟨(x : ℕ → JH M H) n, tate_apply_mem M H p x n⟩ :
        ↥(Jtor M H p n)) : JH M H) := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C c =>
    rw [MvPolynomial.aeval_C, algebraMap_smul 𝕋 c x, TateModule.smul_apply, evalJ_C, GA.toEnd_algebraMap_apply,
      coe_zmod_smul]
    refine TateModule.natCast_smul_eq_of_zmod_eq (TateModule.torsion x n) ?_
    rw [ZMod.natCast_zmod_val, ← TateModule.toZModPow_eq_appr]
  | add P Q hP hQ =>
    rw [map_add, add_smul, TateModule.coe_add, Pi.add_apply, hP, hQ, map_add]
    show _ = (((GA.toEnd M H S p (evalJ M H S p n P) + GA.toEnd M H S p (evalJ M H S p n Q)) _ : ↥(Jtor M H p n)) : JH M H)
    rw [LinearMap.add_apply, AddSubgroup.coe_add]
  | mul_X P g hP =>
    rw [map_mul, MvPolynomial.aeval_X, mul_smul, hP (op g • x), map_mul, evalJ_X]
    show _ = (((GA.toEnd M H S p (evalJ M H S p n P)) ((GA.toEnd M H S p (gaGen M H S p n g)) _) : ↥(Jtor M H p n)) : JH M H)
    congr 2
    apply Subtype.ext
    show ((op g • x : TateModule p (JH M H)) : ℕ → JH M H) n = genOpH M H S g ((x : ℕ → JH M H) n)
    rw [hop, tateGenOpH_apply_coe]

end Link
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.GA"

section Theta

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {S : Set ℕ} {p : ℕ} [Fact p.Prime]
variable {O : Type} [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)]
  (hinj : Function.Injective (algebraMap O (AlgebraicClosure ℚ)))
  {h : ℕ} (𝒢 : PDivisibleGroup O p h)
  (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ JH M H) (hΔ : Function.Injective Δ)

def Realises (ψ : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v) (g : CohCarrier.Gen M S) : Prop :=
  ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
    Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
      ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : 𝒢.level v →ₐ[O] 𝒢.level v))))) =
      genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))

include hinj in

theorem algHom_eq_of_forall_point {v : ℕ} (f f' : 𝒢.level v →ₐ[O] 𝒢.level v)
    (hff' : ∀ χ : 𝒢.level v →ₐ[O] AlgebraicClosure ℚ, χ.comp f = χ.comp f') : f = f' := by
  apply AlgHom.ext
  intro a
  apply PDivisibleGroup.eq_of_forall_point_toAlgHom_apply_eq p hinj 𝒢 v
  intro x
  exact DFunLike.congr_fun (hff' (PDivisibleGroup.Point.toAlgHom x)) a

include hΔ in

theorem point_eq_of_Δ_eq {v : ℕ} (x y : 𝒢.Point (AlgebraicClosure ℚ) v)
    (hxy : Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y))) :
    x = y :=
  Additive.ofMul.injective (𝒢.pointsMkAdd_injective v (hΔ hxy))

include hinj hΔ in

theorem comp_comm_of_realises {ψ ψ' : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v} {g g' : CohCarrier.Gen M S}
    (hψ : Realises 𝒢 Δ ψ g) (hψ' : Realises 𝒢 Δ ψ' g') (v : ℕ) :
    (ψ v).comp (ψ' v) = (ψ' v).comp (ψ v) := by
  apply BialgHom.coe_algHom_injective
  refine algHom_eq_of_forall_point hinj 𝒢 _ _ fun χ => ?_

  have key : PDivisibleGroup.Point.ofAlgHom (χ.comp (((ψ v).comp (ψ' v) : 𝒢.level v →ₐc[O] 𝒢.level v) :
      𝒢.level v →ₐ[O] 𝒢.level v)) =
      PDivisibleGroup.Point.ofAlgHom (χ.comp (((ψ' v).comp (ψ v) : 𝒢.level v →ₐc[O] 𝒢.level v) :
      𝒢.level v →ₐ[O] 𝒢.level v)) := by
    apply point_eq_of_Δ_eq 𝒢 Δ hΔ
    have h1 := hψ' v (PDivisibleGroup.Point.ofAlgHom (χ.comp (ψ v : 𝒢.level v →ₐ[O] 𝒢.level v)))
    have h2 := hψ v (PDivisibleGroup.Point.ofAlgHom χ)
    have h3 := hψ v (PDivisibleGroup.Point.ofAlgHom (χ.comp (ψ' v : 𝒢.level v →ₐ[O] 𝒢.level v)))
    have h4 := hψ' v (PDivisibleGroup.Point.ofAlgHom χ)

    simp only [PDivisibleGroup.Point.toAlgHom, PDivisibleGroup.Point.ofAlgHom, WithConv.ofConv_toConv,
      AlgHom.comp_assoc] at h1 h2 h3 h4 ⊢
    have hc : (((ψ v).comp (ψ' v) : 𝒢.level v →ₐc[O] 𝒢.level v) : 𝒢.level v →ₐ[O] 𝒢.level v) =
        (ψ v : 𝒢.level v →ₐ[O] 𝒢.level v).comp (ψ' v : 𝒢.level v →ₐ[O] 𝒢.level v) := rfl
    have hc' : (((ψ' v).comp (ψ v) : 𝒢.level v →ₐc[O] 𝒢.level v) : 𝒢.level v →ₐ[O] 𝒢.level v) =
        (ψ' v : 𝒢.level v →ₐ[O] 𝒢.level v).comp (ψ v : 𝒢.level v →ₐ[O] 𝒢.level v) := rfl
    rw [hc, hc', h1, h2, h3, h4, genOpH_comm]
  exact congrArg PDivisibleGroup.Point.toAlgHom key

end Theta
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.GA"

section ThetaDef

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {S : Set ℕ} {p : ℕ} [Fact p.Prime]
variable {O : Type} [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)]
  {h : ℕ} (𝒢 : PDivisibleGroup O p h)
  (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ JH M H)
  (ψ : CohCarrier.Gen M S → ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v)

def bpow {v : ℕ} (f : 𝒢.level v →ₐc[O] 𝒢.level v) : ℕ → (𝒢.level v →ₐc[O] 𝒢.level v)
  | 0 => BialgHom.id O (𝒢.level v)
  | k + 1 => f.comp (bpow f k)

noncomputable def monB (v : ℕ) (α : CohCarrier.Gen M S →₀ ℕ) : 𝒢.level v →ₐc[O] 𝒢.level v :=
  α.support.toList.foldr (fun g acc => (bpow 𝒢 (ψ g v) (α g)).comp acc) (BialgHom.id O (𝒢.level v))

noncomputable def termE (v : ℕ) (α : CohCarrier.Gen M S →₀ ℕ) (c : ℤ_[p]) : E 𝒢 v :=
  WithConv.toConv ((PDivisibleGroup.Hopf.nsmulAlgHom O (𝒢.level v) (PadicInt.toZModPow v c).val).comp
    (monB 𝒢 ψ v α : 𝒢.level v →ₐ[O] 𝒢.level v))

noncomputable def theta (v : ℕ) (P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) : E 𝒢 v :=
  (AddMonoidAlgebra.coeff P).prod fun α c => termE 𝒢 ψ v α c

noncomputable def img {v : ℕ} (χ : 𝒢.level v →ₐ[O] AlgebraicClosure ℚ) : JH M H :=
  Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom χ)))

theorem img_mem_Jtor {v : ℕ} (χ : 𝒢.level v →ₐ[O] AlgebraicClosure ℚ) : img 𝒢 Δ χ ∈ Jtor M H p v := by
  rw [mem_Jtor, img, ← map_zsmul, natCast_zsmul]
  show Δ ((p ^ v) • 𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom χ))) = 0
  rw [𝒢.nsmul_pointsMkAdd_eq_zero, map_zero]

theorem img_mul {v : ℕ} (x y : WithConv (𝒢.level v →ₐ[O] AlgebraicClosure ℚ)) :
    img 𝒢 Δ (x * y).ofConv = img 𝒢 Δ x.ofConv + img 𝒢 Δ y.ofConv := by
  show Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofConv (x * y)))) = _
  rw [PDivisibleGroup.Point.ofConv_mul, ofMul_mul, map_add, map_add]
  rfl

theorem img_one {v : ℕ} : img 𝒢 Δ (1 : WithConv (𝒢.level v →ₐ[O] AlgebraicClosure ℚ)).ofConv = 0 := by
  show Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofConv 1))) = 0
  rw [show (PDivisibleGroup.Point.ofConv 1 : 𝒢.Point (AlgebraicClosure ℚ) v) = 1 from rfl, ofMul_one, map_zero, map_zero]

theorem img_pow {v : ℕ} (x : WithConv (𝒢.level v →ₐ[O] AlgebraicClosure ℚ)) (k : ℕ) :
    img 𝒢 Δ (x ^ k).ofConv = (k : ℤ) • img 𝒢 Δ x.ofConv := by
  induction k with
  | zero => rw [pow_zero, img_one, Nat.cast_zero, zero_zsmul]
  | succ k ih => rw [pow_succ, img_mul, ih, Nat.cast_succ, add_zsmul, one_zsmul]

end ThetaDef
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.GA"

section ThetaPoints

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {S : Set ℕ} {p : ℕ} [Fact p.Prime]
variable {O : Type} [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)]
  {h : ℕ} (𝒢 : PDivisibleGroup O p h)
  (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ JH M H)
  (ψ : CohCarrier.Gen M S → ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v)
  (hψ : ∀ g : CohCarrier.Gen M S, Realises 𝒢 Δ (ψ g) g)

theorem GA.toEnd_mul {n : ℕ} (a b : GA M H S p n) : GA.toEnd M H S p (a * b) = GA.toEnd M H S p a * GA.toEnd M H S p b := rfl
theorem GA.toEnd_one {n : ℕ} : GA.toEnd M H S p (1 : GA M H S p n) = 1 := rfl
theorem GA.toEnd_add {n : ℕ} (a b : GA M H S p n) : GA.toEnd M H S p (a + b) = GA.toEnd M H S p a + GA.toEnd M H S p b := rfl
theorem GA.toEnd_pow {n : ℕ} (a : GA M H S p n) (k : ℕ) : GA.toEnd M H S p (a ^ k) = GA.toEnd M H S p a ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, GA.toEnd_mul, ih]
theorem GA.toEnd_sum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → GA M H S p n) :
    GA.toEnd M H S p (∑ i ∈ s, f i) = ∑ i ∈ s, GA.toEnd M H S p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GA.toEnd_add, ih]

theorem coe_toEnd_gaGen_pow_apply {v : ℕ} (g : CohCarrier.Gen M S) (k : ℕ) (y : ↥(Jtor M H p v)) :
    ((GA.toEnd M H S p (gaGen M H S p v g ^ k) y : ↥(Jtor M H p v)) : JH M H) = (genOpH M H S g)^[k] (y : JH M H) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', GA.toEnd_mul, Module.End.mul_apply, Function.iterate_succ_apply']
    rw [show ((GA.toEnd M H S p (gaGen M H S p v g)) _ : ↥(Jtor M H p v)) = resTor p v (genOpH M H S g) _ from rfl,
      resTor_apply_coe, ih]

include hψ in

theorem img_comp_bpow {v : ℕ} (g : CohCarrier.Gen M S) (k : ℕ) (χ : 𝒢.level v →ₐ[O] AlgebraicClosure ℚ) :
    img 𝒢 Δ (χ.comp (bpow 𝒢 (ψ g v) k : 𝒢.level v →ₐ[O] 𝒢.level v)) = (genOpH M H S g)^[k] (img 𝒢 Δ χ) := by
  induction k generalizing χ with
  | zero => rfl
  | succ k ih =>
    have hc : ((bpow 𝒢 (ψ g v) (k + 1) : 𝒢.level v →ₐc[O] 𝒢.level v) : 𝒢.level v →ₐ[O] 𝒢.level v) =
        (ψ g v : 𝒢.level v →ₐ[O] 𝒢.level v).comp (bpow 𝒢 (ψ g v) k : 𝒢.level v →ₐ[O] 𝒢.level v) := rfl
    rw [hc, ← AlgHom.comp_assoc, ih (χ.comp (ψ g v : 𝒢.level v →ₐ[O] 𝒢.level v)), Function.iterate_succ_apply]
    congr 1
    exact hψ g v (PDivisibleGroup.Point.ofAlgHom χ)

include hψ in

theorem img_comp_monB {v : ℕ} (α : CohCarrier.Gen M S →₀ ℕ) (χ : 𝒢.level v →ₐ[O] AlgebraicClosure ℚ) :
    img 𝒢 Δ (χ.comp (monB 𝒢 ψ v α : 𝒢.level v →ₐ[O] 𝒢.level v)) =
      ((GA.toEnd M H S p (α.prod fun g k => gaGen M H S p v g ^ k) ⟨img 𝒢 Δ χ, img_mem_Jtor 𝒢 Δ χ⟩ :
        ↥(Jtor M H p v)) : JH M H) := by

  have key : ∀ (l : List (CohCarrier.Gen M S)) (χ : 𝒢.level v →ₐ[O] AlgebraicClosure ℚ),
      img 𝒢 Δ (χ.comp ((l.foldr (fun g acc => (bpow 𝒢 (ψ g v) (α g)).comp acc) (BialgHom.id O (𝒢.level v)) :
        𝒢.level v →ₐc[O] 𝒢.level v) : 𝒢.level v →ₐ[O] 𝒢.level v)) =
      ((GA.toEnd M H S p (l.foldr (fun g acc => gaGen M H S p v g ^ (α g) * acc) 1) ⟨img 𝒢 Δ χ, img_mem_Jtor 𝒢 Δ χ⟩ :
        ↥(Jtor M H p v)) : JH M H) := by
    intro l
    induction l with
    | nil => intro χ; rfl
    | cons g l ih =>
      intro χ
      rw [List.foldr_cons, List.foldr_cons]
      have hc : ((((bpow 𝒢 (ψ g v) (α g)).comp (l.foldr (fun g acc => (bpow 𝒢 (ψ g v) (α g)).comp acc)
          (BialgHom.id O (𝒢.level v)))) : 𝒢.level v →ₐc[O] 𝒢.level v) : 𝒢.level v →ₐ[O] 𝒢.level v) =
          (bpow 𝒢 (ψ g v) (α g) : 𝒢.level v →ₐ[O] 𝒢.level v).comp
            ((l.foldr (fun g acc => (bpow 𝒢 (ψ g v) (α g)).comp acc) (BialgHom.id O (𝒢.level v)) :
              𝒢.level v →ₐc[O] 𝒢.level v) : 𝒢.level v →ₐ[O] 𝒢.level v) := rfl
      rw [hc, ← AlgHom.comp_assoc, ih, mul_comm, GA.toEnd_mul, Module.End.mul_apply]
      congr 2
      apply Subtype.ext
      rw [coe_toEnd_gaGen_pow_apply]
      exact img_comp_bpow 𝒢 Δ ψ hψ g (α g) χ
  rw [monB, key]
  congr 3

  rw [Finsupp.prod, ← Finset.prod_map_toList, ← List.foldr_map, List.prod_eq_foldr]

end ThetaPoints
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.GA"

section ThetaLink

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {S : Set ℕ} {p : ℕ} [Fact p.Prime]
variable {O : Type} [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)]
  (hinj : Function.Injective (algebraMap O (AlgebraicClosure ℚ)))
  {h : ℕ} (𝒢 : PDivisibleGroup O p h)
  (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ JH M H) (hΔ : Function.Injective Δ)
  (ψ : CohCarrier.Gen M S → ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v)
  (hψ : ∀ g : CohCarrier.Gen M S, Realises 𝒢 Δ (ψ g) g)

include hψ in

theorem img_comp_termE {v : ℕ} (α : CohCarrier.Gen M S →₀ ℕ) (c : ℤ_[p]) (χ : 𝒢.level v →ₐ[O] AlgebraicClosure ℚ) :
    img 𝒢 Δ (χ.comp (termE 𝒢 ψ v α c).ofConv) =
      ((GA.toEnd M H S p (evalJ M H S p v (MvPolynomial.monomial α c)) ⟨img 𝒢 Δ χ, img_mem_Jtor 𝒢 Δ χ⟩ :
        ↥(Jtor M H p v)) : JH M H) := by

  have h1 : WithConv.toConv (χ.comp (termE 𝒢 ψ v α c).ofConv) =
      WithConv.toConv (χ.comp (monB 𝒢 ψ v α : 𝒢.level v →ₐ[O] 𝒢.level v)) ^ (PadicInt.toZModPow v c).val :=
    point_comp_nsmul_comp 𝒢 χ _ (monB 𝒢 ψ v α)
  have h2 : img 𝒢 Δ (χ.comp (termE 𝒢 ψ v α c).ofConv) =
      img 𝒢 Δ ((WithConv.toConv (χ.comp (monB 𝒢 ψ v α : 𝒢.level v →ₐ[O] 𝒢.level v)) ^ (PadicInt.toZModPow v c).val).ofConv) := by
    rw [← h1]
  rw [h2, img_pow, WithConv.ofConv_toConv, img_comp_monB 𝒢 Δ ψ hψ]

  show _ = ((GA.toEnd M H S p (MvPolynomial.aeval (gaGen M H S p v)
      (MvPolynomial.map (PadicInt.toZModPow v) (MvPolynomial.monomial α c))) _ : ↥(Jtor M H p v)) : JH M H)
  rw [MvPolynomial.map_monomial, MvPolynomial.aeval_monomial, GA.toEnd_mul, Module.End.mul_apply,
    GA.toEnd_algebraMap_apply, coe_zmod_smul]

theorem img_finset_prod {v : ℕ} {ι : Type} (s : Finset ι) (f : ι → WithConv (𝒢.level v →ₐ[O] AlgebraicClosure ℚ)) :
    img 𝒢 Δ (∏ i ∈ s, f i).ofConv = ∑ i ∈ s, img 𝒢 Δ (f i).ofConv := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, img_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, img_mul, ih]

include hψ in

theorem img_comp_theta {v : ℕ} (P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) (χ : 𝒢.level v →ₐ[O] AlgebraicClosure ℚ) :
    img 𝒢 Δ (χ.comp (theta 𝒢 ψ v P).ofConv) =
      ((GA.toEnd M H S p (evalJ M H S p v P) ⟨img 𝒢 Δ χ, img_mem_Jtor 𝒢 Δ χ⟩ : ↥(Jtor M H p v)) : JH M H) := by

  have h1 : WithConv.toConv (χ.comp (theta 𝒢 ψ v P).ofConv) = ∏ α ∈ P.support, evalAt 𝒢 χ (termE 𝒢 ψ v α (P.coeff α)) := by
    show evalAt 𝒢 χ (theta 𝒢 ψ v P) = _
    rw [theta, Finsupp.prod, map_prod]
    rfl
  have h2 : img 𝒢 Δ (χ.comp (theta 𝒢 ψ v P).ofConv) = img 𝒢 Δ (∏ α ∈ P.support, evalAt 𝒢 χ (termE 𝒢 ψ v α (P.coeff α))).ofConv := by
    rw [← h1]
  rw [h2, img_finset_prod]
  conv_rhs => rw [MvPolynomial.as_sum P, map_sum, GA.toEnd_sum, LinearMap.sum_apply, AddSubgroup.val_finsetSum]
  refine Finset.sum_congr rfl fun α _ => ?_
  exact img_comp_termE 𝒢 Δ ψ hψ α (P.coeff α) χ

include hinj hΔ hψ in

theorem theta_eq_of_aeval_eq
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (JH M H))] [IsScalarTower ℤ_[p] 𝕋 (TateModule p (JH M H))]
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (JH M H)), op g • x = tateGenOpH M H S p g x)
    (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (JH M H))
    (he : ∀ (y : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ), ((e y : TateModule p (JH M H)) : ℕ → JH M H) n = Δ ((y : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n))
    {P Q : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]} (hPQ : MvPolynomial.aeval op P = MvPolynomial.aeval op Q) (v : ℕ) :
    (theta 𝒢 ψ v P).ofConv = (theta 𝒢 ψ v Q).ofConv := by
  refine algHom_eq_of_forall_point hinj 𝒢 _ _ fun χ => ?_

  obtain ⟨z, hz⟩ := exists_tate_apply_eq 𝒢 v (PDivisibleGroup.Point.ofAlgHom χ)
  have hez : ((e z : TateModule p (JH M H)) : ℕ → JH M H) v = img 𝒢 Δ χ := by rw [he, hz]; rfl
  have key : img 𝒢 Δ (χ.comp (theta 𝒢 ψ v P).ofConv) = img 𝒢 Δ (χ.comp (theta 𝒢 ψ v Q).ofConv) := by
    rw [img_comp_theta 𝒢 Δ ψ hψ, img_comp_theta 𝒢 Δ ψ hψ]
    have hP := coe_aeval_smul_apply M H S p op hop P (e z) v
    have hQ := coe_aeval_smul_apply M H S p op hop Q (e z) v
    rw [hPQ] at hP
    have hsub : (⟨((e z : TateModule p (JH M H)) : ℕ → JH M H) v, tate_apply_mem M H p (e z) v⟩ : ↥(Jtor M H p v)) =
        ⟨img 𝒢 Δ χ, img_mem_Jtor 𝒢 Δ χ⟩ := Subtype.ext hez
    rw [hsub] at hP hQ
    rw [← hP, ← hQ]
  have := point_eq_of_Δ_eq 𝒢 Δ hΔ _ _ key
  exact congrArg PDivisibleGroup.Point.toAlgHom this

end ThetaLink
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.GA"

section ThetaBialg

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {S : Set ℕ} {p : ℕ} [Fact p.Prime]
variable {O : Type} [CommRing O]
  {h : ℕ} (𝒢 : PDivisibleGroup O p h)
  (ψ : CohCarrier.Gen M S → ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v)

theorem toConv_comp_termE_mul {v : ℕ} (T : Type) [CommRing T] [Algebra O T]
    (χ χ' : WithConv (𝒢.level v →ₐ[O] T)) (α : CohCarrier.Gen M S →₀ ℕ) (c : ℤ_[p]) :
    WithConv.toConv ((χ * χ').ofConv.comp (termE 𝒢 ψ v α c).ofConv) =
      WithConv.toConv (χ.ofConv.comp (termE 𝒢 ψ v α c).ofConv) * WithConv.toConv (χ'.ofConv.comp (termE 𝒢 ψ v α c).ofConv) := by
  rw [show WithConv.toConv ((χ * χ').ofConv.comp (termE 𝒢 ψ v α c).ofConv) = _ from
      point_comp_nsmul_comp 𝒢 (χ * χ').ofConv _ (monB 𝒢 ψ v α),
    show WithConv.toConv (χ.ofConv.comp (termE 𝒢 ψ v α c).ofConv) = _ from
      point_comp_nsmul_comp 𝒢 χ.ofConv _ (monB 𝒢 ψ v α),
    show WithConv.toConv (χ'.ofConv.comp (termE 𝒢 ψ v α c).ofConv) = _ from
      point_comp_nsmul_comp 𝒢 χ'.ofConv _ (monB 𝒢 ψ v α),
    ← mul_pow]
  congr 1
  rw [AlgHom.convMul_comp_bialgHom_distrib]

theorem toConv_one_comp_termE {v : ℕ} (T : Type) [CommRing T] [Algebra O T]
    (α : CohCarrier.Gen M S →₀ ℕ) (c : ℤ_[p]) :
    WithConv.toConv ((1 : WithConv (𝒢.level v →ₐ[O] T)).ofConv.comp (termE 𝒢 ψ v α c).ofConv) = 1 := by
  rw [show WithConv.toConv ((1 : WithConv (𝒢.level v →ₐ[O] T)).ofConv.comp (termE 𝒢 ψ v α c).ofConv) = _ from
      point_comp_nsmul_comp 𝒢 (1 : WithConv (𝒢.level v →ₐ[O] T)).ofConv _ (monB 𝒢 ψ v α)]
  have h0 := PDivisibleGroup.Hopf.convPow_comp_bialgHom (1 : WithConv (𝒢.level v →ₐ[O] T)) (monB 𝒢 ψ v α) 0
  rw [pow_zero, pow_zero] at h0
  rw [h0, WithConv.toConv_ofConv, one_pow]

theorem exists_bialgHom_coe_eq_theta (v : ℕ) (P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) :
    ∃ Θ : 𝒢.level v →ₐc[O] 𝒢.level v, (Θ : 𝒢.level v →ₐ[O] 𝒢.level v) = (theta 𝒢 ψ v P).ofConv := by
  refine Bialgebra.exists_bialgHom_coe_eq_of_comp_convMul (theta 𝒢 ψ v P).ofConv (fun T _ _ χ χ' => ?_) (fun T _ _ => ?_)
  ·
    show evalAt 𝒢 (χ * χ').ofConv (theta 𝒢 ψ v P) = evalAt 𝒢 χ.ofConv (theta 𝒢 ψ v P) * evalAt 𝒢 χ'.ofConv (theta 𝒢 ψ v P)
    rw [theta, Finsupp.prod, map_prod, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun α _ => ?_
    exact toConv_comp_termE_mul 𝒢 ψ T χ χ' α (P.coeff α)
  ·
    show evalAt 𝒢 (1 : WithConv (𝒢.level v →ₐ[O] T)).ofConv (theta 𝒢 ψ v P) = 1
    rw [theta, Finsupp.prod, map_prod]
    refine Finset.prod_eq_one fun α _ => ?_
    exact toConv_one_comp_termE 𝒢 ψ T α (P.coeff α)

noncomputable def Theta (v : ℕ) (P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) : 𝒢.level v →ₐc[O] 𝒢.level v :=
  (exists_bialgHom_coe_eq_theta 𝒢 ψ v P).choose

theorem coe_Theta (v : ℕ) (P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) :
    (Theta 𝒢 ψ v P : 𝒢.level v →ₐ[O] 𝒢.level v) = (theta 𝒢 ψ v P).ofConv :=
  (exists_bialgHom_coe_eq_theta 𝒢 ψ v P).choose_spec

end ThetaBialg
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.GA"

section Transfer

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {S : Set ℕ} {p : ℕ} [Fact p.Prime]
variable {O : Type} [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)]
  (hinj : Function.Injective (algebraMap O (AlgebraicClosure ℚ)))
  {h : ℕ} (𝒢 : PDivisibleGroup O p h)
  (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ JH M H) (hΔ : Function.Injective Δ)
  (ψ : CohCarrier.Gen M S → ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v)
  (hψ : ∀ g : CohCarrier.Gen M S, Realises 𝒢 Δ (ψ g) g)
  {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (JH M H))] [IsScalarTower ℤ_[p] 𝕋 (TateModule p (JH M H))]
  (op : CohCarrier.Gen M S → 𝕋)
  (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (JH M H)), op g • x = tateGenOpH M H S p g x)
  (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (JH M H))
  (he : ∀ (y : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ), ((e y : TateModule p (JH M H)) : ℕ → JH M H) n = Δ ((y : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n))

include hψ in

theorem img_comp_Theta_comp {v : ℕ} (P Q : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) (χ : 𝒢.level v →ₐ[O] AlgebraicClosure ℚ) :
    img 𝒢 Δ (χ.comp (((Theta 𝒢 ψ v P).comp (Theta 𝒢 ψ v Q) : 𝒢.level v →ₐc[O] 𝒢.level v) : 𝒢.level v →ₐ[O] 𝒢.level v)) =
      img 𝒢 Δ (χ.comp (theta 𝒢 ψ v (P * Q)).ofConv) := by
  have hc : (((Theta 𝒢 ψ v P).comp (Theta 𝒢 ψ v Q) : 𝒢.level v →ₐc[O] 𝒢.level v) : 𝒢.level v →ₐ[O] 𝒢.level v) =
      (theta 𝒢 ψ v P).ofConv.comp (theta 𝒢 ψ v Q).ofConv := by
    rw [← coe_Theta, ← coe_Theta]; rfl
  rw [hc, ← AlgHom.comp_assoc, img_comp_theta 𝒢 Δ ψ hψ Q (χ.comp (theta 𝒢 ψ v P).ofConv),
    img_comp_theta 𝒢 Δ ψ hψ (P * Q) χ, map_mul, mul_comm, GA.toEnd_mul, Module.End.mul_apply]
  congr 2
  apply Subtype.ext
  exact img_comp_theta 𝒢 Δ ψ hψ P χ

include hinj hΔ hψ in

theorem Theta_comp_eq {v : ℕ} (P Q : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) :
    (((Theta 𝒢 ψ v P).comp (Theta 𝒢 ψ v Q) : 𝒢.level v →ₐc[O] 𝒢.level v) : 𝒢.level v →ₐ[O] 𝒢.level v) =
      (Theta 𝒢 ψ v (P * Q) : 𝒢.level v →ₐ[O] 𝒢.level v) := by
  refine algHom_eq_of_forall_point hinj 𝒢 _ _ fun χ => ?_
  have key := img_comp_Theta_comp 𝒢 Δ ψ hψ P Q χ
  rw [← coe_Theta 𝒢 ψ v (P * Q)] at key
  exact congrArg PDivisibleGroup.Point.toAlgHom (point_eq_of_Δ_eq 𝒢 Δ hΔ _ _ key)

include hinj hΔ hψ hop he in

theorem Theta_eq_of_aeval_eq {v : ℕ} {P Q : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]}
    (hPQ : MvPolynomial.aeval op P = MvPolynomial.aeval op Q) : Theta 𝒢 ψ v P = Theta 𝒢 ψ v Q := by
  apply BialgHom.coe_algHom_injective
  rw [coe_Theta, coe_Theta]
  exact theta_eq_of_aeval_eq hinj 𝒢 Δ hΔ ψ hψ op hop e he hPQ v

include hinj hΔ hψ hop he in

theorem Theta_comp_eq_of_aeval {v : ℕ} {P Q R : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]}
    (hPQR : MvPolynomial.aeval op P * MvPolynomial.aeval op Q = MvPolynomial.aeval op R) :
    (Theta 𝒢 ψ v P).comp (Theta 𝒢 ψ v Q) = Theta 𝒢 ψ v R := by
  have h1 : (Theta 𝒢 ψ v P).comp (Theta 𝒢 ψ v Q) = Theta 𝒢 ψ v (P * Q) :=
    BialgHom.coe_algHom_injective (Theta_comp_eq hinj 𝒢 Δ hΔ ψ hψ P Q)
  rw [h1]
  exact Theta_eq_of_aeval_eq hinj 𝒢 Δ hΔ ψ hψ op hop e he (by rw [map_mul, hPQR])

end Transfer
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.GA"

section Final

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {S : Set ℕ} {p : ℕ} [Fact p.Prime]
variable {O : Type} [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)]
  (hinj : Function.Injective (algebraMap O (AlgebraicClosure ℚ)))
  {h : ℕ} (𝒢 : PDivisibleGroup O p h)
  (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ JH M H) (hΔ : Function.Injective Δ)
  (ψ : CohCarrier.Gen M S → ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v)
  (hψ : ∀ g : CohCarrier.Gen M S, Realises 𝒢 Δ (ψ g) g)

include hinj in

theorem algHom_eq_of_forall_point' {v : ℕ} {A : Type} [CommRing A] [Algebra O A] (f f' : A →ₐ[O] 𝒢.level v)
    (hff' : ∀ χ : 𝒢.level v →ₐ[O] AlgebraicClosure ℚ, χ.comp f = χ.comp f') : f = f' := by
  apply AlgHom.ext
  intro a
  apply PDivisibleGroup.eq_of_forall_point_toAlgHom_apply_eq p hinj 𝒢 v
  intro x
  exact DFunLike.congr_fun (hff' (PDivisibleGroup.Point.toAlgHom x)) a

theorem img_comp_transition {v : ℕ} (χ : 𝒢.level v →ₐ[O] AlgebraicClosure ℚ) :
    img 𝒢 Δ (χ.comp (𝒢.transitionAlgHom v)) = img 𝒢 Δ χ := by
  show Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) (v + 1) (Additive.ofMul (𝒢.pointIncl (AlgebraicClosure ℚ) v (PDivisibleGroup.Point.ofAlgHom χ)))) = _
  rw [𝒢.pointsMkAdd_pointIncl]
  rfl

theorem coe_toEnd_evalJ_succ (v : ℕ) (P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) (y : JH M H)
    (hy : y ∈ Jtor M H p v) (hy' : y ∈ Jtor M H p (v + 1)) :
    ((GA.toEnd M H S p (evalJ M H S p (v + 1) P) ⟨y, hy'⟩ : ↥(Jtor M H p (v + 1))) : JH M H) =
      ((GA.toEnd M H S p (evalJ M H S p v P) ⟨y, hy⟩ : ↥(Jtor M H p v)) : JH M H) := by
  induction P using MvPolynomial.induction_on generalizing y with
  | C c =>
    rw [evalJ_C, evalJ_C, GA.toEnd_algebraMap_apply, GA.toEnd_algebraMap_apply, coe_zmod_smul, coe_zmod_smul]
    refine TateModule.natCast_smul_eq_of_zmod_eq ((mem_Jtor M H p y).mp hy) ?_
    rw [ZMod.natCast_val, ZMod.natCast_zmod_val]
    have hcast := RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow v (v + 1) v.le_succ) c
    rw [RingHom.comp_apply, ZMod.castHom_apply] at hcast
    exact hcast
  | add P Q hP hQ =>
    rw [map_add, map_add, GA.toEnd_add, GA.toEnd_add, LinearMap.add_apply, LinearMap.add_apply,
      AddSubgroup.coe_add, AddSubgroup.coe_add, hP y hy hy', hQ y hy hy']
  | mul_X P g hP =>
    rw [map_mul, map_mul, evalJ_X, evalJ_X, GA.toEnd_mul, GA.toEnd_mul, Module.End.mul_apply, Module.End.mul_apply]
    have h1 : ((GA.toEnd M H S p (gaGen M H S p (v + 1) g) ⟨y, hy'⟩ : ↥(Jtor M H p (v + 1))) : JH M H) = genOpH M H S g y := rfl
    have h2 : ((GA.toEnd M H S p (gaGen M H S p v g) ⟨y, hy⟩ : ↥(Jtor M H p v)) : JH M H) = genOpH M H S g y := rfl
    have hgy : genOpH M H S g y ∈ Jtor M H p v := (GA.toEnd M H S p (gaGen M H S p v g) ⟨y, hy⟩).2
    have hgy' : genOpH M H S g y ∈ Jtor M H p (v + 1) := (GA.toEnd M H S p (gaGen M H S p (v + 1) g) ⟨y, hy'⟩).2
    have e1 : (GA.toEnd M H S p (gaGen M H S p (v + 1) g) ⟨y, hy'⟩ : ↥(Jtor M H p (v + 1))) = ⟨genOpH M H S g y, hgy'⟩ := Subtype.ext h1
    have e2 : (GA.toEnd M H S p (gaGen M H S p v g) ⟨y, hy⟩ : ↥(Jtor M H p v)) = ⟨genOpH M H S g y, hgy⟩ := Subtype.ext h2
    rw [e1, e2]
    exact hP _ hgy hgy'

theorem coe_toEnd_evalJ_add (m k : ℕ) (P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) (y : JH M H)
    (hy : y ∈ Jtor M H p m) (hy' : y ∈ Jtor M H p (m + k)) :
    ((GA.toEnd M H S p (evalJ M H S p (m + k) P) ⟨y, hy'⟩ : ↥(Jtor M H p (m + k))) : JH M H) =
      ((GA.toEnd M H S p (evalJ M H S p m P) ⟨y, hy⟩ : ↥(Jtor M H p m)) : JH M H) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hyk : y ∈ Jtor M H p (m + k) := by
      rw [mem_Jtor] at hy ⊢
      rw [pow_add, Nat.cast_mul, mul_comm, mul_smul, hy, smul_zero]
    exact (coe_toEnd_evalJ_succ (m + k) P y hyk hy').trans (ih hyk)

theorem coe_toEnd_evalJ_eq_of_le {a b : ℕ} (hab : a ≤ b) (P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) (y : JH M H)
    (ha : y ∈ Jtor M H p a) (hb : y ∈ Jtor M H p b) :
    ((GA.toEnd M H S p (evalJ M H S p b P) ⟨y, hb⟩ : ↥(Jtor M H p b)) : JH M H) =
      ((GA.toEnd M H S p (evalJ M H S p a P) ⟨y, ha⟩ : ↥(Jtor M H p a)) : JH M H) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact coe_toEnd_evalJ_add a k P y ha hb

theorem coe_toEnd_evalJ_eq_of_mem (a b : ℕ) (P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) (y : JH M H)
    (ha : y ∈ Jtor M H p a) (hb : y ∈ Jtor M H p b) :
    ((GA.toEnd M H S p (evalJ M H S p a P) ⟨y, ha⟩ : ↥(Jtor M H p a)) : JH M H) =
      ((GA.toEnd M H S p (evalJ M H S p b P) ⟨y, hb⟩ : ↥(Jtor M H p b)) : JH M H) := by
  rcases le_total a b with h | h
  · exact (coe_toEnd_evalJ_eq_of_le h P y ha hb).symm
  · exact coe_toEnd_evalJ_eq_of_le h P y hb ha

include hinj hΔ hψ in

theorem transition_comp_Theta (v : ℕ) (P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) :
    (𝒢.transition v).comp (Theta 𝒢 ψ (v + 1) P) = (Theta 𝒢 ψ v P).comp (𝒢.transition v) := by
  apply BialgHom.coe_algHom_injective
  refine algHom_eq_of_forall_point' hinj 𝒢 _ _ fun χ => ?_
  have hL : χ.comp (((𝒢.transition v).comp (Theta 𝒢 ψ (v + 1) P) : 𝒢.level (v+1) →ₐc[O] 𝒢.level v) :
      𝒢.level (v + 1) →ₐ[O] 𝒢.level v) = (χ.comp (𝒢.transitionAlgHom v)).comp (Theta 𝒢 ψ (v + 1) P : 𝒢.level (v+1) →ₐ[O] 𝒢.level (v+1)) := rfl
  have hR : χ.comp (((Theta 𝒢 ψ v P).comp (𝒢.transition v) : 𝒢.level (v+1) →ₐc[O] 𝒢.level v) :
      𝒢.level (v + 1) →ₐ[O] 𝒢.level v) = (χ.comp (Theta 𝒢 ψ v P : 𝒢.level v →ₐ[O] 𝒢.level v)).comp (𝒢.transitionAlgHom v) := rfl
  rw [hL, hR]

  have key : img 𝒢 Δ ((χ.comp (𝒢.transitionAlgHom v)).comp (Theta 𝒢 ψ (v + 1) P : 𝒢.level (v+1) →ₐ[O] 𝒢.level (v+1))) =
      img 𝒢 Δ ((χ.comp (Theta 𝒢 ψ v P : 𝒢.level v →ₐ[O] 𝒢.level v)).comp (𝒢.transitionAlgHom v)) := by
    rw [img_comp_transition, coe_Theta, coe_Theta, img_comp_theta 𝒢 Δ ψ hψ, img_comp_theta 𝒢 Δ ψ hψ]
    have hsub : (⟨img 𝒢 Δ (χ.comp (𝒢.transitionAlgHom v)), img_mem_Jtor 𝒢 Δ _⟩ : ↥(Jtor M H p (v + 1))) =
        ⟨img 𝒢 Δ χ, by rw [← img_comp_transition]; exact img_mem_Jtor 𝒢 Δ _⟩ := Subtype.ext (img_comp_transition 𝒢 Δ χ)
    rw [hsub]
    exact coe_toEnd_evalJ_succ v P _ (img_mem_Jtor 𝒢 Δ χ) _
  exact congrArg PDivisibleGroup.Point.toAlgHom (point_eq_of_Δ_eq 𝒢 Δ hΔ _ _ key)

end Final
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.GA"

section Assembly

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {S : Set ℕ} {p : ℕ} [Fact p.Prime]
variable {O : Type} [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)]
  (hinj : Function.Injective (algebraMap O (AlgebraicClosure ℚ)))
  {h : ℕ} (𝒢 : PDivisibleGroup O p h)
  (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ JH M H) (hΔ : Function.Injective Δ)
  (ψ : CohCarrier.Gen M S → ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v)
  (hψ : ∀ g : CohCarrier.Gen M S, Realises 𝒢 Δ (ψ g) g)

include hinj hΔ hψ in

theorem Theta_comp_comm_of_realises {φ : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v} {g : CohCarrier.Gen M S}
    (hφ : Realises 𝒢 Δ φ g) (v : ℕ) (P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) :
    (Theta 𝒢 ψ v P).comp (φ v) = (φ v).comp (Theta 𝒢 ψ v P) := by
  apply BialgHom.coe_algHom_injective
  refine algHom_eq_of_forall_point hinj 𝒢 _ _ fun χ => ?_
  have hL : χ.comp (((Theta 𝒢 ψ v P).comp (φ v) : 𝒢.level v →ₐc[O] 𝒢.level v) : 𝒢.level v →ₐ[O] 𝒢.level v) =
      (χ.comp (Theta 𝒢 ψ v P : 𝒢.level v →ₐ[O] 𝒢.level v)).comp (φ v : 𝒢.level v →ₐ[O] 𝒢.level v) := rfl
  have hR : χ.comp (((φ v).comp (Theta 𝒢 ψ v P) : 𝒢.level v →ₐc[O] 𝒢.level v) : 𝒢.level v →ₐ[O] 𝒢.level v) =
      (χ.comp (φ v : 𝒢.level v →ₐ[O] 𝒢.level v)).comp (Theta 𝒢 ψ v P : 𝒢.level v →ₐ[O] 𝒢.level v) := rfl
  rw [hL, hR]
  have key : img 𝒢 Δ ((χ.comp (Theta 𝒢 ψ v P : 𝒢.level v →ₐ[O] 𝒢.level v)).comp (φ v : 𝒢.level v →ₐ[O] 𝒢.level v)) =
      img 𝒢 Δ ((χ.comp (φ v : 𝒢.level v →ₐ[O] 𝒢.level v)).comp (Theta 𝒢 ψ v P : 𝒢.level v →ₐ[O] 𝒢.level v)) := by

    have h1 : img 𝒢 Δ ((χ.comp (Theta 𝒢 ψ v P : 𝒢.level v →ₐ[O] 𝒢.level v)).comp (φ v : 𝒢.level v →ₐ[O] 𝒢.level v)) =
        genOpH M H S g (img 𝒢 Δ (χ.comp (Theta 𝒢 ψ v P : 𝒢.level v →ₐ[O] 𝒢.level v))) :=
      hφ v (PDivisibleGroup.Point.ofAlgHom (χ.comp (Theta 𝒢 ψ v P : 𝒢.level v →ₐ[O] 𝒢.level v)))
    have h2 : img 𝒢 Δ (χ.comp (φ v : 𝒢.level v →ₐ[O] 𝒢.level v)) = genOpH M H S g (img 𝒢 Δ χ) :=
      hφ v (PDivisibleGroup.Point.ofAlgHom χ)
    rw [h1, coe_Theta, img_comp_theta 𝒢 Δ ψ hψ, img_comp_theta 𝒢 Δ ψ hψ]
    have hsub : (⟨img 𝒢 Δ (χ.comp (φ v : 𝒢.level v →ₐ[O] 𝒢.level v)), img_mem_Jtor 𝒢 Δ _⟩ : ↥(Jtor M H p v)) =
        GA.toEnd M H S p (gaGen M H S p v g) ⟨img 𝒢 Δ χ, img_mem_Jtor 𝒢 Δ χ⟩ := Subtype.ext h2
    rw [hsub, ← Module.End.mul_apply, ← GA.toEnd_mul, mul_comm, GA.toEnd_mul, Module.End.mul_apply]
    rfl
  exact congrArg PDivisibleGroup.Point.toAlgHom (point_eq_of_Δ_eq 𝒢 Δ hΔ _ _ key)

include hinj hΔ hψ in

theorem eq_Theta_X_of_realises {φ : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v} {g : CohCarrier.Gen M S}
    (hφ : Realises 𝒢 Δ φ g) (v : ℕ) : φ v = Theta 𝒢 ψ v (MvPolynomial.X g) := by
  apply BialgHom.coe_algHom_injective
  refine algHom_eq_of_forall_point hinj 𝒢 _ _ fun χ => ?_
  have key : img 𝒢 Δ (χ.comp (φ v : 𝒢.level v →ₐ[O] 𝒢.level v)) =
      img 𝒢 Δ (χ.comp (Theta 𝒢 ψ v (MvPolynomial.X g) : 𝒢.level v →ₐ[O] 𝒢.level v)) := by
    rw [coe_Theta, img_comp_theta 𝒢 Δ ψ hψ, evalJ_X]
    exact hφ v (PDivisibleGroup.Point.ofAlgHom χ)
  exact congrArg PDivisibleGroup.Point.toAlgHom (point_eq_of_Δ_eq 𝒢 Δ hΔ _ _ key)

include hψ in

theorem img_toAlgHom_comp_Theta {v : ℕ} (P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) (x : 𝒢.Point (AlgebraicClosure ℚ) v) :
    Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
      ((PDivisibleGroup.Point.toAlgHom x).comp (Theta 𝒢 ψ v P : 𝒢.level v →ₐ[O] 𝒢.level v))))) =
      ((GA.toEnd M H S p (evalJ M H S p v P) ⟨Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)),
        img_mem_Jtor 𝒢 Δ (PDivisibleGroup.Point.toAlgHom x)⟩ : ↥(Jtor M H p v)) : JH M H) := by
  rw [coe_Theta]
  exact img_comp_theta 𝒢 Δ ψ hψ P (PDivisibleGroup.Point.toAlgHom x)

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.GA"

end OrdProj
p2m_reactivate "P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.GA P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj"

open OrdProj in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (S : Set ℕ)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (hfaith : ∀ t : 𝕋, (∀ x : TateModule p (ModularCurve.JH M H), t • x = 0) → t = 0)
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (hord : op (CohCarrier.Gen.U p Fact.out hpM) ∉ S'.𝔪 i₀)

    {O : Type} [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)]
    (hinj : Function.Injective (algebraMap O (AlgebraicClosure ℚ)))
    {h : ℕ} (𝒢 : PDivisibleGroup O p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H) (hΔ : Function.Injective Δ)
    (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H))
    (he : ∀ (y : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
      ((e y : TateModule p (ModularCurve.JH M H)) : ℕ → ModularCurve.JH M H) n = Δ ((y : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n))

    (u : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v)
    (hut : ∀ v : ℕ, (𝒢.transition v).comp (u (v + 1)) = (u v).comp (𝒢.transition v))
    (huΔ : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
        ((PDivisibleGroup.Point.toAlgHom x).comp (u v : 𝒢.level v →ₐ[O] 𝒢.level v))))) =
        ModularCurve.genOpH M H S (CohCarrier.Gen.U p Fact.out hpM) (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))

    (hgenG : ∀ g : CohCarrier.Gen M S, ∃ ψ : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (𝒢.transition v)) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : 𝒢.level v →ₐ[O] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))) :
    ∃ (ε w : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v),
      (∀ v : ℕ, (ε v).comp (ε v) = ε v) ∧
      (∀ v : ℕ, (𝒢.transition v).comp (ε (v + 1)) = (ε v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, (ε v).comp (u v) = (u v).comp (ε v)) ∧
      (∀ v : ℕ, (𝒢.transition v).comp (w (v + 1)) = (w v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, (ε v).comp (w v) = w v) ∧ (∀ v : ℕ, (w v).comp (ε v) = w v) ∧
      (∀ v : ℕ, (w v).comp ((u v).comp (ε v)) = ε v) ∧
      (∀ v : ℕ, ((u v).comp (ε v)).comp (w v) = ε v) ∧

      (∀ (g : CohCarrier.Gen M S) (ψ : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v),
        (∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (𝒢.transition v)) →
        (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : 𝒢.level v →ₐ[O] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))) →
        ∀ v : ℕ, (ε v).comp (ψ v) = (ψ v).comp (ε v)) ∧

      (∀ (g g' : CohCarrier.Gen M S) (ψ ψ' : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v),
        (∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (𝒢.transition v)) →
        (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : 𝒢.level v →ₐ[O] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))) →
        (∀ v : ℕ, (𝒢.transition v).comp (ψ' (v + 1)) = (ψ' v).comp (𝒢.transition v)) →
        (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (ψ' v : 𝒢.level v →ₐ[O] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g' (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))) →
        ∀ v : ℕ, (ψ v).comp (ψ' v) = (ψ' v).comp (ψ v)) ∧

      ∃ Eop : Module.End ℤ_[p] (TateModule p (𝒢.Points (AlgebraicClosure ℚ))),
        (∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n v : ℕ) (f : 𝒢.Point (AlgebraicClosure ℚ) v),
          𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul f) = (x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n →
          ((Eop x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n =
            𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
              ((PDivisibleGroup.Point.toAlgHom f).comp (ε v : 𝒢.level v →ₐ[O] 𝒢.level v))))) ∧
        ∀ y : TateModule p (𝒢.Points (AlgebraicClosure ℚ)), e (Eop y) = (S'.e i₀) • e y := by
  classical

  let ψ : CohCarrier.Gen M S → ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v := fun g => (hgenG g).choose
  have hψt : ∀ (g : CohCarrier.Gen M S) (v : ℕ), (𝒢.transition v).comp (ψ g (v + 1)) = (ψ g v).comp (𝒢.transition v) :=
    fun g => (hgenG g).choose_spec.1
  have hψ : ∀ g : CohCarrier.Gen M S, Realises 𝒢 Δ (ψ g) g := fun g => (hgenG g).choose_spec.2
  have huR : Realises 𝒢 Δ u (CohCarrier.Gen.U p Fact.out hpM) := huΔ

  have hrange : ∀ s : 𝕋, ∃ P : MvPolynomial (CohCarrier.Gen M S) ℤ_[p], MvPolynomial.aeval op P = s := by
    intro s
    have hs : s ∈ Algebra.adjoin ℤ_[p] (Set.range op) := by rw [hgen]; exact Algebra.mem_top
    rw [Algebra.adjoin_range_eq_range_aeval] at hs
    exact hs
  obtain ⟨Pe, hPe⟩ := hrange (S'.e i₀)
  obtain ⟨t, ht⟩ := IharaLemma.exists_mul_mul_eq_of_notMem (S'.idem i₀) (S'.𝔪 i₀) (S'.mem_of_isMaximal_of_ne i₀) hord
  obtain ⟨Pt, hPt⟩ := hrange t

  have he2 : S'.e i₀ * S'.e i₀ = S'.e i₀ := (S'.idem i₀).eq
  have hU : MvPolynomial.aeval op (MvPolynomial.X (CohCarrier.Gen.U p Fact.out hpM) : MvPolynomial (CohCarrier.Gen M S) ℤ_[p]) =
      op (CohCarrier.Gen.U p Fact.out hpM) := MvPolynomial.aeval_X _ _

  have huX : ∀ v, u v = Theta 𝒢 ψ v (MvPolynomial.X (CohCarrier.Gen.U p Fact.out hpM)) :=
    fun v => eq_Theta_X_of_realises hinj 𝒢 Δ hΔ ψ hψ huR v

  refine ⟨fun v => Theta 𝒢 ψ v Pe, fun v => Theta 𝒢 ψ v (Pt * Pe), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v
    exact Theta_comp_eq_of_aeval hinj 𝒢 Δ hΔ ψ hψ op hop e he (by rw [hPe, he2])
  ·
    intro v
    exact transition_comp_Theta hinj 𝒢 Δ hΔ ψ hψ v Pe
  ·
    intro v
    exact Theta_comp_comm_of_realises hinj 𝒢 Δ hΔ ψ hψ huR v Pe
  ·
    intro v
    exact transition_comp_Theta hinj 𝒢 Δ hΔ ψ hψ v (Pt * Pe)
  ·
    intro v
    exact Theta_comp_eq_of_aeval hinj 𝒢 Δ hΔ ψ hψ op hop e he (by rw [map_mul, hPe, hPt, mul_left_comm, he2])
  ·
    intro v
    exact Theta_comp_eq_of_aeval hinj 𝒢 Δ hΔ ψ hψ op hop e he (by rw [map_mul, hPe, hPt, mul_assoc, he2])
  ·
    intro v
    rw [huX, Theta_comp_eq_of_aeval hinj 𝒢 Δ hΔ ψ hψ op hop e he (P := MvPolynomial.X _) (Q := Pe)
      (R := MvPolynomial.X (CohCarrier.Gen.U p Fact.out hpM) * Pe) (by rw [map_mul])]
    exact Theta_comp_eq_of_aeval hinj 𝒢 Δ hΔ ψ hψ op hop e he (by
      rw [map_mul, map_mul, hPe, hPt, hU]
      calc t * S'.e i₀ * (op (CohCarrier.Gen.U p Fact.out hpM) * S'.e i₀)
          = (t * op (CohCarrier.Gen.U p Fact.out hpM) * S'.e i₀) * S'.e i₀ := by ring
        _ = S'.e i₀ := by rw [ht, he2])
  ·
    intro v
    rw [huX, Theta_comp_eq_of_aeval hinj 𝒢 Δ hΔ ψ hψ op hop e he (P := MvPolynomial.X _) (Q := Pe)
      (R := MvPolynomial.X (CohCarrier.Gen.U p Fact.out hpM) * Pe) (by rw [map_mul])]
    exact Theta_comp_eq_of_aeval hinj 𝒢 Δ hΔ ψ hψ op hop e he (by
      rw [map_mul, map_mul, hPe, hPt, hU]
      calc op (CohCarrier.Gen.U p Fact.out hpM) * S'.e i₀ * (t * S'.e i₀)
          = (t * op (CohCarrier.Gen.U p Fact.out hpM) * S'.e i₀) * S'.e i₀ := by ring
        _ = S'.e i₀ := by rw [ht, he2])
  ·
    intro g φ hφt hφ v
    exact Theta_comp_comm_of_realises hinj 𝒢 Δ hΔ ψ hψ hφ v Pe
  ·
    intro g g' φ φ' hφt hφ hφ't hφ' v
    exact comp_comm_of_realises hinj 𝒢 Δ hΔ hφ hφ' v
  ·
    obtain ⟨Eop, hEop⟩ := PDivisibleGroup.exists_moduleEnd_tateModule_apply_eq_pointsMkAdd_comp_of_comp_transition_eq
      (L := AlgebraicClosure ℚ) p 𝒢 (fun v => Theta 𝒢 ψ v Pe) (fun v => transition_comp_Theta hinj 𝒢 Δ hΔ ψ hψ v Pe)
    refine ⟨Eop, hEop, fun y => ?_⟩
    apply Subtype.ext
    funext n
    obtain ⟨w, f, hf⟩ := PDivisibleGroup.Points.exists_mkAdd 𝒢 ((y : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n)
    rw [he, hEop y n w f hf, ← hPe, coe_aeval_smul_apply M H S p op hop Pe (e y) n,
      img_toAlgHom_comp_Theta 𝒢 Δ ψ hψ Pe f]
    have hyn : ((e y : TateModule p (ModularCurve.JH M H)) : ℕ → ModularCurve.JH M H) n = Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f)) := by rw [he, hf]
    have hmemn : Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f)) ∈ Jtor M H p n := by rw [← hyn]; exact tate_apply_mem M H p (e y) n
    rw [coe_toEnd_evalJ_eq_of_mem w n Pe _ _ hmemn]
    congr 2
    exact Subtype.ext hyn.symm

end S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH
end P2MW
export P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH (solution)
