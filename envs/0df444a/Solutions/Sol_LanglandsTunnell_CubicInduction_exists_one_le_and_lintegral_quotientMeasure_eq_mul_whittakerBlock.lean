-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_one_le_and_lintegral_quotientMeasure_eq_mul_whittakerBlock
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d30b23f4-ef4b-5507-bc6f-d486c9f0a372

import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
import Theorems.Thm_HaarQuotient_lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer
import Theorems.Thm_WhittakerBlock_isHaarMeasure_unipotentHaar3
import Theorems.Thm_WhittakerBlock_isMulRightInvariant_unipotentHaar3
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_one_le_and_lintegral_quotientMeasure_eq_mul_whittakerBlock
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicHaar LanglandsTunnell.CubicInduction MeasureTheory
open scoped ENNReal

noncomputable section

namespace ShellPeeling

private abbrev evalHom (q : HeightOneSpectrum (𝓞 ℚ)) : AdeleRing (𝓞 ℚ) ℚ →+* q.adicCompletion ℚ :=
  (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ q).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

private theorem coe_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    ((localToAdelic3 p x : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ p (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) :=
  rfl

private theorem coe_componentAt3 (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((componentAt3 (𝓞 ℚ) ℚ q g : GL (Fin 3) (q.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) =
      (evalHom q).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_archComponent3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem componentAt3_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ p (localToAdelic3 p x) = x := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3]
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, finMatN, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_self]

private theorem componentAt3_localToAdelic3_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ q (localToAdelic3 p x) = 1 := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3, Units.val_one]
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, finMatN, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ i j hq]

private theorem archComponent3_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 p x) = 1 := by
  apply Units.ext
  rw [coe_archComponent3, coe_localToAdelic3, mapMatrix_arch_finMatN, Units.val_one]

private theorem ext_of_components {g h : AdelicGL 3 (𝓞 ℚ) ℚ}
    (harch : archComponent3 (𝓞 ℚ) ℚ g = archComponent3 (𝓞 ℚ) ℚ h)
    (hfin : ∀ q : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ q g = componentAt3 (𝓞 ℚ) ℚ q h) : g = h := by
  apply Units.ext
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · have h₁ := congrArg Units.val harch
    rwa [coe_archComponent3, coe_archComponent3] at h₁
  · refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_
    have h₂ := congrArg Units.val (hfin w)
    rw [coe_componentAt3, coe_componentAt3] at h₂
    ext i j
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun h₂ i) j

private theorem commute_localToAdelic3 {p : HeightOneSpectrum (𝓞 ℚ)} {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : componentAt3 (𝓞 ℚ) ℚ p g = 1) (x : LocalGL3 p) :
    g * localToAdelic3 p x = localToAdelic3 p x * g := by
  refine ext_of_components ?_ fun q => ?_
  · rw [map_mul, map_mul, archComponent3_localToAdelic3, mul_one, one_mul]
  · by_cases hq : q = p
    · subst hq
      rw [map_mul, map_mul, hg, one_mul, mul_one]
    · rw [map_mul, map_mul, componentAt3_localToAdelic3_of_ne hq, mul_one, one_mul]

private def awayPart (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  g * (localToAdelic3 p (componentAt3 (𝓞 ℚ) ℚ p g))⁻¹

private theorem componentAt3_awayPart (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ p (awayPart p g) = 1 := by
  rw [awayPart, map_mul, map_inv, componentAt3_localToAdelic3, mul_inv_cancel]

private theorem awayPart_mul_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    awayPart p g * localToAdelic3 p (componentAt3 (𝓞 ℚ) ℚ p g) = g :=
  inv_mul_cancel_right g _

private theorem awayPart_commute (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (x : LocalGL3 p) :
    awayPart p g * localToAdelic3 p x = localToAdelic3 p x * awayPart p g :=
  commute_localToAdelic3 (componentAt3_awayPart p g) x

private theorem map_upperUnipotent3 {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x y z : A) :
    Matrix.GeneralLinearGroup.map f (upperUnipotent3 x y z) = upperUnipotent3 (f x) (f y) (f z) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply, upperUnipotent3_coe]

private def adeleAt (p : HeightOneSpectrum (𝓞 ℚ)) (a : p.adicCompletion ℚ) : AdeleRing (𝓞 ℚ) ℚ :=
  ((0 : InfiniteAdeleRing ℚ), AdelicDock.splice (𝓞 ℚ) ℚ p 0 a)

private theorem adeleArch_adeleAt (p : HeightOneSpectrum (𝓞 ℚ)) (a : p.adicCompletion ℚ) :
    AdelicLevel.adeleArch (𝓞 ℚ) ℚ (adeleAt p a) = 0 :=
  rfl

private theorem eval_adeleAt_self (p : HeightOneSpectrum (𝓞 ℚ)) (a : p.adicCompletion ℚ) :
    evalHom p (adeleAt p a) = a := by
  simp [evalHom, adeleAt, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply]

private theorem eval_adeleAt_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (a : p.adicCompletion ℚ) :
    evalHom q (adeleAt p a) = 0 := by
  simp [evalHom, adeleAt, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
    AdelicDock.splice_apply_of_ne (𝓞 ℚ) ℚ p _ _ hq]
  rfl

private theorem localToAdelic3_upperUnipotent3 (p : HeightOneSpectrum (𝓞 ℚ)) (x y z : p.adicCompletion ℚ) :
    localToAdelic3 p (upperUnipotent3 x y z) = upperUnipotent3 (adeleAt p x) (adeleAt p y) (adeleAt p z) := by
  refine ext_of_components ?_ fun q => ?_
  · rw [archComponent3_localToAdelic3]
    exact (map_upperUnipotent3 (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) _ _ _).trans (by
      rw [adeleArch_adeleAt, adeleArch_adeleAt, adeleArch_adeleAt, upperUnipotent3_zero]) |>.symm
  · by_cases hq : q = p
    · subst hq
      rw [componentAt3_localToAdelic3]
      exact (map_upperUnipotent3 (evalHom q) _ _ _).trans (by simp only [eval_adeleAt_self]) |>.symm
    · rw [componentAt3_localToAdelic3_of_ne hq]
      exact (map_upperUnipotent3 (evalHom q) _ _ _).trans
        (by simp only [eval_adeleAt_of_ne hq, upperUnipotent3_zero]) |>.symm

private theorem localToAdelic3_upperUnipotent3_mem (p : HeightOneSpectrum (𝓞 ℚ)) (x y z : p.adicCompletion ℚ) :
    localToAdelic3 p (upperUnipotent3 x y z) ∈ WhittakerBlock.unipotentSubgroup3 :=
  (WhittakerBlock.mem_unipotentSubgroup3_iff _).2 ⟨_, _, _, localToAdelic3_upperUnipotent3 p x y z⟩

private theorem diagonal_mul_upperUnipotent3_mul_diagonal_inv {A : Type} [CommRing A] (d : Fin 3 → Aˣ) (x y z : A) :
    Matrix.diagonal (fun i => (d i : A)) * (upperUnipotent3 x y z : Matrix (Fin 3) (Fin 3) A) *
        Matrix.diagonal (fun i => (((d i)⁻¹ : Aˣ) : A)) =
      (upperUnipotent3 (d 0 * x * ((d 1)⁻¹ : Aˣ)) (d 1 * y * ((d 2)⁻¹ : Aˣ)) (d 0 * z * ((d 2)⁻¹ : Aˣ)) :
        Matrix (Fin 3) (Fin 3) A) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

section LocalShells

variable (p : HeightOneSpectrum (𝓞 ℚ))

private def localDiag (v : ℤ × ℤ × ℤ) : LocalGL3 p :=
  iotaGL (diagUnits2 (ratPrimeUnit p ^ (v.1 - v.2.2)) (ratPrimeUnit p ^ (v.2.1 - v.2.2))) *
    Matrix.GeneralLinearGroup.scalar (Fin 3) (ratPrimeUnit p ^ v.2.2)

private def IsUnip (n : LocalGL3 p) : Prop :=
  ∃ x y z : p.adicCompletion ℚ, n = upperUnipotent3 x y z

private def InShell (v : ℤ × ℤ × ℤ) (g : LocalGL3 p) : Prop :=
  ∃ n k : LocalGL3 p, IsUnip p n ∧ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ g = n * localDiag p v * k

private theorem valued_natCast_eq_intValuation (n : ℕ) :
    Valued.v ((n : ℕ) : p.adicCompletion ℚ) = p.intValuation (n : 𝓞 ℚ) := by
  rw [← map_natCast (algebraMap ℚ (p.adicCompletion ℚ)) n, ← map_natCast (algebraMap (𝓞 ℚ) ℚ) n]
  exact AdelicLevel.valued_algebraMap p (n : 𝓞 ℚ)

private theorem absNorm_span_intCast (z : ℤ) : Ideal.absNorm (Ideal.span {(z : 𝓞 ℚ)}) = z.natAbs := by
  rw [Ideal.absNorm_span_singleton, ← eq_intCast (algebraMap ℤ (𝓞 ℚ)) z, Algebra.norm_algebraMap,
    NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]

private theorem absNorm_span_natCast (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  simpa using absNorm_span_intCast (n : ℤ)

private theorem intValuation_absNorm :
    p.intValuation (Ideal.absNorm p.asIdeal : 𝓞 ℚ) = WithZero.exp (-1 : ℤ) := by
  have hN : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hmem : ((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 ℚ) ∈ p.asIdeal := Ideal.absNorm_mem p.asIdeal
  have h1 : p.intValuation ((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, pow_one]
    exact hmem
  have h2 : ¬ p.intValuation ((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]
    intro hmem2
    have hle : Ideal.span {((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 ℚ)} ≤ p.asIdeal ^ 2 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hmem2
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [map_pow, absNorm_span_natCast] at hdvd
    have hle' := Nat.le_of_dvd (by omega) hdvd
    nlinarith
  have hr : ((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 ℚ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, p.intValuation ((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 ℚ) = WithZero.exp (-(c : ℤ)) :=
    ⟨_, p.intValuation_if_neg hr⟩
  rw [hc, WithZero.exp_le_exp] at h1 h2
  rw [hc]
  congr 1
  omega

private theorem valued_ratPrimeUnit :
    Valued.v ((ratPrimeUnit p : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  show Valued.v ((Ideal.absNorm p.asIdeal : ℕ) : p.adicCompletion ℚ) = _
  rw [valued_natCast_eq_intValuation, intValuation_absNorm]

private theorem valued_ratPrimeUnit_zpow (a : ℤ) :
    Valued.v ((ratPrimeUnit p ^ a : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = WithZero.exp (-a) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_ratPrimeUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem coe_localDiag (v : ℤ × ℤ × ℤ) :
    ((localDiag p v : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      Matrix.diagonal ![((ratPrimeUnit p ^ v.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ),
        ((ratPrimeUnit p ^ v.2.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ),
        ((ratPrimeUnit p ^ v.2.2 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)] := by
  have hz : ∀ a b : ℤ, ratPrimeUnit p ^ a = ratPrimeUnit p ^ (a - b) * ratPrimeUnit p ^ b := fun a b => by
    rw [← zpow_add, sub_add_cancel]
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin 3) (ratPrimeUnit p ^ v.2.2) : LocalGL3 p) :
        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      Matrix.scalar (Fin 3) (↑(ratPrimeUnit p ^ v.2.2) : p.adicCompletion ℚ) := rfl
  rw [hz v.1 v.2.2, hz v.2.1 v.2.2, localDiag, Units.val_mul, coe_iotaGL, coe_diagUnits2, hs, Matrix.scalar_apply]
  ext i j
  rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

private theorem localDiag_zero : localDiag p 0 = 1 := by
  apply Units.ext
  rw [coe_localDiag, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem isUnip_one : IsUnip p 1 := by
  exact ⟨0, 0, 0, upperUnipotent3_zero.symm⟩

private theorem isUnip_mul {n n' : LocalGL3 p} (hn : IsUnip p n) (hn' : IsUnip p n') : IsUnip p (n * n') := by
  obtain ⟨x, y, z, rfl⟩ := hn
  obtain ⟨x', y', z', rfl⟩ := hn'
  refine ⟨x' + x, y' + y, z' + x * y' + z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem isUnip_inv {n : LocalGL3 p} (hn : IsUnip p n) : IsUnip p n⁻¹ := by
  obtain ⟨x, y, z, rfl⟩ := hn
  exact ⟨-x, -y, x * y - z, Units.ext rfl⟩

private theorem bottomRow_unip_mul {n : LocalGL3 p} (hn : IsUnip p n) (g : LocalGL3 p) (j : Fin 3) :
    ((n * g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j =
      (g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j := by
  obtain ⟨x, y, z, rfl⟩ := hn
  simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem valuation_bottomRow_le {k : LocalGL3 p} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) (j : Fin 3) :
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j) ≤ 1 := by
  exact hk.1 2 j

private theorem exists_valuation_bottomRow_eq_one {k : LocalGL3 p} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    ∃ j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j) = 1 := by
  by_contra hcon
  have hlt : ∀ l : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l) < 1 := fun l =>
    lt_of_le_of_ne (hk.1 2 l) fun h => hcon ⟨l, h⟩
  have hterm : ∀ l : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 l *
      ((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) l 2) < 1 := fun l => by
    rw [map_mul]
    exact (mul_le_mul_right (hk.2 l 2) _).trans_lt (by rw [mul_one]; exact hlt l)
  have h1 : ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) *
      ((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) 2 2 = 1 := by
    rw [Units.mul_inv, Matrix.one_apply_eq]
  have h2 : Valued.v (((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) *
      ((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) 2 2) < 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    exact Valuation.map_add_lt _ (Valuation.map_add_lt _ (hterm 0) (hterm 1)) (hterm 2)
  rw [h1, map_one] at h2
  exact lt_irrefl _ h2

private theorem isUnip_localDiag_conj (v : ℤ × ℤ × ℤ) {n : LocalGL3 p} (hn : IsUnip p n) :
    IsUnip p (localDiag p v * n * (localDiag p v)⁻¹) := by
  obtain ⟨x, y, z, rfl⟩ := hn
  refine ⟨(↑(ratPrimeUnit p ^ v.1) : p.adicCompletion ℚ) * x * (↑((ratPrimeUnit p ^ v.2.1)⁻¹) : p.adicCompletion ℚ),
    (↑(ratPrimeUnit p ^ v.2.1) : p.adicCompletion ℚ) * y * (↑((ratPrimeUnit p ^ v.2.2)⁻¹) : p.adicCompletion ℚ),
    (↑(ratPrimeUnit p ^ v.1) : p.adicCompletion ℚ) * z * (↑((ratPrimeUnit p ^ v.2.2)⁻¹) : p.adicCompletion ℚ), ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_localDiag, -Units.val_zpow_eq_zpow_val]

private theorem isUnip_localDiag_inv_conj (v : ℤ × ℤ × ℤ) {n : LocalGL3 p} (hn : IsUnip p n) :
    IsUnip p ((localDiag p v)⁻¹ * n * localDiag p v) := by
  obtain ⟨x, y, z, rfl⟩ := hn
  refine ⟨(↑((ratPrimeUnit p ^ v.1)⁻¹) : p.adicCompletion ℚ) * (x * (↑(ratPrimeUnit p ^ v.2.1) : p.adicCompletion ℚ)),
    (↑((ratPrimeUnit p ^ v.2.1)⁻¹) : p.adicCompletion ℚ) * (y * (↑(ratPrimeUnit p ^ v.2.2) : p.adicCompletion ℚ)),
    (↑((ratPrimeUnit p ^ v.1)⁻¹) : p.adicCompletion ℚ) * (z * (↑(ratPrimeUnit p ^ v.2.2) : p.adicCompletion ℚ)), ?_⟩
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_localDiag, -Units.val_zpow_eq_zpow_val]

private theorem inShell_iff_inShell_zero (v : ℤ × ℤ × ℤ) (g : LocalGL3 p) :
    InShell p v g ↔ InShell p 0 ((localDiag p v)⁻¹ * g) := by
  constructor
  · rintro ⟨n, k, hn, hk, rfl⟩
    refine ⟨(localDiag p v)⁻¹ * n * localDiag p v, k, isUnip_localDiag_inv_conj p v hn, hk, ?_⟩
    rw [localDiag_zero, mul_one]
    simp only [mul_assoc]
  · rintro ⟨n, k, hn, hk, h⟩
    rw [localDiag_zero, mul_one, inv_mul_eq_iff_eq_mul] at h
    refine ⟨localDiag p v * n * (localDiag p v)⁻¹, k, isUnip_localDiag_conj p v hn, hk, ?_⟩
    rw [h]
    group

private theorem inShell_unip_mul_iff {n : LocalGL3 p} (hn : IsUnip p n) (v : ℤ × ℤ × ℤ) (g : LocalGL3 p) :
    InShell p v (n * g) ↔ InShell p v g := by
  constructor
  · rintro ⟨n', k, hn', hk, h⟩
    refine ⟨n⁻¹ * n', k, isUnip_mul p (isUnip_inv p hn) hn', hk, ?_⟩
    calc g = n⁻¹ * (n * g) := (inv_mul_cancel_left n g).symm
      _ = n⁻¹ * (n' * localDiag p v * k) := by rw [h]
      _ = n⁻¹ * n' * localDiag p v * k := by simp only [mul_assoc]
  · rintro ⟨n', k, hn', hk, rfl⟩
    exact ⟨n * n', k, isUnip_mul p hn hn', hk, by simp only [mul_assoc]⟩

private theorem inShell_unique {v w : ℤ × ℤ × ℤ} {g : LocalGL3 p} (hv : InShell p v g) (hw : InShell p w g) :
    v = w := by
  have key : ∀ {v₁ v₂ : ℤ × ℤ × ℤ} {g₀ : LocalGL3 p}, InShell p v₁ g₀ → InShell p v₂ g₀ →
      v₁.1 ≤ v₂.1 ∧ v₁.2.1 ≤ v₂.2.1 ∧ v₁.2.2 ≤ v₂.2.2 := by
    intro v₁ v₂ g₀ h₁ h₂
    obtain ⟨n, k, hn, hk, rfl⟩ := h₁
    obtain ⟨n', k', hn', hk', h⟩ := h₂
    obtain ⟨x, y, z, hm⟩ := isUnip_mul p (isUnip_inv p hn) hn'
    obtain ⟨u, hu, hkey⟩ : ∃ u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
        localDiag p v₁ * u = upperUnipotent3 x y z * localDiag p v₂ := by
      refine ⟨k * k'⁻¹, mul_mem hk (inv_mem hk'), ?_⟩
      rw [← hm]
      calc localDiag p v₁ * (k * k'⁻¹) = n⁻¹ * (n * localDiag p v₁ * k) * k'⁻¹ := by group
        _ = n⁻¹ * (n' * localDiag p v₂ * k') * k'⁻¹ := by rw [h]
        _ = n⁻¹ * n' * localDiag p v₂ := by group
    have hle : ∀ (a b : ℤ) (t : p.adicCompletion ℚ), Valued.v t ≤ 1 →
        (↑(ratPrimeUnit p ^ a) : p.adicCompletion ℚ) * t = 1 * (↑(ratPrimeUnit p ^ b) : p.adicCompletion ℚ) →
        a ≤ b := by
      intro a b t ht hab
      have h' : Valued.v ((↑(ratPrimeUnit p ^ a) : p.adicCompletion ℚ) * t) =
          Valued.v (1 * (↑(ratPrimeUnit p ^ b) : p.adicCompletion ℚ)) := by
        rw [hab]
      rw [map_mul, map_mul, map_one, one_mul, valued_ratPrimeUnit_zpow, valued_ratPrimeUnit_zpow] at h'
      have h'' : WithZero.exp (-b) ≤ WithZero.exp (-a) := by
        rw [← h']
        calc WithZero.exp (-a) * Valued.v t ≤ WithZero.exp (-a) * 1 := mul_le_mul_right ht _
          _ = WithZero.exp (-a) := mul_one _
      rw [WithZero.exp_le_exp] at h''
      omega
    have h0 := congrArg (fun m : LocalGL3 p => (m : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 0 0) hkey
    have h1 := congrArg (fun m : LocalGL3 p => (m : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 1 1) hkey
    have h2 := congrArg (fun m : LocalGL3 p => (m : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 2) hkey
    simp only [Units.val_mul, coe_localDiag, Matrix.diagonal_mul, Matrix.mul_diagonal, upperUnipotent3_coe]
      at h0 h1 h2
    exact ⟨hle _ _ _ (hu.1 0 0) h0, hle _ _ _ (hu.1 1 1) h1, hle _ _ _ (hu.1 2 2) h2⟩
  obtain ⟨a₁, a₂, a₃⟩ := v
  obtain ⟨b₁, b₂, b₃⟩ := w
  obtain ⟨h₁, h₂, h₃⟩ := key hv hw
  obtain ⟨h₁', h₂', h₃'⟩ := key hw hv
  have e₁ : a₁ = b₁ := le_antisymm h₁ h₁'
  have e₂ : a₂ = b₂ := le_antisymm h₂ h₂'
  have e₃ : a₃ = b₃ := le_antisymm h₃ h₃'
  rw [e₁, e₂, e₃]

private theorem exists_inShell (g : LocalGL3 p) : ∃ v : ℤ × ℤ × ℤ, InShell p v g := by
  obtain ⟨x, y, z, t, d, k, hk, ht, hg⟩ :=
    exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 p g
  have hd : ∀ i, d i ≠ 0 := fun i => by
    have h : ((t : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) *
        ((t⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i i = 1 := by
      rw [Units.mul_inv, Matrix.one_apply_eq]
    rw [ht, Matrix.diagonal_mul] at h
    exact left_ne_zero_of_mul_eq_one h
  have hexp : ∀ i, ∃ a : ℤ, Valued.v (d i) = WithZero.exp (-a) := fun i =>
    ⟨-WithZero.log (Valued.v (d i)), by rw [neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff Valued.v).mpr (hd i))]⟩
  choose a ha using hexp
  obtain ⟨e, he_def⟩ :
      ∃ e : Fin 3 → p.adicCompletion ℚ, ∀ i, e i = d i * (↑(ratPrimeUnit p ^ (-a i)) : p.adicCompletion ℚ) :=
    ⟨fun i => d i * (↑(ratPrimeUnit p ^ (-a i)) : p.adicCompletion ℚ), fun _ => rfl⟩
  have he : ∀ i, Valued.v (e i) = 1 := fun i => by
    rw [he_def, map_mul, ha, valued_ratPrimeUnit_zpow, neg_neg, ← WithZero.exp_add, (by omega : -a i + a i = 0),
      WithZero.exp_zero]
  have he0 : ∀ i, e i ≠ 0 := fun i => (Valuation.ne_zero_iff Valued.v).mp (by rw [he i]; exact one_ne_zero)
  have hgen : ∀ i, d i = (↑(ratPrimeUnit p ^ a i) : p.adicCompletion ℚ) * e i := fun i => by
    rw [he_def, mul_left_comm, ← Units.val_mul, ← zpow_add, (by omega : a i + -a i = 0), zpow_zero, Units.val_one,
      mul_one]
  have hval : Matrix.diagonal e * Matrix.diagonal (fun i => (e i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (he0 i)
  have hinv : Matrix.diagonal (fun i => (e i)⁻¹) * Matrix.diagonal e = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (he0 i)
  have hentry : ∀ f : Fin 3 → p.adicCompletion ℚ, (∀ i, Valued.v (f i) ≤ 1) →
      ∀ i j : Fin 3, Valued.v (Matrix.diagonal f i j) ≤ 1 := fun f hf i j => by
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      exact hf _
    · rw [Matrix.diagonal_apply_ne _ hij, map_zero]
      exact zero_le
  obtain ⟨k₀, hk₀, hk₀val⟩ : ∃ k₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
      (k₀ : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) = Matrix.diagonal e :=
    ⟨⟨Matrix.diagonal e, Matrix.diagonal (fun i => (e i)⁻¹), hval, hinv⟩,
      (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ p).mpr
        ⟨hentry e (fun i => (he i).le), hentry (fun i => (e i)⁻¹) (fun i => by
          show Valued.v (e i)⁻¹ ≤ 1
          rw [map_inv₀, he i, inv_one])⟩, rfl⟩
  refine ⟨(a 0, a 1, a 2), upperUnipotent3 x y z, k₀ * k, ⟨x, y, z, rfl⟩, mul_mem hk₀ hk, ?_⟩
  have ht' : t = localDiag p (a 0, a 1, a 2) * k₀ := by
    apply Units.ext
    rw [Units.val_mul, coe_localDiag, hk₀val, ht, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> exact hgen _
  rw [hg, ht']
  simp only [mul_assoc]

private theorem isOpen_localMaximalCompact3 : IsOpen ((localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p))) := by
  have hpre : ∀ f : LocalGL3 p → p.adicCompletion ℚ, Continuous f → IsOpen {k : LocalGL3 p | Valued.v (f k) ≤ 1} :=
    fun f hf => by
      simpa [Set.preimage, Valuation.mem_integer_iff] using (Valued.isOpen_integer (p.adicCompletion ℚ)).preimage hf
  have hK : (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p)) =
      (⋂ i, ⋂ j, {k : LocalGL3 p | Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1}) ∩
        ⋂ i, ⋂ j, {k : LocalGL3 p |
          Valued.v (((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1} := by
    ext k
    simp only [SetLike.mem_coe, mem_localMaximalCompact3_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hK]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hpre _ (Units.continuous_val.matrix_elem i j)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hpre _ (Units.continuous_coe_inv.matrix_elem i j))

private theorem isOpen_setOf_inShell (v : ℤ × ℤ × ℤ) : IsOpen {g : LocalGL3 p | InShell p v g} := by
  have hset : {g : LocalGL3 p | InShell p v g} = ⋃ n ∈ {n : LocalGL3 p | IsUnip p n},
      (fun k : LocalGL3 p => n * localDiag p v * k) '' (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p)) := by
    ext g
    constructor
    · rintro ⟨n, k, hn, hk, rfl⟩
      exact Set.mem_iUnion₂.mpr ⟨n, hn, k, hk, rfl⟩
    · intro hg
      obtain ⟨n, hn, k, hk, rfl⟩ := Set.mem_iUnion₂.mp hg
      exact ⟨n, k, hn, hk, rfl⟩
  rw [hset]
  exact isOpen_biUnion fun n _ => isOpenMap_mul_left (n * localDiag p v) _ (isOpen_localMaximalCompact3 p)

private theorem zpow_mul_mem_adicCompletionIntegers {γ : ℤ} (hγ : 0 ≤ γ) {x : p.adicCompletion ℚ}
    (hx : Valued.v x ≤ 1) :
    ((ratPrimeUnit p ^ γ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * x ∈ p.adicCompletionIntegers ℚ := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, valued_ratPrimeUnit_zpow]
  refine mul_le_one' ?_ hx
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

private theorem zpow_mul_notMem_adicCompletionIntegers {γ : ℤ} (hγ : γ < 0) {x : p.adicCompletion ℚ}
    (hx : Valued.v x = 1) :
    ((ratPrimeUnit p ^ γ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * x ∉ p.adicCompletionIntegers ℚ := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, valued_ratPrimeUnit_zpow, hx, mul_one,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

end LocalShells

private def ideleAt (p : HeightOneSpectrum (𝓞 ℚ)) : (p.adicCompletion ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ)).comp (AdelicLevel.localUnit (𝓞 ℚ) ℚ p)

private theorem adeleArch_ideleAt (p : HeightOneSpectrum (𝓞 ℚ)) (u : (p.adicCompletion ℚ)ˣ) :
    AdelicLevel.adeleArch (𝓞 ℚ) ℚ (ideleAt p u : AdeleRing (𝓞 ℚ) ℚ) = 1 := by
  simp [ideleAt, AdelicLevel.adeleArch_apply, AdelicLevel.finIncl_apply_fst]

private theorem evalHom_ideleAt_self (p : HeightOneSpectrum (𝓞 ℚ)) (u : (p.adicCompletion ℚ)ˣ) :
    evalHom p (ideleAt p u : AdeleRing (𝓞 ℚ) ℚ) = u := by
  simp [evalHom, ideleAt, AdelicLevel.adeleFin_apply, AdelicLevel.finIncl_apply_snd, AdelicLevel.finAdeleEval_apply,
    AdelicLevel.localUnit_apply_self]

private theorem evalHom_ideleAt_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (u : (p.adicCompletion ℚ)ˣ) :
    evalHom q (ideleAt p u : AdeleRing (𝓞 ℚ) ℚ) = 1 := by
  simp [evalHom, ideleAt, AdelicLevel.adeleFin_apply, AdelicLevel.finIncl_apply_snd, AdelicLevel.finAdeleEval_apply,
    AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ p u hq]

private theorem unitsMap_arch_ideleAt (p : HeightOneSpectrum (𝓞 ℚ)) (u : (p.adicCompletion ℚ)ˣ) :
    Units.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ : AdeleRing (𝓞 ℚ) ℚ →* InfiniteAdeleRing ℚ) (ideleAt p u) = 1 :=
  Units.ext (by simp [adeleArch_ideleAt])

private theorem unitsMap_evalHom_ideleAt_self (p : HeightOneSpectrum (𝓞 ℚ)) (u : (p.adicCompletion ℚ)ˣ) :
    Units.map (evalHom p : AdeleRing (𝓞 ℚ) ℚ →* p.adicCompletion ℚ) (ideleAt p u) = u :=
  Units.ext (by simp [evalHom_ideleAt_self])

private theorem unitsMap_evalHom_ideleAt_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p)
    (u : (p.adicCompletion ℚ)ˣ) :
    Units.map (evalHom q : AdeleRing (𝓞 ℚ) ℚ →* q.adicCompletion ℚ) (ideleAt p u) = 1 :=
  Units.ext (by simp [evalHom_ideleAt_of_ne hq])

private theorem map_scalar {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 3) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (f : A →* B) u) := by
  apply Units.ext
  ext i j
  by_cases hij : i = j <;>
    simp [Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, hij]

private def diagGL {A : Type} [CommRing A] (d : Fin 3 → Aˣ) : GL (Fin 3) A where
  val := Matrix.diagonal fun i => (d i : A)
  inv := Matrix.diagonal fun i => ((d i)⁻¹ : Aˣ)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp

private theorem coe_diagGL {A : Type} [CommRing A] (d : Fin 3 → Aˣ) :
    ((diagGL d : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal fun i => (d i : A) :=
  rfl

private theorem diagGL_one {A : Type} [CommRing A] : diagGL (fun _ : Fin 3 => (1 : Aˣ)) = 1 :=
  Units.ext (by simp [coe_diagGL])

private theorem map_diagGL {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (d : Fin 3 → Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagGL d) = diagGL fun i => Units.map (f : A →* B) (d i) := by
  apply Units.ext
  ext i j
  by_cases hij : i = j <;>
    simp [Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply, coe_diagGL, Matrix.diagonal_apply,
      hij]

private theorem centralScalarGL_comm (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    centralScalarGL 3 (𝓞 ℚ) ℚ z * g = g * centralScalarGL 3 (𝓞 ℚ) ℚ z :=
  Units.ext (Matrix.scalar_commute (z : AdeleRing (𝓞 ℚ) ℚ) (fun r => Commute.all _ r) _)

private theorem componentAt3_centralScalarGL (q : HeightOneSpectrum (𝓞 ℚ)) (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    componentAt3 (𝓞 ℚ) ℚ q (centralScalarGL 3 (𝓞 ℚ) ℚ z) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (evalHom q : AdeleRing (𝓞 ℚ) ℚ →* q.adicCompletion ℚ) z) :=
  map_scalar (evalHom q) z

private theorem archComponent3_centralScalarGL (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    archComponent3 (𝓞 ℚ) ℚ (centralScalarGL 3 (𝓞 ℚ) ℚ z) =
      Matrix.GeneralLinearGroup.scalar (Fin 3)
        (Units.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ : AdeleRing (𝓞 ℚ) ℚ →* InfiniteAdeleRing ℚ) z) :=
  map_scalar (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) z

private theorem diagUnits2_one_one {A : Type} [CommRing A] : diagUnits2 (1 : Aˣ) 1 = 1 := by
  apply Units.ext
  rw [coe_diagUnits2, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private def torus (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  localToAdelic3 p (iotaGL (diagUnits2 (ratPrimeUnit p ^ (v.1 - v.2.2)) (ratPrimeUnit p ^ (v.2.1 - v.2.2)))) *
    centralScalarGL 3 (𝓞 ℚ) ℚ (ideleAt p (ratPrimeUnit p ^ v.2.2))

private theorem componentAt3_torus (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) :
    componentAt3 (𝓞 ℚ) ℚ p (torus p v) = localDiag p v := by
  rw [torus, map_mul, componentAt3_localToAdelic3, componentAt3_centralScalarGL, unitsMap_evalHom_ideleAt_self]
  rfl

private theorem componentAt3_torus_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (v : ℤ × ℤ × ℤ) :
    componentAt3 (𝓞 ℚ) ℚ q (torus p v) = 1 := by
  rw [torus, map_mul, componentAt3_localToAdelic3_of_ne hq, componentAt3_centralScalarGL,
    unitsMap_evalHom_ideleAt_of_ne hq, map_one, one_mul]

private theorem archComponent3_torus (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) :
    archComponent3 (𝓞 ℚ) ℚ (torus p v) = 1 := by
  rw [torus, map_mul, archComponent3_localToAdelic3, archComponent3_centralScalarGL, unitsMap_arch_ideleAt, map_one,
    one_mul]

private theorem torus_zero (p : HeightOneSpectrum (𝓞 ℚ)) : torus p 0 = 1 := by
  simp only [torus, Prod.fst_zero, Prod.snd_zero, sub_zero, zpow_zero, diagUnits2_one_one, map_one, one_mul]

private def torusIdeles (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  ![ideleAt p (ratPrimeUnit p ^ v.1), ideleAt p (ratPrimeUnit p ^ v.2.1), ideleAt p (ratPrimeUnit p ^ v.2.2)]

private theorem localDiag_eq_diagGL (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) :
    localDiag p v = diagGL ![ratPrimeUnit p ^ v.1, ratPrimeUnit p ^ v.2.1, ratPrimeUnit p ^ v.2.2] := by
  apply Units.ext
  rw [coe_localDiag, coe_diagGL]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem torus_eq_diagGL (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) :
    torus p v = diagGL (torusIdeles p v) := by
  refine ext_of_components ?_ fun q => ?_
  · rw [archComponent3_torus]
    show _ = Matrix.GeneralLinearGroup.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) (diagGL (torusIdeles p v))
    rw [map_diagGL]
    refine (diagGL_one.symm.trans (congrArg diagGL ?_))
    funext i
    fin_cases i <;> simp [torusIdeles, unitsMap_arch_ideleAt]
  · show _ = Matrix.GeneralLinearGroup.map (evalHom q) (diagGL (torusIdeles p v))
    rw [map_diagGL]
    by_cases hq : q = p
    · subst hq
      rw [componentAt3_torus, localDiag_eq_diagGL]
      congr 1
      funext i
      fin_cases i <;> simp [torusIdeles, unitsMap_evalHom_ideleAt_self]
    · rw [componentAt3_torus_of_ne hq]
      refine (diagGL_one.symm.trans (congrArg diagGL ?_))
      funext i
      fin_cases i <;> simp [torusIdeles, unitsMap_evalHom_ideleAt_of_ne hq]

private theorem coe_torus (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) :
    ((torus p v : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      Matrix.diagonal fun i => (torusIdeles p v i : AdeleRing (𝓞 ℚ) ℚ) := by
  rw [torus_eq_diagGL, coe_diagGL]

private theorem torus_mul_apply_two (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (j : Fin 3) :
    ((torus p v * g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j =
      (ideleAt p (ratPrimeUnit p ^ v.2.2) : AdeleRing (𝓞 ℚ) ℚ) *
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j := by
  rw [Units.val_mul, coe_torus, Matrix.diagonal_mul]
  rfl

private theorem det_torus (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) :
    Matrix.GeneralLinearGroup.det (torus p v) =
      ideleAt p (ratPrimeUnit p ^ v.1) * ideleAt p (ratPrimeUnit p ^ v.2.1) * ideleAt p (ratPrimeUnit p ^ v.2.2) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_torus, Matrix.det_diagonal, Fin.prod_univ_three]
  rfl

section Cosets

variable {G : Type} [Group G] (H : Subgroup G)

private theorem exists_mem_mul_eq_out (g : G) :
    ∃ n ∈ H, n * g = (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out := by
  have h : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out ∈ MulAction.orbit H g := by
    rw [← MulAction.orbitRel.Quotient.orbit_mk]
    exact MulAction.orbitRel.Quotient.mem_orbit.2 (Quotient.out_eq' _)
  obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.1 h
  exact ⟨n, n.2, hn⟩

variable {H}

private theorem prop_out_mk_iff {P : G → Prop} (hinv : ∀ n ∈ H, ∀ g, P (n * g) ↔ P g) (g : G) :
    P (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out ↔ P g := by
  obtain ⟨n, hn, h⟩ := exists_mem_mul_eq_out H g
  rw [← h, hinv n hn]

private theorem measurableSet_setOf_out [MeasurableSpace G] {P : G → Prop} (hP : MeasurableSet {g | P g})
    (hinv : ∀ n ∈ H, ∀ g, P (n * g) ↔ P g) : MeasurableSet {q : MulAction.orbitRel.Quotient H G | P q.out} := by
  rw [measurableSet_quotient]
  convert hP using 1
  all_goals try rfl
  ext g
  exact prop_out_mk_iff hinv g

private theorem lintegral_indicator_out [MeasurableSpace G] {P : G → Prop} (hP : MeasurableSet {g | P g})
    (hinv : ∀ n ∈ H, ∀ g, P (n * g) ↔ P g) (F : G → ℝ≥0∞) (ν : Measure (MulAction.orbitRel.Quotient H G)) :
    ∫⁻ q, {g | P g}.indicator F q.out ∂ν = ∫⁻ q in {q : MulAction.orbitRel.Quotient H G | P q.out}, F q.out ∂ν := by
  rw [← lintegral_indicator (measurableSet_setOf_out hP hinv) (fun q => F q.out)]
  refine lintegral_congr fun q => ?_
  by_cases hq : P q.out <;> simp [hq]

private theorem indicator_mul_left_eq {P : G → Prop} (hinv : ∀ n ∈ H, ∀ g, P (n * g) ↔ P g) {F : G → ℝ≥0∞}
    (hF : ∀ n ∈ H, ∀ g, F (n * g) = F g) (n : G) (hn : n ∈ H) (g : G) :
    {g | P g}.indicator F (n * g) = {g | P g}.indicator F g := by
  by_cases hg : P g
  · have hng : P (n * g) := (hinv n hn g).2 hg
    simp [hg, hng, hF n hn g]
  · have hng : ¬ P (n * g) := fun h => hg ((hinv n hn g).1 h)
    simp [hg, hng]

end Cosets

private theorem continuous_evalHom (q : HeightOneSpectrum (𝓞 ℚ)) : Continuous (evalHom q) :=
  (AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ q).comp continuous_snd

private theorem continuous_componentAt3 (q : HeightOneSpectrum (𝓞 ℚ)) : Continuous (componentAt3 (𝓞 ℚ) ℚ q) :=
  Continuous.units_map _ ((continuous_id.matrix_map (continuous_evalHom q)) :
    Continuous fun m : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) => m.map (evalHom q))

private theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 ℚ)) :=
  Countable.of_equiv _ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm

private theorem isUnip_componentAt3_of_mem {n : AdelicGL 3 (𝓞 ℚ) ℚ} (hn : n ∈ WhittakerBlock.unipotentSubgroup3)
    (p : HeightOneSpectrum (𝓞 ℚ)) : IsUnip p (componentAt3 (𝓞 ℚ) ℚ p n) := by
  obtain ⟨x, y, z, rfl⟩ := (WhittakerBlock.mem_unipotentSubgroup3_iff n).1 hn
  exact ⟨_, _, _, map_upperUnipotent3 (evalHom p) x y z⟩

attribute [local instance] NumberField.AdelicHaar.glBorel in

private theorem measurableSet_local {p : HeightOneSpectrum (𝓞 ℚ)} {Q : LocalGL3 p → Prop} (hQ : IsOpen {x | Q x}) :
    MeasurableSet {g : AdelicGL 3 (𝓞 ℚ) ℚ | Q (componentAt3 (𝓞 ℚ) ℚ p g)} := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  exact (hQ.preimage (continuous_componentAt3 p)).measurableSet

attribute [local instance] NumberField.AdelicHaar.glBorel in

private theorem measurableSet_forall_notMem (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Q : ∀ p : HeightOneSpectrum (𝓞 ℚ), LocalGL3 p → Prop) (hQ : ∀ p, IsOpen {x | Q p x}) :
    MeasurableSet {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, p ∉ S → Q p (componentAt3 (𝓞 ℚ) ℚ p g)} := by
  haveI := countable_heightOneSpectrum
  have : {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, p ∉ S → Q p (componentAt3 (𝓞 ℚ) ℚ p g)} =
      ⋂ p, ⋂ (_ : p ∉ S), {g | Q p (componentAt3 (𝓞 ℚ) ℚ p g)} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => measurableSet_local (hQ p)

private theorem local_mul_iff {p : HeightOneSpectrum (𝓞 ℚ)} {Q : LocalGL3 p → Prop}
    (hQ : ∀ n, IsUnip p n → ∀ x, Q (n * x) ↔ Q x) (n : AdelicGL 3 (𝓞 ℚ) ℚ) (hn : n ∈ WhittakerBlock.unipotentSubgroup3)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Q (componentAt3 (𝓞 ℚ) ℚ p (n * g)) ↔ Q (componentAt3 (𝓞 ℚ) ℚ p g) := by
  rw [map_mul]
  exact hQ _ (isUnip_componentAt3_of_mem hn p) _

private theorem forall_notMem_mul_iff (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Q : ∀ p : HeightOneSpectrum (𝓞 ℚ), LocalGL3 p → Prop) (hQ : ∀ p n, IsUnip p n → ∀ x, Q p (n * x) ↔ Q p x)
    (n : AdelicGL 3 (𝓞 ℚ) ℚ) (hn : n ∈ WhittakerBlock.unipotentSubgroup3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (∀ p, p ∉ S → Q p (componentAt3 (𝓞 ℚ) ℚ p (n * g))) ↔ ∀ p, p ∉ S → Q p (componentAt3 (𝓞 ℚ) ℚ p g) :=
  forall_congr' fun p => imp_congr_right fun _ => local_mul_iff (hQ p) n hn g

private def integrand (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℝ≥0∞ :=
  (‖W g‖₊ : ℝ≥0∞) ^ 2 * (‖Φ fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
    ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ)

private theorem continuous_coe_matrix :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  Units.continuous_val

private theorem continuous_bottomRow :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j :=
  continuous_pi fun j =>
    show Continuous ((fun r : Fin 3 → AdeleRing (𝓞 ℚ) ℚ => r j) ∘
        ((fun m : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) => m 2) ∘
          fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) from
      (continuous_apply j).comp ((continuous_apply (2 : Fin 3)).comp continuous_coe_matrix)

attribute [local instance] NumberField.AdelicHaar.glBorel in
private theorem measurable_integrand {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : Continuous W)
    {Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hΦ : Continuous Φ) (σ : ℝ) : Measurable (integrand W Φ σ) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  have h1 : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (‖W g‖₊ : ℝ≥0∞) :=
    ENNReal.continuous_coe.measurable.comp hW.nnnorm.measurable
  have h1sq : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (‖W g‖₊ : ℝ≥0∞) ^ 2 := by
    simpa only [sq] using h1.fun_mul h1
  have h2 : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      (‖Φ fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) :=
    ENNReal.continuous_coe.measurable.comp (hΦ.comp continuous_bottomRow).nnnorm.measurable
  have h3 : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    refine Continuous.rpow_const ((NumberField.TateGlobal.continuous_ideleNorm ℚ).comp
      Matrix.GeneralLinearGroup.continuous_det) fun g => Or.inl ?_
    exact (NumberField.TateGlobal.ideleNorm_pos _).ne'
  exact (h1sq.mul h2).mul h3

open scoped Classical in

private theorem continuous_of_mem_pureTensorSet {φ : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hφ : φ ∈ AdelicFourier.pureTensorSet ℚ) :
    Continuous φ := by
  obtain ⟨g, h, hh, -, rfl⟩ := hφ
  exact (g.continuous.comp ((AdelicBox.continuous_ringEquiv_mixedSpace (K := ℚ)).comp continuous_fst)).mul
    (hh.continuous.comp continuous_snd)

private theorem continuous_prod_of_pureTensors {Φc : Fin 3 → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hΦc : ∀ i, Φc i ∈ AdelicFourier.pureTensorSet ℚ) :
    Continuous fun x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ => ∏ i, Φc i (x i) :=
  continuous_finsetProd _ fun i _ => (continuous_of_mem_pureTensorSet (hΦc i)).comp (continuous_apply i)

private theorem upperUnipotent3_mul_apply_two {A : Type} [CommRing A] (x y z : A) (N : Matrix (Fin 3) (Fin 3) A)
    (j : Fin 3) : ((upperUnipotent3 x y z : GL (Fin 3) A) * N : Matrix (Fin 3) (Fin 3) A) 2 j = N 2 j := by
  simp [upperUnipotent3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem det_upperUnipotent3 {A : Type} [CommRing A] (x y z : A) :
    Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z : GL (Fin 3) A) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent3_coe, Units.val_one]
  simp [Matrix.det_fin_three]

private theorem integrand_mul_left {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hW : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g, ‖W (n * g)‖ = ‖W g‖) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (σ : ℝ) (n : AdelicGL 3 (𝓞 ℚ) ℚ) (hn : n ∈ WhittakerBlock.unipotentSubgroup3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    integrand W Φ σ (n * g) = integrand W Φ σ g := by
  obtain ⟨x, y, z, rfl⟩ := (WhittakerBlock.mem_unipotentSubgroup3_iff n).1 hn
  have h₁ : ‖W (upperUnipotent3 x y z * g)‖₊ = ‖W g‖₊ := NNReal.coe_injective (hW _ hn g)
  have h₂ : (fun j : Fin 3 => ((upperUnipotent3 x y z * g : AdelicGL 3 (𝓞 ℚ) ℚ) :
      Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) =
      fun j => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j := by
    funext j
    rw [Units.val_mul]
    exact upperUnipotent3_mul_apply_two x y z _ j
  simp only [integrand, h₁, h₂, map_mul, det_upperUnipotent3, one_mul]

section Combination

variable {n : ℕ} (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)

private def comb : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun x => ∑ i, c i * f (x * t i)

private theorem comb_def : comb c t f = fun x => ∑ i, c i * f (x * t i) := rfl

private theorem comb_continuous (hc : Continuous f) : Continuous (comb c t f) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (hc.comp (continuous_mul_const (t i)))

private theorem comb_aut
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : comb c t f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = comb c t f g := by
  simp only [comb, mul_assoc, haut]

private theorem comb_cen (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    comb c t f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * comb c t f g := by
  simp only [comb, mul_assoc, hcen, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

variable {c t f}

private theorem comb_isRightInvariant {p : HeightOneSpectrum (𝓞 ℚ)} (ht : ∀ i, componentAt3 (𝓞 ℚ) ℚ p (t i) = 1)
    (hK : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f) :
    IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) (comb c t f) := by
  intro g u hu
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hu
  simp only [comb]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← commute_localToAdelic3 (ht i) k, ← mul_assoc, hK (g * t i) _ (Subgroup.mem_map_of_mem _ hk)]

private theorem exists_eq_localToAdelic3_of_mem_doubleCoset {p : HeightOneSpectrum (𝓞 ℚ)} {gen : LocalGL3 p}
    {x : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hx : x ∈ HeckePair.doubleCoset ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p gen)) :
    ∃ y : LocalGL3 p, x = localToAdelic3 p y := by
  obtain ⟨u, hu, w, hw, rfl⟩ := HeckePair.mem_doubleCoset_iff.1 hx
  obtain ⟨k₁, -, rfl⟩ := Subgroup.mem_map.1 hu
  obtain ⟨k₂, -, rfl⟩ := Subgroup.mem_map.1 hw
  exact ⟨k₁ * gen * k₂, by rw [map_mul, map_mul]⟩

private theorem comb_isCosetEigenfunction {p : HeightOneSpectrum (𝓞 ℚ)} (ht : ∀ i, componentAt3 (𝓞 ℚ) ℚ p (t i) = 1)
    {gen : LocalGL3 p} {lam : ℂ}
    (hT : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) (localToAdelic3 p gen)
      f lam) :
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) (localToAdelic3 p gen)
      (comb c t f) lam := by
  intro ι _ reps hreps g
  have hcomm : ∀ i j, reps i * t j = t j * reps i := by
    intro i j
    obtain ⟨y, hy⟩ := exists_eq_localToAdelic3_of_mem_doubleCoset (hreps.mem_doubleCoset i)
    rw [hy]
    exact (commute_localToAdelic3 (ht j) y).symm
  show (∑ i, ∑ j, c j * f (g * reps i * t j)) = lam * ∑ j, c j * f (g * t j)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := hT ι reps hreps (g * t j)
  simp only [cosetSum] at h
  calc (∑ i, c j * f (g * reps i * t j)) = c j * ∑ i, f (g * t j * reps i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc g, hcomm i j, ← mul_assoc]
    _ = c j * (lam * f (g * t j)) := by rw [h]
    _ = lam * (c j * f (g * t j)) := by ring

end Combination

private theorem torus_eq_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) :
    torus p v = localToAdelic3 p (localDiag p v) := by
  refine ext_of_components ?_ fun q => ?_
  · rw [archComponent3_torus, archComponent3_localToAdelic3]
  · by_cases hq : q = p
    · subst hq
      rw [componentAt3_torus, componentAt3_localToAdelic3]
    · rw [componentAt3_torus_of_ne hq, componentAt3_localToAdelic3_of_ne hq]

private theorem localToAdelic3_scalar (p : HeightOneSpectrum (𝓞 ℚ)) (u : (p.adicCompletion ℚ)ˣ) :
    localToAdelic3 p (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = centralScalarGL 3 (𝓞 ℚ) ℚ (ideleAt p u) := by
  refine ext_of_components ?_ fun q => ?_
  · rw [archComponent3_localToAdelic3, archComponent3_centralScalarGL, unitsMap_arch_ideleAt, map_one]
  · by_cases hq : q = p
    · subst hq
      rw [componentAt3_localToAdelic3, componentAt3_centralScalarGL, unitsMap_evalHom_ideleAt_self]
    · rw [componentAt3_localToAdelic3_of_ne hq, componentAt3_centralScalarGL, unitsMap_evalHom_ideleAt_of_ne hq,
        map_one]

private theorem localToAdelic3_localDiag (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) :
    localToAdelic3 p (localDiag p v) =
      localToAdelic3 p (iotaGL (diagUnits2 (ratPrimeUnit p ^ (v.1 - v.2.2)) (ratPrimeUnit p ^ (v.2.1 - v.2.2)))) *
        centralScalarGL 3 (𝓞 ℚ) ℚ (ideleAt p (ratPrimeUnit p ^ v.2.2)) := by
  rw [localDiag, map_mul, localToAdelic3_scalar]

private abbrev pins0 : AutomorphicForm.CarrierPins ℚ :=
  AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)

private theorem whittaker3_mul_right {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {k : AdelicGL 3 (𝓞 ℚ) ℚ} (hf : ∀ h, f (h * k) = f h)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins0 NumberField.StandardAddChar.psiQ f (g * k) =
      whittaker3 pins0 NumberField.StandardAddChar.psiQ f g := by
  unfold whittaker3
  simp only [← mul_assoc, hf]

private theorem whittaker3_central_mul {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins0 NumberField.StandardAddChar.psiQ f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) =
      (ω z : ℂ) * whittaker3 pins0 NumberField.StandardAddChar.psiQ f g := by
  have key : ∀ x y w : AdeleRing (𝓞 ℚ) ℚ,
      f (upperUnipotent3 x y w * (centralScalarGL 3 (𝓞 ℚ) ℚ z * g)) = (ω z : ℂ) * f (upperUnipotent3 x y w * g) := by
    intro x y w
    rw [← mul_assoc, ← centralScalarGL_comm, mul_assoc, hcen]
  unfold whittaker3
  simp only [key, mul_assoc, MeasureTheory.integral_const_mul]

private def InZeroShellAt (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Prop :=
  ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k

private theorem norm_whittaker3_torus_mul {p : HeightOneSpectrum (𝓞 ℚ)}
    {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : ℤ × ℤ → ℂ)
    (hN : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖whittaker3 pins0 NumberField.StandardAddChar.psiQ f (n * g)‖ =
        ‖whittaker3 pins0 NumberField.StandardAddChar.psiQ f g‖)
    (hK : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (hE : ∀ (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ), (∀ x : LocalGL3 p, g₀ * localToAdelic3 p x = localToAdelic3 p x * g₀) →
      ∀ m : ℤ × ℤ,
        whittaker3 pins0 NumberField.StandardAddChar.psiQ f
            (g₀ * localToAdelic3 p (iotaGL (diagUnits2 (ratPrimeUnit p ^ m.1) (ratPrimeUnit p ^ m.2)))) =
          whittaker3 pins0 NumberField.StandardAddChar.psiQ f g₀ * u m)
    (v : ℤ × ℤ × ℤ) {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : InZeroShellAt p g) :
    ‖whittaker3 pins0 NumberField.StandardAddChar.psiQ f (torus p v * g)‖ =
      ‖u (v.1 - v.2.2, v.2.1 - v.2.2)‖ * ‖(ω (ideleAt p (ratPrimeUnit p ^ v.2.2)) : ℂ)‖ *
        ‖whittaker3 pins0 NumberField.StandardAddChar.psiQ f g‖ := by
  obtain ⟨x, y, z, k, hk, hcomp⟩ := hg
  have hfk : ∀ h, f (h * localToAdelic3 p k) = f h := fun h => hK h _ (Subgroup.mem_map_of_mem _ hk)

  obtain ⟨a, hac, hgeq⟩ : ∃ a : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ w : LocalGL3 p, a * localToAdelic3 p w = localToAdelic3 p w * a) ∧
        a * (localToAdelic3 p (upperUnipotent3 x y z) * localToAdelic3 p k) = g :=
    ⟨awayPart p g, awayPart_commute p g, by rw [← map_mul, ← hcomp, awayPart_mul_localToAdelic3]⟩
  subst hgeq

  have hWg : ‖whittaker3 pins0 NumberField.StandardAddChar.psiQ f
        (a * (localToAdelic3 p (upperUnipotent3 x y z) * localToAdelic3 p k))‖ =
      ‖whittaker3 pins0 NumberField.StandardAddChar.psiQ f a‖ := by
    rw [← mul_assoc, hac, mul_assoc, hN _ (localToAdelic3_upperUnipotent3_mem p x y z), whittaker3_mul_right hfk]

  obtain ⟨x', y', z', hn'⟩ := isUnip_localDiag_conj p v ⟨x, y, z, rfl⟩
  have hsplit : localDiag p v * (upperUnipotent3 x y z * k) = upperUnipotent3 x' y' z' * (localDiag p v * k) := by
    rw [← hn']
    group
  have hsplit' : localToAdelic3 p (localDiag p v) *
        (localToAdelic3 p (upperUnipotent3 x y z) * localToAdelic3 p k) =
      localToAdelic3 p (upperUnipotent3 x' y' z') * (localToAdelic3 p (localDiag p v) * localToAdelic3 p k) := by
    rw [← map_mul, ← map_mul, hsplit, map_mul, map_mul]
  have hteq : torus p v * (a * (localToAdelic3 p (upperUnipotent3 x y z) * localToAdelic3 p k)) =
      localToAdelic3 p (upperUnipotent3 x' y' z') * (a * localToAdelic3 p (localDiag p v) * localToAdelic3 p k) := by
    rw [torus_eq_localToAdelic3, ← mul_assoc, ← hac, mul_assoc, hsplit', ← mul_assoc, hac]
    simp only [mul_assoc]

  have hEm := hE a hac (v.1 - v.2.2, v.2.1 - v.2.2)
  rw [hteq, hN _ (localToAdelic3_upperUnipotent3_mem p x' y' z'), whittaker3_mul_right hfk, localToAdelic3_localDiag,
    ← mul_assoc, ← centralScalarGL_comm, whittaker3_central_mul ω hcen, hEm, norm_mul, norm_mul, hWg]
  ring

private theorem ideleNorm_det_torus_mul (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (σ : ℝ) :
    ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (torus p v * g)) ^ σ) =
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (torus p v)) ^ σ) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) := by
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul,
    Real.mul_rpow (NumberField.TateGlobal.ideleNorm_pos _).le (NumberField.TateGlobal.ideleNorm_pos _).le,
    ENNReal.ofReal_mul (Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le σ)]

private theorem evalHom_ideleAt_mul_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (w : (p.adicCompletion ℚ)ˣ)
    (a : AdeleRing (𝓞 ℚ) ℚ) : evalHom q ((ideleAt p w : AdeleRing (𝓞 ℚ) ℚ) * a) = evalHom q a := by
  rw [map_mul, evalHom_ideleAt_of_ne hq, one_mul]

private theorem evalHom_ideleAt_mul_self (p : HeightOneSpectrum (𝓞 ℚ)) (w : (p.adicCompletion ℚ)ˣ)
    (a : AdeleRing (𝓞 ℚ) ℚ) : evalHom p ((ideleAt p w : AdeleRing (𝓞 ℚ) ℚ) * a) = w * evalHom p a := by
  rw [map_mul, evalHom_ideleAt_self]

private theorem adeleArch_ideleAt_mul (p : HeightOneSpectrum (𝓞 ℚ)) (w : (p.adicCompletion ℚ)ˣ)
    (a : AdeleRing (𝓞 ℚ) ℚ) :
    AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((ideleAt p w : AdeleRing (𝓞 ℚ) ℚ) * a) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ a := by
  rw [map_mul, adeleArch_ideleAt, one_mul]

private theorem finite_component_eq_evalHom (q : HeightOneSpectrum (𝓞 ℚ)) (a : AdeleRing (𝓞 ℚ) ℚ) :
    (a.2 : FiniteAdeleRing (𝓞 ℚ) ℚ) q = evalHom q a :=
  rfl

private theorem factorizable_ideleAt_mul_eq {φ : AdeleRing (𝓞 ℚ) ℚ → ℂ} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {gw : (w : InfinitePlace ℚ) → w.Completion → ℂ} {hv : (q : HeightOneSpectrum (𝓞 ℚ)) → q.adicCompletion ℚ → ℂ}
    (hφ : NumberField.TateGlobal.IsFactorizableStandardOutside φ S gw hv) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S)
    (w : (p.adicCompletion ℚ)ˣ) (a : AdeleRing (𝓞 ℚ) ℚ)
    (hint : (w : p.adicCompletion ℚ) * evalHom p a ∈ p.adicCompletionIntegers ℚ ↔
      evalHom p a ∈ p.adicCompletionIntegers ℚ) :
    φ ((ideleAt p w : AdeleRing (𝓞 ℚ) ℚ) * a) = φ a := by
  rw [hφ, hφ a]
  have hmem : (ideleAt p w : AdeleRing (𝓞 ℚ) ℚ) * a ∈ NumberField.TateGlobal.integralOutside S ↔
      a ∈ NumberField.TateGlobal.integralOutside S := by
    simp only [NumberField.TateGlobal.integralOutside, Set.mem_setOf_eq, finite_component_eq_evalHom]
    refine forall_congr' fun q => imp_congr_right fun _ => ?_
    by_cases hq : q = p
    · subst hq
      rw [evalHom_ideleAt_mul_self]
      exact hint
    · rw [evalHom_ideleAt_mul_of_ne hq]
  have hval : (∏ x, gw x ((((ideleAt p w : AdeleRing (𝓞 ℚ) ℚ) * a).1) x)) *
        ∏ q ∈ S, hv q ((((ideleAt p w : AdeleRing (𝓞 ℚ) ℚ) * a).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) q) =
      (∏ x, gw x (a.1 x)) * ∏ q ∈ S, hv q ((a.2 : FiniteAdeleRing (𝓞 ℚ) ℚ) q) := by
    congr 1
    · have h1 : ((ideleAt p w : AdeleRing (𝓞 ℚ) ℚ) * a).1 = a.1 := adeleArch_ideleAt_mul p w a
      rw [h1]
    · refine Finset.prod_congr rfl fun q hq => ?_
      rw [finite_component_eq_evalHom, finite_component_eq_evalHom,
        evalHom_ideleAt_mul_of_ne (fun h : q = p => hp (h ▸ hq))]
  by_cases ha : a ∈ NumberField.TateGlobal.integralOutside S
  · rw [Set.indicator_of_mem (hmem.2 ha), Set.indicator_of_mem ha, hval]
  · rw [Set.indicator_of_notMem (fun h => ha (hmem.1 h)), Set.indicator_of_notMem ha]

private theorem factorizable_eq_zero_of_notMem {φ : AdeleRing (𝓞 ℚ) ℚ → ℂ} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {gw : (w : InfinitePlace ℚ) → w.Completion → ℂ} {hv : (q : HeightOneSpectrum (𝓞 ℚ)) → q.adicCompletion ℚ → ℂ}
    (hφ : NumberField.TateGlobal.IsFactorizableStandardOutside φ S gw hv) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S)
    {a : AdeleRing (𝓞 ℚ) ℚ} (ha : evalHom p a ∉ p.adicCompletionIntegers ℚ) : φ a = 0 := by
  rw [hφ]
  refine Set.indicator_of_notMem (fun h => ha ?_) _
  exact h p hp

section Generic

variable {α : Type} [MeasurableSpace α] (ν : Measure α)

private theorem lintegral_eq_iSup_of_exhausting {ι : Type} [Countable ι] (Z : Finset ι → Set α) (hmono : Monotone Z)
    (hcover : ∀ a, ∃ T, a ∈ Z T) (F : α → ℝ≥0∞) : ∫⁻ a, F a ∂ν = ⨆ T, ∫⁻ a in Z T, F a ∂ν := by
  have hU : (⋃ T, Z T) = Set.univ := Set.eq_univ_of_forall fun a => Set.mem_iUnion.2 (hcover a)
  rw [← setLIntegral_univ, ← hU, setLIntegral_iUnion_of_directed F hmono.directed_le]

private theorem eq_prod_mul_of_step {ι : Type} [DecidableEq ι] (I : Finset ι → ℝ≥0∞) (L : ι → ℝ≥0∞)
    (hstep : ∀ (T : Finset ι) (p : ι), p ∉ T → I (insert p T) = L p * I T) (T : Finset ι) :
    I T = (∏ p ∈ T, L p) * I ∅ := by
  refine Finset.induction_on T ?_ ?_
  · simp
  · intro p T hp ih
    rw [hstep T p hp, ih, Finset.prod_insert hp, mul_assoc]

end Generic

private theorem inZeroShellAt_of_mem {p : HeightOneSpectrum (𝓞 ℚ)} {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (h : componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) : InZeroShellAt p g :=
  ⟨0, 0, 0, _, h, by rw [upperUnipotent3_zero, one_mul]⟩

private theorem eventually_valuation_le (a : AdeleRing (𝓞 ℚ) ℚ) :
    ∀ᶠ p : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, Valued.v (evalHom p a) ≤ 1 :=
  (a.2.2 : ∀ᶠ p : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, a.2 p ∈ p.adicCompletionIntegers ℚ).mono
    fun _ hp => (HeightOneSpectrum.mem_adicCompletionIntegers ..).1 hp

private theorem componentAt3_apply (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    ((componentAt3 (𝓞 ℚ) ℚ p g : GL (Fin 3) (p.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j =
      evalHom p ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) := by
  rw [coe_componentAt3]
  rfl

private theorem eventually_componentAt3_mem (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∀ᶠ p : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  have h₁ : ∀ᶠ p : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ∀ i j : Fin 3, Valued.v (evalHom p ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j)) ≤ 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le _
  have h₂ : ∀ᶠ p : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ∀ i j : Fin 3,
        Valued.v (evalHom p (((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j)) ≤ 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le _
  refine (h₁.and h₂).mono fun p ⟨hg, hg'⟩ => ?_
  refine (mem_localMaximalCompact3_iff ..).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [componentAt3_apply]
    exact hg i j
  · rw [← map_inv, componentAt3_apply]
    exact hg' i j

private theorem exists_finset_inZeroShellAt (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ p, p ∉ T → InZeroShellAt p g := by
  have hfin := Filter.eventually_cofinite.1 (eventually_componentAt3_mem g)
  refine ⟨hfin.toFinset, fun p hp => inZeroShellAt_of_mem ?_⟩
  by_contra h
  exact hp (hfin.mem_toFinset.2 h)

private def shellSet (S T : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    Set (MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)) :=
  {q | ∀ p, p ∉ S → p ∉ T → InZeroShellAt p q.out}

private theorem shellSet_empty (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    shellSet S ∅ = WhittakerBlock.zerothShell S := by
  ext q
  simp only [shellSet, Set.mem_setOf_eq, Finset.notMem_empty, not_false_eq_true, true_implies]
  rfl

private theorem shellSet_mono (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Monotone (shellSet S) :=
  fun _ _ hTT' _ hq p hpS hpT' => hq p hpS fun hpT => hpT' (hTT' hpT)

private theorem exists_mem_shellSet (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (q : MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    ∃ T, q ∈ shellSet S T := by
  obtain ⟨T, hT⟩ := exists_finset_inZeroShellAt q.out
  exact ⟨T, fun p _ hpT => hT p hpT⟩

private theorem shellSet_eq_insert_inter {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {p : HeightOneSpectrum (𝓞 ℚ)}
    (hp : p ∉ S)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (hpT : p ∉ T) [DecidableEq (HeightOneSpectrum (𝓞 ℚ))] :
    shellSet S T = shellSet S (insert p T) ∩ {q | InZeroShellAt p q.out} := by
  ext q
  constructor
  · intro hq
    exact ⟨fun r hrS hr => hq r hrS fun hrT => hr (Finset.mem_insert_of_mem hrT), hq p hp hpT⟩
  · rintro ⟨hq, hqp⟩ r hrS hrT
    by_cases hrp : r = p
    · subst hrp
      exact hqp
    · exact hq r hrS fun h => (Finset.mem_insert.1 h).elim hrp hrT

private theorem shellSet_insert_of_mem {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {p : HeightOneSpectrum (𝓞 ℚ)}
    (hp : p ∈ S) (T : Finset (HeightOneSpectrum (𝓞 ℚ))) [DecidableEq (HeightOneSpectrum (𝓞 ℚ))] :
    shellSet S (insert p T) = shellSet S T := by
  ext q
  constructor
  · intro hq r hrS hrT
    exact hq r hrS fun h => (Finset.mem_insert.1 h).elim (fun hrp => hrS (hrp ▸ hp)) hrT
  · intro hq r hrS hr
    exact hq r hrS fun hrT => hr (Finset.mem_insert_of_mem hrT)

section HaarFactor

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private theorem exists_conj_factor (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure]
    (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) :
    ∃ D : ℝ≥0∞, D ≠ 0 ∧ D ≠ ∞ ∧ ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ x, F ⟨b * (x : G) * b⁻¹, (hb (x : G)).mp x.2⟩ ∂μH = D * ∫⁻ x, F x ∂μH := by
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have hmem : ∀ x : H, b⁻¹ * (x : G) * b ∈ H := fun x => (hb _).mpr (by simp [mul_assoc])
  let e : H ≃* H :=
    { toFun := fun x => ⟨b * (x : G) * b⁻¹, (hb (x : G)).mp x.2⟩
      invFun := fun x => ⟨b⁻¹ * (x : G) * b, hmem x⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have he : Continuous e := by
    show Continuous fun x : H => (⟨b * (x : G) * b⁻¹, (hb (x : G)).mp x.2⟩ : H)
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hesymm : Continuous e.symm := by
    show Continuous fun x : H => (⟨b⁻¹ * (x : G) * b, hmem x⟩ : H)
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  haveI : (μH.map e).IsHaarMeasure := e.isHaarMeasure_map μH he hesymm
  obtain ⟨c, hc0, hc⟩ : ∃ c : NNReal, c ≠ 0 ∧ μH.map e = c • μH :=
    ⟨(μH.map e).haarScalarFactor μH, (Measure.haarScalarFactor_pos_of_isHaarMeasure (μH.map e) μH).ne',
      Measure.isMulLeftInvariant_eq_smul (μH.map e) μH⟩
  refine ⟨(c : ℝ≥0∞), ENNReal.coe_ne_zero.mpr hc0, ENNReal.coe_ne_top, fun F hF => ?_⟩
  calc ∫⁻ x, F ⟨b * (x : G) * b⁻¹, (hb (x : G)).mp x.2⟩ ∂μH
      = ∫⁻ x, F x ∂(μH.map e) := (lintegral_map hF he.measurable).symm
    _ = (c : ℝ≥0∞) * ∫⁻ x, F x ∂μH := by
      rw [hc]
      exact lintegral_smul_measure c _

end HaarFactor

private theorem evalHom_bottomRow {p : HeightOneSpectrum (𝓞 ℚ)} {g : AdelicGL 3 (𝓞 ℚ) ℚ} {x y z : p.adicCompletion ℚ}
    {k : LocalGL3 p} (hcomp : componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k) (i : Fin 3) :
    evalHom p ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 i) =
      (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 i := by
  rw [← componentAt3_apply, hcomp, Units.val_mul, upperUnipotent3_mul_apply_two]

private theorem prod_bottomRow_torus_mul {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {p : HeightOneSpectrum (𝓞 ℚ)}
    (hp : p ∉ S)
    {Φc : Fin 3 → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hfact : ∀ i, ∃ gw hv, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S gw hv) (v : ℤ × ℤ × ℤ)
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : InZeroShellAt p g) :
    (∏ i, Φc i (((torus p v * g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 i)) =
      (if 0 ≤ v.2.2 then 1 else 0) * ∏ i, Φc i ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 i) := by
  obtain ⟨x, y, z, k, hk, hcomp⟩ := hg
  split_ifs with hγ
  · rw [one_mul]
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨gw, hv, hf⟩ := hfact i
    rw [torus_mul_apply_two]
    refine factorizable_ideleAt_mul_eq hf hp _ _ (iff_of_true ?_ ?_)
    · rw [evalHom_bottomRow hcomp]
      exact zpow_mul_mem_adicCompletionIntegers p hγ (valuation_bottomRow_le p hk i)
    · rw [evalHom_bottomRow hcomp]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers ..).2 (valuation_bottomRow_le p hk i)
  · rw [zero_mul]
    obtain ⟨j, hj⟩ := exists_valuation_bottomRow_eq_one p hk
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    obtain ⟨gw, hv, hf⟩ := hfact j
    rw [torus_mul_apply_two]
    refine factorizable_eq_zero_of_notMem hf hp ?_
    rw [evalHom_ideleAt_mul_self, evalHom_bottomRow hcomp]
    exact zpow_mul_notMem_adicCompletionIntegers p (not_le.1 hγ) hj

private theorem diagGL_conj_mem (d : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) {y : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hy : y ∈ WhittakerBlock.unipotentSubgroup3) :
    diagGL d * y * (diagGL d)⁻¹ ∈ WhittakerBlock.unipotentSubgroup3 := by
  obtain ⟨x, y', z, rfl⟩ := (WhittakerBlock.mem_unipotentSubgroup3_iff y).1 hy
  refine (WhittakerBlock.mem_unipotentSubgroup3_iff _).2
    ⟨d 0 * x * ((d 1)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ), d 1 * y' * ((d 2)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ),
      d 0 * z * ((d 2)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ), Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul]
  exact diagonal_mul_upperUnipotent3_mul_diagonal_inv d x y' z

private theorem diagGL_inv (d : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) : (diagGL d)⁻¹ = diagGL fun i => (d i)⁻¹ :=
  Units.ext (by simp only [coe_diagGL]; rfl)

private theorem mem_unipotentSubgroup3_iff_torus_conj (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ)
    (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    y ∈ WhittakerBlock.unipotentSubgroup3 ↔
      torus p v * y * (torus p v)⁻¹ ∈ WhittakerBlock.unipotentSubgroup3 := by
  rw [torus_eq_diagGL]
  refine ⟨diagGL_conj_mem _, fun h => ?_⟩
  have h' := diagGL_conj_mem (fun i => (torusIdeles p v i)⁻¹) h
  rw [← diagGL_inv (torusIdeles p v), inv_inv] at h'
  have hy : (diagGL (torusIdeles p v))⁻¹ * (diagGL (torusIdeles p v) * y * (diagGL (torusIdeles p v))⁻¹) *
      diagGL (torusIdeles p v) = y := by
    group
  rwa [hy] at h'

private theorem inShell_zero_iff (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    InShell p 0 x ↔ ∃ (a b c : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
      k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ x = upperUnipotent3 a b c * k := by
  constructor
  · rintro ⟨n, k, ⟨a, b, c, rfl⟩, hk, rfl⟩
    exact ⟨a, b, c, k, hk, by rw [localDiag_zero, mul_one]⟩
  · rintro ⟨a, b, c, k, hk, rfl⟩
    exact ⟨upperUnipotent3 a b c, k, ⟨a, b, c, rfl⟩, hk, by rw [localDiag_zero, mul_one]⟩

private theorem inZeroShellAt_iff (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    InZeroShellAt p g ↔ InShell p 0 (componentAt3 (𝓞 ℚ) ℚ p g) := by
  rw [inShell_zero_iff]
  rfl

private theorem inZeroShellAt_torus_inv_mul_of_ne {p r : HeightOneSpectrum (𝓞 ℚ)} (hr : r ≠ p) (v : ℤ × ℤ × ℤ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : InZeroShellAt r ((torus p v)⁻¹ * g) ↔ InZeroShellAt r g := by
  simp only [InZeroShellAt, map_mul, map_inv, componentAt3_torus_of_ne hr, inv_one, one_mul]

private theorem inShell_componentAt3_iff (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    InShell p v (componentAt3 (𝓞 ℚ) ℚ p g) ↔ InZeroShellAt p ((torus p v)⁻¹ * g) := by
  rw [inShell_iff_inShell_zero, inZeroShellAt_iff, map_mul, map_inv, componentAt3_torus]

private def shellWeight (p : HeightOneSpectrum (𝓞 ℚ)) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : ℤ × ℤ → ℂ) (σ : ℝ)
    (v : ℤ × ℤ × ℤ) : ℝ≥0∞ :=
  ((‖u (v.1 - v.2.2, v.2.1 - v.2.2)‖₊ * ‖(ω (ideleAt p (ratPrimeUnit p ^ v.2.2)) : ℂ)‖₊ : ℝ≥0∞) ^ 2 *
      (if 0 ≤ v.2.2 then 1 else 0)) *
    ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (torus p v)) ^ σ)

private theorem shellWeight_ne_top (p : HeightOneSpectrum (𝓞 ℚ)) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : ℤ × ℤ → ℂ)
    (σ : ℝ) (v : ℤ × ℤ × ℤ) : shellWeight p ω u σ v ≠ ⊤ := by
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) ?_) ENNReal.ofReal_ne_top
  split_ifs <;> simp

private theorem integrand_torus_mul {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S)
    {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : ℤ × ℤ → ℂ)
    (hN : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖whittaker3 pins0 NumberField.StandardAddChar.psiQ f (n * g)‖ =
        ‖whittaker3 pins0 NumberField.StandardAddChar.psiQ f g‖)
    (hK : IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (hE : ∀ (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ), (∀ x : LocalGL3 p, g₀ * localToAdelic3 p x = localToAdelic3 p x * g₀) →
      ∀ m : ℤ × ℤ,
        whittaker3 pins0 NumberField.StandardAddChar.psiQ f
            (g₀ * localToAdelic3 p (iotaGL (diagUnits2 (ratPrimeUnit p ^ m.1) (ratPrimeUnit p ^ m.2)))) =
          whittaker3 pins0 NumberField.StandardAddChar.psiQ f g₀ * u m)
    {Φc : Fin 3 → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hfact : ∀ i, ∃ gw hv, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S gw hv) (σ : ℝ)
    (v : ℤ × ℤ × ℤ) {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : InZeroShellAt p g) :
    integrand (whittaker3 pins0 NumberField.StandardAddChar.psiQ f) (fun x => ∏ i, Φc i (x i)) σ (torus p v * g) =
      shellWeight p ω u σ v *
        integrand (whittaker3 pins0 NumberField.StandardAddChar.psiQ f) (fun x => ∏ i, Φc i (x i)) σ g := by
  have hW : ‖whittaker3 pins0 NumberField.StandardAddChar.psiQ f (torus p v * g)‖₊ =
      ‖u (v.1 - v.2.2, v.2.1 - v.2.2)‖₊ * ‖(ω (ideleAt p (ratPrimeUnit p ^ v.2.2)) : ℂ)‖₊ *
        ‖whittaker3 pins0 NumberField.StandardAddChar.psiQ f g‖₊ :=
    NNReal.coe_injective (by push_cast; exact norm_whittaker3_torus_mul ω u hN hK hcen hE v hg)
  have hΦ := prod_bottomRow_torus_mul hp hfact v hg
  simp only [integrand, shellWeight]
  rw [hW, hΦ, ideleNorm_det_torus_mul]
  split_ifs
  · simp only [one_mul, mul_one, ENNReal.coe_mul]
    ring
  · simp only [zero_mul, mul_zero, nnnorm_zero, ENNReal.coe_zero]

private theorem secondCountableTopology_adelicGL3 : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdeleRing.secondCountableTopology ℚ
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem continuous_integral_of_isCompact_carrier {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] (hY : OpensMeasurableSpace Y) (ν : MeasureTheory.Measure Y)
    (hν : MeasureTheory.IsFiniteMeasure ν) {C : Set Y} (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν, y ∈ C) (F : X → Y → ℂ)
    (hF : Continuous fun p : X × Y => F p.1 p.2) : Continuous fun x => ∫ y, F x y ∂ν := by
  haveI := hY
  haveI := hν
  have hslice : ∀ x, Continuous (F x) := fun x =>
    hF.comp (continuous_const.prodMk continuous_id : Continuous fun y : Y => (x, y))
  have hint : ∀ x, MeasureTheory.Integrable (F x) ν := by
    intro x
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hslice x).continuousOn
    exact MeasureTheory.Integrable.of_bound (hslice x).aestronglyMeasurable M (hνC.mono fun y hy => hM y hy)
  have hcurry : Continuous (ContinuousMap.curry (⟨fun p : X × Y => F p.1 p.2, hF⟩ : ContinuousMap (X × Y) ℂ)) :=
    (ContinuousMap.curry _).continuous
  rw [continuous_iff_continuousAt]
  intro x₀
  have hunif : TendstoUniformlyOn (fun x y => F x y) (F x₀) (nhds x₀) C :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 (hcurry.tendsto x₀)) C hC
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hmpos : (0 : ℝ) < ν.real Set.univ + 1 := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg one_pos
  have hδ : (0 : ℝ) < ε / (ν.real Set.univ + 1) := div_pos hε hmpos
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif _ hδ] with x hx
  show dist (∫ y, F x y ∂ν) (∫ y, F x₀ y ∂ν) < ε
  rw [dist_eq_norm, ← MeasureTheory.integral_sub (hint x) (hint x₀)]
  calc ‖∫ y, (F x y - F x₀ y) ∂ν‖ ≤ ε / (ν.real Set.univ + 1) * ν.real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const (hνC.mono fun y hy => by
          rw [← dist_eq_norm, dist_comm]; exact (hx y hy).le)
    _ < ε / (ν.real Set.univ + 1) * (ν.real Set.univ + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hδ
    _ = ε := div_mul_cancel₀ ε hmpos.ne'

private theorem continuous_upperUnipotent3_triple {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous fun p : A × A × A => LanglandsTunnell.CubicInduction.upperUnipotent3 p.1 p.2.1 p.2.2 := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.upperUnipotent3] <;> fun_prop

private theorem exists_isCompact_ae_mem_productionPins_measure :
    ∃ C : Set (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ), IsCompact C ∧
      (∀ᵐ y ∂(AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (NumberField.AdelicBox.adelicBox ℚ)).ν,
        y ∈ C) := by
  obtain ⟨C, hC, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset ℚ
  refine ⟨C, hC, ?_⟩
  have h : ∀ᵐ y ∂(AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1)
      (NumberField.AdelicBox.adelicBox ℚ)).ν, y ∈ NumberField.AdelicBox.adelicBox ℚ :=
    MeasureTheory.Measure.ae_smul_measure
      (MeasureTheory.ae_restrict_mem (NumberField.AdelicBox.measurableSet_adelicBox ℚ)) _
  exact h.mono fun y hy => hsub hy

private theorem continuous_whittaker3_productionPins
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (f : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hf : Continuous f) :
    Continuous (LanglandsTunnell.CubicInduction.whittaker3
      (AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (NumberField.AdelicBox.adelicBox ℚ)) ψ f) := by
  letI : MeasurableSpace (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :=
    NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers ℚ) ℚ
  have hY : OpensMeasurableSpace (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :=
    (NumberField.AdelicHaar.borelSpace_adeleBorel (NumberField.RingOfIntegers ℚ) ℚ).opensMeasurable
  set ν : @MeasureTheory.Measure (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
      (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers ℚ) ℚ) :=
    (AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (NumberField.AdelicBox.adelicBox ℚ)).ν
  haveI : MeasureTheory.IsProbabilityMeasure ν := NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  have hν : MeasureTheory.IsFiniteMeasure ν := inferInstance
  obtain ⟨C, hC, hνC⟩ := exists_isCompact_ae_mem_productionPins_measure
  have hn := continuous_upperUnipotent3_triple (A := NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)

  have hF₃ : Continuous fun p : (LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
      NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
      NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ =>
      ∫ z, f (LanglandsTunnell.CubicInduction.upperUnipotent3 p.1.2 p.2 z * p.1.1) * ψ (-(p.1.2 + p.2)) ∂ν := by
    refine continuous_integral_of_isCompact_carrier hY ν hν hC hνC _ ?_

    have hq : Continuous fun pz : ((LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ => (pz.1.1.2, pz.1.2, pz.2) :=
      (continuous_snd.comp (continuous_fst.comp continuous_fst)).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    have hU : Continuous fun pz : ((LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ =>
        LanglandsTunnell.CubicInduction.upperUnipotent3 pz.1.1.2 pz.1.2 pz.2 := hn.comp hq
    have hg : Continuous fun pz : ((LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ => pz.1.1.1 :=
      continuous_fst.comp (continuous_fst.comp continuous_fst)
    have hs : Continuous fun pz : ((LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ => -(pz.1.1.2 + pz.1.2) :=
      ((continuous_snd.comp (continuous_fst.comp continuous_fst)).add (continuous_snd.comp continuous_fst)).neg
    exact (hf.comp (hU.mul hg)).mul (hψ.comp hs)

  have hF₂ : Continuous fun gx : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
      NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ =>
      ∫ y, ∫ z, f (LanglandsTunnell.CubicInduction.upperUnipotent3 gx.2 y z * gx.1) * ψ (-(gx.2 + y)) ∂ν ∂ν := by
    refine continuous_integral_of_isCompact_carrier hY ν hν hC hνC _ ?_
    exact hF₃

  have h1 : Continuous fun g : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ =>
      ∫ x, ∫ y, ∫ z, f (LanglandsTunnell.CubicInduction.upperUnipotent3 x y z * g) * ψ (-(x + y)) ∂ν ∂ν ∂ν := by
    refine continuous_integral_of_isCompact_carrier hY ν hν hC hνC _ ?_
    exact hF₂
  exact h1

section Glue

attribute [local instance] NumberField.AdelicHaar.glBorel

private def ShellCond (S T : Finset (HeightOneSpectrum (𝓞 ℚ))) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Prop :=
  ∀ p, p ∉ S → p ∉ T → InZeroShellAt p g

private theorem shellSet_eq (S T : Finset (HeightOneSpectrum (𝓞 ℚ))) : shellSet S T = {q | ShellCond S T q.out} :=
  rfl

private theorem shellCond_iff (S T : Finset (HeightOneSpectrum (𝓞 ℚ))) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    [DecidableEq (HeightOneSpectrum (𝓞 ℚ))] :
    ShellCond S T g ↔ ∀ p, p ∉ S ∪ T → InShell p 0 (componentAt3 (𝓞 ℚ) ℚ p g) := by
  simp only [ShellCond, Finset.mem_union, not_or, and_imp, inZeroShellAt_iff]

private theorem measurableSet_shellCond (S T : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    MeasurableSet {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S T g} := by
  classical
  simp only [shellCond_iff]
  exact measurableSet_forall_notMem (S ∪ T) (fun p x => InShell p 0 x) fun p => isOpen_setOf_inShell p 0

private theorem shellCond_mul_iff (S T : Finset (HeightOneSpectrum (𝓞 ℚ))) (n : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hn : n ∈ WhittakerBlock.unipotentSubgroup3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ShellCond S T (n * g) ↔ ShellCond S T g := by
  classical
  rw [shellCond_iff, shellCond_iff]
  exact forall_notMem_mul_iff (S ∪ T) (fun p x => InShell p 0 x) (fun p m hm x => inShell_unip_mul_iff p hm 0 x) n hn g

private def PieceCond (S T : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ)
    [DecidableEq (HeightOneSpectrum (𝓞 ℚ))] (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Prop :=
  ShellCond S (insert p T) g ∧ InShell p v (componentAt3 (𝓞 ℚ) ℚ p g)

variable [DecidableEq (HeightOneSpectrum (𝓞 ℚ))]

private theorem measurableSet_pieceCond (S T : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : HeightOneSpectrum (𝓞 ℚ))
    (v : ℤ × ℤ × ℤ) : MeasurableSet {g : AdelicGL 3 (𝓞 ℚ) ℚ | PieceCond S T p v g} :=
  (measurableSet_shellCond S (insert p T)).inter (measurableSet_local (isOpen_setOf_inShell p v))

private theorem pieceCond_mul_iff (S T : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : HeightOneSpectrum (𝓞 ℚ))
    (v : ℤ × ℤ × ℤ)
    (n : AdelicGL 3 (𝓞 ℚ) ℚ) (hn : n ∈ WhittakerBlock.unipotentSubgroup3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    PieceCond S T p v (n * g) ↔ PieceCond S T p v g :=
  and_congr (shellCond_mul_iff S (insert p T) n hn g)
    (local_mul_iff (fun m hm x => inShell_unip_mul_iff p hm v x) n hn g)

private theorem shellCond_torus_inv_mul_iff {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {p : HeightOneSpectrum (𝓞 ℚ)}
    (hp : p ∉ S)
    {T : Finset (HeightOneSpectrum (𝓞 ℚ))} (hpT : p ∉ T) (v : ℤ × ℤ × ℤ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ShellCond S T ((torus p v)⁻¹ * g) ↔ PieceCond S T p v g := by
  constructor
  · intro h
    refine ⟨fun r hrS hr => ?_, (inShell_componentAt3_iff p v g).2 (h p hp hpT)⟩
    have hrp : r ≠ p := fun hrp => hr (hrp ▸ Finset.mem_insert_self p T)
    exact (inZeroShellAt_torus_inv_mul_of_ne hrp v g).1 (h r hrS fun hrT => hr (Finset.mem_insert_of_mem hrT))
  · rintro ⟨h, hv⟩ r hrS hrT
    by_cases hrp : r = p
    · subst hrp
      exact (inShell_componentAt3_iff r v g).1 hv
    · exact (inZeroShellAt_torus_inv_mul_of_ne hrp v g).2
        (h r hrS fun hmem => (Finset.mem_insert.1 hmem).elim hrp hrT)

private theorem shellSet_insert_eq_iUnion (S T : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : HeightOneSpectrum (𝓞 ℚ)) :
    shellSet S (insert p T) = ⋃ v : ℤ × ℤ × ℤ, {q | PieceCond S T p v q.out} := by
  ext q
  simp only [shellSet_eq, Set.mem_setOf_eq, Set.mem_iUnion, PieceCond]
  exact ⟨fun h => (exists_inShell p _).imp fun v hv => ⟨h, hv⟩, fun ⟨_, h, _⟩ => h⟩

private theorem pairwise_disjoint_pieces (S T : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : HeightOneSpectrum (𝓞 ℚ)) :
    Pairwise (Function.onFun Disjoint fun v : ℤ × ℤ × ℤ =>
      {q : MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ) |
        PieceCond S T p v q.out}) :=
  fun _ _ hvw => Set.disjoint_left.2 fun _ h₁ h₂ => hvw (inShell_unique p h₁.2 h₂.2)

private theorem step_of_prime {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S)
    {T : Finset (HeightOneSpectrum (𝓞 ℚ))} (hpT : p ∉ T) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : ℤ × ℤ → ℂ) (σ : ℝ)
    (D : ℤ × ℤ × ℤ → ℝ≥0∞)
    (hD : ∀ v, ∀ F : WhittakerBlock.unipotentSubgroup3 → ℝ≥0∞, Measurable F →
      ∫⁻ x, F ⟨torus p v * (x : AdelicGL 3 (𝓞 ℚ) ℚ) * (torus p v)⁻¹,
          (mem_unipotentSubgroup3_iff_torus_conj p v (x : AdelicGL 3 (𝓞 ℚ) ℚ)).mp x.2⟩ ∂WhittakerBlock.unipotentHaar3 =
        D v * ∫⁻ x, F x ∂WhittakerBlock.unipotentHaar3)
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞} (hFm : Measurable F)
    (hFN : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g, F (n * g) = F g)
    (hFt : ∀ v, ∀ g, InZeroShellAt p g → F (torus p v * g) = shellWeight p ω u σ v * F g) :
    ∫⁻ q in shellSet S (insert p T), F q.out ∂WhittakerBlock.quotientMeasure =
      (∑' v, shellWeight p ω u σ v * D v) * ∫⁻ q in shellSet S T, F q.out ∂WhittakerBlock.quotientMeasure := by
  haveI := borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := secondCountableTopology_adelicGL3
  haveI := isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI := WhittakerBlock.isHaarMeasure_unipotentHaar3
  haveI := WhittakerBlock.isMulRightInvariant_unipotentHaar3
  rw [shellSet_insert_eq_iUnion, lintegral_iUnion (fun v => measurableSet_setOf_out (measurableSet_pieceCond S T p v)
    (pieceCond_mul_iff S T p v)) (pairwise_disjoint_pieces S T p), ← ENNReal.tsum_mul_right]
  refine tsum_congr fun v => ?_

  have hind : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, {g | PieceCond S T p v g}.indicator F g =
      shellWeight p ω u σ v * {g | ShellCond S T g}.indicator F ((torus p v)⁻¹ * g) := by
    intro g
    by_cases h : PieceCond S T p v g
    · have h' : ShellCond S T ((torus p v)⁻¹ * g) := (shellCond_torus_inv_mul_iff hp hpT v g).2 h
      rw [Set.indicator_of_mem (show g ∈ {g | PieceCond S T p v g} from h),
        Set.indicator_of_mem (show (torus p v)⁻¹ * g ∈ {g | ShellCond S T g} from h')]
      have hz : InZeroShellAt p ((torus p v)⁻¹ * g) := (inShell_componentAt3_iff p v g).1 h.2
      have := hFt v _ hz
      rwa [mul_inv_cancel_left] at this
    · have h' : ¬ ShellCond S T ((torus p v)⁻¹ * g) := fun h' => h ((shellCond_torus_inv_mul_iff hp hpT v g).1 h')
      rw [Set.indicator_of_notMem (show g ∉ {g | PieceCond S T p v g} from h),
        Set.indicator_of_notMem (show (torus p v)⁻¹ * g ∉ {g | ShellCond S T g} from h'), mul_zero]
  have hβ : ∫⁻ q, {g | ShellCond S T g}.indicator F ((torus p v)⁻¹ * q.out) ∂WhittakerBlock.quotientMeasure =
      D v * ∫⁻ q, {g | ShellCond S T g}.indicator F q.out ∂WhittakerBlock.quotientMeasure :=
    HaarQuotient.lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer (adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
      WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3 WhittakerBlock.unipotentHaar3
      (torus p v) (mem_unipotentSubgroup3_iff_torus_conj p v) (D v) (hD v) _
      (hFm.indicator (measurableSet_shellCond S T))
      (fun n hn g => indicator_mul_left_eq (shellCond_mul_iff S T) hFN n hn g)
  rw [← lintegral_indicator_out (measurableSet_pieceCond S T p v) (pieceCond_mul_iff S T p v), shellSet_eq,
    ← lintegral_indicator_out (measurableSet_shellCond S T) (shellCond_mul_iff S T), mul_assoc, ← hβ,
    ← lintegral_const_mul' _ _ (shellWeight_ne_top p ω u σ v)]
  exact lintegral_congr fun q => hind q.out

end Glue

section Statement

attribute [local instance] NumberField.AdelicHaar.glBorel

private theorem lintegral_eq_iSup_prod_mul [DecidableEq (HeightOneSpectrum (𝓞 ℚ))]
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} (L : HeightOneSpectrum (𝓞 ℚ) → ℝ≥0∞)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞)
    (hstep : ∀ (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : HeightOneSpectrum (𝓞 ℚ)), p ∉ T →
      (∫⁻ q in shellSet S (insert p T), F q.out ∂WhittakerBlock.quotientMeasure) =
        L p * ∫⁻ q in shellSet S T, F q.out ∂WhittakerBlock.quotientMeasure) :
    ∫⁻ q, F q.out ∂WhittakerBlock.quotientMeasure =
      (⨆ T : Finset (HeightOneSpectrum (𝓞 ℚ)), ∏ p ∈ T, L p) *
        ∫⁻ q in WhittakerBlock.zerothShell S, F q.out ∂WhittakerBlock.quotientMeasure := by
  haveI := countable_heightOneSpectrum
  rw [lintegral_eq_iSup_of_exhausting WhittakerBlock.quotientMeasure (shellSet S) (shellSet_mono S)
    (exists_mem_shellSet S) (fun q => F q.out), ENNReal.iSup_mul, ← shellSet_empty S]
  exact iSup_congr fun T =>
    eq_prod_mul_of_step (fun T => ∫⁻ q in shellSet S T, F q.out ∂WhittakerBlock.quotientMeasure) L hstep T

end Statement

end ShellPeeling

end

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar in
open scoped ENNReal in
open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction ShellPeeling in
theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (hE : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (_hp : p ∉ S),
    ∃ u : ℤ × ℤ → ℂ, u (0, 0) = 1 ∧ (∀ m : ℤ × ℤ, ¬ (0 ≤ m.2 ∧ m.2 ≤ m.1) → u m = 0) ∧
      ∀ (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
        (_haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
        (_hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
          f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
        (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
        (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen1 p)) f (lam1 p))
        (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen2 p)) f (lam2 p))
        (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (_hg₀ : ∀ x : LocalGL3 p, g₀ * localToAdelic3 p x = localToAdelic3 p x * g₀)
        (m : ℤ × ℤ),
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ f
            (g₀ * localToAdelic3 p (iotaGL (diagUnits2 (ratPrimeUnit p ^ m.1) (ratPrimeUnit p ^ m.2)))) =
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ f g₀ *
            u m) :
    ∃ Λ : ℝ → ℝ≥0∞, (∀ σ : ℝ, 1 ≤ Λ σ) ∧
      ∀ (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
      (_haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
      (_hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
      (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
      (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen1 p)) f (lam1 p))
      (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen2 p)) f (lam2 p)),
      ∀ (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ),
        (∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1 ∧
          ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (t i) = 1) →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
      ∀ σ : ℝ,
        (letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
          ∫⁻ q,
            ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                    NumberField.StandardAddChar.psiQ (fun x => ∑ i, c i * f (x * t i)) q.out‖₊ : ℝ≥0∞) ^ 2 *
              (‖Φ fun j : Fin 3 => (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det q.out) ^ σ))
            ∂WhittakerBlock.quotientMeasure) =
          Λ σ *
            WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (fun x => ∑ i, c i * f (x * t i)) Φ σ S := by
  classical
  choose u _hu0 _huvanish hu using hE

  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := secondCountableTopology_adelicGL3
  haveI := WhittakerBlock.isHaarMeasure_unipotentHaar3
  have hDex := fun (p : HeightOneSpectrum (𝓞 ℚ)) (v : ℤ × ℤ × ℤ) =>
    exists_conj_factor WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3
      WhittakerBlock.unipotentHaar3 (torus p v) (mem_unipotentSubgroup3_iff_torus_conj p v)
  choose D _hD0 _hDtop hD using hDex

  let L : HeightOneSpectrum (𝓞 ℚ) → ℝ → ℝ≥0∞ := fun p σ =>
    if hp : p ∈ S then 1 else ∑' v, shellWeight p ω (u p hp) σ v * D p v
  refine ⟨fun σ => ⨆ T : Finset (HeightOneSpectrum (𝓞 ℚ)), ∏ p ∈ T, L p σ, fun σ => ?_, ?_⟩
  · exact le_iSup_of_le (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) (by simp)
  intro f hc haut hcen hK hT1 hT2 n c t ht Φ hΦ σ
  obtain ⟨⟨Φc, hΦc, hfact, rfl⟩, -, -⟩ := hΦ

  have hWN :=
    (whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul (comb c t f) (comb_aut c t f haut)).2
  have hWc : Continuous (whittaker3 pins0 NumberField.StandardAddChar.psiQ (comb c t f)) :=
    continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ (comb_continuous c t f hc)
  have hFm := measurable_integrand hWc (continuous_prod_of_pureTensors hΦc) σ
  have hFN := integrand_mul_left hWN (fun x => ∏ i, Φc i (x i)) σ
  show ∫⁻ q, integrand (whittaker3 pins0 NumberField.StandardAddChar.psiQ (comb c t f))
        (fun x => ∏ i, Φc i (x i)) σ q.out ∂WhittakerBlock.quotientMeasure =
      _ * ∫⁻ q in WhittakerBlock.zerothShell S,
        integrand (whittaker3 pins0 NumberField.StandardAddChar.psiQ (comb c t f)) (fun x => ∏ i, Φc i (x i)) σ q.out
          ∂WhittakerBlock.quotientMeasure
  refine lintegral_eq_iSup_prod_mul (fun p => L p σ) _ fun T p hpT => ?_
  by_cases hp : p ∈ S
  · simp only [L, dif_pos hp, one_mul, shellSet_insert_of_mem hp]
  · simp only [L, dif_neg hp]
    refine step_of_prime hp hpT ω (u p hp) σ (D p) (hD p) hFm hFN fun v g hg => ?_
    exact integrand_torus_mul hp ω (u p hp) hWN (comb_isRightInvariant (fun i => (ht i).2 p hp) (hK p hp))
      (comb_cen c t f ω hcen)
      (hu p hp (comb c t f) (comb_continuous c t f hc) (comb_aut c t f haut) (comb_cen c t f ω hcen)
        (fun r hr => comb_isRightInvariant (fun i => (ht i).2 r hr) (hK r hr))
        (fun r hr => comb_isCosetEigenfunction (fun i => (ht i).2 r hr) (hT1 r hr))
        (fun r hr => comb_isCosetEigenfunction (fun i => (ht i).2 r hr) (hT2 r hr)))
      hfact σ v hg

end S_LanglandsTunnell_CubicInduction_exists_one_le_and_lintegral_quotientMeasure_eq_mul_whittakerBlock
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_one_le_and_lintegral_quotientMeasure_eq_mul_whittakerBlock (solution)
