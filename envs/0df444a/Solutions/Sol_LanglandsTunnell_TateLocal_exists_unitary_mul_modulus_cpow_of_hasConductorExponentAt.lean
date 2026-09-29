-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/df8cf920-3324-50b2-b149-b4e03b67c84e

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Mathlib.Topology.Algebra.Ring.Compact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt.LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "higherUnitsAt HasConductorExponentAt modulus modulus_pos modulus_ne_zero modulus_one modulus_mul modulus_adicCompletion_eq_nnnorm"
namespace UnitSplit
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

section UnitSplitAux

p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt.LanglandsTunnell.TateLocal IsDedekindDomain.HeightOneSpectrum"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem us_one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have h2 : 1 < Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast h2

private theorem us_norm_eq_zpow_of_valued {x : v.adicCompletion K} {m : ℤ}
    (hx : Valued.v x = WithZero.exp m) : ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd, NNReal.coe_zpow,
    NNReal.coe_natCast]

private theorem us_coe_modulus_of_valued {x : v.adicCompletion K} {m : ℤ}
    (hx : Valued.v x = WithZero.exp m) :
    (modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm,
    us_norm_eq_zpow_of_valued K v hx]

private theorem us_coe_modulus_of_valued_one {x : v.adicCompletion K} (hx : Valued.v x = 1) :
    (modulus x : ℝ) = 1 := by
  have h := us_coe_modulus_of_valued K v (x := x) (m := 0) (by rw [hx, WithZero.exp_zero])
  rw [h, zpow_zero]

private theorem us_exists_valued_eq_exp (a : (v.adicCompletion K)ˣ) :
    ∃ m : ℤ, Valued.v (a : v.adicCompletion K) = WithZero.exp m := by
  refine ⟨WithZero.log (Valued.v (a : v.adicCompletion K)), (WithZero.exp_log ?_).symm⟩
  exact (Valuation.ne_zero_iff _).mpr a.ne_zero

private theorem us_exists_valued_eq_exp_neg_one :
    ∃ π : (v.adicCompletion K)ˣ, Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective K (WithZero.exp (-1 : ℤ))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

private theorem us_valued_zpow (π : (v.adicCompletion K)ˣ)
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) (m : ℤ) :
    Valued.v ((π ^ m : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem us_exists_pow_mem_higherUnitsAt (c : ℕ) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    ∃ n : ℕ, 0 < n ∧ u ^ n ∈ higherUnitsAt K v c := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · exact ⟨1, one_pos, by rw [pow_one]; exact ⟨hu, Or.inl hc⟩⟩
  obtain ⟨π, hπ⟩ := us_exists_valued_eq_exp_neg_one K v
  let O := v.adicCompletionIntegers K
  let I : Ideal O :=
    { carrier := {x : O | Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-(c : ℤ))}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [AddMemClass.coe_add]
        exact (Valuation.map_add _ _ _).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := fun a {b} hb => by
        simp only [Set.mem_setOf_eq] at hb ⊢
        rw [smul_eq_mul, MulMemClass.coe_mul, map_mul]
        have ha : Valued.v (a : v.adicCompletion K) ≤ 1 := a.2
        calc Valued.v (a : v.adicCompletion K) * Valued.v (b : v.adicCompletion K)
            ≤ 1 * Valued.v (b : v.adicCompletion K) := mul_le_mul_left ha _
          _ = Valued.v (b : v.adicCompletion K) := one_mul _
          _ ≤ WithZero.exp (-(c : ℤ)) := hb }
  have hπO : ((π ^ (c : ℤ) : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ O := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, us_valued_zpow K v π hπ, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hIne : I ≠ ⊥ := by
    intro h
    have hmem : (⟨_, hπO⟩ : O) ∈ I := by
      show Valued.v _ ≤ WithZero.exp (-(c : ℤ))
      rw [us_valued_zpow K v π hπ]
    rw [h, Ideal.mem_bot] at hmem
    have h' := congrArg (fun z : O => (z : v.adicCompletion K)) hmem
    simp only [ZeroMemClass.coe_zero] at h'
    exact (π ^ (c : ℤ)).ne_zero h'
  have hIopen : IsOpen (I : Set O) := IsDedekindDomain.isOpen_of_ne_bot hIne
  haveI hfin : Finite (O ⧸ I) := AddSubgroup.quotient_finite_of_isOpen I.toAddSubgroup hIopen
  have huO : (u : v.adicCompletion K) ∈ O := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hu.le
  have huiO : ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ O := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  let uO : Oˣ :=
    ⟨⟨_, huO⟩, ⟨_, huiO⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  let ub : (O ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I : O →* O ⧸ I) uO
  have hfo : IsOfFinOrder ub := isOfFinOrder_of_finite ub
  refine ⟨orderOf ub, hfo.orderOf_pos, ?_⟩
  have h1 : ub ^ orderOf ub = 1 := pow_orderOf_eq_one ub
  have h2 : ((uO ^ orderOf ub : Oˣ) : O) - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, map_one]
    have h1' := congrArg Units.val h1
    rwa [← map_pow, Units.coe_map] at h1'
  have h3 : Valued.v ((((uO ^ orderOf ub : Oˣ) : O) - 1 : O) : v.adicCompletion K)
      ≤ WithZero.exp (-(c : ℤ)) := h2
  have h4 : ((((uO ^ orderOf ub : Oˣ) : O) - 1 : O) : v.adicCompletion K)
      = (u : v.adicCompletion K) ^ orderOf ub - 1 := by
    rw [Units.val_pow_eq_pow_val, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, OneMemClass.coe_one]
  refine ⟨?_, Or.inr ?_⟩
  · rw [Units.val_pow_eq_pow_val, map_pow, hu, one_pow]
  · rw [Units.val_pow_eq_pow_val, ← h4]
    exact h3

private theorem us_norm_apply_eq_one_of_valued_one (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ)
    (hχ : HasConductorExponentAt K v χ c) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) : ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hmem⟩ := us_exists_pow_mem_higherUnitsAt K v c u hu
  have h := hχ.1 _ hmem
  have hpow : ‖((χ u : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp hpow

private theorem us_norm_apply_eq_zpow (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ)
    (hχ : HasConductorExponentAt K v χ c) (π : (v.adicCompletion K)ˣ)
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (a : (v.adicCompletion K)ˣ) {m : ℤ} (ha : Valued.v (a : v.adicCompletion K) = WithZero.exp m) :
    ‖((χ a : ℂˣ) : ℂ)‖ = ‖((χ π : ℂˣ) : ℂ)‖ ^ (-m) := by
  have hu : Valued.v ((a * π ^ m : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_mul, map_mul, ha, us_valued_zpow K v π hπ m, ← WithZero.exp_add,
      add_neg_cancel, WithZero.exp_zero]
  have h1 := us_norm_apply_eq_one_of_valued_one K v χ c hχ _ hu
  rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow] at h1
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_left h1

private def us_modPow (σ : ℝ) : (v.adicCompletion K)ˣ →* ℂˣ where
  toFun a := Units.mk0 (((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ ((σ : ℝ) : ℂ)) (by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left
    exact_mod_cast modulus_ne_zero a.ne_zero)
  map_one' := by
    ext
    simp only [Units.val_mk0, Units.val_one, modulus_one, NNReal.coe_one, Complex.ofReal_one,
      Complex.one_cpow]
  map_mul' a b := by
    ext
    simp only [Units.val_mk0, Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) _

private theorem us_modPow_apply (σ : ℝ) (a : (v.adicCompletion K)ˣ) :
    ((us_modPow K v σ a : ℂˣ) : ℂ) = ((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ ((σ : ℝ) : ℂ) :=
  rfl

private theorem us_modPow_apply_of_valued_one (σ : ℝ) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) : us_modPow K v σ u = 1 := by
  ext
  rw [us_modPow_apply, us_coe_modulus_of_valued_one K v hu, Complex.ofReal_one, Complex.one_cpow,
    Units.val_one]

end UnitSplitAux

end LanglandsTunnell.TateLocal.UnitSplit

end

open LanglandsTunnell.TateLocal.UnitSplit in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) (hχ : HasConductorExponentAt K v χ c) :
    ∃ (η : (v.adicCompletion K)ˣ →* ℂˣ) (σ : ℝ),
      (∀ z : (v.adicCompletion K)ˣ, ‖((η z : ℂˣ) : ℂ)‖ = 1) ∧
      HasConductorExponentAt K v η c ∧
      ∀ z : (v.adicCompletion K)ˣ, ((χ z : ℂˣ) : ℂ) =
        ((η z : ℂˣ) : ℂ) * ((modulus (z : v.adicCompletion K) : ℝ) : ℂ) ^ ((σ : ℝ) : ℂ) := by
  obtain ⟨π, hπ⟩ := us_exists_valued_eq_exp_neg_one K v
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hN
  set r : ℝ := ‖((χ π : ℂˣ) : ℂ)‖ with hr
  have hN1 : 1 < N := us_one_lt_absNorm_real K v
  have hN0 : 0 < N := zero_lt_one.trans hN1
  have hr0 : 0 < r := norm_pos_iff.mpr (χ π).ne_zero
  have hlogN : Real.log N ≠ 0 := (Real.log_pos hN1).ne'
  set σ : ℝ := -Real.log r / Real.log N with hσ

  have hkey : ∀ a : (v.adicCompletion K)ˣ,
      ‖((χ a : ℂˣ) : ℂ)‖ = (modulus (a : v.adicCompletion K) : ℝ) ^ σ := by
    intro a
    obtain ⟨m, hm⟩ := us_exists_valued_eq_exp K v a
    rw [us_norm_apply_eq_zpow K v χ c hχ π hπ a hm, us_coe_modulus_of_valued K v hm,
      Real.rpow_def_of_pos (zpow_pos hN0 m), Real.log_zpow, ← Real.rpow_intCast,
      Real.rpow_def_of_pos hr0]
    congr 1
    rw [hσ]
    field_simp
    push_cast
    ring
  have hmpos : ∀ z : (v.adicCompletion K)ˣ, 0 < (modulus (z : v.adicCompletion K) : ℝ) := fun z =>
    NNReal.coe_pos.mpr (modulus_pos z.ne_zero)
  refine ⟨χ * (us_modPow K v σ)⁻¹, σ, ?_, ?_, ?_⟩
  · intro z
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
      norm_inv, us_modPow_apply, Complex.norm_cpow_eq_rpow_re_of_pos (hmpos z),
      Complex.ofReal_re, hkey z]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos (hmpos z) σ).ne'
  · have heq : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
        (χ * (us_modPow K v σ)⁻¹) u = χ u := by
      intro u hu
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, us_modPow_apply_of_valued_one K v σ u hu, inv_one,
        mul_one]
    refine ⟨fun u hu => ?_, fun m hm => ?_⟩
    · rw [heq u hu.1]
      exact hχ.1 u hu
    · obtain ⟨u, hu, hne⟩ := hχ.2 m hm
      exact ⟨u, hu, by rwa [heq u hu.1]⟩
  · intro z
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      us_modPow_apply]
    exact (inv_mul_cancel_right₀ (us_modPow K v σ z).ne_zero _).symm

end S_LanglandsTunnell_TateLocal_exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_exists_unitary_mul_modulus_cpow_of_hasConductorExponentAt (solution)
