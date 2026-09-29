-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.exists_norm_eq_one_and_hasConductorExponentAt_and_eq_mul_modulus_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/4e4a2808-2957-5799-b451-692facbf1d17

import Mathlib
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_exists_norm_eq_one_and_hasConductorExponentAt_and_eq_mul_modulus_cpow
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace R1NormOnePolar

noncomputable section

open LanglandsTunnell.TateLocal

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem val_units_ne_zero (u : (v.adicCompletion K)ˣ) :
    Valued.v (u : v.adicCompletion K) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr u.ne_zero

def higherUnitsSubgroup (b : ℕ) : Subgroup (v.adicCompletion K)ˣ where
  carrier := higherUnitsAt K v b
  one_mem' := one_mem_higherUnitsAt K v b
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    refine ⟨by simp [Units.val_mul, map_mul, hx1, hy1], ?_⟩
    rcases Nat.eq_zero_or_pos b with hb | hb
    · exact Or.inl hb
    · right
      have hx2' : Valued.v ((x : v.adicCompletion K) - 1) ≤ WithZero.exp (-(b : ℤ)) := by
        rcases hx2 with h | h
        · omega
        · exact h
      have hy2' : Valued.v ((y : v.adicCompletion K) - 1) ≤ WithZero.exp (-(b : ℤ)) := by
        rcases hy2 with h | h
        · omega
        · exact h
      have hsplit : ((x * y : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
          (x : v.adicCompletion K) * ((y : v.adicCompletion K) - 1) + ((x : v.adicCompletion K) - 1) := by
        push_cast; ring
      rw [hsplit]
      refine (Valuation.map_add _ _ _).trans (max_le ?_ hx2')
      rw [map_mul, hx1, one_mul]
      exact hy2'
  inv_mem' := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have hinv : Valued.v ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx1, inv_one]
    refine ⟨hinv, ?_⟩
    rcases Nat.eq_zero_or_pos b with hb | hb
    · exact Or.inl hb
    · right
      have hx2' : Valued.v ((x : v.adicCompletion K) - 1) ≤ WithZero.exp (-(b : ℤ)) := by
        rcases hx2 with h | h
        · omega
        · exact h
      have hsplit : ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
          -(((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) * ((x : v.adicCompletion K) - 1)) := by
        rw [mul_sub, mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
        ring
      rw [hsplit, Valuation.map_neg, map_mul, hinv, one_mul]
      exact hx2'

theorem mem_higherUnitsSubgroup_iff (b : ℕ) (u : (v.adicCompletion K)ˣ) :
    u ∈ higherUnitsSubgroup K v b ↔ u ∈ higherUnitsAt K v b := Iff.rfl

theorem exists_uniformizer :
    ∃ ϖ : v.adicCompletion K, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  refine ⟨((WithVal.equiv (v.valuation K)).symm π : v.adicCompletion K), ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hπ

section WithUniformizer

variable {K v}
variable (ϖu : (v.adicCompletion K)ˣ) (hϖ : Valued.v (ϖu : v.adicCompletion K) = WithZero.exp (-1 : ℤ))

def retract : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ where
  toFun x := x * ϖu ^ (WithZero.log (Valued.v (x : v.adicCompletion K)))
  map_one' := by simp
  map_mul' x y := by
    have hx := val_units_ne_zero K v x
    have hy := val_units_ne_zero K v y
    rw [Units.val_mul, map_mul, WithZero.log_mul hx hy, zpow_add]
    simp only [mul_mul_mul_comm]

theorem retract_apply (x : (v.adicCompletion K)ˣ) :
    retract ϖu x = x * ϖu ^ (WithZero.log (Valued.v (x : v.adicCompletion K))) := rfl

include hϖ in
theorem val_retract (x : (v.adicCompletion K)ˣ) :
    Valued.v ((retract ϖu x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  have hx := val_units_ne_zero K v x
  rw [retract_apply]
  set n : ℤ := WithZero.log (Valued.v (x : v.adicCompletion K)) with hn
  have hvx : Valued.v (x : v.adicCompletion K) = WithZero.exp n := by
    rw [hn, WithZero.exp_log hx]
  rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul,
    smul_neg, zsmul_eq_mul, mul_one, Int.cast_id, hvx, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

def bigSubgroup (b : ℕ) : Subgroup (v.adicCompletion K)ˣ :=
  higherUnitsSubgroup K v b ⊔ Subgroup.zpowers ϖu

theorem mem_bigSubgroup_of_mem_higherUnitsAt (b : ℕ) {h : (v.adicCompletion K)ˣ}
    (hh : h ∈ higherUnitsAt K v b) : h ∈ bigSubgroup ϖu b :=
  Subgroup.mem_sup_left ((mem_higherUnitsSubgroup_iff K v b h).mpr hh)

theorem uniformizer_mem_bigSubgroup (b : ℕ) : ϖu ∈ bigSubgroup ϖu b :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers ϖu)

theorem val_eq_one_iff_norm_eq_one (x : v.adicCompletion K) :
    Valued.v x = 1 ↔ ‖x‖ = 1 := by
  constructor
  · intro h
    apply le_antisymm
    · exact Valued.toNormedField.norm_le_one_iff.mpr h.le
    · exact Valued.toNormedField.one_le_norm_iff.mpr h.ge
  · intro h
    apply le_antisymm
    · exact Valued.toNormedField.norm_le_one_iff.mp h.le
    · exact Valued.toNormedField.one_le_norm_iff.mp h.ge

include hϖ in
theorem finite_quotient_bigSubgroup (b : ℕ) :
    Finite ((v.adicCompletion K)ˣ ⧸ bigSubgroup ϖu b) := by

  have hS : IsCompact (Metric.sphere (0 : v.adicCompletion K) 1) := isCompact_sphere _ _

  have hϖ0 : (ϖu : v.adicCompletion K) ≠ 0 := ϖu.ne_zero
  set r : ℝ := ‖(ϖu : v.adicCompletion K) ^ b‖ with hr
  have hrpos : 0 < r := by rw [hr]; exact norm_pos_iff.mpr (pow_ne_zero _ hϖ0)
  obtain ⟨t, htS, htfin, hcover⟩ := hS.finite_cover_balls hrpos

  have htne : ∀ x ∈ t, x ≠ 0 := by
    intro x hx h0
    have := htS hx
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at this
    exact zero_ne_one this

  let f : t → (v.adicCompletion K)ˣ ⧸ bigSubgroup ϖu b := fun x =>
    QuotientGroup.mk (Units.mk0 (x : v.adicCompletion K) (htne x x.2))
  haveI : Finite t := htfin.to_subtype
  refine Finite.of_surjective f ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>

    set u := retract ϖu x with hu
    have hu1 : Valued.v (u : v.adicCompletion K) = 1 := val_retract ϖu hϖ x
    have huS : (u : v.adicCompletion K) ∈ Metric.sphere (0 : v.adicCompletion K) 1 := by
      rw [mem_sphere_zero_iff_norm]
      exact (val_eq_one_iff_norm_eq_one (u : v.adicCompletion K)).mp hu1
    obtain ⟨y, hy, hyball⟩ : ∃ y ∈ t, (u : v.adicCompletion K) ∈ Metric.ball y r := by
      have := hcover huS
      simpa only [Set.mem_iUnion, exists_prop] using this
    refine ⟨⟨y, hy⟩, ?_⟩

    have hy0 : y ≠ 0 := htne y hy
    have hy1 : Valued.v y = 1 := by
      have := htS hy
      rw [mem_sphere_zero_iff_norm] at this
      exact (val_eq_one_iff_norm_eq_one y).mpr this

    have hxu : (QuotientGroup.mk x : (v.adicCompletion K)ˣ ⧸ bigSubgroup ϖu b) = QuotientGroup.mk u := by
      rw [QuotientGroup.eq, hu, retract_apply, ← mul_assoc, inv_mul_cancel, one_mul]
      exact Subgroup.zpow_mem _ (uniformizer_mem_bigSubgroup ϖu b) _
    change (QuotientGroup.mk (Units.mk0 y hy0) : (v.adicCompletion K)ˣ ⧸ bigSubgroup ϖu b) = QuotientGroup.mk x
    rw [hxu, QuotientGroup.eq]
    apply mem_bigSubgroup_of_mem_higherUnitsAt
    refine ⟨?_, Or.inr ?_⟩
    · rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_mk0, hy1, inv_one, one_mul, hu1]
    ·
      have hsplit : (((Units.mk0 y hy0)⁻¹ * u : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
          y⁻¹ * ((u : v.adicCompletion K) - y) := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, mul_sub, inv_mul_cancel₀ hy0]
      rw [hsplit, map_mul, map_inv₀, hy1, inv_one, one_mul]
      have hlt : ‖(u : v.adicCompletion K) - y‖ < ‖(ϖu : v.adicCompletion K) ^ b‖ := by
        rw [← dist_eq_norm]; exact hyball
      have hlt' := Valued.toNormedField.norm_lt_iff.mp hlt
      rw [map_pow, hϖ, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one] at hlt'
      exact hlt'.le

include hϖ in

theorem exists_pow_mem_higherUnitsAt (b : ℕ) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    ∃ N : ℕ, 0 < N ∧ u ^ N ∈ higherUnitsAt K v b := by
  haveI := finite_quotient_bigSubgroup ϖu hϖ b
  set q : (v.adicCompletion K)ˣ ⧸ bigSubgroup ϖu b := QuotientGroup.mk u with hq
  refine ⟨orderOf q, orderOf_pos q, ?_⟩
  have hmem : u ^ orderOf q ∈ bigSubgroup ϖu b := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hq]
    exact pow_orderOf_eq_one q
  obtain ⟨h, hh, z, hz, hprod⟩ := Subgroup.mem_sup.mp hmem
  rw [Subgroup.mem_zpowers_iff] at hz
  obtain ⟨k, rfl⟩ := hz
  have hh' : h ∈ higherUnitsAt K v b := (mem_higherUnitsSubgroup_iff K v b h).mp hh

  have hk : k = 0 := by
    have h1 : Valued.v (((u ^ orderOf q : (v.adicCompletion K)ˣ) : v.adicCompletion K)) = 1 := by
      rw [Units.val_pow_eq_pow_val, map_pow, hu, one_pow]
    rw [← hprod, Units.val_mul, map_mul, hh'.1, one_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ,
      ← WithZero.exp_zsmul, smul_neg, zsmul_eq_mul, mul_one, Int.cast_id, ← WithZero.exp_zero,
      WithZero.exp_inj] at h1
    omega
  subst hk
  rw [zpow_zero, mul_one] at hprod
  rw [← hprod]
  exact hh'

include hϖ in

theorem norm_apply_eq_one_of_val_eq_one (χ : (v.adicCompletion K)ˣ →* ℂˣ) (b : ℕ)
    (hχb : ∀ h ∈ higherUnitsAt K v b, χ h = 1)
    (u : (v.adicCompletion K)ˣ) (hu : Valued.v (u : v.adicCompletion K) = 1) :
    ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨N, hN, hmem⟩ := exists_pow_mem_higherUnitsAt ϖu hϖ b u hu
  have hχN : χ u ^ N = 1 := by
    rw [← map_pow]
    exact hχb _ hmem
  have hnorm : ‖((χ u : ℂˣ) : ℂ)‖ ^ N = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, hχN, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').mp hnorm

end WithUniformizer

theorem coe_modulus_eq_norm (x : v.adicCompletion K) : (modulus x : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm]

theorem coe_modulus_eq_one_of_val_eq_one (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    (modulus (u : v.adicCompletion K) : ℝ) = 1 := by
  rw [coe_modulus_eq_norm]
  exact (val_eq_one_iff_norm_eq_one (u : v.adicCompletion K)).mp hu

theorem coe_modulus_units_pos (a : (v.adicCompletion K)ˣ) :
    0 < (modulus (a : v.adicCompletion K) : ℝ) :=
  NNReal.coe_pos.mpr (modulus_pos a.ne_zero)

theorem coe_modulus_lt_one_of_val_eq_exp_neg_one (ϖu : (v.adicCompletion K)ˣ)
    (hϖ : Valued.v (ϖu : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    (modulus (ϖu : v.adicCompletion K) : ℝ) < 1 := by
  rw [coe_modulus_eq_norm]
  apply Valued.toNormedField.norm_lt_one_iff.mpr
  rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

variable {K v}

def normHom (χ : (v.adicCompletion K)ˣ →* ℂˣ) : (v.adicCompletion K)ˣ →* ℝ where
  toFun a := ‖((χ a : ℂˣ) : ℂ)‖
  map_one' := by rw [map_one, Units.val_one, norm_one]
  map_mul' a b := by rw [map_mul, Units.val_mul, norm_mul]

theorem normHom_apply (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : (v.adicCompletion K)ˣ) :
    normHom χ a = ‖((χ a : ℂˣ) : ℂ)‖ := rfl

def modulusRpowHom (t : ℝ) : (v.adicCompletion K)ˣ →* ℝ where
  toFun a := (modulus (a : v.adicCompletion K) : ℝ) ^ t
  map_one' := by rw [Units.val_one, modulus_one, NNReal.coe_one, Real.one_rpow]
  map_mul' a b := by
    rw [Units.val_mul, modulus_mul, NNReal.coe_mul,
      Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]

theorem modulusRpowHom_apply (t : ℝ) (a : (v.adicCompletion K)ˣ) :
    modulusRpowHom t a = (modulus (a : v.adicCompletion K) : ℝ) ^ t := rfl

theorem modulusRpowHom_pos (t : ℝ) (a : (v.adicCompletion K)ˣ) : 0 < modulusRpowHom t a :=
  Real.rpow_pos_of_pos (coe_modulus_units_pos K v a) t

theorem modulusRpowHom_of_val_eq_one (t : ℝ) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) : modulusRpowHom t u = 1 := by
  rw [modulusRpowHom_apply, coe_modulus_eq_one_of_val_eq_one K v u hu, Real.one_rpow]

def expo (χ : (v.adicCompletion K)ˣ →* ℂˣ) (ϖu : (v.adicCompletion K)ˣ) : ℝ :=
  Real.log ‖((χ ϖu : ℂˣ) : ℂ)‖ / Real.log (modulus (ϖu : v.adicCompletion K) : ℝ)

section WithUniformizer

variable (ϖu : (v.adicCompletion K)ˣ) (hϖ : Valued.v (ϖu : v.adicCompletion K) = WithZero.exp (-1 : ℤ))

include hϖ in

theorem modulusRpowHom_expo_uniformizer (χ : (v.adicCompletion K)ˣ →* ℂˣ) :
    modulusRpowHom (expo χ ϖu) ϖu = normHom χ ϖu := by
  have hβpos : 0 < (modulus (ϖu : v.adicCompletion K) : ℝ) := coe_modulus_units_pos K v ϖu
  have hβlt : (modulus (ϖu : v.adicCompletion K) : ℝ) < 1 :=
    coe_modulus_lt_one_of_val_eq_exp_neg_one K v ϖu hϖ
  have hlogβ : Real.log (modulus (ϖu : v.adicCompletion K) : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hβpos hβlt.ne
  have hαpos : 0 < ‖((χ ϖu : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (χ ϖu).ne_zero
  rw [modulusRpowHom_apply, normHom_apply, Real.rpow_def_of_pos hβpos, expo,
    mul_div_cancel₀ _ hlogβ, Real.exp_log hαpos]

include hϖ in

theorem norm_apply_eq_modulus_rpow (χ : (v.adicCompletion K)ˣ →* ℂˣ) (b : ℕ)
    (hχb : ∀ h ∈ higherUnitsAt K v b, χ h = 1) (a : (v.adicCompletion K)ˣ) :
    ‖((χ a : ℂˣ) : ℂ)‖ = (modulus (a : v.adicCompletion K) : ℝ) ^ (expo χ ϖu) := by
  set S : Subgroup (v.adicCompletion K)ˣ := (normHom χ).eqLocus (modulusRpowHom (expo χ ϖu)) with hS

  have hunits : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → u ∈ S := by
    intro u hu
    change normHom χ u = modulusRpowHom (expo χ ϖu) u
    rw [normHom_apply, norm_apply_eq_one_of_val_eq_one ϖu hϖ χ b hχb u hu,
      modulusRpowHom_of_val_eq_one _ u hu]

  have hϖS : ϖu ∈ S := by
    change normHom χ ϖu = modulusRpowHom (expo χ ϖu) ϖu
    exact (modulusRpowHom_expo_uniformizer ϖu hϖ χ).symm

  have ha : a ∈ S := by
    have hdec : a = retract ϖu a * (ϖu ^ (WithZero.log (Valued.v (a : v.adicCompletion K))))⁻¹ := by
      rw [retract_apply, mul_inv_cancel_right]
    rw [hdec]
    exact S.mul_mem (hunits _ (val_retract ϖu hϖ a)) (S.inv_mem (S.zpow_mem hϖS _))
  exact ha

end WithUniformizer

def modulusChar (t : ℝ) : (v.adicCompletion K)ˣ →* ℂˣ :=
  (Complex.ofRealHom.toMonoidHom.comp (modulusRpowHom t)).toHomUnits

theorem coe_modulusChar_apply (t : ℝ) (a : (v.adicCompletion K)ˣ) :
    ((modulusChar t a : ℂˣ) : ℂ) = (((modulus (a : v.adicCompletion K) : ℝ) ^ t : ℝ) : ℂ) := rfl

theorem coe_modulusChar_apply_eq_cpow (t : ℝ) (a : (v.adicCompletion K)ˣ) :
    ((modulusChar t a : ℂˣ) : ℂ) = ((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ (t : ℂ) := by
  rw [coe_modulusChar_apply, Complex.ofReal_cpow (NNReal.coe_nonneg _)]

theorem norm_coe_modulusChar_apply (t : ℝ) (a : (v.adicCompletion K)ˣ) :
    ‖((modulusChar t a : ℂˣ) : ℂ)‖ = (modulus (a : v.adicCompletion K) : ℝ) ^ t := by
  have hpos : 0 < (modulus (a : v.adicCompletion K) : ℝ) ^ t := modulusRpowHom_pos t a
  rw [coe_modulusChar_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

theorem modulusChar_of_val_eq_one (t : ℝ) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) : modulusChar t u = 1 := by
  apply Units.ext
  rw [coe_modulusChar_apply, Units.val_one, ← modulusRpowHom_apply, modulusRpowHom_of_val_eq_one t u hu,
    Complex.ofReal_one]

def unitaryPart (χ : (v.adicCompletion K)ˣ →* ℂˣ) (t : ℝ) : (v.adicCompletion K)ˣ →* ℂˣ :=
  χ * (modulusChar t)⁻¹

theorem unitaryPart_apply (χ : (v.adicCompletion K)ˣ →* ℂˣ) (t : ℝ) (a : (v.adicCompletion K)ˣ) :
    unitaryPart χ t a = χ a * (modulusChar t a)⁻¹ := rfl

theorem unitaryPart_of_val_eq_one (χ : (v.adicCompletion K)ˣ →* ℂˣ) (t : ℝ)
    (u : (v.adicCompletion K)ˣ) (hu : Valued.v (u : v.adicCompletion K) = 1) :
    unitaryPart χ t u = χ u := by
  rw [unitaryPart_apply, modulusChar_of_val_eq_one t u hu, inv_one, mul_one]

theorem apply_eq_unitaryPart_mul (χ : (v.adicCompletion K)ˣ →* ℂˣ) (t : ℝ) (a : (v.adicCompletion K)ˣ) :
    ((χ a : ℂˣ) : ℂ) = ((unitaryPart χ t a : ℂˣ) : ℂ) *
      (((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ (t : ℂ)) := by
  rw [← coe_modulusChar_apply_eq_cpow, ← Units.val_mul, unitaryPart_apply, inv_mul_cancel_right]

theorem val_eq_one_of_mem_higherUnitsAt {m : ℕ} {u : (v.adicCompletion K)ˣ}
    (hu : u ∈ higherUnitsAt K v m) : Valued.v (u : v.adicCompletion K) = 1 :=
  hu.1

theorem hasConductorExponentAt_unitaryPart (χ : (v.adicCompletion K)ˣ →* ℂˣ) (t : ℝ) (c : ℕ)
    (hχ : HasConductorExponentAt K v χ c) : HasConductorExponentAt K v (unitaryPart χ t) c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [unitaryPart_of_val_eq_one χ t u (val_eq_one_of_mem_higherUnitsAt hu)]
    exact hχ.1 u hu
  · obtain ⟨u, hu, hne⟩ := hχ.2 m hm
    refine ⟨u, hu, ?_⟩
    rw [unitaryPart_of_val_eq_one χ t u (val_eq_one_of_mem_higherUnitsAt hu)]
    exact hne

theorem polar (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) (hχ : HasConductorExponentAt K v χ c)
    (ϖu : (v.adicCompletion K)ˣ) (hϖ : Valued.v (ϖu : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    ∃ (η : (v.adicCompletion K)ˣ →* ℂˣ) (t : ℝ),
      (∀ x : (v.adicCompletion K)ˣ, ‖((η x : ℂˣ) : ℂ)‖ = 1) ∧
      HasConductorExponentAt K v η c ∧
      ∀ a : (v.adicCompletion K)ˣ,
        ((χ a : ℂˣ) : ℂ) = ((η a : ℂˣ) : ℂ) * (((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ (t : ℂ)) := by
  refine ⟨unitaryPart χ (expo χ ϖu), expo χ ϖu, fun x => ?_,
    hasConductorExponentAt_unitaryPart χ _ c hχ, fun a => apply_eq_unitaryPart_mul χ _ a⟩
  have hpos : 0 < (modulus (x : v.adicCompletion K) : ℝ) ^ (expo χ ϖu) := modulusRpowHom_pos _ x
  rw [unitaryPart_apply, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv,
    norm_coe_modulusChar_apply, norm_apply_eq_modulus_rpow ϖu hϖ χ c hχ.1 x,
    mul_inv_cancel₀ hpos.ne']

end

end R1NormOnePolar

open NumberField IsDedekindDomain LanglandsTunnell.TateLocal in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ)
    (hχ : LanglandsTunnell.TateLocal.HasConductorExponentAt K v χ c) :
    ∃ (η : (v.adicCompletion K)ˣ →* ℂˣ) (t : ℝ),
      (∀ x : (v.adicCompletion K)ˣ, ‖((η x : ℂˣ) : ℂ)‖ = 1) ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K v η c ∧
      ∀ a : (v.adicCompletion K)ˣ,
        ((χ a : ℂˣ) : ℂ) = ((η a : ℂˣ) : ℂ) * (((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ (t : ℂ)) := by
  obtain ⟨ϖ, hϖ⟩ := R1NormOnePolar.exists_uniformizer K v
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  exact R1NormOnePolar.polar χ c hχ (Units.mk0 ϖ hϖ0) (by simpa using hϖ)

end S_LanglandsTunnell_TateLocal_exists_norm_eq_one_and_hasConductorExponentAt_and_eq_mul_modulus_cpow
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_exists_norm_eq_one_and_hasConductorExponentAt_and_eq_mul_modulus_cpow (solution)
