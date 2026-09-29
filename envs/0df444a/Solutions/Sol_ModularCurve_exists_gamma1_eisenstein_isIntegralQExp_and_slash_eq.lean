-- Prove2me | solution 1 for ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/68c4babe-a089-5eb3-83fd-e041b8c32d37

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_EisensteinSeries_EisensteinG
import Theorems.Thm_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG
import Theorems.Thm_EisensteinSeries_qExpansion_eisensteinG_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "UpperHalfPlane ModularForm CongruenceSubgroup Function Matrix Complex Function.Complex Real ModularCurve"
open scoped MatrixGroups ModularForm Manifold Nat

namespace Gamma1Eisenstein

local notation "Γ₁ᴳ(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable (M : ℕ) [NeZero M] (k : ℕ)

abbrev ent (γ : SL(2, ℤ)) (i j : Fin 2) : ZMod M := ((γ i j : ℤ) : ZMod M)

theorem vecMul_eq (c b : ZMod M) (γ : SL(2, ℤ)) :
    (![c, b] ᵥ* γ : Fin 2 → ZMod M) =
      ![c * ent M γ 0 0 + b * ent M γ 1 0, c * ent M γ 0 1 + b * ent M γ 1 1] := by
  ext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, ent]

variable {M} in
theorem ent_one_zero_eq_zero {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : ent M γ 1 0 = 0 := Gamma0_mem.mp hγ

variable {M} in

theorem isUnit_ent_one_one {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : IsUnit (ent M γ 1 1) := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have h := congrArg (fun z : ℤ => (z : ZMod M)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at h
  have hc : ent M γ 1 0 = 0 := ent_one_zero_eq_zero hγ
  simp only [ent] at hc ⊢
  rw [hc, mul_zero, sub_zero, mul_comm] at h
  exact IsUnit.of_mul_eq_one _ h

variable {M} in

theorem bijective_affine (c : ZMod M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    Function.Bijective fun b : ZMod M => c * ent M γ 0 1 + b * ent M γ 1 1 := by
  obtain ⟨u, hu⟩ := isUnit_ent_one_one hγ
  refine (Finite.injective_iff_bijective).mp fun b b' h => ?_
  have h' : b * ent M γ 1 1 = b' * ent M γ 1 1 := add_left_cancel h
  rw [← hu] at h'
  exact (Units.mul_left_inj u).mp h'

def gsum (c : ZMod M) : ℍ → ℂ := ∑ b : ZMod M, EisensteinSeries.eisensteinG M k ![c, b]

theorem finset_sum_slash {kk : ℤ} {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ) (γ : SL(2, ℤ)) :
    (∑ i ∈ s, F i) ∣[kk] γ = ∑ i ∈ s, (F i ∣[kk] γ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

variable {k} in
theorem hk' (hk : 3 ≤ k) : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk

theorem gsum_slash (hk : 3 ≤ k) (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    gsum M k c ∣[(k : ℤ)] γ = gsum M k (c * ent M γ 0 0) := by
  rw [gsum, gsum, finset_sum_slash]
  have hsl : ∀ b : ZMod M, EisensteinSeries.eisensteinG M k ![c, b] ∣[(k : ℤ)] γ
      = EisensteinSeries.eisensteinG M k ![c * ent M γ 0 0, c * ent M γ 0 1 + b * ent M γ 1 1] := by
    intro b
    rw [(EisensteinSeries.exists_modularForm_coe_eq_eisensteinG M k (hk' hk) ![c, b]).2 γ,
      vecMul_eq, ent_one_zero_eq_zero hγ, mul_zero, add_zero]
  simp_rw [hsl]
  exact Fintype.sum_bijective _ (bijective_affine c hγ) _ _ fun b => rfl

theorem gsum_slash_of_mem_Gamma1 (hk : 3 ≤ k) (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 M) :
    gsum M k c ∣[(k : ℤ)] γ = gsum M k c := by
  have h := (Gamma1_mem M γ).mp hγ
  rw [gsum_slash M k hk c γ (Gamma1_in_Gamma0 M hγ)]
  simp only [ent, h.1, mul_one]

def Fform (hk : 3 ≤ k) (c b : ZMod M) : ModularForm Γ(M) (k : ℤ) :=
  (EisensteinSeries.exists_modularForm_coe_eq_eisensteinG M k (hk' hk) ![c, b]).1.choose

theorem coe_Fform (hk : 3 ≤ k) (c b : ZMod M) : (⇑(Fform M k hk c b) : ℍ → ℂ) = EisensteinSeries.eisensteinG M k ![c, b] :=
  (EisensteinSeries.exists_modularForm_coe_eq_eisensteinG M k (hk' hk) ![c, b]).1.choose_spec

theorem coe_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {kk : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → ModularForm Γ kk) : (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(F i) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ih]

def Sform (hk : 3 ≤ k) (c : ZMod M) : ModularForm Γ(M) (k : ℤ) := ∑ b : ZMod M, Fform M k hk c b

theorem coe_Sform (hk : 3 ≤ k) (c : ZMod M) : (⇑(Sform M k hk c) : ℍ → ℂ) = gsum M k c := by
  rw [Sform, coe_finset_sum, gsum]
  exact Finset.sum_congr rfl fun b _ => coe_Fform M k hk c b

def Sform1 (hk : 3 ≤ k) (c : ZMod M) : ModularForm Γ₁ᴳ(M) (k : ℤ) where
  toFun := gsum M k c
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    have := gsum_slash_of_mem_Gamma1 M k hk c γ hγ
    rwa [ModularForm.SL_slash] at this
  holo' := by
    change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gsum M k c)
    rw [← coe_Sform M k hk c]; exact (Sform M k hk c).holo'
  bdd_at_cusps' {cu} hcu := by
    have hcu' : IsCusp cu Γ(M) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hcu ⊢
      exact hcu
    change cu.IsBoundedAt (gsum M k c) (k : ℤ)
    rw [← coe_Sform M k hk c]
    exact (Sform M k hk c).bdd_at_cusps' hcu'

theorem coe_Sform1 (hk : 3 ≤ k) (c : ZMod M) : (⇑(Sform1 M k hk c) : ℍ → ℂ) = gsum M k c := rfl

def kappa : ℂ := (-2 * π * Complex.I) ^ k / (k - 1)!

theorem kappa_ne_zero : kappa k ≠ 0 := by
  rw [kappa]
  refine div_ne_zero (pow_ne_zero _ ?_) (by exact_mod_cast (Nat.factorial_ne_zero _))
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

def Gform (hk : 3 ≤ k) (c : ZMod M) : ModularForm Γ₁ᴳ(M) (k : ℤ) := (kappa k)⁻¹ • Sform1 M k hk c

theorem coe_Gform (hk : 3 ≤ k) (c : ZMod M) : (⇑(Gform M k hk c) : ℍ → ℂ) = (kappa k)⁻¹ • gsum M k c := by
  rw [Gform, IsGLPos.coe_smul, coe_Sform1]

theorem Gform_slash (hk : 3 ≤ k) (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(Gform M k hk c) : ℍ → ℂ) ∣[(k : ℤ)] γ = ⇑(Gform M k hk (c * ent M γ 0 0)) := by
  rw [coe_Gform, coe_Gform, ModularForm.SL_smul_slash, gsum_slash M k hk c γ hγ]

section QExp

def acoef (c : ZMod M) (n : ℕ) : ℤ :=
  (∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = c, (m : ℤ) ^ (k - 1)) +
    (-1) ^ k * ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = -c, (m : ℤ) ^ (k - 1)

theorem acoef_eq (c : ZMod M) (n : ℕ) :
    ((acoef M k c n : ℤ) : ℂ) = ∑ m ∈ n.divisors,
      ((if ((n / m : ℕ) : ZMod M) = c then (1 : ℂ) else 0) +
        (-1) ^ k * (if ((n / m : ℕ) : ZMod M) = -c then (1 : ℂ) else 0)) * (m : ℂ) ^ (k - 1) := by
  classical
  rw [acoef, Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_sum, Finset.sum_filter, Finset.sum_filter]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> ring

theorem sum_stdAddChar_mul (t : ZMod M) :
    ∑ b : ZMod M, ZMod.stdAddChar (b * t) = if t = 0 then (M : ℂ) else 0 := by
  classical
  rw [AddChar.sum_mulShift t (ZMod.isPrimitive_stdAddChar M)]
  split_ifs <;> simp [ZMod.card]

theorem sum_divisors_filter_dvd (n' : ℕ) (f : ℕ → ℂ) :
    ∑ m ∈ (M * n').divisors with M ∣ m, f m = ∑ m' ∈ n'.divisors, f (M * m') := by
  classical
  have hM : M ≠ 0 := NeZero.ne M
  have e : (M * n').divisors.filter (M ∣ ·) = n'.divisors.map ⟨fun m' => M * m', mul_right_injective₀ hM⟩ := by
    ext m
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨hmn, hn0⟩, m', rfl⟩
      refine ⟨m', ⟨(Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hM)).mp hmn, ?_⟩, rfl⟩
      exact right_ne_zero_of_mul hn0
    · rintro ⟨m', ⟨hm', hn'0⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left M hm', mul_ne_zero hM hn'0⟩, dvd_mul_right M m'⟩
  rw [e, Finset.sum_map]
  rfl

theorem sum_coeff_eq (hk : 3 ≤ k) (c : ZMod M) (hc : c ≠ 0) (n : ℕ) :
    ∑ b : ZMod M, (qExpansion M (EisensteinSeries.eisensteinG M k ![c, b])).coeff n =
      if M ∣ n then kappa k * ((acoef M k c (n / M) : ℤ) : ℂ) else 0 := by
  classical
  have hM : M ≠ 0 := NeZero.ne M
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  simp_rw [EisensteinSeries.qExpansion_eisensteinG_coeff M k hk _ n]
  by_cases hn : n = 0
  ·
    subst hn
    simp only [if_true, Matrix.cons_val_zero, if_neg hc, Finset.sum_const_zero]
    rw [if_pos (dvd_zero M), Nat.zero_div, acoef]
    simp
  simp only [if_neg hn, Matrix.cons_val_zero, Matrix.cons_val_one]

  rw [← Finset.mul_sum, Finset.sum_comm]
  have hchar : ∀ m ∈ n.divisors,
      ∑ b : ZMod M, ((if ((n / m : ℕ) : ZMod M) = c then ZMod.stdAddChar (b * (m : ZMod M)) else 0) +
          (-1) ^ k * (if ((n / m : ℕ) : ZMod M) = -c then ZMod.stdAddChar (-(b * (m : ZMod M))) else 0)) *
            (m : ℂ) ^ (k - 1)
        = (if (M ∣ m) then (M : ℂ) * (((if ((n / m : ℕ) : ZMod M) = c then (1 : ℂ) else 0) +
            (-1) ^ k * (if ((n / m : ℕ) : ZMod M) = -c then (1 : ℂ) else 0)) * (m : ℂ) ^ (k - 1)) else 0) := by
    intro m _
    rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e1 : ∑ b : ZMod M, (if ((n / m : ℕ) : ZMod M) = c then ZMod.stdAddChar (b * (m : ZMod M)) else 0)
        = (if ((n / m : ℕ) : ZMod M) = c then (1 : ℂ) else 0) * (if ((m : ℕ) : ZMod M) = 0 then (M : ℂ) else 0) := by
      by_cases h1 : ((n / m : ℕ) : ZMod M) = c
      · simp only [if_pos h1, one_mul]; exact sum_stdAddChar_mul M _
      · simp only [if_neg h1, Finset.sum_const_zero, zero_mul]
    have e2 : ∑ b : ZMod M, (if ((n / m : ℕ) : ZMod M) = -c then ZMod.stdAddChar (-(b * (m : ZMod M))) else 0)
        = (if ((n / m : ℕ) : ZMod M) = -c then (1 : ℂ) else 0) * (if ((m : ℕ) : ZMod M) = 0 then (M : ℂ) else 0) := by
      by_cases h1 : ((n / m : ℕ) : ZMod M) = -c
      · simp only [if_pos h1, one_mul]
        have : ∀ b : ZMod M, -(b * (m : ZMod M)) = b * (-(m : ZMod M)) := fun b => by ring
        simp_rw [this]
        rw [sum_stdAddChar_mul M _]
        simp only [neg_eq_zero]
      · simp only [if_neg h1, Finset.sum_const_zero, zero_mul]
    rw [e1, e2]
    by_cases hMm : M ∣ m
    · have h0 : ((m : ℕ) : ZMod M) = 0 := (ZMod.natCast_eq_zero_iff m M).mpr hMm
      simp only [if_pos h0, if_pos hMm]; ring
    · have h0 : ((m : ℕ) : ZMod M) ≠ 0 := fun h => hMm ((ZMod.natCast_eq_zero_iff m M).mp h)
      simp only [if_neg h0, if_neg hMm]; ring
  rw [Finset.sum_congr rfl hchar, ← Finset.sum_filter]
  split_ifs with hMn
  · obtain ⟨n', rfl⟩ := hMn
    rw [sum_divisors_filter_dvd, Nat.mul_div_cancel_left n' (Nat.pos_of_ne_zero hM), acoef_eq, kappa,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' hm' => ?_
    have hm'0 : m' ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hm')
    rw [Nat.mul_div_mul_left n' m' (Nat.pos_of_ne_zero hM)]
    push_cast
    have hk1 : 1 ≤ k := by omega
    have epow : ((M : ℂ) * (m' : ℂ)) ^ (k - 1) = (M : ℂ) ^ (k - 1) * (m' : ℂ) ^ (k - 1) := mul_pow _ _ _
    rw [epow]
    have eM : (M : ℂ) ^ k = (M : ℂ) * (M : ℂ) ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ, mul_comm]
    rw [eM]
    field_simp
  ·
    rw [Finset.sum_eq_zero, mul_zero]
    intro m hm
    rw [Finset.mem_filter, Nat.mem_divisors] at hm
    exact absurd (hm.2.trans hm.1.1) hMn

theorem qParam_pow (τ : ℍ) : Periodic.qParam (M : ℝ) τ ^ M = Periodic.qParam 1 τ := by
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem M_mem_strictPeriods : ((M : ℕ) : ℝ) ∈ (Γ(M) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples _

theorem one_mem_strictPeriods_one : (1 : ℝ) ∈ (Γ₁ᴳ(M)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem hasSum_gsum (hk : 3 ≤ k) (c : ZMod M) (hc : c ≠ 0) (τ : ℍ) :
    HasSum (fun n' : ℕ => (kappa k * ((acoef M k c n' : ℤ) : ℂ)) • Periodic.qParam 1 τ ^ n') (gsum M k c τ) := by
  classical
  have hM : M ≠ 0 := NeZero.ne M
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM

  have hb : ∀ b : ZMod M, HasSum (fun n : ℕ =>
      (qExpansion M (EisensteinSeries.eisensteinG M k ![c, b])).coeff n • Periodic.qParam M τ ^ n)
      (EisensteinSeries.eisensteinG M k ![c, b] τ) := by
    intro b
    have h := hasSum_qExpansion hMpos
      (SlashInvariantFormClass.periodic_comp_ofComplex (Fform M k hk c b) (M_mem_strictPeriods M))
      (Fform M k hk c b).holo' (ModularFormClass.bdd_at_infty (Fform M k hk c b)) τ
    rwa [coe_Fform] at h

  have hs : HasSum (fun n : ℕ => (∑ b : ZMod M,
      (qExpansion M (EisensteinSeries.eisensteinG M k ![c, b])).coeff n) • Periodic.qParam M τ ^ n)
      (gsum M k c τ) := by
    have h := hasSum_sum (s := (Finset.univ : Finset (ZMod M))) (fun b _ => hb b)
    rw [gsum, Finset.sum_apply]
    convert h using 1
    funext n
    rw [Finset.sum_smul]

  simp_rw [sum_coeff_eq M k hk c hc] at hs
  have hzero : ∀ n : ℕ, n ∉ Set.range (fun n' : ℕ => M * n') →
      (if M ∣ n then kappa k * ((acoef M k c (n / M) : ℤ) : ℂ) else 0) • Periodic.qParam M τ ^ n = 0 := by
    intro n hn
    rw [if_neg, zero_smul]
    rintro ⟨n', rfl⟩
    exact hn ⟨n', rfl⟩
  have hinj : Function.Injective (fun n' : ℕ => M * n') := mul_right_injective₀ hM
  rw [← hinj.hasSum_iff hzero] at hs
  refine hs.congr_fun fun n' => ?_
  simp only [Function.comp_apply]
  rw [if_pos (dvd_mul_right M n'), Nat.mul_div_cancel_left n' (Nat.pos_of_ne_zero hM), pow_mul, qParam_pow]

theorem qExpansion_Gform_coeff (hk : 3 ≤ k) (c : ZMod M) (hc : c ≠ 0) (n : ℕ) :
    (qExpansion 1 (⇑(Gform M k hk c))).coeff n = ((acoef M k c n : ℤ) : ℂ) := by
  have hsum : ∀ τ : ℍ, HasSum (fun n' : ℕ => (((acoef M k c n' : ℤ) : ℂ)) • Periodic.qParam 1 τ ^ n')
      (Gform M k hk c τ) := by
    intro τ
    have h := (hasSum_gsum M k hk c hc τ).const_smul ((kappa k)⁻¹)
    rw [coe_Gform, Pi.smul_apply]
    refine h.congr_fun fun n' => ?_
    rw [smul_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (kappa_ne_zero k), one_mul]
  exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_one M)
    (f := Gform M k hk c) hsum n).symm

theorem isIntegralQExp_Gform (hk : 3 ≤ k) (c : ZMod M) (hc : c ≠ 0) :
    IsIntegralQExp (⇑(Gform M k hk c)) (PowerSeries.mk (acoef M k c)) := by
  rw [isIntegralQExp_iff]
  intro n
  rw [PowerSeries.coeff_mk, qExpansion_Gform_coeff M k hk c hc n]

end QExp

end Gamma1Eisenstein

open Gamma1Eisenstein in

theorem solution (M : ℕ) [NeZero M]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ G : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ c : ZMod M, c ≠ 0 →
        ModularCurve.IsIntegralQExp (G c)
          (PowerSeries.mk fun n : ℕ =>
            (∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = c, (m : ℤ) ^ (k - 1)) +
              (-1) ^ k * ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = -c, (m : ℤ) ^ (k - 1))) ∧
      ∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        ((⇑(G c) : UpperHalfPlane → ℂ) ∣[(k : ℤ)] γ) =
          (⇑(G (c * ((γ 0 0 : ℤ) : ZMod M))) : UpperHalfPlane → ℂ) :=
  ⟨Gform M k hk, fun c hc => isIntegralQExp_Gform M k hk c hc, fun c γ hγ => Gform_slash M k hk c γ hγ⟩

end
end S_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq
end P2MW
export P2MW.S_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq (solution)
