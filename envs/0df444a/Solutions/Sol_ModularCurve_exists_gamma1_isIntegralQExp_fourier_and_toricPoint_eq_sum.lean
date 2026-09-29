-- Prove2me | solution 1 for ModularCurve.exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/49d6e723-ef1e-59d2-a91b-5bce07b4f027

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_TateSlots
import Theorems.Thm_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "UpperHalfPlane~I"
open Complex Filter Function ModularForm CongruenceSubgroup Polynomial ModularCurve HahnSeries
p2m_open_scoped "MatrixGroups ModularForm Topology Manifold Matrix Real Polynomial Real.Polynomial"

namespace ToricFourier

section Generic

variable {F : Type*} [Field F] {M : ℕ} [NeZero M] {z : F} (hz : IsPrimitiveRoot z M)

def ψ (hz : IsPrimitiveRoot z M) : AddChar (ZMod M) F := AddChar.zmodChar M hz.pow_eq_one

theorem ψ_apply (a : ZMod M) : ψ hz a = z ^ a.val := rfl

theorem ψ_isPrimitive : (ψ hz).IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root M hz

theorem ψ_eq_one_iff (a : ZMod M) : ψ hz a = 1 ↔ a = 0 :=
  (ψ_isPrimitive hz).zmod_char_eq_one_iff M a

theorem sum_ψ_mul (b : ZMod M) : ∑ a : ZMod M, ψ hz (a * b) = if b = 0 then (M : F) else 0 := by
  classical
  rw [AddChar.sum_mulShift b (ψ_isPrimitive hz)]
  split_ifs <;> simp [ZMod.card]

theorem ψ_pow (a : ZMod M) (j : ℕ) : ψ hz a ^ j = ψ hz ((j : ZMod M) * a) := by
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

include hz in
theorem natCast_ne_zero : (M : F) ≠ 0 :=
  haveI : NeZero (M : F) := IsPrimitiveRoot.neZero' hz
  NeZero.ne (M : F)

theorem ψ_ne_zero (a : ZMod M) : ψ hz a ≠ 0 := by
  rw [ψ_apply]
  exact pow_ne_zero _ (hz.ne_zero (NeZero.ne M))

theorem ψ_pow_M (a : ZMod M) : ψ hz a ^ M = 1 := by
  rw [ψ_apply, ← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]

theorem ψ_ne_one {a : ZMod M} (ha : a ≠ 0) : ψ hz a ≠ 1 := fun h => ha ((ψ_eq_one_iff hz a).mp h)

theorem one_sub_ψ_ne_zero {a : ZMod M} (ha : a ≠ 0) : 1 - ψ hz a ≠ 0 :=
  sub_ne_zero.mpr (ψ_ne_one hz ha).symm

theorem geom_ψ {a : ZMod M} (ha : a ≠ 0) : ∑ j ∈ Finset.range M, ψ hz a ^ j = 0 := by
  rw [geom_sum_eq (ψ_ne_one hz ha) M, ψ_pow_M, sub_self, zero_div]

theorem ψ_pow_sub_one (a : ZMod M) : ψ hz a ^ (M - 1) = (ψ hz a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [pow_sub_one_mul (NeZero.ne M), ψ_pow_M]

def avg (M : ℕ) (R : ℤ[X]) : ℤ :=
  ∑ j ∈ Finset.range (R.natDegree + 1), if M ∣ j then R.coeff j else 0

theorem sum_aeval (R : ℤ[X]) : ∑ a : ZMod M, aeval (ψ hz a) R = (M : F) * (avg M R : ℤ) := by
  classical
  simp_rw [aeval_eq_sum_range]
  rw [Finset.sum_comm, avg, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [zsmul_eq_mul]
  rw [← Finset.mul_sum]
  have h : ∑ a : ZMod M, ψ hz a ^ j = if M ∣ j then (M : F) else 0 := by
    simp_rw [ψ_pow hz _ j]
    have : ∀ a : ZMod M, (j : ZMod M) * a = a * (j : ZMod M) := fun a => mul_comm _ _
    simp_rw [this]
    rw [sum_ψ_mul hz (j : ZMod M)]
    exact if_congr (ZMod.natCast_eq_zero_iff j M) rfl rfl
  rw [h]
  split_ifs <;> simp [mul_comm]

def four (M : ℕ) (c : ZMod M) (R : ℤ[X]) : ℤ := M * avg M (X ^ (-c).val * R) - R.eval 1

theorem filter_ne_zero_eq : (Finset.univ.filter fun a : ZMod M => a ≠ 0) = Finset.univ.erase 0 := by
  classical
  exact Finset.filter_ne' _ _

theorem sum_filter_aeval (c : ZMod M) (R : ℤ[X]) :
    ∑ a ∈ Finset.univ.filter (fun a : ZMod M => a ≠ 0), ψ hz (-(a * c)) * aeval (ψ hz a) R =
      ((four M c R : ℤ) : F) := by
  classical
  have h1 : ∀ a : ZMod M, ψ hz (-(a * c)) * aeval (ψ hz a) R = aeval (ψ hz a) (X ^ (-c).val * R) := by
    intro a
    rw [map_mul, map_pow, aeval_X, ψ_pow hz a (-c).val, ZMod.natCast_zmod_val]
    congr 2
    ring
  simp_rw [h1]
  rw [filter_ne_zero_eq, Finset.sum_erase_eq_sub (Finset.mem_univ _), sum_aeval hz, four,
    Int.cast_sub, Int.cast_mul, Int.cast_natCast, AddChar.map_zero_eq_one]
  congr 1
  rw [aeval_def, eval₂_at_one, eq_intCast, eval_mul, eval_pow, eval_X, one_pow, one_mul]

theorem fourier_inversion (g : ZMod M → F) (s : ZMod M) (hs : s ≠ 0) :
    ∑ c : ZMod M, ψ hz (s * c) *
        ∑ a ∈ Finset.univ.filter (fun a : ZMod M => a ≠ 0), ψ hz (-(a * c)) * g a =
      (M : F) * g s := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ a : ZMod M, ∑ c : ZMod M, ψ hz (s * c) * (ψ hz (-(a * c)) * g a) =
      (if a = s then (M : F) else 0) * g a := by
    intro a
    have : ∀ c : ZMod M, ψ hz (s * c) * (ψ hz (-(a * c)) * g a) = ψ hz (c * (s - a)) * g a := by
      intro c
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    simp_rw [this]
    rw [← Finset.sum_mul, sum_ψ_mul hz (s - a)]
    congr 1
    simp only [sub_eq_zero]
    by_cases h : a = s
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]
  simp_rw [h, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp [hs]

def S1 (M : ℕ) : ℤ[X] := ∑ j ∈ Finset.range M, (j : ℤ[X]) * X ^ j

theorem aeval_S1 (u : F) : aeval u (S1 M) = ∑ j ∈ Finset.range M, (j : F) * u ^ j := by
  simp [S1, map_sum]

theorem one_sub_mul_S1 {a : ZMod M} (ha : a ≠ 0) :
    (1 - ψ hz a) * aeval (ψ hz a) (S1 M) = -(M : F) := by
  set u := ψ hz a with hu
  set T : F := ∑ j ∈ Finset.range M, (j : F) * u ^ j with hT
  rw [aeval_S1, ← hT]
  have h1 : ∑ j ∈ Finset.range (M + 1), (j : F) * u ^ j = T + M * u ^ M := Finset.sum_range_succ _ M
  have h2 : ∑ j ∈ Finset.range (M + 1), (j : F) * u ^ j =
      ∑ j ∈ Finset.range M, ((j + 1 : ℕ) : F) * u ^ (j + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have h3 : ∑ j ∈ Finset.range M, ((j + 1 : ℕ) : F) * u ^ (j + 1) =
      u * T + u * ∑ j ∈ Finset.range M, u ^ j := by
    rw [hT, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [geom_ψ hz ha, ψ_pow_M] at *
  have key : u * T = T + M := by
    have := h1.symm.trans (h2.trans h3)
    rw [mul_zero, add_zero, mul_one] at this
    exact this.symm
  linear_combination -key

theorem inv_formula {a : ZMod M} (ha : a ≠ 0) :
    (M : F) ^ 2 * (ψ hz a / (1 - ψ hz a) ^ 2) = ψ hz a * (aeval (ψ hz a) (S1 M)) ^ 2 := by
  have h := one_sub_mul_S1 hz ha
  have hne := one_sub_ψ_ne_zero hz ha
  have : aeval (ψ hz a) (S1 M) = -(M : F) / (1 - ψ hz a) := by
    rw [eq_div_iff hne, mul_comm]; exact h
  rw [this]
  field_simp

def xcoef (u : F) (n : ℕ) : F :=
  if n = 0 then u / (1 - u) ^ 2
  else (∑ d ∈ n.divisors, (d : F) * (u ^ d + u⁻¹ ^ d)) - 2 * ∑ d ∈ n.divisors, (d : F)

def xT (M : ℕ) (n : ℕ) : ℤ[X] :=
  if n = 0 then X * S1 M ^ 2
  else C ((M : ℤ) ^ 2) *
    ((∑ d ∈ n.divisors, (d : ℤ[X]) * (X ^ d + X ^ ((M - 1) * d))) - C (2 * ∑ d ∈ n.divisors, (d : ℤ)))

theorem aeval_xT {a : ZMod M} (ha : a ≠ 0) (n : ℕ) :
    aeval (ψ hz a) (xT M n) = (M : F) ^ 2 * xcoef (ψ hz a) n := by
  by_cases hn : n = 0
  · subst hn
    rw [xT, if_pos rfl, xcoef, if_pos rfl, map_mul, map_pow, aeval_X, inv_formula hz ha]
  · rw [xT, if_neg hn, xcoef, if_neg hn]
    have h : ∀ d ∈ n.divisors, aeval (ψ hz a) ((d : ℤ[X]) * (X ^ d + X ^ ((M - 1) * d))) =
        (d : F) * (ψ hz a ^ d + (ψ hz a)⁻¹ ^ d) := by
      intro d _
      rw [map_mul, map_natCast, map_add, map_pow, map_pow, aeval_X, pow_mul, ψ_pow_sub_one hz a]
    rw [map_mul, map_sub, map_sum, Finset.sum_congr rfl h, aeval_C, aeval_C]
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_pow, Int.cast_natCast, Int.cast_mul,
      Int.cast_ofNat, Int.cast_sum]

def wcoef (u : F) (n : ℕ) : F := (if n = 0 then (1 : F) else 0) + 12 * xcoef u n

def wT (M : ℕ) (n : ℕ) : ℤ[X] := C ((M : ℤ) ^ 2 * (if n = 0 then 1 else 0)) + C 12 * xT M n

theorem aeval_wT {a : ZMod M} (ha : a ≠ 0) (n : ℕ) :
    aeval (ψ hz a) (wT M n) = (M : F) ^ 2 * wcoef (ψ hz a) n := by
  have hx := aeval_xT hz ha n
  by_cases hn : n = 0
  · subst hn
    simp only [wT, if_true, mul_one, map_add, map_mul, map_pow, map_natCast, map_ofNat, hx, wcoef]
    ring
  · simp only [wT, hn, if_false, mul_zero, map_zero, zero_add, map_mul, map_ofNat, hx, wcoef]
    ring

def a4Z (n : ℕ) : ℤ := PowerSeries.coeff n tateA4

def fcoef (u : F) (n : ℕ) : F :=
  xcoef u n + 6 * (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, xcoef u p.1 * xcoef u p.2) + 2 * (a4Z n : ℤ)

def fT (M : ℕ) (n : ℕ) : ℤ[X] :=
  C ((M : ℤ) ^ 2) * xT M n + C 6 * (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, xT M p.1 * xT M p.2) +
    C (2 * (M : ℤ) ^ 4 * a4Z n)

theorem aeval_fT {a : ZMod M} (ha : a ≠ 0) (n : ℕ) :
    aeval (ψ hz a) (fT M n) = (M : F) ^ 4 * fcoef (ψ hz a) n := by
  have h : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, aeval (ψ hz a) (xT M p.1 * xT M p.2) =
      (M : F) ^ 4 * (xcoef (ψ hz a) p.1 * xcoef (ψ hz a) p.2) := by
    intro p _
    rw [map_mul, aeval_xT hz ha, aeval_xT hz ha]; ring
  rw [fT, map_add, map_add, map_mul, map_mul, map_sum, Finset.sum_congr rfl h, ← Finset.mul_sum,
    aeval_xT hz ha, fcoef]
  simp only [eq_intCast, map_pow, map_natCast, map_ofNat, map_mul, map_intCast]
  ring

def bZ (M : ℕ) (c : ZMod M) (n : ℕ) : ℤ := four M c (wT M n)

def dZ (M : ℕ) (c : ZMod M) (n : ℕ) : ℤ := four M c (fT M n)

theorem bZ_eq_sum (c : ZMod M) (n : ℕ) :
    ((bZ M c n : ℤ) : F) = ∑ a ∈ Finset.univ.filter (fun a : ZMod M => a ≠ 0),
      ψ hz (-(a * c)) * ((M : F) ^ 2 * wcoef (ψ hz a) n) := by
  rw [bZ, ← sum_filter_aeval hz]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [aeval_wT hz (Finset.mem_filter.mp ha).2]

theorem dZ_eq_sum (c : ZMod M) (n : ℕ) :
    ((dZ M c n : ℤ) : F) = ∑ a ∈ Finset.univ.filter (fun a : ZMod M => a ≠ 0),
      ψ hz (-(a * c)) * ((M : F) ^ 4 * fcoef (ψ hz a) n) := by
  rw [dZ, ← sum_filter_aeval hz]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [aeval_fT hz (Finset.mem_filter.mp ha).2]

theorem sum_ψ_bZ (s : ZMod M) (hs : s ≠ 0) (n : ℕ) :
    ∑ c : ZMod M, ψ hz (s * c) * ((bZ M c n : ℤ) : F) = (M : F) ^ 3 * wcoef (ψ hz s) n := by
  simp_rw [bZ_eq_sum hz]
  rw [fourier_inversion hz (fun a => (M : F) ^ 2 * wcoef (ψ hz a) n) s hs]
  ring

theorem sum_ψ_dZ (s : ZMod M) (hs : s ≠ 0) (n : ℕ) :
    ∑ c : ZMod M, ψ hz (s * c) * ((dZ M c n : ℤ) : F) = (M : F) ^ 5 * fcoef (ψ hz s) n := by
  simp_rw [dZ_eq_sum hz]
  rw [fourier_inversion hz (fun a => (M : F) ^ 4 * fcoef (ψ hz a) n) s hs]
  ring

def xS (u : F) : PowerSeries F := PowerSeries.mk (xcoef u)

def wS (u : F) : PowerSeries F := PowerSeries.mk (wcoef u)

def fS (u : F) : PowerSeries F := PowerSeries.mk (fcoef u)

theorem wS_eq (u : F) : wS u = 1 + PowerSeries.C (12 : F) * xS u := by
  ext n
  simp only [wS, xS, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    wcoef]

theorem fS_eq (u : F) :
    fS u = xS u + PowerSeries.C (6 : F) * (xS u * xS u) +
      PowerSeries.C (2 : F) * (tateA4.map (Int.castRingHom F)) := by
  ext n
  rw [map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
    PowerSeries.coeff_map]
  simp only [fS, xS, PowerSeries.coeff_mk, fcoef, a4Z, eq_intCast]

theorem wS_eq' (u : F) : wS u = 1 + 12 * xS u := by
  rw [wS_eq, show PowerSeries.C (12 : F) = (12 : PowerSeries F) from map_ofNat _ 12]

theorem fS_eq' (u : F) :
    fS u = xS u + 6 * (xS u * xS u) + 2 * (tateA4.map (Int.castRingHom F)) := by
  rw [fS_eq, show PowerSeries.C (6 : F) = (6 : PowerSeries F) from map_ofNat _ 6,
    show PowerSeries.C (2 : F) = (2 : PowerSeries F) from map_ofNat _ 2]

theorem eisenstein4_map_eq :
    eisenstein4.map (Int.castRingHom F) = 1 - 48 * tateA4.map (Int.castRingHom F) := by
  rw [show (48 : PowerSeries F) = PowerSeries.C (48 : F) from (map_ofNat _ 48).symm]
  ext n
  rw [PowerSeries.coeff_map, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_map, coeff_tateA4, eisenstein4, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [hn, if_false, eq_intCast, Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Int.cast_pow,
      Int.cast_natCast, Int.cast_neg, zero_sub, Finset.mul_sum, mul_neg, neg_neg]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring

end Generic

section OverComplex

variable (M : ℕ) [NeZero M]

local notation "Γ₁ᴳ" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

def μ : ℂ := cexp (2 * π * I / M)

theorem hμ : IsPrimitiveRoot (μ M) M := Complex.isPrimitiveRoot_exp M (NeZero.ne M)

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ₁ᴳ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

def W : ZMod M → ModularForm Γ₁ᴳ 2 :=
  (PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff M).choose

theorem W_slash (t : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(W M t) : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑(W M (t * ((γ 1 1 : ℤ) : ZMod M))) :=
  (PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff M).choose_spec.2.1 t γ hγ

theorem qExpansion_W_coeff (t : ZMod M) (ht : t ≠ 0) (n : ℕ) :
    (qExpansion 1 (W M t)).coeff n = wcoef (ψ (hμ M) t) n := by
  rw [W, (PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff M).choose_spec.2.2
    t ht n, wcoef, xcoef, ψ_apply]
  by_cases hn : n = 0
  · simp [hn, μ, mul_div_assoc]
  · simp only [hn, if_false, zero_add, μ]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← pow_mul, ← inv_pow, ← pow_mul]

theorem qExpansion_W (t : ZMod M) (ht : t ≠ 0) : qExpansion 1 (W M t) = wS (ψ (hμ M) t) := by
  ext n
  rw [qExpansion_W_coeff M t ht, wS, PowerSeries.coeff_mk]

theorem coe_finset_sum {k : ℤ} {ι : Type*} (s : Finset ι) (G : ι → ModularForm Γ₁ᴳ k) :
    (⇑(∑ i ∈ s, G i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(G i) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ih]

theorem qExpansion_finset_sum {k : ℤ} {ι : Type*} (s : Finset ι) (G : ι → ModularForm Γ₁ᴳ k) :
    qExpansion 1 (⇑(∑ i ∈ s, G i)) = ∑ i ∈ s, qExpansion 1 (⇑(G i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos (one_mem_strictPeriods M) (G a) (∑ i ∈ s, G i), ih]

theorem qExpansion_smul' {k : ℤ} (c : ℂ) (f : ModularForm Γ₁ᴳ k) :
    qExpansion 1 (⇑(c • f)) = c • qExpansion 1 (⇑f) := by
  rw [IsGLPos.coe_smul]
  exact ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M) c f

theorem finset_sum_slash {k : ℤ} {ι : Type*} (s : Finset ι) (G : ι → ℍ → ℂ) (γ : SL(2, ℤ)) :
    (∑ i ∈ s, G i) ∣[k] γ = ∑ i ∈ s, (G i ∣[k] γ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

abbrev nz : Finset (ZMod M) := Finset.univ.filter fun a : ZMod M => a ≠ 0

def B (c : ZMod M) : ModularForm Γ₁ᴳ 2 :=
  ((M : ℂ) ^ 2) • ∑ t ∈ nz M, (ψ (hμ M) (-(t * c))) • W M t

theorem coe_B (c : ZMod M) :
    (⇑(B M c) : ℍ → ℂ) = ((M : ℂ) ^ 2) • ∑ t ∈ nz M, (ψ (hμ M) (-(t * c))) • (⇑(W M t) : ℍ → ℂ) := by
  rw [B, IsGLPos.coe_smul, coe_finset_sum]
  simp only [IsGLPos.coe_smul]

theorem qExpansion_B_coeff (c : ZMod M) (n : ℕ) :
    (qExpansion 1 (B M c)).coeff n = ((bZ M c n : ℤ) : ℂ) := by
  rw [B, qExpansion_smul', qExpansion_finset_sum, bZ_eq_sum (hμ M)]
  simp only [map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [qExpansion_smul', map_smul, smul_eq_mul, qExpansion_W_coeff M t (Finset.mem_filter.mp ht).2]
  ring

theorem isIntegralQExp_B (c : ZMod M) : IsIntegralQExp (⇑(B M c)) (PowerSeries.mk (bZ M c)) := by
  rw [isIntegralQExp_iff]
  intro n
  rw [PowerSeries.coeff_mk, qExpansion_B_coeff]

def E4Γ : ModularForm Γ₁ᴳ 4 := restrictForm (Subgroup.map_le_range _ _) E₄

theorem coe_E4Γ : (⇑(E4Γ M) : ℍ → ℂ) = E₄ := rfl

theorem qExpansion_E4Γ : qExpansion 1 (⇑(E4Γ M)) = eisenstein4.map (Int.castRingHom ℂ) := by
  rw [coe_E4Γ]
  exact ModularCurve.qExpansion_E4_eq_map_eisenstein4

theorem E4Γ_slash (γ : SL(2, ℤ)) : (⇑(E4Γ M) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(E4Γ M) := by
  rw [coe_E4Γ, ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq E₄ _ ⟨γ, rfl⟩

def Wsq (t : ZMod M) : ModularForm Γ₁ᴳ 4 := ((W M t).mul (W M t)).mcast (by norm_num)

theorem coe_Wsq (t : ZMod M) : (⇑(Wsq M t) : ℍ → ℂ) = ⇑(W M t) * ⇑(W M t) := by
  rw [Wsq, coe_mcast, ModularForm.coe_mul]

def Fform (t : ZMod M) : ModularForm Γ₁ᴳ 4 := (24 : ℂ)⁻¹ • (Wsq M t - E4Γ M)

theorem coe_Fform (t : ZMod M) :
    (⇑(Fform M t) : ℍ → ℂ) = (24 : ℂ)⁻¹ • (⇑(W M t) * ⇑(W M t) - ⇑(E4Γ M)) := by
  rw [Fform, IsGLPos.coe_smul, ModularForm.coe_sub, coe_Wsq]

theorem qExpansion_Fform (t : ZMod M) (ht : t ≠ 0) : qExpansion 1 (Fform M t) = fS (ψ (hμ M) t) := by
  rw [Fform, qExpansion_smul', ModularForm.coe_sub,
    ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods M) (Wsq M t) (E4Γ M), coe_Wsq,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M) (W M t) (W M t),
    qExpansion_W M t ht, qExpansion_E4Γ, eisenstein4_map_eq, wS_eq', fS_eq', PowerSeries.smul_eq_C_mul]
  set x := xS (ψ (hμ M) t)
  set a := tateA4.map (Int.castRingHom ℂ)
  have h : (1 + 12 * x) * (1 + 12 * x) - (1 - 48 * a) = 24 * (x + 6 * (x * x) + 2 * a) := by ring
  rw [h, ← mul_assoc, show PowerSeries.C (24 : ℂ)⁻¹ * (24 : PowerSeries ℂ) = 1 by
    rw [← map_ofNat PowerSeries.C 24, ← map_mul, inv_mul_cancel₀ (by norm_num), map_one], one_mul]

theorem qExpansion_Fform_coeff (t : ZMod M) (ht : t ≠ 0) (n : ℕ) :
    (qExpansion 1 (Fform M t)).coeff n = fcoef (ψ (hμ M) t) n := by
  rw [qExpansion_Fform M t ht, fS, PowerSeries.coeff_mk]

theorem Fform_slash (t : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(Fform M t) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(Fform M (t * ((γ 1 1 : ℤ) : ZMod M))) := by
  rw [coe_Fform, coe_Fform, ModularForm.SL_smul_slash, sub_eq_add_neg, SlashAction.add_slash,
    SlashAction.neg_slash, E4Γ_slash, ← sub_eq_add_neg]
  congr 2
  have h := ModularForm.mul_slash_SL2 2 2 γ (⇑(W M t)) (⇑(W M t))
  rw [show (2 : ℤ) + 2 = 4 by norm_num] at h
  rw [h, W_slash M t γ hγ]

def D (c : ZMod M) : ModularForm Γ₁ᴳ 4 :=
  ((M : ℂ) ^ 4) • ∑ t ∈ nz M, (ψ (hμ M) (-(t * c))) • Fform M t

theorem coe_D (c : ZMod M) :
    (⇑(D M c) : ℍ → ℂ) = ((M : ℂ) ^ 4) • ∑ t ∈ nz M, (ψ (hμ M) (-(t * c))) • (⇑(Fform M t) : ℍ → ℂ) := by
  rw [D, IsGLPos.coe_smul, coe_finset_sum]
  simp only [IsGLPos.coe_smul]

theorem qExpansion_D_coeff (c : ZMod M) (n : ℕ) :
    (qExpansion 1 (D M c)).coeff n = ((dZ M c n : ℤ) : ℂ) := by
  rw [D, qExpansion_smul', qExpansion_finset_sum, dZ_eq_sum (hμ M)]
  simp only [map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [qExpansion_smul', map_smul, smul_eq_mul, qExpansion_Fform_coeff M t (Finset.mem_filter.mp ht).2]
  ring

theorem isIntegralQExp_D (c : ZMod M) : IsIntegralQExp (⇑(D M c)) (PowerSeries.mk (dZ M c)) := by
  rw [isIntegralQExp_iff]
  intro n
  rw [PowerSeries.coeff_mk, qExpansion_D_coeff]

theorem det_mod {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ((γ 1 1 : ℤ) : ZMod M) * ((γ 0 0 : ℤ) : ZMod M) = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have h := congrArg (fun z : ℤ => (z : ZMod M)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at h
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ
  rw [hc, mul_zero, sub_zero, mul_comm] at h
  exact h

theorem sum_reindex {V : Type*} [AddCommMonoid V] [Module ℂ V] (G : ZMod M → V) (c : ZMod M)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ∑ t ∈ nz M, (ψ (hμ M) (-(t * c))) • G (t * ((γ 1 1 : ℤ) : ZMod M)) =
      ∑ t ∈ nz M, (ψ (hμ M) (-(t * (c * ((γ 0 0 : ℤ) : ZMod M))))) • G t := by
  set δ : ZMod M := ((γ 1 1 : ℤ) : ZMod M) with hδ
  set a : ZMod M := ((γ 0 0 : ℤ) : ZMod M) with ha
  have hda : δ * a = 1 := det_mod M hγ
  refine Finset.sum_nbij' (fun t => t * δ) (fun t => t * a) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [nz, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    intro h
    apply ht
    have : t * δ * a = 0 := by rw [h, zero_mul]
    rwa [mul_assoc, hda, mul_one] at this
  · intro t ht
    simp only [nz, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    intro h
    apply ht
    have : t * a * δ = 0 := by rw [h, zero_mul]
    rwa [mul_assoc, mul_comm a δ, hda, mul_one] at this
  · intro t _
    rw [mul_assoc, hda, mul_one]
  · intro t _
    rw [mul_assoc, mul_comm a δ, hda, mul_one]
  · intro t _
    congr 2
    linear_combination (t * c) * hda

theorem B_slash (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(B M c) : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑(B M (c * ((γ 0 0 : ℤ) : ZMod M))) := by
  rw [coe_B, coe_B, ModularForm.SL_smul_slash, finset_sum_slash]
  congr 1
  have h : ∀ t ∈ nz M, ((ψ (hμ M) (-(t * c))) • (⇑(W M t) : ℍ → ℂ)) ∣[(2 : ℤ)] γ =
      (ψ (hμ M) (-(t * c))) • (⇑(W M (t * ((γ 1 1 : ℤ) : ZMod M))) : ℍ → ℂ) := by
    intro t _
    rw [ModularForm.SL_smul_slash, W_slash M t γ hγ]
  rw [Finset.sum_congr rfl h]
  exact sum_reindex M (fun t => (⇑(W M t) : ℍ → ℂ)) c hγ

theorem D_slash (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(D M c) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(D M (c * ((γ 0 0 : ℤ) : ZMod M))) := by
  rw [coe_D, coe_D, ModularForm.SL_smul_slash, finset_sum_slash]
  congr 1
  have h : ∀ t ∈ nz M, ((ψ (hμ M) (-(t * c))) • (⇑(Fform M t) : ℍ → ℂ)) ∣[(4 : ℤ)] γ =
      (ψ (hμ M) (-(t * c))) • (⇑(Fform M (t * ((γ 1 1 : ℤ) : ZMod M))) : ℍ → ℂ) := by
    intro t _
    rw [ModularForm.SL_smul_slash, Fform_slash M t γ hγ]
  rw [Finset.sum_congr rfl h]
  exact sum_reindex M (fun t => (⇑(Fform M t) : ℍ → ℂ)) c hγ

end OverComplex

section AnyField

variable {M : ℕ} [NeZero M] (K : Type*) [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)

theorem toricPoint_fst_eq (u : K) : (toricPoint K 1 u).1 = ofPowerSeries ℤ K (xS u) := by
  rw [toricPoint_fst]
  congr 1
  ext m
  rw [PowerSeries.coeff_mk, xS, PowerSeries.coeff_mk, xcoef]
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, if_false, one_dvd, if_true, Nat.div_one]
    congr 1
    exact Nat.sum_div_divisors m (fun d => (d : K) * (u ^ d + u⁻¹ ^ d))

theorem intSeriesC_eq (p : PowerSeries ℤ) : intSeriesC K p = ofPowerSeries ℤ K (p.map (Int.castRingHom K)) := rfl

theorem smul_ofPowerSeries (a : K) (P : PowerSeries K) :
    a • ofPowerSeries ℤ K P = ofPowerSeries ℤ K (PowerSeries.C a * P) := by
  rw [map_mul, ofPowerSeries_C, C_mul_eq_smul]

include hζ in

theorem weightTwo (s : ZMod M) (hs : s ≠ 0) :
    (M : LaurentSeries K) ^ 3 * (1 + 12 * (toricPoint K 1 (ζ ^ s.val)).1) =
      ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (PowerSeries.mk (bZ M c)) := by
  have hu : ζ ^ s.val = ψ hζ s := rfl
  rw [toricPoint_fst_eq, hu]

  have lhs : (M : LaurentSeries K) ^ 3 * (1 + 12 * ofPowerSeries ℤ K (xS (ψ hζ s))) =
      ofPowerSeries ℤ K (PowerSeries.C ((M : K) ^ 3) * wS (ψ hζ s)) := by
    rw [wS_eq', map_mul, map_add, map_one, map_mul, map_ofNat, ofPowerSeries_C, map_pow, map_natCast]
  have rhs : ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (PowerSeries.mk (bZ M c)) =
      ofPowerSeries ℤ K (∑ c : ZMod M, PowerSeries.C (ψ hζ (s * c)) *
        (PowerSeries.mk (bZ M c)).map (Int.castRingHom K)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [intSeriesC_eq, smul_ofPowerSeries]
    rfl
  rw [lhs, rhs]
  congr 1
  ext n
  rw [PowerSeries.coeff_C_mul, map_sum, wS, PowerSeries.coeff_mk, ← sum_ψ_bZ hζ s hs n]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]

include hζ in

theorem weightFour (s : ZMod M) (hs : s ≠ 0) :
    (M : LaurentSeries K) ^ 5 * ((toricPoint K 1 (ζ ^ s.val)).1 + 6 * (toricPoint K 1 (ζ ^ s.val)).1 ^ 2 +
        2 * (tateLaurent K).a₄) =
      ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (PowerSeries.mk (dZ M c)) := by
  have hu : ζ ^ s.val = ψ hζ s := rfl
  rw [toricPoint_fst_eq, hu, tateLaurent_a₄, laurentOfInt_apply]
  have lhs : (M : LaurentSeries K) ^ 5 * (ofPowerSeries ℤ K (xS (ψ hζ s)) +
      6 * ofPowerSeries ℤ K (xS (ψ hζ s)) ^ 2 + 2 * ofPowerSeries ℤ K (tateA4.map (Int.castRingHom K))) =
      ofPowerSeries ℤ K (PowerSeries.C ((M : K) ^ 5) * fS (ψ hζ s)) := by
    simp only [fS_eq', map_mul, map_add, map_ofNat, map_pow, map_natCast, sq]
  have rhs : ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (PowerSeries.mk (dZ M c)) =
      ofPowerSeries ℤ K (∑ c : ZMod M, PowerSeries.C (ψ hζ (s * c)) *
        (PowerSeries.mk (dZ M c)).map (Int.castRingHom K)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [intSeriesC_eq, smul_ofPowerSeries]
    rfl
  rw [lhs, rhs]
  congr 1
  ext n
  rw [PowerSeries.coeff_C_mul, map_sum, fS, PowerSeries.coeff_mk, ← sum_ψ_dZ hζ s hs n]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]

end AnyField

theorem main (M : ℕ) [NeZero M] :
    ∃ (B : ZMod M → ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2)
      (D : ZMod M → ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 4)
      (b d : ZMod M → PowerSeries ℤ),
      (∀ c : ZMod M, IsIntegralQExp (B c) (b c)) ∧
      (∀ c : ZMod M, IsIntegralQExp (D c) (d c)) ∧
      (∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ Gamma0 M →
        (⇑(B c) : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑(B (c * ((γ 0 0 : ℤ) : ZMod M))) ∧
        (⇑(D c) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(D (c * ((γ 0 0 : ℤ) : ZMod M)))) ∧
      ∀ (K : Type*) [Field K] (ζ : K), IsPrimitiveRoot ζ M → ∀ s : ZMod M, s ≠ 0 →
        (M : LaurentSeries K) ^ 3 * (1 + 12 * (toricPoint K 1 (ζ ^ s.val)).1) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (b c) ∧
        (M : LaurentSeries K) ^ 5 *
            ((toricPoint K 1 (ζ ^ s.val)).1 + 6 * (toricPoint K 1 (ζ ^ s.val)).1 ^ 2 +
              2 * (tateLaurent K).a₄) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (d c) :=
  ⟨B M, D M, fun c => PowerSeries.mk (bZ M c), fun c => PowerSeries.mk (dZ M c),
    isIntegralQExp_B M, isIntegralQExp_D M, fun c γ hγ => ⟨B_slash M c γ hγ, D_slash M c γ hγ⟩,
    fun K _ ζ hζ s hs => ⟨weightTwo K hζ s hs, weightFour K hζ s hs⟩⟩

end ToricFourier

end

universe u in
open scoped MatrixGroups ModularForm in

theorem solution (M : ℕ) [NeZero M] :
    ∃ (B : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 2)
      (D : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 4)
      (b d : ZMod M → PowerSeries ℤ),
      (∀ c : ZMod M, ModularCurve.IsIntegralQExp (B c) (b c)) ∧
      (∀ c : ZMod M, ModularCurve.IsIntegralQExp (D c) (d c)) ∧
      (∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(B c) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ = ⇑(B (c * ((γ 0 0 : ℤ) : ZMod M))) ∧
        (⇑(D c) : UpperHalfPlane → ℂ) ∣[(4 : ℤ)] γ = ⇑(D (c * ((γ 0 0 : ℤ) : ZMod M)))) ∧
      ∀ (K : Type u) [Field K] (ζ : K), IsPrimitiveRoot ζ M → ∀ s : ZMod M, s ≠ 0 →
        (M : LaurentSeries K) ^ 3 * (1 + 12 * (ModularCurve.toricPoint K 1 (ζ ^ s.val)).1) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • ModularCurve.intSeriesC K (b c) ∧
        (M : LaurentSeries K) ^ 5 *
            ((ModularCurve.toricPoint K 1 (ζ ^ s.val)).1 +
                6 * (ModularCurve.toricPoint K 1 (ζ ^ s.val)).1 ^ 2 +
              2 * (ModularCurve.tateLaurent K).a₄) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • ModularCurve.intSeriesC K (d c) :=
  ToricFourier.main M

end S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum
end P2MW
export P2MW.S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum (solution)
