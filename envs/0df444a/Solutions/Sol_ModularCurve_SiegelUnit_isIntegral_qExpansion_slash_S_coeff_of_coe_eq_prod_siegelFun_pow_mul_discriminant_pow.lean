-- Prove2me | solution 1 for ModularCurve.SiegelUnit.isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/09dcaf7e-d52c-5c75-b35c-9a3059960e34

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul
import Theorems.Thm_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow
import Theorems.Thm_ModularCurve_qParam_coeff_unique
import Theorems.Thm_ModularCurve_hasSum_qParam_mul
import Theorems.Thm_ModularCurve_hasSum_coeff_etaProd_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped Real Manifold MatrixGroups ModularForm Topology Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "siegelFun etaProd constantCoeff_etaProd SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow qParam_coeff_unique hasSum_qParam_mul hasSum_coeff_etaProd_pow"
namespace SiegelUnit
p2m_export "ModularCurve.SiegelUnit" "prod_siegelFun_pow_specialLinearGroup_smul exists_isIntegral_hasSum_prod_siegelFun_pow"
namespace IntZero
p2m_open "ModularCurve.SiegelUnit ModularCurve"

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Group

variable {N : ℕ}

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.T]

theorem T_pow_mem_Gamma (N : ℕ) : ModularGroup.T ^ N ∈ CongruenceSubgroup.Gamma N := by
  rw [Gamma_mem, ← zpow_natCast]
  simp only [ModularGroup.coe_T_zpow]
  simp

theorem Gamma_le_Gamma1 (N : ℕ) : CongruenceSubgroup.Gamma N ≤ Gamma1 N := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

theorem conj_mem_Gamma (α : SL(2, ℤ)) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma N) :
    α * g * α⁻¹ ∈ CongruenceSubgroup.Gamma N :=
  (Gamma_normal N).conj_mem g hg α

theorem coeGL_mul (β γ : SL(2, ℤ)) :
    ((β * γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (β : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) :=
  map_mul (Matrix.SpecialLinearGroup.mapGL ℝ) β γ

theorem coeGL_inv (β : SL(2, ℤ)) :
    ((β⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (β : GL (Fin 2) ℝ)⁻¹ :=
  map_inv (Matrix.SpecialLinearGroup.mapGL ℝ) β

def GammaS (N : ℕ) : Subgroup SL(2, ℤ) :=
  (ConjAct.toConjAct ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹ • Γ₁(N)).comap
    (Matrix.SpecialLinearGroup.mapGL ℝ)

theorem mem_conj_iff (g x : GL (Fin 2) ℝ) (Γ : Subgroup (GL (Fin 2) ℝ)) :
    x ∈ ConjAct.toConjAct g⁻¹ • Γ ↔ g * x * g⁻¹ ∈ Γ := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]

theorem mem_GammaS_iff {γ : SL(2, ℤ)} :
    γ ∈ GammaS N ↔ ((ModularGroup.S * γ * ModularGroup.S⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ Γ₁(N) := by
  rw [GammaS, Subgroup.mem_comap, mem_conj_iff, coeGL_mul, coeGL_mul, coeGL_inv]
  rfl

theorem mem_GammaS_of {γ : SL(2, ℤ)} (h : ModularGroup.S * γ * ModularGroup.S⁻¹ ∈ Gamma1 N) :
    γ ∈ GammaS N :=
  mem_GammaS_iff.mpr ⟨_, h, rfl⟩

theorem Gamma_le_GammaS (N : ℕ) : CongruenceSubgroup.Gamma N ≤ GammaS N := fun _ hγ =>
  mem_GammaS_of (Gamma_le_Gamma1 N (conj_mem_Gamma ModularGroup.S hγ))

scoped instance instFiniteIndexGammaS (N : ℕ) [NeZero N] : (GammaS N).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaS N)

theorem T_pow_mem_GammaS (N : ℕ) : ModularGroup.T ^ N ∈ GammaS N :=
  Gamma_le_GammaS N (T_pow_mem_Gamma N)

theorem natCast_mem_strictPeriods_GammaS (N : ℕ) :
    (N : ℝ) ∈ ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T ^ N, T_pow_mem_GammaS N, ?_⟩
  apply Units.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    ← zpow_natCast, ModularGroup.coe_T_zpow]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom_apply]

theorem GammaS_le_conjS (N : ℕ) :
    ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹ • Γ₁(N) :=
  Subgroup.map_comap_le _ _

end Group

section Forms

variable {N : ℕ} [NeZero N] {w : ℤ}

def restrictMF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ' ≤ Γ) (f : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

def Thetaform (ϑ : ModularForm Γ₁(N) w) :
    ModularForm ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) w :=
  restrictMF (GammaS_le_conjS N)
    (ModularForm.translate ϑ ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))

theorem coe_Thetaform (ϑ : ModularForm Γ₁(N) w) :
    (⇑(Thetaform ϑ) : ℍ → ℂ) = (⇑ϑ : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) :=
  rfl

theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

end Forms

section QSeries

theorem hasSum_shift {q : ℂ} {b : ℕ → ℂ} {v : ℂ} (M : ℕ)
    (h : HasSum (fun n : ℕ => b n * q ^ (n + M)) v) :
    HasSum (fun n : ℕ => (if M ≤ n then b (n - M) else 0) * q ^ n) v := by
  set a : ℕ → ℂ := fun n => (if M ≤ n then b (n - M) else 0) * q ^ n with ha
  have h1 : (fun n : ℕ => a (n + M)) = fun n : ℕ => b n * q ^ (n + M) := by
    funext n
    simp [ha]
  have h2 : ∑ i ∈ Finset.range M, a i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : ¬ M ≤ i := Nat.not_le.mpr (Finset.mem_range.mp hi)
    simp [ha, hi']
  rw [← h1] at h
  have h3 := (hasSum_nat_add_iff (f := a) M).mp h
  rwa [h2, add_zero] at h3

theorem hasSum_spread {q : ℂ} {c : ℕ → ℂ} {v : ℂ} (N : ℕ) (hN : 0 < N)
    (h : HasSum (fun k : ℕ => c k * (q ^ N) ^ k) v) :
    HasSum (fun n : ℕ => (if N ∣ n then c (n / N) else 0) * q ^ n) v := by
  have hinj : Function.Injective (fun k : ℕ => N * k) := fun a b hab =>
    Nat.eq_of_mul_eq_mul_left hN hab
  have key : (fun n : ℕ => (if N ∣ n then c (n / N) else 0) * q ^ n) =
      Function.extend (fun k : ℕ => N * k) (fun k : ℕ => c k * (q ^ N) ^ k) 0 := by
    funext n
    by_cases hn : N ∣ n
    · obtain ⟨k, rfl⟩ := hn
      rw [hinj.extend_apply]
      simp [Nat.mul_div_cancel_left k hN, pow_mul]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨k, rfl⟩; exact hn ⟨k, rfl⟩)]
      simp [hn]
  rw [key]
  exact (hasSum_extend_zero hinj).mpr h

theorem qExpansion_coeff_eq_of_hasSum_div_qParam_zpow {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : ModularForm Γ k) (h : ℝ) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (M : ℤ) (b : ℕ → ℂ)
    (hb0 : b 0 ≠ 0)
    (hb : ∀ τ : ℍ, HasSum (fun n : ℕ => b n * Periodic.qParam h (τ : ℂ) ^ n)
      (f τ / Periodic.qParam h (τ : ℂ) ^ M)) :
    0 ≤ M ∧ ∀ n : ℕ, (qExpansion h (⇑f : ℍ → ℂ)).coeff n =
      if M ≤ (n : ℤ) then b (n - M.toNat) else 0 := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hq0 : ∀ τ : ℍ, Periodic.qParam h (τ : ℂ) ≠ 0 := fun τ => Periodic.qParam_ne_zero _
  have hf : ∀ τ : ℍ, HasSum (fun n : ℕ => (qExpansion h (⇑f : ℍ → ℂ)).coeff n *
      Periodic.qParam h (τ : ℂ) ^ n) (f τ) := fun τ => by
    simpa only [smul_eq_mul] using hasSum_qExpansion hh
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) f.holo' (ModularFormClass.bdd_at_infty f) τ
  rcases le_or_gt 0 M with hM | hM
  · obtain ⟨M', rfl⟩ := Int.eq_ofNat_of_zero_le hM
    refine ⟨hM, fun n => ?_⟩
    have hb' : ∀ τ : ℍ, HasSum (fun n : ℕ => (if M' ≤ n then b (n - M') else 0) *
        Periodic.qParam h (τ : ℂ) ^ n) (f τ) := fun τ => by
      refine hasSum_shift (b := b) M' ?_
      have h1 := (hb τ).mul_right (Periodic.qParam h (τ : ℂ) ^ M')
      rw [zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ (hq0 τ))] at h1
      convert h1 using 1 <;> try with_reducible_and_instances rfl
      funext n
      rw [pow_add]
      ring
    have huniq := ModularCurve.qParam_coeff_unique h hh (⇑f) _ _ hf hb'
    rw [congr_fun huniq n]
    simp only [Int.toNat_natCast, Nat.cast_le]
  · exfalso
    obtain ⟨M', hM'⟩ := Int.exists_eq_neg_ofNat hM.le
    have hM'pos : 0 < M' := by omega
    have hb2 : ∀ τ : ℍ, HasSum (fun n : ℕ => b n * Periodic.qParam h (τ : ℂ) ^ n)
        (f τ * Periodic.qParam h (τ : ℂ) ^ M') := fun τ => by
      have h1 := hb τ
      rwa [hM', zpow_neg, zpow_natCast, div_inv_eq_mul] at h1
    have hf2 : ∀ τ : ℍ, HasSum (fun n : ℕ =>
        (if M' ≤ n then (qExpansion h (⇑f : ℍ → ℂ)).coeff (n - M') else 0) *
          Periodic.qParam h (τ : ℂ) ^ n) (f τ * Periodic.qParam h (τ : ℂ) ^ M') := fun τ => by
      refine hasSum_shift (b := fun n : ℕ => (qExpansion h (⇑f : ℍ → ℂ)).coeff n) M' ?_
      have h1 := (hf τ).mul_right (Periodic.qParam h (τ : ℂ) ^ M')
      convert h1 using 1 <;> try with_reducible_and_instances rfl
      funext n
      rw [pow_add]
      ring
    have huniq := ModularCurve.qParam_coeff_unique h hh
      (fun τ : ℍ => f τ * Periodic.qParam h (τ : ℂ) ^ M') _ _ hf2 hb2
    have h0 := congr_fun huniq 0
    have : ¬ M' ≤ 0 := Nat.not_le.mpr hM'pos
    simp only [this, if_false] at h0
    exact hb0 h0.symm

end QSeries

section Siegel

variable (N : ℕ)

def uProd [NeZero N] (m : ZMod N → ZMod N → ℕ) (τ : ℍ) : ℂ :=
  ∏ r : ZMod N, ∏ s : ZMod N, siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)

theorem siegelFun_zero_zero (z : ℂ) : siegelFun N 0 0 z = 0 := by
  simp [ModularCurve.siegelFun]

theorem uProd_eq_zero [NeZero N] {m : ZMod N → ZMod N → ℕ} (hm : m 0 0 ≠ 0) (τ : ℍ) :
    uProd N m τ = 0 := by
  unfold uProd
  apply Finset.prod_eq_zero (Finset.mem_univ (0 : ZMod N))
  apply Finset.prod_eq_zero (Finset.mem_univ (0 : ZMod N))
  rw [ZMod.val_zero, Nat.cast_zero, siegelFun_zero_zero, zero_pow]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (NeZero.ne N)) hm

theorem uProd_S_smul [NeZero N] (m : ZMod N → ZMod N → ℕ) (τ : ℍ) :
    uProd N m (ModularGroup.S • τ) = uProd N (fun r s => m (-s) r) τ := by
  have h := (ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul N m).1 ModularGroup.S τ
  have e00 : ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 0 := by
    rw [ModularGroup.coe_S]; rfl
  have e01 : ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -1 := by
    rw [ModularGroup.coe_S]; rfl
  have e10 : ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    rw [ModularGroup.coe_S]; rfl
  have e11 : ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 := by
    rw [ModularGroup.coe_S]; rfl
  unfold uProd
  rw [h]
  simp only [e00, e01, e10, e11, mul_zero, zero_add, mul_one, add_zero, mul_neg, Int.cast_neg,
    Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  exact Fintype.prod_equiv (Equiv.neg (ZMod N)) _ _ (fun r => by simp)

theorem slash_S_apply [NeZero N] (m : ZMod N → ZMod N → ℕ) (t : ℕ)
    (ϑ : ModularForm Γ₁(N) (12 * (t : ℤ)))
    (hϑ : ∀ τ : ℍ, ϑ τ = uProd N m τ * ModularForm.discriminant τ ^ t) (τ : ℍ) :
    ((⇑ϑ : ℍ → ℂ) ∣[12 * (t : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ =
      uProd N m (ModularGroup.S • τ) * ModularForm.discriminant τ ^ t := by
  have hz : ((τ : ℍ) : ℂ) ≠ 0 := τ.ne_zero
  have hS := congrFun ModularForm.discriminant_S_invariant τ
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S] at hS

  have hΔ : ModularForm.discriminant (ModularGroup.S • τ) =
      ModularForm.discriminant τ * (τ : ℂ) ^ (12 : ℕ) := by
    have h12 : ((τ : ℂ) ^ (-(12 : ℤ))) * (τ : ℂ) ^ (12 : ℕ) = 1 := by
      rw [zpow_neg, show ((12 : ℤ)) = ((12 : ℕ) : ℤ) by norm_num, zpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero _ hz)]
    calc ModularForm.discriminant (ModularGroup.S • τ)
        = ModularForm.discriminant (ModularGroup.S • τ) * (((τ : ℂ) ^ (-(12 : ℤ))) * (τ : ℂ) ^ (12 : ℕ)) := by
          rw [h12, mul_one]
      _ = (ModularForm.discriminant (ModularGroup.S • τ) * (τ : ℂ) ^ (-(12 : ℤ))) * (τ : ℂ) ^ (12 : ℕ) := by
          ring
      _ = ModularForm.discriminant τ * (τ : ℂ) ^ (12 : ℕ) := by rw [hS]
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, ModularGroup.denom_S, hϑ, hΔ]
  have h2 : ((τ : ℂ) ^ (12 : ℕ)) ^ t * (τ : ℂ) ^ (-(12 * (t : ℤ))) = 1 := by
    rw [← pow_mul, zpow_neg, show (12 * (t : ℤ)) = ((12 * t : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      mul_inv_cancel₀ (pow_ne_zero _ hz)]
  rw [mul_pow]
  calc uProd N m (ModularGroup.S • τ) * (ModularForm.discriminant τ ^ t * ((τ : ℂ) ^ (12 : ℕ)) ^ t) *
        (τ : ℂ) ^ (-(12 * (t : ℤ)))
      = uProd N m (ModularGroup.S • τ) * ModularForm.discriminant τ ^ t *
          (((τ : ℂ) ^ (12 : ℕ)) ^ t * (τ : ℂ) ^ (-(12 * (t : ℤ)))) := by ring
    _ = uProd N m (ModularGroup.S • τ) * ModularForm.discriminant τ ^ t := by rw [h2, mul_one]

end Siegel

section Delta

theorem qParam_one_eq_pow (N : ℕ) (hN : 0 < N) (z : ℂ) :
    Periodic.qParam 1 z = Periodic.qParam N z ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

theorem hasSum_discriminant_pow (t : ℕ) (τ : ℍ) :
    HasSum (fun k : ℕ => ((PowerSeries.coeff k (etaProd ^ (24 * t)) : ℤ) : ℂ) *
        Periodic.qParam 1 (τ : ℂ) ^ k)
      (ModularForm.discriminant τ ^ t / Periodic.qParam 1 (τ : ℂ) ^ t) := by
  have hq : ‖Periodic.qParam 1 (τ : ℂ)‖ < 1 := by
    simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have h24 : Periodic.qParam 24 (τ : ℂ) ^ 24 = Periodic.qParam 1 (τ : ℂ) :=
    (qParam_one_eq_pow 24 (by norm_num) (τ : ℂ)).symm
  have hΔ : ModularForm.discriminant τ =
      Periodic.qParam 1 (τ : ℂ) * (∏' n : ℕ, (1 - Periodic.qParam 1 (τ : ℂ) ^ (n + 1))) ^ 24 := by
    simp only [ModularForm.discriminant, ModularForm.eta, ModularForm.eta_q, mul_pow, h24]
  have key : ModularForm.discriminant τ ^ t / Periodic.qParam 1 (τ : ℂ) ^ t =
      (∏' n : ℕ, (1 - Periodic.qParam 1 (τ : ℂ) ^ (n + 1))) ^ (24 * t) := by
    rw [hΔ, mul_pow, ← pow_mul,
      mul_div_cancel_left₀ _ (pow_ne_zero _ (Periodic.qParam_ne_zero _))]
  rw [key]
  exact ModularCurve.hasSum_coeff_etaProd_pow (24 * t) hq

end Delta

section Main

variable (N : ℕ) [NeZero N]

theorem isIntegral_intCast (z : ℤ) : IsIntegral ℤ (z : ℂ) := by
  have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := z)
  simpa using this

theorem main (m : ZMod N → ZMod N → ℕ) (t : ℕ)
    (ϑ : ModularForm Γ₁(N) (12 * (t : ℤ)))
    (hϑ : ∀ τ : ℍ, ϑ τ =
      (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t) (n : ℕ) :
    IsIntegral ℤ ((qExpansion (N : ℝ) (⇑(Thetaform ϑ) : ℍ → ℂ)).coeff n) := by
  have hN : 0 < N := NeZero.pos N
  have hϑ' : ∀ τ : ℍ, ϑ τ = uProd N m τ * ModularForm.discriminant τ ^ t := hϑ
  set Θ := Thetaform ϑ with hΘdef
  have hΘ : ∀ τ : ℍ, Θ τ = uProd N m (ModularGroup.S • τ) * ModularForm.discriminant τ ^ t :=
    fun τ => slash_S_apply N m t ϑ hϑ' τ
  by_cases hm : m 0 0 = 0
  swap
  ·
    have hΘ0 : ∀ τ : ℍ, Θ τ = 0 := fun τ => by
      rw [hΘ, uProd_eq_zero N hm, zero_mul]
    have hs : ∀ τ : ℍ, HasSum (fun k : ℕ => (fun _ : ℕ => (0 : ℂ)) k •
        Periodic.qParam (N : ℝ) (τ : ℂ) ^ k) (Θ τ) := fun τ => by
      simpa [hΘ0 τ] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
    have h0 := ModularFormClass.qExpansion_coeff_unique natCast_pos
      (natCast_mem_strictPeriods_GammaS N) (f := Θ) hs n
    rw [← h0]
    exact isIntegral_zero
  ·
    set e : ZMod N → ZMod N → ℕ := fun r s => m (-s) r with he_def
    have he : e 0 0 = 0 := by simp [he_def, hm]
    obtain ⟨C, d, hCN, hdint, -, hd0, -, hsum, -⟩ :=
      ModularCurve.SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow N e he
    set Ord : ℤ := ∑ r : ZMod N, ∑ s : ZMod N,
      (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2) with hOrd
    have hC0 : C ≠ 0 := by
      rintro rfl
      rw [zero_pow hN.ne'] at hCN
      exact zero_ne_one hCN
    have hCint : IsIntegral ℤ C :=
      IsIntegral.of_pow hN (by rw [hCN]; exact isIntegral_one)

    set qN : ℍ → ℂ := fun τ => Periodic.qParam (N : ℝ) (τ : ℂ) with hqN
    have hqN0 : ∀ τ : ℍ, qN τ ≠ 0 := fun τ => Periodic.qParam_ne_zero _
    have hqn : ∀ (τ : ℍ) (k : ℕ),
        cexp (2 * π * Complex.I * (k : ℂ) * (τ : ℂ) / (N : ℂ)) = qN τ ^ k := fun τ k => by
      change _ = cexp (2 * π * Complex.I * (τ : ℂ) / ((N : ℝ) : ℂ)) ^ k
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hOrdC : (∑ r : ZMod N, ∑ s : ZMod N, ((e r s : ℤ) : ℂ) *
        (6 * ((r.val : ℤ) : ℂ) ^ 2 - 6 * ((N : ℤ) : ℂ) * ((r.val : ℤ) : ℂ) + ((N : ℤ) : ℂ) ^ 2)) =
        ((Ord : ℤ) : ℂ) := by
      rw [hOrd]
      norm_cast
    have hqZ : ∀ τ : ℍ,
        cexp (2 * π * Complex.I * (∑ r : ZMod N, ∑ s : ZMod N, ((e r s : ℤ) : ℂ) *
          (6 * ((r.val : ℤ) : ℂ) ^ 2 - 6 * ((N : ℤ) : ℂ) * ((r.val : ℤ) : ℂ) + ((N : ℤ) : ℂ) ^ 2)) *
            (τ : ℂ) / (N : ℂ)) = qN τ ^ Ord := fun τ => by
      rw [hOrdC]
      change _ = cexp (2 * π * Complex.I * (τ : ℂ) / ((N : ℝ) : ℂ)) ^ Ord
      rw [← Complex.exp_int_mul]
      congr 1
      push_cast
      ring

    have hu : ∀ τ : ℍ, HasSum (fun k : ℕ => (C * d k) * qN τ ^ k) (uProd N e τ / qN τ ^ Ord) :=
      fun τ => by
      have h1 := (hsum τ).mul_left C
      convert h1 using 1 <;> try with_reducible_and_instances rfl
      · funext k
        rw [hqn]
        ring
      · change uProd N e τ / qN τ ^ Ord = C * (uProd N e τ / (C * _))
        rw [hqZ]
        field_simp

    set cN : ℕ → ℂ := fun k =>
      if N ∣ k then ((PowerSeries.coeff (k / N) (etaProd ^ (24 * t)) : ℤ) : ℂ) else 0 with hcN
    have hΔ : ∀ τ : ℍ, HasSum (fun k : ℕ => cN k * qN τ ^ k)
        (ModularForm.discriminant τ ^ t / qN τ ^ (N * t)) := fun τ => by
      have h1 := hasSum_discriminant_pow t τ
      rw [qParam_one_eq_pow N hN (τ : ℂ)] at h1
      have h2 := hasSum_spread (q := qN τ)
        (c := fun k : ℕ => ((PowerSeries.coeff k (etaProd ^ (24 * t)) : ℤ) : ℂ)) N hN h1
      rwa [← pow_mul] at h2

    set A : PowerSeries ℂ := PowerSeries.mk fun k => C * d k with hA
    set B : PowerSeries ℂ := PowerSeries.mk cN with hB
    have hAB : ∀ τ : ℍ, HasSum (fun k : ℕ => PowerSeries.coeff k (A * B) * qN τ ^ k)
        (Θ τ / qN τ ^ (Ord + ((N * t : ℕ) : ℤ))) := fun τ => by
      have h1 := ModularCurve.hasSum_qParam_mul (N : ℝ) natCast_pos A B
        (fun τ => uProd N e τ / qN τ ^ Ord)
        (fun τ => ModularForm.discriminant τ ^ t / qN τ ^ (N * t))
        (fun τ => by simpa only [hA, PowerSeries.coeff_mk] using hu τ)
        (fun τ => by simpa only [hB, PowerSeries.coeff_mk] using hΔ τ) τ
      have h2 : Θ τ = uProd N e τ * ModularForm.discriminant τ ^ t := by
        rw [hΘ, uProd_S_smul]
      convert h1 using 1
      rw [zpow_add₀ (hqN0 τ), zpow_natCast, div_mul_div_comm, h2]

    have hcN0 : cN 0 = 1 := by
      simp [hcN, PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_etaProd]
    have hb0 : PowerSeries.coeff 0 (A * B) ≠ 0 := by
      rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      simp only [hA, hB, PowerSeries.coeff_mk, hcN0, mul_one]
      exact mul_ne_zero hC0 hd0

    have hcNint : ∀ k : ℕ, IsIntegral ℤ (cN k) := fun k => by
      simp only [hcN]
      split_ifs
      · exact isIntegral_intCast _
      · exact isIntegral_zero
    have hABint : ∀ k : ℕ, IsIntegral ℤ (PowerSeries.coeff k (A * B)) := fun k => by
      rw [PowerSeries.coeff_mul]
      refine IsIntegral.sum _ fun p _ => ?_
      simp only [hA, hB, PowerSeries.coeff_mk]
      exact (hCint.mul (hdint _)).mul (hcNint _)

    obtain ⟨-, hcoeff⟩ := qExpansion_coeff_eq_of_hasSum_div_qParam_zpow Θ (N : ℝ) natCast_pos
      (natCast_mem_strictPeriods_GammaS N) (Ord + ((N * t : ℕ) : ℤ))
      (fun k => PowerSeries.coeff k (A * B)) hb0 hAB
    rw [hcoeff n]
    split_ifs
    · exact hABint _
    · exact isIntegral_zero

end Main

end ModularCurve.SiegelUnit.IntZero
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.ModularCurve P2MW.S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.ModularCurve.SiegelUnit P2MW.S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.ModularCurve.SiegelUnit.IntZero"
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.ModularCurve P2MW.S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.ModularCurve.SiegelUnit"
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.ModularCurve P2MW.S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.ModularCurve.SiegelUnit P2MW.S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.ModularCurve.SiegelUnit.IntZero"

open scoped MatrixGroups ModularForm in

theorem solution
    (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t : ℕ)
    (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)))
    (hϑ : ∀ τ : UpperHalfPlane, ϑ τ =
      (∏ r : ZMod N, ∏ s : ZMod N,
          ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t) :
    ∃ a : ℕ, ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
      ((⇑ϑ : UpperHalfPlane → ℂ) ∣[12 * (t : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n) := by
  refine ⟨0, fun n => ?_⟩
  rw [pow_zero, one_mul]
  exact ModularCurve.SiegelUnit.IntZero.main N m t ϑ hϑ n

end S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow (solution)
