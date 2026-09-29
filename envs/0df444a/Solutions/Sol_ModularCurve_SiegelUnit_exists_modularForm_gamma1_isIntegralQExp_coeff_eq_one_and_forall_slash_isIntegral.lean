-- Prove2me | solution 1 for ModularCurve.SiegelUnit.exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/32041798-1d06-5566-92ae-9f6f9bdf51ca

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul
import Theorems.Thm_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow
import Theorems.Thm_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
import Theorems.Thm_ModularCurve_qParam_coeff_unique
import Theorems.Thm_ModularCurve_hasSum_qParam_mul
import Theorems.Thm_ModularCurve_hasSum_coeff_etaProd_pow
import Definitions.Def_ModularCurve_LevelFunctionField
import Theorems.Thm_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div
import Theorems.Thm_ModularCurve_exists_algebraMap_int_eq_of_mem_zetaSubring_of_forall_algEquiv_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped Real Manifold MatrixGroups ModularForm Topology Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "siegelFun etaProd constantCoeff_etaProd IsIntegralQExp SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow SiegelUnit.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow qParam_coeff_unique hasSum_qParam_mul hasSum_coeff_etaProd_pow zetaQ isPrimitiveRoot_zetaQ zetaQ_pow zetaSubring zetaQ_mem_zetaSubring multipliable_one_sub_C_mul_X_pow siegelExponent siegelConstExponent siegelSeriesInt multipliable_siegelFactor_left multipliable_siegelFactor_right siegelSeries SiegelUnit.hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div exists_algebraMap_int_eq_of_mem_zetaSubring_of_forall_algEquiv_apply_eq"
namespace SiegelUnit
p2m_export "ModularCurve.SiegelUnit" "prod_siegelFun_pow_specialLinearGroup_smul exists_isIntegral_hasSum_prod_siegelFun_pow exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div"
namespace WF1A
p2m_open "ModularCurve.SiegelUnit ModularCurve"

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Group

variable {N : ℕ}

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

def GammaC (N : ℕ) (β : SL(2, ℤ)) : Subgroup SL(2, ℤ) :=
  (ConjAct.toConjAct ((β : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹ • Γ₁(N)).comap
    (Matrix.SpecialLinearGroup.mapGL ℝ)

theorem mem_conj_iff (g x : GL (Fin 2) ℝ) (Γ : Subgroup (GL (Fin 2) ℝ)) :
    x ∈ ConjAct.toConjAct g⁻¹ • Γ ↔ g * x * g⁻¹ ∈ Γ := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]

theorem mem_GammaC_iff {β γ : SL(2, ℤ)} :
    γ ∈ GammaC N β ↔ ((β * γ * β⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ Γ₁(N) := by
  rw [GammaC, Subgroup.mem_comap, mem_conj_iff, coeGL_mul, coeGL_mul, coeGL_inv]
  rfl

theorem mem_GammaC_of {β γ : SL(2, ℤ)} (h : β * γ * β⁻¹ ∈ Gamma1 N) : γ ∈ GammaC N β :=
  mem_GammaC_iff.mpr ⟨_, h, rfl⟩

theorem Gamma_le_GammaC (N : ℕ) (β : SL(2, ℤ)) : CongruenceSubgroup.Gamma N ≤ GammaC N β := fun _ hγ =>
  mem_GammaC_of (Gamma_le_Gamma1 N (conj_mem_Gamma β hγ))

scoped instance instFiniteIndexGammaC (N : ℕ) [NeZero N] (β : SL(2, ℤ)) : (GammaC N β).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaC N β)

theorem T_pow_mem_GammaC (N : ℕ) (β : SL(2, ℤ)) : ModularGroup.T ^ N ∈ GammaC N β :=
  Gamma_le_GammaC N β (T_pow_mem_Gamma N)

theorem natCast_mem_strictPeriods_GammaC (N : ℕ) (β : SL(2, ℤ)) :
    (N : ℝ) ∈ ((GammaC N β : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T ^ N, T_pow_mem_GammaC N β, ?_⟩
  apply Units.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    ← zpow_natCast, ModularGroup.coe_T_zpow]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom_apply]

theorem GammaC_le_conj (N : ℕ) (β : SL(2, ℤ)) :
    ((GammaC N β : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct ((β : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹ • Γ₁(N) :=
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

def ThetaC (ϑ : ModularForm Γ₁(N) w) (β : SL(2, ℤ)) :
    ModularForm ((GammaC N β : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) w :=
  restrictMF (GammaC_le_conj N β)
    (ModularForm.translate ϑ ((β : SL(2, ℤ)) : GL (Fin 2) ℝ))

theorem coe_ThetaC (ϑ : ModularForm Γ₁(N) w) (β : SL(2, ℤ)) :
    (⇑(ThetaC ϑ β) : ℍ → ℂ) = (⇑ϑ : ℍ → ℂ) ∣[w] ((β : SL(2, ℤ)) : GL (Fin 2) ℝ) :=
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
      convert h1 using 1
      all_goals try rfl
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
      convert h1 using 1
      all_goals try rfl
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

def rowMul [NeZero N] (β : SL(2, ℤ)) : ZMod N × ZMod N ≃ ZMod N × ZMod N where
  toFun p := (p.1 * ((β 0 0 : ℤ) : ZMod N) + p.2 * ((β 1 0 : ℤ) : ZMod N),
    p.1 * ((β 0 1 : ℤ) : ZMod N) + p.2 * ((β 1 1 : ℤ) : ZMod N))
  invFun p := (p.1 * ((β 1 1 : ℤ) : ZMod N) - p.2 * ((β 1 0 : ℤ) : ZMod N),
    - p.1 * ((β 0 1 : ℤ) : ZMod N) + p.2 * ((β 0 0 : ℤ) : ZMod N))
  left_inv p := by
    have hdet : ((β 0 0 : ℤ) : ZMod N) * ((β 1 1 : ℤ) : ZMod N) - ((β 0 1 : ℤ) : ZMod N) * ((β 1 0 : ℤ) : ZMod N) = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe β
      rw [Matrix.det_fin_two] at h
      have := congrArg (Int.cast : ℤ → ZMod N) h
      push_cast at this
      exact this
    ext
    · simp only; linear_combination (p.1) * hdet
    · simp only; linear_combination (p.2) * hdet
  right_inv p := by
    have hdet : ((β 0 0 : ℤ) : ZMod N) * ((β 1 1 : ℤ) : ZMod N) - ((β 0 1 : ℤ) : ZMod N) * ((β 1 0 : ℤ) : ZMod N) = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe β
      rw [Matrix.det_fin_two] at h
      have := congrArg (Int.cast : ℤ → ZMod N) h
      push_cast at this
      exact this
    ext
    · simp only; linear_combination (p.1) * hdet
    · simp only; linear_combination (p.2) * hdet

def expTransport [NeZero N] (β : SL(2, ℤ)) (m : ZMod N → ZMod N → ℕ) : ZMod N → ZMod N → ℕ :=
  fun r s => m ((rowMul N β).symm (r, s)).1 ((rowMul N β).symm (r, s)).2

theorem expTransport_zero_zero [NeZero N] (β : SL(2, ℤ)) (m : ZMod N → ZMod N → ℕ) :
    expTransport N β m 0 0 = m 0 0 := by
  simp [expTransport, rowMul]

theorem uProd_smul [NeZero N] (m : ZMod N → ZMod N → ℕ) (β : SL(2, ℤ)) (τ : ℍ) :
    uProd N m (β • τ) = uProd N (expTransport N β m) τ := by
  have h := (ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul N m).1 β τ
  unfold uProd
  rw [h]
  rw [← Fintype.prod_prod_type', ← Fintype.prod_prod_type']
  refine Fintype.prod_equiv (rowMul N β) _ _ (fun p => ?_)
  have h1 : (((p.1.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (p.2.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N)
      = ((rowMul N β) p).1 := by
    simp [rowMul]
  have h2 : (((p.1.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + (p.2.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N)
      = ((rowMul N β) p).2 := by
    simp [rowMul]
  rw [h1, h2]
  congr 2
  simp only [expTransport, Prod.mk.eta, Equiv.symm_apply_apply]

theorem slash_apply [NeZero N] (m : ZMod N → ZMod N → ℕ) (t : ℕ)
    (ϑ : ModularForm Γ₁(N) (12 * (t : ℤ)))
    (hϑ : ∀ τ : ℍ, ϑ τ = uProd N m τ * ModularForm.discriminant τ ^ t) (β : SL(2, ℤ)) (τ : ℍ) :
    ((⇑ϑ : ℍ → ℂ) ∣[12 * (t : ℤ)] ((β : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ =
      uProd N m (β • τ) * ModularForm.discriminant τ ^ t := by
  have hd : UpperHalfPlane.denom ((β : SL(2, ℤ)) : GL (Fin 2) ℝ) (τ : ℂ) ≠ 0 :=
    UpperHalfPlane.denom_ne_zero _ _
  have hΔ : ModularForm.discriminant (β • τ) =
      UpperHalfPlane.denom ((β : SL(2, ℤ)) : GL (Fin 2) ℝ) (τ : ℂ) ^ (12 : ℤ) * ModularForm.discriminant τ := by
    have := SlashInvariantForm.slash_action_eqn'' (CuspForm.discriminant) (γ := ((β : SL(2, ℤ)) : GL (Fin 2) ℝ))
      (MonoidHom.mem_range.mpr ⟨β, rfl⟩) τ
    rw [CuspForm.coe_discriminant] at this
    convert this using 2
    all_goals try rfl
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, hϑ, hΔ, mul_pow, ← zpow_natCast, ← zpow_mul]
  have h2 : UpperHalfPlane.denom ((β : SL(2, ℤ)) : GL (Fin 2) ℝ) (τ : ℂ) ^ ((12 : ℤ) * (t : ℕ)) *
      UpperHalfPlane.denom ((β : SL(2, ℤ)) : GL (Fin 2) ℝ) (τ : ℂ) ^ (-(12 * (t : ℤ))) = 1 := by
    rw [← zpow_add₀ hd]; norm_num
  calc uProd N m (β • τ) * (UpperHalfPlane.denom ((β : SL(2, ℤ)) : GL (Fin 2) ℝ) (τ : ℂ) ^ ((12 : ℤ) * (t : ℕ)) *
        ModularForm.discriminant τ ^ t) *
        UpperHalfPlane.denom ((β : SL(2, ℤ)) : GL (Fin 2) ℝ) (τ : ℂ) ^ (-(12 * (t : ℤ)))
      = uProd N m (β • τ) * ModularForm.discriminant τ ^ t *
          (UpperHalfPlane.denom ((β : SL(2, ℤ)) : GL (Fin 2) ℝ) (τ : ℂ) ^ ((12 : ℤ) * (t : ℕ)) *
            UpperHalfPlane.denom ((β : SL(2, ℤ)) : GL (Fin 2) ℝ) (τ : ℂ) ^ (-(12 * (t : ℤ)))) := by ring
    _ = uProd N m (β • τ) * ModularForm.discriminant τ ^ t := by rw [h2, mul_one]

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

theorem main (m : ZMod N → ZMod N → ℕ) (t : ℕ) (β : SL(2, ℤ))
    (ϑ : ModularForm Γ₁(N) (12 * (t : ℤ)))
    (hϑ : ∀ τ : ℍ, ϑ τ =
      (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t) (n : ℕ) :
    IsIntegral ℤ ((qExpansion (N : ℝ) (⇑(ThetaC ϑ β) : ℍ → ℂ)).coeff n) := by
  have hN : 0 < N := NeZero.pos N
  have hϑ' : ∀ τ : ℍ, ϑ τ = uProd N m τ * ModularForm.discriminant τ ^ t := hϑ
  set Θ := ThetaC ϑ β with hΘdef
  have hΘ : ∀ τ : ℍ, Θ τ = uProd N m (β • τ) * ModularForm.discriminant τ ^ t :=
    fun τ => slash_apply N m t ϑ hϑ' β τ
  by_cases hm : m 0 0 = 0
  swap
  ·
    have hΘ0 : ∀ τ : ℍ, Θ τ = 0 := fun τ => by
      rw [hΘ, uProd_eq_zero N hm, zero_mul]
    have hs : ∀ τ : ℍ, HasSum (fun k : ℕ => (fun _ : ℕ => (0 : ℂ)) k •
        Periodic.qParam (N : ℝ) (τ : ℂ) ^ k) (Θ τ) := fun τ => by
      simpa [hΘ0 τ] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
    have h0 := ModularFormClass.qExpansion_coeff_unique natCast_pos
      (natCast_mem_strictPeriods_GammaC N β) (f := Θ) hs n
    rw [← h0]
    exact isIntegral_zero
  ·
    set e : ZMod N → ZMod N → ℕ := expTransport N β m with he_def
    have he : e 0 0 = 0 := by rw [he_def, expTransport_zero_zero]; exact hm
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
      convert h1 using 1
      all_goals try rfl
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
        rw [hΘ, uProd_smul]
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
      (natCast_mem_strictPeriods_GammaC N β) (Ord + ((N * t : ℕ) : ℤ))
      (fun k => PowerSeries.coeff k (A * B)) hb0 hAB
    rw [hcoeff n]
    split_ifs
    · exact hABint _
    · exact isIntegral_zero

end Main

section Alpha

theorem sum_levelWeight_eq (q : ℕ) [NeZero q] :
    ∑ y : ZMod q, (6 * ((y.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((y.val : ℕ) : ℤ) + (q : ℤ) ^ 2) = (q : ℤ) := by
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos q)).symm⟩
  subst hk
  change ∑ y : Fin (k + 1), (6 * (((y : ℕ)) : ℤ) ^ 2 - 6 * ((k + 1 : ℕ) : ℤ) * (((y : ℕ)) : ℤ) + ((k + 1 : ℕ) : ℤ) ^ 2) = _
  rw [Fin.sum_univ_eq_sum_range (fun i => (6 * ((i : ℕ) : ℤ) ^ 2 - 6 * ((k + 1 : ℕ) : ℤ) * ((i : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) ^ 2)) (k + 1)]
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (6 * ((i : ℕ) : ℤ) ^ 2 - 6 * ((k + 1 : ℕ) : ℤ) * ((i : ℕ) : ℤ)) =
      ((n : ℤ) - 1) * (n : ℤ) * (2 * (n : ℤ) - 1) - 3 * ((k + 1 : ℕ) : ℤ) * (n : ℤ) * ((n : ℤ) - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [Finset.sum_add_distrib, h1, Finset.sum_const, Finset.card_range]
  push_cast
  ring

theorem growth_of_level (q : ℕ) [Fact q.Prime] (μ : ZMod q → ℕ) (t : ℕ)
    (ht : ∀ x : ZMod q, x ≠ 0 →
      0 ≤ (∑ r : ZMod q, (μ r : ℤ) *
          (6 * (((r * x).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * x).val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ))
    (β : SL(2, ℤ)) :
    0 ≤ (∑ r : ZMod q, ∑ s : ZMod q, ((fun (r _ : ZMod q) => μ r) r s : ℤ) *
          (6 * ((r * ((β 0 0 : ℤ) : ZMod q) + s * ((β 1 0 : ℤ) : ZMod q)).val : ℤ) ^ 2
            - 6 * (q : ℤ) * ((r * ((β 0 0 : ℤ) : ZMod q) + s * ((β 1 0 : ℤ) : ZMod q)).val : ℤ) + (q : ℤ) ^ 2)) +
      (q : ℤ) * t := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  set a : ZMod q := ((β 0 0 : ℤ) : ZMod q) with ha
  set c : ZMod q := ((β 1 0 : ℤ) : ZMod q) with hc
  simp only []
  by_cases hc0 : c = 0
  ·
    have hdet : ((β 0 0 : ℤ) : ZMod q) * ((β 1 1 : ℤ) : ZMod q) - ((β 0 1 : ℤ) : ZMod q) * ((β 1 0 : ℤ) : ZMod q) = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe β
      rw [Matrix.det_fin_two] at h
      have := congrArg (Int.cast : ℤ → ZMod q) h
      push_cast at this
      exact this
    have ha0 : a ≠ 0 := by
      intro h0
      rw [← ha, ← hc, h0, hc0, zero_mul, mul_zero, sub_zero] at hdet
      exact zero_ne_one hdet
    have key := ht a ha0
    have hrw : ∀ r s : ZMod q, r * a + s * c = r * a := fun r s => by rw [hc0, mul_zero, add_zero]
    simp_rw [hrw]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    have : (0 : ℤ) ≤ (q : ℤ) * ((∑ r : ZMod q, (μ r : ℤ) *
        (6 * (((r * a).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * a).val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ)) :=
      mul_nonneg (by positivity) key
    linarith
  ·
    have hinner : ∀ r : ZMod q, ∑ s : ZMod q,
        (6 * (((r * a + s * c).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * a + s * c).val : ℕ) : ℤ) + (q : ℤ) ^ 2) = (q : ℤ) := by
      intro r
      refine (Fintype.sum_equiv ((Equiv.mulRight₀ c hc0).trans (Equiv.addLeft (r * a)))
        (fun s : ZMod q => (6 * (((r * a + s * c).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * a + s * c).val : ℕ) : ℤ) + (q : ℤ) ^ 2))
        (fun y : ZMod q => (6 * ((y.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((y.val : ℕ) : ℤ) + (q : ℤ) ^ 2))
        (fun s => ?_)).trans (sum_levelWeight_eq q)
      simp [Equiv.mulRight₀]
    have : ∀ r : ZMod q, ∑ s : ZMod q, (μ r : ℤ) *
        (6 * (((r * a + s * c).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * a + s * c).val : ℕ) : ℤ) + (q : ℤ) ^ 2) =
        (μ r : ℤ) * q := fun r => by rw [← Finset.mul_sum, hinner]
    simp_rw [this]
    positivity

end Alpha

section Beta

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods_Gamma1 (N : ℕ) : (1 : ℝ) ∈ (Γ₁(N)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, T_mem_Gamma1 N, ?_⟩
  apply Units.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom_apply, ModularGroup.T]

theorem natCast_mem_strictPeriods_Gamma1 (N : ℕ) : (N : ℝ) ∈ (Γ₁(N)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T ^ N, Gamma_le_Gamma1 N (T_pow_mem_Gamma N), ?_⟩
  apply Units.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    ← zpow_natCast, ModularGroup.coe_T_zpow]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom_apply]

theorem spread_test (N : ℕ) (hN : 0 < N) (a : ℕ → ℂ) (τ : ℍ) (v : ℂ)
    (h1 : HasSum (fun j : ℕ => a j * Periodic.qParam 1 (τ : ℂ) ^ j) v) :
    HasSum (fun n : ℕ => (if N ∣ n then a (n / N) else 0) * Periodic.qParam (N : ℝ) (τ : ℂ) ^ n) v := by
  rw [qParam_one_eq_pow N hN (τ : ℂ)] at h1
  exact hasSum_spread (q := Periodic.qParam (N : ℝ) (τ : ℂ)) N hN h1

theorem exists_isIntegralQExp_of_hasSum {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (ϑ : ModularForm Γ k)
    (N : ℕ) (hN : 0 < N) (hΓ1 : (1 : ℝ) ∈ Γ.strictPeriods) (hΓN : (N : ℝ) ∈ Γ.strictPeriods)
    (c : ℕ → ℤ) (hc0 : c 0 = 1) (M : ℤ)
    (hb : ∀ τ : ℍ, HasSum (fun n : ℕ => ((c n : ℤ) : ℂ) * Periodic.qParam (N : ℝ) (τ : ℂ) ^ n)
      (ϑ τ / Periodic.qParam (N : ℝ) (τ : ℂ) ^ ((N : ℤ) * M))) :
    ∃ (p : PowerSeries ℤ) (n₀ : ℕ), ModularCurve.IsIntegralQExp ϑ p ∧ (n₀ : ℤ) = M ∧
      (∀ n : ℕ, n < n₀ → PowerSeries.coeff n p = 0) ∧ PowerSeries.coeff n₀ p = 1 := by
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hb0 : (((c 0 : ℤ) : ℂ)) ≠ 0 := by rw [hc0]; simp
  obtain ⟨hM, hcoeff⟩ := qExpansion_coeff_eq_of_hasSum_div_qParam_zpow ϑ (N : ℝ) hNR
    hΓN ((N : ℤ) * M) (fun n => ((c n : ℤ) : ℂ)) hb0 hb
  have hM0 : 0 ≤ M := by
    have : (0 : ℤ) < N := by exact_mod_cast hN
    nlinarith
  obtain ⟨n₀, hn₀⟩ := Int.eq_ofNat_of_zero_le hM0
  haveI : Fact (IsCusp OnePoint.infty Γ) :=
    ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ1⟩
  have hf1 : ∀ τ : ℍ, HasSum (fun j : ℕ => (qExpansion 1 (⇑ϑ : ℍ → ℂ)).coeff j * Periodic.qParam 1 (τ : ℂ) ^ j) (ϑ τ) :=
    fun τ => by
    simpa only [smul_eq_mul] using hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex ϑ hΓ1) ϑ.holo'
      (ModularFormClass.bdd_at_infty ϑ) τ
  have hfq : ∀ τ : ℍ, HasSum (fun n : ℕ => (qExpansion (N : ℝ) (⇑ϑ : ℍ → ℂ)).coeff n *
      Periodic.qParam (N : ℝ) (τ : ℂ) ^ n) (ϑ τ) := fun τ => by
    simpa only [smul_eq_mul] using hasSum_qExpansion hNR
      (SlashInvariantFormClass.periodic_comp_ofComplex ϑ hΓN) ϑ.holo'
      (ModularFormClass.bdd_at_infty ϑ) τ
  have hspread : ∀ τ : ℍ, HasSum (fun n : ℕ =>
      (if N ∣ n then (fun j : ℕ => (qExpansion 1 (⇑ϑ : ℍ → ℂ)).coeff j) (n / N) else 0) *
        Periodic.qParam (N : ℝ) (τ : ℂ) ^ n) (ϑ τ) :=
    fun τ => spread_test N hN (fun j : ℕ => (qExpansion 1 (⇑ϑ : ℍ → ℂ)).coeff j) τ (ϑ τ) (hf1 τ)
  have huniq := ModularCurve.qParam_coeff_unique (N : ℝ) hNR (⇑ϑ) _ _ hspread hfq
  refine ⟨PowerSeries.mk (fun j => if n₀ ≤ j then c (N * (j - n₀)) else 0), n₀, ?_, hn₀.symm, ?_, ?_⟩
  · unfold ModularCurve.IsIntegralQExp
    ext j
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    have h1 := congr_fun huniq (N * j)
    simp only [dvd_mul_right, if_true, Nat.mul_div_cancel_left j hN] at h1
    rw [h1, hcoeff (N * j), hn₀]
    by_cases hj : n₀ ≤ j
    · have hle : (N : ℤ) * (n₀ : ℕ) ≤ ((N * j : ℕ) : ℤ) := by
        push_cast; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) (by positivity)
      rw [if_pos hj, if_pos hle]
      have : (N * j : ℕ) - ((N : ℤ) * (n₀ : ℕ)).toNat = N * (j - n₀) := by
        have : ((N : ℤ) * (n₀ : ℕ)).toNat = N * n₀ := by push_cast; exact Int.toNat_natCast _
        rw [this, Nat.mul_sub]
      rw [this]
      simp
    · have hlt : ¬ (N : ℤ) * (n₀ : ℕ) ≤ ((N * j : ℕ) : ℤ) := by
        push_cast; push Not at hj ⊢; exact mul_lt_mul_of_pos_left (by exact_mod_cast hj) (by exact_mod_cast hN)
      rw [if_neg hj, if_neg hlt]
      simp
  · intro n hn
    rw [PowerSeries.coeff_mk, if_neg (Nat.not_le.mpr hn)]
  · rw [PowerSeries.coeff_mk, if_pos le_rfl, Nat.sub_self, mul_zero, hc0]

end Beta

end ModularCurve.SiegelUnit.WF1A
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit.WF1A"
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit"
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit.WF1A"

section BlockB
p2m_open "ModularCurve P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve Complex"
open scoped PowerSeries.WithPiTopology

namespace EngS2CC

theorem continuous_map {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R] [DiscreteTopology R]
    [TopologicalSpace S] (f : R →+* S) : Continuous (PowerSeries.map f) := by
  rw [continuous_iff_continuousAt]
  intro P
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  simp_rw [PowerSeries.coeff_map]
  exact (continuous_of_discreteTopology (f := f)).continuousAt.tendsto.comp
    ((PowerSeries.WithPiTopology.continuous_coeff (R := R) d).continuousAt)

theorem map_siegelSeriesInt (q : ℕ) [Fact q.Prime] {S : Type*} [CommRing S] (φ : ↥(zetaSubring q) →+* S) (a : Fin 2 → ZMod q) :
    letI : TopologicalSpace S := ⊥
    (siegelSeriesInt q a).map φ =
      (1 - PowerSeries.C (φ (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ (a 1).val)) * PowerSeries.X ^ (a 0).val) *
        ((∏' n : ℕ, (1 - PowerSeries.C (φ (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ (a 1).val)) *
            PowerSeries.X ^ (q * (n + 1) + (a 0).val))) *
          ∏' n : ℕ, (1 - PowerSeries.C (φ (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ (q - (a 1).val))) *
            PowerSeries.X ^ (q * (n + 1) - (a 0).val))) := by
  letI : TopologicalSpace S := ⊥
  haveI : DiscreteTopology S := ⟨rfl⟩
  letI : TopologicalSpace ↥(zetaSubring q) := ⊥
  haveI : DiscreteTopology ↥(zetaSubring q) := ⟨rfl⟩
  have hc : Continuous (PowerSeries.map φ) := continuous_map φ
  have hfac : ∀ (c : ↥(zetaSubring q)) (m : ℕ),
      PowerSeries.map φ (1 - PowerSeries.C c * PowerSeries.X ^ m) = 1 - PowerSeries.C (φ c) * PowerSeries.X ^ m := by
    intro c m
    rw [map_sub, map_one, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  rw [siegelSeriesInt]
  rw [map_mul, map_mul, hfac,
    Multipliable.map_tprod (multipliable_siegelFactor_left q a) (PowerSeries.map φ) hc,
    Multipliable.map_tprod (multipliable_siegelFactor_right q a) (PowerSeries.map φ) hc]
  simp only [hfac]

theorem constantCoeff_one_sub_C_mul_X_pow {R : Type} [CommRing R] (c : R) {m : ℕ} (hm : m ≠ 0) :
    PowerSeries.constantCoeff (1 - PowerSeries.C c * PowerSeries.X ^ m) = 1 := by
  rw [map_sub, map_one, map_mul, map_pow, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, zero_pow hm,
    mul_zero, sub_zero]

theorem constantCoeff_tprod_one_sub {R : Type} [CommRing R] (c : R) (m : ℕ → ℕ) (hm : ∀ n, n < m n) :
    letI : TopologicalSpace R := ⊥
    PowerSeries.constantCoeff (∏' n : ℕ, (1 - PowerSeries.C c * PowerSeries.X ^ m n)) = 1 := by
  letI : TopologicalSpace R := ⊥
  haveI : DiscreteTopology R := ⟨rfl⟩
  have hmul := multipliable_one_sub_C_mul_X_pow c m hm
  have hcont : Continuous (PowerSeries.constantCoeff (R := R)) := by
    have : (PowerSeries.constantCoeff (R := R) : PowerSeries R → R) = PowerSeries.coeff 0 := by
      funext x; rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [this]
    exact PowerSeries.WithPiTopology.continuous_coeff (R := R) 0
  rw [Multipliable.map_tprod hmul (PowerSeries.constantCoeff (R := R)) hcont]
  have : ∀ n, PowerSeries.constantCoeff (1 - PowerSeries.C c * PowerSeries.X ^ m n) = 1 := fun n =>
    constantCoeff_one_sub_C_mul_X_pow c (Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le n) (hm n)))
  simp_rw [this]
  exact tprod_one

end EngS2CC
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit.WF1A"

namespace ModularCurve p2m_export "ModularCurve" "siegelFun etaProd constantCoeff_etaProd IsIntegralQExp SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow SiegelUnit.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow qParam_coeff_unique hasSum_qParam_mul hasSum_coeff_etaProd_pow zetaQ isPrimitiveRoot_zetaQ zetaQ_pow zetaSubring zetaQ_mem_zetaSubring multipliable_one_sub_C_mul_X_pow siegelExponent siegelConstExponent siegelSeriesInt multipliable_siegelFactor_left multipliable_siegelFactor_right siegelSeries SiegelUnit.hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div exists_algebraMap_int_eq_of_mem_zetaSubring_of_forall_algEquiv_apply_eq" end ModularCurve
p2m_open_scoped "ModularCurve" in
open EngS2CC in
theorem ModularCurve.constantCoeff_siegelSeries_eq_one (q : ℕ) [Fact q.Prime] (a : Fin 2 → ZMod q) (ha : a 0 ≠ 0) :
    PowerSeries.constantCoeff (siegelSeries q a) = 1 := by
  letI : TopologicalSpace (CyclotomicField q ℚ) := ⊥
  haveI : DiscreteTopology (CyclotomicField q ℚ) := ⟨rfl⟩
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  have ha' : (a 0).val ≠ 0 := (ZMod.val_ne_zero (a 0)).mpr ha
  have halt : (a 0).val < q := (a 0).val_lt
  rw [siegelSeries, map_siegelSeriesInt q (algebraMap (zetaSubring q) (CyclotomicField q ℚ)) a, map_mul, map_mul,
    constantCoeff_one_sub_C_mul_X_pow _ ha',
    constantCoeff_tprod_one_sub _ (fun n => q * (n + 1) + (a 0).val) (fun n => by nlinarith),
    constantCoeff_tprod_one_sub _ (fun n => q * (n + 1) - (a 0).val) (fun n => by
      show n < q * (n + 1) - (a 0).val
      have h1 : q * (n + 1) = q * n + q := by ring
      have h2 : n ≤ q * n := Nat.le_mul_of_pos_left n (by omega)
      omega)]
  simp

namespace WF1B

theorem exp_eq_qParam_pow (q : ℕ) (z : ℂ) (n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * n * z / q) = Function.Periodic.qParam q z ^ n := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem exp_int_eq_qParam_zpow (q : ℕ) (hq : (q : ℂ) ≠ 0) (z : ℂ) (e : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (e : ℂ) * z / q) = Complex.exp (2 * Real.pi * Complex.I * z / q * e) := by
  congr 1; ring

theorem hasSum_finset_prod {ι : Type} [DecidableEq ι] (h : ℝ) (hh : 0 < h) (S : Finset ι)
    (A : ι → PowerSeries ℂ) (F : ι → UpperHalfPlane → ℂ)
    (hA : ∀ i ∈ S, ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => PowerSeries.coeff m (A i) * Function.Periodic.qParam h (τ : ℂ) ^ m) (F i τ)) :
    ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => PowerSeries.coeff m (∏ i ∈ S, A i) * Function.Periodic.qParam h (τ : ℂ) ^ m)
        (∏ i ∈ S, F i τ) := by
  induction S using Finset.induction_on with
  | empty =>
    intro τ
    simp only [Finset.prod_empty]
    have : (fun m : ℕ => PowerSeries.coeff m (1 : PowerSeries ℂ) * Function.Periodic.qParam h (τ : ℂ) ^ m) =
        fun m => if m = 0 then 1 else 0 := by
      funext m; rw [PowerSeries.coeff_one]; split_ifs with hm <;> simp [hm]
    rw [this]
    simpa using (hasSum_single (f := fun m : ℕ => if m = 0 then (1 : ℂ) else 0) 0 (fun b hb => if_neg hb))
  | insert i S hi ih =>
    intro τ
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ModularCurve.hasSum_qParam_mul h hh (A i) (∏ j ∈ S, A j) (F i) (fun τ => ∏ j ∈ S, F j τ)
      (hA i (Finset.mem_insert_self i S)) (fun τ => ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)) τ) τ

theorem hasSum_pow (h : ℝ) (hh : 0 < h) (A : PowerSeries ℂ) (F : UpperHalfPlane → ℂ)
    (hA : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => PowerSeries.coeff m A * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) (k : ℕ) :
    ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => PowerSeries.coeff m (A ^ k) * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ ^ k) := by
  classical
  intro τ
  have := hasSum_finset_prod h hh (Finset.range k) (fun _ => A) (fun _ => F) (fun _ _ => hA) τ
  simpa only [Finset.prod_const, Finset.card_range] using this

variable (q : ℕ) [hqp : Fact q.Prime]

theorem q_pos : 0 < q := (Fact.out : q.Prime).pos
theorem q_ne_zero_C : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

theorem hasSum_index (a : Fin 2 → ZMod q)
    (ι : CyclotomicField q ℚ →+* ℂ) (hι : ι (zetaQ q) = Complex.exp (2 * Real.pi * Complex.I / (q : ℂ)))
    (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => PowerSeries.coeff m ((siegelSeries q a ^ (12 * q)).map ι) *
        Function.Periodic.qParam q (τ : ℂ) ^ m)
      (siegelFun q ((a 0).val : ℤ) ((a 1).val : ℤ) (τ : ℂ) ^ (12 * q) /
        (ι (zetaQ q ^ siegelConstExponent q a) *
          Complex.exp (2 * Real.pi * Complex.I * ((siegelExponent q a : ℤ) : ℂ) * (τ : ℂ) / (q : ℂ)))) := by
  have h := ModularCurve.SiegelUnit.hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div q a ι hι τ
  simp only [PowerSeries.coeff_map, ← exp_eq_qParam_pow]
  exact h

theorem sum_val_eq (hq : 0 < q) : ∑ s : ZMod q, s.val = ∑ i ∈ Finset.range q, i := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have himg : (Finset.univ : Finset (ZMod q)).image ZMod.val = Finset.range q := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨s, rfl⟩; exact ZMod.val_lt s
    · intro hi; exact ⟨(i : ZMod q), ZMod.val_natCast_of_lt hi⟩
  rw [← himg, Finset.sum_image (fun x _ y _ h => ZMod.val_injective q h)]

theorem q_dvd_sum_const (μ : ZMod q → ℕ) :
    q ∣ ∑ p : ZMod q × ZMod q, 6 * p.1.val * p.2.val * μ p.1 := by
  have hq := q_pos q
  have h2 : (∑ i ∈ Finset.range q, i) * 2 = q * (q - 1) := Finset.sum_range_id_mul_two q
  have hinner : ∀ r : ZMod q, ∑ s : ZMod q, 6 * r.val * s.val * μ r = (6 * r.val * μ r) * ∑ s : ZMod q, s.val := by
    intro r
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have key : ∑ p : ZMod q × ZMod q, 6 * p.1.val * p.2.val * μ p.1 =
      (∑ r : ZMod q, 3 * r.val * μ r) * ((∑ i ∈ Finset.range q, i) * 2) := by
    rw [Fintype.sum_prod_type]
    simp only []
    rw [Finset.sum_congr rfl (fun r _ => hinner r), ← sum_val_eq q hq, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [key, h2]
  exact Dvd.dvd.mul_left (dvd_mul_right q _) _

theorem hasSum_siegelProd (μ : ZMod q → ℕ)
    (ι : CyclotomicField q ℚ →+* ℂ) (hι : ι (zetaQ q) = Complex.exp (2 * Real.pi * Complex.I / (q : ℂ)))
    (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => PowerSeries.coeff m
        (∏ p : ZMod q × ZMod q, ((siegelSeries q ![p.1, p.2] ^ (12 * q)).map ι) ^ (μ p.1)) *
        Function.Periodic.qParam q (τ : ℂ) ^ m)
      (∏ p : ZMod q × ZMod q,
        (siegelFun q (p.1.val : ℤ) (p.2.val : ℤ) (τ : ℂ) ^ (12 * q) /
          (ι (zetaQ q ^ siegelConstExponent q ![p.1, p.2]) *
            Complex.exp (2 * Real.pi * Complex.I * ((siegelExponent q ![p.1, p.2] : ℤ) : ℂ) * (τ : ℂ) / (q : ℂ)))) ^ (μ p.1)) := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (q_pos q)
  refine hasSum_finset_prod (q : ℝ) hqR (Finset.univ : Finset (ZMod q × ZMod q))
    (fun p => ((siegelSeries q ![p.1, p.2] ^ (12 * q)).map ι) ^ (μ p.1))
    (fun p τ => (siegelFun q (p.1.val : ℤ) (p.2.val : ℤ) (τ : ℂ) ^ (12 * q) /
          (ι (zetaQ q ^ siegelConstExponent q ![p.1, p.2]) *
            Complex.exp (2 * Real.pi * Complex.I * ((siegelExponent q ![p.1, p.2] : ℤ) : ℂ) * (τ : ℂ) / (q : ℂ)))) ^ (μ p.1))
    (fun p _ => ?_) τ
  intro τ
  have h := hasSum_pow (q : ℝ) hqR _ _ (fun τ => hasSum_index q ![p.1, p.2] ι hι τ) (μ p.1) τ
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem siegelProd_value (μ : ZMod q → ℕ)
    (ι : CyclotomicField q ℚ →+* ℂ) (hι : ι (zetaQ q) = Complex.exp (2 * Real.pi * Complex.I / (q : ℂ)))
    (τ : UpperHalfPlane) :
    (∏ p : ZMod q × ZMod q,
        (siegelFun q (p.1.val : ℤ) (p.2.val : ℤ) (τ : ℂ) ^ (12 * q) /
          (ι (zetaQ q ^ siegelConstExponent q ![p.1, p.2]) *
            Complex.exp (2 * Real.pi * Complex.I * ((siegelExponent q ![p.1, p.2] : ℤ) : ℂ) * (τ : ℂ) / (q : ℂ)))) ^ (μ p.1)) =
      (∏ r : ZMod q, ∏ s : ZMod q, siegelFun q (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * q * μ r)) /
        Complex.exp (2 * Real.pi * Complex.I *
          ((∑ r : ZMod q, (μ r : ℤ) * (6 * ((r.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((r.val : ℕ) : ℤ) + (q : ℤ) ^ 2) : ℤ) : ℂ) *
          (τ : ℂ)) := by
  have hq0 := q_ne_zero_C q

  simp only [div_pow, Finset.prod_div_distrib, ← pow_mul, mul_pow]
  have hnum : ∏ x : ZMod q × ZMod q, siegelFun q (x.1.val : ℤ) (x.2.val : ℤ) (τ : ℂ) ^ (12 * q * μ x.1) =
      ∏ r : ZMod q, ∏ s : ZMod q, siegelFun q (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * q * μ r) := by
    rw [Fintype.prod_prod_type]
  rw [hnum]
  congr 1

  have hζ : ∏ p : ZMod q × ZMod q, ι (zetaQ q ^ siegelConstExponent q ![p.1, p.2]) ^ μ p.1 = 1 := by
    simp only [map_pow, ← pow_mul, siegelConstExponent, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.prod_pow_eq_pow_sum]
    obtain ⟨k, hk⟩ := q_dvd_sum_const q μ
    rw [hk, pow_mul, ← map_pow, zetaQ_pow, map_one, one_pow]

  have hexp : ∏ p : ZMod q × ZMod q,
      Complex.exp (2 * Real.pi * Complex.I * ((siegelExponent q ![p.1, p.2] : ℤ) : ℂ) * (τ : ℂ) / (q : ℂ)) ^ μ p.1 =
      Complex.exp (2 * Real.pi * Complex.I *
          ((∑ r : ZMod q, (μ r : ℤ) * (6 * ((r.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((r.val : ℕ) : ℤ) + (q : ℤ) ^ 2) : ℤ) : ℂ) *
          (τ : ℂ)) := by
    simp only [← Complex.exp_nat_mul, ← Complex.exp_sum]
    congr 1
    rw [Fintype.sum_prod_type]
    simp only [siegelExponent, Matrix.cons_val_zero, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
  rw [Finset.prod_mul_distrib, hζ, one_mul, hexp]

theorem hasSum_spread {x : ℂ} {c : ℕ → ℂ} {v : ℂ} (N : ℕ) (hN : 0 < N)
    (h : HasSum (fun k : ℕ => c k * (x ^ N) ^ k) v) :
    HasSum (fun n : ℕ => (if N ∣ n then c (n / N) else 0) * x ^ n) v := by
  have hinj : Function.Injective (fun k : ℕ => N * k) := fun a b hab =>
    Nat.eq_of_mul_eq_mul_left hN hab
  have key : (fun n : ℕ => (if N ∣ n then c (n / N) else 0) * x ^ n) =
      Function.extend (fun k : ℕ => N * k) (fun k : ℕ => c k * (x ^ N) ^ k) 0 := by
    funext n
    by_cases hn : N ∣ n
    · obtain ⟨k, rfl⟩ := hn
      rw [hinj.extend_apply]
      simp [Nat.mul_div_cancel_left k hN, pow_mul]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨k, rfl⟩; exact hn ⟨k, rfl⟩)]
      simp [hn]
  rw [key]
  exact (hasSum_extend_zero hinj).mpr h

theorem qParam_one_eq_pow (N : ℕ) (hN : 0 < N) (z : ℂ) :
    Function.Periodic.qParam 1 z = Function.Periodic.qParam N z ^ N := by
  simp only [Function.Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

theorem hasSum_discriminant_pow (t : ℕ) (τ : UpperHalfPlane) :
    HasSum (fun k : ℕ => ((PowerSeries.coeff k (etaProd ^ (24 * t)) : ℤ) : ℂ) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ k)
      (ModularForm.discriminant τ ^ t / Function.Periodic.qParam 1 (τ : ℂ) ^ t) := by
  have hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 := by
    simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have h24 : Function.Periodic.qParam 24 (τ : ℂ) ^ 24 = Function.Periodic.qParam 1 (τ : ℂ) :=
    (qParam_one_eq_pow 24 (by norm_num) (τ : ℂ)).symm
  have hΔ : ModularForm.discriminant τ =
      Function.Periodic.qParam 1 (τ : ℂ) * (∏' n : ℕ, (1 - Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1))) ^ 24 := by
    simp only [ModularForm.discriminant, ModularForm.eta, ModularForm.eta_q, mul_pow, h24]
  have key : ModularForm.discriminant τ ^ t / Function.Periodic.qParam 1 (τ : ℂ) ^ t =
      (∏' n : ℕ, (1 - Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1))) ^ (24 * t) := by
    rw [hΔ, mul_pow, ← pow_mul,
      mul_div_cancel_left₀ _ (pow_ne_zero _ (Function.Periodic.qParam_ne_zero _))]
  rw [key]
  exact ModularCurve.hasSum_coeff_etaProd_pow (24 * t) hq

noncomputable def etaSpread (t : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if q ∣ n then PowerSeries.coeff (n / q) (etaProd ^ (24 * t)) else 0

theorem coeff_etaSpread (t n : ℕ) :
    PowerSeries.coeff n (etaSpread q t) = if q ∣ n then PowerSeries.coeff (n / q) (etaProd ^ (24 * t)) else 0 := by
  rw [etaSpread, PowerSeries.coeff_mk]

theorem hasSum_etaSpread (t : ℕ) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => PowerSeries.coeff m ((etaSpread q t).map (Int.castRingHom ℂ)) *
        Function.Periodic.qParam q (τ : ℂ) ^ m)
      (ModularForm.discriminant τ ^ t / Function.Periodic.qParam q (τ : ℂ) ^ (q * t)) := by
  have hq := q_pos q
  have h := hasSum_discriminant_pow t τ
  rw [qParam_one_eq_pow q hq] at h
  have h2 := hasSum_spread (c := fun k => ((PowerSeries.coeff k (etaProd ^ (24 * t)) : ℤ) : ℂ)) q hq h
  rw [← pow_mul] at h2
  convert h2 using 2 with m
  rw [PowerSeries.coeff_map, coeff_etaSpread]
  split_ifs <;> simp

theorem value_eq (μ : ZMod q → ℕ) (t : ℕ) (τ : UpperHalfPlane) :
    (∏ r : ZMod q, ∏ s : ZMod q, siegelFun q (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * q * μ r)) /
        Complex.exp (2 * Real.pi * Complex.I *
          ((∑ r : ZMod q, (μ r : ℤ) * (6 * ((r.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((r.val : ℕ) : ℤ) + (q : ℤ) ^ 2) : ℤ) : ℂ) *
          (τ : ℂ)) *
      (ModularForm.discriminant τ ^ t / Function.Periodic.qParam q (τ : ℂ) ^ (q * t)) =
    (∏ r : ZMod q, ∏ s : ZMod q,
        ModularCurve.siegelFun q (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * q * μ r)) *
        ModularForm.discriminant τ ^ t /
      Complex.exp (2 * Real.pi * Complex.I *
        (((∑ r : ZMod q, (μ r : ℤ) *
            (6 * ((r.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((r.val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ) : ℤ) : ℂ) *
          (τ : ℂ)) := by
  have hq0 := q_ne_zero_C q
  rw [div_mul_div_comm, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp

theorem hasSum_full (μ : ZMod q → ℕ) (t : ℕ)
    (ι : CyclotomicField q ℚ →+* ℂ) (hι : ι (zetaQ q) = Complex.exp (2 * Real.pi * Complex.I / (q : ℂ)))
    (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => PowerSeries.coeff m
        ((∏ p : ZMod q × ZMod q, ((siegelSeries q ![p.1, p.2] ^ (12 * q)).map ι) ^ (μ p.1)) *
          (etaSpread q t).map (Int.castRingHom ℂ)) *
        Function.Periodic.qParam q (τ : ℂ) ^ m)
      ((∏ r : ZMod q, ∏ s : ZMod q,
          ModularCurve.siegelFun q (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * q * μ r)) *
          ModularForm.discriminant τ ^ t /
        Complex.exp (2 * Real.pi * Complex.I *
          (((∑ r : ZMod q, (μ r : ℤ) *
              (6 * ((r.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((r.val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ) : ℤ) : ℂ) *
            (τ : ℂ))) := by
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (q_pos q)
  have h := ModularCurve.hasSum_qParam_mul (q : ℝ) hqR _ _ _ _
    (fun τ => (siegelProd_value q μ ι hι τ) ▸ hasSum_siegelProd q μ ι hι τ) (hasSum_etaSpread q t) τ
  rw [← value_eq q μ t τ]
  exact h

section Descent

theorem continuous_map {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R] [DiscreteTopology R]
    [TopologicalSpace S] (f : R →+* S) : Continuous (PowerSeries.map f) := by
  rw [continuous_iff_continuousAt]
  intro P
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  simp_rw [PowerSeries.coeff_map]
  exact (continuous_of_discreteTopology (f := f)).continuousAt.tendsto.comp
    ((PowerSeries.WithPiTopology.continuous_coeff (R := R) d).continuousAt)

theorem map_siegelSeriesInt {S : Type*} [CommRing S] (φ : ↥(zetaSubring q) →+* S) (a : Fin 2 → ZMod q) :
    letI : TopologicalSpace S := ⊥
    (siegelSeriesInt q a).map φ =
      (1 - PowerSeries.C (φ (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ (a 1).val)) * PowerSeries.X ^ (a 0).val) *
        ((∏' n : ℕ, (1 - PowerSeries.C (φ (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ (a 1).val)) *
            PowerSeries.X ^ (q * (n + 1) + (a 0).val))) *
          ∏' n : ℕ, (1 - PowerSeries.C (φ (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ (q - (a 1).val))) *
            PowerSeries.X ^ (q * (n + 1) - (a 0).val))) := by
  letI : TopologicalSpace S := ⊥
  haveI : DiscreteTopology S := ⟨rfl⟩
  letI : TopologicalSpace ↥(zetaSubring q) := ⊥
  haveI : DiscreteTopology ↥(zetaSubring q) := ⟨rfl⟩
  have hc : Continuous (PowerSeries.map φ) := continuous_map φ
  have hfac : ∀ (c : ↥(zetaSubring q)) (m : ℕ),
      PowerSeries.map φ (1 - PowerSeries.C c * PowerSeries.X ^ m) = 1 - PowerSeries.C (φ c) * PowerSeries.X ^ m := by
    intro c m
    rw [map_sub, map_one, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  rw [siegelSeriesInt]
  rw [map_mul, map_mul, hfac,
    Multipliable.map_tprod (multipliable_siegelFactor_left q a) (PowerSeries.map φ) hc,
    Multipliable.map_tprod (multipliable_siegelFactor_right q a) (PowerSeries.map φ) hc]
  simp only [hfac]

theorem map_siegelSeries_algEquiv (t : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) (n : ℕ)
    (ht : t (zetaQ q) = zetaQ q ^ n) (a : Fin 2 → ZMod q) :
    (siegelSeries q a).map (t : CyclotomicField q ℚ →+* CyclotomicField q ℚ) = siegelSeries q ![a 0, (n : ZMod q) * a 1] := by
  classical
  letI : TopologicalSpace (CyclotomicField q ℚ) := ⊥
  haveI : DiscreteTopology (CyclotomicField q ℚ) := ⟨rfl⟩
  set a' : Fin 2 → ZMod q := ![a 0, (n : ZMod q) * a 1] with ha'
  have h0 : a' 0 = a 0 := rfl
  have h1 : a' 1 = (n : ZMod q) * a 1 := rfl
  have hζpow : ∀ i j : ℕ, i ≡ j [MOD q] → zetaQ q ^ i = zetaQ q ^ j := fun i j h => by
    have h' : i % q = j % q := h
    rw [← Nat.mod_add_div i q, ← Nat.mod_add_div j q, _root_.pow_add, _root_.pow_add, _root_.pow_mul, _root_.pow_mul, zetaQ_pow,
      _root_.one_pow, _root_.one_pow, _root_.mul_one, _root_.mul_one, h']
  have hval1 : (a' 1).val ≡ n * (a 1).val [MOD q] := by
    rw [h1, ZMod.val_mul, ZMod.val_natCast]
    exact (Nat.mod_modEq _ _).trans ((Nat.mod_modEq _ _).mul_right _)
  have hpow1 : zetaQ q ^ (n * (a 1).val) = zetaQ q ^ (a' 1).val := hζpow _ _ hval1.symm
  have hpow2 : zetaQ q ^ (n * (q - (a 1).val)) = zetaQ q ^ (q - (a' 1).val) := by
    apply hζpow
    have ha1 : (a 1).val ≤ q := (ZMod.val_lt (a 1)).le
    have ha1' : (a' 1).val ≤ q := (ZMod.val_lt (a' 1)).le
    have hL : n * (q - (a 1).val) + (a' 1).val ≡ 0 [MOD q] := by
      calc n * (q - (a 1).val) + (a' 1).val ≡ n * (q - (a 1).val) + n * (a 1).val [MOD q] := hval1.add_left _
        _ = n * q := by rw [← mul_add, Nat.sub_add_cancel ha1]
        _ ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_left q n)
    have hR : (q - (a' 1).val) + (a' 1).val ≡ 0 [MOD q] := by
      rw [Nat.sub_add_cancel ha1']; exact (Nat.modEq_zero_iff_dvd).mpr (dvd_refl q)
    exact Nat.ModEq.add_right_cancel' _ (hL.trans hR.symm)
  have hψ : ∀ m : ℕ, ((t : CyclotomicField q ℚ →+* CyclotomicField q ℚ).comp
        (algebraMap ↥(zetaSubring q) (CyclotomicField q ℚ))) (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ m) = zetaQ q ^ (n * m) := by
    intro m
    rw [map_pow, RingHom.comp_apply, RingHom.coe_coe, show algebraMap ↥(zetaSubring q) (CyclotomicField q ℚ) ⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ = zetaQ q from rfl,
      ht, ← pow_mul]
  have hα : ∀ m : ℕ, (algebraMap ↥(zetaSubring q) (CyclotomicField q ℚ)) (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ m) = zetaQ q ^ m := by
    intro m; rw [map_pow]; rfl
  rw [siegelSeries, siegelSeries,
    show PowerSeries.map (t : CyclotomicField q ℚ →+* CyclotomicField q ℚ)
        (PowerSeries.map (algebraMap ↥(zetaSubring q) (CyclotomicField q ℚ)) (siegelSeriesInt q a))
      = PowerSeries.map ((t : CyclotomicField q ℚ →+* CyclotomicField q ℚ).comp
          (algebraMap ↥(zetaSubring q) (CyclotomicField q ℚ))) (siegelSeriesInt q a) from by
      rw [PowerSeries.map_comp]; rfl,
    map_siegelSeriesInt, map_siegelSeriesInt]
  simp only [hψ, hα, h0, hpow1, hpow2]

noncomputable def siegelProd (μ : ZMod q → ℕ) : PowerSeries (CyclotomicField q ℚ) :=
  ∏ p : ZMod q × ZMod q, (siegelSeries q ![p.1, p.2] ^ (12 * q)) ^ (μ p.1)

theorem map_siegelProd (μ : ZMod q → ℕ) (ι : CyclotomicField q ℚ →+* ℂ) :
    (siegelProd q μ).map ι = ∏ p : ZMod q × ZMod q, ((siegelSeries q ![p.1, p.2] ^ (12 * q)).map ι) ^ (μ p.1) := by
  rw [siegelProd, map_prod]
  simp only [map_pow]

theorem coeff_siegelProd_mem (μ : ZMod q → ℕ) (n : ℕ) :
    PowerSeries.coeff n (siegelProd q μ) ∈ zetaSubring q := by
  have : siegelProd q μ = (∏ p : ZMod q × ZMod q, (siegelSeriesInt q ![p.1, p.2] ^ (12 * q)) ^ (μ p.1)).map
      (algebraMap ↥(zetaSubring q) (CyclotomicField q ℚ)) := by
    rw [siegelProd, map_prod]; simp only [map_pow, siegelSeries]
  rw [this, PowerSeries.coeff_map]
  exact Subtype.property _

theorem exists_pow_eq (t : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) :
    ∃ n : ℕ, t (zetaQ q) = zetaQ q ^ n ∧ (n : ZMod q) ≠ 0 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hζ := isPrimitiveRoot_zetaQ q
  have h1 : (t (zetaQ q)) ^ q = 1 := by rw [← map_pow, zetaQ_pow, map_one]
  obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one h1
  refine ⟨i, hi'.symm, fun h0 => ?_⟩
  have hi0 : i = 0 := by
    have := (ZMod.natCast_eq_zero_iff i q).1 h0
    exact Nat.eq_zero_of_dvd_of_lt this hi
  rw [hi0, pow_zero] at hi'
  have : zetaQ q = 1 := t.injective (by rw [map_one]; exact hi'.symm)
  exact hζ.ne_one (Fact.out : q.Prime).one_lt this

theorem map_siegelProd_algEquiv (μ : ZMod q → ℕ) (t : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) :
    (siegelProd q μ).map (t : CyclotomicField q ℚ →+* CyclotomicField q ℚ) = siegelProd q μ := by
  obtain ⟨n, hn, hn0⟩ := exists_pow_eq q t
  rw [siegelProd, map_prod]
  have hterm : ∀ p : ZMod q × ZMod q,
      PowerSeries.map (t : CyclotomicField q ℚ →+* CyclotomicField q ℚ) ((siegelSeries q ![p.1, p.2] ^ (12 * q)) ^ (μ p.1)) =
        (siegelSeries q ![p.1, (n : ZMod q) * p.2] ^ (12 * q)) ^ (μ p.1) := by
    intro p
    rw [map_pow, map_pow, map_siegelSeries_algEquiv q t n hn]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [hterm]
  have hbij : Function.Bijective (fun p : ZMod q × ZMod q => (p.1, (n : ZMod q) * p.2)) := by
    refine Finite.injective_iff_bijective.1 ?_
    intro p₁ p₂ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (mul_left_cancel₀ hn0 h.2)
  exact Fintype.prod_bijective (fun p : ZMod q × ZMod q => (p.1, (n : ZMod q) * p.2)) hbij
    (fun p => (siegelSeries q ![p.1, (n : ZMod q) * p.2] ^ (12 * q)) ^ (μ p.1))
    (fun p => (siegelSeries q ![p.1, p.2] ^ (12 * q)) ^ (μ p.1)) (fun p => rfl)

theorem coeff_siegelProd_fixed (μ : ZMod q → ℕ) (t : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) (n : ℕ) :
    t (PowerSeries.coeff n (siegelProd q μ)) = PowerSeries.coeff n (siegelProd q μ) := by
  conv_rhs => rw [← map_siegelProd_algEquiv q μ t]
  rw [PowerSeries.coeff_map]
  rfl

theorem exists_int_siegelProd (μ : ZMod q → ℕ) :
    ∃ S₀ : PowerSeries ℤ, (siegelProd q μ) = S₀.map (algebraMap ℤ (CyclotomicField q ℚ)) := by
  have h : ∀ n, ∃ m : ℤ, algebraMap ℤ (CyclotomicField q ℚ) m = PowerSeries.coeff n (siegelProd q μ) := fun n =>
    ModularCurve.exists_algebraMap_int_eq_of_mem_zetaSubring_of_forall_algEquiv_apply_eq q _
      (coeff_siegelProd_mem q μ n) (fun σ => coeff_siegelProd_fixed q μ σ n)
  choose m hm using h
  refine ⟨PowerSeries.mk m, ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hm]

end Descent
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit.WF1A"

theorem coeff_zero_siegelProd (μ : ZMod q → ℕ) (hμ0 : μ 0 = 0) :
    PowerSeries.coeff 0 (siegelProd q μ) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, siegelProd, map_prod]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [map_pow, map_pow]
  by_cases hp : p.1 = 0
  · rw [hp, hμ0, pow_zero]
  · rw [ModularCurve.constantCoeff_siegelSeries_eq_one q _ (by simpa using hp), one_pow, one_pow]

theorem exists_embedding : ∃ ι : CyclotomicField q ℚ →+* ℂ, ι (zetaQ q) = Complex.exp (2 * Real.pi * Complex.I / (q : ℂ)) := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  haveI : NeZero q := ⟨hq0⟩
  haveI : NeZero ((q : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hq0⟩
  haveI : IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) := CyclotomicField.isCyclotomicExtension q ℚ
  have hζ := isPrimitiveRoot_zetaQ q
  have hexp : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (q : ℂ))) q := Complex.isPrimitiveRoot_exp q hq0
  have hirr := Polynomial.cyclotomic.irreducible_rat (Fact.out : q.Prime).pos
  set x : ↥(primitiveRoots q ℂ) := ⟨_, (mem_primitiveRoots (Fact.out : q.Prime).pos).2 hexp⟩ with hx
  refine ⟨((hζ.embeddingsEquivPrimitiveRoots ℂ hirr).symm x).toRingHom, ?_⟩
  have h1 := IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe hζ ℂ hirr ((hζ.embeddingsEquivPrimitiveRoots ℂ hirr).symm x)
  rw [Equiv.apply_symm_apply] at h1
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ← h1]

end WF1B
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit.WF1A"

namespace ModularCurve p2m_export "ModularCurve" "siegelFun etaProd constantCoeff_etaProd IsIntegralQExp SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow SiegelUnit.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow qParam_coeff_unique hasSum_qParam_mul hasSum_coeff_etaProd_pow zetaQ isPrimitiveRoot_zetaQ zetaQ_pow zetaSubring zetaQ_mem_zetaSubring multipliable_one_sub_C_mul_X_pow siegelExponent siegelConstExponent siegelSeriesInt multipliable_siegelFactor_left multipliable_siegelFactor_right siegelSeries SiegelUnit.hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div exists_algebraMap_int_eq_of_mem_zetaSubring_of_forall_algEquiv_apply_eq" namespace SiegelUnit p2m_export "ModularCurve.SiegelUnit" "prod_siegelFun_pow_specialLinearGroup_smul exists_isIntegral_hasSum_prod_siegelFun_pow exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div" end ModularCurve.SiegelUnit
p2m_open_scoped "ModularCurve ModularCurve.SiegelUnit" in
open WF1B in
theorem ModularCurve.SiegelUnit.exists_int_hasSum_prod_siegelFun_pow_mul_discriminant_pow
    (q : ℕ) [Fact q.Prime] (μ : ZMod q → ℕ) (hμ0 : μ 0 = 0) (t : ℕ) :
    ∃ c : ℕ → ℤ, c 0 = 1 ∧
      ∀ τ : UpperHalfPlane,
        HasSum
          (fun n : ℕ => ((c n : ℤ) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ) / (q : ℂ)))
          ((∏ r : ZMod q, ∏ s : ZMod q,
              ModularCurve.siegelFun q (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * q * μ r)) *
              ModularForm.discriminant τ ^ t /
            Complex.exp (2 * Real.pi * Complex.I *
              (((∑ r : ZMod q, (μ r : ℤ) *
                  (6 * ((r.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((r.val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ) : ℤ) : ℂ) *
                (τ : ℂ))) := by
  obtain ⟨ι, hι⟩ := exists_embedding q
  obtain ⟨S₀, hS₀⟩ := exists_int_siegelProd q μ
  refine ⟨fun n => PowerSeries.coeff n (S₀ * etaSpread q t), ?_, ?_⟩
  ·
    have h1 : PowerSeries.coeff 0 S₀ = 1 := by
      have := coeff_zero_siegelProd q μ hμ0
      rw [hS₀, PowerSeries.coeff_map] at this
      exact (algebraMap ℤ (CyclotomicField q ℚ)).injective_int (by rw [this, map_one])
    have h2 : PowerSeries.coeff 0 (etaSpread q t) = 1 := by
      rw [coeff_etaSpread, if_pos (dvd_zero q), Nat.zero_div, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_pow, constantCoeff_etaProd, one_pow]
    show PowerSeries.coeff 0 (S₀ * etaSpread q t) = 1
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, h1, h2, mul_one]
  · intro τ
    have h := hasSum_full q μ t ι hι τ
    have hmap : (∏ p : ZMod q × ZMod q, ((siegelSeries q ![p.1, p.2] ^ (12 * q)).map ι) ^ (μ p.1)) *
        (etaSpread q t).map (Int.castRingHom ℂ) = (S₀ * etaSpread q t).map (Int.castRingHom ℂ) := by
      rw [← map_siegelProd, hS₀,
        show PowerSeries.map ι (PowerSeries.map (algebraMap ℤ (CyclotomicField q ℚ)) S₀) =
            PowerSeries.map (ι.comp (algebraMap ℤ (CyclotomicField q ℚ))) S₀ from by rw [PowerSeries.map_comp]; rfl,
        RingHom.ext_int (ι.comp (algebraMap ℤ (CyclotomicField q ℚ))) (Int.castRingHom ℂ), map_mul]
    rw [hmap] at h
    simpa only [PowerSeries.coeff_map, Int.coe_castRingHom, exp_eq_qParam_pow] using h

end BlockB
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral.ModularCurve.SiegelUnit.WF1A"

set_option maxHeartbeats 3200000 in
open scoped MatrixGroups ModularForm in

theorem solution
    (q : ℕ) [Fact q.Prime] (μ : ZMod q → ℕ) (hμ0 : μ 0 = 0) (t : ℕ)
    (ht : ∀ x : ZMod q, x ≠ 0 →
      0 ≤ (∑ r : ZMod q, (μ r : ℤ) *
          (6 * (((r * x).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * x).val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ)) :
    ∃ ϑ : ModularForm (CongruenceSubgroup.Gamma1 q : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)),
      (∀ τ : UpperHalfPlane, ϑ τ =
        (∏ r : ZMod q, ∏ s : ZMod q,
          ModularCurve.siegelFun q (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * q * μ r)) *
          ModularForm.discriminant τ ^ t) ∧
      ∃ (p : PowerSeries ℤ) (n₀ : ℕ), ModularCurve.IsIntegralQExp ϑ p ∧
        (n₀ : ℤ) = (∑ r : ZMod q, (μ r : ℤ) *
          (6 * ((r.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((r.val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ) ∧
        (∀ n : ℕ, n < n₀ → PowerSeries.coeff n p = 0) ∧ PowerSeries.coeff n₀ p = 1 ∧
        ∀ (γ : SL(2, ℤ)) (n : ℕ), IsIntegral ℤ
          ((UpperHalfPlane.qExpansion (q : ℝ) ((⇑ϑ : UpperHalfPlane → ℂ) ∣[12 * (t : ℤ)] (γ : GL (Fin 2) ℝ))).coeff n) := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq : 0 < q := NeZero.pos q

  obtain ⟨ϑ, hϑ, -⟩ :=
    ModularCurve.SiegelUnit.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow q
      (fun r _ => μ r) hμ0 (fun _ _ => rfl) t (fun β => ModularCurve.SiegelUnit.WF1A.growth_of_level q μ t ht β)
  have hϑ' : ∀ τ : UpperHalfPlane, ϑ τ =
      (∏ r : ZMod q, ∏ s : ZMod q,
          ModularCurve.siegelFun q (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * q * μ r)) *
        ModularForm.discriminant τ ^ t := fun τ => hϑ τ
  refine ⟨ϑ, hϑ', ?_⟩

  have hγ : ∀ (γ : SL(2, ℤ)) (n : ℕ), IsIntegral ℤ
      ((UpperHalfPlane.qExpansion (q : ℝ) ((⇑ϑ : UpperHalfPlane → ℂ) ∣[12 * (t : ℤ)] (γ : GL (Fin 2) ℝ))).coeff n) :=
    fun γ n => ModularCurve.SiegelUnit.WF1A.main q (fun r _ => μ r) t γ ϑ hϑ n

  obtain ⟨c, hc0, hcsum⟩ := ModularCurve.SiegelUnit.exists_int_hasSum_prod_siegelFun_pow_mul_discriminant_pow q μ hμ0 t
  have hqn : ∀ (τ : UpperHalfPlane) (k : ℕ),
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (τ : ℂ) / (q : ℂ)) = Function.Periodic.qParam (q : ℝ) (τ : ℂ) ^ k :=
    fun τ k => by
    change _ = Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ) / ((q : ℝ) : ℂ)) ^ k
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hqz : ∀ (τ : UpperHalfPlane),
      Complex.exp (2 * Real.pi * Complex.I *
        (((∑ r : ZMod q, (μ r : ℤ) *
          (6 * ((r.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((r.val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ) : ℤ) : ℂ) * (τ : ℂ)) =
      Function.Periodic.qParam (q : ℝ) (τ : ℂ) ^ ((q : ℤ) *
        ((∑ r : ZMod q, (μ r : ℤ) *
          (6 * ((r.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((r.val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ))) := fun τ => by
    change _ = Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ) / ((q : ℝ) : ℂ)) ^ _
    rw [← Complex.exp_int_mul]
    congr 1
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    push_cast
    field_simp
  have hb : ∀ τ : UpperHalfPlane, HasSum (fun n : ℕ => ((c n : ℤ) : ℂ) * Function.Periodic.qParam (q : ℝ) (τ : ℂ) ^ n)
      (ϑ τ / Function.Periodic.qParam (q : ℝ) (τ : ℂ) ^ ((q : ℤ) *
        ((∑ r : ZMod q, (μ r : ℤ) *
          (6 * ((r.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((r.val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ)))) := fun τ => by
    have h1 := hcsum τ
    simp only [hqn] at h1
    rw [hqz, ← hϑ'] at h1
    exact h1
  obtain ⟨p, n₀, hp, hn₀, hlow, hlead⟩ :=
    ModularCurve.SiegelUnit.WF1A.exists_isIntegralQExp_of_hasSum ϑ q hq
      (ModularCurve.SiegelUnit.WF1A.one_mem_strictPeriods_Gamma1 q)
      (ModularCurve.SiegelUnit.WF1A.natCast_mem_strictPeriods_Gamma1 q) c hc0 _ hb
  exact ⟨p, n₀, hp, hn₀, hlow, hlead, hγ⟩

end S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral (solution)
