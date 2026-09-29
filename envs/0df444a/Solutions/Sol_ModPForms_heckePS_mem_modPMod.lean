-- Prove2me | solution 1 for ModPForms.heckePS_mem_modPMod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2561fa01-16b4-5938-b2b1-02514744dcc2

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModPForms_modPMod_eq_bot_of_neg
import Theorems.Thm_ModPForms_modPCusp_eq_bot_of_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_heckePS_mem_modPMod

set_option autoImplicit false

open scoped MatrixGroups

namespace FltWs24
namespace HeckeStab

open UpperHalfPlane

theorem T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
  simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T]

theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma0 N)]
  exact AddSubgroup.mem_zmultiples 1

section PS
variable {F : Type} [Field F]

theorem coeff_heckePS (k : ℤ) (ℓ : ℕ) (φ : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff n (ModPForms.heckePS k ℓ φ) =
      PowerSeries.coeff (n * ℓ) φ + if ℓ ∣ n then (ℓ : F) ^ (k - 1) * PowerSeries.coeff (n / ℓ) φ else 0 := by
  unfold ModPForms.heckePS
  rw [PowerSeries.coeff_mk]

theorem heckePS_zero (k : ℤ) (ℓ : ℕ) : ModPForms.heckePS k ℓ (0 : PowerSeries F) = 0 := by
  ext n
  rw [coeff_heckePS]
  simp

theorem heckePS_add (k : ℤ) (ℓ : ℕ) (φ ψ : PowerSeries F) :
    ModPForms.heckePS k ℓ (φ + ψ) = ModPForms.heckePS k ℓ φ + ModPForms.heckePS k ℓ ψ := by
  ext n
  simp only [coeff_heckePS, map_add]
  split_ifs <;> ring

theorem heckePS_smul (k : ℤ) (ℓ : ℕ) (a : F) (φ : PowerSeries F) :
    ModPForms.heckePS k ℓ (a • φ) = a • ModPForms.heckePS k ℓ φ := by
  ext n
  simp only [coeff_heckePS, map_smul, smul_eq_mul]
  split_ifs <;> ring

theorem heckePS_zero_weight_of_support (ℓ : ℕ) (hℓ : ℓ.Prime) (c : ℕ → ℤ) (hc : ∀ n, 1 ≤ n → c n = 0) :
    ModPForms.heckePS 0 ℓ (PowerSeries.mk fun n => ((c n : ℤ) : F)) =
      (1 + (ℓ : F) ^ ((0 : ℤ) - 1)) • PowerSeries.mk fun n => ((c n : ℤ) : F) := by
  ext n
  simp only [coeff_heckePS, map_smul, PowerSeries.coeff_mk, smul_eq_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [zero_mul, if_pos (dvd_zero ℓ), Nat.zero_div]
    ring
  · have h1 : c (n * ℓ) = 0 := hc _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hn.ne' hℓ.ne_zero))
    have h2 : c n = 0 := hc n hn
    rw [h1, h2]
    split_ifs with hdvd
    · have h3 : c (n / ℓ) = 0 := hc _ (Nat.div_pos (Nat.le_of_dvd hn hdvd) hℓ.pos)
      rw [h3]
      simp
    · simp

end PS

theorem qExpansion_const (c : ℂ) :
    qExpansion 1 (Function.const UpperHalfPlane c) = c • (1 : PowerSeries ℂ) := by
  have h1 : Function.const UpperHalfPlane c = c • (1 : UpperHalfPlane → ℂ) := by
    funext z
    simp
  have hcf : cuspFunction 1 (1 : UpperHalfPlane → ℂ) = 1 := by
    ext q
    rcases eq_or_ne q 0 with rfl | hq
    · simp [cuspFunction, Function.Periodic.cuspFunction]
      exact tendsto_const_nhds.limUnder_eq
    · simp [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero 1 _ hq]
  rw [h1, qExpansion_smul (by rw [hcf]; exact analyticAt_const) c, qExpansion_one]

theorem intCoeff_eq_zero_of_weight_zero {N' : ℕ} [NeZero N']
    (f : ModularForm (CongruenceSubgroup.Gamma0 N') 0) (c : ℕ → ℤ)
    (hc : ∀ n, ModularFormClass.qCoeff f n = (c n : ℂ)) (n : ℕ) (hn : 1 ≤ n) : c n = 0 := by
  obtain ⟨c₀, hf⟩ := ModularForm.eq_const_of_weight_zero f
  have h := hc n
  unfold ModularFormClass.qCoeff at h
  rw [hf, qExpansion_const, map_smul, PowerSeries.coeff_one, if_neg (by omega), smul_zero] at h
  exact_mod_cast h.symm

theorem heckeT_intCoeff {N' : ℕ} {k : ℤ} (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (F : Type) [Field F]
    {G : Type*} [FunLike G UpperHalfPlane ℂ] (f : G) [ModularFormClass G (CongruenceSubgroup.Gamma0 N') k]
    (c : ℕ → ℤ) (hc : ∀ n, ModularFormClass.qCoeff f n = (c n : ℂ)) :
    (∀ n, ModularFormClass.qCoeff (ModularForm.heckeT k ℓ ⇑f) n =
      ((c (n * ℓ) + if ℓ ∣ n then (ℓ : ℤ) ^ (k - 1).toNat * c (n / ℓ) else 0 : ℤ) : ℂ)) ∧
    ModPForms.heckePS k ℓ (PowerSeries.mk fun n => ((c n : ℤ) : F)) =
      PowerSeries.mk fun n => (((c (n * ℓ) + if ℓ ∣ n then (ℓ : ℤ) ^ (k - 1).toNat * c (n / ℓ) else 0 : ℤ) : ℤ) : F) := by
  have hk' : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
  refine ⟨fun n => ?_, ?_⟩
  · rw [ModularFormClass.qCoeff_heckeT f (one_mem_strictPeriods_Gamma0 N') hℓ.ne_zero n,
      ModularForm.coeffHeckeT]
    have hq : ModularFormClass.qCoeff (⇑f) = fun m => (c m : ℂ) := funext hc
    rw [hq]
    push_cast
    split_ifs
    · rw [← zpow_natCast, hk']
    · rfl
  · ext n
    rw [coeff_heckePS, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    push_cast
    split_ifs
    · rw [← zpow_natCast, hk']
    · rfl

end FltWs24.HeckeStab

open FltWs24.HeckeStab in
theorem solution (N' : ℕ) [NeZero N'] (F : Type) [Field F]
    (k : ℤ) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N')
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N' k F) :
    ModPForms.heckePS k ℓ φ ∈ ModPForms.modPMod N' k F := by

  rcases lt_or_ge k 0 with hk | hk
  · rw [ModPForms.modPMod_eq_bot_of_neg N' k hk F, Submodule.mem_bot] at hφ
    rw [hφ, heckePS_zero]
    exact Submodule.zero_mem _

  unfold ModPForms.modPMod at hφ ⊢
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, c, hc, rfl⟩ := hx
    rcases eq_or_lt_of_le hk with hk0 | hk1
    ·
      subst hk0
      rw [heckePS_zero_weight_of_support ℓ hℓ c (intCoeff_eq_zero_of_weight_zero f c hc)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, c, hc, rfl⟩)
    ·
      obtain ⟨he, hps⟩ := heckeT_intCoeff (show 1 ≤ k by omega) hℓ F f c hc
      rw [hps]
      exact Submodule.subset_span ⟨ModularForm.heckeTLin k hℓ hℓN f, _, he, rfl⟩
  | zero => rw [heckePS_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [heckePS_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [heckePS_smul]; exact Submodule.smul_mem _ a hx

end S_ModPForms_heckePS_mem_modPMod
end P2MW
export P2MW.S_ModPForms_heckePS_mem_modPMod (solution)
