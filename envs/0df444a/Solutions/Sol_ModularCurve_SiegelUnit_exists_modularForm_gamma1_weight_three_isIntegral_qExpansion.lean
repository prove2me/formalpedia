-- Prove2me | solution 1 for ModularCurve.SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/54fcc106-c0e6-5dc5-8fde-1a20ee362c9f

import Mathlib
import Definitions.Def_EisensteinSeries_EisensteinG
import Theorems.Thm_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG
import Theorems.Thm_EisensteinSeries_qExpansion_eisensteinG_coeff
import Theorems.Thm_EisensteinSeries_tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_weight_three_isIntegral_qExpansion

set_option autoImplicit false

open scoped MatrixGroups CongruenceSubgroup ModularForm Nat
open Matrix

namespace Ws45
namespace Eis3Lift

theorem vecMul_SL_eq (N : ℕ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    a ᵥ* γ = a ᵥ* ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) := rfl

theorem vecMul_eq_self_of_mem_Gamma1 (N : ℕ) (a₁ : ZMod N) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) :
    (![0, a₁] : Fin 2 → ZMod N) ᵥ* γ = ![0, a₁] := by
  rw [CongruenceSubgroup.Gamma1_mem] at hγ
  obtain ⟨-, h11, h10⟩ := hγ
  rw [vecMul_SL_eq]
  ext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply, h11, h10]

theorem vecMul_S (N : ℕ) (a₁ : ZMod N) :
    (![0, a₁] : Fin 2 → ZMod N) ᵥ* ModularGroup.S = ![a₁, 0] := by
  rw [vecMul_SL_eq, ModularGroup.coe_S]
  ext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply]

end Ws45.Eis3Lift

theorem Ws45.Eis3Lift.exists_modularForm_gamma1_coe_eq_eisensteinG_and_slash_S
    (N : ℕ) [NeZero N] (k : ℤ) (hk : 3 ≤ k) (a₁ : ZMod N) :
    (∃ F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k,
        ⇑F = EisensteinSeries.eisensteinG N k ![0, a₁]) ∧
      EisensteinSeries.eisensteinG N k ![0, a₁] ∣[k] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) =
        EisensteinSeries.eisensteinG N k ![a₁, 0] := by
  obtain ⟨⟨F, hF⟩, hslash⟩ := EisensteinSeries.exists_modularForm_coe_eq_eisensteinG N k hk ![0, a₁]
  refine ⟨⟨{ toFun := EisensteinSeries.eisensteinG N k ![0, a₁]
             slash_action_eq' := ?_
             holo' := ?_
             bdd_at_cusps' := ?_ }, rfl⟩, ?_⟩
  ·
    intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    have h := hslash A
    rw [Ws45.Eis3Lift.vecMul_eq_self_of_mem_Gamma1 N a₁ A hA, ModularForm.SL_slash] at h
    exact h
  ·
    have := F.holo'
    rw [show (⇑F.toSlashInvariantForm : UpperHalfPlane → ℂ) = EisensteinSeries.eisensteinG N k ![0, a₁] from hF] at this
    exact this
  ·
    intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    have hc' : IsCusp c (Γ(N) : Subgroup (GL (Fin 2) ℝ)) := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).2 hc
    have := F.bdd_at_cusps' hc'
    rw [show (F.toSlashInvariantForm.toFun : UpperHalfPlane → ℂ) = EisensteinSeries.eisensteinG N k ![0, a₁] from hF] at this
    exact this
  ·
    rw [← ModularForm.SL_slash, hslash, Ws45.Eis3Lift.vecMul_S]

namespace Ws45
namespace Eis3

open UpperHalfPlane

theorem qExpansion_one_coeff_eq (N : ℕ) [NeZero N] {k : ℤ}
    (E : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    (qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff n = (qExpansion (N : ℝ) (⇑E : UpperHalfPlane → ℂ)).coeff (N * n) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1
  have hN : (N : ℝ) ∈ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1, AddSubgroup.mem_zmultiples_iff]; exact ⟨N, by simp⟩

  have hs1 : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => (qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff m • Function.Periodic.qParam 1 τ ^ m) (E τ) :=
    fun τ => hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex E h1)
      (ModularFormClass.holo E) (ModularFormClass.bdd_at_infty E) τ

  set c : ℕ → ℂ := fun m => if N ∣ m then (qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff (m / N) else 0 with hc
  have hq : ∀ τ : UpperHalfPlane, Function.Periodic.qParam (N : ℝ) τ ^ N = Function.Periodic.qParam 1 τ := by
    intro τ
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    have : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    push_cast
    field_simp
  have hsN : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => c m • Function.Periodic.qParam (N : ℝ) τ ^ m) (E τ) := by
    intro τ
    have hinj : Function.Injective (fun n : ℕ => N * n) := mul_right_injective₀ (NeZero.ne N)
    rw [← hinj.hasSum_iff]
    · convert hs1 τ using 1
      funext n
      simp only [Function.comp_apply, hc, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N)),
        pow_mul, hq]
    · intro m hm
      have : ¬ N ∣ m := fun ⟨d, hd⟩ => hm ⟨d, hd.symm⟩
      simp [hc, this]
  have := ModularFormClass.qExpansion_coeff_unique hNpos hN (f := E) hsN (N * n)
  rw [← this, hc]
  simp [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N))]

theorem isIntegral_stdAddChar (N : ℕ) [NeZero N] (x : ZMod N) : IsIntegral ℤ (ZMod.stdAddChar x : ℂ) := by
  refine IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne N)) ?_
  have : (ZMod.stdAddChar x : ℂ) ^ N = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    simp
  rw [this]; exact isIntegral_one

theorem isIntegral_natCast (m : ℕ) : IsIntegral ℤ (m : ℂ) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (m : ℤ))

theorem isIntegral_divisorSum (N : ℕ) [NeZero N] (a : Fin 2 → ZMod N) (n k : ℕ) :
    IsIntegral ℤ (∑ m ∈ n.divisors,
      ((if ((n / m : ℕ) : ZMod N) = a 0 then ZMod.stdAddChar (a 1 * (m : ZMod N)) else 0) +
        (-1) ^ k * (if ((n / m : ℕ) : ZMod N) = -a 0 then ZMod.stdAddChar (-(a 1 * (m : ZMod N))) else 0)) *
      (m : ℂ) ^ (k - 1)) := by
  refine IsIntegral.sum _ fun m _ => IsIntegral.mul (IsIntegral.add ?_ (IsIntegral.mul (isIntegral_one.neg.pow k) ?_)) ((isIntegral_natCast m).pow _)
  · split_ifs
    · exact isIntegral_stdAddChar N _
    · exact isIntegral_zero
  · split_ifs
    · exact isIntegral_stdAddChar N _
    · exact isIntegral_zero

end Ws45.Eis3

theorem solution
    (N : ℕ) (hN : 3 ≤ N) :
    ∃ (E : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 3) (a : ℕ),
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff n)) ∧
      (UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0 ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0)⁻¹) ∧
      ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
        ((⇑E : UpperHalfPlane → ℂ) ∣[(3 : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n) := by
  haveI : NeZero N := ⟨by omega⟩
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

  obtain ⟨⟨F, hF⟩, hS⟩ := Ws45.Eis3Lift.exists_modularForm_gamma1_coe_eq_eisensteinG_and_slash_S N 3 le_rfl 1

  obtain ⟨hx0, a₀, hxa, hxinv⟩ := EisensteinSeries.tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral N hN
  set c : ℂ := 2 / (2 * Real.pi * Complex.I) ^ 3 with hc
  have hP : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have := Complex.two_pi_I_ne_zero; simpa [mul_comm, mul_assoc, mul_left_comm] using this

  obtain ⟨⟨F01, hF01⟩, -⟩ := EisensteinSeries.exists_modularForm_coe_eq_eisensteinG N 3 le_rfl ![0, 1]
  obtain ⟨⟨F10, hF10⟩, -⟩ := EisensteinSeries.exists_modularForm_coe_eq_eisensteinG N 3 le_rfl ![1, 0]
  have hNΓ : (N : ℝ) ∈ (Γ(N) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma]; exact AddSubgroup.mem_zmultiples _
  have han01 : AnalyticAt ℂ (UpperHalfPlane.cuspFunction (N : ℝ) (EisensteinSeries.eisensteinG N 3 ![0, 1])) 0 := by
    rw [← hF01]; exact ModularFormClass.analyticAt_cuspFunction_zero F01 hNpos hNΓ
  have han10 : AnalyticAt ℂ (UpperHalfPlane.cuspFunction (N : ℝ) (EisensteinSeries.eisensteinG N 3 ![1, 0])) 0 := by
    rw [← hF10]; exact ModularFormClass.analyticAt_cuspFunction_zero F10 hNpos hNΓ

  have hcoeE : (⇑(c • F) : UpperHalfPlane → ℂ) = c • EisensteinSeries.eisensteinG N 3 ![0, 1] := by
    rw [ModularForm.IsGLPos.coe_smul, hF]
  have hinf : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑(c • F) : UpperHalfPlane → ℂ)).coeff n =
      c * (UpperHalfPlane.qExpansion (N : ℝ) (EisensteinSeries.eisensteinG N 3 ![0, 1])).coeff (N * n) := by
    intro n
    rw [Ws45.Eis3.qExpansion_one_coeff_eq N (c • F) n, hcoeE, UpperHalfPlane.qExpansion_smul han01]
    simp

  have hzeroF : (⇑(c • F) : UpperHalfPlane → ℂ) ∣[(3 : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      c • EisensteinSeries.eisensteinG N 3 ![1, 0] := by
    rw [hcoeE, ← ModularForm.SL_slash, ModularForm.SL_smul_slash, ModularForm.SL_slash, hS]
  have hzero : ∀ n : ℕ, (UpperHalfPlane.qExpansion (N : ℝ)
      ((⇑(c • F) : UpperHalfPlane → ℂ) ∣[(3 : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n =
      c * (UpperHalfPlane.qExpansion (N : ℝ) (EisensteinSeries.eisensteinG N 3 ![1, 0])).coeff n := by
    intro n
    rw [hzeroF, UpperHalfPlane.qExpansion_smul han10]
    simp

  have hq01 := EisensteinSeries.qExpansion_eisensteinG_coeff N 3 le_rfl ![0, 1]
  have hq10 := EisensteinSeries.qExpansion_eisensteinG_coeff N 3 le_rfl ![1, 0]
  simp only [Nat.cast_ofNat] at hq01 hq10
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hv0 : (![0, 1] : Fin 2 → ZMod N) 0 = 0 := rfl
  have hv1 : (![0, 1] : Fin 2 → ZMod N) 1 = 1 := rfl
  have hw0 : (![1, 0] : Fin 2 → ZMod N) 0 = 1 := rfl
  have hfac : (((3 - 1)! : ℕ) : ℂ) = 2 := by norm_num [Nat.factorial]

  have hcoeff0 : (UpperHalfPlane.qExpansion 1 (⇑(c • F) : UpperHalfPlane → ℂ)).coeff 0 =
      2 / (2 * Real.pi * Complex.I) ^ 3 * ∑' d : {d : ℤ // (d : ZMod N) = 1}, ((d : ℂ) ^ 3)⁻¹ := by
    rw [hinf 0, mul_zero, hq01 0, if_pos rfl, if_pos hv0, hv1, hc]

  have halg : ∀ (S : ℂ), (N : ℂ) ^ (a₀ + 3) * (c * ((-2 * Real.pi * Complex.I) ^ 3 / ((((3 - 1)! : ℕ) : ℂ) * (N : ℂ) ^ 3) * S)) =
      -((N : ℂ) ^ a₀ * S) := by
    intro S
    rw [hfac, hc]
    field_simp
    ring
  have hNint : IsIntegral ℤ ((N : ℂ) ^ a₀) := (Ws45.Eis3.isIntegral_natCast N).pow _
  refine ⟨c • F, a₀ + 3, ?_, ?_, ?_, ?_⟩
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hcoeff0, pow_add, mul_comm ((N : ℂ) ^ a₀), mul_assoc]
      exact ((Ws45.Eis3.isIntegral_natCast N).pow 3).mul (by simpa [hc] using hxa)
    · rw [hinf n, hq01 (N * n), if_neg (Nat.mul_ne_zero (NeZero.ne N) hn.ne'), halg]
      exact (hNint.mul (Ws45.Eis3.isIntegral_divisorSum N ![0, 1] (N * n) 3)).neg
  · rw [hcoeff0]
    exact mul_ne_zero (by rw [← hc]; exact div_ne_zero two_ne_zero (pow_ne_zero _ hP)) hx0
  · rw [hcoeff0, pow_add, mul_comm ((N : ℂ) ^ a₀), mul_assoc]
    exact ((Ws45.Eis3.isIntegral_natCast N).pow 3).mul (by simpa [hc] using hxinv)
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : (UpperHalfPlane.qExpansion (N : ℝ) (EisensteinSeries.eisensteinG N 3 ![1, 0])).coeff 0 = 0 := by
        rw [hq10 0, if_pos rfl, if_neg]
        rw [hw0]; exact one_ne_zero
      rw [hzero 0, h0, mul_zero, mul_zero]
      exact isIntegral_zero
    · rw [hzero n, hq10 n, if_neg hn.ne', halg]
      exact (hNint.mul (Ws45.Eis3.isIntegral_divisorSum N ![1, 0] n 3)).neg

end S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_weight_three_isIntegral_qExpansion
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_weight_three_isIntegral_qExpansion (solution)
