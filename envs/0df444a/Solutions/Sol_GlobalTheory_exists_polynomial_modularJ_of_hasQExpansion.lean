-- Prove2me | solution 1 for GlobalTheory.exists_polynomial_modularJ_of_hasQExpansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:08.303176+00:00
-- url     : https://prove2.me/submissions/9d08dc9a-1d8a-48a9-8613-2d9f62d93556

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Theorems.Thm_GlobalTheory_modularJ_smul
import Theorems.Thm_GlobalTheory_exists_hasQExpansion_modularJ
import Theorems.Thm_GlobalTheory_HasQExpansion_congr
import Theorems.Thm_GlobalTheory_HasQExpansion_const
import Theorems.Thm_GlobalTheory_HasQExpansion_isBoundedAtImInfty
import Theorems.Thm_GlobalTheory_HasQExpansion_mdifferentiable
import Theorems.Thm_GlobalTheory_HasQExpansion_mul
import Theorems.Thm_GlobalTheory_HasQExpansion_of_qParam_mul
import Theorems.Thm_GlobalTheory_HasQExpansion_pow
import Theorems.Thm_GlobalTheory_HasQExpansion_sub
import Theorems.Thm_GlobalTheory_HasQExpansion_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real ArithmeticFunction.sigma
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
namespace GlobalTheory
theorem _root_.solution (A : AddSubgroup ℂ) {m : ℕ} {f : ℍ → ℂ}
    {φ : ℂ⟦X⟧} (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (hf : HasQExpansion 1 (fun τ ↦ 𝕢 1 τ ^ m * f τ) φ) (hA : ∀ k, coeff k φ ∈ A) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧ P.coeff m = coeff 0 φ ∧ (∀ i, P.coeff i ∈ A) ∧
      ∀ τ, f τ = P.eval (modularJ τ) := by
  induction m generalizing f φ with
  | zero =>
    simp only [pow_zero, one_mul] at hf
    have hs (γ : SL(2, ℤ)) : f ∣[(0 : ℤ)] γ = f := by
      ext τ; simpa [SL_slash_apply] using hinv γ τ
    let F : ModularForm 𝒮ℒ 0 :=
      { toFun := f
        slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hs γ
        holo' := hf.mdifferentiable one_pos
        bdd_at_cusps' := fun {c} hc ↦ by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
          rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
          intro γ _
          rw [hs γ]
          exact hf.isBoundedAtImInfty one_pos }
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
    have hc' : f = fun _ ↦ c := hc
    have h0 : φ = C c := hf.unique one_pos (hc' ▸ HasQExpansion.const 1 c)
    have h1 : c ∈ A := by simpa [h0] using hA 0
    refine ⟨Polynomial.C c, by simp, by simp [h0], fun i ↦ ?_, fun τ ↦ by simp [hc']⟩
    rw [Polynomial.coeff_C]
    split_ifs
    exacts [h1, A.zero_mem]
  | succ m ih =>
    obtain ⟨J, hJ0, hJ⟩ := exists_hasQExpansion_modularJ
    set c := coeff 0 φ with hc
    have h1 := hf.sub ((HasQExpansion.const 1 c).mul (hJ.pow (m + 1)))
    set ψ := φ - C c * PowerSeries.map (Int.castRingHom ℂ) J ^ (m + 1) with hψ
    have hψA (k : ℕ) : coeff k ψ ∈ A := by
      rw [hψ, map_sub, coeff_C_mul, ← map_pow, coeff_map]
      refine A.sub_mem (hA k) ?_
      simpa [mul_comm, hc] using A.zsmul_mem (hA 0) (coeff k (J ^ (m + 1)))
    obtain ⟨χ, hχ⟩ : X ∣ ψ := X_dvd_iff.mpr (by
      have : constantCoeff (PowerSeries.map (Int.castRingHom ℂ) J) = 1 := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, hJ0, map_one]
      simp [hψ, hc, this])
    have h2 : HasQExpansion 1 (fun τ ↦ 𝕢 1 τ ^ m * (f τ - c * modularJ τ ^ (m + 1))) χ :=
      .of_qParam_mul (hχ ▸ h1.congr fun τ ↦ by ring)
    obtain ⟨P, hP1, -, hP3, hP4⟩ := ih (fun γ τ ↦ by rw [hinv, modularJ_smul]) h2
      (fun k ↦ by simpa [hχ, coeff_succ_X_mul] using hψA (k + 1))
    refine ⟨P + Polynomial.monomial (m + 1) c, ?_, ?_, fun i ↦ ?_, fun τ ↦ ?_⟩
    · exact Polynomial.natDegree_add_le_of_degree_le (by omega)
        (Polynomial.natDegree_monomial_le _)
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hP1)]
    · rw [Polynomial.coeff_add, Polynomial.coeff_monomial]
      refine A.add_mem (hP3 i) ?_
      split_ifs
      exacts [hA 0, A.zero_mem]
    · simp [← hP4]
end GlobalTheory
