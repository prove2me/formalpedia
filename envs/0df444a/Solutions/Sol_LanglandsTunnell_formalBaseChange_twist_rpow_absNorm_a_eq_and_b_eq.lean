-- Prove2me | solution 1 for LanglandsTunnell.formalBaseChange_twist_rpow_absNorm_a_eq_and_b_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/7128ce7b-8218-59fc-805f-17b51eb042ac

import Mathlib
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_formalBaseChange_twist_rpow_absNorm_a_eq_and_b_eq

set_option autoImplicit false

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

noncomputable section

namespace Ws23
namespace BCWPT

open NumberField IsDedekindDomain AutomorphicForm

theorem satakePow_smul_aux {R : Type*} [CommRing R] (c s e : R) :
    ∀ n : ℕ, satakePow n (c * s) (c ^ 2 * e) = c ^ n * satakePow n s e ∧
      satakePow (n + 1) (c * s) (c ^ 2 * e) = c ^ (n + 1) * satakePow (n + 1) s e
  | 0 => by
      refine ⟨?_, ?_⟩
      · simp only [satakePow_zero, pow_zero, one_mul]
      · show satakePow 1 (c * s) (c ^ 2 * e) = c ^ 1 * satakePow 1 s e
        simp only [satakePow_one, pow_one]
  | (n + 1) => by
      obtain ⟨h0, h1⟩ := satakePow_smul_aux c s e n
      refine ⟨h1, ?_⟩
      rw [satakePow_add_two, satakePow_add_two, h0, h1]
      ring

theorem satakePow_smul {R : Type*} [CommRing R] (n : ℕ) (c s e : R) :
    satakePow n (c * s) (c ^ 2 * e) = c ^ n * satakePow n s e :=
  (satakePow_smul_aux c s e n).1

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

theorem absNorm_eq_pow_inertiaDeg_under (𝔓 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm 𝔓.asIdeal =
      Ideal.absNorm (𝔓.under (𝓞 F)).asIdeal ^ (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 F)).asIdeal := by first | infer_instance | exact ⟨rfl⟩
  haveI : (𝔓.under (𝓞 F)).asIdeal.IsMaximal := (𝔓.under (𝓞 F)).isMaximal
  letI : Field ((𝓞 F) ⧸ (𝔓.under (𝓞 F)).asIdeal) := Ideal.Quotient.field _
  haveI : Finite ((𝓞 K) ⧸ 𝔓.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔓.ne_bot
  haveI : Module.Finite ((𝓞 F) ⧸ (𝔓.under (𝓞 F)).asIdeal) ((𝓞 K) ⧸ 𝔓.asIdeal) := Module.Finite.of_finite
  have h1 : Ideal.absNorm 𝔓.asIdeal = Nat.card ((𝓞 K) ⧸ 𝔓.asIdeal) := rfl
  have h2 : Ideal.absNorm (𝔓.under (𝓞 F)).asIdeal = Nat.card ((𝓞 F) ⧸ (𝔓.under (𝓞 F)).asIdeal) := rfl
  rw [h1, h2, Ideal.inertiaDeg_algebraMap]
  exact Module.natCard_eq_pow_finrank

theorem rpow_neg_pow_inertiaDeg (t : ℝ) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    ((((Ideal.absNorm (𝔓.under (𝓞 F)).asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)) ^ (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal =
      (((Ideal.absNorm 𝔓.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_pow]
  congr 1
  have hx : (0 : ℝ) ≤ (Ideal.absNorm (𝔓.under (𝓞 F)).asIdeal : ℝ) := Nat.cast_nonneg _
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_comm, Real.rpow_mul hx, Real.rpow_natCast, ← Nat.cast_pow,
    ← absNorm_eq_pow_inertiaDeg_under F K 𝔓]

end Ws23.BCWPT

end

open IsDedekindDomain NumberField AutomorphicForm

theorem solution
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
    (Φ : HeckeEigensystem F ℂ) (t : ℝ) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange F K (Φ.twist (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))).a 𝔓 =
      ((formalBaseChange F K Φ).twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).a 𝔓 ∧
    (formalBaseChange F K (Φ.twist (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))).b 𝔓 =
      ((formalBaseChange F K Φ).twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).b 𝔓 := by
  have hN := Ws23.BCWPT.rpow_neg_pow_inertiaDeg F K t 𝔓
  refine ⟨?_, ?_⟩
  · simp only [AutomorphicForm.formalBaseChange_a, HeckeEigensystem.twist_a, HeckeEigensystem.twist_b]
    rw [Ws23.BCWPT.satakePow_smul, hN]
  · simp only [AutomorphicForm.formalBaseChange_b, HeckeEigensystem.twist_b]
    rw [← hN]
    ring

end S_LanglandsTunnell_formalBaseChange_twist_rpow_absNorm_a_eq_and_b_eq
end P2MW
export P2MW.S_LanglandsTunnell_formalBaseChange_twist_rpow_absNorm_a_eq_and_b_eq (solution)
