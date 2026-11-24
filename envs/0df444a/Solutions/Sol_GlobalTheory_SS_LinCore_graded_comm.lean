-- Prove2me | solution 1 for GlobalTheory.SS.LinCore.graded_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:35:51.736223+00:00
-- url     : https://prove2.me/submissions/66f26b58-f533-49c1-be2f-c544cd92c81f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplectic
import Theorems.Thm_GlobalTheory_SS_LinCore_eq_zero_of_isCoprime
import Theorems.Thm_GlobalTheory_SS_LinCore_exists_binom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LinCore
open Polynomial
variable {𝕜 V : Type} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [Module ℚ V] [IsScalarTower ℚ 𝕜 V]
namespace GlobalTheory.SS.LinCore
theorem _root_.solution (T Φ : Module.End 𝕜 V) (q : ℕ) (hq : q ≠ 0) (hT : IsNilpotent T)
    (h : Φ * (T + 1) = (T + 1) ^ q * Φ) (i : ℕ) (x : V) (hx : (T ^ (i + 1)) x = 0) :
    (T ^ (i + 1)) (Φ x) = 0 ∧ Φ ((T ^ i) x) = (T ^ i) ((((q : ℚ) ^ i) • Φ) x) := by
  obtain ⟨v, hv⟩ := exists_binom q
  obtain ⟨n, hn⟩ := hT
  set u : ℚ[X] := C (q : ℚ) + X * v with hu
  have h1 : Φ * T = aeval T (X * u) * Φ := by
    have h2 := congrArg (aeval T) hv
    rw [map_pow, map_add, map_add, map_one, aeval_X] at h2
    rw [h2, mul_add, add_mul, _root_.mul_one, _root_.one_mul, add_comm Φ] at h
    exact add_right_cancel h
  have h2 : ∀ k : ℕ, Φ * T ^ k = aeval T ((X * u) ^ k) * Φ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← _root_.mul_assoc, ih, _root_.mul_assoc, h1, ← _root_.mul_assoc, ← map_mul,
        ← pow_succ]
  have hcop : IsCoprime u X := by
    have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq
    refine ⟨C (q : ℚ)⁻¹, - (C (q : ℚ)⁻¹ * v), ?_⟩
    have : (C (q : ℚ)⁻¹ * C (q : ℚ) : ℚ[X]) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hq', map_one]
    rw [hu]
    linear_combination this
  have h3 : (T ^ (i + 1)) (Φ x) = 0 := by
    refine eq_zero_of_isCoprime T (hcop.pow (m := i + 1) (n := n)) ?_ ?_
    · have := congrArg (fun f : Module.End 𝕜 V => f x) (h2 (i + 1))
      simp only [Module.End.mul_apply, hx, map_zero] at this
      rw [mul_pow, mul_comm, map_mul, map_pow (aeval T) X, aeval_X, Module.End.mul_apply] at this
      exact this.symm
    · simp [hn]
  refine ⟨h3, ?_⟩
  obtain ⟨w, hw⟩ : (X : ℚ[X]) ∣ u ^ i - C (q : ℚ) ^ i :=
    Dvd.dvd.trans ⟨v, by rw [hu]; ring⟩ (sub_dvd_pow_sub_pow u (C (q : ℚ)) i)
  have h4 : (X * u) ^ i = C ((q : ℚ) ^ i) * X ^ i + w * X ^ (i + 1) := by
    rw [mul_pow, map_pow]
    linear_combination X ^ i * hw
  have := congrArg (fun f : Module.End 𝕜 V => f x) (h2 i)
  simp only [Module.End.mul_apply, h4, map_add, map_mul, map_pow (aeval T) X, aeval_X, aeval_C,
    LinearMap.add_apply, h3, map_zero, add_zero] at this
  rw [this, LinearMap.smul_apply, LinearMap.map_smul_of_tower, Algebra.algebraMap_eq_smul_one]
  simp
end GlobalTheory.SS.LinCore
