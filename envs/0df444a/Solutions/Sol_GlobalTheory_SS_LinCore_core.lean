-- Prove2me | solution 1 for GlobalTheory.SS.LinCore.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:06:44.441822+00:00
-- url     : https://prove2.me/submissions/74a2bdf9-ab78-4a92-ac13-30c63d8f29da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplectic
import Theorems.Thm_GlobalTheory_SS_LinCore_eq_zero_of_isCoprime
import Theorems.Thm_GlobalTheory_SS_LinCore_aeval_adjoint
import Theorems.Thm_GlobalTheory_SS_LinCore_exists_rev
import Theorems.Thm_GlobalTheory_SS_LinCore_aeval_scale
import Theorems.Thm_GlobalTheory_SS_LinCore_graded_aeval
import Theorems.Thm_GlobalTheory_SS_LinCore_sq_eq_zero_of_cube
import Theorems.Thm_GlobalTheory_SS_LinCore_finrank_le_of_injective

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
theorem _root_.solution [FiniteDimensional 𝕜 V] (B : LinearMap.BilinForm 𝕜 V) (hB : B.Nondegenerate)
    (T Φ Ψ : Module.End 𝕜 V) (q : ℕ) (hq : 2 ≤ q) (hT : IsNilpotent T) (hΨ : Φ * Ψ = 1)
    (hΦ : ∀ x y, B (Φ x) (Φ y) = q * B x y) (h : Φ * (T + 1) = (T + 1) ^ q * Φ)
    (W : Submodule 𝕜 V) (P : ℚ[X]) (hP : ∀ β : ℂ, aeval β P = 0 → ‖β‖ < q)
    (hW : ∀ x ∈ W, Φ x = (q : 𝕜) • x) (hPW : ∀ x, T x = 0 → aeval Φ P x ∈ W) :
    Module.finrank 𝕜 V ≤ Module.finrank 𝕜 (LinearMap.ker T) + Module.finrank 𝕜 W := by
  have hq0 : q ≠ 0 := by omega
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqQ : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq0
  set Q : ℚ[X] := (X - C (q : ℚ)) * P with hQ
  have hQr : ∀ β : ℂ, aeval β Q = 0 → ‖β‖ ≤ q := by
    intro β hβ
    rw [hQ, map_mul, mul_eq_zero] at hβ
    rcases hβ with hβ | hβ
    · have : β = q := by simpa [sub_eq_zero] using hβ
      simp [this]
    · exact (hP β hβ).le
  have hQk : ∀ x, T x = 0 → aeval Φ Q x = 0 := by
    intro x hx
    have := hW _ (hPW x hx)
    rw [hQ, map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C, LinearMap.sub_apply, this,
      Algebra.algebraMap_eq_smul_one]
    simp [Nat.cast_smul_eq_nsmul]
  have hTT : ∀ (i : ℕ) x, (T ^ (i + 1)) x = T ((T ^ i) x) := by
    intro i x
    rw [pow_succ', Module.End.mul_apply]
  have hR : ∀ i : ℕ, ∃ R : ℚ[X], (∀ β : ℂ, aeval β R = 0 → ‖β‖ ≤ q) ∧
      ∀ x, (T ^ i) x = 0 → aeval Φ R x = 0 := by
    intro i
    induction i with
    | zero => exact ⟨1, by simp, fun x hx => by simpa using hx⟩
    | succ i ih =>
      obtain ⟨R, hR1, hR2⟩ := ih
      refine ⟨R * Q.comp (C ((q : ℚ) ^ i) * X), fun β hβ => ?_, fun x hx => ?_⟩
      · rw [map_mul, mul_eq_zero] at hβ
        rcases hβ with hβ | hβ
        · exact hR1 β hβ
        · rw [aeval_scale] at hβ
          have h1 := hQr _ hβ
          rw [Rat.smul_def, norm_mul] at h1
          have h2 : (1 : ℝ) ≤ ‖(((q : ℚ) ^ i : ℚ) : ℂ)‖ := by
            simp only [Rat.cast_pow, Rat.cast_natCast, norm_pow, Complex.norm_natCast]
            exact one_le_pow₀ (by linarith)
          nlinarith [norm_nonneg β]
      · rw [map_mul, Module.End.mul_apply, aeval_scale]
        apply hR2
        have := graded_aeval T Φ q hq0 hT h i 1 Q x hx
        rw [_root_.one_mul, one_smul] at this
        rw [← this]
        exact hQk _ (by rw [← hTT, hx])
  obtain ⟨n, hn⟩ := id hT
  obtain ⟨R, hR1, hR2⟩ := hR n
  have hadj : ∀ x y, B (((q : ℚ) • Ψ) x) y = B x (Φ y) := by
    intro x y
    have h1 : Φ (Ψ x) = x := by rw [← Module.End.mul_apply, hΨ]; rfl
    have := hΦ (Ψ x) y
    rw [h1] at this
    rw [this]
    simp [Nat.cast_smul_eq_nsmul]
  have hR3 : aeval Ψ (R.comp (C (q : ℚ) * X)) = 0 := by
    rw [aeval_scale]
    ext x
    refine hB.1 _ fun y => ?_
    rw [aeval_adjoint B _ _ hadj, hR2 y (by simp [hn]), map_zero]
  obtain ⟨R', hR'1, hR'2⟩ := exists_rev Φ Ψ hΨ _ (fun β hβ => by
    rw [aeval_scale] at hβ
    have h1 := hR1 _ hβ
    rw [Rat.smul_def, norm_mul] at h1
    simp only [Rat.cast_natCast, Complex.norm_natCast] at h1
    nlinarith [norm_nonneg β]) hR3
  have key : ∀ (i : ℕ) (p : ℚ[X]), (∀ β : ℂ, aeval β p = 0 → ‖β‖ < (q : ℝ) ^ i) →
      ∀ x, (T ^ (i + 1)) x = 0 → aeval Φ p ((T ^ i) x) = 0 → (T ^ i) x = 0 := by
    intro i p hp x hx hpx
    refine eq_zero_of_isCoprime Φ (a := p) (b := R'.comp (C ((q : ℚ) ^ i)⁻¹ * X)) ?_ hpx ?_
    · rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ ℂ]
      intro β
      by_contra hc
      push Not at hc
      have h1 := hp _ hc.1
      have h2 := hc.2
      rw [aeval_scale] at h2
      have h3 := hR'1 _ h2
      rw [Rat.smul_def, norm_mul] at h3
      simp only [Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, norm_inv, norm_pow,
        Complex.norm_natCast] at h3
      have h4 : (0 : ℝ) < (q : ℝ) ^ i := by positivity
      rw [inv_mul_eq_div, one_le_div h4] at h3
      linarith
    · rw [aeval_scale, graded_aeval T Φ q hq0 hT h i _ R' x hx,
        inv_mul_cancel₀ (pow_ne_zero i hqQ), one_smul, hR'2]
      simp
  have h32 : ∀ x, (T ^ (2 + 1)) x = 0 → (T ^ 2) x = 0 := by
    intro x hx
    refine key 2 Q (fun β hβ => ?_) x hx (hQk _ (by rw [← hTT, hx]))
    have h1 := hQr β hβ
    have h2 : (q : ℝ) < (q : ℝ) ^ 2 := by
      clear * - hqR
      nlinarith
    exact h1.trans_lt h2
  have hTk := sq_eq_zero_of_cube T hT h32
  refine finrank_le_of_injective T (aeval Φ P) W (fun x => hPW _ (hTk x)) fun x hx => ?_
  have := key 1 P (by simpa only [pow_one] using hP) x (by rw [hTT, pow_one, hTk])
    (by rw [pow_one, hx])
  rwa [pow_one] at this
end GlobalTheory.SS.LinCore
