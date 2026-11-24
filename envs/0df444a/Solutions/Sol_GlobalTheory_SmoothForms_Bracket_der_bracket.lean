-- Prove2me | solution 1 for GlobalTheory.SmoothForms.Bracket.der_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:06:43.561752+00:00
-- url     : https://prove2.me/submissions/8c022d87-a87c-4d3f-98cf-5d7da35675e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracket
import Theorems.Thm_GlobalTheory_SmoothForms_Bracket_der_eq
import Theorems.Thm_GlobalTheory_SmoothForms_Bracket_der_der_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.Bracket
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
namespace GlobalTheory.SmoothForms.Bracket
theorem _root_.solution : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G),
    IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → ∀ X Y Z : L,
    j Z = j X * j Y - j Y * j X →
    Der (expMap j s) X (Der (expMap j s) Y φ) - Der (expMap j s) Y (Der (expMap j s) X φ) =
      Der (expMap j s) Z φ := by
  intro 𝔸 L G _ _ _ _ _ _ σ j s H hl φ hφ X Y Z hZ
  funext g
  obtain ⟨Λ, hΛ, hΛ1, -⟩ := hl
  have hFs : ContDiffAt ℝ ∞ (fun h : 𝔸 => φ (g * expMap j s (Λ h))) 1 :=
    (hφ g).contDiffAt.comp (1 : 𝔸) hΛ
  have hF2 : ContDiffAt ℝ 2 (fun h : 𝔸 => φ (g * expMap j s (Λ h))) 1 :=
    hFs.of_le (WithTop.coe_le_coe.2 le_top)
  have he : ∀ᶠ h in 𝓝 (1 : 𝔸), σ h * h = 1 → φ (g * s h) = φ (g * expMap j s (Λ h)) := by
    filter_upwards [hΛ1] with h hh hu
    show φ (g * s h) = φ (g * s (NormedSpace.exp (j (Λ h))))
    rw [hh hu]
  have hs1 : s 1 = 1 := by
    have h11 := H.mul 1 1 (by rw [H.one, one_mul]) (by rw [H.one, one_mul])
    rw [one_mul] at h11
    simpa using h11
  have hZd := der_eq H (a := 1) (g := g) (by rw [H.one, one_mul]) (hF2.differentiableAt two_ne_zero) he Z
  rw [hs1, mul_one, one_mul] at hZd
  have hsym := hF2.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  rw [Pi.sub_apply, der_der_eq H hF2 he X Y, der_der_eq H hF2 he Y X, hZd, hZ, map_sub, hsym (j X) (j Y)]
  abel
end GlobalTheory.SmoothForms.Bracket
