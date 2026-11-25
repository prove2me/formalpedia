-- Prove2me | solution 1 for GlobalTheory.SW.ShortStep.quot_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:36.4476+00:00
-- url     : https://prove2.me/submissions/9695b12c-e20f-42cb-a0cd-5c23bab820eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.ShortStep
theorem _root_.solution {N : ℕ} {n m : ℕ} {G : Matrix (Fin n) (Fin n) E} {V w : Matrix (Fin 1) (Fin n) E}
    {B : Matrix (Fin m) (Fin n) E} {S : Matrix (Fin n) (Fin m) E} (hG : Gᴴ = G)
    (hV : V * G * Vᴴ = 0) (hB : B * G * Vᴴ = 0)
    (hS : S * B = 1 - G * wᴴ * V - G * Vᴴ * w) {W : Matrix (Fin (N + 1)) (Fin n) E}
    (hW : IsoRows G W) : ∃ T : Matrix (Fin N) (Fin m) E, IsoRows (B * G * Bᴴ) T := by
  classical
  have hiso : W * G * Wᴴ = 0 := hW.2
  have hWi := Matrix.vecMul_injective_iff.2 hW.1
  have key : ∃ z : Matrix (Fin 1) (Fin n) E, ∀ t : Fin (N + 1) → E, t ᵥ* (W * G * zᴴ) = 0 →
      t ᵥ* (W * G * Vᴴ) = 0 ∧ (t ᵥ* (W * S) = 0 → t = 0) := by
    have main : ∀ t : Fin (N + 1) → E, t ᵥ* (W * G * Vᴴ) = 0 → t ᵥ* (W * S) = 0 →
        t ᵥ* W = (t ᵥ* (W * G * wᴴ)) ᵥ* V := fun t h1 h2 => by
      have h3 : W * S * B = W - W * G * wᴴ * V - W * G * Vᴴ * w := by
        rw [Matrix.mul_assoc, hS]; simp [Matrix.mul_sub, Matrix.mul_assoc]
      have := congrArg (fun Z => t ᵥ* Z) h3
      simp only [vecMul_sub] at this
      rw [← vecMul_vecMul t (W * S), h2, ← vecMul_vecMul t (W * G * Vᴴ), h1,
        ← vecMul_vecMul t (W * G * wᴴ)] at this
      simp only [zero_vecMul, sub_zero] at this
      exact sub_eq_zero.1 this.symm
    by_cases hv : ∃ s : Matrix (Fin 1) (Fin (N + 1)) E, s * W = V
    · obtain ⟨s, rfl⟩ := hv
      have h1 : W * G * (s * W)ᴴ = 0 := by
        rw [conjTranspose_mul, ← Matrix.mul_assoc, hiso, Matrix.zero_mul]
      refine ⟨w, fun t ht => ⟨by rw [h1, vecMul_zero], fun h2 => hWi ?_⟩⟩
      have := main t (by rw [h1, vecMul_zero]) h2
      simpa [ht] using this
    · refine ⟨V, fun t ht => ⟨ht, fun h2 => hWi ?_⟩⟩
      have h3 := main t ht h2
      generalize t ᵥ* (W * G * wᴴ) = α at h3
      by_cases hα : α 0 = 0
      · have : α = 0 := by ext i; rw [Subsingleton.elim i 0]; exact hα
        simpa [this] using h3
      · refine (hv ⟨Matrix.of fun _ => (α 0)⁻¹ • t, ?_⟩).elim
        ext i j
        have := congrFun h3 j
        rw [Subsingleton.elim i 0]
        change (((α 0)⁻¹ • t) ᵥ* W) j = _
        rw [smul_vecMul, Pi.smul_apply, this]
        simp [vecMul, dotProduct, hα]
  obtain ⟨z, hz⟩ := key
  have hr : N ≤ Module.finrank E (LinearMap.ker (W * G * zᴴ).vecMulLinear) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (W * G * zᴴ).vecMulLinear
    have h2 := Submodule.finrank_le (LinearMap.range (W * G * zᴴ).vecMulLinear)
    simp only [Module.finrank_fin_fun] at h1 h2
    omega
  obtain ⟨u, hu⟩ := exists_linearIndependent_of_le_finrank hr
  have hu' := hu.map' _ (Submodule.ker_subtype _)
  let U : Matrix (Fin N) (Fin (N + 1)) E := Matrix.of fun i => (u i).1
  have hUi : Function.Injective U.vecMul := Matrix.vecMul_injective_iff.2 hu'
  have hU : U * (W * G * zᴴ) = 0 := by ext i j; exact congrFun (u i).2 j
  have hUV : U * (W * G * Vᴴ) = 0 := by ext i j; exact congrFun (hz _ (u i).2).1 j
  refine ⟨U * (W * S), Matrix.vecMul_injective_iff.1 ?_, ?_⟩
  · change Function.Injective (U * (W * S)).vecMulLinear
    rw [injective_iff_map_eq_zero]
    intro c hc
    refine hUi ?_
    have := (hz (c ᵥ* U) (by rw [vecMul_vecMul, hU, vecMul_zero])).2
      (by rw [vecMul_vecMul]; exact hc)
    simpa using this
  · have h3 : U * (W * S) * B = U * W - U * W * G * wᴴ * V := by
      have : U * (W * (G * (Vᴴ * w))) = 0 := by
        simpa [Matrix.mul_assoc] using congrArg (fun Z => Z * w) hUV
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hS]; simp [Matrix.mul_sub, Matrix.mul_assoc, this]
    have h4 : U * (W * S) * B * G * Vᴴ = 0 := by
      rw [Matrix.mul_assoc _ B, Matrix.mul_assoc _ (B * G), hB, Matrix.mul_zero]
    have h5 : V * G * (U * W)ᴴ = 0 := by
      simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using congrArg conjTranspose hUV
    have h6 : U * W * G * (U * W)ᴴ = 0 := by
      rw [conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc U, Matrix.mul_assoc U, hiso]; simp
    have h7 : U * (W * S) * (B * G * Bᴴ) * (U * (W * S))ᴴ =
        U * (W * S) * B * G * (U * (W * S) * B)ᴴ := by
      rw [conjTranspose_mul _ B]; simp only [Matrix.mul_assoc]
    refine h7.trans ?_
    nth_rewrite 2 [h3]
    rw [conjTranspose_sub, conjTranspose_mul _ V, Matrix.mul_sub, ← Matrix.mul_assoc _ Vᴴ, h4, h3,
      Matrix.sub_mul, Matrix.sub_mul, h6, Matrix.mul_assoc _ V, Matrix.mul_assoc _ (V * G), h5]
    simp
end GlobalTheory.SW.ShortStep
