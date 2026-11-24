-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SmallPair.exists_small_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:29:00.253285+00:00
-- url     : https://prove2.me/submissions/aaec0a47-a007-4c8c-954d-4a35f6c9ed81

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBound
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SmallPair_exists_realBasis
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SmallPair_exists_small

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SmallPair
namespace GlobalTheory.CompanionTheory.SW.SmallPair
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∃ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) ∧
      ∀ w, ‖((ρ w (c : F) : ℝ) : ℂ) * τ w + (ρ w (d : F) : ℝ)‖ ^ 2 ≤ C * (τ w).im := by
  intro F _ _ hF ρ hρ
  classical
  obtain ⟨κ, _, b, hb⟩ := exists_realBasis hF ρ hρ
  let Φ : 𝓞 F →+ (InfinitePlace F → ℝ) :=
    { toFun := fun a w => ρ w (a : F)
      map_zero' := by funext w; simp
      map_add' := fun x y => by funext w; simp }
  obtain ⟨R, hR, H⟩ := exists_small b Φ.range (fun i => by
    obtain ⟨a, ha⟩ := hb i
    exact ⟨a, funext fun w => (ha w).symm⟩)
  refine ⟨2 * R ^ 2, fun τ hτ => ?_⟩
  obtain ⟨u, ⟨c, rfl⟩, v, ⟨d, rfl⟩, hne, hbd⟩ := H τ hτ
  refine ⟨c, d, ?_, fun w => ?_⟩
  · rcases hne with h | h
    · left; rintro rfl; exact h (map_zero Φ)
    · right; rintro rfl; exact h (map_zero Φ)
  · obtain ⟨h1, h2⟩ := hbd w
    set y := (τ w).im with hy
    set X := (τ w).re with hX
    have hy0 : 0 < y := hτ w
    have hs : 0 < √y := Real.sqrt_pos.mpr hy0
    have hss : √y * √y = y := Real.mul_self_sqrt hy0.le
    set a : ℝ := ρ w (c : F) with ha
    set e : ℝ := ρ w (d : F) with he
    have h1' : |√y * a| ≤ R := h1
    have h2' : |X / √y * a + 1 / √y * e| ≤ R := h2
    have q1 : (√y * a) ^ 2 ≤ R ^ 2 := sq_le_sq' (abs_le.mp h1').1 (abs_le.mp h1').2
    have q2 : (X / √y * a + 1 / √y * e) ^ 2 ≤ R ^ 2 :=
      sq_le_sq' (abs_le.mp h2').1 (abs_le.mp h2').2
    have r1 : y * a ^ 2 ≤ R ^ 2 := by
      have : (√y * a) ^ 2 = y * a ^ 2 := by rw [mul_pow, Real.sq_sqrt hy0.le]
      linarith
    have r2 : (X * a + e) ^ 2 ≤ R ^ 2 * y := by
      have : (X / √y * a + 1 / √y * e) ^ 2 * y = (X * a + e) ^ 2 := by
        have : X / √y * a + 1 / √y * e = (X * a + e) / √y := by field_simp
        rw [this, div_pow, Real.sq_sqrt hy0.le]
        field_simp
      rw [← this]
      exact mul_le_mul_of_nonneg_right q2 hy0.le
    have nrm : ‖((a : ℝ) : ℂ) * τ w + (e : ℝ)‖ ^ 2 = (a * X + e) ^ 2 + (a * y) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [hX, hy]
      ring
    rw [nrm]
    have r3 : (a * y) ^ 2 ≤ R ^ 2 * y := by
      have : (a * y) ^ 2 = (y * a ^ 2) * y := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right r1 hy0.le
    have r4 : (a * X + e) ^ 2 = (X * a + e) ^ 2 := by ring
    rw [r4]
    nlinarith
end GlobalTheory.CompanionTheory.SW.SmallPair
