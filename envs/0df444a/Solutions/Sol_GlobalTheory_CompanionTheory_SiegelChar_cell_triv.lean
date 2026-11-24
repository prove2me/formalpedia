-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelChar.cell_triv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:55.832282+00:00
-- url     : https://prove2.me/submissions/dca996c6-cc35-4b62-8b7d-7551d3595d4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelChar
variable {E : Type} [CommRing E] {R : Type} [Ring R] [Algebra E R] {c : E → E} {σ : R →+ R}
  {G : Type} [Group G] {φ : G →* R} {e f : R}
namespace GlobalTheory.CompanionTheory.SiegelChar
theorem _root_.solution (hmul : ∀ x y, σ (x * y) = σ y * σ x) (h1 : σ 1 = 1) (hu : ∀ g, σ (φ g) * φ g = 1)
    (hef : e + f = 1) (hee : e * e = e) (hff : f * f = f) (hef0 : e * f = 0) (hfe0 : f * e = 0)
    (hse : σ e = f) (hsf : σ f = e) (lam : G →* ℂˣ)
    (hlow : ∀ s, e * s = 0 → s * f = 0 → σ s = -s → ∃ n, φ n = 1 + s ∧ lam n = 1)
    (hP : ∀ g, f * φ g * e = 0 → lam g = 1) (g : G) (hg : IsUnit (φ g * e + f)) : lam g = 1 := by
  obtain ⟨x, hx⟩ : ∃ x : R, x = φ g := ⟨_, rfl⟩
  rw [← hx] at hg
  have hux : σ x * x = 1 := by rw [hx]; exact hu g
  obtain ⟨u, hu'⟩ := hg
  obtain ⟨w, hw⟩ : ∃ w : R, w = ↑u⁻¹ := ⟨_, rfl⟩
  have hwu : w * (x * e + f) = 1 := by rw [hw, ← hu', Units.inv_mul]
  have huw : (x * e + f) * w = 1 := by rw [hw, ← hu', Units.mul_inv]
  have he2 : ∀ z, e * (e * z) = e * z := fun z => by rw [← mul_assoc, hee]
  have hf2 : ∀ z, f * (f * z) = f * z := fun z => by rw [← mul_assoc, hff]
  have hef2 : ∀ z, e * (f * z) = 0 := fun z => by rw [← mul_assoc, hef0, zero_mul]
  have hfe2 : ∀ z, f * (e * z) = 0 := fun z => by rw [← mul_assoc, hfe0, zero_mul]
  have hwf : w * f = f := by
    have h0 : (x * e + f) * f = f := by rw [add_mul, mul_assoc, hef0, mul_zero, zero_add, hff]
    calc w * f = w * ((x * e + f) * f) := by rw [h0]
      _ = f := by rw [← mul_assoc, hwu, one_mul]
  have hwxe : w * (x * e) = e := by
    have h0 : (x * e + f) * e = x * e := by rw [add_mul, mul_assoc, hee, hfe0, add_zero]
    calc w * (x * e) = w * ((x * e + f) * e) := by rw [h0]
      _ = e := by rw [← mul_assoc, hwu, one_mul]
  have hxe : x * e = e * x * e + f * x * e := by rw [← add_mul, ← add_mul, hef, one_mul]
  have hwfxe : w * (f * x * e) = f * x * e := by rw [← mul_assoc, ← mul_assoc, hwf]
  have hweaxe : w * (e * x * e) = e - f * x * e := by
    have h0 : w * (e * x * e) + w * (f * x * e) = e := by rw [← mul_add, ← hxe, hwxe]
    rw [← hwfxe]
    exact eq_sub_of_add_eq h0
  obtain ⟨s, hs_def⟩ : ∃ s : R, s = -(f * w * e) := ⟨_, rfl⟩
  have hsa : s * (e * x * e) = f * x * e := by
    have h1' : f * w * e * (e * x * e) = f * (w * (e * x * e)) := by simp only [mul_assoc, he2]
    rw [hs_def, neg_mul, h1', hweaxe, mul_sub, hfe0, zero_sub, neg_neg]
    simp only [mul_assoc, hf2]
  have haa' : e * x * e * (e * w * e) = e := by
    have h := congrArg (fun z => e * z * e) huw
    simp only [add_mul, mul_add, mul_assoc, hef2, add_zero, one_mul, mul_one, hee] at h
    simp only [mul_assoc, he2]
    exact h
  have hσ3 : ∀ a b d : R, σ (a * b * d) = σ d * σ b * σ a := by
    intro a b d
    rw [hmul (a * b) d, hmul a b, ← mul_assoc]
  have hσc : σ (f * x * e) = f * σ x * e := by rw [hσ3, hse, hsf]
  have hσa : σ (e * x * e) = f * σ x * f := by rw [hσ3, hse]
  have hrel : σ (f * x * e) * (e * x * e) + σ (e * x * e) * (f * x * e) = 0 := by
    rw [hσc, hσa]
    simp only [mul_assoc, he2, hf2]
    rw [← mul_add, ← mul_add, ← add_mul, hef, one_mul, ← mul_assoc (σ x) x e, hux, one_mul, hfe0]
  have hes : e * s = 0 := by
    rw [hs_def, mul_neg]
    simp only [mul_assoc, hef2, neg_zero]
  have hsf : s * f = 0 := by
    rw [hs_def, neg_mul]
    simp only [mul_assoc, hef0, mul_zero, neg_zero]
  have hse' : s * e = s := by simp only [hs_def, neg_mul, mul_assoc, hee]
  have hfs : f * s = s := by simp only [hs_def, mul_neg, ← mul_assoc, hff]
  have hs_eq : s = f * x * e * (e * w * e) := by
    calc s = s * e := hse'.symm
      _ = s * (e * x * e * (e * w * e)) := by rw [haa']
      _ = f * x * e * (e * w * e) := by rw [← mul_assoc, hsa]
  have hσce : σ (f * x * e) * e = σ (f * x * e) := by
    rw [hσc]
    simp only [mul_assoc, hee]
  have hσc2 : σ (f * x * e) = -(σ (e * x * e) * s) := by
    calc σ (f * x * e) = σ (f * x * e) * e := hσce.symm
      _ = σ (f * x * e) * (e * x * e * (e * w * e)) := by rw [haa']
      _ = (σ (f * x * e) * (e * x * e)) * (e * w * e) := (mul_assoc _ _ _).symm
      _ = (-(σ (e * x * e) * (f * x * e))) * (e * w * e) := by rw [eq_neg_of_add_eq_zero_left hrel]
      _ = -(σ (e * x * e) * s) := by rw [hs_eq, neg_mul, mul_assoc (σ (e * x * e))]
  have hσs : σ s = -s := by
    calc σ s = σ (f * x * e * (e * w * e)) := by rw [← hs_eq]
      _ = σ (e * w * e) * σ (f * x * e) := hmul _ _
      _ = -(σ (e * w * e) * σ (e * x * e) * s) := by rw [hσc2, mul_neg, ← mul_assoc]
      _ = -(σ (e * x * e * (e * w * e)) * s) := by rw [hmul (e * x * e) (e * w * e)]
      _ = -s := by rw [haa', hse, hfs]
  obtain ⟨n, hn, hln⟩ := hlow s hes hsf hσs
  have hss : s * s = 0 := by
    calc s * s = (s * e) * (f * s) := by rw [hse', hfs]
      _ = s * (e * f) * s := by simp only [mul_assoc]
      _ = 0 := by rw [hef0, mul_zero, zero_mul]
  have hninv : φ n⁻¹ = 1 - s := by
    have h0 : (1 + s) * φ n⁻¹ = 1 := by rw [← hn, ← map_mul, mul_inv_cancel, map_one]
    have h1s : (1 - s) * (1 + s) = 1 := by
      calc (1 - s) * (1 + s) = 1 - s * s := by noncomm_ring
        _ = 1 := by rw [hss, sub_zero]
    calc φ n⁻¹ = ((1 - s) * (1 + s)) * φ n⁻¹ := by rw [h1s, one_mul]
      _ = 1 - s := by rw [mul_assoc, h0, mul_one]
  have hsfxe : s * (f * x * e) = 0 := by rw [← mul_assoc, ← mul_assoc, hsf, zero_mul, zero_mul]
  have hsxe : s * (x * e) = f * x * e := by rw [hxe, mul_add, hsa, hsfxe, add_zero]
  have hpar : f * φ (n⁻¹ * g) * e = 0 := by
    rw [map_mul, hninv, ← hx]
    calc f * ((1 - s) * x) * e = f * x * e - f * (s * (x * e)) := by noncomm_ring
      _ = 0 := by rw [← mul_assoc f s, hfs, hsxe, sub_self]
  calc lam g = lam (n * (n⁻¹ * g)) := by rw [mul_inv_cancel_left]
    _ = 1 := by rw [map_mul, hln, hP _ hpar, one_mul]
end GlobalTheory.CompanionTheory.SiegelChar
