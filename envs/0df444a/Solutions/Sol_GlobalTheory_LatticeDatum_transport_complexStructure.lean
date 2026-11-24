-- Prove2me | solution 1 for GlobalTheory.LatticeDatum.transport_complexStructure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:53.111412+00:00
-- url     : https://prove2.me/submissions/b31fccfd-4aaa-4903-bd76-6013805ab333

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeDatumOfSelfDualLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix nonZeroDivisors TensorProduct
open GlobalTheory GlobalTheory.LatticeDatum
namespace GlobalTheory.LatticeDatum
theorem _root_.solution {O L L' : Type} [CommRing O] [AddCommGroup L] [Module O L]
    [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L')
    (ψ : L' →ₗ[O] L) (χ : L →ₗ[O] L') (K c : ℕ) (hK : 0 < K) (hc : 0 < c)
    (h1 : ∀ x, ψ (χ x) = K • x) (h2 : ∀ x, χ (ψ x) = K • x)
    (hB : ∀ x y, B (ψ x) (ψ y) = c * B' x y) (T : O → ℂ)
    (h : ∃ J : ℝ ⊗[ℤ] L →ₗ[ℝ] ℝ ⊗[ℤ] L, (∀ x, J (J x) = -x) ∧
      (∀ x y, B.baseChange ℝ (J x) (J y) = B.baseChange ℝ x y) ∧
      (∀ x, x ≠ 0 → 0 < B.baseChange ℝ (J x) x) ∧
      ∀ (a : O) (A : ℝ ⊗[ℤ] L →ₗ[ℝ] ℝ ⊗[ℤ] L) (t : ℂ), (∀ x : L, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) → t = T a →
        J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im) :
    ∃ J : ℝ ⊗[ℤ] L' →ₗ[ℝ] ℝ ⊗[ℤ] L', (∀ x, J (J x) = -x) ∧
      (∀ x y, B'.baseChange ℝ (J x) (J y) = B'.baseChange ℝ x y) ∧
      (∀ x, x ≠ 0 → 0 < B'.baseChange ℝ (J x) x) ∧
      ∀ (a : O) (A : ℝ ⊗[ℤ] L' →ₗ[ℝ] ℝ ⊗[ℤ] L') (t : ℂ), (∀ x : L', A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) → t = T a →
        J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im := by
  obtain ⟨J, hJ1, hJ2, hJ3, hJ4⟩ := h
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  let f : ℝ ⊗[ℤ] L' →ₗ[ℝ] ℝ ⊗[ℤ] L := ψ.toAddMonoidHom.toIntLinearMap.baseChange ℝ
  let g : ℝ ⊗[ℤ] L →ₗ[ℝ] ℝ ⊗[ℤ] L' := (K : ℝ)⁻¹ • χ.toAddMonoidHom.toIntLinearMap.baseChange ℝ
  have hf : ∀ (s : ℝ) x, f (s ⊗ₜ x) = s ⊗ₜ ψ x := fun s x => rfl
  have hg : ∀ (s : ℝ) x, g (s ⊗ₜ x) = (K : ℝ)⁻¹ • (s ⊗ₜ χ x) := fun s x => rfl
  have hfg : ∀ x, f (g x) = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul s x =>
      rw [hg, map_smul, hf, h1, ← TensorProduct.mk_apply, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        inv_mul_cancel₀ hK', one_smul, TensorProduct.mk_apply]
  have hgf : ∀ x, g (f x) = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul s x =>
      rw [hf, hg, h2, ← TensorProduct.mk_apply, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        inv_mul_cancel₀ hK', one_smul, TensorProduct.mk_apply]
  have hBf : ∀ x y, B.baseChange ℝ (f x) (f y) = c * B'.baseChange ℝ x y := fun x y => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', mul_add]
    | tmul s x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy', mul_add]
      | tmul u y =>
        rw [hf, hf, LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hB]
        simp only [zsmul_eq_mul]; push_cast; ring
  let e : (ℝ ⊗[ℤ] L') ≃ₗ[ℝ] ℝ ⊗[ℤ] L :=
    LinearEquiv.ofLinear f g (LinearMap.ext hfg) (LinearMap.ext hgf)
  refine ⟨g ∘ₗ J ∘ₗ f, fun x => ?_, fun x y => ?_, fun x hx => ?_, fun a A t hA ht => ?_⟩
  · simp only [LinearMap.comp_apply, hfg, hJ1, map_neg, hgf]
  · apply mul_left_cancel₀ hc'.ne'
    rw [← hBf, ← hBf]
    simp only [LinearMap.comp_apply, hfg, hJ2]
  · have hx' : f x ≠ 0 := fun h0 => hx (by rw [← hgf x, h0, map_zero])
    have := hJ3 _ hx'
    rw [← mul_pos_iff_of_pos_left hc', ← hBf]
    simpa only [LinearMap.comp_apply, hfg] using this
  · obtain ⟨k1, k2, k3⟩ := hJ4 a (f ∘ₗ A ∘ₗ g) t (fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hg, map_smul, hA, ← map_smul χ, ← hg, hfg]) ht
    refine ⟨LinearMap.ext fun x => ?_, ?_, ?_⟩
    · have := congrArg g (LinearMap.congr_fun k1 (f x))
      simpa only [LinearMap.comp_apply, hgf] using this
    · rw [← k2, ← LinearMap.trace_conj' A e]
      congr 1
    · rw [← k3, ← LinearMap.trace_conj' _ e]
      congr 1
      refine LinearMap.ext fun x => ?_
      change f (g (J (f (A (g x))))) = J (f (A (g x)))
      rw [hfg]
end GlobalTheory.LatticeDatum
