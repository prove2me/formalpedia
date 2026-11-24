-- Prove2me | solution 1 for GlobalTheory.exists_smul_eq_bilin_of_anisotropic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:46:57.13081+00:00
-- url     : https://prove2.me/submissions/e157570d-80c5-4d50-be82-55832aaf4b28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSmulEqBilinOfAnisotropic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (B : X →+ X →+ ℤ) (hB : ∀ a, B a a = 0 → a = 0) (l : X →+ ℚ) :
    ∃ (M : ℤ) (x : X), 0 < M ∧ ∀ m, (B x m : ℚ) = M * l m := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (S := ℚ) (fun i => l (b i))
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose c hc using hint
  let φ : Module.Dual ℤ X := b.constr ℤ c
  have hφ : ∀ m, (φ m : ℚ) = d * l m := by
    have : (Algebra.linearMap ℤ ℚ).comp φ = d • l.toIntLinearMap := by
      refine b.ext fun i => ?_
      have := hc i
      simpa [φ] using this
    intro m
    have := LinearMap.congr_fun this m
    simpa using this
  let Bh : X →+ Module.Dual ℤ X :=
    { toFun := fun x => (B x).toIntLinearMap
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let BL : X →ₗ[ℤ] Module.Dual ℤ X := Bh.toIntLinearMap
  have hBL : ∀ x m, BL x m = B x m := fun _ _ => rfl
  have hinj : Function.Injective BL := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply hB
    rw [← hBL, ha]; rfl
  have hrk : Module.finrank ℤ (LinearMap.range BL) = Module.finrank ℤ (Module.Dual ℤ X) := by
    rw [LinearMap.finrank_range_of_inj hinj]
    exact b.toDualEquiv.finrank_eq
  have hfin : Finite (Module.Dual ℤ X ⧸ LinearMap.range BL) :=
    Submodule.finiteQuotientOfFreeOfRankEq _ hrk
  obtain ⟨n, hn, hnφ⟩ := (isOfFinAddOrder_of_finite
    (Submodule.Quotient.mk (p := LinearMap.range BL) φ)).exists_nsmul_eq_zero
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hnφ
  obtain ⟨x, hx⟩ := hnφ
  refine ⟨n * (d * d), d • x, mul_pos (by exact_mod_cast hn) (mul_self_pos.2 hd0), fun m => ?_⟩
  have h1 : B x m = n * φ m := by
    rw [← hBL, hx]; simp
  rw [map_zsmul, AddMonoidHom.zsmul_apply, h1]
  simp only [smul_eq_mul]
  push_cast
  rw [hφ]; ring
end GlobalTheory
