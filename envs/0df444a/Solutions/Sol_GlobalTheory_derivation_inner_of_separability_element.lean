-- Prove2me | solution 1 for GlobalTheory.derivation_inner_of_separability_element
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:03.252631+00:00
-- url     : https://prove2.me/submissions/6a38724c-31af-436a-9a06-8871e098ab33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_DerivationInnerOfSeparabilityElement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O : Type) [CommRing O] (N : ℕ)
    (e : TensorProduct ℤ O O) (hN : 0 < N) (he : Algebra.TensorProduct.lmul' ℤ e = (N : O))
    (hc : ∀ c : O, (TensorProduct.tmul ℤ c (1 : O) - TensorProduct.tmul ℤ (1 : O) c) * e = 0)
    (V : Type) [AddCommGroup V] [Module ℚ V] (l r : O →+* Module.End ℚ V)
    (hlr : ∀ a b, Commute (l a) (r b)) (δ : O →+ V)
    (hδ : ∀ a b, δ (a * b) = l b (δ a) + r a (δ b)) :
    ∃ v : V, ∀ a, δ a = l a v - r a v := by
  let Φ : TensorProduct ℤ O O →ₗ[ℤ] V := TensorProduct.lift
    (LinearMap.mk₂ ℤ (fun a b => l a (δ b))
      (fun a a' b => by simp) (fun n a b => by simp)
      (fun a b b' => by simp) (fun n a b => by rw [map_zsmul, map_zsmul]))
  have hΦ : ∀ a b, Φ (TensorProduct.tmul ℤ a b) = l a (δ b) := fun a b => TensorProduct.lift.tmul a b
  have h1 : ∀ (c : O) (t : TensorProduct ℤ O O),
      Φ (TensorProduct.tmul ℤ c (1 : O) * t) = l c (Φ t) := by
    intro c t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, hΦ]
    | add x y hx hy => simp [mul_add, hx, hy]
  have h2 : ∀ (c : O) (t : TensorProduct ℤ O O),
      Φ (TensorProduct.tmul ℤ (1 : O) c * t)
        = l (Algebra.TensorProduct.lmul' ℤ t) (δ c) + r c (Φ t) := by
    intro c t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have h := LinearMap.congr_fun (hlr a c).eq (δ b)
      simp only [Module.End.mul_apply] at h
      simp [Algebra.TensorProduct.tmul_mul_tmul, hΦ, hδ, h]
    | add x y hx hy =>
      simp only [mul_add, map_add, hx, hy, LinearMap.add_apply]
      abel
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨(N : ℚ)⁻¹ • Φ e, fun c => ?_⟩
  have h := congrArg Φ (hc c)
  rw [sub_mul, map_sub, h1, h2, he, map_zero, map_natCast, Module.End.natCast_apply] at h
  have h' : l c (Φ e) - r c (Φ e) = (N : ℚ) • δ c := by
    rw [Nat.cast_smul_eq_nsmul]
    rw [sub_eq_zero] at h
    rw [h]; abel
  rw [map_smul, map_smul, ← smul_sub, h', smul_smul, inv_mul_cancel₀ hN', one_smul]
end GlobalTheory
