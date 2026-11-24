-- Prove2me | solution 1 for GlobalTheory.SmoothForms.Sized.proj_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:51:42.880874+00:00
-- url     : https://prove2.me/submissions/f20eef34-98da-4f4c-81fd-f5ee9c71663f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_OrthogonalFrameOfAnisotropicFiniteLengths

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
open GlobalTheory GlobalTheory.SmoothForms
open Module Submodule
namespace GlobalTheory.SmoothForms
namespace Sized
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {V : Type} [AddCommGroup V] [Module E V]
    {h : V →ₗ[E] V →ₗ⋆[E] E} {Λ : Submodule ℤ V} {N : ℤ} {ν : V → ℝ} {B : ℝ} (H : Sized h Λ N ν B)
    {T : ℝ} (hT : 2 ≤ T) {v x : V} (hv : ν v ≤ T) (hx : ν x ≤ T) :
    ν (h v v • x - h x v • v) ≤ T ^ 4 := by
  have hneg : house (-(h x v)) = house (h x v) := by simp [house]
  have h0 : 0 ≤ T := by linarith
  have h1 : house (h v v) ≤ T * T := (H.form_le v v).trans (mul_le_mul hv hv (H.nonneg _) h0)
  have h2 : house (h x v) ≤ T * T := (H.form_le x v).trans (mul_le_mul hx hv (H.nonneg _) h0)
  have h3 : ν (h v v • x) ≤ T * T * T :=
    (H.smul_le _ _).trans (mul_le_mul h1 hx (H.nonneg _) (by positivity))
  have h4 : ν ((-(h x v)) • v) ≤ T * T * T :=
    (H.smul_le _ _).trans (by rw [hneg]; exact mul_le_mul h2 hv (H.nonneg _) (by positivity))
  rw [sub_eq_add_neg, ← neg_smul]
  have h5 : 2 * (T * T * T) ≤ T * (T * T * T) := mul_le_mul_of_nonneg_right hT (by positivity)
  refine (H.add_le _ _).trans ?_
  calc _ ≤ 2 * (T * T * T) := by linarith
    _ ≤ _ := h5
    _ = _ := by ring
end Sized
end GlobalTheory.SmoothForms
