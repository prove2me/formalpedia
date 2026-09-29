-- Prove2me | solution 1 for HighDimStat.Rkhs.thm12_13_converse
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:39:46.72122+00:00
-- url     : https://prove2.me/submissions/2339c4c6-466c-4a52-b507-c9d9323639c8

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace

noncomputable def aux_mac_eval {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (hEval : HasBoundedEvalFunctionals toFun) (x : X) :
    H →L[ℝ] ℝ :=
  LinearMap.mkContinuous ((LinearMap.proj x).comp toFun) (Classical.choose (hEval x))
    (fun f => by
      have := Classical.choose_spec (hEval x) f
      simpa [Real.norm_eq_abs] using this)

noncomputable def aux_mac_feat {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (hEval : HasBoundedEvalFunctionals toFun) (x : X) : H :=
  (InnerProductSpace.toDual ℝ H).symm (aux_mac_eval toFun hEval x)

theorem aux_mac_repr {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (hEval : HasBoundedEvalFunctionals toFun) (f : H) (x : X) :
    ⟪f, aux_mac_feat toFun hEval x⟫ = toFun f x := by
  rw [real_inner_comm]
  unfold aux_mac_feat
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

end HighDimStat.Rkhs

open HighDimStat.Rkhs
open scoped RealInnerProductSpace

theorem solution {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (htoFun : Function.Injective toFun)
    (hEval : HasBoundedEvalFunctionals toFun) :
    ∃! K : X → X → ℝ, IsPSDKernel K ∧ ∃ feature : X → H, IsRKHS K toFun feature := by
  set φ := aux_mac_feat toFun hEval with hφ
  have hrep : ∀ (f : H) (x : X), ⟪f, φ x⟫ = toFun f x := aux_mac_repr toFun hEval
  refine ⟨fun z x => ⟪φ z, φ x⟫, ⟨⟨fun x y => real_inner_comm _ _, ?_⟩, φ, ⟨htoFun, ?_, hrep⟩⟩, ?_⟩
  · intro n x α
    have : ∑ i, ∑ j, α i * α j * ⟪φ (x i), φ (x j)⟫
        = ⟪∑ i, α i • φ (x i), ∑ j, α j • φ (x j)⟫ := by
      rw [sum_inner]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [inner_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [real_inner_smul_left, real_inner_smul_right]
      ring
    rw [this]
    exact real_inner_self_nonneg
  · intro x
    funext z
    rw [← hrep, real_inner_comm]
  · rintro K' ⟨_, feature', hK'⟩
    funext z x
    calc K' z x = toFun (feature' x) z := (congrFun (hK'.feature_eq x) z).symm
      _ = ⟪feature' x, φ z⟫ := (hrep _ _).symm
      _ = ⟪φ z, feature' x⟫ := real_inner_comm _ _
      _ = toFun (φ z) x := hK'.reproducing _ _
      _ = ⟪φ z, φ x⟫ := (hrep _ _).symm
