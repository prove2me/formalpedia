-- Prove2me | solution 1 for InconsistentDR.Shadow.corollary_5_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:16:13.236177+00:00
-- url     : https://prove2.me/submissions/56186f5c-b23b-4603-8606-ded332be4c97

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators
import Theorems.Thm_InconsistentDR_Shadow_theorem_5_5

open scoped InnerProductSpace Pointwise
open ThreeOpSplitting.Convergence InconsistentDR.Shadow

namespace DRShadow57Aux

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

lemma res_fne (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X) (hJ : IsResolvent 1 A J)
    (x y : X) : ‖J x - J y‖ ^ 2 ≤ ⟪J x - J y, x - y⟫_ℝ := by
  have hx := hJ x
  have hy := hJ y
  rw [inv_one, one_smul] at hx hy
  have := hA _ _ _ _ hx hy
  have e : (x - J x) - (y - J y) = (x - y) - (J x - J y) := by abel
  rw [e, inner_sub_right, real_inner_self_eq_norm_sq] at this
  linarith

lemma refl_nonexp (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X) (hJ : IsResolvent 1 A J)
    (x y : X) : ‖refl J x - refl J y‖ ≤ ‖x - y‖ := by
  have h := res_fne A hA J hJ x y
  have e : refl J x - refl J y = (2 : ℝ) • (J x - J y) - (x - y) := by
    simp only [InconsistentDR.Shadow.refl]; module
  have h2 : ‖refl J x - refl J y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [e]
    generalize J x - J y = a at h ⊢
    generalize x - y = b at h ⊢
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, mul_pow]
    norm_num
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

lemma drT_nonexp (A B : X → Set X) (hA : IsMonotoneOp A) (hB : IsMonotoneOp B) (JA JB : X → X)
    (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB) (x y : X) :
    ‖drT JA JB x - drT JA JB y‖ ≤ ‖x - y‖ := by
  have hN : ‖refl JB (refl JA x) - refl JB (refl JA y)‖ ≤ ‖x - y‖ :=
    (refl_nonexp B hB JB hJB _ _).trans (refl_nonexp A hA JA hJA x y)
  have e1 : drT JA JB x - drT JA JB y =
      (1 / 2 : ℝ) • ((x - y) + (refl JB (refl JA x) - refl JB (refl JA y))) := by
    simp only [InconsistentDR.Shadow.drT, InconsistentDR.Shadow.refl]; module
  rw [e1, norm_smul]
  have := norm_add_le (x - y) (refl JB (refl JA x) - refl JB (refl JA y))
  norm_num
  linarith

end DRShadow57Aux

theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB)
    (v vD vR : X)
    (hv : IsMinNormPt (closure (Set.range fun x => x - drT JA JB x)) v)
    (hvD : IsMinNormPt (closure (setD A B)) vD) (hvR : IsMinNormPt (closure (setR A B)) vR)
    (h12 : Standing12 A B JA JB)
    (hvR0 : vR = 0) (hfix : (FixSet fun y => v + drT JA JB y).Nonempty) (x : X) :
    Bornology.IsBounded (Set.range fun n : ℕ => JA ((drT JA JB)^[n] x)) ∧
      Bornology.IsBounded (Set.range fun n : ℕ => JB (refl JA ((drT JA JB)^[n] x))) := by
  have h55 := (theorem_5_5 A B hA hB JA JB hJA hJB v vD vR hv hvD hvR h12 hfix x).1.1
  subst hvR0
  simp only [smul_zero, add_zero] at h55
  refine ⟨h55, ?_⟩
  -- `J_B R_A Tⁿx = J_A Tⁿx - (Tⁿx - Tⁿ⁺¹x)` and the displacement is bounded by `‖x - T x‖`
  set T := drT JA JB with hT
  have hdisp : ∀ n : ℕ, ‖T^[n] x - T (T^[n] x)‖ ≤ ‖x - T x‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (DRShadow57Aux.drT_nonexp A B hA.1 hB.1 JA JB hJA hJB _ _).trans ih
  have hid : ∀ n : ℕ, JB (refl JA (T^[n] x)) = JA (T^[n] x) - (T^[n] x - T (T^[n] x)) := by
    intro n; simp only [hT, drT]; abel
  have hdb : Bornology.IsBounded (Set.range fun n : ℕ => T^[n] x - T (T^[n] x)) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨‖x - T x‖, by rintro _ ⟨n, rfl⟩; exact hdisp n⟩
  have : (Set.range fun n : ℕ => JB (refl JA (T^[n] x))) ⊆
      (Set.range fun n : ℕ => JA (T^[n] x)) - (Set.range fun n : ℕ => T^[n] x - T (T^[n] x)) := by
    rintro _ ⟨n, rfl⟩
    exact ⟨_, ⟨n, rfl⟩, _, ⟨n, rfl⟩, (hid n).symm⟩
  exact (h55.sub hdb).subset this
