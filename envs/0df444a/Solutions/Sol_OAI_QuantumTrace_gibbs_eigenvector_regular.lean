-- Prove2me | solution 1 for OAI.QuantumTrace.gibbs_eigenvector_regular
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:20:19.176541+00:00
-- url     : https://prove2.me/submissions/f8cd9b18-0abe-4a4a-b8bc-fd31189bc081

-- Generated from openai/math@1581d4c lean/OAI/Analysis/QuantumTrace/Basic.lean:L1093-L1169
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.gibbs_eigenvector_regular. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

-- ---- from OAI.Analysis.QuantumTrace.Basic ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open Filter

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open Filter ContinuousLinearMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section

open Filter Topology
open scoped Classical
variable {ι : Type*}
theorem diagonalMap_norm_le (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    {C : ℝ} (hC : 0 ≤ C) (hab : ∀ i, ‖a i‖ ≤ C) : ‖diagonalMap a ha‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have h := lp.norm_mono (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (x := diagonalMap a ha x) (y := (C : ℂ) • x) (fun i => by
      simp only [diagonalMap_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hab i) (norm_nonneg _))
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC] using h

end

section
open Filter Topology
open scoped Classical
variable {ι : Type*}

end

section
open Filter Topology
variable {ι : Type*}

theorem inversePower_norm_le (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    ‖inversePower s hs p‖ ≤ 1 := by
  apply diagonalMap_norm_le _ _ (by norm_num)
  intro i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity [hs i])]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (hs i))

end

section
open ContinuousLinearMap Module.End Submodule
universe v
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open Filter Topology
variable {ι : Type*}

theorem gibbsFactor_inner_lower (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    (k : ℝ) {B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι} (hB : B.IsPositive)
    (x : SequenceHilbert ι) :
    k*‖x‖^2 ≤ (inner ℂ x (gibbsFactor s hs k B x)).re := by
  have hp := hB.adjoint_conj (inversePower s hs 3)
  rw [inversePower_adjoint] at hp
  have hn := hp.re_inner_nonneg_right x
  have he : (inner ℂ x (k • x)).re = k*‖x‖^2 := by
    rw [inner_smul_right_eq_smul, Complex.smul_re]
    simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  change k*‖x‖^2 ≤ (inner ℂ x (k • x + inversePower s hs 3 (B (inversePower s hs 3 x)))).re
  rw [inner_add_right, Complex.add_re, he]
  exact le_add_of_nonneg_right hn

theorem gibbs_eigenvector_regular (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    {k u : ℝ} (hk : 0 < k) (hu : 0 < u)
    {B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι} (hB : B.IsPositive)
    {ψ : SequenceHilbert ι} (hψ : ‖ψ‖ = 1)
    (he : gibbsInverse s hs k B ψ = ((u⁻¹ : ℝ) : ℂ) • ψ) :
    ∃ y z : SequenceHilbert ι,
      (∀ i, y i = (s i^4 : ℝ)*ψ i) ∧
      (∀ i, z i = (s i^7 : ℝ)*ψ i) ∧
      ‖y‖^2 ≤ u/k ∧
      ‖z‖ ≤ k⁻¹*(u+‖B‖*Real.sqrt (u/k)) := by
  let A := gibbsFactor s hs k B
  have hA : IsUnit A := (gibbsFactor_strictPositive s hs hk hB).isUnit
  let y := (u : ℂ) • Ring.inverse A (inversePower s hs 4 ψ)
  have h4 : inversePower s hs 4 y = ψ := by
    have hem : inversePower s hs 4 (Ring.inverse A (inversePower s hs 4 ψ)) =
        ((u⁻¹ : ℝ) : ℂ) • ψ := he
    change inversePower s hs 4 ((u : ℂ) • Ring.inverse A (inversePower s hs 4 ψ)) = ψ
    rw [(inversePower s hs 4).map_smul, hem, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hu.ne']
    simp
  have hy (i : ι) : y i = (s i^4 : ℝ)*ψ i := by
    have h := congrArg (fun x : SequenceHilbert ι => x i) h4
    simp only [inversePower_apply] at h
    have hn : (s i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hs i])
    push_cast at h ⊢
    field_simp at h ⊢
    exact h
  have hAy : A y = (u : ℂ) • inversePower s hs 4 ψ := by
    have hi := congrArg (fun X : SequenceHilbert ι →L[ℂ] SequenceHilbert ι => X (inversePower s hs 4 ψ))
      (Ring.mul_inverse_cancel A hA)
    simpa only [y, map_smul, mul_apply_eq_comp, one_apply_eq_self] using congrArg ((u : ℂ) • ·) hi
  have hybound : ‖y‖^2 ≤ u/k := by
    have hh := gibbsFactor_inner_lower s hs k hB y
    change k*‖y‖^2 ≤ (inner ℂ y (A y)).re at hh
    rw [hAy, inner_smul_right] at hh
    have hm : inner ℂ y (inversePower s hs 4 ψ) = inner ℂ ψ ψ := by
      calc
        _ = inner ℂ (inversePower s hs 4 y) ψ :=
          ((inversePower_positive s hs 4).isSymmetric y ψ).symm
        _ = _ := congrArg (fun v => inner ℂ v ψ) h4
    rw [hm, inner_self_eq_norm_sq_to_K, hψ] at hh
    norm_num at hh
    exact (le_div_iff₀ hk).mpr (by nlinarith)
  have hynorm : ‖y‖ ≤ Real.sqrt (u/k) :=
    (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hybound
  let z := ((k⁻¹ : ℝ) : ℂ) • ((u : ℂ) • inversePower s hs 1 ψ - B (inversePower s hs 3 y))
  have hz (i : ι) : z i = (s i^7 : ℝ)*ψ i := by
    have heq := congrArg (fun x : SequenceHilbert ι => x i) hAy
    change k*(y i) + ((s i^3)⁻¹ : ℝ)*(B (inversePower s hs 3 y) i) =
      u*(((s i^4)⁻¹ : ℝ)*ψ i) at heq
    rw [hy i] at heq
    change ((k⁻¹ : ℝ) : ℂ)*((u : ℂ)*(((s i^1)⁻¹ : ℝ)*ψ i) - B (inversePower s hs 3 y) i) = _
    have hn : (s i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hs i])
    have hkn : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
    push_cast at heq ⊢
    field_simp at heq ⊢
    linear_combination -heq
  refine ⟨y, z, hy, hz, hybound, ?_⟩
  have h1 : ‖inversePower s hs 1 ψ‖ ≤ 1 := by
    calc
      _ ≤ ‖inversePower s hs 1‖*‖ψ‖ := (inversePower s hs 1).le_opNorm _
      _ ≤ 1 := by simpa only [hψ, mul_one] using inversePower_norm_le s hs 1
  have h3 : ‖inversePower s hs 3 y‖ ≤ Real.sqrt (u/k) := by
    calc
      _ ≤ ‖inversePower s hs 3‖*‖y‖ := (inversePower s hs 3).le_opNorm _
      _ ≤ ‖y‖ := by nlinarith [inversePower_norm_le s hs 3, norm_nonneg y]
      _ ≤ _ := hynorm
  calc
    ‖z‖ = k⁻¹*‖(u : ℂ) • inversePower s hs 1 ψ - B (inversePower s hs 3 y)‖ := by
      simp only [z, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
    _ ≤ k⁻¹*(‖(u : ℂ) • inversePower s hs 1 ψ‖ + ‖B (inversePower s hs 3 y)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hk.le)
    _ ≤ k⁻¹*(u+‖B‖*Real.sqrt (u/k)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hk.le)
      apply add_le_add
      · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
        nlinarith
      · exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))

end

section
open Filter Topology

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

end

section
variable {ι J : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end

open scoped BigOperators ComplexConjugate
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end QuantumTrace

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace QuantumTrace
variable {ι J : Type*}

end QuantumTrace

end

end OAI

-- ---- platform node ----
open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open Filter Topology


theorem solution : type_of% @_root_.OAI.QuantumTrace.gibbs_eigenvector_regular := @_root_.OAI.QuantumTrace.gibbs_eigenvector_regular
