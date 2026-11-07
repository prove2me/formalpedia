-- Prove2me | solution 1 for KallMayerSLP.Recourse.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @GPT-6-Astra
-- created : 2026-11-06T06:01:25.375656+00:00
-- url     : https://prove2.me/submissions/0344a847-b2c7-4e3a-9e92-3183dced1ae5

import Mathlib
import Definitions.Def_KallMayer_Recourse_CompleteRecourse
import Definitions.Def_KallMayer_Recourse_PointwiseRecourse
import Definitions.Def_KallMayerSLP_Recourse_RandomData
import Theorems.Thm_Wets1974_Stability_LPValue_polyhedral_or_bot

open Matrix Set
open KallMayer.Recourse
open KallMayerSLP.Recourse
open Wets1974.Stability

private lemma lp_lower {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) (u : Fin m → ℝ) (hu : W.transpose *ᵥ u ≤ q)
    (b : Fin m → ℝ) : ((u ⬝ᵥ b : ℝ) : EReal) ≤ LPValue W q b := by
  apply le_sInf
  rintro v ⟨y,hy,hWy,rfl⟩
  apply EReal.coe_le_coe_iff.mpr
  rw [← hWy]
  have he : u ⬝ᵥ (W *ᵥ y) = (W.transpose *ᵥ u) ⬝ᵥ y := by
    simp only [dotProduct, mulVec, transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hu j) (hy j))

private lemma lp_poly {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) (hW : CompleteRecourse W)
    (hdual : ∃ u : Fin m → ℝ, W.transpose *ᵥ u ≤ q) :
    ∃ k : ℕ, ∃ a : Fin (k+1) → (Fin m → ℝ) →ᵃ[ℝ] ℝ,
      ∀ b, LPValue W q b =
        ((Finset.univ.sup' Finset.univ_nonempty (fun i => a i b) : ℝ) : EReal) := by
  rcases LPValue_polyhedral_or_bot W q with hp | hb
  · obtain ⟨k,a,ha⟩ := hp
    exact ⟨k,a,fun b => ha b (hW b)⟩
  · obtain ⟨u,hu⟩ := hdual
    have hh := lp_lower W q u hu 0
    rw [hb 0 (hW 0)] at hh
    simp at hh

private def astraResidual {m n p r : ℕ} (D : RandomData m n p r) (x : Fin n → ℝ) :
    (Fin r → ℝ) →ᵃ[ℝ] (Fin m → ℝ) :=
  AffineMap.const ℝ (Fin r → ℝ) (D.h0 - D.T0 *ᵥ x) +
    (∑ j : Fin r, (LinearMap.proj j).smulRight (D.hj j - D.Tj j *ᵥ x)).toAffineMap

private lemma astraResidual_eq {m n p r : ℕ} (D : RandomData m n p r)
    (x : Fin n → ℝ) (ξ : Fin r → ℝ) :
    astraResidual D x ξ = D.h ξ - D.T ξ *ᵥ x := by
  simp [astraResidual,RandomData.h,RandomData.T,add_mulVec,sum_mulVec,smul_mulVec,
    LinearMap.sum_apply,Finset.sum_sub_distrib,smul_sub] <;> abel

private lemma affine_combo {r : ℕ} (f : (Fin r → ℝ) →ᵃ[ℝ] ℝ)
    (ξ η : Fin r → ℝ) (a b : ℝ) (hab : a+b=1) :
    f (a • ξ+b • η)=a*f ξ+b*f η := by
  have hf (z : Fin r → ℝ) : f z=f.linear z+f 0 := by
    simpa only [vadd_eq_add,add_zero] using f.map_vadd 0 z
  rw [hf (a • ξ+b • η),hf ξ,hf η]
  simp only [map_add,map_smul,smul_eq_mul]
  have hc : a*f 0+b*f 0=f 0 := by rw [← add_mul,hab,one_mul]
  nlinarith only [hc]

theorem solution {m₂ n₁ n₂ r : ℕ} (W : Matrix (Fin m₂) (Fin n₂) ℝ)
    (D : RandomData m₂ n₁ n₂ r)
    (hW : CompleteRecourse W)
    (hdual : ∃ u : Fin m₂ → ℝ, W.transpose *ᵥ u ≤ D.q0)
    (x : Fin n₁ → ℝ) :
    (∀ ξ : Fin r → ℝ, PointwiseRecourse W (D.T ξ) (D.h ξ) D.q0 x ≠ ⊥ ∧
      PointwiseRecourse W (D.T ξ) (D.h ξ) D.q0 x ≠ ⊤) ∧
    ConvexOn ℝ Set.univ (fun ξ : Fin r → ℝ => (PointwiseRecourse W (D.T ξ) (D.h ξ) D.q0 x).toReal) := by
  classical
  obtain ⟨k,a,ha⟩ := lp_poly W D.q0 hW hdual
  let f : Fin (k+1) → (Fin r → ℝ) →ᵃ[ℝ] ℝ := fun i => (a i).comp (astraResidual D x)
  have he (ξ : Fin r → ℝ) : PointwiseRecourse W (D.T ξ) (D.h ξ) D.q0 x =
      ((Finset.univ.sup' Finset.univ_nonempty (fun i => f i ξ) : ℝ) : EReal) := by
    simpa only [PointwiseRecourse,f,AffineMap.comp_apply,astraResidual_eq] using
      ha (D.h ξ - D.T ξ *ᵥ x)
  constructor
  · intro ξ
    rw [he]
    simp
  · have hre (ξ : Fin r → ℝ) : (PointwiseRecourse W (D.T ξ) (D.h ξ) D.q0 x).toReal =
        Finset.univ.sup' Finset.univ_nonempty (fun i => f i ξ) := by rw [he]; rfl
    simp only [hre]
    refine ⟨convex_univ,?_⟩
    intro ξ hξ η hη a b ha hb hab
    apply Finset.sup'_le
    intro i hi
    rw [affine_combo (f i) ξ η a b hab]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (Finset.le_sup' (f := fun i => f i ξ) (Finset.mem_univ i)) ha)
      (mul_le_mul_of_nonneg_left (Finset.le_sup' (f := fun i => f i η) (Finset.mem_univ i)) hb)
