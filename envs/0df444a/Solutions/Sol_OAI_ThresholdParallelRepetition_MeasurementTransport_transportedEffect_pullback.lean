-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.MeasurementTransport.transportedEffect_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:42:54.764764+00:00
-- url     : https://prove2.me/submissions/03712b91-d66e-4cb2-8bb5-f6f69aa327e5

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/MeasurementTransport.lean:L168-L186
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.MeasurementTransport.transportedEffect_pullback. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Theorems.Thm_OAI_ThresholdParallelRepetition_MeasurementTransport_self_mul_supportInverse_mul

-- ---- from OAI.Probability.EntangledGames.MeasurementTransport ----
namespace OAI

universe u_n u_m u_A

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix

namespace ThresholdParallelRepetition.MeasurementTransport
variable {n : Type u_n} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma bounded_mulVec_zero {G T : Matrix n n ℂ} (hG : G.PosSemidef) (hGT : G ≤ T)
    (x : n → ℂ) (hx : T *ᵥ x = 0) : G *ᵥ x = 0 := by
  apply (hG.dotProduct_mulVec_zero_iff x).mp
  apply le_antisymm _ (hG.dotProduct_mulVec_nonneg x)
  have ht := (Matrix.le_iff.mp hGT).dotProduct_mulVec_nonneg x
  simpa only [Matrix.sub_mulVec, dotProduct_sub, hx, dotProduct_zero, zero_sub,
    dotProduct_neg, neg_nonneg] using ht

omit [DecidableEq n] in
lemma bounded_mul_zero {m : Type u_m} {G T : Matrix n n ℂ}
    (hG : G.PosSemidef) (hGT : G ≤ T) (R : Matrix n m ℂ)
    (hTR : T * R = 0) : G * R = 0 := by
  ext i j
  exact congrFun (bounded_mulVec_zero hG hGT (fun k => R k j)
    (funext fun k => congrFun (congrFun hTR k) j)) i

lemma right_support {G T : Matrix n n ℂ} (hT : T.IsHermitian)
    (hG : G.PosSemidef) (hGT : G ≤ T) : G * (supportInverse T * T) = G := by
  have hzero : T * (1 - supportInverse T * T) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, self_mul_supportInverse_mul hT, sub_self]
  have hz := bounded_mul_zero hG hGT _ hzero
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hz
  exact hz.symm

lemma left_support {G T : Matrix n n ℂ} (hT : T.IsHermitian)
    (hG : G.PosSemidef) (hGT : G ≤ T) : (T * supportInverse T) * G = G := by
  have h := congrArg Matrix.conjTranspose (right_support hT hG hGT)
  simpa only [Matrix.conjTranspose_mul, hT.eq, (supportInverse_isHermitian T).eq,
    hG.isHermitian.eq, Matrix.mul_assoc] using h

variable {m : Type u_m} [Fintype m] [DecidableEq m]

lemma complement_pullback (F : Matrix m n ℂ) :
    Fᴴ * (1 - rangeProjection F) * F = 0 := by
  have h := self_mul_supportInverse_mul (Matrix.isHermitian_conjTranspose_mul_self F)
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  change Fᴴ * F - Fᴴ * (F * supportInverse (Fᴴ * F) * Fᴴ) * F = 0
  rw [show Fᴴ * (F * supportInverse (Fᴴ * F) * Fᴴ) * F =
      (Fᴴ * F) * supportInverse (Fᴴ * F) * (Fᴴ * F) by simp only [Matrix.mul_assoc], h,
    sub_self]

variable {A : Type u_A} [Fintype A] [DecidableEq A]

lemma transportedEffect_pullback (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∀ a, (G a).PosSemidef) (hGT : ∑ a, G a = Fᴴ * F) (a₀ a : A) :
    Fᴴ * transportedEffect F G a₀ a * F = G a := by
  have hle : G a ≤ Fᴴ * F := by
    rw [← hGT]
    exact Finset.single_le_sum (fun b _ => (hG b).nonneg) (Finset.mem_univ a)
  have hherm := Matrix.isHermitian_conjTranspose_mul_self F
  unfold transportedEffect
  rw [Matrix.mul_add, Matrix.add_mul]
  have hzero : Fᴴ * (if a = a₀ then 1 - rangeProjection F else 0) * F = 0 := by
    split_ifs
    · exact complement_pullback F
    · simp
  rw [hzero, add_zero, Matrix.conjTranspose_mul,
    (supportInverse_isHermitian _).eq]
  calc
    _ = ((Fᴴ * F) * supportInverse (Fᴴ * F)) * G a * (supportInverse (Fᴴ * F) * (Fᴴ * F)) := by
      simp only [Matrix.mul_assoc]
    _ = G a := by rw [left_support hherm (hG a) hle, right_support hherm (hG a) hle]

end ThresholdParallelRepetition.MeasurementTransport

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MeasurementTransport
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix


theorem solution.{u_n,u_m,u_A} : type_of% @_root_.OAI.ThresholdParallelRepetition.MeasurementTransport.transportedEffect_pullback.{u_n,u_m,u_A} := @_root_.OAI.ThresholdParallelRepetition.MeasurementTransport.transportedEffect_pullback.{u_n,u_m,u_A}
