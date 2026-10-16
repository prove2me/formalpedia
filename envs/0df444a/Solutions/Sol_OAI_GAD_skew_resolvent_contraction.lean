-- Prove2me | solution 1 for OAI.GAD.skew_resolvent_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:21:49.183147+00:00
-- url     : https://prove2.me/submissions/0b4b5b26-cdfc-4f07-83d9-9358e33b559e

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean:L181-L204
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.skew_resolvent_contraction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation

-- ---- from OAI.InformationTheory.AmplitudeDamping.MatrixDifferentiation ----
namespace OAI

universe u_1 u_2

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

/-- A skew-Hermitian perturbation of the identity is nonsingular. -/
theorem skew_one_add_isUnit (K : Matrix ι ι ℂ) (hK : K.conjTranspose = -K) :
    IsUnit (1 + K) := by
  have he : (1 + K).conjTranspose * (1 + K) = 1 + K.conjTranspose * K := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    noncomm_ring [hK]
  have hp : ((1 + K).conjTranspose * (1 + K)).PosDef := by
    rw [he]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self K)
  have hd := hp.isUnit
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at hd
  exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hd)

/-- The resolvent of a skew-Hermitian matrix is a contraction in quadratic-form order. -/
theorem skew_resolvent_contraction (K : Matrix ι ι ℂ) (hK : K.conjTranspose = -K) :
    (1 - ((1 + K)⁻¹).conjTranspose * (1 + K)⁻¹).PosSemidef := by
  let R := (1 + K)⁻¹
  have hd : IsUnit (1 + K).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (skew_one_add_isUnit K hK)
  have hR : (1 + K) * R = 1 := Matrix.mul_nonsing_inv _ hd
  have hRt : R.conjTranspose * (1 + K).conjTranspose = 1 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
      congrArg Matrix.conjTranspose hR
  have he : (1 + K).conjTranspose * (1 + K) = 1 + K.conjTranspose * K := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    noncomm_ring [hK]
  have hh : R.conjTranspose * (1 + K.conjTranspose * K) * R = 1 := by
    rw [← he, ← Matrix.mul_assoc, hRt, Matrix.one_mul, hR]
  have hh' : 1 - R.conjTranspose * R = (K * R).conjTranspose * (K * R) := by
    rw [Matrix.conjTranspose_mul]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul] at hh
    apply sub_eq_iff_eq_add.2
    rw [← hh]
    noncomm_ring
  change (1 - R.conjTranspose * R).PosSemidef
  rw [hh']
  exact Matrix.posSemidef_conjTranspose_mul_self _

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.skew_resolvent_contraction := @_root_.OAI.GAD.skew_resolvent_contraction
