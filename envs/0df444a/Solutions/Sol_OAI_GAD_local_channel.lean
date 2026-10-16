-- Prove2me | solution 1 for OAI.GAD.local_channel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:05:37.404165+00:00
-- url     : https://prove2.me/submissions/36dc85ae-846a-48bf-8cd4-e045600556a7

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/Channel.lean:L39-L59
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.local_channel. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel

-- ---- from OAI.InformationTheory.AmplitudeDamping.Channel ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem local_channel (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    applyKraus (kraus γ ν) P =
      !![((1-γ*ν:ℝ):ℂ)*P 0 0+((γ*(1-ν):ℝ):ℂ)*P 1 1,
         (Real.sqrt (1-γ):ℂ)*P 0 1;
         (Real.sqrt (1-γ):ℂ)*P 1 0,
         ((γ*ν:ℝ):ℂ)*P 0 0+((1-γ*(1-ν):ℝ):ℂ)*P 1 1] := by
  have hγ0 : 0 ≤ 1-γ := sub_nonneg.mpr hγ.2
  have hν0 : 0 ≤ 1-ν := sub_nonneg.mpr hν.2
  have hs (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ)^2 = (x:ℂ) := by
    norm_cast; exact Real.sq_sqrt hx
  have hsν := hs ν hν.1
  have hsγν := hs (ν*γ) (mul_nonneg hν.1 hγ.1)
  have hsγν' := hs (-(ν*γ)+γ) (by nlinarith only [mul_nonneg hγ.1 hν0])
  simp only [applyKraus, Fin.sum_univ_four, kraus_zero, kraus_one, kraus_two, kraus_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    simp only [hsν, hsγν, hsγν', hs (1-ν) hν0, hs (1-γ) hγ0] <;>
    push_cast <;> ring

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.local_channel := @_root_.OAI.GAD.local_channel
