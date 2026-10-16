-- Prove2me | solution 1 for OAI.ShortEgyptian.holder_density
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:42:35.666687+00:00
-- url     : https://prove2.me/submissions/8788981a-3c5c-4cbd-96ac-98078cb4287c

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/Holder.lean:L23-L40
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.holder_density. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale

-- ---- from OAI.NumberTheory.ShortEgyptian.Holder ----
namespace OAI

universe uι

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma finite_holder_card {ι : Type uι} (H : Finset ι) (f : ι → ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hf : ∀ i ∈ H, 0 ≤ f i) :
    ∑ i ∈ H, f i ≤ (H.card:ℝ)^(1-1/(r:ℝ))*(∑ i ∈ H, (f i)^r)^(1/(r:ℝ)) := by
  have hrR : 1 < (r:ℝ) := by exact_mod_cast (show 1 < r by omega)
  have hc := Real.HolderConjugate.conjExponent hrR
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s:=H) (f:=f) (g:=fun _ => (1:ℝ)) hc hf (by intros; norm_num)
  rw [show 1/Real.conjExponent (r:ℝ) = 1-1/(r:ℝ) by simpa only [one_div] using hc.one_sub_inv.symm] at hh
  simpa only [mul_one,Real.one_rpow,sum_const, nsmul_eq_mul,Real.rpow_natCast,mul_comm] using hh

lemma holder_density {ι : Type uι} (H : Finset ι) (f : ι → ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hf : ∀ i ∈ H, 0 ≤ f i) (Y E : ℝ) (hY : 0 < Y)
    (hm : ∑ i ∈ H, (f i)^r ≤ Y*Real.exp E) :
    ∑ i ∈ H, f i ≤ Y*Real.exp (E/(r:ℝ))*((H.card:ℝ)/Y)^(1-1/(r:ℝ)) := by
  have hrp : 0 < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hh := (finite_holder_card H f r hr hf).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (sum_nonneg (fun i hi => pow_nonneg (hf i hi) r)) hm
      (by positivity : 0 ≤ 1/(r:ℝ))) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply hh.trans_eq
  rw [Real.mul_rpow hY.le (Real.exp_nonneg _),←Real.exp_mul,Real.div_rpow (Nat.cast_nonneg _) hY.le]
  have hy : Y^(1-1/(r:ℝ))*Y^(1/(r:ℝ)) = Y := by rw [←Real.rpow_add hY]; ring_nf; exact Real.rpow_one Y
  have hym : Y^(1-1/(r:ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hY _).ne'
  rw [show E*(1/(r:ℝ)) = E/(r:ℝ) by ring]
  rw [←mul_div_assoc]
  apply (eq_div_iff hym).mpr
  calc
    _ = (Y^(1-1/(r:ℝ))*Y^(1/(r:ℝ)))*Real.exp (E/(r:ℝ))*(H.card:ℝ)^(1-1/(r:ℝ)) := by ring
    _ = _ := by rw [hy]

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical


theorem solution.{uι} : type_of% @_root_.OAI.ShortEgyptian.holder_density.{uι} := @_root_.OAI.ShortEgyptian.holder_density.{uι}
