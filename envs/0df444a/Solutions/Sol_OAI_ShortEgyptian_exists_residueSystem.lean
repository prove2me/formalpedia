-- Prove2me | solution 1 for OAI.ShortEgyptian.exists_residueSystem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:32:29.454558+00:00
-- url     : https://prove2.me/submissions/9771f3b6-368f-4ee1-b8d8-5ff037e20c65

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ResidueSystem.lean:L141-L180
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.exists_residueSystem. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_assemble_residueSystem
import Theorems.Thm_OAI_ShortEgyptian_choose_random_lists
import Theorems.Thm_OAI_ShortEgyptian_scalePrimes_card
import Theorems.Thm_OAI_ShortEgyptian_terminal_interval

-- ---- from OAI.NumberTheory.ShortEgyptian.PrimeLists ----
namespace OAI

namespace ShortEgyptian

open Finset
lemma scalePrimes_mem (S : ℝ) (p : ℕ) (hp : p ∈ scalePrimes S) :
    p.Prime ∧ S^100 ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*S^100 := by
  obtain ⟨hI,hprime⟩ := mem_filter.mp hp
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hI
  have hS : 0 ≤ S^100 := even_two.mul_right (50:ℕ) |>.pow_nonneg S
  refine ⟨hprime,?_,?_⟩
  · exact (Nat.lt_of_floor_lt hlo).le
  · have hh : (p:ℝ) ≤ 2*(⌊S^100⌋₊:ℝ) := by exact_mod_cast hhi
    exact hh.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hS) (by norm_num))

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical Filter Topology

lemma scaleM_bounds (S : ℝ) (hlog : 1 ≤ Real.log S) (hS : 4*Real.log S ≤ S) :
    S/(2*Real.log S) ≤ (scaleM S:ℝ) ∧ (scaleM S:ℝ) ≤ S/Real.log S ∧
      (scaleM S:ℝ) ≤ S := by
  have hl : 0 < Real.log S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hf := Nat.sub_one_lt_floor (S/Real.log S)
  have hu := Nat.floor_le (div_nonneg hS0 hl.le)
  have hx : 4 ≤ S/Real.log S := (le_div_iff₀ hl).mpr (by linarith)
  refine ⟨?_,hu,hu.trans (div_le_self hS0 hlog)⟩
  dsimp [scaleM]
  have heq : S/(2*Real.log S) = (S/Real.log S)/2 := by ring
  rw [heq]
  linarith

lemma level_before_depth (S : ℝ) (hm : 0 < scaleM S) (j : ℕ) :
    j < depth S ↔ Real.exp (scaleM S:ℝ) < level S j := by
  have hmR : 0 < (scaleM S:ℝ) := by exact_mod_cast hm
  rw [depth,Nat.lt_ceil,lt_div_iff₀ (by positivity : (0:ℝ)<(1/10000:ℝ)*scaleM S)]
  unfold level
  rw [Real.exp_lt_exp]
  constructor <;> intro h <;> nlinarith

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleBounds ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open Filter Topology

lemma ListScale.log_one {S : ℝ} (h : ListScale S) : 1 ≤ Real.log S := by linarith [h.log_large]
lemma ListScale.m_bounds {S : ℝ} (h : ListScale S) :
    S/(2*Real.log S) ≤ (scaleM S:ℝ) ∧ (scaleM S:ℝ) ≤ S/Real.log S ∧ (scaleM S:ℝ) ≤ S :=
  scaleM_bounds S h.log_one (by linarith [h.log_bound,h.log_large])
lemma ListScale.m_pos {S : ℝ} (h : ListScale S) : 0 < scaleM S := by
  have hh : 0 < (scaleM S:ℝ) := by linarith [h.m_large,h.log_large]
  exact_mod_cast hh
lemma ListScale.m_fourier {S : ℝ} (h : ListScale S) : 100000*Real.log S ≤ (99/100:ℝ)*scaleM S := by
  linarith [h.m_large,h.log_large]
end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ResidueSystem ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uA

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma exists_residueSystem (S : ℝ) (h : ListScale S) (C : ℕ)
    (hClo : Real.exp ((dimC:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) :
    Nonempty (ResidueSystem S C) := by
  let P := scalePrimes S
  have hP : S^99 ≤ (P.card:ℝ) := scalePrimes_card S h.two_le h.log_one
    (by linarith [h.log_bound,h.log_large])
  have hmP : scaleM S ≤ Fintype.card P := by
    have hpow : S ≤ S^99 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith [h.two_le] : (1:ℝ)≤S) (by norm_num : 1 ≤ 99)
    have hh : (scaleM S:ℝ) ≤ Fintype.card P := by simpa using h.m_bounds.2.2.trans (hpow.trans hP)
    exact_mod_cast hh
  have hPpos : 0 < P.card := by simpa using h.m_pos.trans_le hmP
  obtain ⟨p',hp'⟩ := P.card_pos.mp hPpos
  have : Nonempty P := ⟨⟨p',hp'⟩⟩
  let p : P → ℕ := Subtype.val
  have hp (x : P) := (scalePrimes_mem S x x.property).1
  have hpmax (x : P) := (scalePrimes_mem S x x.property).2.2
  have hpmin (x : P) := (scalePrimes_mem S x x.property).2.1
  let e : Fin (scaleM S) → P := fun j => (Fintype.equivFin P).symm ⟨j.val,lt_of_lt_of_le j.isLt hmP⟩
  let p₀ : Fin (scaleM S) → ℕ := fun j => p (e j)
  have hinj : Function.Injective p₀ := by
    intro i j hij
    have he : e i = e j := Subtype.ext hij
    have hh := (Fintype.equivFin P).symm.injective he
    exact Fin.ext (congrArg (fun x : Fin (Fintype.card P) => x.val) hh)
  let D := {j : Fin (depth S) // level S j ≤ Real.exp S}
  let X : D → ℝ := fun j => level S j.val
  let U := Icc (⌊S^100000⌋₊+1) ⌊Real.exp (scaleM S:ℝ)⌋₊
  have hX (j : D) : Real.exp (⌊S/Real.log S⌋₊:ℝ) ≤ X j ∧ X j ≤ Real.exp S :=
    ⟨((level_before_depth S h.m_pos j.val).mp j.val.isLt).le,j.property⟩
  have hsmall : (Fintype.card D:ℝ)*Real.exp (-(1/250:ℝ)*(scaleM S:ℝ)) < 1/2 := by
    have hd : Fintype.card D ≤ depth S := by
      simpa only [Fintype.card_fin] using (Fintype.card_subtype_le (fun j : Fin (depth S) => level S j ≤ Real.exp S))
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hd) (Real.exp_nonneg _)).trans_lt h.depth_tail
  obtain ⟨f,hf,hterm⟩ := choose_random_lists S (J := Fin (scaleM S)) (Fintype.card_fin _)
    h.log_one (by linarith [h.log_bound,h.log_large]) p hp Subtype.val_injective hpmax
    (by simpa using hP) h.m_fourier h.m_bounds.2.2 X hX U (terminal_interval S h) hsmall
  exact assemble_residueSystem S h C hClo hChi p₀ (fun j => hp (e j)) hinj
    (fun j => hpmax (e j)) (fun j => hpmin (e j)) p hp hpmax f
    (fun j hj hx => hf ⟨⟨j,hj⟩,hx⟩) hterm

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical


theorem solution : type_of% @_root_.OAI.ShortEgyptian.exists_residueSystem := @_root_.OAI.ShortEgyptian.exists_residueSystem
