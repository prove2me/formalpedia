-- Prove2me | solution 1 for OAI.ShortEgyptian.prepare_aux
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:04:30.404823+00:00
-- url     : https://prove2.me/submissions/c983273e-7568-4aa3-81da-434e0f3f1a91

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/GreedyPreparation.lean:L85-L128
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.prepare_aux. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Density
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_GreedyPreparation
import Theorems.Thm_OAI_ShortEgyptian_greedy_step
import Theorems.Thm_OAI_ShortEgyptian_prepared_cons

-- ---- from OAI.NumberTheory.ShortEgyptian.GreedyPreparation ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

lemma prepared_of_large (A C : ℕ) (hAC : A < C) (T : ℝ) (k : ℕ)
    (hClo : T ≤ C) (hChi : (C:ℝ)<T^2) : Prepared A C T k := by
  exact ⟨[],A,C,by simp,by simp,le_rfl,hAC,by simp,Or.inr ⟨hClo,hChi⟩⟩

lemma prepared_zero (C : ℕ) (hC : 0<C) (T : ℝ) (k : ℕ) : Prepared 0 C T k := by
  exact ⟨[],0,C,by simp,by simp,le_rfl,hC,by simp,Or.inl rfl⟩

lemma prepare_aux (k : ℕ) (A C : ℕ) (hAC : A<C) (T v : ℝ) (hT : 1<T)
    (hv : 0<v) (hsize : (C:ℝ)<T^2) (hsmall : (A:ℝ)/C ≤ Real.exp (-v))
    (hcap : T ≤ Real.exp ((2:ℝ)^k*v)) : Prepared A C T k := by
  induction k generalizing A C v with
  | zero =>
    by_cases hA0 : A=0
    · subst A; exact prepared_zero C hAC T 0
    have hA : 0<A := Nat.pos_of_ne_zero hA0
    have hC : (0:ℝ)<C := by exact_mod_cast hA.trans hAC
    have h1 : (1:ℝ)≤A := by exact_mod_cast hA
    have hE : Real.exp (-v)=1/Real.exp v := by simp only [Real.exp_neg,one_div]
    rw [hE] at hsmall
    simp only [pow_zero,one_mul] at hcap
    have hprod := (div_le_div_iff₀ hC (Real.exp_pos v)).mp hsmall
    have hx : Real.exp v ≤ (C:ℝ) := by nlinarith [Real.exp_pos v]
    exact prepared_of_large A C hAC T 0 (hcap.trans hx) hsize
  | succ k ih =>
    by_cases hA0 : A=0
    · subst A; exact prepared_zero C hAC T (k+1)
    have hA : 0<A := Nat.pos_of_ne_zero hA0
    by_cases hCT : T ≤ (C:ℝ)
    · exact prepared_of_large A C hAC T (k+1) hCT hsize
    have hCT' : (C:ℝ)<T := lt_of_not_ge hCT
    have hC : 0<C := hA.trans hAC
    have hCR : (0:ℝ)<C := by exact_mod_cast hC
    let z := quotient C A
    let r := residue C A z
    have hs := greedy_step A C hA hAC
    change 2 ≤ z ∧ z ≤ C ∧ r < A ∧ _ at hs
    have hz : 0<z := by omega
    have hrCz : r<C*z := by nlinarith [hs.2.2.1]
    have hnextsize : ((C*z:ℕ):ℝ)<T^2 := by
      push_cast
      have hh : (z:ℝ)≤C := by exact_mod_cast hs.2.1
      nlinarith
    have hnextsmall : (r:ℝ)/(C*z:ℕ) ≤ Real.exp (-(2*v)) := by
      rw [Nat.cast_mul]
      apply hs.2.2.2.2.1.trans
      calc
        ((A:ℝ)/C)^2 ≤ (Real.exp (-v))^2 := pow_le_pow_left₀ (by positivity) hsmall 2
        _ = _ := by rw [pow_two,←Real.exp_add]; congr 1; ring
    have hnextcap : T ≤ Real.exp ((2:ℝ)^k*(2*v)) := by
      simpa only [pow_succ,mul_assoc] using hcap
    exact prepared_cons A C hA hAC T k (ih r (C*z) hrCz (2*v) (by positivity) hnextsize hnextsmall hnextcap)

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq


theorem solution : type_of% @_root_.OAI.ShortEgyptian.prepare_aux := @_root_.OAI.ShortEgyptian.prepare_aux
