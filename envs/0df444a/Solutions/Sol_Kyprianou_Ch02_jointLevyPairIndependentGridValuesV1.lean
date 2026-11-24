-- Prove2me | solution 1 for Kyprianou.Ch02.jointLevyPairIndependentGridValuesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:26:04.844291+00:00
-- url     : https://prove2.me/submissions/5470b142-18c5-41c5-a68f-c810ef92cf87

import Theorems.Thm_Kyprianou_Ch02_indepFunOfPairIdentDistribV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_independentPairFamilyProjectionsV1
import Theorems.Thm_Kyprianou_Ch02_finPrefixSumDifferencesV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ℝ≥0 → Ω → ℝ)
    (hA0 : A 0 = fun _ => 0) (hB0 : B 0 = fun _ => 0)
    (hmA : ∀ t, AEMeasurable (A t) P) (hmB : ∀ t, AEMeasurable (B t) P)
    (hi : HasIndependentIncrements (fun t ω => (A t ω,B t ω)) P)
    (hs : HasStationaryIncrements (fun t ω => (A t ω,B t ω)) P)
    (hc : ∀ t, IndepFun (A t) (B t) P)
    (n : ℕ) (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) :
    IndepFun (fun ω i => A (t i) ω) (fun ω i => B (t i) ω) P := by
  let a (i : Fin n) (ω : Ω) := A (t i.succ) ω - A (t i.castSucc) ω
  let b (i : Fin n) (ω : Ω) := B (t i.succ) ω - B (t i.castSucc) ω
  have ha (i : Fin n) : AEMeasurable (a i) P := (hmA _).sub (hmA _)
  have hb (i : Fin n) : AEMeasurable (b i) P := (hmB _).sub (hmB _)
  have hp : iIndepFun (fun i ω => (a i ω, b i ω)) P := hi n t ht
  have hc' (i : Fin n) : IndepFun (a i) (b i) P := by
    let r := t i.succ - t i.castSucc
    have he : t i.castSucc + r = t i.succ := add_tsub_cancel_of_le (ht (Fin.castSucc_le_succ i))
    have hl := hs (t i.castSucc) r
    have hl' : IdentDistrib (fun ω => (a i ω,b i ω))
        (fun ω => (A r ω,B r ω)) P P := by
      rw [he] at hl
      have hzero : increment (fun t ω => (A t ω,B t ω)) 0 r =
          (fun ω => (A r ω,B r ω)) := by
        funext ω
        change (A r ω - A 0 ω,B r ω - B 0 ω) = _
        simp [hA0,hB0]
      rw [hzero] at hl
      exact hl
    exact Kyprianou.Ch02.indepFunOfPairIdentDistribV1 P _ _ hl' (hc r)
  have hind := Kyprianou.Ch02.independentPairFamilyProjectionsV1 P n a b ha hb hp hc'
  let F (v : Fin n → ℝ) (j : Fin (n+1)) :=
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j.val), v i
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro j
    unfold F
    fun_prop
  have heA : F ∘ (fun ω i => a i ω) = fun ω i => A (t i) ω := by
    funext ω j
    exact Kyprianou.Ch02.finPrefixSumDifferencesV1 n (fun i => A (t i) ω)
      (by simp [ht0,hA0]) j
  have heB : F ∘ (fun ω i => b i ω) = fun ω i => B (t i) ω := by
    funext ω j
    exact Kyprianou.Ch02.finPrefixSumDifferencesV1 n (fun i => B (t i) ω)
      (by simp [ht0,hB0]) j
  simpa only [heA,heB] using hind.comp hF hF
