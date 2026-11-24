-- Prove2me | solution 1 for Kyprianou.Ch02.independentPairArraysSeparateVectorsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:28:39.243087+00:00
-- url     : https://prove2.me/submissions/3fd48045-7049-4107-b028-467962ba4156

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_independentPairArraysUncurryV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (F : Fin n → Ω → ℝ × ℝ)
    (hm : ∀ i, AEMeasurable (F i) P) (hi : iIndepFun F P)
    (hc : ∀ i, IndepFun (fun ω => (F i ω).1) (fun ω => (F i ω).2) P) :
    IndepFun (fun ω i => (F i ω).1) (fun ω i => (F i ω).2) P := by
  classical
  let G (i : Fin n) := (hm i).mk (F i)
  have hG : ∀ i, Measurable (G i) := fun i => (hm i).measurable_mk
  have hFG : ∀ i, F i =ᵐ[P] G i := fun i => (hm i).ae_eq_mk
  have hC : ∀ i, IndepFun (fun ω => (G i ω).1) (fun ω => (G i ω).2) P :=
    fun i => (hc i).congr ((hFG i).fun_comp Prod.fst) ((hFG i).fun_comp Prod.snd)
  have h := Kyprianou.Ch02.independentPairArraysUncurryV1 P n G hG (hi.congr hFG) hC
  let S : Finset (Fin n × Fin 2) := Finset.univ.filter fun p => p.2 = 0
  let T : Finset (Fin n × Fin 2) := Finset.univ.filter fun p => p.2 = 1
  have hd : Disjoint S T := by
    simp [S,T,Finset.disjoint_left]
  let U (p : Fin n × Fin 2) (ω : Ω) :=
    if p.2=0 then (G p.1 ω).1 else (G p.1 ω).2
  have hmU : ∀ p, Measurable (U p) := by
    intro p
    unfold U
    split_ifs
    · exact measurable_fst.comp (hG _)
    · exact measurable_snd.comp (hG _)
  have hST := h.indepFun_finset S T hd hmU
  let a (i : Fin n) : S := ⟨(i,0),by simp [S]⟩
  let b (i : Fin n) : T := ⟨(i,1),by simp [T]⟩
  have ha : Measurable (fun v : S → ℝ => fun i => v (a i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hb : Measurable (fun v : T → ℝ => fun i => v (b i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hg : IndepFun (fun ω i => (G i ω).1) (fun ω i => (G i ω).2) P := by
    simpa [Function.comp_def,U,a,b] using hST.comp ha hb
  have he : ∀ᵐ ω ∂P, ∀ i, F i ω = G i ω := ae_all_iff.2 hFG
  apply hg.congr
  · filter_upwards [he] with ω hw
    funext i
    rw [hw i]
  · filter_upwards [he] with ω hw
    funext i
    rw [hw i]
