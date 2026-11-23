-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionStripEvalSigmaJointIndependentV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:34:18.7813+00:00
-- url     : https://prove2.me/submissions/f4a43175-dd19-4ee4-98ad-610109a14b7d

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_ch02PoissonDisjointRegionsIndependentSigma
import Theorems.Thm_Kyprianou_Ch02_iIndepFiniteFromOutsideJoinV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t),
      iIndep (fun (i : Fin n) =>
        (⨆ C ∈ {C : Set (ℝ × ℝ) |
              C ⊆ (Set.Ioc (t i.castSucc : ℝ) (t i.succ : ℝ) ×ˢ B) ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)) P := by
  intro n t ht
  classical
  let R : Fin n → Set (ℝ × ℝ) := fun i =>
    Set.Ioc (t i.castSucc : ℝ) (t i.succ : ℝ) ×ˢ B
  let m : Fin n → MeasurableSpace Ω := fun i =>
    ⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R i ∧ MeasurableSet C},
      MeasurableSpace.comap (fun ω => N.N ω C) inferInstance
  have hRm (i : Fin n) : MeasurableSet (R i) :=
    measurableSet_Ioc.prod hB
  have hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω) := by
    intro i
    dsimp [m]
    exact iSup₂_le fun C hC => (N.measurable_eval hC.2).comap_le
  have hRdisj : ∀ i j : Fin n, i ≠ j → Disjoint (R i) (R j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have hh : i.succ ≤ j.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      exact Set.Disjoint.set_prod_left
        (Set.Ioc_disjoint_Ioc_of_le
          (a := (t i.castSucc : ℝ)) (d := (t j.succ : ℝ)) (ht hh)) B B
    · have hh : j.succ ≤ i.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      exact (Set.Disjoint.set_prod_left
        (Set.Ioc_disjoint_Ioc_of_le
          (a := (t j.castSucc : ℝ)) (d := (t i.succ : ℝ)) (ht hh)) B B).symm
  have hjoin (i : Fin n) (s : Finset (Fin n)) (hi : i ∉ s) :
      Indep (m i) (⨆ j ∈ s, m j) P := by
    let U : Set (ℝ × ℝ) := ⋃ j ∈ s, R j
    have hUm : MeasurableSet U := by
      exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hRm j
    have hIU : Disjoint (R i) U := by
      apply Set.disjoint_left.mpr
      intro z hz hzU
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hzU
      obtain ⟨hjs, hzj⟩ := Set.mem_iUnion.mp hj
      have hij : i ≠ j := fun he => hi (he ▸ hjs)
      exact (Set.disjoint_left.mp (hRdisj i j hij)) hz hzj
    have hInd := (Kyprianou.ch02PoissonDisjointRegionsIndependentSigma
      P ν N) (R i) U (hRm i) hUm hIU
    have hle :
        (⨆ j ∈ s, m j) ≤
        (⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ U ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => N.N ω C) inferInstance) := by
      refine iSup₂_le fun j hj => ?_
      dsimp [m]
      refine iSup₂_le fun C hC => le_iSup₂_of_le C ?_ le_rfl
      refine ⟨hC.1.trans ?_, hC.2⟩
      intro z hz
      exact Set.mem_iUnion.mpr
        ⟨j, Set.mem_iUnion.mpr ⟨hj, hz⟩⟩
    exact indep_of_indep_of_le_right (by simpa only [m] using hInd) hle
  change iIndep m P
  exact Kyprianou.Ch02.iIndepFiniteFromOutsideJoinV1 P n m hm hjoin
