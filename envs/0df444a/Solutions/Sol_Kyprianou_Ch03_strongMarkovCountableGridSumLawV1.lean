-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovCountableGridSumLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:08:21.233805+00:00
-- url     : https://prove2.me/submissions/33712f85-9884-4799-a557-49965281389c

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (X : NNReal → Omega → Real) (hMeas : ∀ t, Measurable (X t))
    (hDet : ∀ (s : NNReal) (B : Set Omega), MeasurableSet[F s] B →
      Measure.map (fun w u => X (s + u) w - X s w) (P.restrict B) =
        P B • Measure.map (fun w u => X u w) P)
    (T : Omega → NNReal) (hCount : Countable (Set.range T))
    (hFib : ∀ s, MeasurableSet[F s]
      ({w : Omega | tau w ≠ ⊤} ∩ {w | T w = s}))
    (hAbove : ∀ w, tau w ≠ ⊤ → finiteTime w ≤ T w)
    (hZ : Measurable (fun w : Omega => fun u : NNReal => X (T w + u) w - X (T w) w)) :
    ∀ B : Set Omega, (∀ s : NNReal, MeasurableSet[F s]
      (B ∩ {w : Omega | tau w ≤ (s : WithTop NNReal)})) →
      Measure.map (fun w => fun u : NNReal => X (T w + u) w - X (T w) w)
        (P.restrict (B ∩ {w : Omega | tau w ≠ ⊤})) =
      P (B ∩ {w : Omega | tau w ≠ ⊤}) • Measure.map (fun w u => X u w) P := by
  classical
  let I := Set.range T
  letI : Countable I := hCount
  let D : Set Omega := {w | tau w ≠ ⊤}
  let A (s : I) : Set Omega := D ∩ {w | T w = (s : NNReal)}
  let Y (s : NNReal) (w : Omega) (u : NNReal) := X (s + u) w - X s w
  let Z (w : Omega) := Y (T w) w
  have hY (s : NNReal) : Measurable (Y s) :=
    measurable_pi_lambda _ (fun u => (hMeas (s + u)).sub (hMeas s))
  intro B hB
  let E (s : I) := B ∩ A s
  have hEs (s : I) : MeasurableSet[F s] (E s) := by
    have heq : E s = (B ∩ {w | tau w ≤ (s : WithTop NNReal)}) ∩ A s := by
      ext w
      constructor
      · rintro ⟨hb, hd, hs⟩
        refine ⟨⟨hb, ?_⟩, hd, hs⟩
        change tau w ≤ ((s : NNReal) : WithTop NNReal)
        change T w = (s : NNReal) at hs
        rw [hFiniteTime w hd]
        exact_mod_cast (hs ▸ hAbove w hd)
      · rintro ⟨⟨hb, _⟩, ha⟩
        exact ⟨hb, ha⟩
    rw [heq]
    exact (hB s).inter (hFib s)
  have hEm (s : I) : MeasurableSet (E s) := F.le s (E s) (hEs s)
  have hEU : (⋃ s : I, E s) = B ∩ D := by
    ext w
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨s, hb, hd, hs⟩
      exact ⟨hb, hd⟩
    · rintro ⟨hb, hd⟩
      exact ⟨⟨T w, ⟨w, rfl⟩⟩, hb, hd, rfl⟩
  have hdis : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro w hi hj
    exact hij (Subtype.ext (hi.2.2.symm.trans hj.2.2))
  ext C hC
  rw [Measure.map_apply hZ hC, Measure.restrict_apply (hZ hC), Measure.smul_apply]
  rw [← hEU, measure_iUnion hdis hEm]
  have hU : Z ⁻¹' C ∩ (⋃ s : I, E s) = ⋃ s : I, (Z ⁻¹' C ∩ E s) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    exact ⟨fun ⟨hz, s, hs⟩ => ⟨s, hz, hs⟩, fun ⟨s, hz, hs⟩ => ⟨hz, s, hs⟩⟩
  rw [hU, measure_iUnion]
  · have hcell (s : I) : P (Z ⁻¹' C ∩ E s) =
        P (E s) * Measure.map (fun w u => X u w) P C := by
      have heq : Z ⁻¹' C ∩ E s = Y s ⁻¹' C ∩ E s := by
        ext w
        constructor
        · rintro ⟨hz, he⟩
          have ht : T w = (s : NNReal) := he.2.2
          exact ⟨by simpa [Z, ht] using hz, he⟩
        · rintro ⟨hy, he⟩
          have ht : T w = (s : NNReal) := he.2.2
          exact ⟨by simpa [Z, ht] using hy, he⟩
      rw [heq, ← Measure.restrict_apply (hY s hC), ← Measure.map_apply (hY s) hC]
      rw [hDet s (E s) (hEs s), Measure.smul_apply]
      rfl
    simp_rw [hcell]
    exact ENNReal.tsum_mul_right
  · intro i j hij
    exact (hdis hij).mono Set.inter_subset_right Set.inter_subset_right
  · intro s
    exact (hZ hC).inter (hEm s)
