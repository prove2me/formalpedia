-- Prove2me | solution 1 for Kyprianou.Ch03.supInfFiniteVectorPairTransferV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T11:47:33.372336+00:00
-- url     : https://prove2.me/submissions/f5180451-7a2b-4547-8e3c-d68e3065c042

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (m : ℕ) (V : Omega → Fin (m + 1) → Real)
    (hV : AEMeasurable V P) (hV0 : ∀ ω, V ω 0 = 0)
    (hLaw : P.map V = P.map (fun ω : Omega => fun i =>
      V ω (Fin.last m) - V ω i.rev)) :
    P.map (fun ω : Omega =>
      let a := sSup (Set.range (V ω))
      (a, a - V ω (Fin.last m))) =
    P.map (fun ω : Omega =>
      let b := sInf (Set.range (V ω))
      (V ω (Fin.last m) - b, -b)) := by
  let R (v : Fin (m + 1) → ℝ) (i : Fin (m + 1)) := v (Fin.last m) - v i.rev
  let H (v : Fin (m + 1) → ℝ) :=
    (sSup (Set.range v), sSup (Set.range v) - v (Fin.last m))
  have hmR : Measurable R := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (Fin.last m)).sub (measurable_pi_apply i.rev)
  have hmS : Measurable (fun v : Fin (m + 1) → ℝ => sSup (Set.range v)) :=
    Measurable.iSup fun i => measurable_pi_apply i
  have hmH : Measurable H :=
    hmS.prodMk (hmS.sub (measurable_pi_apply (Fin.last m)))
  have h := congrArg (Measure.map H) hLaw
  change Measure.map H (P.map V) = Measure.map H (P.map (R ∘ V)) at h
  rw [AEMeasurable.map_map_of_aemeasurable hmH.aemeasurable hV,
    AEMeasurable.map_map_of_aemeasurable hmH.aemeasurable (hmR.comp_aemeasurable hV)] at h
  have key (v : Fin (m + 1) → ℝ) :
      sSup (Set.range (R v)) = v (Fin.last m) - sInf (Set.range v) := by
    have hA := (Set.finite_range v).bddBelow
    have hB := (Set.finite_range (R v)).bddAbove
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨i, rfl⟩
      have hi := csInf_le hA (Set.mem_range_self i.rev)
      dsimp [R]
      linarith
    · have hh : v (Fin.last m) - sSup (Set.range (R v)) ≤ sInf (Set.range v) := by
        apply le_csInf (Set.range_nonempty _)
        rintro _ ⟨i, rfl⟩
        have hi := le_csSup hB (Set.mem_range_self i.rev)
        dsimp [R] at hi
        rw [Fin.rev_involutive i] at hi
        linarith
      linarith
  have e : H ∘ (R ∘ V) = (fun ω : Omega =>
      (V ω (Fin.last m) - sInf (Set.range (V ω)), -sInf (Set.range (V ω)))) := by
    funext ω
    have hz : (Fin.last m).rev = 0 := by
      apply Fin.ext
      simp [Fin.rev]
    dsimp [Function.comp_def, H]
    rw [key]
    congr 1
    simp [R, hz, hV0 ω]
  rw [e] at h
  exact h
