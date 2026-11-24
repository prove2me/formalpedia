-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovCountableGridMeasV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:08:10.710161+00:00
-- url     : https://prove2.me/submissions/1c224d0b-0087-4a7e-a294-8a8f75c05896

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (X : NNReal → Omega → Real) (hMeas : ∀ t, Measurable (X t))
    (T : Omega → NNReal) (hCount : Countable (Set.range T))
    (hFib : ∀ s, MeasurableSet[F s]
      ({w : Omega | tau w ≠ ⊤} ∩ {w | T w = s}))
    (hZero : ∀ w, tau w = ⊤ → T w = 0) :
    Measurable (fun w : Omega => fun u : NNReal => X (T w + u) w - X (T w) w) := by
  classical
  let I := Set.range T
  letI : Countable I := hCount
  let D : Set Omega := {w | tau w ≠ ⊤}
  let A (s : I) : Set Omega := D ∩ {w | T w = (s : NNReal)}
  let Y (s : NNReal) (w : Omega) (u : NNReal) := X (s + u) w - X s w
  let Z (w : Omega) := Y (T w) w
  have hD : MeasurableSet D := hTau.measurableSet_eq_top.compl
  have hA (s : I) : MeasurableSet (A s) := F.le s (A s) (hFib s)
  have hY (s : NNReal) : Measurable (Y s) :=
    measurable_pi_lambda _ (fun u => (hMeas (s + u)).sub (hMeas s))
  have hZ : Measurable Z := by
    intro C hC
    have heq : Z ⁻¹' C =
        (Dᶜ ∩ Y 0 ⁻¹' C) ∪ ⋃ s : I, A s ∩ Y s ⁻¹' C := by
      ext w
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion,
        Set.mem_compl_iff]
      constructor
      · intro hw
        by_cases hf : w ∈ D
        · exact Or.inr ⟨⟨T w, ⟨w, rfl⟩⟩, ⟨hf, rfl⟩, hw⟩
        · exact Or.inl ⟨hf, by simpa [Z, hZero w (by simpa [D] using hf)] using hw⟩
      · rintro (⟨hf, hw⟩ | ⟨s, hs, hw⟩)
        · simpa [Z, hZero w (by simpa [D] using hf)] using hw
        · change w ∈ D ∧ T w = (s : NNReal) at hs
          simpa [Z, hs.2] using hw
    rw [heq]
    exact (hD.compl.inter (hY 0 hC)).union
      (MeasurableSet.iUnion (fun s => (hA s).inter (hY s hC)))
  exact hZ
