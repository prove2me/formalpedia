-- Prove2me | solution 1 for Kyprianou.Ch03.entranceHit_eventualClosureAtPassage
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:11:26.032984+00:00
-- url     : https://prove2.me/submissions/1753e742-2525-47e6-952a-5044866f7e29

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Topology Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

namespace ClosureAux

theorem key (f : NNReal → ℝ) (hf : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (A : Set NNReal) (B : Set ℝ) (hA : ∀ t ∈ A, f t ∈ B) (τ : NNReal)
    (hs : sInf ((fun t : NNReal => (t : WithTop NNReal)) '' A) = (τ : WithTop NNReal)) :
    f τ ∈ closure B := by
  have hne : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    subst h
    rw [Set.image_empty, sInf_empty] at hs
    exact WithTop.top_ne_coe hs
  have hbdd : BddBelow A := ⟨0, fun x _ => zero_le⟩
  have hcoe : sInf ((fun t : NNReal => (t : WithTop NNReal)) '' A) = ((sInf A : NNReal) : WithTop NNReal) :=
    (WithTop.coe_sInf' hne hbdd).symm
  rw [hcoe] at hs
  have hτ : sInf A = τ := WithTop.coe_injective hs
  have hmem : τ ∈ closure A := hτ ▸ csInf_mem_closure hne hbdd
  have hsub : A ⊆ Set.Ici τ := fun x hx => hτ ▸ csInf_le hbdd hx
  have hc : ContinuousWithinAt f A τ := (hf τ).mono hsub
  have h1 := hc.mem_closure_image hmem
  exact closure_mono (by rintro _ ⟨x, hx, rfl⟩; exact hA x hx) h1

end ClosureAux

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (B : Set Real) (hB : IsOpen B ∨ IsClosed B)
    (entranceTime hittingTime : Omega -> NNReal)
    (hEntranceTime : forall omega,
      firstEntranceTime X B omega != ⊤ ->
        firstEntranceTime X B omega = (entranceTime omega : WithTop NNReal))
    (hHittingTime : forall omega,
      firstHittingTime X B omega != ⊤ ->
        firstHittingTime X B omega = (hittingTime omega : WithTop NNReal)) :
    (∀ᵐ omega : Omega ∂ P,
      (firstEntranceTime X B omega != ⊤ ->
        X (entranceTime omega) omega ∈ closure B) ∧
      (firstHittingTime X B omega != ⊤ ->
        X (hittingTime omega) omega ∈ closure B)) := by
  filter_upwards [hX.cadlag_ae] with omega hcad
  have hrc : ∀ t, ContinuousWithinAt (fun s => X s omega) (Set.Ici t) t := fun t => (hcad t).1
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : firstEntranceTime X B omega ≠ ⊤ := by simpa using h
    exact ClosureAux.key (fun s => X s omega) hrc {t : NNReal | X t omega ∈ B} B
      (fun t ht => ht) (entranceTime omega) (hEntranceTime omega h)
  · exact ClosureAux.key (fun s => X s omega) hrc {t : NNReal | 0 < t ∧ X t omega ∈ B} B
      (fun t ht => ht.2) (hittingTime omega) (hHittingTime omega h)
