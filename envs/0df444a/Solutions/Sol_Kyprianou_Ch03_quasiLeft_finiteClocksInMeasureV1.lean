-- Prove2me | solution 1 for Kyprianou.Ch03.quasiLeft_finiteClocksInMeasureV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:44:04.061806+00:00
-- url     : https://prove2.me/submissions/4ef2eb68-6ea4-4de4-99cc-852c16e82b59

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

open scoped Topology

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : Omega -> WithTop NNReal)
    (Tn : Nat -> Omega -> WithTop NNReal)
    (timeT : Omega -> NNReal) (timeTn : Nat -> Omega -> NNReal)
    (hTimeT : forall omega, T omega != ⊤ ->
      T omega = (timeT omega : WithTop NNReal))
    (hTimeTn : forall n omega, Tn n omega != ⊤ ->
      Tn n omega = (timeTn n omega : WithTop NNReal))
    (hT : IsStoppingTime F T)
    (hTn : forall n, IsStoppingTime F (Tn n))
    (hIncreasing : ∀ᵐ omega : Omega ∂ P,
      Monotone (fun n => Tn n omega))
    (hLimit : ∀ᵐ omega : Omega ∂ P,
      Tendsto (fun n => Tn n omega) atTop (nhds (T omega))) :
    (∀ᵐ omega : Omega ∂ P.restrict {omega : Omega | T omega ≠ ⊤},
      ∀ n, Tn n omega ≠ ⊤ ∧ timeTn n omega ≤ timeT omega) ∧
    TendstoInMeasure (P.restrict {omega : Omega | T omega ≠ ⊤})
      timeTn atTop timeT := by
  let Q := P.restrict {omega : Omega | T omega ≠ ⊤}
  have hfin : MeasurableSet {omega : Omega | T omega ≠ ⊤} :=
    hT.measurableSet_eq_top.compl
  have hgood : ∀ᵐ omega ∂Q,
      (∀ n, Tn n omega ≠ ⊤ ∧ timeTn n omega ≤ timeT omega) ∧
      Tendsto (fun n => timeTn n omega) atTop (nhds (timeT omega)) := by
    dsimp [Q]
    rw [ae_restrict_iff' hfin]
    filter_upwards [hIncreasing, hLimit] with omega hm hc
    intro ht
    have hle (n : Nat) := hm.ge_of_tendsto hc n
    have hf (n : Nat) : Tn n omega ≠ ⊤ :=
      fun h => ht (top_le_iff.mp (h ▸ hle n))
    have ht_eq := hTimeT omega (by simpa using ht)
    have hn_eq (n : Nat) := hTimeTn n omega (by simpa using hf n)
    refine ⟨fun n => ⟨hf n, ?_⟩, ?_⟩
    · simpa only [hn_eq n, ht_eq, WithTop.coe_le_coe] using hle n
    · apply WithTop.isEmbedding_coe.tendsto_nhds_iff.mpr
      change Tendsto (fun n => (timeTn n omega : WithTop NNReal)) atTop
        (nhds (timeT omega : WithTop NNReal))
      rw [← funext hn_eq, ← ht_eq]
      exact hc
  have hf : ∀ n, AEStronglyMeasurable (timeTn n) Q := by
    intro n
    have hm : Measurable (fun omega => (Tn n omega).untopD (0 : NNReal)) :=
      (hTn n).measurable'.untopD _
    apply hm.aestronglyMeasurable.congr
    filter_upwards [hgood] with omega h
    rw [hTimeTn n omega (by simpa using (h.1 n).1)]
    exact WithTop.untopD_coe _ _
  have hclock : TendstoInMeasure Q timeTn atTop timeT :=
    tendstoInMeasure_of_tendsto_ae hf (hgood.mono fun _ h => h.2)
  exact ⟨hgood.mono fun _ h => h.1, hclock⟩
