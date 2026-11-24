-- Prove2me | solution 1 for Kyprianou.Ch03.quasiLeft_stoppedValuesPathwiseLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:29:44.609828+00:00
-- url     : https://prove2.me/submissions/d7dccb61-d65f-48c0-b148-02a42629448d

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
    ∀ᵐ omega : Omega ∂ P.restrict {omega : Omega | T omega ≠ ⊤},
      ∃ l : Real, Tendsto (fun n => X (timeTn n omega) omega) atTop (nhds l) := by
  have hfin : MeasurableSet {omega : Omega | T omega ≠ ⊤} :=
    hT.measurableSet_eq_top.compl
  rw [ae_restrict_iff' hfin]
  filter_upwards [hIncreasing, hLimit, hX.cadlag_ae] with omega hmono hconv hcad
  intro ht
  have hle (n : Nat) : Tn n omega ≤ T omega :=
    hmono.ge_of_tendsto hconv n
  have hf (n : Nat) : Tn n omega ≠ ⊤ := fun h => ht (top_le_iff.mp (h ▸ hle n))
  have ht_eq : T omega = (timeT omega : WithTop NNReal) :=
    hTimeT omega (by simpa using ht)
  have hn_eq (n : Nat) : Tn n omega = (timeTn n omega : WithTop NNReal) :=
    hTimeTn n omega (by simpa using hf n)
  have hco : (fun n => Tn n omega) =
      (fun n => (timeTn n omega : WithTop NNReal)) :=
    funext hn_eq
  have hc : Tendsto (fun n => timeTn n omega) atTop (nhds (timeT omega)) := by
    apply WithTop.isEmbedding_coe.tendsto_nhds_iff.mpr
    change Tendsto (fun n => (timeTn n omega : WithTop NNReal)) atTop
      (nhds (timeT omega : WithTop NNReal))
    rw [← hco, ← ht_eq]
    exact hconv
  by_cases he : ∃ n, Tn n omega = T omega
  · obtain ⟨n, hn⟩ := he
    refine ⟨X (timeT omega) omega, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with k hk
    have heq : Tn k omega = T omega := le_antisymm (hle k) (hn ▸ hmono hk)
    have htime : timeTn k omega = timeT omega := by
      exact WithTop.coe_injective (by rw [← hn_eq k, heq, ht_eq])
    rw [htime]
  · have hlt (n : Nat) : timeTn n omega < timeT omega := by
      have hstrict := lt_of_le_of_ne (hle n) (fun h => he ⟨n, h⟩)
      simpa only [hn_eq n, ht_eq,
        WithTop.coe_lt_coe] using hstrict
    have hw : Tendsto (fun n => timeTn n omega) atTop
        (nhdsWithin (timeT omega) (Set.Iio (timeT omega))) :=
      tendsto_nhdsWithin_iff.mpr ⟨hc, Eventually.of_forall hlt⟩
    obtain ⟨l, hl⟩ := (hcad (timeT omega)).2
    exact ⟨l, hl.comp hw⟩
