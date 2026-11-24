-- Prove2me | solution 1 for Kyprianou.Ch03.quasiLeft_denseShiftOscillationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:56:44.230167+00:00
-- url     : https://prove2.me/submissions/180c6e96-2058-4517-b367-947807572145

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open Kyprianou.Ch03
set_option autoImplicit false

theorem solution
    (f : NNReal → Real) (hf : ProbabilityTheory.IsCadlag f)
    (S : Set NNReal) (hS : Dense S)
    (a delta : NNReal) (eps : Real) (heps : 0 < eps)
    (u : NNReal) (hu : u < delta)
    (hbig : eps ≤ dist (f (a + u)) (f a)) :
    ∃ v ∈ S, v < delta ∧ eps / 2 < |f (a + v) - f a| := by
  classical
  have hrc : ContinuousWithinAt f (Set.Ici (a + u)) (a + u) :=
    (hf (a + u)).1
  obtain ⟨r, hr, hclose⟩ := Metric.continuousWithinAt_iff.mp hrc
    (eps / 2) (by linarith)
  let rr : NNReal := Real.toNNReal r
  have hrr : 0 < rr := Real.toNNReal_pos.mpr hr
  have htop : u < min delta (u + rr) := lt_min hu (lt_add_of_pos_right u hrr)
  obtain ⟨w, hw⟩ := exists_between htop
  have hne : (Set.Ioo u (min delta (u + rr))).Nonempty := ⟨w, hw⟩
  obtain ⟨v, hv, hvS⟩ := hS.inter_open_nonempty _ isOpen_Ioo hne
  have hvd : v < delta := lt_of_lt_of_le hv.2 (min_le_left _ _)
  have hvr : v < u + rr := lt_of_lt_of_le hv.2 (min_le_right _ _)
  have hdist : dist (a + v) (a + u) < r := by
    rw [NNReal.dist_eq, NNReal.coe_add, NNReal.coe_add]
    have hvu : (u : Real) < (v : Real) := by exact_mod_cast hv.1
    have hrv : (v : Real) < (u : Real) + r := by
      have hh : (v : Real) < ((u + rr : NNReal) : Real) := by exact_mod_cast hvr
      simpa [rr, Real.coe_toNNReal r (le_of_lt hr)] using hh
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hc := hclose (x := a + v) (add_le_add_right (le_of_lt hv.1) a) hdist
  have ht := dist_triangle (f (a + u)) (f (a + v)) (f a)
  rw [dist_comm (f (a + u)) (f (a + v))] at ht
  have hresult : eps / 2 < dist (f (a + v)) (f a) := by linarith
  exact ⟨v, hvS, hvd, by simpa only [Real.dist_eq] using hresult⟩
