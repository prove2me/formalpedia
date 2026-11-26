-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46PhysicalBusySplitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:36:27.205745+00:00
-- url     : https://prove2.me/submissions/4df3de15-d85b-4f2a-9f86-50b3e8c5b065

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46PrefixCanonicalBusyV1
import Theorems.Thm_Kyprianou_Ch04_exercise46RecoveryRecordPrefixV1
import Theorems.Thm_Kyprianou_Ch04_exercise46BusyRestartAtRecordV1
import Theorems.Thm_Kyprianou_Ch04_exercise46BusySetRestartAssemblyV1
import Theorems.Thm_Kyprianou_Ch04_exercise46BusyCountShiftCardV1
import Theorems.Thm_Kyprianou_Ch04_exercise46RawSupEqualsRunningSupV1
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (hFirst : ∀ᵐ w ∂P, A w = ((A w).untopD 0 : NNReal) ∧
      0 < (A w).untopD 0 ∧
      L.X ((A w).untopD 0) w <
        Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0) ∧
      ∀ u : NNReal, 0 < u → u < (A w).untopD 0 →
        L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u)
    (hPrefix : ∀ᵐ w ∂P,
      (∀ s : NNReal, s < (A w).untopD 0 → L.X s w = (s : Real)) ∧
      (∀ s : NNReal, L.X s w ≤ (s : Real)))
    (Wleft : NNReal → Omega → Real) (hWLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => sSup ((fun u => L.X u w) '' Iic s) - L.X s w)
        (nhdsWithin t (Iio t)) (nhds (Wleft t w)))
    (hNo : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t → A w < (t : WithTop NNReal) →
      Function.leftLim (fun u : NNReal => L.X u w) t =
        (((A w).untopD 0 : NNReal) : Real) →
      ¬ L.X t w < Function.leftLim (fun u : NNReal => L.X u w) t)
    (C : (NNReal → Real) → ENNReal) (hOriginal : ∀ᵐ w ∂P, C (fun t => L.X t w) =
      (({t : NNReal | 0 < t ∧ Wleft t w = 0 ∧
        0 < sSup ((fun u => L.X u w) '' Iic t) - L.X t w}).encard : ENNReal))
    (hShiftCount : ∀ w s, let Y : NNReal → Real := fun t => L.X (s+t) w - L.X s w
      C Y = (({t : NNReal | 0 < t ∧ sSup (Y '' Iic t) = Function.leftLim Y t ∧
        Y t < Function.leftLim Y t}).encard : ENNReal)) :
    let R : Omega → WithTop NNReal := fun w =>
      ⨅ r : NNReal, if A w < (r : WithTop NNReal) ∧
        (((A w).untopD 0 : NNReal) : Real) < L.X r w
        then (r : WithTop NNReal) else ⊤
    ∀ᵐ w ∂P,
      (R w ≠ ⊤ → C (fun t => L.X t w) = 1 +
        C (fun u => L.X ((R w).untopD 0 + u) w - L.X ((R w).untopD 0) w)) ∧
      (R w = ⊤ → C (fun t => L.X t w) = 1) := by
  classical
  dsimp only
  filter_upwards [hFirst,hPrefix,hWLeft,hNo,hOriginal] with w hf hp hl hn hc
  let a : NNReal := (A w).untopD 0
  let f : NNReal → Real := fun t => L.X t w
  let R : WithTop NNReal := ⨅ t : NNReal, if (a : WithTop NNReal) < (t : WithTop NNReal) ∧
    (a : Real) < f t then (t : WithTop NNReal) else ⊤
  let S : Set NNReal := {t | 0 < t ∧ sSup (f '' Iic t) = Function.leftLim f t ∧
    f t < Function.leftLim f t}
  have hS : C f = (S.encard : ENNReal) := by
    rw [hc]
    apply congrArg (fun B : Set NNReal => (B.encard : ENNReal))
    ext t
    by_cases ht : 0 < t
    · letI : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,ht⟩
      have hsup := Kyprianou.Ch04.exercise46RawSupEqualsRunningSupV1 P G L w
      have hh := hl t ht
      simp_rw [hsup] at hh
      have hL := (avram_p2_a_zero_rate_original_cadlag_regular_all_times L w).1 t
      have hC := ((runningSup_continuous_actual L w).continuousAt (x := t)).tendsto
      have he := tendsto_nhds_unique hh ((hC.mono_left nhdsWithin_le_nhds).sub hL)
      simp only [S,f,mem_setOf_eq,ht,true_and,hsup,he,sub_eq_zero,sub_pos]
      exact and_congr_right (fun h => by rw [h])
    · simp [S,ht]
  have hno (t : NNReal) (ht : 0 < t) (hat : a < t)
      (he : Function.leftLim f t = (a : Real)) : ¬ f t < Function.leftLim f t :=
    hn t ht (hf.1.trans_lt (WithTop.coe_lt_coe.mpr hat)) he
  have hUnique := Kyprianou.Ch04.exercise46PrefixCanonicalBusyV1 P G L w a
    hf.2.1 hf.2.2.1 hp.1 hp.2 hf.2.2.2 hno
  have hRec := Kyprianou.Ch04.exercise46RecoveryRecordPrefixV1 P G L w a hp.2
  rw [hf.1]
  change (R ≠ ⊤ → C f = 1 + C (fun u => f (R.untopD 0+u) - f (R.untopD 0))) ∧
    (R = ⊤ → C f = 1)
  constructor
  · intro hfin
    let r : NNReal := R.untopD 0
    have hr : (r : WithTop NNReal) = R :=
      WithTop.coe_untop₀_of_ne_top (by simpa using hfin)
    have har : a ≤ r := WithTop.coe_le_coe.mp (hr ▸ hRec.1)
    have hval : f r = (a : Real) := hRec.2.2 hfin
    have hrecord (t : NNReal) (ht : t ≤ r) : f t ≤ f r := by
      by_cases he : t = r
      · rw [he]
      · rw [hval]
        exact hRec.2.1 t (show (t : WithTop NNReal) < R from hr ▸ WithTop.coe_lt_coe.mpr (lt_of_le_of_ne ht he))
    let Y : NNReal → Real := fun u => f (r+u) - f r
    let T : Set NNReal := {u | 0 < u ∧ sSup (Y '' Iic u) = Function.leftLim Y u ∧
      Y u < Function.leftLim Y u}
    have hpos : ∀ u ∈ T, 0 < u := fun u hu => hu.1
    have hshift (u : NNReal) (hu : 0 < u) : (r+u ∈ S ↔ u ∈ T) := by
      have hb : BddAbove (f '' Iic (r+u)) := by
        use ((r+u : NNReal) : Real)
        rintro x ⟨t,ht,rfl⟩
        exact (hp.2 t).trans (by exact_mod_cast ht)
      exact Kyprianou.Ch04.exercise46BusyRestartAtRecordV1 P G L w r u hu hrecord hb
    have hset := Kyprianou.Ch04.exercise46BusySetRestartAssemblyV1 S T a r
      hUnique.1 har (fun t ht htr => hUnique.2 t ht (show (t : WithTop NNReal) ≤ R from hr ▸ WithTop.coe_le_coe.mpr htr)) hpos hshift
    rw [hS,show C Y = (T.encard : ENNReal) from hShiftCount w r]
    exact Kyprianou.Ch04.exercise46BusyCountShiftCardV1 S T a r har hpos hset
  · intro hi
    have hset : S = {a} := by
      ext t
      exact ⟨fun ht => hUnique.2 t ht (show (t : WithTop NNReal) ≤ R from hi.symm ▸ le_top),
        fun ht => by rw [mem_singleton_iff.mp ht]; exact hUnique.1⟩
    rw [hS,hset]; simp
