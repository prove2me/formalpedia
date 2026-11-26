-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46PrefixCanonicalBusyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:36:21.969823+00:00
-- url     : https://prove2.me/submissions/7f0d19ba-710b-4040-839b-9bb23ccde68a

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46RecoveryRecordPrefixV1
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (w : Omega) (a : NNReal) (ha : 0 < a)
    (hJump : L.X a w < Function.leftLim (fun u : NNReal => L.X u w) a)
    (hPrefix : ∀ s : NNReal, s < a → L.X s w = (s : Real))
    (hBound : ∀ s : NNReal, L.X s w ≤ (s : Real))
    (hBefore : ∀ u : NNReal, 0 < u → u < a →
      L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u)
    (hNo : ∀ t : NNReal, 0 < t → a < t →
      Function.leftLim (fun u : NNReal => L.X u w) t = (a : Real) →
      ¬ L.X t w < Function.leftLim (fun u : NNReal => L.X u w) t) :
    let S : Set NNReal := {t | 0 < t ∧ sSup ((fun u => L.X u w) '' Iic t) =
      Function.leftLim (fun u : NNReal => L.X u w) t ∧
      L.X t w < Function.leftLim (fun u : NNReal => L.X u w) t}
    let R : WithTop NNReal := ⨅ t : NNReal, if (a : WithTop NNReal) < (t : WithTop NNReal) ∧
      (a : Real) < L.X t w then (t : WithTop NNReal) else ⊤
    a ∈ S ∧ (∀ t ∈ S, (t : WithTop NNReal) ≤ R → t = a) := by
  classical
  dsimp only
  let f : NNReal → Real := fun t => L.X t w
  let R : WithTop NNReal := ⨅ t : NNReal, if (a : WithTop NNReal) < (t : WithTop NNReal) ∧
    (a : Real) < L.X t w then (t : WithTop NNReal) else ⊤
  have hRec := Kyprianou.Ch04.exercise46RecoveryRecordPrefixV1 P G L w a hBound
  have hb (t : NNReal) : BddAbove (f '' Iic t) := by
    use (t : Real)
    rintro x ⟨u,hu,rfl⟩
    exact (hBound u).trans (by exact_mod_cast hu)
  letI : (nhdsWithin a (Iio a)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,ha⟩
  have he : f =ᶠ[nhdsWithin a (Iio a)] (fun u => (u : Real)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hPrefix u hu
  have hl : Function.leftLim f a = (a : Real) :=
    tendsto_nhds_unique ((avram_p2_a_zero_rate_original_cadlag_regular_all_times L w).1 a)
      ((NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
  have hsupLower (t : NNReal) (hat : a ≤ t) : (a : Real) ≤ sSup (f '' Iic t) := by
    have hlim := (avram_p2_a_zero_rate_original_cadlag_regular_all_times L w).1 a
    rw [hl] at hlim
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact le_csSup (hb t) ⟨u,hu.le.trans hat,rfl⟩
  constructor
  · refine ⟨ha,?_,hJump⟩
    rw [hl]
    apply le_antisymm _ (hsupLower a le_rfl)
    apply csSup_le (show (f '' Iic a).Nonempty from ⟨f a,a,mem_Iic.mpr le_rfl,rfl⟩)
    rintro x ⟨u,hu,rfl⟩
    exact (hBound u).trans (by exact_mod_cast hu)
  · intro t ht htr
    by_contra hne
    have hat : a < t := by
      by_contra hn
      have hlt : t < a := lt_of_le_of_ne (le_of_not_gt hn) hne
      exact (ne_of_lt ht.2.2) (hBefore t ht.1 hlt)
    have hupper (u : NNReal) (hu : u ≤ t) : f u ≤ (a : Real) := by
      by_cases hh : (u : WithTop NNReal) < R
      · exact hRec.2.1 u hh
      · have eq : (u : WithTop NNReal) = R :=
          le_antisymm ((WithTop.coe_le_coe.mpr hu).trans htr) (le_of_not_gt hh)
        have hf : R ≠ ⊤ := eq.symm.trans_ne WithTop.coe_ne_top
        have hval : f (R.untopD 0) = (a : Real) := hRec.2.2 hf
        rw [← eq,WithTop.untopD_coe] at hval
        exact hval.le
    have hs : sSup (f '' Iic t) = (a : Real) := by
      apply le_antisymm _ (hsupLower t hat.le)
      apply csSup_le (show (f '' Iic t).Nonempty from ⟨f t,t,mem_Iic.mpr le_rfl,rfl⟩)
      rintro x ⟨u,hu,rfl⟩
      exact hupper u hu
    exact hNo t ht.1 hat (ht.2.1.symm.trans hs) ht.2.2
