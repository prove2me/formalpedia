-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RecoveryKernelFiniteEventV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:27:30.236082+00:00
-- url     : https://prove2.me/submissions/af04294d-865f-44e0-90c6-dff6593294d9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
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
    (K : Real × (NNReal → Real) → WithTop NNReal)
    (hKshift : ∀ (w : Omega) (s : NNReal) (x : Real),
      K (x,fun u => L.X (s+u) w - L.X s w) =
        ⨅ u : NNReal, if x < L.X (s+u) w - L.X s w
          then (u : WithTop NNReal) else ⊤) :
    let R : Omega → WithTop NNReal := fun w =>
      ⨅ r : NNReal, if A w < (r : WithTop NNReal) ∧
        (((A w).untopD 0 : NNReal) : Real) < L.X r w
        then (r : WithTop NNReal) else ⊤
    let a : Omega → NNReal := fun w => (A w).untopD 0
    let J : Omega → Real := fun w => -(L.X (a w) w -
      Function.leftLim (fun u : NNReal => L.X u w) (a w))
    let Z : Omega → (NNReal → Real) := fun w u => L.X (a w+u) w - L.X (a w) w
    ∀ᵐ w ∂P, R w = ⊤ ↔ K (J w,Z w) = ⊤ := by
  classical
  dsimp only
  let a : Omega → NNReal := fun w => (A w).untopD 0
  let R : Omega → WithTop NNReal := fun w =>
    ⨅ r : NNReal, if A w < (r : WithTop NNReal) ∧ (a w : Real) < L.X r w
      then (r : WithTop NNReal) else ⊤
  let J : Omega → Real := fun w => -(L.X (a w) w -
    Function.leftLim (fun u : NNReal => L.X u w) (a w))
  let Z : Omega → (NNReal → Real) := fun w u => L.X (a w+u) w - L.X (a w) w
  have hJP : ∀ᵐ w ∂P, 0 < J w :=
    hFirst.mono fun w hw => neg_pos.mpr (sub_neg.mpr hw.2.2.1)
  have hEq : ∀ᵐ w ∂P, R w = ⊤ ↔ K (J w,Z w) = ⊤ := by
    filter_upwards [hFirst,hPrefix,hJP] with w hw hp hj
    letI : (nhdsWithin (a w) (Iio (a w))).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0,hw.2.1⟩
    have he : (fun u : NNReal => L.X u w) =ᶠ[nhdsWithin (a w) (Iio (a w))]
        (fun u => (u : Real)) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact hp.1 u hu
    have hl := tendsto_nhds_unique
      ((avram_p2_a_zero_rate_original_cadlag_regular_all_times L w).1 (a w))
      ((NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
    have hl' : Function.leftLim (fun u : NNReal => L.X u w) (a w) = (a w : Real) := by
      exact hl
    have hXA : L.X (a w) w = (a w : Real) - J w := by
      dsimp [J]
      linarith
    change R w = ⊤ ↔ K (J w,fun u => L.X (a w+u) w - L.X (a w) w) = ⊤
    rw [hKshift]
    change (⨅ r : NNReal, if A w < (r : WithTop NNReal) ∧
      (a w : Real) < L.X r w then (r : WithTop NNReal) else ⊤) = ⊤ ↔ _
    simp only [iInf_eq_top]
    constructor
    · intro h u
      by_cases hu : J w < L.X (a w+u) w - L.X (a w) w
      · have hup : 0 < u := by
          by_contra hn
          have hz : u = 0 := le_antisymm (le_of_not_gt hn) zero_le
          simp [hz] at hu
          exact (not_lt_of_ge hj.le) hu
        have hg : A w < ((a w+u : NNReal) : WithTop NNReal) ∧
            (a w : Real) < L.X (a w+u) w := by
          refine ⟨?_,by linarith⟩
          rw [hw.1]
          exact WithTop.coe_lt_coe.mpr (lt_add_of_pos_right _ hup)
        exact False.elim (WithTop.coe_ne_top (by simpa only [if_pos hg] using h (a w+u)))
      · rw [if_neg hu]
    · intro h r
      by_cases hr : A w < (r : WithTop NNReal) ∧ (a w : Real) < L.X r w
      · have har : a w < r := WithTop.coe_lt_coe.mp (hw.1 ▸ hr.1)
        have heq : a w + (r-a w) = r := add_tsub_cancel_of_le har.le
        have hg : J w < L.X (a w+(r-a w)) w - L.X (a w) w := by
          rw [heq]
          linarith [hr.2]
        exact False.elim (WithTop.coe_ne_top (by simpa only [if_pos hg] using h (r-a w)))
      · rw [if_neg hr]
  exact hEq
