-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42GridCoefficientAELimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T16:04:55.642715+00:00
-- url     : https://prove2.me/submissions/2de7ab8e-7d05-40b4-a397-52dbec98b684

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_cadlagNNRealDiscontinuitiesCountableV1
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hd : 0 < c) (hzero : X 0 omega = 0)
    (hCadlag : IsCadlag (fun t : NNReal => X t omega))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hNeg : ∀ t : NNReal, 0 < t → X t omega ≤ Xleft t omega)
    (hRep : ∀ t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (U : NNReal → Real) (K : NNReal) (hU : LipschitzWith K U)
    (hU0 : 0 ≤ U 0) (hUp : ∀ s : NNReal, 0 < s → 0 < U s)
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f (Set.prod (Set.Ici (0 : Real)) Set.univ))

    (t : NNReal) (ht : 0 < t) :
    let T : ℝ := t
    ∀ᵐ s ∂(volume.restrict (Icc 0 T)),
      Tendsto (fun n : ℕ => (fun s : NNReal => fderiv ℝ f (U s, X s omega) (1, 0)) (T * (⌊(s / T) * ((n : ℝ) + 2)⌋₊ : ℝ) / ((n : ℝ) + 2)).toNNReal) atTop (nhds ((fun s : NNReal => fderiv ℝ f (U s, X s omega) (1, 0)) s.toNNReal)) := by
  classical
  intro T
  have hT : 0 < T := ht
  let g : NNReal → ℝ := fun s => fderiv ℝ f (U s, X s omega) (1, 0)
  let q : ℕ → ℕ → ℝ := fun n i => T * (i : ℝ) / ((n : ℝ) + 2)
  let j : ℕ → ℝ → ℕ := fun n s => ⌊(s / T) * ((n : ℝ) + 2)⌋₊
  let H : Set (ℝ × ℝ) := Set.prod (Ici (0 : ℝ)) univ
  have hUnique : UniqueDiffOn ℝ H := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hcont := hf.continuousOn_fderivWithin hUnique le_rfl
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hDisc := Kyprianou.Ch02.cadlagNNRealDiscontinuitiesCountableV1
    (fun s => X s omega) (fun s => (hCadlag s).1)
    (fun s hs => ⟨Xleft s omega, hLeft s hs⟩)
  let Bad : Set ℝ := (fun s : NNReal => (s : ℝ)) ''
    {s : NNReal | ¬ ContinuousAt (fun v => X v omega) s} ∪ {0}
  have hBad : Bad.Countable := (hDisc.image _).union (Set.countable_singleton 0)
  have hBadNull : μ Bad = 0 := hBad.measure_zero μ
  have hgood : ∀ᵐ s ∂μ, s ∉ Bad := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using hBadNull
  change ∀ᵐ s ∂μ, Tendsto (fun n => g (q n (j n s)).toNNReal)
    atTop (nhds (g s.toNNReal))
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc, hgood] with s hs hb
  have hs0 : s ≠ 0 := fun he => hb (Or.inr he)
  have hsp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  have hsP : 0 < s.toNNReal := Real.toNNReal_pos.mpr hsp
  have hx : ContinuousAt (fun v : NNReal => X v omega) s.toNNReal := by
    by_contra hn
    exact hb (Or.inl ⟨s.toNNReal, hn, Real.coe_toNNReal _ hs.1⟩)
  have hq := (AvramDividend.Classical.avram_bvb_b21_original_uniform_floor_samples_converge_from_left
    T s hT hs.1).2
  have hnn : Tendsto (fun n => (q n (j n s)).toNNReal) atTop (nhds s.toNNReal) :=
    (Real.lipschitzWith_toNNReal.continuous.continuousAt :
      ContinuousAt Real.toNNReal s).tendsto.comp hq
  have hp : Tendsto (fun n => (U (q n (j n s)).toNNReal,
      X (q n (j n s)).toNNReal omega)) atTop (nhds (U s.toNNReal, X s.toNNReal omega)) :=
    (hU.continuous.continuousAt.tendsto.comp hnn).prodMk_nhds (hx.tendsto.comp hnn)
  have hop : Set.prod (Ioi (0 : ℝ)) (univ : Set ℝ) ∈
      nhds (U s.toNNReal, X s.toNNReal omega) :=
    (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hUp _ hsP, mem_univ _⟩
  have hnH : H ∈ nhds (U s.toNNReal, X s.toNNReal omega) :=
    Filter.mem_of_superset hop (fun z hz => ⟨le_of_lt (show 0 < z.1 from hz.1), hz.2⟩)
  have hc : ContinuousAt (fderivWithin ℝ f H) (U s.toNNReal, X s.toNNReal omega) :=
    (hcont _ (show (U s.toNNReal, X s.toNNReal omega) ∈ H from ⟨(hUp _ hsP).le, mem_univ _⟩)).continuousAt hnH
  have heq (z : ℝ × ℝ) (hz : z ∈ Set.prod (Ioi (0 : ℝ)) (univ : Set ℝ)) :
      fderivWithin ℝ f H z = fderiv ℝ f z :=
    fderivWithin_of_mem_nhds (Filter.mem_of_superset
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds hz) (fun w hw => ⟨le_of_lt (show 0 < w.1 from hw.1), hw.2⟩))
  have hder : Tendsto (fun n => fderiv ℝ f (U (q n (j n s)).toNNReal,
      X (q n (j n s)).toNNReal omega)) atTop
      (nhds (fderiv ℝ f (U s.toNNReal, X s.toNNReal omega))) := by
    have hh := hc.tendsto.comp hp
    rw [heq (U s.toNNReal, X s.toNNReal omega) ⟨hUp _ hsP, mem_univ _⟩] at hh
    apply hh.congr'
    filter_upwards [hp.eventually hop] with n hn
    exact heq _ hn
  exact (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).continuous.continuousAt.tendsto.comp hder
