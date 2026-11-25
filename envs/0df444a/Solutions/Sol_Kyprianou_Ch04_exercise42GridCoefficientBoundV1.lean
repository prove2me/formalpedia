-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42GridCoefficientBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T11:34:32.249408+00:00
-- url     : https://prove2.me/submissions/38a7ec51-d43c-4b98-bfc0-2bb48b41846c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathCompactBoundV1
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

    (t : NNReal) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : NNReal, s ≤ t → ‖(fun s : NNReal => fderiv ℝ f (U s, X s omega) (1, 0)) s‖ ≤ C := by
  classical
  let T : ℝ := t
  let g : NNReal → ℝ := fun s => fderiv ℝ f (U s, X s omega) (1, 0)
  have hB := Kyprianou.Ch04.bvTruncatedPathCompactBoundV1 X Xleft omega c hRep hLeft t
  let M : ℝ := |X 0 omega| + |c| * T +
    ∑' s : Set.Ioc (0 : NNReal) t, |X s omega - Xleft s omega|
  have hXbd (s : NNReal) (hs : s ≤ t) : |X s omega| ≤ M := hB.2.2.1 s hs
  let B : ℝ := |U 0| + (K : ℝ) * T
  have hUbd (s : NNReal) (hs : s ≤ t) : U s ∈ Icc (0 : ℝ) B := by
    have hn : 0 ≤ U s := by
      rcases eq_or_lt_of_le (show 0 ≤ s from zero_le) with h | h
      · simpa [← h] using hU0
      · exact (hUp s h).le
    have h := hU.dist_le_mul s 0
    change |U s - U 0| ≤ (K : ℝ) * |(s : ℝ) - 0| at h
    rw [sub_zero, abs_of_nonneg s.coe_nonneg] at h
    have h' := mul_le_mul_of_nonneg_left (show (s : ℝ) ≤ T from hs) K.coe_nonneg
    have h0 := le_abs_self (U 0)
    have h1 := le_abs_self (U s - U 0)
    exact ⟨hn, by dsimp [B]; linarith⟩
  let H : Set (ℝ × ℝ) := Set.prod (Ici (0 : ℝ)) univ
  let Cmp : Set (ℝ × ℝ) := Set.prod (Icc (0 : ℝ) B) (Icc (-M) M)
  have hsub : Cmp ⊆ H := fun z hz => ⟨hz.1.1, mem_univ _⟩
  have hUnique : UniqueDiffOn ℝ H := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hcont := hf.continuousOn_fderivWithin hUnique le_rfl
  have hcompact : IsCompact Cmp := isCompact_Icc.prod isCompact_Icc
  obtain ⟨A, hA⟩ := hcompact.bddAbove_image (hcont.norm.mono hsub)
  let C : ℝ := max A 0
  have hC : 0 ≤ C := le_max_right _ _
  have hgbd (s : NNReal) (hs : s ≤ t) : ‖g s‖ ≤ C := by
    have hz : (U s, X s omega) ∈ Cmp := ⟨hUbd s hs, abs_le.mp (hXbd s hs)⟩
    have hd' : ‖fderivWithin ℝ f H (U s, X s omega)‖ ≤ C :=
      (hA (mem_image_of_mem _ hz)).trans (le_max_left _ _)
    by_cases hh : DifferentiableAt ℝ f (U s, X s omega)
    · dsimp [g]
      rw [← fderivWithin_eq_fderiv (hUnique _ (hsub hz)) hh]
      calc
        _ ≤ ‖fderivWithin ℝ f H (U s, X s omega)‖ * ‖((1, 0) : ℝ × ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ C := by simpa [Prod.norm_def] using hd'
    · simp [g, fderiv_zero_of_not_differentiableAt hh, hC]
  exact ⟨C, hC, hgbd⟩
