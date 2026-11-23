-- Prove2me | solution 1 for Kyprianou.Ch01.autonomousODEUniqueWithCompactPositiveRange
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:37:23.538214+00:00
-- url     : https://prove2.me/submissions/b56a9de6-6ea8-46c1-8c39-5efb50b7f637

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 Set Filter
open scoped Topology NNReal
set_option autoImplicit false

theorem solution
    (v : ℝ → ℝ) (δ B C : ℝ) (hδ : 0 < δ)
    (hδB : δ ≤ B) (hC : 0 ≤ C)
    (hLip : ∀ x ∈ Set.Icc δ B, ∀ y ∈ Set.Icc δ B,
      |v y - v x| ≤ C * |y - x|)
    (f g : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hfCont : ContinuousOn f (Set.Icc 0 T))
    (hgCont : ContinuousOn g (Set.Icc 0 T))
    (hfRange : ∀ t ∈ Set.Icc 0 T, f t ∈ Set.Icc δ B)
    (hgRange : ∀ t ∈ Set.Icc 0 T, g t ∈ Set.Icc δ B)
    (hfDer : ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt f (v (f t)) (Set.Ici t) t)
    (hgDer : ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt g (v (g t)) (Set.Ici t) t)
    (hInit : f 0 = g 0) : f T = g T := by
  let K : ℝ≥0 := ⟨C, hC⟩
  have hv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      LipschitzOnWith K v (Set.Icc δ B) := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
    change |v x - v y| ≤ C * |x - y|
    simpa only [abs_sub_comm] using (hLip x hx y hy)
  have hEq := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => v) (s := fun _ => Set.Icc δ B)
    (K := K) (a := 0) (b := T)
    hv hfCont hfDer
    (fun t ht => hfRange t ⟨ht.1, ht.2.le⟩)
    hgCont hgDer
    (fun t ht => hgRange t ⟨ht.1, ht.2.le⟩) hInit
  exact hEq ⟨hT, le_rfl⟩
