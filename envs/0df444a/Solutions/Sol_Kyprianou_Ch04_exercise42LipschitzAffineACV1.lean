-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzAffineACV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:35:54.936022+00:00
-- url     : https://prove2.me/submissions/3fd192ee-ee7e-4469-b189-7f5fe762d0b5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42AffineSecondCoordinateLipschitzV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (U : ℝ → ℝ) (K : ℝ≥0) (hU : LipschitzWith K U)
    (a c l r : ℝ) (hlr : l ≤ r)
    (hpos : ∀ s ∈ Icc l r, 0 ≤ U s) :
    AbsolutelyContinuousOnInterval (fun s : ℝ => f (U s, a + c * s)) l r := by
  let q : ℝ → ℝ × ℝ := fun s => (U s, a + c * s)
  let H : Set (ℝ × ℝ) := Set.prod (Ici (0 : ℝ)) Set.univ
  have hqLip : LipschitzWith (max K ‖c‖₊) q := by
    exact hU.prodMk (Kyprianou.Ch04.exercise42AffineSecondCoordinateLipschitzV1 a c)
  have hcompact : IsCompact (q '' Icc l r) :=
    isCompact_Icc.image hqLip.continuous
  have hconv : Convex ℝ H :=
    (convex_Ici (0 : ℝ)).prod convex_univ
  have hsubset : q '' Icc l r ⊆ H := by
    rintro z ⟨s, hs, rfl⟩
    exact ⟨hpos s hs, mem_univ _⟩
  have hlocal : LocallyLipschitzOn (q '' Icc l r) f :=
    (hf.locallyLipschitzOn hconv).mono hsubset
  obtain ⟨C, hCf⟩ :=
    hlocal.exists_lipschitzOnWith_of_compact hcompact
  have hqOn : LipschitzOnWith (max K ‖c‖₊) q (Icc l r) :=
    fun _ _ _ _ => hqLip _ _
  have hcomp : LipschitzOnWith (C * max K ‖c‖₊)
      (f ∘ q) (Icc l r) :=
    hCf.comp hqOn (fun s hs => mem_image_of_mem q hs)
  have hcomp' : LipschitzOnWith (C * max K ‖c‖₊)
      (f ∘ q) (uIcc l r) := by
    simpa only [uIcc_of_le hlr] using hcomp
  simpa only [q, Function.comp_def] using hcomp'.absolutelyContinuousOnInterval


