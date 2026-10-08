-- Prove2me | solution 1 for KleywegtSAA.ValueCLT.sqrt_mul_minOnOpt_sub
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:11:11.556985+00:00
-- url     : https://prove2.me/submissions/cf1abd18-4a3d-42ce-bb93-6f9ec7451524

import Mathlib
import Definitions.Def_KleywegtSAA_ValueCLT_Setting

open KleywegtSAA.ValueCLT MeasureTheory ProbabilityTheory Filter Topology

theorem solution
    {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} (G : X → 𝒲 → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℕ → Ω → 𝒲) :
    ∀ (N : ℕ) (ω : Ω),
      Real.sqrt N * (minOnOpt S hS G P W N ω - S.inf' hS (KleywegtSAA.ExpRate.trueObj G P W)) =
        (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W)).inf' (optSet_nonempty S hS (KleywegtSAA.ExpRate.trueObj G P W))
          (fun x => Real.sqrt N * (KleywegtSAA.ExpRate.sampleObj G W N ω x - KleywegtSAA.ExpRate.trueObj G P W x)) := by
  classical
  intro N ω
  let g := KleywegtSAA.ExpRate.trueObj G P W
  let f := KleywegtSAA.ExpRate.sampleObj G W N ω
  let T := optSet S hS g
  have ht : T.Nonempty := optSet_nonempty S hS g
  have hg (x : X) (hx : x ∈ T) : g x = S.inf' hS g := by
    have h := Finset.mem_filter.mp hx
    exact le_antisymm h.2 (Finset.inf'_le g h.1)
  obtain ⟨y, hy, heq⟩ := Finset.exists_mem_eq_inf' ht f
  change Real.sqrt N * (T.inf' ht f - S.inf' hS g) = T.inf' ht (fun x => Real.sqrt N * (f x - g x))
  apply le_antisymm
  · apply Finset.le_inf'
    intro x hx
    rw [hg x hx]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (Finset.inf'_le f hx) _) (Real.sqrt_nonneg _)
  · calc
      T.inf' ht (fun x => Real.sqrt N * (f x - g x)) ≤ Real.sqrt N * (f y - g y) := Finset.inf'_le _ hy
      _ = Real.sqrt N * (T.inf' ht f - S.inf' hS g) := by rw [hg y hy, heq]

#print axioms solution
