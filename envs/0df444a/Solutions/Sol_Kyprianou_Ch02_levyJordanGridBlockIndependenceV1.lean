-- Prove2me | solution 1 for Kyprianou.Ch02.levyJordanGridBlockIndependenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:51:31.853808+00:00
-- url     : https://prove2.me/submissions/e8eb5ed3-b297-4621-a8e3-5359eb4c6bdf

import Theorems.Thm_Kyprianou_Ch02_equalGridRefinementExistsV1
import Theorems.Thm_Kyprianou_Ch02_iIndepFunRectangularBlockSumsV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    let G : ℕ → ℝ≥0 → ℝ≥0 → Ω → ℝ × ℝ := fun n a b ω =>
      let g (k : ℕ) := a + (b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
      let d (k : ℕ) := X (g (k+1)) ω - X (g k) ω
      (∑ k : Fin (n+1), max (d k) 0, ∑ k : Fin (n+1), max (-d k) 0)
    ∀ (n m : ℕ) (t : Fin (m+1) → ℝ≥0), Monotone t →
      iIndepFun (fun i : Fin m => G n (t i.castSucc) (t i.succ)) P := by
  dsimp only
  intro n m t ht
  obtain ⟨v,hv,he⟩ := Kyprianou.Ch02.equalGridRefinementExistsV1 n m t ht
  let D (p : Fin m × Fin (n+1)) :=
    increment X (v (finProdFinEquiv p).castSucc) (v (finProdFinEquiv p).succ)
  have hi : iIndepFun D P :=
    (hX.indep_increments _ v hv).precomp finProdFinEquiv.injective
  have hmX := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  have hm (p : Fin m × Fin (n+1)) : AEMeasurable (D p) P :=
    (hmX _).sub (hmX _)
  have hb := Kyprianou.Ch02.iIndepFunRectangularBlockSumsV1 P m (n+1) D hm hi
  have hD (i : Fin m) (j : Fin (n+1)) (ω : Ω) :
      D (i,j) ω = X (t i.castSucc+(t i.succ-t i.castSucc)*
        ((j.val+1 : ℕ):ℝ≥0)/((n+1 : ℕ):ℝ≥0)) ω -
      X (t i.castSucc+(t i.succ-t i.castSucc)*
        (j.val:ℝ≥0)/((n+1 : ℕ):ℝ≥0)) ω := by
    simp only [D, increment, (he i j).1, (he i j).2]
  simpa only [hD] using hb
