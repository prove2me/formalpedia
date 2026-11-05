-- Prove2me | solution 1 for GraphonGames.Existence.lemma_3_16_aggregate_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T17:51:22.085255+00:00
-- url     : https://prove2.me/submissions/68c7ada6-3268-42c6-a45a-e60a5f70ed58

import Mathlib
import Definitions.Def_GraphonGames_Existence_Setting
import Theorems.Thm_GraphonGames_Stability_lemma_3_16_aggregate_lipschitz

open MeasureTheory
open scoped ENNReal

open GraphonGames.Existence

theorem solution (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : Asm1 b μ0 cα cz) (w : I → I → ℝ) (hw : IsGraphon w)
    (hW : Real.sqrt cz * (opNorm w).toReal < 1)
    (α1 α2 : I → ℝ) (hα1 : MemLp α1 2 volume) (hα2 : MemLp α2 2 volume)
    (z1 z2 : I → ℝ) (hz1 : IsAggregate w b α1 z1) (hz2 : IsAggregate w b α2 z2) :
    eLpNorm (z1 - z2) 2 volume ≤
      ENNReal.ofReal (Real.sqrt cα * (opNorm w).toReal / (1 - Real.sqrt cz * (opNorm w).toReal)) *
        eLpNorm (α1 - α2) 2 volume :=
  GraphonGames.Stability.lemma_3_16_aggregate_lipschitz b μ0 cα cz h1 w hw hW α1 α2 hα1 hα2 z1 z2 hz1 hz2
