-- Prove2me | solution 1 for Kyprianou.Ch04.affineLeftLimitBudgetV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:59:31.762881+00:00
-- url     : https://prove2.me/submissions/1825b164-7505-48b4-8412-5e461348dcce

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_twoAffineStepsBoundedV1
import Theorems.Thm_Kyprianou_Ch04_compactDifferenceSquareRangeV1
import Theorems.Thm_Kyprianou_Ch04_leftLimitSquareSupV1
open MeasureTheory Set Filter Topology
open scoped NNReal
set_option autoImplicit false

/-- The left-limit square difference is dominated by the compact supremum of two affine step paths. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (U V UL VL : NNReal → Ω → ℝ) (d e : ℝ) (T : NNReal)
    (hU : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ (L S : Finset (ℝ × ℝ)) (a c : ℝ × ℝ → ℝ),
      ∀ t : NNReal, t ≤ (n : NNReal) → U t ω = d * (t : ℝ) +
        (∑ p ∈ L, if p.1 ≤ (t : ℝ) then a p else 0) +
        (∑ p ∈ S, if p.1 ≤ (t : ℝ) then c p else 0))
    (hV : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ (L S : Finset (ℝ × ℝ)) (a c : ℝ × ℝ → ℝ),
      ∀ t : NNReal, t ≤ (n : NNReal) → V t ω = e * (t : ℝ) +
        (∑ p ∈ L, if p.1 ≤ (t : ℝ) then a p else 0) +
        (∑ p ∈ S, if p.1 ≤ (t : ℝ) then c p else 0))
    (hUL : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → Tendsto (fun s => U s ω) (𝓝[<] t) (𝓝 (UL t ω)))
    (hVL : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → Tendsto (fun s => V s ω) (𝓝[<] t) (𝓝 (VL t ω))) :
    ∀ᵐ ω ∂P,
      let Q := sSup ((fun t : NNReal => |U t ω - V t ω|^2) '' Iic T)
      0 ≤ Q ∧ ∀ t : NNReal, 0 < t → t ≤ T → (UL t ω - VL t ω)^2 ≤ Q := by
  obtain ⟨n,hn⟩ := exists_nat_ge T
  filter_upwards [hU,hV,hUL,hVL] with ω hu hv hul hvl
  obtain ⟨L,S,a,c,hA⟩ := hu n
  obtain ⟨L',S',a',c',hB⟩ := hv n
  have h1 := Kyprianou.Ch04.twoAffineStepsBoundedV1 L S a Prod.fst c Prod.fst d T
    (fun t => U t ω) (fun t ht => hA t (ht.trans hn))
  have h2 := Kyprianou.Ch04.twoAffineStepsBoundedV1 L' S' a' Prod.fst c' Prod.fst e T
    (fun t => V t ω) (fun t ht => hB t (ht.trans hn))
  have hb := Kyprianou.Ch04.compactDifferenceSquareRangeV1 (fun t => U t ω)
    (fun t => V t ω) T _ _ ((abs_nonneg _).trans (h1 0 zero_le))
    ((abs_nonneg _).trans (h2 0 zero_le)) h1 h2
  refine ⟨(sq_nonneg _).trans (le_csSup hb ⟨0,mem_Iic.mpr zero_le,rfl⟩),?_⟩
  intro t ht htT
  exact Kyprianou.Ch04.leftLimitSquareSupV1 (fun s => U s ω) (fun s => V s ω)
    (UL t ω) (VL t ω) t T ht htT (hul t ht) (hvl t ht) hb
