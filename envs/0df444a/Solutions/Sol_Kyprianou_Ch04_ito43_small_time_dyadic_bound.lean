-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_small_time_dyadic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:51:13.377387+00:00
-- url     : https://prove2.me/submissions/0a2abfa2-f467-4238-bc9c-360f1df26bdb

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_compact_kernel_bound
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution {Ω : Type} [MeasurableSpace Ω]
    (X : NNReal → Ω → ℝ)
    (hX : Measurable (fun z : NNReal × Ω => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w)) (T : NNReal) :
    let d : ℕ → ℕ × ℕ → NNReal := fun n k =>
      min (T / (n : NNReal)) ((k.1 : NNReal) / 2 ^ k.2)
    let K : ℕ → (ℕ × ℕ) → Ω → ℝ := fun n k w => |X (d n k) w - X 0 w|
    let B : ℕ → Ω → ℝ := fun n w => ⨆ k, K n k w
    ∀ (n : ℕ) (w : Ω) (r : NNReal), r ≤ T / (n : NNReal) → |X r w - X 0 w| ≤ B n w := by
  intro d K B
  have hbdd (n : ℕ) (w : Ω) : BddAbove (range (fun k => K n k w)) := by
    obtain ⟨C,_,hC⟩ := Kyprianou.Ch04.ito43_compact_kernel_bound
      (fun t => X t w) (hCad w) (fun z : ℝ × ℝ => z.2 - X 0 w)
      (by fun_prop) (T / (n : NNReal))
    exact ⟨C, by rintro _ ⟨k,rfl⟩; exact hC 0 ⟨le_rfl,by positivity⟩ _ (min_le_left _ _)⟩
  have hle (n : ℕ) (w : Ω) (k : ℕ × ℕ) : K n k w ≤ B n w :=
    le_ciSup (hbdd n w) k
  have hnon (n : ℕ) (w : Ω) : 0 ≤ B n w :=
    (abs_nonneg _).trans (hle n w (0,0))
  intro n w r hr
  let a : ℕ → ℕ × ℕ := fun j => (Nat.ceil ((r : ℝ)*2^j),j)
  have hdt : Tendsto (fun j => d n (a j)) atTop (nhds r) := by
    simpa only [d,a,min_eq_right hr] using
      (tendsto_const_nhds (x := T/(n : NNReal))).min
        (AvramDividend.Classical.dyadic_ceiling_nnreal_tendsto r)
  have hdr (j : ℕ) : r ≤ d n (a j) :=
    le_min hr (AvramDividend.Classical.dyadic_ceiling_time_ge_nnreal r j)
  have hrt : Tendsto (fun j => d n (a j)) atTop (nhdsWithin r (Ici r)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hdt,Eventually.of_forall hdr⟩
  have hl := (((hCad w r).1.tendsto.comp hrt).sub
    (tendsto_const_nhds (x := X 0 w))).abs
  exact le_of_tendsto hl (Eventually.of_forall fun j => hle n w (a j))
