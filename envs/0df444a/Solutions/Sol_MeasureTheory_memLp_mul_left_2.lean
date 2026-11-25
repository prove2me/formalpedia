-- Prove2me | solution 2 for MeasureTheory.memLp_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T03:44:53.799195+00:00
-- url     : https://prove2.me/submissions/b9198373-3364-4a1c-8cf0-12c8dcbc148f

module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder
public import Definitions.Def_BasicResults_Spectral_MultiplicationOperator
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal NNReal
open MeasureTheory
open MeasureTheory
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Multiplying an `L²` function by a bounded function preserves `L²`. -/
theorem solution {f : α → 𝕜} (hf : MemLp f ⊤ μ) (g : Lp 𝕜 2 μ) :
    MemLp (f • ⇑g) 2 μ :=
  MemLp.smul (Lp.memLp g) hf
