-- Prove2me | solution 1 for MeasureTheory.memLp_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:25:49.265472+00:00
-- url     : https://prove2.me/submissions/da2a8185-ad80-4deb-979a-1bb75cdc6837

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
namespace MeasureTheory
theorem _root_.solution {f : α → 𝕜} (hf : MemLp f ⊤ μ) (g : Lp 𝕜 2 μ) :
    MemLp (f • ⇑g) 2 μ :=
  ⟨hf.aestronglyMeasurable.smul (Lp.aestronglyMeasurable g), lt_of_le_of_lt
    (eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 (Lp.aestronglyMeasurable g) f)
    (ENNReal.mul_lt_top hf.eLpNorm_lt_top (Lp.memLp g).eLpNorm_lt_top)⟩
end MeasureTheory
