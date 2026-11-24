-- Prove2me | solution 1 for GlobalTheory.SplitDict.integral_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:06:46.316794+00:00
-- url     : https://prove2.me/submissions/9a95f4aa-7fcc-4633-8615-fdf2f0b07030

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
import Theorems.Thm_GlobalTheory_SplitDict_chr_add
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitDict
theorem _root_.solution (ψ : AddChar k Circle) (m : Measure k) [m.IsAddHaarMeasure] (s : ℤˣ)
    {a b : Type} [Fintype a] [Fintype b] (G : Matrix a b k → ℂ) (L : Matrix a b k → k)
    (hL : ∀ x y, L (x + y) = L x + L y) (d : Matrix a b k) :
    ∫ c, G (c + d) * chr ψ (-s) (L c) ∂(volM m a b) =
      chr ψ s (L d) * ∫ c, G c * chr ψ (-s) (L c) ∂(volM m a b) := by
  haveI := secondCountable k
  have hsub : ∀ c, L (c - d) = L c - L d := fun c =>
    eq_sub_of_add_eq (by rw [← hL, sub_add_cancel])
  have hchr : ∀ c, chr ψ (-s) (L (c - d)) = chr ψ (-s) (L c) * chr ψ s (L d) := by
    intro c
    rw [hsub, sub_eq_add_neg, chr_add]
    congr 1
    simp [chr]
  haveI : (volM m a b).IsAddRightInvariant := Measure.pi.isAddRightInvariant _
  haveI : MeasurableAdd (Matrix a b k) := inferInstanceAs (MeasurableAdd (a → b → k))
  have e : ∫ c, G (c + d) * chr ψ (-s) (L c) ∂(volM m a b) =
      ∫ c, G c * chr ψ (-s) (L (c - d)) ∂(volM m a b) := by
    have := integral_add_right_eq_self (μ := volM m a b)
      (fun c : Matrix a b k => G c * chr ψ (-s) (L (c - d))) d
    simp only [add_sub_cancel_right] at this
    exact this
  rw [e]
  simp_rw [hchr, ← mul_assoc]
  rw [integral_mul_const, mul_comm]
end GlobalTheory.SplitDict
