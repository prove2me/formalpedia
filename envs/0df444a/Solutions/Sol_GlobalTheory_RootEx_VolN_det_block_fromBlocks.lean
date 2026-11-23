-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.det_block_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:26.907802+00:00
-- url     : https://prove2.me/submissions/7f29dae4-bc39-4e3a-a45f-73c6e04e3041

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution {n t : Type} [Fintype n] [DecidableEq n] [Fintype t] [DecidableEq t]
    (x : Matrix n n k) (Q : n ⊕ t → Prop) [DecidablePred Q] (q : Prop) [Decidable q]
    (hQ : ∀ a, Q (Sum.inl a) ↔ q) :
    ((fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k).toSquareBlockProp Q).det = if q then x.det else 1 := by
  have key : ∀ (Q : n ⊕ t → Prop) [DecidablePred Q], (∀ a, ¬ Q (Sum.inl a)) →
      ((fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k).toSquareBlockProp Q).det = 1 := by
    intro Q _ hQ
    have : (fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k).toSquareBlockProp Q = 1 := by
      ext ⟨r | r, hr⟩ ⟨s | s, hs⟩
      · exact absurd hr (hQ _)
      · exact absurd hr (hQ _)
      · exact absurd hs (hQ _)
      · simp [toSquareBlockProp_def, Matrix.one_apply]
    rw [this, det_one]
  split_ifs with hq
  · have := Matrix.twoBlockTriangular_det (fromBlocks x 0 0 1 : Matrix (n ⊕ t) (n ⊕ t) k) Q (by
      rintro (r | r) hr (s | s) hs
      · exact absurd ((hQ r).2 hq) hr
      · exact absurd ((hQ r).2 hq) hr
      · simp
      · have : r ≠ s := by rintro rfl; exact hr hs
        simp [this])
    rw [key (fun i => ¬ Q i) (fun a ha => ha ((hQ a).2 hq)), mul_one] at this
    rw [← this]; simp
  · exact key Q fun a ha => hq ((hQ a).1 ha)
end GlobalTheory.RootEx.VolN
