-- Prove2me | solution 1 for LinearOptimization.lp_dual_dual
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:22:26.141095+00:00
-- url     : https://prove2.me/submissions/8e72ba6e-38cd-48f1-97dd-1c17eae60f98

import Definitions.Def_LinearOptimization_DualLP

open LinearOptimization

theorem solution {m n : ℕ} (P : GeneralFormLP m n) :
    dualLP (dualLP P) = P := by
  -- the two Table 4.1 tag maps are mutually inverse
  have hrel : ∀ r : ConstraintRel, r.dualSign.dualRel = r := by
    intro r; cases r <;> rfl
  have hsign : ∀ s : VarSign, s.dualRel.dualSign = s := by
    intro s; cases s <;> rfl
  cases P with
  | mk A b c rowRel colSign =>
    simp only [dualLP, Matrix.transpose_neg, Matrix.transpose_transpose, neg_neg]
    congr 1
    · funext i; exact hrel _
    · funext j; exact hsign _
