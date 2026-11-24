-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.leadMinor_rowAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:50.915961+00:00
-- url     : https://prove2.me/submissions/4fe63f69-07ba-4d69-acbe-2c28c423cfe4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}
namespace GlobalTheory.UnipotentInvariant
theorem _root_.solution (i a b : Fin p) (hab : a < b) (t : K) (M : Matrix (Fin p) (Fin p) K) :
    leadMinor i (rowAdd a b t M) = leadMinor i M := by
  unfold leadMinor
  by_cases hb : b.val < i.val + 1
  · have ha : a.val < i.val + 1 := lt_trans hab hb
    have hne : (⟨b.val, hb⟩ : Fin (i.val + 1)) ≠ ⟨a.val, ha⟩ := by
      intro h
      have : b.val = a.val := Fin.mk.inj h
      exact absurd hab (by simp [Fin.lt_def, this])
    rw [← det_updateRow_add_smul_self
      (Matrix.of fun a b : Fin (i.val + 1) => M (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)) hne t]
    congr 1
    ext u v
    by_cases hu : u = ⟨b.val, hb⟩
    · subst hu
      simp [rowAdd, Fin.castLE]
    · have : Fin.castLE i.isLt u ≠ b := by
        intro h
        apply hu
        ext
        simpa using congrArg Fin.val h
      simp [rowAdd, updateRow_ne hu, this]
  · congr 1
    ext u v
    have : Fin.castLE i.isLt u ≠ b := by
      intro h
      apply hb
      rw [← h]
      exact u.isLt
    simp [rowAdd, this]
end GlobalTheory.UnipotentInvariant
