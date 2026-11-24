-- Prove2me | solution 1 for GlobalTheory.AddLaw.diagXYZ_equiv_add_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:39:27.17619+00:00
-- url     : https://prove2.me/submissions/d221eb88-de5e-4d50-8019-908126c79137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_AddLaw_diagXYZ_self
import Theorems.Thm_GlobalTheory_AddLaw_diagXYZ_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Projective
open GlobalTheory GlobalTheory.AddLaw
variable {F : Type*} [Field F] {W : Projective F}
namespace GlobalTheory.AddLaw
theorem _root_.solution {P Q : Fin 3 → F} (hP : W.Equation P) (h : P ≈ Q) :
    diagXYZ W P Q ≈ W.add P Q := by
  rw [add_of_equiv h, ← diagXYZ_self hP]
  obtain ⟨u, e⟩ := Setoid.symm h
  have := diagXYZ_smul (W := W) P P 1 u
  rw [one_smul, one_mul] at this
  rw [← show (u : F) • P = Q from e, this]
  exact smul_equiv _ (u.isUnit.pow 2)
end GlobalTheory.AddLaw
