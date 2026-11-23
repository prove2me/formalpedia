-- Prove2me | solution 1 for GlobalTheory.CountId.tw_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:06.135852+00:00
-- url     : https://prove2.me/submissions/d358e26a-a1c6-409a-9636-aca700c0932f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {n : ℕ} {E V : Type} [Field E] [AddCommGroup V] [Module E V]
namespace GlobalTheory.CountId
theorem _root_.solution (e : Basis (Fin n) E V) (γ : GL (Fin n) E) (j : Fin n) :
    tw e γ j = ∑ i, ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j • e i := by
  simp [tw, Matrix.toLin_self]
end GlobalTheory.CountId
