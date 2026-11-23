-- Prove2me | solution 1 for GlobalTheory.CountId.tw_repr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:55.326306+00:00
-- url     : https://prove2.me/submissions/088f3af7-6e77-428b-bdd6-37d28394b869

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
theorem _root_.solution (e : Basis (Fin n) E V) (γ : GL (Fin n) E) (y : V) :
    (fun i => (tw e γ).repr y i) = (γ : Matrix (Fin n) (Fin n) E) *ᵥ fun i => e.repr y i := by
  funext i
  show e.repr (Matrix.toLin e e (γ : Matrix (Fin n) (Fin n) E) y) i = _
  rw [← LinearMap.toMatrix_mulVec_repr e e, LinearMap.toMatrix_toLin]
end GlobalTheory.CountId
