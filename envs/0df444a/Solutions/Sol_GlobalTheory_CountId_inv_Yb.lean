-- Prove2me | solution 1 for GlobalTheory.CountId.inv_Yb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:38:07.927942+00:00
-- url     : https://prove2.me/submissions/78b56f33-cdd7-4117-b662-518053f6ac1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
import Theorems.Thm_GlobalTheory_CountId_mom_Yb

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
theorem _root_.solution [Module.Finite E V] (e : Basis (Fin n) E V) (T : V →ₗ[E] V) (v : V) (l : V →ₗ[E] E) :
    inv (Yb e T v l) = (fun i : Fin n => T.charpoly.coeff i, fun i : Fin n => l ((T ^ (i : ℕ)) v), 0) := by
  simp only [JR.inv]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only [Yb]
    rw [LinearMap.charpoly_toMatrix]
  · funext i
    exact mom_Yb e T v l i
end GlobalTheory.CountId
