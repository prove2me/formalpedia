-- Prove2me | solution 1 for GlobalTheory.CountId.Inv_map_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:38:14.807081+00:00
-- url     : https://prove2.me/submissions/7a831c83-cad8-4775-82da-685b4eaca46f

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
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k']
namespace GlobalTheory.CountId
theorem _root_.solution (φ : k →+* k') (h : Function.Injective φ) :
    Function.Injective (fun a : Inv r k => a.map φ) := by
  intro a b hab
  simp only [Inv.map, Prod.mk.injEq] at hab
  obtain ⟨h1, h2, h3⟩ := hab
  exact Prod.ext (funext fun i => h (congrFun h1 i)) (Prod.ext (funext fun i => h (congrFun h2 i)) (h h3))
end GlobalTheory.CountId
