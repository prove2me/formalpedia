-- Prove2me | solution 1 for GlobalTheory.LatPair.map_mem_EqForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:52.074199+00:00
-- url     : https://prove2.me/submissions/7c978b2c-0d54-42a1-ae7a-16331cd7f37e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)
variable [Fintype n] [DecidableEq n]
variable (π : Representation ℂ (GL n k) M)
namespace GlobalTheory.LatPair
theorem _root_.solution {T : Module.End ℂ (Form k n M)}
    (h1 : ∀ (g : GL n k) φ P, T φ (g • P) = T (fun Q => φ (g • Q)) P)
    (h2 : ∀ (g : GL n k) (φ : Form k n M) P, T (fun Q => π g (φ Q)) P = π g (T φ P))
    {φ : Form k n M} (h : φ ∈ EqForm π) : T φ ∈ EqForm π := fun g P => by
  rw [h1, ← h2]
  exact congrArg (T · P) (funext (h g))
end GlobalTheory.LatPair
