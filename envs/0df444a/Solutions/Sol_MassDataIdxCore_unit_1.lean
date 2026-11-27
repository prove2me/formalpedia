-- Prove2me | solution 1 for MassDataIdxCore.unit_1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:50:30.602886+00:00
-- url     : https://prove2.me/submissions/a7b9dee8-0fc6-4a1b-9f07-c481902b0be1

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_StRedCore
import Theorems.Thm_MassDataIdxCore_firstSplit_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K)
variable {θ} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap)
include hs
variable {n : Type} [Fintype n] [DecidableEq n]
namespace MassDataIdxCore
theorem _root_.solution (J : Matrix n n T) (g : GL n T) (hg : g ∈ Formalism.UG.UJ s J) :
    ((g : Matrix n n T).map (t2 θ))ᵀ * J.map (t1 θ) * (g : Matrix n n T).map (t1 θ) = J.map (t1 θ) := by
  have hg' : Formalism.UG.cT s (g : Matrix n n T) * J * (g : Matrix n n T) = J := hg
  have e : ((g : Matrix n n T).map (t2 θ))ᵀ = (Formalism.UG.cT s (g : Matrix n n T)).map (t1 θ) := by
    ext i j
    simp [Formalism.UG.cT, firstSplit_conj hs]
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (fun M : Matrix n n T => M.map (t1 θ)) hg'
end MassDataIdxCore
