-- Prove2me | solution 1 for MassDataIdxCore.unit_2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:50:36.118204+00:00
-- url     : https://prove2.me/submissions/818c75be-d686-46ca-a0cb-8f2ed8cf303b

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_StRedCore
import Theorems.Thm_MassDataIdxCore_secondSplit_conj

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
    ((g : Matrix n n T).map (t1 θ))ᵀ * J.map (t2 θ) * (g : Matrix n n T).map (t2 θ) = J.map (t2 θ) := by
  have hg' : Formalism.UG.cT s (g : Matrix n n T) * J * (g : Matrix n n T) = J := hg
  have e : ((g : Matrix n n T).map (t1 θ))ᵀ = (Formalism.UG.cT s (g : Matrix n n T)).map (t2 θ) := by
    ext i j
    simp [Formalism.UG.cT, secondSplit_conj hs]
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (fun M : Matrix n n T => M.map (t2 θ)) hg'
end MassDataIdxCore
