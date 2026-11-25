-- Prove2me | solution 1 for MassDataIdxCore.group_law_jacobian_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:44.774662+00:00
-- url     : https://prove2.me/submissions/575f5335-1f7a-4e0d-a33d-02a2b0a617be

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
theorem _root_.solution (J : Matrix n n T) (hJ : Formalism.UG.cT s J = J) : J.map (t2 θ) = (J.map (t1 θ))ᵀ := by
  ext i j
  have hij := congrFun (congrFun hJ i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at hij
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  rw [← hij, secondSplit_conj hs]
end MassDataIdxCore
