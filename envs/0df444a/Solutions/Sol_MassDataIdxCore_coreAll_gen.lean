-- Prove2me | solution 1 for MassDataIdxCore.coreAll_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:36:49.772932+00:00
-- url     : https://prove2.me/submissions/bb7ec4ec-b9b2-4d2d-87f2-b79d2cbd241f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_KerBack
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PairMatrixSecondSplit
import Theorems.Thm_MassDataIdxCore_surjCore
import Theorems.Thm_MassDataIdxCore_kerBack


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
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]
variable (θ : T ≃ₐ[K] K × K)
variable {θ} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap) (J : Matrix n n T) (P : GL n K)
include hs
namespace MassDataIdxCore
theorem _root_.solution (hJ : Formalism.UG.cT s J = J) (hJu : IsUnit J.det) :
    KerBack O θ s J P ∧ SurjCore O θ s J P :=
  ⟨kerBack (O := O) (θ := θ) (s := s) (J := J) (P := P) (hs := hs) hJu, surjCore (O := O) (hs := hs) (J := J) (P := P) hJ hJu⟩
end MassDataIdxCore
