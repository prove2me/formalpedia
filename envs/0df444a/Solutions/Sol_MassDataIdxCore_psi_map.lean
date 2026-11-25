-- Prove2me | solution 1 for MassDataIdxCore.psi_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:17:34.198586+00:00
-- url     : https://prove2.me/submissions/96533e19-af13-4c28-8371-63a5089639ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitTensorVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PsiKerIff

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
variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K) {H : Type} [Group H] (m : H →* GL n T)
  (hK : ∀ h x, x ∈ Lat O θ J P ↔ ((m h : GL n T) : Matrix n n T) *ᵥ x ∈ Lat O θ J P)
namespace MassDataIdxCore
theorem _root_.solution (h : H) : ((psi O θ J P m hK h : GL n O) : Matrix n n O).map (algebraMap O K) =
    conjPrime₂ θ P (m h) :=
  psiU_map O θ J P m hK h
end MassDataIdxCore
