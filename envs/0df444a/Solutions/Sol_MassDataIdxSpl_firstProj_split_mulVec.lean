-- Prove2me | solution 1 for MassDataIdxSpl.firstProj_split_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:32.497655+00:00
-- url     : https://prove2.me/submissions/09b183aa-6d10-4e06-be0a-f2a2597596e5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_FstMemSpan
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondProjSplitMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxSpl
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Matrix
open scoped TensorProduct
namespace MassDataIdxSpl
theorem _root_.solution {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}
    [Fintype n] (M : Matrix n n T) (v : n → T) :
    pr1 θ (M *ᵥ v) = (M.map fun t => (θ t).1) *ᵥ pr1 θ v := by
  ext i
  simp [pr1, Matrix.mulVec, dotProduct, Prod.fst_sum]
end MassDataIdxSpl
