-- Prove2me | solution 1 for MassDataIdxSpl.secondProj_split_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:13.331679+00:00
-- url     : https://prove2.me/submissions/a0336afe-1e4d-4a4a-a4e9-2a0e8ca6ed62

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
    pr2 θ (M *ᵥ v) = (M.map fun t => (θ t).2) *ᵥ pr2 θ v := by
  ext i
  simp [pr2, Matrix.mulVec, dotProduct, Prod.snd_sum]
end MassDataIdxSpl
