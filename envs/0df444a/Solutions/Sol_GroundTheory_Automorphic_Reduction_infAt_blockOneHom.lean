-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.infAt_blockOneHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:03:34.910782+00:00
-- url     : https://prove2.me/submissions/1d81e5de-85ce-4de2-9d91-5f1f3b1cc967

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionBlock
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
import Theorems.Thm_GroundTheory_Automorphic_Reduction_blockOne_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {m : ℕ} (w : InfinitePlace K) (k : AdelicGLn.AdelicGL K m) :
    infAt w (blockOneHom k) = blockOneHom (infAt w k) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact congrArg (fun N => N i j) (blockOne_map (infEval w) (k : Matrix (Fin m) (Fin m) 𝔸[K]))
end GroundTheory.Automorphic.Reduction
