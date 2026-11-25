-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.finAt_blockOneHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:51.03705+00:00
-- url     : https://prove2.me/submissions/89d935ad-fdbf-4feb-a9d1-99929a5f590d

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
theorem _root_.solution {m : ℕ} (v : HeightOneSpectrum (𝓞 K)) (k : AdelicGLn.AdelicGL K m) :
    finAt v (blockOneHom k) = blockOneHom (finAt v k) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact congrArg (fun N => N i j) (blockOne_map (finEval v) (k : Matrix (Fin m) (Fin m) 𝔸[K]))
end GroundTheory.Automorphic.Reduction
