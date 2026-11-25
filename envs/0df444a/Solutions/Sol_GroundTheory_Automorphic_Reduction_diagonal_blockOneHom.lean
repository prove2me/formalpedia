-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.diagonal_blockOneHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:36.475079+00:00
-- url     : https://prove2.me/submissions/c424df3b-3200-43dc-9ec5-29718390e8b9

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
theorem _root_.solution {m : ℕ} (γ : GL (Fin m) K) :
    AdelicGLn.diagonal K (m + 1) (blockOneHom γ) = blockOneHom (AdelicGLn.diagonal K m γ) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact congrArg (fun N => N i j) (blockOne_map (algebraMap K 𝔸[K]) (γ : Matrix (Fin m) (Fin m) K))
end GroundTheory.Automorphic.Reduction
