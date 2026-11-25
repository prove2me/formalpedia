-- Prove2me | solution 1 for GroundTheory.Automorphic.AdelicGLn.isClosed_rationalGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:27.369833+00:00
-- url     : https://prove2.me/submissions/4651c000-dde7-4b44-9722-8f9c752459e7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_RestrictedProductMatrix
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_discreteTopology_rationalGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.AdelicGLn
variable (K : Type*) [Field K] [NumberField K] (n : ℕ)
namespace GroundTheory.Automorphic.AdelicGLn
theorem _root_.solution : IsClosed (rationalGL K n : Set (AdelicGL K n)) :=
  have := discreteTopology_rationalGL K n
  Subgroup.isClosed_of_discrete
end GroundTheory.Automorphic.AdelicGLn
