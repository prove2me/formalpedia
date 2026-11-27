-- Prove2me | solution 1 for GroundTheory.Automorphic.AdelicGLn.finite_hasBasis_nhds_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:27.570954+00:00
-- url     : https://prove2.me/submissions/9cc7cd99-75f4-4a39-8c32-ccea0e694b38

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_RestrictedProductMatrix
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Theorems.Thm_GroundTheory_Automorphic_hasBasis_nhds_one_compactOpenSubgroup


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
theorem _root_.solution :
    (𝓝 (1 : FiniteAdelicGL K n)).HasBasis
      (fun H : OpenSubgroup (FiniteAdelicGL K n) => IsCompact (H : Set (FiniteAdelicGL K n)))
      fun H => (H : Set (FiniteAdelicGL K n)) :=
  hasBasis_nhds_one_compactOpenSubgroup
end GroundTheory.Automorphic.AdelicGLn
