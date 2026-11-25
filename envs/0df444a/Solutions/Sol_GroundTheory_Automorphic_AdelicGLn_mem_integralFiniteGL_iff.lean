-- Prove2me | solution 1 for GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:02:18.61356+00:00
-- url     : https://prove2.me/submissions/dad78642-157a-44dd-8d7d-aa327aa711a8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_RestrictedProductMatrix
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn

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
theorem _root_.solution {g : FiniteAdelicGL K n} :
    g ∈ integralFiniteGL K n ↔
      (∀ a b, g a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) ∧
        ∀ a b, (g⁻¹ : FiniteAdelicGL K n) a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
  rw [integralFiniteGL, Submonoid.mem_units_iff, Subring.mem_toSubmonoid,
    Subring.mem_toSubmonoid, mem_integralFiniteMatrices, mem_integralFiniteMatrices]
end GroundTheory.Automorphic.AdelicGLn
