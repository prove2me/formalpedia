-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isOpen_conj_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:35:50.889895+00:00
-- url     : https://prove2.me/submissions/35c0a417-4fb9-4826-98fb-2404a4021269

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable (γ : Fin n → ℕ)
variable {γ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (t : GL (Fin n) F) :
    IsOpen (((integralGL F n).comap (MulAut.conj t).toMonoidHom : Subgroup (GL (Fin n) F)) :
      Set (GL (Fin n) F)) :=
  (isOpen_integralGL F n).preimage (conjHomeomorph t).continuous
end GroundTheory.Automorphic.Parabolic
