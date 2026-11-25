-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isClosed_cellUnipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:50:18.211923+00:00
-- url     : https://prove2.me/submissions/613b4646-a12c-4483-a071-c5e7aa5b7bbc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isClosed_unipotentRadical


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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {γ : Fin n → ℕ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} :
    IsClosed (cellUnipotent F β γ w : Set (GL (Fin n) F)) :=
  isClosed_unipotentRadical.inter (Measures.isClosed_blockUpper F n (β ∘ w))
end GroundTheory.Automorphic.Parabolic
