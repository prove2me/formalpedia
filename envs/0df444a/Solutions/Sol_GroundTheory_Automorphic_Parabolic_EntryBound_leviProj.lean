-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.EntryBound.leviProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:35:45.706973+00:00
-- url     : https://prove2.me/submissions/444a6a12-bdff-4bcc-9ea0-a5196616a304

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_apply


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
namespace GroundTheory.Automorphic.Parabolic
namespace EntryBound
theorem _root_.solution {γ : Fin n → ℕ} {e : ℕ} {p : blockUpper F n γ}
    (hp : EntryBound F e ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    EntryBound F e (((leviProj F n γ p : levi F n γ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  intro i j
  rw [leviProj_apply]
  split_ifs
  · exact hp i j
  · rw [mul_zero]
    exact zero_mem _
end EntryBound
end GroundTheory.Automorphic.Parabolic
