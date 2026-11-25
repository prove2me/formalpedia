-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.EntryBound.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:35:44.352004+00:00
-- url     : https://prove2.me/submissions/fd567374-e731-4aed-bfe1-b13408571be7

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
namespace GroundTheory.Automorphic.Parabolic
namespace EntryBound
theorem _root_.solution {a b : ℕ} {A B : Matrix (Fin n) (Fin n) F} (hA : EntryBound F a A)
    (hB : EntryBound F b B) : EntryBound F (a + b) (A * B) := by
  intro i j
  rw [mul_apply, Finset.mul_sum]
  refine sum_mem fun k _ => ?_
  have := mul_mem (hA i k) (hB k j)
  convert this using 1
  ring
end EntryBound
end GroundTheory.Automorphic.Parabolic
