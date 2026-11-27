-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mem_lieLeviPar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:04.474234+00:00
-- url     : https://prove2.me/submissions/e696dc45-325d-456d-9290-a05d61ee1954

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular

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
open Matrix Iwasawa MeasureTheory Measure Topology Set ValuativeRel Measures
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α α' : Type*} [LinearOrder α] [LinearOrder α'] (γ : Fin n → α) (δ : Fin n → α')
variable {F n γ δ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {A : Matrix (Fin n) (Fin n) F} :
    A ∈ lieLeviPar F n γ δ ↔ ∀ i j, ¬ (γ i = γ j ∧ ¬ δ j < δ i) → A i j = 0 :=
  Iff.rfl
end GroundTheory.Automorphic.Parabolic
