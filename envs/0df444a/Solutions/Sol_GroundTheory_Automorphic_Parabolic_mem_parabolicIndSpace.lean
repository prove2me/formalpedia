-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mem_parabolicIndSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:14:43.46266+00:00
-- url     : https://prove2.me/submissions/f59eff37-5ac0-4f05-a8da-74c51bef2f2e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (σ : Representation ℂ (levi F n β) W) {f : GL (Fin n) F → W} :
    f ∈ parabolicIndSpace F n β σ ↔
      (∀ p : blockUpper F n β, ∀ g, f (p * g) = sqrtModular F n β p • σ (leviProj F n β p) (f g)) ∧
        ∃ K : Subgroup (GL (Fin n) F), IsOpen (K : Set (GL (Fin n) F)) ∧
          ∀ k ∈ K, ∀ g, f (g * k) = f g :=
  Iff.rfl
end GroundTheory.Automorphic.Parabolic
