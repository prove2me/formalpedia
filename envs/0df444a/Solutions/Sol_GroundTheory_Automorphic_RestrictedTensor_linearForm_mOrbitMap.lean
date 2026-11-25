-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.linearForm_mOrbitMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:07.098639+00:00
-- url     : https://prove2.me/submissions/6c57c5d1-bff3-4748-8b21-2c20b130d51a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow

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
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (ρ : Representation ℂ M V) (v : V) (l : Dual ℂ V) (h : M)
    (c : M →₀ ℂ) : l (ρ h (mOrbitMap ρ v c)) = c.sum fun g a => a * l (ρ (h * g) v) := by
  rw [mOrbitMap, Finsupp.linearCombination_apply, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, map_mul, Module.End.mul_apply]
end GroundTheory.Automorphic.RestrictedTensor
