-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.linearForm_orbitMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:11.580857+00:00
-- url     : https://prove2.me/submissions/e46e1687-9b1d-450e-9aeb-7f4ec289687e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_orbitMap_apply

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
open Set
open GroundTheory.Automorphic.RestrictedTensor
variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (ρ : Representation ℂ G V) (v : V) (l : Module.Dual ℂ V) (h : G)
    (c : G →₀ ℂ) : l (ρ h (orbitMap ρ v c)) = c.sum fun g a => a * l (ρ (h * g) v) := by
  rw [orbitMap_apply, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, map_mul, Module.End.mul_apply]
end GroundTheory.Automorphic.RestrictedTensor
