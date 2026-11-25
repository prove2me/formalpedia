-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.mOrbitMap_mapDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:26.155367+00:00
-- url     : https://prove2.me/submissions/c16cefb9-e3a1-417d-af86-94d6f24cad7b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mOrbitMap_single

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
theorem _root_.solution (ρ : Representation ℂ M V) (v : V) (h : M) (c : M →₀ ℂ) :
    mOrbitMap ρ v (Finsupp.mapDomain (h * ·) c) = ρ h (mOrbitMap ρ v c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [mOrbitMap]
  | add c d hc hd => rw [Finsupp.mapDomain_add, map_add, hc, hd, map_add, map_add]
  | single g a => simp [Finsupp.mapDomain_single, mOrbitMap_single, map_mul]
end GroundTheory.Automorphic.RestrictedTensor
