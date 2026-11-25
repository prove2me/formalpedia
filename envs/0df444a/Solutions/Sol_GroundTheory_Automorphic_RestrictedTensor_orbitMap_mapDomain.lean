-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.orbitMap_mapDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:29.816555+00:00
-- url     : https://prove2.me/submissions/97ecf582-2a19-4e66-a3b4-0aae64ce7634

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_orbitMap_single

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
theorem _root_.solution (ρ : Representation ℂ G V) (v : V) (h : G) (c : G →₀ ℂ) :
    orbitMap ρ v (Finsupp.mapDomain (h * ·) c) = ρ h (orbitMap ρ v c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [orbitMap]
  | add c d hc hd => rw [Finsupp.mapDomain_add, map_add, hc, hd, map_add, map_add]
  | single g a => simp [Finsupp.mapDomain_single, orbitMap_single, map_mul]
end GroundTheory.Automorphic.RestrictedTensor
