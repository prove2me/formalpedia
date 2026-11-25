-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isSmooth_comp_singleHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:13:57.748916+00:00
-- url     : https://prove2.me/submissions/43b5b6c2-e363-4e2d-b662-fef41d039f23

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Existence
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_boxSubgroup_subset
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_singleHom_mem_boxSubgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Filter Function Module Set PiTensorProduct
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {V : Type u} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (Πʳ v, [G v, K v]) V}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution [DecidableEq ι] (hρ : IsSmooth ρ) (v : ι) :
    IsSmooth (ρ.comp (singleHom K v)) := by
  intro u
  obtain ⟨B, hBc, hBo, -, -, hsub⟩ := exists_boxSubgroup_subset
    (fun v => isCompact_iff_compactSpace.2 (hKc v)) ((hρ u).mem_nhds (stabilizerOf ρ u).one_mem)
  refine Subgroup.isOpen_mono (H₁ := B v) (fun k hk => ?_) (hBo v)
  exact hsub (singleHom_mem_boxSubgroup hk)
end GroundTheory.Automorphic.RestrictedTensor
