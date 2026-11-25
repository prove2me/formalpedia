-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_latticeStabilizer_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:30.058394+00:00
-- url     : https://prove2.me/submissions/f415ea4f-3f74-45f5-a2b0-76387ce89333

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Lattice
import Theorems.Thm_GroundTheory_Automorphic_single_one_mem_stdLattice
import Theorems.Thm_GroundTheory_Automorphic_mulVec_mem_stdLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
noncomputable section
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {R : Type*} [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable {H b}
namespace GroundTheory.Automorphic
theorem _root_.solution {O : Subring R} (hO : IsAdapted b O)
    (g : unitaryPoints K E H R) :
    g ∈ latticeStabilizer H R b O ↔
      (∀ p, unitaryCoords H R b g p ∈ O) ∧ ∀ p, unitaryCoords H R b g⁻¹ p ∈ O := by
  constructor
  · intro hg
    refine ⟨fun ⟨i, j, k⟩ => ?_, fun ⟨i, j, k⟩ => ?_⟩
    · have := (hg _ (single_one_mem_stdLattice hO j)).1 i k
      rwa [Matrix.mulVec_single_one] at this
    · have := (hg _ (single_one_mem_stdLattice hO j)).2 i k
      rwa [Matrix.mulVec_single_one] at this
  · rintro ⟨h₁, h₂⟩ x hx
    exact ⟨mulVec_mem_stdLattice hO (fun i j k => h₁ (i, j, k)) hx,
      mulVec_mem_stdLattice hO (fun i j k => h₂ (i, j, k)) hx⟩
end GroundTheory.Automorphic
