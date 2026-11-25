-- Prove2me | solution 1 for GlobalTheory.Klein.not_red_addSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:58:27.282696+00:00
-- url     : https://prove2.me/submissions/0698fe10-96e6-4125-8da2-9824cb5f441d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReductionSetSubgroup
import Theorems.Thm_GlobalTheory_Klein_Red_neg
import Theorems.Thm_GlobalTheory_Klein_Red_add_lattice
import Theorems.Thm_GlobalTheory_Klein_Red_add_of_not
import Theorems.Thm_GlobalTheory_Klein_not_red_of_mem
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk



set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
open GlobalTheory GlobalTheory.Klein
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.Klein
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ), Good ι L r → (∀ z, Red ι L r z → Red ι L r (-z)) ∧ (∀ z, Red ι L r z → ∀ ω ∈ L.lattice, Red ι L r (z + ω)) ∧ (∀ u w, ¬ Red ι L r u → Red ι L r w → Red ι L r (u + w)) ∧ ∃ G : AddSubgroup ℂ, (∀ z, z ∈ G ↔ ¬ Red ι L r z) ∧ ∀ ω ∈ L.lattice, ω ∈ G := by
  intro p _ ι L r hg
  refine ⟨fun z h => h.neg, fun z h ω hω => h.add_lattice hω, fun u w hu hw => Red.add_of_not hg hu hw, ?_⟩
  have hneg : ∀ {z : ℂ}, ¬ Red ι L r z → ¬ Red ι L r (-z) := fun hz h => hz (by simpa using h.neg)
  refine ⟨{ carrier := {z | ¬ Red ι L r z}
            add_mem' := fun {u v} hu hv h => hu ?_
            zero_mem' := not_red_of_mem ι L r L.lattice.zero_mem
            neg_mem' := hneg }, fun z => Iff.rfl, fun ω hω => not_red_of_mem ι L r hω⟩
  have := Red.add_of_not hg (hneg hv) h
  rwa [show -v + (u + v) = u by ring] at this
end GlobalTheory.Klein
