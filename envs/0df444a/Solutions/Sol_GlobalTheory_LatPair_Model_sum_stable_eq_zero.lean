-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.sum_stable_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:32.713286+00:00
-- url     : https://prove2.me/submissions/51c8f892-d506-4d45-837a-2f69471b32f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_LatPair_mem_Mram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.LatPair.Model
theorem _root_.solution {φ : Form k n M} (h : φ ∈ Mram k n M) (s : Finset (Pair k n))
    (hs : ∀ (c : 𝓀[k]ˣ) P, c • P ∈ s ↔ P ∈ s) : ∑ P ∈ s, φ P = 0 := by
  letI := Fintype.ofFinite 𝓀[k]ˣ
  have h1 : ∑ P ∈ s, ∑ c : 𝓀[k]ˣ, φ (c • P) = 0 := Finset.sum_eq_zero fun P _ => (mem_Mram φ).1 h P
  rw [Finset.sum_comm] at h1
  have h2 : ∀ c : 𝓀[k]ˣ, ∑ P ∈ s, φ (c • P) = ∑ P ∈ s, φ P := fun c =>
    Finset.sum_equiv (MulAction.toPerm c) (fun P => (hs c P).symm) fun _ _ => rfl
  simp only [h2, Finset.sum_const, Finset.card_univ] at h1
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1).resolve_left (by exact_mod_cast Fintype.card_ne_zero)
end GlobalTheory.LatPair.Model
