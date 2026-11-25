-- Prove2me | solution 1 for GlobalTheory.exists_representatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:10.042986+00:00
-- url     : https://prove2.me/submissions/db02d542-7258-4189-8a6d-30114ea44068

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
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
open Filter PeriodPair Polynomial
open scoped Topology
noncomputable section
open GlobalTheory
variable {L L' : PeriodPair} {α : ℂ}
namespace GlobalTheory
theorem _root_.solution (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) :
    ∃ (Q : Type) (_ : AddCommGroup Q) (_ : Finite Q) (r : Q → ℂ),
      Nat.card Q = (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
        L'.lattice.toAddSubgroup ∧
      (∀ t, α * r t ∈ L'.lattice) ∧ (∀ s t, r s - r t ∈ L.lattice ↔ s = t) ∧
      (∀ s t, r s + r t ∈ L.lattice ↔ s = -t) ∧ (∀ t, r t ∈ L.lattice ↔ t = 0) ∧
      (∀ m, α * m ∈ L'.lattice → ∃ t, m - r t ∈ L.lattice) := by
  let N : Submodule ℤ L'.lattice := (L.lattice.map (LinearMap.mulLeft ℤ α)).submoduleOf L'.lattice
  have hle : L.lattice.map (LinearMap.mulLeft ℤ α) ≤ L'.lattice := by
    rintro _ ⟨l, hl, rfl⟩; exact hα l hl
  have hN : Module.finrank ℤ N = Module.finrank ℤ L'.lattice := by
    rw [(Submodule.submoduleOfEquivOfLe hle).finrank_eq, ← (Submodule.equivMapOfInjective _
      (mul_right_injective₀ hα0) L.lattice).finrank_eq, finrank_lattice, finrank_lattice]
  have key : ∀ x : L'.lattice, α⁻¹ * x ∈ L.lattice ↔ N.mkQ x = 0 := fun x ↦ by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · exact fun h ↦ ⟨_, h, by simp [hα0]⟩
    · rintro ⟨l, hl, e⟩
      have e' : α * l = x := e
      rw [← e', inv_mul_cancel_left₀ hα0]
      exact hl
  choose o ho using N.mkQ_surjective
  refine ⟨L'.lattice ⧸ N, inferInstance, Submodule.finiteQuotientOfFreeOfRankEq N hN,
    fun t ↦ α⁻¹ * o t, rfl, fun t ↦ by simp [hα0], fun s t ↦ ?_, fun s t ↦ ?_, fun t ↦ ?_,
    fun m hm ↦ ⟨N.mkQ ⟨_, hm⟩, ?_⟩⟩
  · rw [← mul_sub, ← Submodule.coe_sub, key, map_sub, ho, ho, sub_eq_zero]
  · rw [← mul_add, ← Submodule.coe_add, key, map_add, ho, ho, add_eq_zero_iff_eq_neg]
  · rw [key, ho]
  · have := (key (⟨_, hm⟩ - o (N.mkQ ⟨_, hm⟩))).mpr (by rw [map_sub, ho, sub_self])
    simpa [mul_sub, hα0] using this
end GlobalTheory
