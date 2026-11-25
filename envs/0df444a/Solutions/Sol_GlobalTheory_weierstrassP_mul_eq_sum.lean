-- Prove2me | solution 1 for GlobalTheory.weierstrassP_mul_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:16.543455+00:00
-- url     : https://prove2.me/submissions/3f9fe0df-0017-4d36-80bf-1c06974249ee

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
theorem _root_.solution (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice)
    {ι : Type*} [Fintype ι] (r : ι → ℂ) (h₁ : ∀ t, α * r t ∈ L'.lattice)
    (h₂ : ∀ s t, r s - r t ∈ L.lattice → s = t)
    (h₃ : ∀ m, α * m ∈ L'.lattice → ∃ t, m - r t ∈ L.lattice) (z : ℂ) :
    α ^ 2 * ℘[L'] (α * z) = ∑ t, (℘[L] (z - r t) - ℘[L] (r t)) := by
  let e : ι × L.lattice → L'.lattice := fun x ↦
    ⟨α * (r x.1 + x.2), by rw [mul_add]; exact add_mem (h₁ _) (hα _ x.2.2)⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨s, l⟩ ⟨t, l'⟩ h
      have h0 : r s + l = r t + l' := mul_left_cancel₀ hα0 (congrArg Subtype.val h)
      obtain rfl : s = t := h₂ _ _ (by
        rw [show r s - r t = l' - l by linear_combination h0]; exact sub_mem l'.2 l.2)
      rw [Subtype.ext (add_left_cancel h0)]
    · rintro ⟨m, hm⟩
      obtain ⟨t, ht⟩ := h₃ (α⁻¹ * m) (by rwa [mul_inv_cancel_left₀ hα0])
      exact ⟨⟨t, _, ht⟩, Subtype.ext (by simp [e, hα0])⟩
  have h := (Equiv.ofBijective e he).hasSum_iff.mpr
    ((L'.hasSum_weierstrassP (α * z)).mul_left (α ^ 2))
  refine (h.prod_fiberwise fun t ↦ ?_).unique (hasSum_fintype _)
  rw [← L.weierstrassP_neg (r t)]
  refine ((L.hasSum_weierstrassP (z - r t)).sub (L.hasSum_weierstrassP (-r t))).congr_fun ?_
  intro l
  simp only [e, Equiv.ofBijective_apply, Function.comp_apply, ← mul_sub, mul_pow]
  field_simp
  ring
end GlobalTheory
