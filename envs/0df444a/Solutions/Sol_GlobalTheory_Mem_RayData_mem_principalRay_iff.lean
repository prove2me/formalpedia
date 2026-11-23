-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.mem_principalRay_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:01.639959+00:00
-- url     : https://prove2.me/submissions/31ae0c8f-68b3-42cc-b21e-b36a56f01f77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIntegralOfMemRayI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory.Mem.RayData
section aux
variable {K : Type} [Field K] [NumberField K]
open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma coe_idealUnit_eq (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ((_root_.GlobalTheory.Mem.RayData.idealUnit I hI : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = I := rfl
open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma idealUnit_span_mem_rayP_of_sub_one_mem {𝔮 : Ideal (𝓞 K)} {a : 𝓞 K} (ha : a ≠ 0)
    (h : a - 1 ∈ 𝔮) : _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha) ∈ _root_.GlobalTheory.Mem.An.rayP 𝔮 := by
  unfold _root_.GlobalTheory.Mem.An.rayP
  exact Subgroup.subset_closure ⟨a, h, rfl⟩
variable {M : ℕ} (D : RayData K M)
end aux
end GlobalTheory.Mem.RayData
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K]
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.RayData
namespace _root_.GlobalTheory.Mem.RayData
theorem _root_.solution (𝔮 : Ideal (𝓞 K)) (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    x ∈ _root_.GlobalTheory.Mem.An.rayP 𝔮 ↔ ∃ (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0), a - 1 ∈ 𝔮 ∧ b - 1 ∈ 𝔮 ∧
      x * _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot hb) = _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha) := by
  constructor
  · intro hx
    unfold _root_.GlobalTheory.Mem.An.rayP at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha1, hya⟩ := hy
      have ha : a ≠ 0 := by
        rintro rfl
        exact y.ne_zero (by rw [hya]; simp)
      refine ⟨a, 1, ha, one_ne_zero, ha1, by simp, ?_⟩
      ext
      simp [coe_idealUnit_eq, hya]
    | one =>
      exact ⟨1, 1, one_ne_zero, one_ne_zero, by simp, by simp, one_mul _⟩
    | mul y z _ _ hy hz =>
      obtain ⟨a, b, ha, hb, ha1, hb1, hyab⟩ := hy
      obtain ⟨c, d, hc, hd, hc1, hd1, hzcd⟩ := hz
      refine ⟨a * c, b * d, mul_ne_zero ha hc, mul_ne_zero hb hd, ?_, ?_, ?_⟩
      · have e : a * c - 1 = a * (c - 1) + (a - 1) := by ring
        rw [e]
        exact 𝔮.add_mem (𝔮.mul_mem_left _ hc1) ha1
      · have e : b * d - 1 = b * (d - 1) + (b - 1) := by ring
        rw [e]
        exact 𝔮.add_mem (𝔮.mul_mem_left _ hd1) hb1
      · rw [Units.ext_iff] at hyab hzcd ⊢
        simp only [Units.val_mul, coe_idealUnit_eq] at hyab hzcd ⊢
        rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
          FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, ← hyab, ← hzcd]
        ring
    | inv y _ hy =>
      obtain ⟨a, b, ha, hb, ha1, hb1, hyab⟩ := hy
      refine ⟨b, a, hb, ha, hb1, ha1, ?_⟩
      rw [← hyab, inv_mul_cancel_left]
  · rintro ⟨a, b, ha, hb, ha1, hb1, h⟩
    have hx : x = _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha) * (_root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot hb))⁻¹ := by
      rw [← h, mul_inv_cancel_right]
    rw [hx]
    exact mul_mem (idealUnit_span_mem_rayP_of_sub_one_mem ha ha1)
      (inv_mem (idealUnit_span_mem_rayP_of_sub_one_mem hb hb1))
end _root_.GlobalTheory.Mem.RayData
end GlobalTheory.Mem.RayData
