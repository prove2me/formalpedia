-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.card_eq_rayNo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:17:28.579666+00:00
-- url     : https://prove2.me/submissions/23119e15-9c88-4960-8253-563a75cda7f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIntegralOfMemRayI
import Theorems.Thm_GlobalTheory_Mem_RayData_idealUnit_mul
import Theorems.Thm_GlobalTheory_Mem_RayData_idealUnit_congr
import Theorems.Thm_GlobalTheory_Mem_RayData_mem_principalRay_iff
import Theorems.Thm_GlobalTheory_Mem_An_Model_mem_rayI_of_coprime

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
open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma ideal_mul_ne_bot {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : I * J ≠ ⊥ :=
  fun h => (Ideal.mul_eq_bot.mp h).elim hI hJ
open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma exists_coprime_idealUnit_mul_mem_rayP {𝔮 I : Ideal (𝓞 K)}
    (hIq : IsCoprime I 𝔮) (hI : I ≠ ⊥) :
    ∃ (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥), IsCoprime J 𝔮 ∧
      _root_.GlobalTheory.Mem.RayData.idealUnit I hI * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ ∈ _root_.GlobalTheory.Mem.An.rayP 𝔮 := by
  have hsup : I ⊔ 𝔮 = ⊤ := Ideal.isCoprime_iff_sup_eq.mp hIq
  obtain ⟨c, hcI, hc0, hc1⟩ : ∃ c ∈ I, c ≠ 0 ∧ c - 1 ∈ 𝔮 := by
    have h1 : (1 : 𝓞 K) ∈ I ⊔ 𝔮 := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨i, hi, r, hr, hir⟩ := Submodule.mem_sup.mp h1
    by_cases hi0 : i = 0
    · have h1q : (1 : 𝓞 K) ∈ 𝔮 := by rw [← hir, hi0, zero_add]; exact hr
      obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      refine ⟨c, hc, hc0, ?_⟩
      rw [(Ideal.eq_top_iff_one _).mpr h1q]
      exact Submodule.mem_top
    · refine ⟨i, hi, hi0, ?_⟩
      have e : i - 1 = -r := by rw [← hir]; ring
      rw [e]
      exact 𝔮.neg_mem hr
  obtain ⟨J, hJ⟩ := Ideal.dvd_span_singleton.mpr hcI
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    exact _root_.GlobalTheory.Mem.RayData.span_ne_bot hc0 (by rw [hJ, Ideal.mul_bot])
  have hcq : Ideal.span {c} ⊔ 𝔮 = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 K) = c - (c - 1) := by ring
    rw [e]
    exact Submodule.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self c))
      (Ideal.mem_sup_right hc1)
  refine ⟨J, hJ0, Ideal.isCoprime_iff_sup_eq.mpr (eq_top_mono (sup_le_sup_right ?_ _) hcq), ?_⟩
  · rw [hJ]
    exact Ideal.mul_le_inf.trans inf_le_right
  · rw [← _root_.GlobalTheory.Mem.RayData.idealUnit_mul I J hI hJ0 (ideal_mul_ne_bot hI hJ0)]
    have e : _root_.GlobalTheory.Mem.RayData.idealUnit (I * J) (ideal_mul_ne_bot hI hJ0) = _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot hc0) :=
      (_root_.GlobalTheory.Mem.RayData.idealUnit_congr _ _).2 hJ.symm
    rw [e]
    exact idealUnit_span_mem_rayP_of_sub_one_mem hc0 hc1
end GlobalTheory.Mem.RayData
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayData
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory.Mem.RayData
namespace _root_.GlobalTheory.Mem.RayData
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), M ≠ 0 →
    ∀ D : _root_.GlobalTheory.Mem.RayData K M,
    Fintype.card D.G =
      _root_.GlobalTheory.Mem.An.rayNo (Ideal.span {(M : NumberField.RingOfIntegers K)}) := by
  intro K _ _ M _ D
  set 𝔮 : Ideal (𝓞 K) := Ideal.span {(M : 𝓞 K)} with h𝔮
  have memF : ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥), IsCoprime I 𝔮 →
      _root_.GlobalTheory.Mem.RayData.idealUnit I hI ∈ _root_.GlobalTheory.Mem.An.rayI 𝔮 := fun I hI hIq =>
    _root_.GlobalTheory.Mem.An.Model.mem_rayI_of_coprime 𝔮 I hI (Ideal.isCoprime_iff_sup_eq.mp hIq) _ rfl
  have S : ∀ x ∈ _root_.GlobalTheory.Mem.An.rayI 𝔮, ∃ (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥),
      IsCoprime J 𝔮 ∧ x⁻¹ * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ ∈ _root_.GlobalTheory.Mem.An.rayP 𝔮 := by
    intro x hx
    unfold _root_.GlobalTheory.Mem.An.rayI at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, hyv⟩ := hy
      have hv0 : v.asIdeal ≠ ⊥ := v.ne_bot
      refine ⟨v.asIdeal, hv0, ?_, ?_⟩
      · rw [Ideal.isCoprime_iff_sup_eq]
        by_contra h
        have e := v.isMaximal.eq_of_le h le_sup_left
        exact hv (Ideal.dvd_iff_le.mpr (le_sup_right.trans e.ge))
      · have e : y = _root_.GlobalTheory.Mem.RayData.idealUnit v.asIdeal hv0 := Units.ext hyv
        rw [e, inv_mul_cancel]
        exact one_mem _
    | one =>
      refine ⟨⊤, top_ne_bot, Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _), ?_⟩
      have e : _root_.GlobalTheory.Mem.RayData.idealUnit (⊤ : Ideal (𝓞 K)) top_ne_bot = 1 := by
        ext
        simp [coe_idealUnit_eq]
      rw [e, mul_one, inv_one]
      exact one_mem _
    | mul y z _ _ hy hz =>
      obtain ⟨J, hJ, hJq, hyJ⟩ := hy
      obtain ⟨L, hL, hLq, hzL⟩ := hz
      refine ⟨J * L, ideal_mul_ne_bot hJ hL, hJq.mul_left hLq, ?_⟩
      rw [_root_.GlobalTheory.Mem.RayData.idealUnit_mul J L hJ hL, mul_inv, mul_mul_mul_comm]
      exact mul_mem hyJ hzL
    | inv y _ hy =>
      obtain ⟨J, hJ, hJq, hyJ⟩ := hy
      obtain ⟨L, hL, hLq, hJL⟩ := exists_coprime_idealUnit_mul_mem_rayP hJq hJ
      refine ⟨L, hL, hLq, ?_⟩
      have e : y⁻¹⁻¹ * _root_.GlobalTheory.Mem.RayData.idealUnit L hL = (y⁻¹ * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ)⁻¹ * (_root_.GlobalTheory.Mem.RayData.idealUnit J hJ * _root_.GlobalTheory.Mem.RayData.idealUnit L hL) := by
        rw [mul_inv_rev, inv_inv, mul_comm (_root_.GlobalTheory.Mem.RayData.idealUnit J hJ)⁻¹ y, mul_assoc,
          inv_mul_cancel_left]
      rw [e]
      exact mul_mem (inv_mem hyJ) hJL
  choose I hIq hI0 hIcls using D.cls_surj
  let f : D.G → _root_.GlobalTheory.Mem.An.rayI 𝔮 ⧸
      (_root_.GlobalTheory.Mem.An.rayP 𝔮).subgroupOf (_root_.GlobalTheory.Mem.An.rayI 𝔮) :=
    fun c => QuotientGroup.mk ⟨_root_.GlobalTheory.Mem.RayData.idealUnit (I c) (hI0 c), memF _ _ (hIq c)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c d hcd
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hcd
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcd
      obtain ⟨a, b, ha, hb, ha1, hb1, h⟩ := (_root_.GlobalTheory.Mem.RayData.mem_principalRay_iff 𝔮 _).mp hcd
      rw [← hIcls c, ← hIcls d, D.cls_eq _ _ (hIq c) (hIq d) (hI0 c) (hI0 d)]
      refine ⟨a, b, ha, hb, ha1, hb1, ?_⟩
      have h' : _root_.GlobalTheory.Mem.RayData.idealUnit (I d) (hI0 d) * _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot hb) =
          _root_.GlobalTheory.Mem.RayData.idealUnit (I c) (hI0 c) * _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha) := by
        rw [← h]
        group
      rw [← _root_.GlobalTheory.Mem.RayData.idealUnit_mul _ _ _ _ (ideal_mul_ne_bot (hI0 d) (_root_.GlobalTheory.Mem.RayData.span_ne_bot hb)),
        ← _root_.GlobalTheory.Mem.RayData.idealUnit_mul _ _ _ _ (ideal_mul_ne_bot (hI0 c) (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha)), _root_.GlobalTheory.Mem.RayData.idealUnit_congr] at h'
      rw [mul_comm (Ideal.span {a}), mul_comm (Ideal.span {b})]
      exact h'.symm
    · intro y
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨J, hJ0, hJq, hxJ⟩ := S x hx
      refine ⟨D.cls J, ?_⟩
      have hc := hIcls (D.cls J)
      rw [D.cls_eq _ _ (hIq _) hJq (hI0 _) hJ0] at hc
      obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := hc
      set u := _root_.GlobalTheory.Mem.RayData.idealUnit (I (D.cls J)) (hI0 _) with hu
      have e : _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha) * u = _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot hb) * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ0 := by
        rw [hu, ← _root_.GlobalTheory.Mem.RayData.idealUnit_mul _ _ _ _ (ideal_mul_ne_bot (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha) (hI0 _)),
          ← _root_.GlobalTheory.Mem.RayData.idealUnit_mul _ _ _ _ (ideal_mul_ne_bot (_root_.GlobalTheory.Mem.RayData.span_ne_bot hb) hJ0), _root_.GlobalTheory.Mem.RayData.idealUnit_congr]
        exact hab
      have hP : u⁻¹ * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ0 ∈ _root_.GlobalTheory.Mem.An.rayP 𝔮 := by
        rw [_root_.GlobalTheory.Mem.RayData.mem_principalRay_iff]
        refine ⟨a, b, ha, hb, ha1, hb1, ?_⟩
        rw [mul_assoc, mul_comm (_root_.GlobalTheory.Mem.RayData.idealUnit J hJ0), ← e, mul_comm (_root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha)),
          inv_mul_cancel_left]
      show QuotientGroup.mk _ = QuotientGroup.mk _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have e' : u⁻¹ * x = (u⁻¹ * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ0) * (x⁻¹ * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ0)⁻¹ := by group
      rw [e']
      exact mul_mem hP (inv_mem hxJ)
  rw [Fintype.card_eq_nat_card, Nat.card_eq_of_bijective f hf]
  rfl
end _root_.GlobalTheory.Mem.RayData
end GlobalTheory.Mem.RayData
