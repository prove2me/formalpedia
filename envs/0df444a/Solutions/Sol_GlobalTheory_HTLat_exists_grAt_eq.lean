-- Prove2me | solution 1 for GlobalTheory.HTLat.exists_grAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:51:39.903969+00:00
-- url     : https://prove2.me/submissions/da6384b5-9928-4752-8070-347145052551

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Theorems.Thm_GlobalTheory_HTLat_fg_inf
import Theorems.Thm_GlobalTheory_HTLat_step_mono
import Theorems.Thm_GlobalTheory_HTLat_mem_step_succ
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
set_option autoImplicit false
open scoped TensorProduct NNReal NumberField Pointwise
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
namespace GlobalTheory.HTLat
namespace _root_.GlobalTheory.HTLat
theorem _root_.solution {v : Valuation C ℝ≥0} (hv : v.Integers O)
    {La : Submodule O U} (hfg : La.FG)
    (f : Fin N → U) (i : Fin N) (hf : f i ∉ _root_.GlobalTheory.HTLat.step C f i) {a : C}
    (ha : a ≠ 0) {y : U} (hy : y ∈ _root_.GlobalTheory.HTLat.step C f i)
    (hLa : a • f i + y ∈ La) :
    ∃ c : C, c ≠ 0 ∧ _root_.GlobalTheory.HTLat.grAt C La f i =
        Submodule.span O {c • (_root_.GlobalTheory.HTLat.step C f i).mkQ (f i)} ∧
      _root_.GlobalTheory.HTLat.grNorm v La f i = (v c)⁻¹ := by
  classical
  set S := _root_.GlobalTheory.HTLat.step C f i with hS
  set S' := _root_.GlobalTheory.HTLat.step C f (i + 1) with hS'
  set xb := S.mkQ (f i) with hxb
  have hxb0 : xb ≠ 0 := by
    rw [hxb, Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
    exact hf
  have hSS' : S ≤ S' := _root_.GlobalTheory.HTLat.step_mono f (Nat.le_succ _)
  have hfi : f i ∈ S' := _root_.GlobalTheory.HTLat.mem_step_succ f i
  have hS'le : S' ≤ S ⊔ C ∙ f i := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨k, hk, rfl⟩)
    · rw [Fin.ext hk]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hG : ∀ q ∈ _root_.GlobalTheory.HTLat.grAt C La f i, ∃ b : C, q = b • xb := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hq
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hS'le hw.2)
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 ht
    refine ⟨b, ?_⟩
    show S.mkQ w = b • S.mkQ (f i)
    rw [← hst, map_add, map_smul, Submodule.mkQ_apply S s,
      (Submodule.Quotient.mk_eq_zero S).2 hs, zero_add]
  have hmem : a • xb ∈ _root_.GlobalTheory.HTLat.grAt C La f i := by
    refine Submodule.mem_map.2 ⟨a • f i + y, ⟨hLa, ?_⟩, ?_⟩
    · exact S'.add_mem (S'.smul_mem a hfi) (hSS' hy)
    · show S.mkQ (a • f i + y) = a • S.mkQ (f i)
      rw [map_add, map_smul, Submodule.mkQ_apply S y, (Submodule.Quotient.mk_eq_zero S).2 hy,
        add_zero]
  have hGfg : (_root_.GlobalTheory.HTLat.grAt C La f i).FG :=
    (_root_.GlobalTheory.HTLat.fg_inf hv hfg S').map _
  obtain ⟨s, hs⟩ := hGfg
  choose! coef hcoef using hG
  have hsG : ∀ q ∈ s, q ∈ _root_.GlobalTheory.HTLat.grAt C La f i := fun q hq =>
    hs ▸ Submodule.subset_span hq
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, Submodule.span_empty] at hs
    rw [← hs, Submodule.mem_bot] at hmem
    exact smul_ne_zero ha hxb0 hmem
  obtain ⟨q₀, hq₀, hmax⟩ := s.exists_max_image (fun q => v (coef q)) hsne
  have hc : coef q₀ ≠ 0 := by
    intro hc0
    have hzero : ∀ q ∈ (s : Set (U ⧸ S)), q = 0 := by
      intro q hq
      have h1 := hmax q hq
      rw [hc0, map_zero, nonpos_iff_eq_zero, Valuation.zero_iff] at h1
      rw [hcoef q (hsG q hq), h1, zero_smul]
    have hbot : _root_.GlobalTheory.HTLat.grAt C La f i = ⊥ := by
      rw [← hs, Submodule.span_eq_bot]
      exact hzero
    rw [hbot, Submodule.mem_bot] at hmem
    exact smul_ne_zero ha hxb0 hmem
  have hspan : _root_.GlobalTheory.HTLat.grAt C La f i = Submodule.span O {coef q₀ • xb} := by
    apply le_antisymm
    · rw [← hs, Submodule.span_le]
      intro q hq
      have hle : v (coef q / coef q₀) ≤ 1 := by
        rw [map_div₀]
        exact div_le_one_of_le₀ (hmax q hq) (by positivity)
      obtain ⟨o, ho⟩ := hv.exists_of_le_one hle
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨o, ?_⟩
      rw [← algebraMap_smul C o, ho, smul_smul, div_mul_cancel₀ _ hc, ← hcoef q (hsG q hq)]
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        ← hcoef q₀ (hsG q₀ hq₀)]
      exact hsG q₀ hq₀
  refine ⟨coef q₀, hc, hspan, ?_⟩
  show _root_.GlobalTheory.HTLat.latNorm v (_root_.GlobalTheory.HTLat.grAt C La f i) xb = _
  rw [hspan]
  unfold _root_.GlobalTheory.HTLat.latNorm _root_.GlobalTheory.HTLat.scaleLat
  refine IsLeast.csInf_eq ⟨⟨(coef q₀)⁻¹, ?_, map_inv₀ v _⟩, ?_⟩
  · refine Submodule.mem_map.2 ⟨coef q₀ • xb, Submodule.mem_span_singleton_self _, ?_⟩
    simp only [LinearMap.coe_restrictScalars, LinearMap.smul_apply, LinearMap.id_apply]
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rintro r ⟨b, hb, rfl⟩
    obtain ⟨z, hz, hbz⟩ := Submodule.mem_map.1 hb
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have h1 : (b * algebraMap O C o * coef q₀) • xb = xb := by
      have e1 : (b • LinearMap.id : (U ⧸ S) →ₗ[C] (U ⧸ S)) (o • coef q₀ • xb) = xb := hbz
      rw [LinearMap.smul_apply, LinearMap.id_apply, ← algebraMap_smul C o, smul_smul,
        smul_smul] at e1
      exact e1
    have h2 : b * algebraMap O C o * coef q₀ = 1 := by
      have h3 : (b * algebraMap O C o * coef q₀ - 1) • xb = 0 := by
        rw [sub_smul, h1, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hxb0)
    have h4 : b * algebraMap O C o = (coef q₀)⁻¹ := eq_inv_of_mul_eq_one_left h2
    show (v (coef q₀))⁻¹ ≤ v b
    rw [← map_inv₀, ← h4, map_mul]
    exact mul_le_of_le_one_right (by positivity) (hv.map_le_one o)
end _root_.GlobalTheory.HTLat
end GlobalTheory.HTLat
