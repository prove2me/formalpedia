-- Prove2me | solution 1 for GlobalTheory.exists_det_add_mul_ne_zero_of_ker_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:40:14.466607+00:00
-- url     : https://prove2.me/submissions/81fc0f25-21f6-478c-b08e-4c976b006c4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualPairIsUnitDetBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k : Type} [Field k] {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) k)
    (h : ∀ v : Fin n → k, A *ᵥ v = 0 → C *ᵥ v = 0 → v = 0) :
    ∃ X : Matrix (Fin n) (Fin n) k, (A + X * C).det ≠ 0 := by
  classical
  set a := Matrix.toLin' A with ha
  set c := Matrix.toLin' C with hc
  obtain ⟨L', hL'⟩ := Submodule.exists_isCompl (LinearMap.ker c)
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl ((LinearMap.ker c).map a)

  have hkey : ∀ x ∈ LinearMap.ker c, a x = 0 → x = 0 := by
    intro x hx hax
    rw [LinearMap.mem_ker] at hx
    exact h x (by simpa [ha] using hax) (by simpa [hc] using hx)
  have hinj : Function.Injective (a.domRestrict (LinearMap.ker c)) := by
    intro x y hxy
    have hxy' : a ((x : Fin n → k) - y) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr (by simpa using hxy)
    have := hkey _ (Submodule.sub_mem _ x.2 y.2) hxy'
    exact Subtype.ext (sub_eq_zero.mp this)
  have hrank : Module.finrank k L' = Module.finrank k U := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hL'
    have h2 := Submodule.finrank_add_eq_of_isCompl hU
    have h3 : Module.finrank k ((LinearMap.ker c).map a) = Module.finrank k (LinearMap.ker c) := by
      rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
    omega
  let e : L' ≃ₗ[k] U := LinearEquiv.ofFinrankEq L' U hrank
  let g : (Fin n → k) →ₗ[k] (Fin n → k) :=
    LinearMap.ofIsCompl hL' (a.domRestrict (LinearMap.ker c)) (U.subtype ∘ₗ e.toLinearMap)
  have hgL : ∀ x (hx : x ∈ LinearMap.ker c), g x = a x := fun x hx =>
    LinearMap.ofIsCompl_apply_left hL' ⟨x, hx⟩
  have hgL' : ∀ y (hy : y ∈ L'), g y = (e ⟨y, hy⟩ : Fin n → k) := fun y hy =>
    LinearMap.ofIsCompl_apply_right hL' ⟨y, hy⟩

  have hg_inj : ∀ v, g v = 0 → v = 0 := by
    intro v hv
    have hvmem : v ∈ LinearMap.ker c ⊔ L' := by rw [hL'.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hvmem
    rw [map_add, hgL x hx, hgL' y hy] at hv
    have hax : a x ∈ (LinearMap.ker c).map a ⊓ U := by
      refine ⟨Submodule.mem_map_of_mem hx, ?_⟩
      rw [eq_neg_of_add_eq_zero_left hv]
      exact U.neg_mem (e ⟨y, hy⟩).2
    rw [hU.inf_eq_bot, Submodule.mem_bot] at hax
    have hx0 := hkey x hx hax
    rw [hax, zero_add] at hv
    have hy0 : e ⟨y, hy⟩ = 0 := Subtype.ext hv
    rw [LinearEquiv.map_eq_zero_iff] at hy0
    rw [hx0, zero_add]
    exact congrArg Subtype.val hy0

  have hle : LinearMap.ker c ≤ LinearMap.ker (g - a) := fun x hx => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hgL x hx, sub_self]
  let f0 : LinearMap.range c →ₗ[k] (Fin n → k) :=
    ((LinearMap.ker c).liftQ (g - a) hle) ∘ₗ (c.quotKerEquivRange.symm.toLinearMap)
  obtain ⟨Y, hY⟩ := LinearMap.exists_extend f0
  have hfac : ∀ v, Y (c v) = g v - a v := by
    intro v
    have h0 := LinearMap.congr_fun hY ⟨c v, LinearMap.mem_range_self c v⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h0
    rw [h0]
    simp only [f0, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.sub_apply]
  refine ⟨LinearMap.toMatrix' Y, fun hdet => ?_⟩
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  apply hg_inj
  have hmv : (A + LinearMap.toMatrix' Y * C) *ᵥ v = g v := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    have hcv : C *ᵥ v = c v := by rw [hc, Matrix.toLin'_apply]
    have hav : A *ᵥ v = a v := by rw [ha, Matrix.toLin'_apply]
    rw [hcv, hfac, hav]
    abel
  rw [← hmv, hv]
end GlobalTheory
