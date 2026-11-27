-- Prove2me | solution 1 for GlobalTheory.tensor_component_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:42:42.233259+00:00
-- url     : https://prove2.me/submissions/fdb3beb1-4aa8-43a8-93c3-4b9c2cd91242

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TensorComponentNeZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F : Type) [Field F] (X C : Type) [Finite C] (cl : X → C)
    (E : Type) [AddCommGroup E] [Module F E] (W : X → Type) [∀ a, AddCommGroup (W a)]
    [∀ a, Module F (W a)] (ex : ∀ a, E →ₗ[F] W a)
    (hsep : ∀ s, (∀ a, ex a s = 0) → s = 0)
    (hcut : ∀ (c : C) (s : E), ∃ s' : E, ∀ a,
      (cl a = c → ex a s' = ex a s) ∧ (cl a ≠ c → ex a s' = 0))
    (hinj : ∀ a, ex a ≠ 0 → ∀ s, (∀ b, cl b ≠ cl a → ex b s = 0) → ex a s = 0 → s = 0)
    (w : TensorProduct F E E)
    (hfull : ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E →ₗ[F] E) w = 0 → π = 0)
    (hoff : ∀ a b, cl a ≠ cl b → TensorProduct.map (ex a) (ex b) w = 0)
    (a b : X) (hab : cl a = cl b) :
    TensorProduct.map (ex a) (ex b) w ≠ 0 ↔ ex a ≠ 0 ∧ ex b ≠ 0 := by
  classical
  have := Fintype.ofFinite C
  choose p hp using hcut
  have hext : ∀ s t : E, (∀ x, ex x s = ex x t) → s = t := fun s t h =>
    sub_eq_zero.mp (hsep _ fun x => by rw [map_sub, h x, sub_self])
  let π : C → E →ₗ[F] E := fun c =>
    { toFun := p c
      map_add' := fun s t => hext _ _ fun x => by
        by_cases hx : cl x = c
        · rw [map_add, (hp c _ x).1 hx, (hp c _ x).1 hx, (hp c _ x).1 hx, map_add]
        · rw [map_add, (hp c _ x).2 hx, (hp c _ x).2 hx, (hp c _ x).2 hx, add_zero]
      map_smul' := fun r s => hext _ _ fun x => by
        by_cases hx : cl x = c
        · rw [RingHom.id_apply, map_smul, (hp c _ x).1 hx, (hp c _ x).1 hx, map_smul]
        · rw [RingHom.id_apply, map_smul, (hp c _ x).2 hx, (hp c _ x).2 hx, smul_zero] }
  have h1 : ∀ c s x, cl x = c → ex x (π c s) = ex x s := fun c s x h => (hp c s x).1 h
  have h0 : ∀ c s x, cl x ≠ c → ex x (π c s) = 0 := fun c s x h => (hp c s x).2 h
  have hsum : ∑ c, π c = LinearMap.id := by
    refine LinearMap.ext fun s => hext _ _ fun x => ?_
    rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single (cl x)]
    · exact h1 _ s x rfl
    · intro c _ hc
      exact h0 c s x (Ne.symm hc)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hfac : ∀ x, ex x ≠ 0 → ∃ r : W x →ₗ[F] E, r ∘ₗ ex x = π (cl x) := by
    intro x hx
    have hk : LinearMap.ker (ex x ∘ₗ (LinearMap.range (π (cl x))).subtype) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      rintro ⟨_, s, rfl⟩ hs
      exact Subtype.ext (hinj x hx _ (fun y hy => h0 _ s y hy) hs)
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
    refine ⟨(LinearMap.range (π (cl x))).subtype ∘ₗ g, LinearMap.ext fun s => ?_⟩
    have h2 := congrArg Subtype.val
      (LinearMap.congr_fun hg ⟨π (cl x) s, LinearMap.mem_range_self _ s⟩)
    rw [LinearMap.comp_apply, ← h1 (cl x) s x rfl]
    exact h2
  have hpass : ∀ x y, ex x ≠ 0 → ex y ≠ 0 → TensorProduct.map (ex x) (ex y) w = 0 →
      TensorProduct.map (π (cl x)) (π (cl y)) w = 0 := by
    intro x y hx hy h
    obtain ⟨r, hr⟩ := hfac x hx
    obtain ⟨t, ht⟩ := hfac y hy
    rw [← hr, ← ht, TensorProduct.map_comp, LinearMap.comp_apply, h, map_zero]
  constructor
  · intro h
    constructor
    · intro ha
      apply h
      rw [ha, TensorProduct.map_zero_left, LinearMap.zero_apply]
    · intro hb
      apply h
      rw [hb, TensorProduct.map_zero_right, LinearMap.zero_apply]
  · rintro ⟨ha, hb⟩ h
    have hall : ∀ c, TensorProduct.map (π (cl a)) (π c) w = 0 := by
      intro c
      by_cases hc : cl b = c
      · rw [← hc]
        exact hpass a b ha hb h
      by_cases hy : ∃ y, cl y = c ∧ ex y ≠ 0
      · obtain ⟨y, rfl, hy⟩ := hy
        exact hpass a y ha hy (hoff a y (hab ▸ hc))
      · have hz : π c = 0 := by
          refine LinearMap.ext fun s => hsep _ fun y => ?_
          by_cases hyc : cl y = c
          · have : ex y = 0 := by
              by_contra hne
              exact hy ⟨y, hyc, hne⟩
            rw [this, LinearMap.zero_apply]
          · exact h0 c s y hyc
        rw [hz, TensorProduct.map_zero_right, LinearMap.zero_apply]
    have hz : π (cl a) = 0 := by
      apply hfull
      have e : TensorProduct.map (π (cl a)) (∑ c, π c) =
          ∑ c, TensorProduct.map (π (cl a)) (π c) :=
        map_sum (TensorProduct.mapBilinear (RingHom.id F) E E E E (π (cl a))) π Finset.univ
      rw [← hsum, e, LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun c _ => hall c
    apply ha
    refine LinearMap.ext fun s => ?_
    rw [← h1 (cl a) s a rfl, hz, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
end GlobalTheory
