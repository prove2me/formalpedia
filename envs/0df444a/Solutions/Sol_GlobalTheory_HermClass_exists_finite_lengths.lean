-- Prove2me | solution 1 for GlobalTheory.HermClass.exists_finite_lengths
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:32.562513+00:00
-- url     : https://prove2.me/submissions/4f099d74-7928-4c39-9a76-fcb0df7db7d4

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteOrthogonalLengths_208b36ca428fb8e7
import Theorems.Thm_GlobalTheory_HermClass_exists_bound_short
import Theorems.Thm_GlobalTheory_HermClass_exists_finite_residues
import Theorems.Thm_GlobalTheory_HermClass_exists_int_mul_mem_span
import Theorems.Thm_GlobalTheory_HermClass_fg_integers
import Theorems.Thm_GlobalTheory_HermClass_isIntegral_star


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HermClass
theorem _root_.solution (n : ℕ) (hn : n ≠ 0) {N : ℤ} (hN : N ≠ 0) :
    ∃ S : Set E, S.Finite ∧ (0 : E) ∉ S ∧
      ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V), finrank E V = n →
      (∀ x y, h y x = star (h x y)) → (∀ y, (∀ x, h y x = 0) → y = 0) →
      Λ.FG → span E (Λ : Set V) = ⊤ →
      (∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (h x y)) →
      (∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ) →
      ∃ v ∈ Λ, h v v ∈ S := by
  classical
  obtain ⟨C, hC⟩ := exists_bound_short (E := E) n hn hN
  obtain ⟨M, hM, hMJ⟩ := exists_int_mul_mem_span E
  let L : Submodule ℤ E := Subalgebra.toSubmodule (integralClosure ℤ E) ⊓
    LinearMap.ker ((starRingEnd E).toIntAlgHom.toLinearMap - LinearMap.id)
  have hL : ∀ x, x ∈ L ↔ IsIntegral ℤ x ∧ star x = x := fun x => by
    simp [L, sub_eq_zero, mem_integralClosure_iff, starRingEnd_apply]
  have hLfg : L.FG := (fg_integers E).of_le inf_le_left
  have hK : 2 * (N * M) ≠ 0 := by positivity
  obtain ⟨R, hR, -, hRL⟩ := exists_finite_residues L hLfg hK
  refine ⟨({x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C} ∪ R ∪
    {((2 * (N * M) : ℤ) : E)}) \ {0},
    (((Embeddings.finite_of_norm_le E ℂ C).union hR).union (Set.finite_singleton _)).subset
      Set.diff_subset, by simp, ?_⟩
  intro V _ _ _ h Λ hV hs hnd hfg hsp hO hint hdual
  obtain ⟨v, hv, hv0, hvC⟩ := hC V h Λ hV hs hfg hsp hO hdual
  by_cases hvv : h v v = 0
  swap
  · exact ⟨v, hv, Or.inl (Or.inl ⟨hint v hv v hv, hvC⟩), hvv⟩
  let J : Ideal (𝓞 E) :=
    { carrier := {a | ∃ x ∈ Λ, h x v = algebraMap (𝓞 E) E a}
      add_mem' := by
        rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
        exact ⟨x + y, add_mem hx hy, by simp [ha, hb]⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c a ⟨x, hx, ha⟩
        exact ⟨algebraMap (𝓞 E) E c • x, hO _ c.isIntegral_coe x hx, by
          rw [map_smul, LinearMap.smul_apply, ha, smul_eq_mul, smul_eq_mul, map_mul]⟩ }
  have hJ : ∀ x ∈ Λ, ∃ a ∈ J, algebraMap (𝓞 E) E a = h x v := fun x hx =>
    ⟨⟨h x v, hint x hx v hv⟩, ⟨x, hx, rfl⟩, rfl⟩
  have hJ0 : J ≠ ⊥ := by
    intro h0
    refine hv0 (hnd v fun x => ?_)
    have h1 : span E (Λ : Set V) ≤ LinearMap.ker (h.flip v) := span_le.2 fun y hy => by
      obtain ⟨a, ha, hay⟩ := hJ y hy
      rw [h0, Ideal.mem_bot] at ha
      rw [ha, map_zero] at hay
      exact hay.symm
    have h2 : h x v = 0 := h1 (hsp ▸ mem_top)
    rw [hs, h2, star_zero]
  obtain ⟨j, ⟨w, hw, hwj⟩, hj0, hj⟩ := hMJ J hJ0
  have hj0' : algebraMap (𝓞 E) E j ≠ 0 := fun h0 => hj0 (RingOfIntegers.ext h0)
  set v' : V := (N : E) • star ((M : E) / algebraMap (𝓞 E) E j) • v with hv'
  have hv'Λ : v' ∈ Λ := hdual _ fun x hx => by
    obtain ⟨a, ha, hax⟩ := hJ x hx
    obtain ⟨c, hc⟩ := hj _ ha
    have hc' := congrArg (algebraMap (𝓞 E) E) hc
    rw [map_mul, map_mul, map_intCast, hax] at hc'
    have : (M : E) / algebraMap (𝓞 E) E j * h x v = algebraMap (𝓞 E) E c := by
      field_simp; exact hc'
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hs x v, ← star_mul', this]
    exact isIntegral_star c.isIntegral_coe
  have h1 : h w v' = N * M := by
    simp only [hv', map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, hwj, star_intCast]
    field_simp
  have h2 : h v' w = N * M := by rw [hs, h1]; simp
  have h3 : h v' v' = 0 := by simp [hv', hvv]
  have h4 : ∀ s : E, star s = s → h (w - s • v') (w - s • v') = h w w - 2 * (N * M) * s := by
    intro s hs'
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_smulₛₗ,
      starRingEnd_apply, hs', smul_eq_mul, h1, h2, h3, RingHom.id_apply]
    ring
  obtain ⟨ρ, hρ, y, hy, hwρ⟩ := hRL (h w w) ((hL _).2 ⟨hint w hw w hw, (hs w w).symm⟩)
  obtain ⟨hyi, hys⟩ := (hL y).1 hy
  by_cases hρ0 : ρ = 0
  · refine ⟨w - (y - 1) • v', sub_mem hw (hO _ (hyi.sub isIntegral_one) _ hv'Λ), ?_⟩
    have : h (w - (y - 1) • v') (w - (y - 1) • v') = ((2 * (N * M) : ℤ) : E) := by
      rw [h4 _ (by rw [star_sub, hys, star_one]), hwρ, hρ0, zsmul_eq_mul]; push_cast; ring
    rw [this]
    exact ⟨Or.inr rfl, by simpa using hK⟩
  · refine ⟨w - y • v', sub_mem hw (hO _ hyi _ hv'Λ), ?_⟩
    have : h (w - y • v') (w - y • v') = ρ := by
      rw [h4 _ hys, hwρ, zsmul_eq_mul]; push_cast; ring
    rw [this]
    exact ⟨Or.inl (Or.inr hρ), hρ0⟩
end GlobalTheory.HermClass
