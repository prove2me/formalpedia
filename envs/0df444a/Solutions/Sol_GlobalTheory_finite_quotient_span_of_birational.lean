-- Prove2me | solution 1 for GlobalTheory.finite_quotient_span_of_birational
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:27.263493+00:00
-- url     : https://prove2.me/submissions/b974be54-4cbb-4e44-99fe-5c1c240a3983

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_isArtinianRing_quotient_of_dimensionLEOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
variable [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
namespace GlobalTheory
theorem _root_.solution
    (hB : ∀ x : B, ∃ c : A, c ≠ 0 ∧ ∃ b : A, algebraMap A B c * x = algebraMap A B b)
    {a : A} (ha : a ≠ 0) : Module.Finite A (B ⧸ Ideal.span {algebraMap A B a}) := by
  set α := algebraMap A B a with hα
  have hα0 : α ≠ 0 := by simpa [hα] using ha
  have hart : IsArtinianRing (A ⧸ Ideal.span {a}) :=
    isArtinianRing_quotient_of_dimensionLEOne (by simpa using ha)
  let J : ℕ →o (Submodule (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a}))ᵒᵈ :=
    ⟨fun n => OrderDual.toDual
      (((Ideal.span {α ^ n}).comap (algebraMap A B)).map (Ideal.Quotient.mk (Ideal.span {a}))),
      fun m n hmn => by
        apply OrderDual.toDual_le_toDual.mpr
        exact Ideal.map_mono (Ideal.comap_mono
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow α hmn)))⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes J
  let P : ℕ → B → Prop := fun h x => ∃ (u : B) (v : A), α ^ h * x = α ^ (h + 1) * u + algebraMap A B v
  have up : ∀ h x, P h x → P (h + 1) x := by
    rintro h x ⟨u, v, e⟩
    refine ⟨u, a * v, ?_⟩
    rw [map_mul, ← hα]
    linear_combination α * e
  have down : ∀ h x, n ≤ h → P (h + 1) x → P h x := by
    rintro h x hh ⟨u, v, e⟩
    have h1 : J (h + 1) = J (h + 2) := (hn _ (by omega)).symm.trans (hn _ (by omega))
    have h2 : ((Ideal.span {α ^ (h + 1)}).comap (algebraMap A B)).map
        (Ideal.Quotient.mk (Ideal.span {a})) = ((Ideal.span {α ^ (h + 2)}).comap
        (algebraMap A B)).map (Ideal.Quotient.mk (Ideal.span {a})) := OrderDual.toDual.injective h1
    have h3 : v ∈ (Ideal.span {α ^ (h + 1)}).comap (algebraMap A B) := by
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact ⟨x - α * u, by linear_combination -e⟩
    have h4 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {a})) h3
    rw [h2, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h4
    obtain ⟨w, hw, hwv⟩ := h4
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hw
    obtain ⟨z, hz⟩ := hw
    rw [eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hwv
    obtain ⟨t, ht⟩ := hwv
    have ht' := congrArg (algebraMap A B) ht
    rw [map_sub, map_mul, ← hα] at ht'
    refine ⟨u + z, t, mul_left_cancel₀ hα0 ?_⟩
    linear_combination e + ht' + hz
  have hP : ∀ x, P n x := by
    intro x
    obtain ⟨c, hc, b, hb⟩ := hB x
    have hart' : IsArtinianRing (A ⧸ Ideal.span {c}) :=
      isArtinianRing_quotient_of_dimensionLEOne (by simpa using hc)
    obtain ⟨h, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd
      (Ideal.Quotient.mk (Ideal.span {c}) a) (1 : A ⧸ Ideal.span {c})
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [smul_eq_mul, mul_one, ← map_pow, ← map_mul] at hy
    rw [eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hy
    obtain ⟨s, hs⟩ := hy
    have hs' := congrArg (algebraMap A B) hs
    simp only [map_sub, map_mul, map_pow, ← hα, Nat.succ_eq_add_one] at hs'
    have h0 : P h x := ⟨algebraMap A B r * x, b * s, by
      rw [map_mul]
      linear_combination x * hs' + algebraMap A B s * hb⟩
    have h1 : ∀ k, P (h + k) x := by
      intro k
      induction k with
      | zero => exact h0
      | succ k ih => exact up _ _ ih
    have h2 : ∀ k, P (n + k) x → P n x := by
      intro k
      induction k with
      | zero => exact id
      | succ k ih => exact fun hk => ih (down _ _ (Nat.le_add_right _ _) hk)
    exact h2 h (add_comm h n ▸ h1 n)
  let f : B →ₗ[A] B := LinearMap.mulLeft A (α ^ n)
  have hf : Function.Injective f := fun x y hxy => mul_left_cancel₀ (pow_ne_zero n hα0) hxy
  let N : Submodule A B := (Submodule.span A {(1 : B)}).comap f
  have hN : N.FG := by
    refine Submodule.fg_of_fg_map_injective f hf ?_
    exact Submodule.FG.of_le (Submodule.fg_span_singleton _) (Submodule.map_comap_le _ _)
  refine ⟨?_⟩
  have := hN.map (Ideal.Quotient.mkₐ A (Ideal.span {α})).toLinearMap
  suffices h : N.map (Ideal.Quotient.mkₐ A (Ideal.span {α})).toLinearMap = ⊤ from h ▸ this
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨u, v, e⟩ := hP x
  refine ⟨x - α * u, ?_, ?_⟩
  · change α ^ n * (x - α * u) ∈ Submodule.span A {(1 : B)}
    rw [Submodule.mem_span_singleton]
    refine ⟨v, ?_⟩
    rw [← Algebra.algebraMap_eq_smul_one]
    linear_combination -e
  · change Ideal.Quotient.mk _ _ = _
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-u, by ring⟩
end GlobalTheory
