-- Prove2me | solution 1 for GlobalTheory.CompleteDiscreteValuationRing.fg_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:10.55049+00:00
-- url     : https://prove2.me/submissions/8b47cca6-2976-4e61-b32d-7f3a3b684d98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrOfDimOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompleteDiscreteValuationRing
namespace GlobalTheory.CompleteDiscreteValuationRing
theorem _root_.solution {A B : Type} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (a : A) (ha : algebraMap A B a ≠ 0)
    (hart : IsArtinian A (A ⧸ Ideal.span {a}))
    (hden : ∀ x : B, ∃ (n : ℕ) (r : A), algebraMap A B a ^ n * x = algebraMap A B r)
    (J : Ideal B) (hJ : algebraMap A B a ∈ J) : J.FG := by
  set α := algebraMap A B a with hα
  let D : ℕ → Ideal A := fun n => (Ideal.span {α ^ n}).comap (algebraMap A B)
  have hD : ∀ {m n : ℕ}, m ≤ n → D n ≤ D m := fun h =>
    Ideal.comap_mono (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h))
  let E : ℕ →o (Submodule A (A ⧸ Ideal.span {a}))ᵒᵈ :=
    ⟨fun n => OrderDual.toDual (Submodule.map (Ideal.span {a}).mkQ (D n)),
      fun m n h => Submodule.map_mono (hD h)⟩
  obtain ⟨l, hl⟩ := IsArtinian.monotone_stabilizes E
  have key : ∀ n, l ≤ n → ∀ r : A, α ^ n ∣ algebraMap A B r →
      ∃ (b : B) (s : A), algebraMap A B r = α ^ (n + 1) * b + α * algebraMap A B s := by
    intro n hn r hr
    have h1 : Submodule.map (Ideal.span {a}).mkQ (D n) =
        Submodule.map (Ideal.span {a}).mkQ (D (n + 1)) :=
      (hl n hn).symm.trans (hl (n + 1) (by omega))
    have h2 : (Ideal.span {a}).mkQ r ∈ Submodule.map (Ideal.span {a}).mkQ (D n) :=
      Submodule.mem_map_of_mem (Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 hr))
    rw [h1] at h2
    obtain ⟨r', hr', e⟩ := h2
    have h3 : r - r' ∈ Ideal.span {a} := (Submodule.Quotient.eq _).1 e.symm
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.1 h3
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 (Ideal.mem_comap.1 hr')
    refine ⟨b, s, ?_⟩
    rw [← hb, hα, ← map_mul, ← hs, ← map_add]
    congr 1; ring
  have down : ∀ (x : B) (j : ℕ),
      (∃ (b : B) (r : A), α ^ (l + j) * x = α ^ (l + j + 1) * b + algebraMap A B r) →
      ∃ (b : B) (r : A), α ^ l * x = α ^ (l + 1) * b + algebraMap A B r := by
    intro x j
    induction j with
    | zero => exact id
    | succ j ih =>
      rintro ⟨b, r, h⟩
      apply ih
      obtain ⟨b', s, hs⟩ := key (l + (j + 1)) (by omega) r
        ⟨x - α * b, by rw [mul_sub, h]; ring⟩
      refine ⟨b + b', s, mul_left_cancel₀ ha ?_⟩
      rw [hs] at h
      linear_combination h
  have claim : ∀ x : B, ∃ (b : B) (r : A), α ^ l * x = α ^ (l + 1) * b + algebraMap A B r := by
    intro x
    obtain ⟨n, r, h⟩ := hden x
    refine down x n ⟨0, a ^ l * r, ?_⟩
    rw [map_mul, map_pow, ← hα, ← h]; ring
  let Q : Ideal B := Ideal.span {α ^ (l + 1)}
  let φ : B →ₗ[B] B ⧸ Q := Q.mkQ ∘ₗ LinearMap.mul B B (α ^ l)
  refine Submodule.fg_of_fg_map_of_fg_inf_ker φ ?_ ?_
  · apply Submodule.FG.of_restrictScalars A
    refine Submodule.FG.of_le (Submodule.fg_span_singleton (R := A) (1 : B ⧸ Q)) ?_
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨b, r, h⟩ := claim x
    refine Submodule.mem_span_singleton.2 ⟨r, ?_⟩
    have : φ x = Ideal.Quotient.mk Q (α ^ l * x) := rfl
    rw [this, h, map_add, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_span_singleton.2 (dvd_mul_right _ _)), zero_add, Algebra.smul_def, mul_one]
    rfl
  · have : (J : Submodule B B) ⊓ LinearMap.ker φ = Ideal.span {α} := by
      apply le_antisymm
      · rintro x ⟨-, hx⟩
        have h1 : Ideal.Quotient.mk Q (α ^ l * x) = 0 := hx
        have h2 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
        rw [pow_succ] at h2
        exact Ideal.mem_span_singleton.2 ((mul_dvd_mul_iff_left (pow_ne_zero l ha)).1 h2)
      · rw [Ideal.span_singleton_le_iff_mem]
        refine ⟨hJ, ?_⟩
        change Ideal.Quotient.mk Q (α ^ l * α) = 0
        rw [← pow_succ]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [this]
    exact Submodule.fg_span_singleton _
end GlobalTheory.CompleteDiscreteValuationRing
