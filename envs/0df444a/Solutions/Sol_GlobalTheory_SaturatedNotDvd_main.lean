-- Prove2me | solution 1 for GlobalTheory.SaturatedNotDvd.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:48:06.93047+00:00
-- url     : https://prove2.me/submissions/870a227c-98cd-480f-8bd7-4d2413feb3fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSaturated
import Theorems.Thm_GlobalTheory_SaturatedNotDvd_exists_saturated
import Theorems.Thm_GlobalTheory_SaturatedNotDvd_exists_not_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.SaturatedNotDvd
namespace GlobalTheory.SaturatedNotDvd
theorem _root_.solution : (let d1 : (A : Type u_1) → [CommRing A] → Prop := @(fun (A : Type u_1) [CommRing A] ↦ ∀ (a b : A) (I : Ideal A), b ≠ (0 : A) → I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a); ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] {x : A}, Prime x → d1 (A ⧸ Ideal.span {x}) → ∀ {a b : A}, ¬x ∣ b → ∀ {I : Ideal A}, I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a) := by
  intro d1 A _ _ _ _ x hx hd a b hb I hI h
  have hd' : ∀ (a b : A ⧸ Ideal.span {x}) (I : Ideal (A ⧸ Ideal.span {x})), b ≠ 0 → I ≠ ⊥ →
      (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a := hd
  obtain ⟨K, hK, hsat, hKa⟩ := exists_saturated hx hb hI h
  obtain ⟨u₀, hu₀, hxu⟩ := exists_not_dvd hx.not_unit hK hsat
  have hz : ∀ y : A, Ideal.Quotient.mk (Ideal.span {x}) y = 0 ↔ x ∣ y := fun y => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have step : ∀ a : A, (∀ r ∈ K, ∃ s ∈ K, a * r = b * s) →
      ∃ c d : A, a = b * c + x * d ∧ ∀ r ∈ K, ∃ s ∈ K, d * r = b * s := by
    intro a ha
    have hdiv : Ideal.Quotient.mk (Ideal.span {x}) b ∣ Ideal.Quotient.mk (Ideal.span {x}) a := by
      refine hd' _ _ (K.map (Ideal.Quotient.mk (Ideal.span {x}))) (fun h0 => hb ((hz b).1 h0)) ?_ ?_
      · intro hbot
        have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {x})) hu₀
        rw [hbot, Ideal.mem_bot] at hm
        exact hxu ((hz _).1 hm)
      · intro r hr
        obtain ⟨r', hr', rfl⟩ :=
          (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hr
        obtain ⟨s, hs, hrs⟩ := ha r' hr'
        exact ⟨_, Ideal.mem_map_of_mem _ hs, by rw [← map_mul, ← map_mul, hrs]⟩
    obtain ⟨c', hc'⟩ := hdiv
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
    have hxd : x ∣ a - b * c := (hz _).1 (by rw [map_sub, map_mul, hc', sub_self])
    obtain ⟨d, hdd⟩ := hxd
    refine ⟨c, d, by linear_combination hdd, ?_⟩
    intro r hr
    obtain ⟨s, hs, hrs⟩ := ha r hr
    have h1 : b * (s - c * r) = x * (d * r) := by linear_combination r * hdd - hrs
    have h2 : x ∣ s - c * r := (hx.dvd_or_dvd ⟨_, h1⟩).resolve_left hb
    obtain ⟨w, hw⟩ := h2
    have hwK : w ∈ K := hsat w (hw ▸ K.sub_mem hs (K.mul_mem_left c hr))
    refine ⟨w, hwK, ?_⟩
    apply mul_left_cancel₀ hx.ne_zero
    rw [← h1, hw]; ring
  have iter : ∀ n : ℕ, ∀ a : A, (∀ r ∈ K, ∃ s ∈ K, a * r = b * s) →
      ∃ c y : A, a = b * c + x ^ n * y := by
    intro n
    induction n with
    | zero => intro a _; exact ⟨0, a, by simp⟩
    | succ n ih =>
      intro a ha
      obtain ⟨c, d, rfl, hd2⟩ := step a ha
      obtain ⟨c', y, rfl⟩ := ih d hd2
      exact ⟨c + x * c', y, by ring⟩
  have hne : Ideal.span {x} ≠ ⊤ := fun h => hx.not_unit (Ideal.span_singleton_eq_top.1 h)
  have hk := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ Ideal.span {b})
    (Ideal.span {x}) hne
  have hmem : Ideal.Quotient.mk (Ideal.span {b}) a ∈
      (⨅ i : ℕ, Ideal.span {x} ^ i • ⊤ : Submodule A (A ⧸ Ideal.span {b})) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨c, y, hcy⟩ := iter n a hKa
    have : Ideal.Quotient.mk (Ideal.span {b}) a
        = x ^ n • Ideal.Quotient.mk (Ideal.span {b}) y := by
      change _ = Ideal.Quotient.mk (Ideal.span {b}) (x ^ n * y)
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact ⟨c, by rw [hcy]; ring⟩
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self x) n)
      Submodule.mem_top
  rw [hk, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmem
  exact hmem
end GlobalTheory.SaturatedNotDvd
