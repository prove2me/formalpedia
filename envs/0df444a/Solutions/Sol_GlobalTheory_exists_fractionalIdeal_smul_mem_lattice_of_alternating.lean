-- Prove2me | solution 1 for GlobalTheory.exists_fractionalIdeal_smul_mem_lattice_of_alternating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:35.460615+00:00
-- url     : https://prove2.me/submissions/0bb1ed73-280d-4675-ba33-c4877841a90d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeFormIdealDualVectorIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V]
    (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0)
    (L : Set V) (h0 : (0 : V) ∈ L) (hadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L)
    (hsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (J : FractionalIdeal (𝓞 F)⁰ F) (hJ : J ≠ 0) (hBJ : ∀ z ∈ L, ∀ w ∈ L, B z w ∈ J)
    (hspan : ∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w})
    {v : V} (hv : v ≠ 0) :
    ∃ I : FractionalIdeal (𝓞 F)⁰ F, I ≠ 0 ∧ ∀ a : F, a ∈ I ↔ a • v ∈ L := by
  obtain ⟨x, hx, x', hx', hxx⟩ : ∃ x ∈ L, ∃ x' ∈ L, B x x' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hJ
    rw [FractionalIdeal.eq_zero_iff]
    intro t ht
    have h1 := hspan t ht
    have h2 : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨z, hz, w, hw, rfl⟩
      exact hcon z hz w hw
    rw [h2] at h1
    exact (Submodule.mem_bot _).1 h1
  have hli : LinearIndependent F ![x, x'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 : B (s • x + t • x') x' = 0 := by rw [hst]; simp
    have e2 : B x (s • x + t • x') = 0 := by rw [hst]; simp
    simp [hB, hxx] at e1 e2
    exact ⟨e1, e2⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hvm : v ∈ Submodule.span F ({x, x'} : Set V) := by
    have : Set.range ![x, x'] = {x, x'} := by simp [Set.pair_comm]
    rw [← this, htop]; trivial
  obtain ⟨c, c', hc⟩ := Submodule.mem_span_pair.1 hvm
  obtain ⟨t, ht0, ht⟩ : ∃ t : F, t ≠ 0 ∧ ∀ a : F, a • v ∈ L → a * t ∈ J := by
    by_cases hc0 : c = 0
    · have hc' : c' ≠ 0 := by
        rintro rfl
        apply hv
        rw [← hc, hc0]; simp
      refine ⟨B x v, ?_, fun a ha => ?_⟩
      · rw [← hc]; simp [hB, hxx, hc']
      · simpa using hBJ x hx _ ha
    · refine ⟨B v x', ?_, fun a ha => ?_⟩
      · rw [← hc]; simp [hB, hxx, hc0]
      · simpa using hBJ _ ha x' hx'
  let M : Submodule (𝓞 F) F :=
    { carrier := {a | a • v ∈ L}
      add_mem' := fun {a b} ha hb => by
        show (a + b) • v ∈ L
        rw [add_smul]; exact hadd _ ha _ hb
      zero_mem' := by
        show (0 : F) • v ∈ L
        rw [zero_smul]; exact h0
      smul_mem' := fun r a ha => by
        show ((r : F) * a) • v ∈ L
        rw [mul_smul]; exact hsmul r _ ha }
  have hM : IsFractional (𝓞 F)⁰ M := by
    apply FractionalIdeal.isFractional_of_le
      (J := FractionalIdeal.spanSingleton (𝓞 F)⁰ t⁻¹ * J)
    intro a ha
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul]
    exact ⟨a * t, ht a ha, by field_simp⟩
  refine ⟨⟨M, hM⟩, ?_, fun a => Iff.rfl⟩
  obtain ⟨d, n, hn⟩ := IsLocalization.exists_integer_multiple (𝓞 F)⁰ c
  obtain ⟨d', n', hn'⟩ := IsLocalization.exists_integer_multiple (𝓞 F)⁰ c'
  have hn1 : (n : F) = ((d : 𝓞 F) : F) * c := by
    simpa [Algebra.smul_def] using hn
  have hn2 : (n' : F) = ((d' : 𝓞 F) : F) * c' := by
    simpa [Algebra.smul_def] using hn'
  intro hz
  replace hz := FractionalIdeal.eq_zero_iff.1 hz
  have hmem : (((d : 𝓞 F) : F) * ((d' : 𝓞 F) : F)) • v ∈ L := by
    have e : (((d : 𝓞 F) : F) * ((d' : 𝓞 F) : F)) • v
        = ((d' : 𝓞 F) : F) • (n : F) • x + ((d : 𝓞 F) : F) • (n' : F) • x' := by
      rw [← hc, hn1, hn2]; module
    rw [e]
    exact hadd _ (hsmul _ _ (hsmul _ _ hx)) _ (hsmul _ _ (hsmul _ _ hx'))
  have h := hz _ hmem
  have hd : ((d : 𝓞 F) : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
  have hd' : ((d' : 𝓞 F) : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d'
  exact mul_ne_zero hd hd' h
end GlobalTheory
