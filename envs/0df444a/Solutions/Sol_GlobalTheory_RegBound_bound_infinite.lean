-- Prove2me | solution 1 for GlobalTheory.RegBound.bound_infinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:39:45.75669+00:00
-- url     : https://prove2.me/submissions/9656ff40-77d4-446c-baef-44b138b7194b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
import Theorems.Thm_GlobalTheory_RegBound_mem_sup_span
import Theorems.Thm_GlobalTheory_RegBound_exists_regular_form
import Theorems.Thm_GlobalTheory_RegBound_hom_sup_span
import Theorems.Thm_GlobalTheory_RegBound_finrank_section
import Theorems.Thm_GlobalTheory_RegBound_gen_of_section
import Theorems.Thm_GlobalTheory_RegBound_gen_top
import Theorems.Thm_GlobalTheory_RegBound_exists_saturation
import Theorems.Thm_GlobalTheory_RegBound_finrank_forms
import Theorems.Thm_GlobalTheory_RegBound_numeric
import Theorems.Thm_GlobalTheory_RegBound_piece_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution (σ : Type) [Finite σ] (k : ℕ) : ∀ q : ℕ → ℚ, ∃ d : ℕ,
    ∀ (K : Type) [Field K] [Infinite K] (I : Ideal (MvPolynomial σ K)),
      (∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) → (∀ F, (∀ i, X i * F ∈ I) → F ∈ I) →
      nmon σ 1 ≤ finrank K (piece I 1) + k →
      (∀ᶠ e in atTop, (finrank K (piece I e) : ℚ) = q e) →
      ∀ e ≥ d, (finrank K (piece I e) : ℚ) = q e ∧
        ∀ F ∈ I, F.IsHomogeneous (e + 1) → F ∈ genIn I e := by
  have htop : ∀ (K : Type) [Field K] (e : ℕ),
      finrank K (piece (⊤ : Ideal (MvPolynomial σ K)) e) = nmon σ e := by
    intro K _ e
    have : piece (⊤ : Ideal (MvPolynomial σ K)) e = homogeneousSubmodule σ K e := by simp [piece]
    rw [this, finrank_forms]
  induction k with
  | zero =>
    intro q
    have : ∃ d : ℕ, (∀ᶠ e in atTop, (nmon σ e : ℚ) = q e) → ∀ e ≥ d, (nmon σ e : ℚ) = q e := by
      by_cases h : ∀ᶠ e in atTop, (nmon σ e : ℚ) = q e
      · obtain ⟨d, hd⟩ := eventually_atTop.1 h
        exact ⟨d, fun _ => hd⟩
      · exact ⟨0, fun h' => absurd h' h⟩
    obtain ⟨d, hd⟩ := this
    refine ⟨d, fun K _ _ I _ hsat hk hq e he => ?_⟩
    have h1 : piece I 1 = homogeneousSubmodule σ K 1 :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by rwa [finrank_forms])
    have h2 : I = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      refine hsat 1 fun i => ?_
      have : X i ∈ piece I 1 := h1 ▸ isHomogeneous_X K i
      simpa using this.2
    subst h2
    simp only [htop] at hq ⊢
    exact ⟨hd hq e he, fun F _ hF => gen_top hF⟩
  | succ k ih =>
    intro q
    obtain ⟨d₀, hd₀⟩ := ih q
    obtain ⟨d₁, hd₁⟩ := ih fun e => q e + nmon σ (e - 1) - q (e - 1)
    refine ⟨max d₀ (d₁ + ⌈(nmon σ d₁ : ℚ) - q d₁⌉₊ + 1), fun K _ _ I hI hsat hk hq e he => ?_⟩
    by_cases hne : I = ⊤
    · exact hd₀ K I hI hsat (by rw [hne, htop]; omega) hq e (le_of_max_le_left he)
    obtain ⟨h, hh, hreg⟩ := exists_regular_form hsat
    obtain ⟨J', hJJ, hJ'h, hJ's, hJ'e⟩ := exists_saturation (hom_sup_span hI hh)
    have hdim := finrank_section hI hh hreg hne
    simp only [finrank_forms] at hdim
    set J := I ⊔ Ideal.span {h} with hJ
    have hhJ : h ∈ J := mem_sup_span.2 ⟨0, I.zero_mem, 1, by simp⟩
    have hlt : finrank K (piece I 1) < finrank K (piece J' 1) := by
      refine Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne (piece_mono (le_sup_left.trans hJJ) 1) fun heq => hne ?_)
      have : h ∈ piece I 1 := heq ▸ (⟨hh, hJJ hhJ⟩ : h ∈ piece J' 1)
      exact (Ideal.eq_top_iff_one _).2 (hreg 1 (by simpa using this.2))
    have hle : ∀ e, finrank K (piece J e) ≤ finrank K (piece J' e) := fun e =>
      Submodule.finrank_mono (piece_mono hJJ e)
    have hgood := hd₁ K J' hJ'h hJ's (by omega) (by
      obtain ⟨N, hN⟩ := eventually_atTop.1 hq
      filter_upwards [hJ'e, eventually_ge_atTop (N + 1)] with e h1 h2
      obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      have : piece J' (e + 1) = piece J (e + 1) :=
        le_antisymm (fun F hF => ⟨hF.1, h1 F hF.2 hF.1⟩) (piece_mono hJJ _)
      rw [this, Nat.add_sub_cancel, ← hN (e + 1) (by omega), ← hN e (by omega)]
      have := congrArg (Nat.cast : ℕ → ℚ) (hdim e)
      push_cast at this
      linarith)
    have hz : ∀ e, finrank K (piece J' e) - finrank K (piece J e) = 0 →
        genIn J' e ≤ genIn J e := by
      intro e h0
      have : piece J e = piece J' e :=
        Submodule.eq_of_le_of_finrank_le (piece_mono hJJ e) (by omega)
      refine Ideal.span_mono fun G hG => ⟨?_, hG.2⟩
      have h1 : G ∈ piece J e := this ▸ (⟨hG.2, hG.1⟩ : G ∈ piece J' e)
      exact h1.2
    have hnum := numeric (g := fun e => (finrank K (piece I e) : ℚ) - q e)
      (δ := fun e => finrank K (piece J' e) - finrank K (piece J e)) (d := d₁)
      (B := ⌈(nmon σ d₁ : ℚ) - q d₁⌉₊)
      (fun e he => by
        have h1 := (hgood (e + 1) (by omega)).1
        have h2 := congrArg (Nat.cast : ℕ → ℚ) (hdim e)
        rw [Nat.add_sub_cancel] at h1
        simp only [Nat.cast_sub (hle _)]
        push_cast at h2
        linarith)
      (hq.mono fun e he => sub_eq_zero.2 he)
      (by
        refine le_trans ?_ (Nat.le_ceil _)
        have : finrank K (piece I d₁) ≤ nmon σ d₁ := by
          rw [← finrank_forms (K := K)]
          exact Submodule.finrank_mono inf_le_left
        have : (finrank K (piece I d₁) : ℚ) ≤ nmon σ d₁ := by exact_mod_cast this
        linarith)
      (fun e he h0 => by
        refine Nat.sub_eq_zero_of_le (Submodule.finrank_mono fun F hF => ⟨hF.1, ?_⟩)
        exact (Ideal.span_le.2 fun G hG => hG.1 : genIn J e ≤ J)
          (hz e h0 ((hgood e he).2 F hF.2 hF.1)))
      e (le_of_max_le_right he)
    refine ⟨sub_eq_zero.1 hnum.2, fun F hF hFe => gen_of_section hI hh hreg hF hFe ?_⟩
    have he' : d₁ ≤ e := by have := le_of_max_le_right he; omega
    exact hz e hnum.1 ((hgood e he').2 F (hJJ (Ideal.mem_sup_left hF)) hFe)
end GlobalTheory.RegBound
