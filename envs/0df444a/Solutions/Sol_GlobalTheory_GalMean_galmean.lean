-- Prove2me | solution 1 for GlobalTheory.GalMean.galmean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:46.420407+00:00
-- url     : https://prove2.me/submissions/641db5d3-a1ef-4584-8fb4-037f9910f217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeanLogNormConjugatesOverIdealClasses
import Theorems.Thm_GlobalTheory_GalMean_exists_field
import Theorems.Thm_GlobalTheory_GalMean_sum_log_emb
import Theorems.Thm_GlobalTheory_GalMean_sum_halve
import Theorems.Thm_GlobalTheory_GalMean_cover
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.GalMean
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
namespace GlobalTheory.GalMean
theorem _root_.solution : ∀ {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (j₀ : ℂ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (β : ℂ) (F : (ℂ ≃+* ℂ) → ℝ), Module.finrank ℚ K = 2 → (starRingEnd ℂ).comp φK ≠ φK →
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Equidistributed φK j₀ 𝔞 → IsAlgebraic ℚ β → β ≠ 0 →
    (∀ σ σ' : ℂ ≃+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ' →
      ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') → F σ = F σ') →
    (∀ σ : ℂ ≃+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → Real.log ‖σ β‖ ≤ F σ) →
    ∃ rep : ClassGroup (𝓞 K) → (ℂ ≃+* ℂ), (∀ c, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK (rep c) ∧ ClassGroup.mk K (𝔞 (rep c)) = c) ∧
      Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| ≤
        (minpoly ℚ β).natDegree * ((∑ c, F (rep c)) / (NumberField.classNumber K : ℝ)) := by
  intro K _ _ φK j₀ 𝔞 β F hK2 hc hE hβa hβ0 hFc hFb
  classical
  obtain ⟨L, hLf, hLg, hK, hj, hβ⟩ := exists_field φK j₀ β hE.1 hβa
  haveI : NumberField L := ⟨⟩
  set Fx := Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x) with hFx
  have hcard : 2 * Fx.card = Module.finrank ℚ L := by
    have := sum_halve φK hK2 hc L hK (fun _ => (1 : ℝ)) (fun _ => rfl)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, NumberField.Embeddings.card] at this
    exact_mod_cast this.symm
  obtain ⟨ext, hext, hcnt⟩ := cover φK j₀ 𝔞 hE L hK hj hcard
  have hn : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hh : 0 < classNumber K := Fintype.card_pos
  have hrep : ∀ C : ClassGroup (𝓞 K), ∃ σ, Fixes φK σ ∧ ClassGroup.mk K (𝔞 σ) = C := by
    intro C
    have h1 := hcnt C
    obtain ⟨τ, hτ⟩ : (Fx.filter (fun τ => ClassGroup.mk K (𝔞 (ext τ)) = C)).Nonempty := by
      rw [← Finset.card_pos]
      by_contra h0
      rw [Nat.eq_zero_of_not_pos h0, zero_mul] at h1
      omega
    rw [Finset.mem_filter] at hτ
    exact ⟨ext τ, (hext τ hτ.1).1, hτ.2⟩
  choose rep hrepP using hrep
  refine ⟨rep, fun C => hrepP C, ?_⟩
  obtain ⟨m, hm, hdeg, hsum⟩ := sum_log_emb L β hβ hβ0
  set b : L := ⟨β, hβ⟩
  set cls : (L →+* ℂ) → ClassGroup (𝓞 K) := fun τ => ClassGroup.mk K (𝔞 (ext τ))

  have hb : ∀ τ ∈ Fx, Real.log ‖τ b‖ ≤ F (rep (cls τ)) := by
    intro τ hτ
    have e : ext τ β = τ b := (hext τ hτ).2 b
    rw [← e]
    refine (hFb _ (hext τ hτ).1).trans (le_of_eq ?_)
    exact hFc _ _ (hext τ hτ).1 (hrepP _).1 (hrepP _).2.symm
  have hhalf := sum_halve φK hK2 hc L hK (fun τ => Real.log ‖τ b‖) (fun τ => by simp)
  set k : ClassGroup (𝓞 K) → ℕ := fun C => (Fx.filter (fun τ => cls τ = C)).card
  have hfib : ∑ τ ∈ Fx, F (rep (cls τ)) = ∑ C, (k C : ℝ) * F (rep C) := by
    rw [← Finset.sum_fiberwise Fx cls (fun τ => F (rep (cls τ)))]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finset.sum_congr rfl (fun τ hτ => by rw [(Finset.mem_filter.1 hτ).2]), Finset.sum_const, nsmul_eq_mul]
  have hk : ∀ C, (2 : ℝ) * k C = m * (minpoly ℚ β).natDegree / classNumber K := by
    intro C
    have := hcnt C
    rw [hdeg] at this
    have hhr : (classNumber K : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    rw [eq_div_iff hhr]
    have : ((k C * (2 * classNumber K) : ℕ) : ℝ) = ((m * (minpoly ℚ β).natDegree : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at this
    linarith
  have hmain : (m : ℝ) * Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| ≤
      m * ((minpoly ℚ β).natDegree * ((∑ c, F (rep c)) / (classNumber K : ℝ))) := by
    rw [← hsum, hhalf]
    calc 2 * ∑ τ ∈ Fx, Real.log ‖τ b‖ ≤ 2 * ∑ τ ∈ Fx, F (rep (cls τ)) := by
          gcongr with τ hτ; exact hb τ hτ
      _ = ∑ C, (2 * (k C : ℝ)) * F (rep C) := by
          rw [hfib, Finset.mul_sum]; refine Finset.sum_congr rfl fun C _ => by ring
      _ = ∑ C, (m * (minpoly ℚ β).natDegree / classNumber K) * F (rep C) := by
          refine Finset.sum_congr rfl fun C _ => by rw [hk C]
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  exact le_of_mul_le_mul_left hmain hm'
end GlobalTheory.GalMean
