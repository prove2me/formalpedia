-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:54:17.762554+00:00
-- url     : https://prove2.me/submissions/14b3280b-b0b8-469c-b134-b039a45d7361

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_GlobalTheory_AdaptedChain_tan_eq
import Theorems.Thm_GlobalTheory_AdaptedChain_stepA
import Theorems.Thm_GlobalTheory_AdaptedChain_stepB
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {X : Cart V d I J}
namespace GlobalTheory.AdaptedChain
theorem _root_.solution [IsAlgClosed C] (j' : ℕ) (K : ℕ) : (∀ s, 0 < s → s < K → ((2 * s : ℕ) : ZMod d) ≠ 0) →
    ∀ (a : ZMod d), (∀ s < K, (Finset.univ.filter fun k =>
      X.ty (Sum.inl k) = a + ((2 * s : ℕ) : ZMod d) + 1).card ≤ j') →
    ∀ (S : Sys X) (Q : Finset I), (∀ c ∈ Q, X.ty (Sum.inl c) = a) →
    ∀ (L : AddSubgroup (I → C)), Stable V L → (∀ c ∈ Q, S.tan c ∈ L) →
    ∃ (S' : Sys X) (lev : I → ℕ),
      (∀ c, (∀ s < K, X.ty (Sum.inl c) ≠ a + ((2 * s : ℕ) : ZMod d)) → S'.cur c = S.cur c) ∧
      (∀ c, lev c < K → X.ty (Sum.inl c) = a + ((2 * lev c : ℕ) : ZMod d) ∧
        ∀ k, S'.cur c 1 (Sum.inl k) = 0) ∧
      (∀ c ∈ Q, lev c = 0 → S'.tan c ∈ L) ∧
      Q.card ≤ (Q.filter fun c => lev c = 0).card + K * j' ∧
      ∀ c, lev c + 1 < K → ∃ g lam : I → C, (∀ e, V.Ge 0 (g e)) ∧ (∀ e, V.Ge 0 (lam e)) ∧
        (∀ e, lev e ≠ lev c + 1 → g e = 0) ∧
        ∀ k, (V.l : C) * S'.cur c 2 (Sum.inl k) = ∑ e, g e * S'.tan e k + (V.l : C) * lam k := by
  induction K with
  | zero =>
    intro _ a _ S Q _ L _ hQL
    exact ⟨S, fun _ => 0, fun _ _ => rfl, by simp, fun c hc _ => hQL c hc, by simp, by simp⟩
  | succ K ih =>
    intro hd a hsm S Q hQ L hL hQL
    have hsh : ∀ s : ℕ, a + 2 + ((2 * s : ℕ) : ZMod d) = a + ((2 * (s + 1) : ℕ) : ZMod d) := by
      intro s; push_cast; ring
    have hne : ∀ s < K, a + 2 + ((2 * s : ℕ) : ZMod d) ≠ a := by
      intro s hs h
      rw [hsh] at h
      exact hd (s + 1) (by omega) (by omega) (by simpa using h)
    set T := Finset.univ.filter fun k => X.ty (Sum.inl k) = a + 2 with hT
    obtain ⟨S1, lev, p1, p2, -, p4, p5⟩ := ih (fun s h1 h2 => hd s h1 (by omega)) (a + 2)
      (fun s hs => by rw [hsh]; exact hsm (s + 1) (by omega)) S T (fun c hc => by simpa [hT] using hc)
      ⊤ (fun _ _ _ _ => trivial) (fun _ _ => trivial)
    have hS1 : ∀ c ∈ Q, S1.cur c = S.cur c := fun c hc =>
      p1 c fun s hs => by rw [hQ c hc]; exact (hne s hs).symm
    have hnQ : ∀ c, lev c < K → c ∉ Q := fun c hc hh => hne _ hc (by rw [← (p2 c hc).1, hQ c hh])
    obtain ⟨S2, Q2, q1, q2, q3, q4, q5⟩ := stepA S1 a Q hQ L hL
      (fun c hc => by rw [tan_eq (hS1 c hc)]; exact hQL c hc)
    obtain ⟨S3, Q3, r1, r2, r3, r4, r5, r6⟩ := stepB S2 a Q2 (fun c hc => hQ c (q1 hc)) L hL
      (fun c hc => q4 c (q1 hc)) q5 (T.filter fun c => ¬ lev c = 0)
    have h31 : ∀ c, c ∉ Q → S3.cur c = S1.cur c := fun c hc => by
      rw [r3 c (fun hh => hc (q1 hh)), q3 c hc]
    have hQ3 : ∀ c ∈ Q3, c ∈ Q := fun c hc => q1 (r1 hc)
    refine ⟨S3, fun c => if c ∈ Q3 then 0 else lev c + 1, fun c hc => ?_, fun c hc => ?_,
      fun c hc h0 => ?_, ?_, fun c hc => ?_⟩
    · rw [h31 c (fun hh => hc 0 (by omega) (by simpa using hQ c hh))]
      exact p1 c fun s hs => by rw [hsh]; exact hc (s + 1) (by omega)
    · by_cases h : c ∈ Q3
      · simp only [if_pos h]
        exact ⟨by simpa using hQ c (hQ3 c h), r5 c (r1 h)⟩
      · simp only [if_neg h] at hc ⊢
        have hc' : lev c < K := by omega
        rw [h31 c (hnQ c hc'), ← hsh]
        exact p2 c hc'
    · by_cases h : c ∈ Q3
      · exact r4 c (r1 h)
      · simp [h] at h0
    · have e1 : Q3.card ≤ (Q.filter fun c => (if c ∈ Q3 then 0 else lev c + 1) = 0).card :=
        Finset.card_le_card fun c hc => by simp [hc, hQ3 c hc]
      have e2 := Finset.card_filter_add_card_filter_not (s := T) (fun c => lev c = 0)
      have e3 := hsm 0 (by omega)
      simp only [mul_zero, Nat.cast_zero, add_zero] at e3
      rw [Nat.succ_mul]
      beta_reduce
      omega
    · by_cases h : c ∈ Q3
      · simp only [if_pos h] at hc ⊢
        obtain ⟨g, lam, g1, g2, g3, g4⟩ := r6 c h
        have hg : ∀ e, g e ≠ 0 → e ∉ Q ∧ lev e = 0 := by
          intro e he
          obtain ⟨t1, t2⟩ := g3 e he
          have t3 : lev e = 0 := by
            by_contra hh; exact t2 (by simp [hT, t1, hh])
          exact ⟨hnQ e (by omega), t3⟩
        refine ⟨g, lam, g1, g2, fun e he => ?_, fun k => ?_⟩
        · by_contra hh
          obtain ⟨t1, t2⟩ := hg e hh
          apply he
          rw [if_neg (fun h3 => t1 (hQ3 e h3)), t2]
        · rw [g4]
          congr 1
          refine Finset.sum_congr rfl fun e _ => ?_
          by_cases hh : g e = 0
          · simp [hh]
          · rw [tan_eq (r3 e fun h2 => (hg e hh).1 (q1 h2))]
      · simp only [if_neg h] at hc ⊢
        obtain ⟨g, lam, g1, g2, g3, g4⟩ := p5 c (by omega)
        have hg : ∀ e, g e ≠ 0 → e ∉ Q ∧ lev e = lev c + 1 := by
          intro e he
          have t3 : lev e = lev c + 1 := by
            by_contra hh; exact he (g3 e hh)
          exact ⟨hnQ e (by omega), t3⟩
        refine ⟨g, lam, g1, g2, fun e he => ?_, fun k => ?_⟩
        · by_contra hh
          obtain ⟨t1, t2⟩ := hg e hh
          apply he
          rw [if_neg (fun h3 => t1 (hQ3 e h3)), t2]
        · rw [h31 c (hnQ c (by omega)), g4]
          congr 1
          refine Finset.sum_congr rfl fun e _ => ?_
          by_cases hh : g e = 0
          · simp [hh]
          · rw [tan_eq (h31 e (hg e hh).1)]
end GlobalTheory.AdaptedChain
