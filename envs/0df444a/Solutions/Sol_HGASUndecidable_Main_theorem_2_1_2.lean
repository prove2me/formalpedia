-- Prove2me | solution 2 for HGASUndecidable.Main.theorem_2_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:53:03.718394+00:00
-- url     : https://prove2.me/submissions/54f76778-a629-41c5-bc42-82774dbf6baf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HGASUndecidable_Main_theorem_2_4
import Theorems.Thm_HGASUndecidable_Main_lemma_6_1
import Theorems.Thm_HGASUndecidable_Main_proposition_4_4
import Theorems.Thm_HGASUndecidable_Main_validCode_polynomialField_homogeneous
import Theorems.Thm_HGASUndecidable_Main_theorem_2_1_guarded_padding_codes

open Filter Topology MeasureTheory
open scoped BigOperators
open HGASUndecidable.Main

theorem solution (n₀ k₀ : ℕ) (hn₀ : 1 ≤ n₀) (hk₀ : 1 ≤ k₀) :
    ∀ n d : ℕ, Nat.choose (n₀+k₀-1) k₀ ≤ n → 3 ≤ d → Odd d →
      (ManyOneComplete (HGAS n₀ (2*k₀+1)) → ManyOneComplete (HGAS n d)) ∧
      (¬ComputablePred (HGAS n₀ (2*k₀+1)) → ¬ComputablePred (HGAS n d)) ∧
      (ManyOneHard (HLS n₀ (2*k₀+1)) → ManyOneHard (HLS n d)) ∧
      (¬ComputablePred (HLS n₀ (2*k₀+1)) → ¬ComputablePred (HLS n d)) := by
  intro n d hn hd hodd
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, d = 3 + 2*j := by
    obtain ⟨k, hk⟩ := hodd
    use k - 1
    omega
  obtain ⟨f, hf, hfSpec⟩ := theorem_2_4
  obtain ⟨r, hr, hrForward, hrBackward⟩ :=
    theorem_2_1_guarded_padding_codes n₀ k₀ n j hn₀ hk₀ hn f hf
  have lift_spec (c : RawFieldCode) (hcv : ValidCode c)
      (hcn : c.1 = n₀) (hcd : c.2.1 = 2*k₀+1) :
      ∃ terms : List (ℕ × List ℕ × ℚ),
        decodeField (f (Encodable.encode c)) =
          some (Nat.choose (n₀+k₀-1) k₀, 3, terms) ∧
        ValidCode (Nat.choose (n₀+k₀-1) k₀, 3, terms) ∧
        (GAS (codeField c) ↔ GAS (codeField (Nat.choose (n₀+k₀-1) k₀, 3, terms))) ∧
        (LyapunovStable (codeField c) ↔
          LyapunovStable (codeField (Nat.choose (n₀+k₀-1) k₀, 3, terms))) := by
    obtain ⟨h, hfh, hhv, hhn, hhd, hhgas, hhls⟩ :=
      hfSpec n₀ k₀ hn₀ hk₀ c hcv hcn hcd
    rcases h with ⟨hN, hD, terms⟩
    dsimp only at hhn hhd
    subst hN
    subst hD
    exact ⟨terms, hfh, hhv, hhgas, hhls⟩
  have hGAS : ManyOneReducible (HGAS n₀ (2*k₀+1)) (HGAS n (3+2*j)) := by
    refine ⟨r, hr, fun e => ⟨?_, ?_⟩⟩
    · rintro ⟨c, hc, hcv, hcn, hcd, hcgas⟩
      obtain ⟨terms, hfh, hhv, hhgas, hhls⟩ := lift_spec c hcv hcn hcd
      obtain ⟨outTerms, hrq, hqv, hqeq⟩ :=
        hrForward e c terms hc hcv hcn hcd hfh hhv
      obtain ⟨hhP, hh3⟩ := validCode_polynomialField_homogeneous _ hhv
      dsimp only at hh3
      have hpad := lemma_6_1 hn j
        (codeField (Nat.choose (n₀+k₀-1) k₀, 3, terms)) hhP hh3
      exact ⟨(n,3+2*j,outTerms), hrq, hqv, rfl, rfl,
        hqeq ▸ hpad.2.2.1.mpr (hhgas.mp hcgas)⟩
    · rintro ⟨q, hrq, hqv, hqn, hqd,hqgas⟩
      obtain ⟨c, hc, hcv, hcn, hcd⟩ := hrBackward e q hrq hqv
      obtain ⟨terms, hfh, hhv, hhgas, hhls⟩ := lift_spec c hcv hcn hcd
      obtain ⟨outTerms, hrq', hqv', hqeq⟩ :=
        hrForward e c terms hc hcv hcn hcd hfh hhv
      have hqq : (n,3+2*j,outTerms) = q := Option.some.inj (hrq'.symm.trans hrq)
      subst q
      obtain ⟨hhP, hh3⟩ := validCode_polynomialField_homogeneous _ hhv
      dsimp only at hh3
      have hpad := lemma_6_1 hn j
        (codeField (Nat.choose (n₀+k₀-1) k₀, 3, terms)) hhP hh3
      refine ⟨c, hc, hcv, hcn, hcd, hhgas.mpr ?_⟩
      apply hpad.2.2.1.mp
      rwa [← hqeq]
  have hHLS : ManyOneReducible (HLS n₀ (2*k₀+1)) (HLS n (3+2*j)) := by
    refine ⟨r, hr, fun e => ⟨?_, ?_⟩⟩
    · rintro ⟨c, hc, hcv, hcn, hcd, hcls⟩
      obtain ⟨terms, hfh, hhv, hhgas, hhls⟩ := lift_spec c hcv hcn hcd
      obtain ⟨outTerms, hrq, hqv, hqeq⟩ :=
        hrForward e c terms hc hcv hcn hcd hfh hhv
      obtain ⟨hhP, hh3⟩ := validCode_polynomialField_homogeneous _ hhv
      dsimp only at hh3
      have hpad := lemma_6_1 hn j
        (codeField (Nat.choose (n₀+k₀-1) k₀, 3, terms)) hhP hh3
      exact ⟨(n,3+2*j,outTerms), hrq, hqv, rfl, rfl,
        hqeq ▸ hpad.2.2.2.mpr (hhls.mp hcls)⟩
    · rintro ⟨q, hrq, hqv, hqn, hqd, hqls⟩
      obtain ⟨c, hc, hcv, hcn, hcd⟩ := hrBackward e q hrq hqv
      obtain ⟨terms, hfh, hhv, hhgas, hhls⟩ := lift_spec c hcv hcn hcd
      obtain ⟨outTerms, hrq', hqv', hqeq⟩ :=
        hrForward e c terms hc hcv hcn hcd hfh hhv
      have hqq : (n,3+2*j,outTerms) = q := Option.some.inj (hrq'.symm.trans hrq)
      subst q
      obtain ⟨hhP, hh3⟩ := validCode_polynomialField_homogeneous _ hhv
      dsimp only at hh3
      have hpad := lemma_6_1 hn j
        (codeField (Nat.choose (n₀+k₀-1) k₀, 3, terms)) hhP hh3
      refine ⟨c, hc, hcv, hcn, hcd, hhls.mpr ?_⟩
      apply hpad.2.2.2.mp
      rwa [← hqeq]
  have hard_transfer {S T : ℕ → Prop} (red : ManyOneReducible S T)
      (hS : ManyOneHard S) : ManyOneHard T := by
    intro A hA
    exact (hS A hA).trans red
  have noncomputable_transfer {S T : ℕ → Prop} (red : ManyOneReducible S T)
      (hS : ¬ ComputablePred S) : ¬ ComputablePred T := by
    intro hT
    apply hS
    obtain ⟨f, hf, hred⟩ := red
    obtain ⟨inst, hinst⟩ := hT
    have hpull : ComputablePred (fun e => T (f e)) :=
      ⟨fun e => inst (f e), hinst.comp hf⟩
    exact hpull.of_eq (fun e => (hred e).symm)
  exact ⟨fun h => ⟨proposition_4_4.2.1 n (3+2*j), hard_transfer hGAS h.2⟩,
    noncomputable_transfer hGAS, hard_transfer hHLS,
    noncomputable_transfer hHLS⟩
