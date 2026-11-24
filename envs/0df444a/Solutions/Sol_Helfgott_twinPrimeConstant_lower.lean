-- Prove2me | solution 1 for Helfgott.twinPrimeConstant_lower
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T01:22:56.362982+00:00
-- url     : https://prove2.me/submissions/9f7986f7-2355-4f66-bcf8-8ef4ccaa4f4b

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Explicit lower bound with finite kernel certificates and a proved full tail. Written by Codex. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open scoped BigOperators
open Finset

namespace Helfgott

noncomputable def twinLocal (p : ℕ) : ℝ :=
  if Nat.Prime p ∧ 2 < p then 1-1/((p:ℝ)-1)^2 else 1

lemma twinLocal_nonneg (p : ℕ) : 0 ≤ twinLocal p := by
  unfold twinLocal
  split_ifs with hp
  · have hp3 : (3:ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
    have hs : 1 ≤ ((p:ℝ)-1)^2 := by nlinarith
    have hdpos : (0:ℝ) < ((p:ℝ)-1)^2 := by linarith
    have hi : 1/((p:ℝ)-1)^2 ≤ (1:ℝ) := (div_le_one hdpos).2 hs
    linarith
  · norm_num

lemma twinLocal_le_one (p : ℕ) : twinLocal p ≤ 1 := by
  unfold twinLocal
  split_ifs with hp
  · exact sub_le_self _ (by positivity)
  · norm_num

lemma twinPrimePartial_eq_local (Q : ℕ) :
    TaoFivePrimes.twinPrimePartial Q = ∏ p ∈ range (Q+1), twinLocal p := rfl

lemma twinPrimePartial_nonneg (Q : ℕ) : 0 ≤ TaoFivePrimes.twinPrimePartial Q := by
  rw [twinPrimePartial_eq_local]
  exact prod_nonneg fun p _ => twinLocal_nonneg p

lemma twinPrimePartial_le_one (Q : ℕ) : TaoFivePrimes.twinPrimePartial Q ≤ 1 := by
  rw [twinPrimePartial_eq_local]
  exact prod_le_one (fun p _ => twinLocal_nonneg p) (fun p _ => twinLocal_le_one p)

lemma twinPrimePartial_antitone : Antitone TaoFivePrimes.twinPrimePartial := by
  intro a b hab
  simp only [twinPrimePartial_eq_local]
  exact prod_le_prod_of_subset_of_le_one (range_mono (Nat.add_le_add_right hab 1))
    (fun p _ => twinLocal_nonneg p) (fun p _ _ => twinLocal_le_one p)

end Helfgott

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators
open Finset

namespace Helfgott

noncomputable def twinRaw (p : ℕ) : ℝ := 1-1/((p:ℝ)-1)^2

def primeBlock0 : List ℕ := [3,5,7,11,13,17,19,23,29,31,37,41]
def primeBlock1 : List ℕ := [43,47,53,59,61,67,71,73,79,83,89,97]
def primeBlock2 : List ℕ := [101,103,107,109,113,127,131,137,139,149,151,157]
def primeBlock3 : List ℕ := [163,167,173,179,181,191,193,197,199,211,223,227]
def primeBlock4 : List ℕ := [229,233,239,241,251,257,263,269,271,277,281,283]
def primeBlock5 : List ℕ := [293,307,311,313,317,331,337,347,349,353,359,367]
def primeBlock6 : List ℕ := [373,379,383,389,397,401,409,419,421,431,433,439]
def primeBlock7 : List ℕ := [443,449,457,461,463,467,479,487,491,499,503,509]
def primeBlock8 : List ℕ := [521,523,541,547,557,563,569,571,577,587,593,599]
def primeBlock9 : List ℕ := [601,607,613,617,619,631,641,643,647,653,659,661]
def primeBlock10 : List ℕ := [673,677,683,691,701,709,719,727,733,739,743,751]
def primeBlock11 : List ℕ := [757,761,769,773,787,797,809,811,821,823,827,829]
def primeBlock12 : List ℕ := [839,853,857,859,863,877,881,883,887,907,911,919]
def primeBlock13 : List ℕ := [929,937,941,947,953,967,971,977,983,991,997]

def certifiedPrimeList : List ℕ := (((((((((((((primeBlock0 ++ primeBlock1) ++ primeBlock2) ++ primeBlock3) ++ primeBlock4) ++ primeBlock5) ++ primeBlock6) ++ primeBlock7) ++ primeBlock8) ++ primeBlock9) ++ primeBlock10) ++ primeBlock11) ++ primeBlock12) ++ primeBlock13)

lemma primeCoverage0 (j : Fin 64) :
    0+j.val ≤ 2 ∨ 0+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 0+j.val ∧ d.val ∣ 0+j.val := by
  revert j
  decide

lemma primeCoverage1 (j : Fin 64) :
    64+j.val ≤ 2 ∨ 64+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 64+j.val ∧ d.val ∣ 64+j.val := by
  revert j
  decide

lemma primeCoverage2 (j : Fin 64) :
    128+j.val ≤ 2 ∨ 128+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 128+j.val ∧ d.val ∣ 128+j.val := by
  revert j
  decide

lemma primeCoverage3 (j : Fin 64) :
    192+j.val ≤ 2 ∨ 192+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 192+j.val ∧ d.val ∣ 192+j.val := by
  revert j
  decide

lemma primeCoverage4 (j : Fin 64) :
    256+j.val ≤ 2 ∨ 256+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 256+j.val ∧ d.val ∣ 256+j.val := by
  revert j
  decide

lemma primeCoverage5 (j : Fin 64) :
    320+j.val ≤ 2 ∨ 320+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 320+j.val ∧ d.val ∣ 320+j.val := by
  revert j
  decide

lemma primeCoverage6 (j : Fin 64) :
    384+j.val ≤ 2 ∨ 384+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 384+j.val ∧ d.val ∣ 384+j.val := by
  revert j
  decide

lemma primeCoverage7 (j : Fin 64) :
    448+j.val ≤ 2 ∨ 448+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 448+j.val ∧ d.val ∣ 448+j.val := by
  revert j
  decide

lemma primeCoverage8 (j : Fin 64) :
    512+j.val ≤ 2 ∨ 512+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 512+j.val ∧ d.val ∣ 512+j.val := by
  revert j
  decide

lemma primeCoverage9 (j : Fin 64) :
    576+j.val ≤ 2 ∨ 576+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 576+j.val ∧ d.val ∣ 576+j.val := by
  revert j
  decide

lemma primeCoverage10 (j : Fin 64) :
    640+j.val ≤ 2 ∨ 640+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 640+j.val ∧ d.val ∣ 640+j.val := by
  revert j
  decide

lemma primeCoverage11 (j : Fin 64) :
    704+j.val ≤ 2 ∨ 704+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 704+j.val ∧ d.val ∣ 704+j.val := by
  revert j
  decide

lemma primeCoverage12 (j : Fin 64) :
    768+j.val ≤ 2 ∨ 768+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 768+j.val ∧ d.val ∣ 768+j.val := by
  revert j
  decide

lemma primeCoverage13 (j : Fin 64) :
    832+j.val ≤ 2 ∨ 832+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 832+j.val ∧ d.val ∣ 832+j.val := by
  revert j
  decide

lemma primeCoverage14 (j : Fin 64) :
    896+j.val ≤ 2 ∨ 896+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 896+j.val ∧ d.val ∣ 896+j.val := by
  revert j
  decide

lemma primeCoverage15 (j : Fin 48) :
    960+j.val ≤ 2 ∨ 960+j.val ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < 960+j.val ∧ d.val ∣ 960+j.val := by
  revert j
  decide

lemma certifiedPrimeList_complete (p : ℕ) (hp : p < 1008)
    (hprime : Nat.Prime p) (h2 : 2 < p) : p ∈ certifiedPrimeList := by
  have hcover : p ≤ 2 ∨ p ∈ certifiedPrimeList ∨
      ∃ d : Fin 32, 1 < d.val ∧ d.val < p ∧ d.val ∣ p := by
    by_cases h0 : p < 64
    · have hh := primeCoverage0 ⟨p-0,by omega⟩
      have he : 0+(p-0) = p := by omega
      simpa only [he] using hh
    ·
      by_cases h1 : p < 128
      · have hh := primeCoverage1 ⟨p-64,by omega⟩
        have he : 64+(p-64) = p := by omega
        simpa only [he] using hh
      ·
        by_cases h2 : p < 192
        · have hh := primeCoverage2 ⟨p-128,by omega⟩
          have he : 128+(p-128) = p := by omega
          simpa only [he] using hh
        ·
          by_cases h3 : p < 256
          · have hh := primeCoverage3 ⟨p-192,by omega⟩
            have he : 192+(p-192) = p := by omega
            simpa only [he] using hh
          ·
            by_cases h4 : p < 320
            · have hh := primeCoverage4 ⟨p-256,by omega⟩
              have he : 256+(p-256) = p := by omega
              simpa only [he] using hh
            ·
              by_cases h5 : p < 384
              · have hh := primeCoverage5 ⟨p-320,by omega⟩
                have he : 320+(p-320) = p := by omega
                simpa only [he] using hh
              ·
                by_cases h6 : p < 448
                · have hh := primeCoverage6 ⟨p-384,by omega⟩
                  have he : 384+(p-384) = p := by omega
                  simpa only [he] using hh
                ·
                  by_cases h7 : p < 512
                  · have hh := primeCoverage7 ⟨p-448,by omega⟩
                    have he : 448+(p-448) = p := by omega
                    simpa only [he] using hh
                  ·
                    by_cases h8 : p < 576
                    · have hh := primeCoverage8 ⟨p-512,by omega⟩
                      have he : 512+(p-512) = p := by omega
                      simpa only [he] using hh
                    ·
                      by_cases h9 : p < 640
                      · have hh := primeCoverage9 ⟨p-576,by omega⟩
                        have he : 576+(p-576) = p := by omega
                        simpa only [he] using hh
                      ·
                        by_cases h10 : p < 704
                        · have hh := primeCoverage10 ⟨p-640,by omega⟩
                          have he : 640+(p-640) = p := by omega
                          simpa only [he] using hh
                        ·
                          by_cases h11 : p < 768
                          · have hh := primeCoverage11 ⟨p-704,by omega⟩
                            have he : 704+(p-704) = p := by omega
                            simpa only [he] using hh
                          ·
                            by_cases h12 : p < 832
                            · have hh := primeCoverage12 ⟨p-768,by omega⟩
                              have he : 768+(p-768) = p := by omega
                              simpa only [he] using hh
                            ·
                              by_cases h13 : p < 896
                              · have hh := primeCoverage13 ⟨p-832,by omega⟩
                                have he : 832+(p-832) = p := by omega
                                simpa only [he] using hh
                              ·
                                by_cases h14 : p < 960
                                · have hh := primeCoverage14 ⟨p-896,by omega⟩
                                  have he : 896+(p-896) = p := by omega
                                  simpa only [he] using hh
                                ·
                                  have hh := primeCoverage15 ⟨p-960,by omega⟩
                                  have he : 960+(p-960) = p := by omega
                                  simpa only [he] using hh
  rcases hcover with hsmall | hmem | ⟨d,hd1,hdp,hdvd⟩
  · omega
  · exact hmem
  · rcases hprime.eq_one_or_self_of_dvd d.val hdvd with he | he <;> omega

lemma certifiedPrimeList_bounds : ∀ p ∈ certifiedPrimeList, 3 ≤ p ∧ p < 1008 := by
  decide

lemma certifiedPrimeList_nodup : certifiedPrimeList.Nodup := by decide

lemma twinRaw_le_local (p : ℕ) : twinRaw p ≤ twinLocal p := by
  unfold twinRaw twinLocal
  split_ifs
  · rfl
  · exact sub_le_self _ (by positivity)

lemma twinRaw_nonneg_of_three_le (p : ℕ) (hp : 3 ≤ p) : 0 ≤ twinRaw p := by
  have hpR : (3:ℝ) ≤ p := by exact_mod_cast hp
  have hs : (1:ℝ) ≤ ((p:ℝ)-1)^2 := by nlinarith
  have hpos : (0:ℝ) < ((p:ℝ)-1)^2 := by linarith
  have hi : 1/((p:ℝ)-1)^2 ≤ (1:ℝ) := (div_le_one hpos).2 hs
  unfold twinRaw
  linarith

lemma certified_raw_product_lower :
    (16506/25000:ℝ) ≤ (certifiedPrimeList.map twinRaw).prod := by
  have h0 : (663471770761/1000000000000:ℝ) ≤ (primeBlock0.map twinRaw).prod := by
    norm_num [primeBlock0,twinRaw]
  have ha0 : (663471770761/1000000000000:ℝ) ≤ (primeBlock0.map twinRaw).prod := h0
  have h1 : (996842840483/1000000000000:ℝ) ≤ (primeBlock1.map twinRaw).prod := by
    norm_num [primeBlock1,twinRaw]
  have ha1 : (661377084545/1000000000000:ℝ) ≤ ((primeBlock0.map twinRaw).prod)*(primeBlock1.map twinRaw).prod := by
    calc
      _ ≤ (663471770761/1000000000000:ℝ)*(996842840483/1000000000000:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul ha0 h1 (by norm_num) (by linarith [ha0])
  have h2 : (999189803641/1000000000000:ℝ) ≤ (primeBlock2.map twinRaw).prod := by
    norm_num [primeBlock2,twinRaw]
  have ha2 : (660841239239/1000000000000:ℝ) ≤ (((primeBlock0.map twinRaw).prod)*(primeBlock1.map twinRaw).prod)*(primeBlock2.map twinRaw).prod := by
    calc
      _ ≤ (661377084545/1000000000000:ℝ)*(999189803641/1000000000000:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul ha1 h2 (by norm_num) (by linarith [ha1])
  have h3 : (999660520073/1000000000000:ℝ) ≤ (primeBlock3.map twinRaw).prod := by
    norm_num [primeBlock3,twinRaw]
  have ha3 : (660616896903/1000000000000:ℝ) ≤ ((((primeBlock0.map twinRaw).prod)*(primeBlock1.map twinRaw).prod)*(primeBlock2.map twinRaw).prod)*(primeBlock3.map twinRaw).prod := by
    calc
      _ ≤ (660841239239/1000000000000:ℝ)*(999660520073/1000000000000:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul ha2 h3 (by norm_num) (by linarith [ha2])
  have h4 : (999815260156/1000000000000:ℝ) ≤ (primeBlock4.map twinRaw).prod := by
    norm_num [primeBlock4,twinRaw]
  have ha4 : (660494854640/1000000000000:ℝ) ≤ (((((primeBlock0.map twinRaw).prod)*(primeBlock1.map twinRaw).prod)*(primeBlock2.map twinRaw).prod)*(primeBlock3.map twinRaw).prod)*(primeBlock4.map twinRaw).prod := by
    calc
      _ ≤ (660616896903/1000000000000:ℝ)*(999815260156/1000000000000:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul ha3 h4 (by norm_num) (by linarith [ha3])
  have h5 : (999888915299/1000000000000:ℝ) ≤ (primeBlock5.map twinRaw).prod := by
    norm_num [primeBlock5,twinRaw]
  have ha5 : (660421483766/1000000000000:ℝ) ≤ ((((((primeBlock0.map twinRaw).prod)*(primeBlock1.map twinRaw).prod)*(primeBlock2.map twinRaw).prod)*(primeBlock3.map twinRaw).prod)*(primeBlock4.map twinRaw).prod)*(primeBlock5.map twinRaw).prod := by
    calc
      _ ≤ (660494854640/1000000000000:ℝ)*(999888915299/1000000000000:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul ha4 h5 (by norm_num) (by linarith [ha4])
  have h6 : (999926276360/1000000000000:ℝ) ≤ (primeBlock6.map twinRaw).prod := by
    norm_num [primeBlock6,twinRaw]
  have ha6 : (660372795090/1000000000000:ℝ) ≤ (((((((primeBlock0.map twinRaw).prod)*(primeBlock1.map twinRaw).prod)*(primeBlock2.map twinRaw).prod)*(primeBlock3.map twinRaw).prod)*(primeBlock4.map twinRaw).prod)*(primeBlock5.map twinRaw).prod)*(primeBlock6.map twinRaw).prod := by
    calc
      _ ≤ (660421483766/1000000000000:ℝ)*(999926276360/1000000000000:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul ha5 h6 (by norm_num) (by linarith [ha5])
  have h7 : (999946424309/1000000000000:ℝ) ≤ (primeBlock7.map twinRaw).prod := by
    norm_num [primeBlock7,twinRaw]
  have ha7 : (660337415161/1000000000000:ℝ) ≤ ((((((((primeBlock0.map twinRaw).prod)*(primeBlock1.map twinRaw).prod)*(primeBlock2.map twinRaw).prod)*(primeBlock3.map twinRaw).prod)*(primeBlock4.map twinRaw).prod)*(primeBlock5.map twinRaw).prod)*(primeBlock6.map twinRaw).prod)*(primeBlock7.map twinRaw).prod := by
    calc
      _ ≤ (660372795090/1000000000000:ℝ)*(999946424309/1000000000000:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul ha6 h7 (by norm_num) (by linarith [ha6])
  have h8 : (999961694435/1000000000000:ℝ) ≤ (primeBlock8.map twinRaw).prod := by
    norm_num [primeBlock8,twinRaw]
  have ha8 : (660312120563/1000000000000:ℝ) ≤ (((((((((primeBlock0.map twinRaw).prod)*(primeBlock1.map twinRaw).prod)*(primeBlock2.map twinRaw).prod)*(primeBlock3.map twinRaw).prod)*(primeBlock4.map twinRaw).prod)*(primeBlock5.map twinRaw).prod)*(primeBlock6.map twinRaw).prod)*(primeBlock7.map twinRaw).prod)*(primeBlock8.map twinRaw).prod := by
    calc
      _ ≤ (660337415161/1000000000000:ℝ)*(999961694435/1000000000000:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul ha7 h8 (by norm_num) (by linarith [ha7])
  have h9 : (999969834880/1000000000000:ℝ) ≤ (primeBlock9.map twinRaw).prod := by
    norm_num [primeBlock9,twinRaw]
  have ha9 : (660292202168/1000000000000:ℝ) ≤ ((((((((((primeBlock0.map twinRaw).prod)*(primeBlock1.map twinRaw).prod)*(primeBlock2.map twinRaw).prod)*(primeBlock3.map twinRaw).prod)*(primeBlock4.map twinRaw).prod)*(primeBlock5.map twinRaw).prod)*(primeBlock6.map twinRaw).prod)*(primeBlock7.map twinRaw).prod)*(primeBlock8.map twinRaw).prod)*(primeBlock9.map twinRaw).prod := by
    calc
      _ ≤ (660312120563/1000000000000:ℝ)*(999969834880/1000000000000:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul ha8 h9 (by norm_num) (by linarith [ha8])
  have h10 : (999976177920/1000000000000:ℝ) ≤ (primeBlock10.map twinRaw).prod := by
    norm_num [primeBlock10,twinRaw]
  have ha10 : (660276472634/1000000000000:ℝ) ≤ (((((((((((primeBlock0.map twinRaw).prod)*(primeBlock1.map twinRaw).prod)*(primeBlock2.map twinRaw).prod)*(primeBlock3.map twinRaw).prod)*(primeBlock4.map twinRaw).prod)*(primeBlock5.map twinRaw).prod)*(primeBlock6.map twinRaw).prod)*(primeBlock7.map twinRaw).prod)*(primeBlock8.map twinRaw).prod)*(primeBlock9.map twinRaw).prod)*(primeBlock10.map twinRaw).prod := by
    calc
      _ ≤ (660292202168/1000000000000:ℝ)*(999976177920/1000000000000:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul ha9 h10 (by norm_num) (by linarith [ha9])
  have h11 : (999981001618/1000000000000:ℝ) ≤ (primeBlock11.map twinRaw).prod := by
    norm_num [primeBlock11,twinRaw]
  have ha11 : (660263928449/1000000000000:ℝ) ≤ ((((((((((((primeBlock0.map twinRaw).prod)*(primeBlock1.map twinRaw).prod)*(primeBlock2.map twinRaw).prod)*(primeBlock3.map twinRaw).prod)*(primeBlock4.map twinRaw).prod)*(primeBlock5.map twinRaw).prod)*(primeBlock6.map twinRaw).prod)*(primeBlock7.map twinRaw).prod)*(primeBlock8.map twinRaw).prod)*(primeBlock9.map twinRaw).prod)*(primeBlock10.map twinRaw).prod)*(primeBlock11.map twinRaw).prod := by
    calc
      _ ≤ (660276472634/1000000000000:ℝ)*(999981001618/1000000000000:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul ha10 h11 (by norm_num) (by linarith [ha10])
  have h12 : (999984363245/1000000000000:ℝ) ≤ (primeBlock12.map twinRaw).prod := by
    norm_num [primeBlock12,twinRaw]
  have ha12 : (660253604063/1000000000000:ℝ) ≤ (((((((((((((primeBlock0.map twinRaw).prod)*(primeBlock1.map twinRaw).prod)*(primeBlock2.map twinRaw).prod)*(primeBlock3.map twinRaw).prod)*(primeBlock4.map twinRaw).prod)*(primeBlock5.map twinRaw).prod)*(primeBlock6.map twinRaw).prod)*(primeBlock7.map twinRaw).prod)*(primeBlock8.map twinRaw).prod)*(primeBlock9.map twinRaw).prod)*(primeBlock10.map twinRaw).prod)*(primeBlock11.map twinRaw).prod)*(primeBlock12.map twinRaw).prod := by
    calc
      _ ≤ (660263928449/1000000000000:ℝ)*(999984363245/1000000000000:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul ha11 h12 (by norm_num) (by linarith [ha11])
  have h13 : (999988095327/1000000000000:ℝ) ≤ (primeBlock13.map twinRaw).prod := by
    norm_num [primeBlock13,twinRaw]
  have ha13 : (660245743959/1000000000000:ℝ) ≤ ((((((((((((((primeBlock0.map twinRaw).prod)*(primeBlock1.map twinRaw).prod)*(primeBlock2.map twinRaw).prod)*(primeBlock3.map twinRaw).prod)*(primeBlock4.map twinRaw).prod)*(primeBlock5.map twinRaw).prod)*(primeBlock6.map twinRaw).prod)*(primeBlock7.map twinRaw).prod)*(primeBlock8.map twinRaw).prod)*(primeBlock9.map twinRaw).prod)*(primeBlock10.map twinRaw).prod)*(primeBlock11.map twinRaw).prod)*(primeBlock12.map twinRaw).prod)*(primeBlock13.map twinRaw).prod := by
    calc
      _ ≤ (660253604063/1000000000000:ℝ)*(999988095327/1000000000000:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul ha12 h13 (by norm_num) (by linarith [ha12])
  have hnum : (16506/25000:ℝ) ≤ (660245743959/1000000000000:ℝ) := by norm_num
  apply hnum.trans
  simpa only [certifiedPrimeList,List.map_append,List.prod_append] using ha13

lemma twinPrimePartial_1007_lower :
    (16506/25000:ℝ) ≤ TaoFivePrimes.twinPrimePartial 1007 := by
  have hsub : certifiedPrimeList.toFinset ⊆ range 1008 := by
    intro p hp
    exact mem_range.mpr (certifiedPrimeList_bounds p (List.mem_toFinset.mp hp)).2
  have hproduct : certifiedPrimeList.toFinset.prod twinLocal =
      TaoFivePrimes.twinPrimePartial 1007 := by
    rw [twinPrimePartial_eq_local]
    apply prod_subset hsub
    intro p hp hnot
    unfold twinLocal
    apply if_neg
    intro hprime
    exact hnot (List.mem_toFinset.mpr (certifiedPrimeList_complete p
      (mem_range.mp hp) hprime.1 hprime.2))
  calc
    _ ≤ (certifiedPrimeList.map twinRaw).prod := certified_raw_product_lower
    _ = certifiedPrimeList.toFinset.prod twinRaw :=
      (List.prod_toFinset twinRaw certifiedPrimeList_nodup).symm
    _ ≤ certifiedPrimeList.toFinset.prod twinLocal := by
      apply prod_le_prod
      · intro p hp
        exact twinRaw_nonneg_of_three_le p (certifiedPrimeList_bounds p (List.mem_toFinset.mp hp)).1
      · intro p _
        exact twinRaw_le_local p
    _ = _ := hproduct

end Helfgott

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Finset

namespace Helfgott

lemma twinLocal_of_proper_prime_divisor (p d : ℕ) (hd : Nat.Prime d)
    (hdiv : d ∣ p) (hne : p ≠ d) : twinLocal p = 1 := by
  unfold twinLocal
  apply if_neg
  intro hp
  have he : d = p := (Nat.prime_dvd_prime_iff_eq hd hp.1).mp hdiv
  exact hne he.symm

lemma twinLocal_block_lower (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    1-1/(36*(k:ℝ)^2) ≤ twinLocal (6*k+r) := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hpos : 0 < 36*(k:ℝ)^2 := by positivity
  unfold twinLocal
  split_ifs with hp
  · have hden : 36*(k:ℝ)^2 ≤ (((6*k+r:ℕ):ℝ)-1)^2 := by
      push_cast
      nlinarith
    exact sub_le_sub_left (one_div_le_one_div_of_le hpos hden) 1
  · have hn : 0 ≤ 1/(36*(k:ℝ)^2) := by positivity
    linarith

noncomputable def twinBlock (k : ℕ) : ℝ :=
  ∏ r ∈ range 6, twinLocal (6*k+r)

lemma twinBlock_nonneg (k : ℕ) : 0 ≤ twinBlock k := by
  exact prod_nonneg fun r _ => twinLocal_nonneg _

lemma twinBlock_le_one (k : ℕ) : twinBlock k ≤ 1 := by
  exact prod_le_one (fun r _ => twinLocal_nonneg _) (fun r _ => twinLocal_le_one _)

lemma twinBlock_lower (k : ℕ) (hk : 1 ≤ k) :
    1-1/(18*(k:ℝ)^2) ≤ twinBlock k := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have h0 : twinLocal (6*k) = 1 :=
    twinLocal_of_proper_prime_divisor _ 2 Nat.prime_two ⟨3*k,by omega⟩ (by omega)
  have h2 : twinLocal (6*k+2) = 1 :=
    twinLocal_of_proper_prime_divisor _ 2 Nat.prime_two ⟨3*k+1,by omega⟩ (by omega)
  have h3 : twinLocal (6*k+3) = 1 :=
    twinLocal_of_proper_prime_divisor _ 3 Nat.prime_three ⟨2*k+1,by omega⟩ (by omega)
  have h4 : twinLocal (6*k+4) = 1 :=
    twinLocal_of_proper_prime_divisor _ 2 Nat.prime_two ⟨3*k+2,by omega⟩ (by omega)
  have hprod : twinBlock k = twinLocal (6*k+1)*twinLocal (6*k+5) := by
    unfold twinBlock
    norm_num only [prod_range_succ,prod_range_zero,Nat.add_zero]
    rw [h0,h2,h3,h4]
    ring
  have hzpos : 0 < 36*(k:ℝ)^2 := by positivity
  have hz : 0 ≤ 1-1/(36*(k:ℝ)^2) := by
    have hsq : 1 ≤ 36*(k:ℝ)^2 := by nlinarith
    have hi : 1/(36*(k:ℝ)^2) ≤ (1:ℝ) := (div_le_one hzpos).2 hsq
    linarith
  have h1 := twinLocal_block_lower k 1 hk (by decide)
  have h5 := twinLocal_block_lower k 5 hk (by decide)
  have hm := mul_le_mul h1 h5 hz (twinLocal_nonneg (6*k+1))
  rw [hprod]
  have hid : (1-1/(36*(k:ℝ)^2))*(1-1/(36*(k:ℝ)^2)) =
      1-1/(18*(k:ℝ)^2)+(1/(36*(k:ℝ)^2))^2 := by ring
  rw [hid] at hm
  nlinarith [sq_nonneg (1/(36*(k:ℝ)^2))]

lemma reciprocal_block_gap (x : ℝ) (hx : 1 < x) :
    1/(18*x^2) ≤ 1/(18*(x-1))-1/(18*x) := by
  have hx0 : 0 < x := by linarith
  have hxm : 0 < x-1 := by linarith
  field_simp
  nlinarith

noncomputable def twinTail (n : ℕ) : ℝ := ∏ j ∈ range n, twinBlock (168+j)

lemma twinTail_nonneg (n : ℕ) : 0 ≤ twinTail n := by
  exact prod_nonneg fun j _ => twinBlock_nonneg _

lemma twinTail_le_one (n : ℕ) : twinTail n ≤ 1 := by
  exact prod_le_one (fun j _ => twinBlock_nonneg _) (fun j _ => twinBlock_le_one _)

lemma twinTail_lower_strong (n : ℕ) :
    1-1/3006+1/(18*(167+(n:ℝ))) ≤ twinTail n := by
  induction n with
  | zero => norm_num [twinTail]
  | succ n ih =>
    rw [twinTail,prod_range_succ]
    change 1-1/3006+1/(18*(167+((n+1:ℕ):ℝ))) ≤
      twinTail n*twinBlock (168+n)
    have hn0 := twinTail_nonneg n
    have hn1 := twinTail_le_one n
    have hb := twinBlock_lower (168+n) (by omega)
    have hgap := reciprocal_block_gap (168+(n:ℝ)) (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    have ha : 0 ≤ 1/(18*(168+(n:ℝ))^2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hb hn0
    push_cast at hmul
    have hsave := mul_nonneg (sub_nonneg.mpr hn1) ha
    have hstep : twinTail n-1/(18*(168+(n:ℝ))^2) ≤
        twinTail n*twinBlock (168+n) := by nlinarith
    push_cast
    have hident : 168+(n:ℝ)-1 = 167+(n:ℝ) := by ring
    rw [hident] at hgap
    have hnext : 167+((n:ℝ)+1) = 168+(n:ℝ) := by ring
    rw [hnext]
    linarith

lemma twinTail_lower (n : ℕ) : 1-1/3006 ≤ twinTail n := by
  have hh := twinTail_lower_strong n
  have hb : 0 ≤ 1/(18*(167+(n:ℝ))) := by positivity
  linarith

lemma twin_prefix_blocks (K n : ℕ) :
    (∏ p ∈ range (6*(K+n)), twinLocal p) =
      (∏ p ∈ range (6*K), twinLocal p)*(∏ j ∈ range n, twinBlock (K+j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : 6*(K+(n+1)) = 6*(K+n)+6 := by omega
    rw [he,prod_range_add,prod_range_succ (fun j => twinBlock (K+j)) n,ih,mul_assoc]
    rfl

lemma twinPrimePartial_block_lower (n : ℕ) :
    (16506/25000:ℝ)*(1-1/3006) ≤
      TaoFivePrimes.twinPrimePartial (6*(168+n)-1) := by
  have hsize : 6*(168+n)-1+1 = 6*(168+n) := by omega
  rw [twinPrimePartial_eq_local,hsize,twin_prefix_blocks]
  change (16506/25000:ℝ)*(1-1/3006) ≤
    TaoFivePrimes.twinPrimePartial 1007*twinTail n
  exact mul_le_mul twinPrimePartial_1007_lower (twinTail_lower n) (by norm_num)
    (twinPrimePartial_nonneg 1007)

lemma twinPrimePartial_uniform_lower (Q : ℕ) :
    (33/50:ℝ) ≤ TaoFivePrimes.twinPrimePartial Q := by
  have hlarge : Q ≤ 6*(168+Q)-1 := by omega
  have hb := twinPrimePartial_block_lower Q
  have ha := twinPrimePartial_antitone hlarge
  have hnum : (33/50:ℝ) ≤ (16506/25000:ℝ)*(1-1/3006) := by norm_num
  exact hnum.trans (hb.trans ha)

lemma twinPrimeConstant_lower : (33/25:ℝ) ≤ TaoFivePrimes.twinPrimeConstant := by
  have hs : (33/50:ℝ) ≤ sInf (Set.range TaoFivePrimes.twinPrimePartial) := by
    apply le_csInf (Set.range_nonempty _)
    rintro y ⟨Q,rfl⟩
    exact twinPrimePartial_uniform_lower Q
  unfold TaoFivePrimes.twinPrimeConstant
  linarith

end Helfgott

theorem solution : (33/25:ℝ) ≤ TaoFivePrimes.twinPrimeConstant := Helfgott.twinPrimeConstant_lower

#print axioms solution
