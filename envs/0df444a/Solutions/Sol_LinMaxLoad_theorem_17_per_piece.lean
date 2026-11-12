-- Prove2me | solution 1 for LinMaxLoad.theorem_17_per_piece
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:49:41.58953+00:00
-- url     : https://prove2.me/submissions/4cc9ce01-3071-49d0-bff5-5711fa480bec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinMaxLoad_expLoad
import Definitions.Def_LinMaxLoad_cosetSum
import Theorems.Thm_LinMaxLoad_lemma_7
import Theorems.Thm_LinMaxLoad_theorem_7

section
set_option autoImplicit false
namespace LinMaxLoad.Dev.PerPiece
open LinMaxLoad

open Classical

theorem maxLoad_le_card {A B : Type*} [DecidableEq B] (f : A → B) (S : Finset A) :
    LinMaxLoad.maxLoad f S ≤ S.card := by
  unfold LinMaxLoad.maxLoad
  apply Finset.sup_le
  intro b _
  exact Finset.card_filter_le _ _

theorem avgLin_le {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (ℓ : ℕ) (X : (E →ₗ[K] (Fin ℓ → K)) → ℝ) (b : ℝ) (hb : 0 ≤ b) (hX : ∀ h, X h ≤ b) :
    LinMaxLoad.avgLin K E ℓ X ≤ b := by
  unfold LinMaxLoad.avgLin
  refine div_le_of_le_mul₀ (Nat.cast_nonneg _) hb ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => b) fun h _ => hX h) ?_
  simp [mul_comm]

/-- the real-number core: the quotient set is below the bin count and the bound is `3p/ε` -/
theorem key (p : ℕ) (hp : 2 ≤ p) (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) (l : ℕ) (hl : 1 ≤ l)
    (R : ℝ) (hR1 : 1 ≤ R) (hRn : R ≤ (p : ℝ) ^ l) (m : ℕ) (hm : (m : ℝ) ≤ R ^ (1 - ε)) :
    (m : ℝ) < (p : ℝ) ^ l ∧ 0 ≤ (p : ℝ) * l / Real.log ((p : ℝ) ^ l / m) ∧
      (p : ℝ) * l / Real.log ((p : ℝ) ^ l / m) + p ≤ 3 * p / ε := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hpn : (p : ℝ) ≤ (p : ℝ) ^ l := by
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ l := pow_le_pow_right₀ (by linarith) hl
  have hlt : (m : ℝ) < (p : ℝ) ^ l := by
    rcases eq_or_lt_of_le hR1 with h | h
    · rw [← h, Real.one_rpow] at hm
      linarith
    · have : R ^ (1 - ε) < R := Real.rpow_lt_self_of_one_lt h (by linarith)
      linarith
  refine ⟨hlt, ?_⟩
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hpε : (p : ℝ) ≤ p / ε := by
    rw [le_div_iff₀ h0]; nlinarith
  by_cases hm0 : m = 0
  · subst hm0
    refine ⟨by simp, ?_⟩
    simp only [Nat.cast_zero, div_zero, Real.log_zero, zero_add]
    have : (3 : ℝ) * p / ε = 3 * (p / ε) := by ring
    linarith
  · have hm1 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have hn0 : (0 : ℝ) < (p : ℝ) ^ l := by positivity
    have hR0 : 0 < R := by linarith
    have hlogm : Real.log m ≤ (1 - ε) * Real.log R := by
      have := Real.log_le_log hm1 hm
      rwa [Real.log_rpow hR0] at this
    have hlogR : Real.log R ≤ Real.log ((p : ℝ) ^ l) := Real.log_le_log hR0 hRn
    have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg hR1
    have hlogn : Real.log ((p : ℝ) ^ l) = l * Real.log p := Real.log_pow _ _
    have hlogp : (1 : ℝ) / 2 ≤ Real.log p := by
      have h2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
      have := Real.log_two_gt_d9
      linarith
    have hL : ε * l * (1 / 2) ≤ Real.log ((p : ℝ) ^ l / m) := by
      rw [Real.log_div hn0.ne' hm1.ne']
      have h3 : (1 - ε) * Real.log R ≤ (1 - ε) * Real.log ((p : ℝ) ^ l) :=
        mul_le_mul_of_nonneg_left hlogR (by linarith)
      have h4 : ε * l * (1 / 2) ≤ ε * (l * Real.log p) := by
        have : (l : ℝ) * (1 / 2) ≤ l * Real.log p := mul_le_mul_of_nonneg_left hlogp (by linarith)
        nlinarith
      nlinarith
    have hLpos : 0 < ε * l * (1 / 2) := by positivity
    refine ⟨div_nonneg (by positivity) (hLpos.le.trans hL), ?_⟩
    have : (p : ℝ) * l / Real.log ((p : ℝ) ^ l / m) ≤ (p : ℝ) * l / (ε * l * (1 / 2)) :=
      div_le_div_of_nonneg_left (by positivity) hLpos hL
    have e : (p : ℝ) * l / (ε * l * (1 / 2)) = 2 * p / ε := by field_simp
    have e2 : (3 : ℝ) * p / ε = 2 * p / ε + p / ε := by ring
    linarith

theorem main (p : ℕ) [Fact p.Prime] (u : ℕ) (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1)
    (S : Finset (Fin u → ZMod p)) (V : Submodule (ZMod p) (Fin u → ZMod p))
    (T : Finset (Fin u → ZMod p))
    (hVS : Nat.card V ≤ S.card)
    (hT : ((T.card : ℝ) ≤ ((S.card : ℝ) / Nat.card V) ^ (1 - ε)))
    (c7 : ℝ)
    (hc7 : ∀ l : ℕ, 1 ≤ l → l ≤ Module.finrank (ZMod p) ((Fin u → ZMod p) ⧸ V) →
      ∀ S' : Finset ((Fin u → ZMod p) ⧸ V), S'.card < Fintype.card (ZMod p) ^ l →
        LinMaxLoad.expLoad (ZMod p) ((Fin u → ZMod p) ⧸ V) l S' ≤
          c7 * ((Fintype.card (ZMod p) : ℝ) * l /
              Real.log ((Fintype.card (ZMod p) : ℝ) ^ l / S'.card) + Fintype.card (ZMod p))) :
    LinMaxLoad.expLoad (ZMod p) (Fin u → ZMod p) (Nat.clog p S.card)
        (LinMaxLoad.cosetSum V T) ≤ (6 * max c7 0 + 1) * p / ε := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp1
  set ℓ := Nat.clog p S.card with hℓdef
  set d := Module.finrank (ZMod p) V with hd
  have hcardV : Nat.card V = p ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have hSpos : 1 ≤ S.card := by omega
  have hSp : S.card ≤ p ^ ℓ := Nat.le_pow_clog hp1 _
  have hdℓ : d ≤ ℓ := by
    have : p ^ d ≤ p ^ ℓ := by rw [← hcardV]; omega
    exact (Nat.pow_le_pow_iff_right hp1).mp this
  have hSu : S.card ≤ p ^ u := by
    have := Finset.card_le_univ S
    simpa [ZMod.card] using this
  have hℓu : ℓ ≤ u := Nat.clog_le_of_le_pow hSu
  have h7 := LinMaxLoad.lemma_7 ℓ V hdℓ T
  have hfin : Module.finrank (ZMod p) ((Fin u → ZMod p) ⧸ V) + d = u := by
    have := Submodule.finrank_quotient_add_finrank V
    rwa [Module.finrank_fin_fun] at this
  have hpε : (p : ℝ) ≤ p / ε := by
    rw [le_div_iff₀ h0]; nlinarith
  have hCnn : (0 : ℝ) ≤ max c7 0 := le_max_right _ _
  have hTc : (T.image V.mkQ).card ≤ T.card := Finset.card_image_le
  by_cases hl' : ℓ - d = 0
  · -- l' = 0 : |T| ≤ 1
    have hSV : S.card ≤ Nat.card V := by
      rw [hcardV]
      calc S.card ≤ p ^ ℓ := hSp
        _ = p ^ d := by congr 1; omega
    have hR : ((S.card : ℝ) / Nat.card V) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hVpos)]; exact_mod_cast hSV
    have hR1 : ((S.card : ℝ) / Nat.card V) ^ (1 - ε) ≤ 1 :=
      Real.rpow_le_one (by positivity) hR (by linarith)
    have hT1 : T.card ≤ 1 := by
      have : (T.card : ℝ) ≤ 1 := hT.trans hR1
      exact_mod_cast this
    have hE' : LinMaxLoad.expLoad (ZMod p) ((Fin u → ZMod p) ⧸ V) (ℓ - d)
        (T.image V.mkQ) ≤ 1 := by
      unfold LinMaxLoad.expLoad
      apply avgLin_le _ _ _ (by norm_num)
      intro h
      have := @maxLoad_le_card _ _ (fun a b => Classical.propDecidable (a = b))
        (h : ((Fin u → ZMod p) ⧸ V) → Fin (ℓ - d) → ZMod p) (T.image V.mkQ)
      have h2 := this.trans (hTc.trans hT1)
      refine Nat.cast_le_one.mpr ?_
      convert h2 <;> rfl
    have : (3 : ℝ) * p / ε ≥ 0 := by positivity
    have e : (6 * max c7 0 + 1) * p / ε = 6 * max c7 0 * (p / ε) + p / ε := by ring
    have : 0 ≤ max c7 0 * (p / ε) := by positivity
    nlinarith
  · have hl1 : 1 ≤ ℓ - d := by omega
    have hR0 : (0 : ℝ) < Nat.card V := by exact_mod_cast hVpos
    have hR1 : (1 : ℝ) ≤ (S.card : ℝ) / Nat.card V := by
      rw [le_div_iff₀ hR0]; simpa using (by exact_mod_cast hVS : (Nat.card V : ℝ) ≤ S.card)
    have hRn : (S.card : ℝ) / Nat.card V ≤ (p : ℝ) ^ (ℓ - d) := by
      rw [div_le_iff₀ hR0, hcardV]
      have : p ^ ℓ = p ^ (ℓ - d) * p ^ d := by rw [← pow_add]; congr 1; omega
      have h' : S.card ≤ p ^ (ℓ - d) * p ^ d := this ▸ hSp
      exact_mod_cast h'
    have hm : ((T.image V.mkQ).card : ℝ) ≤ ((S.card : ℝ) / Nat.card V) ^ (1 - ε) :=
      le_trans (by exact_mod_cast hTc) hT
    obtain ⟨hlt, hX0, hX3⟩ := key p hp1 ε h0 h1 (ℓ - d) hl1 _ hR1 hRn _ hm
    have hlt' : (T.image V.mkQ).card < Fintype.card (ZMod p) ^ (ℓ - d) := by
      rw [ZMod.card]; exact_mod_cast hlt
    have hfl : ℓ - d ≤ Module.finrank (ZMod p) ((Fin u → ZMod p) ⧸ V) := by omega
    have hb := hc7 (ℓ - d) hl1 hfl (T.image V.mkQ) hlt'
    rw [ZMod.card] at hb
    have h5 : c7 * ((p : ℝ) * (ℓ - d : ℕ) / Real.log ((p : ℝ) ^ (ℓ - d) / (T.image V.mkQ).card) + p)
        ≤ max c7 0 * (3 * p / ε) := by
      calc _ ≤ max c7 0 * ((p : ℝ) * (ℓ - d : ℕ) /
            Real.log ((p : ℝ) ^ (ℓ - d) / (T.image V.mkQ).card) + p) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_left hX3 hCnn
    have e : (6 * max c7 0 + 1) * p / ε = 6 * (max c7 0 * (3 * p / ε)) / 3 + p / ε := by ring
    have : 0 ≤ p / ε := by positivity
    nlinarith

end LinMaxLoad.Dev.PerPiece

namespace LinMaxLoad
open LinMaxLoad.Dev.PerPiece in
theorem chk_theorem_17_per_piece :
    ∃ c : ℝ, ∀ (p : ℕ) [Fact p.Prime] (u : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (S : Finset (Fin u → ZMod p)) (V : Submodule (ZMod p) (Fin u → ZMod p))
        (T : Finset (Fin u → ZMod p)),
        Nat.card V ≤ S.card →
        ((T.card : ℝ) ≤ ((S.card : ℝ) / Nat.card V) ^ (1 - ε)) →
        expLoad (ZMod p) (Fin u → ZMod p) (Nat.clog p S.card) (cosetSum V T) ≤ c * p / ε := by
  obtain ⟨c7, hc7⟩ := LinMaxLoad.theorem_7
  refine ⟨6 * max c7 0 + 1, ?_⟩
  intro p _ u ε h0 h1 S V T hVS hT
  exact main p u ε h0 h1 S V T hVS hT c7
    (fun l hl hl' S' hS' => hc7 (ZMod p) ((Fin u → ZMod p) ⧸ V) l hl hl' S' hS')
end LinMaxLoad
end

theorem solution : type_of% @LinMaxLoad.chk_theorem_17_per_piece := @LinMaxLoad.chk_theorem_17_per_piece
