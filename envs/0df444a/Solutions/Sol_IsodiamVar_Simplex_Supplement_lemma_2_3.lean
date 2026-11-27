-- Prove2me | solution 1 for IsodiamVar.Simplex.Supplement.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:47.841824+00:00
-- url     : https://prove2.me/submissions/d8bc5325-4c87-443f-b4a0-0b7229c0dd15

import Definitions.Def_IsodiamVar_Simplex_Supplement_Legendre

open MeasureTheory

open IsodiamVar
open IsodiamVar.Simplex
open IsodiamVar.Simplex.Supplement

/-- Lemma 2.3, p. 11: the complete translation identity and minimization equivalence. -/
theorem solution {n : ℕ} (K : Set (E n)) (hK : IsCompact K) :
    (∀ x w : E n,
      phiBiconjugate ((fun y : E n => y - w) '' K) x =
        (((‖x + w‖ ^ 2 - ‖x‖ ^ 2 : ℝ) : EReal) + phiBiconjugate K (x + w))) ∧
    ((∀ w : E n, phiBiconjugate K 0 ≤
        phiBiconjugate ((fun y : E n => y - w) '' K) 0) ↔
      ∀ x : E n, phiBiconjugate K 0 ≤ phiBiconjugate K x) := by
        classical
        have hmove (a : ℝ) (u v : EReal) :
            (a : EReal) + u ≤ v ↔ u ≤ ((-a : ℝ) : EReal) + v := by
          constructor
          · intro h
            have hh := add_le_add (le_refl (((-a : ℝ) : EReal))) h
            simpa only [← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add] using hh
          · intro h
            have hh := add_le_add (le_refl ((a : EReal))) h
            simpa only [← add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, zero_add] using hh
        have haddSup {ι : Type} (a : ℝ) (f : ι → EReal) :
            (⨆ i, ((a : EReal) + f i)) = (a : EReal) + ⨆ i, f i := by
          apply le_antisymm
          · exact iSup_le fun i => add_le_add le_rfl (le_iSup f i)
          · apply (hmove a _ _).2
            exact iSup_le fun i => (hmove a _ _).1 (le_iSup (fun i => (a : EReal) + f i) i)
        have hstar (L : Set (E n)) (p : E n) :
            phiStar L p = ⨆ y : L, ((inner ℝ p (y : E n) + ‖(y : E n)‖ ^ 2 : ℝ) : EReal) := by
          unfold phiStar WassersteinDRO.ConvexLossP1.conjugate
          apply le_antisymm
          · apply iSup_le
            intro y
            by_cases hy : y ∈ L
            · simpa only [phi, if_pos hy, innerSL_apply_apply, ← EReal.coe_sub, sub_neg_eq_add] using
                (le_iSup (fun y : L => ((inner ℝ p (y : E n) + ‖(y : E n)‖ ^ 2 : ℝ) : EReal)) ⟨y, hy⟩)
            · simp [phi, hy]
          · apply iSup_le
            intro y
            simpa only [phi, if_pos y.property, innerSL_apply_apply, ← EReal.coe_sub, sub_neg_eq_add] using
              (le_iSup (fun y : E n => ((innerSL ℝ p y : ℝ) : EReal) - phi L y) (y : E n))
        have hshift (p w : E n) :
            phiStar ((fun y : E n => y - w) '' K) p =
              ((‖w‖ ^ 2 - inner ℝ p w : ℝ) : EReal) + phiStar K (p - (2 : ℝ) • w) := by
          rw [hstar, hstar, ← haddSup]
          have hid (y : E n) :
              inner ℝ p (y - w) + ‖y - w‖ ^ 2 =
                (‖w‖ ^ 2 - inner ℝ p w) + (inner ℝ (p - (2 : ℝ) • w) y + ‖y‖ ^ 2) := by
            simp only [inner_sub_right, inner_sub_left, inner_smul_left, norm_sub_sq_real, map_ofNat]
            rw [real_inner_comm w y]
            ring
          apply le_antisymm
          · apply iSup_le
            intro y
            obtain ⟨z, hz, heq⟩ := y.property
            rw [← heq]
            rw [hid, EReal.coe_add]
            exact le_iSup_of_le ⟨z, hz⟩ le_rfl
          · apply iSup_le
            intro y
            rw [← EReal.coe_add, ← hid]
            exact le_iSup_of_le ⟨(y : E n) - w, ⟨y, y.property, rfl⟩⟩ le_rfl
        have htrans (x w : E n) :
            phiBiconjugate ((fun y : E n => y - w) '' K) x =
              ((‖x + w‖ ^ 2 - ‖x‖ ^ 2 : ℝ) : EReal) + phiBiconjugate K (x + w) := by
          unfold phiBiconjugate WassersteinDRO.ConvexLossP1.conjugate
          simp only [hshift]
          rw [← haddSup]
          have hid (p : E n) :
              ((innerSL ℝ x p : ℝ) : EReal) -
                  (((‖w‖ ^ 2 - inner ℝ p w : ℝ) : EReal) + phiStar K (p - (2 : ℝ) • w)) =
                ((‖x + w‖ ^ 2 - ‖x‖ ^ 2 : ℝ) : EReal) +
                  (((innerSL ℝ (x + w) (p - (2 : ℝ) • w) : ℝ) : EReal) -
                    phiStar K (p - (2 : ℝ) • w)) := by
            have hr : inner ℝ x p - (‖w‖ ^ 2 - inner ℝ p w) =
                (‖x + w‖ ^ 2 - ‖x‖ ^ 2) + inner ℝ (x + w) (p - (2 : ℝ) • w) := by
              simp only [norm_add_sq_real, inner_add_left, inner_sub_right, inner_smul_right]
              rw [real_inner_comm p w, real_inner_self_eq_norm_sq]
              ring
            generalize phiStar K (p - (2 : ℝ) • w) = s
            cases s using EReal.rec with
            | bot => simp only [EReal.add_bot, EReal.coe_sub_bot, EReal.coe_add_top]
            | top => simp only [EReal.coe_add_top, EReal.sub_top, EReal.add_bot]
            | coe s =>
              rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add]
              congr 1
              change inner ℝ x p - (‖w‖ ^ 2 - inner ℝ p w + s) =
                (‖x + w‖ ^ 2 - ‖x‖ ^ 2) + (inner ℝ (x + w) (p - (2 : ℝ) • w) - s)
              linarith [hr]
          simp only [hid]
          exact (Equiv.subRight ((2 : ℝ) • w)).iSup_comp (g := fun p : E n =>
            ((‖x + w‖ ^ 2 - ‖x‖ ^ 2 : ℝ) : EReal) +
              (((innerSL ℝ (x + w) p : ℝ) : EReal) - phiStar K p))
        have hconv (x : E n) (a b t : ℝ)
            (h0 : phiBiconjugate K 0 = (a : EReal))
            (hx : phiBiconjugate K x = (b : EReal)) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
            phiBiconjugate K (t • x) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
          unfold phiBiconjugate WassersteinDRO.ConvexLossP1.conjugate at h0 hx ⊢
          apply iSup_le
          intro p
          have hp0 := (le_iSup (fun p : E n =>
            ((innerSL ℝ (0 : E n) p : ℝ) : EReal) - phiStar K p) p).trans (le_of_eq h0)
          have hpx := (le_iSup (fun p : E n =>
            ((innerSL ℝ x p : ℝ) : EReal) - phiStar K p) p).trans (le_of_eq hx)
          cases hs : phiStar K p using EReal.rec with
          | bot =>
            simp only [hs, EReal.coe_sub_bot] at hp0
            exact False.elim (EReal.coe_ne_top a (top_le_iff.mp hp0))
          | top => simp only [EReal.sub_top, bot_le]
          | coe c =>
            rw [hs, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hp0 hpx
            rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
            simp only [innerSL_apply_apply, inner_zero_left] at hp0 hpx ⊢
            rw [real_inner_smul_left]
            nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (show 0 ≤ a + c by linarith),
              mul_nonneg ht (show 0 ≤ b - (inner ℝ x p - c) by linarith)]
        refine ⟨htrans, ?_⟩
        constructor
        · intro H x
          have H' (w : E n) : phiBiconjugate K 0 ≤
              ((‖w‖ ^ 2 : ℝ) : EReal) + phiBiconjugate K w := by
            simpa only [htrans, zero_add, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] using H w
          have hh := H' x
          cases h0 : phiBiconjugate K 0 using EReal.rec with
          | bot => exact bot_le
          | top =>
            cases hx : phiBiconjugate K x using EReal.rec with
            | bot => simpa only [h0, hx, EReal.add_bot] using hh
            | top => exact le_rfl
            | coe b =>
              rw [h0, hx, ← EReal.coe_add] at hh
              exact False.elim (EReal.coe_ne_top (‖x‖ ^ 2 + b) (top_le_iff.mp hh))
          | coe a =>
            cases hx : phiBiconjugate K x using EReal.rec with
            | bot =>
              rw [h0, hx, EReal.add_bot] at hh
              exact False.elim (EReal.coe_ne_bot a (le_bot_iff.mp hh))
            | top => exact le_top
            | coe b =>
              apply EReal.coe_le_coe_iff.mpr
              by_contra hab
              have hd : 0 < a - b := sub_pos.mpr (lt_of_not_ge hab)
              have hq : 0 < ‖x‖ ^ 2 + 1 := by positivity
              obtain ⟨t, ht, htmax⟩ := exists_between
                (show (0 : ℝ) < min 1 ((a - b) / (‖x‖ ^ 2 + 1)) by positivity)
              have ht1 : t ≤ 1 := (lt_of_lt_of_le htmax (min_le_left _ _)).le
              have htq : t * (‖x‖ ^ 2 + 1) < a - b :=
                (lt_div_iff₀ hq).mp (lt_of_lt_of_le htmax (min_le_right _ _))
              have hc := hconv x a b t h0 hx ht.le ht1
              have hf := (H' (t • x)).trans (add_le_add le_rfl hc)
              rw [h0, ← EReal.coe_add, EReal.coe_le_coe_iff] at hf
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hf
              have hm : 0 < t * (a - b - t * ‖x‖ ^ 2) :=
                mul_pos ht (by linarith)
              nlinarith
        · intro H w
          rw [htrans]
          have hh := H w
          simpa using hh.trans (le_add_of_nonneg_left (show (0 : EReal) ≤ ((‖(0 : E n) + w‖ ^ 2 - ‖(0 : E n)‖ ^ 2 : ℝ) : EReal) by simp))
