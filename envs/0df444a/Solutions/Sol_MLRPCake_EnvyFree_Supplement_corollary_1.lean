-- Prove2me | solution 1 for MLRPCake.EnvyFree.Supplement.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:09:05.434262+00:00
-- url     : https://prove2.me/submissions/78b839b7-f550-4b82-979a-7504609df1c6

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_SwitchPoints

open MLRPCake
open MLRPCake.EnvyFree
open MLRPCake.EnvyFree.Supplement

/-- Corollary 1, p. 18: for agents `i < j` of an MLRP instance (so `f_i, f_j` bear MLRP) and
`γ ∈ (0,1)`, the binary search over cells of mesh `2^{-K}`, `K = ⌈log₂(2/γ)⌉`, using two Eval
queries per iteration, returns an interval of length at most `γ` containing the switching point
`p_{ij}`, and its number of queries is `O(log(1/γ))` (universal constant). -/
theorem solution : ∃ c : ℕ, ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (i j : Fin n) (γ : ℝ),
    IsInstance f → IsMLRP f → i < j → 0 < γ → γ < 1 →
    locLeft f i j γ ≤ switchPt (f i) (f j) ∧ switchPt (f i) (f j) ≤ locRight f i j γ ∧
      locRight f i j γ - locLeft f i j γ ≤ γ ∧
      (locQueries γ : ℝ) ≤ c * (Real.logb 2 (1 / γ) + 1) := by
        classical
        refine ⟨4, ?_⟩
        intro n f i j γ hf hm hij hγ hγ1
        have hratio : ∀ k : ℕ, ∀ a b : Fin n, b.val = a.val + k →
            ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ 1 →
            f b x / f a x ≤ f b y / f a y := by
          intro k
          induction k with
          | zero =>
            intro a b hab x y hx hxy hy
            have : b = a := Fin.ext (by omega)
            subst b
            rw [div_self (hm.1 a x ⟨hx, hxy.trans hy⟩).ne',
              div_self (hm.1 a y ⟨hx.trans hxy, hy⟩).ne']
          | succ k ih =>
            intro a b hab x y hx hxy hy
            let t : Fin n := ⟨a.val + k, by omega⟩
            have ha := hm.1 a x ⟨hx, hxy.trans hy⟩
            have hay := hm.1 a y ⟨hx.trans hxy, hy⟩
            have ht := hm.1 t x ⟨hx, hxy.trans hy⟩
            have hty := hm.1 t y ⟨hx.trans hxy, hy⟩
            have hb := hm.1 b x ⟨hx, hxy.trans hy⟩
            have hby := hm.1 b y ⟨hx.trans hxy, hy⟩
            have h₁ := ih a t rfl x y hx hxy hy
            have h₂ := hm.2 t b (by dsimp [t]; omega) x y hx hxy hy
            calc
              f b x / f a x = (f b x / f t x) * (f t x / f a x) := by field_simp
              _ ≤ (f b y / f t y) * (f t y / f a y) :=
                mul_le_mul h₂ h₁ (div_nonneg ht.le ha.le) (div_nonneg hby.le hty.le)
              _ = f b y / f a y := by field_simp
        have hmono : ∀ x y : ℝ, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 →
            x ≤ y → f i x ≤ f j x → f i y ≤ f j y := by
          intro x y hx hy hxy h
          have hr := hratio (j.val - i.val) i j (by have := hij; omega) x y hx.1 hxy hy.2
          have hix := hm.1 i x hx
          have hiy := hm.1 i y hy
          have hx' : 1 ≤ f j x / f i x := (le_div_iff₀ hix).2 (by simpa using h)
          simpa using (le_div_iff₀ hiy).1 (hx'.trans hr)
        have hint : ∀ a : Fin n, MeasureTheory.IntegrableOn (f a) (Set.Icc (0:ℝ) 1) := by
          intro a
          exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)).1 (hf a).2.2.1
        have hnorm : ∀ a : Fin n, (∫ x in Set.Icc (0:ℝ) 1, f a x) = 1 := by
          intro a
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
          exact (hf a).2.2.2
        have hstrict : ∀ (a b : ℝ), a < b → 0 ≤ a → b ≤ 1 →
            (∀ x ∈ Set.Icc a b, f j x < f i x) →
            (∫ x in Set.Icc a b, f j x) < ∫ x in Set.Icc a b, f i x := by
          intro a b hab ha hb hlt
          have hs : Set.Icc a b ⊆ Set.Icc (0:ℝ) 1 := fun x hx => ⟨ha.trans hx.1, hx.2.trans hb⟩
          have hi := (hint i).mono_set hs
          have hj := (hint j).mono_set hs
          have hd : IntervalIntegrable (fun x => f i x - f j x) MeasureTheory.volume a b :=
            (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).2 (hi.sub hj)
          have hp := intervalIntegral.intervalIntegral_pos_of_pos_on hd
            (fun x hx => sub_pos.2 (hlt x ⟨hx.1.le, hx.2.le⟩)) hab
          rw [intervalIntegral.integral_of_le hab.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc,
            MeasureTheory.integral_sub hi hj] at hp
          linarith
        let S : Set ℝ := {x | x ∈ Set.Icc (0:ℝ) 1 ∧ f i x ≤ f j x}
        have hS : S.Nonempty := by
          by_contra h
          have hlt : ∀ x ∈ Set.Icc (0:ℝ) 1, f j x < f i x := by
            intro x hx
            exact lt_of_not_ge (fun hle => h ⟨x, hx, hle⟩)
          have := hstrict 0 1 (by norm_num) (by norm_num) (by norm_num) hlt
          rw [hnorm i, hnorm j] at this
          linarith
        have hSb : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
        have hp0 : 0 ≤ switchPt (f i) (f j) := le_csInf hS (fun x hx => hx.1.1)
        have hp1 : switchPt (f i) (f j) ≤ 1 := by
          obtain ⟨x, hx⟩ := hS
          exact (csInf_le hSb hx).trans hx.1.2
        have hbefore : ∀ x ∈ Set.Icc (0:ℝ) 1, x < switchPt (f i) (f j) → f j x < f i x := by
          intro x hx hxp
          exact lt_of_not_ge (fun hle => (not_le_of_gt hxp) (csInf_le hSb ⟨hx, hle⟩))
        have hafter : ∀ x ∈ Set.Icc (0:ℝ) 1, switchPt (f i) (f j) < x → f i x ≤ f j x := by
          intro x hx hpx
          obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hS hpx
          exact hmono y x hy.1 hx hyx.le hy.2
        have hcell : ∀ (K k : ℕ), 1 ≤ k → k ≤ 2 ^ K →
            (cellTest f i j K k → switchPt (f i) (f j) ≤ (k:ℝ) / 2 ^ K) ∧
            (¬cellTest f i j K k → ((k:ℝ) - 1) / 2 ^ K ≤ switchPt (f i) (f j)) := by
          intro K k hk hkN
          have hD : (0:ℝ) < 2 ^ K := by positivity
          have hD0 := hD.ne'
          have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
          have hkNR : (k:ℝ) ≤ 2 ^ K := by exact_mod_cast hkN
          have ha : 0 ≤ ((k:ℝ) - 1) / 2 ^ K := div_nonneg (by linarith) hD.le
          have hb : (k:ℝ) / 2 ^ K ≤ 1 := (div_le_one hD).2 hkNR
          have hab : ((k:ℝ) - 1) / 2 ^ K < (k:ℝ) / 2 ^ K := (div_lt_div_iff_of_pos_right hD).2 (by linarith)
          have hs : Set.Icc (((k:ℝ) - 1) / 2 ^ K) ((k:ℝ) / 2 ^ K) ⊆ Set.Icc (0:ℝ) 1 :=
            fun x hx => ⟨ha.trans hx.1, hx.2.trans hb⟩
          have heval : ∀ a : Fin n, eval f a (((k:ℝ) - 1) / 2 ^ K) ((k:ℝ) / 2 ^ K) =
              ∫ x in Set.Icc (((k:ℝ) - 1) / 2 ^ K) ((k:ℝ) / 2 ^ K), f a x := by
            intro a
            simp [eval, dens, a.isLt]
          constructor
          · intro ht
            by_contra hn
            have hlt := hstrict _ _ hab ha hb (fun x hx => hbefore x (hs hx) (lt_of_le_of_lt hx.2 (lt_of_not_ge hn)))
            change eval f i _ _ ≤ eval f j _ _ at ht
            rw [heval i, heval j] at ht
            linarith
          · intro ht
            by_contra hn
            apply ht
            change eval f i _ _ ≤ eval f j _ _
            rw [heval i, heval j]
            apply MeasureTheory.setIntegral_mono_on ((hint i).mono_set hs) ((hint j).mono_set hs) measurableSet_Icc
            intro x hx
            exact hafter x (hs hx) (lt_of_lt_of_le (lt_of_not_ge hn) hx.1)
        have hiter : ∀ K s : ℕ, s ≤ K →
            let q := locIter f i j K s
            q.1 < q.2 ∧ q.2 ≤ 2 ^ K ∧
            (q.1 = 0 ∨ ((q.1:ℝ) - 1) / 2 ^ K ≤ switchPt (f i) (f j)) ∧
            switchPt (f i) (f j) ≤ (q.2:ℝ) / 2 ^ K ∧ q.2 - q.1 ≤ 2 ^ (K - s) := by
          intro K s
          induction s with
          | zero =>
            intro hs
            dsimp [locIter]
            refine ⟨by positivity, le_rfl, Or.inl rfl, ?_, by simp⟩
            simpa using hp1
          | succ s ih =>
            intro hs
            have H := ih (by omega)
            let q := locIter f i j K s
            change q.1 < q.2 ∧ q.2 ≤ 2 ^ K ∧
              (q.1 = 0 ∨ ((q.1:ℝ) - 1) / 2 ^ K ≤ switchPt (f i) (f j)) ∧
              switchPt (f i) (f j) ≤ (q.2:ℝ) / 2 ^ K ∧ q.2 - q.1 ≤ 2 ^ (K - s) at H
            have hpow : 0 < 2 ^ (K - (s + 1)) := by positivity
            have hpoweq : 2 ^ (K - s) = 2 * 2 ^ (K - (s + 1)) := by
              have he : K - s = (K - (s + 1)) + 1 := by omega
              rw [he, pow_succ]
              omega
            by_cases hstop : q.2 ≤ q.1 + 1
            · simp only [locIter, show (locIter f i j K s).2 ≤ (locIter f i j K s).1 + 1 from hstop,
                ↓reduceIte]
              exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, by
                change q.2 - q.1 ≤ 2 ^ (K - (s + 1))
                omega⟩
            · have hmlo : q.1 < (q.1 + q.2) / 2 := by omega
              have hmhi : (q.1 + q.2) / 2 < q.2 := by omega
              have hm1 : 1 ≤ (q.1 + q.2) / 2 := by omega
              have hmN : (q.1 + q.2) / 2 ≤ 2 ^ K := by omega
              have hc := hcell K ((q.1 + q.2) / 2) hm1 hmN
              by_cases ht : cellTest f i j K ((q.1 + q.2) / 2)
              · simp only [locIter, show ¬(locIter f i j K s).2 ≤ (locIter f i j K s).1 + 1 from hstop,
                  ↓reduceIte, show cellTest f i j K (((locIter f i j K s).1 + (locIter f i j K s).2) / 2) from ht]
                exact ⟨hmlo, hmN, H.2.2.1, hc.1 ht, by omega⟩
              · simp only [locIter, show ¬(locIter f i j K s).2 ≤ (locIter f i j K s).1 + 1 from hstop,
                  ↓reduceIte, show ¬cellTest f i j K (((locIter f i j K s).1 + (locIter f i j K s).2) / 2) from ht]
                exact ⟨hmhi, H.2.1, Or.inr (hc.2 ht), H.2.2.2.1, by omega⟩
        have hmesh : 2 / γ ≤ (2:ℝ) ^ locSteps γ := by
          have hc := Nat.le_ceil (Real.logb 2 (2 / γ))
          have hr := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) (div_pos (by norm_num) hγ)).1 hc
          simpa only [Real.rpow_natCast, locSteps] using hr
        have hlog : 0 ≤ Real.logb 2 (1 / γ) :=
          Real.logb_nonneg (by norm_num) ((one_le_div hγ).2 hγ1.le)
        have hlog2 : Real.logb 2 (2 / γ) = Real.logb 2 (1 / γ) + 1 := by
          rw [show (2:ℝ) / γ = 2 * (1 / γ) by ring,
            Real.logb_mul (by norm_num) (ne_of_gt (div_pos (by norm_num) hγ)), Real.logb_self_eq_one (by norm_num)]
          ring
        have hsteps : (locSteps γ : ℝ) ≤ Real.logb 2 (1 / γ) + 2 := by
          have := Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 (2 / γ) by rw [hlog2]; linarith)
          change (locSteps γ : ℝ) < Real.logb 2 (2 / γ) + 1 at this
          rw [hlog2] at this
          linarith
        have H := hiter (locSteps γ) (locSteps γ) le_rfl
        dsimp only at H
        have hleft : locLeft f i j γ ≤ switchPt (f i) (f j) := by
          apply max_le hp0
          rcases H.2.2.1 with hzero | hbound
          · rw [hzero]
            have : (0:ℝ) ≤ 2 ^ locSteps γ := by positivity
            exact le_trans (div_nonpos_of_nonpos_of_nonneg (by norm_num) this) hp0
          · exact hbound
        have hright : switchPt (f i) (f j) ≤ locRight f i j γ := H.2.2.2.1
        have hlen : locRight f i j γ - locLeft f i j γ ≤ γ := by
          have hD : (0:ℝ) < 2 ^ locSteps γ := by positivity
          have hgap : (locIter f i j (locSteps γ) (locSteps γ)).2 ≤
              (locIter f i j (locSteps γ) (locSteps γ)).1 + 1 := by
            have := H.2.2.2.2
            simp only [Nat.sub_self, pow_zero] at this
            omega
          have hgapR : ((locIter f i j (locSteps γ) (locSteps γ)).2:ℝ) ≤
              ((locIter f i j (locSteps γ) (locSteps γ)).1:ℝ) + 1 := by exact_mod_cast hgap
          have hl := le_max_right (0:ℝ)
            ((((locIter f i j (locSteps γ) (locSteps γ)).1:ℝ) - 1) / 2 ^ locSteps γ)
          have hsmall : 2 / (2:ℝ) ^ locSteps γ ≤ γ := by
            apply (div_le_iff₀ hD).2
            have := (div_le_iff₀ hγ).1 hmesh
            nlinarith
          change (locRight f i j γ) - locLeft f i j γ ≤ γ
          unfold locRight locLeft
          calc
            _ ≤ ((locIter f i j (locSteps γ) (locSteps γ)).2:ℝ) / 2 ^ locSteps γ -
                (((locIter f i j (locSteps γ) (locSteps γ)).1:ℝ) - 1) / 2 ^ locSteps γ := sub_le_sub_left hl _
            _ ≤ 2 / (2:ℝ) ^ locSteps γ := by
              rw [← sub_div]
              exact (div_le_div_iff_of_pos_right hD).2 (by linarith)
            _ ≤ γ := hsmall
        refine ⟨hleft, hright, hlen, ?_⟩
        simp only [locQueries, Nat.cast_mul, Nat.cast_ofNat]
        linarith
