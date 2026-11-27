-- Prove2me | solution 1 for MLRPCake.EnvyFree.Supplement.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:11:05.762019+00:00
-- url     : https://prove2.me/submissions/78ecf5f9-0df5-4270-bf30-5b6e385818cd

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_Divisions
import Definitions.Def_MLRPCake_EnvyFree_Supplement_MovingKnife

open MLRPCake
open MLRPCake.EnvyFree
open MLRPCake.EnvyFree.Supplement

/-- Theorem 4, p. 9: under MLRP and `λ`-Lipschitz queries, for every `η > 0` the §8 algorithm
(binary search for a feasible moving-knife target on a grid of mesh at most `η`, leftover cake
to the last agent) returns an allocation whose egalitarian welfare is within `η` of the optimum
over all allocations, with work polynomial in `n`, `log λ` and `log(1/η)`. -/
theorem solution : ∃ c : ℕ, ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (lam η : ℝ),
    1 ≤ n → IsInstance f → IsMLRP f → 1 ≤ lam → QueriesLipschitz f lam → 0 < η →
    IsAllocation (n := n) (ewOutput f η) ∧
      (∀ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x →
        EW f x σ - η ≤ EW f (ewOutput f η) (Equiv.refl (Fin n))) ∧
      (ewCost n η : ℝ) ≤
        c * ((n : ℝ) + Real.logb 2 lam + max 0 (Real.logb 2 (1 / η)) + 1) ^ c := by
          refine ⟨7, ?_⟩
          intro n f lam η hn hI hM hlam hQ hη
          have hdens : ∀ k (hk : k < n), dens f k = f ⟨k, hk⟩ := by
            intro k hk; simp [dens, hk]
          have hpos : ∀ k, k < n → ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < dens f k x := by
            intro k hk x hx; rw [hdens k hk]; exact hM.1 _ x hx
          have hint : ∀ k, k < n → ∀ a b, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 →
              IntervalIntegrable (dens f k) MeasureTheory.volume a b := by
            intro k hk a b ha hb
            rw [hdens k hk]
            exact (hI ⟨k,hk⟩).2.2.1.mono_set (by
              rw [Set.uIcc_of_le zero_le_one]; exact Set.uIcc_subset_Icc ha hb)
          have htot : ∀ k, k < n → val f k 0 1 = 1 := by
            intro k hk; simp only [val]; rw [hdens k hk]; exact (hI ⟨k,hk⟩).2.2.2
          have hadd : ∀ k, k < n → ∀ a b c, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 →
              c ∈ Set.Icc (0:ℝ) 1 → val f k a b + val f k b c = val f k a c := by
            intro k hk a b c ha hb hc
            exact intervalIntegral.integral_add_adjacent_intervals (hint k hk a b ha hb) (hint k hk b c hb hc)
          have hnonneg : ∀ k, k < n → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → 0 ≤ val f k a b := by
            intro k hk a b ha hab hb
            exact intervalIntegral.integral_nonneg hab (fun x hx => le_of_lt (hpos k hk x ⟨by linarith [hx.1], by linarith [hx.2]⟩))
          have hposv : ∀ k, k < n → ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → 0 < val f k a b := by
            intro k hk a b ha hab hb
            exact intervalIntegral.intervalIntegral_pos_of_pos_on (hint k hk a b ⟨ha, by linarith⟩ ⟨by linarith, hb⟩)
              (fun x hx => hpos k hk x ⟨by linarith [hx.1], by linarith [hx.2]⟩) hab
          have hsm : ∀ k, k < n → ∀ ℓ a b, ℓ ∈ Set.Icc (0:ℝ) 1 → a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 →
              a < b → val f k ℓ a < val f k ℓ b := by
            intro k hk ℓ a b hl ha hb hab
            rw [← hadd k hk ℓ a b hl ha hb]
            linarith [hposv k hk a b ha.1 hab hb.2]
          have hle_iff : ∀ k, k < n → ∀ ℓ a b, ℓ ∈ Set.Icc (0:ℝ) 1 → a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 →
              (val f k ℓ a ≤ val f k ℓ b ↔ a ≤ b) := by
            intro k hk ℓ a b hl ha hb
            constructor
            · intro h; by_contra h'; push Not at h'; linarith [hsm k hk ℓ b a hl hb ha h']
            · intro h; rcases h.lt_or_eq with h | h
              · exact (hsm k hk ℓ a b hl ha hb h).le
              · rw [h]
          have hcont : ∀ k, k < n → ∀ ℓ ∈ Set.Icc (0:ℝ) 1, ContinuousOn (fun y => val f k ℓ y) (Set.Icc ℓ 1) := by
            intro k hk ℓ hl
            have := intervalIntegral.continuousOn_primitive_interval' (a := ℓ) (hint k hk ℓ 1 hl ⟨zero_le_one, le_rfl⟩)
              (by rw [Set.uIcc_of_le hl.2]; exact ⟨le_rfl, hl.2⟩)
            rw [Set.uIcc_of_le hl.2] at this
            exact this
          have hcut : ∀ k, k < n → ∀ ℓ τ, ℓ ∈ Set.Icc (0:ℝ) 1 → 0 ≤ τ → τ ≤ val f k ℓ 1 →
              cut f k ℓ τ ∈ Set.Icc ℓ 1 ∧ val f k ℓ (cut f k ℓ τ) = τ := by
            intro k hk ℓ τ hℓ hτ0 hτ1
            obtain ⟨y, hy, hyv⟩ : ∃ y ∈ Set.Icc ℓ 1, val f k ℓ y = τ := by
              have := intermediate_value_Icc hℓ.2 (hcont k hk ℓ hℓ)
              have hl : val f k ℓ ℓ = 0 := intervalIntegral.integral_same
              exact this ⟨by rw [hl]; exact hτ0, hτ1⟩
            have hy01 : y ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hℓ.1 hy.1, hy.2⟩
            have hS : {y | y ∈ Set.Icc ℓ 1 ∧ val f k ℓ y = τ} = {y} := by
              ext z; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]; constructor
              · rintro ⟨hz, hzv⟩
                have hz01 : z ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hℓ.1 hz.1, hz.2⟩
                rcases lt_trichotomy z y with h|h|h
                · have := hsm k hk ℓ z y hℓ hz01 hy01 h; linarith
                · exact h
                · have := hsm k hk ℓ y z hℓ hy01 hz01 h; linarith
              · rintro rfl; exact ⟨hy, hyv⟩
            have hex : ∃ y ∈ Set.Icc ℓ 1, val f k ℓ y = τ := ⟨y, hy, hyv⟩
            unfold cut; rw [if_pos hex, hS, csInf_singleton]; exact ⟨hy, hyv⟩
          have hcutrange : ∀ k ℓ τ, ℓ ≤ 1 → ℓ ≤ cut f k ℓ τ ∧ cut f k ℓ τ ≤ 1 := by
            intro k ℓ τ hℓ
            unfold cut
            split_ifs with h
            · obtain ⟨y, hy, hyv⟩ := h
              have hne : ({y | y ∈ Set.Icc ℓ 1 ∧ val f k ℓ y = τ}).Nonempty := ⟨y, hy, hyv⟩
              have hbdd : BddBelow {y | y ∈ Set.Icc ℓ 1 ∧ val f k ℓ y = τ} := ⟨ℓ, fun z hz => hz.1.1⟩
              exact ⟨le_csInf hne (fun z hz => hz.1.1), (csInf_le hbdd ⟨hy, hyv⟩).trans hy.2⟩
            · exact ⟨hℓ, le_rfl⟩
          have hmk : ∀ τ k, mk f k τ ∈ Set.Icc (0:ℝ) 1 := by
            intro τ k
            induction k with
            | zero => exact ⟨le_rfl, zero_le_one⟩
            | succ k ih =>
              have := hcutrange k (mk f k τ) τ ih.2
              exact ⟨le_trans ih.1 this.1, this.2⟩
          have hmkstep : ∀ τ k, mk f (k+1) τ = cut f k (mk f k τ) τ := fun τ k => rfl
          have hev : ∀ k a b, a ≤ b → eval f k a b = val f k a b := by
            intro k a b hab
            rw [eval, val, intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]
          -- MLRP cross ratio
          have hcons : ∀ i, i + 1 < n → ∀ s u, s ∈ Set.Icc (0:ℝ) 1 → u ∈ Set.Icc (0:ℝ) 1 → s ≤ u →
              dens f (i+1) s * dens f i u ≤ dens f i s * dens f (i+1) u := by
            intro i hi s u hs hu hsu
            have h := hM.2 ⟨i, by omega⟩ ⟨i+1, hi⟩ rfl s u hs.1 hsu hu.2
            rw [div_le_div_iff₀ (hM.1 _ s hs) (hM.1 _ u hu)] at h
            rw [hdens i (by omega), hdens (i+1) hi]
            linarith
          have hratio0 : ∀ d k, k + d + 1 < n → ∀ s u, s ∈ Set.Icc (0:ℝ) 1 → u ∈ Set.Icc (0:ℝ) 1 → s ≤ u →
              dens f (k+d+1) s * dens f k u ≤ dens f k s * dens f (k+d+1) u := by
            intro d
            induction d with
            | zero => intro k hk s u hs hu hsu; simpa using hcons k (by omega) s u hs hu hsu
            | succ d ih =>
              intro k hk s u hs hu hsu
              have h2 := ih k (by omega) s u hs hu hsu
              have h1 := hcons (k+d+1) (by omega) s u hs hu hsu
              have e : k + (d+1) + 1 = k + d + 1 + 1 := by omega
              rw [e]
              set A := dens f (k+d+1+1) s
              set B := dens f (k+d+1) u
              set C := dens f (k+d+1) s
              set D := dens f k u
              set E := dens f (k+d+1+1) u
              set G := dens f k s
              have hB : 0 < B := hpos _ (by omega) u hu
              have hC : 0 < C := hpos _ (by omega) s hs
              have hA : 0 < A := hpos _ (by omega) s hs
              have hD : 0 < D := hpos _ (by omega) u hu
              have hE : 0 < E := hpos _ (by omega) u hu
              have hm := mul_le_mul h1 h2 (mul_pos hC hD).le (mul_pos hC hE).le
              have : (A * D) * (C * B) ≤ (G * E) * (C * B) := by nlinarith
              exact le_of_mul_le_mul_right this (mul_pos hC hB)
          have hratio : ∀ k j, k < j → j < n → ∀ s u, s ∈ Set.Icc (0:ℝ) 1 → u ∈ Set.Icc (0:ℝ) 1 → s ≤ u →
              dens f j s * dens f k u ≤ dens f k s * dens f j u := by
            intro k j hkj hj
            obtain ⟨d, rfl⟩ : ∃ d, j = k + d + 1 := ⟨j - k - 1, by omega⟩
            exact hratio0 d k hj
          have hrho : ∀ k j, k < j → j < n → ∀ m ∈ Set.Icc (0:ℝ) 1,
              (∀ a b, 0 ≤ a → a ≤ b → b ≤ m → val f j a b ≤ (dens f j m / dens f k m) * val f k a b) ∧
              (∀ c d, m ≤ c → c ≤ d → d ≤ 1 → (dens f j m / dens f k m) * val f k c d ≤ val f j c d) := by
            intro k j hkj hj m hm
            have hkm : 0 < dens f k m := hpos k (by omega) m hm
            constructor
            · intro a b ha hab hb
              have ha' : a ∈ Set.Icc (0:ℝ) 1 := ⟨ha, by linarith [hm.2]⟩
              have hb' : b ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith [hm.2]⟩
              unfold val
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_mono_on hab (hint j hj a b ha' hb') ((hint k (by omega) a b ha' hb').const_mul _)
              intro x hx
              have hx' : x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2, hm.2]⟩
              have := hratio k j hkj hj x m hx' hm (by linarith [hx.2])
              rw [div_mul_eq_mul_div, le_div_iff₀ hkm]
              linarith
            · intro c d hc hcd hd
              have hc' : c ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hm.1], by linarith⟩
              have hd' : d ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hm.1], hd⟩
              unfold val
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_mono_on hcd ((hint k (by omega) c d hc' hd').const_mul _) (hint j hj c d hc' hd')
              intro x hx
              have hx' : x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.1, hm.1], by linarith [hx.2]⟩
              have := hratio k j hkj hj m x hm hx' (by linarith [hx.1])
              rw [div_mul_eq_mul_div, div_le_iff₀ hkm]
              linarith
          have hshift : ∀ k j, k < j → j < n → ∀ p q p' q' : ℝ, 0 ≤ p → p ≤ q → q ≤ 1 → 0 ≤ p' → p' ≤ q' →
              q' ≤ 1 → p ≤ p' → q ≤ q' → val f k p q = val f k p' q' → val f j p q ≤ val f j p' q' := by
            intro k j hkj hj p q p' q' hp hpq hq hp' hpq' hq' hpp hqq heq
            have hk : k < n := by omega
            rcases le_or_gt q p' with h | h
            · obtain ⟨r1, r2⟩ := hrho k j hkj hj q ⟨by linarith, hq⟩
              have a1 := r1 p q hp hpq le_rfl
              have a2 := r2 p' q' h hpq' hq'
              rw [heq] at a1; linarith
            · obtain ⟨r1, r2⟩ := hrho k j hkj hj p' ⟨hp', by linarith⟩
              have a1 := r1 p p' hp hpp le_rfl
              have a2 := r2 q q' h.le hqq hq'
              have I : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → z ∈ Set.Icc (0:ℝ) 1 := fun z h1 h2 => ⟨h1, h2⟩
              have e1 := hadd j hj p p' q (I p hp (by linarith)) (I p' hp' (by linarith)) (I q (by linarith) hq)
              have e2 := hadd j hj p' q q' (I p' hp' (by linarith)) (I q (by linarith) hq) (I q' (by linarith) hq')
              have e3 := hadd k hk p p' q (I p hp (by linarith)) (I p' hp' (by linarith)) (I q (by linarith) hq)
              have e4 := hadd k hk p' q q' (I p' hp' (by linarith)) (I q (by linarith) hq) (I q' (by linarith) hq')
              have e5 : val f k p p' = val f k q q' := by linarith
              rw [e5] at a1; linarith
          have hkey : ∀ τ : ℝ, 0 ≤ τ → ∀ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x →
              (∀ i, τ ≤ pieceVal f x σ i) → ewFeasible f τ := by
            intro τ hτ x σ hx hxv
            obtain ⟨hx0, hxs, hxn⟩ := hx
            have hxmono : ∀ a b, a ≤ b → b ≤ n → x a ≤ x b := by
              intro a b hab hb
              induction b with
              | zero =>
                have : a = 0 := by omega
                subst this; exact le_rfl
              | succ b ih =>
                rcases Nat.lt_or_ge b a with h | h
                · have : a = b+1 := by omega
                  subst this; exact le_rfl
                · exact le_trans (ih h (by omega)) (hxs b (by omega))
            have hx01 : ∀ a, a ≤ n → x a ∈ Set.Icc (0:ℝ) 1 := fun a ha =>
              ⟨hx0 ▸ hxmono 0 a (Nat.zero_le _) ha, hxn ▸ hxmono a n ha le_rfl⟩
            let M := fun k => mk f k τ
            let H : ℕ → Prop := fun k => ∃ p q : ℕ → ℝ,
              (∀ j, k ≤ j → j < n → M k ≤ p j ∧ p j ≤ q j ∧ q j ≤ 1 ∧ τ ≤ val f j (p j) (q j)) ∧
              (∀ j j', k ≤ j → j < n → k ≤ j' → j' < n → j ≠ j' → q j ≤ p j' ∨ q j' ≤ p j)
            have H0 : H 0 := by
              refine ⟨fun j => if h : j < n then x (σ ⟨j, h⟩) else 0,
                fun j => if h : j < n then x ((σ ⟨j, h⟩ : ℕ) + 1) else 0, ?_, ?_⟩
              · intro j _ hj
                simp only [hj, dif_pos]
                have h1 := hx01 (σ ⟨j,hj⟩) (σ ⟨j,hj⟩).is_lt.le
                refine ⟨?_, hxs _ (σ ⟨j,hj⟩).is_lt, (hx01 _ (σ ⟨j,hj⟩).is_lt).2, hxv ⟨j,hj⟩⟩
                show (0:ℝ) ≤ _
                exact h1.1
              · intro j j' _ hj _ hj' hne
                simp only [hj, hj', dif_pos]
                have hne' : (σ ⟨j,hj⟩ : ℕ) ≠ σ ⟨j',hj'⟩ := by
                  intro h; apply hne; have := σ.injective (Fin.ext h); simpa using this
                rcases Nat.lt_or_gt_of_ne hne' with h | h
                · left; exact hxmono _ _ h (σ ⟨j',hj'⟩).is_lt.le
                · right; exact hxmono _ _ h (σ ⟨j,hj⟩).is_lt.le
            have Hstep : ∀ k, k < n → H k → H (k+1) := by
              rintro k hk ⟨p, q, hP, hD⟩
              have hℓ : M k ∈ Set.Icc (0:ℝ) 1 := hmk τ k
              obtain ⟨hpk1, hpk2, hpk3, hpk4⟩ := hP k le_rfl hk
              have hpk01 : p k ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hℓ.1 hpk1, le_trans hpk2 hpk3⟩
              have hqk01 : q k ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hpk01.1 hpk2, hpk3⟩
              have e1 := hadd k hk (M k) (p k) (q k) hℓ hpk01 hqk01
              have e2 := hadd k hk (M k) (q k) 1 hℓ hqk01 ⟨zero_le_one, le_rfl⟩
              have n1 := hnonneg k hk (M k) (p k) hℓ.1 hpk1 hpk01.2
              have n2 := hnonneg k hk (q k) 1 hqk01.1 hqk01.2 le_rfl
              have hM1 : M (k+1) = cut f k (M k) τ := rfl
              obtain ⟨hc1, hc2⟩ := hcut k hk (M k) τ hℓ hτ (by linarith)
              have hM101 : M (k+1) ∈ Set.Icc (0:ℝ) 1 := hmk τ (k+1)
              have hc2' : val f k (M k) (M (k+1)) = τ := hc2
              have hMq : M (k+1) ≤ q k := by
                rw [← hle_iff k hk (M k) _ _ hℓ hM101 hqk01, hc2']; linarith
              let φ := fun y => cut f k (M k) (val f k (M k) y + τ)
              have hφ : ∀ y, M k ≤ y → y ≤ p k → φ y ∈ Set.Icc (0:ℝ) 1 ∧
                  val f k (M k) (φ y) = val f k (M k) y + τ ∧ y ≤ φ y ∧ M (k+1) ≤ φ y := by
                intro y h1 h2
                have hy : y ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hℓ.1 h1, by linarith [hpk01.2]⟩
                have e3 := hadd k hk (M k) y (p k) hℓ hy hpk01
                have n3 := hnonneg k hk (M k) y hℓ.1 h1 hy.2
                have n4 := hnonneg k hk y (p k) hy.1 h2 hpk01.2
                obtain ⟨hr, hv⟩ := hcut k hk (M k) (val f k (M k) y + τ) hℓ (by linarith) (by linarith)
                have hφ01 : φ y ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hℓ.1 hr.1, hr.2⟩
                have hv' : val f k (M k) (φ y) = val f k (M k) y + τ := hv
                refine ⟨hφ01, hv', ?_, ?_⟩
                · rw [← hle_iff k hk (M k) _ _ hℓ hy hφ01, hv']; linarith
                · rw [← hle_iff k hk (M k) _ _ hℓ hM101 hφ01, hv', hc2']; linarith
              have hφmono : ∀ a b, M k ≤ a → a ≤ b → b ≤ p k → φ a ≤ φ b := by
                intro a b h1 h2 h3
                obtain ⟨a1, a2, -, -⟩ := hφ a h1 (by linarith)
                obtain ⟨b1, b2, -, -⟩ := hφ b (by linarith) h3
                have ha : a ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hℓ.1 h1, by linarith [hpk01.2]⟩
                have hb : b ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hℓ.1 (le_trans h1 h2), by linarith [hpk01.2]⟩
                rw [← hle_iff k hk (M k) _ _ hℓ a1 b1, a2, b2]
                have := (hle_iff k hk (M k) _ _ hℓ ha hb).2 h2
                linarith
              have hφpk : φ (p k) ≤ q k := by
                obtain ⟨a1, a2, -, -⟩ := hφ (p k) hpk1 le_rfl
                rw [← hle_iff k hk (M k) _ _ hℓ a1 hqk01, a2]; linarith
              have hφval : ∀ a b, M k ≤ a → a ≤ b → b ≤ p k → val f k (φ a) (φ b) = val f k a b := by
                intro a b h1 h2 h3
                obtain ⟨a1, a2, -, -⟩ := hφ a h1 (by linarith)
                obtain ⟨b1, b2, -, -⟩ := hφ b (by linarith) h3
                have ha : a ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hℓ.1 h1, by linarith [hpk01.2]⟩
                have hb : b ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hℓ.1 (le_trans h1 h2), by linarith [hpk01.2]⟩
                have f1 := hadd k hk (M k) (φ a) (φ b) hℓ a1 b1
                have f2 := hadd k hk (M k) a b hℓ ha hb
                linarith
              refine ⟨fun j => if q j ≤ p k then φ (p j) else p j,
                fun j => if q j ≤ p k then φ (q j) else q j, ?_, ?_⟩
              · intro j hj1 hj2
                obtain ⟨h1, h2, h3, h4⟩ := hP j (by omega) hj2
                by_cases hB : q j ≤ p k
                · simp only [if_pos hB]
                  obtain ⟨a1, a2, a3, a4⟩ := hφ (p j) h1 (by linarith)
                  obtain ⟨b1, b2, b3, b4⟩ := hφ (q j) (by linarith) hB
                  have hmo := hφmono _ _ h1 h2 hB
                  refine ⟨a4, hmo, b1.2, ?_⟩
                  have hpj0 : 0 ≤ p j := le_trans hℓ.1 h1
                  exact le_trans h4 (hshift k j (by omega) hj2 (p j) (q j) (φ (p j)) (φ (q j)) hpj0 h2 h3
                    a1.1 hmo b1.2 a3 b3 (hφval _ _ h1 h2 hB).symm)
                · simp only [if_neg hB]
                  have := hD k j le_rfl hk (by omega) hj2 (by omega)
                  have hqp : q k ≤ p j := by tauto
                  exact ⟨le_trans hMq hqp, h2, h3, h4⟩
              · intro j j' hj1 hj2 hj1' hj2' hne
                have Dj := hD j j' (by omega) hj2 (by omega) hj2' hne
                obtain ⟨h1, h2, h3, h4⟩ := hP j (by omega) hj2
                obtain ⟨h1', h2', h3', h4'⟩ := hP j' (by omega) hj2'
                by_cases hB : q j ≤ p k <;> by_cases hB' : q j' ≤ p k
                · simp only [if_pos hB, if_pos hB']
                  rcases Dj with d | d
                  · left; exact hφmono _ _ (by linarith) d (by linarith)
                  · right; exact hφmono _ _ (by linarith) d (by linarith)
                · simp only [if_pos hB, if_neg hB']
                  left
                  have hq' : q k ≤ p j' := by
                    have := hD k j' le_rfl hk (by omega) hj2' (by omega); tauto
                  exact le_trans (hφmono _ _ (by linarith) hB le_rfl) (le_trans hφpk hq')
                · simp only [if_neg hB, if_pos hB']
                  right
                  have hq' : q k ≤ p j := by
                    have := hD k j le_rfl hk (by omega) hj2 (by omega); tauto
                  exact le_trans (hφmono _ _ (by linarith) hB' le_rfl) (le_trans hφpk hq')
                · simp only [if_neg hB, if_neg hB']
                  exact Dj
            have Hall : ∀ k, k ≤ n → H k := by
              intro k; induction k with
              | zero => intro _; exact H0
              | succ k ih => intro hk; exact Hstep k (by omega) (ih (by omega))
            intro i hi
            obtain ⟨p, q, hP, -⟩ := Hall i hi.le
            obtain ⟨h1, h2, h3, h4⟩ := hP i le_rfl hi
            have hMi : M i ∈ Set.Icc (0:ℝ) 1 := hmk τ i
            have hp01 : p i ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hMi.1 h1, le_trans h2 h3⟩
            have hq01 : q i ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hp01.1 h2, h3⟩
            have f1 := hadd i hi (M i) (p i) (q i) hMi hp01 hq01
            have f2 := hadd i hi (M i) (q i) 1 hMi hq01 ⟨zero_le_one, le_rfl⟩
            have g1 := hnonneg i hi (M i) (p i) hMi.1 h1 hp01.2
            have g2 := hnonneg i hi (q i) 1 hq01.1 hq01.2 le_rfl
            have hτi : τ ≤ val f i (mk f i τ) 1 := by show τ ≤ val f i (M i) 1; linarith
            obtain ⟨hr, hv⟩ := hcut i hi (mk f i τ) τ hMi hτ hτi
            rw [hmkstep, hev i _ _ hr.1]
            exact hv
          set m := ewMesh η with hmdef
          have hm1 : (1:ℝ) / η ≤ m := Nat.le_ceil _
          have hmposR : (0:ℝ) < m := lt_of_lt_of_le (by positivity) hm1
          have hmpos : 0 < m := by exact_mod_cast hmposR
          have hinvm : 1 / (m:ℝ) ≤ η := by
            rw [div_le_iff₀ hη] at hm1
            rw [div_le_iff₀ hmposR]; linarith
          have hmk0 : ∀ k, k ≤ n → mk f k 0 = 0 := by
            intro k; induction k with
            | zero => intro _; rfl
            | succ k ih =>
              intro hk
              rw [hmkstep, ih (by omega)]
              have h01 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
              obtain ⟨hr, hv⟩ := hcut k (by omega) 0 0 h01 le_rfl (hnonneg k (by omega) 0 1 le_rfl zero_le_one le_rfl)
              by_contra hne
              have := hposv k (by omega) 0 (cut f k 0 0) le_rfl (lt_of_le_of_ne hr.1 (Ne.symm hne)) hr.2
              linarith
          have hfeas0 : ewFeasible f 0 := by
            intro i hi
            rw [hmk0 i hi.le, hmk0 (i+1) hi, hev i 0 0 le_rfl]
            exact intervalIntegral.integral_same
          have hinv : ∀ s, (ewIter f η s).1 < (ewIter f η s).2 ∧ (ewIter f η s).2 ≤ m + 1 ∧
              ewFeasible f (((ewIter f η s).1 : ℝ) / m) ∧
              ((ewIter f η s).2 = m + 1 ∨ ¬ ewFeasible f (((ewIter f η s).2 : ℝ) / m)) ∧
              ((ewIter f η s).2 - (ewIter f η s).1 - 1) * 2 ^ s ≤ m := by
            intro s
            induction s with
            | zero =>
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · show 0 < m + 1; omega
              · show m + 1 ≤ m + 1; exact le_rfl
              · show ewFeasible f (((0:ℕ):ℝ) / m); simpa using hfeas0
              · left; rfl
              · show (m + 1 - 0 - 1) * 2 ^ 0 ≤ m; simp
            | succ s ih =>
              obtain ⟨i1, i2, i3, i4, i5⟩ := ih
              classical
              rw [show ewIter f η (s+1) = (if (ewIter f η s).2 ≤ (ewIter f η s).1 + 1 then ewIter f η s
                  else if ewFeasible f ((((ewIter f η s).1 + (ewIter f η s).2) / 2 : ℕ) / (ewMesh η : ℝ))
                    then (((ewIter f η s).1 + (ewIter f η s).2) / 2, (ewIter f η s).2)
                    else ((ewIter f η s).1, ((ewIter f η s).1 + (ewIter f η s).2) / 2)) from rfl]
              generalize ewIter f η s = P at *
              obtain ⟨lo, hi⟩ := P
              simp only at *
              rw [pow_succ]
              split_ifs with h1 h2
              · refine ⟨i1, i2, i3, i4, ?_⟩
                have : hi - lo - 1 = 0 := by omega
                rw [this]; simp
              · refine ⟨by omega, i2, h2, i4, ?_⟩
                calc (hi - (lo+hi)/2 - 1) * (2^s * 2) = (2 * (hi - (lo+hi)/2 - 1)) * 2^s := by ring
                  _ ≤ (hi - lo - 1) * 2^s := Nat.mul_le_mul_right _ (by omega)
                  _ ≤ m := i5
              · refine ⟨by omega, by omega, i3, Or.inr h2, ?_⟩
                calc ((lo+hi)/2 - lo - 1) * (2^s * 2) = (2 * ((lo+hi)/2 - lo - 1)) * 2^s := by ring
                  _ ≤ (hi - lo - 1) * 2^s := Nat.mul_le_mul_right _ (by omega)
                  _ ≤ m := i5
          refine ⟨?_, ?_, ?_⟩
          · refine ⟨?_, ?_, ?_⟩
            · simp only [ewOutput, coalesce, if_neg (show (0:ℕ) ≠ n by omega)]; rfl
            · intro k hk
              simp only [ewOutput, coalesce, if_neg (show k ≠ n by omega)]
              split_ifs with h
              · exact (hmk _ k).2
              · exact (hcutrange k _ _ (hmk _ k).2).1
            · simp [ewOutput, coalesce]
          · intro x σ hx
            obtain ⟨i1, i2, i3, i4, i5⟩ := hinv (ewSteps η)
            set P := ewIter f η (ewSteps η) with hP
            have hg : P.2 = P.1 + 1 := by
              by_contra hne
              have h1 : 1 * 2 ^ (ewSteps η) ≤ (P.2 - P.1 - 1) * 2 ^ (ewSteps η) :=
                Nat.mul_le_mul_right _ (by omega)
              have h2 : m + 1 ≤ 2 ^ (ewSteps η) := Nat.le_pow_clog (by norm_num) (m+1)
              generalize (P.2 - P.1 - 1) * 2 ^ (ewSteps η) = A at h1 i5
              generalize 2 ^ (ewSteps η) = T at h1 h2
              omega
            set τ0 := ewTarget f η with hτ0
            have i3' : ewFeasible f τ0 := i3
            have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
            have hout : τ0 ≤ EW f (ewOutput f η) (Equiv.refl (Fin n)) := by
              apply le_ciInf
              intro i
              have hin : (i:ℕ) ≠ n := by omega
              have hfe := i3' i i.is_lt
              have ha := hmk τ0 i
              have hab := (hcutrange i (mk f i τ0) τ0 ha.2)
              show τ0 ≤ val f (i:ℕ) (coalesce n (fun k => mk f k (ewTarget f η)) (i:ℕ))
                (coalesce n (fun k => mk f k (ewTarget f η)) ((i:ℕ)+1))
              unfold coalesce
              simp only [if_neg hin, ← hτ0]
              rw [hmkstep, hev _ _ _ hab.1] at hfe
              split_ifs with h
              · have hb01 : cut f i (mk f i τ0) τ0 ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans ha.1 hab.1, hab.2⟩
                have e := hadd i i.is_lt (mk f i τ0) (cut f i (mk f i τ0) τ0) 1 ha hb01 ⟨zero_le_one, le_rfl⟩
                have nn := hnonneg i i.is_lt _ 1 hb01.1 hb01.2 le_rfl
                linarith
              · exact hfe.ge
            by_contra hcon
            push Not at hcon
            have hEW : ∀ i, EW f x σ ≤ pieceVal f x σ i := fun i => ciInf_le (Finite.bddBelow_range _) i
            have hhi : (P.2 : ℝ) / m ≤ τ0 + η := by
              have : ((P.1 + 1 : ℕ) : ℝ) / m = (P.1:ℝ)/m + 1/m := by push_cast; ring
              rw [hg, this]
              have : τ0 = (P.1 : ℝ) / m := rfl
              linarith
            rcases i4 with h4 | h4
            · -- top of grid: target is 1
              have hP1 : P.1 = m := by omega
              have hτ1 : τ0 = 1 := by
                show (P.1 : ℝ) / m = 1
                rw [hP1]; exact div_self hmposR.ne'
              obtain ⟨hx0, hxs, hxn⟩ := hx
              have hxmono : ∀ a b, a ≤ b → b ≤ n → x a ≤ x b := by
                intro a b hab hb
                induction b with
                | zero =>
                  have : a = 0 := by omega
                  subst this; exact le_rfl
                | succ b ih =>
                  rcases Nat.lt_or_ge b a with h | h
                  · have : a = b+1 := by omega
                    subst this; exact le_rfl
                  · exact le_trans (ih h (by omega)) (hxs b (by omega))
              let i0 : Fin n := ⟨0, by omega⟩
              have ha : x (σ i0) ∈ Set.Icc (0:ℝ) 1 :=
                ⟨hx0 ▸ hxmono 0 _ (Nat.zero_le _) (σ i0).is_lt.le, hxn ▸ hxmono _ n (σ i0).is_lt.le le_rfl⟩
              have hb : x ((σ i0 : ℕ) + 1) ∈ Set.Icc (0:ℝ) 1 :=
                ⟨hx0 ▸ hxmono 0 _ (Nat.zero_le _) (σ i0).is_lt, hxn ▸ hxmono _ n (σ i0).is_lt le_rfl⟩
              have hle := hxs _ (σ i0).is_lt
              have e1 := hadd 0 (by omega) 0 (x (σ i0)) 1 ⟨le_rfl, zero_le_one⟩ ha ⟨zero_le_one, le_rfl⟩
              have e2 := hadd 0 (by omega) (x (σ i0)) (x ((σ i0 : ℕ) + 1)) 1 ha hb ⟨zero_le_one, le_rfl⟩
              have n1 := hnonneg 0 (by omega) 0 (x (σ i0)) le_rfl ha.1 ha.2
              have n2 := hnonneg 0 (by omega) (x ((σ i0 : ℕ) + 1)) 1 hb.1 hb.2 le_rfl
              have ht := htot 0 (by omega)
              have hpv : pieceVal f x σ i0 = val f 0 (x (σ i0)) (x ((σ i0 : ℕ) + 1)) := rfl
              have := hEW i0
              linarith
            · apply h4
              have hnn : (0:ℝ) ≤ (P.2 : ℝ) / m := by positivity
              exact hkey _ hnn x σ hx (fun i => by linarith [hEW i])
          · set L := max 0 (Real.logb 2 (1/η)) with hLdef
            have hL0 : 0 ≤ L := le_max_left _ _
            have hLge : Real.logb 2 (1/η) ≤ L := le_max_right _ _
            have hlog0 : 0 ≤ Real.logb 2 lam := Real.logb_nonneg one_lt_two hlam
            have hKle : ((⌈L⌉₊ + 2 : ℕ) : ℝ) ≤ L + 3 := by
              have := Nat.ceil_lt_add_one hL0; push_cast; linarith
            have h2K : ((m + 1 : ℕ) : ℝ) ≤ 2 ^ (⌈L⌉₊ + 2) := by
              have hc : (m:ℝ) < 1/η + 1 := Nat.ceil_lt_add_one (by positivity)
              have h2L : (2:ℝ) ^ L ≤ 2 ^ (⌈L⌉₊ : ℕ) := by
                rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)
              have h1 : 1/η ≤ (2:ℝ)^L := by
                calc 1/η = (2:ℝ) ^ (Real.logb 2 (1/η)) := (Real.rpow_logb two_pos (by norm_num) (by positivity)).symm
                  _ ≤ 2 ^ L := Real.rpow_le_rpow_of_exponent_le one_le_two hLge
              have h1' : (1:ℝ) ≤ 2^L := Real.one_le_rpow one_le_two hL0
              have : (2:ℝ)^(⌈L⌉₊ + 2) = 4 * 2^(⌈L⌉₊) := by rw [pow_add]; ring
              push_cast; rw [this]
              rcases le_or_gt (1/η) 1 with h | h <;> nlinarith
            have hsteps : ewSteps η ≤ ⌈L⌉₊ + 2 := Nat.clog_le_of_le_pow (by exact_mod_cast h2K)
            have hS : (ewSteps η : ℝ) ≤ L + 3 := le_trans (by exact_mod_cast hsteps) hKle
            have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
            set X := (n:ℝ) + Real.logb 2 lam + L + 1 with hX
            have hX1 : 1 ≤ X := by linarith
            have hnX : (n:ℝ) ≤ X := by linarith
            have hLX : L + 3 ≤ 3 * X := by linarith
            have hcost : (ewCost n η : ℝ) = (ewSteps η : ℝ) * (2 * n) + n := by
              simp only [ewCost]; push_cast; ring
            rw [hcost]
            have hS0 : (0:ℝ) ≤ ewSteps η := by positivity
            have hm1' := mul_le_mul (hS.trans hLX) (show 2 * (n:ℝ) ≤ 2 * X by linarith) (by positivity) (by linarith)
            have hX2 : X ^ 2 ≤ X ^ 7 := pow_le_pow_right₀ hX1 (by norm_num)
            have hXX : X ≤ X ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by linarith only [hX1]) hX1
            have hsq : 3 * X * (2 * X) = 6 * X ^ 2 := by ring
            push_cast
            linarith only [hm1', hnX, hX2, hXX, hsq]
