-- Prove2me | solution 1 for KellyLossNetworks.RevisedDual.Supplement.theorem_4_40
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:32:33.776277+00:00
-- url     : https://prove2.me/submissions/83020ecd-e206-4010-80b0-fe6f79295f15

import Mathlib
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_RedWhite

open Filter Topology

open KellyLossNetworks
open KellyLossNetworks.RevisedDual
open KellyLossNetworks.RevisedDual.Supplement

/-- **Theorem 4.40** (due to Hajek). For `p < 1/3`, `P(K) → 1` as `K → ∞`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 357, Theorem 4.40; the model and `P(K)` on pp. 356–357, §4.6.

**Formalization Note.** `whiteRoutingProb p K` is `P(K)`: the probability, when each edge of
the complete graph on `K` nodes is independently red with probability `p`, that every red pair
can split its unit of excess traffic over two-white-edge paths with no white edge carrying
more than one unit (`WhiteRoutable`). The parameter range is the paper's `p ∈ (0, 1)` (p. 356)
intersected with `p < 1/3`. -/
theorem solution (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 3) :
    Tendsto (fun K : ℕ => whiteRoutingProb p K) atTop (𝓝 1) := by
      classical
      have master : ∀ (K : ℕ) (G : KellyLossNetworks.Routing.Edge K → Bool → ℝ),
          ∑ red : KellyLossNetworks.Routing.Edge K → Bool, colouringProb p red * ∏ e, G e (red e)
            = ∏ e, (p * G e true + (1 - p) * G e false) := by
        intro K G
        have := Fintype.prod_sum (fun (e : KellyLossNetworks.Routing.Edge K) (r : Bool) => (if r then p else 1 - p) * G e r)
        simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false] at this
        rw [this]
        refine Finset.sum_congr rfl fun red _ => ?_
        rw [colouringProb, ← Finset.prod_mul_distrib]
      have cardS : ∀ (K : ℕ) (x : Fin K) (S : Finset (Fin K)), (∀ b ∈ S, b ≠ x) →
          (Finset.univ.filter fun e : KellyLossNetworks.Routing.Edge K => ∃ b ∈ S, e.1 = s(x, b)).card = S.card := by
        intro K x S hS
        refine (Finset.card_bij (fun b hb => (⟨s(x, b), by
            rw [Sym2.mk_isDiag_iff]; exact (hS b hb).symm⟩ : KellyLossNetworks.Routing.Edge K)) ?_ ?_ ?_).symm
        · intro b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨b, hb, rfl⟩
        · intro b1 _ b2 _ h
          have := congrArg Subtype.val h
          exact Sym2.congr_right.mp this
        · intro e he
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
          obtain ⟨b, hb, hbe⟩ := he
          exact ⟨b, hb, Subtype.ext hbe.symm⟩
      have pairE : ∀ (K : ℕ) (a k : Fin K), a ≠ k → ∀ (u v : Bool) (S : Finset (Fin K)),
          (∀ b ∈ S, b ≠ a ∧ b ≠ k) →
          ∑ red : KellyLossNetworks.Routing.Edge K → Bool, colouringProb p red *
            (if ∀ b ∈ S, ((∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = u) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = v)) then 1 else 0)
            = ((if u then p else 1 - p) * (if v then p else 1 - p)) ^ S.card := by
        intro K a k hak u v S hS
        have h1 := master K (fun e r => if (∀ b ∈ S, e.1 = s(a, b) → r = u) ∧
          (∀ b ∈ S, e.1 = s(b, k) → r = v) then 1 else 0)
        have hL : ∀ red : KellyLossNetworks.Routing.Edge K → Bool, (∏ e, (fun e r => if (∀ b ∈ S, e.1 = s(a, b) → r = u) ∧
            (∀ b ∈ S, e.1 = s(b, k) → r = v) then (1:ℝ) else 0) e (red e)) =
            (if ∀ b ∈ S, ((∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = u) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = v)) then 1 else 0) := by
          intro red
          rw [Fintype.prod_boole]
          congr 1
          apply propext
          constructor
          · intro h b hb
            exact ⟨fun g hg => (h g).1 b hb hg, fun g hg => (h g).2 b hb hg⟩
          · intro h g
            exact ⟨fun b hb hg => (h b hb).1 g hg, fun b hb hg => (h b hb).2 g hg⟩
        simp only [hL] at h1
        rw [h1]
        have disj : ∀ e : KellyLossNetworks.Routing.Edge K, (∃ b ∈ S, e.1 = s(a, b)) → ¬ ∃ b ∈ S, e.1 = s(b, k) := by
          rintro e ⟨b, hb, hbe⟩ ⟨b', hb', hbe'⟩
          rw [hbe] at hbe'
          rcases Sym2.eq_iff.mp hbe' with h | h
          · exact (hS b' hb').1 h.1.symm
          · exact hak h.1
        have hval : ∀ e : KellyLossNetworks.Routing.Edge K, (p * (if (∀ b ∈ S, e.1 = s(a, b) → true = u) ∧
            (∀ b ∈ S, e.1 = s(b, k) → true = v) then (1:ℝ) else 0) +
            (1 - p) * (if (∀ b ∈ S, e.1 = s(a, b) → false = u) ∧
            (∀ b ∈ S, e.1 = s(b, k) → false = v) then (1:ℝ) else 0)) =
            if (∃ b ∈ S, e.1 = s(a, b)) then (if u then p else 1 - p) else
              if (∃ b ∈ S, e.1 = s(b, k)) then (if v then p else 1 - p) else 1 := by
          intro e
          by_cases hA : ∃ b ∈ S, e.1 = s(a, b)
          · have hB := disj e hA
            obtain ⟨b, hb, hbe⟩ := hA
            have hA' : ∃ b ∈ S, e.1 = s(a, b) := ⟨b, hb, hbe⟩
            push Not at hB
            have c1 : ∀ r : Bool, ((∀ b ∈ S, e.1 = s(a, b) → r = u) ∧
                (∀ b ∈ S, e.1 = s(b, k) → r = v)) ↔ r = u := fun r =>
              ⟨fun h => h.1 b hb hbe, fun h => ⟨fun _ _ _ => h, fun b' hb' h' => absurd h' (hB b' hb')⟩⟩
            simp only [c1, hA', if_true]
            cases u <;> simp
          · rw [if_neg hA]
            by_cases hB : ∃ b ∈ S, e.1 = s(b, k)
            · obtain ⟨b, hb, hbe⟩ := hB
              have hB' : ∃ b ∈ S, e.1 = s(b, k) := ⟨b, hb, hbe⟩
              push Not at hA
              have c1 : ∀ r : Bool, ((∀ b ∈ S, e.1 = s(a, b) → r = u) ∧
                  (∀ b ∈ S, e.1 = s(b, k) → r = v)) ↔ r = v := fun r =>
                ⟨fun h => h.2 b hb hbe, fun h => ⟨fun b' hb' h' => absurd h' (hA b' hb'), fun _ _ _ => h⟩⟩
              simp only [c1, hB', if_true]
              cases v <;> simp
            · rw [if_neg hB]
              push Not at hA hB
              rw [if_pos ⟨fun b hb h => absurd h (hA b hb), fun b hb h => absurd h (hB b hb)⟩,
                if_pos ⟨fun b hb h => absurd h (hA b hb), fun b hb h => absurd h (hB b hb)⟩]
              ring
        rw [Finset.prod_congr rfl fun e _ => hval e]
        generalize (if u then p else 1 - p) = wu
        generalize (if v then p else 1 - p) = wv
        rw [Finset.prod_ite, Finset.prod_ite,
          Finset.prod_const, Finset.prod_const, Finset.prod_const_one, mul_one,
          cardS K a S (fun b hb => (hS b hb).1)]
        have : ((Finset.univ.filter fun e : KellyLossNetworks.Routing.Edge K => ¬ ∃ b ∈ S, e.1 = s(a, b)).filter
            fun e : KellyLossNetworks.Routing.Edge K => ∃ b ∈ S, e.1 = s(b, k)) =
            (Finset.univ.filter fun e : KellyLossNetworks.Routing.Edge K => ∃ b ∈ S, e.1 = s(k, b)) := by
          ext e
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨_, b, hb, h⟩
            exact ⟨b, hb, h.trans Sym2.eq_swap⟩
          · rintro ⟨b, hb, h⟩
            have h' : ∃ b ∈ S, e.1 = s(b, k) := ⟨b, hb, h.trans Sym2.eq_swap⟩
            exact ⟨fun hA => disj e hA h', h'⟩
        rw [this, cardS K k S (fun b hb => (hS b hb).2), mul_pow]
      have sumone : ∀ K : ℕ, ∑ red : KellyLossNetworks.Routing.Edge K → Bool, colouringProb p red = 1 := by
        intro K
        have := master K (fun _ _ => 1)
        simp only [Finset.prod_const_one, mul_one] at this
        rw [this]
        simp
      have cpnn : ∀ (K : ℕ) (red : KellyLossNetworks.Routing.Edge K → Bool), 0 ≤ colouringProb p red := by
        intro K red
        refine Finset.prod_nonneg fun e _ => ?_
        split_ifs <;> linarith
      have cardB : ∀ (K : ℕ) (a k : Fin K), a ≠ k →
          ((Finset.univ : Finset (Fin K)) \ {a, k}).card = K - 2 := by
        intro K a k hak
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
          Finset.card_pair hak]
      have tail : ∀ (K : ℕ) (a k : Fin K), a ≠ k → ∀ (u v : Bool) (l θ : ℝ), |l| ≤ 1 →
          ∑ red : KellyLossNetworks.Routing.Edge K → Bool, colouringProb p red *
            (if θ ≤ l * (((Finset.univ : Finset (Fin K)) \ {a, k}).filter fun b =>
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = u) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = v)).card then 1 else 0)
            ≤ Real.exp (-θ + ((K - 2 : ℕ) : ℝ) * ((if u then p else 1 - p) * (if v then p else 1 - p))
                * (l + l ^ 2)) := by
        intro K a k hak u v l θ hl
        set B := ((Finset.univ : Finset (Fin K)) \ {a, k}) with hBdef
        have hB : ∀ b ∈ B, b ≠ a ∧ b ≠ k := by
          intro b hb
          simp only [hBdef, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
            Finset.mem_singleton, true_and, not_or] at hb
          exact hb
        set q := (if u then p else 1 - p) * (if v then p else 1 - p) with hq
        have hq0 : 0 ≤ q := by
          rw [hq]; apply mul_nonneg <;> split_ifs <;> linarith
        have hq1 : q ≤ 1 := by
          rw [hq]
          have h1 : (if u then p else 1 - p) ≤ 1 := by split_ifs <;> linarith
          have h2 : (if v then p else 1 - p) ≤ 1 := by split_ifs <;> linarith
          have h3 : 0 ≤ (if v then p else 1 - p) := by split_ifs <;> linarith
          nlinarith
        -- mgf
        have mgf : ∀ c : ℝ, ∑ red : KellyLossNetworks.Routing.Edge K → Bool, colouringProb p red *
            ∏ b ∈ B, (1 + c * (if (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = u) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = v) then 1 else 0)) = (1 + c * q) ^ (K - 2) := by
          intro c
          have e1 : ∀ red : KellyLossNetworks.Routing.Edge K → Bool, ∏ b ∈ B, (1 + c * (if (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = u) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = v) then (1:ℝ) else 0)) =
              ∑ T ∈ B.powerset, c ^ T.card * (if ∀ b ∈ T, ((∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = u) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = v)) then 1 else 0) := by
            intro red
            rw [Finset.prod_one_add]
            refine Finset.sum_congr rfl fun T _ => ?_
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_boole]
            congr
          simp only [e1, Finset.mul_sum]
          rw [Finset.sum_comm]
          have e2 : ∀ T ∈ B.powerset, ∑ red : KellyLossNetworks.Routing.Edge K → Bool, colouringProb p red * (c ^ T.card *
              (if ∀ b ∈ T, ((∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = u) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = v)) then (1:ℝ) else 0)) = ∏ b ∈ T, (c * q) := by
            intro T hT
            rw [Finset.mem_powerset] at hT
            simp only [mul_left_comm (colouringProb p _) (c ^ T.card)]
            rw [← Finset.mul_sum, pairE K a k hak u v T (fun b hb => hB b (hT hb)), Finset.prod_const,
              hq]
            ring
          rw [Finset.sum_congr rfl e2, ← Finset.prod_one_add, Finset.prod_const, cardB K a k hak]
        have hpt : ∀ red : KellyLossNetworks.Routing.Edge K → Bool,
            (if θ ≤ l * ((B.filter fun b =>
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = u) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = v)).card : ℝ) then (1:ℝ) else 0) ≤
            Real.exp (-θ) * ∏ b ∈ B, (1 + (Real.exp l - 1) *
              (if (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = u) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = v) then 1 else 0)) := by
          intro red
          have : ∏ b ∈ B, (1 + (Real.exp l - 1) *
              (if (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = u) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = v) then (1:ℝ) else 0)) =
              Real.exp (((B.filter fun b =>
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = u) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = v)).card : ℝ) * l) := by
            rw [Real.exp_nat_mul, ← Finset.prod_const, Finset.prod_filter]
            refine Finset.prod_congr rfl fun b _ => ?_
            split_ifs <;> ring
          rw [this, ← Real.exp_add]
          split_ifs with h
          · exact Real.one_le_exp (by linarith)
          · exact (Real.exp_pos _).le
        calc _ ≤ ∑ red : KellyLossNetworks.Routing.Edge K → Bool, colouringProb p red * (Real.exp (-θ) * ∏ b ∈ B, (1 + (Real.exp l - 1) *
              (if (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = u) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = v) then 1 else 0))) :=
              Finset.sum_le_sum fun red _ => mul_le_mul_of_nonneg_left (hpt red) (cpnn K red)
          _ = Real.exp (-θ) * (1 + (Real.exp l - 1) * q) ^ (K - 2) := by
              rw [← mgf, Finset.mul_sum]
              refine Finset.sum_congr rfl fun red _ => ?_
              ring
          _ ≤ Real.exp (-θ) * Real.exp ((l + l ^ 2) * q) ^ (K - 2) := by
              refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ _) (Real.exp_pos _).le
              · nlinarith [Real.exp_pos l]
              · have h1 := Real.add_one_le_exp ((Real.exp l - 1) * q)
                have h2 : Real.exp l - 1 ≤ l + l ^ 2 := by
                  have := Real.abs_exp_sub_one_sub_id_le hl
                  have := le_abs_self (Real.exp l - 1 - l)
                  linarith
                have h3 : Real.exp ((Real.exp l - 1) * q) ≤ Real.exp ((l + l ^ 2) * q) :=
                  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h2 hq0)
                linarith
          _ = _ := by
              rw [← Real.exp_nat_mul, ← Real.exp_add]
              congr 1
              ring
      have route : ∀ (K : ℕ) (red : KellyLossNetworks.Routing.Edge K → Bool) (L : ℝ), 0 < L →
          (∀ a k : Fin K, a ≠ k → L < ((((Finset.univ : Finset (Fin K)) \ {a, k}).filter fun b =>
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = false) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = false)).card : ℝ)) →
          (∀ a k : Fin K, a ≠ k → ((((Finset.univ : Finset (Fin K)) \ {a, k}).filter fun b =>
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = true) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = false)).card : ℝ) ≤ L / 2) →
          WhiteRoutable red := by
        intro K red L hL hN hM
        have pairOf : ∀ g : KellyLossNetworks.Routing.Edge K, ∃ a c, a ≠ c ∧ g.1 = s(a, c) := by
          intro g
          obtain ⟨a, c, h⟩ : ∃ a c, g.1 = s(a, c) :=
            Sym2.ind (f := fun z => ∃ a c, z = s(a, c)) (fun a c => ⟨a, c, rfl⟩) g.1
          refine ⟨a, c, fun hac => g.2 ?_, h⟩
          rw [h, Sym2.mk_isDiag_iff]; exact hac
        set V : KellyLossNetworks.Routing.Edge K → Fin K → Prop := fun e k => k ∉ e.1 ∧ ∀ g, KellyLossNetworks.Routing.OnDetour e k g → red g = false
          with hV
        have hNe : ∀ e : KellyLossNetworks.Routing.Edge K, L < ((Finset.univ.filter fun k => V e k).card : ℝ) := by
          intro e
          obtain ⟨a, b, hab, he⟩ := pairOf e
          refine lt_of_lt_of_le (hN a b hab) ?_
          exact_mod_cast Finset.card_le_card (by
            intro k hk
            simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
              Finset.mem_singleton, true_and, not_or] at hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, hV]
            obtain ⟨⟨hka, hkb⟩, h1, h2⟩ := hk
            refine ⟨?_, ?_⟩
            · rw [he, Sym2.mem_iff]; tauto
            · rintro g ⟨_, w, hw, hg⟩
              rw [he, Sym2.mem_iff] at hw
              rcases hw with rfl | rfl
              · exact h1 g hg
              · exact h2 g (hg.trans Sym2.eq_swap))
        refine ⟨fun e k => if red e = true ∧ V e k then 1 / ((Finset.univ.filter fun k => V e k).card : ℝ)
          else 0, ?_, ?_, ?_, ?_⟩
        · intro e k
          dsimp only
          split_ifs
          · exact div_nonneg zero_le_one (Nat.cast_nonneg _)
          · exact le_rfl
        · intro e k h
          dsimp only at h
          split_ifs at h with h'
          · exact ⟨h'.1, h'.2.1, h'.2.2⟩
          · exact absurd rfl h
        · intro e he
          dsimp only
          have hpos := lt_trans hL (hNe e)
          rw [← Finset.sum_filter]
          simp only [he, true_and, Finset.sum_const, nsmul_eq_mul]
          field_simp
        · intro g hg
          obtain ⟨a, c, hac, hgac⟩ := pairOf g
          have hL1 : 0 ≤ 1 / L := (div_pos one_pos hL).le
          have hcnt : ∀ a c : Fin K, a ≠ c →
              ((Finset.univ.filter fun e : KellyLossNetworks.Routing.Edge K => (red e = true ∧ V e c) ∧ a ∈ e.1).card : ℝ) ≤ L / 2 := by
            intro a c hac
            refine le_trans ?_ (hM a c hac)
            exact_mod_cast Finset.card_le_card_of_injOn
              (fun e : KellyLossNetworks.Routing.Edge K => if h : a ∈ e.1 then Sym2.Mem.other h else a) (by
                intro e he
                simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he
                obtain ⟨⟨hre, hVc1, hVc2⟩, ha⟩ := he
                simp only [dif_pos ha, Finset.coe_filter, Finset.mem_sdiff, Finset.mem_univ,
                  Finset.mem_insert, Finset.mem_singleton, true_and, not_or, Set.mem_ofPred_eq]
                have hsp := Sym2.other_spec ha
                have hom := Sym2.other_mem ha
                refine ⟨⟨fun h => e.2 ?_, fun h => hVc1 (h ▸ hom)⟩, fun g' hg' => ?_, fun g' hg' => ?_⟩
                · rw [← hsp, Sym2.mk_isDiag_iff]; exact h.symm
                · have : g' = e := Subtype.ext (hg'.trans hsp)
                  rw [this]; exact hre
                · exact hVc2 g' ⟨hVc1, _, hom, hg'⟩) (by
                intro e1 he1 e2 he2 h12
                simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he1 he2
                simp only [dif_pos he1.2, dif_pos he2.2] at h12
                apply Subtype.ext
                rw [← Sym2.other_spec he1.2, ← Sym2.other_spec he2.2, h12])
          have hpt : ∀ (e : KellyLossNetworks.Routing.Edge K) (k : Fin K), (if KellyLossNetworks.Routing.OnDetour e k g then
              (if red e = true ∧ V e k then 1 / ((Finset.univ.filter fun k => V e k).card : ℝ) else 0)
              else 0) ≤ (if k = c then (if (red e = true ∧ V e c) ∧ a ∈ e.1 then 1 / L else 0) else 0) +
                (if k = a then (if (red e = true ∧ V e a) ∧ c ∈ e.1 then 1 / L else 0) else 0) := by
            intro e k
            have n1 : 0 ≤ (if k = c then (if (red e = true ∧ V e c) ∧ a ∈ e.1 then 1 / L else 0) else 0) := by
              split_ifs <;> first | exact hL1 | exact le_rfl
            have n2 : 0 ≤ (if k = a then (if (red e = true ∧ V e a) ∧ c ∈ e.1 then 1 / L else 0) else 0) := by
              split_ifs <;> first | exact hL1 | exact le_rfl
            by_cases hO : KellyLossNetworks.Routing.OnDetour e k g
            · by_cases hf : red e = true ∧ V e k
              · rw [if_pos hO, if_pos hf]
                have hle : 1 / ((Finset.univ.filter fun k => V e k).card : ℝ) ≤ 1 / L :=
                  one_div_le_one_div_of_le hL (hNe e).le
                obtain ⟨_, v, hv, hgv⟩ := hO
                rw [hgac] at hgv
                rcases Sym2.eq_iff.mp hgv with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · subst h1 h2
                  rw [if_pos rfl, if_pos ⟨hf, hv⟩]; linarith
                · subst h1 h2
                  rw [if_neg hac, if_pos rfl, if_pos ⟨hf, hv⟩]; linarith
              · rw [if_pos hO, if_neg hf]; linarith
            · rw [if_neg hO]; linarith
          unfold KellyLossNetworks.Routing.detourLoad
          calc _ ≤ ∑ e : KellyLossNetworks.Routing.Edge K, ∑ k : Fin K, ((if k = c then (if (red e = true ∧ V e c) ∧ a ∈ e.1 then 1 / L else 0) else 0) +
                (if k = a then (if (red e = true ∧ V e a) ∧ c ∈ e.1 then 1 / L else 0) else 0)) :=
                Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun k _ => hpt e k
            _ = ((Finset.univ.filter fun e : KellyLossNetworks.Routing.Edge K => (red e = true ∧ V e c) ∧ a ∈ e.1).card : ℝ) * (1 / L) +
                ((Finset.univ.filter fun e : KellyLossNetworks.Routing.Edge K => (red e = true ∧ V e a) ∧ c ∈ e.1).card : ℝ) * (1 / L) := by
                simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
                rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
                  nsmul_eq_mul, nsmul_eq_mul]
            _ ≤ (L / 2) * (1 / L) + (L / 2) * (1 / L) := by
                have := hcnt a c hac
                have := hcnt c a (Ne.symm hac)
                nlinarith
            _ = 1 := by field_simp; ring
      obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (1 - p) * (1 - 3 * p) / 3 := ⟨_, rfl⟩
      have hε0 : 0 < ε := by rw [hε]; apply div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)
      have hε1 : ε ≤ 1 / 3 := by rw [hε]; nlinarith
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ε / 2 := ⟨_, rfl⟩
      have ht0 : 0 < t := by rw [ht]; linarith
      have htabs : |t| ≤ 1 := by rw [abs_of_pos ht0]; linarith
      have htabs' : |-t| ≤ 1 := by rw [abs_neg]; exact htabs
      have hP1 : ∀ K : ℕ, whiteRoutingProb p K ≤ 1 := by
        intro K
        rw [← sumone K, whiteRoutingProb]
        refine Finset.sum_le_sum fun red _ => ?_
        split_ifs
        · exact le_rfl
        · exact cpnn K red
      have hK : ∀ K : ℕ, 3 ≤ K →
          1 - (K : ℝ) * (K : ℝ) * (2 * Real.exp (-(((K - 2 : ℕ) : ℝ) * (ε ^ 2 / 4)))) ≤
            whiteRoutingProb p K := by
        intro K hK3
        obtain ⟨n, hn⟩ : ∃ n : ℝ, n = ((K - 2 : ℕ) : ℝ) := ⟨_, rfl⟩
        have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast (by omega : 1 ≤ K - 2)
        obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ((1 - p) * (1 - p) - ε) * n := ⟨_, rfl⟩
        have hL0 : 0 < L := by
          rw [hL]; apply mul_pos _ (by linarith); rw [hε]; nlinarith
        -- the bad events
        set E1 : Fin K → Fin K → (KellyLossNetworks.Routing.Edge K → Bool) → Prop := fun a k red =>
          t * ((p * (1 - p) + ε) * n) ≤ t * ((((Finset.univ : Finset (Fin K)) \ {a, k}).filter fun b =>
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = true) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = false)).card : ℝ) with hE1
        set E2 : Fin K → Fin K → (KellyLossNetworks.Routing.Edge K → Bool) → Prop := fun a k red =>
          -t * (((1 - p) * (1 - p) - ε) * n) ≤ -t * ((((Finset.univ : Finset (Fin K)) \ {a, k}).filter fun b =>
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(a, b) → red g = false) ∧
                (∀ g : KellyLossNetworks.Routing.Edge K, g.1 = s(b, k) → red g = false)).card : ℝ) with hE2
        have hpt : ∀ red : KellyLossNetworks.Routing.Edge K → Bool, (if WhiteRoutable red then (0:ℝ) else 1) ≤
            ∑ a : Fin K, ∑ k : Fin K, (if a ≠ k then (if E1 a k red then (1:ℝ) else 0) +
              (if E2 a k red then (1:ℝ) else 0) else 0) := by
          intro red
          have nn : ∀ a k : Fin K, 0 ≤ (if a ≠ k then (if E1 a k red then (1:ℝ) else 0) +
              (if E2 a k red then (1:ℝ) else 0) else 0) := by
            intro a k; split_ifs <;> norm_num
          by_cases hW : WhiteRoutable red
          · rw [if_pos hW]
            exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun k _ => nn a k
          · rw [if_neg hW]
            have : ∃ a k : Fin K, a ≠ k ∧ (E1 a k red ∨ E2 a k red) := by
              by_contra hcon
              push Not at hcon
              apply hW
              refine route K red L hL0 (fun a k hak => ?_) (fun a k hak => ?_)
              · have h2 := (hcon a k hak).2
                simp only [hE2, not_le] at h2
                rw [hL]
                nlinarith
              · have h1 := (hcon a k hak).1
                simp only [hE1, not_le] at h1
                have : (p * (1 - p) + ε) * n ≤ L / 2 := by
                  rw [hL]
                  have : p * (1 - p) + ε ≤ ((1 - p) * (1 - p) - ε) / 2 := by rw [hε]; nlinarith
                  nlinarith
                nlinarith
            obtain ⟨a, k, hak, hev⟩ := this
            have h1 : (1:ℝ) ≤ (if a ≠ k then (if E1 a k red then (1:ℝ) else 0) +
                (if E2 a k red then (1:ℝ) else 0) else 0) := by
              rw [if_pos hak]
              rcases hev with h | h
              · rw [if_pos h]; split_ifs <;> norm_num
              · rw [if_pos h]; split_ifs <;> norm_num
            calc (1:ℝ) ≤ _ := h1
              _ ≤ ∑ k' : Fin K, (if a ≠ k' then (if E1 a k' red then (1:ℝ) else 0) +
                  (if E2 a k' red then (1:ℝ) else 0) else 0) :=
                Finset.single_le_sum (f := fun k' => (if a ≠ k' then (if E1 a k' red then (1:ℝ) else 0) +
                  (if E2 a k' red then (1:ℝ) else 0) else 0)) (fun k' _ => nn a k') (Finset.mem_univ k)
              _ ≤ _ := Finset.single_le_sum (f := fun a' => ∑ k' : Fin K, (if a' ≠ k' then
                  (if E1 a' k' red then (1:ℝ) else 0) + (if E2 a' k' red then (1:ℝ) else 0) else 0))
                  (fun a' _ => Finset.sum_nonneg fun k' _ => nn a' k') (Finset.mem_univ a)
        have hev : ∀ a k : Fin K, (if a ≠ k then
            ∑ red : KellyLossNetworks.Routing.Edge K → Bool, colouringProb p red * (if E1 a k red then (1:ℝ) else 0) +
            ∑ red : KellyLossNetworks.Routing.Edge K → Bool, colouringProb p red * (if E2 a k red then (1:ℝ) else 0) else 0) ≤
            2 * Real.exp (-(n * (ε ^ 2 / 4))) := by
          intro a k
          have h2 : 0 ≤ 2 * Real.exp (-(n * (ε ^ 2 / 4))) := by positivity
          split_ifs with hak
          · have T1 := tail K a k hak true false t (t * ((p * (1 - p) + ε) * n)) htabs
            have T2 := tail K a k hak false false (-t) (-t * (((1 - p) * (1 - p) - ε) * n)) htabs'
            rw [if_pos rfl, if_neg Bool.false_ne_true] at T1
            rw [if_neg Bool.false_ne_true] at T2
            rw [← hn] at T1 T2
            have b1 : -(t * ((p * (1 - p) + ε) * n)) + n * (p * (1 - p)) * (t + t ^ 2) ≤
                -(n * (ε ^ 2 / 4)) := by
              have : p * (1 - p) * t ^ 2 ≤ t ^ 2 := by nlinarith
              rw [ht] at this ⊢; nlinarith
            have b2 : -(-t * (((1 - p) * (1 - p) - ε) * n)) + n * ((1 - p) * (1 - p)) * (-t + (-t) ^ 2) ≤
                -(n * (ε ^ 2 / 4)) := by
              have : (1 - p) * (1 - p) * t ^ 2 ≤ t ^ 2 := by nlinarith
              rw [ht] at this ⊢; nlinarith
            have := Real.exp_le_exp.mpr b1
            have := Real.exp_le_exp.mpr b2
            linarith
          · exact h2
        have hsplit : whiteRoutingProb p K + ∑ red : KellyLossNetworks.Routing.Edge K → Bool,
            colouringProb p red * (if WhiteRoutable red then (0:ℝ) else 1) = 1 := by
          refine Eq.trans ?_ (sumone K)
          rw [whiteRoutingProb, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun red _ => ?_
          split_ifs <;> ring
        have hbad : ∑ red : KellyLossNetworks.Routing.Edge K → Bool,
            colouringProb p red * (if WhiteRoutable red then (0:ℝ) else 1) ≤
            (K : ℝ) * (K : ℝ) * (2 * Real.exp (-(n * (ε ^ 2 / 4)))) := by
          calc _ ≤ ∑ red : KellyLossNetworks.Routing.Edge K → Bool, colouringProb p red * ∑ a : Fin K, ∑ k : Fin K,
                (if a ≠ k then (if E1 a k red then (1:ℝ) else 0) +
                  (if E2 a k red then (1:ℝ) else 0) else 0) :=
                Finset.sum_le_sum fun red _ => mul_le_mul_of_nonneg_left (hpt red) (cpnn K red)
            _ = ∑ a : Fin K, ∑ k : Fin K, (if a ≠ k then
                ∑ red : KellyLossNetworks.Routing.Edge K → Bool, colouringProb p red * (if E1 a k red then (1:ℝ) else 0) +
                ∑ red : KellyLossNetworks.Routing.Edge K → Bool, colouringProb p red * (if E2 a k red then (1:ℝ) else 0) else 0) := by
                simp only [Finset.mul_sum]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun a _ => ?_
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun k _ => ?_
                split_ifs
                · rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun red _ => ?_
                  ring
                · simp
            _ ≤ ∑ a : Fin K, ∑ k : Fin K, 2 * Real.exp (-(n * (ε ^ 2 / 4))) :=
                Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun k _ => hev a k
            _ = _ := by
                rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                  nsmul_eq_mul, nsmul_eq_mul]
                ring
        rw [← hn]
        linarith
      -- limit
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ε ^ 2 / 4 := ⟨_, rfl⟩
      have hc0 : 0 < c := by rw [hc]; positivity
      have hlim0 : Tendsto (fun K : ℕ => (2 * Real.exp (2 * c) / c ^ 2) *
          ((c * (K : ℝ)) ^ 2 * Real.exp (-(c * (K : ℝ))))) atTop (𝓝 0) := by
        have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
          (tendsto_natCast_atTop_atTop.const_mul_atTop hc0)
        simpa using this.const_mul (2 * Real.exp (2 * c) / c ^ 2)
      have hlim : Tendsto (fun K : ℕ => 1 - (2 * Real.exp (2 * c) / c ^ 2) *
          ((c * (K : ℝ)) ^ 2 * Real.exp (-(c * (K : ℝ))))) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hlim0
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_
        (Eventually.of_forall hP1)
      filter_upwards [eventually_ge_atTop 3] with K hK3
      refine le_trans (le_of_eq ?_) (hK K hK3)
      have hK2 : ((K - 2 : ℕ) : ℝ) = (K : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [hK2, ← hc]
      have : Real.exp (-(((K : ℝ) - 2) * c)) = Real.exp (2 * c) * Real.exp (-(c * K)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      field_simp
