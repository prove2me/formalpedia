-- Prove2me | solution 1 for MatchVec3.exact_weight_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-16T16:27:21.865676+00:00
-- url     : https://prove2.me/submissions/ac930378-6ea9-4f32-be0c-d653ca39c3a6

import Mathlib

theorem solution {p : ℕ} (hp : p.Prime) (L r : ℕ) (hr : r ≤ L) :
    ∃ (c : ℕ → ZMod p) (P : MvPolynomial (Fin L) (ZMod p)),
      P = ∑ d ∈ Finset.range (L + 1), MvPolynomial.C (c d) * MvPolynomial.esymm (Fin L) (ZMod p) d ∧
      P.totalDegree ≤ L ∧
      ∀ z : Fin L → ZMod p, (∀ s, z s = 0 ∨ z s = 1) →
        MvPolynomial.eval z P = if (Finset.univ.filter fun s => z s = 1).card = r then 1 else 0 := by
  classical
  haveI hfact : Fact p.Prime := ⟨hp⟩
  have hesymm_eval : ∀ (d : ℕ) (z : Fin L → ZMod p), (∀ s, z s = 0 ∨ z s = 1) →
      MvPolynomial.eval z (MvPolynomial.esymm (Fin L) (ZMod p) d) =
        (((Finset.univ.filter (fun s => z s = 1)).card.choose d : ℕ) : ZMod p) := by
    intro d z hz
    have h1 : MvPolynomial.eval z (MvPolynomial.esymm (Fin L) (ZMod p) d) =
        (Multiset.map z Finset.univ.val).esymm d := by
      rw [← MvPolynomial.aeval_eq_eval]
      exact MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin L) (ZMod p) d z
    rw [h1, Finset.esymm_map_val]
    have h2 : ∀ t ∈ (Finset.univ : Finset (Fin L)).powersetCard d,
        t.prod z = if t ⊆ Finset.univ.filter (fun s => z s = 1) then 1 else 0 := by
      intro t _
      by_cases hsub : t ⊆ Finset.univ.filter (fun s => z s = 1)
      · rw [if_pos hsub]
        apply Finset.prod_eq_one
        intro i hi
        have hmem := hsub hi
        simpa using hmem
      · rw [if_neg hsub]
        obtain ⟨i, hi, hzi⟩ : ∃ i ∈ t, z i ≠ 1 := by
          by_contra h
          apply hsub
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_contra h'
          exact h ⟨i, hi, h'⟩
        have hz0 : z i = 0 := by
          rcases hz i with h | h
          · exact h
          · exact absurd h hzi
        exact Finset.prod_eq_zero hi hz0
    rw [Finset.sum_congr rfl h2, Finset.sum_boole]
    have h3 : ({x ∈ (Finset.univ : Finset (Fin L)).powersetCard d |
        x ⊆ Finset.univ.filter (fun s => z s = 1)}).card =
        ((Finset.univ.filter (fun s => z s = 1)).powersetCard d).card := by
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨-, hcard⟩, hsub⟩
        exact ⟨hsub, hcard⟩
      · rintro ⟨hsub, hcard⟩
        exact ⟨⟨fun _ _ => Finset.mem_univ _, hcard⟩, hsub⟩
    rw [h3, Finset.card_powersetCard]
  have hesymm_deg : ∀ d : ℕ, (MvPolynomial.esymm (Fin L) (ZMod p) d).totalDegree ≤ d := by
    intro d
    have h1 : MvPolynomial.esymm (Fin L) (ZMod p) d =
        ∑ t ∈ (Finset.univ : Finset (Fin L)).powersetCard d, t.prod MvPolynomial.X := by
      rw [MvPolynomial.esymm_eq_multiset_esymm, Finset.esymm_map_val]
    rw [h1]
    calc (∑ t ∈ (Finset.univ : Finset (Fin L)).powersetCard d, t.prod MvPolynomial.X).totalDegree
        ≤ ((Finset.univ : Finset (Fin L)).powersetCard d).sup
            (fun t => (t.prod MvPolynomial.X).totalDegree) :=
          MvPolynomial.totalDegree_finset_sum _ _
      _ ≤ d := by
          apply Finset.sup_le
          intro t ht
          rw [Finset.mem_powersetCard] at ht
          calc (t.prod MvPolynomial.X).totalDegree
              ≤ ∑ i ∈ t, (MvPolynomial.X i : MvPolynomial (Fin L) (ZMod p)).totalDegree :=
                MvPolynomial.totalDegree_finset_prod _ _
            _ = t.card := by
                rw [Finset.sum_congr rfl (fun i _ => MvPolynomial.totalDegree_X i), Finset.sum_const,
                  smul_eq_mul, mul_one]
            _ = d := ht.2
  have htri : ∀ (L : ℕ) (f : ℕ → ZMod p), ∃ c : ℕ → ZMod p,
      ∀ w ≤ L, ∑ d ∈ Finset.range (L + 1), c d * ((w.choose d : ℕ) : ZMod p) = f w := by
    intro L
    induction L with
    | zero =>
      intro f
      refine ⟨fun d => if d = 0 then f 0 else 0, ?_⟩
      intro w hw
      have hw0 : w = 0 := by omega
      subst hw0
      simp
    | succ L ih =>
      intro f
      obtain ⟨c, hc⟩ := ih f
      refine ⟨fun d => if d = L + 1 then f (L + 1) -
          ∑ d ∈ Finset.range (L + 1), c d * (((L + 1).choose d : ℕ) : ZMod p) else c d, ?_⟩
      intro w hw
      rcases Nat.lt_or_ge w (L + 1) with hlt | hge
      · have hwL : w ≤ L := by omega
        have hzero : ((w.choose (L + 1) : ℕ) : ZMod p) = 0 := by
          rw [Nat.choose_eq_zero_of_lt (by omega)]
          simp
        have e1 : ∑ d ∈ Finset.range (L + 2),
            (if d = L + 1 then f (L + 1) -
              ∑ d ∈ Finset.range (L + 1), c d * (((L + 1).choose d : ℕ) : ZMod p) else c d)
            * ((w.choose d : ℕ) : ZMod p)
            = ∑ d ∈ Finset.range (L + 1), c d * ((w.choose d : ℕ) : ZMod p) := by
          rw [Finset.sum_range_succ]
          simp only [if_true]
          rw [hzero, mul_zero, add_zero]
          exact Finset.sum_congr rfl (fun d hd => by
            rw [Finset.mem_range] at hd
            rw [if_neg (by omega)])
        rw [e1, hc w hwL]
      · have hwL : w = L + 1 := by omega
        subst hwL
        have e2 : ∑ x ∈ Finset.range (L + 1),
            (if x = L + 1 then f (L + 1) -
              ∑ x ∈ Finset.range (L + 1), c x * (((L + 1).choose x : ℕ) : ZMod p) else c x)
            * (((L + 1).choose x : ℕ) : ZMod p)
            = ∑ x ∈ Finset.range (L + 1), c x * (((L + 1).choose x : ℕ) : ZMod p) := by
          exact Finset.sum_congr rfl (fun x hx => by
            rw [Finset.mem_range] at hx
            rw [if_neg (by omega)])
        rw [Finset.sum_range_succ, e2]
        simp only [if_true, Nat.choose_self, Nat.cast_one, mul_one]
        ring
  obtain ⟨c, hc⟩ := htri L (fun w => if w = r then 1 else 0)
  refine ⟨c, ∑ d ∈ Finset.range (L + 1),
    MvPolynomial.C (c d) * MvPolynomial.esymm (Fin L) (ZMod p) d, rfl, ?_, ?_⟩
  · calc (∑ d ∈ Finset.range (L + 1),
        MvPolynomial.C (c d) * MvPolynomial.esymm (Fin L) (ZMod p) d).totalDegree
        ≤ (Finset.range (L + 1)).sup (fun d =>
            (MvPolynomial.C (c d) * MvPolynomial.esymm (Fin L) (ZMod p) d).totalDegree) :=
          MvPolynomial.totalDegree_finset_sum _ _
      _ ≤ L := by
          apply Finset.sup_le
          intro d hd
          rw [Finset.mem_range] at hd
          calc (MvPolynomial.C (c d) * MvPolynomial.esymm (Fin L) (ZMod p) d).totalDegree
              ≤ (MvPolynomial.esymm (Fin L) (ZMod p) d).totalDegree := by
                rw [← MvPolynomial.smul_eq_C_mul]
                exact MvPolynomial.totalDegree_smul_le _ _
            _ ≤ d := hesymm_deg d
            _ ≤ L := by omega
  · intro z hz
    rw [MvPolynomial.eval_sum]
    have hwL : (Finset.univ.filter (fun s => z s = 1)).card ≤ L := by
      calc (Finset.univ.filter (fun s => z s = 1)).card ≤ (Finset.univ : Finset (Fin L)).card :=
            Finset.card_filter_le _ _
        _ = L := by simp
    have hstep : ∀ d ∈ Finset.range (L + 1),
        MvPolynomial.eval z (MvPolynomial.C (c d) * MvPolynomial.esymm (Fin L) (ZMod p) d) =
        c d * ((((Finset.univ.filter (fun s => z s = 1)).card.choose d : ℕ)) : ZMod p) := by
      intro d _
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, hesymm_eval d z hz]
    rw [Finset.sum_congr rfl hstep, hc _ hwL]
