-- Prove2me | solution 1 for HararySachs.Hyper.coeff_eq_numTours
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T03:53:35.968443+00:00
-- url     : https://prove2.me/submissions/4bdb8cab-560d-4d2c-b77f-ead9796244ec

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators

open HararySachs.Hyper MvPolynomial
open Classical

namespace CoeffToursAux

variable {n : ℕ}

/-! ## Step 1: constant term of a monomial differential operator -/

lemma coeff_iterate_pderiv (a : Fin n × Fin n) (j : ℕ) (s : (Fin n × Fin n) →₀ ℕ)
    (p : AuxPoly n) :
    coeff s ((pderiv a)^[j] p) =
      coeff (s + j • Finsupp.single a 1) p * ∏ i ∈ Finset.range j, ((s a : ℚ) + i + 1) := by
  induction j generalizing p with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih, coeff_pderiv, Finset.prod_range_succ]
    have h : s + (j + 1) • Finsupp.single a 1 = s + j • Finsupp.single a 1 + Finsupp.single a 1 := by
      rw [add_smul, one_smul, add_assoc]
    rw [h]
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one, Nat.cast_add]
    ring

/-- The exponent vector of the operator `∂^m`. -/
noncomputable def expo (m : ArcMult n) : (Fin n × Fin n) →₀ ℕ :=
  ∑ a : Fin n × Fin n, m a.1 a.2 • Finsupp.single a 1

lemma coeff_zero_foldl (m : ArcMult n) (l : List (Fin n × Fin n)) (hl : l.Nodup)
    (p : AuxPoly n) :
    coeff 0 (l.foldl (fun q a => (pderiv a)^[m a.1 a.2] q) p) =
      coeff (l.map (fun a => m a.1 a.2 • Finsupp.single a 1)).sum p *
        (l.map (fun a => ((m a.1 a.2).factorial : ℚ))).prod := by
  induction l generalizing p with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih hl.of_cons, coeff_iterate_pderiv]
    have ha : a ∉ l := (List.nodup_cons.mp hl).1
    have h0 : (l.map (fun b => m b.1 b.2 • Finsupp.single b 1)).sum a = 0 := by
      rw [← Finsupp.applyAddHom_apply, map_list_sum]
      apply List.sum_eq_zero
      intro x hx
      simp only [List.map_map, List.mem_map, Function.comp_apply,
        Finsupp.applyAddHom_apply] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      have hba : b ≠ a := fun h => ha (h ▸ hb)
      simp [hba]
    rw [h0]
    have hfact : ∏ i ∈ Finset.range (m a.1 a.2), (((0 : ℕ) : ℚ) + i + 1) =
        ((m a.1 a.2).factorial : ℚ) := by
      rw [← Finset.prod_range_add_one_eq_factorial]
      push_cast
      simp
    rw [hfact, List.map_cons, List.map_cons, List.sum_cons, List.prod_cons, add_comm]
    ring

lemma coeff_zero_diffMonomial (m : ArcMult n) (p : AuxPoly n) :
    coeff 0 (diffMonomial m p) =
      coeff (expo m) p * ∏ a : Fin n × Fin n, ((m a.1 a.2).factorial : ℚ) := by
  unfold diffMonomial
  rw [coeff_zero_foldl m _ (Finset.nodup_toList _), Finset.sum_map_toList,
    Finset.prod_map_toList]
  rfl

/-! ## Step 2: the trace of a matrix power as a sum over closed walks -/

lemma pow_apply_walks {R : Type*} [CommSemiring R] (M : Matrix (Fin n) (Fin n) R) (k : ℕ)
    (i j : Fin n) :
    (M ^ k) i j = ∑ w : Fin (k + 1) → Fin n,
      if w 0 = i ∧ w (Fin.last k) = j then ∏ t : Fin k, M (w t.castSucc) (w t.succ) else 0 := by
  induction k generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_apply, ← (Equiv.funUnique (Fin 1) (Fin n)).symm.sum_comp]
    simp only [Fin.last_zero, Equiv.funUnique_symm_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg h]
      symm
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact h (h1.symm.trans h2)
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    conv_rhs => rw [← (Fin.snocEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have h0 : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, h0, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.prod_univ_castSucc, Fin.succ_castSucc, Fin.succ_last]
    by_cases hw : w 0 = i
    · simp [hw, Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp [hw]

/-- successor modulo `L` -/
def nxt {L : ℕ} (hL : 0 < L) (t : Fin L) : Fin L := ⟨(t.val + 1) % L, Nat.mod_lt _ hL⟩

lemma trace_pow_walks {R : Type*} [CommSemiring R] (M : Matrix (Fin n) (Fin n) R) {L : ℕ}
    (hL : 0 < L) :
    Matrix.trace (M ^ L) = ∑ v : Fin L → Fin n, ∏ t : Fin L, M (v t) (v (nxt hL t)) := by
  obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  simp_rw [pow_apply_walks]
  rw [Finset.sum_comm]
  simp only [ite_and]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← (Fin.snocEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  have h0 : (0 : Fin (L + 2)) = (0 : Fin (L + 1)).castSucc := rfl
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, h0, Fin.snoc_castSucc, Fin.snoc_last]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  congr 1
  by_cases ht : t = Fin.last L
  · subst ht
    rw [Fin.succ_last, Fin.snoc_last]
    congr 1
    ext
    simp [nxt]
  · have hlt : t.val < L := by
      have := Fin.val_lt_last ht
      simpa using this
    have hs : t.succ = (⟨t.val + 1, by omega⟩ : Fin (L + 1)).castSucc := by
      ext
      simp
    rw [hs, Fin.snoc_castSucc]
    congr 1
    ext
    simp [nxt, Nat.mod_eq_of_lt (by omega : t.val + 1 < L + 1)]

/-- number of steps of the closed walk `v` that go from `p.1` to `p.2` -/
noncomputable def cnt {L : ℕ} (hL : 0 < L) (v : Fin L → Fin n) (p : Fin n × Fin n) : ℕ :=
  (Finset.univ.filter (fun t => v t = p.1 ∧ v (nxt hL t) = p.2)).card

lemma coeff_trPow {L : ℕ} (hL : 0 < L) (s : (Fin n × Fin n) →₀ ℕ) :
    coeff s (trPow n L) =
      ((Finset.univ.filter (fun v : Fin L → Fin n =>
        ∑ t, Finsupp.single (v t, v (nxt hL t)) 1 = s)).card : ℚ) := by
  unfold trPow
  rw [trace_pow_walks _ hL, coeff_sum]
  simp only [Matrix.of_apply]
  have hmono : ∀ v : Fin L → Fin n, (∏ t, (X (v t, v (nxt hL t)) : AuxPoly n)) =
      monomial (∑ t, Finsupp.single (v t, v (nxt hL t)) 1) 1 := by
    intro v
    rw [monomial_sum_one]
    rfl
  simp_rw [hmono, coeff_monomial]
  rw [Finset.sum_boole]

lemma walk_expo_iff (m : ArcMult n) {L : ℕ} (hL : 0 < L) (v : Fin L → Fin n) :
    (∑ t, Finsupp.single (v t, v (nxt hL t)) 1 = expo m) ↔
      ∀ p : Fin n × Fin n, cnt hL v p = m p.1 p.2 := by
  rw [Finsupp.ext_iff]
  refine forall_congr' (fun p => ?_)
  have h1 : (∑ t, Finsupp.single (v t, v (nxt hL t)) 1 : (Fin n × Fin n) →₀ ℕ) p =
      cnt hL v p := by
    rw [Finsupp.finsetSum_apply, cnt, Finset.card_filter]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finsupp.single_apply]
    by_cases h : v t = p.1 ∧ v (nxt hL t) = p.2
    · rw [if_pos (Prod.ext h.1 h.2), if_pos h]
    · rw [if_neg (fun h' => h ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩), if_neg h]
  have h2 : expo m p = m p.1 p.2 := by
    rw [expo, Finsupp.finsetSum_apply, Finset.sum_eq_single p]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [h1, h2]

/-! ## Step 3: tours along a fixed closed walk -/

section Fiber

variable {L : ℕ} (hL : 0 < L) (m : ArcMult n) (v : Fin L → Fin n)

/-- positions where the walk `v` steps from `p.1` to `p.2` -/
abbrev Pos (p : Fin n × Fin n) := {t : Fin L // v t = p.1 ∧ v (nxt hL t) = p.2}

/-- tours whose sequence of tails is the walk `v` -/
abbrev Fib := {σ : Fin L ≃ Arcs m // IsTour m hL σ ∧ ∀ t, (σ t).1 = v t}

lemma arcs_eq {u w : Fin n} (x : Arcs m) (h1 : x.1 = u) (h2 : x.2.1 = w) :
    ∃ j : Fin (m u w), x = ⟨u, w, j⟩ := by
  obtain ⟨a, b, j⟩ := x
  simp only at h1 h2
  subst h1 h2
  exact ⟨j, rfl⟩

lemma tour_step {σ : Fin L ≃ Arcs m} (hσ : IsTour m hL σ) (t : Fin L) :
    (σ t).2.1 = (σ (nxt hL t)).1 := hσ t

/-- a tour along `v` labels, for each arc class `p`, the positions `Pos v p` bijectively -/
noncomputable def fwd (σ : Fib hL m v) (p : Fin n × Fin n) : Fin (m p.1 p.2) ≃ Pos hL v p :=
  Equiv.ofBijective
    (fun j => ⟨σ.1.symm ⟨p.1, p.2, j⟩, by
      refine ⟨?_, ?_⟩
      · rw [← σ.2.2, Equiv.apply_symm_apply]
      · rw [← σ.2.2, ← tour_step hL m σ.2.1, Equiv.apply_symm_apply]⟩)
    ⟨fun j j' h => by
      have := σ.1.symm.injective (congrArg Subtype.val h)
      simpa using this,
     fun ⟨t, h1, h2⟩ => by
      obtain ⟨j, hj⟩ := arcs_eq m (σ.1 t) (u := p.1) (w := p.2) (by rw [σ.2.2]; exact h1)
        (by rw [tour_step hL m σ.2.1, σ.2.2]; exact h2)
      refine ⟨j, Subtype.ext ?_⟩
      show σ.1.symm ⟨p.1, p.2, j⟩ = t
      rw [← hj, Equiv.symm_apply_apply]⟩

/-- the arc at position `t` determined by a family of labelings -/
noncomputable def bwdFun (e : ∀ p : Fin n × Fin n, Fin (m p.1 p.2) ≃ Pos hL v p) (t : Fin L) :
    Arcs m :=
  ⟨v t, v (nxt hL t), (e (v t, v (nxt hL t))).symm ⟨t, rfl, rfl⟩⟩

lemma bwdFun_eq (e : ∀ p : Fin n × Fin n, Fin (m p.1 p.2) ≃ Pos hL v p) (t : Fin L)
    (u w : Fin n) (j : Fin (m u w)) (hu : v t = u) (hw : v (nxt hL t) = w)
    (hj : e (u, w) j = ⟨t, hu, hw⟩) : bwdFun hL m v e t = ⟨u, w, j⟩ := by
  subst hu hw
  have : (e (v t, v (nxt hL t))).symm ⟨t, rfl, rfl⟩ = j := (Equiv.symm_apply_eq _).mpr hj.symm
  unfold bwdFun
  rw [this]

/-- the tour along `v` determined by a family of labelings -/
noncomputable def bwd (e : ∀ p : Fin n × Fin n, Fin (m p.1 p.2) ≃ Pos hL v p) : Fib hL m v :=
  ⟨{ toFun := bwdFun hL m v e
     invFun := fun x => (e (x.1, x.2.1) x.2.2).val
     left_inv := fun t => by
       show ((e (v t, v (nxt hL t))) ((e (v t, v (nxt hL t))).symm ⟨t, rfl, rfl⟩)).val = t
       rw [Equiv.apply_symm_apply]
     right_inv := fun x => by
       obtain ⟨u, w, j⟩ := x
       exact bwdFun_eq hL m v e _ u w j (e (u, w) j).2.1 (e (u, w) j).2.2 rfl },
   fun _ => rfl, fun _ => rfl⟩

noncomputable def fibEquiv :
    Fib hL m v ≃ (∀ p : Fin n × Fin n, Fin (m p.1 p.2) ≃ Pos hL v p) where
  toFun := fwd hL m v
  invFun := bwd hL m v
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro t
    obtain ⟨j, hj⟩ := arcs_eq m (σ.1 t) (u := v t) (w := v (nxt hL t)) (σ.2.2 t)
      (by rw [tour_step hL m σ.2.1, σ.2.2])
    rw [hj]
    refine bwdFun_eq hL m v _ t _ _ j rfl rfl ?_
    apply Subtype.ext
    show σ.1.symm ⟨v t, v (nxt hL t), j⟩ = t
    rw [← hj, Equiv.symm_apply_apply]
  right_inv e := by
    funext p
    apply Equiv.ext
    intro j
    apply Subtype.ext
    rfl

lemma card_fib : Fintype.card (Fib hL m v) =
    ∏ p : Fin n × Fin n, (if cnt hL v p = m p.1 p.2 then (m p.1 p.2).factorial else 0) := by
  rw [Fintype.card_congr (fibEquiv hL m v), Fintype.card_pi]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  have hc : Fintype.card (Pos hL v p) = cnt hL v p := by
    rw [Fintype.card_subtype]
    rfl
  split_ifs with h
  · rw [Fintype.card_equiv (Fintype.equivOfCardEq (by rw [hc, h, Fintype.card_fin]))]
    simp
  · rw [Fintype.card_eq_zero_iff]
    constructor
    intro e
    exact h (by rw [← hc, ← Fintype.card_congr e, Fintype.card_fin])

end Fiber

lemma numTours_eq (m : ArcMult n) {L : ℕ} (hL : 0 < L) :
    numTours m hL = ∑ v : Fin L → Fin n, Fintype.card (Fib hL m v) := by
  unfold numTours
  rw [← Fintype.card_subtype,
    ← Fintype.card_congr
      (Equiv.sigmaFiberEquiv (fun σ : {σ // IsTour m hL σ} => fun t => (σ.1 t).1)),
    Fintype.card_sigma]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  apply Fintype.card_congr
  exact
    { toFun := fun x => ⟨x.1.1, x.1.2, fun t => congrFun x.2 t⟩
      invFun := fun σ => ⟨⟨σ.1, σ.2.1⟩, funext σ.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end CoeffToursAux

open CoeffToursAux in
theorem solution {n L : ℕ} (hL : 0 < L) (m : ArcMult n)
    (_hm : (∑ u : Fin n, ∑ v : Fin n, m u v) = L) :
    MvPolynomial.coeff 0 (diffMonomial m (trPow n L)) = (numTours m hL : ℚ) := by
  rw [coeff_zero_diffMonomial, coeff_trPow hL, numTours_eq]
  simp_rw [card_fib, Finset.prod_ite_zero, Finset.mem_univ, true_implies]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  push_cast
  rw [Finset.filter_congr (fun v _ => walk_expo_iff m hL v)]
