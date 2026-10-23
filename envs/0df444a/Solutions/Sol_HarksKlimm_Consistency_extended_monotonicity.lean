-- Prove2me | solution 1 for HarksKlimm.Consistency.extended_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:21:22.303156+00:00
-- url     : https://prove2.me/submissions/7544d67c-3d0c-4a76-bb15-0739d93c9bec

import Definitions.Def_HarksKlimm_Consistency_Consistent
import Definitions.Def_HarksKlimm_Consistency_IntegerHull
import Definitions.Def_HarksKlimm_Consistency_ShiftHull
import Definitions.Def_HarksKlimm_Consistency_ThreeConsistent
import Definitions.Def_HarksKlimm_Consistency_TwoHull
import Theorems.Thm_HarksKlimm_Consistency_three_load_witness

open scoped NNReal

namespace X8HK
open HarksKlimm.Consistency

set_option linter.unusedSectionVars false

noncomputable section
open Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

def x8S {m : ℕ} (eF : Fin m ≃ Option X) (side : X → Bool) (p : Bool) : Finset (Fin m) :=
  (Finset.univ.filter (fun x => side x = p)).image (fun x => eF.symm (some x))

def x8Sd {m : ℕ} (eF : Fin m ≃ Option X) (D : Y → Finset X) (y : Y) : Finset (Fin m) :=
  (D y).image (fun x => eF.symm (some x))

def x8strat {m : ℕ} (eF : Fin m ≃ Option X) (side p2 : X → Bool) (D : Y → Finset X) :
    Bool ⊕ Y → Finset (Finset (Fin m))
  | .inl true => {x8S eF side true, x8S eF side false}
  | .inl false => {x8S eF p2 true, x8S eF p2 false}
  | .inr y => {x8Sd eF D y}

def x8dem (d1 d2 : ℝ≥0) (e : Y → ℝ≥0) : Bool ⊕ Y → ℝ≥0
  | .inl true => d1
  | .inl false => d2
  | .inr y => e y

def x8game {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (eP : Fin n ≃ Bool ⊕ Y) (eF : Fin m ≃ Option X)
    (side p2 : X → Bool) (D : Y → Finset X) (d1 d2 : ℝ≥0) (e : Y → ℝ≥0) (hd1 : 0 < d1)
    (hd2 : 0 < d2) (he : ∀ y, 0 < e y) (cf : X → ℝ≥0 → ℝ) (c0 : ℝ≥0 → ℝ) : Game n m where
  players_pos := hn
  facilities_pos := hm
  strategies i := x8strat eF side p2 D (eP i)
  strategies_nonempty i := by
    generalize eP i = z
    rcases z with ((_ | _) | y) <;> simp [x8strat]
  demand i := x8dem d1 d2 e (eP i)
  demand_pos i := by
    generalize eP i = z
    rcases z with ((_ | _) | y) <;> simp [x8dem, hd1, hd2, he]
  cost f := (eF f).elim c0 cf

section
variable {n m : ℕ} {hn : 0 < n} {hm : 0 < m} {eP : Fin n ≃ Bool ⊕ Y} {eF : Fin m ≃ Option X}
    {side p2 : X → Bool} {D : Y → Finset X} {d1 d2 : ℝ≥0} {e : Y → ℝ≥0} {hd1 : 0 < d1}
    {hd2 : 0 < d2} {he : ∀ y, 0 < e y} {cf : X → ℝ≥0 → ℝ} {c0 : ℝ≥0 → ℝ}

local notation "G" => x8game hn hm eP eF side p2 D d1 d2 e hd1 hd2 he cf c0

lemma x8_dummy (s : (G).Profile) (y : Y) : (s (eP.symm (.inr y))).val = x8Sd eF D y := by
  have := (s (eP.symm (.inr y))).2
  simpa [x8game, x8strat] using this

lemma x8_choice1 (s : (G).Profile) : ∃ p, (s (eP.symm (.inl true))).val = x8S eF side p := by
  have := (s (eP.symm (.inl true))).2
  simp only [x8game, Equiv.apply_symm_apply, x8strat, Finset.mem_insert,
    Finset.mem_singleton] at this
  rcases this with h | h
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩

lemma x8_choice2 (s : (G).Profile) : ∃ q, (s (eP.symm (.inl false))).val = x8S eF p2 q := by
  have := (s (eP.symm (.inl false))).2
  simp only [x8game, Equiv.apply_symm_apply, x8strat, Finset.mem_insert,
    Finset.mem_singleton] at this
  rcases this with h | h
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩

lemma x8_mem_S (side : X → Bool) (p : Bool) (x : X) :
    eF.symm (some x) ∈ x8S eF side p ↔ side x = p := by
  simp [x8S]

lemma x8_mem_Sd (y : Y) (x : X) : eF.symm (some x) ∈ x8Sd eF D y ↔ x ∈ D y := by
  simp [x8Sd]

lemma x8_load (s : (G).Profile) (p q : Bool)
    (h1 : (s (eP.symm (.inl true))).val = x8S eF side p)
    (h2 : (s (eP.symm (.inl false))).val = x8S eF p2 q) (x : X) :
    load G s (eF.symm (some x)) =
      (∑ y, if x ∈ D y then e y else 0) + (if side x = p then d1 else 0) +
        (if p2 x = q then d2 else 0) := by
  unfold load
  rw [← eP.symm.sum_comp, Fintype.sum_sum_type, Fintype.sum_bool]
  have hd : ∀ y, (if eF.symm (some x) ∈ (s (eP.symm (.inr y))).val then
      (x8game hn hm eP eF side p2 D d1 d2 e hd1 hd2 he cf c0).demand (eP.symm (.inr y)) else 0) =
      if x ∈ D y then e y else 0 := fun y => by
    simp only [x8_dummy, x8_mem_Sd]
    simp [x8game, x8dem]
  simp only [hd, h1, h2, x8_mem_S]
  simp only [x8game, Equiv.apply_symm_apply, x8dem]
  ring

lemma x8_cost1 (s : (G).Profile) (p : Bool)
    (h1 : (s (eP.symm (.inl true))).val = x8S eF side p) :
    privateCost G s (eP.symm (.inl true)) =
      ∑ x ∈ Finset.univ.filter (fun x => side x = p), (d1 : ℝ) * cf x (load G s (eF.symm (some x))) := by
  unfold privateCost
  rw [h1, x8S, Finset.sum_image (fun a _ b _ h => by simpa using h)]
  simp [x8game, x8dem]

lemma x8_cost2 (s : (G).Profile) (q : Bool)
    (h2 : (s (eP.symm (.inl false))).val = x8S eF p2 q) :
    privateCost G s (eP.symm (.inl false)) =
      ∑ x ∈ Finset.univ.filter (fun x => p2 x = q), (d2 : ℝ) * cf x (load G s (eF.symm (some x))) := by
  unfold privateCost
  rw [h2, x8S, Finset.sum_image (fun a _ b _ h => by simpa using h)]
  simp [x8game, x8dem]

/-- The two Nash inequalities. -/
lemma x8_nash (s : (G).Profile) (o : X → ℝ≥0)
    (ho : ∀ x, (∑ y, if x ∈ D y then e y else 0) = o x)
    (hs : AGT.IsPureNash (fun i t => -privateCost G t i) s) :
    ∃ p q : Bool,
      (∑ x ∈ Finset.univ.filter (fun x => side x = p), (d1 : ℝ) *
          cf x (o x + d1 + (if p2 x = q then d2 else 0))) ≤
        (∑ x ∈ Finset.univ.filter (fun x => side x = !p), (d1 : ℝ) *
          cf x (o x + d1 + (if p2 x = q then d2 else 0))) ∧
      (∑ x ∈ Finset.univ.filter (fun x => p2 x = q), (d2 : ℝ) *
          cf x (o x + (if side x = p then d1 else 0) + d2)) ≤
        (∑ x ∈ Finset.univ.filter (fun x => p2 x = !q), (d2 : ℝ) *
          cf x (o x + (if side x = p then d1 else 0) + d2)) := by
  obtain ⟨p, h1⟩ := x8_choice1 s
  obtain ⟨q, h2⟩ := x8_choice2 s
  have hne : eP.symm (.inl false) ≠ eP.symm (.inl true) := by simp
  refine ⟨p, q, ?_, ?_⟩
  · have hmem : x8S eF side (!p) ∈ (G).strategies (eP.symm (.inl true)) := by
      cases p <;> simp [x8game, x8strat]
    have hN := hs (eP.symm (.inl true)) ⟨_, hmem⟩
    set s' := Function.update s (eP.symm (.inl true)) ⟨_, hmem⟩ with hs'
    have h1' : (s' (eP.symm (.inl true))).val = x8S eF side (!p) := by simp [hs']
    have h2' : (s' (eP.symm (.inl false))).val = x8S eF p2 q := by
      rw [hs', Function.update_of_ne hne]; exact h2
    simp only [neg_le_neg_iff] at hN
    rw [x8_cost1 s p h1, x8_cost1 s' (!p) h1'] at hN
    refine le_trans (le_of_eq ?_) (le_trans hN (le_of_eq ?_))
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [x8_load s p q h1 h2]
      simp only [Finset.mem_filter] at hx
      simp [hx.2, ho]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [x8_load s' (!p) q h1' h2']
      simp only [Finset.mem_filter] at hx
      simp [hx.2, ho]
  · have hmem : x8S eF p2 (!q) ∈ (G).strategies (eP.symm (.inl false)) := by
      cases q <;> simp [x8game, x8strat]
    have hN := hs (eP.symm (.inl false)) ⟨_, hmem⟩
    set s' := Function.update s (eP.symm (.inl false)) ⟨_, hmem⟩ with hs'
    have h2' : (s' (eP.symm (.inl false))).val = x8S eF p2 (!q) := by simp [hs']
    have h1' : (s' (eP.symm (.inl true))).val = x8S eF side p := by
      rw [hs', Function.update_of_ne hne.symm]; exact h1
    simp only [neg_le_neg_iff] at hN
    rw [x8_cost2 s q h2, x8_cost2 s' (!q) h2'] at hN
    refine le_trans (le_of_eq ?_) (le_trans hN (le_of_eq ?_))
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [x8_load s p q h1 h2]
      simp only [Finset.mem_filter] at hx
      simp [hx.2, ho]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [x8_load s' p (!q) h1' h2']
      simp only [Finset.mem_filter] at hx
      simp [hx.2, ho]

end

end

end X8HK


open scoped NNReal

namespace X8HK
open HarksKlimm.Consistency

noncomputable section
open Classical

lemma x8_sum1 {K : ℕ} (a : Fin K → ℤ) (G : (Σ k, Fin (a k).natAbs) × Bool → ℝ) (p : Bool) :
    ∑ x ∈ Finset.univ.filter (fun x : (Σ k, Fin (a k).natAbs) × Bool => x.2 = p), G x =
      ∑ σ, G (σ, p) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  cases p <;> simp [Fintype.sum_bool]

lemma x8_sum2 {K : ℕ} (a : Fin K → ℤ) (f : Fin K → Bool)
    (G : (Σ k, Fin (a k).natAbs) × Bool → ℝ) (q : Bool) :
    ∑ x ∈ Finset.univ.filter (fun x : (Σ k, Fin (a k).natAbs) × Bool => xor x.2 (f x.1.1) = q),
      G x = ∑ σ, G (σ, xor q (f σ.1)) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rcases h : f σ.1 with _ | _ <;> cases q <;> simp [h]

lemma x8_sigma {K : ℕ} (a : Fin K → ℤ) (g : Fin K → ℝ) :
    ∑ σ : (Σ k, Fin (a k).natAbs), g σ.1 = ∑ k, ((a k).natAbs : ℝ) * g k := by
  rw [Fintype.sum_sigma]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma x8_term (a : ℤ) (F : Bool → ℝ) (r : Bool) :
    (a.natAbs : ℝ) * F (xor (!r) (decide (a < 0))) - (a.natAbs : ℝ) * F (xor r (decide (a < 0))) =
      (a : ℝ) * (F (!r) - F r) := by
  have hc : (a.natAbs : ℝ) = |(a : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hc]
  rcases lt_or_ge a 0 with h | h
  · have h' : (a : ℝ) < 0 := Int.cast_lt_zero.mpr h
    rw [abs_of_neg h']
    cases r <;> simp [h] <;> ring
  · have h' : (0 : ℝ) ≤ a := by exact_mod_cast h
    rw [abs_of_nonneg h']
    have : ¬ a < 0 := not_lt.mpr h
    cases r <;> simp [this] <;> ring

/-- Consistency for games with player set `Fin n ≃ Bool ⊕ Y` yields the two Nash inequalities
for the integer combination `H t = ∑ a_k c_k (t + b_k)`. -/
theorem x8_core (C : Set (ℝ≥0 → ℝ)) {K : ℕ} (a : Fin K → ℤ) (b : Fin K → ℝ≥0)
    (c : Fin K → ℝ≥0 → ℝ) (hc : ∀ k, c k ∈ C) (c0 : ℝ≥0 → ℝ) (hc0 : c0 ∈ C)
    {Y : Type*} [Fintype Y] (e : Y → ℝ≥0) (he : ∀ y, 0 < e y)
    (D : Y → Finset ((Σ k, Fin (a k).natAbs) × Bool))
    (ho : ∀ x, (∑ y, if x ∈ D y then e y else 0) = b x.1.1)
    {n : ℕ} (hn : 0 < n) (eP : Fin n ≃ Bool ⊕ Y)
    (hcons : ∀ (m : ℕ) (G : Game n m), (∀ f, G.cost f ∈ C) →
      ∃ s : G.Profile, AGT.IsPureNash (fun i t => -privateCost G t i) s)
    (d1 d2 : ℝ≥0) (hd1 : 0 < d1) (hd2 : 0 < d2) :
    ∃ p q : Bool,
      ∑ k, (a k : ℝ) * c k ((d1 + if p = q then d2 else 0) + b k) ≤
        ∑ k, (a k : ℝ) * c k ((d1 + if (!p) = q then d2 else 0) + b k) ∧
      ∑ k, (a k : ℝ) * c k ((d2 + if q = p then d1 else 0) + b k) ≤
        ∑ k, (a k : ℝ) * c k ((d2 + if (!q) = p then d1 else 0) + b k) := by
  let X := (Σ k, Fin (a k).natAbs) × Bool
  let fl : Fin K → Bool := fun k => decide (a k < 0)
  let side : X → Bool := fun x => x.2
  let p2 : X → Bool := fun x => xor x.2 (fl x.1.1)
  let cf : X → ℝ≥0 → ℝ := fun x => c x.1.1
  let eF : Fin (Fintype.card (Option X)) ≃ Option X := (Fintype.equivFin (Option X)).symm
  have hm : 0 < Fintype.card (Option X) := Fintype.card_pos
  let G := x8game hn hm eP eF side p2 D d1 d2 e hd1 hd2 he cf c0
  have hcost : ∀ f, G.cost f ∈ C := fun f => by
    change (eF f).elim c0 cf ∈ C
    rcases eF f with _ | x
    · exact hc0
    · exact hc _
  obtain ⟨s, hs⟩ := hcons _ G hcost
  obtain ⟨p, q, i1, i2⟩ := x8_nash s (fun x => b x.1.1) (fun x => by convert ho x) hs
  refine ⟨p, q, ?_, ?_⟩
  · 
    rw [x8_sum1 a (fun x => (d1 : ℝ) * cf x (b x.1.1 + d1 + if p2 x = q then d2 else 0)),
      x8_sum1 a (fun x => (d1 : ℝ) * cf x (b x.1.1 + d1 + if p2 x = q then d2 else 0))] at i1
    rw [x8_sigma a (fun k => (d1 : ℝ) * c k (b k + d1 + if xor p (fl k) = q then d2 else 0)),
      x8_sigma a (fun k => (d1 : ℝ) * c k (b k + d1 + if xor (!p) (fl k) = q then d2 else 0))] at i1
    have key : ∑ k, ((a k).natAbs : ℝ) * ((d1 : ℝ) * c k (b k + d1 + if xor (!p) (fl k) = q then d2 else 0)) -
        ∑ k, ((a k).natAbs : ℝ) * ((d1 : ℝ) * c k (b k + d1 + if xor p (fl k) = q then d2 else 0)) =
        (d1 : ℝ) * (∑ k, (a k : ℝ) * c k ((d1 + if (!p) = q then d2 else 0) + b k) -
          ∑ k, (a k : ℝ) * c k ((d1 + if p = q then d2 else 0) + b k)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := x8_term (a k) (fun t => c k ((d1 + if t = q then d2 else 0) + b k)) p
      have e1 : ∀ t : Bool, b k + d1 + (if t = q then d2 else 0) = (d1 + if t = q then d2 else 0) + b k :=
        fun t => by ring
      simp only [e1]
      linear_combination (d1 : ℝ) * this
    have hd : (0 : ℝ) < d1 := hd1
    nlinarith
  · 
    rw [x8_sum2 a fl (fun x => (d2 : ℝ) * cf x (b x.1.1 + (if side x = p then d1 else 0) + d2)),
      x8_sum2 a fl (fun x => (d2 : ℝ) * cf x (b x.1.1 + (if side x = p then d1 else 0) + d2))] at i2
    rw [x8_sigma a (fun k => (d2 : ℝ) * c k (b k + (if xor q (fl k) = p then d1 else 0) + d2)),
      x8_sigma a (fun k => (d2 : ℝ) * c k (b k + (if xor (!q) (fl k) = p then d1 else 0) + d2))] at i2
    have key : ∑ k, ((a k).natAbs : ℝ) * ((d2 : ℝ) * c k (b k + (if xor (!q) (fl k) = p then d1 else 0) + d2)) -
        ∑ k, ((a k).natAbs : ℝ) * ((d2 : ℝ) * c k (b k + (if xor q (fl k) = p then d1 else 0) + d2)) =
        (d2 : ℝ) * (∑ k, (a k : ℝ) * c k ((d2 + if (!q) = p then d1 else 0) + b k) -
          ∑ k, (a k : ℝ) * c k ((d2 + if q = p then d1 else 0) + b k)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := x8_term (a k) (fun t => c k ((d2 + if t = p then d1 else 0) + b k)) q
      have e1 : ∀ t : Bool, b k + (if t = p then d1 else 0) + d2 = (d2 + if t = p then d1 else 0) + b k :=
        fun t => by ring
      simp only [e1]
      linear_combination (d2 : ℝ) * this
    have hd : (0 : ℝ) < d2 := hd2
    nlinarith

end

end X8HK


open scoped NNReal

namespace X8HK
open HarksKlimm.Consistency

noncomputable section
open Classical

theorem x8_mono (C : Set (ℝ≥0 → ℝ)) (hC : ∀ c ∈ C, Continuous c) {K : ℕ} (a : Fin K → ℤ)
    (b : Fin K → ℝ≥0) (c : Fin K → ℝ≥0 → ℝ) (hc : ∀ k, c k ∈ C) (c0 : ℝ≥0 → ℝ) (hc0 : c0 ∈ C)
    {Y : Type*} [Fintype Y] (e : Y → ℝ≥0) (he : ∀ y, 0 < e y)
    (D : Y → Finset ((Σ k, Fin (a k).natAbs) × Bool))
    (ho : ∀ x, (∑ y, if x ∈ D y then e y else 0) = b x.1.1)
    {n : ℕ} (hn : 0 < n) (eP : Fin n ≃ Bool ⊕ Y)
    (hcons : ∀ (m : ℕ) (G : Game n m), (∀ f, G.cost f ∈ C) →
      ∃ s : G.Profile, AGT.IsPureNash (fun i t => -privateCost G t i) s)
    (h : ℝ≥0 → ℝ) (hEq : ∀ x, h x = ∑ k, (a k : ℝ) * c k (x + b k)) : IsMonotonic h := by
  by_contra hnm
  have hcont : Continuous h := by
    have : h = fun x => ∑ k, (a k : ℝ) * c k (x + b k) := funext hEq
    rw [this]
    exact continuous_finsetSum _ fun k _ =>
      continuous_const.mul ((hC _ (hc k)).comp (continuous_id.add continuous_const))
  obtain ⟨x, y, hx, hxy, hw⟩ := three_load_witness h hcont hnm
  have hd2 : 0 < y - x := tsub_pos_of_lt hxy
  obtain ⟨p, q, i1, i2⟩ := x8_core C a b c hc c0 hc0 e he D ho hn eP hcons x (y - x) hx hd2
  simp only [← hEq] at i1 i2
  have e1 : x + (y - x) = y := add_tsub_cancel_of_le hxy.le
  have e2 : y - x + x = y := tsub_add_cancel_of_le hxy.le
  cases p <;> cases q <;> simp [e1, e2] at i1 i2 <;> rcases hw with ⟨w1, w2⟩ | ⟨w1, w2⟩ <;> linarith

theorem x8_ext_mono (C : Set (ℝ≥0 → ℝ)) (hC : ∀ c ∈ C, Continuous c) (hcons : Consistent C) :
    ∀ h ∈ IntegerHull C, IsMonotonic h := by
  intro h hh
  obtain ⟨K, a, b, c, hc, hEq⟩ := hh
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    left
    intro u v _
    simp [hEq]
  let Y := {k : Fin K // 0 < b k}
  let D : Y → Finset ((Σ k, Fin (a k).natAbs) × Bool) :=
    fun y => Finset.univ.filter (fun x => x.1.1 = y.1)
  have ho : ∀ x, (∑ y : Y, if x ∈ D y then b y.1 else 0) = b x.1.1 := by
    intro x
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h0 : 0 < b x.1.1
    · rw [Fintype.sum_eq_single ⟨x.1.1, h0⟩]
      · simp
      · intro y hy
        have : x.1.1 ≠ y.1 := fun h' => hy (Subtype.ext h'.symm)
        simp [this]
    · have hb0 : b x.1.1 = 0 := le_antisymm (not_lt.mp h0) zero_le
      rw [hb0]
      refine Finset.sum_eq_zero fun y _ => ?_
      have : x.1.1 ≠ y.1 := fun h' => h0 (h' ▸ y.2)
      simp [this]
  exact x8_mono C hC a b c hc (c ⟨0, hK⟩) (hc _) (fun y : Y => b y.1) (fun y => y.2) D ho
    Fintype.card_pos (Fintype.equivFin (Bool ⊕ Y)).symm (hcons _) h hEq

theorem x8_restricted (C : Set (ℝ≥0 → ℝ)) (hC : ∀ c ∈ C, Continuous c)
    (hcons : ThreeConsistent C) :
    (∀ h ∈ TwoHull C, IsMonotonic h) ∧ (∀ h ∈ ShiftHull C, IsMonotonic h) := by
  have eP : Fin 3 ≃ Bool ⊕ Unit := Fintype.equivOfCardEq (by simp)
  refine ⟨fun h hh => ?_, fun h hh => ?_⟩
  · obtain ⟨a₁, a₂, c₁, c₂, h1, h2, hEq⟩ := hh
    let a : Fin 2 → ℤ := ![a₁, a₂]
    let c : Fin 2 → ℝ≥0 → ℝ := ![c₁, c₂]
    have hc : ∀ k, c k ∈ C := fun k => by fin_cases k <;> simpa [c]
    refine x8_mono C hC a (fun _ => 0) c hc c₁ h1 (fun _ : Unit => 1) (fun _ => one_pos)
      (fun _ => ∅) (fun x => by simp) (by norm_num) eP (fun m G => hcons m G) h ?_
    intro x
    simp [Fin.sum_univ_two, a, c, hEq]
  · obtain ⟨a₁, a₂, c₀, δ, h0, hδ, hEq⟩ := hh
    let a : Fin 2 → ℤ := ![a₁, a₂]
    let b : Fin 2 → ℝ≥0 := ![0, δ]
    let c : Fin 2 → ℝ≥0 → ℝ := ![c₀, c₀]
    have hc : ∀ k, c k ∈ C := fun k => by fin_cases k <;> simpa [c]
    have ho : ∀ x : (Σ k, Fin (a k).natAbs) × Bool,
        (∑ y : Unit, if x ∈ (Finset.univ.filter (fun x : (Σ k, Fin (a k).natAbs) × Bool =>
          x.1.1 = 1)) then δ else 0) = b x.1.1 := by
      intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.univ_unique,
        Finset.sum_singleton]
      generalize x.1.1 = k
      fin_cases k <;> simp [b]
    refine x8_mono C hC a b c hc c₀ h0 (fun _ : Unit => δ) (fun _ => hδ) _ ho (by norm_num) eP
      (fun m G => hcons m G) h ?_
    intro x
    simp [Fin.sum_univ_two, a, b, c, hEq]

end

end X8HK


open HarksKlimm.Consistency in
theorem solution (C : Set (ℝ≥0 → ℝ))
    (hC : ∀ c ∈ C, Continuous c) (hcons : Consistent C) :
    ∀ h ∈ IntegerHull C, IsMonotonic h :=
  X8HK.x8_ext_mono C hC hcons
