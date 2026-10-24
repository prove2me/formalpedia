-- Prove2me | solution 1 for MultiSecretary.NonAdaptive.sqrt_regret_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-23T06:23:27.608757+00:00
-- url     : https://prove2.me/submissions/26990e37-65a6-4fcb-9026-024574c88bfc

import Mathlib
import Definitions.Def_MultiSecretary_NonAdaptive_Model
import Definitions.Def_MultiSecretary_NonAdaptive_Policy

noncomputable section
open MultiSecretary.NonAdaptive Finset
namespace MultiSecretaryProof

def pairExpect {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (H : (Fin n → Fin m × Bool) → ℝ) : ℝ :=
  ∑ ω, naWeight f p ω * H ω

def boolExpect {n : ℕ} (q : Fin n → ℝ) (H : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ b, bernWeight q b * H b

def selectedSet {m n : ℕ} (k : ℕ) (ω : Fin n → Fin m × Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun t => selected k ω t = true)

def coinCount {n : ℕ} (b : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun t => b t = true)).card

def regret {m n : ℕ} (a f : Fin m → ℝ) (k : ℕ)
    (p : Fin m → Fin n → ℝ) : ℝ := Voff a f n k - Vna a f k p

def liveProb {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (k : ℕ) (t : Fin n) : ℝ :=
  pairExpect f p (fun ω => if
    (Finset.univ.filter (fun s : Fin n => s < t ∧ (ω s).2 = true)).card < k
    then 1 else 0)

def blocked {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ t, (1 - liveProb f p k t)

def separatedValues {m : ℕ} (g : ℝ) (a : Fin m → ℝ) : Prop :=
  (∀ j, g ≤ a j) ∧ ∀ i j, i < j → g ≤ a i - a j

end MultiSecretaryProof

noncomputable section
open MultiSecretary.NonAdaptive Finset
namespace MultiSecretaryProof

private def weightedExpect {n : ℕ} {α : Type*} [Fintype α]
    (w : Fin n → α → ℝ) (H : (Fin n → α) → ℝ) : ℝ :=
  ∑ x, (∏ t, w t (x t)) * H x

private theorem weightedExpect_snoc {n : ℕ} {α : Type*} [Fintype α]
    (w : Fin (n+1) → α → ℝ) (H : (Fin (n+1) → α) → ℝ) :
    weightedExpect w H = weightedExpect (fun t => w t.castSucc)
      (fun b => ∑ z, w (Fin.last n) z * H (Fin.snoc b z)) := by
  classical
  unfold weightedExpect
  rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => α)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro z _
  ring

private theorem weightedExpect_map {n : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    (w : Fin n → α → ℝ) (v : Fin n → β → ℝ) (F : Fin n → α → β)
    (h : ∀ t (G : β → ℝ), (∑ z, w t z * G (F t z)) = ∑ z, v t z * G z)
    (H : (Fin n → β) → ℝ) :
    weightedExpect w (fun x => H (fun t => F t (x t))) = weightedExpect v H := by
  classical
  induction n with
  | zero =>
    simp only [weightedExpect, Finset.univ_eq_empty, Finset.prod_empty, one_mul, Fintype.sum_unique]
    congr 1
    exact funext (fun t => Fin.elim0 t)
  | succ n ih =>
    rw [weightedExpect_snoc, weightedExpect_snoc]
    have he (b : Fin n → α) (z : α) :
        (fun t => F t (Fin.snoc (α := fun _ : Fin (n+1) => α) b z t)) =
          Fin.snoc (fun t => F t.castSucc (b t)) (F (Fin.last n) z) := by
      ext t
      refine Fin.lastCases ?_ (fun i => ?_) t <;> simp
    simp_rw [he]
    have hh (b : Fin n → α) := h (Fin.last n)
      (fun z => H (Fin.snoc (fun t => F t.castSucc (b t)) z))
    simp_rw [hh]
    exact ih (fun t => w t.castSucc) (fun t => v t.castSucc)
      (fun t => F t.castSucc) (fun t => h t.castSucc)
      (fun b => ∑ z, v (Fin.last n) z * H (Fin.snoc b z))

private theorem weightedExpect_const {n : ℕ} {α : Type*} [Fintype α]
    (w : Fin n → α → ℝ) (hw : ∀ t, ∑ z, w t z = 1) (c : ℝ) :
    weightedExpect w (fun _ => c) = c := by
  classical
  unfold weightedExpect
  rw [← Finset.sum_mul, ← Fintype.prod_sum]
  simp [hw]

private theorem weightedExpect_add {n : ℕ} {α : Type*} [Fintype α]
    (w : Fin n → α → ℝ) (H G : (Fin n → α) → ℝ) :
    weightedExpect w (fun x => H x + G x) = weightedExpect w H + weightedExpect w G := by
  simp [weightedExpect, mul_add, Finset.sum_add_distrib]

private theorem weightedExpect_mul_const {n : ℕ} {α : Type*} [Fintype α]
    (w : Fin n → α → ℝ) (H : (Fin n → α) → ℝ) (c : ℝ) :
    weightedExpect w (fun x => H x * c) = weightedExpect w H * c := by
  simp [weightedExpect, ← mul_assoc, Finset.sum_mul]

private theorem snoc_update {n : ℕ} {α : Type*} (b : Fin n → α)
    (t : Fin n) (z a : α) :
    Fin.snoc (α := fun _ : Fin (n+1) => α) (Function.update b t z) a = Function.update (Fin.snoc (α := fun _ : Fin (n+1) => α) b a) t.castSucc z := by
  classical
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Function.update_of_ne ((ne_of_gt (Fin.castSucc_lt_last t)))]
  · by_cases h : j = t
    · subst j; simp
    · simp [h]

private theorem weightedExpect_factor {n : ℕ} {α : Type*} [Fintype α] [Nonempty α]
    (w : Fin n → α → ℝ) (hw : ∀ t, ∑ z, w t z = 1)
    (t : Fin n) (H : (Fin n → α) → ℝ) (G : α → ℝ)
    (hH : ∀ x z, H (Function.update x t z) = H x) :
    weightedExpect w (fun x => H x * G (x t)) =
      weightedExpect w H * ∑ z, w t z * G z := by
  classical
  induction n with
  | zero => exact Fin.elim0 t
  | succ n ih =>
    revert hH
    refine Fin.lastCases ?_ (fun i => ?_) t
    · intro hH
      let a : α := Classical.choice inferInstance
      have he (b : Fin n → α) (z : α) : H (Fin.snoc b z) = H (Fin.snoc b a) := by
        have h := hH (Fin.snoc b a) z
        have hu : Function.update (Fin.snoc (α := fun _ : Fin (n+1) => α) b a) (Fin.last n) z = Fin.snoc (α := fun _ : Fin (n+1) => α) b z := by
          ext j
          refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
        simpa only [hu] using h
      rw [weightedExpect_snoc, weightedExpect_snoc]
      simp only [Fin.snoc_last]
      simp_rw [he]
      simp only [← Finset.sum_mul, hw, one_mul]
      have hx (b : Fin n → α) :
          (∑ z, w (Fin.last n) z * (H (Fin.snoc b a) * G z)) =
            H (Fin.snoc b a) * ∑ z, w (Fin.last n) z * G z := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      rw [show (fun b => ∑ z, w (Fin.last n) z * (H (Fin.snoc b a) * G z)) =
        (fun b => H (Fin.snoc b a) * ∑ z, w (Fin.last n) z * G z) from funext hx]
      exact weightedExpect_mul_const _ _ _
    · intro hH
      rw [weightedExpect_snoc, weightedExpect_snoc]
      simp only [Fin.snoc_castSucc]
      have he (b : Fin n → α) :
          (∑ z, w (Fin.last n) z * (H (Fin.snoc b z) * G (b i))) =
          (∑ z, w (Fin.last n) z * H (Fin.snoc b z)) * G (b i) := by
        simp [← mul_assoc, Finset.sum_mul]
      simp_rw [he]
      apply ih (fun t => w t.castSucc) (fun t => hw t.castSucc) i
      intro b z
      apply Finset.sum_congr rfl
      intro a _
      rw [snoc_update, hH]

def pairLocal {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (t : Fin n) (z : Fin m × Bool) : ℝ :=
  f z.1 * (if z.2 then p z.1 t else 1-p z.1 t)

 theorem pairLocal_sum {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (hf : IsMasses f) (t : Fin n) : ∑ z, pairLocal f p t z = 1 := by
  classical
  simp only [pairLocal, Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
    if_false, if_true]
  convert! hf.2 using 1
  apply Finset.sum_congr rfl
  intro j _
  ring

 theorem pairLocal_nonneg {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (hf : IsMasses f) (hp : IsNAPolicy p) (t : Fin n) (z : Fin m × Bool) :
    0 ≤ pairLocal f p t z := by
  apply mul_nonneg (hf.1 z.1).le
  split_ifs
  · exact (hp z.1 t).1
  · exact sub_nonneg.mpr (hp z.1 t).2

 theorem pairExpect_nonneg {m n : ℕ} (f : Fin m → ℝ)
    (p : Fin m → Fin n → ℝ) (hf : IsMasses f) (hp : IsNAPolicy p)
    (H : (Fin n → Fin m × Bool) → ℝ) (hH : ∀ ω, 0 ≤ H ω) :
    0 ≤ pairExpect f p H := by
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (Finset.prod_nonneg (fun t _ => pairLocal_nonneg f p hf hp t (ω t))) (hH ω)

 theorem pairExpect_mono {m n : ℕ} (f : Fin m → ℝ)
    (p : Fin m → Fin n → ℝ) (hf : IsMasses f) (hp : IsNAPolicy p)
    {H G : (Fin n → Fin m × Bool) → ℝ} (h : ∀ ω, H ω ≤ G ω) :
    pairExpect f p H ≤ pairExpect f p G := by
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (h ω)
    (Finset.prod_nonneg (fun t _ => pairLocal_nonneg f p hf hp t (ω t)))

 theorem pairExpect_const {m n : ℕ} (f : Fin m → ℝ)
    (p : Fin m → Fin n → ℝ) (hf : IsMasses f) (c : ℝ) :
    pairExpect f p (fun _ => c) = c :=
  weightedExpect_const (pairLocal f p) (pairLocal_sum f p hf) c

 theorem pairExpect_one {m n : ℕ} (f : Fin m → ℝ)
    (p : Fin m → Fin n → ℝ) (hf : IsMasses f) (hp : IsNAPolicy p) :
    pairExpect f p (fun _ => 1) = 1 := by
  have _ := hp
  exact pairExpect_const f p hf 1

 theorem pairExpect_add {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (H G : (Fin n → Fin m × Bool) → ℝ) :
    pairExpect f p (fun ω => H ω+G ω) = pairExpect f p H + pairExpect f p G := by
  simp [pairExpect, mul_add, Finset.sum_add_distrib]

 theorem pairExpect_sub {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (H G : (Fin n → Fin m × Bool) → ℝ) :
    pairExpect f p (fun ω => H ω-G ω) = pairExpect f p H - pairExpect f p G := by
  simp [pairExpect, mul_sub, Finset.sum_sub_distrib]

 theorem pairExpect_mul {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (c : ℝ) (H : (Fin n → Fin m × Bool) → ℝ) :
    pairExpect f p (fun ω => c*H ω) = c*pairExpect f p H := by
  simp only [pairExpect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

 theorem pairExpect_sum {m n : ℕ} {ι : Type*} [Fintype ι]
    (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (H : ι → (Fin n → Fin m × Bool) → ℝ) :
    pairExpect f p (fun ω => ∑ i, H i ω) = ∑ i, pairExpect f p (H i) := by
  simp only [pairExpect, Finset.mul_sum]
  rw [Finset.sum_comm]

 theorem boolExpect_const {n : ℕ} (q : Fin n → ℝ) (c : ℝ) :
    boolExpect q (fun _ => c) = c := by
  change weightedExpect (fun (t : Fin n) (b : Bool) => if b then q t else 1-q t) (fun _ => c) = c
  apply weightedExpect_const
  intro t
  simp

 theorem boolExpect_one {n : ℕ} (q : Fin n → ℝ) :
    boolExpect q (fun _ => 1) = 1 := boolExpect_const q 1

 theorem boolExpect_nonneg {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) (H : (Fin n → Bool) → ℝ)
    (hH : ∀ b, 0 ≤ H b) : 0 ≤ boolExpect q H := by
  apply Finset.sum_nonneg
  intro b _
  apply mul_nonneg _ (hH b)
  apply Finset.prod_nonneg
  intro t _
  split_ifs
  · exact (hq t).1
  · exact sub_nonneg.mpr (hq t).2

 theorem boolExpect_mono {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) {H G : (Fin n → Bool) → ℝ}
    (h : ∀ b, H b ≤ G b) : boolExpect q H ≤ boolExpect q G := by
  have hh := boolExpect_nonneg q hq (fun b => G b-H b) (fun b => sub_nonneg.mpr (h b))
  change 0 ≤ ∑ b, bernWeight q b * (G b-H b) at hh
  simp only [mul_sub, Finset.sum_sub_distrib] at hh
  exact sub_nonneg.mp hh

 theorem boolExpect_add {n : ℕ} (q : Fin n → ℝ) (H G : (Fin n → Bool) → ℝ) :
    boolExpect q (fun b => H b+G b) = boolExpect q H + boolExpect q G := by
  simp [boolExpect, mul_add, Finset.sum_add_distrib]

 theorem boolExpect_sub {n : ℕ} (q : Fin n → ℝ) (H G : (Fin n → Bool) → ℝ) :
    boolExpect q (fun b => H b-G b) = boolExpect q H - boolExpect q G := by
  simp [boolExpect, mul_sub, Finset.sum_sub_distrib]

 theorem boolExpect_mul {n : ℕ} (q : Fin n → ℝ) (c : ℝ) (H : (Fin n → Bool) → ℝ) :
    boolExpect q (fun b => c*H b) = c*boolExpect q H := by
  simp only [boolExpect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

 theorem boolExpect_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (q : Fin n → ℝ) (H : ι → (Fin n → Bool) → ℝ) :
    boolExpect q (fun b => ∑ i, H i b) = ∑ i, boolExpect q (H i) := by
  simp only [boolExpect, Finset.mul_sum]
  rw [Finset.sum_comm]

 theorem boolExpect_snoc {n : ℕ} (q : Fin (n+1) → ℝ)
    (H : (Fin (n+1) → Bool) → ℝ) :
    boolExpect q H = boolExpect (fun t => q t.castSucc)
      (fun b => (1-q (Fin.last n))*H (Fin.snoc b false)+q (Fin.last n)*H (Fin.snoc b true)) := by
  rw [show boolExpect q H = weightedExpect (fun t b => if b then q t else 1-q t) H from rfl,
    weightedExpect_snoc]
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
  change weightedExpect (fun (t : Fin n) (b : Bool) => if b then q t.castSucc else 1-q t.castSucc) _ =
    weightedExpect (fun (t : Fin n) (b : Bool) => if b then q t.castSucc else 1-q t.castSucc) _
  congr 1
  funext b
  ring

 theorem pairExpect_disintegrate {m n : ℕ} (f : Fin m → ℝ)
    (p : Fin m → Fin n → ℝ) (H : (Fin n → Fin m × Bool) → ℝ) :
    pairExpect f p H = ∑ x : Fin n → Fin m,
      prob f x * boolExpect (fun t => p (x t) t) (fun b => H (fun t => (x t,b t))) := by
  classical
  unfold pairExpect
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin m) (fun _ => Bool)).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Equiv.arrowProdEquivProdArrow, Equiv.symm_mk, Equiv.coe_fn_mk,
    naWeight, Finset.prod_mul_distrib, boolExpect, prob, bernWeight, Finset.mul_sum]
  simp only [mul_assoc]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro b _
  ac_rfl

 theorem pairExpect_ability {m n : ℕ} (f : Fin m → ℝ)
    (p : Fin m → Fin n → ℝ) (hp : IsNAPolicy p)
    (H : (Fin n → Fin m) → ℝ) :
    pairExpect f p (fun ω => H (fun t => (ω t).1)) = expect f H := by
  have _ := hp
  rw [pairExpect_disintegrate]
  simp only [boolExpect_const, MultiSecretary.NonAdaptive.expect]

 theorem pairExpect_coin {m n : ℕ} (f : Fin m → ℝ)
    (p : Fin m → Fin n → ℝ) (hf : IsMasses f) (H : (Fin n → Bool) → ℝ) :
    pairExpect f p (fun ω => H (fun t => (ω t).2)) = boolExpect (selProb f p) H := by
  apply weightedExpect_map (pairLocal f p) (fun t b => if b then selProb f p t else 1-selProb f p t)
    (fun _ z => z.2)
  intro t G
  simp only [pairLocal, Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
    if_false, if_true, selProb]
  calc
    _ = (∑ j, p j t*f j)*G true + (∑ j, (f j- p j t*f j))*G false := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul]
      apply congrArg₂ (·+·)
      · apply Finset.sum_congr rfl
        intro j _
        ring
      · apply Finset.sum_congr rfl
        intro j _
        ring
    _ = _ := by rw [Finset.sum_sub_distrib, hf.2]

 theorem selProb_bounds {m n : ℕ} (f : Fin m → ℝ)
    (p : Fin m → Fin n → ℝ) (hf : IsMasses f) (hp : IsNAPolicy p) :
    ∀ t, 0 ≤ selProb f p t ∧ selProb f p t ≤ 1 := by
  intro t
  constructor
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (hp j t).1 (hf.1 j).le)
  · calc
      _ ≤ ∑ j, f j := Finset.sum_le_sum (fun j _ => mul_le_of_le_one_left (hf.1 j).le (hp j t).2)
      _ = 1 := hf.2

 theorem pairExpect_factor {m n : ℕ} (f : Fin m → ℝ)
    (p : Fin m → Fin n → ℝ) (hf : IsMasses f) (hp : IsNAPolicy p)
    (t : Fin n) (H : (Fin n → Fin m × Bool) → ℝ) (G : Fin m × Bool → ℝ)
    (hH : ∀ ω z, H (Function.update ω t z) = H ω) :
    pairExpect f p (fun ω => H ω*G (ω t)) =
      pairExpect f p H * ∑ z : Fin m × Bool,
        (f z.1*(if z.2 then p z.1 t else 1-p z.1 t))*G z := by
  have _ := hp
  have hm : Nonempty (Fin m) := by
    by_contra he
    have : IsEmpty (Fin m) := not_nonempty_iff.mp he
    simpa using hf.2
  let := hm
  exact weightedExpect_factor (pairLocal f p) (pairLocal_sum f p hf) t H G hH

 theorem expect_indicator_law {m n : ℕ} (f : Fin m → ℝ)
    (hf : IsMasses f) (j : Fin m) (H : (Fin n → Bool) → ℝ) :
    expect f (fun x => H (fun t => decide (x t=j))) = boolExpect (fun _ => f j) H := by
  classical
  apply weightedExpect_map (fun _ z => f z) (fun _ b => if b then f j else 1-f j)
    (fun _ z => decide (z=j))
  intro t G
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
  have he : ∀ z, f z*G (decide (z=j)) =
      (if z=j then f z*G true else 0)+(if z≠j then f z*G false else 0) := by
    intro z
    by_cases h : z=j <;> simp [h]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', mem_univ, if_true]
  have hh : (∑ z, if z≠j then f z else 0) = 1-f j := by
    have hsum : (∑ z, f z) = f j + ∑ z, if z≠j then f z else 0 := by
      calc
        _ = ∑ z, ((if z=j then f z else 0)+(if z≠j then f z else 0)) := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases h : z=j <;> simp [h]
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    linarith [hf.2]
  rw [show (∑ z, if z≠j then f z*G false else 0) = (∑ z, if z≠j then f z else 0)*G false by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro z _; split_ifs <;> simp, hh]

 theorem boolExpect_coordinate {n : ℕ} (q : Fin n → ℝ) (t : Fin n) :
    boolExpect q (fun b => if b t then (1:ℝ) else 0) = q t := by
  have h := weightedExpect_factor (fun (t : Fin n) (b : Bool) => if b then q t else 1-q t)
    (fun t => by simp) t (fun _ => (1:ℝ))
    (fun b => if b then (1:ℝ) else 0) (fun _ _ => rfl)
  have hw (t : Fin n) : (∑ b : Bool, if b then q t else 1-q t) = 1 := by simp
  rw [weightedExpect_const _ hw] at h
  change weightedExpect (fun (t : Fin n) (b : Bool) => if b then q t else 1-q t) _ = q t
  simpa only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, mul_one, mul_zero, add_zero, one_mul] using h

 theorem coinCount_eq_sum {n : ℕ} (b : Fin n → Bool) :
    (coinCount b : ℝ) = ∑ t, if b t then (1:ℝ) else 0 := by
  simp [coinCount, Finset.sum_boole]

 theorem boolExpect_count {n : ℕ} (q : Fin n → ℝ) :
    boolExpect q (fun b => (coinCount b : ℝ)) = ∑ t, q t := by
  simp_rw [coinCount_eq_sum]
  rw [boolExpect_sum]
  simp only [boolExpect_coordinate]

 theorem boolExpect_prefix_event {n : ℕ} (q : Fin n → ℝ) (k : ℕ) :
    boolExpect q (fun b => if ∀ t : Fin n, t.val<k → b t=true then 1 else 0) =
      ∏ t : Fin n, if t.val<k then q t else 1 := by
  classical
  have he (b : Fin n → Bool) :
      (∏ t, if b t then q t else 1-q t) *
        (if ∀ t, t.val<k → b t=true then 1 else 0) =
      ∏ t, (if b t then q t else 1-q t) * (if t.val<k → b t=true then 1 else 0) := by
    by_cases h : ∀ t, t.val<k → b t=true
    · rw [if_pos h, mul_one]
      apply Finset.prod_congr rfl
      intro t _
      rw [if_pos (h t), mul_one]
    · obtain ⟨t, ht⟩ := not_forall.mp h
      rw [if_neg h, mul_zero]
      symm
      apply Finset.prod_eq_zero (mem_univ t)
      simp [ht]
  simp only [boolExpect, bernWeight]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun (t : Fin n) (b : Bool) =>
    (if b then q t else 1-q t) * (if t.val < k → b = true then (1 : ℝ) else 0))]
  apply Finset.prod_congr rfl
  intro t _
  by_cases h : t.val<k <;> simp [h]

private theorem min_coin_step (k c : ℕ) (z : Bool) :
    min c k + (if z && decide (c < k) then 1 else 0) = min (c+(if z then 1 else 0)) k := by
  cases z
  · simp
  · by_cases h : c < k
    · simp [h, Nat.min_eq_left (Nat.le_of_lt h)]
    · simp [h, Nat.min_eq_right (show k ≤ c by omega), Nat.min_eq_right (show k ≤ c+1 by omega)]

 theorem selectedSet_card {m n : ℕ} (k : ℕ) (ω : Fin n → Fin m × Bool) :
    (selectedSet k ω).card = min (coinCount (fun t => (ω t).2)) k := by
  classical
  induction n with
  | zero => simp [selectedSet, coinCount]
  | succ n ih =>
    let b : Fin n → Fin m × Bool := fun t => ω t.castSucc
    have hp (i : Fin n) :
        (univ.filter (fun s : Fin (n+1) => s < i.castSucc ∧ (ω s).2=true)).card =
        (univ.filter (fun s : Fin n => s < i ∧ (b s).2=true)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Fin.sum_univ_castSucc]
      simp [b, not_lt.mpr (Fin.castSucc_lt_last i).le]
    have hl :
        (univ.filter (fun s : Fin (n+1) => s < Fin.last n ∧ (ω s).2=true)).card =
        coinCount (fun t => (b t).2) := by
      simp only [coinCount, Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.castSucc_lt_last, true_and, lt_self_iff_false, false_and, if_false, Nat.add_zero]
      rfl
    have hc : coinCount (fun t => (ω t).2) = coinCount (fun t => (b t).2) +
        (if (ω (Fin.last n)).2 then 1 else 0) := by
      simp only [coinCount, Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Fin.sum_univ_castSucc]
    have hsc : (selectedSet k ω).card = (selectedSet k b).card +
        (if (ω (Fin.last n)).2 && decide (coinCount (fun t => (b t).2)<k) then 1 else 0) := by
      simp only [selectedSet, Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Fin.sum_univ_castSucc]
      simp only [selected, hp, hl, b]
    calc
      _ = min (coinCount (fun t => (b t).2)) k +
          (if (ω (Fin.last n)).2 && decide (coinCount (fun t => (b t).2)<k) then 1 else 0) := by
        rw [hsc, ih b]
      _ = min (coinCount (fun t => (b t).2)+(if (ω (Fin.last n)).2 then 1 else 0)) k := min_coin_step k _ _
      _ = _ := by rw [hc]


end MultiSecretaryProof

noncomputable section
open MultiSecretary.NonAdaptive Finset
namespace MultiSecretaryProof

theorem separatedValues_exists {m : ℕ} (a : Fin m → ℝ) (ha : IsValues a) :
    ∃ g : ℝ, 0 < g ∧ separatedValues g a := by
  classical
  let v : Option (Fin m ⊕ (Fin m × Fin m)) → ℝ
    | none => 1
    | some (.inl i) => a i
    | some (.inr (i,j)) => if i < j then a i - a j else 1
  have hv : ∀ z, 0 < v z := by
    intro z
    cases z with
    | none => norm_num [v]
    | some z =>
      cases z with
      | inl i => exact ha.2 i
      | inr ij =>
        rcases ij with ⟨i,j⟩
        dsimp [v]
        split_ifs with h
        · exact sub_pos.mpr (ha.1 h)
        · norm_num
  let g := univ.inf' univ_nonempty v
  have hg : 0 < g := (lt_inf'_iff _).mpr (fun z _ => hv z)
  refine ⟨g, hg, ?_, ?_⟩
  · intro j
    exact inf'_le v (mem_univ (some (Sum.inl j)))
  · intro i j hij
    simpa [v, hij] using (inf'_le v (mem_univ (some (Sum.inr (i,j)))))

theorem offMax_ge_sum {m n : ℕ} (a : Fin m → ℝ) (k : ℕ)
    (x : Fin n → Fin m) (S : Finset (Fin n)) (hS : S.card ≤ k) :
    (∑ t ∈ S, a (x t)) ≤ offMax a k x := by
  classical
  unfold offMax
  exact le_sup' (fun T : Finset (Fin n) => ∑ t ∈ T, a (x t)) (mem_filter.mpr ⟨mem_univ S, hS⟩)

/-- Add missing desirable positions and remove as many low positions as needed. -/
theorem threshold_gap {m n : ℕ} (a : Fin m → ℝ) (k : ℕ)
    (x : Fin n → Fin m) (U S : Finset (Fin n)) (g c : ℝ)
    (hg : 0 ≤ g) (hc : 0 ≤ c) (hS : S.card ≤ k)
    (hu : ∀ t ∈ U, c + g ≤ a (x t))
    (hl : ∀ t ∉ U, a (x t) ≤ c) :
    g * ((min k U.card - (S ∩ U).card : ℕ) : ℝ) ≤
      offMax a k x - ∑ t ∈ S, a (x t) := by
  classical
  have _ := hg
  let d := min k U.card - (S ∩ U).card
  let e := min d (S \ U).card
  have hiS : (S ∩ U).card ≤ S.card := card_le_card inter_subset_left
  have hiU : (S ∩ U).card ≤ U.card := card_le_card inter_subset_right
  have hSU := card_sdiff_add_card_inter S U
  have hUS := card_sdiff_add_card_inter U S
  have hcard : (U ∩ S).card = (S ∩ U).card := by rw [inter_comm]
  have hd : d ≤ (U \ S).card := by dsimp [d]; omega
  obtain ⟨T, hT, hTd⟩ := exists_subset_card_eq hd
  have he : e ≤ (S \ U).card := Nat.min_le_right _ _
  obtain ⟨V, hV, hVe⟩ := exists_subset_card_eq he
  have hVS : V ⊆ S := hV.trans sdiff_subset
  have hTS : Disjoint S T := by
    refine disjoint_left.mpr ?_
    intro t ht hs
    exact (mem_sdiff.mp (hT hs)).2 ht
  have hdis : Disjoint (S \ V) T := hTS.mono_left sdiff_subset
  have hW : ((S \ V) ∪ T).card ≤ k := by
    rw [card_union_of_disjoint hdis, card_sdiff_of_subset hVS, hTd, hVe]
    dsimp [d, e]
    omega
  have ho := offMax_ge_sum a k x ((S \ V) ∪ T) hW
  rw [sum_union hdis] at ho
  have hsum := sum_sdiff hVS (f := fun t => a (x t))
  have hlo : (∑ t ∈ V, a (x t)) ≤ (e : ℝ) * c := by
    calc
      _ ≤ ∑ _t ∈ V, c := sum_le_sum (fun t ht => hl t (mem_sdiff.mp (hV ht)).2)
      _ = _ := by simp [hVe]
  have hhi : (d : ℝ) * (c + g) ≤ ∑ t ∈ T, a (x t) := by
    calc
      _ = ∑ _t ∈ T, (c + g) := by simp [hTd]; ring
      _ ≤ _ := sum_le_sum (fun t ht => hu t (mem_sdiff.mp (hT ht)).1)
  have hed : (e : ℝ) ≤ d := by exact_mod_cast (Nat.min_le_left d (S \ U).card)
  have hextra := mul_nonneg (sub_nonneg.mpr hed) hc
  change g * (d : ℝ) ≤ _
  nlinarith only [ho, hsum, hlo, hhi, hextra]

theorem threshold_gap_real {m n : ℕ} (a : Fin m → ℝ) (k : ℕ)
    (x : Fin n → Fin m) (U S : Finset (Fin n)) (g c : ℝ)
    (hg : 0 ≤ g) (hc : 0 ≤ c) (hS : S.card ≤ k)
    (hu : ∀ t ∈ U, c + g ≤ a (x t))
    (hl : ∀ t ∉ U, a (x t) ≤ c) :
    g * (min (k : ℝ) (U.card : ℝ) - ((S ∩ U).card : ℝ)) ≤
      offMax a k x - ∑ t ∈ S, a (x t) := by
  have hh := threshold_gap a k x U S g c hg hc hS hu hl
  have hi : (S ∩ U).card ≤ min k U.card :=
    le_min ((card_le_card inter_subset_left).trans hS) (card_le_card inter_subset_right)
  simpa only [Nat.cast_sub hi, Nat.cast_min] using hh

theorem separated_winner_gap {m n : ℕ} (a : Fin m → ℝ) (k : ℕ)
    (x : Fin n → Fin m) (W S : Finset (Fin n)) (g : ℝ) (hg : 0 < g)
    (hW : W.card = k) (hS : S.card ≤ k) (hne : S ≠ W)
    (hpos : ∀ t ∈ W, g ≤ a (x t))
    (hsep : ∀ t ∈ W, ∀ u ∉ W, g ≤ a (x t) - a (x u)) :
    g ≤ offMax a k x - ∑ t ∈ S, a (x t) := by
  classical
  have hneW : W.Nonempty := by
    by_contra hh
    have hw0 : W = ∅ := not_nonempty_iff_eq_empty.mp hh
    have hs0 : S = ∅ := card_eq_zero.mp (by simpa [hw0] using hS.trans_eq hW.symm)
    exact hne (hs0.trans hw0.symm)
  let c := W.inf' hneW (fun t => a (x t)) - g
  have hc : 0 ≤ c := sub_nonneg.mpr (le_inf' hneW _ hpos)
  have hu : ∀ t ∈ W, c + g ≤ a (x t) := by
    intro t ht
    dsimp [c]
    rw [sub_add_cancel]
    exact inf'_le (fun t => a (x t)) ht
  have hl : ∀ u ∉ W, a (x u) ≤ c := by
    intro u hu
    dsimp [c]
    apply le_sub_iff_add_le.mpr
    exact le_inf' hneW _ (fun t ht => by linarith [hsep t ht u hu])
  have hstrict : (S ∩ W).card < k := by
    by_contra hh
    have hi : (S ∩ W).card ≤ S.card := card_le_card inter_subset_left
    have hiW : (S ∩ W).card ≤ W.card := card_le_card inter_subset_right
    have h1 : S ∩ W = S := eq_of_subset_of_card_le inter_subset_left (by omega)
    have h2 : S ∩ W = W := eq_of_subset_of_card_le inter_subset_right (by omega)
    exact hne (h1.symm.trans h2)
  have hd : (1 : ℝ) ≤ (min k W.card - (S ∩ W).card : ℕ) := by
    exact_mod_cast (show 1 ≤ min k W.card - (S ∩ W).card by omega)
  have hmul : g ≤ g * ((min k W.card - (S ∩ W).card : ℕ) : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hg.le
  exact hmul.trans (threshold_gap a k x W S g c hg.le hc hS hu hl)

theorem unused_gap {m n : ℕ} (a : Fin m → ℝ) (k : ℕ)
    (x : Fin n → Fin m) (S : Finset (Fin n)) (g : ℝ)
    (hpos : ∀ j, g ≤ a j) (hS : S.card ≤ k) (hkn : k ≤ n) :
    g * ((k - S.card : ℕ) : ℝ) ≤ offMax a k x - ∑ t ∈ S, a (x t) := by
  classical
  obtain ⟨W, hSW, _, hW⟩ := exists_subsuperset_card_eq (subset_univ S) hS (by simpa using hkn)
  have hsum := sum_sdiff hSW (f := fun t => a (x t))
  have hl : g * ((k - S.card : ℕ) : ℝ) ≤ ∑ t ∈ W \ S, a (x t) := by
    calc
      _ = ∑ _t ∈ W \ S, g := by simp [card_sdiff_of_subset hSW, hW, mul_comm]
      _ ≤ _ := sum_le_sum (fun t _ => hpos (x t))
  have ho := offMax_ge_sum a k x W hW.le
  linarith


end MultiSecretaryProof

noncomputable section
open MultiSecretary.NonAdaptive Finset
namespace MultiSecretaryProof

 theorem centeredSum_eq {n : ℕ} (q : Fin n → ℝ) (b : Fin n → Bool) :
    centeredSum q b = (coinCount b : ℝ) - ∑ t, q t := by
  simp only [centeredSum, Finset.sum_sub_distrib, coinCount_eq_sum]

 theorem varSum_nonneg {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) : 0 ≤ varSum q :=
  Finset.sum_nonneg (fun t _ => mul_nonneg (hq t).1 (sub_nonneg.mpr (hq t).2))

 theorem varSum_le_quarter {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) : varSum q ≤ n/4 := by
  have _ := hq
  calc
    _ ≤ ∑ _ : Fin n, (1:ℝ)/4 := by
      apply Finset.sum_le_sum
      intro t _
      nlinarith [sq_nonneg (q t-1/2)]
    _ = _ := by simp [div_eq_mul_inv]

 theorem centeredSum_snoc {n : ℕ} (q : Fin (n+1) → ℝ) (b : Fin n → Bool) (z : Bool) :
    centeredSum q (Fin.snoc b z) = centeredSum (fun t => q t.castSucc) b +
      (if z then (1:ℝ) else 0) - q (Fin.last n) := by
  simp only [centeredSum, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

 theorem varSum_succ {n : ℕ} (q : Fin (n+1) → ℝ) :
    varSum q = varSum (fun t => q t.castSucc) + q (Fin.last n)*(1-q (Fin.last n)) := by
  simp only [varSum, Fin.sum_univ_castSucc]

 theorem bernoulli_mean_zero {n : ℕ} (q : Fin n → ℝ) :
    boolExpect q (centeredSum q) = 0 := by
  induction n with
  | zero => simp [boolExpect, centeredSum]
  | succ n ih =>
    rw [boolExpect_snoc]
    simp only [centeredSum_snoc, Bool.false_eq_true, if_false, if_true]
    have he (b : Fin n → Bool) :
        (1-q (Fin.last n))*(centeredSum (fun t => q t.castSucc) b+0-q (Fin.last n)) +
          q (Fin.last n)*(centeredSum (fun t => q t.castSucc) b+1-q (Fin.last n)) =
        centeredSum (fun t => q t.castSucc) b := by ring
    simp_rw [he]
    exact ih _

 theorem bernoulli_second {n : ℕ} (q : Fin n → ℝ) :
    boolExpect q (fun b => (centeredSum q b)^2) = varSum q := by
  induction n with
  | zero => simp [boolExpect, centeredSum, varSum]
  | succ n ih =>
    rw [boolExpect_snoc]
    simp only [centeredSum_snoc, Bool.false_eq_true, if_false, if_true]
    have he (b : Fin n → Bool) :
        (1-q (Fin.last n))*(centeredSum (fun t => q t.castSucc) b+0-q (Fin.last n))^2 +
          q (Fin.last n)*(centeredSum (fun t => q t.castSucc) b+1-q (Fin.last n))^2 =
        (centeredSum (fun t => q t.castSucc) b)^2 + q (Fin.last n)*(1-q (Fin.last n)) := by ring
    simp_rw [he]
    rw [boolExpect_add, boolExpect_const, ih, varSum_succ]

 theorem bernoulli_fourth {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) :
    boolExpect q (fun b => (centeredSum q b)^4) ≤ 3*(varSum q)^2+varSum q := by
  induction n with
  | zero => simp [boolExpect, centeredSum, varSum]
  | succ n ih =>
    let q' : Fin n → ℝ := fun t => q t.castSucc
    let p := q (Fin.last n)
    let w := p*(1-p)
    have hw : 0 ≤ w := mul_nonneg (hq (Fin.last n)).1 (sub_nonneg.mpr (hq (Fin.last n)).2)
    have hv := varSum_nonneg q' (fun t => hq t.castSucc)
    have hi := ih q' (fun t => hq t.castSucc)
    rw [boolExpect_snoc]
    simp only [centeredSum_snoc, Bool.false_eq_true, if_false, if_true]
    have he (b : Fin n → Bool) :
        (1-q (Fin.last n))*(centeredSum q' b+0-q (Fin.last n))^4 +
          q (Fin.last n)*(centeredSum q' b+1-q (Fin.last n))^4 =
        (centeredSum q' b)^4 + 6*w*(centeredSum q' b)^2 +
          (4*w*(1-2*p))*(centeredSum q' b) + w*(1-3*w) := by
      dsimp [p,w]
      ring
    change boolExpect q' (fun b =>
      (1-q (Fin.last n))*(centeredSum q' b+0-q (Fin.last n))^4 +
      q (Fin.last n)*(centeredSum q' b+1-q (Fin.last n))^4) ≤ _
    simp_rw [he]
    rw [boolExpect_add, boolExpect_add, boolExpect_add, boolExpect_mul,
      boolExpect_mul, bernoulli_mean_zero, bernoulli_second, boolExpect_const, varSum_succ]
    change _ ≤ 3*(varSum q'+w)^2+(varSum q'+w)
    nlinarith [sq_nonneg w]

 theorem bernoulli_positive_part {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) :
    Real.sqrt (varSum q) ≤
      16*(boolExpect q (fun b => max 0 (centeredSum q b))+1) := by
  let v := varSum q
  have hv : 0 ≤ v := varSum_nonneg q hq
  have hp : 0 ≤ boolExpect q (fun b => max 0 (centeredSum q b)) :=
    boolExpect_nonneg q hq _ (fun _ => le_max_left _ _)
  by_cases hv1 : 1 ≤ v
  · have hpos : 0 < v := lt_of_lt_of_le zero_lt_one hv1
    have hs := Real.sqrt_nonneg v
    have hs2 := Real.sq_sqrt hv
    have hspos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hpos
    have hpoint (z : ℝ) : z^2 ≤ 4*Real.sqrt v*|z| + z^4/(16*v) := by
      have hfour : 0 ≤ z^4/(16*v) := by positivity
      by_cases hz : |z| ≤ 4*Real.sqrt v
      · have hh := mul_le_mul_of_nonneg_right hz (abs_nonneg z)
        nlinarith [sq_abs z]
      · have hsq : 16*v ≤ z^2 := by
          have hza : 4*Real.sqrt v ≤ |z| := (lt_of_not_ge hz).le
          have hh := mul_self_le_mul_self (by positivity : 0 ≤ 4*Real.sqrt v) hza
          nlinarith [sq_abs z]
        have hdiv : z^2 ≤ z^4/(16*v) := by
          apply (le_div_iff₀ (by positivity : 0 < 16*v)).mpr
          have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg z)
          nlinarith [sq_nonneg (z^2)]
        have hnon : 0 ≤ 4*Real.sqrt v*|z| := by positivity
        linarith
    have he := boolExpect_mono q hq (fun b => hpoint (centeredSum q b))
    have heq (b : Fin n → Bool) :
        4*Real.sqrt v*|centeredSum q b|+(centeredSum q b)^4/(16*v) =
        (4*Real.sqrt v)*|centeredSum q b| + (1/(16*v))*(centeredSum q b)^4 := by ring
    simp_rw [heq] at he
    rw [bernoulli_second, boolExpect_add, boolExpect_mul, boolExpect_mul] at he
    have hfour := bernoulli_fourth q hq
    have hf : boolExpect q (fun b => (centeredSum q b)^4) ≤ 4*v^2 := by
      change _ ≤ 4*(varSum q)^2
      nlinarith [sq_nonneg (v-1)]
    have hm := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 1/(16*v))
    have hcancel : (1/(16*v))*(4*v^2) = v/4 := by field_simp [ne_of_gt hpos]; ring
    rw [hcancel] at hm
    have habs : boolExpect q (fun b => |centeredSum q b|) =
        2*boolExpect q (fun b => max 0 (centeredSum q b)) := by
      have hz (z : ℝ) : |z| = 2*max 0 z-z := by
        by_cases h : 0 ≤ z
        · rw [abs_of_nonneg h,max_eq_right h]; ring
        · rw [abs_of_nonpos (le_of_not_ge h),max_eq_left (le_of_not_ge h)]; ring
      simp_rw [hz]
      rw [boolExpect_sub, boolExpect_mul, bernoulli_mean_zero, sub_zero]
    rw [habs] at he
    have hh : Real.sqrt v ≤ 16*boolExpect q (fun b => max 0 (centeredSum q b)) := by
      nlinarith
    change Real.sqrt v ≤ _
    linarith
  · have hs : Real.sqrt v ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by nlinarith⟩
    change Real.sqrt v ≤ _
    linarith

end MultiSecretaryProof

noncomputable section
open MultiSecretary.NonAdaptive Finset
namespace MultiSecretaryProof

def selectedType {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (k : ℕ) (j : Fin m) : ℝ := ∑ t, liveProb f p k t * f j * p j t

theorem pe_sub {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (H G : (Fin n → Fin m × Bool) → ℝ) :
    pairExpect f p (fun ω => H ω - G ω) = pairExpect f p H - pairExpect f p G := by
  simp [pairExpect, mul_sub, sum_sub_distrib]

theorem pe_sum {m n : ℕ} {ι : Type*} [Fintype ι]
    (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (H : ι → (Fin n → Fin m × Bool) → ℝ) :
    pairExpect f p (fun ω => ∑ i, H i ω) = ∑ i, pairExpect f p (H i) := by
  simp only [pairExpect, mul_sum]
  exact sum_comm

theorem pe_const_mul {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (c : ℝ) (H : (Fin n → Fin m × Bool) → ℝ) :
    pairExpect f p (fun ω => c * H ω) = c * pairExpect f p H := by
  simp [pairExpect, mul_sum, mul_left_comm]

theorem pe_const {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (hf : IsMasses f) (hp : IsNAPolicy p) (c : ℝ) :
    pairExpect f p (fun _ => c) = c := by
  simpa using (pe_const_mul f p c (fun _ => 1)).trans (by rw [pairExpect_one f p hf hp, mul_one])

theorem pe_mono {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (hf : IsMasses f) (hp : IsNAPolicy p)
    (H G : (Fin n → Fin m × Bool) → ℝ) (h : ∀ ω : Fin n → Fin m × Bool, H ω ≤ G ω) :
    pairExpect f p H ≤ pairExpect f p G := by
  have hh := pairExpect_nonneg f p hf hp (fun ω => G ω - H ω)
    (fun ω => sub_nonneg.mpr (h ω))
  rw [pe_sub] at hh
  linarith

theorem pairExpect_loss {m n : ℕ} (a f : Fin m → ℝ) (k : ℕ)
    (p : Fin m → Fin n → ℝ) (hp : IsNAPolicy p) :
    pairExpect f p (fun ω => offMax a k (fun t => (ω t).1) -
      ∑ t ∈ selectedSet k ω, a (ω t).1) = regret a f k p := by
  rw [pe_sub, pairExpect_ability f p hp]
  unfold regret Voff Vna pairExpect
  congr 1
  apply sum_congr rfl
  intro ω _
  congr 1
  simp [selectedSet, sum_filter]

theorem regret_nonneg {m n : ℕ} (a f : Fin m → ℝ) (hf : IsMasses f)
    (k : ℕ) (p : Fin m → Fin n → ℝ) (hp : IsNAPolicy p) :
    0 ≤ regret a f k p := by
  classical
  have h := pairExpect_nonneg f p hf hp
    (fun ω => offMax a k (fun t => (ω t).1) - ∑ t ∈ selectedSet k ω, a (ω t).1)
    (fun ω => sub_nonneg.mpr (offMax_ge_sum a k _ _ ((selectedSet_card k ω).trans_le (Nat.min_le_right _ _))))
  rw [pairExpect_loss a f k p hp] at h
  exact h


theorem mass_bounds {m : ℕ} [NeZero m] (f : Fin m → ℝ) (hf : IsMasses f)
    (ε : ℝ) (heps : eps f = ε) (j : Fin m) : 2 * ε ≤ f j ∧ f j ≤ 1 := by
  have hm := inf'_le f (mem_univ j)
  have hs := single_le_sum (fun i _ => (hf.1 i).le) (mem_univ j)
  rw [hf.2] at hs
  unfold eps at heps
  constructor <;> linarith

theorem live_bounds {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (hf : IsMasses f) (hp : IsNAPolicy p) (k : ℕ) (t : Fin n) :
    0 ≤ liveProb f p k t ∧ liveProb f p k t ≤ 1 := by
  classical
  constructor
  · exact pairExpect_nonneg f p hf hp _ (fun ω => by split_ifs <;> norm_num)
  · calc
      _ ≤ pairExpect f p (fun _ => 1) := pe_mono f p hf hp _ _ (fun ω => by split_ifs <;> norm_num)
      _ = 1 := pairExpect_one f p hf hp

theorem selected_indicator_mean {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (hf : IsMasses f) (hp : IsNAPolicy p) (k : ℕ) (j : Fin m) (t : Fin n) :
    pairExpect f p (fun ω => if selected k ω t = true ∧ (ω t).1 = j then 1 else 0) =
      liveProb f p k t * f j * p j t := by
  classical
  let H : (Fin n → Fin m × Bool) → ℝ := fun ω =>
    if (univ.filter (fun s : Fin n => s < t ∧ (ω s).2 = true)).card < k then 1 else 0
  let G : Fin m × Bool → ℝ := fun z => if z.1 = j ∧ z.2 = true then 1 else 0
  have hH : ∀ ω z, H (Function.update ω t z) = H ω := by
    intro ω z
    have he : (univ.filter (fun s : Fin n => s < t ∧ (Function.update ω t z s).2 = true)) =
        univ.filter (fun s : Fin n => s < t ∧ (ω s).2 = true) := by
      ext s
      by_cases hst : s < t
      · simp [hst, Function.update_of_ne (ne_of_lt hst)]
      · simp [hst]
    dsimp [H]
    rw [he]
  have hfct := pairExpect_factor f p hf hp t H G hH
  have he : (fun ω => if selected k ω t = true ∧ (ω t).1 = j then (1 : ℝ) else 0) =
      (fun ω => H ω * G (ω t)) := by
    funext ω
    simp only [selected, Bool.and_eq_true, H, G]
    split_ifs <;> simp_all
  rw [he, hfct]
  change liveProb f p k t * _ = _
  rw [Fintype.sum_prod_type]
  simp [G, mul_assoc]

theorem selected_type_mean {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (hf : IsMasses f) (hp : IsNAPolicy p) (k : ℕ) (j : Fin m) :
    pairExpect f p (fun ω => ((selectedSet k ω).filter (fun t => (ω t).1 = j)).card) =
      selectedType f p k j := by
  classical
  have he : (fun ω => (((selectedSet k ω).filter (fun t => (ω t).1 = j)).card : ℝ)) =
      (fun ω => ∑ t : Fin n, if selected k ω t = true ∧ (ω t).1 = j then (1 : ℝ) else 0) := by
    funext ω
    simp [selectedSet, filter_filter, sum_boole]
  rw [he, pe_sum]
  exact sum_congr rfl (fun t _ => selected_indicator_mean f p hf hp k j t)

theorem selected_count_mean {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (hf : IsMasses f) (hp : IsNAPolicy p) (k : ℕ) :
    pairExpect f p (fun ω => ((selectedSet k ω).card : ℝ)) =
      ∑ t, liveProb f p k t * selProb f p t := by
  classical
  have he : ∀ ω : Fin n → Fin m × Bool, ((selectedSet k ω).card : ℝ) =
      ∑ j : Fin m, (((selectedSet k ω).filter (fun t => (ω t).1 = j)).card : ℝ) := by
    intro ω
    rw [← Nat.cast_sum]
    congr 1
    symm
    simpa using sum_card_fiberwise_eq_card_filter (selectedSet k ω) univ (fun t => (ω t).1)
  simp_rw [he]
  rw [pe_sum]
  simp_rw [selected_type_mean f p hf hp k]
  unfold selectedType selProb
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  ring

theorem be_mono {n : ℕ} (q : Fin n → ℝ) (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1)
    (H G : (Fin n → Bool) → ℝ) (h : ∀ b, H b ≤ G b) :
    boolExpect q H ≤ boolExpect q G := by
  have hh := boolExpect_nonneg q hq (fun b => G b - H b) (fun b => sub_nonneg.mpr (h b))
  simp only [boolExpect, mul_sub, sum_sub_distrib] at hh ⊢
  linarith

theorem bernoulli_cutoff {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) (c z : ℝ) (hc : 0 < c)
    (hz : (∑ t, q t) + c ≤ z) :
    boolExpect q (fun b => max 0 ((coinCount b : ℝ) - z)) ≤ varSum q / c := by
  have hh : ∀ b, max 0 ((coinCount b : ℝ) - z) ≤ (centeredSum q b)^2 / c := by
    intro b
    rw [centeredSum_eq]
    apply max_le
    · positivity
    · apply (le_div_iff₀ hc).mpr
      nlinarith [sq_nonneg ((coinCount b : ℝ) - ∑ t, q t - c / 2)]
  have hm := be_mono q hq _ _ hh
  have he : boolExpect q (fun b => (centeredSum q b)^2 / c) = varSum q / c := by
    simp only [boolExpect, ← mul_div_assoc, ← sum_div]
    exact congrArg (fun r : ℝ => r / c) (bernoulli_second q)
  exact hm.trans_eq he

theorem bernoulli_cutoff_reverse {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) (c z : ℝ) (hc : 0 < c)
    (hz : z + c ≤ ∑ t, q t) :
    boolExpect q (fun b => max 0 (z - (coinCount b : ℝ))) ≤ varSum q / c := by
  have hh : ∀ b, max 0 (z - (coinCount b : ℝ)) ≤ (centeredSum q b)^2 / c := by
    intro b
    rw [centeredSum_eq]
    apply max_le
    · positivity
    · apply (le_div_iff₀ hc).mpr
      nlinarith [sq_nonneg ((coinCount b : ℝ) - ∑ t, q t + c / 2)]
  have hm := be_mono q hq _ _ hh
  have he : boolExpect q (fun b => (centeredSum q b)^2 / c) = varSum q / c := by
    simp only [boolExpect, ← mul_div_assoc, ← sum_div]
    exact congrArg (fun r : ℝ => r / c) (bernoulli_second q)
  exact hm.trans_eq he

def typeSet {m n : ℕ} (x : Fin n → Fin m) (j : Fin m) : Finset (Fin n) :=
  univ.filter (fun t => x t = j)

theorem type_count_mean {m n : ℕ} (f : Fin m → ℝ) (hf : IsMasses f) (j : Fin m) :
    expect f (fun x : Fin n → Fin m => ((typeSet x j).card : ℝ)) = n * f j := by
  classical
  have he : (fun x : Fin n → Fin m => ((typeSet x j).card : ℝ)) =
      (fun x : Fin n → Fin m => (coinCount (fun t => decide (x t = j)) : ℝ)) := by
    funext x
    simp [typeSet, coinCount]
  rw [he, expect_indicator_law f hf j (fun b : Fin n → Bool => (coinCount b : ℝ)), boolExpect_count]
  simp

theorem top_pathwise {m n : ℕ} [NeZero m] (a : Fin m → ℝ) (g : ℝ)
    (hg : 0 < g) (hgap : separatedValues g a) (k : ℕ)
    (x : Fin n → Fin m) (S : Finset (Fin n)) (hS : S.card ≤ k) :
    g * (((typeSet x 0).card : ℝ) - ((S.filter (fun t => x t = 0)).card : ℝ) -
      max 0 (((typeSet x 0).card : ℝ) - k)) ≤ offMax a k x - ∑ t ∈ S, a (x t) := by
  classical
  have hu : ∀ t ∈ typeSet x 0, (a 0 - g) + g ≤ a (x t) := by
    intro t ht
    have hh : x t = 0 := (mem_filter.mp ht).2
    simp [hh]
  have hl : ∀ t ∉ typeSet x 0, a (x t) ≤ a 0 - g := by
    intro t ht
    have hx : x t ≠ 0 := by simpa [typeSet] using ht
    have hh := hgap.2 0 (x t) ((Fin.pos_iff_ne_zero' _).mpr hx)
    linarith
  have hh := threshold_gap_real a k x (typeSet x 0) S g (a 0 - g)
    hg.le (sub_nonneg.mpr (hgap.1 0)) hS hu hl
  have he : S ∩ typeSet x 0 = S.filter (fun t => x t = 0) := by ext t; simp [typeSet]
  rw [he] at hh
  have hid : min (k : ℝ) ((typeSet x 0).card : ℝ) =
      ((typeSet x 0).card : ℝ) - max 0 (((typeSet x 0).card : ℝ) - k) := by
    rcases le_total (k : ℝ) ((typeSet x 0).card : ℝ) with h | h
    · rw [min_eq_left h, max_eq_right (sub_nonneg.mpr h)]; ring
    · rw [min_eq_right h, max_eq_left (sub_nonpos.mpr h)]; ring
  rw [hid] at hh
  convert hh using 1
  ring

theorem bottom_pathwise {m n : ℕ} [NeZero m] (a : Fin m → ℝ) (g : ℝ)
    (hg : 0 < g) (hgap : separatedValues g a) (k : ℕ)
    (x : Fin n → Fin m) (S : Finset (Fin n)) (hS : S.card ≤ k) :
    g * (((S.filter (fun t => x t = Fin.rev 0)).card : ℝ) -
      max 0 ((k : ℝ) - (n - ((typeSet x (Fin.rev 0)).card : ℝ)))) ≤
      offMax a k x - ∑ t ∈ S, a (x t) := by
  classical
  let U := univ.filter (fun t : Fin n => x t ≠ Fin.rev 0)
  have hu : ∀ t ∈ U, a (Fin.rev 0) + g ≤ a (x t) := by
    intro t ht
    have hx : x t ≠ Fin.rev 0 := (mem_filter.mp ht).2
    have hh := hgap.2 (x t) (Fin.rev 0) (lt_of_le_of_ne (show x t ≤ Fin.rev 0 by
      rw [Fin.le_iff_val_le_val]
      simp only [Fin.val_rev, Fin.val_zero]
      omega) hx)
    linarith
  have hl : ∀ t ∉ U, a (x t) ≤ a (Fin.rev 0) := by
    intro t ht
    have hx : x t = Fin.rev 0 := by simpa [U] using ht
    simp [hx]
  have hh := threshold_gap_real a k x U S g (a (Fin.rev 0)) hg.le
    ((hg.le).trans (hgap.1 _)) hS hu hl
  have hcu : U.card + (typeSet x (Fin.rev 0)).card = n := by
    simpa [U, typeSet, add_comm] using (card_filter_add_card_filter_not
      (s := (univ : Finset (Fin n))) (fun t => x t = Fin.rev 0))
  have hcs : (S ∩ U).card + (S.filter (fun t => x t = Fin.rev 0)).card = S.card := by
    have he : S ∩ U = S.filter (fun t => x t ≠ Fin.rev 0) := by ext t; simp [U]
    rw [he]
    simpa [add_comm] using card_filter_add_card_filter_not (s := S) (fun t => x t = Fin.rev 0)
  have hcuR : (U.card : ℝ) + (typeSet x (Fin.rev 0)).card = n := by exact_mod_cast hcu
  have hcsR : ((S ∩ U).card : ℝ) + (S.filter (fun t => x t = Fin.rev 0)).card = S.card := by exact_mod_cast hcs
  have hSR : (S.card : ℝ) ≤ k := by exact_mod_cast hS
  have hm : ((S.filter (fun t => x t = Fin.rev 0)).card : ℝ) -
      max 0 ((k : ℝ) - (n - ((typeSet x (Fin.rev 0)).card : ℝ))) ≤
      min (k : ℝ) (U.card : ℝ) - ((S ∩ U).card : ℝ) := by
    rcases le_total (k : ℝ) (U.card : ℝ) with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]
      linarith
    · rw [min_eq_right h, max_eq_right (by linarith)]
      linarith
  exact (mul_le_mul_of_nonneg_left hm hg.le).trans hh

theorem type_tail {m n : ℕ} (f : Fin m → ℝ) (hf : IsMasses f)
    (j : Fin m) (ε : ℝ) (hε : 0 < ε) (hn : 0 < n) (z : ℝ)
    (hz : (f j + ε) * n ≤ z) :
    expect f (fun x : Fin n → Fin m => max 0 (((typeSet x j).card : ℝ) - z)) ≤ 1 / (4 * ε) := by
  classical
  have hp0 := (hf.1 j).le
  have hp1 : f j ≤ 1 := by simpa [hf.2] using single_le_sum (fun i _ => (hf.1 i).le) (mem_univ j)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (fun x : Fin n → Fin m => max 0 (((typeSet x j).card : ℝ) - z)) =
      (fun x : Fin n → Fin m => max 0 ((coinCount (fun t => decide (x t = j)) : ℝ) - z)) := by
    funext x; simp [coinCount, typeSet]
  rw [he, expect_indicator_law f hf j (fun b : Fin n → Bool => max 0 ((coinCount b : ℝ) - z))]
  have hh := bernoulli_cutoff (fun _ : Fin n => f j) (fun _ => ⟨hp0,hp1⟩)
    (ε * n) z (mul_pos hε hnr) (by simpa [mul_add, add_mul, mul_comm] using hz)
  have hv : varSum (fun _ : Fin n => f j) ≤ n / 4 := by
    simp only [varSum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hq : f j * (1 - f j) ≤ 1 / 4 := by nlinarith [sq_nonneg (f j - 1 / 2)]
    nlinarith
  refine hh.trans ?_
  apply (div_le_iff₀ (mul_pos hε hnr)).mpr
  have heq : 1 / (4 * ε) * (ε * n) = (n : ℝ) / 4 := by field_simp [hε.ne']
  rw [heq]
  exact hv

theorem expected_loss_div {m n : ℕ} (a f : Fin m → ℝ) (k : ℕ)
    (p : Fin m → Fin n → ℝ) (hp : IsNAPolicy p) (g : ℝ) :
    pairExpect f p (fun ω => (offMax a k (fun t => (ω t).1) -
      ∑ t ∈ selectedSet k ω, a (ω t).1) / g) = regret a f k p / g := by
  change (∑ ω, _ * (_ / g)) = _
  simp only [← mul_div_assoc, ← sum_div]
  exact congrArg (fun z : ℝ => z / g) (pairExpect_loss a f k p hp)

theorem pe_add {m n : ℕ} (f : Fin m → ℝ) (p : Fin m → Fin n → ℝ)
    (H G : (Fin n → Fin m × Bool) → ℝ) :
    pairExpect f p (fun ω => H ω + G ω) = pairExpect f p H + pairExpect f p G := by
  simp [pairExpect, mul_add, sum_add_distrib]

theorem top_bottom_controls {m n : ℕ} [NeZero m]
    (a f : Fin m → ℝ) (g ε : ℝ) (hg : 0 < g) (hgap : separatedValues g a)
    (hf : IsMasses f) (hε : 0 < ε)
    (k : ℕ) (hn : 0 < n) (hklo : (f 0 + ε) * n ≤ k)
    (hkhi : (k : ℝ) ≤ (1 - f (Fin.rev 0) - ε) * n)
    (p : Fin m → Fin n → ℝ) (hp : IsNAPolicy p) :
    n * f 0 - selectedType f p k 0 ≤ regret a f k p / g + 1 / (4 * ε) ∧
    selectedType f p k (Fin.rev 0) ≤ regret a f k p / g + 1 / (4 * ε) := by
  classical
  have hfeas : ∀ ω : Fin n → Fin m × Bool, (selectedSet k ω).card ≤ k := fun ω =>
    (selectedSet_card k ω).trans_le (Nat.min_le_right _ _)
  constructor
  · have hpoint : ∀ ω : Fin n → Fin m × Bool, ((typeSet (fun t => (ω t).1) 0).card : ℝ) -
        (((selectedSet k ω).filter (fun t => (ω t).1 = 0)).card : ℝ) ≤
        (offMax a k (fun t => (ω t).1) - ∑ t ∈ selectedSet k ω, a (ω t).1) / g +
          max 0 (((typeSet (fun t => (ω t).1) 0).card : ℝ) - k) := by
      intro ω
      have hh := top_pathwise a g hg hgap k (fun t => (ω t).1) (selectedSet k ω) (hfeas ω)
      have hd := (le_div_iff₀ hg).mpr (by simpa only [mul_comm] using hh)
      nlinarith only [hd]
    have hh := pe_mono f p hf hp _ _ hpoint
    rw [pe_sub, pairExpect_ability f p hp (fun x : Fin n → Fin m => ((typeSet x 0).card : ℝ)), type_count_mean f hf 0,
      selected_type_mean f p hf hp k 0, pe_add, expected_loss_div a f k p hp g,
      pairExpect_ability f p hp (fun x : Fin n → Fin m => max 0 (((typeSet x 0).card : ℝ) - k))] at hh
    exact hh.trans (add_le_add_right (type_tail f hf 0 ε hε hn k hklo) _)
  · have hpoint : ∀ ω : Fin n → Fin m × Bool,
        (((selectedSet k ω).filter (fun t => (ω t).1 = Fin.rev 0)).card : ℝ) ≤
        (offMax a k (fun t => (ω t).1) - ∑ t ∈ selectedSet k ω, a (ω t).1) / g +
          max 0 (((typeSet (fun t => (ω t).1) (Fin.rev 0)).card : ℝ) - (n - k)) := by
      intro ω
      have hh := bottom_pathwise a g hg hgap k (fun t => (ω t).1) (selectedSet k ω) (hfeas ω)
      have hd := (le_div_iff₀ hg).mpr (by simpa only [mul_comm] using hh)
      have he : (k : ℝ) - (n - ((typeSet (fun t => (ω t).1) (Fin.rev 0)).card : ℝ)) =
          ((typeSet (fun t => (ω t).1) (Fin.rev 0)).card : ℝ) - (n - k) := by ring
      rw [he] at hd
      nlinarith only [hd]
    have hh := pe_mono f p hf hp _ _ hpoint
    rw [selected_type_mean f p hf hp k (Fin.rev 0), pe_add,
      expected_loss_div a f k p hp g, pairExpect_ability f p hp (fun x : Fin n → Fin m => max 0 (((typeSet x (Fin.rev 0)).card : ℝ) - (n - k)))] at hh
    exact hh.trans (add_le_add_right (type_tail f hf (Fin.rev 0) ε hε hn ((n : ℝ) - k) (by nlinarith only [hkhi])) _)

theorem unused_expectation {m n : ℕ} (a f : Fin m → ℝ) (g : ℝ)
    (hg : 0 < g) (hgap : separatedValues g a) (hf : IsMasses f)
    (k : ℕ) (hkn : k ≤ n) (p : Fin m → Fin n → ℝ) (hp : IsNAPolicy p) :
    boolExpect (selProb f p) (fun b => max 0 ((k : ℝ) - coinCount b)) ≤ regret a f k p / g := by
  classical
  have hpoint : ∀ ω : Fin n → Fin m × Bool, max 0 ((k : ℝ) - coinCount (fun t => (ω t).2)) ≤
      (offMax a k (fun t => (ω t).1) - ∑ t ∈ selectedSet k ω, a (ω t).1) / g := by
    intro ω
    have hS : (selectedSet k ω).card ≤ k := (selectedSet_card k ω).trans_le (Nat.min_le_right _ _)
    have hh := unused_gap a k (fun t => (ω t).1) (selectedSet k ω) g hgap.1 hS hkn
    rw [Nat.cast_sub hS, selectedSet_card, Nat.cast_min] at hh
    have he : (k : ℝ) - min (coinCount (fun t => (ω t).2) : ℝ) k =
        max 0 ((k : ℝ) - coinCount (fun t => (ω t).2)) := by
      rcases le_total (coinCount (fun t => (ω t).2) : ℝ) k with h | h
      · rw [min_eq_left h, max_eq_right (sub_nonneg.mpr h)]
      · rw [min_eq_right h, max_eq_left (sub_nonpos.mpr h)]; ring
    rw [he] at hh
    exact (le_div_iff₀ hg).mpr (by nlinarith only [hh])
  have hh := pe_mono f p hf hp _ _ hpoint
  rw [pairExpect_coin f p hf (fun b : Fin n → Bool => max 0 ((k : ℝ) - coinCount b)), expected_loss_div a f k p hp g] at hh
  exact hh

theorem overshoot_blocked {m n : ℕ} (f : Fin m → ℝ) (hf : IsMasses f)
    (k : ℕ) (p : Fin m → Fin n → ℝ) (hp : IsNAPolicy p) :
    boolExpect (selProb f p) (fun b => max 0 ((coinCount b : ℝ) - k)) ≤ blocked f p k := by
  classical
  have hpoint : ∀ ω : Fin n → Fin m × Bool, max 0 ((coinCount (fun t => (ω t).2) : ℝ) - k) =
      (coinCount (fun t => (ω t).2) : ℝ) - (selectedSet k ω).card := by
    intro ω
    rw [selectedSet_card, Nat.cast_min]
    rcases le_total (coinCount (fun t => (ω t).2) : ℝ) k with h | h
    · rw [min_eq_left h, max_eq_left (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, max_eq_right (sub_nonneg.mpr h)]
  have he : boolExpect (selProb f p) (fun b => max 0 ((coinCount b : ℝ) - k)) =
      ∑ t, (1 - liveProb f p k t) * selProb f p t := by
    rw [← pairExpect_coin f p hf]
    simp_rw [hpoint]
    rw [pe_sub, pairExpect_coin f p hf (fun b : Fin n → Bool => (coinCount b : ℝ)), boolExpect_count, selected_count_mean f p hf hp k]
    simp [sub_mul, sum_sub_distrib]
  rw [he]
  apply sum_le_sum
  intro t _
  have hr := live_bounds f p hf hp k t
  have hq := selProb_bounds f p hf hp t
  nlinarith

theorem mean_deviation {m n : ℕ} (a f : Fin m → ℝ) (g : ℝ)
    (hg : 0 < g) (hgap : separatedValues g a) (hf : IsMasses f)
    (k : ℕ) (hkn : k ≤ n) (p : Fin m → Fin n → ℝ) (hp : IsNAPolicy p) :
    |(∑ t, selProb f p t) - k| ≤ blocked f p k + regret a f k p / g := by
  have hu := unused_expectation a f g hg hgap hf k hkn p hp
  have ho := overshoot_blocked f hf k p hp
  have h0 := boolExpect_nonneg (selProb f p) (selProb_bounds f p hf hp)
    (fun b => max 0 ((coinCount b : ℝ) - k)) (fun b => le_max_left _ _)
  have h1 := boolExpect_nonneg (selProb f p) (selProb_bounds f p hf hp)
    (fun b => max 0 ((k : ℝ) - coinCount b)) (fun b => le_max_left _ _)
  have he : (∑ t, selProb f p t) - k =
      boolExpect (selProb f p) (fun b => max 0 ((coinCount b : ℝ) - k)) -
      boolExpect (selProb f p) (fun b => max 0 ((k : ℝ) - coinCount b)) := by
    have hpw : ∀ b : Fin n → Bool, (coinCount b : ℝ) - k =
        max 0 ((coinCount b : ℝ) - k) - max 0 ((k : ℝ) - coinCount b) := by
      intro b
      rcases le_total (coinCount b : ℝ) k with h | h
      · rw [max_eq_left (sub_nonpos.mpr h), max_eq_right (sub_nonneg.mpr h)]; ring
      · rw [max_eq_right (sub_nonneg.mpr h), max_eq_left (sub_nonpos.mpr h)]; ring
    have hh := congrArg (boolExpect (selProb f p)) (funext hpw)
    simp only [boolExpect, mul_sub, sum_sub_distrib] at hh
    have hc : (∑ b : Fin n → Bool, bernWeight (selProb f p) b * (k : ℝ)) = k := by
      rw [← sum_mul]
      have hm := boolExpect_one (selProb f p)
      simpa [boolExpect] using congrArg (fun z : ℝ => z * k) hm
    rw [hc] at hh
    exact (congrArg (fun z : ℝ => z - k) (boolExpect_count (selProb f p))).symm.trans hh
  rw [he, abs_le]
  constructor <;> linarith

theorem regret_controls {m n : ℕ} [NeZero m] (hm : 3 ≤ m)
    (a f : Fin m → ℝ) (g ε : ℝ) (hg : 0 < g) (hgap : separatedValues g a)
    (hf : IsMasses f) (hε : 0 < ε) (heps : eps f = ε)
    (k : ℕ) (hn : 0 < n) (hklo : (f 0 + ε) * n ≤ k)
    (hkhi : (k : ℝ) ≤ (1 - f (Fin.rev 0) - ε) * n)
    (p : Fin m → Fin n → ℝ) (hp : IsNAPolicy p) :
    blocked f p k ≤ (regret a f k p / g + 1 / (4 * ε)) / (2 * ε) ∧
    |(∑ t, selProb f p t) - k| ≤ blocked f p k + regret a f k p / g ∧
    boolExpect (selProb f p) (fun b => max 0 ((coinCount b : ℝ) - k)) ≤ blocked f p k := by
  have _ := hm
  have hb := (top_bottom_controls a f g ε hg hgap hf hε k hn hklo hkhi p hp).1
  have hd0 : 0 ≤ blocked f p k := sum_nonneg (fun t _ => sub_nonneg.mpr (live_bounds f p hf hp k t).2)
  have ht : f 0 * blocked f p k ≤ n * f 0 - selectedType f p k 0 := by
    unfold blocked selectedType
    rw [mul_sum]
    have he : (n : ℝ) * f 0 = ∑ _t : Fin n, f 0 := by simp
    rw [he, ← sum_sub_distrib]
    apply sum_le_sum
    intro t _
    have hr := live_bounds f p hf hp k t
    have hpt := hp 0 t
    have hft := (hf.1 0).le
    nlinarith [mul_nonneg hr.1 hft, mul_nonneg (mul_nonneg hr.1 hft) (sub_nonneg.mpr hpt.2)]
  have hmass := (mass_bounds f hf ε heps 0).1
  have hD : blocked f p k ≤ (regret a f k p / g + 1 / (4 * ε)) / (2 * ε) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ε)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hmass) hd0]
  have hkn : k ≤ n := by
    have hnr : (0 : ℝ) ≤ n := by positivity
    have hfb := hf.1 (Fin.rev 0)
    have hh : (k : ℝ) ≤ n := by nlinarith [mul_nonneg (by linarith : 0 ≤ f (Fin.rev 0) + ε) hnr]
    exact_mod_cast hh
  exact ⟨hD, mean_deviation a f g hg hgap hf k hkn p hp, overshoot_blocked f hf k p hp⟩

end MultiSecretaryProof

noncomputable section
open MultiSecretary.NonAdaptive Finset
namespace MultiSecretaryProof

theorem variance_control {m n : ℕ} [NeZero m] (hm : 3 ≤ m)
    (a f : Fin m → ℝ) (g ε : ℝ) (hg : 0 < g) (hgap : separatedValues g a)
    (hf : IsMasses f) (hε : 0 < ε) (heps : eps f = ε)
    (k : ℕ) (hn : 0 < n) (hklo : (f 0 + ε) * n ≤ k)
    (hkhi : (k : ℝ) ≤ (1 - f (Fin.rev 0) - ε) * n)
    (p : Fin m → Fin n → ℝ) (hp : IsNAPolicy p) :
    4 * ε ^ 2 * n - 2 * (regret a f k p / g + 1 / (4 * ε)) - blocked f p k
      ≤ varSum (selProb f p) := by
  have _ := hm
  let H := regret a f k p / g + 1 / (4 * ε)
  let A := ∑ t : Fin n, f 0 * (1 - p 0 t)
  let B := ∑ t : Fin n, f (Fin.rev 0) * p (Fin.rev 0) t
  have htb := top_bottom_controls a f g ε hg hgap hf hε k hn hklo hkhi p hp
  have hA : A ≤ H := by
    apply le_trans (b := (n : ℝ) * f 0 - selectedType f p k 0) ?_ htb.1
    unfold A selectedType
    have he : (n : ℝ) * f 0 = ∑ _t : Fin n, f 0 := by simp
    rw [he, ← sum_sub_distrib]
    apply sum_le_sum
    intro t _
    have hr := live_bounds f p hf hp k t
    have hpt := hp 0 t
    have hft := (hf.1 0).le
    nlinarith [mul_nonneg (sub_nonneg.mpr hr.2) (mul_nonneg hft hpt.1)]
  have hB : B ≤ H + blocked f p k := by
    apply le_trans (b := selectedType f p k (Fin.rev 0) + blocked f p k) ?_ (add_le_add_left htb.2 _)
    unfold B selectedType blocked
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro t _
    have hr := live_bounds f p hf hp k t
    have hpt := hp (Fin.rev 0) t
    have hfb := mass_bounds f hf ε heps (Fin.rev 0)
    have hfb0 := (hf.1 (Fin.rev 0)).le
    have hprod : f (Fin.rev 0) * p (Fin.rev 0) t ≤ 1 :=
      (mul_le_mul_of_nonneg_left hpt.2 hfb0).trans (by simpa using hfb.2)
    nlinarith [mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr hprod)]
  have hvariance : f 0 * f (Fin.rev 0) * n - f (Fin.rev 0) * A - f 0 * B ≤
      varSum (selProb f p) := by
    have he : f 0 * f (Fin.rev 0) * n = ∑ _t : Fin n, f 0 * f (Fin.rev 0) := by simp; ring
    rw [he]
    simp only [A, B, mul_sum, ← sum_sub_distrib, varSum]
    apply sum_le_sum
    intro t _
    have hq := selProb_bounds f p hf hp t
    have hqtop : f 0 * p 0 t ≤ selProb f p t := by
      unfold selProb
      simpa [mul_comm] using single_le_sum (fun j _ => mul_nonneg (hp j t).1 (hf.1 j).le) (mem_univ (0 : Fin m))
    have hqbot : f (Fin.rev 0) * (1 - p (Fin.rev 0) t) ≤ 1 - selProb f p t := by
      have heq : 1 - selProb f p t = ∑ j, f j * (1 - p j t) := by
        simp [selProb, mul_sub, sum_sub_distrib, hf.2, mul_comm]
      rw [heq]
      exact single_le_sum (fun j _ => mul_nonneg (hf.1 j).le (sub_nonneg.mpr (hp j t).2)) (mem_univ _)
    have hp1 := mul_le_mul hqtop hqbot
      (mul_nonneg (hf.1 _).le (sub_nonneg.mpr (hp _ t).2)) hq.1
    have hp2 := mul_nonneg (mul_nonneg (hf.1 0).le (hf.1 (Fin.rev 0)).le)
      (mul_nonneg (sub_nonneg.mpr (hp 0 t).2) (hp (Fin.rev 0) t).1)
    nlinarith only [hp1, hp2]
  have hf0 := mass_bounds f hf ε heps 0
  have hfb := mass_bounds f hf ε heps (Fin.rev 0)
  have hH : 0 ≤ H := by
    have hR := regret_nonneg a f hf k p hp
    dsimp [H]
    positivity
  have hD : 0 ≤ blocked f p k := sum_nonneg (fun t _ => sub_nonneg.mpr (live_bounds f p hf hp k t).2)
  have hlo : 4 * ε^2 ≤ f 0 * f (Fin.rev 0) := by
    have hh := mul_le_mul hf0.1 hfb.1 (by positivity : 0 ≤ 2 * ε) (hf.1 0).le
    nlinarith only [hh]
  have htop : f (Fin.rev 0) * A ≤ H :=
    (mul_le_mul_of_nonneg_left hA (hf.1 _).le).trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hfb.2) hH])
  have hbot : f 0 * B ≤ H + blocked f p k :=
    (mul_le_mul_of_nonneg_left hB (hf.1 0).le).trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hf0.2) (add_nonneg hH hD)])
  have htimes := mul_le_mul_of_nonneg_right hlo (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  change 4 * ε^2 * n - 2 * H - blocked f p k ≤ _
  linarith only [hvariance, htop, hbot, htimes]

end MultiSecretaryProof

noncomputable section
open MultiSecretary.NonAdaptive Finset
namespace MultiSecretaryProof

private theorem prefix_card {n k : ℕ} (hkn : k < n) :
    (univ.filter (fun t : Fin n => t.val < k)).card = k := by
  have he : univ.filter (fun t : Fin n => t.val < k) = Iio (⟨k,hkn⟩ : Fin n) := by
    ext t
    simp [Fin.lt_def]
  rw [he, Fin.card_Iio]

private theorem selected_false_of_prefix {m n k : ℕ} (hkn : k < n)
    (ω : Fin n → Fin m × Bool) (h : ∀ t : Fin n, t.val < k → (ω t).2 = true)
    (t : Fin n) (ht : k ≤ t.val) : selected k ω t = false := by
  have hs : univ.filter (fun s : Fin n => s.val < k) ⊆
      univ.filter (fun s : Fin n => s < t ∧ (ω s).2 = true) := by
    intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs ⊢
    exact ⟨by change s.val < t.val; omega, h s hs⟩
  have hc := card_le_card hs
  rw [prefix_card hkn] at hc
  simp [selected, not_lt.mpr hc]

 theorem small_horizon_regret {m n : ℕ} [NeZero m] (hm : 3 ≤ m)
    (a f : Fin m → ℝ) (g ε : ℝ) (hg : 0 < g)
    (hgap : separatedValues g a) (hf : IsMasses f) (hε : 0 < ε)
    (heps : eps f = ε) (k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (p : Fin m → Fin n → ℝ) (hp : IsNAPolicy p) :
    g * (2 * ε)^n ≤ regret a f k p := by
  classical
  let mid : Fin m := ⟨1, by omega⟩
  let bot : Fin m := ⟨m-1, by omega⟩
  let last : Fin n := ⟨n-1, by omega⟩
  let xA : Fin n → Fin m := fun t => if t.val < k-1 then 0 else if t.val = k-1 then mid else bot
  let xB : Fin n → Fin m := fun t => if t=last then 0 else xA t
  let WA : Finset (Fin n) := univ.filter (fun t => t.val < k)
  let WB : Finset (Fin n) := insert last (univ.filter (fun t => t.val < k-1))
  have hlast : k ≤ last.val := by dsimp [last]; omega
  have hAcard : WA.card = k := prefix_card hkn
  have hBcard : WB.card = k := by
    dsimp [WB]
    rw [card_insert_of_notMem (by simp; omega), prefix_card (by omega)]
    omega
  have hAB : xA ≠ xB := by
    intro h
    have hh := congrFun h last
    have hb : xA last = bot := by simp [xA, show ¬last.val < k-1 by omega, show last.val ≠ k-1 by omega]
    rw [hb] at hh
    have he : bot = 0 := by simpa [xB] using hh
    have := congrArg Fin.val he
    dsimp [bot] at this
    omega
  have hAp (t) (_ht : t ∈ WA) : g ≤ a (xA t) := hgap.1 _
  have hBp (t) (_ht : t ∈ WB) : g ≤ a (xB t) := hgap.1 _
  have hAs (t) (ht : t ∈ WA) (u) (hu : u ∉ WA) : g ≤ a (xA t)-a (xA u) := by
    have ht' : t.val < k := by simpa [WA] using ht
    have hu' : k ≤ u.val := by simpa [WA] using hu
    have hux : xA u = bot := by simp [xA, show ¬u.val < k-1 by omega, show u.val ≠ k-1 by omega]
    rw [hux]
    dsimp [xA]
    split_ifs
    · exact hgap.2 0 bot (by change 0 < m-1; omega)
    · exact hgap.2 mid bot (by change 1 < m-1; omega)
    · omega
  have hBs (t) (ht : t ∈ WB) (u) (hu : u ∉ WB) : g ≤ a (xB t)-a (xB u) := by
    have ht' : t=last ∨ t.val < k-1 := by simpa [WB] using ht
    have hu' : u≠last ∧ ¬u.val < k-1 := by simpa [WB] using hu
    have htx : xB t = 0 := by
      rcases ht' with h | h
      · simp [xB, h]
      · simp [xB, xA, h]
    rw [htx]
    simp only [xB, if_neg hu'.1, xA, if_neg hu'.2]
    split_ifs
    · exact hgap.2 0 mid (by change 0 < 1; omega)
    · exact hgap.2 0 bot (by change 0 < m-1; omega)
  let L : (Fin n → Fin m) → (Fin n → Bool) → ℝ := fun x b =>
    offMax a k x - ∑ t ∈ selectedSet k (fun i => (x i,b i)), a (x t)
  have hL (x : Fin n → Fin m) (b : Fin n → Bool) : 0 ≤ L x b := by
    apply sub_nonneg.mpr
    exact offMax_ge_sum a k x _ ((selectedSet_card k _).trans_le (Nat.min_le_right _ _))
  let E : (Fin n → Bool) → Prop := fun b => ∀ t : Fin n, t.val < k → b t=true
  have hLA (b : Fin n → Bool) : (if E b then 0 else g) ≤ L xA b := by
    split_ifs with he
    · exact hL xA b
    · apply separated_winner_gap a k xA WA _ g hg hAcard
        ((selectedSet_card k _).trans_le (Nat.min_le_right _ _)) _ hAp hAs
      intro hs
      apply he
      intro t ht
      have hmemb : t ∈ selectedSet k (fun i => (xA i,b i)) := by rw [hs]; simpa [WA] using ht
      have hh := (mem_filter.mp hmemb).2
      simp only [selected, Bool.and_eq_true] at hh
      exact hh.1
  have hLB (b : Fin n → Bool) : (if E b then g else 0) ≤ L xB b := by
    split_ifs with he
    · apply separated_winner_gap a k xB WB _ g hg hBcard
        ((selectedSet_card k _).trans_le (Nat.min_le_right _ _)) _ hBp hBs
      intro hs
      have hmem : last ∈ selectedSet k (fun i => (xB i,b i)) := by rw [hs]; simp [WB]
      have hc := (mem_filter.mp hmem).2
      have hn := selected_false_of_prefix hkn (fun i => (xB i,b i)) he last hlast
      rw [hn] at hc
      contradiction
    · exact hL xB b
  let qA : Fin n → ℝ := fun t => p (xA t) t
  let qB : Fin n → ℝ := fun t => p (xB t) t
  have hqA (t) : 0 ≤ qA t ∧ qA t ≤ 1 := hp _ t
  have hqB (t) : 0 ≤ qB t ∧ qB t ≤ 1 := hp _ t
  have hE : boolExpect qA (fun b => if E b then 1 else 0) =
      boolExpect qB (fun b => if E b then 1 else 0) := by
    rw [boolExpect_prefix_event, boolExpect_prefix_event]
    apply prod_congr rfl
    intro t _
    by_cases ht : t.val < k
    · have hn : t ≠ last := by intro he; subst t; omega
      simp [ht, qA, qB, xB, hn]
    · simp [ht]
  have hEA : boolExpect qA (fun b => if E b then 0 else g) =
      g * (1-boolExpect qA (fun b => if E b then 1 else 0)) := by
    have he : (fun b => if E b then (0:ℝ) else g) =
        (fun b => g*((1:ℝ)-(if E b then 1 else 0))) := by funext b; split_ifs <;> ring
    rw [he, boolExpect_mul, boolExpect_sub, boolExpect_const]
  have hEB : boolExpect qB (fun b => if E b then g else 0) =
      g * boolExpect qB (fun b => if E b then 1 else 0) := by
    have he : (fun b => if E b then g else (0:ℝ)) =
        (fun b => g*(if E b then 1 else 0)) := by funext b; split_ifs <;> ring
    rw [he, boolExpect_mul]
  have hsum : g ≤ boolExpect qA (L xA) + boolExpect qB (L xB) := by
    have ha := boolExpect_mono qA hqA hLA
    have hb := boolExpect_mono qB hqB hLB
    rw [hEA, hE] at ha
    rw [hEB] at hb
    linarith
  have hprob (x : Fin n → Fin m) : (2*ε)^n ≤ prob f x := by
    calc
      _ = ∏ _t : Fin n, 2*ε := by simp
      _ ≤ _ := prod_le_prod (fun _ _ => by positivity) (fun t _ => (mass_bounds f hf ε heps (x t)).1)
  have hpn (x : Fin n → Fin m) : 0 ≤ prob f x := prod_nonneg (fun t _ => (hf.1 _).le)
  have hLn (x : Fin n → Fin m) : 0 ≤ boolExpect (fun t => p (x t) t) (L x) :=
    boolExpect_nonneg _ (fun t => hp _ t) _ (hL x)
  have hreg : regret a f k p = ∑ x : Fin n → Fin m,
      prob f x * boolExpect (fun t => p (x t) t) (L x) := by
    rw [← pairExpect_loss a f k p hp, pairExpect_disintegrate]
  have htwo : prob f xA * boolExpect qA (L xA) + prob f xB * boolExpect qB (L xB) ≤ regret a f k p := by
    rw [hreg]
    have h := sum_le_sum_of_subset_of_nonneg (subset_univ ({xA,xB} : Finset (Fin n → Fin m)))
      (fun x _ _ => mul_nonneg (hpn x) (hLn x))
    simpa [hAB, qA, qB] using h
  have ha := mul_le_mul_of_nonneg_right (hprob xA) (hLn xA)
  have hb := mul_le_mul_of_nonneg_right (hprob xB) (hLn xB)
  have hh := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (2*ε)^n)
  dsimp [qA, qB] at htwo hsum ha hb hh
  nlinarith only [htwo, ha, hb, hh]

end MultiSecretaryProof

noncomputable section
open MultiSecretary.NonAdaptive Finset
namespace MultiSecretaryProof

 theorem uniform_policy_regret {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (a : Fin m → ℝ) (g ε : ℝ) (hg : 0 < g)
    (hgap : separatedValues g a) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : Fin m → ℝ, IsMasses f → eps f = ε →
      ∀ n k : ℕ, (f 0 + ε) * n ≤ k →
      (k : ℝ) ≤ (1 - f (Fin.rev 0) - ε) * n →
      ∀ p : Fin m → Fin n → ℝ, IsNAPolicy p →
      M * Real.sqrt n ≤ regret a f k p := by
  let C := 1/(4*ε)
  let H := 1/g+C
  let D := H/(2*ε)
  let A := 32*D+16/g+16
  let B := 2*H+D
  let Z := A^2+B+1
  let K := Z/(2*ε)
  have hC : 0 < C := by dsimp [C]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hZ : 1 < Z := by dsimp [Z]; nlinarith [sq_nonneg A]
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt ((2*K)^2+1)
  have hN0 : 0 < N := by exact_mod_cast (show (0:ℝ) < N by nlinarith [sq_nonneg (2*K)])
  let M := min (1/(2*K)) (g*(2*ε)^N/Real.sqrt N)
  have hM : 0 < M := by
    apply lt_min
    · positivity
    · exact div_pos (mul_pos hg (pow_pos (by positivity) N)) (Real.sqrt_pos.mpr (by exact_mod_cast hN0))
  refine ⟨M, hM, ?_⟩
  intro f hf heps n k hklo hkhi p hp
  have hR := regret_nonneg a f hf k p hp
  by_cases hn0 : n=0
  · subst n
    simpa using hR
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hk : 1 ≤ k := by
    have hh : (0:ℝ) < k := (mul_pos (add_pos (hf.1 0) hε) hnR).trans_le hklo
    exact_mod_cast hh
  have hkn : k < n := by
    have hh : (k:ℝ) < n := hkhi.trans_lt (by nlinarith [hf.1 (Fin.rev 0)])
    exact_mod_cast hh
  let R := regret a f k p
  let d := blocked f p k
  let q := selProb f p
  let v := varSum q
  have hq := selProb_bounds f p hf hp
  have hv0 : 0 ≤ v := varSum_nonneg q hq
  have hctrl := regret_controls hm a f g ε hg hgap hf hε heps k hn hklo hkhi p hp
  have hvar := variance_control hm a f g ε hg hgap hf hε heps k hn hklo hkhi p hp
  have hHC : R/g+C ≤ H*(R+1) := by
    dsimp [H]
    have hh := mul_nonneg hC.le hR
    change 0 ≤ C*R at hh
    simp only [div_eq_mul_inv]
    nlinarith only [hh, inv_nonneg.mpr hg.le]
  have hd : d ≤ D*(R+1) := by
    apply le_trans hctrl.1
    calc
      _ ≤ (H*(R+1))/(2*ε) := div_le_div_of_nonneg_right hHC (by positivity)
      _ = _ := by dsimp [D]; ring
  have hpos : boolExpect q (fun b => max 0 (centeredSum q b)) ≤ 2*d+R/g := by
    have hh := boolExpect_mono q hq (H := fun b => max 0 (centeredSum q b))
      (G := fun b => max 0 ((coinCount b:ℝ)-k)+|(∑ t,q t)-(k:ℝ)|) (by
        intro b
        apply max_le
        · positivity
        · rw [centeredSum_eq]
          have hx := le_max_right 0 ((coinCount b:ℝ)-k)
          have hy := neg_le_abs ((∑ t,q t)-(k:ℝ))
          linarith)
    rw [boolExpect_add, boolExpect_const] at hh
    change _ ≤ 2*blocked f p k+regret a f k p/g
    exact hh.trans (by linarith [hctrl.2.1, hctrl.2.2])
  have hs : Real.sqrt v ≤ A*(R+1) := by
    have hh := bernoulli_positive_part q hq
    have hi : R/g ≤ (R+1)/g := div_le_div_of_nonneg_right (by linarith) hg.le
    have hr1 : (1:ℝ) ≤ R+1 := by linarith
    have hz := mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 32)
    dsimp [A]
    simp only [div_eq_mul_inv] at hi hpos ⊢
    nlinarith only [hh, hpos, hi, hz, hr1]
  have hlow : 4*ε^2*n ≤ v+B*(R+1) := by
    change 4*ε^2*n-2*(R/g+C)-d ≤ v at hvar
    dsimp [B]
    nlinarith only [hvar, hHC, hd]
  have hlinear : Real.sqrt n ≤ K*(R+1) := by
    have hsqv := Real.sq_sqrt hv0
    have hs0 := Real.sqrt_nonneg v
    have hsq : v ≤ A^2*(R+1)^2 := by
      have hsq' := mul_self_le_mul_self hs0 hs
      nlinarith only [hsq', hsqv]
    have hb : B*(R+1) ≤ B*(R+1)^2 :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hR]) hB.le
    have hz : A^2+B ≤ Z^2 := by
      dsimp [Z]
      nlinarith only [sq_nonneg (A^2+B), hB, sq_nonneg A]
    have hzz := mul_le_mul_of_nonneg_right hz (sq_nonneg (R+1))
    have hsn := Real.sq_sqrt hnR.le
    have hsn2 := congrArg (fun z : ℝ => 4*ε^2*z) hsn
    have hprod : 0 ≤ Z*(R+1) := mul_nonneg (by linarith) (by linarith)
    have hbase : 2*ε*Real.sqrt n ≤ Z*(R+1) := by
      have heq : (2*ε*Real.sqrt n)^2 ≤ (Z*(R+1))^2 := by
        nlinarith only [hlow, hsq, hb, hzz, hsn2]
      have hleft : 0 ≤ 2*ε*Real.sqrt n := by positivity
      exact (sq_le_sq₀ hleft hprod).mp heq
    calc
      Real.sqrt n ≤ Z*(R+1)/(2*ε) := (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hbase])
      _ = K*(R+1) := by dsimp [K]; ring
  by_cases hlarge : N ≤ n
  · have hnn : (N:ℝ) ≤ n := by exact_mod_cast hlarge
    have hsn := Real.sq_sqrt hnR.le
    have hnon := Real.sqrt_nonneg (n:ℝ)
    have h2 : 2*K ≤ Real.sqrt n := by nlinarith only [hN, hnn, hsn, hnon, hK]
    have hhalf : Real.sqrt n/(2*K) ≤ R := by
      apply (div_le_iff₀ (show 0 < 2*K by positivity)).mpr
      nlinarith only [hlinear, h2, hK]
    calc
      M*Real.sqrt n ≤ (1/(2*K))*Real.sqrt n := mul_le_mul_of_nonneg_right (min_le_left _ _) hnon
      _ = Real.sqrt n/(2*K) := by ring
      _ ≤ R := hhalf
  · have hnN : n ≤ N := by omega
    have hp0 : 0 ≤ 2*ε := by positivity
    have hp1 : 2*ε ≤ 1 := (mass_bounds f hf ε heps 0).1.trans (mass_bounds f hf ε heps 0).2
    have hpow : (2*ε)^N ≤ (2*ε)^n := pow_le_pow_of_le_one hp0 hp1 hnN
    have hsmall := small_horizon_regret hm a f g ε hg hgap hf hε heps k hk hkn p hp
    have hsqrt : Real.sqrt (n:ℝ) ≤ Real.sqrt (N:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hnN)
    have hden : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN0)
    calc
      M*Real.sqrt n ≤ (g*(2*ε)^N/Real.sqrt N)*Real.sqrt n :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
      _ ≤ (g*(2*ε)^N/Real.sqrt N)*Real.sqrt N :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = g*(2*ε)^N := div_mul_cancel₀ _ (ne_of_gt hden)
      _ ≤ g*(2*ε)^n := mul_le_mul_of_nonneg_left hpow hg.le
      _ ≤ R := hsmall

end MultiSecretaryProof

noncomputable section
open MultiSecretary.NonAdaptive Finset
namespace MultiSecretaryProof

theorem supremum_gap {m n : ℕ} (a f : Fin m → ℝ) (k : ℕ) (M : ℝ)
    (h : ∀ p : Fin m → Fin n → ℝ, IsNAPolicy p → M * Real.sqrt n ≤ regret a f k p) :
    M * Real.sqrt n ≤ Voff a f n k - VstarNa a f n k := by
  have hp0 : IsNAPolicy (fun (_ : Fin m) (_ : Fin n) => (0 : ℝ)) := by
    intro j t
    exact ⟨le_rfl, zero_le_one⟩
  have hn : ((fun p : Fin m → Fin n → ℝ => Vna a f k p) '' {p | IsNAPolicy p}).Nonempty :=
    ⟨_, ⟨_, hp0, rfl⟩⟩
  have hs : VstarNa a f n k ≤ Voff a f n k - M * Real.sqrt n := by
    apply csSup_le hn
    rintro v ⟨p, hp, rfl⟩
    have hh := h p hp
    unfold regret at hh
    linarith
  linarith

theorem small_alphabet_mass {m : ℕ} [NeZero m] (hm : m ≤ 2)
    (f : Fin m → ℝ) (hf : IsMasses f) : 1 ≤ f 0 + f (Fin.rev 0) := by
  interval_cases m
  · exact False.elim (NeZero.ne 0 rfl)
  · have h : f 0 = 1 := by simpa using hf.2
    norm_num [h]
  · have h : f 0 + f 1 = 1 := by simpa [Fin.sum_univ_two] using hf.2
    simpa using h.ge

end MultiSecretaryProof

namespace MultiSecretary.NonAdaptive

open Finset

/-- Theorem 3 (p. 25): for `ϵ = ½ min f_j` and `(f_1 + ϵ) n ≤ k ≤ (1 - f_m - ϵ) n` there is a constant
`M ≡ M(ϵ, m, a_1, …, a_m) > 0` with `M√n ≤ V*_off(n, k) - V*_na(n, k)`. -/
theorem sqrt_regret_lower_bound (ε : ℝ) (hε : 0 < ε) (m : ℕ) [NeZero m] (a : Fin m → ℝ)
    (ha : IsValues a) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : Fin m → ℝ, IsMasses f → eps f = ε → ∀ n k : ℕ,
      (f 0 + ε) * n ≤ k → (k : ℝ) ≤ (1 - f (Fin.rev 0) - ε) * n →
      M * Real.sqrt n ≤ Voff a f n k - VstarNa a f n k := by
  classical
  by_cases hm : 3 ≤ m
  · obtain ⟨g, hg, hgap⟩ := MultiSecretaryProof.separatedValues_exists a ha
    obtain ⟨M, hM, hbound⟩ := MultiSecretaryProof.uniform_policy_regret hm a g ε hg hgap hε
    refine ⟨M, hM, ?_⟩
    intro f hf heps n k hklo hkhi
    exact MultiSecretaryProof.supremum_gap a f k M (hbound f hf heps n k hklo hkhi)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro f hf heps n k hklo hkhi
    have _ := heps
    have hs := MultiSecretaryProof.small_alphabet_mass (by omega) f hf
    have hn : n = 0 := by
      have hnr : (0 : ℝ) ≤ n := by positivity
      have hmul := mul_nonneg (sub_nonneg.mpr hs) hnr
      have hn0 : (n : ℝ) = 0 := by nlinarith only [hklo, hkhi, hmul, hε, hnr]
      exact_mod_cast hn0
    apply MultiSecretaryProof.supremum_gap a f k 1
    intro p hp
    simpa [hn] using MultiSecretaryProof.regret_nonneg a f hf k p hp

end MultiSecretary.NonAdaptive

open MultiSecretary.NonAdaptive


open Finset

/-- Theorem 3 (p. 25): for `ϵ = ½ min f_j` and `(f_1 + ϵ) n ≤ k ≤ (1 - f_m - ϵ) n` there is a constant
`M ≡ M(ϵ, m, a_1, …, a_m) > 0` with `M√n ≤ V*_off(n, k) - V*_na(n, k)`. -/
theorem solution (ε : ℝ) (hε : 0 < ε) (m : ℕ) [NeZero m] (a : Fin m → ℝ)
    (ha : IsValues a) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : Fin m → ℝ, IsMasses f → eps f = ε → ∀ n k : ℕ,
      (f 0 + ε) * n ≤ k → (k : ℝ) ≤ (1 - f (Fin.rev 0) - ε) * n →
      M * Real.sqrt n ≤ Voff a f n k - VstarNa a f n k := by
  exact MultiSecretary.NonAdaptive.sqrt_regret_lower_bound ε hε m a ha
