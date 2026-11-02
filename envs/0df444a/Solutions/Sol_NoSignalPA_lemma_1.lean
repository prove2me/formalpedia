-- Prove2me | solution 1 for NoSignalPA.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T22:10:24.648456+00:00
-- url     : https://prove2.me/submissions/2be24530-8cc6-4d3b-8658-8e5eccef3980

import Mathlib
import Definitions.Def_NoSignalPA_pairing
import Definitions.Def_NoSignalPA_gammaVec

namespace NoSignalPALemma1Aux


/-- Masanes' `γ''_t` (independent of Bob's bit): `P(a=t | x=0)` averaged over Bob's input. -/
noncomputable def gpp (t a x y : Bool) : ℝ :=
  if x then (if a = t then (if y then 1 / 4 else -1 / 4) else (if y then -1 / 4 else 1 / 4))
  else (if a = t then 1 / 2 else 0)

/-- The difference `γ_t - γ''_t`. -/
noncomputable def dd (t a b x y : Bool) : ℝ := NoSignalPA.gammaCoef t a b x y - gpp t a x y

lemma dd_indep_a (t a a' b x y : Bool) : dd t a b x y = dd t a' b x y := by
  cases t <;> cases a <;> cases a' <;> cases b <;> cases x <;> cases y <;>
    simp [dd, gpp, NoSignalPA.gammaCoef, NoSignalPA.cell] <;> norm_num

lemma dd_odd_x (t a b y : Bool) : dd t a b true y = -dd t a b false y := by
  cases t <;> cases a <;> cases b <;> cases y <;>
    simp [dd, gpp, NoSignalPA.gammaCoef, NoSignalPA.cell] <;> norm_num

lemma gpp_sum_y (t a x : Bool) : ∑ y : Bool, gpp t a x y = if x = false ∧ a = t then 1 else 0 := by
  rw [Fintype.sum_bool]
  cases t <;> cases a <;> cases x <;> simp [gpp] <;> norm_num



/-- Split a sum over strings by the value of coordinate `j`. -/
lemma sum_split {n : ℕ} (j : Fin n) (φ : NoSignalPA.Str n → ℝ) :
    ∑ a, φ a = ∑ a ∈ Finset.univ.filter (fun a : NoSignalPA.Str n => a j = false),
      ∑ t : Bool, φ (Function.update a j t) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : NoSignalPA.Str n => a j = false)]
  have e1 : ∑ a ∈ Finset.univ.filter (fun a : NoSignalPA.Str n => a j = false), φ a =
      ∑ a ∈ Finset.univ.filter (fun a : NoSignalPA.Str n => a j = false),
        φ (Function.update a j false) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_filter] at ha
    rw [← ha.2, Function.update_eq_self]
  have e2 : ∑ a ∈ Finset.univ.filter (fun a : NoSignalPA.Str n => ¬ a j = false), φ a =
      ∑ a ∈ Finset.univ.filter (fun a : NoSignalPA.Str n => a j = false),
        φ (Function.update a j true) := by
    refine Finset.sum_nbij' (fun a => Function.update a j false) (fun a => Function.update a j true)
      ?_ ?_ ?_ ?_ ?_
    · intro a _
      simp
    · intro a _
      simp
    · intro a ha
      have ha' : a j = true := by simpa using ha
      rw [Function.update_idem, ← ha', Function.update_eq_self]
    · intro a ha
      have ha' : a j = false := by simpa using ha
      rw [Function.update_idem, ← ha', Function.update_eq_self]
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_false] at ha
      rw [Function.update_idem]
      congr 1
      rw [← ha, Function.update_eq_self]
  rw [e1, e2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_bool, add_comm]

/-- The vanishing lemma: pairing a box satisfying Alice-`j` no-signalling with a vector that is
independent of `a_j` and odd in `x_j` gives zero. -/
lemma pairing_eq_zero {n : ℕ} (j : Fin n)
    (Q : NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → ℝ)
    (hA : ∀ (x : NoSignalPA.Str n) (c : Bool) (y a b : NoSignalPA.Str n),
      ∑ t : Bool, Q (Function.update a j t) b x y
        = ∑ t : Bool, Q (Function.update a j t) b (Function.update x j c) y)
    (F : NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → ℝ)
    (hFa : ∀ a b x y t, F (Function.update a j t) b x y = F a b x y)
    (hFx : ∀ a b x y, F a b (Function.update x j true) y = -F a b (Function.update x j false) y) :
    NoSignalPA.pairing F Q = 0 := by
  classical
  unfold NoSignalPA.pairing
  -- bring the sums over `x` and `a` inside
  have h1 : ∀ b y, ∑ x, ∑ a, F a b x y * Q a b x y = 0 := by
    intro b y
    rw [sum_split j]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hS : ∀ c, ∑ a, F a b (Function.update x j c) y * Q a b (Function.update x j c) y =
        ∑ a ∈ Finset.univ.filter (fun a : NoSignalPA.Str n => a j = false),
          F a b (Function.update x j c) y *
            ∑ t : Bool, Q (Function.update a j t) b (Function.update x j false) y := by
      intro c
      rw [sum_split j]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hFa, ← Finset.mul_sum]
      congr 1
      have h := hA (Function.update x j c) false y a b
      rw [Function.update_idem] at h
      rw [h]
    rw [Fintype.sum_bool, hS true, hS false, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hFx]
    ring
  calc ∑ a, ∑ b, ∑ x, ∑ y, F a b x y * Q a b x y
      = ∑ b, ∑ a, ∑ x, ∑ y, F a b x y * Q a b x y := Finset.sum_comm
    _ = ∑ b, ∑ x, ∑ a, ∑ y, F a b x y * Q a b x y :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ x, ∑ y, ∑ a, F a b x y * Q a b x y :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ b, ∑ y, ∑ x, ∑ a, F a b x y * Q a b x y :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun y _ => h1 b y


/-- `pairing` is additive in its first argument. -/
lemma pairing_sub_left {n : ℕ}
    (G1 G2 Q : NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → ℝ) :
    NoSignalPA.pairing G1 Q - NoSignalPA.pairing G2 Q =
      NoSignalPA.pairing (fun a b x y => G1 a b x y - G2 a b x y) Q := by
  unfold NoSignalPA.pairing
  simp only [← Finset.sum_sub_distrib, sub_mul]

/-- The vectors interpolating between `Γ_s` (`S = ∅`) and `Γ''_s` (`S = univ`). -/
noncomputable def mixed {n : ℕ} (s : NoSignalPA.Str n) (S : Finset (Fin n))
    (a b x y : NoSignalPA.Str n) : ℝ :=
  ∏ i, (if i ∈ S then gpp (s i) (a i) (x i) (y i) else
    NoSignalPA.gammaCoef (s i) (a i) (b i) (x i) (y i))

lemma mixed_step {n : ℕ} (s : NoSignalPA.Str n)
    (Q : NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → ℝ)
    (hA : ∀ (i : Fin n) (x : NoSignalPA.Str n) (c : Bool) (y a b : NoSignalPA.Str n),
      ∑ t : Bool, Q (Function.update a i t) b x y
        = ∑ t : Bool, Q (Function.update a i t) b (Function.update x i c) y)
    (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S) :
    NoSignalPA.pairing (mixed s (insert j S)) Q = NoSignalPA.pairing (mixed s S) Q := by
  classical
  -- the remaining factors
  let R : NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → NoSignalPA.Str n → ℝ :=
    fun a b x y => ∏ i ∈ Finset.univ.erase j, (if i ∈ S then gpp (s i) (a i) (x i) (y i) else
      NoSignalPA.gammaCoef (s i) (a i) (b i) (x i) (y i))
  have hsplitI : ∀ a b x y, mixed s (insert j S) a b x y = gpp (s j) (a j) (x j) (y j) * R a b x y := by
    intro a b x y
    simp only [mixed]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), if_pos (Finset.mem_insert_self j S)]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp only [Finset.mem_insert, hij, false_or]
  have hsplitS : ∀ a b x y, mixed s S a b x y =
      NoSignalPA.gammaCoef (s j) (a j) (b j) (x j) (y j) * R a b x y := by
    intro a b x y
    simp only [mixed]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), if_neg hj]
  rw [← sub_eq_zero, pairing_sub_left]
  refine pairing_eq_zero j Q (hA j) _ ?_ ?_
  · intro a b x y t
    simp only [hsplitI, hsplitS, Function.update_self]
    have hR : R (Function.update a j t) b x y = R a b x y := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hR, ← sub_mul, ← sub_mul]
    congr 1
    have h1 := dd_indep_a (s j) t (a j) (b j) (x j) (y j)
    simp only [dd] at h1
    linarith
  · intro a b x y
    simp only [hsplitI, hsplitS, Function.update_self]
    have hR : ∀ c, R a b (Function.update x j c) y = R a b (Function.update x j false) y := by
      intro c
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
        Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hR true, ← sub_mul, ← sub_mul, ← neg_mul]
    congr 1
    have h1 := dd_odd_x (s j) (a j) (b j) (y j)
    simp only [dd] at h1
    linarith

end NoSignalPALemma1Aux

open NoSignalPALemma1Aux in
theorem solution {Nr : ℕ} (Q : NoSignalPA.Str Nr → NoSignalPA.Str Nr → NoSignalPA.Str Nr →
      NoSignalPA.Str Nr → ℝ)
    (hA : ∀ (i : Fin Nr) (x : NoSignalPA.Str Nr) (c : Bool) (y a b : NoSignalPA.Str Nr),
      ∑ t : Bool, Q (Function.update a i t) b x y
        = ∑ t : Bool, Q (Function.update a i t) b (Function.update x i c) y)
    (hB : ∀ (a x y y' : NoSignalPA.Str Nr), ∑ b : NoSignalPA.Str Nr, Q a b x y =
      ∑ b : NoSignalPA.Str Nr, Q a b x y')
    (s y : NoSignalPA.Str Nr) :
    ∑ b : NoSignalPA.Str Nr, Q s b (fun _ => false) y = NoSignalPA.pairing (NoSignalPA.gammaVec s) Q := by
  classical
  -- Step 1 (Alice): replace `γ` by `γ''` one system at a time
  have hstep : ∀ S : Finset (Fin Nr),
      NoSignalPA.pairing (mixed s S) Q = NoSignalPA.pairing (mixed s ∅) Q := by
    intro S
    induction S using Finset.induction_on with
    | empty => rfl
    | insert j S hj ih => rw [mixed_step s Q hA S j hj, ih]
  have h0 : mixed s ∅ = NoSignalPA.gammaVec s := by
    funext a b x y'
    simp [mixed, NoSignalPA.gammaVec]
  rw [← h0, ← hstep Finset.univ]
  -- Step 2 (Bob): `Γ''` does not depend on `b`; sum `b` out and use Bob's no-signalling
  have hmix : ∀ a b x y', mixed s Finset.univ a b x y' = ∏ i, gpp (s i) (a i) (x i) (y' i) := by
    intro a b x y'
    simp [mixed]
  unfold NoSignalPA.pairing
  simp only [hmix]
  have hcollapse : ∀ a x, ∑ y' : NoSignalPA.Str Nr, ∏ i, gpp (s i) (a i) (x i) (y' i) =
      if x = (fun _ => false) ∧ a = s then 1 else 0 := by
    intro a x
    rw [← Fintype.prod_sum (fun i t => gpp (s i) (a i) (x i) t)]
    simp only [gpp_sum_y]
    rw [Fintype.prod_boole]
    congr 1
    apply propext
    constructor
    · intro h
      exact ⟨funext fun i => (h i).1, funext fun i => (h i).2⟩
    · rintro ⟨hx, ha⟩ i
      exact ⟨congrFun hx i, congrFun ha i⟩
  have hR : ∀ a x, ∑ y', (∏ i, gpp (s i) (a i) (x i) (y' i)) * ∑ b, Q a b x y' =
      (∑ b, Q a b x y) * (if x = (fun _ => false) ∧ a = s then 1 else 0) := by
    intro a x
    rw [Finset.sum_congr rfl fun y' _ => by rw [hB a x y' y], ← Finset.sum_mul, hcollapse,
      mul_comm]
  symm
  calc ∑ a, ∑ b, ∑ x, ∑ y', (∏ i, gpp (s i) (a i) (x i) (y' i)) * Q a b x y'
      = ∑ a, ∑ x, ∑ y', ∑ b, (∏ i, gpp (s i) (a i) (x i) (y' i)) * Q a b x y' := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ a, ∑ x, ∑ y', (∏ i, gpp (s i) (a i) (x i) (y' i)) * ∑ b, Q a b x y' := by
        simp only [Finset.mul_sum]
    _ = ∑ a, ∑ x, (∑ b, Q a b x y) * (if x = (fun _ => false) ∧ a = s then 1 else 0) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => hR a x
    _ = ∑ b, Q s b (fun _ => false) y := by
        rw [Finset.sum_eq_single s]
        · rw [Finset.sum_eq_single (fun _ => false)]
          · simp
          · intro x _ hx
            simp [hx]
          · simp
        · intro a _ ha
          refine Finset.sum_eq_zero fun x _ => ?_
          simp [ha]
        · simp
