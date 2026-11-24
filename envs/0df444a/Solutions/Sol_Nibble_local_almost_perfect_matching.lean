-- Prove2me | solution 1 for Nibble.local_almost_perfect_matching
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T13:03:12.049539+00:00
-- url     : https://prove2.me/submissions/d1a8c27f-2db8-4d81-ad65-32d91264b850

import Mathlib
import Theorems.Thm_PartialResampling_pra_exists

set_option autoImplicit false

section SecBasic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset

namespace Nib

variable {J Sl O : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
  [Fintype O] [DecidableEq O]

/-- the hypergraph: each option belongs to a job and uses a finite set of slots -/
structure HG (J Sl O : Type) where
  job : O → J
  sl : O → Finset Sl

variable (H : HG J Sl O)

/-- mass of a job -/
noncomputable def mass (x : O → ℝ) (e : J) : ℝ := ∑ o ∈ univ.filter (fun o => H.job o = e), x o

/-- load of a slot -/
noncomputable def load (x : O → ℝ) (s : Sl) : ℝ := ∑ o ∈ univ.filter (fun o => s ∈ H.sl o), x o

/-- mass of job `f` on options meeting the slot set `T` -/
noncomputable def aff (x : O → ℝ) (f : J) (T : Finset Sl) : ℝ :=
  ∑ o ∈ univ.filter (fun o => H.job o = f ∧ ¬ Disjoint (H.sl o) T), x o

/-- pick distribution of job `e` -/
noncomputable def pp (θ : ℝ) (x : O → ℝ) (e : J) : Option O → ℝ
  | none => 1 - θ * mass H x e
  | some o => if H.job o = e then θ * x o else 0

/-- avoidance indicator: the pick `y` uses no slot of `T` -/
def avoid (T : Finset Sl) : Option O → ℝ
  | none => 1
  | some o => if Disjoint (H.sl o) T then 1 else 0

/-- expectation over pick configurations -/
noncomputable def EE (θ : ℝ) (x : O → ℝ) (F : (J → Option O) → ℝ) : ℝ :=
  ∑ Z : J → Option O, (∏ e, pp H θ x e (Z e)) * F Z

variable {H}

theorem sum_pp (θ : ℝ) (x : O → ℝ) (e : J) : ∑ y, pp H θ x e y = 1 := by
  rw [Fintype.sum_option]
  simp only [pp]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, mass, Finset.mul_sum]
  ring

theorem pp_nonneg (θ : ℝ) (x : O → ℝ) (hθ : 0 ≤ θ) (hx : ∀ o, 0 ≤ x o)
    (hm : ∀ e, θ * mass H x e ≤ 1) (e : J) (y : Option O) : 0 ≤ pp H θ x e y := by
  cases y with
  | none => simp only [pp]; linarith [hm e]
  | some o => simp only [pp]; split_ifs; exact mul_nonneg hθ (hx o); exact le_rfl

/-- expectation of a product of per-coordinate factors -/
theorem EE_prod (θ : ℝ) (x : O → ℝ) (g : J → Option O → ℝ) :
    EE H θ x (fun Z => ∏ e, g e (Z e)) = ∏ e, ∑ y, pp H θ x e y * g e y := by
  unfold EE
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun Z _ => ?_)
  rw [Finset.prod_mul_distrib]

/-- average of an avoidance indicator -/
theorem sum_pp_avoid (θ : ℝ) (x : O → ℝ) (f : J) (T : Finset Sl) :
    ∑ y, pp H θ x f y * avoid H T y = 1 - θ * aff H x f T := by
  rw [Fintype.sum_option]
  simp only [pp, avoid, mul_one]
  have : ∑ o, (if H.job o = f then θ * x o else 0) * (if Disjoint (H.sl o) T then (1 : ℝ) else 0) =
      θ * mass H x f - θ * aff H x f T := by
    have hpt : ∀ o, (if H.job o = f then θ * x o else 0) * (if Disjoint (H.sl o) T then (1 : ℝ) else 0) =
        θ * (if H.job o = f then x o else 0) - θ * (if H.job o = f ∧ ¬ Disjoint (H.sl o) T then x o else 0) := by
      intro o
      by_cases h1 : H.job o = f <;> by_cases h2 : Disjoint (H.sl o) T <;> simp [h1, h2]
    simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, mass, aff, Finset.sum_filter]
  rw [this]; ring


/-! ## Round definitions (validity-aware) -/

variable (H)

/-- `f`'s pick `y` avoids the slot set `T` (invalid picks avoid everything) -/
def av (f : J) (T : Finset Sl) : Option O → ℝ
  | none => 1
  | some o => if H.job o = f ∧ ¬ Disjoint (H.sl o) T then 0 else 1

/-- survival factor of option `o` -/
noncomputable def piF (θ : ℝ) (x : O → ℝ) (o : O) : ℝ :=
  ∏ f ∈ univ.erase (H.job o), (1 - θ * aff H x f (H.sl o))

/-- job `e` wins under picks `Z` -/
noncomputable def win (Z : J → Option O) (e : J) : ℝ :=
  ∑ o ∈ univ.filter (fun o => H.job o = e),
    (if Z e = some o then 1 else 0) * ∏ f ∈ univ.erase e, av H f (H.sl o) (Z f)

/-- the next weights -/
noncomputable def nxt (θ : ℝ) (x : O → ℝ) (Z : J → Option O) (o : O) : ℝ :=
  x o / piF H θ x o * (∏ f, av H f (H.sl o) (Z f)) * (1 - win H Z (H.job o))

variable {H}

theorem av_eq_avoid (f : J) (T : Finset Sl) (θ : ℝ) (x : O → ℝ) (y : Option O) :
    pp H θ x f y * av H f T y = pp H θ x f y * avoid H T y := by
  cases y with
  | none => simp [av, avoid]
  | some o =>
    simp only [pp, av, avoid]
    by_cases h1 : H.job o = f <;> by_cases h2 : Disjoint (H.sl o) T <;> simp [h1, h2]

theorem sum_pp_av (θ : ℝ) (x : O → ℝ) (f : J) (T : Finset Sl) :
    ∑ y, pp H θ x f y * av H f T y = 1 - θ * aff H x f T := by
  simp_rw [av_eq_avoid]; exact sum_pp_avoid θ x f T

theorem av_nonneg (f : J) (T : Finset Sl) (y : Option O) : 0 ≤ av H f T y := by
  cases y with
  | none => simp [av]
  | some o => simp only [av]; split_ifs <;> norm_num

theorem av_le_one (f : J) (T : Finset Sl) (y : Option O) : av H f T y ≤ 1 := by
  cases y with
  | none => simp [av]
  | some o => simp only [av]; split_ifs <;> norm_num

theorem av_mono (f : J) (T T' : Finset Sl) (h : T ⊆ T') (y : Option O) :
    av H f T' y ≤ av H f T y := by
  cases y with
  | none => simp [av]
  | some o =>
    simp only [av]
    by_cases h1 : H.job o = f ∧ ¬Disjoint (H.sl o) T
    · rw [if_pos h1, if_pos ⟨h1.1, fun hd => h1.2 (Finset.disjoint_of_subset_right h hd)⟩]
    · rw [if_neg h1]; split_ifs <;> norm_num

/-- expectation of a product over all jobs except one -/
theorem EE_prod_erase (θ : ℝ) (x : O → ℝ) (e : J) (g : J → Option O → ℝ) :
    EE H θ x (fun Z => ∏ f ∈ univ.erase e, g f (Z f)) =
      ∏ f ∈ univ.erase e, ∑ y, pp H θ x f y * g f y := by
  have hfe : univ.erase e = univ.filter (fun f => f ≠ e) := by ext; simp
  have := EE_prod (H := H) θ x (fun f y => if f = e then 1 else g f y)
  have e1 : (fun Z : J → Option O => ∏ f, (if f = e then 1 else g f (Z f))) =
      (fun Z => ∏ f ∈ univ.erase e, g f (Z f)) := by
    funext Z
    rw [hfe, Finset.prod_filter]
    refine Finset.prod_congr rfl (fun f _ => ?_)
    by_cases h : f = e <;> simp [h]
  rw [e1] at this
  rw [this, hfe, Finset.prod_filter]
  refine Finset.prod_congr rfl (fun f _ => ?_)
  by_cases h : f = e
  · subst h
    have := sum_pp (H := H) θ x f
    simpa using this
  · simp [h]

theorem EE_add (θ : ℝ) (x : O → ℝ) (F G : (J → Option O) → ℝ) :
    EE H θ x (fun Z => F Z + G Z) = EE H θ x F + EE H θ x G := by
  unfold EE; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun Z _ => by ring)

theorem EE_smul (θ : ℝ) (x : O → ℝ) (c : ℝ) (F : (J → Option O) → ℝ) :
    EE H θ x (fun Z => c * F Z) = c * EE H θ x F := by
  unfold EE; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun Z _ => by ring)

theorem EE_finsum {α : Type} (θ : ℝ) (x : O → ℝ) (s : Finset α) (F : α → (J → Option O) → ℝ) :
    EE H θ x (fun Z => ∑ a ∈ s, F a Z) = ∑ a ∈ s, EE H θ x (F a) := by
  unfold EE; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]

end Nib

end SecBasic

section SecRIC

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset

namespace RIC

variable {X : Type} [Fintype X]

/-- iterated expectation over `Fin m → X` with independent coordinates -/
noncomputable def E : (m : ℕ) → (Fin m → X → ℝ) → ((Fin m → X) → ℝ) → ℝ
  | 0, _, f => f Fin.elim0
  | m + 1, p, f => ∑ y, p 0 y * E m (fun i => p i.succ) (fun x => f (Fin.cons y x))

theorem E_affine : ∀ (m : ℕ) (p : Fin m → X → ℝ) (hp1 : ∀ i, ∑ y, p i y = 1)
    (a b : ℝ) (f : (Fin m → X) → ℝ), E m p (fun x => a + b * f x) = a + b * E m p f
  | 0, p, _, a, b, f => rfl
  | m + 1, p, hp1, a, b, f => by
    simp only [E]
    have key : ∀ y, E m (fun i => p i.succ) (fun x => a + b * f (Fin.cons y x)) =
        a + b * E m (fun i => p i.succ) (fun x => f (Fin.cons y x)) :=
      fun y => E_affine m _ (fun i => hp1 i.succ) a b _
    simp_rw [key, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1 0, one_mul]
    congr 1
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun y _ => by ring)

theorem E_add : ∀ (m : ℕ) (p : Fin m → X → ℝ) (f g : (Fin m → X) → ℝ),
    E m p (fun x => f x + g x) = E m p f + E m p g
  | 0, p, f, g => rfl
  | m + 1, p, f, g => by
    simp only [E]
    have key : ∀ y, E m (fun i => p i.succ) (fun x => f (Fin.cons y x) + g (Fin.cons y x)) =
        E m (fun i => p i.succ) (fun x => f (Fin.cons y x)) +
          E m (fun i => p i.succ) (fun x => g (Fin.cons y x)) := fun y => E_add m _ _ _
    simp_rw [key, mul_add, Finset.sum_add_distrib]

theorem E_smul : ∀ (m : ℕ) (p : Fin m → X → ℝ) (b : ℝ) (f : (Fin m → X) → ℝ),
    E m p (fun x => b * f x) = b * E m p f
  | 0, p, b, f => rfl
  | m + 1, p, b, f => by
    simp only [E]
    have key : ∀ y, E m (fun i => p i.succ) (fun x => b * f (Fin.cons y x)) =
        b * E m (fun i => p i.succ) (fun x => f (Fin.cons y x)) := fun y => E_smul m _ _ _
    simp_rw [key, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => by ring)

theorem E_mono : ∀ (m : ℕ) (p : Fin m → X → ℝ) (hp0 : ∀ i y, 0 ≤ p i y)
    (f g : (Fin m → X) → ℝ), (∀ x, f x ≤ g x) → E m p f ≤ E m p g
  | 0, p, _, f, g, h => h _
  | m + 1, p, hp0, f, g, h => by
    simp only [E]
    refine Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left ?_ (hp0 0 y))
    exact E_mono m _ (fun i => hp0 i.succ) _ _ (fun x => h _)

theorem E_const (m : ℕ) (p : Fin m → X → ℝ) (hp1 : ∀ i, ∑ y, p i y = 1) (a : ℝ) :
    E m p (fun _ => a) = a := by
  have := E_affine m p hp1 a 0 (fun _ => 0)
  simpa using this

theorem E_finsum {α : Type} (m : ℕ) (p : Fin m → X → ℝ) (s : Finset α) (b : α → ℝ)
    (F : α → (Fin m → X) → ℝ) :
    E m p (fun x => ∑ a ∈ s, b a * F a x) = ∑ a ∈ s, b a * E m p (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := E_smul m p 0 (fun _ => (0 : ℝ))
    simpa using this
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [E_add m p (fun x => b a * F a x) (fun x => ∑ a ∈ s, b a * F a x), ih, E_smul]

/-- Jensen: (E f)^2 ≤ E f^2 -/
theorem E_sq_le : ∀ (m : ℕ) (p : Fin m → X → ℝ) (hp0 : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y = 1) (f : (Fin m → X) → ℝ), (E m p f) ^ 2 ≤ E m p (fun x => (f x) ^ 2)
  | 0, p, _, _, f => le_rfl
  | m + 1, p, hp0, hp1, f => by
    simp only [E]
    set a : X → ℝ := fun y => E m (fun i => p i.succ) (fun x => f (Fin.cons y x)) with ha
    have IH : ∀ y, (a y) ^ 2 ≤ E m (fun i => p i.succ) (fun x => (f (Fin.cons y x)) ^ 2) :=
      fun y => E_sq_le m _ (fun i => hp0 i.succ) (fun i => hp1 i.succ) _
    have hvar : 0 ≤ ∑ y, p 0 y * (a y - ∑ y', p 0 y' * a y') ^ 2 :=
      Finset.sum_nonneg (fun y _ => mul_nonneg (hp0 0 y) (sq_nonneg _))
    have hexp : ∑ y, p 0 y * (a y - ∑ y', p 0 y' * a y') ^ 2 =
        ∑ y, p 0 y * (a y) ^ 2 - (∑ y', p 0 y' * a y') ^ 2 := by
      set ā := ∑ y', p 0 y' * a y'
      have e1 : ∀ y, p 0 y * (a y - ā) ^ 2 = p 0 y * (a y) ^ 2 - 2 * ā * (p 0 y * a y) + ā ^ 2 * p 0 y :=
        fun y => by ring
      simp_rw [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp1 0]
      ring
    calc (∑ y, p 0 y * a y) ^ 2 ≤ ∑ y, p 0 y * (a y) ^ 2 := by linarith
      _ ≤ _ := Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (IH y) (hp0 0 y))

/-- single-variable MGF bound -/
theorem mgf_single (q : X → ℝ) (hq0 : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1) (Z : X → ℝ)
    (hZ0 : ∑ y, q y * Z y = 0) (c v t : ℝ) (hc : ∀ y, |Z y| ≤ c) (hv : ∑ y, q y * (Z y) ^ 2 ≤ v)
    (ht0 : 0 ≤ t) (htc : t * c ≤ 1) :
    ∑ y, q y * Real.exp (t * Z y) ≤ Real.exp (t ^ 2 * v) := by
  have hb : ∀ y, Real.exp (t * Z y) ≤ 1 + t * Z y + (t * Z y) ^ 2 := by
    intro y
    have h1 : |t * Z y| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ht0]
      exact le_trans (mul_le_mul_of_nonneg_left (hc y) ht0) htc
    have := Real.abs_exp_sub_one_sub_id_le h1
    have := (abs_le.mp this).2
    linarith
  calc ∑ y, q y * Real.exp (t * Z y) ≤ ∑ y, q y * (1 + t * Z y + (t * Z y) ^ 2) :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hb y) (hq0 y))
    _ = 1 + t * (∑ y, q y * Z y) + t ^ 2 * ∑ y, q y * (Z y) ^ 2 := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← hq1]
        rw [hq1, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · congr 1
          · simpa using hq1
          · refine Finset.sum_congr rfl (fun y _ => by ring)
        · refine Finset.sum_congr rfl (fun y _ => by ring)
    _ ≤ 1 + t ^ 2 * v := by rw [hZ0]; nlinarith [sq_nonneg t]
    _ ≤ Real.exp (t ^ 2 * v) := by linarith [Real.add_one_le_exp (t ^ 2 * v)]

theorem mgf_bound [DecidableEq X] : ∀ (m : ℕ) (p : Fin m → X → ℝ) (hp0 : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y = 1) (f : (Fin m → X) → ℝ) (c : ℝ) (v : Fin m → ℝ)
    (hrange : ∀ x i y y', |f (Function.update x i y) - f (Function.update x i y')| ≤ c)
    (hvar : ∀ x i, ∑ y, p i y * (f (Function.update x i y) -
        ∑ y', p i y' * f (Function.update x i y')) ^ 2 ≤ v i)
    (t : ℝ) (ht0 : 0 ≤ t) (htc : t * c ≤ 1),
    E m p (fun x => Real.exp (t * (f x - E m p f))) ≤ Real.exp (t ^ 2 * ∑ i, v i)
  | 0, p, _, _, f, c, v, _, _, t, _, _ => by simp [E]
  | m + 1, p, hp0, hp1, f, c, v, hrange, hvar, t, ht0, htc => by
    set p' : Fin m → X → ℝ := fun i => p i.succ with hp'
    set g : X → ℝ := fun y => E m p' (fun x => f (Fin.cons y x)) with hg
    have hEf : E (m + 1) p f = ∑ y, p 0 y * g y := rfl
    -- IH for each slice
    have IH : ∀ y, E m p' (fun x => Real.exp (t * (f (Fin.cons y x) - g y))) ≤
        Real.exp (t ^ 2 * ∑ i : Fin m, v i.succ) := by
      intro y
      refine mgf_bound m p' (fun i => hp0 i.succ) (fun i => hp1 i.succ) (fun x => f (Fin.cons y x))
        c (fun i => v i.succ) ?_ ?_ t ht0 htc
      · intro x i y1 y2
        simp only [Fin.cons_update]
        exact hrange _ _ _ _
      · intro x i
        simp only [Fin.cons_update]
        exact hvar _ _
    -- the first coordinate
    have hZ : ∑ y, p 0 y * Real.exp (t * (g y - E (m + 1) p f)) ≤ Real.exp (t ^ 2 * v 0) := by
      refine mgf_single (p 0) (hp0 0) (hp1 0) (fun y => g y - E (m + 1) p f) ?_ c (v 0) t ?_ ?_ ht0 htc
      · simp only [mul_sub, Finset.sum_sub_distrib, hEf, ← Finset.sum_mul, hp1 0, one_mul, sub_self]
      · intro y
        rw [hEf]
        have : g y - ∑ y', p 0 y' * g y' = ∑ y', p 0 y' * (g y - g y') := by
          simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1 0, one_mul]
        rw [this]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        calc ∑ y', |p 0 y' * (g y - g y')| ≤ ∑ y', p 0 y' * c := by
              refine Finset.sum_le_sum (fun y' _ => ?_)
              rw [abs_mul, abs_of_nonneg (hp0 0 y')]
              refine mul_le_mul_of_nonneg_left ?_ (hp0 0 y')
              rw [hg]
              simp only
              have h1 : E m p' (fun x => f (Fin.cons y x)) - E m p' (fun x => f (Fin.cons y' x)) =
                  E m p' (fun x => f (Fin.cons y x) - f (Fin.cons y' x)) := by
                have := E_add m p' (fun x => f (Fin.cons y x)) (fun x => -f (Fin.cons y' x))
                have h2 := E_smul m p' (-1) (fun x => f (Fin.cons y' x))
                simp only [neg_one_mul] at h2
                rw [sub_eq_add_neg, ← h2, ← this]; rfl
              rw [h1]
              have hb : ∀ x : Fin m → X, |f (Fin.cons y x) - f (Fin.cons y' x)| ≤ c := by
                intro x
                have := hrange (Fin.cons y x) 0 y y'
                simpa [Fin.update_cons_zero] using this
              have hup := E_mono m p' (fun i => hp0 i.succ) _ (fun _ => c) (fun x => (abs_le.mp (hb x)).2)
              have hlo := E_mono m p' (fun i => hp0 i.succ) (fun _ => -c) _ (fun x => (abs_le.mp (hb x)).1)
              rw [E_const m p' (fun i => hp1 i.succ)] at hup hlo
              exact abs_le.mpr ⟨hlo, hup⟩
          _ = c := by rw [← Finset.sum_mul, hp1 0, one_mul]
      · -- variance via Jensen
        rw [hEf]
        have hjen : ∀ y, (g y - ∑ y', p 0 y' * g y') ^ 2 ≤
            E m p' (fun x => (f (Fin.cons y x) - ∑ y', p 0 y' * f (Fin.cons y' x)) ^ 2) := by
          intro y
          have : g y - ∑ y', p 0 y' * g y' =
              E m p' (fun x => f (Fin.cons y x) - ∑ y', p 0 y' * f (Fin.cons y' x)) := by
            have h1 := E_add m p' (fun x => f (Fin.cons y x))
              (fun x => -1 * ∑ y', p 0 y' * f (Fin.cons y' x))
            have h2 := E_smul m p' (-1) (fun x => ∑ y', p 0 y' * f (Fin.cons y' x))
            have h3 := E_finsum m p' Finset.univ (fun y' => p 0 y') (fun y' x => f (Fin.cons y' x))
            simp only [neg_one_mul, ← sub_eq_add_neg] at h1 h2
            rw [h1, h2, h3, ← sub_eq_add_neg]
          rw [this]
          exact E_sq_le m p' (fun i => hp0 i.succ) (fun i => hp1 i.succ) _
        calc ∑ y, p 0 y * (g y - ∑ y', p 0 y' * g y') ^ 2
            ≤ ∑ y, p 0 y * E m p' (fun x => (f (Fin.cons y x) - ∑ y', p 0 y' * f (Fin.cons y' x)) ^ 2) :=
              Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hjen y) (hp0 0 y))
          _ = E m p' (fun x => ∑ y, p 0 y * (f (Fin.cons y x) - ∑ y', p 0 y' * f (Fin.cons y' x)) ^ 2) :=
              (E_finsum m p' Finset.univ (fun y => p 0 y)
                (fun y x => (f (Fin.cons y x) - ∑ y', p 0 y' * f (Fin.cons y' x)) ^ 2)).symm
          _ ≤ E m p' (fun _ => v 0) := by
              refine E_mono m p' (fun i => hp0 i.succ) _ _ (fun x => ?_)
              have : Nonempty X := by
                by_contra h
                rw [not_nonempty_iff] at h
                have := hp1 0
                simp at this
              have := hvar (Fin.cons (Classical.arbitrary X) x) 0
              simpa [Fin.update_cons_zero] using this
          _ = v 0 := E_const m p' (fun i => hp1 i.succ) _
    -- combine
    show ∑ y, p 0 y * E m p' (fun x => Real.exp (t * (f (Fin.cons y x) - E (m + 1) p f))) ≤ _
    have e1 : ∀ y, E m p' (fun x => Real.exp (t * (f (Fin.cons y x) - E (m + 1) p f))) =
        Real.exp (t * (g y - E (m + 1) p f)) * E m p' (fun x => Real.exp (t * (f (Fin.cons y x) - g y))) := by
      intro y
      rw [← E_smul]
      congr 1; funext x
      rw [← Real.exp_add]; congr 1; ring
    simp_rw [e1]
    calc ∑ y, p 0 y * (Real.exp (t * (g y - E (m + 1) p f)) *
          E m p' (fun x => Real.exp (t * (f (Fin.cons y x) - g y))))
        ≤ ∑ y, p 0 y * (Real.exp (t * (g y - E (m + 1) p f)) * Real.exp (t ^ 2 * ∑ i : Fin m, v i.succ)) :=
          Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (IH y) (Real.exp_pos _).le) (hp0 0 y))
      _ = (∑ y, p 0 y * Real.exp (t * (g y - E (m + 1) p f))) * Real.exp (t ^ 2 * ∑ i : Fin m, v i.succ) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun y _ => by ring)
      _ ≤ Real.exp (t ^ 2 * v 0) * Real.exp (t ^ 2 * ∑ i : Fin m, v i.succ) :=
          mul_le_mul_of_nonneg_right hZ (Real.exp_pos _).le
      _ = Real.exp (t ^ 2 * ∑ i, v i) := by
          rw [← Real.exp_add, Fin.sum_univ_succ]; congr 1; ring

theorem E_eq_sum [DecidableEq X] : ∀ (m : ℕ) (p : Fin m → X → ℝ) (f : (Fin m → X) → ℝ),
    E m p f = ∑ x : Fin m → X, (∏ i, p i (x i)) * f x
  | 0, p, f => by
    simp only [E, Finset.univ_unique, Finset.prod_empty, one_mul, Finset.sum_singleton]
    rw [Subsingleton.elim (Fin.elim0 : Fin 0 → X) default]; simp
  | m + 1, p, f => by
    simp only [E]
    rw [← (Fin.consEquiv (fun _ => X)).sum_comp]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [E_eq_sum m, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [mul_assoc]; rfl

/-- tail bound on `Fin m → X` -/
theorem tail_fin [DecidableEq X] (m : ℕ) (p : Fin m → X → ℝ) (hp0 : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y = 1) (f : (Fin m → X) → ℝ) (c : ℝ) (v : Fin m → ℝ)
    (hrange : ∀ x i y y', |f (Function.update x i y) - f (Function.update x i y')| ≤ c)
    (hvar : ∀ x i, ∑ y, p i y * (f (Function.update x i y) -
        ∑ y', p i y' * f (Function.update x i y')) ^ 2 ≤ v i)
    (t lam : ℝ) (ht0 : 0 ≤ t) (htc : t * c ≤ 1) :
    E m p (fun x => if lam ≤ f x - E m p f then 1 else 0) ≤ Real.exp (-(t * lam) + t ^ 2 * ∑ i, v i) := by
  have hmgf := mgf_bound m p hp0 hp1 f c v hrange hvar t ht0 htc
  have hmk : ∀ x, (if lam ≤ f x - E m p f then (1 : ℝ) else 0) ≤
      Real.exp (-(t * lam)) * Real.exp (t * (f x - E m p f)) := by
    intro x
    split_ifs with h
    · rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    · positivity
  calc E m p (fun x => if lam ≤ f x - E m p f then 1 else 0)
      ≤ E m p (fun x => Real.exp (-(t * lam)) * Real.exp (t * (f x - E m p f))) :=
        E_mono m p hp0 _ _ hmk
    _ = Real.exp (-(t * lam)) * E m p (fun x => Real.exp (t * (f x - E m p f))) := E_smul _ _ _ _
    _ ≤ Real.exp (-(t * lam)) * Real.exp (t ^ 2 * ∑ i, v i) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]

end RIC

/-- **Bernstein-type bounded-differences inequality** on a finite product space, general index type. -/
theorem ric_tail {K X : Type} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]
    (p : K → X → ℝ) (hp0 : ∀ k y, 0 ≤ p k y) (hp1 : ∀ k, ∑ y, p k y = 1)
    (f : (K → X) → ℝ) (c : ℝ) (v : K → ℝ)
    (hrange : ∀ x k y y', |f (Function.update x k y) - f (Function.update x k y')| ≤ c)
    (hvar : ∀ x k, ∑ y, p k y * (f (Function.update x k y) -
        ∑ y', p k y' * f (Function.update x k y')) ^ 2 ≤ v k)
    (t lam : ℝ) (ht0 : 0 ≤ t) (htc : t * c ≤ 1) :
    ∑ x : K → X, (∏ k, p k (x k)) *
        (if lam ≤ f x - ∑ x' : K → X, (∏ k, p k (x' k)) * f x' then 1 else 0) ≤
      Real.exp (-(t * lam) + t ^ 2 * ∑ k, v k) := by
  set m := Fintype.card K
  let e : K ≃ Fin m := Fintype.equivFin K
  -- transported data
  let p' : Fin m → X → ℝ := fun i => p (e.symm i)
  let f' : (Fin m → X) → ℝ := fun x' => f (fun k => x' (e k))
  let v' : Fin m → ℝ := fun i => v (e.symm i)
  let T : (Fin m → X) ≃ (K → X) := (Equiv.arrowCongr e (Equiv.refl X)).symm
  have hT : ∀ x', T x' = fun k => x' (e k) := fun x' => by
    funext k; simp [T, Equiv.arrowCongr]
  have hsum : ∀ g : (K → X) → ℝ, ∑ x : K → X, (∏ k, p k (x k)) * g x =
      RIC.E m p' (fun x' => g (fun k => x' (e k))) := by
    intro g
    rw [RIC.E_eq_sum]
    rw [← T.sum_comp]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    rw [hT]
    congr 1
    rw [← e.symm.prod_comp]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp [p']
  have hupd : ∀ (x' : Fin m → X) (i : Fin m) (y : X),
      (fun k => Function.update x' i y (e k)) = Function.update (fun k => x' (e k)) (e.symm i) y := by
    intro x' i y
    funext k
    by_cases hk : k = e.symm i
    · subst hk; simp
    · have : e k ≠ i := fun h => hk (by rw [← h]; simp)
      simp [Function.update_of_ne this, Function.update_of_ne hk]
  rw [hsum, hsum f]
  have key := RIC.tail_fin m p' (fun i y => hp0 _ y) (fun i => hp1 _) f' c v'
    (fun x' i y y' => by simp only [f']; rw [hupd, hupd]; exact hrange _ _ _ _)
    (fun x' i => by simp only [f']; simp_rw [hupd]; exact hvar _ _) t lam ht0 htc
  have hv : ∑ i, v' i = ∑ k, v k := e.symm.sum_comp v
  rw [hv] at key
  exact key

/-- deviation form: with `λ = 2√(VΛ) + 2cΛ` the upper tail is at most `e^{-Λ}` -/
theorem ric_dev {K X : Type} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]
    (p : K → X → ℝ) (hp0 : ∀ k y, 0 ≤ p k y) (hp1 : ∀ k, ∑ y, p k y = 1)
    (f : (K → X) → ℝ) (c : ℝ) (hc : 0 < c) (v : K → ℝ) (hv : ∀ k, 0 ≤ v k)
    (hrange : ∀ x k y y', |f (Function.update x k y) - f (Function.update x k y')| ≤ c)
    (hvar : ∀ x k, ∑ y, p k y * (f (Function.update x k y) -
        ∑ y', p k y' * f (Function.update x k y')) ^ 2 ≤ v k)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∑ x : K → X, (∏ k, p k (x k)) *
        (if 2 * Real.sqrt ((∑ k, v k) * Λ) + 2 * c * Λ ≤ f x - ∑ x' : K → X, (∏ k, p k (x' k)) * f x'
          then 1 else 0) ≤ Real.exp (-Λ) := by
  set V := ∑ k, v k with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun k _ => hv k)
  set lam := 2 * Real.sqrt (V * Λ) + 2 * c * Λ with hlam
  by_cases hcase : c ^ 2 * Λ ≤ V
  · -- t = √(Λ/V)
    by_cases hVz : V = 0
    · have hΛ0 : Λ = 0 := by
        have : c ^ 2 * Λ ≤ 0 := by rw [← hVz]; exact hcase
        have hc2 : 0 < c ^ 2 := by positivity
        nlinarith
      have := ric_tail p hp0 hp1 f c v hrange hvar 0 lam le_rfl (by simp)
      simp only [zero_mul, neg_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Real.exp_zero] at this
      rw [hΛ0, neg_zero, Real.exp_zero]; exact this
    have hVp : 0 < V := lt_of_le_of_ne hV0 (Ne.symm hVz)
    set t := Real.sqrt (Λ / V) with ht
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have htc : t * c ≤ 1 := by
      have : t ^ 2 * c ^ 2 ≤ 1 := by
        rw [ht, Real.sq_sqrt (div_nonneg hΛ hV0)]
        rw [div_mul_eq_mul_div, div_le_one hVp]; nlinarith
      nlinarith [sq_nonneg (t * c - 1), mul_nonneg ht0 hc.le]
    have key := ric_tail p hp0 hp1 f c v hrange hvar t lam ht0 htc
    refine le_trans key (Real.exp_le_exp.mpr ?_)
    have h1 : t ^ 2 * V = Λ := by
      rw [ht, Real.sq_sqrt (div_nonneg hΛ hV0)]; field_simp
    have h2 : t * Real.sqrt (V * Λ) = Λ := by
      rw [ht, ← Real.sqrt_mul (div_nonneg hΛ hV0)]
      rw [show Λ / V * (V * Λ) = Λ ^ 2 by field_simp]
      exact Real.sqrt_sq hΛ
    have h3 : 0 ≤ t * (2 * c * Λ) := by positivity
    rw [hlam, mul_add, mul_comm t (2 * Real.sqrt (V * Λ)), mul_assoc, mul_comm (Real.sqrt _) t, h2]
    linarith
  · -- t = 1/c
    push_neg at hcase
    have key := ric_tail p hp0 hp1 f c v hrange hvar (1 / c) lam (by positivity)
      (by rw [div_mul_cancel₀ 1 hc.ne'])
    refine le_trans key (Real.exp_le_exp.mpr ?_)
    have hs : 0 ≤ Real.sqrt (V * Λ) := Real.sqrt_nonneg _
    rw [← hV]
    have e1 : (1 / c) * lam = 2 * Real.sqrt (V * Λ) / c + 2 * Λ := by
      rw [hlam]; field_simp
    have e2 : (1 / c) ^ 2 * V ≤ Λ := by
      rw [div_pow, one_pow, one_div_mul_eq_div, div_le_iff₀ (by positivity)]; linarith
    have e3 : 0 ≤ 2 * Real.sqrt (V * Λ) / c := by positivity
    linarith

/-- lower-tail deviation form -/
theorem ric_dev_lower {K X : Type} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]
    (p : K → X → ℝ) (hp0 : ∀ k y, 0 ≤ p k y) (hp1 : ∀ k, ∑ y, p k y = 1)
    (f : (K → X) → ℝ) (c : ℝ) (hc : 0 < c) (v : K → ℝ) (hv : ∀ k, 0 ≤ v k)
    (hrange : ∀ x k y y', |f (Function.update x k y) - f (Function.update x k y')| ≤ c)
    (hvar : ∀ x k, ∑ y, p k y * (f (Function.update x k y) -
        ∑ y', p k y' * f (Function.update x k y')) ^ 2 ≤ v k)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∑ x : K → X, (∏ k, p k (x k)) *
        (if f x ≤ (∑ x' : K → X, (∏ k, p k (x' k)) * f x') -
            (2 * Real.sqrt ((∑ k, v k) * Λ) + 2 * c * Λ) then 1 else 0) ≤ Real.exp (-Λ) := by
  have key := ric_dev p hp0 hp1 (fun x => -f x) c hc v hv
    (fun x k y y' => by rw [show -f (Function.update x k y) - -f (Function.update x k y') =
      -(f (Function.update x k y) - f (Function.update x k y')) by ring, abs_neg]; exact hrange x k y y')
    (fun x k => by
      have h := hvar x k
      have e : ∀ y, (-f (Function.update x k y) - ∑ y', p k y' * -f (Function.update x k y')) ^ 2 =
          (f (Function.update x k y) - ∑ y', p k y' * f (Function.update x k y')) ^ 2 := by
        intro y
        rw [show ∑ y', p k y' * -f (Function.update x k y') = -∑ y', p k y' * f (Function.update x k y') by
          rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun y' _ => by ring)]
        ring
      simp_rw [e]; exact h) Λ hΛ
  refine le_trans (le_of_eq ?_) key
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  have e : ∑ x' : K → X, (∏ k, p k (x' k)) * -f x' = -∑ x' : K → X, (∏ k, p k (x' k)) * f x' := by
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun y' _ => by ring)
  rw [e]
  congr 1
  apply propext
  constructor <;> intro h <;> linarith

end SecRIC

section SecTwoStage

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset

namespace TwoStage

variable {K X : Type} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]

/-- expectation under independent coordinates -/
noncomputable def wE (p : K → X → ℝ) (F : (K → X) → ℝ) : ℝ :=
  ∑ Z : K → X, (∏ k, p k (Z k)) * F Z

/-- conditional distribution: coordinates in `A` fixed to `a` -/
def condp (p : K → X → ℝ) (A : Finset K) (a : K → X) : K → X → ℝ :=
  fun k y => if k ∈ A then (if y = a k then 1 else 0) else p k y

theorem condp_nonneg (p : K → X → ℝ) (hp0 : ∀ k y, 0 ≤ p k y) (A : Finset K) (a : K → X) (k : K) (y : X) :
    0 ≤ condp p A a k y := by
  unfold condp; split_ifs
  · norm_num
  · norm_num
  · exact hp0 k y

theorem condp_sum (p : K → X → ℝ) (hp1 : ∀ k, ∑ y, p k y = 1) (A : Finset K) (a : K → X) (k : K) :
    ∑ y, condp p A a k y = 1 := by
  unfold condp; split_ifs
  · simp
  · exact hp1 k

/-- tower property -/
theorem tower (p : K → X → ℝ) (A : Finset K) (x₀ : X) (F : (K → X) → ℝ) :
    wE p F = ∑ a : K → X, (∏ k, (if k ∈ A then p k (a k) else (if a k = x₀ then 1 else 0))) *
      wE (condp p A a) F := by
  unfold wE
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun Z _ => ?_)
  have e : ∀ a : K → X, (∏ k, (if k ∈ A then p k (a k) else (if a k = x₀ then (1 : ℝ) else 0))) *
      ((∏ k, condp p A a k (Z k)) * F Z) =
      (∏ k, ((if k ∈ A then p k (a k) else (if a k = x₀ then 1 else 0)) *
        (if k ∈ A then (if Z k = a k then 1 else 0) else p k (Z k)))) * F Z := by
    intro a
    rw [Finset.prod_mul_distrib]; simp only [condp]; ring
  simp_rw [e]
  rw [← Finset.sum_mul]
  congr 1
  rw [← Fintype.prod_sum (fun k y => (if k ∈ A then p k y else (if y = x₀ then 1 else 0)) *
    (if k ∈ A then (if Z k = y then 1 else 0) else p k (Z k)))]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  by_cases hk : k ∈ A
  · simp only [hk, if_true]
    rw [Finset.sum_eq_single (Z k)]
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb), mul_zero]
    · simp
  · simp only [hk, if_false]
    rw [Finset.sum_eq_single x₀]
    · simp
    · intro b _ hb; rw [if_neg hb, zero_mul]
    · simp

/-- the conditional expectation only depends on the conditioning coordinates -/
theorem cond_congr (p : K → X → ℝ) (A : Finset K) (a a' : K → X) (h : ∀ k ∈ A, a k = a' k)
    (F : (K → X) → ℝ) : wE (condp p A a) F = wE (condp p A a') F := by
  unfold wE condp
  refine Finset.sum_congr rfl (fun Z _ => ?_)
  congr 1
  refine Finset.prod_congr rfl (fun k _ => ?_)
  by_cases hk : k ∈ A
  · simp [hk, h k hk]
  · simp [hk]

/-- under the conditional distribution, functions agreeing on the fibre have the same expectation -/
theorem cond_fibre (p : K → X → ℝ) (A : Finset K) (a : K → X) (F G : (K → X) → ℝ)
    (h : ∀ Z : K → X, (∀ k ∈ A, Z k = a k) → F Z = G Z) :
    wE (condp p A a) F = wE (condp p A a) G := by
  unfold wE
  refine Finset.sum_congr rfl (fun Z _ => ?_)
  by_cases hZ : ∀ k ∈ A, Z k = a k
  · rw [h Z hZ]
  · push_neg at hZ
    obtain ⟨k, hk, hne⟩ := hZ
    have : ∏ k, condp p A a k (Z k) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (by simp [condp, hk, hne])
    rw [this, zero_mul, zero_mul]

theorem wE_mono (p : K → X → ℝ) (hp0 : ∀ k y, 0 ≤ p k y) (F G : (K → X) → ℝ)
    (h : ∀ Z, F Z ≤ G Z) : wE p F ≤ wE p G :=
  Finset.sum_le_sum (fun Z _ => mul_le_mul_of_nonneg_left (h Z)
    (Finset.prod_nonneg (fun k _ => hp0 k _)))

theorem wE_add (p : K → X → ℝ) (F G : (K → X) → ℝ) :
    wE p (fun Z => F Z + G Z) = wE p F + wE p G := by
  unfold wE; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun Z _ => by ring)

theorem wE_const (p : K → X → ℝ) (hp1 : ∀ k, ∑ y, p k y = 1) (c : ℝ) :
    wE p (fun _ => c) = c := by
  unfold wE
  rw [← Finset.sum_mul, ← Fintype.prod_sum]
  simp [hp1]

theorem E_cond_eq (p : K → X → ℝ) (hp1 : ∀ k, ∑ y, p k y = 1) (A : Finset K) (x₀ : X)
    (Q : (K → X) → ℝ) : wE p (fun Z => wE (condp p A Z) Q) = wE p Q := by
  rw [tower p A x₀ Q, tower p A x₀ (fun Z => wE (condp p A Z) Q)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  rw [cond_fibre p A a (fun Z => wE (condp p A Z) Q) (fun _ => wE (condp p A a) Q)]
  · rw [wE_const _ (condp_sum p hp1 A a)]
  · intro Z hZ
    exact cond_congr p A Z a hZ Q

/-- **two-stage lower tail** -/
theorem two_stage_lower (p : K → X → ℝ) (hp0 : ∀ k y, 0 ≤ p k y) (hp1 : ∀ k, ∑ y, p k y = 1)
    (A : Finset K) (x₀ : X) (Q : (K → X) → ℝ) (lam1 lam2 rho1 rho2 : ℝ)
    (H1 : ∀ a : K → X, wE (condp p A a)
      (fun Z => if Q Z ≤ wE (condp p A a) Q - lam1 then 1 else 0) ≤ rho1)
    (H2 : wE p (fun Z => if wE (condp p A Z) Q ≤ wE p Q - lam2 then 1 else 0) ≤ rho2) :
    wE p (fun Z => if Q Z ≤ wE p Q - (lam1 + lam2) then 1 else 0) ≤ rho1 + rho2 := by
  set h : (K → X) → ℝ := fun Z => wE (condp p A Z) Q with hh
  have hpt : ∀ Z, (if Q Z ≤ wE p Q - (lam1 + lam2) then (1 : ℝ) else 0) ≤
      (if h Z ≤ wE p Q - lam2 then 1 else 0) + (if Q Z ≤ h Z - lam1 then 1 else 0) := by
    intro Z
    by_cases h1 : Q Z ≤ wE p Q - (lam1 + lam2)
    · rw [if_pos h1]
      by_cases h2 : h Z ≤ wE p Q - lam2
      · rw [if_pos h2]; split_ifs <;> norm_num
      · rw [if_neg h2, if_pos (by push_neg at h2; linarith)]; norm_num
    · rw [if_neg h1]; split_ifs <;> norm_num
  refine le_trans (wE_mono p hp0 _ _ hpt) ?_
  rw [wE_add]
  have hsecond : wE p (fun Z => if Q Z ≤ h Z - lam1 then (1 : ℝ) else 0) ≤ rho1 := by
    rw [tower p A x₀]
    have hw0 : ∀ a : K → X, 0 ≤ ∏ k, (if k ∈ A then p k (a k) else (if a k = x₀ then (1 : ℝ) else 0)) :=
      fun a => Finset.prod_nonneg (fun k _ => by
        split_ifs
        · exact hp0 k _
        · norm_num
        · norm_num)
    have hw1 : ∑ a : K → X, ∏ k, (if k ∈ A then p k (a k) else (if a k = x₀ then (1 : ℝ) else 0)) = 1 := by
      rw [← Fintype.prod_sum (fun k y => if k ∈ A then p k y else (if y = x₀ then (1 : ℝ) else 0))]
      refine Finset.prod_eq_one (fun k _ => ?_)
      by_cases hk : k ∈ A
      · simp [hk, hp1 k]
      · simp [hk]
    calc ∑ a : K → X, (∏ k, (if k ∈ A then p k (a k) else (if a k = x₀ then 1 else 0))) *
          wE (condp p A a) (fun Z => if Q Z ≤ h Z - lam1 then 1 else 0)
        ≤ ∑ a : K → X, (∏ k, (if k ∈ A then p k (a k) else (if a k = x₀ then 1 else 0))) * rho1 := by
          refine Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left ?_ (hw0 a))
          rw [cond_fibre p A a (fun Z => if Q Z ≤ h Z - lam1 then (1 : ℝ) else 0)
            (fun Z => if Q Z ≤ wE (condp p A a) Q - lam1 then 1 else 0)]
          · exact H1 a
          · intro Z hZ
            simp only [hh]
            rw [cond_congr p A Z a hZ]
      _ = rho1 := by rw [← Finset.sum_mul, hw1, one_mul]
  have hEh : wE p h = wE p Q := by
    rw [tower p A x₀ Q, tower p A x₀ h]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [cond_fibre p A a h (fun _ => h a)]
    · rw [wE_const _ (condp_sum p hp1 A a)]
    · intro Z hZ
      simp only [hh]
      exact cond_congr p A Z a hZ Q
  have hfirst : wE p (fun Z => if h Z ≤ wE p Q - lam2 then (1 : ℝ) else 0) ≤ rho2 := H2
  linarith

end TwoStage

end SecTwoStage

section SecCond

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset

namespace TwoStage

variable {K X : Type} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]

/-- coordinates in `S` from `a`, the rest from `Z` -/
def merge (S : Finset K) (a Z : K → X) : K → X := fun k => if k ∈ S then a k else Z k

/-- conditional expectation as an average over the free coordinates -/
theorem cond_as_free (p : K → X → ℝ) (S : Finset K) (a : K → X) (x₀ : X) (Q : (K → X) → ℝ) :
    wE (condp p S a) Q = wE (condp p S (fun _ => x₀)) (fun Z => Q (merge S a Z)) := by
  unfold wE
  symm
  refine Finset.sum_bij_ne_zero (fun Z _ _ => merge S a Z) ?_ ?_ ?_ ?_
  · intro Z _ _; exact Finset.mem_univ _
  · intro Z1 _ h1 Z2 _ h2 heq
    have hS : ∀ Z : K → X, (∏ k, condp p S (fun _ => x₀) k (Z k)) * Q (merge S a Z) ≠ 0 →
        ∀ k ∈ S, Z k = x₀ := by
      intro Z hZ k hk
      by_contra hne
      apply hZ
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [condp, hk, hne]), zero_mul]
    funext k
    by_cases hk : k ∈ S
    · rw [hS Z1 h1 k hk, hS Z2 h2 k hk]
    · have := congrFun heq k
      simp only [merge, hk, if_false] at this
      exact this
  · intro Z' _ hZ'
    have hS : ∀ k ∈ S, Z' k = a k := by
      intro k hk
      by_contra hne
      apply hZ'
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [condp, hk, hne]), zero_mul]
    refine ⟨fun k => if k ∈ S then x₀ else Z' k, Finset.mem_univ _, ?_, ?_⟩
    · have hm : merge S a (fun k => if k ∈ S then x₀ else Z' k) = Z' := by
        funext k; by_cases hk : k ∈ S
        · simp [merge, hk, hS k hk]
        · simp [merge, hk]
      show (∏ k, condp p S (fun _ => x₀) k (if k ∈ S then x₀ else Z' k)) *
        Q (merge S a (fun k => if k ∈ S then x₀ else Z' k)) ≠ 0
      rw [hm]
      have hw : ∏ k, condp p S (fun _ => x₀) k (if k ∈ S then x₀ else Z' k) = ∏ k, condp p S a k (Z' k) := by
        refine Finset.prod_congr rfl (fun k _ => ?_)
        by_cases hk : k ∈ S
        · simp [condp, hk, hS k hk]
        · simp [condp, hk]
      rw [hw]; exact hZ'
    · funext k; by_cases hk : k ∈ S
      · simp [merge, hk, hS k hk]
      · simp [merge, hk]
  · intro Z _ hZ
    congr 1
    refine Finset.prod_congr rfl (fun k _ => ?_)
    by_cases hk : k ∈ S
    · have : Z k = x₀ := by
        by_contra hne
        apply hZ
        rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [condp, hk, hne]), zero_mul]
      simp [condp, merge, hk, this]
    · simp [condp, merge, hk]

theorem condp_free_nonneg (p : K → X → ℝ) (hp0 : ∀ k y, 0 ≤ p k y) (S : Finset K) (x₀ : X) :
    ∀ k y, 0 ≤ condp p S (fun _ => x₀) k y := fun k y => condp_nonneg p hp0 S _ k y

theorem condp_free_sum (p : K → X → ℝ) (hp1 : ∀ k, ∑ y, p k y = 1) (S : Finset K) (x₀ : X) :
    ∀ k, ∑ y, condp p S (fun _ => x₀) k y = 1 := fun k => condp_sum p hp1 S _ k

/-- influence of an `S`-coordinate on the conditional expectation -/
theorem cond_infl (p : K → X → ℝ) (hp0 : ∀ k y, 0 ≤ p k y) (hp1 : ∀ k, ∑ y, p k y = 1)
    (S : Finset K) (x₀ : X) (Q : (K → X) → ℝ) (a a' : K → X) (B : ℝ)
    (hB : ∀ Z, |Q (merge S a Z) - Q (merge S a' Z)| ≤ B) :
    |wE (condp p S a) Q - wE (condp p S a') Q| ≤ B := by
  rw [cond_as_free p S a x₀, cond_as_free p S a' x₀]
  unfold wE
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hw0 : ∀ Z : K → X, 0 ≤ ∏ k, condp p S (fun _ => x₀) k (Z k) :=
    fun Z => Finset.prod_nonneg (fun k _ => condp_nonneg p hp0 S _ k _)
  calc ∑ Z : K → X, |(∏ k, condp p S (fun _ => x₀) k (Z k)) * Q (merge S a Z) -
        (∏ k, condp p S (fun _ => x₀) k (Z k)) * Q (merge S a' Z)|
      ≤ ∑ Z : K → X, (∏ k, condp p S (fun _ => x₀) k (Z k)) * B := by
        refine Finset.sum_le_sum (fun Z _ => ?_)
        rw [← mul_sub, abs_mul, abs_of_nonneg (hw0 Z)]
        exact mul_le_mul_of_nonneg_left (hB Z) (hw0 Z)
    _ = B := by
        rw [← Finset.sum_mul]
        have := wE_const (condp p S (fun _ => x₀)) (condp_sum p hp1 S _) 1
        unfold wE at this; simp only [mul_one] at this
        rw [this, one_mul]

end TwoStage

end SecCond

section SecOneStage

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset

namespace OneStage

variable {K X : Type} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]

theorem var_le_dev (p : X → ℝ) (hp0 : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1) (F : X → ℝ) (a : ℝ) :
    ∑ y, p y * (F y - ∑ y', p y' * F y') ^ 2 ≤ ∑ y, p y * (F y - a) ^ 2 := by
  set m := ∑ y', p y' * F y'
  have e : ∑ y, p y * (F y - a) ^ 2 = ∑ y, p y * (F y - m) ^ 2 + (m - a) ^ 2 := by
    have e1 : ∀ y, p y * (F y - a) ^ 2 = p y * (F y - m) ^ 2 + 2 * (m - a) * (p y * F y) -
        2 * (m - a) * m * p y + (m - a) ^ 2 * p y := fun y => by ring
    simp_rw [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp1]
    ring
  rw [e]; nlinarith [sq_nonneg (m - a)]

/-- generic deviation bound from influence relative to a reference value `y₀` -/
theorem dev_of_infl (p : K → X → ℝ) (hp0 : ∀ k y, 0 ≤ p k y) (hp1 : ∀ k, ∑ y, p k y = 1)
    (f : (K → X) → ℝ) (y₀ : X) (D : K → X → ℝ) (c : ℝ) (hc : 0 < c)
    (hD : ∀ Z k y, |f (Function.update Z k y) - f (Function.update Z k y₀)| ≤ D k y)
    (hDc : ∀ k y, 2 * D k y ≤ c) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    (∑ Z : K → X, (∏ k, p k (Z k)) *
        (if 2 * Real.sqrt ((∑ k, ∑ y, p k y * D k y ^ 2) * Λ) + 2 * c * Λ ≤
          f Z - ∑ Z' : K → X, (∏ k, p k (Z' k)) * f Z' then 1 else 0) ≤ Real.exp (-Λ)) ∧
    (∑ Z : K → X, (∏ k, p k (Z k)) *
        (if f Z ≤ (∑ Z' : K → X, (∏ k, p k (Z' k)) * f Z') -
          (2 * Real.sqrt ((∑ k, ∑ y, p k y * D k y ^ 2) * Λ) + 2 * c * Λ) then 1 else 0) ≤
          Real.exp (-Λ)) := by
  have hrange : ∀ Z k y y', |f (Function.update Z k y) - f (Function.update Z k y')| ≤ c := by
    intro Z k y y'
    have h1 := hD Z k y
    have h2 := hD Z k y'
    have h3 := hDc k y
    have h4 := hDc k y'
    calc |f (Function.update Z k y) - f (Function.update Z k y')|
        = |(f (Function.update Z k y) - f (Function.update Z k y₀)) -
            (f (Function.update Z k y') - f (Function.update Z k y₀))| := by ring_nf
      _ ≤ |f (Function.update Z k y) - f (Function.update Z k y₀)| +
          |f (Function.update Z k y') - f (Function.update Z k y₀)| := abs_sub _ _
      _ ≤ c := by linarith
  have hvar : ∀ Z k, ∑ y, p k y * (f (Function.update Z k y) -
      ∑ y', p k y' * f (Function.update Z k y')) ^ 2 ≤ ∑ y, p k y * D k y ^ 2 := by
    intro Z k
    refine le_trans (var_le_dev (p k) (hp0 k) (hp1 k) (fun y => f (Function.update Z k y))
      (f (Function.update Z k y₀))) ?_
    refine Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left ?_ (hp0 k y))
    have := hD Z k y
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hv : ∀ k, 0 ≤ ∑ y, p k y * D k y ^ 2 :=
    fun k => Finset.sum_nonneg (fun y _ => mul_nonneg (hp0 k y) (sq_nonneg _))
  exact ⟨ric_dev p hp0 hp1 f c hc _ hv hrange hvar Λ hΛ,
    ric_dev_lower p hp0 hp1 f c hc _ hv hrange hvar Λ hΛ⟩

end OneStage

end SecOneStage

section SecBounds

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset

namespace Nib

variable {J Sl O : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
  [Fintype O] [DecidableEq O] {H : HG J Sl O}

/-- job-slot weight -/
noncomputable def yw (H : HG J Sl O) (x : O → ℝ) (e : J) (t : Sl) : ℝ :=
  ∑ o ∈ univ.filter (fun o => H.job o = e ∧ t ∈ H.sl o), x o

/-- slot-pair weight -/
noncomputable def kw (H : HG J Sl O) (x : O → ℝ) (s t : Sl) : ℝ :=
  ∑ o ∈ univ.filter (fun o => s ∈ H.sl o ∧ t ∈ H.sl o), x o

/-- the round invariants -/
structure Inv (H : HG J Sl O) (σ δ κ : ℝ) (x : O → ℝ) : Prop where
  x0 : ∀ o, 0 ≤ x o
  mass : ∀ e, mass H x e = 0 ∨ (1 - δ ≤ mass H x e ∧ mass H x e ≤ 1 + δ)
  load : ∀ s, load H x s ≤ 1 - σ / 2
  cod1 : ∀ e t, yw H x e t ≤ κ
  cod2 : ∀ s t, s ≠ t → kw H x s t ≤ κ

theorem weierstrass {α : Type} (s : Finset α) (u : α → ℝ) (h0 : ∀ i ∈ s, 0 ≤ u i)
    (h1 : ∀ i ∈ s, u i ≤ 1) : 1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 - u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hP : 0 ≤ ∏ i ∈ s, (1 - u i) := Finset.prod_nonneg (fun i hi => by
      linarith [h1 i (Finset.mem_insert_of_mem hi)])
    have hua := h0 a (Finset.mem_insert_self a s)
    have hu1 := h1 a (Finset.mem_insert_self a s)
    have hs : 0 ≤ ∑ i ∈ s, u i := Finset.sum_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    nlinarith

theorem aff_le_sum (x : O → ℝ) (hx : ∀ o, 0 ≤ x o) (f : J) (T : Finset Sl) :
    aff H x f T ≤ ∑ t ∈ T, yw H x f t := by
  unfold aff yw
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun o _ => ?_)
  by_cases h : H.job o = f ∧ ¬Disjoint (H.sl o) T
  · rw [if_pos h]
    obtain ⟨t, ht1, ht2⟩ := Finset.not_disjoint_iff.mp h.2
    have := Finset.single_le_sum (f := fun t => if H.job o = f ∧ t ∈ H.sl o then x o else 0)
      (fun t _ => by split_ifs; exact hx o; exact le_rfl) ht2
    simpa [h.1, ht1] using this
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun t _ => by split_ifs; exact hx o; exact le_rfl)

theorem sum_yw (x : O → ℝ) (t : Sl) : ∑ f, yw H x f t = load H x t := by
  unfold yw load
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun o _ => ?_)
  by_cases h : t ∈ H.sl o
  · simp [h]
  · simp [h]

theorem sum_aff_le (x : O → ℝ) (hx : ∀ o, 0 ≤ x o) (T : Finset Sl) (A : Finset J) :
    ∑ f ∈ A, aff H x f T ≤ ∑ t ∈ T, load H x t := by
  calc ∑ f ∈ A, aff H x f T ≤ ∑ f, aff H x f T :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun f _ _ => Finset.sum_nonneg (fun o _ => hx o))
    _ ≤ ∑ f, ∑ t ∈ T, yw H x f t := Finset.sum_le_sum (fun f _ => aff_le_sum x hx f T)
    _ = ∑ t ∈ T, load H x t := by rw [Finset.sum_comm]; simp_rw [sum_yw]

theorem aff_nonneg (x : O → ℝ) (hx : ∀ o, 0 ≤ x o) (f : J) (T : Finset Sl) : 0 ≤ aff H x f T :=
  Finset.sum_nonneg (fun o _ => hx o)

theorem aff_le_card (σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (f : J) (T : Finset Sl) :
    aff H x f T ≤ T.card * κ := by
  refine le_trans (aff_le_sum x hI.x0 f T) ?_
  calc ∑ t ∈ T, yw H x f t ≤ ∑ _t ∈ T, κ := Finset.sum_le_sum (fun t _ => hI.cod1 f t)
    _ = T.card * κ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- bounds on the survival factor -/
theorem piF_bounds (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ : κ ≤ 1) (hσ : 0 ≤ σ) (o : O) :
    1 - 2 * θ ≤ piF H θ x o ∧ piF H θ x o ≤ 1 := by
  have hu0 : ∀ f, 0 ≤ θ * aff H x f (H.sl o) := fun f => mul_nonneg hθ0 (aff_nonneg x hI.x0 f _)
  have hu1 : ∀ f, θ * aff H x f (H.sl o) ≤ 1 := by
    intro f
    have h1 := aff_le_card σ δ κ x hI f (H.sl o)
    have h2 : ((H.sl o).card : ℝ) ≤ 2 := by exact_mod_cast hsl o
    have : aff H x f (H.sl o) ≤ 2 := by nlinarith [le_trans (aff_nonneg x hI.x0 f (H.sl o)) h1]
    nlinarith
  constructor
  · refine le_trans ?_ (weierstrass _ _ (fun f _ => hu0 f) (fun f _ => hu1 f))
    have hs := sum_aff_le (H := H) x hI.x0 (H.sl o) (univ.erase (H.job o))
    have hl : ∑ t ∈ H.sl o, load H x t ≤ 2 := by
      calc ∑ t ∈ H.sl o, load H x t ≤ ∑ _t ∈ H.sl o, (1 : ℝ) :=
            Finset.sum_le_sum (fun t _ => by linarith [hI.load t])
        _ ≤ 2 := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast hsl o
    rw [← Finset.mul_sum]
    nlinarith
  · exact Finset.prod_le_one (fun f _ => by linarith [hu1 f]) (fun f _ => by linarith [hu0 f])

end Nib

end SecBounds

section SecMass

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset

namespace Nib

variable {J Sl O : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
  [Fintype O] [DecidableEq O] {H : HG J Sl O}

/-- the mass functional -/
noncomputable def Mf (H : HG J Sl O) (θ : ℝ) (x : O → ℝ) (e : J) (Z : J → Option O) : ℝ :=
  ∑ o ∈ univ.filter (fun o => H.job o = e),
    (x o / piF H θ x o) * ∏ f ∈ univ.erase e, av H f (H.sl o) (Z f)

theorem EE_Mf (θ : ℝ) (x : O → ℝ) (e : J) (hpi : ∀ o, 0 < piF H θ x o) :
    EE H θ x (Mf H θ x e) = mass H x e := by
  unfold Mf
  rw [EE_finsum]
  unfold mass
  refine Finset.sum_congr rfl (fun o ho => ?_)
  have hj := (Finset.mem_filter.mp ho).2
  rw [EE_smul, EE_prod_erase]
  simp_rw [sum_pp_av]
  have : ∏ f ∈ univ.erase e, (1 - θ * aff H x f (H.sl o)) = piF H θ x o := by
    unfold piF; rw [hj]
  rw [this, div_mul_cancel₀ _ (hpi o).ne']

/-- the influence of job `k` on the mass functional of `e` -/
noncomputable def DM (H : HG J Sl O) (θ : ℝ) (x : O → ℝ) (e k : J) (y : Option O) : ℝ :=
  if k = e then 0 else
    (1 / (1 - 2 * θ)) * ∑ o ∈ univ.filter (fun o => H.job o = e), x o * (1 - av H k (H.sl o) y)

theorem prod_erase_split (e k : J) (hke : k ≠ e) (g : J → ℝ) :
    ∏ f ∈ univ.erase e, g f = g k * ∏ f ∈ (univ.erase e).erase k, g f :=
  (Finset.mul_prod_erase _ g (Finset.mem_erase.mpr ⟨hke, Finset.mem_univ k⟩)).symm

theorem Mf_infl (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ : κ ≤ 1) (hσ : 0 ≤ σ) (e : J)
    (Z : J → Option O) (k : J) (y : Option O) :
    |Mf H θ x e (Function.update Z k y) - Mf H θ x e (Function.update Z k none)| ≤ DM H θ x e k y := by
  unfold Mf DM
  by_cases hke : k = e
  · rw [if_pos hke]
    have : ∀ o, ∏ f ∈ univ.erase e, av H f (H.sl o) (Function.update Z k y f) =
        ∏ f ∈ univ.erase e, av H f (H.sl o) (Function.update Z k none f) := by
      intro o
      refine Finset.prod_congr rfl (fun f hf => ?_)
      have hfk : f ≠ k := by rw [hke]; exact Finset.ne_of_mem_erase hf
      simp [Function.update_of_ne hfk]
    simp_rw [this, sub_self, abs_zero]; exact le_rfl
  · rw [if_neg hke, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun o ho => ?_)
    have hpb := piF_bounds θ σ δ κ x hI hsl hθ0 hθ hκ hσ o
    have hpos : 0 < piF H θ x o := by linarith [hpb.1]
    rw [prod_erase_split e k hke, prod_erase_split e k hke]
    simp only [Function.update_self]
    have hrest : ∀ f ∈ (univ.erase e).erase k,
        av H f (H.sl o) (Function.update Z k y f) = av H f (H.sl o) (Function.update Z k none f) := by
      intro f hf
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hf)]
    rw [Finset.prod_congr rfl hrest]
    set P := ∏ f ∈ (univ.erase e).erase k, av H f (H.sl o) (Function.update Z k none f)
    have hP0 : 0 ≤ P := Finset.prod_nonneg (fun f _ => av_nonneg _ _ _)
    have hP1 : P ≤ 1 := Finset.prod_le_one (fun f _ => av_nonneg _ _ _) (fun f _ => av_le_one _ _ _)
    have hnone : av H k (H.sl o) none = 1 := rfl
    rw [hnone]
    have ha0 := av_nonneg (H := H) k (H.sl o) y
    have ha1 := av_le_one (H := H) k (H.sl o) y
    have hx := hI.x0 o
    rw [show x o / piF H θ x o * (av H k (H.sl o) y * P) - x o / piF H θ x o * (1 * P) =
      -(x o / piF H θ x o * P * (1 - av H k (H.sl o) y)) by ring, abs_neg]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (div_nonneg hx hpos.le) hP0) (by linarith))]
    have h1 : x o / piF H θ x o ≤ x o * (1 / (1 - 2 * θ)) := by
      rw [div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ hx
      apply one_div_le_one_div_of_le (by linarith) hpb.1
    have h2 : 0 ≤ 1 - av H k (H.sl o) y := by linarith
    calc x o / piF H θ x o * P * (1 - av H k (H.sl o) y)
        ≤ x o * (1 / (1 - 2 * θ)) * 1 * (1 - av H k (H.sl o) y) := by
          apply mul_le_mul_of_nonneg_right _ h2
          exact mul_le_mul h1 hP1 hP0 (mul_nonneg hx (one_div_nonneg.mpr (by linarith)))
      _ = 1 / (1 - 2 * θ) * (x o * (1 - av H k (H.sl o) y)) := by ring

theorem sum_x_sl (x : O → ℝ) (F : Sl → ℝ) :
    ∑ o, x o * ∑ t ∈ H.sl o, F t = ∑ t, load H x t * F t := by
  unfold load
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun a _ => ⟨a.2, a.1⟩) (fun a _ => ⟨a.2, a.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_filter] at ha ⊢; exact ha
  · intro a ha; simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_filter] at ha ⊢; exact ha
  · intro a _; rfl
  · intro a _; rfl
  · intro a _; ring

theorem sum_yw_le (x : O → ℝ) (hx : ∀ o, 0 ≤ x o) (hsl : ∀ o, (H.sl o).card ≤ 2) (e : J) :
    ∑ t, yw H x e t ≤ 2 * mass H x e := by
  unfold yw mass
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun o _ => ?_)
  by_cases hj : H.job o = e
  · simp only [hj, true_and, if_true]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : ((univ.filter (fun t => t ∈ H.sl o)).card : ℝ) ≤ 2 := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]; exact_mod_cast hsl o
    nlinarith [hx o]
  · simp [hj]

theorem DM_some (θ : ℝ) (x : O → ℝ) (e k : J) (hke : k ≠ e) (o' : O) :
    DM H θ x e k (some o') = if H.job o' = k then (1 / (1 - 2 * θ)) * aff H x e (H.sl o') else 0 := by
  unfold DM aff
  rw [if_neg hke]
  by_cases hk : H.job o' = k
  · rw [if_pos hk]
    congr 1
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    simp only [av, hk, true_and]
    by_cases hj : H.job o = e
    · by_cases hd : Disjoint (H.sl o') (H.sl o)
      · have : Disjoint (H.sl o) (H.sl o') := hd.symm
        simp [hj, hd, this]
      · have : ¬Disjoint (H.sl o) (H.sl o') := fun h => hd h.symm
        simp [hj, hd, this]
    · simp [hj]
  · rw [if_neg hk]
    simp [av, hk]

theorem DM_none (θ : ℝ) (x : O → ℝ) (e k : J) : DM H θ x e k none = 0 := by
  unfold DM; split_ifs <;> simp [av]

theorem DM_le (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ0 : 0 ≤ κ) (e k : J) (y : Option O) :
    2 * DM H θ x e k y ≤ 4 * κ / (1 - 2 * θ) := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  have hr : 0 ≤ 4 * κ / (1 - 2 * θ) := by positivity
  cases y with
  | none => rw [DM_none, mul_zero]; exact hr
  | some o' =>
    by_cases hke : k = e
    · unfold DM; rw [if_pos hke, mul_zero]; exact hr
    · rw [DM_some θ x e k hke]
      split_ifs
      · have h1 := aff_le_card σ δ κ x hI e (H.sl o')
        have h2 : ((H.sl o').card : ℝ) ≤ 2 := by exact_mod_cast hsl o'
        have h3 : aff H x e (H.sl o') ≤ 2 * κ := by nlinarith
        rw [show 4 * κ / (1 - 2 * θ) = 2 * (1 / (1 - 2 * θ) * (2 * κ)) by ring]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      · rw [mul_zero]; exact hr

theorem V_Mf (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hσ : 0 ≤ σ) (hκ0 : 0 ≤ κ) (e : J) :
    ∑ k, ∑ y, pp H θ x k y * DM H θ x e k y ^ 2 ≤
      4 * θ * κ * mass H x e / (1 - 2 * θ) ^ 2 := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  -- rewrite the inner sums over options
  have hk : ∀ k, ∑ y, pp H θ x k y * DM H θ x e k y ^ 2 =
      ∑ o', (if H.job o' = k ∧ k ≠ e then θ * x o' * ((1 / (1 - 2 * θ)) * aff H x e (H.sl o')) ^ 2 else 0) := by
    intro k
    rw [Fintype.sum_option, DM_none]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
    refine Finset.sum_congr rfl (fun o' _ => ?_)
    by_cases hke : k = e
    · unfold DM; rw [if_pos hke]; simp [hke]
    · rw [DM_some θ x e k hke]
      by_cases hj : H.job o' = k
      · simp [pp, hj, hke]; try ring
      · simp [pp, hj]
  simp_rw [hk]
  rw [Finset.sum_comm]
  have hstep : ∀ o', ∑ k, (if H.job o' = k ∧ k ≠ e then θ * x o' * ((1 / (1 - 2 * θ)) * aff H x e (H.sl o')) ^ 2 else 0) ≤
      θ / (1 - 2 * θ) ^ 2 * (x o' * (2 * ∑ t ∈ H.sl o', yw H x e t ^ 2)) := by
    intro o'
    rw [Finset.sum_eq_single (H.job o')]
    · split_ifs with h
      · have haff := aff_le_sum (H := H) x hI.x0 e (H.sl o')
        have haff0 := aff_nonneg (H := H) x hI.x0 e (H.sl o')
        have hcs : (∑ t ∈ H.sl o', yw H x e t) ^ 2 ≤ 2 * ∑ t ∈ H.sl o', yw H x e t ^ 2 := by
          have := sq_sum_le_card_mul_sum_sq (s := H.sl o') (f := fun t => yw H x e t)
          have h2 : ((H.sl o').card : ℝ) ≤ 2 := by exact_mod_cast hsl o'
          have h3 : 0 ≤ ∑ t ∈ H.sl o', yw H x e t ^ 2 := Finset.sum_nonneg (fun t _ => sq_nonneg _)
          nlinarith
        have hsq : aff H x e (H.sl o') ^ 2 ≤ 2 * ∑ t ∈ H.sl o', yw H x e t ^ 2 :=
          le_trans (pow_le_pow_left₀ haff0 haff 2) hcs
        have hx := hI.x0 o'
        calc θ * x o' * (1 / (1 - 2 * θ) * aff H x e (H.sl o')) ^ 2
            = θ / (1 - 2 * θ) ^ 2 * (x o' * aff H x e (H.sl o') ^ 2) := by field_simp
          _ ≤ θ / (1 - 2 * θ) ^ 2 * (x o' * (2 * ∑ t ∈ H.sl o', yw H x e t ^ 2)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left hsq hx
      · have : 0 ≤ ∑ t ∈ H.sl o', yw H x e t ^ 2 := Finset.sum_nonneg (fun t _ => sq_nonneg _)
        have := hI.x0 o'
        positivity
    · intro k _ hk
      rw [if_neg (fun h => hk h.1.symm)]
    · simp
  refine le_trans (Finset.sum_le_sum (fun o' _ => hstep o')) ?_
  rw [← Finset.mul_sum]
  simp_rw [mul_left_comm (x _) 2, ← Finset.mul_sum]
  rw [sum_x_sl x (fun t => yw H x e t ^ 2)]
  have hload : ∑ t, load H x t * yw H x e t ^ 2 ≤ κ * ∑ t, yw H x e t := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun t _ => ?_)
    have hl := hI.load t
    have hy0 : 0 ≤ yw H x e t := Finset.sum_nonneg (fun o _ => hI.x0 o)
    have hy := hI.cod1 e t
    have hl0 : 0 ≤ load H x t := Finset.sum_nonneg (fun o _ => hI.x0 o)
    nlinarith [mul_le_mul_of_nonneg_left hy hy0]
  have hsum := sum_yw_le (H := H) x hI.x0 hsl e
  have hm0 : 0 ≤ mass H x e := Finset.sum_nonneg (fun o _ => hI.x0 o)
  have hc : 0 ≤ θ / (1 - 2 * θ) ^ 2 := by positivity
  calc θ / (1 - 2 * θ) ^ 2 * (2 * ∑ t, load H x t * yw H x e t ^ 2)
      ≤ θ / (1 - 2 * θ) ^ 2 * (2 * (κ * (2 * mass H x e))) := by
        apply mul_le_mul_of_nonneg_left _ hc
        nlinarith
    _ = 4 * θ * κ * mass H x e / (1 - 2 * θ) ^ 2 := by ring

end Nib

end SecMass

section SecNext

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset

namespace Nib

variable {J Sl O : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
  [Fintype O] [DecidableEq O] {H : HG J Sl O}

/-- valid picks: every pick is an option of the picking job -/
def Valid (H : HG J Sl O) (Z : J → Option O) : Prop := ∀ e o, Z e = some o → H.job o = e

theorem prod_av_mem01 (T : J → Finset Sl) (Z : J → Option O) (s : Finset J) :
    (∏ f ∈ s, av H f (T f) (Z f) = 0) ∨ (∏ f ∈ s, av H f (T f) (Z f) = 1) := by
  classical
  by_cases h : ∀ f ∈ s, av H f (T f) (Z f) = 1
  · right; exact Finset.prod_eq_one h
  · left
    push_neg at h
    obtain ⟨f, hf, hne⟩ := h
    refine Finset.prod_eq_zero hf ?_
    cases hZ : Z f with
    | none => rw [hZ] at hne; simp [av] at hne
    | some o => rw [hZ] at hne; simp only [av] at hne ⊢; split_ifs at hne ⊢ <;> simp_all

theorem win_eq (Z : J → Option O) (e : J) :
    win H Z e = match Z e with
      | none => 0
      | some o => if H.job o = e then ∏ f ∈ univ.erase e, av H f (H.sl o) (Z f) else 0 := by
  unfold win
  cases hZ : Z e with
  | none => simp
  | some o =>
    simp only
    by_cases hj : H.job o = e
    · rw [if_pos hj, Finset.sum_eq_single o]
      · simp
      · intro b hb hbo
        simp [Ne.symm hbo]
      · intro ho; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ o, hj⟩) ho
    · rw [if_neg hj]
      refine Finset.sum_eq_zero (fun b hb => ?_)
      have hb' := (Finset.mem_filter.mp hb).2
      have : b ≠ o := fun h => hj (h ▸ hb')
      simp [Ne.symm this]

theorem win_01 (Z : J → Option O) (e : J) : win H Z e = 0 ∨ win H Z e = 1 := by
  rw [win_eq]
  cases Z e with
  | none => left; rfl
  | some o =>
    simp only
    split_ifs
    · exact prod_av_mem01 (fun _ => H.sl o) Z _
    · left; rfl

theorem win_nonneg (Z : J → Option O) (e : J) : 0 ≤ win H Z e := by
  rcases win_01 (H := H) Z e with h | h <;> rw [h] <;> norm_num

theorem win_le_one (Z : J → Option O) (e : J) : win H Z e ≤ 1 := by
  rcases win_01 (H := H) Z e with h | h <;> rw [h] <;> norm_num

/-- winners pick slot-disjoint options -/
theorem win_disjoint (Z : J → Option O) (hZ : Valid H Z) (e e' : J) (hee : e ≠ e') (o o' : O)
    (ho : Z e = some o) (ho' : Z e' = some o') (hw : win H Z e = 1) :
    Disjoint (H.sl o) (H.sl o') := by
  rw [win_eq, ho] at hw
  simp only at hw
  have hj := hZ e o ho
  rw [if_pos hj] at hw
  have hmem : e' ∈ univ.erase e := Finset.mem_erase.mpr ⟨Ne.symm hee, Finset.mem_univ _⟩
  by_contra hd
  have h0 : av H e' (H.sl o) (Z e') = 0 := by
    rw [ho']; simp only [av]
    rw [if_pos ⟨hZ e' o' ho', fun h => hd h.symm⟩]
  rw [Finset.prod_eq_zero hmem h0] at hw
  norm_num at hw

/-- mass of a job after the round -/
theorem mass_nxt (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (Z : J → Option O)
    (hZ : Valid H Z) (e : J) :
    (win H Z e = 1 → mass H (nxt H θ x Z) e = 0) ∧
    (win H Z e = 0 → Mf H θ x e Z - 2 * κ / (1 - 2 * θ) ≤ mass H (nxt H θ x Z) e ∧
      mass H (nxt H θ x Z) e ≤ Mf H θ x e Z) := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  have hsplit : ∀ o, H.job o = e → nxt H θ x Z o =
      (x o / piF H θ x o * av H e (H.sl o) (Z e) * ∏ f ∈ univ.erase e, av H f (H.sl o) (Z f)) *
        (1 - win H Z e) := by
    intro o hj
    unfold nxt
    rw [hj, ← Finset.mul_prod_erase univ (fun f => av H f (H.sl o) (Z f)) (Finset.mem_univ e)]
    ring
  constructor
  · intro hw
    unfold mass
    refine Finset.sum_eq_zero (fun o ho => ?_)
    rw [hsplit o (Finset.mem_filter.mp ho).2, hw, sub_self, mul_zero]
  · intro hw
    have hm : mass H (nxt H θ x Z) e = ∑ o ∈ univ.filter (fun o => H.job o = e),
        x o / piF H θ x o * av H e (H.sl o) (Z e) * ∏ f ∈ univ.erase e, av H f (H.sl o) (Z f) := by
      unfold mass
      refine Finset.sum_congr rfl (fun o ho => ?_)
      rw [hsplit o (Finset.mem_filter.mp ho).2, hw, sub_zero, mul_one]
    rw [hm]
    unfold Mf
    constructor
    · -- lower bound: loss from e's own pick
      have hloss : ∀ o ∈ univ.filter (fun o => H.job o = e),
          x o / piF H θ x o * ∏ f ∈ univ.erase e, av H f (H.sl o) (Z f) -
            x o / piF H θ x o * av H e (H.sl o) (Z e) * ∏ f ∈ univ.erase e, av H f (H.sl o) (Z f) ≤
          (1 / (1 - 2 * θ)) * (x o * (1 - av H e (H.sl o) (Z e))) := by
        intro o _
        have hpb := piF_bounds θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ o
        have hpos : 0 < piF H θ x o := by linarith [hpb.1]
        set P := ∏ f ∈ univ.erase e, av H f (H.sl o) (Z f)
        have hP0 : 0 ≤ P := Finset.prod_nonneg (fun f _ => av_nonneg _ _ _)
        have hP1 : P ≤ 1 := Finset.prod_le_one (fun f _ => av_nonneg _ _ _) (fun f _ => av_le_one _ _ _)
        have ha0 := av_nonneg (H := H) e (H.sl o) (Z e)
        have ha1 := av_le_one (H := H) e (H.sl o) (Z e)
        have hx := hI.x0 o
        have h1 : x o / piF H θ x o ≤ x o * (1 / (1 - 2 * θ)) := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hπ hpb.1) hx
        have h2 : 0 ≤ x o / piF H θ x o := div_nonneg hx hpos.le
        nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ 1 - av H e (H.sl o) (Z e)),
          mul_nonneg h2 (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - av H e (H.sl o) (Z e)) (by linarith : (0:ℝ) ≤ 1 - P))]
      have htot : ∑ o ∈ univ.filter (fun o => H.job o = e), x o * (1 - av H e (H.sl o) (Z e)) ≤ 2 * κ := by
        cases hZe : Z e with
        | none => simp [av]; positivity
        | some o' =>
          have hj' := hZ e o' hZe
          have : ∑ o ∈ univ.filter (fun o => H.job o = e), x o * (1 - av H e (H.sl o) (some o')) =
              aff H x e (H.sl o') := by
            unfold aff
            rw [Finset.sum_filter, Finset.sum_filter]
            refine Finset.sum_congr rfl (fun o _ => ?_)
            by_cases hj : H.job o = e
            · simp only [hj, true_and, if_true, av, hj']
              by_cases hd : Disjoint (H.sl o') (H.sl o)
              · simp [hd, hd.symm]
              · have hd' : ¬Disjoint (H.sl o) (H.sl o') := fun h => hd h.symm
                simp [hd, hd']
            · simp [hj]
          rw [this]
          have h1 := aff_le_card σ δ κ x hI e (H.sl o')
          have h2 : ((H.sl o').card : ℝ) ≤ 2 := by exact_mod_cast hsl o'
          nlinarith
      have := Finset.sum_le_sum hloss
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
      have h3 : 1 / (1 - 2 * θ) * ∑ o ∈ univ.filter (fun o => H.job o = e), x o * (1 - av H e (H.sl o) (Z e)) ≤
          2 * κ / (1 - 2 * θ) := by
        rw [div_eq_mul_one_div (2 * κ), mul_comm (2 * κ)]
        exact mul_le_mul_of_nonneg_left htot (by positivity)
      linarith
    · refine Finset.sum_le_sum (fun o _ => ?_)
      have hpb := piF_bounds θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ o
      have h2 : 0 ≤ x o / piF H θ x o := div_nonneg (hI.x0 o) (by linarith [hpb.1])
      have hP0 : 0 ≤ ∏ f ∈ univ.erase e, av H f (H.sl o) (Z f) := Finset.prod_nonneg (fun f _ => av_nonneg _ _ _)
      have ha1 := av_le_one (H := H) e (H.sl o) (Z e)
      have ha0 := av_nonneg (H := H) e (H.sl o) (Z e)
      nlinarith [mul_le_mul_of_nonneg_left ha1 h2]

end Nib

end SecNext

section SecWins

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset

namespace Nib

variable {J Sl O : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
  [Fintype O] [DecidableEq O] {H : HG J Sl O}

/-- the slot set of a pick -/
def psl (H : HG J Sl O) : Option O → Finset Sl
  | none => ∅
  | some o => H.sl o

/-- updating another job's pick multiplies the win indicator by an avoidance factor -/
theorem win_upd (Z : J → Option O) (k e : J) (hke : k ≠ e) (y : Option O) :
    win H (Function.update Z k y) e = win H (Function.update Z k none) e * av H k (psl H (Z e)) y := by
  rw [win_eq, win_eq]
  simp only [Function.update_of_ne (Ne.symm hke)]
  cases hZ : Z e with
  | none => simp
  | some o =>
    simp only [psl]
    split_ifs with hj
    · have hk : k ∈ univ.erase e := Finset.mem_erase.mpr ⟨hke, Finset.mem_univ k⟩
      rw [← Finset.mul_prod_erase _ _ hk, ← Finset.mul_prod_erase _ _ hk]
      simp only [Function.update_self]
      have hr : ∏ f ∈ (univ.erase e).erase k, av H f (H.sl o) (Function.update Z k y f) =
          ∏ f ∈ (univ.erase e).erase k, av H f (H.sl o) (Function.update Z k none f) :=
        Finset.prod_congr rfl (fun f hf => by
          simp [Function.update_of_ne (Finset.ne_of_mem_erase hf)])
      rw [hr]
      simp only [av]
      ring
    · simp

theorem one_sub_av_le (k : J) (T : Finset Sl) (y : Option O) :
    1 - av H k T y ≤ ∑ t ∈ psl H y, (if t ∈ T then 1 else 0) := by
  cases y with
  | none => simp [av, psl]
  | some o =>
    simp only [av, psl]
    split_ifs with h
    · obtain ⟨t, ht1, ht2⟩ := Finset.not_disjoint_iff.mp h.2
      have := Finset.single_le_sum (f := fun t => if t ∈ T then (1 : ℝ) else 0)
        (fun t _ => by split_ifs <;> norm_num) ht1
      simp only [ht2, if_true] at this
      linarith
    · rw [sub_self]
      exact Finset.sum_nonneg (fun t _ => by split_ifs <;> norm_num)

/-- influence of one pick on a weighted sum of wins -/
theorem wsum_infl (Z : J → Option O) (k : J) (y : Option O) (S : Finset J) (c : J → ℝ)
    (hc0 : ∀ e, 0 ≤ c e) :
    |∑ e ∈ S, c e * win H (Function.update Z k y) e - ∑ e ∈ S, c e * win H (Function.update Z k none) e| ≤
      (if k ∈ S then c k else 0) +
        ∑ t ∈ psl H y, ∑ e ∈ S.filter (fun e => e ≠ k ∧ win H (Function.update Z k none) e = 1 ∧
          t ∈ psl H (Z e)), c e := by
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hpt : ∀ e ∈ S, |c e * win H (Function.update Z k y) e - c e * win H (Function.update Z k none) e| ≤
      (if e = k then c k else 0) +
        c e * win H (Function.update Z k none) e * ∑ t ∈ psl H y, (if t ∈ psl H (Z e) then 1 else 0) := by
    intro e he
    by_cases hek : e = k
    · subst hek
      rw [if_pos rfl]
      have h1 := win_nonneg (H := H) (Function.update Z e y) e
      have h2 := win_le_one (H := H) (Function.update Z e y) e
      have h3 : win H (Function.update Z e none) e = 0 := by
        rw [win_eq]; simp
      rw [h3, mul_zero, sub_zero, abs_of_nonneg (mul_nonneg (hc0 e) h1)]
      have h4 : 0 ≤ c e * 0 * ∑ t ∈ psl H y, (if t ∈ psl H (Z e) then (1 : ℝ) else 0) := by simp
      nlinarith [hc0 e]
    · rw [if_neg hek, zero_add, win_upd Z k e (Ne.symm hek) y]
      have hw0 := win_nonneg (H := H) (Function.update Z k none) e
      have ha0 := av_nonneg (H := H) k (psl H (Z e)) y
      have ha1 := av_le_one (H := H) k (psl H (Z e)) y
      rw [show c e * (win H (Function.update Z k none) e * av H k (psl H (Z e)) y) -
          c e * win H (Function.update Z k none) e =
          -(c e * win H (Function.update Z k none) e * (1 - av H k (psl H (Z e)) y)) by ring, abs_neg,
        abs_of_nonneg (mul_nonneg (mul_nonneg (hc0 e) hw0) (by linarith))]
      exact mul_le_mul_of_nonneg_left (one_sub_av_le k _ y) (mul_nonneg (hc0 e) hw0)
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_add_distrib]
  apply add_le_add
  · by_cases hk : k ∈ S
    · rw [if_pos hk, Finset.sum_ite_eq' S k (fun _ => c k), if_pos hk]
    · rw [if_neg hk]
      refine le_of_eq (Finset.sum_eq_zero (fun e he => ?_))
      rw [if_neg (fun h : e = k => hk (h ▸ he))]
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun t _ => ?_)
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun e _ => ?_)
    rcases win_01 (H := H) (Function.update Z k none) e with hw | hw
    · rw [hw]; simp only [mul_zero, zero_mul]; split_ifs <;> first | exact le_rfl | exact hc0 e
    · rw [hw, mul_one]
      by_cases hek : e = k
      · subst hek
        have : win H (Function.update Z e none) e = 0 := by rw [win_eq]; simp
        rw [this] at hw; norm_num at hw
      · by_cases ht : t ∈ psl H (Z e)
        · rw [if_pos ht, mul_one, if_pos ⟨hek, rfl, ht⟩]
        · rw [if_neg ht, mul_zero]; split_ifs <;> first | exact le_rfl | exact hc0 e

/-- winners have disjoint pick slots, so each slot carries at most one winner -/
theorem sum_winners_le (Z : J → Option O) (hZ : Valid H Z) (S : Finset J) (c : J → ℝ)
    (hc0 : ∀ e, 0 ≤ c e) (cm : ℝ) (hcm0 : 0 ≤ cm) (hcm : ∀ e, c e ≤ cm) (t : Sl) :
    ∑ e ∈ S.filter (fun e => win H Z e = 1 ∧ t ∈ psl H (Z e)), c e ≤ cm := by
  by_cases hne : (S.filter (fun e => win H Z e = 1 ∧ t ∈ psl H (Z e))).Nonempty
  · obtain ⟨e, he⟩ := hne
    have huniq : S.filter (fun e => win H Z e = 1 ∧ t ∈ psl H (Z e)) = {e} := by
      ext e'
      simp only [Finset.mem_singleton]
      constructor
      · intro he'
        by_contra hne'
        obtain ⟨_, hw, ht⟩ := Finset.mem_filter.mp he
        obtain ⟨_, hw', ht'⟩ := Finset.mem_filter.mp he'
        cases hZe : Z e with
        | none => rw [hZe] at ht; simp [psl] at ht
        | some o =>
          cases hZe' : Z e' with
          | none => rw [hZe'] at ht'; simp [psl] at ht'
          | some o' =>
            rw [hZe] at ht; rw [hZe'] at ht'
            simp only [psl] at ht ht'
            have := win_disjoint Z hZ e e' (Ne.symm hne') o o' hZe hZe' hw
            exact Finset.disjoint_left.mp this ht ht'
      · intro h; rw [h]; exact he
    rw [huniq, Finset.sum_singleton]; exact hcm e
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]; exact hcm0

/-- winners pick disjoint options (no validity assumption needed) -/
theorem win_disjoint' (Z : J → Option O) (e e' : J) (hee : e ≠ e') (o o' : O)
    (ho : Z e = some o) (ho' : Z e' = some o') (hw : win H Z e = 1) (hw' : win H Z e' = 1) :
    Disjoint (H.sl o) (H.sl o') := by
  have hj' : H.job o' = e' := by
    rw [win_eq, ho'] at hw'
    simp only at hw'
    by_contra h; rw [if_neg h] at hw'; norm_num at hw'
  rw [win_eq, ho] at hw
  simp only at hw
  have hj : H.job o = e := by by_contra h; rw [if_neg h] at hw; norm_num at hw
  rw [if_pos hj] at hw
  have hmem : e' ∈ univ.erase e := Finset.mem_erase.mpr ⟨Ne.symm hee, Finset.mem_univ _⟩
  by_contra hd
  have h0 : av H e' (H.sl o) (Z e') = 0 := by
    rw [ho']; simp only [av]
    rw [if_pos ⟨hj', fun h => hd h.symm⟩]
  rw [Finset.prod_eq_zero hmem h0] at hw
  norm_num at hw

theorem sum_winners_le' (Z : J → Option O) (S : Finset J) (c : J → ℝ)
    (hc0 : ∀ e, 0 ≤ c e) (cm : ℝ) (hcm0 : 0 ≤ cm) (hcm : ∀ e, c e ≤ cm) (t : Sl) :
    ∑ e ∈ S.filter (fun e => win H Z e = 1 ∧ t ∈ psl H (Z e)), c e ≤ cm := by
  by_cases hne : (S.filter (fun e => win H Z e = 1 ∧ t ∈ psl H (Z e))).Nonempty
  · obtain ⟨e, he⟩ := hne
    have huniq : S.filter (fun e => win H Z e = 1 ∧ t ∈ psl H (Z e)) = {e} := by
      ext e'
      simp only [Finset.mem_singleton]
      constructor
      · intro he'
        by_contra hne'
        obtain ⟨_, hw, ht⟩ := Finset.mem_filter.mp he
        obtain ⟨_, hw', ht'⟩ := Finset.mem_filter.mp he'
        cases hZe : Z e with
        | none => rw [hZe] at ht; simp [psl] at ht
        | some o =>
          cases hZe' : Z e' with
          | none => rw [hZe'] at ht'; simp [psl] at ht'
          | some o' =>
            rw [hZe] at ht; rw [hZe'] at ht'
            simp only [psl] at ht ht'
            have := win_disjoint' Z e e' (Ne.symm hne') o o' hZe hZe' hw hw'
            exact Finset.disjoint_left.mp this ht ht'
      · intro h; rw [h]; exact he
    rw [huniq, Finset.sum_singleton]; exact hcm e
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]; exact hcm0

/-- expected win -/
theorem EE_win (θ : ℝ) (x : O → ℝ) (e : J) :
    EE H θ x (win H · e) = ∑ o ∈ univ.filter (fun o => H.job o = e), θ * x o * piF H θ x o := by
  have h1 : (win H · e) = fun Z => ∑ o ∈ univ.filter (fun o => H.job o = e),
      ∏ f, (if f = e then (if Z f = some o then (1 : ℝ) else 0) else av H f (H.sl o) (Z f)) := by
    funext Z
    unfold win
    refine Finset.sum_congr rfl (fun o _ => ?_)
    rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ e)]
    simp only [if_pos rfl]
    congr 1
    refine Finset.prod_congr rfl (fun f hf => ?_)
    rw [if_neg (Finset.ne_of_mem_erase hf)]
  rw [h1, EE_finsum]
  refine Finset.sum_congr rfl (fun o ho => ?_)
  have hj := (Finset.mem_filter.mp ho).2
  rw [EE_prod (H := H) θ x (fun f y => if f = e then (if y = some o then (1 : ℝ) else 0) else av H f (H.sl o) y)]
  rw [← Finset.mul_prod_erase univ (fun f => ∑ y, pp H θ x f y *
    (if f = e then (if y = some o then (1 : ℝ) else 0) else av H f (H.sl o) y)) (Finset.mem_univ e)]
  simp only [if_true]
  have h2 : ∑ y, pp H θ x e y * (if y = some o then (1 : ℝ) else 0) = θ * x o := by
    rw [Finset.sum_eq_single (some o)]
    · simp [pp, hj]
    · intro b _ hb; simp [hb]
    · simp
  rw [h2]
  congr 1
  unfold piF
  rw [hj]
  refine Finset.prod_congr rfl (fun f hf => ?_)
  have hfe : f ≠ e := Finset.ne_of_mem_erase hf
  simp only [hfe, if_false]
  exact sum_pp_av θ x f (H.sl o)

end Nib

end SecWins

section SecGroup

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset TwoStage

namespace Nib

variable {J Sl O : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
  [Fintype O] [DecidableEq O] {H : HG J Sl O}

/-- weighted wins over a group -/
noncomputable def Qw (H : HG J Sl O) (S : Finset J) (c : J → ℝ) (Z : J → Option O) : ℝ :=
  ∑ e ∈ S, c e * win H Z e

/-- active group member under the group's picks `a` -/
def actv (H : HG J Sl O) (S : Finset J) (a : J → Option O) (e : J) : Prop :=
  ∃ o, a e = some o ∧ H.job o = e ∧ ∀ e' ∈ S, e' ≠ e → av H e' (H.sl o) (a e') = 1

noncomputable instance actvDec (H : HG J Sl O) (S : Finset J) (a : J → Option O) :
    DecidablePred (actv H S a) := Classical.decPred _

noncomputable def cw (H : HG J Sl O) (S : Finset J) (c : J → ℝ) (a : J → Option O) (t : Sl) : ℝ :=
  ∑ e ∈ S.filter (fun e => actv H S a e ∧ t ∈ psl H (a e)), c e

theorem winner_actv (S : Finset J) (a Z : J → Option O) (e : J) (he : e ∈ S)
    (hw : win H (merge S a Z) e = 1) : actv H S a e := by
  have hme : merge S a Z e = a e := by simp [merge, he]
  rw [win_eq, hme] at hw
  cases ha : a e with
  | none => rw [ha] at hw; simp at hw
  | some o =>
    rw [ha] at hw
    simp only at hw
    have hj : H.job o = e := by by_contra h; rw [if_neg h] at hw; norm_num at hw
    rw [if_pos hj] at hw
    refine ⟨o, ha, hj, fun e' he' hne => ?_⟩
    have hmem : e' ∈ univ.erase e := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
    have h01 := prod_av_mem01 (H := H) (fun _ => H.sl o) (merge S a Z) (univ.erase e)
    have hall : ∀ f ∈ univ.erase e, av H f (H.sl o) (merge S a Z f) = 1 := by
      intro f hf
      by_contra hne'
      have h0 : av H f (H.sl o) (merge S a Z f) = 0 := by
        have := av_nonneg (H := H) f (H.sl o) (merge S a Z f)
        have := av_le_one (H := H) f (H.sl o) (merge S a Z f)
        cases hmz : merge S a Z f with
        | none => rw [hmz] at hne'; simp [av] at hne'
        | some o'' => rw [hmz] at hne'; simp only [av] at hne' ⊢; split_ifs at hne' ⊢ <;> simp_all
      rw [Finset.prod_eq_zero hf h0] at hw; norm_num at hw
    have := hall e' hmem
    simpa [merge, he'] using this

theorem actv_disjoint (S : Finset J) (a : J → Option O) (e1 e2 : J) (h1 : e1 ∈ S) (h2 : e2 ∈ S)
    (hne : e1 ≠ e2) (ha1 : actv H S a e1) (ha2 : actv H S a e2) :
    Disjoint (psl H (a e1)) (psl H (a e2)) := by
  obtain ⟨o1, hz1, hj1, hav1⟩ := ha1
  obtain ⟨o2, hz2, hj2, hav2⟩ := ha2
  have := hav1 e2 h2 (Ne.symm hne)
  rw [hz2] at this
  simp only [av] at this
  rw [hz1, hz2]; simp only [psl]
  by_contra hd
  rw [if_pos ⟨hj2, fun h => hd h.symm⟩] at this
  norm_num at this

theorem cw_le_one (S : Finset J) (c : J → ℝ) (hc0 : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (a : J → Option O) (t : Sl) : cw H S c a t ≤ 1 := by
  unfold cw
  set F := S.filter (fun e => actv H S a e ∧ t ∈ psl H (a e))
  by_cases hne : F.Nonempty
  · obtain ⟨e, he⟩ := hne
    have huniq : F = {e} := by
      ext e'
      simp only [Finset.mem_singleton]
      constructor
      · intro he'
        by_contra hne'
        have m1 := Finset.mem_filter.mp he
        have m2 := Finset.mem_filter.mp he'
        have := actv_disjoint S a e e' m1.1 m2.1 (Ne.symm hne') m1.2.1 m2.2.1
        exact Finset.disjoint_left.mp this m1.2.2 m2.2.2
      · intro h; rw [h]; exact he
    rw [huniq, Finset.sum_singleton]; exact hc1 e
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]; norm_num

theorem cw_nonneg (S : Finset J) (c : J → ℝ) (hc0 : ∀ e, 0 ≤ c e) (a : J → Option O) (t : Sl) :
    0 ≤ cw H S c a t := Finset.sum_nonneg (fun e _ => hc0 e)

theorem sum_cw_le (S : Finset J) (c : J → ℝ) (hc0 : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (hsl : ∀ o, (H.sl o).card ≤ 2) (a : J → Option O) :
    ∑ t, cw H S c a t ≤ 2 * S.card := by
  unfold cw
  have : ∀ t, ∑ e ∈ S.filter (fun e => actv H S a e ∧ t ∈ psl H (a e)), c e ≤
      ∑ e ∈ S, (if t ∈ psl H (a e) then c e else 0) := by
    intro t
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun e _ => ?_)
    by_cases h1 : actv H S a e ∧ t ∈ psl H (a e)
    · rw [if_pos h1, if_pos h1.2]
    · rw [if_neg h1]; split_ifs <;> first | exact le_rfl | exact hc0 e
  refine le_trans (Finset.sum_le_sum (fun t _ => this t)) ?_
  rw [Finset.sum_comm]
  calc ∑ e ∈ S, ∑ t, (if t ∈ psl H (a e) then c e else 0) ≤ ∑ e ∈ S, (2 : ℝ) := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hcard : ((univ.filter (fun t => t ∈ psl H (a e))).card : ℝ) ≤ 2 := by
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
          cases a e with
          | none => simp [psl]
          | some o => simp only [psl]; exact_mod_cast hsl o
        nlinarith [hc0 e, hc1 e]
    _ = 2 * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem merge_upd_out (S : Finset J) (a Z : J → Option O) (k : J) (hk : k ∉ S) (y : Option O) :
    merge S a (Function.update Z k y) = Function.update (merge S a Z) k y := by
  funext f
  by_cases hf : f = k
  · subst hf; simp [merge, hk]
  · by_cases hfS : f ∈ S
    · simp [merge, hfS, Function.update_of_ne hf]
    · simp [merge, hfS, Function.update_of_ne hf]

theorem merge_upd_in (S : Finset J) (a Z : J → Option O) (k : J) (hk : k ∉ S) :
    merge S (Function.update a k (none : Option O)) Z = merge S a Z := by
  funext f
  by_cases hfS : f ∈ S
  · have : f ≠ k := fun h => hk (h ▸ hfS)
    simp [merge, hfS, Function.update_of_ne this]
  · simp [merge, hfS]

theorem merge_upd_mem (S : Finset J) (Z Z' : J → Option O) (k : J) (hk : k ∈ S) (y : Option O) :
    merge S (Function.update Z k y) Z' = Function.update (merge S Z Z') k y := by
  funext f
  by_cases hf : f = k
  · subst hf; simp [merge, hk]
  · by_cases hfS : f ∈ S
    · simp [merge, hfS, Function.update_of_ne hf]
    · simp [merge, hfS, Function.update_of_ne hf]

theorem card_psl_le (hsl : ∀ o, (H.sl o).card ≤ 2) (y : Option O) : (psl H y).card ≤ 2 := by
  cases y with
  | none => simp [psl]
  | some o => exact hsl o

/-- B-stage influence -/
theorem infl_B (S : Finset J) (c : J → ℝ) (hc0 : ∀ e, 0 ≤ c e) (a Z : J → Option O) (k : J)
    (hk : k ∉ S) (y : Option O) :
    |Qw H S c (merge S a (Function.update Z k y)) - Qw H S c (merge S a (Function.update Z k none))| ≤
      ∑ t ∈ psl H y, cw H S c a t := by
  rw [merge_upd_out S a Z k hk, merge_upd_out S a Z k hk]
  have h := wsum_infl (H := H) (merge S a Z) k y S c hc0
  rw [if_neg hk, zero_add] at h
  unfold Qw
  refine le_trans h (Finset.sum_le_sum (fun t _ => ?_))
  unfold cw
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => hc0 e)
  intro e he
  rw [Finset.mem_filter] at he ⊢
  obtain ⟨heS, _, hw, ht⟩ := he
  refine ⟨heS, ?_, ?_⟩
  · rw [← merge_upd_out S a Z k hk] at hw
    exact winner_actv S a _ e heS hw
  · have : merge S a Z e = a e := by simp [merge, heS]
    rw [this] at ht; exact ht

/-- A-stage influence -/
theorem infl_A (hsl : ∀ o, (H.sl o).card ≤ 2) (S : Finset J) (c : J → ℝ) (hc0 : ∀ e, 0 ≤ c e)
    (hc1 : ∀ e, c e ≤ 1) (Z Z' : J → Option O) (k : J) (hk : k ∈ S) (y : Option O) :
    |Qw H S c (merge S (Function.update Z k y) Z') - Qw H S c (merge S (Function.update Z k none) Z')| ≤
      (if y = none then 0 else 3) := by
  by_cases hy : y = none
  · subst hy; simp
  rw [if_neg hy, merge_upd_mem S Z Z' k hk, merge_upd_mem S Z Z' k hk]
  have h := wsum_infl (H := H) (merge S Z Z') k y S c hc0
  rw [if_pos hk] at h
  unfold Qw
  refine le_trans h ?_
  have h2 : ∑ t ∈ psl H y, ∑ e ∈ S.filter (fun e => e ≠ k ∧
      win H (Function.update (merge S Z Z') k none) e = 1 ∧ t ∈ psl H (merge S Z Z' e)), c e ≤ 2 := by
    calc _ ≤ ∑ t ∈ psl H y, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun t _ => ?_)
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := S.filter (fun e =>
            win H (Function.update (merge S Z Z') k none) e = 1 ∧
              t ∈ psl H (Function.update (merge S Z Z') k none e))) ?_ (fun e _ _ => hc0 e)) ?_
          · intro e he
            rw [Finset.mem_filter] at he ⊢
            obtain ⟨heS, hek, hw, ht⟩ := he
            refine ⟨heS, hw, ?_⟩
            rw [Function.update_of_ne hek]; exact ht
          · exact sum_winners_le' (H := H) _ S c hc0 1 (by norm_num) hc1 t
      _ ≤ 2 := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast card_psl_le hsl y
  linarith [hc1 k]

theorem sum_pp_some (θ : ℝ) (x : O → ℝ) (k : J) (F : O → ℝ) :
    ∑ o, pp H θ x k (some o) * F o = ∑ o ∈ univ.filter (fun o => H.job o = k), θ * x o * F o := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun o _ => ?_)
  simp only [pp]; split_ifs <;> ring

theorem VB_le (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hσ : 0 ≤ σ) (S : Finset J) (c : J → ℝ) (hc0 : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (a : J → Option O) :
    ∑ k, ∑ y, condp (pp H θ x) S (fun _ => none) k y *
      (if k ∈ S then 0 else ∑ t ∈ psl H y, cw H S c a t) ^ 2 ≤ 4 * θ * S.card := by
  have hstep : ∀ k, ∑ y, condp (pp H θ x) S (fun _ => none) k y *
      (if k ∈ S then 0 else ∑ t ∈ psl H y, cw H S c a t) ^ 2 ≤
      ∑ o ∈ univ.filter (fun o => H.job o = k), θ * x o * (2 * ∑ t ∈ H.sl o, cw H S c a t ^ 2) := by
    intro k
    by_cases hk : k ∈ S
    · simp only [hk, if_true]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
      exact Finset.sum_nonneg (fun o _ => mul_nonneg (mul_nonneg hθ0 (hI.x0 o))
        (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun t _ => sq_nonneg _))))
    · simp only [hk, if_false, condp]
      rw [Fintype.sum_option]
      simp only [psl, Finset.sum_empty, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, zero_add]
      rw [sum_pp_some]
      refine Finset.sum_le_sum (fun o _ => ?_)
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hθ0 (hI.x0 o))
      have := sq_sum_le_card_mul_sum_sq (s := H.sl o) (f := fun t => cw H S c a t)
      have h2 : ((H.sl o).card : ℝ) ≤ 2 := by exact_mod_cast hsl o
      have h3 : 0 ≤ ∑ t ∈ H.sl o, cw H S c a t ^ 2 := Finset.sum_nonneg (fun t _ => sq_nonneg _)
      nlinarith
  refine le_trans (Finset.sum_le_sum (fun k _ => hstep k)) ?_
  rw [Finset.sum_fiberwise (s := univ) (g := H.job)
    (f := fun o => θ * x o * (2 * ∑ t ∈ H.sl o, cw H S c a t ^ 2))]
  have e1 : ∑ o, θ * x o * (2 * ∑ t ∈ H.sl o, cw H S c a t ^ 2) =
      2 * θ * ∑ o, x o * ∑ t ∈ H.sl o, cw H S c a t ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun o _ => by ring)
  rw [e1, sum_x_sl x (fun t => cw H S c a t ^ 2)]
  have h4 : ∑ t, load H x t * cw H S c a t ^ 2 ≤ ∑ t, cw H S c a t := by
    refine Finset.sum_le_sum (fun t _ => ?_)
    have hl := hI.load t
    have hl0 : 0 ≤ load H x t := Finset.sum_nonneg (fun o _ => hI.x0 o)
    have hc := cw_le_one (H := H) S c hc0 hc1 a t
    have hc' := cw_nonneg (H := H) S c hc0 a t
    nlinarith [mul_le_mul hl hc (by positivity) (by linarith : (0:ℝ) ≤ 1 - σ / 2)]
  have h5 := sum_cw_le (H := H) S c hc0 hc1 hsl a
  nlinarith

theorem VA_le (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hθ0 : 0 ≤ θ) (hδ : δ ≤ 1)
    (S : Finset J) :
    ∑ k, ∑ y, pp H θ x k y * (if k ∈ S ∧ y ≠ none then (3 : ℝ) else 0) ^ 2 ≤ 18 * θ * S.card := by
  have hstep : ∀ k, ∑ y, pp H θ x k y * (if k ∈ S ∧ y ≠ none then (3 : ℝ) else 0) ^ 2 =
      if k ∈ S then 9 * (θ * mass H x k) else 0 := by
    intro k
    rw [Fintype.sum_option]
    by_cases hk : k ∈ S
    · simp only [hk, true_and, ne_eq, not_true_eq_false, if_false, reduceCtorEq, not_false_eq_true,
        if_true]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
      rw [sum_pp_some θ x k (fun _ => (3 : ℝ) ^ 2), mass, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun o _ => by ring)
    · simp [hk]
  simp_rw [hstep]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  calc ∑ k ∈ S, 9 * (θ * mass H x k) ≤ ∑ _k ∈ S, 18 * θ := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have hm : mass H x k ≤ 2 := by
          rcases hI.mass k with h | h
          · rw [h]; norm_num
          · linarith [h.2]
        nlinarith
    _ = 18 * θ * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem merge_upd_S (S : Finset J) (a Z : J → Option O) (k : J) (hk : k ∈ S) (y : Option O) :
    merge S a (Function.update Z k y) = merge S a Z := by
  funext f
  by_cases hfS : f ∈ S
  · simp [merge, hfS]
  · have : f ≠ k := fun h => hfS (h ▸ hk)
    simp [merge, hfS, Function.update_of_ne this]

theorem thr_mono {K X : Type} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]
    (p : K → X → ℝ) (hp0 : ∀ k y, 0 ≤ p k y) (f : (K → X) → ℝ) (E l1 l2 : ℝ) (h : l1 ≤ l2) :
    wE p (fun Z => if f Z ≤ E - l2 then 1 else 0) ≤ wE p (fun Z => if f Z ≤ E - l1 then 1 else 0) := by
  refine wE_mono p hp0 _ _ (fun Z => ?_)
  by_cases h2 : f Z ≤ E - l2
  · rw [if_pos h2, if_pos (by linarith)]
  · rw [if_neg h2]; split_ifs <;> norm_num

theorem pp_nonneg' (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16)
    (hδ : δ ≤ 1) : ∀ k y, 0 ≤ pp H θ x k y := by
  intro k y
  refine pp_nonneg θ x hθ0 hI.x0 (fun e => ?_) k y
  have hm : mass H x e ≤ 2 := by
    rcases hI.mass e with h | h
    · rw [h]; norm_num
    · linarith [h.2]
  nlinarith

/-- **group event**: weighted wins rarely fall far below their mean -/
theorem group_lower (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hσ : 0 ≤ σ) (hδ : δ ≤ 1) (S : Finset J) (c : J → ℝ)
    (hc0 : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    EE H θ x (fun Z => if Qw H S c Z ≤ EE H θ x (Qw H S c) -
      ((2 * Real.sqrt (4 * θ * S.card * Λ) + 2 * 4 * Λ) +
        (2 * Real.sqrt (18 * θ * S.card * Λ) + 2 * 6 * Λ)) then 1 else 0) ≤
      Real.exp (-Λ) + Real.exp (-Λ) := by
  have hp0 := pp_nonneg' θ σ δ κ x hI hθ0 hθ hδ
  have hp1 : ∀ k, ∑ y, pp H θ x k y = 1 := fun k => sum_pp θ x k
  show wE (pp H θ x) _ ≤ _
  have hEE : EE H θ x (Qw H S c) = wE (pp H θ x) (Qw H S c) := rfl
  rw [hEE]
  refine two_stage_lower (pp H θ x) hp0 hp1 S none (Qw H S c) _ _ _ _ ?_ ?_
  · -- B stage
    intro a
    rw [cond_as_free (pp H θ x) S a none, cond_as_free (pp H θ x) S a none (Qw H S c)]
    set pB := condp (pp H θ x) S (fun _ => none)
    have hpB0 := condp_free_nonneg (pp H θ x) hp0 S none
    have hpB1 := condp_free_sum (pp H θ x) hp1 S none
    set DB : J → Option O → ℝ := fun k y => if k ∈ S then 0 else ∑ t ∈ psl H y, cw H S c a t
    have key := (OneStage.dev_of_infl pB hpB0 hpB1 (fun Z => Qw H S c (merge S a Z)) none DB 4
      (by norm_num) ?_ ?_ Λ hΛ).2
    · refine le_trans ?_ key
      refine thr_mono pB hpB0 _ _ _ _ ?_
      have hV := VB_le θ σ δ κ x hI hsl hθ0 hσ S c hc0 hc1 a
      have : Real.sqrt ((∑ k, ∑ y, pB k y * DB k y ^ 2) * Λ) ≤ Real.sqrt (4 * θ * S.card * Λ) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hV hΛ)
      linarith
    · intro Z k y
      by_cases hk : k ∈ S
      · simp only [DB, hk, if_true]
        rw [merge_upd_S S a Z k hk, merge_upd_S S a Z k hk, sub_self, abs_zero]
      · simp only [DB, hk, if_false]
        exact infl_B S c hc0 a Z k hk y
    · intro k y
      simp only [DB]
      split_ifs
      · norm_num
      · have : ∑ t ∈ psl H y, cw H S c a t ≤ 2 := by
          calc _ ≤ ∑ _t ∈ psl H y, (1 : ℝ) := Finset.sum_le_sum (fun t _ => cw_le_one S c hc0 hc1 a t)
            _ ≤ 2 := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast card_psl_le hsl y
        linarith
  · -- A stage
    rw [← E_cond_eq (pp H θ x) hp1 S none (Qw H S c)]
    set DA : J → Option O → ℝ := fun k y => if k ∈ S ∧ y ≠ none then 3 else 0
    have key := (OneStage.dev_of_infl (pp H θ x) hp0 hp1 (fun Z => wE (condp (pp H θ x) S Z) (Qw H S c))
      none DA 6 (by norm_num) ?_ ?_ Λ hΛ).2
    · refine le_trans ?_ key
      refine thr_mono (pp H θ x) hp0 _ _ _ _ ?_
      have hV := VA_le θ σ δ κ x hI hθ0 hδ S
      have : Real.sqrt ((∑ k, ∑ y, pp H θ x k y * DA k y ^ 2) * Λ) ≤ Real.sqrt (18 * θ * S.card * Λ) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hV hΛ)
      linarith
    · intro Z k y
      by_cases hk : k ∈ S
      · have hB := cond_infl (pp H θ x) hp0 hp1 S none (Qw H S c) (Function.update Z k y)
          (Function.update Z k none) (if y = none then 0 else 3)
          (fun Z' => infl_A hsl S c hc0 hc1 Z Z' k hk y)
        refine le_trans hB ?_
        simp only [DA]
        by_cases hy : y = none
        · simp [hy]
        · simp [hy, hk]
      · have : wE (condp (pp H θ x) S (Function.update Z k y)) (Qw H S c) =
            wE (condp (pp H θ x) S (Function.update Z k none)) (Qw H S c) := by
          refine cond_congr _ S _ _ (fun f hf => ?_) _
          have : f ≠ k := fun h => hk (h ▸ hf)
          simp [Function.update_of_ne this]
        rw [this, sub_self, abs_zero]
        simp only [DA]; split_ifs <;> norm_num
    · intro k y; simp only [DA]; split_ifs <;> norm_num

end Nib

end SecGroup

section SecDummy

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset TwoStage

namespace Nib

variable {J Sl O : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
  [Fintype O] [DecidableEq O] {H : HG J Sl O}

/-- indicator that a pick is a valid dummy pick of job `e` -/
def dpk (H : HG J Sl O) (dum : O → Prop) [DecidablePred dum] (e : J) : Option O → ℝ
  | none => 0
  | some o => if dum o ∧ H.job o = e then 1 else 0

/-- weighted dummy picks of a group -/
noncomputable def Dq (H : HG J Sl O) (dum : O → Prop) [DecidablePred dum] (S : Finset J) (c : J → ℝ)
    (Z : J → Option O) : ℝ := ∑ e ∈ S, c e * dpk H dum e (Z e)

/-- dummy mass -/
noncomputable def dmass (H : HG J Sl O) (dum : O → Prop) [DecidablePred dum] (x : O → ℝ) (e : J) : ℝ :=
  ∑ o ∈ univ.filter (fun o => H.job o = e ∧ dum o), x o

theorem EE_Dq (θ : ℝ) (x : O → ℝ) (dum : O → Prop) [DecidablePred dum] (S : Finset J) (c : J → ℝ) :
    EE H θ x (Dq H dum S c) = θ * ∑ e ∈ S, c e * dmass H dum x e := by
  unfold Dq
  rw [EE_finsum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [EE_smul]
  have h : EE H θ x (fun Z => dpk H dum e (Z e)) = θ * dmass H dum x e := by
    have := EE_prod (H := H) θ x (fun f y => if f = e then dpk H dum e y else 1)
    have e1 : (fun Z : J → Option O => ∏ f, (if f = e then dpk H dum e (Z f) else 1)) =
        (fun Z => dpk H dum e (Z e)) := by
      funext Z; rw [Finset.prod_ite_eq' univ e]; simp
    rw [e1] at this
    rw [this, Finset.prod_eq_single e]
    · simp only [if_true]
      rw [Fintype.sum_option]
      simp only [dpk, mul_zero, zero_add]
      unfold dmass
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun o _ => ?_)
      simp only [pp]
      by_cases h1 : H.job o = e <;> by_cases h2 : dum o <;> simp [h1, h2]
    · intro f _ hf
      simp only [if_neg hf, mul_one]
      exact sum_pp θ x f
    · simp
  rw [h]; ring

/-- **dummy event**: dummy picks rarely exceed their mean -/
theorem dummy_upper (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16)
    (hδ : δ ≤ 1) (dum : O → Prop) [DecidablePred dum] (S : Finset J) (c : J → ℝ)
    (hc0 : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    EE H θ x (fun Z => if 2 * Real.sqrt (2 * θ * S.card * Λ) + 2 * 2 * Λ ≤
      Dq H dum S c Z - EE H θ x (Dq H dum S c) then 1 else 0) ≤ Real.exp (-Λ) := by
  have hp0 := pp_nonneg' θ σ δ κ x hI hθ0 hθ hδ
  have hp1 : ∀ k, ∑ y, pp H θ x k y = 1 := fun k => sum_pp θ x k
  set D : J → Option O → ℝ := fun k y => if k ∈ S then dpk H dum k y else 0
  have hdpk0 : ∀ k y, 0 ≤ dpk H dum k y := by
    intro k y; cases y with
    | none => simp [dpk]
    | some o => simp only [dpk]; split_ifs <;> norm_num
  have hdpk1 : ∀ k y, dpk H dum k y ≤ 1 := by
    intro k y; cases y with
    | none => simp [dpk]
    | some o => simp only [dpk]; split_ifs <;> norm_num
  have key := (OneStage.dev_of_infl (pp H θ x) hp0 hp1 (Dq H dum S c) none D 2 (by norm_num) ?_ ?_ Λ hΛ).1
  · refine le_trans ?_ key
    show wE (pp H θ x) _ ≤ wE (pp H θ x) _
    refine wE_mono _ hp0 _ _ (fun Z => ?_)
    have hV : ∑ k, ∑ y, pp H θ x k y * D k y ^ 2 ≤ 2 * θ * S.card := by
      have hstep : ∀ k, ∑ y, pp H θ x k y * D k y ^ 2 ≤ if k ∈ S then 2 * θ else 0 := by
        intro k
        simp only [D]
        by_cases hk : k ∈ S
        · simp only [hk, if_true]
          rw [Fintype.sum_option]
          simp only [dpk, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
          rw [sum_pp_some θ x k (fun o => (if dum o ∧ H.job o = k then (1 : ℝ) else 0) ^ 2)]
          have : ∑ o ∈ univ.filter (fun o => H.job o = k),
              θ * x o * (if dum o ∧ H.job o = k then (1 : ℝ) else 0) ^ 2 ≤ θ * mass H x k := by
            rw [mass, Finset.mul_sum]
            refine Finset.sum_le_sum (fun o _ => ?_)
            have := hI.x0 o
            split_ifs <;> nlinarith
          have hm : mass H x k ≤ 2 := by
            rcases hI.mass k with h | h
            · rw [h]; norm_num
            · linarith [h.2]
          nlinarith
        · simp [hk]
      refine le_trans (Finset.sum_le_sum (fun k _ => hstep k)) ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_mem_eq_inter,
        Finset.univ_inter]
      ring_nf; exact le_rfl
    have hs : Real.sqrt ((∑ k, ∑ y, pp H θ x k y * D k y ^ 2) * Λ) ≤ Real.sqrt (2 * θ * S.card * Λ) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hV hΛ)
    have hE : EE H θ x (Dq H dum S c) = ∑ Z' : J → Option O, (∏ k, pp H θ x k (Z' k)) * Dq H dum S c Z' := rfl
    by_cases h1 : 2 * Real.sqrt (2 * θ * S.card * Λ) + 2 * 2 * Λ ≤ Dq H dum S c Z - EE H θ x (Dq H dum S c)
    · rw [if_pos h1, if_pos (by rw [← hE]; linarith)]
    · rw [if_neg h1]; split_ifs <;> norm_num
  · intro Z k y
    simp only [D]
    unfold Dq
    by_cases hk : k ∈ S
    · rw [if_pos hk, ← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single k]
      · simp only [Function.update_self]
        have : dpk H dum k none = 0 := rfl
        rw [this, mul_zero, sub_zero, abs_of_nonneg (mul_nonneg (hc0 k) (hdpk0 k y))]
        nlinarith [hc1 k, hdpk0 k y]
      · intro e _ hek
        simp [Function.update_of_ne hek]
      · intro h; exact absurd hk h
    · rw [if_neg hk]
      have : ∀ e ∈ S, Function.update Z k y e = Function.update Z k none e := by
        intro e he
        have : e ≠ k := fun h => hk (h ▸ he)
        simp [Function.update_of_ne this]
      rw [Finset.sum_congr rfl (fun e he => by rw [this e he]), sub_self, abs_zero]
  · intro k y
    simp only [D]
    split_ifs
    · linarith [hdpk1 k y]
    · norm_num

end Nib

end SecDummy

section SecLoad

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset TwoStage

namespace Nib

variable {J Sl O : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
  [Fintype O] [DecidableEq O] {H : HG J Sl O}

/-- avoidance product of the other slots of `o` (besides `s`) -/
noncomputable def PT (H : HG J Sl O) (s : Sl) (o : O) (Z : J → Option O) : ℝ :=
  ∏ f ∈ univ.erase (H.job o), av H f ((H.sl o).erase s) (Z f)

noncomputable def Ya (H : HG J Sl O) (θ : ℝ) (x : O → ℝ) (s : Sl) (Z : J → Option O) : ℝ :=
  ∑ o ∈ univ.filter (fun o => s ∈ H.sl o), (x o / piF H θ x o) * PT H s o Z

noncomputable def Yw (H : HG J Sl O) (θ : ℝ) (x : O → ℝ) (s : Sl) (Z : J → Option O) : ℝ :=
  ∑ o ∈ univ.filter (fun o => s ∈ H.sl o), (x o / piF H θ x o) * PT H s o Z * win H Z (H.job o)

theorem PT_nonneg (s : Sl) (o : O) (Z : J → Option O) : 0 ≤ PT H s o Z :=
  Finset.prod_nonneg (fun f _ => av_nonneg _ _ _)

theorem PT_le_one (s : Sl) (o : O) (Z : J → Option O) : PT H s o Z ≤ 1 :=
  Finset.prod_le_one (fun f _ => av_nonneg _ _ _) (fun f _ => av_le_one _ _ _)

/-- deterministic: the next load is at most `Ya − Yw` -/
theorem load_nxt_le (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (s : Sl) (Z : J → Option O) :
    load H (nxt H θ x Z) s ≤ Ya H θ x s Z - Yw H θ x s Z := by
  unfold load Ya Yw
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun o ho => ?_)
  have hs : s ∈ H.sl o := (Finset.mem_filter.mp ho).2
  have hpb := piF_bounds θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ o
  have hq0 : 0 ≤ x o / piF H θ x o := div_nonneg (hI.x0 o) (by linarith [hpb.1])
  have hw0 := win_nonneg (H := H) Z (H.job o)
  have hw1 := win_le_one (H := H) Z (H.job o)
  unfold nxt
  have hprod : ∏ f, av H f (H.sl o) (Z f) ≤ PT H s o Z := by
    unfold PT
    rw [← Finset.mul_prod_erase univ (fun f => av H f (H.sl o) (Z f)) (Finset.mem_univ (H.job o))]
    have h1 := av_le_one (H := H) (H.job o) (H.sl o) (Z (H.job o))
    have h2 : ∏ f ∈ univ.erase (H.job o), av H f (H.sl o) (Z f) ≤
        ∏ f ∈ univ.erase (H.job o), av H f ((H.sl o).erase s) (Z f) :=
      Finset.prod_le_prod (fun f _ => av_nonneg _ _ _)
        (fun f _ => av_mono f _ _ (Finset.erase_subset s _) (Z f))
    have h3 : 0 ≤ ∏ f ∈ univ.erase (H.job o), av H f (H.sl o) (Z f) :=
      Finset.prod_nonneg (fun f _ => av_nonneg _ _ _)
    have h4 := av_nonneg (H := H) (H.job o) (H.sl o) (Z (H.job o))
    nlinarith
  have hP0 : 0 ≤ ∏ f, av H f (H.sl o) (Z f) := Finset.prod_nonneg (fun f _ => av_nonneg _ _ _)
  calc x o / piF H θ x o * (∏ f, av H f (H.sl o) (Z f)) * (1 - win H Z (H.job o))
      ≤ x o / piF H θ x o * PT H s o Z * (1 - win H Z (H.job o)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hq0) (by linarith)
    _ = x o / piF H θ x o * PT H s o Z - x o / piF H θ x o * PT H s o Z * win H Z (H.job o) := by ring

/-- `α`-factor of an option at a slot -/
noncomputable def alF (H : HG J Sl O) (θ : ℝ) (x : O → ℝ) (s : Sl) (o : O) : ℝ :=
  ∏ f ∈ univ.erase (H.job o), (1 - θ * aff H x f ((H.sl o).erase s))

theorem EE_PT (θ : ℝ) (x : O → ℝ) (s : Sl) (o : O) :
    EE H θ x (PT H s o) = alF H θ x s o := by
  unfold PT alF
  rw [EE_prod_erase]
  simp_rw [sum_pp_av]

theorem EE_Ya (θ : ℝ) (x : O → ℝ) (s : Sl) :
    EE H θ x (Ya H θ x s) = ∑ o ∈ univ.filter (fun o => s ∈ H.sl o),
      (x o / piF H θ x o) * alF H θ x s o := by
  unfold Ya
  rw [EE_finsum]
  refine Finset.sum_congr rfl (fun o _ => ?_)
  rw [EE_smul, EE_PT]

theorem av_mul_av (f : J) (T T' : Finset Sl) (y : Option O) :
    av H f T y * av H f T' y = av H f (T ∪ T') y := by
  cases y with
  | none => simp [av]
  | some o =>
    simp only [av]
    by_cases hj : H.job o = f
    · by_cases h1 : Disjoint (H.sl o) T <;> by_cases h2 : Disjoint (H.sl o) T' <;>
        simp [hj, h1, h2, Finset.disjoint_union_right]
    · simp [hj]

/-- expectation of a `PT × win` term -/
theorem EE_PT_win (θ : ℝ) (x : O → ℝ) (s : Sl) (o : O) :
    EE H θ x (fun Z => PT H s o Z * win H Z (H.job o)) =
      ∑ o' ∈ univ.filter (fun o' => H.job o' = H.job o),
        θ * x o' * ∏ f ∈ univ.erase (H.job o), (1 - θ * aff H x f ((H.sl o).erase s ∪ H.sl o')) := by
  have h1 : (fun Z => PT H s o Z * win H Z (H.job o)) = fun Z => ∑ o' ∈ univ.filter (fun o' => H.job o' = H.job o),
      ∏ f, (if f = H.job o then (if Z f = some o' then (1 : ℝ) else 0)
        else av H f ((H.sl o).erase s ∪ H.sl o') (Z f)) := by
    funext Z
    unfold PT win
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun o' _ => ?_)
    rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ (H.job o))]
    simp only [if_true]
    have : ∏ f ∈ univ.erase (H.job o), (if f = H.job o then (if Z f = some o' then (1 : ℝ) else 0)
        else av H f ((H.sl o).erase s ∪ H.sl o') (Z f)) =
        ∏ f ∈ univ.erase (H.job o), av H f ((H.sl o).erase s ∪ H.sl o') (Z f) :=
      Finset.prod_congr rfl (fun f hf => by rw [if_neg (Finset.ne_of_mem_erase hf)])
    rw [this]
    simp_rw [← av_mul_av]
    rw [Finset.prod_mul_distrib]
    ring
  rw [h1, EE_finsum]
  refine Finset.sum_congr rfl (fun o' ho' => ?_)
  have hj := (Finset.mem_filter.mp ho').2
  rw [EE_prod (H := H) θ x (fun f y => if f = H.job o then (if y = some o' then (1 : ℝ) else 0)
    else av H f ((H.sl o).erase s ∪ H.sl o') y)]
  rw [← Finset.mul_prod_erase univ (fun f => ∑ y, pp H θ x f y *
    (if f = H.job o then (if y = some o' then (1 : ℝ) else 0) else av H f ((H.sl o).erase s ∪ H.sl o') y))
    (Finset.mem_univ (H.job o))]
  simp only [if_true]
  have h2 : ∑ y, pp H θ x (H.job o) y * (if y = some o' then (1 : ℝ) else 0) = θ * x o' := by
    rw [Finset.sum_eq_single (some o')]
    · simp [pp, hj]
    · intro b _ hb; simp [hb]
    · simp
  rw [h2]
  congr 1
  refine Finset.prod_congr rfl (fun f hf => ?_)
  have hfe : f ≠ H.job o := Finset.ne_of_mem_erase hf
  simp only [hfe, if_false]
  exact sum_pp_av θ x f _

theorem aff_union_le (x : O → ℝ) (hx : ∀ o, 0 ≤ x o) (f : J) (A B : Finset Sl) :
    aff H x f (A ∪ B) ≤ aff H x f A + aff H x f B := by
  unfold aff
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun o _ => ?_)
  by_cases h1 : H.job o = f ∧ ¬Disjoint (H.sl o) (A ∪ B)
  · rw [if_pos h1]
    rw [Finset.disjoint_union_right] at h1
    by_cases hA : Disjoint (H.sl o) A
    · have hB : ¬Disjoint (H.sl o) B := fun hB => h1.2 ⟨hA, hB⟩
      rw [if_neg (fun h => h.2 hA), if_pos ⟨h1.1, hB⟩]; linarith [hx o]
    · rw [if_pos ⟨h1.1, hA⟩]; split_ifs <;> linarith [hx o]
  · rw [if_neg h1]; split_ifs <;> linarith [hx o]

theorem aff_le_kappa1 (σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (f : J) (o : O) (s : Sl) (hs : s ∈ H.sl o) : aff H x f ((H.sl o).erase s) ≤ κ := by
  have h1 := aff_le_card σ δ κ x hI f ((H.sl o).erase s)
  have h2 : ((H.sl o).erase s).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hs]; have := hsl o; omega
  have hκ0 : 0 ≤ κ := le_trans (Finset.sum_nonneg (fun o _ => hI.x0 o)) (hI.cod1 f s)
  have h3 : (((H.sl o).erase s).card : ℝ) ≤ 1 := by exact_mod_cast h2
  nlinarith

/-- factorwise: 1 - u - v ≥ (1-u)(1-v)(1-2uv) -/
theorem fac1 (u v : ℝ) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hu : u ≤ 1 / 4) (hv : v ≤ 1 / 4) :
    (1 - u) * (1 - v) * (1 - 2 * (u * v)) ≤ 1 - u - v := by
  have h1 : (0:ℝ) ≤ 1 / 2 - u - v + u * v := by nlinarith [mul_nonneg hu0 hv0]
  nlinarith [mul_nonneg hu0 hv0, mul_nonneg (mul_nonneg hu0 hv0) h1]

/-- factorwise: 1 - u - w ≥ (1-u)(1-w(1+2u)) -/
theorem fac2 (u w : ℝ) (hu0 : 0 ≤ u) (hw0 : 0 ≤ w) (hu : u ≤ 1 / 2) :
    (1 - u) * (1 - w * (1 + 2 * u)) ≤ 1 - u - w := by
  nlinarith [mul_nonneg hu0 hw0, mul_nonneg (mul_nonneg hu0 hw0) (by linarith : (0:ℝ) ≤ 1 - 2 * u)]

theorem prod_ge_mul_weier {α : Type} (S : Finset α) (a b : α → ℝ) (ha0 : ∀ i ∈ S, 0 ≤ a i)
    (hb0 : ∀ i ∈ S, 0 ≤ b i) (hb1 : ∀ i ∈ S, b i ≤ 1) (P : α → ℝ)
    (hP : ∀ i ∈ S, a i * (1 - b i) ≤ P i) :
    (∏ i ∈ S, a i) * (1 - ∑ i ∈ S, b i) ≤ ∏ i ∈ S, P i := by
  have h1 : (∏ i ∈ S, a i) * (1 - ∑ i ∈ S, b i) ≤ (∏ i ∈ S, a i) * ∏ i ∈ S, (1 - b i) :=
    mul_le_mul_of_nonneg_left (weierstrass S b hb0 hb1) (Finset.prod_nonneg ha0)
  rw [← Finset.prod_mul_distrib] at h1
  exact le_trans h1 (Finset.prod_le_prod (fun i hi => mul_nonneg (ha0 i hi) (by linarith [hb1 i hi])) hP)

/-- `α_o (1 - r) ≤ π_o` -/
theorem alF_le (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (s : Sl) (o : O) (hs : s ∈ H.sl o) :
    alF H θ x s o * (1 - (1 + 2 * θ * κ) * (θ * load H x s)) ≤ piF H θ x o := by
  have hκ0 : 0 ≤ κ := le_trans (Finset.sum_nonneg (fun o _ => hI.x0 o)) (hI.cod1 (H.job o) s)
  set E := univ.erase (H.job o)
  have hu : ∀ f, θ * aff H x f ((H.sl o).erase s) ≤ θ * κ := fun f =>
    mul_le_mul_of_nonneg_left (aff_le_kappa1 σ δ κ x hI hsl f o s hs) hθ0
  have hw1 : ∀ f, θ * aff H x f {s} ≤ θ * κ := by
    intro f
    have := aff_le_card σ δ κ x hI f {s}
    simp at this
    exact mul_le_mul_of_nonneg_left this hθ0
  have hθκ : θ * κ ≤ 1 / 16 := by nlinarith
  have key := prod_ge_mul_weier E (fun f => 1 - θ * aff H x f ((H.sl o).erase s))
    (fun f => θ * aff H x f {s} * (1 + 2 * (θ * aff H x f ((H.sl o).erase s))))
    (fun f _ => by linarith [hu f])
    (fun f _ => mul_nonneg (mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f _))
      (by nlinarith [mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f ((H.sl o).erase s))]))
    (fun f _ => by
      have h1 := hw1 f; have h2 := hu f
      have h3 := mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f ((H.sl o).erase s))
      have h4 := mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f {s})
      nlinarith)
    (fun f => 1 - θ * aff H x f (H.sl o))
    (fun f _ => by
      have hsplit : H.sl o = (H.sl o).erase s ∪ {s} := by
        rw [Finset.union_comm]; exact (Finset.insert_erase hs).symm
      have hsub : aff H x f (H.sl o) ≤ aff H x f ((H.sl o).erase s) + aff H x f {s} := by
        conv_lhs => rw [hsplit]
        exact aff_union_le x hI.x0 f _ _
      have hf := fac2 (θ * aff H x f ((H.sl o).erase s)) (θ * aff H x f {s})
        (mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f _)) (mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f _))
        (by linarith [hu f])
      nlinarith [mul_le_mul_of_nonneg_left hsub hθ0])
  have hsum : ∑ f ∈ E, θ * aff H x f {s} * (1 + 2 * (θ * aff H x f ((H.sl o).erase s))) ≤
      (1 + 2 * θ * κ) * (θ * load H x s) := by
    calc ∑ f ∈ E, θ * aff H x f {s} * (1 + 2 * (θ * aff H x f ((H.sl o).erase s)))
        ≤ ∑ f ∈ E, θ * aff H x f {s} * (1 + 2 * θ * κ) := by
          refine Finset.sum_le_sum (fun f _ => mul_le_mul_of_nonneg_left (by linarith [hu f])
            (mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f _)))
      _ = (1 + 2 * θ * κ) * (θ * ∑ f ∈ E, aff H x f {s}) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
      _ ≤ (1 + 2 * θ * κ) * (θ * load H x s) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hθ0
          have := sum_aff_le (H := H) x hI.x0 {s} E
          simpa using this
  have hal0 : 0 ≤ alF H θ x s o := Finset.prod_nonneg (fun f _ => by linarith [hu f])
  unfold piF
  calc alF H θ x s o * (1 - (1 + 2 * θ * κ) * (θ * load H x s))
      ≤ alF H θ x s o * (1 - ∑ f ∈ E, θ * aff H x f {s} * (1 + 2 * (θ * aff H x f ((H.sl o).erase s)))) :=
        mul_le_mul_of_nonneg_left (by linarith) hal0
    _ ≤ _ := key

theorem PTwin_lower (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (s : Sl) (o : O) (hs : s ∈ H.sl o) :
    alF H θ x s o * (1 - 4 * θ ^ 2 * κ) * (θ * (1 - 2 * θ) * mass H x (H.job o)) ≤
      ∑ o' ∈ univ.filter (fun o' => H.job o' = H.job o),
        θ * x o' * ∏ f ∈ univ.erase (H.job o), (1 - θ * aff H x f ((H.sl o).erase s ∪ H.sl o')) := by
  have hκ0 : 0 ≤ κ := le_trans (Finset.sum_nonneg (fun o _ => hI.x0 o)) (hI.cod1 (H.job o) s)
  set E := univ.erase (H.job o)
  have hu : ∀ f, θ * aff H x f ((H.sl o).erase s) ≤ θ * κ := fun f =>
    mul_le_mul_of_nonneg_left (aff_le_kappa1 σ δ κ x hI hsl f o s hs) hθ0
  have hθκ : θ * κ ≤ 1 / 16 := by nlinarith
  have hal0 : 0 ≤ alF H θ x s o := Finset.prod_nonneg (fun f _ => by linarith [hu f])
  have hterm : ∀ o' ∈ univ.filter (fun o' => H.job o' = H.job o),
      θ * x o' * (alF H θ x s o * (1 - 4 * θ ^ 2 * κ) * (1 - 2 * θ)) ≤
      θ * x o' * ∏ f ∈ E, (1 - θ * aff H x f ((H.sl o).erase s ∪ H.sl o')) := by
    intro o' ho'
    have hj := (Finset.mem_filter.mp ho').2
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hθ0 (hI.x0 o'))
    have hv : ∀ f, θ * aff H x f (H.sl o') ≤ 2 * θ * κ := by
      intro f
      have h1 := aff_le_card σ δ κ x hI f (H.sl o')
      have h2 : ((H.sl o').card : ℝ) ≤ 2 := by exact_mod_cast hsl o'
      have := aff_nonneg (H := H) x hI.x0 f (H.sl o')
      have h3 : aff H x f (H.sl o') ≤ 2 * κ := by nlinarith [mul_le_mul_of_nonneg_right h2 hκ0]
      nlinarith [mul_le_mul_of_nonneg_left h3 hθ0]
    have key := prod_ge_mul_weier E
      (fun f => (1 - θ * aff H x f ((H.sl o).erase s)) * (1 - θ * aff H x f (H.sl o')))
      (fun f => 2 * ((θ * aff H x f ((H.sl o).erase s)) * (θ * aff H x f (H.sl o'))))
      (fun f _ => mul_nonneg (by linarith [hu f]) (by linarith [hv f]))
      (fun f _ => by
        have := mul_nonneg (mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f ((H.sl o).erase s)))
          (mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f (H.sl o')))
        linarith)
      (fun f _ => by
        have h1 := hu f; have h2 := hv f
        have h3 := mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f ((H.sl o).erase s))
        have h4 := mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f (H.sl o'))
        nlinarith [mul_le_mul h1 h2 h4 (by linarith)])
      (fun f => 1 - θ * aff H x f ((H.sl o).erase s ∪ H.sl o'))
      (fun f _ => by
        have hsub := aff_union_le (H := H) x hI.x0 f ((H.sl o).erase s) (H.sl o')
        have hf := fac1 (θ * aff H x f ((H.sl o).erase s)) (θ * aff H x f (H.sl o'))
          (mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f _)) (mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f _))
          (by linarith [hu f]) (by linarith [hv f])
        nlinarith [mul_le_mul_of_nonneg_left hsub hθ0])
    have hprodsplit : ∏ f ∈ E, ((1 - θ * aff H x f ((H.sl o).erase s)) * (1 - θ * aff H x f (H.sl o'))) =
        alF H θ x s o * piF H θ x o' := by
      rw [Finset.prod_mul_distrib]; unfold alF piF; rw [hj]
    rw [hprodsplit] at key
    have hpb := piF_bounds θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ o'
    have hsumuv : ∑ f ∈ E, 2 * ((θ * aff H x f ((H.sl o).erase s)) * (θ * aff H x f (H.sl o'))) ≤
        4 * θ ^ 2 * κ := by
      calc ∑ f ∈ E, 2 * ((θ * aff H x f ((H.sl o).erase s)) * (θ * aff H x f (H.sl o')))
          ≤ ∑ f ∈ E, 2 * ((θ * κ) * (θ * aff H x f (H.sl o'))) := by
            refine Finset.sum_le_sum (fun f _ => ?_)
            have := mul_nonneg hθ0 (aff_nonneg (H := H) x hI.x0 f (H.sl o'))
            nlinarith [hu f]
        _ = 2 * θ ^ 2 * κ * ∑ f ∈ E, aff H x f (H.sl o') := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun f _ => by ring)
        _ ≤ 2 * θ ^ 2 * κ * 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            refine le_trans (sum_aff_le (H := H) x hI.x0 (H.sl o') E) ?_
            calc ∑ t ∈ H.sl o', load H x t ≤ ∑ _t ∈ H.sl o', (1 : ℝ) :=
                  Finset.sum_le_sum (fun t _ => by linarith [hI.load t])
              _ ≤ 2 := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast hsl o'
        _ = 4 * θ ^ 2 * κ := by ring
    have hpos : 0 ≤ alF H θ x s o * piF H θ x o' := mul_nonneg hal0 (by linarith [hpb.1])
    calc alF H θ x s o * (1 - 4 * θ ^ 2 * κ) * (1 - 2 * θ)
        ≤ alF H θ x s o * piF H θ x o' * (1 - 4 * θ ^ 2 * κ) := by
          have h4 : 0 ≤ 1 - 4 * θ ^ 2 * κ := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hpb.1 (mul_nonneg hal0 h4)]
      _ ≤ alF H θ x s o * piF H θ x o' * (1 - ∑ f ∈ E, 2 * ((θ * aff H x f ((H.sl o).erase s)) *
            (θ * aff H x f (H.sl o')))) := mul_le_mul_of_nonneg_left (by linarith) hpos
      _ ≤ _ := key
  calc alF H θ x s o * (1 - 4 * θ ^ 2 * κ) * (θ * (1 - 2 * θ) * mass H x (H.job o))
      = ∑ o' ∈ univ.filter (fun o' => H.job o' = H.job o),
          θ * x o' * (alF H θ x s o * (1 - 4 * θ ^ 2 * κ) * (1 - 2 * θ)) := by
        unfold mass; rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun o' _ => by ring)
    _ ≤ _ := Finset.sum_le_sum hterm

theorem mass_pos_alive (σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (o : O) (ho : 0 < x o) :
    1 - δ ≤ mass H x (H.job o) := by
  rcases hI.mass (H.job o) with h | h
  · exfalso
    have : x o ≤ mass H x (H.job o) := by
      unfold mass
      exact Finset.single_le_sum (f := x) (fun o _ => hI.x0 o)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ o, rfl⟩)
    linarith
  · exact h.1

/-- **load drift** -/
theorem load_drift (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1) (s : Sl) :
    EE H θ x (Ya H θ x s) - EE H θ x (Yw H θ x s) ≤
      load H x s * (1 - θ * (1 - 2 * θ) * (1 - 4 * θ ^ 2 * κ) * (1 - δ)) /
        (1 - (1 + 2 * θ * κ) * (θ * load H x s)) := by
  have hL0 : 0 ≤ load H x s := Finset.sum_nonneg (fun o _ => hI.x0 o)
  have hL1 : load H x s ≤ 1 := by linarith [hI.load s]
  set r := (1 + 2 * θ * κ) * (θ * load H x s) with hr
  set q := θ * (1 - 2 * θ) * (1 - 4 * θ ^ 2 * κ) * (1 - δ) with hq
  have hr1 : r ≤ 1 / 2 := by
    rw [hr]; nlinarith [mul_le_mul hL1 hκ1 hκ0 (by norm_num : (0:ℝ) ≤ 1), mul_nonneg hθ0 hκ0,
      mul_nonneg hθ0 hL0, mul_nonneg (mul_nonneg hθ0 hκ0) (mul_nonneg hθ0 hL0)]
  have hq0 : 0 ≤ 1 - q := by
    rw [hq]
    have h1 : 0 ≤ 1 - 4 * θ ^ 2 * κ := by nlinarith
    have h1' : 1 - 4 * θ ^ 2 * κ ≤ 1 := by nlinarith [sq_nonneg θ]
    have h2 : 0 ≤ 1 - 2 * θ := by linarith
    have h3 : 0 ≤ 1 - δ := by linarith
    have h4 : (1 - 2 * θ) * (1 - 4 * θ ^ 2 * κ) * (1 - δ) ≤ 1 := by
      have := mul_le_one₀ (mul_le_one₀ (by linarith : 1 - 2 * θ ≤ 1) h1 h1') h3 (by linarith : 1 - δ ≤ 1)
      linarith
    have h5 : 0 ≤ (1 - 2 * θ) * (1 - 4 * θ ^ 2 * κ) * (1 - δ) := by positivity
    nlinarith
  rw [EE_Ya]
  unfold Yw
  rw [EE_finsum]
  rw [← Finset.sum_sub_distrib]
  have hstep : ∀ o ∈ univ.filter (fun o => s ∈ H.sl o),
      x o / piF H θ x o * alF H θ x s o - EE H θ x (fun Z => x o / piF H θ x o * PT H s o Z * win H Z (H.job o)) ≤
      x o * (1 - q) / (1 - r) := by
    intro o ho
    have hs := (Finset.mem_filter.mp ho).2
    have hpb := piF_bounds θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ o
    have hpos : 0 < piF H θ x o := by linarith [hpb.1]
    have hc : (fun Z => x o / piF H θ x o * PT H s o Z * win H Z (H.job o)) =
        (fun Z => x o / piF H θ x o * (PT H s o Z * win H Z (H.job o))) := by
      funext Z; ring
    rw [hc, EE_smul, EE_PT_win]
    have hlow := PTwin_lower θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ s o hs
    have hal := alF_le θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ s o hs
    have hq0' : 0 ≤ x o / piF H θ x o := div_nonneg (hI.x0 o) hpos.le
    have hal0 : 0 ≤ alF H θ x s o := by
      unfold alF
      refine Finset.prod_nonneg (fun f _ => ?_)
      have := mul_le_mul_of_nonneg_left (aff_le_kappa1 σ δ κ x hI hsl f o s hs) hθ0
      nlinarith
    rcases (hI.x0 o).eq_or_lt with hx | hx
    · rw [← hx]; simp
    · have hm := mass_pos_alive σ δ κ x hI o hx
      have hmult : alF H θ x s o * (1 - (1 - 4 * θ ^ 2 * κ) * (θ * (1 - 2 * θ) * mass H x (H.job o))) ≤
          alF H θ x s o * (1 - q) := by
        apply mul_le_mul_of_nonneg_left _ hal0
        rw [hq]
        have h1 : 0 ≤ 1 - 4 * θ ^ 2 * κ := by nlinarith
        have h2 : 0 ≤ θ * (1 - 2 * θ) := mul_nonneg hθ0 (by linarith)
        nlinarith [mul_le_mul_of_nonneg_left hm (mul_nonneg h2 h1)]
      have hratio : x o / piF H θ x o * alF H θ x s o ≤ x o / (1 - r) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hpos (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_left hal (hI.x0 o)]
      calc x o / piF H θ x o * alF H θ x s o - x o / piF H θ x o *
            ∑ o' ∈ univ.filter (fun o' => H.job o' = H.job o),
              θ * x o' * ∏ f ∈ univ.erase (H.job o), (1 - θ * aff H x f ((H.sl o).erase s ∪ H.sl o'))
          ≤ x o / piF H θ x o * alF H θ x s o - x o / piF H θ x o *
              (alF H θ x s o * (1 - 4 * θ ^ 2 * κ) * (θ * (1 - 2 * θ) * mass H x (H.job o))) := by
            linarith [mul_le_mul_of_nonneg_left hlow hq0']
        _ = x o / piF H θ x o * (alF H θ x s o *
              (1 - (1 - 4 * θ ^ 2 * κ) * (θ * (1 - 2 * θ) * mass H x (H.job o)))) := by ring
        _ ≤ x o / piF H θ x o * (alF H θ x s o * (1 - q)) := mul_le_mul_of_nonneg_left hmult hq0'
        _ = (x o / piF H θ x o * alF H θ x s o) * (1 - q) := by ring
        _ ≤ x o / (1 - r) * (1 - q) := mul_le_mul_of_nonneg_right hratio hq0
        _ = x o * (1 - q) / (1 - r) := by ring
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  rw [← Finset.sum_div, ← Finset.sum_mul]
  rfl

theorem PT_upd (s : Sl) (o : O) (Z : J → Option O) (k : J) (hk : k ≠ H.job o) (y : Option O) :
    PT H s o (Function.update Z k y) = PT H s o (Function.update Z k none) * av H k ((H.sl o).erase s) y := by
  unfold PT
  have hmem : k ∈ univ.erase (H.job o) := Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem]
  simp only [Function.update_self]
  have hr : ∏ f ∈ (univ.erase (H.job o)).erase k, av H f ((H.sl o).erase s) (Function.update Z k y f) =
      ∏ f ∈ (univ.erase (H.job o)).erase k, av H f ((H.sl o).erase s) (Function.update Z k none f) :=
    Finset.prod_congr rfl (fun f hf => by simp [Function.update_of_ne (Finset.ne_of_mem_erase hf)])
  rw [hr]; simp only [av]; ring

theorem PT_upd_self (s : Sl) (o : O) (Z : J → Option O) (y : Option O) :
    PT H s o (Function.update Z (H.job o) y) = PT H s o (Function.update Z (H.job o) none) := by
  unfold PT
  refine Finset.prod_congr rfl (fun f hf => ?_)
  simp [Function.update_of_ne (Finset.ne_of_mem_erase hf)]

/-- the avoidance influence term -/
noncomputable def Da (H : HG J Sl O) (θ : ℝ) (x : O → ℝ) (s : Sl) (k : J) (y : Option O) : ℝ :=
  (1 / (1 - 2 * θ)) * ∑ o ∈ univ.filter (fun o => s ∈ H.sl o), x o * (1 - av H k ((H.sl o).erase s) y)

/-- jobs using slot `s` -/
def As (H : HG J Sl O) (s : Sl) : Finset J := univ.filter (fun e => ∃ o, H.job o = e ∧ s ∈ H.sl o)

theorem one_sub_mul_le (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    1 - a * b ≤ (1 - a) + (1 - b) := by nlinarith

/-- influence of a pick on `Yw` -/
theorem Yw_infl (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (s : Sl) (Z : J → Option O) (k : J)
    (y : Option O) :
    |Yw H θ x s (Function.update Z k y) - Yw H θ x s (Function.update Z k none)| ≤
      Da H θ x s k y + (if y = none then 0 else yw H x k s / (1 - 2 * θ)) +
        ∑ t ∈ psl H y, ∑ e ∈ (As H s).filter (fun e => e ≠ k ∧
          win H (Function.update Z k none) e = 1 ∧ t ∈ psl H (Z e)), yw H x e s / (1 - 2 * θ) := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  by_cases hy : y = none
  · subst hy; simp only [sub_self, abs_zero, if_true, add_zero]
    have : 0 ≤ Da H θ x s k none := by unfold Da; simp [av]
    have h2 : 0 ≤ ∑ t ∈ psl H (none : Option O), ∑ e ∈ (As H s).filter (fun e => e ≠ k ∧
        win H (Function.update Z k none) e = 1 ∧ t ∈ psl H (Z e)), yw H x e s / (1 - 2 * θ) := by simp [psl]
    linarith
  rw [if_neg hy]
  unfold Yw
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  -- split into own-job terms and others
  have hpt : ∀ o ∈ univ.filter (fun o => s ∈ H.sl o),
      |x o / piF H θ x o * PT H s o (Function.update Z k y) * win H (Function.update Z k y) (H.job o) -
        x o / piF H θ x o * PT H s o (Function.update Z k none) * win H (Function.update Z k none) (H.job o)| ≤
      (1 / (1 - 2 * θ)) * (x o * (1 - av H k ((H.sl o).erase s) y)) +
      (if H.job o = k then x o / (1 - 2 * θ) else 0) +
      (if H.job o = k then 0 else x o / (1 - 2 * θ) * win H (Function.update Z k none) (H.job o) *
        (1 - av H k (psl H (Z (H.job o))) y)) := by
    intro o ho
    have hpb := piF_bounds θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ o
    have hpos : 0 < piF H θ x o := by linarith [hpb.1]
    have hq0 : 0 ≤ x o / piF H θ x o := div_nonneg (hI.x0 o) hpos.le
    have hq1 : x o / piF H θ x o ≤ x o / (1 - 2 * θ) := div_le_div_of_nonneg_left (hI.x0 o) hπ hpb.1
    have hxπ : 0 ≤ x o / (1 - 2 * θ) := div_nonneg (hI.x0 o) hπ.le
    have hav0 := av_nonneg (H := H) k ((H.sl o).erase s) y
    have hav1 := av_le_one (H := H) k ((H.sl o).erase s) y
    have hextra0 : 0 ≤ (1 / (1 - 2 * θ)) * (x o * (1 - av H k ((H.sl o).erase s) y)) :=
      mul_nonneg (by positivity) (mul_nonneg (hI.x0 o) (by linarith))
    by_cases hjk : H.job o = k
    · rw [if_pos hjk, if_pos hjk, add_zero]
      subst hjk
      rw [PT_upd_self s o Z y, ← mul_sub]
      have hw0 := win_nonneg (H := H) (Function.update Z (H.job o) y) (H.job o)
      have hw1 := win_le_one (H := H) (Function.update Z (H.job o) y) (H.job o)
      have hw0' := win_nonneg (H := H) (Function.update Z (H.job o) none) (H.job o)
      have hw1' := win_le_one (H := H) (Function.update Z (H.job o) none) (H.job o)
      have hP0 := PT_nonneg (H := H) s o (Function.update Z (H.job o) none)
      have hP1 := PT_le_one (H := H) s o (Function.update Z (H.job o) none)
      rw [abs_mul, abs_of_nonneg (mul_nonneg hq0 hP0)]
      have : |win H (Function.update Z (H.job o) y) (H.job o) - win H (Function.update Z (H.job o) none) (H.job o)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      calc x o / piF H θ x o * PT H s o (Function.update Z (H.job o) none) *
            |win H (Function.update Z (H.job o) y) (H.job o) - win H (Function.update Z (H.job o) none) (H.job o)|
          ≤ x o / (1 - 2 * θ) * 1 * 1 := by
            apply mul_le_mul (mul_le_mul hq1 hP1 hP0 hxπ) this (abs_nonneg _) (by simpa using hxπ)
        _ ≤ _ := by simp only [mul_one]; linarith
    · rw [if_neg hjk, if_neg hjk, add_zero]
      rw [PT_upd s o Z k (Ne.symm hjk) y, win_upd Z k (H.job o) (Ne.symm hjk) y]
      set P := PT H s o (Function.update Z k none)
      set W := win H (Function.update Z k none) (H.job o)
      set aT := av H k ((H.sl o).erase s) y
      set aW := av H k (psl H (Z (H.job o))) y
      have hP0 : 0 ≤ P := PT_nonneg s o _
      have hP1 : P ≤ 1 := PT_le_one s o _
      have hW0 : 0 ≤ W := win_nonneg _ _
      have hW1 : W ≤ 1 := win_le_one _ _
      have haW0 : 0 ≤ aW := av_nonneg _ _ _
      have haW1 : aW ≤ 1 := av_le_one _ _ _
      rw [show x o / piF H θ x o * (P * aT) * (W * aW) - x o / piF H θ x o * P * W =
        -(x o / piF H θ x o * P * W * (1 - aT * aW)) by ring, abs_neg]
      have h1m := one_sub_mul_le aT aW hav0 hav1 haW0 haW1
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hq0 hP0) hW0) (by nlinarith))]
      calc x o / piF H θ x o * P * W * (1 - aT * aW)
          ≤ x o / piF H θ x o * P * W * ((1 - aT) + (1 - aW)) :=
            mul_le_mul_of_nonneg_left h1m (mul_nonneg (mul_nonneg hq0 hP0) hW0)
        _ = x o / piF H θ x o * P * W * (1 - aT) + x o / piF H θ x o * P * W * (1 - aW) := by ring
        _ ≤ x o / (1 - 2 * θ) * (1 - aT) + x o / (1 - 2 * θ) * W * (1 - aW) := by
            apply add_le_add
            · apply mul_le_mul_of_nonneg_right _ (by linarith)
              calc x o / piF H θ x o * P * W ≤ x o / (1 - 2 * θ) * 1 * 1 :=
                    mul_le_mul (mul_le_mul hq1 hP1 hP0 hxπ) hW1 hW0 (by simpa using hxπ)
                _ = x o / (1 - 2 * θ) := by ring
            · apply mul_le_mul_of_nonneg_right _ (by linarith)
              apply mul_le_mul_of_nonneg_right _ hW0
              calc x o / piF H θ x o * P ≤ x o / (1 - 2 * θ) * 1 := mul_le_mul hq1 hP1 hP0 hxπ
                _ = x o / (1 - 2 * θ) := by ring
        _ = (1 / (1 - 2 * θ)) * (x o * (1 - aT)) + x o / (1 - 2 * θ) * W * (1 - aW) := by ring
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  apply add_le_add (add_le_add ?_ ?_) ?_
  · unfold Da; rw [Finset.mul_sum]
  · rw [← Finset.sum_filter]
    unfold yw
    rw [Finset.sum_div]
    apply le_of_eq
    refine Finset.sum_congr ?_ (fun o _ => rfl)
    ext o; simp [and_comm]
  · -- regroup the win part
    set Os := univ.filter (fun o => s ∈ H.sl o)
    have hπ' : 0 ≤ 1 / (1 - 2 * θ) := by positivity
    have h1 : ∀ o ∈ Os, (if H.job o = k then 0 else x o / (1 - 2 * θ) *
        win H (Function.update Z k none) (H.job o) * (1 - av H k (psl H (Z (H.job o))) y)) ≤
        ∑ t ∈ psl H y, (if H.job o ≠ k ∧ win H (Function.update Z k none) (H.job o) = 1 ∧
          t ∈ psl H (Z (H.job o)) then x o / (1 - 2 * θ) else 0) := by
      intro o _
      have hxπ : 0 ≤ x o / (1 - 2 * θ) := div_nonneg (hI.x0 o) hπ.le
      by_cases hjk : H.job o = k
      · rw [if_pos hjk]
        exact Finset.sum_nonneg (fun t _ => by split_ifs <;> first | exact le_rfl | exact hxπ)
      · rw [if_neg hjk]
        rcases win_01 (H := H) (Function.update Z k none) (H.job o) with hw | hw
        · rw [hw, mul_zero, zero_mul]
          exact Finset.sum_nonneg (fun t _ => by split_ifs <;> first | exact le_rfl | exact hxπ)
        · rw [hw, mul_one]
          have := one_sub_av_le (H := H) k (psl H (Z (H.job o))) y
          calc x o / (1 - 2 * θ) * (1 - av H k (psl H (Z (H.job o))) y)
              ≤ x o / (1 - 2 * θ) * ∑ t ∈ psl H y, (if t ∈ psl H (Z (H.job o)) then 1 else 0) :=
                mul_le_mul_of_nonneg_left this hxπ
            _ = _ := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun t _ => ?_)
                by_cases ht : t ∈ psl H (Z (H.job o))
                · rw [if_pos ht, if_pos ⟨hjk, rfl, ht⟩, mul_one]
                · rw [if_neg ht, if_neg (fun h => ht h.2.2), mul_zero]
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun t _ => ?_)
    rw [← Finset.sum_fiberwise_of_maps_to (s := Os) (t := As H s) (g := H.job)
      (fun o ho => Finset.mem_filter.mpr ⟨Finset.mem_univ _, o, rfl, (Finset.mem_filter.mp ho).2⟩)]
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun e he => ?_)
    by_cases hc : e ≠ k ∧ win H (Function.update Z k none) e = 1 ∧ t ∈ psl H (Z e)
    · rw [if_pos hc]
      unfold yw
      rw [Finset.sum_div]
      apply le_of_eq
      rw [Finset.filter_filter]
      refine Finset.sum_congr ?_ (fun o ho => ?_)
      · ext o; simp [Os]; tauto
      · have hj := (Finset.mem_filter.mp ho).2.1
        rw [if_pos (by rw [hj]; exact hc)]
    · rw [if_neg hc]
      refine le_of_eq (Finset.sum_eq_zero (fun o ho => ?_))
      have hj := (Finset.mem_filter.mp ho).2
      rw [if_neg (by rw [hj]; exact hc)]

theorem Ya_infl (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (s : Sl) (Z : J → Option O) (k : J)
    (y : Option O) :
    |Ya H θ x s (Function.update Z k y) - Ya H θ x s (Function.update Z k none)| ≤ Da H θ x s k y := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  unfold Ya Da
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun o _ => ?_))
  have hpb := piF_bounds θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ o
  have hpos : 0 < piF H θ x o := by linarith [hpb.1]
  have hq0 : 0 ≤ x o / piF H θ x o := div_nonneg (hI.x0 o) hpos.le
  have hq1 : x o / piF H θ x o ≤ x o / (1 - 2 * θ) := div_le_div_of_nonneg_left (hI.x0 o) hπ hpb.1
  have hav0 := av_nonneg (H := H) k ((H.sl o).erase s) y
  have hav1 := av_le_one (H := H) k ((H.sl o).erase s) y
  by_cases hjk : k = H.job o
  · subst hjk
    rw [PT_upd_self s o Z y, sub_self, abs_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (hI.x0 o) (by linarith))
  · rw [PT_upd s o Z k hjk y]
    have hP0 := PT_nonneg (H := H) s o (Function.update Z k none)
    have hP1 := PT_le_one (H := H) s o (Function.update Z k none)
    rw [show x o / piF H θ x o * (PT H s o (Function.update Z k none) * av H k ((H.sl o).erase s) y) -
      x o / piF H θ x o * PT H s o (Function.update Z k none) =
      -(x o / piF H θ x o * PT H s o (Function.update Z k none) * (1 - av H k ((H.sl o).erase s) y)) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (mul_nonneg hq0 hP0) (by linarith))]
    calc x o / piF H θ x o * PT H s o (Function.update Z k none) * (1 - av H k ((H.sl o).erase s) y)
        ≤ x o / (1 - 2 * θ) * 1 * (1 - av H k ((H.sl o).erase s) y) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hq1 hP1 hP0 (div_nonneg (hI.x0 o) hπ.le)) (by linarith)
      _ = 1 / (1 - 2 * θ) * (x o * (1 - av H k ((H.sl o).erase s) y)) := by ring

theorem meet_le_kw (x : O → ℝ) (hx : ∀ o, 0 ≤ x o) (s : Sl) (o'' : O) :
    ∑ o ∈ univ.filter (fun o => s ∈ H.sl o), x o * (if Disjoint (H.sl o'') ((H.sl o).erase s) then 0 else 1) ≤
      ∑ t ∈ (H.sl o'').erase s, kw H x s t := by
  unfold kw
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun o _ => ?_)
  by_cases hs : s ∈ H.sl o
  · rw [if_pos hs]
    by_cases hd : Disjoint (H.sl o'') ((H.sl o).erase s)
    · rw [if_pos hd, mul_zero]
      exact Finset.sum_nonneg (fun t _ => by split_ifs <;> first | exact le_rfl | exact hx o)
    · rw [if_neg hd, mul_one]
      obtain ⟨t, ht1, ht2⟩ := Finset.not_disjoint_iff.mp hd
      have htne : t ≠ s := Finset.ne_of_mem_erase ht2
      have hto : t ∈ H.sl o := Finset.mem_of_mem_erase ht2
      have := Finset.single_le_sum (f := fun t => if s ∈ H.sl o ∧ t ∈ H.sl o then x o else 0)
        (fun t _ => by split_ifs <;> first | exact le_rfl | exact hx o)
        (Finset.mem_erase.mpr ⟨htne, ht1⟩)
      simpa [hs, hto] using this
  · rw [if_neg hs]
    exact Finset.sum_nonneg (fun t _ => by split_ifs <;> first | exact le_rfl | exact hx o)

theorem Da_some (θ : ℝ) (x : O → ℝ) (s : Sl) (k : J) (o'' : O) :
    Da H θ x s k (some o'') = if H.job o'' = k then (1 / (1 - 2 * θ)) * ∑ o ∈ univ.filter (fun o => s ∈ H.sl o),
      x o * (if Disjoint (H.sl o'') ((H.sl o).erase s) then 0 else 1) else 0 := by
  unfold Da
  split_ifs with hj
  · congr 1
    refine Finset.sum_congr rfl (fun o _ => ?_)
    simp only [av, hj, true_and]
    by_cases hd : Disjoint (H.sl o'') ((H.sl o).erase s)
    · have : Disjoint (H.sl o'') ((H.sl o).erase s) := hd
      simp [hd]
    · simp [hd]
  · simp [av, hj]

theorem Da_le (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ0 : 0 ≤ κ) (s : Sl) (k : J) (y : Option O) :
    Da H θ x s k y ≤ 2 * κ / (1 - 2 * θ) := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  have hr : 0 ≤ 2 * κ / (1 - 2 * θ) := by positivity
  cases y with
  | none => unfold Da; simp [av]; exact hr
  | some o'' =>
    rw [Da_some]
    split_ifs
    · have h1 := meet_le_kw (H := H) x hI.x0 s o''
      have h2 : ∑ t ∈ (H.sl o'').erase s, kw H x s t ≤ 2 * κ := by
        calc ∑ t ∈ (H.sl o'').erase s, kw H x s t ≤ ∑ _t ∈ (H.sl o'').erase s, κ :=
              Finset.sum_le_sum (fun t ht => hI.cod2 s t (Ne.symm (Finset.ne_of_mem_erase ht)))
          _ ≤ 2 * κ := by
              rw [Finset.sum_const, nsmul_eq_mul]
              have : (((H.sl o'').erase s).card : ℝ) ≤ 2 := by
                have := Finset.card_erase_le (s := H.sl o'') (a := s)
                exact_mod_cast le_trans this (hsl o'')
              nlinarith
      have h3 := le_trans h1 h2
      calc 1 / (1 - 2 * θ) * ∑ o ∈ univ.filter (fun o => s ∈ H.sl o),
            x o * (if Disjoint (H.sl o'') ((H.sl o).erase s) then 0 else 1)
          ≤ 1 / (1 - 2 * θ) * (2 * κ) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 2 * κ / (1 - 2 * θ) := by ring
    · exact hr

/-- generic variance bound for influences dominated by slot sums -/
theorem VS_gen (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (F : J → Option O → ℝ) (g : Sl → ℝ) (hg0 : ∀ t, 0 ≤ g t)
    (hF0 : ∀ k y, 0 ≤ F k y) (hF : ∀ k y, F k y ≤ ∑ t ∈ psl H y, g t) :
    ∑ k, ∑ y, pp H θ x k y * F k y ^ 2 ≤ 2 * θ * ∑ t, load H x t * g t ^ 2 := by
  have hstep : ∀ k, ∑ y, pp H θ x k y * F k y ^ 2 ≤
      ∑ o ∈ univ.filter (fun o => H.job o = k), θ * x o * (2 * ∑ t ∈ H.sl o, g t ^ 2) := by
    intro k
    rw [Fintype.sum_option]
    have hnone : F k none = 0 := le_antisymm (by simpa [psl] using hF k none) (hF0 k none)
    rw [hnone]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
    rw [sum_pp_some]
    refine Finset.sum_le_sum (fun o _ => mul_le_mul_of_nonneg_left ?_ (mul_nonneg hθ0 (hI.x0 o)))
    have h1 := hF k (some o)
    simp only [psl] at h1
    have h2 := sq_sum_le_card_mul_sum_sq (s := H.sl o) (f := g)
    have h3 : ((H.sl o).card : ℝ) ≤ 2 := by exact_mod_cast hsl o
    have h4 : 0 ≤ ∑ t ∈ H.sl o, g t ^ 2 := Finset.sum_nonneg (fun t _ => sq_nonneg _)
    have h5 : F k (some o) ^ 2 ≤ (∑ t ∈ H.sl o, g t) ^ 2 := pow_le_pow_left₀ (hF0 k _) h1 2
    nlinarith
  refine le_trans (Finset.sum_le_sum (fun k _ => hstep k)) ?_
  rw [Finset.sum_fiberwise (s := univ) (g := H.job) (f := fun o => θ * x o * (2 * ∑ t ∈ H.sl o, g t ^ 2))]
  have e1 : ∑ o, θ * x o * (2 * ∑ t ∈ H.sl o, g t ^ 2) = 2 * θ * ∑ o, x o * ∑ t ∈ H.sl o, g t ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun o _ => by ring)
  rw [e1, sum_x_sl x (fun t => g t ^ 2)]

theorem sum_kw_le (σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2) (s : Sl) :
    ∑ t ∈ univ.erase s, kw H x s t ≤ load H x s := by
  unfold kw load
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun o _ => ?_)
  by_cases hs : s ∈ H.sl o
  · rw [if_pos hs]
    simp only [hs, true_and]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : (((univ.erase s).filter (fun t => t ∈ H.sl o)).card : ℝ) ≤ 1 := by
      have h1 : (univ.erase s).filter (fun t => t ∈ H.sl o) = (H.sl o).erase s := by
        ext t; simp [and_comm]
      rw [h1]
      have := Finset.card_erase_of_mem hs
      have h2 := hsl o
      exact_mod_cast (show ((H.sl o).erase s).card ≤ 1 by omega)
    nlinarith [hI.x0 o]
  · rw [if_neg hs]
    simp [hs]

theorem cw_le (S : Finset J) (c : J → ℝ) (hc0 : ∀ e, 0 ≤ c e) (cm : ℝ) (hcm0 : 0 ≤ cm)
    (hcm : ∀ e, c e ≤ cm) (a : J → Option O) (t : Sl) : cw H S c a t ≤ cm := by
  unfold cw
  set F := S.filter (fun e => actv H S a e ∧ t ∈ psl H (a e))
  by_cases hne : F.Nonempty
  · obtain ⟨e, he⟩ := hne
    have huniq : F = {e} := by
      ext e'
      simp only [Finset.mem_singleton]
      constructor
      · intro he'
        by_contra hne'
        have m1 := Finset.mem_filter.mp he
        have m2 := Finset.mem_filter.mp he'
        have := actv_disjoint S a e e' m1.1 m2.1 (Ne.symm hne') m1.2.1 m2.2.1
        exact Finset.disjoint_left.mp this m1.2.2 m2.2.2
      · intro h; rw [h]; exact he
    rw [huniq, Finset.sum_singleton]; exact hcm e
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]; exact hcm0

theorem sum_cw_le' (S : Finset J) (c : J → ℝ) (hc0 : ∀ e, 0 ≤ c e)
    (hsl : ∀ o, (H.sl o).card ≤ 2) (a : J → Option O) :
    ∑ t, cw H S c a t ≤ 2 * ∑ e ∈ S, c e := by
  unfold cw
  have : ∀ t, ∑ e ∈ S.filter (fun e => actv H S a e ∧ t ∈ psl H (a e)), c e ≤
      ∑ e ∈ S, (if t ∈ psl H (a e) then c e else 0) := by
    intro t
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun e _ => ?_)
    by_cases h1 : actv H S a e ∧ t ∈ psl H (a e)
    · rw [if_pos h1, if_pos h1.2]
    · rw [if_neg h1]; split_ifs <;> first | exact le_rfl | exact hc0 e
  refine le_trans (Finset.sum_le_sum (fun t _ => this t)) ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun e _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((univ.filter (fun t => t ∈ psl H (a e))).card : ℝ) ≤ 2 := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact_mod_cast card_psl_le hsl (a e)
  nlinarith [hc0 e]

theorem Da_le_sum (θ : ℝ) (hθ : θ ≤ 1 / 16) (x : O → ℝ) (hx : ∀ o, 0 ≤ x o) (s : Sl) (k : J) (y : Option O) :
    Da H θ x s k y ≤ ∑ t ∈ psl H y, (if t = s then 0 else kw H x s t / (1 - 2 * θ)) := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  cases y with
  | none => unfold Da; simp [av, psl]
  | some o'' =>
    rw [Da_some]
    split_ifs with hj
    · have h1 := meet_le_kw (H := H) x hx s o''
      simp only [psl]
      have h2 : ∑ t ∈ H.sl o'', (if t = s then (0 : ℝ) else kw H x s t / (1 - 2 * θ)) =
          (1 / (1 - 2 * θ)) * ∑ t ∈ (H.sl o'').erase s, kw H x s t := by
        rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not (H.sl o'') (fun t => t = s)]
        rw [Finset.sum_eq_zero (fun t ht => by rw [if_pos (Finset.mem_filter.mp ht).2]), zero_add]
        rw [show (H.sl o'').filter (fun t => ¬t = s) = (H.sl o'').erase s by ext; simp [and_comm]]
        refine Finset.sum_congr rfl (fun t ht => ?_)
        rw [if_neg (Finset.ne_of_mem_erase ht)]; ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    · exact Finset.sum_nonneg (fun t _ => by
        split_ifs; exact le_rfl
        exact div_nonneg (Finset.sum_nonneg (fun o _ => hx o)) hπ.le)

theorem Da_nonneg (θ : ℝ) (hθ : θ ≤ 1 / 16) (x : O → ℝ) (hx : ∀ o, 0 ≤ x o) (s : Sl) (k : J) (y : Option O) :
    0 ≤ Da H θ x s k y := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  unfold Da
  refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun o _ => mul_nonneg (hx o) ?_))
  linarith [av_le_one (H := H) k ((H.sl o).erase s) y]

theorem V_Da (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ0 : 0 ≤ κ) (hσ : 0 ≤ σ) (s : Sl) :
    ∑ k, ∑ y, pp H θ x k y * Da H θ x s k y ^ 2 ≤ 2 * θ * κ / (1 - 2 * θ) ^ 2 := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  set g : Sl → ℝ := fun t => if t = s then 0 else kw H x s t / (1 - 2 * θ)
  have hg0 : ∀ t, 0 ≤ g t := fun t => by
    simp only [g]; split_ifs; exact le_rfl
    exact div_nonneg (Finset.sum_nonneg (fun o _ => hI.x0 o)) hπ.le
  refine le_trans (VS_gen θ σ δ κ x hI hsl hθ0 (Da H θ x s) g hg0 (Da_nonneg θ hθ x hI.x0 s)
    (Da_le_sum θ hθ x hI.x0 s)) ?_
  have h1 : ∀ t, load H x t * g t ^ 2 ≤ (if t = s then 0 else κ / (1 - 2 * θ) ^ 2 * kw H x s t) := by
    intro t
    simp only [g]
    split_ifs with hts
    · simp
    · have hl := hI.load t
      have hl0 : 0 ≤ load H x t := Finset.sum_nonneg (fun o _ => hI.x0 o)
      have hk := hI.cod2 s t (Ne.symm hts)
      have hk0 : 0 ≤ kw H x s t := Finset.sum_nonneg (fun o _ => hI.x0 o)
      rw [div_pow]
      have : kw H x s t ^ 2 ≤ κ * kw H x s t := by nlinarith
      calc load H x t * (kw H x s t ^ 2 / (1 - 2 * θ) ^ 2) ≤ 1 * (κ * kw H x s t / (1 - 2 * θ) ^ 2) := by
            apply mul_le_mul (by linarith) (div_le_div_of_nonneg_right this (by positivity))
              (by positivity) (by norm_num)
        _ = κ / (1 - 2 * θ) ^ 2 * kw H x s t := by ring
  have h2 : ∑ t, (if t = s then 0 else κ / (1 - 2 * θ) ^ 2 * kw H x s t) ≤ κ / (1 - 2 * θ) ^ 2 := by
    have hite : ∀ t, (if t = s then (0 : ℝ) else κ / (1 - 2 * θ) ^ 2 * kw H x s t) =
        if t ≠ s then κ / (1 - 2 * θ) ^ 2 * kw H x s t else 0 := fun t => by split_ifs <;> simp_all
    simp_rw [hite]
    rw [← Finset.sum_filter, show univ.filter (fun t => t ≠ s) = univ.erase s by ext; simp,
      ← Finset.mul_sum]
    have h3 := sum_kw_le σ δ κ x hI hsl s
    have h4 : load H x s ≤ 1 := by linarith [hI.load s]
    calc κ / (1 - 2 * θ) ^ 2 * ∑ t ∈ univ.erase s, kw H x s t ≤ κ / (1 - 2 * θ) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = κ / (1 - 2 * θ) ^ 2 := by ring
  calc 2 * θ * ∑ t, load H x t * g t ^ 2 ≤ 2 * θ * (κ / (1 - 2 * θ) ^ 2) :=
        mul_le_mul_of_nonneg_left (le_trans (Finset.sum_le_sum (fun t _ => h1 t)) h2) (by positivity)
    _ = 2 * θ * κ / (1 - 2 * θ) ^ 2 := by ring

/-- **load event (a)**: `Ya` rarely exceeds its mean -/
theorem Ya_upper (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (hδ : δ ≤ 1)
    (s : Sl) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    EE H θ x (fun Z => if 2 * Real.sqrt (2 * θ * κ / (1 - 2 * θ) ^ 2 * Λ) + 2 * (4 * κ / (1 - 2 * θ)) * Λ ≤
      Ya H θ x s Z - EE H θ x (Ya H θ x s) then 1 else 0) ≤ Real.exp (-Λ) := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  have hp0 := pp_nonneg' θ σ δ κ x hI hθ0 hθ hδ
  have hp1 : ∀ k, ∑ y, pp H θ x k y = 1 := fun k => sum_pp θ x k
  have key := (OneStage.dev_of_infl (pp H θ x) hp0 hp1 (Ya H θ x s) none (Da H θ x s) (4 * κ / (1 - 2 * θ))
    (by positivity) (fun Z k y => Ya_infl θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ s Z k y)
    (fun k y => by
      have := Da_le θ σ δ κ x hI hsl hθ0 hθ hκ0.le s k y
      have e : 2 * (2 * κ / (1 - 2 * θ)) = 4 * κ / (1 - 2 * θ) := by ring
      linarith) Λ hΛ).1
  refine le_trans ?_ key
  show wE (pp H θ x) _ ≤ wE (pp H θ x) _
  refine wE_mono _ hp0 _ _ (fun Z => ?_)
  have hV := V_Da θ σ δ κ x hI hsl hθ0 hθ hκ0.le hσ s
  have hs : Real.sqrt ((∑ k, ∑ y, pp H θ x k y * Da H θ x s k y ^ 2) * Λ) ≤
      Real.sqrt (2 * θ * κ / (1 - 2 * θ) ^ 2 * Λ) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hV hΛ)
  have hE : EE H θ x (Ya H θ x s) = ∑ Z' : J → Option O, (∏ k, pp H θ x k (Z' k)) * Ya H θ x s Z' := rfl
  by_cases h1 : 2 * Real.sqrt (2 * θ * κ / (1 - 2 * θ) ^ 2 * Λ) + 2 * (4 * κ / (1 - 2 * θ)) * Λ ≤
      Ya H θ x s Z - EE H θ x (Ya H θ x s)
  · rw [if_pos h1, if_pos (by rw [← hE]; linarith)]
  · rw [if_neg h1]; split_ifs <;> norm_num

theorem yw_zero_of_not_As (x : O → ℝ) (s : Sl) (k : J) (hk : k ∉ As H s) : yw H x k s = 0 := by
  unfold yw
  refine Finset.sum_eq_zero (fun o ho => ?_)
  exfalso; apply hk
  have := (Finset.mem_filter.mp ho).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, o, this.1, this.2⟩

theorem sum_yw_As (x : O → ℝ) (s : Sl) : ∑ e ∈ As H s, yw H x e s ≤ load H x s := by
  have : ∑ e ∈ As H s, yw H x e s = ∑ e, yw H x e s := by
    refine Finset.sum_subset (Finset.subset_univ _) (fun e _ he => yw_zero_of_not_As x s e he)
  rw [this, sum_yw]

/-- **load event (b)**: `Yw` rarely falls far below its mean -/
theorem Yw_lower (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (hδ : δ ≤ 1)
    (s : Sl) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    EE H θ x (fun Z => if Yw H θ x s Z ≤ EE H θ x (Yw H θ x s) -
      ((2 * Real.sqrt (12 * θ * κ / (1 - 2 * θ) ^ 2 * Λ) + 2 * (8 * κ / (1 - 2 * θ)) * Λ) +
        (2 * Real.sqrt (50 * θ * κ ^ 2 * (As H s).card / (1 - 2 * θ) ^ 2 * Λ) +
          2 * (10 * κ / (1 - 2 * θ)) * Λ)) then 1 else 0) ≤
      Real.exp (-Λ) + Real.exp (-Λ) := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  have hp0 := pp_nonneg' θ σ δ κ x hI hθ0 hθ hδ
  have hp1 : ∀ k, ∑ y, pp H θ x k y = 1 := fun k => sum_pp θ x k
  set A := As H s
  set cs : J → ℝ := fun e => yw H x e s / (1 - 2 * θ)
  set cm := κ / (1 - 2 * θ)
  have hcs0 : ∀ e, 0 ≤ cs e := fun e => div_nonneg (Finset.sum_nonneg (fun o _ => hI.x0 o)) hπ.le
  have hcm0 : 0 ≤ cm := by positivity
  have hcsm : ∀ e, cs e ≤ cm := fun e => div_le_div_of_nonneg_right (hI.cod1 e s) hπ.le
  show wE (pp H θ x) _ ≤ _
  have hEE : EE H θ x (Yw H θ x s) = wE (pp H θ x) (Yw H θ x s) := rfl
  rw [hEE]
  refine two_stage_lower (pp H θ x) hp0 hp1 A none (Yw H θ x s) _ _ _ _ ?_ ?_
  · -- B stage
    intro a
    rw [cond_as_free (pp H θ x) A a none, cond_as_free (pp H θ x) A a none (Yw H θ x s)]
    set pB := condp (pp H θ x) A (fun _ => none)
    have hpB0 := condp_free_nonneg (pp H θ x) hp0 A none
    have hpB1 := condp_free_sum (pp H θ x) hp1 A none
    set DB : J → Option O → ℝ := fun k y => if k ∈ A then 0 else Da H θ x s k y + ∑ t ∈ psl H y, cw H A cs a t
    have hDB0 : ∀ k y, 0 ≤ DB k y := fun k y => by
      simp only [DB]; split_ifs; exact le_rfl
      exact add_nonneg (Da_nonneg θ hθ x hI.x0 s k y) (Finset.sum_nonneg (fun t _ => cw_nonneg A cs hcs0 a t))
    have key := (OneStage.dev_of_infl pB hpB0 hpB1 (fun Z => Yw H θ x s (merge A a Z)) none DB
      (8 * κ / (1 - 2 * θ)) (by positivity) ?_ ?_ Λ hΛ).2
    · refine le_trans ?_ key
      refine thr_mono pB hpB0 _ _ _ _ ?_
      -- variance
      set g : Sl → ℝ := fun t => (if t = s then 0 else kw H x s t / (1 - 2 * θ)) + cw H A cs a t
      have hg0 : ∀ t, 0 ≤ g t := fun t => add_nonneg (by
        split_ifs; exact le_rfl
        exact div_nonneg (Finset.sum_nonneg (fun o _ => hI.x0 o)) hπ.le) (cw_nonneg A cs hcs0 a t)
      have hDBg : ∀ k y, DB k y ≤ ∑ t ∈ psl H y, g t := by
        intro k y
        simp only [DB, g]
        split_ifs
        · exact Finset.sum_nonneg (fun t _ => hg0 t)
        · rw [Finset.sum_add_distrib]
          exact add_le_add (Da_le_sum θ hθ x hI.x0 s k y) le_rfl
      have hVeq : ∑ k, ∑ y, pB k y * DB k y ^ 2 = ∑ k, ∑ y, pp H θ x k y * DB k y ^ 2 := by
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun y _ => ?_))
        by_cases hk : k ∈ A
        · simp [DB, hk]
        · simp [pB, condp, hk]
      have hV1 := VS_gen θ σ δ κ x hI hsl hθ0 DB g hg0 hDB0 hDBg
      have hV2 : 2 * θ * ∑ t, load H x t * g t ^ 2 ≤ 12 * θ * κ / (1 - 2 * θ) ^ 2 := by
        have hga : ∑ t, (if t = s then 0 else kw H x s t / (1 - 2 * θ)) ^ 2 ≤ κ / (1 - 2 * θ) ^ 2 := by
          have hite : ∀ t, (if t = s then (0 : ℝ) else kw H x s t / (1 - 2 * θ)) ^ 2 =
              if t ≠ s then kw H x s t ^ 2 / (1 - 2 * θ) ^ 2 else 0 := fun t => by
            split_ifs <;> simp_all [div_pow]
          simp_rw [hite]
          rw [← Finset.sum_filter, show univ.filter (fun t => t ≠ s) = univ.erase s by ext; simp,
            ← Finset.sum_div]
          rw [div_le_div_iff_of_pos_right (by positivity)]
          calc ∑ t ∈ univ.erase s, kw H x s t ^ 2 ≤ ∑ t ∈ univ.erase s, κ * kw H x s t := by
                refine Finset.sum_le_sum (fun t ht => ?_)
                have hk := hI.cod2 s t (Ne.symm (Finset.ne_of_mem_erase ht))
                have hk0 : 0 ≤ kw H x s t := Finset.sum_nonneg (fun o _ => hI.x0 o)
                nlinarith
            _ = κ * ∑ t ∈ univ.erase s, kw H x s t := by rw [Finset.mul_sum]
            _ ≤ κ * 1 := by
                apply mul_le_mul_of_nonneg_left _ hκ0.le
                linarith [sum_kw_le σ δ κ x hI hsl s, hI.load s]
            _ = κ := by ring
        have hcw2 : ∑ t, cw H A cs a t ^ 2 ≤ cm * (2 / (1 - 2 * θ)) := by
          calc ∑ t, cw H A cs a t ^ 2 ≤ ∑ t, cm * cw H A cs a t := by
                refine Finset.sum_le_sum (fun t _ => ?_)
                have h1 := cw_le (H := H) A cs hcs0 cm hcm0 hcsm a t
                have h2 := cw_nonneg (H := H) A cs hcs0 a t
                nlinarith
            _ = cm * ∑ t, cw H A cs a t := by rw [Finset.mul_sum]
            _ ≤ cm * (2 / (1 - 2 * θ)) := by
                apply mul_le_mul_of_nonneg_left _ hcm0
                refine le_trans (sum_cw_le' (H := H) A cs hcs0 hsl a) ?_
                have h3 : ∑ e ∈ A, cs e ≤ 1 / (1 - 2 * θ) := by
                  simp only [cs]
                  rw [← Finset.sum_div]
                  apply div_le_div_of_nonneg_right _ hπ.le
                  linarith [sum_yw_As (H := H) x s, hI.load s]
                calc 2 * ∑ e ∈ A, cs e ≤ 2 * (1 / (1 - 2 * θ)) := by linarith
                  _ = 2 / (1 - 2 * θ) := by ring
        have hsum : ∑ t, load H x t * g t ^ 2 ≤ 2 * (κ / (1 - 2 * θ) ^ 2) + 2 * (cm * (2 / (1 - 2 * θ))) := by
          calc ∑ t, load H x t * g t ^ 2 ≤ ∑ t, g t ^ 2 := by
                refine Finset.sum_le_sum (fun t _ => ?_)
                have hl := hI.load t
                have hl0 : 0 ≤ load H x t := Finset.sum_nonneg (fun o _ => hI.x0 o)
                have := sq_nonneg (g t)
                nlinarith
            _ ≤ ∑ t, (2 * (if t = s then 0 else kw H x s t / (1 - 2 * θ)) ^ 2 + 2 * cw H A cs a t ^ 2) := by
                refine Finset.sum_le_sum (fun t _ => ?_)
                simp only [g]
                nlinarith [sq_nonneg ((if t = s then 0 else kw H x s t / (1 - 2 * θ)) - cw H A cs a t)]
            _ = 2 * ∑ t, (if t = s then 0 else kw H x s t / (1 - 2 * θ)) ^ 2 + 2 * ∑ t, cw H A cs a t ^ 2 := by
                rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
            _ ≤ 2 * (κ / (1 - 2 * θ) ^ 2) + 2 * (cm * (2 / (1 - 2 * θ))) := by linarith
        calc 2 * θ * ∑ t, load H x t * g t ^ 2 ≤ 2 * θ * (2 * (κ / (1 - 2 * θ) ^ 2) + 2 * (cm * (2 / (1 - 2 * θ)))) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = 12 * θ * κ / (1 - 2 * θ) ^ 2 := by simp only [cm]; field_simp; ring
      have : Real.sqrt ((∑ k, ∑ y, pB k y * DB k y ^ 2) * Λ) ≤ Real.sqrt (12 * θ * κ / (1 - 2 * θ) ^ 2 * Λ) := by
        rw [hVeq]
        exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (le_trans hV1 hV2) hΛ)
      linarith
    · intro Z k y
      by_cases hk : k ∈ A
      · simp only [DB, hk, if_true]
        rw [merge_upd_S A a Z k hk, merge_upd_S A a Z k hk, sub_self, abs_zero]
      · simp only [DB, hk, if_false]
        rw [merge_upd_out A a Z k hk, merge_upd_out A a Z k hk]
        refine le_trans (Yw_infl θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ s (merge A a Z) k y) ?_
        rw [yw_zero_of_not_As x s k hk, zero_div]
        simp only [ite_self, add_zero]
        apply add_le_add le_rfl
        refine Finset.sum_le_sum (fun t _ => ?_)
        unfold cw
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => hcs0 e)
        intro e he
        rw [Finset.mem_filter] at he ⊢
        obtain ⟨heA, _, hw, ht⟩ := he
        refine ⟨heA, ?_, ?_⟩
        · rw [← merge_upd_out A a Z k hk] at hw
          exact winner_actv A a _ e heA hw
        · have : merge A a Z e = a e := by unfold merge; rw [if_pos heA]
          rw [this] at ht; exact ht
    · intro k y
      simp only [DB]
      split_ifs
      · rw [mul_zero]; positivity
      · have h1 := Da_le θ σ δ κ x hI hsl hθ0 hθ hκ0.le s k y
        have h2 : ∑ t ∈ psl H y, cw H A cs a t ≤ 2 * cm := by
          calc _ ≤ ∑ _t ∈ psl H y, cm := Finset.sum_le_sum (fun t _ => cw_le (H := H) A cs hcs0 cm hcm0 hcsm a t)
            _ ≤ 2 * cm := by
                rw [Finset.sum_const, nsmul_eq_mul]
                have : ((psl H y).card : ℝ) ≤ 2 := by exact_mod_cast card_psl_le hsl y
                nlinarith
        have e1 : 2 * (2 * κ / (1 - 2 * θ) + 2 * cm) = 8 * κ / (1 - 2 * θ) := by simp only [cm]; ring
        linarith
  · -- A stage
    rw [← E_cond_eq (pp H θ x) hp1 A none (Yw H θ x s)]
    set DA : J → Option O → ℝ := fun k y => if k ∈ A ∧ y ≠ none then 5 * κ / (1 - 2 * θ) else 0
    have key := (OneStage.dev_of_infl (pp H θ x) hp0 hp1 (fun Z => wE (condp (pp H θ x) A Z) (Yw H θ x s))
      none DA (10 * κ / (1 - 2 * θ)) (by positivity) ?_ ?_ Λ hΛ).2
    · refine le_trans ?_ key
      refine thr_mono (pp H θ x) hp0 _ _ _ _ ?_
      have hV : ∑ k, ∑ y, pp H θ x k y * DA k y ^ 2 ≤ 50 * θ * κ ^ 2 * A.card / (1 - 2 * θ) ^ 2 := by
        have hstep : ∀ k, ∑ y, pp H θ x k y * DA k y ^ 2 =
            if k ∈ A then (5 * κ / (1 - 2 * θ)) ^ 2 * (θ * mass H x k) else 0 := by
          intro k
          rw [Fintype.sum_option]
          by_cases hk : k ∈ A
          · simp only [DA, hk, true_and, ne_eq, not_true_eq_false, if_false, reduceCtorEq,
              not_false_eq_true, if_true]
            simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
            rw [sum_pp_some θ x k (fun _ => (5 * κ / (1 - 2 * θ)) ^ 2), mass, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun o _ => by ring)
          · simp [DA, hk]
        simp_rw [hstep]
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        calc ∑ k ∈ A, (5 * κ / (1 - 2 * θ)) ^ 2 * (θ * mass H x k) ≤ ∑ _k ∈ A, (5 * κ / (1 - 2 * θ)) ^ 2 * (θ * 2) := by
              refine Finset.sum_le_sum (fun k _ => ?_)
              have hm : mass H x k ≤ 2 := by
                rcases hI.mass k with h | h
                · rw [h]; norm_num
                · linarith [h.2]
              apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
              exact mul_le_mul_of_nonneg_left hm hθ0
          _ = 50 * θ * κ ^ 2 * A.card / (1 - 2 * θ) ^ 2 := by
              rw [Finset.sum_const, nsmul_eq_mul]; field_simp; ring
      have : Real.sqrt ((∑ k, ∑ y, pp H θ x k y * DA k y ^ 2) * Λ) ≤
          Real.sqrt (50 * θ * κ ^ 2 * A.card / (1 - 2 * θ) ^ 2 * Λ) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hV hΛ)
      linarith
    · intro Z k y
      by_cases hk : k ∈ A
      · have hB := cond_infl (pp H θ x) hp0 hp1 A none (Yw H θ x s) (Function.update Z k y)
          (Function.update Z k none) (if y = none then 0 else 5 * κ / (1 - 2 * θ)) (fun Z' => by
            rw [merge_upd_mem A Z Z' k hk, merge_upd_mem A Z Z' k hk]
            refine le_trans (Yw_infl θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ s (merge A Z Z') k y) ?_
            by_cases hy : y = none
            · subst hy
              simp only [if_true, psl, Finset.sum_empty, add_zero]
              unfold Da; simp [av]
            · rw [if_neg hy, if_neg hy]
              have h1 := Da_le θ σ δ κ x hI hsl hθ0 hθ hκ0.le s k y
              have h2 : yw H x k s / (1 - 2 * θ) ≤ κ / (1 - 2 * θ) :=
                div_le_div_of_nonneg_right (hI.cod1 k s) hπ.le
              have h3 : ∑ t ∈ psl H y, ∑ e ∈ A.filter (fun e => e ≠ k ∧
                  win H (Function.update (merge A Z Z') k none) e = 1 ∧ t ∈ psl H (merge A Z Z' e)), cs e ≤
                  2 * cm := by
                calc _ ≤ ∑ _t ∈ psl H y, cm := by
                      refine Finset.sum_le_sum (fun t _ => ?_)
                      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := A.filter (fun e =>
                        win H (Function.update (merge A Z Z') k none) e = 1 ∧
                          t ∈ psl H (Function.update (merge A Z Z') k none e))) ?_ (fun e _ _ => hcs0 e)) ?_
                      · intro e he
                        rw [Finset.mem_filter] at he ⊢
                        obtain ⟨heA, hek, hw, ht⟩ := he
                        refine ⟨heA, hw, ?_⟩
                        rw [Function.update_of_ne hek]; exact ht
                      · exact sum_winners_le' (H := H) _ A cs hcs0 cm hcm0 hcsm t
                  _ ≤ 2 * cm := by
                      rw [Finset.sum_const, nsmul_eq_mul]
                      have : ((psl H y).card : ℝ) ≤ 2 := by exact_mod_cast card_psl_le hsl y
                      nlinarith
              have e1 : 2 * κ / (1 - 2 * θ) + κ / (1 - 2 * θ) + 2 * cm = 5 * κ / (1 - 2 * θ) := by
                simp only [cm]; ring
              linarith)
        refine le_trans hB ?_
        simp only [DA]
        by_cases hy : y = none
        · simp [hy]
        · simp [hy, hk]
      · have : wE (condp (pp H θ x) A (Function.update Z k y)) (Yw H θ x s) =
            wE (condp (pp H θ x) A (Function.update Z k none)) (Yw H θ x s) := by
          refine cond_congr _ A _ _ (fun f hf => ?_) _
          have : f ≠ k := fun h => hk (h ▸ hf)
          simp [Function.update_of_ne this]
        rw [this, sub_self, abs_zero]
        simp only [DA]; split_ifs
        · positivity
        · exact le_rfl
    · intro k y; simp only [DA]; split_ifs
      · have e1 : 2 * (5 * κ / (1 - 2 * θ)) = 10 * κ / (1 - 2 * θ) := by ring
        linarith
      · rw [mul_zero]; positivity

end Nib

end SecLoad

section SecRound1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset TwoStage

namespace Nib

variable {J Sl O : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
  [Fintype O] [DecidableEq O] {H : HG J Sl O}

/-- jobs interacting with job `e` (including `e`) -/
noncomputable def Nb (H : HG J Sl O) (e : J) : Finset J :=
  insert e (@Finset.filter _ (fun f => ∃ o o', H.job o = e ∧ H.job o' = f ∧ ¬Disjoint (H.sl o) (H.sl o'))
    (fun _ => Classical.propDecidable _) univ)

theorem mem_Nb (e f : J) : f ∈ Nb H e ↔ f = e ∨ ∃ o o', H.job o = e ∧ H.job o' = f ∧ ¬Disjoint (H.sl o) (H.sl o') := by
  unfold Nb
  rw [Finset.mem_insert, @Finset.mem_filter _ _ (fun _ => Classical.propDecidable _)]
  simp

theorem Nb_symm (e f : J) : f ∈ Nb H e ↔ e ∈ Nb H f := by
  rw [mem_Nb, mem_Nb]
  constructor
  · rintro (h | ⟨o, o', h1, h2, h3⟩)
    · left; exact h.symm
    · right; exact ⟨o', o, h2, h1, fun hd => h3 hd.symm⟩
  · rintro (h | ⟨o, o', h1, h2, h3⟩)
    · left; exact h.symm
    · right; exact ⟨o', o, h2, h1, fun hd => h3 hd.symm⟩

theorem self_mem_Nb (e : J) : e ∈ Nb H e := (mem_Nb e e).2 (Or.inl rfl)

/-- `av` is trivially one outside the neighbourhood -/
theorem av_one_of_not_Nb (e f : J) (hf : f ∉ Nb H e) (o : O) (ho : H.job o = e) (T : Finset Sl)
    (hT : T ⊆ H.sl o) (y : Option O) : av H f T y = 1 := by
  cases y with
  | none => rfl
  | some o' =>
    simp only [av]
    rw [if_neg]
    rintro ⟨hj, hd⟩
    apply hf
    rw [mem_Nb]
    right
    refine ⟨o, o', ho, hj, fun hd' => hd ?_⟩
    exact Finset.disjoint_of_subset_right hT hd'.symm

theorem av_congr_Nb (e : J) (o : O) (ho : H.job o = e) (T : Finset Sl) (hT : T ⊆ H.sl o)
    (Z Z' : J → Option O) (hZ : ∀ f ∈ Nb H e, Z f = Z' f) (f : J) :
    av H f T (Z f) = av H f T (Z' f) := by
  by_cases hf : f ∈ Nb H e
  · rw [hZ f hf]
  · rw [av_one_of_not_Nb e f hf o ho T hT, av_one_of_not_Nb e f hf o ho T hT]

theorem win_congr (e : J) (Z Z' : J → Option O) (hZ : ∀ f ∈ Nb H e, Z f = Z' f) :
    win H Z e = win H Z' e := by
  rw [win_eq, win_eq, hZ e (self_mem_Nb e)]
  cases hZe : Z' e with
  | none => rfl
  | some o =>
    simp only
    split_ifs with hj
    · refine Finset.prod_congr rfl (fun f _ => av_congr_Nb e o hj _ (subset_refl _) Z Z' hZ f)
    · rfl

theorem Mf_congr (θ : ℝ) (x : O → ℝ) (e : J) (Z Z' : J → Option O) (hZ : ∀ f ∈ Nb H e, Z f = Z' f) :
    Mf H θ x e Z = Mf H θ x e Z' := by
  unfold Mf
  refine Finset.sum_congr rfl (fun o ho => ?_)
  have hj := (Finset.mem_filter.mp ho).2
  congr 1
  exact Finset.prod_congr rfl (fun f _ => av_congr_Nb e o hj _ (subset_refl _) Z Z' hZ f)

theorem Ya_congr (θ : ℝ) (x : O → ℝ) (s : Sl) (Z Z' : J → Option O)
    (hZ : ∀ f ∈ (As H s).biUnion (Nb H), Z f = Z' f) :
    Ya H θ x s Z = Ya H θ x s Z' := by
  unfold Ya PT
  refine Finset.sum_congr rfl (fun o ho => ?_)
  have hs := (Finset.mem_filter.mp ho).2
  have hA : H.job o ∈ As H s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, o, rfl, hs⟩
  have hZ' : ∀ f ∈ Nb H (H.job o), Z f = Z' f := fun f hf => hZ f (Finset.mem_biUnion.mpr ⟨_, hA, hf⟩)
  congr 1
  exact Finset.prod_congr rfl (fun f _ =>
    av_congr_Nb (H.job o) o rfl _ (Finset.erase_subset s _) Z Z' hZ' f)

theorem Yw_congr (θ : ℝ) (x : O → ℝ) (s : Sl) (Z Z' : J → Option O)
    (hZ : ∀ f ∈ (As H s).biUnion (Nb H), Z f = Z' f) :
    Yw H θ x s Z = Yw H θ x s Z' := by
  unfold Yw PT
  refine Finset.sum_congr rfl (fun o ho => ?_)
  have hs := (Finset.mem_filter.mp ho).2
  have hA : H.job o ∈ As H s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, o, rfl, hs⟩
  have hZ' : ∀ f ∈ Nb H (H.job o), Z f = Z' f := fun f hf => hZ f (Finset.mem_biUnion.mpr ⟨_, hA, hf⟩)
  rw [win_congr (H.job o) Z Z' hZ']
  congr 2
  exact Finset.prod_congr rfl (fun f _ =>
    av_congr_Nb (H.job o) o rfl _ (Finset.erase_subset s _) Z Z' hZ' f)

theorem Qw_congr (S : Finset J) (c : J → ℝ) (Z Z' : J → Option O)
    (hZ : ∀ f ∈ S.biUnion (Nb H), Z f = Z' f) : Qw H S c Z = Qw H S c Z' := by
  unfold Qw
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [win_congr e Z Z' (fun f hf => hZ f (Finset.mem_biUnion.mpr ⟨e, he, hf⟩))]

theorem Dq_congr (dum : O → Prop) [DecidablePred dum] (S : Finset J) (c : J → ℝ) (Z Z' : J → Option O)
    (hZ : ∀ f ∈ S.biUnion (Nb H), Z f = Z' f) : Dq H dum S c Z = Dq H dum S c Z' := by
  unfold Dq
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [hZ e (Finset.mem_biUnion.mpr ⟨e, he, self_mem_Nb e⟩)]

/-- dependency sets of the round's bad events -/
noncomputable def evS {G : Type} (H : HG J Sl O) (memb : G → Finset J) : J ⊕ (Sl ⊕ G) → Finset J
  | Sum.inl e => Nb H e
  | Sum.inr (Sum.inl s) => (As H s).biUnion (Nb H)
  | Sum.inr (Sum.inr g) => (memb g).biUnion (Nb H)

theorem card_biUnion_le_mul {α β : Type} [DecidableEq β] (s : Finset α) (t : α → Finset β) (a b : ℕ)
    (hs : s.card ≤ a) (ht : ∀ x ∈ s, (t x).card ≤ b) : (s.biUnion t).card ≤ a * b := by
  refine le_trans Finset.card_biUnion_le ?_
  calc ∑ x ∈ s, (t x).card ≤ ∑ _x ∈ s, b := Finset.sum_le_sum ht
    _ = s.card * b := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ a * b := Nat.mul_le_mul_right b hs

theorem dep_count {G : Type} [Fintype G] [DecidableEq G] (memb : G → Finset J) (D : ℕ) (hD1 : 1 ≤ D)
    (hNb : ∀ e, (Nb H e).card ≤ D) (hAs : ∀ s, (As H s).card ≤ D)
    (hse : ∀ e, (univ.filter (fun s => e ∈ As H s)).card ≤ D)
    (hmemb : ∀ g, (memb g).card ≤ D) (hge : ∀ e, (univ.filter (fun g => e ∈ memb g)).card ≤ D)
    (t : J ⊕ (Sl ⊕ G)) :
    (univ.filter (fun t' => t' = t ∨ ¬Disjoint (evS H memb t) (evS H memb t'))).card ≤ 3 * D ^ 4 + 1 := by
  classical
  -- events containing a given job
  have hcnt : ∀ f, (univ.filter (fun t' : J ⊕ (Sl ⊕ G) => f ∈ evS H memb t')).card ≤ D + D * D + D * D := by
    intro f
    let A1 : Finset J := Nb H f
    let A2 : Finset Sl := (Nb H f).biUnion (fun e => univ.filter (fun s => e ∈ As H s))
    let A3 : Finset G := (Nb H f).biUnion (fun e => univ.filter (fun g => e ∈ memb g))
    have hsub : univ.filter (fun t' : J ⊕ (Sl ⊕ G) => f ∈ evS H memb t') ⊆
        A1.map Function.Embedding.inl ∪ ((A2.map Function.Embedding.inl).map Function.Embedding.inr ∪
          (A3.map Function.Embedding.inr).map Function.Embedding.inr) := by
      intro t' ht'
      rw [Finset.mem_filter] at ht'
      rcases t' with e | (s | g)
      · simp only [evS] at ht'
        apply Finset.mem_union_left
        simp only [Finset.mem_map, Function.Embedding.inl_apply]
        exact ⟨e, (Nb_symm e f).1 ht'.2, rfl⟩
      · simp only [evS, Finset.mem_biUnion] at ht'
        obtain ⟨e, heA, hfe⟩ := ht'.2
        apply Finset.mem_union_right; apply Finset.mem_union_left
        simp only [Finset.mem_map, Function.Embedding.inl_apply, Function.Embedding.inr_apply]
        refine ⟨Sum.inl s, ⟨s, ?_, rfl⟩, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨e, (Nb_symm e f).1 hfe, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heA⟩⟩
      · simp only [evS, Finset.mem_biUnion] at ht'
        obtain ⟨e, heg, hfe⟩ := ht'.2
        apply Finset.mem_union_right; apply Finset.mem_union_right
        simp only [Finset.mem_map, Function.Embedding.inr_apply]
        refine ⟨Sum.inr g, ⟨g, ?_, rfl⟩, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨e, (Nb_symm e f).1 hfe, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heg⟩⟩
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    rw [Finset.card_map, add_assoc]
    refine add_le_add (hNb f) (le_trans (Finset.card_union_le _ _) ?_)
    rw [Finset.card_map, Finset.card_map, Finset.card_map, Finset.card_map]
    exact add_le_add (card_biUnion_le_mul _ _ D D (hNb f) (fun e _ => hse e))
      (card_biUnion_le_mul _ _ D D (hNb f) (fun e _ => hge e))
  have hS : (evS H memb t).card ≤ D * D := by
    rcases t with e | (s | g)
    · simp only [evS]; exact le_trans (hNb e) (Nat.le_mul_of_pos_left D (by omega))
    · simp only [evS]; exact card_biUnion_le_mul _ _ D D (hAs s) (fun e _ => hNb e)
    · simp only [evS]; exact card_biUnion_le_mul _ _ D D (hmemb g) (fun e _ => hNb e)
  have hsub2 : univ.filter (fun t' => t' = t ∨ ¬Disjoint (evS H memb t) (evS H memb t')) ⊆
      insert t ((evS H memb t).biUnion (fun f => univ.filter (fun t' : J ⊕ (Sl ⊕ G) => f ∈ evS H memb t'))) := by
    intro t' ht'
    rw [Finset.mem_filter] at ht'
    rcases ht'.2 with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      obtain ⟨f, hf1, hf2⟩ := Finset.not_disjoint_iff.mp h
      exact Finset.mem_biUnion.mpr ⟨f, hf1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf2⟩⟩
  refine le_trans (Finset.card_le_card hsub2) (le_trans (Finset.card_insert_le _ _) ?_)
  have h3 := card_biUnion_le_mul (evS H memb t) (fun f => univ.filter (fun t' : J ⊕ (Sl ⊕ G) => f ∈ evS H memb t'))
    (D * D) (D + D * D + D * D) hS (fun f _ => hcnt f)
  have h4 : D * D * (D + D * D + D * D) ≤ 3 * D ^ 4 := by
    have : D ≤ D * D := Nat.le_mul_of_pos_left D (by omega)
    nlinarith
  omega

end Nib

end SecRound1

section SecLLL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset

namespace LLLv

variable {I : Type} [Fintype I] [DecidableEq I] {Ω : I → Type} [∀ i, Fintype (Ω i)]
  [∀ i, DecidableEq (Ω i)]

/-- restriction of a configuration to a set of variables, as an atomic set -/
def restr (S : Finset I) (z : ∀ i, Ω i) : ∀ i, Option (Ω i) :=
  fun i => if i ∈ S then some (z i) else none

theorem sum_restr_eq (p : ∀ i, Ω i → ℝ) (hp1 : ∀ i, ∑ ω, p i ω = 1) (S : Finset I)
    (Y : ∀ i, Option (Ω i)) :
    ∑ z : (∀ i, Ω i), (∏ i, p i (z i)) * (if restr S z = Y then 1 else 0) =
      if (∀ i, ((Y i).isSome ↔ i ∈ S)) then ∏ i, (Y i).elim 1 (p i) else 0 := by
  have hind : ∀ z : (∀ i, Ω i), (if restr S z = Y then (1 : ℝ) else 0) =
      ∏ i, (if (if i ∈ S then some (z i) else none) = Y i then 1 else 0) := by
    intro z
    by_cases h : restr S z = Y
    · rw [if_pos h]
      refine (Finset.prod_eq_one (fun i _ => ?_)).symm
      have := congrFun h i
      simp only [restr] at this
      rw [if_pos this]
    · rw [if_neg h]
      have : ∃ i, ¬ (if i ∈ S then some (z i) else none) = Y i := by
        by_contra hc; push_neg at hc; exact h (funext hc)
      obtain ⟨i, hi⟩ := this
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm
  simp_rw [hind, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i ω => p i ω * (if (if i ∈ S then some ω else none) = Y i then 1 else 0))]
  by_cases hY : ∀ i, ((Y i).isSome ↔ i ∈ S)
  · rw [if_pos hY]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hi : i ∈ S
    · have hs := (hY i).2 hi
      obtain ⟨ω, hω⟩ := Option.isSome_iff_exists.mp hs
      rw [hω]
      simp only [hi, if_true, Option.some.injEq, Option.elim]
      rw [Finset.sum_eq_single ω]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · have hn : Y i = none := by
        cases h : Y i
        · rfl
        · exfalso; exact hi ((hY i).1 (by simp [h]))
      rw [hn]; simp [hi, hp1 i]
  · rw [if_neg hY]
    push_neg at hY
    obtain ⟨i, hi⟩ := hY
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    refine Finset.sum_eq_zero (fun ω _ => ?_)
    rw [if_neg, mul_zero]
    intro h
    by_cases hS : i ∈ S
    · rw [if_pos hS] at h
      rcases hi with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2 hS
      · apply h1; rw [← h]; simp
    · rw [if_neg hS] at h
      rcases hi with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [← h] at h1; simp at h1
      · exact hS h2

end LLLv

open LLLv in
/-- **Symmetric variable Lovász Local Lemma** (from the partial-resampling criterion). -/
theorem lll_symm {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
    (Ω : I → Type) [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (p : ∀ i, Ω i → ℝ) (hp : ∀ i ω, 0 < p i ω) (hp1 : ∀ i, ∑ ω, p i ω = 1)
    (bad : T → (∀ i, Ω i) → Prop) (S : T → Finset I)
    (hloc : ∀ t z z', (∀ i ∈ S t, z i = z' i) → bad t z → bad t z')
    (P : ℝ) (d : ℕ)
    (hP : ∀ t, ∑ z : (∀ i, Ω i), (∏ i, p i (z i)) *
      (@ite ℝ (bad t z) (Classical.propDecidable _) 1 0) ≤ P)
    (hd : ∀ t, (Finset.univ.filter (fun t' => t' = t ∨ ¬ Disjoint (S t) (S t'))).card ≤ d + 1)
    (hepd : Real.exp 1 * P * (d + 1) ≤ 1) :
    ∃ z : ∀ i, Ω i, ∀ t, ¬ bad t z := by
  classical
  have hne : ∀ i, Nonempty (Ω i) := fun i => by
    by_contra h; rw [not_nonempty_iff] at h; have := hp1 i; simp at this
  let ext : (∀ i, Option (Ω i)) → (∀ i, Ω i) := fun Y i => (Y i).getD (Classical.arbitrary _)
  let good : T → (∀ i, Option (Ω i)) → Prop := fun t Y =>
    (∀ i, ((Y i).isSome ↔ i ∈ S t)) ∧ bad t (ext Y)
  let q : T → (∀ i, Option (Ω i)) → ℝ := fun t Y => if good t Y then 1 else 0
  let pA : (∀ i, Option (Ω i)) → ℝ := fun Y => ∏ i, (Y i).elim 1 (p i)
  let μ : T → (∀ i, Option (Ω i)) → ℝ := fun t Y => Real.exp 1 * q t Y * pA Y
  have hpA : ∀ Y, 0 ≤ pA Y := fun Y => Finset.prod_nonneg (fun i _ => by
    cases Y i <;> simp [(hp i _).le])
  have hq : ∀ t Y, 0 ≤ q t Y := fun t Y => by simp only [q]; split_ifs <;> norm_num
  have hμ : ∀ t Y, 0 ≤ μ t Y := fun t Y => mul_nonneg (mul_nonneg (Real.exp_pos 1).le (hq t Y)) (hpA Y)
  -- total μ-mass of an event
  have hmass : ∀ t, ∑ Y, μ t Y ≤ Real.exp 1 * P := by
    intro t
    have : ∑ Y, q t Y * pA Y = ∑ z : (∀ i, Ω i), (∏ i, p i (z i)) *
        (@ite ℝ (bad t z) (Classical.propDecidable _) 1 0) := by
      -- group configurations by their restriction
      have h1 : ∀ z : (∀ i, Ω i), (@ite ℝ (bad t z) (Classical.propDecidable _) 1 0) =
          ∑ Y, (if restr (S t) z = Y then 1 else 0) * q t Y := by
        intro z
        rw [Finset.sum_eq_single (restr (S t) z)]
        · rw [if_pos rfl, one_mul]
          simp only [q, good]
          have hsupp : ∀ i, ((restr (S t) z i).isSome ↔ i ∈ S t) := by
            intro i; simp only [restr]; split_ifs with h <;> simp [h]
          have hext : ∀ i ∈ S t, ext (restr (S t) z) i = z i := by
            intro i hi; simp [ext, restr, hi]
          by_cases hb : bad t z
          · rw [if_pos hb, if_pos ⟨hsupp, hloc t z _ (fun i hi => (hext i hi).symm) hb⟩]
          · rw [if_neg hb, if_neg]
            rintro ⟨_, hb'⟩
            exact hb (hloc t _ z (fun i hi => hext i hi) hb')
        · intro Y _ hY; rw [if_neg (Ne.symm hY), zero_mul]
        · simp
      simp_rw [h1, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun Y _ => ?_)
      have h2 := sum_restr_eq p hp1 (S t) Y
      have e : ∀ z : (∀ i, Ω i), (∏ i, p i (z i)) * ((if restr (S t) z = Y then 1 else 0) * q t Y) =
          ((∏ i, p i (z i)) * (if restr (S t) z = Y then 1 else 0)) * q t Y := fun z => by ring
      simp_rw [e]
      rw [← Finset.sum_mul, h2]
      simp only [q, good]
      by_cases hs : ∀ i, ((Y i).isSome ↔ i ∈ S t)
      · rw [if_pos hs]; split_ifs <;> simp [pA]
      · rw [if_neg hs]; simp [hs]
    calc ∑ Y, μ t Y = Real.exp 1 * ∑ Y, q t Y * pA Y := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun Y _ => by simp only [μ]; ring)
      _ ≤ Real.exp 1 * P := by rw [this]; exact mul_le_mul_of_nonneg_left (hP t) (Real.exp_pos 1).le
  suffices H : (∀ t z, bad t z →
      1 ≤ ∑ Y, q t Y * ∏ i, (Y i).elim 1 (fun ω => if z i = ω then 1 else 0)) ∧
      (∀ k Y, (∏ i, (Y i).elim 1 (p i)) * q k Y *
        ∏ ℓ ∈ Finset.univ.filter (fun ℓ : (∀ i, Option (Ω i)) × T =>
          ℓ.2 = k ∨ ∃ i, (Y i).isSome ∧ (ℓ.1 i).isSome), (1 + μ ℓ.2 ℓ.1) ≤ μ k Y) by
    exact PartialResampling.pra_exists Ω p hp hp1 bad q hq H.1 μ hμ H.2
  refine ⟨?_, ?_⟩
  · -- hitting
    intro t z hb
    have hY : good t (restr (S t) z) := by
      refine ⟨fun i => by simp only [restr]; split_ifs with h <;> simp [h], ?_⟩
      exact hloc t z _ (fun i hi => by simp [ext, restr, hi]) hb
    have hhold : ∏ i, ((restr (S t) z) i).elim 1 (fun ω => if z i = ω then (1 : ℝ) else 0) = 1 := by
      refine Finset.prod_eq_one (fun i _ => ?_)
      simp only [restr]; split_ifs <;> simp
    calc (1 : ℝ) = q t (restr (S t) z) * ∏ i, ((restr (S t) z) i).elim 1
          (fun ω => if z i = ω then 1 else 0) := by rw [hhold, mul_one]; simp only [q]; rw [if_pos hY]
      _ ≤ _ := by
        refine Finset.single_le_sum (f := fun Y => q t Y * ∏ i, (Y i).elim 1
          (fun ω => if z i = ω then (1 : ℝ) else 0)) (fun Y _ => mul_nonneg (hq t Y)
            (Finset.prod_nonneg (fun i _ => by cases Y i <;> simp; split_ifs <;> norm_num)))
          (Finset.mem_univ _)
  · -- criterion
    intro k Y
    by_cases hg : good k Y
    · have hqk : q k Y = 1 := if_pos hg
      set N := Finset.univ.filter (fun ℓ : (∀ i, Option (Ω i)) × T =>
        ℓ.2 = k ∨ ∃ i, (Y i).isSome ∧ (ℓ.1 i).isSome) with hN
      have hsum : ∑ ℓ ∈ N, μ ℓ.2 ℓ.1 ≤ 1 := by
        -- only labels supported on S of their event contribute
        set D := Finset.univ.filter (fun t' => t' = k ∨ ¬ Disjoint (S k) (S t')) with hD
        have h1 : ∑ ℓ ∈ N, μ ℓ.2 ℓ.1 ≤ ∑ t' ∈ D, ∑ Y', μ t' Y' := by
          rw [← Finset.sum_filter_add_sum_filter_not N (fun ℓ => ℓ.2 ∈ D)]
          have h0 : ∑ ℓ ∈ N.filter (fun ℓ => ¬ ℓ.2 ∈ D), μ ℓ.2 ℓ.1 = 0 := by
            refine Finset.sum_eq_zero (fun ℓ hℓ => ?_)
            rw [Finset.mem_filter, hN, Finset.mem_filter] at hℓ
            obtain ⟨⟨_, hrel⟩, hnD⟩ := hℓ
            simp only [μ, q]
            rw [if_neg, mul_zero, zero_mul]
            rintro ⟨hs, _⟩
            apply hnD
            rw [hD, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            rcases hrel with h | ⟨i, hi, hi'⟩
            · exact Or.inl h
            · right
              rw [Finset.not_disjoint_iff]
              exact ⟨i, (hg.1 i).1 hi, (hs i).1 hi'⟩
          rw [h0, add_zero]
          calc ∑ ℓ ∈ N.filter (fun ℓ => ℓ.2 ∈ D), μ ℓ.2 ℓ.1
              ≤ ∑ ℓ ∈ (Finset.univ : Finset ((∀ i, Option (Ω i)) × T)).filter (fun ℓ => ℓ.2 ∈ D),
                  μ ℓ.2 ℓ.1 := Finset.sum_le_sum_of_subset_of_nonneg
                    (Finset.filter_subset_filter _ (Finset.subset_univ _)) (fun ℓ _ _ => hμ _ _)
            _ = ∑ t' ∈ D, ∑ Y', μ t' Y' := by
                rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_filter]
                refine Finset.sum_congr rfl (fun t' _ => ?_)
                have hDm : t' ∈ D ↔ (t' = k ∨ ¬Disjoint (S k) (S t')) := by rw [hD]; simp
                by_cases ht : t' ∈ D
                · rw [if_pos (hDm.1 ht)]; refine Finset.sum_congr rfl (fun Y' _ => ?_); simp [ht]
                · rw [if_neg (fun h => ht (hDm.2 h))]; refine Finset.sum_eq_zero (fun Y' _ => ?_); simp [ht]
        have h2 : ∑ t' ∈ D, ∑ Y', μ t' Y' ≤ ∑ t' ∈ D, Real.exp 1 * P :=
          Finset.sum_le_sum (fun t' _ => hmass t')
        rw [Finset.sum_const, nsmul_eq_mul] at h2
        have h3 : (D.card : ℝ) ≤ d + 1 := by exact_mod_cast hd k
        have hP0 : 0 ≤ P := le_trans (Finset.sum_nonneg (fun z _ => mul_nonneg
          (Finset.prod_nonneg (fun i _ => (hp i _).le)) (by split_ifs <;> norm_num))) (hP k)
        nlinarith [Real.exp_pos 1]
      have hprod : ∏ ℓ ∈ N, (1 + μ ℓ.2 ℓ.1) ≤ Real.exp 1 := by
        calc ∏ ℓ ∈ N, (1 + μ ℓ.2 ℓ.1) ≤ ∏ ℓ ∈ N, Real.exp (μ ℓ.2 ℓ.1) :=
              Finset.prod_le_prod (fun ℓ _ => by linarith [hμ ℓ.2 ℓ.1])
                (fun ℓ _ => by linarith [Real.add_one_le_exp (μ ℓ.2 ℓ.1)])
          _ = Real.exp (∑ ℓ ∈ N, μ ℓ.2 ℓ.1) := (Real.exp_sum _ _).symm
          _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsum
      calc (∏ i, (Y i).elim 1 (p i)) * q k Y * ∏ ℓ ∈ N, (1 + μ ℓ.2 ℓ.1)
          ≤ (∏ i, (Y i).elim 1 (p i)) * q k Y * Real.exp 1 :=
            mul_le_mul_of_nonneg_left hprod (mul_nonneg (hpA Y) (hq k Y))
        _ = μ k Y := by simp only [μ, pA]; ring
    · have hqk : q k Y = 0 := if_neg hg
      have : μ k Y = 0 := by simp only [μ]; rw [hqk]; ring
      rw [hqk, this]; simp

/-- sums over configurations only see positive-probability values -/
theorem sum_support_eq {I X : Type} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    (p : I → X → ℝ) (hp0 : ∀ i y, 0 ≤ p i y) (F : (I → X) → ℝ) :
    ∑ z : I → X, (∏ i, p i (z i)) * F z =
      ∑ z' : (∀ i, {y : X // 0 < p i y}), (∏ i, p i (z' i).1) * F (fun i => (z' i).1) := by
  classical
  symm
  refine Finset.sum_bij_ne_zero (fun z' _ _ => fun i => (z' i).1) ?_ ?_ ?_ ?_
  · intro z' _ _; exact Finset.mem_univ _
  · intro z1 _ _ z2 _ _ h
    funext i; exact Subtype.ext (congrFun h i)
  · intro z _ hz
    have hpos : ∀ i, 0 < p i (z i) := by
      intro i
      by_contra hneg
      apply hz
      have h0 : p i (z i) = 0 := le_antisymm (not_lt.mp hneg) (hp0 i (z i))
      rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul]
    exact ⟨fun i => ⟨z i, hpos i⟩, Finset.mem_univ _, by simpa using hz, rfl⟩
  · intro z' _ _; rfl

/-- **Symmetric variable LLL**, non-dependent values, nonnegative probabilities. -/
theorem lll_symm' {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
    [Fintype X] [DecidableEq X]
    (p : I → X → ℝ) (hp0 : ∀ i y, 0 ≤ p i y) (hp1 : ∀ i, ∑ y, p i y = 1)
    (bad : T → (I → X) → Prop) (S : T → Finset I)
    (hloc : ∀ t z z', (∀ i ∈ S t, z i = z' i) → bad t z → bad t z')
    (P : ℝ) (d : ℕ)
    (hP : ∀ t, ∑ z : I → X, (∏ i, p i (z i)) *
      (@ite ℝ (bad t z) (Classical.propDecidable _) 1 0) ≤ P)
    (hd : ∀ t, (Finset.univ.filter (fun t' => t' = t ∨ ¬ Disjoint (S t) (S t'))).card ≤ d + 1)
    (hepd : Real.exp 1 * P * (d + 1) ≤ 1) :
    ∃ z : I → X, (∀ i, 0 < p i (z i)) ∧ ∀ t, ¬ bad t z := by
  classical
  let Ω : I → Type := fun i => {y : X // 0 < p i y}
  have hp1' : ∀ i, ∑ y : Ω i, p i y.1 = 1 := by
    intro i
    rw [← hp1 i]
    have h2 : ∑ y ∈ Finset.univ.filter (fun y => 0 < p i y), p i y = ∑ y : Ω i, p i y.1 :=
      Finset.sum_subtype _ (fun y => by simp) (p i)
    rw [← h2, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    split_ifs with h
    · rfl
    · exact (le_antisymm (not_lt.mp h) (hp0 i y)).symm
  obtain ⟨z', hz'⟩ := lll_symm Ω (fun i y => p i y.1) (fun i y => y.2) hp1'
    (fun t z => bad t (fun i => (z i).1)) S
    (fun t z1 z2 h hb => hloc t _ _ (fun i hi => congrArg Subtype.val (h i hi)) hb) P d
    (fun t => by
      have := sum_support_eq p hp0 (fun z => @ite ℝ (bad t z) (Classical.propDecidable _) 1 0)
      have h := hP t
      rw [this] at h
      exact h) hd hepd
  exact ⟨fun i => (z' i).1, fun i => (z' i).2, hz'⟩

end SecLLL

section SecRound2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset TwoStage

namespace Nib

variable {J Sl O : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
  [Fintype O] [DecidableEq O] {H : HG J Sl O}

/-- the mass event has small probability (both tails) -/
theorem mass_event (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (hδ : δ ≤ 1)
    (e : J) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    EE H θ x (fun Z => @ite ℝ (2 * Real.sqrt (8 * θ * κ / (1 - 2 * θ) ^ 2 * Λ) + 2 * (4 * κ / (1 - 2 * θ)) * Λ ≤
      |Mf H θ x e Z - mass H x e|) (Classical.propDecidable _) 1 0) ≤ 2 * Real.exp (-Λ) := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  have hp0 := pp_nonneg' θ σ δ κ x hI hθ0 hθ hδ
  have hp1 : ∀ k, ∑ y, pp H θ x k y = 1 := fun k => sum_pp θ x k
  have hpi : ∀ o, 0 < piF H θ x o := fun o => by
    have := (piF_bounds θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ o).1; linarith
  have hEM : EE H θ x (Mf H θ x e) = mass H x e := EE_Mf θ x e hpi
  have key := OneStage.dev_of_infl (pp H θ x) hp0 hp1 (Mf H θ x e) none (DM H θ x e) (4 * κ / (1 - 2 * θ))
    (by positivity) (fun Z k y => Mf_infl θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ e Z k y)
    (fun k y => DM_le θ σ δ κ x hI hsl hθ0 hθ hκ0.le e k y) Λ hΛ
  have hV := V_Mf θ σ δ κ x hI hsl hθ0 hθ hσ hκ0.le e
  have hm2 : mass H x e ≤ 2 := by
    rcases hI.mass e with h | h
    · rw [h]; norm_num
    · linarith [h.2]
  have hV' : ∑ k, ∑ y, pp H θ x k y * DM H θ x e k y ^ 2 ≤ 8 * θ * κ / (1 - 2 * θ) ^ 2 := by
    refine le_trans hV ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg hθ0 hκ0.le]
  have hs : Real.sqrt ((∑ k, ∑ y, pp H θ x k y * DM H θ x e k y ^ 2) * Λ) ≤
      Real.sqrt (8 * θ * κ / (1 - 2 * θ) ^ 2 * Λ) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hV' hΛ)
  set lam := 2 * Real.sqrt (8 * θ * κ / (1 - 2 * θ) ^ 2 * Λ) + 2 * (4 * κ / (1 - 2 * θ)) * Λ
  set lam0 := 2 * Real.sqrt ((∑ k, ∑ y, pp H θ x k y * DM H θ x e k y ^ 2) * Λ) + 2 * (4 * κ / (1 - 2 * θ)) * Λ
  have hle : lam0 ≤ lam := by
    show 2 * Real.sqrt ((∑ k, ∑ y, pp H θ x k y * DM H θ x e k y ^ 2) * Λ) + 2 * (4 * κ / (1 - 2 * θ)) * Λ ≤
      2 * Real.sqrt (8 * θ * κ / (1 - 2 * θ) ^ 2 * Λ) + 2 * (4 * κ / (1 - 2 * θ)) * Λ
    linarith [hs]
  have hE : EE H θ x (Mf H θ x e) = ∑ Z' : J → Option O, (∏ k, pp H θ x k (Z' k)) * Mf H θ x e Z' := rfl
  have hlam0 : 0 ≤ lam0 := by
    show 0 ≤ 2 * Real.sqrt ((∑ k, ∑ y, pp H θ x k y * DM H θ x e k y ^ 2) * Λ) + 2 * (4 * κ / (1 - 2 * θ)) * Λ
    have := Real.sqrt_nonneg ((∑ k, ∑ y, pp H θ x k y * DM H θ x e k y ^ 2) * Λ)
    have : 0 ≤ 4 * κ / (1 - 2 * θ) := by positivity
    nlinarith
  calc EE H θ x (fun Z => @ite ℝ (lam ≤ |Mf H θ x e Z - mass H x e|) (Classical.propDecidable _) 1 0)
      ≤ EE H θ x (fun Z => (if lam0 ≤ Mf H θ x e Z - ∑ Z' : J → Option O, (∏ k, pp H θ x k (Z' k)) * Mf H θ x e Z'
          then 1 else 0) + (if Mf H θ x e Z ≤ (∑ Z' : J → Option O, (∏ k, pp H θ x k (Z' k)) * Mf H θ x e Z') - lam0
          then 1 else 0)) := by
        refine wE_mono _ hp0 _ _ (fun Z => ?_)
        rw [← hE, hEM]
        by_cases h : lam ≤ |Mf H θ x e Z - mass H x e|
        · rw [@if_pos _ (Classical.propDecidable _) h]
          rcases le_abs'.mp h with h1 | h1
          · have h2 : Mf H θ x e Z ≤ mass H x e - lam0 := by linarith
            rw [if_pos h2]; split_ifs <;> norm_num
          · rw [if_pos (by linarith)]; split_ifs <;> norm_num
        · rw [@if_neg _ (Classical.propDecidable _) h]; split_ifs <;> norm_num
    _ = EE H θ x (fun Z => if lam0 ≤ Mf H θ x e Z - ∑ Z' : J → Option O, (∏ k, pp H θ x k (Z' k)) * Mf H θ x e Z'
          then 1 else 0) + EE H θ x (fun Z => if Mf H θ x e Z ≤
          (∑ Z' : J → Option O, (∏ k, pp H θ x k (Z' k)) * Mf H θ x e Z') - lam0 then 1 else 0) := EE_add _ _ _ _
    _ ≤ Real.exp (-Λ) + Real.exp (-Λ) := add_le_add key.1 key.2
    _ = 2 * Real.exp (-Λ) := by ring

theorem ind_or_le (A B : Prop) :
    @ite ℝ (A ∨ B) (Classical.propDecidable _) 1 0 ≤
      @ite ℝ A (Classical.propDecidable _) 1 0 + @ite ℝ B (Classical.propDecidable _) 1 0 := by
  by_cases hA : A
  · rw [@if_pos _ (Classical.propDecidable _) (Or.inl hA), @if_pos _ (Classical.propDecidable _) hA]
    split_ifs <;> norm_num
  · rw [@if_neg _ (Classical.propDecidable _) hA]
    by_cases hB : B
    · rw [@if_pos _ (Classical.propDecidable _) (Or.inr hB), @if_pos _ (Classical.propDecidable _) hB]; norm_num
    · rw [@if_neg _ (Classical.propDecidable _) (fun h => h.elim hA hB), @if_neg _ (Classical.propDecidable _) hB]; norm_num

theorem ind_eq_ite (A : Prop) [Decidable A] :
    @ite ℝ A (Classical.propDecidable _) 1 0 = if A then 1 else 0 := by
  by_cases h : A
  · rw [@if_pos _ (Classical.propDecidable _) h, if_pos h]
  · rw [@if_neg _ (Classical.propDecidable _) h, if_neg h]

/-- the round's deviation parameters -/
noncomputable def lam1 (θ κ Λ : ℝ) : ℝ := 2 * Real.sqrt (8 * θ * κ / (1 - 2 * θ) ^ 2 * Λ) + 2 * (4 * κ / (1 - 2 * θ)) * Λ
noncomputable def lama (θ κ Λ : ℝ) : ℝ := 2 * Real.sqrt (2 * θ * κ / (1 - 2 * θ) ^ 2 * Λ) + 2 * (4 * κ / (1 - 2 * θ)) * Λ
noncomputable def lamw (θ κ Λ : ℝ) (n : ℕ) : ℝ :=
  (2 * Real.sqrt (12 * θ * κ / (1 - 2 * θ) ^ 2 * Λ) + 2 * (8 * κ / (1 - 2 * θ)) * Λ) +
    (2 * Real.sqrt (50 * θ * κ ^ 2 * n / (1 - 2 * θ) ^ 2 * Λ) + 2 * (10 * κ / (1 - 2 * θ)) * Λ)
noncomputable def lamg (θ Λ : ℝ) (n : ℕ) : ℝ :=
  (2 * Real.sqrt (4 * θ * n * Λ) + 2 * 4 * Λ) + (2 * Real.sqrt (18 * θ * n * Λ) + 2 * 6 * Λ)
noncomputable def lamD (θ Λ : ℝ) (n : ℕ) : ℝ := 2 * Real.sqrt (2 * θ * n * Λ) + 2 * 2 * Λ

/-- second group weight -/
noncomputable def c2 (H : HG J Sl O) (dum : O → Prop) [DecidablePred dum] (w : J → ℝ) (x : O → ℝ) (e : J) : ℝ :=
  w e * dmass H dum x e / 2

/-- **one round**: a good pick configuration exists -/
theorem round_exists {G : Type} [Fintype G] [DecidableEq G] (hsl : ∀ o, (H.sl o).card ≤ 2)
    (dum : O → Prop) [DecidablePred dum] (memb : G → Finset J) (w : J → ℝ) (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1)
    (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (D : ℕ) (hD1 : 1 ≤ D)
    (hNb : ∀ e, (Nb H e).card ≤ D) (hAs : ∀ s, (As H s).card ≤ D)
    (hse : ∀ e, (univ.filter (fun s => e ∈ As H s)).card ≤ D)
    (hmemb : ∀ g, (memb g).card ≤ D) (hge : ∀ e, (univ.filter (fun g => e ∈ memb g)).card ≤ D)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (hepd : Real.exp 1 * (5 * Real.exp (-Λ)) * ((3 * D ^ 4 : ℕ) + 1) ≤ 1) :
    ∃ Z : J → Option O, (∀ e, 0 < pp H θ x e (Z e)) ∧
      (∀ e, |Mf H θ x e Z - mass H x e| < lam1 θ κ Λ) ∧
      (∀ s, Ya H θ x s Z - EE H θ x (Ya H θ x s) < lama θ κ Λ ∧
        EE H θ x (Yw H θ x s) - lamw θ κ Λ (As H s).card < Yw H θ x s Z) ∧
      (∀ g, EE H θ x (Qw H (memb g) w) - lamg θ Λ (memb g).card < Qw H (memb g) w Z ∧
        EE H θ x (Qw H (memb g) (c2 H dum w x)) - lamg θ Λ (memb g).card < Qw H (memb g) (c2 H dum w x) Z ∧
        Dq H dum (memb g) w Z - EE H θ x (Dq H dum (memb g) w) < lamD θ Λ (memb g).card) := by
  have hp0 := pp_nonneg' θ σ δ κ x hI hθ0 hθ hδ
  have hp1 : ∀ k, ∑ y, pp H θ x k y = 1 := fun k => sum_pp θ x k
  have hc2 : ∀ e, 0 ≤ c2 H dum w x e ∧ c2 H dum w x e ≤ 1 := by
    intro e
    have hd0 : 0 ≤ dmass H dum x e := Finset.sum_nonneg (fun o _ => hI.x0 o)
    have hdm : dmass H dum x e ≤ mass H x e := by
      unfold dmass mass
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun o ho => by
        simp only [Finset.mem_filter] at ho ⊢; exact ⟨ho.1, ho.2.1⟩) (fun o _ _ => hI.x0 o)
    have hm2 : mass H x e ≤ 2 := by
      rcases hI.mass e with h | h
      · rw [h]; norm_num
      · linarith [h.2]
    unfold c2
    constructor
    · exact div_nonneg (mul_nonneg (hw e).1 hd0) (by norm_num)
    · rw [div_le_one (by norm_num)]; nlinarith [(hw e).1, (hw e).2]
  let bad : J ⊕ (Sl ⊕ G) → (J → Option O) → Prop := fun t Z =>
    match t with
    | Sum.inl e => lam1 θ κ Λ ≤ |Mf H θ x e Z - mass H x e|
    | Sum.inr (Sum.inl s) => lama θ κ Λ ≤ Ya H θ x s Z - EE H θ x (Ya H θ x s) ∨
        Yw H θ x s Z ≤ EE H θ x (Yw H θ x s) - lamw θ κ Λ (As H s).card
    | Sum.inr (Sum.inr g) => Qw H (memb g) w Z ≤ EE H θ x (Qw H (memb g) w) - lamg θ Λ (memb g).card ∨
        (Qw H (memb g) (c2 H dum w x) Z ≤ EE H θ x (Qw H (memb g) (c2 H dum w x)) - lamg θ Λ (memb g).card ∨
        lamD θ Λ (memb g).card ≤ Dq H dum (memb g) w Z - EE H θ x (Dq H dum (memb g) w))
  have hloc : ∀ t Z Z', (∀ i ∈ evS H memb t, Z i = Z' i) → bad t Z → bad t Z' := by
    intro t Z Z' hZZ hb
    rcases t with e | (s | g)
    · simp only [bad] at hb ⊢
      rwa [← Mf_congr θ x e Z Z' (fun f hf => hZZ f hf)]
    · simp only [bad] at hb ⊢
      have h1 := Ya_congr θ x s Z Z' (fun f hf => hZZ f hf)
      have h2 := Yw_congr θ x s Z Z' (fun f hf => hZZ f hf)
      rwa [← h1, ← h2]
    · simp only [bad] at hb ⊢
      have h1 := Qw_congr (memb g) w Z Z' (fun f hf => hZZ f hf)
      have h2 := Qw_congr (memb g) (c2 H dum w x) Z Z' (fun f hf => hZZ f hf)
      have h3 := Dq_congr dum (memb g) w Z Z' (fun f hf => hZZ f hf)
      rwa [← h1, ← h2, ← h3]

  have hPr : ∀ t, ∑ z : J → Option O, (∏ i, pp H θ x i (z i)) * @ite ℝ (bad t z) (Classical.propDecidable _) 1 0 ≤
      5 * Real.exp (-Λ) := by
    intro t
    have hE1 : Real.exp (-Λ) ≥ 0 := (Real.exp_pos _).le
    rcases t with e | (s | g)
    · simp only [bad]
      have := mass_event θ σ δ κ x hI hsl hθ0 hθ hκ0 hκ1 hσ hδ e Λ hΛ
      unfold lam1
      exact le_trans this (by linarith)
    · simp only [bad]
      have hA := Ya_upper θ σ δ κ x hI hsl hθ0 hθ hκ0 hκ1 hσ hδ s Λ hΛ
      have hB := Yw_lower θ σ δ κ x hI hsl hθ0 hθ hκ0 hκ1 hσ hδ s Λ hΛ
      calc ∑ Z, (∏ i, pp H θ x i (Z i)) * @ite ℝ (lama θ κ Λ ≤ Ya H θ x s Z - EE H θ x (Ya H θ x s) ∨
            Yw H θ x s Z ≤ EE H θ x (Yw H θ x s) - lamw θ κ Λ (As H s).card) (Classical.propDecidable _) 1 0
          ≤ ∑ Z, (∏ i, pp H θ x i (Z i)) * ((if lama θ κ Λ ≤ Ya H θ x s Z - EE H θ x (Ya H θ x s) then 1 else 0) +
              (if Yw H θ x s Z ≤ EE H θ x (Yw H θ x s) - lamw θ κ Λ (As H s).card then 1 else 0)) := by
            refine Finset.sum_le_sum (fun Z _ => mul_le_mul_of_nonneg_left ?_
              (Finset.prod_nonneg (fun i _ => hp0 i _)))
            refine le_trans (ind_or_le _ _) ?_
            rw [ind_eq_ite, ind_eq_ite]
        _ = EE H θ x (fun Z => if lama θ κ Λ ≤ Ya H θ x s Z - EE H θ x (Ya H θ x s) then 1 else 0) +
            EE H θ x (fun Z => if Yw H θ x s Z ≤ EE H θ x (Yw H θ x s) - lamw θ κ Λ (As H s).card then 1 else 0) := by
            rw [← EE_add]; rfl
        _ ≤ Real.exp (-Λ) + (Real.exp (-Λ) + Real.exp (-Λ)) := add_le_add (by unfold lama; exact hA)
              (by unfold lamw; exact hB)
        _ ≤ 5 * Real.exp (-Λ) := by linarith
    · simp only [bad]
      have hA := group_lower θ σ δ κ x hI hsl hθ0 hθ hσ hδ (memb g) w (fun e => (hw e).1) (fun e => (hw e).2) Λ hΛ
      have hB := group_lower θ σ δ κ x hI hsl hθ0 hθ hσ hδ (memb g) (c2 H dum w x) (fun e => (hc2 e).1)
        (fun e => (hc2 e).2) Λ hΛ
      have hC := dummy_upper θ σ δ κ x hI hθ0 hθ hδ dum (memb g) w (fun e => (hw e).1) (fun e => (hw e).2) Λ hΛ
      calc ∑ Z, (∏ i, pp H θ x i (Z i)) * @ite ℝ (Qw H (memb g) w Z ≤ EE H θ x (Qw H (memb g) w) -
              lamg θ Λ (memb g).card ∨ (Qw H (memb g) (c2 H dum w x) Z ≤ EE H θ x (Qw H (memb g) (c2 H dum w x)) -
              lamg θ Λ (memb g).card ∨ lamD θ Λ (memb g).card ≤ Dq H dum (memb g) w Z - EE H θ x (Dq H dum (memb g) w)))
              (Classical.propDecidable _) 1 0
          ≤ ∑ Z, (∏ i, pp H θ x i (Z i)) * ((if Qw H (memb g) w Z ≤ EE H θ x (Qw H (memb g) w) -
              lamg θ Λ (memb g).card then 1 else 0) +
              ((if Qw H (memb g) (c2 H dum w x) Z ≤ EE H θ x (Qw H (memb g) (c2 H dum w x)) -
              lamg θ Λ (memb g).card then 1 else 0) +
              (if lamD θ Λ (memb g).card ≤ Dq H dum (memb g) w Z - EE H θ x (Dq H dum (memb g) w) then 1 else 0))) := by
            refine Finset.sum_le_sum (fun Z _ => mul_le_mul_of_nonneg_left ?_
              (Finset.prod_nonneg (fun i _ => hp0 i _)))
            refine le_trans (ind_or_le _ _) ?_
            rw [ind_eq_ite]
            apply add_le_add le_rfl
            refine le_trans (ind_or_le _ _) ?_
            rw [ind_eq_ite, ind_eq_ite]
        _ = EE H θ x (fun Z => if Qw H (memb g) w Z ≤ EE H θ x (Qw H (memb g) w) - lamg θ Λ (memb g).card then 1 else 0) +
            (EE H θ x (fun Z => if Qw H (memb g) (c2 H dum w x) Z ≤ EE H θ x (Qw H (memb g) (c2 H dum w x)) -
              lamg θ Λ (memb g).card then 1 else 0) +
            EE H θ x (fun Z => if lamD θ Λ (memb g).card ≤ Dq H dum (memb g) w Z - EE H θ x (Dq H dum (memb g) w)
              then 1 else 0)) := by
            rw [← EE_add, ← EE_add]; rfl
        _ ≤ (Real.exp (-Λ) + Real.exp (-Λ)) + ((Real.exp (-Λ) + Real.exp (-Λ)) + Real.exp (-Λ)) :=
            add_le_add (by unfold lamg; exact hA) (add_le_add (by unfold lamg; exact hB) (by unfold lamD; exact hC))
        _ = 5 * Real.exp (-Λ) := by ring


  obtain ⟨Z, hZp, hZ⟩ := lll_symm' (pp H θ x) hp0 hp1 bad (evS H memb) hloc (5 * Real.exp (-Λ)) (3 * D ^ 4) hPr
    (fun t => dep_count memb D hD1 hNb hAs hse hmemb hge t) hepd
  refine ⟨Z, hZp, fun e => ?_, fun s => ?_, fun g => ?_⟩
  · have := hZ (Sum.inl e); simp only [bad] at this; linarith
  · have := hZ (Sum.inr (Sum.inl s)); simp only [bad, not_or] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · have := hZ (Sum.inr (Sum.inr g)); simp only [bad, not_or] at this
    exact ⟨by linarith [this.1], by linarith [this.2.1], by linarith [this.2.2]⟩

end Nib

end SecRound2

section SecRound3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset TwoStage

namespace Nib

variable {J Sl O : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
  [Fintype O] [DecidableEq O] {H : HG J Sl O}

/-- parameter inequality for the load drift -/
theorem load_param (θ σ δ κ L lam : ℝ) (hθ0 : 0 ≤ θ) (hθσ : θ ≤ σ / 64) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hδ0 : 0 ≤ δ) (hδσ : δ ≤ σ / 8) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hL0 : 0 ≤ L) (hL : L ≤ 1 - σ / 2)
    (hlam : lam ≤ θ * σ / 16) :
    L * (1 - θ * (1 - 2 * θ) * (1 - 4 * θ ^ 2 * κ) * (1 - δ)) / (1 - (1 + 2 * θ * κ) * (θ * L)) + lam ≤
      1 - σ / 2 := by
  have hθ1 : θ ≤ 1 / 64 := by linarith
  set c := 1 + 2 * θ * κ
  have hc1 : 1 ≤ c := by simp only [c]; nlinarith [mul_nonneg hθ0 hκ0]
  have hc2 : c ≤ 2 := by simp only [c]; nlinarith [mul_le_mul hθ1 hκ1 hκ0 (by norm_num : (0:ℝ) ≤ 1 / 64)]
  have hr : c * (θ * L) ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left hL hθ0, mul_nonneg hθ0 hL0]
  have hden : 0 < 1 - c * (θ * L) := by linarith
  set q := θ * (1 - 2 * θ) * (1 - 4 * θ ^ 2 * κ) * (1 - δ)
  -- q ≥ θσ/8 + cθ(1 - σ/2)
  have hq : θ * σ / 8 + c * θ * (1 - σ / 2) ≤ q := by
    simp only [q, c]
    have h1 : (1 - 2 * θ) * (1 - 4 * θ ^ 2 * κ) * (1 - δ) ≥ 1 - 2 * θ - 4 * θ ^ 2 * κ - δ := by
      have a1 : 0 ≤ 2 * θ := by linarith
      have a2 : 0 ≤ 4 * θ ^ 2 * κ := by positivity
      have a3 : 2 * θ ≤ 1 := by linarith
      have a4 : 4 * θ ^ 2 * κ ≤ 1 := by nlinarith [sq_nonneg θ]
      nlinarith [mul_nonneg a1 a2, mul_nonneg (mul_nonneg a1 a2) hδ0, mul_nonneg a1 hδ0, mul_nonneg a2 hδ0]
    have h2 : 2 * θ + 4 * θ ^ 2 * κ + 2 * θ * κ ≤ σ / 4 := by
      nlinarith [mul_le_mul hθ1 hκ1 hκ0 (by norm_num : (0:ℝ) ≤ 1 / 64), sq_nonneg θ,
        mul_nonneg (sq_nonneg θ) hκ0, mul_nonneg hθ0 hκ0]
    have h3 : θ * ((1 - 2 * θ) * (1 - 4 * θ ^ 2 * κ) * (1 - δ)) ≥ θ * (1 - 2 * θ - 4 * θ ^ 2 * κ - δ) :=
      mul_le_mul_of_nonneg_left h1 hθ0
    nlinarith [mul_nonneg hθ0 hσ0.le, mul_nonneg (mul_nonneg hθ0 hκ0) hσ0.le, mul_nonneg hθ0 hκ0]
  -- bound the ratio
  have hratio : L * (1 - q) / (1 - c * (θ * L)) ≤ L * (1 - θ * σ / 8) := by
    rw [div_le_iff₀ hden]
    have hq1 : 1 - q ≤ (1 - θ * σ / 8) * (1 - c * (θ * L)) := by
      have : c * (θ * L) ≤ c * θ * (1 - σ / 2) := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hL (by positivity)
      nlinarith [mul_nonneg (mul_nonneg hθ0 hσ0.le) (by positivity : (0:ℝ) ≤ c * (θ * L))]
    nlinarith [mul_le_mul_of_nonneg_left hq1 hL0]
  have hfin : L * (1 - θ * σ / 8) + lam ≤ 1 - σ / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hL (by nlinarith : (0:ℝ) ≤ 1 - θ * σ / 8),
      mul_nonneg hθ0 hσ0.le]
  calc L * (1 - q) / (1 - c * (θ * L)) + lam ≤ L * (1 - θ * σ / 8) + lam := by linarith
    _ ≤ 1 - σ / 2 := hfin

theorem nxt_nonneg (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (Z : J → Option O) (o : O) :
    0 ≤ nxt H θ x Z o := by
  have hpb := piF_bounds θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ o
  unfold nxt
  refine mul_nonneg (mul_nonneg (div_nonneg (hI.x0 o) (by linarith [hpb.1]))
    (Finset.prod_nonneg (fun f _ => av_nonneg _ _ _))) ?_
  linarith [win_le_one (H := H) Z (H.job o)]

theorem nxt_le (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (Z : J → Option O) (o : O) :
    nxt H θ x Z o ≤ x o / (1 - 2 * θ) := by
  have hpb := piF_bounds θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ o
  have hπ : 0 < 1 - 2 * θ := by linarith
  unfold nxt
  have h1 : x o / piF H θ x o ≤ x o / (1 - 2 * θ) := div_le_div_of_nonneg_left (hI.x0 o) hπ hpb.1
  have h2 : 0 ≤ x o / piF H θ x o := div_nonneg (hI.x0 o) (by linarith [hpb.1])
  have hP0 : 0 ≤ ∏ f, av H f (H.sl o) (Z f) := Finset.prod_nonneg (fun f _ => av_nonneg _ _ _)
  have hP1 : ∏ f, av H f (H.sl o) (Z f) ≤ 1 := Finset.prod_le_one (fun f _ => av_nonneg _ _ _) (fun f _ => av_le_one _ _ _)
  have hw0 := win_nonneg (H := H) Z (H.job o)
  have hw1 := win_le_one (H := H) Z (H.job o)
  have h3 : 0 ≤ x o / (1 - 2 * θ) := div_nonneg (hI.x0 o) hπ.le
  calc x o / piF H θ x o * (∏ f, av H f (H.sl o) (Z f)) * (1 - win H Z (H.job o))
      ≤ x o / (1 - 2 * θ) * 1 * 1 := mul_le_mul (mul_le_mul h1 hP1 hP0 h3) (by linarith)
          (by linarith) (by simpa using h3)
    _ = x o / (1 - 2 * θ) := by ring

theorem valid_of_pos (θ : ℝ) (x : O → ℝ) (Z : J → Option O) (hZp : ∀ e, 0 < pp H θ x e (Z e)) :
    Valid H Z := by
  intro e o ho
  have := hZp e
  rw [ho] at this
  simp only [pp] at this
  by_contra h; rw [if_neg h] at this; exact lt_irrefl _ this

theorem lamw_mono (θ κ Λ : ℝ) (hθ0 : 0 ≤ θ) (hκ0 : 0 ≤ κ) (hΛ : 0 ≤ Λ) (n m : ℕ) (h : n ≤ m) :
    lamw θ κ Λ n ≤ lamw θ κ Λ m := by
  unfold lamw
  have : (n : ℝ) ≤ m := by exact_mod_cast h
  have h2 : 50 * θ * κ ^ 2 * n / (1 - 2 * θ) ^ 2 * Λ ≤ 50 * θ * κ ^ 2 * m / (1 - 2 * θ) ^ 2 * Λ := by
    apply mul_le_mul_of_nonneg_right _ hΛ
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left this (by positivity)
  have := Real.sqrt_le_sqrt h2
  linarith

/-- the invariant after a good round -/
theorem inv_next (θ σ δ κ Λ : ℝ) (D : ℕ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 < θ) (hθσ : θ ≤ σ / 64) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hδ0 : 0 ≤ δ) (hδσ : δ ≤ σ / 8)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hΛ : 0 ≤ Λ) (hAs : ∀ s, (As H s).card ≤ D)
    (hlam : lama θ κ Λ + lamw θ κ Λ D ≤ θ * σ / 16)
    (Z : J → Option O) (hZp : ∀ e, 0 < pp H θ x e (Z e))
    (hM : ∀ e, |Mf H θ x e Z - mass H x e| < lam1 θ κ Λ)
    (hL : ∀ s, Ya H θ x s Z - EE H θ x (Ya H θ x s) < lama θ κ Λ ∧
        EE H θ x (Yw H θ x s) - lamw θ κ Λ (As H s).card < Yw H θ x s Z) :
    Inv H σ (δ + lam1 θ κ Λ + 2 * κ / (1 - 2 * θ)) (κ / (1 - 2 * θ)) (nxt H θ x Z) := by
  have hθ1 : θ ≤ 1 / 16 := by linarith
  have hπ : 0 < 1 - 2 * θ := by linarith
  have hZv := valid_of_pos θ x Z hZp
  refine ⟨fun o => nxt_nonneg θ σ δ κ x hI hsl hθ0.le hθ1 hκ1 hσ0.le Z o, fun e => ?_, fun s => ?_,
    fun e t => ?_, fun s t hst => ?_⟩
  · -- masses
    have hmn := mass_nxt θ σ δ κ x hI hsl hθ0.le hθ1 hκ0.le hκ1 hσ0.le Z hZv e
    rcases win_01 (H := H) Z e with hw | hw
    · obtain ⟨h1, h2⟩ := hmn.2 hw
      have hme := hM e
      rcases hI.mass e with h0 | h0
      · left
        have hMf0 : Mf H θ x e Z = 0 := by
          unfold Mf
          refine Finset.sum_eq_zero (fun o ho => ?_)
          have hx0 : x o = 0 := by
            have : x o ≤ mass H x e := Finset.single_le_sum (f := x) (fun o _ => hI.x0 o) ho
            linarith [hI.x0 o]
          rw [hx0, zero_div, zero_mul]
        have : 0 ≤ mass H (nxt H θ x Z) e :=
          Finset.sum_nonneg (fun o _ => nxt_nonneg θ σ δ κ x hI hsl hθ0.le hθ1 hκ1 hσ0.le Z o)
        linarith
      · right
        have habs := abs_lt.mp hme
        constructor <;> linarith [h0.1, h0.2]
    · left; exact hmn.1 hw
  · -- loads
    have hle := load_nxt_le θ σ δ κ x hI hsl hθ0.le hθ1 hκ1 hσ0.le s Z
    have hdr := load_drift θ σ δ κ x hI hsl hθ0.le hθ1 hκ0.le hκ1 hσ0.le hδ0 (by linarith) s
    have hlw := lamw_mono θ κ Λ hθ0.le hκ0.le hΛ _ _ (hAs s)
    have hp := load_param θ σ δ κ (load H x s) (lama θ κ Λ + lamw θ κ Λ (As H s).card) hθ0.le hθσ hσ0 hσ1
      hδ0 hδσ hκ0.le hκ1 (Finset.sum_nonneg (fun o _ => hI.x0 o)) (hI.load s) (by linarith)
    obtain ⟨ha, hb⟩ := hL s
    linarith
  · -- codegree 1
    unfold yw
    calc ∑ o ∈ univ.filter (fun o => H.job o = e ∧ t ∈ H.sl o), nxt H θ x Z o
        ≤ ∑ o ∈ univ.filter (fun o => H.job o = e ∧ t ∈ H.sl o), x o / (1 - 2 * θ) :=
          Finset.sum_le_sum (fun o _ => nxt_le θ σ δ κ x hI hsl hθ0.le hθ1 hκ1 hσ0.le Z o)
      _ = yw H x e t / (1 - 2 * θ) := by unfold yw; rw [Finset.sum_div]
      _ ≤ κ / (1 - 2 * θ) := div_le_div_of_nonneg_right (hI.cod1 e t) hπ.le
  · -- codegree 2
    unfold kw
    calc ∑ o ∈ univ.filter (fun o => s ∈ H.sl o ∧ t ∈ H.sl o), nxt H θ x Z o
        ≤ ∑ o ∈ univ.filter (fun o => s ∈ H.sl o ∧ t ∈ H.sl o), x o / (1 - 2 * θ) :=
          Finset.sum_le_sum (fun o _ => nxt_le θ σ δ κ x hI hsl hθ0.le hθ1 hκ1 hσ0.le Z o)
      _ = kw H x s t / (1 - 2 * θ) := by unfold kw; rw [Finset.sum_div]
      _ ≤ κ / (1 - 2 * θ) := div_le_div_of_nonneg_right (hI.cod2 s t hst) hπ.le

/-- private-slot property of dummy options -/
def Priv (H : HG J Sl O) (dum : O → Prop) : Prop := ∀ o, dum o → ∀ o', o' ≠ o → Disjoint (H.sl o) (H.sl o')

theorem dummy_pick_wins (dum : O → Prop) (hP : Priv H dum) (Z : J → Option O) (hZ : Valid H Z) (e : J) (o : O)
    (ho : Z e = some o) (hd : dum o) : win H Z e = 1 := by
  rw [win_eq, ho]
  simp only
  rw [if_pos (hZ e o ho)]
  refine Finset.prod_eq_one (fun f hf => ?_)
  have hfe : f ≠ e := Finset.ne_of_mem_erase hf
  cases hZf : Z f with
  | none => rfl
  | some o'' =>
    simp only [av]
    rw [if_neg]
    rintro ⟨hj, hdis⟩
    have : o'' ≠ o := by
      intro h; subst h
      exact hfe (hj.symm.trans (hZ e o'' ho))
    exact hdis (hP o hd o'' this).symm

theorem piF_dummy (θ : ℝ) (x : O → ℝ) (dum : O → Prop) (hP : Priv H dum) (o : O) (hd : dum o) :
    piF H θ x o = 1 := by
  unfold piF
  refine Finset.prod_eq_one (fun f hf => ?_)
  have : aff H x f (H.sl o) = 0 := by
    unfold aff
    refine Finset.sum_eq_zero (fun o' ho' => ?_)
    exfalso
    obtain ⟨hj, hdis⟩ := (Finset.mem_filter.mp ho').2
    have hne : o' ≠ o := by
      intro h; subst h; exact Finset.ne_of_mem_erase hf hj.symm
    exact hdis (hP o hd o' hne).symm
  rw [this]; ring

/-- dummy options of an unmatched job keep their weight -/
theorem nxt_dummy (θ : ℝ) (x : O → ℝ) (dum : O → Prop) (hP : Priv H dum) (Z : J → Option O) (hZ : Valid H Z)
    (o : O) (hd : dum o) (hw : win H Z (H.job o) = 0) : nxt H θ x Z o = x o := by
  unfold nxt
  rw [piF_dummy θ x dum hP o hd, hw, div_one, sub_zero, mul_one]
  have : ∏ f, av H f (H.sl o) (Z f) = 1 := by
    refine Finset.prod_eq_one (fun f _ => ?_)
    cases hZf : Z f with
    | none => rfl
    | some o'' =>
      simp only [av]
      rw [if_neg]
      rintro ⟨hj, hdis⟩
      by_cases h : o'' = o
      · subst h
        have := dummy_pick_wins dum hP Z hZ f o'' hZf hd
        rw [← hj] at this; rw [this] at hw; norm_num at hw
      · exact hdis (hP o hd o'' h).symm
  rw [this, mul_one]

theorem dmass_nxt (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ)
    (dum : O → Prop) [DecidablePred dum] (hP : Priv H dum) (Z : J → Option O) (hZ : Valid H Z) (e : J) :
    dmass H dum (nxt H θ x Z) e = (1 - win H Z e) * dmass H dum x e := by
  rcases win_01 (H := H) Z e with hw | hw
  · rw [hw, sub_zero, one_mul]
    unfold dmass
    refine Finset.sum_congr rfl (fun o ho => ?_)
    obtain ⟨hj, hd⟩ := (Finset.mem_filter.mp ho).2
    exact nxt_dummy θ x dum hP Z hZ o hd (hj ▸ hw)
  · rw [hw, sub_self, zero_mul]
    have hm := (mass_nxt θ σ δ κ x hI hsl hθ0 hθ hκ0 hκ1 hσ Z hZ e).1 hw
    have h1 : dmass H dum (nxt H θ x Z) e ≤ mass H (nxt H θ x Z) e := by
      unfold dmass mass
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun o ho => by
        simp only [Finset.mem_filter] at ho ⊢; exact ⟨ho.1, ho.2.1⟩)
        (fun o _ _ => nxt_nonneg θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ Z o)
    have h2 : 0 ≤ dmass H dum (nxt H θ x Z) e :=
      Finset.sum_nonneg (fun o _ => nxt_nonneg θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ Z o)
    linarith

/-- alive weight of a group -/
noncomputable def Wa (H : HG J Sl O) (S : Finset J) (w : J → ℝ) (x : O → ℝ) : ℝ :=
  ∑ e ∈ S, w e * (if mass H x e = 0 then 0 else 1)

/-- dummy weight of a group -/
noncomputable def Wd (H : HG J Sl O) (dum : O → Prop) [DecidablePred dum] (S : Finset J) (w : J → ℝ)
    (x : O → ℝ) : ℝ := ∑ e ∈ S, c2 H dum w x e

theorem win_alive (θ : ℝ) (hθ0 : 0 < θ) (x : O → ℝ) (hx : ∀ o, 0 ≤ x o) (Z : J → Option O)
    (hZp : ∀ e, 0 < pp H θ x e (Z e)) (e : J) (hw : win H Z e = 1) : mass H x e ≠ 0 := by
  rw [win_eq] at hw
  cases hZe : Z e with
  | none => rw [hZe] at hw; simp at hw
  | some o =>
    have hp := hZp e
    rw [hZe] at hp
    simp only [pp] at hp
    have hj : H.job o = e := by by_contra h; rw [if_neg h] at hp; exact lt_irrefl _ hp
    rw [if_pos hj] at hp
    have hxo : 0 < x o := by
      by_contra h; push_neg at h; nlinarith
    intro hm
    have : x o ≤ mass H x e := Finset.single_le_sum (f := x) (fun o _ => hx o)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    linarith

theorem EE_Qw_ge (θ σ δ κ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hsl : ∀ o, (H.sl o).card ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 16) (hκ1 : κ ≤ 1) (hσ : 0 ≤ σ) (hδ1 : δ < 1) (S : Finset J) (c : J → ℝ)
    (hc0 : ∀ e, 0 ≤ c e) :
    θ * (1 - 2 * θ) * (1 - δ) * ∑ e ∈ S, c e * (if mass H x e = 0 then 0 else 1) ≤ EE H θ x (Qw H S c) := by
  unfold Qw
  rw [EE_finsum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun e _ => ?_)
  rw [EE_smul, EE_win]
  have h1 : θ * (1 - 2 * θ) * mass H x e ≤ ∑ o ∈ univ.filter (fun o => H.job o = e), θ * x o * piF H θ x o := by
    unfold mass
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun o _ => ?_)
    have hpb := piF_bounds θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ o
    nlinarith [mul_nonneg hθ0 (hI.x0 o)]
  have hEw0 : 0 ≤ ∑ o ∈ univ.filter (fun o => H.job o = e), θ * x o * piF H θ x o :=
    Finset.sum_nonneg (fun o _ => by
      have hpb := piF_bounds θ σ δ κ x hI hsl hθ0 hθ hκ1 hσ o
      exact mul_nonneg (mul_nonneg hθ0 (hI.x0 o)) (by linarith [hpb.1]))
  rcases hI.mass e with h | h
  · rw [if_pos h]; simp only [mul_zero]; exact mul_nonneg (hc0 e) hEw0
  · rw [if_neg (by linarith [h.1] : ¬ mass H x e = 0), mul_one]
    have h2 : θ * (1 - 2 * θ) * (1 - δ) ≤ θ * (1 - 2 * θ) * mass H x e :=
      mul_le_mul_of_nonneg_left h.1 (mul_nonneg hθ0 (by linarith))
    nlinarith [hc0 e]

/-- **one round step**: everything the iteration needs -/
theorem round_step {G : Type} [Fintype G] [DecidableEq G] (hsl : ∀ o, (H.sl o).card ≤ 2)
    (dum : O → Prop) [DecidablePred dum] (hP : Priv H dum) (memb : G → Finset J) (w : J → ℝ)
    (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1)
    (θ σ δ κ Λ : ℝ) (x : O → ℝ) (hI : Inv H σ δ κ x) (hθ0 : 0 < θ) (hθσ : θ ≤ σ / 64) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1) (hδ0 : 0 ≤ δ) (hδσ : δ ≤ σ / 8) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (D : ℕ) (hD1 : 1 ≤ D)
    (hNb : ∀ e, (Nb H e).card ≤ D) (hAs : ∀ s, (As H s).card ≤ D)
    (hse : ∀ e, (univ.filter (fun s => e ∈ As H s)).card ≤ D)
    (hmemb : ∀ g, (memb g).card ≤ D) (hge : ∀ e, (univ.filter (fun g => e ∈ memb g)).card ≤ D)
    (hΛ : 0 ≤ Λ) (hepd : Real.exp 1 * (5 * Real.exp (-Λ)) * ((3 * D ^ 4 : ℕ) + 1) ≤ 1)
    (hlam : lama θ κ Λ + lamw θ κ Λ D ≤ θ * σ / 16)
    (hδ' : δ + lam1 θ κ Λ + 2 * κ / (1 - 2 * θ) < 1) :
    ∃ Z : J → Option O, Valid H Z ∧ (∀ e o, Z e = some o → 0 < x o) ∧
      Inv H σ (δ + lam1 θ κ Λ + 2 * κ / (1 - 2 * θ)) (κ / (1 - 2 * θ)) (nxt H θ x Z) ∧
      (∀ e, win H Z e = 1 → mass H (nxt H θ x Z) e = 0) ∧
      (∀ e, mass H (nxt H θ x Z) e = 0 ↔ (mass H x e = 0 ∨ win H Z e = 1)) ∧
      (∀ e, win H Z e = 1 → mass H x e ≠ 0) ∧
      (∀ o o', o ≠ o' → ¬Disjoint (H.sl o) (H.sl o') → (∃ e, Z e = some o' ∧ win H Z e = 1) →
        nxt H θ x Z o = 0) ∧
      (∀ o, x o = 0 → nxt H θ x Z o = 0) ∧
      (∀ g, Wa H (memb g) w (nxt H θ x Z) ≤
          (1 - θ * (1 - 2 * θ) * (1 - δ)) * Wa H (memb g) w x + lamg θ Λ (memb g).card) ∧
      (∀ g, Wd H dum (memb g) w (nxt H θ x Z) ≤
          (1 - θ * (1 - 2 * θ) * (1 - δ)) * Wd H dum (memb g) w x + lamg θ Λ (memb g).card) ∧
      (∀ g, Dq H dum (memb g) w Z ≤ 2 * θ * Wd H dum (memb g) w x + lamD θ Λ (memb g).card) ∧
      (∀ g, Wa H (memb g) w x = Wa H (memb g) w (nxt H θ x Z) + Qw H (memb g) w Z) := by
  have hθ1 : θ ≤ 1 / 16 := by linarith
  have hπ : 0 < 1 - 2 * θ := by linarith
  obtain ⟨Z, hZp, hM, hL, hG⟩ := round_exists hsl dum memb w hw θ σ δ κ x hI hθ0.le hθ1 hκ0 hκ1 hσ0.le hδ0
    (by linarith) D hD1 hNb hAs hse hmemb hge Λ hΛ hepd
  have hZv := valid_of_pos θ x Z hZp
  have hInv := inv_next θ σ δ κ Λ D x hI hsl hθ0 hθσ hσ0 hσ1 hδ0 hδσ hκ0 hκ1 hΛ hAs hlam Z hZp hM hL
  have hiff : ∀ e, mass H (nxt H θ x Z) e = 0 ↔ (mass H x e = 0 ∨ win H Z e = 1) := by
    intro e
    have hmn := mass_nxt θ σ δ κ x hI hsl hθ0.le hθ1 hκ0.le hκ1 hσ0.le Z hZv e
    constructor
    · intro h0
      rcases win_01 (H := H) Z e with hw0 | hw0
      · left
        by_contra hne
        rcases hI.mass e with h | h
        · exact hne h
        · obtain ⟨h1, _⟩ := hmn.2 hw0
          have := abs_lt.mp (hM e)
          linarith [h.1]
      · right; exact hw0
    · rintro (h | h)
      · rcases win_01 (H := H) Z e with hw0 | hw0
        · obtain ⟨_, h2⟩ := hmn.2 hw0
          have hMf0 : Mf H θ x e Z = 0 := by
            unfold Mf
            refine Finset.sum_eq_zero (fun o ho => ?_)
            have hx0 : x o = 0 := by
              have : x o ≤ mass H x e := Finset.single_le_sum (f := x) (fun o _ => hI.x0 o) ho
              linarith [hI.x0 o]
            rw [hx0, zero_div, zero_mul]
          have : 0 ≤ mass H (nxt H θ x Z) e :=
            Finset.sum_nonneg (fun o _ => nxt_nonneg θ σ δ κ x hI hsl hθ0.le hθ1 hκ1 hσ0.le Z o)
          linarith
        · exact hmn.1 hw0
      · exact hmn.1 h
  have hWaeq : ∀ g, Wa H (memb g) w x = Wa H (memb g) w (nxt H θ x Z) + Qw H (memb g) w Z := by
    intro g
    unfold Wa Qw
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rcases win_01 (H := H) Z e with hw0 | hw0
    · rw [hw0, mul_zero, add_zero]
      by_cases h : mass H x e = 0
      · rw [if_pos h, if_pos ((hiff e).2 (Or.inl h))]
      · rw [if_neg h, if_neg (fun h' => by
          rcases (hiff e).1 h' with h1 | h1
          · exact h h1
          · rw [hw0] at h1; norm_num at h1)]
    · rw [hw0, if_neg (win_alive θ hθ0 x hI.x0 Z hZp e hw0), if_pos ((hiff e).2 (Or.inr hw0))]; ring
  refine ⟨Z, hZv, fun e o ho => ?_, hInv, fun e hw0 => ((hiff e).2 (Or.inr hw0)), hiff,
    fun e hw0 => win_alive θ hθ0 x hI.x0 Z hZp e hw0, fun o o' hne hmeet ⟨e, he, hwe⟩ => ?_,
    fun o hx0 => ?_, fun g => ?_, fun g => ?_, fun g => ?_, hWaeq⟩
  · have hp := hZp e
    rw [ho] at hp
    simp only [pp] at hp
    rw [if_pos (hZv e o ho)] at hp
    by_contra h; push_neg at h; nlinarith [hI.x0 o]
  · unfold nxt
    by_cases hj : H.job o = e
    · rw [hj, hwe, sub_self, mul_zero]
    · have : ∏ f, av H f (H.sl o) (Z f) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ e) ?_
        rw [he]; simp only [av]
        rw [if_pos ⟨hZv e o' he, fun h => hmeet h.symm⟩]
      rw [this, mul_zero, zero_mul]
  · unfold nxt; rw [hx0, zero_div, zero_mul, zero_mul]
  · -- alive weight
    have h1 := (hG g).1
    have h2 := EE_Qw_ge θ σ δ κ x hI hsl hθ0.le hθ1 hκ1 hσ0.le (by linarith) (memb g) w (fun e => (hw e).1)
    have h3 := hWaeq g
    unfold Wa at h3 ⊢
    linarith
  · -- dummy weight
    have h1 := (hG g).2.1
    have h2 := EE_Qw_ge θ σ δ κ x hI hsl hθ0.le hθ1 hκ1 hσ0.le (by linarith) (memb g) (c2 H dum w x)
      (fun e => div_nonneg (mul_nonneg (hw e).1 (Finset.sum_nonneg (fun o _ => hI.x0 o))) (by norm_num))
    have hc2alive : ∑ e ∈ memb g, c2 H dum w x e * (if mass H x e = 0 then 0 else 1) = Wd H dum (memb g) w x := by
      unfold Wd
      refine Finset.sum_congr rfl (fun e _ => ?_)
      by_cases h : mass H x e = 0
      · rw [if_pos h, mul_zero]
        unfold c2
        have hdm : dmass H dum x e ≤ mass H x e := by
          unfold dmass mass
          exact Finset.sum_le_sum_of_subset_of_nonneg (fun o ho => by
            simp only [Finset.mem_filter] at ho ⊢; exact ⟨ho.1, ho.2.1⟩) (fun o _ _ => hI.x0 o)
        have : dmass H dum x e = 0 := le_antisymm (h ▸ hdm) (Finset.sum_nonneg (fun o _ => hI.x0 o))
        rw [this]; ring
      · rw [if_neg h, mul_one]
    rw [hc2alive] at h2
    have h3 : Wd H dum (memb g) w (nxt H θ x Z) = Wd H dum (memb g) w x - Qw H (memb g) (c2 H dum w x) Z := by
      unfold Wd Qw
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      unfold c2
      rw [dmass_nxt θ σ δ κ x hI hsl hθ0.le hθ1 hκ0.le hκ1 hσ0.le dum hP Z hZv e]
      ring
    rw [h3]
    linarith
  · -- dummy picks
    have h1 := (hG g).2.2
    rw [EE_Dq] at h1
    have : θ * ∑ e ∈ memb g, w e * dmass H dum x e = 2 * θ * Wd H dum (memb g) w x := by
      unfold Wd c2; rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e _ => by ring)
    linarith

end Nib

end SecRound3

section SecIter

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset TwoStage

namespace Nib

variable {J Sl O : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
  [Fintype O] [DecidableEq O] {H : HG J Sl O}

theorem lam1_mono (θ Λ : ℝ) (hθ : θ ≤ 1 / 16) (hθ0 : 0 ≤ θ) (hΛ : 0 ≤ Λ) (κ κ' : ℝ) (h0 : 0 ≤ κ) (h : κ ≤ κ') :
    lam1 θ κ Λ ≤ lam1 θ κ' Λ := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  unfold lam1
  have h1 : 8 * θ * κ / (1 - 2 * θ) ^ 2 * Λ ≤ 8 * θ * κ' / (1 - 2 * θ) ^ 2 * Λ := by
    apply mul_le_mul_of_nonneg_right _ hΛ
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith
  have h2 := Real.sqrt_le_sqrt h1
  have h3 : 4 * κ / (1 - 2 * θ) ≤ 4 * κ' / (1 - 2 * θ) := div_le_div_of_nonneg_right (by linarith) hπ.le
  nlinarith

theorem lama_mono (θ Λ : ℝ) (hθ : θ ≤ 1 / 16) (hθ0 : 0 ≤ θ) (hΛ : 0 ≤ Λ) (κ κ' : ℝ) (h0 : 0 ≤ κ) (h : κ ≤ κ') :
    lama θ κ Λ ≤ lama θ κ' Λ := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  unfold lama
  have h1 : 2 * θ * κ / (1 - 2 * θ) ^ 2 * Λ ≤ 2 * θ * κ' / (1 - 2 * θ) ^ 2 * Λ := by
    apply mul_le_mul_of_nonneg_right _ hΛ
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith
  have h2 := Real.sqrt_le_sqrt h1
  have h3 : 4 * κ / (1 - 2 * θ) ≤ 4 * κ' / (1 - 2 * θ) := div_le_div_of_nonneg_right (by linarith) hπ.le
  nlinarith

theorem lamw_mono_k (θ Λ : ℝ) (hθ : θ ≤ 1 / 16) (hθ0 : 0 ≤ θ) (hΛ : 0 ≤ Λ) (n : ℕ) (κ κ' : ℝ) (h0 : 0 ≤ κ)
    (h : κ ≤ κ') : lamw θ κ Λ n ≤ lamw θ κ' Λ n := by
  have hπ : 0 < 1 - 2 * θ := by linarith
  unfold lamw
  have h1 : 12 * θ * κ / (1 - 2 * θ) ^ 2 * Λ ≤ 12 * θ * κ' / (1 - 2 * θ) ^ 2 * Λ := by
    apply mul_le_mul_of_nonneg_right _ hΛ
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith
  have h1' : 50 * θ * κ ^ 2 * n / (1 - 2 * θ) ^ 2 * Λ ≤ 50 * θ * κ' ^ 2 * n / (1 - 2 * θ) ^ 2 * Λ := by
    apply mul_le_mul_of_nonneg_right _ hΛ
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have : κ ^ 2 ≤ κ' ^ 2 := pow_le_pow_left₀ h0 h 2
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg hθ0 hn]
  have h2 := Real.sqrt_le_sqrt h1
  have h2' := Real.sqrt_le_sqrt h1'
  have h3 : 8 * κ / (1 - 2 * θ) ≤ 8 * κ' / (1 - 2 * θ) := div_le_div_of_nonneg_right (by linarith) hπ.le
  have h4 : 10 * κ / (1 - 2 * θ) ≤ 10 * κ' / (1 - 2 * θ) := div_le_div_of_nonneg_right (by linarith) hπ.le
  nlinarith

/-- coefficients of the iteration -/
noncomputable def cA (ρ : ℝ) : ℕ → ℝ
  | 0 => 1
  | R + 1 => (1 - ρ) * cA ρ R

noncomputable def cB (θ ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | R + 1 => 2 * θ + (1 - ρ) * cB θ ρ R

noncomputable def cC (θ ρ Λ : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | R + 1 => lamD θ Λ n + (cA ρ R + cB θ ρ R) * lamg θ Λ n + cC θ ρ Λ n R

theorem cA_nonneg (ρ : ℝ) (hρ : ρ ≤ 1) : ∀ R, 0 ≤ cA ρ R
  | 0 => by simp [cA]
  | R + 1 => by simp only [cA]; exact mul_nonneg (by linarith) (cA_nonneg ρ hρ R)

theorem cB_nonneg (θ ρ : ℝ) (hθ : 0 ≤ θ) (hρ : ρ ≤ 1) : ∀ R, 0 ≤ cB θ ρ R
  | 0 => by simp [cB]
  | R + 1 => by simp only [cB]; nlinarith [cB_nonneg θ ρ hθ hρ R]

/-- failure weight: alive jobs of the group not matched through a real option -/
noncomputable def Fail (H : HG J Sl O) (dum : O → Prop) [DecidablePred dum] (S : Finset J) (w : J → ℝ)
    (x : O → ℝ) (M : Finset O) : ℝ :=
  ∑ e ∈ S, w e * (if mass H x e = 0 then 0 else 1) *
    (@ite ℝ (∃ m ∈ M, H.job m = e ∧ ¬ dum m) (Classical.propDecidable _) 0 1)

theorem Wa_nonneg (S : Finset J) (w : J → ℝ) (hw : ∀ e, 0 ≤ w e) (x : O → ℝ) : 0 ≤ Wa H S w x :=
  Finset.sum_nonneg (fun e _ => mul_nonneg (hw e) (by split_ifs <;> norm_num))

theorem Wd_nonneg (dum : O → Prop) [DecidablePred dum] (S : Finset J) (w : J → ℝ) (hw : ∀ e, 0 ≤ w e)
    (x : O → ℝ) (hx : ∀ o, 0 ≤ x o) : 0 ≤ Wd H dum S w x :=
  Finset.sum_nonneg (fun e _ => div_nonneg (mul_nonneg (hw e) (Finset.sum_nonneg (fun o _ => hx o))) (by norm_num))

/-- **the iteration** -/
theorem iterate {G : Type} [Fintype G] [DecidableEq G] (hsl : ∀ o, (H.sl o).card ≤ 2)
    (dum : O → Prop) [DecidablePred dum] (hP : Priv H dum) (memb : G → Finset J) (w : J → ℝ)
    (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1) (θ σ Λ δmax K : ℝ) (hθ0 : 0 < θ) (hθσ : θ ≤ σ / 64) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1) (hδm0 : 0 ≤ δmax) (hδmσ : δmax ≤ σ / 8) (hK0 : 0 < K) (hK1 : K ≤ 1)
    (D : ℕ) (hD1 : 1 ≤ D)
    (hNb : ∀ e, (Nb H e).card ≤ D) (hAs : ∀ s, (As H s).card ≤ D)
    (hse : ∀ e, (univ.filter (fun s => e ∈ As H s)).card ≤ D)
    (hmemb : ∀ g, (memb g).card ≤ D) (hge : ∀ e, (univ.filter (fun g => e ∈ memb g)).card ≤ D)
    (hΛ : 0 ≤ Λ) (hepd : Real.exp 1 * (5 * Real.exp (-Λ)) * ((3 * D ^ 4 : ℕ) + 1) ≤ 1)
    (hlamK : lama θ K Λ + lamw θ K Λ D ≤ θ * σ / 16) :
    ∀ R : ℕ, ∀ (δ κ : ℝ) (x : O → ℝ), Inv H σ δ κ x → 0 ≤ δ →
      δ + R * (lam1 θ K Λ + 2 * K / (1 - 2 * θ)) ≤ δmax → 0 < κ → κ ≤ K * (1 - 2 * θ) ^ R →
      ∃ M : Finset O, (∀ o ∈ M, 0 < x o) ∧
        (∀ o ∈ M, ∀ o' ∈ M, o ≠ o' → H.job o ≠ H.job o' ∧ Disjoint (H.sl o) (H.sl o')) ∧
        ∀ g, Fail H dum (memb g) w x M ≤ cA (θ * (1 - 2 * θ) * (1 - δmax)) R * Wa H (memb g) w x +
          cB θ (θ * (1 - 2 * θ) * (1 - δmax)) R * Wd H dum (memb g) w x +
          cC θ (θ * (1 - 2 * θ) * (1 - δmax)) Λ (memb g).card R := by
  have hθ1 : θ ≤ 1 / 16 := by linarith
  have hπ : 0 < 1 - 2 * θ := by linarith
  set ρ₀ := θ * (1 - 2 * θ) * (1 - δmax) with hρ₀
  have hρ₀1 : ρ₀ ≤ 1 := by
    simp only [ρ₀]; nlinarith [mul_nonneg hθ0.le (by linarith : (0:ℝ) ≤ 1 - 2 * θ)]
  have hε0 : 0 ≤ lam1 θ K Λ + 2 * K / (1 - 2 * θ) := by
    unfold lam1
    have := Real.sqrt_nonneg (8 * θ * K / (1 - 2 * θ) ^ 2 * Λ)
    have : 0 ≤ 4 * K / (1 - 2 * θ) := by positivity
    have : 0 ≤ 2 * K / (1 - 2 * θ) := by positivity
    nlinarith
  intro R
  induction R with
  | zero =>
    intro δ κ x hI _ _ _ _
    refine ⟨∅, by simp, by simp, fun g => ?_⟩
    simp only [cA, cB, cC, zero_mul, add_zero, one_mul]
    unfold Fail Wa
    refine le_of_eq (Finset.sum_congr rfl (fun e _ => ?_))
    have hno : ¬ ∃ m ∈ (∅ : Finset O), H.job m = e ∧ ¬dum m := fun ⟨m, hm, _⟩ => by simp at hm
    rw [@if_neg _ (Classical.propDecidable (∃ m ∈ (∅ : Finset O), H.job m = e ∧ ¬dum m)) hno]; ring
  | succ R ih =>
    intro δ κ x hI hδ0 hδR hκ0 hκR
    have hpowle : (1 - 2 * θ) ^ (R + 1) ≤ 1 := pow_le_one₀ hπ.le (by linarith)
    have hκK : κ ≤ K := le_trans hκR (by nlinarith)
    have hκ1 : κ ≤ 1 := le_trans hκK hK1
    have hlam : lama θ κ Λ + lamw θ κ Λ D ≤ θ * σ / 16 :=
      le_trans (add_le_add (lama_mono θ Λ hθ1 hθ0.le hΛ κ K hκ0.le hκK)
        (lamw_mono_k θ Λ hθ1 hθ0.le hΛ D κ K hκ0.le hκK)) hlamK
    have hRε : (R : ℝ) * (lam1 θ K Λ + 2 * K / (1 - 2 * θ)) ≥ 0 := by positivity
    have hstep_δ : lam1 θ κ Λ + 2 * κ / (1 - 2 * θ) ≤ lam1 θ K Λ + 2 * K / (1 - 2 * θ) :=
      add_le_add (lam1_mono θ Λ hθ1 hθ0.le hΛ κ K hκ0.le hκK) (div_le_div_of_nonneg_right (by linarith) hπ.le)
    have hδ'1 : δ + lam1 θ κ Λ + 2 * κ / (1 - 2 * θ) < 1 := by
      push_cast at hδR; nlinarith
    have hδσ : δ ≤ σ / 8 := by push_cast at hδR; nlinarith
    obtain ⟨Z, hZv, hZx, hInv, hwin0, hiff, hwinA, hkill, hzero, hWa, hWd, hDq, hWaeq⟩ :=
      round_step hsl dum hP memb w hw θ σ δ κ Λ x hI hθ0 hθσ hσ0 hσ1 hδ0 hδσ hκ0 hκ1 D hD1 hNb hAs hse hmemb hge
        hΛ hepd hlam hδ'1
    set x' := nxt H θ x Z
    obtain ⟨M', hM'x, hM'm, hM'F⟩ := ih (δ + lam1 θ κ Λ + 2 * κ / (1 - 2 * θ)) (κ / (1 - 2 * θ)) x' hInv
      (by unfold lam1; positivity) (by push_cast at hδR; nlinarith) (by positivity)
      (by
        rw [div_le_iff₀ hπ]
        calc κ ≤ K * (1 - 2 * θ) ^ (R + 1) := hκR
          _ = K * (1 - 2 * θ) ^ R * (1 - 2 * θ) := by ring)
    set M₁ := @Finset.filter _ (fun o => ∃ e, Z e = some o ∧ win H Z e = 1) (fun _ => Classical.propDecidable _) univ
    have hM₁ : ∀ o, o ∈ M₁ ↔ ∃ e, Z e = some o ∧ win H Z e = 1 := by
      intro o; simp only [M₁]; rw [@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _)]; simp
    have hx'pos : ∀ o, 0 < x' o → 0 < x o := by
      intro o h
      rcases (hI.x0 o).eq_or_lt with h0 | h0
      · rw [hzero o h0.symm] at h; exact absurd h (lt_irrefl 0)
      · exact h0
    -- options of a winner die
    have hwin_dead : ∀ e o, win H Z e = 1 → H.job o = e → x' o = 0 := by
      intro e o hw hj
      have hm := hwin0 e hw
      have : x' o ≤ mass H x' e := Finset.single_le_sum (f := x') (fun o _ => hInv.x0 o)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
      linarith [hInv.x0 o]
    refine ⟨M₁ ∪ M', fun o ho => ?_, fun o ho o' ho' hne => ?_, fun g => ?_⟩
    · rcases Finset.mem_union.mp ho with h | h
      · obtain ⟨e, he, _⟩ := (hM₁ o).1 h; exact hZx e o he
      · exact hx'pos o (hM'x o h)
    · -- matching
      have key : ∀ o ∈ M₁, ∀ o' ∈ M', H.job o ≠ H.job o' ∧ Disjoint (H.sl o) (H.sl o') := by
        intro o ho o' ho'
        obtain ⟨e, he, hw⟩ := (hM₁ o).1 ho
        have hjo : H.job o = e := hZv e o he
        have hpos := hM'x o' ho'
        constructor
        · intro hj
          have := hwin_dead e o' hw (hj ▸ hjo)
          rw [this] at hpos; exact lt_irrefl 0 hpos
        · by_contra hd
          by_cases heq : o' = o
          · subst heq
            have := hwin_dead e o' hw hjo
            rw [this] at hpos; exact lt_irrefl 0 hpos
          · have := hkill o' o heq (fun h => hd h.symm) ⟨e, he, hw⟩
            rw [this] at hpos; exact lt_irrefl 0 hpos
      rcases Finset.mem_union.mp ho with h | h <;> rcases Finset.mem_union.mp ho' with h' | h'
      · obtain ⟨e, he, hw⟩ := (hM₁ o).1 h
        obtain ⟨e', he', hw'⟩ := (hM₁ o').1 h'
        have hee : e ≠ e' := by
          intro heq; subst heq; rw [he] at he'; exact hne (Option.some.inj he')
        refine ⟨by rw [hZv e o he, hZv e' o' he']; exact hee, ?_⟩
        exact win_disjoint' Z e e' hee o o' he he' hw hw'
      · exact key o h o' h'
      · have := key o' h' o h
        exact ⟨fun hj => this.1 hj.symm, this.2.symm⟩
      · exact hM'm o h o' h' hne
    · -- failure bound
      have hF : Fail H dum (memb g) w x (M₁ ∪ M') ≤ Dq H dum (memb g) w Z + Fail H dum (memb g) w x' M' := by
        unfold Fail Dq
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum (fun e _ => ?_)
        have hw0 := (hw e).1
        rcases win_01 (H := H) Z e with hwe | hwe
        · -- not matched this round
          have hal : (mass H x' e = 0 ↔ mass H x e = 0) := by
            rw [hiff e]; constructor
            · rintro (h | h); exact h; rw [hwe] at h; norm_num at h
            · intro h; left; exact h
          have hdpk : 0 ≤ w e * dpk H dum e (Z e) := mul_nonneg hw0 (by
            cases Z e with
            | none => simp [dpk]
            | some o => simp only [dpk]; split_ifs <;> norm_num)
          have hmono : (@ite ℝ (∃ m ∈ M₁ ∪ M', H.job m = e ∧ ¬dum m) (Classical.propDecidable _) 0 1) ≤
              (@ite ℝ (∃ m ∈ M', H.job m = e ∧ ¬dum m) (Classical.propDecidable _) 0 1) := by
            by_cases h1 : ∃ m ∈ M', H.job m = e ∧ ¬dum m
            · obtain ⟨m, hm, hm2⟩ := h1
              rw [@if_pos _ (Classical.propDecidable _) ⟨m, Finset.mem_union_right _ hm, hm2⟩,
                @if_pos _ (Classical.propDecidable _) ⟨m, hm, hm2⟩]
            · rw [@if_neg _ (Classical.propDecidable _) h1]; split_ifs <;> norm_num
          by_cases hm : mass H x e = 0
          · rw [if_pos hm, if_pos (hal.2 hm)]; simp only [mul_zero, zero_mul, add_zero]; exact hdpk
          · rw [if_neg hm, if_neg (fun h => hm (hal.1 h)), mul_one]
            have := mul_le_mul_of_nonneg_left hmono hw0
            linarith
        · -- matched this round
          cases hZe : Z e with
          | none => rw [win_eq, hZe] at hwe; simp at hwe
          | some o =>
            have hoM : o ∈ M₁ := (hM₁ o).2 ⟨e, hZe, hwe⟩
            have hjo : H.job o = e := hZv e o hZe
            have hfail' : 0 ≤ w e * (if mass H x' e = 0 then 0 else 1) *
                (@ite ℝ (∃ m ∈ M', H.job m = e ∧ ¬dum m) (Classical.propDecidable _) 0 1) :=
              mul_nonneg (mul_nonneg hw0 (by split_ifs <;> norm_num)) (by split_ifs <;> norm_num)
            by_cases hd : dum o
            · have : dpk H dum e (some o) = 1 := by simp [dpk, hd, hjo]
              rw [this, mul_one]
              have ha1 : (if mass H x e = 0 then (0:ℝ) else 1) ≤ 1 := by split_ifs <;> norm_num
              have hb1 : (@ite ℝ (∃ m ∈ M₁ ∪ M', H.job m = e ∧ ¬dum m) (Classical.propDecidable _) 0 1) ≤ 1 := by
                split_ifs <;> norm_num
              have ha0 : 0 ≤ (if mass H x e = 0 then (0:ℝ) else 1) := by split_ifs <;> norm_num
              have h1 : w e * (if mass H x e = 0 then 0 else 1) *
                  (@ite ℝ (∃ m ∈ M₁ ∪ M', H.job m = e ∧ ¬dum m) (Classical.propDecidable _) 0 1) ≤ w e := by
                calc w e * (if mass H x e = 0 then 0 else 1) *
                    (@ite ℝ (∃ m ∈ M₁ ∪ M', H.job m = e ∧ ¬dum m) (Classical.propDecidable _) 0 1)
                    ≤ w e * (if mass H x e = 0 then 0 else 1) * 1 :=
                      mul_le_mul_of_nonneg_left hb1 (mul_nonneg hw0 ha0)
                  _ ≤ w e * 1 * 1 := by
                      apply mul_le_mul_of_nonneg_right _ (by norm_num)
                      exact mul_le_mul_of_nonneg_left ha1 hw0
                  _ = w e := by ring
              linarith
            · rw [@if_pos _ (Classical.propDecidable (∃ m ∈ M₁ ∪ M', H.job m = e ∧ ¬dum m))
                ⟨o, Finset.mem_union_left _ hoM, hjo, hd⟩, mul_zero]
              have : 0 ≤ w e * dpk H dum e (some o) := mul_nonneg hw0 (by simp only [dpk]; split_ifs <;> norm_num)
              linarith
      have hρ : 1 - θ * (1 - 2 * θ) * (1 - δ) ≤ 1 - ρ₀ := by
        simp only [ρ₀]
        have : δ ≤ δmax := by push_cast at hδR; nlinarith
        nlinarith [mul_nonneg hθ0.le (by linarith : (0:ℝ) ≤ 1 - 2 * θ)]
      have hWa0 := Wa_nonneg (H := H) (memb g) w (fun e => (hw e).1) x
      have hWd0 := Wd_nonneg (H := H) dum (memb g) w (fun e => (hw e).1) x hI.x0
      have hcA := cA_nonneg ρ₀ hρ₀1 R
      have hcB := cB_nonneg θ ρ₀ hθ0.le hρ₀1 R
      have hIH := hM'F g
      have h1 := hWa g
      have h2 := hWd g
      have h3 := hDq g
      simp only [cA, cB, cC]
      have e1 : cA ρ₀ R * Wa H (memb g) w x' ≤ cA ρ₀ R * ((1 - ρ₀) * Wa H (memb g) w x + lamg θ Λ (memb g).card) :=
        mul_le_mul_of_nonneg_left (le_trans h1 (by linarith [mul_le_mul_of_nonneg_right hρ hWa0])) hcA
      have e2 : cB θ ρ₀ R * Wd H dum (memb g) w x' ≤
          cB θ ρ₀ R * ((1 - ρ₀) * Wd H dum (memb g) w x + lamg θ Λ (memb g).card) :=
        mul_le_mul_of_nonneg_left (le_trans h2 (by linarith [mul_le_mul_of_nonneg_right hρ hWd0])) hcB
      linarith [hF, h3, hIH, e1, e2]

end Nib

end SecIter

section SecFinal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset TwoStage

namespace Nib

theorem cA_le_exp (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : ∀ R, cA ρ R ≤ Real.exp (-(ρ * R))
  | 0 => by simp [cA]
  | R + 1 => by
    simp only [cA]
    have ih := cA_le_exp ρ h0 h1 R
    have h2 : 1 - ρ ≤ Real.exp (-ρ) := by linarith [Real.add_one_le_exp (-ρ)]
    calc (1 - ρ) * cA ρ R ≤ Real.exp (-ρ) * Real.exp (-(ρ * R)) :=
          mul_le_mul h2 ih (cA_nonneg ρ h1 R) (Real.exp_pos _).le
      _ = Real.exp (-(ρ * ↑(R + 1))) := by rw [← Real.exp_add]; push_cast; ring_nf

theorem cA_le_one (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : ∀ R, cA ρ R ≤ 1
  | 0 => by simp [cA]
  | R + 1 => by
    simp only [cA]
    have := cA_le_one ρ h0 h1 R
    have := cA_nonneg ρ h1 R
    nlinarith

theorem cB_le (θ ρ : ℝ) (hθ : 0 ≤ θ) (h0 : 0 < ρ) (h1 : ρ ≤ 1) : ∀ R, cB θ ρ R ≤ 2 * θ / ρ
  | 0 => by simp [cB]; positivity
  | R + 1 => by
    simp only [cB]
    have ih := cB_le θ ρ hθ h0 h1 R
    have h2 : (1 - ρ) * cB θ ρ R ≤ (1 - ρ) * (2 * θ / ρ) := mul_le_mul_of_nonneg_left ih (by linarith)
    have e : 2 * θ + (1 - ρ) * (2 * θ / ρ) = 2 * θ / ρ := by field_simp; ring
    linarith

theorem cC_le (θ ρ Λ : ℝ) (hθ : 0 ≤ θ) (h0 : 0 < ρ) (h1 : ρ ≤ 1) (n : ℕ) (L : ℝ)
    (hL : lamD θ Λ n + (1 + 2 * θ / ρ) * lamg θ Λ n ≤ L) (hlg : 0 ≤ lamg θ Λ n) :
    ∀ R, cC θ ρ Λ n R ≤ R * L
  | 0 => by simp [cC]
  | R + 1 => by
    simp only [cC]
    have ih := cC_le θ ρ Λ hθ h0 h1 n L hL hlg R
    have hA := cA_le_one ρ h0.le h1 R
    have hB := cB_le θ ρ hθ h0 h1 R
    have : (cA ρ R + cB θ ρ R) * lamg θ Λ n ≤ (1 + 2 * θ / ρ) * lamg θ Λ n :=
      mul_le_mul_of_nonneg_right (by linarith) hlg
    push_cast
    linarith

theorem sqrt_le_of (u b : ℝ) (hb : 0 ≤ b) (h : u ≤ b ^ 2) : Real.sqrt u ≤ b :=
  (Real.sqrt_le_sqrt h).trans (Real.sqrt_sq hb).le

theorem sqrt_term (c X u π : ℝ) (hc : 0 ≤ c) (hX0 : 0 ≤ X) (hXu : X ≤ u ^ 2) (hu : 0 ≤ u) (hπ : 0 < π)
    (hπ2 : 1 / π ^ 2 ≤ 4) (s : ℝ) (hs : 4 * c ≤ s ^ 2) (hs0 : 0 ≤ s) :
    Real.sqrt (c * X * (1 / π ^ 2)) ≤ s * u := by
  apply sqrt_le_of _ _ (mul_nonneg hs0 hu)
  calc c * X * (1 / π ^ 2) ≤ c * u ^ 2 * 4 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hXu hc) hπ2 (by positivity) (by positivity)
    _ = 4 * c * u ^ 2 := by ring
    _ ≤ s ^ 2 * u ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg u)
    _ = (s * u) ^ 2 := by ring

set_option maxHeartbeats 1000000 in
/-- the arithmetic of the parameter choice -/
theorem param_arith (θ σ δmax K Λ κ CK R a : ℝ) (D : ℕ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 64) (hσ0 : 0 < σ)
    (hδ0 : 0 < δmax) (hδσ : δmax ≤ σ / 8) (hδ1 : δmax ≤ 1 / 8) (hCK : 1 ≤ CK) (hR0 : 0 ≤ R)
    (ha : a = θ * δmax / (2000 * (R + 1) * CK ^ 2)) (hK : K = κ * CK) (hκ0 : 0 < κ) (hΛ : 0 ≤ Λ)
    (hD : 1 ≤ D) (h1 : κ * (Λ + 1) ≤ a ^ 2) (h2 : κ ^ 2 * (D : ℝ) * (Λ + 1) ≤ a ^ 2) :
    K ≤ 1 ∧ lama θ K Λ + lamw θ K Λ D ≤ θ * σ / 16 ∧
      R * (lam1 θ K Λ + 2 * K / (1 - 2 * θ)) ≤ δmax := by
  have hπ0 : 0 < 1 - 2 * θ := by linarith
  have hπ2 : 1 / (1 - 2 * θ) ^ 2 ≤ 4 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have hπ1 : 1 / (1 - 2 * θ) ≤ 2 := by rw [div_le_iff₀ hπ0]; linarith
  have hCK0 : 0 < CK := by linarith
  have ha0 : 0 < a := by rw [ha]; positivity
  have hθδ : θ * δmax ≤ 1 / 512 := by nlinarith
  have ha1 : a ≤ 1 / 2000 := by
    rw [ha, div_le_iff₀ (by positivity)]
    have : 1 ≤ (R + 1) * CK ^ 2 := by nlinarith
    nlinarith
  set u := CK * a with hu
  have hu0 : 0 ≤ u := by positivity
  have hK0 : 0 < K := by rw [hK]; positivity
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  -- basic bounds
  have hKΛ1 : K * (Λ + 1) ≤ CK * a ^ 2 := by
    rw [hK]
    calc κ * CK * (Λ + 1) = CK * (κ * (Λ + 1)) := by ring
      _ ≤ CK * a ^ 2 := mul_le_mul_of_nonneg_left h1 hCK0.le
  have hKΛ : K * Λ ≤ u * a := by
    have : K * Λ ≤ K * (Λ + 1) := by nlinarith
    calc K * Λ ≤ CK * a ^ 2 := le_trans this hKΛ1
      _ = u * a := by rw [hu]; ring
  have hKle : K ≤ u * a := by
    have : K ≤ K * (Λ + 1) := by nlinarith
    calc K ≤ CK * a ^ 2 := le_trans this hKΛ1
      _ = u * a := by rw [hu]; ring
  have hua : u * a ≤ u ^ 2 := by
    rw [hu]
    have : a ≤ CK * a := by nlinarith
    nlinarith
  have hθKΛ : θ * K * Λ ≤ u ^ 2 := by
    have : θ * K * Λ ≤ K * Λ := by nlinarith [mul_nonneg hK0.le hΛ]
    linarith
  have hK2DΛ : K ^ 2 * (D : ℝ) * Λ ≤ u ^ 2 := by
    rw [hK, hu]
    have hpos : 0 ≤ κ ^ 2 * (D : ℝ) := by positivity
    have h3 : κ ^ 2 * (D : ℝ) * Λ ≤ a ^ 2 := by
      have : κ ^ 2 * (D : ℝ) * Λ ≤ κ ^ 2 * (D : ℝ) * (Λ + 1) := by nlinarith
      linarith
    calc (κ * CK) ^ 2 * (D : ℝ) * Λ = CK ^ 2 * (κ ^ 2 * (D : ℝ) * Λ) := by ring
      _ ≤ CK ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = (CK * a) ^ 2 := by ring
  have hθK2DΛ : θ * K ^ 2 * (D : ℝ) * Λ ≤ u ^ 2 := by
    have : θ * K ^ 2 * (D : ℝ) * Λ ≤ K ^ 2 * (D : ℝ) * Λ := by
      have : 0 ≤ K ^ 2 * (D : ℝ) * Λ := by positivity
      nlinarith
    linarith
  -- square-root terms
  have sq_a : ∀ c : ℝ, 0 ≤ c → ∀ s : ℝ, 0 ≤ s → 4 * c ≤ s ^ 2 →
      Real.sqrt (c * θ * K / (1 - 2 * θ) ^ 2 * Λ) ≤ s * u := by
    intro c hc s hs0 hs
    have e : c * θ * K / (1 - 2 * θ) ^ 2 * Λ = c * (θ * K * Λ) * (1 / (1 - 2 * θ) ^ 2) := by ring
    rw [e]
    exact sqrt_term c (θ * K * Λ) u (1 - 2 * θ) hc (by positivity) hθKΛ hu0 hπ0 hπ2 s hs hs0
  have sq_b : Real.sqrt (50 * θ * K ^ 2 * (D : ℝ) / (1 - 2 * θ) ^ 2 * Λ) ≤ 15 * u := by
    have e : 50 * θ * K ^ 2 * (D : ℝ) / (1 - 2 * θ) ^ 2 * Λ =
        50 * (θ * K ^ 2 * (D : ℝ) * Λ) * (1 / (1 - 2 * θ) ^ 2) := by ring
    rw [e]
    exact sqrt_term 50 _ u (1 - 2 * θ) (by norm_num) (by positivity) hθK2DΛ hu0 hπ0 hπ2 15 (by norm_num) (by norm_num)
  have lin : ∀ c : ℝ, 0 ≤ c → 2 * (c * K / (1 - 2 * θ)) * Λ ≤ 4 * c * (u * a) := by
    intro c hc
    have e : 2 * (c * K / (1 - 2 * θ)) * Λ = 2 * c * (K * Λ) * (1 / (1 - 2 * θ)) := by ring
    rw [e]
    calc 2 * c * (K * Λ) * (1 / (1 - 2 * θ)) ≤ 2 * c * (u * a) * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hKΛ (by positivity)) hπ1 (by positivity) (by positivity)
      _ = 4 * c * (u * a) := by ring
  have hua2 : u * a ≤ u / 2000 := by
    calc u * a ≤ u * (1 / 2000) := mul_le_mul_of_nonneg_left ha1 hu0
      _ = u / 2000 := by ring
  -- the key smallness of u
  have hu_small : u ≤ θ * δmax / (2000 * (R + 1)) := by
    rw [hu, ha]
    have e : CK * (θ * δmax / (2000 * (R + 1) * CK ^ 2)) = θ * δmax / (2000 * (R + 1)) / CK := by
      field_simp
    rw [e, div_le_iff₀ hCK0]
    have : 0 ≤ θ * δmax / (2000 * (R + 1)) := by positivity
    nlinarith
  have hu1 : u ≤ 1 := by
    have : θ * δmax / (2000 * (R + 1)) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  refine ⟨by linarith, ?_, ?_⟩
  · unfold lama lamw
    have t1 := sq_a 2 (by norm_num) 3 (by norm_num) (by norm_num)
    have t2 := sq_a 12 (by norm_num) 7 (by norm_num) (by norm_num)
    have l1 := lin 4 (by norm_num)
    have l2 := lin 8 (by norm_num)
    have l3 := lin 10 (by norm_num)
    have hsum : 2 * (3 * u) + 4 * 4 * (u * a) + (2 * (7 * u) + 4 * 8 * (u * a) + (2 * (15 * u) + 4 * 10 * (u * a)))
        ≤ 51 * u := by nlinarith
    have hfin : 51 * u ≤ θ * σ / 16 := by
      have h3 : θ * δmax / (2000 * (R + 1)) ≤ θ * δmax / 2000 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num); nlinarith
      have h4 : θ * δmax ≤ θ * (σ / 8) := mul_le_mul_of_nonneg_left hδσ hθ0.le
      nlinarith
    nlinarith [t1, t2, sq_b, l1, l2, l3]
  · unfold lam1
    have t1 := sq_a 8 (by norm_num) 6 (by norm_num) (by norm_num)
    have l1 := lin 4 (by norm_num)
    have hk2 : 2 * K / (1 - 2 * θ) ≤ 4 * (u * a) := by
      have e : 2 * K / (1 - 2 * θ) = 2 * K * (1 / (1 - 2 * θ)) := by ring
      rw [e]
      calc 2 * K * (1 / (1 - 2 * θ)) ≤ 2 * (u * a) * 2 :=
            mul_le_mul (by linarith) hπ1 (by positivity) (by positivity)
        _ = 4 * (u * a) := by ring
    have hε : 2 * Real.sqrt (8 * θ * K / (1 - 2 * θ) ^ 2 * Λ) + 2 * (4 * K / (1 - 2 * θ)) * Λ +
        2 * K / (1 - 2 * θ) ≤ 13 * u := by nlinarith
    have hR : R * (13 * u) ≤ δmax := by
      have h3 : R * u ≤ R * (θ * δmax / (2000 * (R + 1))) := mul_le_mul_of_nonneg_left hu_small hR0
      have h4 : R * (θ * δmax / (2000 * (R + 1))) ≤ θ * δmax / 2000 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [mul_nonneg hθ0.le hδ0.le]
      nlinarith [mul_nonneg hθ0.le hδ0.le]
    calc R * (lam1 θ K Λ + 2 * K / (1 - 2 * θ)) ≤ R * (13 * u) := by
          unfold lam1; exact mul_le_mul_of_nonneg_left (by linarith) hR0
      _ ≤ δmax := hR

variable {J Sl O : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
  [Fintype O] [DecidableEq O]

/-- real mass of a job -/
noncomputable def rmass (H : HG J Sl O) (dum : O → Prop) [DecidablePred dum] (x : O → ℝ) (e : J) : ℝ :=
  ∑ o ∈ univ.filter (fun o => H.job o = e ∧ ¬ dum o), x o

theorem mass_split (H : HG J Sl O) (dum : O → Prop) [DecidablePred dum] (x : O → ℝ) (e : J) :
    mass H x e = dmass H dum x e + rmass H dum x e := by
  unfold mass dmass rmass
  rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (fun o => H.job o = e)) dum]
  rw [Finset.filter_filter, Finset.filter_filter]

theorem lamD_le (θ Λ : ℝ) (n : ℕ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 64) (hΛ : 0 ≤ Λ) :
    lamD θ Λ n ≤ 2 * Real.sqrt (n * (Λ + 1)) + 4 * (Λ + 1) := by
  unfold lamD
  have : Real.sqrt (2 * θ * n * Λ) ≤ Real.sqrt (n * (Λ + 1)) := by
    apply Real.sqrt_le_sqrt
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg hn hΛ, mul_nonneg (mul_nonneg hθ0 hn) hΛ]
  linarith

theorem lamg_le (θ Λ : ℝ) (n : ℕ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 64) (hΛ : 0 ≤ Λ) :
    lamg θ Λ n ≤ 4 * Real.sqrt (n * (Λ + 1)) + 20 * (Λ + 1) := by
  unfold lamg
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : Real.sqrt (4 * θ * n * Λ) ≤ Real.sqrt (n * (Λ + 1)) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg hn hΛ, mul_nonneg (mul_nonneg hθ0 hn) hΛ]
  have h2 : Real.sqrt (18 * θ * n * Λ) ≤ Real.sqrt (n * (Λ + 1)) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg hn hΛ, mul_nonneg (mul_nonneg hθ0 hn) hΛ]
  linarith

theorem lamg_nonneg (θ Λ : ℝ) (n : ℕ) (hΛ : 0 ≤ Λ) : 0 ≤ lamg θ Λ n := by
  unfold lamg
  have := Real.sqrt_nonneg (4 * θ * n * Λ)
  have := Real.sqrt_nonneg (18 * θ * n * Λ)
  linarith

theorem hB2_lem (θ δmax ε : ℝ) (hθ0 : 0 < θ) (hθ2 : 2 * θ ≤ ε / 32) (hδ0 : 0 ≤ δmax) (hδ : δmax ≤ ε / 8)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    2 * θ / (θ * (1 - 2 * θ) * (1 - δmax)) ≤ 2 * (1 + ε / 16 + ε / 4) := by
  have h1 : 1 - 2 * θ - δmax ≤ (1 - 2 * θ) * (1 - δmax) := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * θ) hδ0]
  have h2 : 1 ≤ (1 + ε / 16 + ε / 4) * ((1 - 2 * θ) * (1 - δmax)) := by
    have h3 : 1 - 5 * ε / 32 ≤ (1 - 2 * θ) * (1 - δmax) := by linarith
    have h4 : 1 ≤ (1 + ε / 16 + ε / 4) * (1 - 5 * ε / 32) := by nlinarith
    have h5 : 0 ≤ 1 - 5 * ε / 32 := by linarith
    nlinarith
  have hpos : 0 < (1 - 2 * θ) * (1 - δmax) := by nlinarith
  have hpos2 : 0 < θ * (1 - 2 * θ) * (1 - δmax) := by rw [mul_assoc]; exact mul_pos hθ0 hpos
  rw [div_le_iff₀ hpos2]
  nlinarith [mul_le_mul_of_nonneg_left h2 hθ0.le]

theorem final_comb (L A B C W X ε c T : ℝ) (hF : L ≤ A * W + B * (X / 2) + C) (hA : A ≤ ε / 4)
    (hB0 : 0 ≤ B) (hB : B ≤ 2 * (1 + ε / 16 + ε / 4)) (hX0 : 0 ≤ X) (hXW : X ≤ W) (hW0 : 0 ≤ W)
    (hε0 : 0 ≤ ε) (hC : C ≤ c * T) : L ≤ X + ε * W + c * T := by
  have h1 : A * W ≤ ε / 4 * W := mul_le_mul_of_nonneg_right hA hW0
  have h2 : B * (X / 2) ≤ 2 * (1 + ε / 16 + ε / 4) * (X / 2) := mul_le_mul_of_nonneg_right hB (by linarith)
  have h3 : (ε / 16 + ε / 4) * X ≤ (ε / 16 + ε / 4) * W := mul_le_mul_of_nonneg_left hXW (by linarith)
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **local almost-perfect matching** (internal form) -/
theorem lapm_int (σ ε : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ {J Sl O G : Type} [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
      [Fintype O] [DecidableEq O] [Fintype G] [DecidableEq G] (H : HG J Sl O) (dum : O → Prop)
      [DecidablePred dum] (memb : G → Finset J) (w : J → ℝ) (x : O → ℝ) (κ : ℝ) (D : ℕ),
      (∀ o, (H.sl o).card ≤ 2) → Priv H dum → (∀ e, 0 ≤ w e ∧ w e ≤ 1) → (∀ o, 0 ≤ x o) →
      (∀ e, mass H x e = 1) → (∀ s, load H x s ≤ 1 - σ) → (∀ e t, yw H x e t ≤ κ) →
      (∀ s t, s ≠ t → kw H x s t ≤ κ) → 0 < κ → 1 ≤ D →
      (∀ e, (Nb H e).card ≤ D) → (∀ s, (As H s).card ≤ D) →
      (∀ e, (univ.filter (fun s => e ∈ As H s)).card ≤ D) →
      (∀ g, (memb g).card ≤ D) → (∀ e, (univ.filter (fun g => e ∈ memb g)).card ≤ D) →
      κ * (Real.log (5 * Real.exp 1 * ((3 * D ^ 4 : ℕ) + 1)) + 1) ≤ c₁ →
      κ ^ 2 * (D : ℝ) * (Real.log (5 * Real.exp 1 * ((3 * D ^ 4 : ℕ) + 1)) + 1) ≤ c₁ →
      ∃ M : Finset O, (∀ o ∈ M, 0 < x o) ∧
        (∀ o ∈ M, ∀ o' ∈ M, o ≠ o' → H.job o ≠ H.job o' ∧ Disjoint (H.sl o) (H.sl o')) ∧
        ∀ g, ∑ e ∈ memb g, w e * (@ite ℝ (∃ m ∈ M, H.job m = e ∧ ¬ dum m) (Classical.propDecidable _) 0 1) ≤
          ∑ e ∈ memb g, w e * (1 - rmass H dum x e) + ε * ∑ e ∈ memb g, w e +
            c₂ * (Real.sqrt ((memb g).card * (Real.log (5 * Real.exp 1 * ((3 * D ^ 4 : ℕ) + 1)) + 1)) +
              (Real.log (5 * Real.exp 1 * ((3 * D ^ 4 : ℕ) + 1)) + 1)) := by
  set η := min σ ε with hη
  have hη0 : 0 < η := lt_min hσ0 hε0
  have hησ : η ≤ σ := min_le_left _ _
  have hηε : η ≤ ε := min_le_right _ _
  have hη1 : η ≤ 1 := le_trans hηε hε1
  set θ := η / 64 with hθ
  set δmax := η / 8 with hδmax
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 64 := by rw [hθ]; linarith
  have hπ0 : 0 < 1 - 2 * θ := by linarith
  set ρ₀ := θ * (1 - 2 * θ) * (1 - δmax) with hρ₀
  have hδ1 : δmax ≤ 1 / 8 := by rw [hδmax]; linarith
  have hfac : 1 / 2 ≤ (1 - 2 * θ) * (1 - δmax) := by nlinarith
  have hρ₀0 : 0 < ρ₀ := by
    rw [hρ₀]
    have : 0 < 1 - δmax := by linarith
    positivity
  have hρ₀half : θ / 2 ≤ ρ₀ := by rw [hρ₀]; nlinarith
  have hρ₀1 : ρ₀ ≤ 1 := by rw [hρ₀]; nlinarith [mul_pos hθ0 hπ0]
  set R : ℕ := ⌈(2 / θ) * Real.log (4 / ε)⌉₊ with hR
  set CK : ℝ := (1 / (1 - 2 * θ)) ^ R with hCK
  have hCK1 : 1 ≤ CK := one_le_pow₀ (by rw [le_div_iff₀ hπ0]; linarith)
  set a := θ * δmax / (2000 * ((R : ℝ) + 1) * CK ^ 2) with ha
  refine ⟨a ^ 2, 84 * R, by positivity, ?_⟩
  intro J Sl O G _ _ _ _ _ _ _ _ H dum _ memb w x κ D hsl hP hw hx0 hmass hload hc1 hc2 hκ0 hD1 hNb hAs hse hmemb hge hs1 hs2
  set Λ := Real.log (5 * Real.exp 1 * ((3 * D ^ 4 : ℕ) + 1)) with hΛdef
  have hΛ : 0 ≤ Λ := by
    apply Real.log_nonneg
    have : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have : (1 : ℝ) ≤ (3 * D ^ 4 : ℕ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (3 * D ^ 4)]
    nlinarith
  set K := κ * CK with hK
  obtain ⟨hK1, hlamK, hRε⟩ := param_arith θ σ δmax K Λ κ CK R a D hθ0 hθ1 hσ0 (by positivity)
    (by rw [hδmax]; linarith) hδ1 hCK1 (Nat.cast_nonneg R) rfl rfl hκ0 hΛ hD1 hs1 hs2
  have hepd : Real.exp 1 * (5 * Real.exp (-Λ)) * ((3 * D ^ 4 : ℕ) + 1) ≤ 1 := by
    rw [Real.exp_neg, hΛdef, Real.exp_log (by positivity)]
    apply le_of_eq
    field_simp
  have hI : Inv H σ 0 κ x := ⟨hx0, fun e => Or.inr ⟨by rw [hmass e]; norm_num, by rw [hmass e]; norm_num⟩,
    fun s => by linarith [hload s], hc1, hc2⟩
  obtain ⟨M, hMx, hMm, hMF⟩ := iterate (hsl) dum hP memb w hw θ σ Λ δmax K hθ0 (by rw [hθ]; linarith) hσ0 hσ1
    (by positivity) (by rw [hδmax]; linarith) (by positivity) hK1 D hD1 hNb hAs hse hmemb hge hΛ hepd hlamK R
    0 κ x hI le_rfl (by linarith) hκ0 (by
      rw [hK, hCK, mul_assoc, ← mul_pow]
      rw [one_div_mul_cancel hπ0.ne', one_pow, mul_one])
  refine ⟨M, hMx, hMm, fun g => ?_⟩
  have hF := hMF g
  -- rewrite the pieces
  have hFail : Fail H dum (memb g) w x M =
      ∑ e ∈ memb g, w e * (@ite ℝ (∃ m ∈ M, H.job m = e ∧ ¬ dum m) (Classical.propDecidable _) 0 1) := by
    unfold Fail
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [if_neg (by rw [hmass e]; norm_num)]; ring
  have hWa : Wa H (memb g) w x = ∑ e ∈ memb g, w e := by
    unfold Wa
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [if_neg (by rw [hmass e]; norm_num)]; ring
  have hWd : Wd H dum (memb g) w x = (∑ e ∈ memb g, w e * (1 - rmass H dum x e)) / 2 := by
    unfold Wd c2
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    have := mass_split H dum x e
    rw [hmass e] at this
    rw [show dmass H dum x e = 1 - rmass H dum x e by linarith]
  have hr1 : ∀ e, rmass H dum x e ≤ 1 := by
    intro e
    have := mass_split H dum x e
    rw [hmass e] at this
    have : 0 ≤ dmass H dum x e := Finset.sum_nonneg (fun o _ => hx0 o)
    linarith
  have hW1 : 0 ≤ ∑ e ∈ memb g, w e * (1 - rmass H dum x e) :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (hw e).1 (by linarith [hr1 e]))
  have hW1' : ∑ e ∈ memb g, w e * (1 - rmass H dum x e) ≤ ∑ e ∈ memb g, w e := by
    refine Finset.sum_le_sum (fun e _ => ?_)
    have : 0 ≤ rmass H dum x e := Finset.sum_nonneg (fun o _ => hx0 o)
    nlinarith [(hw e).1]
  have hW0 : 0 ≤ ∑ e ∈ memb g, w e := Finset.sum_nonneg (fun e _ => (hw e).1)
  -- coefficient bounds
  have hA : cA ρ₀ R ≤ ε / 4 := by
    refine le_trans (cA_le_exp ρ₀ hρ₀0.le hρ₀1 R) ?_
    have hR' : (2 / θ) * Real.log (4 / ε) ≤ R := Nat.le_ceil _
    have hlog : 0 ≤ Real.log (4 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε0]; linarith)
    have h1 : Real.log (4 / ε) ≤ ρ₀ * R := by
      have : Real.log (4 / ε) = θ / 2 * ((2 / θ) * Real.log (4 / ε)) := by field_simp
      rw [this]
      exact mul_le_mul hρ₀half hR' (by positivity) hρ₀0.le
    calc Real.exp (-(ρ₀ * R)) ≤ Real.exp (-(Real.log (4 / ε))) := Real.exp_le_exp.mpr (by linarith)
      _ = ε / 4 := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have hB : cB θ ρ₀ R ≤ 2 * θ / ρ₀ := cB_le θ ρ₀ hθ0.le hρ₀0 hρ₀1 R
  have hB2 : 2 * θ / ρ₀ ≤ 2 * (1 + ε / 16 + ε / 4) :=
    hB2_lem θ δmax ε hθ0 (by rw [hθ]; linarith) (by positivity) (by rw [hδmax]; linarith) hε0 hε1
  have hC : cC θ ρ₀ Λ (memb g).card R ≤ R * (84 * (Real.sqrt ((memb g).card * (Λ + 1)) + (Λ + 1))) := by
    apply cC_le θ ρ₀ Λ hθ0.le hρ₀0 hρ₀1 _ _ _ (lamg_nonneg θ Λ _ hΛ)
    have h1 := lamD_le θ Λ (memb g).card hθ0.le hθ1 hΛ
    have h2 := lamg_le θ Λ (memb g).card hθ0.le hθ1 hΛ
    have h3 : 1 + 2 * θ / ρ₀ ≤ 4 := by nlinarith
    have h4 := lamg_nonneg θ Λ (memb g).card hΛ
    have hs0 := Real.sqrt_nonneg ((memb g).card * (Λ + 1))
    nlinarith [mul_le_mul_of_nonneg_right h3 h4]
  rw [hFail, hWa, hWd] at hF
  have hB0 := cB_nonneg θ ρ₀ hθ0.le hρ₀1 R
  have hCe : cC θ ρ₀ Λ (memb g).card R ≤ 84 * R * (Real.sqrt ((memb g).card * (Λ + 1)) + (Λ + 1)) := by
    have : R * (84 * (Real.sqrt ((memb g).card * (Λ + 1)) + (Λ + 1))) =
        84 * R * (Real.sqrt ((memb g).card * (Λ + 1)) + (Λ + 1)) := by ring
    linarith
  exact final_comb _ _ _ _ _ _ ε _ _ hF hA hB0 (le_trans hB hB2) hW1 hW1' hW0 hε0.le hCe

end Nib

end SecFinal

section SecPlatform

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Finset

namespace Nib

theorem Lam_le (D : ℕ) (hD : 1 ≤ D) :
    Real.log (5 * Real.exp 1 * ((3 * D ^ 4 : ℕ) + 1)) + 1 ≤ 21 * (Real.log D + 1) := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hlD : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg hD1
  have h4 : (((3 * D ^ 4 : ℕ) : ℝ) + 1) ≤ 4 * (D : ℝ) ^ 4 := by
    push_cast
    have : (1 : ℝ) ≤ (D : ℝ) ^ 4 := one_le_pow₀ hD1
    linarith
  have hpos : (0 : ℝ) < 5 * Real.exp 1 * ((3 * D ^ 4 : ℕ) + 1) := by positivity
  have hle : Real.log (5 * Real.exp 1 * ((3 * D ^ 4 : ℕ) + 1)) ≤ Real.log (20 * Real.exp 1 * (D : ℝ) ^ 4) := by
    apply Real.log_le_log hpos
    have := Real.exp_pos 1
    nlinarith
  have hsplit : Real.log (20 * Real.exp 1 * (D : ℝ) ^ 4) = Real.log 20 + 1 + 4 * Real.log D := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_exp, Real.log_pow]
    push_cast; ring
  have h20 : Real.log 20 ≤ 19 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 20 by norm_num); linarith
  linarith

end Nib

open Finset in
/-- Platform statement: local almost-perfect matching via the nibble. -/
theorem solution (σ ε : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧
      ∀ (J Sl O G : Type) [Fintype J] [DecidableEq J] [Fintype Sl] [DecidableEq Sl]
        [Fintype O] [DecidableEq O] [Fintype G] [DecidableEq G]
        (job : O → J) (sl : O → Finset Sl) (dum : O → Prop) [DecidablePred dum]
        (memb : G → Finset J) (w : J → ℝ) (x : O → ℝ) (κ : ℝ) (D : ℕ),
        (∀ o, (sl o).card ≤ 2) →
        (∀ o, dum o → ∀ o', o' ≠ o → Disjoint (sl o) (sl o')) →
        (∀ e, 0 ≤ w e ∧ w e ≤ 1) → (∀ o, 0 ≤ x o) →
        (∀ e, ∑ o ∈ univ.filter (fun o => job o = e), x o = 1) →
        (∀ s, ∑ o ∈ univ.filter (fun o => s ∈ sl o), x o ≤ 1 - σ) →
        (∀ e t, ∑ o ∈ univ.filter (fun o => job o = e ∧ t ∈ sl o), x o ≤ κ) →
        (∀ s t, s ≠ t → ∑ o ∈ univ.filter (fun o => s ∈ sl o ∧ t ∈ sl o), x o ≤ κ) →
        0 < κ → 1 ≤ D →
        (∀ e, (insert e (univ.filter (fun f => ∃ o o', job o = e ∧ job o' = f ∧
            ¬ Disjoint (sl o) (sl o')))).card ≤ D) →
        (∀ s, (univ.filter (fun e => ∃ o, job o = e ∧ s ∈ sl o)).card ≤ D) →
        (∀ e, (univ.filter (fun s => ∃ o, job o = e ∧ s ∈ sl o)).card ≤ D) →
        (∀ g, (memb g).card ≤ D) →
        (∀ e, (univ.filter (fun g => e ∈ memb g)).card ≤ D) →
        κ * (Real.log D + 1) ≤ c₁ →
        κ ^ 2 * D * (Real.log D + 1) ≤ c₁ →
        ∃ M : Finset O, (∀ o ∈ M, 0 < x o) ∧
          (∀ o ∈ M, ∀ o' ∈ M, o ≠ o' → job o ≠ job o' ∧ Disjoint (sl o) (sl o')) ∧
          ∀ g, ∑ e ∈ memb g, w e * (if ∃ m ∈ M, job m = e ∧ ¬ dum m then 0 else 1) ≤
            ∑ e ∈ memb g, w e * (1 - ∑ o ∈ univ.filter (fun o => job o = e ∧ ¬ dum o), x o) +
              ε * ∑ e ∈ memb g, w e +
              c₂ * (Real.sqrt ((memb g).card * (Real.log D + 1)) + (Real.log D + 1)) := by
  obtain ⟨c₁, c₂, hc₁, hmain⟩ := Nib.lapm_int σ ε hσ0 hσ1 hε0 hε1
  refine ⟨c₁ / 21, 21 * max c₂ 0, by positivity, ?_⟩
  intro J Sl O G _ _ _ _ _ _ _ _ job sl dum _ memb w x κ D hsl hP hw hx0 hmass hload hc1 hc2 hκ hD
    hNb hAs hse hmemb hge hs1 hs2
  let H : Nib.HG J Sl O := ⟨job, sl⟩
  have hL := Nib.Lam_le D hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlD : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg hD1
  set L := Real.log (D : ℝ) + 1 with hLdef
  set Λ1 := Real.log (5 * Real.exp 1 * ((3 * D ^ 4 : ℕ) + 1)) + 1 with hΛ1
  have hLpos : 0 < L := by linarith
  have hNb' : ∀ e, (Nib.Nb H e).card ≤ D := by
    intro e
    have : Nib.Nb H e = insert e (univ.filter (fun f => ∃ o o', job o = e ∧ job o' = f ∧
        ¬ Disjoint (sl o) (sl o'))) := by
      ext f; rw [Nib.mem_Nb]; simp [H]
    rw [this]; exact hNb e
  have hse' : ∀ e, (univ.filter (fun s => e ∈ Nib.As H s)).card ≤ D := by
    intro e
    have : univ.filter (fun s => e ∈ Nib.As H s) = univ.filter (fun s => ∃ o, job o = e ∧ s ∈ sl o) := by
      ext s; simp [Nib.As, H]
    rw [this]; exact hse e
  have hκ0 := hκ.le
  have h1 : κ * Λ1 ≤ c₁ := by
    calc κ * Λ1 ≤ κ * (21 * L) := mul_le_mul_of_nonneg_left hL hκ0
      _ = 21 * (κ * L) := by ring
      _ ≤ 21 * (c₁ / 21) := by linarith
      _ = c₁ := by ring
  have h2 : κ ^ 2 * D * Λ1 ≤ c₁ := by
    have hk2 : 0 ≤ κ ^ 2 * (D : ℝ) := by positivity
    calc κ ^ 2 * D * Λ1 ≤ κ ^ 2 * D * (21 * L) := mul_le_mul_of_nonneg_left hL hk2
      _ = 21 * (κ ^ 2 * D * L) := by ring
      _ ≤ 21 * (c₁ / 21) := by linarith
      _ = c₁ := by ring
  obtain ⟨M, hM1, hM2, hM3⟩ := hmain H dum memb w x κ D hsl hP hw hx0 hmass hload hc1 hc2 hκ hD
    hNb' hAs hse' hmemb hge h1 h2
  refine ⟨M, hM1, hM2, fun g => ?_⟩
  have h3 := hM3 g
  have hite : ∀ e, (@ite ℝ (∃ m ∈ M, H.job m = e ∧ ¬ dum m) (Classical.propDecidable _) 0 1) =
      (if ∃ m ∈ M, job m = e ∧ ¬ dum m then 0 else 1) := by
    intro e
    by_cases h : ∃ m ∈ M, job m = e ∧ ¬ dum m
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  simp only [hite] at h3
  have hm0 : (0 : ℝ) ≤ (memb g).card := Nat.cast_nonneg _
  have hsq : Real.sqrt ((memb g).card * Λ1) ≤ 21 * Real.sqrt ((memb g).card * L) := by
    have hΛ0 : 0 ≤ Λ1 := by
      have : (1 : ℝ) ≤ 5 * Real.exp 1 * ((3 * D ^ 4 : ℕ) + 1) := by
        have : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have : (1 : ℝ) ≤ (3 * D ^ 4 : ℕ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (3 * D ^ 4)]
        nlinarith
      have := Real.log_nonneg this; linarith
    calc Real.sqrt ((memb g).card * Λ1) ≤ Real.sqrt ((memb g).card * (21 * L)) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hL hm0)
      _ = Real.sqrt 21 * Real.sqrt ((memb g).card * L) := by
          rw [← Real.sqrt_mul (by norm_num)]; ring_nf
      _ ≤ 21 * Real.sqrt ((memb g).card * L) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hX : 0 ≤ Real.sqrt ((memb g).card * Λ1) + Λ1 := by
    have : 0 ≤ Λ1 := by
      have : (1 : ℝ) ≤ 5 * Real.exp 1 * ((3 * D ^ 4 : ℕ) + 1) := by
        have : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have : (1 : ℝ) ≤ (3 * D ^ 4 : ℕ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (3 * D ^ 4)]
        nlinarith
      have := Real.log_nonneg this; linarith
    positivity
  have herr : c₂ * (Real.sqrt ((memb g).card * Λ1) + Λ1) ≤
      21 * max c₂ 0 * (Real.sqrt ((memb g).card * L) + L) := by
    calc c₂ * (Real.sqrt ((memb g).card * Λ1) + Λ1) ≤ max c₂ 0 * (Real.sqrt ((memb g).card * Λ1) + Λ1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hX
      _ ≤ max c₂ 0 * (21 * Real.sqrt ((memb g).card * L) + 21 * L) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
      _ = 21 * max c₂ 0 * (Real.sqrt ((memb g).card * L) + L) := by ring
  have hr : ∀ e, Nib.rmass H dum x e = ∑ o ∈ univ.filter (fun o => job o = e ∧ ¬ dum o), x o := fun e => rfl
  simp only [hr] at h3
  linarith

end SecPlatform
