-- Prove2me | solution 1 for KSATSingleFlip.Connect.glauber_uniform_stationary
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:27:56.272086+00:00
-- url     : https://prove2.me/submissions/871f5c08-3a58-44ea-aaed-96e1a869e375

import Definitions.Def_KSATSingleFlip_Connect_Glauber



open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- The planted assignment satisfies the subformula retained by satIdx. -/
theorem audit_satIdx_satisfies {n : ℕ} (Φ : GFormula (Fin n)) (z : Fin n → Bool) :
    z ∈ sols (subF Φ (satIdx Φ z)) := by
  simp only [sols, Finset.mem_filter, Finset.mem_univ, true_and]
  change FSat z (subF Φ (satIdx Φ z))
  intro C hC
  unfold subF at hC
  obtain ⟨c, _, hc⟩ := List.mem_filterMap.mp hC
  split at hc
  next h =>
    have hsat : ClauseSat z (Φ.get c) := (Finset.mem_filter.mp h).2
    cases hc
    exact hsat
  next _ => simp at hc

/-- A Glauber update preserves satisfiability. -/
theorem audit_glauber_step_preserves {n : ℕ} (Φ : GFormula (Fin n)) (x : Fin n → Bool)
    (u : Fin n × Bool) (hx : FSat x Φ) : FSat (glauberStep Φ x u) Φ := by
  unfold glauberStep
  split
  next h => exact h
  next _ =>
    split
    next h => exact h
    next _ => exact hx

/-- The planted-subformula Glauber chain remains satisfying at every time. -/
theorem audit_glauber_planted_satisfies {n t : ℕ} (Φ : GFormula (Fin n))
    (z : Fin n → Bool) (s : Fin t → Fin n × Bool) :
    glauberState (subF Φ (satIdx Φ z)) z s ∈ sols (subF Φ (satIdx Φ z)) := by
  simp only [sols, Finset.mem_filter, Finset.mem_univ, true_and]
  change FSat (glauberRun (subF Φ (satIdx Φ z)) z (List.ofFn s)) (subF Φ (satIdx Φ z))
  have hg : ∀ (seq : List (Fin n × Bool)) x,
      FSat x (subF Φ (satIdx Φ z)) →
      FSat (glauberRun (subF Φ (satIdx Φ z)) x seq) (subF Φ (satIdx Φ z)) := by
    intro seq
    induction seq with
    | nil => intro x hx; exact hx
    | cons u seq ih =>
      intro x hx
      apply ih
      exact audit_glauber_step_preserves _ x u hx
  apply hg
  simpa [sols] using audit_satIdx_satisfies Φ z

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- A symmetric finite transition kernel has uniform column sums. This is the
finite counting form of detailed balance used for Glauber stationarity. -/
theorem audit_symmetric_transition_columns {Ω U : Type} [Fintype Ω] [Fintype U]
    (step : Ω → U → Ω)
    (hsym : ∀ x y, (∑ u, if step x u = y then (1 : ℝ) else 0) =
      ∑ u, if step y u = x then (1 : ℝ) else 0) (y : Ω) :
    (∑ x, ∑ u, if step x u = y then (1 : ℝ) else 0) = Fintype.card U := by
  classical
  calc
    _ = ∑ x, ∑ u, if step y u = x then (1 : ℝ) else 0 := Finset.sum_congr rfl (fun x _ => hsym x y)
    _ = ∑ u, ∑ x, if step y u = x then (1 : ℝ) else 0 := Finset.sum_comm
    _ = Fintype.card U := by simp

/-- A symmetric finite transition kernel preserves the uniform distribution. -/
theorem audit_uniform_stationary_of_symmetric {Ω U : Type} [Fintype Ω] [Fintype U] [Nonempty U]
    (step : Ω → U → Ω)
    (hsym : ∀ x y, (∑ u, if step x u = y then (1 : ℝ) else 0) =
      ∑ u, if step y u = x then (1 : ℝ) else 0) (f : Ω → ℝ) :
    uexp (fun x => uexp (fun u => f (step x u))) = uexp f := by
  classical
  have hU : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ x, ∑ u, f (step x u)) = (Fintype.card U : ℝ) * ∑ y, f y := by
    calc
      _ = ∑ x, ∑ u, ∑ y, if step x u = y then f y else 0 := by simp
      _ = ∑ x, ∑ y, ∑ u, if step x u = y then f y else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
      _ = ∑ y, ∑ x, ∑ u, if step x u = y then f y else 0 := Finset.sum_comm
      _ = ∑ y, (∑ x, ∑ u, if step x u = y then (1 : ℝ) else 0) * f y := by
        apply Finset.sum_congr rfl
        intro y _
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro u _
        split <;> simp_all
      _ = ∑ y, (Fintype.card U : ℝ) * f y := by
        apply Finset.sum_congr rfl
        intro y _
        rw [audit_symmetric_transition_columns step hsym y]
      _ = (Fintype.card U : ℝ) * ∑ y, f y := by rw [Finset.mul_sum]
  unfold uexp
  rw [← Finset.sum_div, hsum]
  field_simp

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

private theorem audit_update_eq_iff {n : ℕ} (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ i, i ≠ v → x i = y i) (b : Bool) :
    Function.update x v b = y ↔ b = y v := by
  constructor
  · intro h
    have hh := congrFun h v
    simpa using hh
  · intro h
    subst b
    funext i
    by_cases hi : i = v
    · subst i; simp
    · rw [Function.update_of_ne hi]
      exact hxy i hi

private theorem audit_glauber_off_coordinate {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (v i : Fin n) (b : Bool) (h : i ≠ v) :
    glauberStep Φ x (v, b) i = x i := by
  unfold glauberStep
  split
  · exact Function.update_of_ne h _ _
  · split
    · exact Function.update_of_ne h _ _
    · rfl

/-- Detailed balance for a fixed coordinate of the satisfying Glauber chain. -/
theorem audit_glauber_coordinate_symmetric {n : ℕ} (Φ : GFormula (Fin n))
    (x y : Fin n → Bool) (v : Fin n) (hx : FSat x Φ) (hy : FSat y Φ) :
    (∑ b : Bool, if glauberStep Φ x (v, b) = y then (1 : ℝ) else 0) =
      ∑ b : Bool, if glauberStep Φ y (v, b) = x then (1 : ℝ) else 0 := by
  classical
  by_cases heq : x = y
  · subst y; rfl
  · by_cases hxy : ∀ i, i ≠ v → x i = y i
    · have hbits : x v ≠ y v := by
        intro hb
        apply heq
        funext i
        by_cases hi : i = v
        · subst i; exact hb
        · exact hxy i hi
      have hupdateX : ∀ b, FSat (Function.update x v b) Φ := by
        intro b
        by_cases hb : b = x v
        · rw [hb, Function.update_eq_self]; exact hx
        · have hby : b = y v := by
            cases hxb : x v <;> cases hyb : y v <;> cases b <;> simp_all
          rw [(audit_update_eq_iff x y v hxy b).mpr hby]
          exact hy
      have hyx : ∀ i, i ≠ v → y i = x i := fun i hi => (hxy i hi).symm
      have hupdateY : ∀ b, FSat (Function.update y v b) Φ := by
        intro b
        by_cases hb : b = y v
        · rw [hb, Function.update_eq_self]; exact hy
        · have hbx : b = x v := by
            cases hxb : x v <;> cases hyb : y v <;> cases b <;> simp_all
          rw [(audit_update_eq_iff y x v hyx b).mpr hbx]
          exact hx
      have hxstep : ∀ b, glauberStep Φ x (v, b) = Function.update x v b := by
        intro b
        simp [glauberStep, hupdateX b]
      have hystep : ∀ b, glauberStep Φ y (v, b) = Function.update y v b := by
        intro b
        simp [glauberStep, hupdateY b]
      simp only [hxstep, hystep, audit_update_eq_iff x y v hxy, audit_update_eq_iff y x v hyx]
      rw [Fintype.sum_bool, Fintype.sum_bool]
      cases hxv : x v <;> cases hyv : y v <;> simp [hxv, hyv]
    · push_neg at hxy
      obtain ⟨i, hi, hdiff⟩ := hxy
      have hnone1 : ∀ b, glauberStep Φ x (v, b) ≠ y := by
        intro b h
        have hh := audit_glauber_off_coordinate Φ x v i b hi
        have he := congrFun h i
        exact hdiff (hh.symm.trans he)
      have hnone2 : ∀ b, glauberStep Φ y (v, b) ≠ x := by
        intro b h
        have hh := audit_glauber_off_coordinate Φ y v i b hi
        have he := congrFun h i
        exact hdiff (he.symm.trans hh)
      simp [hnone1, hnone2]

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Glauber update as a map on the finite solution type. -/
noncomputable def audit_solution_update {n : ℕ} (Φ : GFormula (Fin n))
    (x : ↥(sols Φ)) (u : Fin n × Bool) : ↥(sols Φ) :=
  ⟨glauberStep Φ x.1 u, by
    have hx : FSat x.1 Φ := by simpa [sols] using x.2
    simpa [sols] using audit_glauber_step_preserves Φ x.1 u hx⟩

/-- The solution-space transition has a symmetric counting kernel. -/
theorem audit_solution_update_symmetric {n : ℕ} (Φ : GFormula (Fin n))
    (x y : ↥(sols Φ)) :
    (∑ u : Fin n × Bool, if audit_solution_update Φ x u = y then (1 : ℝ) else 0) =
      ∑ u : Fin n × Bool, if audit_solution_update Φ y u = x then (1 : ℝ) else 0 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  have hx : FSat x.1 Φ := by simpa [sols] using x.2
  have hy : FSat y.1 Φ := by simpa [sols] using y.2
  simpa only [audit_solution_update, Subtype.ext_iff] using
    audit_glauber_coordinate_symmetric Φ x.1 y.1 v hx hy

/-- For n > 0, a uniform solution remains uniform after one Glauber step. -/
theorem audit_glauber_uniform_stationary {n : ℕ} (hn : 0 < n)
    (Φ : GFormula (Fin n)) (f : ↥(sols Φ) → ℝ) :
    uexp (fun x : ↥(sols Φ) => uexp (fun u : Fin n × Bool => f (audit_solution_update Φ x u))) =
      uexp f := by
  letI : Nonempty (Fin n × Bool) := ⟨(⟨0, hn⟩, false)⟩
  apply audit_uniform_stationary_of_symmetric (audit_solution_update Φ) _ f
  intro x y
  convert audit_solution_update_symmetric Φ x y using 1 <;>
    apply Finset.sum_congr rfl <;> intro u hu <;> split_ifs <;> simp_all

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- An update sequence of length t, written recursively from its first update. -/
def audit_iter {Ω U : Type} (step : Ω → U → Ω) : ∀ t : ℕ, Ω → (Fin t → U) → Ω
  | 0, x, _ => x
  | t + 1, x, s => audit_iter step t (step x (s 0)) (fun i => s i.succ)

private def audit_fin_cons_equiv {U : Type} (t : ℕ) : (Fin (t + 1) → U) ≃ U × (Fin t → U) where
  toFun s := (s 0, fun i => s i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv s := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv p := by cases p; rfl

/-- Splitting a uniform update sequence into its first update and its tail. -/
theorem audit_uexp_fin_succ {U : Type} [Fintype U] (t : ℕ) (f : (Fin (t + 1) → U) → ℝ) :
    uexp f = uexp (fun u : U => uexp (fun s : Fin t → U => f (Fin.cons u s))) := by
  classical
  let e := audit_fin_cons_equiv (U := U) t
  have hsum : (∑ s : Fin (t + 1) → U, f s) = ∑ p : U × (Fin t → U), f (Fin.cons p.1 p.2) := by
    symm
    exact e.symm.sum_comp f
  have hcard : Fintype.card (Fin (t + 1) → U) = Fintype.card U * Fintype.card (Fin t → U) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr e
  unfold uexp
  rw [hsum, hcard, Fintype.sum_prod_type]
  push_cast
  rw [← Finset.sum_div]
  ring

/-- Iterating a uniform-stationary finite kernel preserves the uniform law. -/
theorem audit_uniform_stationary_iter {Ω U : Type} [Fintype Ω] [Fintype U] [Nonempty U]
    (step : Ω → U → Ω)
    (hsym : ∀ x y, (∑ u, if step x u = y then (1 : ℝ) else 0) =
      ∑ u, if step y u = x then (1 : ℝ) else 0) (f : Ω → ℝ) (t : ℕ) :
    uexp (fun x : Ω => uexp (fun s : Fin t → U => f (audit_iter step t x s))) = uexp f := by
  induction t with
  | zero =>
    have hseq : ∀ x : Ω, uexp (fun s : Fin 0 → U => f (audit_iter step 0 x s)) = f x := by
      intro x
      simp [uexp, audit_iter]
    simpa only [hseq] 
  | succ t ih =>
    have hsplit : ∀ x : Ω,
        uexp (fun s : Fin (t + 1) → U => f (audit_iter step (t + 1) x s)) =
          uexp (fun u : U => uexp (fun s : Fin t → U => f (audit_iter step t (step x u) s))) := by
      intro x
      rw [audit_uexp_fin_succ]
      congr 2
    simp only [hsplit]
    let g : Ω → ℝ := fun x => uexp (fun s : Fin t → U => f (audit_iter step t x s))
    change uexp (fun x : Ω => uexp (fun u : U => g (step x u))) = uexp f
    rw [audit_uniform_stationary_of_symmetric step hsym g]
    exact ih

/-- Projecting the solution-valued iterated chain gives the paper's Glauber state. -/
theorem audit_iter_glauber_state {n t : ℕ} (Φ : GFormula (Fin n))
    (x : ↥(sols Φ)) (s : Fin t → Fin n × Bool) :
    (audit_iter (audit_solution_update Φ) t x s).1 = glauberState Φ x.1 s := by
  induction t generalizing x with
  | zero => simp [audit_iter, glauberState, glauberRun, List.ofFn_zero]
  | succ t ih =>
    rw [glauberState, List.ofFn_succ]
    change (audit_iter (audit_solution_update Φ) t (audit_solution_update Φ x (s 0))
        (fun i => s i.succ)).1 =
      glauberRun Φ (glauberStep Φ x.1 (s 0)) (List.ofFn fun i => s i.succ)
    simpa [glauberState, audit_solution_update] using ih (audit_solution_update Φ x (s 0))
      (fun i => s i.succ)

/-- Uniformity of a satisfying initial assignment is preserved after any fixed
number of independent uniformly chosen Glauber updates. -/
theorem audit_glauber_uniform_stationary_iter {n : ℕ} (hn : 0 < n)
    (Φ : GFormula (Fin n)) (f : (Fin n → Bool) → ℝ) (t : ℕ) :
    uexp (fun x : ↥(sols Φ) => uexp (fun s : Fin t → Fin n × Bool =>
      f (glauberState Φ x.1 s))) = uexp (fun x : ↥(sols Φ) => f x.1) := by
  classical
  letI : Nonempty (Fin n × Bool) := ⟨(⟨0, hn⟩, false)⟩
  have h := audit_uniform_stationary_iter (audit_solution_update Φ) (by
    intro x y
    convert audit_solution_update_symmetric Φ x y using 1 <;>
      apply Finset.sum_congr rfl <;> intro u hu <;> split_ifs <;> simp_all)
    (fun x => f x.1) t
  simpa only [audit_iter_glauber_state] using h

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

/-- A uniform satisfying assignment remains uniform after any number of Glauber steps. -/
theorem solution {n : ℕ} (hn : 0 < n)
    (Φ : GFormula (Fin n)) (f : (Fin n → Bool) → ℝ) (t : ℕ) :
    uexp (fun x : ↥(sols Φ) => uexp (fun s : Fin t → Fin n × Bool =>
      f (glauberState Φ x.1 s))) = uexp (fun x : ↥(sols Φ) => f x.1) := by
  exact audit_glauber_uniform_stationary_iter hn Φ f t

#print axioms solution
