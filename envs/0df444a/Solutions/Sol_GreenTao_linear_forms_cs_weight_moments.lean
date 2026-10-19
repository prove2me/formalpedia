-- Prove2me | solution 1 for GreenTao.linear_forms_cs_weight_moments
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:31:13.428993+00:00
-- url     : https://prove2.me/submissions/91b56ed1-f31f-4245-bfa4-dd7ffa6d74ed

import Theorems.Thm_GreenTao_linear_forms_finite_indices
import Theorems.Thm_GreenTao_cs_coefficients
import Mathlib

open scoped BigOperators Topology
open Filter GreenTao

private abbrev CubeFace (d : ℕ) := Σ i : Fin d, {ω : Fin d → Bool // ω i = false}
private abbrev MomentRow (d q : ℕ) := (Fin d → Bool) ⊕ (Fin q × CubeFace d)
private abbrev MomentVar (d q : ℕ) := Option (Fin d) ⊕ Fin q

private def momentCoeff (d : ℕ) (j : Fin (d + 1)) (q : ℕ) :
    MomentRow d q → MomentVar d q → ℚ
  | Sum.inl ω, Sum.inl none => 1
  | Sum.inl ω, Sum.inl (some a) => if ω a then 1 else 0
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl none => 1
  | Sum.inr (_, ⟨i, ω⟩), Sum.inl (some a) => if ω.val a then csRatCoeff d j i a else 0
  | Sum.inr (p, ⟨i, _⟩), Sum.inr r => if r = p then (csCoeff d j i : ℚ) else 0

private lemma card_face_digit (d : ℕ) (i : Fin d) :
    Fintype.card {ω : Fin d → Bool // ω i = false} = 2 ^ (d - 1) := by
  classical
  let e : {ω : Fin d → Bool // ω i = false} ≃ ({a : Fin d // a ≠ i} → Bool) :=
    { toFun := fun ω a => ω.val a.val
      invFun := fun z => ⟨fun a => if ha : a = i then false else z ⟨a, ha⟩, by simp⟩
      left_inv := by
        intro ω
        apply Subtype.ext
        funext a
        by_cases ha : a = i
        · subst a
          simp [ω.property]
        · simp [ha]
      right_inv := by intro z; funext a; simp [a.property] }
  have hc : Fintype.card {a : Fin d // a ≠ i} = d - 1 := by
    simpa using Fintype.card_subtype_compl (fun a : Fin d => a = i)
  simpa only [Fintype.card_fun, Fintype.card_bool, hc] using Fintype.card_congr e

private lemma card_cube_face (d : ℕ) : Fintype.card (CubeFace d) = d * 2 ^ (d - 1) := by
  simp only [CubeFace, Fintype.card_sigma, card_face_digit, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

private lemma moment_nonzero (d : ℕ) (j : Fin (d + 1)) (q : ℕ) (r : MomentRow d q) :
    ∃ v, momentCoeff d j q r v ≠ 0 := by
  refine ⟨Sum.inl none, ?_⟩
  cases r <;> norm_num [momentCoeff]

private lemma moment_injective (d : ℕ) (j : Fin (d + 1)) (q : ℕ) :
    Function.Injective (momentCoeff d j q) := by
  classical
  obtain ⟨hci, hcinj, hheight, hzero⟩ := cs_coefficients d j
  have hcRat (i : Fin d) : (csCoeff d j i : ℚ) ≠ 0 := by exact_mod_cast (hci i).1
  intro r r' heq
  have hh (v) := congrFun heq v
  cases r with
  | inl ω =>
    cases r' with
    | inl ω' =>
      apply congrArg Sum.inl
      funext a
      have h := hh (Sum.inl (some a))
      cases hω : ω a <;> cases hω' : ω' a <;> simp [momentCoeff, hω, hω'] at h ⊢
    | inr f =>
      rcases f with ⟨p, i, ω⟩
      have h := hh (Sum.inr p)
      have hz : (0 : ℚ) = (csCoeff d j i : ℚ) := by simpa [momentCoeff] using h
      exact False.elim (hcRat i hz.symm)
  | inr f =>
    rcases f with ⟨p, i, ω⟩
    cases r' with
    | inl ω' =>
      have h := hh (Sum.inr p)
      have hz : (csCoeff d j i : ℚ) = 0 := by simpa [momentCoeff] using h
      exact False.elim (hcRat i hz)
    | inr f' =>
      rcases f' with ⟨p', i', ω'⟩
      have hpp : p = p' := by
        by_contra hne
        have h := hh (Sum.inr p)
        have hz : (csCoeff d j i : ℚ) = 0 := by simpa [momentCoeff, hne] using h
        exact hcRat i hz
      subst p'
      have hcc : (csCoeff d j i : ℚ) = (csCoeff d j i' : ℚ) := by
        simpa [momentCoeff] using hh (Sum.inr p)
      have hii : i = i' := hcinj (by exact_mod_cast hcc)
      subst i'
      have hωeq : ω = ω' := by
        apply Subtype.ext
        funext a
        by_cases hai : a = i
        · subst a
          exact ω.property.trans ω'.property.symm
        · have hca : csRatCoeff d j i a ≠ 0 := fun h => hai ((hzero i a).mp h).symm
          have h := hh (Sum.inl (some a))
          cases hω : ω.val a <;> cases hω' : ω'.val a <;>
            simp [momentCoeff, hω, hω', hca, eq_comm] at h ⊢
      subst ω'
      rfl

private lemma moment_distinct (d : ℕ) (j : Fin (d + 1)) (q : ℕ)
    (r r' : MomentRow d q) (hne : r ≠ r') :
    ¬ ∃ c : ℚ, ∀ v, momentCoeff d j q r v = c * momentCoeff d j q r' v := by
  rintro ⟨c, hc⟩
  have hx (r : MomentRow d q) : momentCoeff d j q r (Sum.inl none) = 1 := by
    cases r <;> rfl
  have hc1 : c = 1 := by simpa only [hx, mul_one] using (hc (Sum.inl none)).symm
  apply hne
  apply moment_injective d j q
  funext v
  simpa only [hc1, one_mul] using hc v

private lemma moment_height (d : ℕ) (j : Fin (d + 1)) (q : ℕ)
    (r : MomentRow d q) (v : MomentVar d q) :
    (momentCoeff d j q r v).num.natAbs ≤ d + 1 ∧
      (momentCoeff d j q r v).den ≤ d + 1 := by
  obtain ⟨hci, _, hheight, _⟩ := cs_coefficients d j
  have h0 : (0 : ℚ).num.natAbs ≤ d + 1 ∧ (0 : ℚ).den ≤ d + 1 := by norm_num
  have h1 : (1 : ℚ).num.natAbs ≤ d + 1 ∧ (1 : ℚ).den ≤ d + 1 := by norm_num
  have hrat (i a) : (csRatCoeff d j i a).num.natAbs ≤ d + 1 ∧
      (csRatCoeff d j i a).den ≤ d + 1 :=
    ⟨(hheight i a).1.trans (Nat.le_succ d), (hheight i a).2.trans (Nat.le_succ d)⟩
  have hint (i) : ((csCoeff d j i : ℚ)).num.natAbs ≤ d + 1 ∧
      ((csCoeff d j i : ℚ)).den ≤ d + 1 := by
    simpa using And.intro ((hci i).2.trans (Nat.le_succ d)) (Nat.succ_le_succ (Nat.zero_le d))
  cases r with
  | inl ω =>
    cases v with
    | inl a =>
      cases a with
      | none => exact h1
      | some a => dsimp [momentCoeff]; split_ifs <;> first | exact h0 | exact h1
    | inr p => exact h0
  | inr f =>
    rcases f with ⟨p, i, ω⟩
    cases v with
    | inl a =>
      cases a with
      | none => exact h1
      | some a => dsimp [momentCoeff]; split_ifs <;> first | exact h0 | exact hrat i _
    | inr p' => dsimp [momentCoeff]; split_ifs <;> first | exact hint i | exact h0

private lemma moment_row_bound (d q : ℕ) (hd : 2 ≤ d) (hq : q ≤ 2) :
    Fintype.card (MomentRow d q) ≤ (d + 1) * 2 ^ d := by
  simp only [MomentRow, Fintype.card_sum, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_prod, card_cube_face]
  have hp : 2 ^ d = 2 * 2 ^ (d - 1) := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
    ring
  calc
    2 ^ d + q * (d * 2 ^ (d - 1)) ≤ 2 ^ d + 2 * (d * 2 ^ (d - 1)) := by gcongr
    _ = (d + 1) * 2 ^ d := by rw [hp]; ring

private lemma moment_var_bound (d q : ℕ) (hd : 2 ≤ d) (hq : q ≤ 2) :
    Fintype.card (MomentVar d q) ≤ 3 * (d + 1) - 4 := by
  simp only [MomentVar, Fintype.card_sum, Fintype.card_option, Fintype.card_fin]
  omega

private lemma avg_equiv_moment {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : avg (fun x => f (e x)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e _

private lemma avg_prod_moment {α β : Type} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    avg f = avg (fun a => avg fun b => f (a, b)) := by
  simp only [avg, Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type,
    ← Finset.mul_sum]
  ring

private lemma avg_mul_moment {α : Type} [Fintype α] (c : ℝ) (f : α → ℝ) :
    avg (fun x => c * f x) = c * avg f := by
  simp only [avg, ← Finset.mul_sum]
  ring

private lemma avg_pi_prod_moment {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α]
    (F : ι → α → ℝ) : avg (fun z : ι → α => ∏ i, F i (z i)) = ∏ i, avg (F i) := by
  unfold avg
  rw [← Fintype.prod_sum F]
  simp only [Fintype.card_fun, Nat.cast_pow, inv_pow, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

private lemma avg_power_moment {α : Type} [Fintype α] (q : ℕ) (f : α → ℝ) :
    (avg f) ^ q = avg (fun r : Fin q → α => ∏ p, f (r p)) := by
  simpa using (avg_pi_prod_moment (fun _ : Fin q => f)).symm

private lemma prod_cube_face (d : ℕ) (f : Fin d → (Fin d → Bool) → ℝ) :
    (∏ a : CubeFace d, f a.1 a.2.val) =
      ∏ i : Fin d, ∏ ω : Fin d → Bool with ω i = false, f i ω := by
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  exact (Finset.prod_subtype (Finset.univ.filter (fun ω : Fin d → Bool => ω i = false))
    (by simp) (f i)).symm

private lemma ratCoeff_ite_moment (m : ℕ+) (p : Prop) [Decidable p] (a b : ℚ) :
    ratCoeff m (if p then a else b) = if p then ratCoeff m a else ratCoeff m b := by
  split_ifs <;> rfl

private lemma ratCoeff_zero_moment (m : ℕ+) : ratCoeff m 0 = 0 := by simp [ratCoeff]
private lemma ratCoeff_one_moment (m : ℕ+) : ratCoeff m 1 = 1 := by simp [ratCoeff]
private lemma ratCoeff_int_moment (m : ℕ+) (a : ℤ) : ratCoeff m (a : ℚ) = (a : ZMod (m : ℕ)) := by
  simp [ratCoeff]

private lemma moment_eval (d : ℕ) (j : Fin (d + 1)) (q : ℕ) (m : ℕ+)
    (r : MomentRow d q) (z : MomentVar d q → ZMod (m : ℕ)) :
    (∑ v : MomentVar d q, ratCoeff m (momentCoeff d j q r v) * z v) =
      match r with
      | Sum.inl ω => z (Sum.inl none) + ∑ a : Fin d, if ω a then z (Sum.inl (some a)) else 0
      | Sum.inr (p, ⟨i, ω⟩) => z (Sum.inl none) + (csCoeff d j i : ZMod (m : ℕ)) * z (Sum.inr p) +
          ∑ a : Fin d, ratCoeff m (csRatCoeff d j i a) * (if ω.val a then z (Sum.inl (some a)) else 0) := by
  classical
  cases r with
  | inl ω =>
    simp only [Fintype.sum_sum_type, Fintype.sum_option, momentCoeff, ratCoeff_ite_moment,
      ratCoeff_zero_moment, ratCoeff_one_moment]
    simp [ite_mul]
  | inr f =>
    rcases f with ⟨p, i, ω⟩
    simp only [Fintype.sum_sum_type, Fintype.sum_option, momentCoeff, ratCoeff_ite_moment,
      ratCoeff_zero_moment, ratCoeff_one_moment, ratCoeff_int_moment]
    simp only [one_mul, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    abel

theorem solution (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ+) (μ : Family M)
    (hLF : LinearFormsCondition M μ ((d + 1) * 2 ^ d) (3 * (d + 1) - 4) (d + 1))
    (j : Fin (d + 1)) (q : ℕ) (hq₀ : 1 ≤ q) (hq₂ : q ≤ 2) :
    Tendsto (fun n => avg fun x => avg fun h : Fin d → ZMod (M n : ℕ) =>
      csWeight d j (μ n) x h ^ q *
        ∏ ω : Fin d → Bool, μ n (x + ∑ a : Fin d, if ω a then h a else 0)) atTop (𝓝 1) := by
  classical
  have h := linear_forms_finite_indices M μ _ _ _ hLF (MomentRow d q) (MomentVar d q)
    (moment_row_bound d q hd hq₂) (moment_var_bound d q hd hq₂) (momentCoeff d j q)
    (moment_height d j q) (moment_nonzero d j q) (moment_distinct d j q) (fun _ _ => 0)
  have heq (n) :
      (avg fun z : MomentVar d q → ZMod (M n : ℕ) =>
        ∏ r : MomentRow d q, μ n ((∑ v, ratCoeff (M n) (momentCoeff d j q r v) * z v) + 0)) =
      avg (fun x => avg fun h : Fin d → ZMod (M n : ℕ) => csWeight d j (μ n) x h ^ q *
        ∏ ω : Fin d → Bool, μ n (x + ∑ a : Fin d, if ω a then h a else 0)) := by
    let V (x : ZMod (M n : ℕ)) (h : Fin d → ZMod (M n : ℕ)) : ℝ :=
      ∏ ω : Fin d → Bool, μ n (x + ∑ a : Fin d, if ω a then h a else 0)
    let B (x : ZMod (M n : ℕ)) (h : Fin d → ZMod (M n : ℕ)) (r : ZMod (M n : ℕ)) : ℝ :=
      ∏ i : Fin d, ∏ ω : Fin d → Bool with ω i = false,
        μ n (x + (csCoeff d j i : ZMod (M n : ℕ)) * r +
          ∑ a : Fin d, ratCoeff (M n) (csRatCoeff d j i a) * (if ω a then h a else 0))
    let e : (MomentVar d q → ZMod (M n : ℕ)) ≃
        ZMod (M n : ℕ) × ((Fin d → ZMod (M n : ℕ)) × (Fin q → ZMod (M n : ℕ))) :=
      { toFun := fun z => (z (Sum.inl none), (fun a => z (Sum.inl (some a)), fun p => z (Sum.inr p)))
        invFun := fun p v => match v with
          | Sum.inl none => p.1
          | Sum.inl (some a) => p.2.1 a
          | Sum.inr r => p.2.2 r
        left_inv := by intro z; funext v; cases v with
          | inl a => cases a <;> rfl
          | inr r => rfl
        right_inv := by intro p; rfl }
    let f : ZMod (M n : ℕ) × ((Fin d → ZMod (M n : ℕ)) × (Fin q → ZMod (M n : ℕ))) → ℝ :=
      fun p => V p.1 p.2.1 * ∏ r : Fin q, B p.1 p.2.1 (p.2.2 r)
    have hp (z : MomentVar d q → ZMod (M n : ℕ)) :
        (∏ r : MomentRow d q, μ n ((∑ v, ratCoeff (M n) (momentCoeff d j q r v) * z v) + 0)) = f (e z) := by
      simp only [add_zero]
      simp_rw [moment_eval]
      simp only [Fintype.prod_sum_type, Fintype.prod_prod_type]
      dsimp [f, e, V, B]
      congr 1
      apply Finset.prod_congr rfl
      intro p _
      exact prod_cube_face d (fun i ω => μ n (z (Sum.inl none) +
        (csCoeff d j i : ZMod (M n : ℕ)) * z (Sum.inr p) +
        ∑ a : Fin d, ratCoeff (M n) (csRatCoeff d j i a) * (if ω a then z (Sum.inl (some a)) else 0)))
    have hcopies (x : ZMod (M n : ℕ)) (h : Fin d → ZMod (M n : ℕ)) :
        avg (fun r : Fin q → ZMod (M n : ℕ) => V x h * ∏ p, B x h (r p)) =
          csWeight d j (μ n) x h ^ q * V x h := by
      rw [avg_mul_moment, ← avg_power_moment]
      change V x h * csWeight d j (μ n) x h ^ q = _
      ring
    simp_rw [hp]
    rw [avg_equiv_moment e f, avg_prod_moment]
    simp only [f]
    simp_rw [avg_prod_moment, hcopies]
    rfl
  simpa only [heq] using h
