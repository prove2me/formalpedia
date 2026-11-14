-- Prove2me | solution 1 for KSATSingleFlip.Connect.glauber_retained_fixed_count
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:12:05.377974+00:00
-- url     : https://prove2.me/submissions/d8eb47f7-c2f7-4068-90cd-300f5fa773a2

import Definitions.Def_KSATSingleFlip_Connect_Glauber


-- Component: AuditKSATBalancedPermutation.lean

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Two equal-sized subsets of a finite type can be exchanged by a permutation
that fixes their intersection and their common complement pointwise. -/
theorem audit_balanced_subset_permutation {α : Type} [Fintype α]
    (S T : Finset α) (hcard : S.card = T.card) :
    ∃ e : Equiv.Perm α,
      (∀ a, a ∈ S ↔ e a ∈ T) ∧
      (∀ a, (a ∈ S ↔ a ∈ T) → e a = a) := by
  classical
  let L := S \ T
  let R := T \ S
  have hLR : L.card = R.card := Finset.card_sdiff_comm hcard
  let h : ↥L ≃ ↥R := Fintype.equivOfCardEq (by simpa using hLR)
  let q : Equiv.Perm (↥L ⊕ ↥R) := (Equiv.sumCongr h h.symm).trans (Equiv.sumComm _ _)
  let embed : (↥L ⊕ ↥R) ↪ α := ⟨Sum.elim Subtype.val Subtype.val, by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => congr 1; exact Subtype.ext hab
      | inr b =>
        have ha := Finset.mem_sdiff.mp a.2
        have hb := Finset.mem_sdiff.mp b.2
        change a.val = b.val at hab
        exact (ha.2 (by rw [hab]; exact hb.1)).elim
    | inr a =>
      cases b with
      | inl b =>
        have ha := Finset.mem_sdiff.mp a.2
        have hb := Finset.mem_sdiff.mp b.2
        change a.val = b.val at hab
        exact (ha.2 (by rw [hab]; exact hb.1)).elim
      | inr b => congr 1; exact Subtype.ext hab⟩
  let e := q.viaFintypeEmbedding embed
  have hL : ∀ a (ha : a ∈ L), e a = (h ⟨a, ha⟩).1 := by
    intro a ha
    have hh := Equiv.Perm.viaFintypeEmbedding_apply_image q embed (Sum.inl ⟨a, ha⟩)
    change e a = (h ⟨a, ha⟩).1 at hh
    exact hh
  have hR : ∀ a (ha : a ∈ R), e a = (h.symm ⟨a, ha⟩).1 := by
    intro a ha
    have hh := Equiv.Perm.viaFintypeEmbedding_apply_image q embed (Sum.inr ⟨a, ha⟩)
    change e a = (h.symm ⟨a, ha⟩).1 at hh
    exact hh
  have hfix : ∀ a, a ∉ L → a ∉ R → e a = a := by
    intro a ha hb
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
    rintro ⟨b, hb'⟩
    cases b with
    | inl b =>
      change b.val = a at hb'
      exact ha (by rw [← hb']; exact b.2)
    | inr b =>
      change b.val = a at hb'
      exact hb (by rw [← hb']; exact b.2)
  refine ⟨e, ?_, ?_⟩
  · intro a
    by_cases ha : a ∈ L
    · have he : e a ∈ R := by rw [hL a ha]; exact (h ⟨a, ha⟩).2
      have hs : a ∈ S := (Finset.mem_sdiff.mp ha).1
      have ht : e a ∈ T := (Finset.mem_sdiff.mp he).1
      simp [hs, ht]
    · by_cases hb : a ∈ R
      · have he : e a ∈ L := by rw [hR a hb]; exact (h.symm ⟨a, hb⟩).2
        have hs : a ∉ S := (Finset.mem_sdiff.mp hb).2
        have ht : e a ∉ T := (Finset.mem_sdiff.mp he).2
        simp [hs, ht]
      · rw [hfix a ha hb]
        by_cases hs : a ∈ S <;> by_cases ht : a ∈ T <;> simp_all [L, R]
  · intro a hiff
    apply hfix
    · intro ha
      have := Finset.mem_sdiff.mp ha
      exact this.2 (hiff.mp this.1)
    · intro ha
      have := Finset.mem_sdiff.mp ha
      exact this.2 (hiff.mpr this.1)

end KSATSingleFlip.Connect


-- Component: AuditKSATSignSymmetry.lean

open scoped Classical BigOperators
open OAI.FixedClauseThreshold
namespace KSATSingleFlip.Connect

/-- Simultaneously flip assignments and literal signs according to a mask. -/
def audit_twist_assignment {n : ℕ} (a x : Fin n → Bool) : Fin n → Bool := fun v => x v ^^ a v

def audit_twist_clause {n : ℕ} (a : Fin n → Bool) (C : GClause (Fin n)) : GClause (Fin n) :=
  fun v => (C v).map (fun b => b ^^ a v)

def audit_twist_formula {n : ℕ} (a : Fin n → Bool) (Φ : GFormula (Fin n)) : GFormula (Fin n) :=
  Φ.map (audit_twist_clause a)

/-- Simultaneous sign and assignment flips preserve clause satisfaction. -/
theorem audit_twist_clause_sat {n : ℕ} (a x : Fin n → Bool) (C : GClause (Fin n)) :
    ClauseSat (audit_twist_assignment a x) (audit_twist_clause a C) ↔ ClauseSat x C := by
  unfold ClauseSat audit_twist_assignment audit_twist_clause
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    cases hC : C v with
    | none => simp [hC] at hv
    | some b =>
      simp only [hC, Option.map_some, Option.some.injEq] at hv
      have hb : b = x v := by
        cases ha : a v <;> cases hb : b <;> cases hx : x v <;> simp_all
      simp [hC, hb]
  · rintro ⟨v, hv⟩
    exact ⟨v, by simp [hv]⟩

/-- Simultaneous flips preserve satisfaction of a formula. -/
theorem audit_twist_formula_sat {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n)) :
    FSat (audit_twist_assignment a x) (audit_twist_formula a Φ) ↔ FSat x Φ := by
  unfold FSat audit_twist_formula
  constructor
  · intro h C hc
    apply (audit_twist_clause_sat a x C).mp
    exact h _ (List.mem_map.mpr ⟨C, hc, rfl⟩)
  · intro h C hc
    obtain ⟨C', hC', rfl⟩ := List.mem_map.mp hc
    exact (audit_twist_clause_sat a x C').mpr (h C' hC')

/-- Updating a variable commutes with the simultaneous sign flip. -/
theorem audit_twist_update {n : ℕ} (a x : Fin n → Bool) (v : Fin n) (b : Bool) :
    audit_twist_assignment a (Function.update x v b) =
      Function.update (audit_twist_assignment a x) v (b ^^ a v) := by
  funext i
  by_cases hi : i = v
  · subst i; simp [audit_twist_assignment]
  · simp [audit_twist_assignment, Function.update_of_ne hi]

/-- A Glauber step is equivariant when the random bit is flipped together with
its variable's literal signs. -/
theorem audit_twist_glauber_step {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (v : Fin n) (b : Bool) :
    glauberStep (audit_twist_formula a Φ) (audit_twist_assignment a x) (v, b ^^ a v) =
      audit_twist_assignment a (glauberStep Φ x (v, b)) := by
  have h1 : FSat (Function.update (audit_twist_assignment a x) v (b ^^ a v))
      (audit_twist_formula a Φ) ↔ FSat (Function.update x v b) Φ := by
    rw [← audit_twist_update]
    exact audit_twist_formula_sat a _ Φ
  have h2 : FSat (Function.update (audit_twist_assignment a x) v (!(b ^^ a v)))
      (audit_twist_formula a Φ) ↔ FSat (Function.update x v (!b)) Φ := by
    rw [← Bool.not_xor, ← audit_twist_update]
    exact audit_twist_formula_sat a _ Φ
  unfold glauberStep
  simp only [h1, h2]
  split
  · rw [audit_twist_update]
  · split
    · rw [audit_twist_update, Bool.not_xor]
    · rfl

/-- Flip the random update bit at the variable selected by the update. -/
def audit_twist_update_input {n : ℕ} (a : Fin n → Bool) (u : Fin n × Bool) : Fin n × Bool :=
  (u.1, u.2 ^^ a u.1)

/-- Simultaneous sign flips commute with a finite Glauber run. -/
theorem audit_twist_glauber_run {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (seq : List (Fin n × Bool)) :
    glauberRun (audit_twist_formula a Φ) (audit_twist_assignment a x)
      (seq.map (audit_twist_update_input a)) = audit_twist_assignment a (glauberRun Φ x seq) := by
  induction seq generalizing x with
  | nil => rfl
  | cons u us ih =>
    rcases u with ⟨v, b⟩
    simp only [List.map_cons, glauberRun, List.foldl_cons]
    change glauberRun (audit_twist_formula a Φ)
      (glauberStep (audit_twist_formula a Φ) (audit_twist_assignment a x) (v, b ^^ a v))
      (us.map (audit_twist_update_input a)) =
      audit_twist_assignment a (glauberRun Φ (glauberStep Φ x (v, b)) us)
    rw [audit_twist_glauber_step]
    exact ih _

/-- Simultaneous sign flips commute with the t-step Glauber state. -/
theorem audit_twist_glauber_state {n t : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (s : Fin t → Fin n × Bool) :
    glauberState (audit_twist_formula a Φ) (audit_twist_assignment a x)
      (fun i => audit_twist_update_input a (s i)) = audit_twist_assignment a (glauberState Φ x s) := by
  unfold glauberState
  change glauberRun (audit_twist_formula a Φ) (audit_twist_assignment a x)
    (List.ofFn ((audit_twist_update_input a) ∘ s)) = audit_twist_assignment a (glauberRun Φ x (List.ofFn s))
  rw [← List.map_ofFn]
  exact audit_twist_glauber_run a x Φ (List.ofFn s)

/-- Literal-sign flips preserve variable scopes and true-literal sets. -/
theorem audit_twist_scope {n : ℕ} (a : Fin n → Bool) (C : GClause (Fin n)) :
    vbl (audit_twist_clause a C) = vbl C := by
  ext v
  simp [vbl, audit_twist_clause]

theorem audit_twist_satSet {n : ℕ} (a x : Fin n → Bool) (C : GClause (Fin n)) :
    satSet (audit_twist_assignment a x) (audit_twist_clause a C) = satSet x C := by
  ext v
  simp only [satSet, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold audit_twist_assignment audit_twist_clause
  cases hC : C v with
  | none => simp [hC]
  | some b =>
    simp only [hC, Option.map_some, Option.some.injEq]
    cases ha : a v <;> cases hb : b <;> cases hx : x v <;> simp_all

/-- The sign flip is its own inverse on assignments, clauses, and updates. -/
theorem audit_twist_assignment_involutive {n : ℕ} (a x : Fin n → Bool) :
    audit_twist_assignment a (audit_twist_assignment a x) = x := by
  funext v
  simp [audit_twist_assignment, Bool.xor_assoc]

theorem audit_twist_clause_involutive {n : ℕ} (a : Fin n → Bool) (C : GClause (Fin n)) :
    audit_twist_clause a (audit_twist_clause a C) = C := by
  funext v
  unfold audit_twist_clause
  cases hC : C v with
  | none => simp [hC]
  | some b => simp [hC, Bool.xor_assoc]

theorem audit_twist_input_involutive {n : ℕ} (a : Fin n → Bool) (u : Fin n × Bool) :
    audit_twist_update_input a (audit_twist_update_input a u) = u := by
  rcases u with ⟨v, b⟩
  simp [audit_twist_update_input, Bool.xor_assoc]

/-- Literal-sign flips are a permutation of the proper k-clauses. -/
noncomputable def audit_twist_proper {n k : ℕ} (a : Fin n → Bool)
    (C : ProperClause n k) : ProperClause n k :=
  ⟨audit_twist_clause a C.1, by
    change (vbl (audit_twist_clause a C.1)).card = k
    rw [audit_twist_scope]
    exact C.2⟩

theorem audit_twist_proper_involutive {n k : ℕ} (a : Fin n → Bool)
    (C : ProperClause n k) : audit_twist_proper a (audit_twist_proper a C) = C := by
  apply Subtype.ext
  exact audit_twist_clause_involutive a C.1

noncomputable def audit_twist_proper_equiv {n k : ℕ} (a : Fin n → Bool) :
    ProperClause n k ≃ ProperClause n k where
  toFun := audit_twist_proper a
  invFun := audit_twist_proper a
  left_inv := audit_twist_proper_involutive a
  right_inv := audit_twist_proper_involutive a

noncomputable def audit_twist_input_equiv {n : ℕ} (a : Fin n → Bool) :
    (Fin n × Bool) ≃ (Fin n × Bool) where
  toFun := audit_twist_update_input a
  invFun := audit_twist_update_input a
  left_inv := audit_twist_input_involutive a
  right_inv := audit_twist_input_involutive a

/-- Uniform finite expectations are invariant under a permutation. -/
theorem audit_uexp_equiv {α : Type} [Fintype α] (e : α ≃ α) (f : α → ℝ) :
    uexp (fun x => f (e x)) = uexp f := by
  unfold uexp
  rw [e.sum_comp]

/-- The all-clauses sampling subtype is permuted by the same sign flip. -/
noncomputable def audit_twist_allClause_equiv {n k : ℕ} (a : Fin n → Bool) :
    ↥(allClauses n k) ≃ ↥(allClauses n k) where
  toFun C := ⟨audit_twist_proper a C.1, Finset.mem_univ _⟩
  invFun C := ⟨audit_twist_proper a C.1, Finset.mem_univ _⟩
  left_inv C := by apply Subtype.ext; exact audit_twist_proper_involutive a C.1
  right_inv C := by apply Subtype.ext; exact audit_twist_proper_involutive a C.1

/-- The Poisson formula-list law is invariant under simultaneous sign flips. -/
theorem audit_pois_formula_sign_invariant {n k : ℕ} (a : Fin n → Bool) (m : ℝ)
    (f : List (ProperClause n k) → ℝ) :
    poisExp (allClauses n k) m (fun l => f (l.map (audit_twist_proper a))) =
      poisExp (allClauses n k) m f := by
  unfold poisExp
  apply tsum_congr
  intro N
  congr 1
  let e : (Fin N → ↥(allClauses n k)) ≃ (Fin N → ↥(allClauses n k)) :=
    Equiv.piCongrRight (fun _ => audit_twist_allClause_equiv a)
  have h := audit_uexp_equiv e (fun F : Fin N → ↥(allClauses n k) =>
    f (List.ofFn fun i => (F i).1))
  convert h using 1
  congr 1
  funext F
  dsimp only
  congr 1
  rw [List.map_ofFn]
  rfl

/-- Uniform update-sequence expectations are invariant under flipping each bit. -/
theorem audit_glauber_input_sign_invariant {n t : ℕ} (a : Fin n → Bool)
    (f : (Fin t → Fin n × Bool) → ℝ) :
    uexp (fun s : Fin t → Fin n × Bool => f (fun i => audit_twist_update_input a (s i))) = uexp f := by
  let e : (Fin t → Fin n × Bool) ≃ (Fin t → Fin n × Bool) :=
    Equiv.piCongrRight (fun _ => audit_twist_input_equiv a)
  exact audit_uexp_equiv e f

/-- Retaining satisfied clause positions is the same ordered list as filtering. -/
theorem audit_subF_satIdx_eq_satBy {n : ℕ} (Φ : GFormula (Fin n)) (z : Fin n → Bool) :
    subF Φ (satIdx Φ z) = satBy Φ z := by
  unfold subF satIdx satBy
  conv_rhs => rw [← List.map_get_finRange Φ]
  rw [← List.filterMap_eq_filter]
  rw [List.filterMap_map]
  congr 1
  funext c
  simp [Option.guard]

/-- Retaining the clauses satisfied by the start commutes with sign flips. -/
theorem audit_twist_satBy {n : ℕ} (a z : Fin n → Bool) (Φ : GFormula (Fin n)) :
    audit_twist_formula a (satBy Φ z) =
      satBy (audit_twist_formula a Φ) (audit_twist_assignment a z) := by
  unfold satBy audit_twist_formula
  induction Φ with
  | nil => rfl
  | cons C Φ ih =>
    simp only [List.filter_cons, List.map_cons]
    have hs := audit_twist_clause_sat a z C
    by_cases h : ClauseSat z C
    · simp [h, hs.mpr h, ih]
    · have ht : ¬ ClauseSat (audit_twist_assignment a z) (audit_twist_clause a C) := fun ht => h (hs.mp ht)
      simp [h, ht, ih]

/-- The actual retained subformula, including its order, commutes with sign flips. -/
theorem audit_twist_retained_subformula {n : ℕ} (a z : Fin n → Bool) (Φ : GFormula (Fin n)) :
    audit_twist_formula a (subF Φ (satIdx Φ z)) =
      subF (audit_twist_formula a Φ) (satIdx (audit_twist_formula a Φ) (audit_twist_assignment a z)) := by
  rw [audit_subF_satIdx_eq_satBy, audit_subF_satIdx_eq_satBy]
  exact audit_twist_satBy a z Φ

/-- Flipping every literal sign twice restores the original clause list. -/
theorem audit_twist_formula_involutive {n : ℕ} (a : Fin n → Bool) (Φ : GFormula (Fin n)) :
    audit_twist_formula a (audit_twist_formula a Φ) = Φ := by
  unfold audit_twist_formula
  rw [List.map_map]
  simpa [Function.comp_def, audit_twist_clause_involutive]

end KSATSingleFlip.Connect


-- Component: AuditKSATClauseCount.lean

open scoped Classical BigOperators
open OAI.FixedClauseThreshold
namespace KSATSingleFlip.Connect

/-- An assignment falsifying a clause is uniquely determined on its scope and
arbitrary on the complementary variables. -/
noncomputable def audit_falsifying_equiv {n : ℕ} (C : GClause (Fin n)) :
    {z : Fin n → Bool // ¬ ClauseSat z C} ≃ ({v : Fin n // C v = none} → Bool) where
  toFun z := fun v => z.1 v.1
  invFun q := ⟨fun v => if h : C v = none then q ⟨v, h⟩ else !(C v).getD false, by
    rintro ⟨v, hv⟩
    by_cases h : C v = none
    · simp [h] at hv
    · cases hc : C v with
      | none => exact h hc
      | some b =>
        simp [hc] at hv⟩
  left_inv z := by
    apply Subtype.ext
    funext v
    by_cases h : C v = none
    · simp [h]
    · have hz : C v ≠ some (z.1 v) := fun hv => z.2 ⟨v, hv⟩
      cases hc : C v with
      | none => exact (h hc).elim
      | some b =>
        simp only [if_neg h, hc, Option.getD_some]
        cases hb : b <;> cases hv : z.1 v <;> simp_all
  right_inv q := by
    funext v
    simp [v.2]

/-- Exactly 2^(n-k) assignments falsify a proper k-clause. -/
theorem audit_falsifying_assignment_count {n k : ℕ} (C : ProperClause n k) :
    Fintype.card {z : Fin n → Bool // ¬ ClauseSat z C.1} = 2 ^ (n - k) := by
  rw [Fintype.card_congr (audit_falsifying_equiv C.1), Fintype.card_fun, Fintype.card_bool]
  congr 1
  have hscope : (Finset.univ.filter fun v => (C.1 v).isSome).card = k := C.2
  have hcomp : Fintype.card {v : Fin n // C.1 v = none} = n - k := by
    rw [Fintype.card_subtype]
    have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun v => (C.1 v).isSome)
    have heq : (Finset.univ.filter fun v : Fin n => C.1 v = none) =
        Finset.univ.filter (fun v => ¬ (C.1 v).isSome) := by
      ext v
      cases hc : C.1 v <;> simp [hc]
    rw [heq]
    simp only [Finset.card_univ, Fintype.card_fin, hscope] at hpart
    omega
  exact hcomp

end KSATSingleFlip.Connect


-- Component: AuditKSATClauseNonempty.lean

open scoped Classical BigOperators
open OAI.FixedClauseThreshold
namespace KSATSingleFlip.Connect

/-- For 1 ≤ k ≤ n, there are proper k-clauses both satisfied and falsified
by each assignment. This supplies nonempty alphabets for Poisson thinning. -/
theorem audit_planted_clause_alphabets_nonempty {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (z : Fin n → Bool) :
    (clausesSatBy (k := k) (fun _ : Fin 1 => z)).Nonempty ∧
      ((allClauses n k).filter fun C => ¬ ClauseSat z C.1).Nonempty := by
  let U : Finset (Fin n) := Finset.univ.filter fun v => v.val < k
  have hU : U.card = k := by
    dsimp [U]
    rw [Fin.card_filter_val_lt]
    exact Nat.min_eq_right hkn
  let v0 : Fin n := ⟨0, by omega⟩
  have hv0 : v0 ∈ U := by simp [U, v0]; omega
  let Cfalse : ProperClause n k := ⟨fun v => if v ∈ U then some (!z v) else none, by
    change (Finset.univ.filter fun v => (if v ∈ U then some (!z v) else none).isSome).card = k
    have hs : (Finset.univ.filter fun v => (if v ∈ U then some (!z v) else none).isSome) = U := by
      ext v
      simp
    rw [hs]
    exact hU⟩
  let Ctrue : ProperClause n k := ⟨fun v => if v ∈ U then some (if v = v0 then z v else !z v) else none, by
    change (Finset.univ.filter fun v => (if v ∈ U then some (if v = v0 then z v else !z v) else none).isSome).card = k
    have hs : (Finset.univ.filter fun v => (if v ∈ U then some (if v = v0 then z v else !z v) else none).isSome) = U := by
      ext v
      simp
    rw [hs]
    exact hU⟩
  constructor
  · refine ⟨Ctrue, ?_⟩
    simp only [clausesSatBy, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    refine ⟨v0, ?_⟩
    simp [Ctrue, hv0]
  · refine ⟨Cfalse, ?_⟩
    simp only [allClauses, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨v, hv⟩
    by_cases hmem : v ∈ U
    · have hb : !z v = z v := by simpa [Cfalse, hmem] using hv
      cases h : z v <;> simp [h] at hb
    · simp [Cfalse, hmem] at hv

end KSATSingleFlip.Connect


-- Component: AuditKSATClauseProbability.lean

open scoped Classical BigOperators
open OAI.FixedClauseThreshold
namespace KSATSingleFlip.Connect

/-- The number of clauses falsified by an assignment does not depend on it. -/
theorem audit_falsified_clause_card_invariant {n k : ℕ} (z z' : Fin n → Bool) :
    (Finset.univ.filter fun C : ProperClause n k => ¬ ClauseSat z C.1).card =
      (Finset.univ.filter fun C : ProperClause n k => ¬ ClauseSat z' C.1).card := by
  let a : Fin n → Bool := fun v => z v ^^ z' v
  have ha : audit_twist_assignment a z = z' := by
    funext v
    dsimp [audit_twist_assignment, a]
    cases hz : z v <;> cases hz' : z' v <;> rfl
  apply Finset.card_bij (fun C _ => audit_twist_proper a C)
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
    change ¬ ClauseSat z' (audit_twist_clause a C.1)
    rw [← ha, audit_twist_clause_sat]
    exact hC
  · intro C hC D hD heq
    apply (audit_twist_proper_equiv a).injective
    exact heq
  · intro D hD
    refine ⟨audit_twist_proper a D, ?_, audit_twist_proper_involutive a D⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
    have hflip := audit_twist_clause_sat a z (audit_twist_clause a D.1)
    rw [audit_twist_clause_involutive, ha] at hflip
    exact fun h => hD (hflip.mpr h)

/-- Double-count falsifying clause/assignment pairs, retaining the exact
occurrence and sign conventions of the random k-SAT model. -/
theorem audit_falsified_clause_double_count {n k : ℕ} (z : Fin n → Bool) :
    (Finset.univ.filter fun C : ProperClause n k => ¬ ClauseSat z C.1).card * 2 ^ n =
      Fintype.card (ProperClause n k) * 2 ^ (n - k) := by
  let Bad := fun q : Fin n → Bool => Finset.univ.filter fun C : ProperClause n k => ¬ ClauseSat q C.1
  have hsum1 : (∑ q : Fin n → Bool, (Bad q).card) = (Bad z).card * 2 ^ n := by
    have hconst : ∀ q, (Bad q).card = (Bad z).card := fun q => audit_falsified_clause_card_invariant q z
    simp [hconst, Fintype.card_fun, Nat.mul_comm]
  have hsum2 : (∑ C : ProperClause n k, Fintype.card {q : Fin n → Bool // ¬ ClauseSat q C.1}) =
      Fintype.card (ProperClause n k) * 2 ^ (n - k) := by
    calc
      _ = ∑ _C : ProperClause n k, 2 ^ (n - k) := by
        apply Finset.sum_congr rfl
        intro C _
        exact audit_falsifying_assignment_count C
      _ = _ := by simp [Nat.mul_comm]
  have hswap : (∑ q : Fin n → Bool, (Bad q).card) =
      ∑ C : ProperClause n k, Fintype.card {q : Fin n → Bool // ¬ ClauseSat q C.1} := by
    simp only [Bad, Finset.card_filter, Fintype.card_subtype]
    rw [Finset.sum_comm]
  exact hsum1.symm.trans (hswap.trans hsum2)

/-- The exact fraction of proper k-clauses falsified by a fixed assignment. -/
theorem audit_falsified_clause_card {n k : ℕ} (hkn : k ≤ n) (z : Fin n → Bool) :
    (Finset.univ.filter fun C : ProperClause n k => ¬ ClauseSat z C.1).card * 2 ^ k =
      Fintype.card (ProperClause n k) := by
  have h := audit_falsified_clause_double_count (k := k) z
  have hp : 2 ^ n = 2 ^ (n - k) * 2 ^ k := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp] at h
  apply Nat.eq_of_mul_eq_mul_left (n := 2 ^ (n - k)) (Nat.pow_pos (by omega : 0 < 2))
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- A uniformly drawn proper k-clause is falsified by a fixed assignment with
probability 2^(-k). -/
theorem audit_random_clause_falsified_probability {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (z : Fin n → Bool) :
    uprob (fun C : ProperClause n k => ¬ ClauseSat z C.1) = 1 / (2 : ℝ) ^ k := by
  obtain ⟨hsat, _⟩ := audit_planted_clause_alphabets_nonempty hk hkn z
  have hne : Nonempty (ProperClause n k) := ⟨hsat.choose⟩
  have hN : (0 : ℝ) < Fintype.card (ProperClause n k) := by
    exact_mod_cast Fintype.card_pos_iff.mpr hne
  have hcard : (((Finset.univ.filter fun C : ProperClause n k => ¬ ClauseSat z C.1).card : ℕ) : ℝ) *
      (2 : ℝ) ^ k = Fintype.card (ProperClause n k) := by
    exact_mod_cast audit_falsified_clause_card hkn z
  have hprob : uprob (fun C : ProperClause n k => ¬ ClauseSat z C.1) =
      ((Finset.univ.filter fun C : ProperClause n k => ¬ ClauseSat z C.1).card : ℝ) /
        Fintype.card (ProperClause n k) := by
    unfold uprob uexp
    congr 1
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro C hC
    by_cases h : ClauseSat z C.1 <;> simp [h]
  rw [hprob]
  apply (div_eq_iff (ne_of_gt hN)).mpr
  have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The planted alphabet occupies the fraction 1 − 2⁻ᵏ of all proper clauses. -/
theorem audit_planted_clause_fraction {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (z : Fin n → Bool) :
    ((clausesSatBy (k := k) (fun _ : Fin 1 => z)).card : ℝ) /
      Fintype.card (ProperClause n k) = 1 - 1 / (2 : ℝ) ^ k := by
  obtain ⟨hsat, _⟩ := audit_planted_clause_alphabets_nonempty hk hkn z
  have hne : Nonempty (ProperClause n k) := ⟨hsat.choose⟩
  have hN : (0 : ℝ) < Fintype.card (ProperClause n k) := by exact_mod_cast Fintype.card_pos_iff.mpr hne
  have hbad := audit_falsified_clause_card hkn z
  have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ProperClause n k)))
      (p := fun C => ClauseSat z C.1)
  have hsatset : clausesSatBy (k := k) (fun _ : Fin 1 => z) =
      Finset.univ.filter (fun C => ClauseSat z C.1) := by
    ext C
    simp [clausesSatBy]
  rw [hsatset]
  have hpartR : ((Finset.univ.filter fun C : ProperClause n k => ClauseSat z C.1).card : ℝ) +
      (Finset.univ.filter fun C : ProperClause n k => ¬ ClauseSat z C.1).card = Fintype.card (ProperClause n k) := by
    exact_mod_cast hpart
  have hbadR : ((Finset.univ.filter fun C : ProperClause n k => ¬ ClauseSat z C.1).card : ℝ) *
      (2 : ℝ) ^ k = Fintype.card (ProperClause n k) := by exact_mod_cast hbad
  have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
  apply (div_eq_iff (ne_of_gt hN)).mpr
  field_simp
  have hmul := congrArg (fun q : ℝ => q * (2 : ℝ) ^ k) hpartR
  nlinarith

end KSATSingleFlip.Connect


-- Component: AuditKSATFilterLikelihood.lean

set_option maxHeartbeats 1000000

open scoped Classical BigOperators
open OAI.FixedClauseThreshold
namespace KSATSingleFlip.Connect

/-- The ordered Poisson list law is invariant under a permutation of its finite alphabet. -/
theorem audit_pois_univ_equiv {α : Type} [Fintype α] (e : Equiv.Perm α) (m : ℝ)
    (f : List α → ℝ) :
    poisExp Finset.univ m (fun l => f (l.map e)) = poisExp Finset.univ m f := by
  classical
  unfold poisExp
  apply tsum_congr
  intro N
  congr 1
  let E : ↥(Finset.univ : Finset α) ≃ ↥(Finset.univ : Finset α) := {
    toFun C := ⟨e C.1, Finset.mem_univ _⟩
    invFun C := ⟨e.symm C.1, Finset.mem_univ _⟩
    left_inv C := by apply Subtype.ext; simp
    right_inv C := by apply Subtype.ext; simp }
  let Eseq : (Fin N → ↥(Finset.univ : Finset α)) ≃ (Fin N → ↥(Finset.univ : Finset α)) :=
    Equiv.piCongrRight (fun _ => E)
  have h := audit_uexp_equiv Eseq (fun F : Fin N → ↥(Finset.univ : Finset α) =>
    f (List.ofFn fun i => (F i).1))
  convert h using 1
  congr 1
  funext F
  dsimp only
  congr 1
  rw [List.map_ofFn]
  rfl

/-- A permuted list filtered by the target set is the permuted source filter. -/
theorem audit_filter_map_equiv {α : Type} [Fintype α] (S T : Finset α)
    (e : Equiv.Perm α) (h : ∀ a, a ∈ S ↔ e a ∈ T) (l : List α) :
    (l.map e).filter (fun a => decide (a ∈ T)) = (l.filter (fun a => decide (a ∈ S))).map e := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro a ha
  simp only [Function.comp_apply]
  simp [h a]

/-- For equal-sized filters, the likelihood of a particular list contained in
both filters is the same under either filter of a uniform Poisson list. -/
theorem audit_pois_filter_common_likelihood {α : Type} [Fintype α]
    (S T : Finset α) (hcard : S.card = T.card) (L : List α)
    (hL : ∀ a ∈ L, a ∈ S ∧ a ∈ T) (m : ℝ) :
    poisProb Finset.univ m (fun l => l.filter (fun a => decide (a ∈ S)) = L) =
      poisProb Finset.univ m (fun l => l.filter (fun a => decide (a ∈ T)) = L) := by
  classical
  obtain ⟨e, he, hfix⟩ := audit_balanced_subset_permutation S T hcard
  have hLfix : L.map e = L := by
    calc
      L.map e = L.map id := (List.map_inj_left).mpr (by
        intro a ha
        exact hfix a ⟨fun _ => (hL a ha).2, fun _ => (hL a ha).1⟩)
      _ = L := List.map_id L
  have hf : ∀ l : List α,
      (l.map e).filter (fun a => decide (a ∈ T)) = L ↔
        l.filter (fun a => decide (a ∈ S)) = L := by
    intro l
    rw [audit_filter_map_equiv S T e he]
    constructor
    · intro h
      apply e.injective.list_map
      simpa [hLfix] using h
    · intro h
      simpa [h, hLfix]
  unfold poisProb
  calc
    _ = poisExp Finset.univ m (fun l => if (l.map e).filter (fun a => decide (a ∈ T)) = L then (1 : ℝ) else 0) := by
      congr 1
      funext l
      by_cases h : l.filter (fun a => decide (a ∈ S)) = L
      · have h' := (hf l).mpr h
        simp [h, h']
      · have h' : (l.map e).filter (fun a => decide (a ∈ T)) ≠ L := fun h' => h ((hf l).mp h')
        simp [h, h']
    _ = _ := by
      have h := audit_pois_univ_equiv e m (fun l : List α => if l.filter (fun a => decide (a ∈ T)) = L then (1 : ℝ) else 0)
      convert h using 1 <;> congr 1 <;> funext l <;> dsimp only <;>
        by_cases hh : l.filter (fun a => decide (a ∈ T)) = L <;> simp [hh]

/-- Retaining a particular clause list has the same likelihood for any two
starting assignments satisfying every clause of that list. -/
theorem audit_retained_list_likelihood_equal {n k : ℕ} (z z' : Fin n → Bool)
    (F : List (ProperClause n k)) (m : ℝ)
    (hF : ∀ C ∈ F, ClauseSat z C.1 ∧ ClauseSat z' C.1) :
    poisProb (allClauses n k) m (fun l => l.filter (fun C => decide (ClauseSat z C.1)) = F) =
    poisProb (allClauses n k) m (fun l => l.filter (fun C => decide (ClauseSat z' C.1)) = F) := by
  classical
  let S : Finset (ProperClause n k) := Finset.univ.filter fun C => ClauseSat z C.1
  let T : Finset (ProperClause n k) := Finset.univ.filter fun C => ClauseSat z' C.1
  have hbad := audit_falsified_clause_card_invariant (k := k) z z'
  have hS := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ProperClause n k)))
      (p := fun C => ClauseSat z C.1)
  have hT := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ProperClause n k)))
      (p := fun C => ClauseSat z' C.1)
  have hcard : S.card = T.card := by dsimp [S, T]; omega
  have hcommon : ∀ C ∈ F, C ∈ S ∧ C ∈ T := by
    intro C hC
    simpa [S, T] using hF C hC
  have h := audit_pois_filter_common_likelihood S T hcard F hcommon m
  simpa [allClauses, S, T] using h

/-- A retained list has zero likelihood at a start that does not satisfy it. -/
theorem audit_retained_list_likelihood_zero {n k : ℕ} (z : Fin n → Bool)
    (F : List (ProperClause n k)) (m : ℝ) (hF : ¬ FSat z (ofList F)) :
    poisProb (allClauses n k) m (fun l => l.filter (fun C => decide (ClauseSat z C.1)) = F) = 0 := by
  classical
  have hzero : ∀ l : List (ProperClause n k), l.filter (fun C => decide (ClauseSat z C.1)) ≠ F := by
    intro l heq
    apply hF
    intro C hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    rw [← heq] at hD
    exact of_decide_eq_true (List.mem_filter.mp hD).2
  unfold poisProb poisExp
  simp [hzero, uexp]


end KSATSingleFlip.Connect


-- Component: AuditKSATFixedRetainedLikelihood.lean

set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open OAI.FixedClauseThreshold
namespace KSATSingleFlip.Connect

/-- With a fixed number of uniformly drawn letters, any particular retained
list common to two equally large alphabets has the same probability. -/
theorem audit_fixed_filter_common_likelihood {α : Type} [Fintype α]
    (S T : Finset α) (hcard : S.card = T.card) (L : List α)
    (hL : ∀ a ∈ L, a ∈ S ∧ a ∈ T) (M : ℕ) :
    uprob (fun F : Fin M → α => (List.ofFn F).filter (fun a => decide (a ∈ S)) = L) =
    uprob (fun F : Fin M → α => (List.ofFn F).filter (fun a => decide (a ∈ T)) = L) := by
  classical
  obtain ⟨e, he, hfix⟩ := audit_balanced_subset_permutation S T hcard
  have hLfix : L.map e = L := by
    calc
      L.map e = L.map id := (List.map_inj_left).mpr (by
        intro a ha
        exact hfix a ⟨fun _ => (hL a ha).2, fun _ => (hL a ha).1⟩)
      _ = L := List.map_id L
  have hf : ∀ l : List α,
      (l.map e).filter (fun a => decide (a ∈ T)) = L ↔
        l.filter (fun a => decide (a ∈ S)) = L := by
    intro l
    rw [audit_filter_map_equiv S T e he]
    constructor
    · intro h
      apply e.injective.list_map
      simpa [hLfix] using h
    · intro h
      simpa [h, hLfix]
  let Eseq : (Fin M → α) ≃ (Fin M → α) := Equiv.piCongrRight (fun _ => e)
  have heq := audit_uexp_equiv Eseq (fun F : Fin M → α =>
    if (List.ofFn F).filter (fun a => decide (a ∈ T)) = L then (1 : ℝ) else 0)
  unfold uprob
  calc
    _ = uexp (fun F : Fin M → α =>
      if (List.ofFn (fun i => e (F i))).filter (fun a => decide (a ∈ T)) = L then (1 : ℝ) else 0) := by
      congr 1
      funext F
      have hf' : (List.ofFn (fun i => e (F i))).filter (fun a => decide (a ∈ T)) = L ↔
          (List.ofFn F).filter (fun a => decide (a ∈ S)) = L := by
        simpa only [List.map_ofFn, Function.comp_def] using hf (List.ofFn F)
      simp only [hf']
      split_ifs <;> simp_all
    _ = _ := by
      convert heq using 1 <;> congr 1 <;> funext F <;> dsimp [Eseq] <;> split_ifs <;> simp_all

/-- Fixed-count retained-list likelihood is equal for every satisfying start. -/
theorem audit_fixed_retained_likelihood_equal {n k : ℕ} (z z' : Fin n → Bool)
    (F : List (ProperClause n k)) (M : ℕ)
    (hF : ∀ C ∈ F, ClauseSat z C.1 ∧ ClauseSat z' C.1) :
    uprob (fun G : Fin M → ProperClause n k =>
      (List.ofFn G).filter (fun C => decide (ClauseSat z C.1)) = F) =
    uprob (fun G : Fin M → ProperClause n k =>
      (List.ofFn G).filter (fun C => decide (ClauseSat z' C.1)) = F) := by
  let S : Finset (ProperClause n k) := Finset.univ.filter fun C => ClauseSat z C.1
  let T : Finset (ProperClause n k) := Finset.univ.filter fun C => ClauseSat z' C.1
  have hbad := audit_falsified_clause_card_invariant (k := k) z z'
  have hS := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ProperClause n k)))
      (p := fun C => ClauseSat z C.1)
  have hT := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ProperClause n k)))
      (p := fun C => ClauseSat z' C.1)
  have hcard : S.card = T.card := by dsimp [S, T]; omega
  have hcommon : ∀ C ∈ F, C ∈ S ∧ C ∈ T := by
    intro C hC
    simpa [S, T] using hF C hC
  have h := audit_fixed_filter_common_likelihood S T hcard F hcommon M
  simpa [S, T] using h

/-- Equal retained-list fiber cardinalities, including empty sample spaces. -/
theorem audit_fixed_filter_common_count {α : Type} [Fintype α]
    (S T : Finset α) (hcard : S.card = T.card) (L : List α)
    (hL : ∀ a ∈ L, a ∈ S ∧ a ∈ T) (M : ℕ) :
    (Finset.univ.filter fun F : Fin M → α =>
      (List.ofFn F).filter (fun a => decide (a ∈ S)) = L).card =
    (Finset.univ.filter fun F : Fin M → α =>
      (List.ofFn F).filter (fun a => decide (a ∈ T)) = L).card := by
  classical
  obtain ⟨e, he, hfix⟩ := audit_balanced_subset_permutation S T hcard
  have hLfix : L.map e = L := by
    calc
      L.map e = L.map id := (List.map_inj_left).mpr (by
        intro a ha
        exact hfix a ⟨fun _ => (hL a ha).2, fun _ => (hL a ha).1⟩)
      _ = L := List.map_id L
  have hf : ∀ l : List α,
      (l.map e).filter (fun a => decide (a ∈ T)) = L ↔
        l.filter (fun a => decide (a ∈ S)) = L := by
    intro l
    rw [audit_filter_map_equiv S T e he]
    constructor
    · intro h
      apply e.injective.list_map
      simpa [hLfix] using h
    · intro h
      simpa [h, hLfix]
  let Eseq : (Fin M → α) ≃ (Fin M → α) := Equiv.piCongrRight (fun _ => e)
  have hiff (F : Fin M → α) :
      (List.ofFn F).filter (fun a => decide (a ∈ S)) = L ↔
      (List.ofFn (Eseq F)).filter (fun a => decide (a ∈ T)) = L := by
    have hh := (hf (List.ofFn F)).symm
    have hE : Eseq F = (fun i => e (F i)) := by
      funext i
      rfl
    rw [hE]
    simpa only [List.map_ofFn, Function.comp_def] using hh
  let P : (Fin M → α) → Prop := fun F =>
    (List.ofFn F).filter (fun a => decide (a ∈ S)) = L
  let Q : (Fin M → α) → Prop := fun F =>
    (List.ofFn F).filter (fun a => decide (a ∈ T)) = L
  have h := Fintype.card_congr (Equiv.subtypeEquiv (p := P) (q := Q) Eseq hiff)
  simpa only [Fintype.card_subtype] using h

/-- The retained-list fibers have exactly equal cardinality for any two starts
that satisfy the retained list, even when the sample space is empty. -/
theorem audit_fixed_retained_count_equal {n k : ℕ} (z z' : Fin n → Bool)
    (F : List (ProperClause n k)) (M : ℕ)
    (hF : ∀ C ∈ F, ClauseSat z C.1 ∧ ClauseSat z' C.1) :
    (Finset.univ.filter fun G : Fin M → ProperClause n k =>
      (List.ofFn G).filter (fun C => decide (ClauseSat z C.1)) = F).card =
    (Finset.univ.filter fun G : Fin M → ProperClause n k =>
      (List.ofFn G).filter (fun C => decide (ClauseSat z' C.1)) = F).card := by
  let S : Finset (ProperClause n k) := Finset.univ.filter fun C => ClauseSat z C.1
  let T : Finset (ProperClause n k) := Finset.univ.filter fun C => ClauseSat z' C.1
  have hbad := audit_falsified_clause_card_invariant (k := k) z z'
  have hS := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ProperClause n k)))
      (p := fun C => ClauseSat z C.1)
  have hT := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ProperClause n k)))
      (p := fun C => ClauseSat z' C.1)
  have hcard : S.card = T.card := by dsimp [S, T]; omega
  have hcommon : ∀ C ∈ F, C ∈ S ∧ C ∈ T := by
    intro C hC
    simpa [S, T] using hF C hC
  have h := audit_fixed_filter_common_count S T hcard F hcommon M
  simpa [S, T] using h

end KSATSingleFlip.Connect


-- Component: AuditKSATFiniteFiberGrouping.lean

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- A finite joint law whose record fibers have constant size on valid
starting states can be grouped by record and valid starting state. -/
theorem audit_finite_fiber_grouping {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (ret : A → B → C) (valid : C → A → Prop) (weight : C → ℝ)
    (hw : ∀ c a, ((Finset.univ.filter fun b => ret a b = c).card : ℝ) =
      if valid c a then weight c else 0)
    (f : C → A → ℝ) :
    (∑ a : A, ∑ b : B, f (ret a b) a) =
      ∑ c : C, weight c * ∑ a ∈ (Finset.univ.filter fun a => valid c a), f c a := by
  classical
  have hgroup (a : A) : (∑ b : B, f (ret a b) a) =
      ∑ c : C, ((Finset.univ.filter fun b => ret a b = c).card : ℝ) * f c a := by
    symm
    calc
      _ = ∑ c : C, ∑ b ∈ (Finset.univ.filter fun b => ret a b = c), f c a := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [nsmul_eq_mul]
      _ = ∑ c : C, ∑ b ∈ (Finset.univ.filter fun b => ret a b = c), f (ret a b) a := by
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro b hb
        rw [(Finset.mem_filter.mp hb).2]
      _ = _ := Finset.sum_fiberwise Finset.univ (ret a) (fun b => f (ret a b) a)
  simp_rw [hgroup, hw]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp_all

end KSATSingleFlip.Connect


-- Component: AuditKSATPlantedReduction.lean

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


-- Component: AuditKSATGlauberSymmetry.lean

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


-- Component: AuditKSATStationarity.lean

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


-- Component: AuditKSATGlauberStationarity.lean

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


-- Component: AuditKSATIteratedStationarity.lean

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


-- Component: AuditKSATPlantedStationarity.lean

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Conditional planting identity at a fixed formula: averaging over uniformly
chosen initial assignments supported on its solutions leaves each solution's
probability unchanged after any fixed number of Glauber steps. -/
theorem audit_glauber_planted_column {n : ℕ} (hn : 0 < n)
    (Φ : GFormula (Fin n)) (t : ℕ) (y : Fin n → Bool) :
    (∑ z ∈ sols Φ, uprob (fun s : Fin t → Fin n × Bool => glauberState Φ z s = y)) =
      if y ∈ sols Φ then 1 else 0 := by
  classical
  let S := sols Φ
  let P : (Fin n → Bool) → ℝ := fun z =>
    uexp (fun s : Fin t → Fin n × Bool => if glauberState Φ z s = y then 1 else 0)
  have hstation := audit_glauber_uniform_stationary_iter hn Φ (fun z => if z = y then 1 else 0) t
  have hleft : (∑ z : ↥S, P z.1) = ∑ z ∈ S, P z := by
    symm
    exact Finset.sum_subtype S (fun z => Iff.rfl) P
  have hright : (∑ z : ↥S, if z.1 = y then (1 : ℝ) else 0) = if y ∈ S then 1 else 0 := by
    have hsum : (∑ z ∈ S, if z = y then (1 : ℝ) else 0) =
        ∑ z : ↥S, if z.1 = y then (1 : ℝ) else 0 :=
      Finset.sum_subtype S (fun z => Iff.rfl) (fun z => if z = y then (1 : ℝ) else 0)
    rw [← hsum]
    simpa using Finset.sum_ite_eq' S y (fun _ => (1 : ℝ))
  have hstat' : (∑ z : ↥S, P z.1) / (Fintype.card ↥S : ℝ) =
      (∑ z : ↥S, if z.1 = y then (1 : ℝ) else 0) / (Fintype.card ↥S : ℝ) := by
    simpa only [uexp, P, S] using hstation
  rw [hleft, hright] at hstat'
  by_cases hS : S.Nonempty
  · have hc : (Fintype.card ↥S : ℝ) ≠ 0 := by
      have : 0 < Fintype.card ↥S := Fintype.card_pos_iff.mpr ⟨⟨hS.choose, hS.choose_spec⟩⟩
      exact_mod_cast (ne_of_gt this)
    have heq := congrArg (fun z : ℝ => z * (Fintype.card ↥S : ℝ)) hstat'
    field_simp at heq
    dsimp [S, P] at heq
    convert heq using 1
    apply Finset.sum_congr rfl
    intro z hz
    unfold uprob uexp
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only
    split_ifs <;> simp_all
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [S, he] at *

/-- The unnormalised uniform measure on a fixed solution set is invariant. -/
theorem audit_glauber_unnormalized_stationary {n : ℕ} (hn : 0 < n)
    (Φ : GFormula (Fin n)) (t : ℕ) (f : (Fin n → Bool) → ℝ) :
    (∑ z ∈ sols Φ, uexp (fun s : Fin t → Fin n × Bool => f (glauberState Φ z s))) =
      ∑ z ∈ sols Φ, f z := by
  let S := sols Φ
  let P : (Fin n → Bool) → ℝ := fun z => uexp (fun s : Fin t → Fin n × Bool => f (glauberState Φ z s))
  have hstation := audit_glauber_uniform_stationary_iter hn Φ f t
  have hleft : (∑ z : ↥S, P z.1) = ∑ z ∈ S, P z := by
    symm
    exact Finset.sum_subtype S (fun z => Iff.rfl) P
  have hright : (∑ z : ↥S, f z.1) = ∑ z ∈ S, f z := by
    symm
    exact Finset.sum_subtype S (fun z => Iff.rfl) f
  have hstat' : (∑ z : ↥S, P z.1) / (Fintype.card ↥S : ℝ) =
      (∑ z : ↥S, f z.1) / (Fintype.card ↥S : ℝ) := by
    simpa only [uexp, P, S] using hstation
  rw [hleft, hright] at hstat'
  by_cases hS : S.Nonempty
  · have hc : (Fintype.card ↥S : ℝ) ≠ 0 := by
      have : 0 < Fintype.card ↥S := Fintype.card_pos_iff.mpr ⟨⟨hS.choose, hS.choose_spec⟩⟩
      exact_mod_cast ne_of_gt this
    have heq := congrArg (fun z : ℝ => z * (Fintype.card ↥S : ℝ)) hstat'
    field_simp at heq
    exact heq
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [S, he] at *

/-- A joint law with formula-dependent weights and uniform weight on each
satisfying start is unchanged by running Glauber dynamics. -/
theorem audit_glauber_weighted_joint_stationary {n : ℕ} (hn : 0 < n)
    {A : Type} [Fintype A] (formula : A → GFormula (Fin n)) (weight : A → ℝ)
    (t : ℕ) (f : A → (Fin n → Bool) → ℝ) :
    (∑ a, weight a * ∑ z ∈ sols (formula a),
      uexp (fun s : Fin t → Fin n × Bool => f a (glauberState (formula a) z s))) =
    ∑ a, weight a * ∑ z ∈ sols (formula a), f a z := by
  apply Finset.sum_congr rfl
  intro a _
  rw [audit_glauber_unnormalized_stationary hn (formula a) t (f a)]

end KSATSingleFlip.Connect


-- Component: AuditKSATFixedJointStationarity.lean

set_option maxHeartbeats 400000
noncomputable section
open scoped Classical BigOperators
open OAI.FixedClauseThreshold
namespace KSATSingleFlip.Connect

/-- The ordered clause list retained by a start assignment. -/
def auditFixedRetain {n k M : ℕ} (z : Fin n → Bool) (G : Fin M → ProperClause n k) :
    List (ProperClause n k) :=
  (List.ofFn G).filter (fun C => decide (ClauseSat z C.1))

/-- Finite set of all lists that can arise at a fixed clause count. -/
def auditFixedRecords (n k M : ℕ) : Finset (List (ProperClause n k)) :=
  (Finset.univ : Finset ((Fin n → Bool) × (Fin M → ProperClause n k))).image
    fun p => auditFixedRetain p.1 p.2

def auditFixedRecord {n k M : ℕ} (z : Fin n → Bool) (G : Fin M → ProperClause n k) :
    ↥(auditFixedRecords n k M) :=
  ⟨auditFixedRetain z G, Finset.mem_image.mpr ⟨(z,G), Finset.mem_univ _, rfl⟩⟩

theorem audit_fixed_retain_satisfies {n k M : ℕ} (z : Fin n → Bool)
    (G : Fin M → ProperClause n k) : FSat z (ofList (auditFixedRetain z G)) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
  exact of_decide_eq_true (List.mem_filter.mp hD).2

/-- A fixed retained record has a witness start and source sequence. -/
theorem audit_fixed_record_has_witness {n k M : ℕ} (F : ↥(auditFixedRecords n k M)) :
    ∃ (z : Fin n → Bool) (G : Fin M → ProperClause n k), auditFixedRetain z G = F.1 := by
  obtain ⟨⟨z,G⟩, _, h⟩ := Finset.mem_image.mp F.2
  exact ⟨z, G, h⟩

noncomputable def auditFixedRecordWitness {n k M : ℕ} (F : ↥(auditFixedRecords n k M)) : Fin n → Bool :=
  Classical.choose (audit_fixed_record_has_witness F)

theorem audit_fixed_record_witness_sat {n k M : ℕ} (F : ↥(auditFixedRecords n k M)) :
    FSat (auditFixedRecordWitness F) (ofList F.1) := by
  obtain ⟨G, hG⟩ := Classical.choose_spec (audit_fixed_record_has_witness F)
  rw [← hG]
  exact audit_fixed_retain_satisfies _ _

noncomputable def auditFixedWeight {n k M : ℕ} (F : ↥(auditFixedRecords n k M)) : ℝ :=
  ((Finset.univ.filter fun G : Fin M → ProperClause n k =>
    auditFixedRetain (auditFixedRecordWitness F) G = F.1).card : ℝ)

/-- The fiber count is constant across satisfying starts and zero otherwise. -/
theorem audit_fixed_record_weight {n k M : ℕ} (F : ↥(auditFixedRecords n k M)) (z : Fin n → Bool) :
    ((Finset.univ.filter fun G => auditFixedRecord z G = F).card : ℝ) =
      if FSat z (ofList F.1) then auditFixedWeight F else 0 := by
  classical
  have hfilters : (Finset.univ.filter fun G => auditFixedRecord z G = F) =
      (Finset.univ.filter fun G : Fin M → ProperClause n k => auditFixedRetain z G = F.1) := by
    ext G
    simp [auditFixedRecord, Subtype.ext_iff]
  rw [hfilters]
  by_cases hz : FSat z (ofList F.1)
  · have hw := audit_fixed_record_witness_sat F
    have hcommon : ∀ C ∈ F.1, ClauseSat z C.1 ∧ ClauseSat (auditFixedRecordWitness F) C.1 := by
      intro C hC
      exact ⟨hz C.1 (List.mem_map.mpr ⟨C, hC, rfl⟩),
        hw C.1 (List.mem_map.mpr ⟨C, hC, rfl⟩)⟩
    have hc := audit_fixed_retained_count_equal z (auditFixedRecordWitness F) F.1 M hcommon
    simp only [hz, if_true, auditFixedWeight]
    exact_mod_cast hc
  · have hnone : ∀ G : Fin M → ProperClause n k, auditFixedRetain z G ≠ F.1 := by
      intro G hG
      apply hz
      rw [← hG]
      exact audit_fixed_retain_satisfies z G
    simp [hz, hnone]

/-- At every fixed clause count, retaining satisfied clauses and then running
Glauber dynamics preserves the joint law under a uniform initial assignment. -/
theorem audit_fixed_retained_joint_stationarity {n k M : ℕ} (hn : 0 < n) (t : ℕ)
    (f : ↥(auditFixedRecords n k M) → (Fin n → Bool) → ℝ) :
    (∑ z : Fin n → Bool, ∑ G : Fin M → ProperClause n k,
      uexp (fun s : Fin t → Fin n × Bool =>
        f (auditFixedRecord z G) (glauberState (ofList (auditFixedRecord z G).1) z s))) =
    ∑ z : Fin n → Bool, ∑ G : Fin M → ProperClause n k, f (auditFixedRecord z G) z := by
  classical
  let valid : ↥(auditFixedRecords n k M) → (Fin n → Bool) → Prop :=
    fun F z => FSat z (ofList F.1)
  let Ret : (Fin n → Bool) → (Fin M → ProperClause n k) → ↥(auditFixedRecords n k M) :=
    fun z G => auditFixedRecord z G
  let W : ↥(auditFixedRecords n k M) → ℝ := fun F => auditFixedWeight F
  have hw : ∀ F z, ((Finset.univ.filter fun G => Ret z G = F).card : ℝ) =
      if valid F z then W F else 0 := by
    exact audit_fixed_record_weight
  have hleft := audit_finite_fiber_grouping (A := Fin n → Bool) (B := Fin M → ProperClause n k)
    (C := ↥(auditFixedRecords n k M)) Ret valid W (by
      intro F z
      have hraw := audit_fixed_record_weight (n := n) (k := k) (M := M) F z
      by_cases hz : FSat z (ofList F.1)
      · simp only [hz, if_true] at hraw
        simpa only [Ret, valid, W, hz, if_true] using hraw
      · simp only [hz, if_false] at hraw
        simpa only [Ret, valid, W, hz, if_false] using hraw)
    (fun F z => uexp (fun s : Fin t → Fin n × Bool => f F (glauberState (ofList F.1) z s)))
  have hright := audit_finite_fiber_grouping (A := Fin n → Bool) (B := Fin M → ProperClause n k)
    (C := ↥(auditFixedRecords n k M)) Ret valid W (by
      intro F z
      have hraw := audit_fixed_record_weight (n := n) (k := k) (M := M) F z
      by_cases hz : FSat z (ofList F.1)
      · simp only [hz, if_true] at hraw
        simpa only [Ret, valid, W, hz, if_true] using hraw
      · simp only [hz, if_false] at hraw
        simpa only [Ret, valid, W, hz, if_false] using hraw) f
  rw [hleft, hright]
  apply Finset.sum_congr rfl
  intro F hF
  congr 1
  change (∑ z ∈ sols (ofList F.1), uexp (fun s : Fin t → Fin n × Bool =>
      f F (glauberState (ofList F.1) z s))) = ∑ z ∈ sols (ofList F.1), f F z
  exact audit_glauber_unnormalized_stationary hn (ofList F.1) t (f F)

/-- Fixed-count stationarity for every event of the ordered retained formula
and Glauber endpoint. -/
theorem audit_fixed_retained_event_stationary {n k M : ℕ} (hn : 0 < n) (t : ℕ)
    (P : GFormula (Fin n) → (Fin n → Bool) → Prop) :
    (∑ z : Fin n → Bool, ∑ G : Fin M → ProperClause n k,
      uprob (fun s : Fin t → Fin n × Bool =>
        P (ofList (auditFixedRetain z G)) (glauberState (ofList (auditFixedRetain z G)) z s))) =
    ∑ z : Fin n → Bool, ∑ G : Fin M → ProperClause n k,
      if P (ofList (auditFixedRetain z G)) z then (1 : ℝ) else 0 := by
  classical
  have h := audit_fixed_retained_joint_stationarity (n := n) (k := k) (M := M) hn t
    (fun F z => if P (ofList F.1) z then (1 : ℝ) else 0)
  convert h using 1
  · apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro G _
    unfold uprob
    congr 1
  · apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro G _
    dsimp [auditFixedRecord]
    split_ifs <;> simp_all

end KSATSingleFlip.Connect


-- Component: AuditKSATRetainedRepresentation.lean

open scoped Classical BigOperators
open OAI.FixedClauseThreshold
namespace KSATSingleFlip.Connect

/-- Sampling from the subtype of the universal clause set is the same
as sampling directly from the clause type. -/
theorem audit_uexp_univ_sequences {α : Type} [Fintype α] (M : ℕ) (f : List α → ℝ) :
    uexp (fun G : Fin M → ↥(Finset.univ : Finset α) => f (List.ofFn fun i => (G i).1)) =
      uexp (fun G : Fin M → α => f (List.ofFn G)) := by
  let E : (Fin M → ↥(Finset.univ : Finset α)) ≃ (Fin M → α) :=
    Equiv.piCongrRight (fun _ => Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _))
  unfold uexp
  rw [Fintype.card_congr E]
  congr 1
  have h := E.sum_comp (fun G : Fin M → α => f (List.ofFn G))
  convert h using 1
  apply Finset.sum_congr rfl
  intro G _
  congr 1

/-- Index-based retained subformulas agree with filtering the ordered proper
clause list; duplicate occurrences remain distinct. -/
theorem audit_retained_ofList {n k : ℕ} (l : List (ProperClause n k)) (z : Fin n → Bool) :
    subF (ofList l) (satIdx (ofList l) z) =
      ofList (l.filter (fun C => decide (ClauseSat z C.1))) := by
  rw [audit_subF_satIdx_eq_satBy]
  unfold satBy ofList
  rw [List.filter_map]
  rfl

end KSATSingleFlip.Connect

namespace KSATSingleFlip.Connect

theorem audit_uexp_two_sums {A B : Type} [Fintype A] [Fintype B] (f g : A → B → ℝ)
    (h : (∑ a, ∑ b, f a b) = ∑ a, ∑ b, g a b) :
    uexp (fun a => uexp (f a)) = uexp (fun a => uexp (g a)) := by
  unfold uexp
  simp only [← Finset.sum_div]
  rw [h]

/-- Joint invariance under a uniform start for any fixed clause count. -/
theorem audit_fixed_retained_uprob_stationary {n k M : ℕ} (hn : 0 < n) (t : ℕ)
    (P : GFormula (Fin n) → (Fin n → Bool) → Prop) :
    uexp (fun z : Fin n → Bool => uexp (fun G : Fin M → ProperClause n k =>
      uprob (fun s : Fin t → Fin n × Bool =>
        P (ofList (auditFixedRetain z G)) (glauberState (ofList (auditFixedRetain z G)) z s)))) =
    uexp (fun z : Fin n → Bool => uprob (fun G : Fin M → ProperClause n k =>
      P (ofList (auditFixedRetain z G)) z)) := by
  classical
  have h := audit_fixed_retained_event_stationary (n := n) (k := k) (M := M) hn t P
  have h' := audit_uexp_two_sums
    (fun z G => uprob (fun s : Fin t → Fin n × Bool =>
      P (ofList (auditFixedRetain z G)) (glauberState (ofList (auditFixedRetain z G)) z s)))
    (fun z G => if P (ofList (auditFixedRetain z G)) z then (1 : ℝ) else 0) h
  simpa only [uprob] using h'

end KSATSingleFlip.Connect


-- Component: AuditKSATPoissonInterchange.lean

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- A bounded finite expectation commutes with the Poisson count mixture. -/
theorem audit_uexp_pois_interchange {A : Type} [Fintype A] (m : ℝ) (hm : 0 ≤ m)
    (f : A → ℕ → ℝ) (hf : ∀ a j, 0 ≤ f a j ∧ f a j ≤ 1) :
    uexp (fun a => ∑' j, poisW m j * f a j) =
      ∑' j, poisW m j * uexp (fun a => f a j) := by
  have hw : Summable (fun j => poisW m j) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp m).summable.mul_left (Real.exp (-m))
    simpa only [poisW, mul_div_assoc] using h
  have hw0 (j : ℕ) : 0 ≤ poisW m j := by
    unfold poisW
    positivity
  have hs (a : A) : Summable (fun j => poisW m j * f a j) := by
    apply Summable.of_nonneg_of_le _ _ hw
    · intro j
      exact mul_nonneg (hw0 j) (hf a j).1
    · intro j
      nlinarith [(hf a j).2, hw0 j]
  unfold uexp
  rw [← Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) => hs a), ← tsum_div_const]
  apply tsum_congr
  intro j
  rw [← Finset.mul_sum]
  ring

end KSATSingleFlip.Connect


-- Component: AuditKSATProbabilityMono.lean

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Uniform finite expectations are monotone, including on an empty type. -/
theorem audit_uexp_mono {β : Type} [Fintype β] (f g : β → ℝ)
    (h : ∀ x, f x ≤ g x) : uexp f ≤ uexp g := by
  unfold uexp
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (Nat.cast_nonneg _)

/-- An event probability is in [0,1], including on an empty sample space. -/
theorem audit_uprob_bounds {β : Type} [Fintype β] (P : β → Prop) :
    0 ≤ uprob P ∧ uprob P ≤ 1 := by
  classical
  have h0 : 0 ≤ uprob P := by
    unfold uprob uexp
    positivity
  have h1 : uprob P ≤ uexp (fun _ : β => (1 : ℝ)) :=
    audit_uexp_mono _ _ (fun x => by split <;> norm_num)
  have hconst : uexp (fun _ : β => (1 : ℝ)) ≤ 1 := by
    unfold uexp
    by_cases h : Fintype.card β = 0
    · simp [h]
    · have hp : (0 : ℝ) < Fintype.card β := by exact_mod_cast (Nat.pos_of_ne_zero h)
      simp [ne_of_gt hp]
  exact ⟨h0, h1.trans hconst⟩

/-- Poisson expectations of [0,1]-valued functions are monotone. -/
theorem audit_poisExp_mono {α : Type} [DecidableEq α] (S : Finset α) (m : ℝ)
    (hm : 0 ≤ m) (f g : List α → ℝ)
    (hf0 : ∀ l, 0 ≤ f l) (hg1 : ∀ l, g l ≤ 1)
    (hfg : ∀ l, f l ≤ g l) : poisExp S m f ≤ poisExp S m g := by
  let A : ℕ → ℝ := fun N => poisW m N * uexp (fun F : Fin N → S => f (List.ofFn fun i => (F i).1))
  let B : ℕ → ℝ := fun N => poisW m N * uexp (fun F : Fin N → S => g (List.ofFn fun i => (F i).1))
  have hw : ∀ N, 0 ≤ poisW m N := by intro N; unfold poisW; positivity
  have hA0 : ∀ N, 0 ≤ A N := by
    intro N
    apply mul_nonneg (hw N)
    unfold uexp
    apply div_nonneg _ (Nat.cast_nonneg _)
    exact Finset.sum_nonneg (fun F _ => hf0 _)
  have hAB : ∀ N, A N ≤ B N := by
    intro N
    exact mul_le_mul_of_nonneg_left (audit_uexp_mono _ _ (fun F => hfg _)) (hw N)
  have hBup : ∀ N, B N ≤ poisW m N := by
    intro N
    have hmean : uexp (fun F : Fin N → S => g (List.ofFn fun i => (F i).1)) ≤ 1 := by
      have h := audit_uexp_mono (fun F : Fin N → S => g (List.ofFn fun i => (F i).1)) (fun _ => 1) (fun F => hg1 _)
      have hc : uexp (fun _ : Fin N → S => (1 : ℝ)) ≤ 1 := by
        unfold uexp
        by_cases he : Fintype.card (Fin N → S) = 0
        · simp [he]
        · have hp : (0 : ℝ) < Fintype.card (Fin N → S) := by exact_mod_cast (Nat.pos_of_ne_zero he)
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          exact (div_le_one₀ hp).mpr le_rfl
      exact h.trans hc
    calc
      B N ≤ poisW m N * 1 := mul_le_mul_of_nonneg_left hmean (hw N)
      _ = poisW m N := mul_one _
  have hs : Summable (fun N => poisW m N) := by
    have h := (Real.summable_pow_div_factorial m).mul_left (Real.exp (-m))
    simpa only [poisW, mul_div_assoc] using h
  have hsB : Summable B := Summable.of_nonneg_of_le (fun N => le_trans (hA0 N) (hAB N)) hBup hs
  have hsA : Summable A := Summable.of_nonneg_of_le hA0 hAB hsB
  exact Summable.tsum_le_tsum hAB hsA hsB

end KSATSingleFlip.Connect


-- Component: AuditKSATLem78Complete.lean

set_option maxHeartbeats 1500000
open scoped Classical BigOperators
open OAI.FixedClauseThreshold
namespace KSATSingleFlip.Connect

theorem audit_uexp_unit_bounds {A : Type} [Fintype A] (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) : 0 ≤ uexp f ∧ uexp f ≤ 1 := by
  constructor
  · unfold uexp
    exact div_nonneg (Finset.sum_nonneg fun a ha => (hf a).1) (Nat.cast_nonneg _)
  · have h := audit_uexp_mono f (fun _ => 1) (fun a => (hf a).2)
    have hconst : uexp (fun _ : A => (1 : ℝ)) ≤ 1 := by
      unfold uexp
      by_cases hc : Fintype.card A = 0
      · simp [hc]
      · have hp : (0 : ℝ) < Fintype.card A := by exact_mod_cast Nat.pos_of_ne_zero hc
        simp [ne_of_gt hp]
    exact h.trans hconst

/-- Lemma 7.8: the exact retained-formula/Glauber-state joint law is invariant. -/
theorem audit_lemma_7_8 {n k : ℕ} (hn : 0 < n) (m : ℝ) (hm : 0 ≤ m) (t : ℕ)
    (P : GFormula (Fin n) → (Fin n → Bool) → Prop) :
    uexp (fun z : Fin n → Bool =>
      poisExp (allClauses n k) m (fun l =>
        uprob fun s : Fin t → Fin n × Bool =>
          let Φ0 := subF (ofList l) (satIdx (ofList l) z)
          P Φ0 (glauberState Φ0 z s))) =
    uexp (fun z : Fin n → Bool =>
      poisProb (allClauses n k) m (fun l =>
        let Φ0 := subF (ofList l) (satIdx (ofList l) z)
        P Φ0 z)) := by
  classical
  let L : (Fin n → Bool) → ℕ → ℝ := fun z M =>
    uexp (fun G : Fin M → ↥(allClauses n k) =>
      uprob fun s : Fin t → Fin n × Bool =>
        let l := List.ofFn fun i => (G i).1
        let Φ0 := subF (ofList l) (satIdx (ofList l) z)
        P Φ0 (glauberState Φ0 z s))
  let R : (Fin n → Bool) → ℕ → ℝ := fun z M =>
    uexp (fun G : Fin M → ↥(allClauses n k) =>
      let l := List.ofFn fun i => (G i).1
      let Φ0 := subF (ofList l) (satIdx (ofList l) z)
      if P Φ0 z then (1 : ℝ) else 0)
  have hL : ∀ z M, 0 ≤ L z M ∧ L z M ≤ 1 := by
    intro z M
    apply audit_uexp_unit_bounds
    intro G
    exact audit_uprob_bounds _
  have hR : ∀ z M, 0 ≤ R z M ∧ R z M ≤ 1 := by
    intro z M
    apply audit_uexp_unit_bounds
    intro G
    dsimp
    split_ifs <;> norm_num
  have hfixed (M : ℕ) : uexp (fun z => L z M) = uexp (fun z => R z M) := by
    have heL (z : Fin n → Bool) : L z M =
        uexp (fun G : Fin M → ProperClause n k =>
          uprob fun s : Fin t → Fin n × Bool =>
            P (ofList (auditFixedRetain z G)) (glauberState (ofList (auditFixedRetain z G)) z s)) := by
      have h := audit_uexp_univ_sequences M (fun l : List (ProperClause n k) =>
        uprob fun s : Fin t → Fin n × Bool =>
          P (subF (ofList l) (satIdx (ofList l) z))
            (glauberState (subF (ofList l) (satIdx (ofList l) z)) z s))
      simp only [allClauses, audit_retained_ofList, auditFixedRetain] at h
      simp only [L, allClauses, audit_retained_ofList, auditFixedRetain]
      convert h using 1 <;> congr 1 <;> funext G <;> congr 1 <;> funext s <;> split_ifs <;> simp_all
    have heR (z : Fin n → Bool) : R z M =
        uprob (fun G : Fin M → ProperClause n k => P (ofList (auditFixedRetain z G)) z) := by
      have h := audit_uexp_univ_sequences M (fun l : List (ProperClause n k) =>
        if P (subF (ofList l) (satIdx (ofList l) z)) z then (1 : ℝ) else 0)
      simp only [allClauses, audit_retained_ofList, auditFixedRetain] at h
      simp only [R, uprob, allClauses, audit_retained_ofList, auditFixedRetain]
      convert h using 1 <;> congr 1 <;> funext G <;> split_ifs <;> simp_all
    simp_rw [heL, heR]
    exact audit_fixed_retained_uprob_stationary hn t P
  change uexp (fun z => ∑' M, poisW m M * L z M) =
    uexp (fun z => ∑' M, poisW m M * R z M)
  rw [audit_uexp_pois_interchange m hm L hL, audit_uexp_pois_interchange m hm R hR]
  apply tsum_congr
  intro M
  rw [hfixed]

end KSATSingleFlip.Connect



open scoped Classical BigOperators
open OAI.FixedClauseThreshold KSATSingleFlip.Connect

theorem solution {n k M : ℕ} (hn : 0 < n) (t : ℕ)
    (P : GFormula (Fin n) → (Fin n → Bool) → Prop) :
    uexp (fun z : Fin n → Bool => uexp (fun G : Fin M → ProperClause n k =>
      uprob (fun s : Fin t → Fin n × Bool =>
        let Φ0 := subF (ofList (List.ofFn G)) (satIdx (ofList (List.ofFn G)) z)
        P Φ0 (glauberState Φ0 z s)))) =
    uexp (fun z : Fin n → Bool => uprob (fun G : Fin M → ProperClause n k =>
      let Φ0 := subF (ofList (List.ofFn G)) (satIdx (ofList (List.ofFn G)) z)
      P Φ0 z)) := by
  have h := audit_fixed_retained_uprob_stationary (n := n) (k := k) (M := M) hn t P
  simp only [audit_retained_ofList, auditFixedRetain] at *
  exact h

#print axioms solution
