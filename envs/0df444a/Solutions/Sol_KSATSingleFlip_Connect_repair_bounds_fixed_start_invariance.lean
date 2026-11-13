-- Prove2me | solution 1 for KSATSingleFlip.Connect.repair_bounds_fixed_start_invariance
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:45:36.566405+00:00
-- url     : https://prove2.me/submissions/74b5120d-1411-4242-8ad1-376d4b8f3be9

import Definitions.Def_KSATSingleFlip_Connect_Repair
import Definitions.Def_KSATSingleFlip_Connect_Glauber



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


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Clause occurrences retain their numeric positions under a sign flip. -/
noncomputable def audit_twist_index {n : ℕ} (a : Fin n → Bool) (Φ : GFormula (Fin n)) :
    Fin Φ.length ≃ Fin (audit_twist_formula a Φ).length :=
  { toFun := fun c => ⟨c.val, by simpa [audit_twist_formula] using c.isLt⟩
    invFun := fun c => ⟨c.val, by simpa [audit_twist_formula] using c.isLt⟩
    left_inv := by intro c; ext; rfl
    right_inv := by intro c; ext; rfl }

theorem audit_twist_get {n : ℕ} (a : Fin n → Bool) (Φ : GFormula (Fin n))
    (c : Fin Φ.length) :
    (audit_twist_formula a Φ).get (audit_twist_index a Φ c) = audit_twist_clause a (Φ.get c) := by
  simp only [audit_twist_formula, List.get_eq_getElem, List.getElem_map]
  rfl

/-- Reindex a forcing tree after simultaneous literal-sign and assignment flips. -/
noncomputable def audit_twist_tree {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (T : ForcingTree Φ x) : ForcingTree (audit_twist_formula a Φ) (audit_twist_assignment a x) where
  root := T.root
  vars := T.vars
  cls := T.cls.map (audit_twist_index a Φ).toEmbedding
  parent c := T.parent ((audit_twist_index a Φ).symm c)
  child c := T.child ((audit_twist_index a Φ).symm c)
  depth := T.depth
  root_mem := T.root_mem
  forces c hc := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
    unfold Forces
    rw [audit_twist_get, audit_twist_satSet]
    exact T.forces d hd
  parent_mem c hc := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    simpa using T.parent_mem d hd
  child_mem c hc := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    simpa using T.child_mem d hd
  child_vbl c hc := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply, audit_twist_get, audit_twist_scope]
    exact T.child_vbl d hd
  depth_root := T.depth_root
  depth_child c hc := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    simpa using T.depth_child d hd
  unique_parent u hu hroot := by
    obtain ⟨d, hd, huniq⟩ := T.unique_parent u hu hroot
    refine ⟨audit_twist_index a Φ d, ?_, ?_⟩
    · exact ⟨Finset.mem_map.mpr ⟨d, hd.1, rfl⟩, by simpa using hd.2⟩
    · intro c hc
      obtain ⟨e, he, heq⟩ := Finset.mem_map.mp hc.1
      have hechild : T.child e = u := by simpa [← heq] using hc.2
      have hed : e = d := huniq e ⟨he, hechild⟩
      calc
        c = (audit_twist_index a Φ) e := by simpa only [Equiv.toEmbedding_apply] using heq.symm
        _ = (audit_twist_index a Φ) d := by rw [hed]

/-- Completeness is preserved when the subformula positions are reindexed. -/
theorem audit_twist_tree_complete {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (T : ForcingTree Φ x) (h : T.CompleteIn I0) :
    (audit_twist_tree a x Φ T).CompleteIn (I0.map (audit_twist_index a Φ).toEmbedding) := by
  constructor
  · intro c hc
    obtain ⟨d, hd, heq⟩ := Finset.mem_map.mp hc
    exact Finset.mem_map.mpr ⟨d, h.1 hd, heq⟩
  · intro v hv c hc hf
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    simp only [Equiv.toEmbedding_apply] at hf ⊢
    have hf' : Forces x (Φ.get d) v := by
      unfold Forces at hf ⊢
      rw [audit_twist_get, audit_twist_satSet] at hf
      exact hf
    obtain ⟨hdT, heq⟩ := h.2 v hv d hd hf'
    exact ⟨Finset.mem_map.mpr ⟨d, hdT, rfl⟩, by simpa [audit_twist_tree] using heq⟩

/-- A complete small forcing tree avoiding B transports to the sign-flipped formula. -/
theorem audit_twist_has_small_CFT {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (u : Fin n) (size : ℝ) (B : Finset (Fin n))
    (h : HasSmallCFT Φ I0 x u size B) :
    HasSmallCFT (audit_twist_formula a Φ) (I0.map (audit_twist_index a Φ).toEmbedding)
      (audit_twist_assignment a x) u size B := by
  obtain ⟨T, hroot, hcomplete, hsize, hdisj⟩ := h
  refine ⟨audit_twist_tree a x Φ T, hroot, audit_twist_tree_complete a x Φ I0 T hcomplete, ?_, hdisj⟩
  exact hsize

/-- Reverse the sign-flipped forcing-tree transformation without changing the
ambient clause-list type by a dependent equality. -/
noncomputable def audit_untwist_tree {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (T : ForcingTree (audit_twist_formula a Φ) (audit_twist_assignment a x)) : ForcingTree Φ x where
  root := T.root
  vars := T.vars
  cls := T.cls.map (audit_twist_index a Φ).symm.toEmbedding
  parent c := T.parent (audit_twist_index a Φ c)
  child c := T.child (audit_twist_index a Φ c)
  depth := T.depth
  root_mem := T.root_mem
  forces c hc := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    have hd' := T.forces d hd
    unfold Forces at hd' ⊢
    have he : audit_twist_index a Φ ((audit_twist_index a Φ).symm d) = d := (audit_twist_index a Φ).apply_symm_apply d
    rw [← he, audit_twist_get, audit_twist_satSet] at hd'
    simpa using hd'
  parent_mem c hc := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    simpa using T.parent_mem d hd
  child_mem c hc := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    simpa using T.child_mem d hd
  child_vbl c hc := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    have he : audit_twist_index a Φ ((audit_twist_index a Φ).symm d) = d := (audit_twist_index a Φ).apply_symm_apply d
    have hd' := T.child_vbl d hd
    rw [← he, audit_twist_get, audit_twist_scope] at hd'
    simpa using hd'
  depth_root := T.depth_root
  depth_child c hc := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    simpa using T.depth_child d hd
  unique_parent u hu hroot := by
    obtain ⟨d, hd, huniq⟩ := T.unique_parent u hu hroot
    refine ⟨(audit_twist_index a Φ).symm d, ?_, ?_⟩
    · exact ⟨Finset.mem_map.mpr ⟨d, hd.1, rfl⟩, by simpa using hd.2⟩
    · intro c hc
      obtain ⟨e, he, heq⟩ := Finset.mem_map.mp hc.1
      have hechild : T.child e = u := by simpa [← heq] using hc.2
      have hed : e = d := huniq e ⟨he, hechild⟩
      calc
        c = (audit_twist_index a Φ).symm e := by simpa only [Equiv.toEmbedding_apply] using heq.symm
        _ = (audit_twist_index a Φ).symm d := by rw [hed]

/-- Completeness transports back to the original clause positions. -/
theorem audit_untwist_tree_complete {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length))
    (T : ForcingTree (audit_twist_formula a Φ) (audit_twist_assignment a x))
    (h : T.CompleteIn (I0.map (audit_twist_index a Φ).toEmbedding)) :
    (audit_untwist_tree a x Φ T).CompleteIn I0 := by
  constructor
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨e, he, heq⟩ := Finset.mem_map.mp (h.1 hd)
    have : e = (audit_twist_index a Φ).symm d := by
      apply (audit_twist_index a Φ).injective
      simpa using heq
    simpa [this] using he
  · intro v hv c hc hf
    have hc' : audit_twist_index a Φ c ∈ I0.map (audit_twist_index a Φ).toEmbedding :=
      Finset.mem_map.mpr ⟨c, hc, rfl⟩
    have hf' : Forces (audit_twist_assignment a x) ((audit_twist_formula a Φ).get (audit_twist_index a Φ c)) v := by
      unfold Forces at hf ⊢
      rw [audit_twist_get, audit_twist_satSet]
      exact hf
    obtain ⟨hcT, heq⟩ := h.2 v hv _ hc' hf'
    exact ⟨Finset.mem_map.mpr ⟨audit_twist_index a Φ c, hcT, by simp⟩, heq⟩

/-- Small complete forcing trees are invariant under sign flips. -/
theorem audit_twist_has_small_CFT_iff {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (u : Fin n) (size : ℝ) (B : Finset (Fin n)) :
    HasSmallCFT (audit_twist_formula a Φ) (I0.map (audit_twist_index a Φ).toEmbedding)
      (audit_twist_assignment a x) u size B ↔ HasSmallCFT Φ I0 x u size B := by
  constructor
  · rintro ⟨T, hroot, hcomplete, hsize, hdisj⟩
    exact ⟨audit_untwist_tree a x Φ T, hroot, audit_untwist_tree_complete a x Φ I0 T hcomplete, hsize, hdisj⟩
  · exact audit_twist_has_small_CFT a x Φ I0 u size B

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Sign flipping preserves the occurrence of an x-false literal. -/
theorem audit_twist_falseLit {n : ℕ} (a x : Fin n → Bool) (C : GClause (Fin n)) (v : Fin n) :
    FalseLitOn (audit_twist_assignment a x) (audit_twist_clause a C) v ↔ FalseLitOn x C v := by
  unfold FalseLitOn audit_twist_assignment audit_twist_clause
  cases hc : C v with
  | none => simp
  | some b =>
    simp only [Option.map_some, Option.some.injEq]
    cases ha : a v <;> cases hb : b <;> cases hx : x v <;> simp_all

/-- Forcing-clause positions are carried along by the sign-flip equivalence. -/
theorem audit_twist_Cforce_mem {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (c : Fin Φ.length) :
    audit_twist_index a Φ c ∈ Cforce (audit_twist_formula a Φ)
      (I0.map (audit_twist_index a Φ).toEmbedding) (audit_twist_assignment a x) ↔ c ∈ Cforce Φ I0 x := by
  unfold Cforce
  rw [Finset.mem_filter, Finset.mem_filter]
  change (audit_twist_index a Φ c ∈ I0.map (audit_twist_index a Φ).toEmbedding ∧
    (satSet (audit_twist_assignment a x) ((audit_twist_formula a Φ).get (audit_twist_index a Φ c))).card = 1) ↔
      (c ∈ I0 ∧ (satSet x (Φ.get c)).card = 1)
  rw [audit_twist_get, audit_twist_satSet]
  simp

theorem audit_twist_Cmulti_mem {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (c : Fin Φ.length) :
    audit_twist_index a Φ c ∈ Cmulti (audit_twist_formula a Φ) (audit_twist_assignment a x) ↔ c ∈ Cmulti Φ x := by
  unfold Cmulti
  rw [Finset.mem_filter, Finset.mem_filter]
  change (audit_twist_index a Φ c ∈ Finset.univ ∧
    2 ≤ (satSet (audit_twist_assignment a x) ((audit_twist_formula a Φ).get (audit_twist_index a Φ c))).card) ↔
      (c ∈ Finset.univ ∧ 2 ≤ (satSet x (Φ.get c)).card)
  rw [audit_twist_get, audit_twist_satSet]
  simp

/-- The NoTree count is invariant under simultaneous sign flips. -/
theorem audit_twist_NoTree {n : ℕ} (k : ℕ) (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (B : Finset (Fin n)) :
    NoTree k (audit_twist_formula a Φ) (I0.map (audit_twist_index a Φ).toEmbedding)
      (audit_twist_assignment a x) B = NoTree k Φ I0 x B := by
  unfold NoTree
  apply Finset.card_bij (fun c _ => (audit_twist_index a Φ).symm c)
  · intro c hc
    let d := (audit_twist_index a Φ).symm c
    have hc_eq : audit_twist_index a Φ d = c := (audit_twist_index a Φ).apply_symm_apply c
    rw [← hc_eq] at hc
    simpa only [Finset.mem_filter, Finset.mem_union, audit_twist_Cforce_mem, audit_twist_Cmulti_mem,
      audit_twist_get, audit_twist_satSet, audit_twist_falseLit, audit_twist_has_small_CFT_iff] using hc
  · intro c hc d hd he
    exact (audit_twist_index a Φ).symm.injective he
  · intro d hd
    refine ⟨audit_twist_index a Φ d, ?_, by simp⟩
    simpa only [Finset.mem_filter, Finset.mem_union, audit_twist_Cforce_mem, audit_twist_Cmulti_mem,
      audit_twist_get, audit_twist_satSet, audit_twist_falseLit, audit_twist_has_small_CFT_iff] using hd

/-- The forcing-clause count on any variable set is sign invariant. -/
theorem audit_twist_forcing_count {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (B : Finset (Fin n)) :
    (((Cforce (audit_twist_formula a Φ) (I0.map (audit_twist_index a Φ).toEmbedding)
      (audit_twist_assignment a x)).filter fun c => satSet (audit_twist_assignment a x) ((audit_twist_formula a Φ).get c) ⊆ B).card) =
    (((Cforce Φ I0 x).filter fun c => satSet x (Φ.get c) ⊆ B).card) := by
  apply Finset.card_bij (fun c _ => (audit_twist_index a Φ).symm c)
  · intro c hc
    let d := (audit_twist_index a Φ).symm c
    have hc_eq : audit_twist_index a Φ d = c := (audit_twist_index a Φ).apply_symm_apply c
    rw [← hc_eq] at hc
    simpa only [Finset.mem_filter, audit_twist_Cforce_mem, audit_twist_get, audit_twist_satSet] using hc
  · intro c hc d hd he
    exact (audit_twist_index a Φ).symm.injective he
  · intro d hd
    refine ⟨audit_twist_index a Φ d, ?_, by simp⟩
    simpa only [Finset.mem_filter, audit_twist_Cforce_mem, audit_twist_get, audit_twist_satSet] using hd

/-- Both weighted link counts are invariant under sign flips. -/
theorem audit_twist_ForcingLink {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (B : Finset (Fin n)) :
    ForcingLink (audit_twist_formula a Φ) (I0.map (audit_twist_index a Φ).toEmbedding)
      (audit_twist_assignment a x) B = ForcingLink Φ I0 x B := by
  unfold ForcingLink
  apply Finset.card_bij (fun c _ => (audit_twist_index a Φ).symm c)
  · intro c hc
    let d := (audit_twist_index a Φ).symm c
    have hc_eq : audit_twist_index a Φ d = c := (audit_twist_index a Φ).apply_symm_apply c
    rw [← hc_eq] at hc
    simpa only [Finset.mem_filter, audit_twist_Cforce_mem, audit_twist_get,
      audit_twist_satSet, audit_twist_falseLit] using hc
  · intro c hc d hd he
    exact (audit_twist_index a Φ).symm.injective he
  · intro d hd
    refine ⟨audit_twist_index a Φ d, ?_, by simp⟩
    simpa only [Finset.mem_filter, audit_twist_Cforce_mem, audit_twist_get,
      audit_twist_satSet, audit_twist_falseLit] using hd

theorem audit_twist_MultiLink {n : ℕ} (a x : Fin n → Bool) (Φ : GFormula (Fin n))
    (B : Finset (Fin n)) :
    MultiLink (audit_twist_formula a Φ) (audit_twist_assignment a x) B = MultiLink Φ x B := by
  unfold MultiLink
  apply Finset.card_bij (fun c _ => (audit_twist_index a Φ).symm c)
  · intro c hc
    let d := (audit_twist_index a Φ).symm c
    have hc_eq : audit_twist_index a Φ d = c := (audit_twist_index a Φ).apply_symm_apply c
    rw [← hc_eq] at hc
    simpa only [Finset.mem_filter, audit_twist_Cmulti_mem, audit_twist_get,
      audit_twist_satSet, audit_twist_falseLit] using hc
  · intro c hc d hd he
    exact (audit_twist_index a Φ).symm.injective he
  · intro d hd
    refine ⟨audit_twist_index a Φ d, ?_, by simp⟩
    simpa only [Finset.mem_filter, audit_twist_Cmulti_mem, audit_twist_get,
      audit_twist_satSet, audit_twist_falseLit] using hd

/-- All three small-set bounds are invariant under simultaneous sign flips. -/
theorem audit_twist_repairBounds_iff {n : ℕ} (k : ℕ) (a x : Fin n → Bool)
    (Φ : GFormula (Fin n)) (I0 : Finset (Fin Φ.length)) :
    RepairBounds k (audit_twist_formula a Φ) (I0.map (audit_twist_index a Φ).toEmbedding)
      (audit_twist_assignment a x) ↔ RepairBounds k Φ I0 x := by
  unfold RepairBounds
  simp only [audit_twist_NoTree, audit_twist_forcing_count, audit_twist_ForcingLink, audit_twist_MultiLink]

/-- The satisfied-position set is transported by the clause-index equivalence. -/
theorem audit_twist_satIdx {n : ℕ} (a z : Fin n → Bool) (Φ : GFormula (Fin n)) :
    satIdx (audit_twist_formula a Φ) (audit_twist_assignment a z) =
      (satIdx Φ z).map (audit_twist_index a Φ).toEmbedding := by
  ext c
  obtain ⟨d, rfl⟩ := (audit_twist_index a Φ).surjective c
  simp only [satIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.toEmbedding_apply]
  rw [audit_twist_get, audit_twist_clause_sat]
  constructor
  · intro hd
    exact ⟨d, hd, rfl⟩
  · rintro ⟨e, he, heq⟩
    have hed : e = d := (audit_twist_index a Φ).injective heq
    simpa [hed] using he

/-- The actual planted/Glauber RepairBounds event is equivariant under sign flips. -/
theorem audit_twist_actual_bounds {n t : ℕ} (k : ℕ) (a z : Fin n → Bool)
    (Φ : GFormula (Fin n)) (s : Fin t → Fin n × Bool) :
    RepairBounds k (audit_twist_formula a Φ)
      (satIdx (audit_twist_formula a Φ) (audit_twist_assignment a z))
      (glauberState (subF (audit_twist_formula a Φ)
        (satIdx (audit_twist_formula a Φ) (audit_twist_assignment a z)))
        (audit_twist_assignment a z) (fun i => audit_twist_update_input a (s i))) ↔
    RepairBounds k Φ (satIdx Φ z) (glauberState (subF Φ (satIdx Φ z)) z s) := by
  rw [← audit_twist_retained_subformula, audit_twist_glauber_state, audit_twist_satIdx,
    audit_twist_repairBounds_iff]

end KSATSingleFlip.Connect


noncomputable section
set_option maxHeartbeats 1000000

open scoped Classical BigOperators
open OAI.FixedClauseThreshold
namespace KSATSingleFlip.Connect

/-- Converting a sign-flipped proper-clause list agrees with flipping its generic formula. -/
theorem audit_twist_ofList {n k : ℕ} (a : Fin n → Bool) (l : List (ProperClause n k)) :
    ofList (l.map (audit_twist_proper a)) = audit_twist_formula a (ofList l) := by
  simp only [ofList, audit_twist_formula, List.map_map, Function.comp_def, audit_twist_proper]

/-- Probability that all repair bounds hold under the actual fixed-start law. -/
def audit_actual_bounds_probability {n : ℕ} (k : ℕ) (m : ℝ) (z : Fin n → Bool) (t : ℕ) : ℝ :=
  poisExp (allClauses n k) m (fun l =>
    uprob fun s : Fin t → Fin n × Bool =>
      let Φ := ofList l
      let I0 := satIdx Φ z
      let X := glauberState (subF Φ I0) z s
      RepairBounds k Φ I0 X)

/-- The actual-law RepairBounds probability is independent of the fixed start. -/
theorem audit_actual_bounds_start_invariant {n : ℕ} (k : ℕ) (m : ℝ)
    (z z' : Fin n → Bool) (t : ℕ) :
    audit_actual_bounds_probability k m z t = audit_actual_bounds_probability k m z' t := by
  classical
  let a : Fin n → Bool := fun v => z v ^^ z' v
  have ha : audit_twist_assignment a z = z' := by
    funext v
    dsimp [audit_twist_assignment, a]
    cases hz : z v <;> cases hz' : z' v <;> rfl
  let P : (Fin n → Bool) → List (ProperClause n k) → (Fin t → Fin n × Bool) → Prop := fun q l s =>
    let Φ := ofList l
    let I0 := satIdx Φ q
    let X := glauberState (subF Φ I0) q s
    RepairBounds k Φ I0 X
  have hp : ∀ l s, P z' (l.map (audit_twist_proper a)) (fun i => audit_twist_update_input a (s i)) ↔ P z l s := by
    intro l s
    dsimp only [P]
    rw [audit_twist_ofList, ← ha]
    exact audit_twist_actual_bounds k a z (ofList l) s
  have hseq : ∀ l, uprob (P z' (l.map (audit_twist_proper a))) = uprob (P z l) := by
    intro l
    unfold uprob
    calc
      uexp (fun s : Fin t → Fin n × Bool => if P z' (l.map (audit_twist_proper a)) s then (1 : ℝ) else 0) =
          uexp (fun s : Fin t → Fin n × Bool => if P z' (l.map (audit_twist_proper a))
            (fun i => audit_twist_update_input a (s i)) then (1 : ℝ) else 0) :=
        (audit_glauber_input_sign_invariant a _).symm
      _ = uexp (fun s : Fin t → Fin n × Bool => if P z l s then (1 : ℝ) else 0) := by
        congr 1
        funext s
        rw [hp]
  unfold audit_actual_bounds_probability
  change poisExp (allClauses n k) m (fun l => uprob (P z l)) =
    poisExp (allClauses n k) m (fun l => uprob (P z' l))
  calc
    _ = poisExp (allClauses n k) m (fun l => uprob (P z' (l.map (audit_twist_proper a)))) := by
      congr 1
      funext l
      exact (hseq l).symm
    _ = _ := audit_pois_formula_sign_invariant (k := k) a m (fun l : List (ProperClause n k) => uprob (P z' l))

/-- The fixed-start probability equals its average over a uniform start. -/
theorem audit_actual_bounds_equals_uniform_start {n : ℕ} (k : ℕ) (m : ℝ)
    (z : Fin n → Bool) (t : ℕ) :
    audit_actual_bounds_probability k m z t =
      uexp (fun q : Fin n → Bool => audit_actual_bounds_probability k m q t) := by
  have hconst : (fun q : Fin n → Bool => audit_actual_bounds_probability k m q t) =
      fun _ => audit_actual_bounds_probability k m z t := by
    funext q
    exact audit_actual_bounds_start_invariant k m q z t
  rw [hconst]
  unfold uexp
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin n → Bool) := Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
    exact_mod_cast (ne_of_gt this)
  simp [hcard]

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect OAI.FixedClauseThreshold

/-- The small-set-bounds probability under the actual law is independent of the fixed start. -/
theorem solution {n : ℕ} (k : ℕ) (m : ℝ)
    (z z' : Fin n → Bool) (t : ℕ) :
    poisExp (allClauses n k) m (fun l => uprob fun s : Fin t → Fin n × Bool =>
      let Φ := ofList l
      let I0 := satIdx Φ z
      let X := glauberState (subF Φ I0) z s
      RepairBounds k Φ I0 X) =
    poisExp (allClauses n k) m (fun l => uprob fun s : Fin t → Fin n × Bool =>
      let Φ := ofList l
      let I0 := satIdx Φ z'
      let X := glauberState (subF Φ I0) z' s
      RepairBounds k Φ I0 X) := by
  exact audit_actual_bounds_start_invariant k m z z' t

#print axioms solution
