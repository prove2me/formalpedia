-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:32:15.472078+00:00
-- url     : https://prove2.me/submissions/358c8e68-9bd1-4583-9a4f-a5206b206295

import Definitions.Def_KSATSingleFlip_Connect_SignAveraging



open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- If the designated literal is forced and lies on the prescribed boundary,
then every assignment with that same boundary satisfies that clause. -/
theorem audit_forced_boundary_clause {n : ℕ} (C : GClause (Fin n)) (v : Fin n)
    (σ η τ : Fin n → Bool) (B : Finset (Fin n))
    (hv : v ∈ B) (hσ : agreesOn B τ σ) (hη : agreesOn B τ η)
    (hforce : Forces σ C v) : ClauseSat η C := by
  have hvtrue : v ∈ satSet σ C := by rw [hforce]; simp
  have hlit : C v = some (σ v) := (Finset.mem_filter.mp hvtrue).2
  refine ⟨v, ?_⟩
  have heq : η v = σ v := (hη v hv).trans (hσ v hv).symm
  simpa [heq] using hlit

/-- On a feasible boundary containing all designated variables, a witness for
the force event makes every base solution with that boundary satisfy all newly
sampled clauses. This is the denominator bound in Lemma 3.4. -/
theorem audit_force_boundary_preserves_solutions {n r : ℕ} (Φ0 : GFormula (Fin n))
    (scopes : Fin r → Finset (Fin n)) (signs : Fin r → Fin n → Bool)
    (designated : Fin r → Fin n) (B : Finset (Fin n)) (τ σ η : Fin n → Bool)
    (hB : ∀ i, designated i ∈ B) (hσ : agreesOn B τ σ) (hη : agreesOn B τ η)
    (hforce : allResampledClausesForce scopes signs designated σ) (hbase : FSat η Φ0) :
    FSat η (signExtendedFormula Φ0 scopes signs) := by
  intro C hC
  unfold signExtendedFormula at hC
  rw [List.mem_append] at hC
  rcases hC with hC | hC
  · exact hbase C hC
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hC
    rw [← hi]
    exact audit_forced_boundary_clause (scopedSignedClause (scopes i) (signs i)) (designated i)
      σ η τ B (hB i) hσ hη (hforce i)

/-- Consequently, the extended formula has at least as many solutions as the
number of base solutions with that prescribed boundary. -/
theorem audit_force_boundary_solution_count {n r : ℕ} (Φ0 : GFormula (Fin n))
    (scopes : Fin r → Finset (Fin n)) (signs : Fin r → Fin n → Bool)
    (designated : Fin r → Fin n) (B : Finset (Fin n)) (τ σ : Fin n → Bool)
    (hB : ∀ i, designated i ∈ B) (hσ : agreesOn B τ σ)
    (hforce : allResampledClausesForce scopes signs designated σ) :
    ((sols Φ0).filter (agreesOn B τ)).card ≤ (sols (signExtendedFormula Φ0 scopes signs)).card := by
  apply Finset.card_le_card
  intro η hη
  obtain ⟨hbase, hagree⟩ := Finset.mem_filter.mp hη
  have hsat : FSat η Φ0 := by simpa [sols] using hbase
  have hnew := audit_force_boundary_preserves_solutions Φ0 scopes signs designated B τ σ η hB hσ hagree hforce hsat
  simpa [sols] using hnew

/-- Forcing a designated variable fixes exactly the signs on the clause scope. -/
theorem audit_scoped_clause_forces_iff {n : ℕ} (scope : Finset (Fin n))
    (sign σ : Fin n → Bool) (v : Fin n) (hv : v ∈ scope) :
    Forces σ (scopedSignedClause scope sign) v ↔
      ∀ u ∈ scope, sign u = if u = v then σ u else !σ u := by
  constructor
  · intro h u hu
    by_cases heq : u = v
    · subst u
      have hmem : v ∈ satSet σ (scopedSignedClause scope sign) := by rw [h]; simp
      have hs := (Finset.mem_filter.mp hmem).2
      simpa [scopedSignedClause, hv] using hs
    · have hnot : u ∉ satSet σ (scopedSignedClause scope sign) := by rw [h]; simp [heq]
      have hs : sign u ≠ σ u := by
        intro hh
        apply hnot
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by simp [scopedSignedClause, hu, hh]⟩
      have hs' : sign u = !σ u := by cases h1 : sign u <;> cases h2 : σ u <;> simp_all
      simp [heq, hs']
  · intro h
    unfold Forces
    ext u
    simp only [satSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hu : u ∈ scope
    · by_cases heq : u = v
      · subst u
        simp [scopedSignedClause, hv, h v hv]
      · have hs := h u hu
        simp [heq] at hs
        simp [scopedSignedClause, hu, heq, hs]
    · have hne : u ≠ v := by intro heq; subst u; exact hu hv
      simp [scopedSignedClause, hu, hne]

/-- Pointwise denominator comparison for the boundary-restricted force event. -/
theorem audit_sign_mass_pointwise {n r : ℕ} (Φ0 : GFormula (Fin n))
    (scopes : Fin r → Finset (Fin n)) (signs : Fin r → Fin n → Bool)
    (designated : Fin r → Fin n) (B : Finset (Fin n)) (τ : Fin n → Bool)
    (A : Finset (Fin n → Bool)) (hA : A ⊆ sols Φ0)
    (hB : ∀ i, designated i ∈ B)
    (hτ : ((sols Φ0).filter (agreesOn B τ)).Nonempty) :
    mass (signExtendedFormula Φ0 scopes signs)
      (A.filter fun σ => allResampledClausesForce scopes signs designated σ ∧ agreesOn B τ σ) ≤
      (((A.filter fun σ => allResampledClausesForce scopes signs designated σ ∧ agreesOn B τ σ).card : ℝ) /
        ((sols Φ0).filter (agreesOn B τ)).card) := by
  let P := A.filter fun σ => allResampledClausesForce scopes signs designated σ ∧ agreesOn B τ σ
  let Z := (sols Φ0).filter (agreesOn B τ)
  have hZ : (0 : ℝ) < Z.card := by exact_mod_cast Finset.card_pos.mpr hτ
  by_cases hP : P.Nonempty
  · obtain ⟨σ, hσ⟩ := hP
    have hσ' := Finset.mem_filter.mp hσ
    have hden := audit_force_boundary_solution_count Φ0 scopes signs designated B τ σ hB hσ'.2.2 hσ'.2.1
    have hdenR : (Z.card : ℝ) ≤ (sols (signExtendedFormula Φ0 scopes signs)).card := by exact_mod_cast hden
    have hnum : ((P ∩ sols (signExtendedFormula Φ0 scopes signs)).card : ℝ) ≤ P.card := by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_left
    unfold mass
    change ((P ∩ sols (signExtendedFormula Φ0 scopes signs)).card : ℝ) /
      (sols (signExtendedFormula Φ0 scopes signs)).card ≤ (P.card : ℝ) / Z.card
    have hnonneg : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
    have h₁ : ((P ∩ sols (signExtendedFormula Φ0 scopes signs)).card : ℝ) /
        (sols (signExtendedFormula Φ0 scopes signs)).card ≤
        (P.card : ℝ) / (sols (signExtendedFormula Φ0 scopes signs)).card :=
      div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)
    have h₂ : (P.card : ℝ) / (sols (signExtendedFormula Φ0 scopes signs)).card ≤ (P.card : ℝ) / Z.card :=
      div_le_div_of_nonneg_left hnonneg hZ hdenR
    exact h₁.trans h₂
  · have hP0 : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    change mass (signExtendedFormula Φ0 scopes signs) P ≤ (P.card : ℝ) / Z.card
    rw [hP0]
    simp [mass]

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- A Boolean assignment fixed on Q is freely specified on the complement. -/
noncomputable def audit_fixed_bits_equiv {α : Type} [Fintype α] [DecidableEq α]
    (Q : Finset α) (target : α → Bool) :
    {f : α → Bool // ∀ i ∈ Q, f i = target i} ≃ (↥(Finset.univ \ Q) → Bool) where
  toFun f := fun i => f.1 i.1
  invFun q := ⟨fun i => if h : i ∈ Q then target i else q ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩⟩, by
    intro i hi
    simp [hi]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ Q
    · simp [hi, f.2 i hi]
    · simp [hi]
  right_inv q := by
    funext i
    have hi : i.1 ∉ Q := (Finset.mem_sdiff.mp i.2).2
    simp [hi]

/-- The number of Boolean assignments fixed on Q is 2^(|α|−|Q|). -/
theorem audit_fixed_bits_count {α : Type} [Fintype α] [DecidableEq α]
    (Q : Finset α) (target : α → Bool) :
    Fintype.card {f : α → Bool // ∀ i ∈ Q, f i = target i} = 2 ^ (Fintype.card α - Q.card) := by
  rw [Fintype.card_congr (audit_fixed_bits_equiv Q target), Fintype.card_fun, Fintype.card_bool]
  congr 1
  rw [Fintype.card_coe, Finset.card_sdiff]
  simp

/-- Uniform independent Boolean signs match prescribed values on Q with
probability exactly 2^(−|Q|). -/
theorem audit_fixed_bits_probability {α : Type} [Fintype α] [DecidableEq α]
    (Q : Finset α) (target : α → Bool) :
    uprob (fun f : α → Bool => ∀ i ∈ Q, f i = target i) = 1 / (2 : ℝ) ^ Q.card := by
  let P : (α → Bool) → Prop := fun f => ∀ i ∈ Q, f i = target i
  have hcount := audit_fixed_bits_count Q target
  have hcard : Q.card ≤ Fintype.card α := by simpa using Finset.card_le_univ Q
  have hpow : 2 ^ Fintype.card α = 2 ^ (Fintype.card α - Q.card) * 2 ^ Q.card := by
    rw [← pow_add]
    congr 1
    omega
  have hreal : (Fintype.card {f : α → Bool // P f} : ℝ) * (2 : ℝ) ^ Q.card =
      Fintype.card (α → Bool) := by
    rw [hcount, Fintype.card_fun, Fintype.card_bool]
    exact_mod_cast hpow.symm
  have hN : (0 : ℝ) < Fintype.card (α → Bool) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ => false⟩)
  have hprob : uprob P = (Fintype.card {f : α → Bool // P f} : ℝ) / Fintype.card (α → Bool) := by
    unfold uprob uexp
    congr 1
    rw [Fintype.card_subtype]
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro f hf
    by_cases h : P f <;> simp [h]
  change uprob P = _
  rw [hprob]
  apply (div_eq_iff (ne_of_gt hN)).mpr
  have hp : (2 : ℝ) ^ Q.card ≠ 0 := by positivity
  field_simp
  nlinarith

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- A fixed assignment is forced by r independently signed k-clauses with
probability exactly 2^(−kr), even when clause scopes overlap. -/
theorem audit_all_forces_probability {n k r : ℕ}
    (scopes : Fin r → Finset (Fin n)) (designated : Fin r → Fin n)
    (hscopes : ∀ i, (scopes i).card = k) (hdesignated : ∀ i, designated i ∈ scopes i)
    (σ : Fin n → Bool) :
    uprob (fun signs : Fin r → Fin n → Bool => allResampledClausesForce scopes signs designated σ) =
      1 / (2 : ℝ) ^ (k * r) := by
  let Q : Finset (Fin r × Fin n) := Finset.univ.filter fun p => p.2 ∈ scopes p.1
  let target : Fin r × Fin n → Bool := fun p => if p.2 = designated p.1 then σ p.2 else !σ p.2
  have hQ : Q.card = k * r := by
    unfold Q
    rw [Finset.card_filter, Fintype.sum_prod_type]
    have hsum : ∀ i : Fin r, (∑ v : Fin n, if v ∈ scopes i then 1 else 0) = k := by
      intro i
      simpa [Finset.card_filter] using hscopes i
    simp [hsum, Nat.mul_comm]
  have hevent : ∀ (f : Fin r × Fin n → Bool),
      (∀ p ∈ Q, f p = target p) ↔ allResampledClausesForce scopes (fun i v => f (i,v)) designated σ := by
    intro f
    unfold allResampledClausesForce
    constructor
    · intro h i
      apply (audit_scoped_clause_forces_iff (scopes i) (fun v => f (i,v)) σ (designated i) (hdesignated i)).mpr
      intro v hv
      exact h (i,v) (by simp [Q, hv])
    · intro h p hp
      have hp' : p.2 ∈ scopes p.1 := by simpa [Q] using hp
      exact (audit_scoped_clause_forces_iff (scopes p.1) (fun v => f (p.1,v)) σ (designated p.1) (hdesignated p.1)).mp (h p.1) p.2 hp'
  have hbase := audit_fixed_bits_probability Q target
  rw [hQ] at hbase
  unfold uprob uexp at *
  have hcard : Fintype.card (Fin r × Fin n → Bool) = Fintype.card (Fin r → Fin n → Bool) :=
    Fintype.card_congr (Equiv.curry (Fin r) (Fin n) Bool)
  rw [hcard] at hbase
  apply Eq.trans _ hbase
  congr 1
  symm
  have hsum := (Equiv.curry (Fin r) (Fin n) Bool).sum_comp (fun signs : Fin r → Fin n → Bool =>
    if allResampledClausesForce scopes signs designated σ then (1 : ℝ) else 0)
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro f hf
  by_cases he : ∀ p ∈ Q, f p = target p
  · have hs : allResampledClausesForce scopes (Function.curry f) designated σ := (hevent f).mp he
    have he' : ∀ i v, (i,v) ∈ Q → f (i,v) = target (i,v) := fun i v hv => he (i,v) hv
    simp [hs]
    exact he'
  · have hs : ¬ allResampledClausesForce scopes (Function.curry f) designated σ := fun hs => he ((hevent f).mpr hs)
    have he' : ¬ ∀ i v, (i,v) ∈ Q → f (i,v) = target (i,v) := by
      intro hh
      apply he
      intro p hp
      exact hh p.1 p.2 hp
    simp [he', hs]

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Average a filtered cardinality by summing the individual inclusion probabilities. -/
theorem audit_uexp_card_filter {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (F : Finset β) (P : α → β → Prop) :
    uexp (fun a : α => ((F.filter (P a)).card : ℝ)) = ∑ b ∈ F, uprob (fun a => P a b) := by
  classical
  unfold uexp uprob
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  congr 1

/-- Averages commute with division by a fixed constant. -/
theorem audit_uexp_div {α : Type} [Fintype α] (f : α → ℝ) (c : ℝ) :
    uexp (fun a => f a / c) = uexp f / c := by
  unfold uexp
  rw [← Finset.sum_div]
  ring

end KSATSingleFlip.Connect


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


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- The boundary-conditioned inequality in Lemma 3.4. -/
theorem audit_sign_averaging_first {n k r : ℕ} (Φ0 : GFormula (Fin n))
    (scopes : Fin r → Finset (Fin n)) (designated : Fin r → Fin n)
    (hscopes : ∀ i, (scopes i).card = k) (hdesignated : ∀ i, designated i ∈ scopes i)
    (A : Finset (Fin n → Bool)) (hA : A ⊆ sols Φ0)
    (B : Finset (Fin n)) (hB : ∀ i, designated i ∈ B) (τ : Fin n → Bool)
    (hτ : ((sols Φ0).filter (agreesOn B τ)).Nonempty) :
    uexp (fun signs : Fin r → Fin n → Bool =>
      mass (signExtendedFormula Φ0 scopes signs)
        (A.filter fun σ => allResampledClausesForce scopes signs designated σ ∧ agreesOn B τ σ)) ≤
      (1 / (2 : ℝ) ^ (k * r)) * conditionalSolutionMass Φ0 A B τ := by
  let F := A.filter (agreesOn B τ)
  let Z := ((sols Φ0).filter (agreesOn B τ)).card
  let p : ℝ := 1 / (2 : ℝ) ^ (k * r)
  have hset : ∀ signs : Fin r → Fin n → Bool,
      A.filter (fun σ => allResampledClausesForce scopes signs designated σ ∧ agreesOn B τ σ) =
        F.filter (allResampledClausesForce scopes signs designated) := by
    intro signs
    ext σ
    simp [F, and_comm, and_left_comm, and_assoc]
  have hp : ∀ σ : Fin n → Bool,
      uprob (fun signs : Fin r → Fin n → Bool => allResampledClausesForce scopes signs designated σ) = p :=
    fun σ => audit_all_forces_probability scopes designated hscopes hdesignated σ
  have hmean : uexp (fun signs : Fin r → Fin n → Bool =>
      ((A.filter fun σ => allResampledClausesForce scopes signs designated σ ∧ agreesOn B τ σ).card : ℝ)) =
        (F.card : ℝ) * p := by
    simp_rw [hset]
    rw [audit_uexp_card_filter]
    simp [hp, Nat.cast_mul, Nat.mul_comm]
  have hpoint := audit_uexp_mono
    (fun signs : Fin r → Fin n → Bool => mass (signExtendedFormula Φ0 scopes signs)
      (A.filter fun σ => allResampledClausesForce scopes signs designated σ ∧ agreesOn B τ σ))
    (fun signs : Fin r → Fin n → Bool =>
      ((A.filter fun σ => allResampledClausesForce scopes signs designated σ ∧ agreesOn B τ σ).card : ℝ) / Z)
    (fun signs => audit_sign_mass_pointwise Φ0 scopes signs designated B τ A hA hB hτ)
  rw [audit_uexp_div, hmean] at hpoint
  have hAeq : sols Φ0 ∩ A = A := Finset.inter_eq_right.mpr hA
  unfold conditionalSolutionMass
  rw [hAeq]
  change _ ≤ p * ((F.card : ℝ) / Z)
  have heq : (F.card : ℝ) * p / Z = p * ((F.card : ℝ) / Z) := by ring
  rw [← heq]
  exact hpoint

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Extend a boundary assignment by false values outside the boundary. -/
noncomputable def audit_boundary_extend {n : ℕ} (B : Finset (Fin n)) (b : ↥B → Bool) : Fin n → Bool :=
  fun v => if h : v ∈ B then b ⟨v, h⟩ else false

/-- Agreement with an extended boundary assignment is equality of restrictions. -/
theorem audit_agrees_iff_restrict {n : ℕ} (B : Finset (Fin n))
    (b : ↥B → Bool) (σ : Fin n → Bool) :
    agreesOn B (audit_boundary_extend B b) σ ↔ (fun v : ↥B => σ v.1) = b := by
  constructor
  · intro h
    funext v
    simpa [audit_boundary_extend, v.2] using h v.1 v.2
  · intro h v hv
    have hh := congrFun h ⟨v, hv⟩
    simpa [audit_boundary_extend, hv] using hh

/-- Solution mass partitions exactly across the 2^|B| boundary assignments. -/
theorem audit_mass_boundary_partition {n : ℕ} (Φ : GFormula (Fin n))
    (A : Finset (Fin n → Bool)) (B : Finset (Fin n)) :
    mass Φ A = ∑ b : ↥B → Bool, mass Φ (A.filter (agreesOn B (audit_boundary_extend B b))) := by
  let S := A ∩ sols Φ
  let res : (Fin n → Bool) → (↥B → Bool) := fun σ v => σ v.1
  have hsum : (∑ b : ↥B → Bool, (S.filter fun σ => res σ = b).card) = S.card := by
    have h := Finset.sum_fiberwise S res (fun _ => (1 : ℕ))
    simpa using h
  unfold mass
  have hset : ∀ b : ↥B → Bool,
      A.filter (agreesOn B (audit_boundary_extend B b)) ∩ sols Φ = S.filter (fun σ => res σ = b) := by
    intro b
    ext σ
    simp [S, res, audit_agrees_iff_restrict, and_comm, and_left_comm, and_assoc]
  simp_rw [hset]
  rw [← Finset.sum_div]
  have hsumR : (∑ b : ↥B → Bool, ((S.filter fun σ => res σ = b).card : ℝ)) = S.card := by
    exact_mod_cast hsum
  rw [hsumR]

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- The unconditional inequality in Lemma 3.4, by partitioning on the boundary. -/
theorem audit_sign_averaging_second {n k r : ℕ} (Φ0 : GFormula (Fin n))
    (scopes : Fin r → Finset (Fin n)) (designated : Fin r → Fin n)
    (hscopes : ∀ i, (scopes i).card = k) (hdesignated : ∀ i, designated i ∈ scopes i)
    (A : Finset (Fin n → Bool)) (hA : A ⊆ sols Φ0)
    (B : Finset (Fin n)) (hB : ∀ i, designated i ∈ B) :
    uexp (fun signs : Fin r → Fin n → Bool =>
      mass (signExtendedFormula Φ0 scopes signs)
        (A.filter fun σ => allResampledClausesForce scopes signs designated σ)) ≤
      (2 : ℝ) ^ B.card / (2 : ℝ) ^ (k * r) := by
  let p : ℝ := 1 / (2 : ℝ) ^ (k * r)
  let part : (↥B → Bool) → (Fin r → Fin n → Bool) → ℝ := fun b signs =>
    mass (signExtendedFormula Φ0 scopes signs)
      (A.filter fun σ => allResampledClausesForce scopes signs designated σ ∧
        agreesOn B (audit_boundary_extend B b) σ)
  have hp : 0 ≤ p := by positivity
  have hbound : ∀ b : ↥B → Bool, uexp (part b) ≤ p := by
    intro b
    let τ := audit_boundary_extend B b
    by_cases hτ : ((sols Φ0).filter (agreesOn B τ)).Nonempty
    · have hfirst := audit_sign_averaging_first Φ0 scopes designated hscopes hdesignated A hA B hB τ hτ
      have hcond : conditionalSolutionMass Φ0 A B τ ≤ 1 := by
        unfold conditionalSolutionMass
        have hsub : (sols Φ0 ∩ A).filter (agreesOn B τ) ⊆ (sols Φ0).filter (agreesOn B τ) := by
          intro σ hσ
          obtain ⟨hσ, hτ⟩ := Finset.mem_filter.mp hσ
          exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hσ).1, hτ⟩
        have hc : (((sols Φ0 ∩ A).filter (agreesOn B τ)).card : ℝ) ≤
            ((sols Φ0).filter (agreesOn B τ)).card := by exact_mod_cast Finset.card_le_card hsub
        have hz : (0 : ℝ) < ((sols Φ0).filter (agreesOn B τ)).card := by
          exact_mod_cast Finset.card_pos.mpr hτ
        exact (div_le_one₀ hz).mpr hc
      have hmul := mul_le_mul_of_nonneg_left hcond hp
      change uexp (part b) ≤ p * conditionalSolutionMass Φ0 A B τ at hfirst
      linarith
    · have hempty : (A.filter (agreesOn B τ)) = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨σ, hσ⟩
        obtain ⟨hσA, hσB⟩ := Finset.mem_filter.mp hσ
        exact hτ ⟨σ, Finset.mem_filter.mpr ⟨hA hσA, hσB⟩⟩
      have hzero : part b = fun _ => 0 := by
        funext signs
        dsimp [part, τ]
        have hset : A.filter (fun σ => allResampledClausesForce scopes signs designated σ ∧ agreesOn B (audit_boundary_extend B b) σ) = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          rintro ⟨σ, hσ⟩
          obtain ⟨hAσ, _, hBσ⟩ := Finset.mem_filter.mp hσ
          have : σ ∈ A.filter (agreesOn B τ) := Finset.mem_filter.mpr ⟨hAσ, hBσ⟩
          simp [hempty] at this
        rw [hset]
        simp [mass]
      rw [hzero]
      simp [uexp, hp]
  have hpartition : ∀ signs : Fin r → Fin n → Bool,
      mass (signExtendedFormula Φ0 scopes signs)
        (A.filter fun σ => allResampledClausesForce scopes signs designated σ) =
      ∑ b : ↥B → Bool, part b signs := by
    intro signs
    rw [audit_mass_boundary_partition _ _ B]
    apply Finset.sum_congr rfl
    intro b hb
    congr 1
    ext σ
    simp [part, and_assoc]
  have hmean : uexp (fun signs : Fin r → Fin n → Bool =>
      mass (signExtendedFormula Φ0 scopes signs)
        (A.filter fun σ => allResampledClausesForce scopes signs designated σ)) =
      ∑ b : ↥B → Bool, uexp (part b) := by
    simp_rw [hpartition]
    unfold uexp
    simp_rw [← Finset.sum_div]
    rw [Finset.sum_comm]
  rw [hmean]
  calc
    _ ≤ ∑ _b : ↥B → Bool, p := Finset.sum_le_sum (fun b _ => hbound b)
    _ = (2 : ℝ) ^ B.card / (2 : ℝ) ^ (k * r) := by
      simp [p, Fintype.card_fun, Fintype.card_coe, div_eq_mul_inv]

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

theorem solution {n k r : ℕ} (Φ0 : GFormula (Fin n))
    (scopes : Fin r → Finset (Fin n)) (designated : Fin r → Fin n)
    (hscopes : ∀ i, (scopes i).card = k) (hdesignated : ∀ i, designated i ∈ scopes i)
    (A : Finset (Fin n → Bool)) (hA : A ⊆ sols Φ0)
    (B : Finset (Fin n)) (hB : ∀ i, designated i ∈ B) (τ : Fin n → Bool)
    (hτ : ((sols Φ0).filter (agreesOn B τ)).Nonempty) :
    (uexp (fun signs : Fin r → Fin n → Bool =>
      mass (signExtendedFormula Φ0 scopes signs)
        (A.filter fun σ => allResampledClausesForce scopes signs designated σ ∧ agreesOn B τ σ)) ≤
      (1 / (2 : ℝ) ^ (k * r)) * conditionalSolutionMass Φ0 A B τ) ∧
    (uexp (fun signs : Fin r → Fin n → Bool =>
      mass (signExtendedFormula Φ0 scopes signs)
        (A.filter fun σ => allResampledClausesForce scopes signs designated σ)) ≤
      (2 : ℝ) ^ B.card / (2 : ℝ) ^ (k * r)) := by
  exact ⟨audit_sign_averaging_first Φ0 scopes designated hscopes hdesignated A hA B hB τ hτ,
    audit_sign_averaging_second Φ0 scopes designated hscopes hdesignated A hA B hB⟩


#print axioms solution
