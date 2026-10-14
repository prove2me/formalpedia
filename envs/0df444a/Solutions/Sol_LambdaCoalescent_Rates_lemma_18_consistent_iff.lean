-- Prove2me | solution 1 for LambdaCoalescent.Rates.lemma_18_consistent_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:56:14.822426+00:00
-- url     : https://prove2.me/submissions/7aa0c4de-0e52-4d99-9850-b982aded7d5a

import Definitions.Def_LambdaCoalescent_Rates_Setting



namespace LambdaCoalescent.Rates

open MeasureTheory


theorem restrictLE_restrictLE' {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) (π : Setoid (Fin c)) :
    restrictLE h1 (restrictLE h2 π) = restrictLE (h1.trans h2) π := by
  ext i j
  exact Iff.rfl

theorem sum_regroup' {α β γ : Type} [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ]
    (g : α → β) (f : β → γ) (σ : γ) (w : α → ℝ) :
    (∑ a, if f (g a) = σ then w a else 0) =
      ∑ b, if f b = σ then (∑ a, if g a = b then w a else 0) else 0 := by
  have : ∀ b, (if f b = σ then (∑ a, if g a = b then w a else 0) else 0) =
      ∑ a, (if g a = b then (if f b = σ then w a else 0) else 0) := by
    intro b
    split_ifs with hb
    · refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> rfl
    · symm; refine Finset.sum_eq_zero fun a _ => ?_
      split_ifs <;> rfl
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem consistent_of_succ_core (lam : ℕ → ℕ → ℝ)
    (hsucc : ∀ (n : ℕ) (π : Setoid (Fin (n + 1))) (σ : Setoid (Fin n))
      (t : ℝ), 0 ≤ t →
        (∑ π' : Setoid (Fin (n + 1)),
          if restrictLE (Nat.le_succ n) π' = σ then
            NormedSpace.exp (t • rateMatrix lam (n + 1)) π π' else 0) =
        NormedSpace.exp (t • rateMatrix lam n)
          (restrictLE (Nat.le_succ n) π) σ) :
    Consistent lam := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => intro π σ t ht; exact hsucc n π σ t ht
  | succ m hm ih =>
    intro π σ t ht
    have h1 : n ≤ m := by omega
    have h2 : m ≤ m + 1 := by omega
    have e : ∀ π' : Setoid (Fin (m + 1)),
        restrictLE (Nat.lt_succ_of_lt hm).le π' = restrictLE h1 (restrictLE h2 π') := by
      intro π'; rw [restrictLE_restrictLE']
    simp_rw [e]
    rw [sum_regroup' (restrictLE h2) (restrictLE h1) σ]
    have hs := hsucc m π
    simp_rw [hs _ t ht]
    rw [ih (restrictLE h2 π) σ t ht, restrictLE_restrictLE']



theorem pow_intertwine' {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : Matrix α α ℝ) (B : Matrix β β ℝ) (R : Matrix α β ℝ) (h : A * R = R * B) (k : ℕ) :
    A ^ k * R = R * B ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem exp_intertwine' {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : Matrix α α ℝ) (B : Matrix β β ℝ) (R : Matrix α β ℝ) (h : A * R = R * B) (t : ℝ) :
    NormedSpace.exp (t • A) * R = R * NormedSpace.exp (t • B) := by
  open scoped Matrix.Norms.Operator in
  have hA := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • A)
  open scoped Matrix.Norms.Operator in
  have hB := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • B)
  let gA : Matrix α α ℝ →+ Matrix α β ℝ :=
    { toFun := fun M => M * R, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }
  let gB : Matrix β β ℝ →+ Matrix α β ℝ :=
    { toFun := fun M => R * M, map_zero' := Matrix.mul_zero _, map_add' := fun _ _ => Matrix.mul_add _ _ _ }
  have h1 := hA.map gA (continuous_id.matrix_mul continuous_const)
  have h2 := hB.map gB (continuous_const.matrix_mul continuous_id)
  have e : (⇑gA ∘ fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (t • A) ^ n) =
      (⇑gB ∘ fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (t • B) ^ n) := by
    funext k
    simp only [Function.comp, gA, gB, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_pow,
      Matrix.smul_mul, Matrix.mul_smul, pow_intertwine' A B R h k]
  rw [e] at h1
  exact h1.unique h2

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_exp_entry' {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) (i j : α) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A) i j) (A i j) 0 := by
  open scoped Matrix.Norms.Operator in
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
  let L : Matrix α α ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : α => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : α => α → ℝ) i)
  open scoped Matrix.Norms.Operator in
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => NormedSpace.exp (t • A) i j) = (⇑L ∘ fun u : ℝ => NormedSpace.exp (u • A)) := rfl
  rw [e]
  convert h2 using 1
  · rfl
  · rfl
  · rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mul]; rfl



section Comb
variable {n : ℕ}

noncomputable def eKey (σ : Setoid (Fin n)) (o : Option (Fin n)) (x : Fin (n+1)) :
    Option (Quotient σ) :=
  if h : x.val < n then some (Quotient.mk σ ⟨x.val, h⟩) else o.map (Quotient.mk σ)

noncomputable def eS (σ : Setoid (Fin n)) (o : Option (Fin n)) : Setoid (Fin (n+1)) := Setoid.ker (eKey σ o)

abbrev R1 (π : Setoid (Fin (n+1))) : Setoid (Fin n) := restrictLE (Nat.le_succ n) π

theorem R1_rel (π : Setoid (Fin (n+1))) (i j : Fin n) :
    (R1 π).r i j ↔ π.r i.castSucc j.castSucc := Iff.rfl

theorem eKey_cs (σ : Setoid (Fin n)) (o : Option (Fin n)) (i : Fin n) :
    eKey σ o i.castSucc = some (Quotient.mk σ i) := by
  simp [eKey, i.isLt]

theorem eKey_last (σ : Setoid (Fin n)) (o : Option (Fin n)) :
    eKey σ o (Fin.last n) = o.map (Quotient.mk σ) := by
  simp [eKey]

theorem eS_rel (σ : Setoid (Fin n)) (o : Option (Fin n)) (x y : Fin (n+1)) :
    (eS σ o).r x y ↔ eKey σ o x = eKey σ o y := Iff.rfl

theorem q_eq (σ : Setoid (Fin n)) (i j : Fin n) :
    Quotient.mk σ i = Quotient.mk σ j ↔ σ.r i j := Quotient.eq

theorem eS_cs_cs (σ : Setoid (Fin n)) (o : Option (Fin n)) (i j : Fin n) :
    (eS σ o).r i.castSucc j.castSucc ↔ σ.r i j := by
  rw [eS_rel, eKey_cs, eKey_cs, Option.some_inj, q_eq]

theorem eSN_last_cs (σ : Setoid (Fin n)) (i : Fin n) :
    ¬ (eS σ none).r (Fin.last n) i.castSucc := by
  rw [eS_rel, eKey_last, eKey_cs]; simp

theorem eSN_cs_last (σ : Setoid (Fin n)) (i : Fin n) :
    ¬ (eS σ none).r i.castSucc (Fin.last n) := by
  rw [eS_rel, eKey_last, eKey_cs]; simp

theorem eSS_last_cs (σ : Setoid (Fin n)) (j i : Fin n) :
    (eS σ (some j)).r (Fin.last n) i.castSucc ↔ σ.r j i := by
  rw [eS_rel, eKey_last, eKey_cs]; simp [q_eq]

theorem eSS_cs_last (σ : Setoid (Fin n)) (j i : Fin n) :
    (eS σ (some j)).r i.castSucc (Fin.last n) ↔ σ.r i j := by
  rw [eS_rel, eKey_last, eKey_cs]; simp [q_eq]

theorem s_refl' {m : ℕ} (π : Setoid (Fin m)) (x) : π.r x x := π.iseqv.refl x
theorem s_refl (π : Setoid (Fin (n+1))) (x) : π.r x x := π.iseqv.refl x
theorem s_symm {m : ℕ} (π : Setoid (Fin m)) {x y} (h : π.r x y) : π.r y x := π.iseqv.symm h
theorem s_trans {m : ℕ} (π : Setoid (Fin m)) {x y z} (h : π.r x y) (h' : π.r y z) : π.r x z :=
  π.iseqv.trans h h'

theorem R1_eS (σ : Setoid (Fin n)) (o : Option (Fin n)) : R1 (eS σ o) = σ := by
  ext i j
  exact (R1_rel _ i j).trans (eS_cs_cs σ o i j)

theorem decomp_some (π : Setoid (Fin (n+1))) (j : Fin n) (h : π.r (Fin.last n) j.castSucc) :
    π = eS (R1 π) (some j) := by
  ext x y
  show π.r x y ↔ (eS (R1 π) (some j)).r x y
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => exact ⟨fun _ => s_refl _ _, fun _ => s_refl _ _⟩
    | cast i =>
      rw [eSS_last_cs, R1_rel]
      exact ⟨fun h' => s_trans _ (s_symm _ h) h', fun h' => s_trans _ h h'⟩
  | cast i =>
    induction y using Fin.lastCases with
    | last =>
      rw [eSS_cs_last, R1_rel]
      exact ⟨fun h' => s_trans _ h' h, fun h' => s_trans _ h' (s_symm _ h)⟩
    | cast i' => rw [eS_cs_cs, R1_rel]

theorem decomp_none (π : Setoid (Fin (n+1))) (h : ∀ j : Fin n, ¬ π.r (Fin.last n) j.castSucc) :
    π = eS (R1 π) none := by
  ext x y
  show π.r x y ↔ (eS (R1 π) none).r x y
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => exact ⟨fun _ => s_refl _ _, fun _ => s_refl _ _⟩
    | cast i => exact ⟨fun h' => absurd h' (h i), fun h' => absurd h' (eSN_last_cs _ i)⟩
  | cast i =>
    induction y using Fin.lastCases with
    | last => exact ⟨fun h' => absurd (s_symm _ h') (h i), fun h' => absurd h' (eSN_cs_last _ i)⟩
    | cast i' => rw [eS_cs_cs, R1_rel]

theorem eSS_congr (σ : Setoid (Fin n)) (j j' : Fin n) (h : σ.r j j') :
    eS σ (some j) = eS σ (some j') := by
  have : eKey σ (some j) = eKey σ (some j') := by
    funext x
    unfold eKey
    split_ifs
    · rfl
    · simp [q_eq, h]
  unfold eS; rw [this]

/-! numBlocks -/

theorem nb_eq {m : ℕ} (π : Setoid (Fin m)) : numBlocks π = Nat.card (Quotient π) := by
  unfold numBlocks; exact Fintype.card_eq_nat_card

theorem card_ker {α β : Type} (f : α → β) (hf : Function.Surjective f) :
    Nat.card (Quotient (Setoid.ker f)) = Nat.card β :=
  Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hf)

theorem nb_eSN (σ : Setoid (Fin n)) : numBlocks (eS σ none) = numBlocks σ + 1 := by
  classical
  rw [nb_eq, nb_eq, eS, card_ker, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_option]
  intro q
  cases q with
  | none => exact ⟨Fin.last n, by rw [eKey_last]; rfl⟩
  | some q =>
    induction q using Quotient.inductionOn with
    | h i => exact ⟨i.castSucc, eKey_cs _ _ _⟩

theorem nb_eSS (σ : Setoid (Fin n)) (j : Fin n) : numBlocks (eS σ (some j)) = numBlocks σ := by
  let g : Fin (n+1) → Quotient σ := fun x =>
    if h : x.val < n then Quotient.mk σ ⟨x.val, h⟩ else Quotient.mk σ j
  have hk : eKey σ (some j) = fun x => some (g x) := by
    funext x; unfold eKey; simp only [g]; split_ifs <;> rfl
  have he : eS σ (some j) = Setoid.ker g := by
    ext x y
    show eKey σ (some j) x = eKey σ (some j) y ↔ g x = g y
    rw [hk]; simp
  rw [he, nb_eq, nb_eq, card_ker]
  intro q
  induction q using Quotient.inductionOn with
  | h i => exact ⟨i.castSucc, by simp [g, i.isLt]⟩

theorem exists_new {m : ℕ} (ρ σ : Setoid (Fin m)) (hle : ρ ≤ σ) (hne : ρ ≠ σ) :
    ∃ a b, σ.r a b ∧ ¬ ρ.r a b := by
  by_contra hc
  push Not at hc
  apply hne
  ext a b
  exact ⟨fun h => hle h, fun h => hc a b h⟩

theorem nb_lt {m : ℕ} (ρ σ : Setoid (Fin m)) (hle : ρ ≤ σ) (hne : ρ ≠ σ) :
    numBlocks σ < numBlocks ρ := by
  classical
  obtain ⟨a, b, hab, hnab⟩ := exists_new ρ σ hle hne
  rw [nb_eq, nb_eq, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  let f : Quotient ρ → Quotient σ :=
    Quotient.lift (fun x => Quotient.mk σ x) (fun x y h => Quotient.sound (hle h))
  apply Fintype.card_lt_of_surjective_not_injective f
  · intro q
    induction q using Quotient.inductionOn with
    | h i => exact ⟨Quotient.mk ρ i, rfl⟩
  · intro hinj
    have : f (Quotient.mk ρ a) = f (Quotient.mk ρ b) := Quotient.sound hab
    exact hnab (Quotient.exact (hinj this))

theorem nb_pos {m : ℕ} (σ : Setoid (Fin m)) (hm : 0 < m) : 0 < numBlocks σ := by
  rw [nb_eq]
  have : Nonempty (Quotient σ) := ⟨Quotient.mk σ ⟨0, hm⟩⟩
  exact Nat.card_pos


/-! IsMerge transport -/

def rep (j : Fin n) (x : Fin (n+1)) : Fin n := if h : x.val < n then ⟨x.val, h⟩ else j

theorem rep_cs (j i : Fin n) : rep j i.castSucc = i := by simp [rep, i.isLt]
theorem rep_last (j : Fin n) : rep j (Fin.last n) = j := by simp [rep]

theorem eSS_rep (σ : Setoid (Fin n)) (j : Fin n) (x y : Fin (n+1)) :
    (eS σ (some j)).r x y ↔ σ.r (rep j x) (rep j y) := by
  have hk : ∀ z, eKey σ (some j) z = some (Quotient.mk σ (rep j z)) := by
    intro z; unfold eKey rep; split_ifs <;> rfl
  rw [eS_rel, hk, hk, Option.some_inj, q_eq]

theorem merge_R1 {π π' : Setoid (Fin (n+1))} (h : IsMerge π π') (hne : R1 π ≠ R1 π') :
    IsMerge (R1 π) (R1 π') :=
  ⟨fun i j hij => h.1 hij, hne, fun i j i' j' h1 h2 h3 h4 => h.2.2 _ _ _ _ h1 h2 h3 h4⟩

theorem merge_eSS {ρ σ : Setoid (Fin n)} (j : Fin n) (hm : IsMerge ρ σ) :
    IsMerge (eS ρ (some j)) (eS σ (some j)) := by
  refine ⟨fun x y hxy => (eSS_rep σ j x y).2 (hm.1 ((eSS_rep ρ j x y).1 hxy)), ?_, ?_⟩
  · intro he
    apply hm.2.1
    rw [← R1_eS ρ (some j), he, R1_eS]
  · intro x y x' y' h1 h2 h3 h4
    rw [eSS_rep] at h1 h3 ⊢
    rw [eSS_rep] at h2 h4
    exact hm.2.2 _ _ _ _ h1 h2 h3 h4

theorem newN {ρ σ : Setoid (Fin n)} {x y : Fin (n+1)} (h1 : (eS σ none).r x y)
    (h2 : ¬ (eS ρ none).r x y) :
    ∃ i j : Fin n, x = i.castSucc ∧ y = j.castSucc ∧ σ.r i j ∧ ¬ ρ.r i j := by
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => exact absurd (s_refl _ _) h2
    | cast i => exact absurd h1 (eSN_last_cs _ _)
  | cast i =>
    induction y using Fin.lastCases with
    | last => exact absurd h1 (eSN_cs_last _ _)
    | cast i' =>
      rw [eS_cs_cs] at h1 h2
      exact ⟨i, i', rfl, rfl, h1, h2⟩

theorem leN {ρ σ : Setoid (Fin n)} (hle : ρ ≤ σ) : ∀ x y : Fin (n+1),
    (eS ρ none).r x y → (eS σ none).r x y := by
  intro x y h
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => exact s_refl _ _
    | cast i => exact absurd h (eSN_last_cs _ _)
  | cast i =>
    induction y using Fin.lastCases with
    | last => exact absurd h (eSN_cs_last _ _)
    | cast i' =>
      rw [eS_cs_cs] at h ⊢
      exact hle h

theorem merge_eSN {ρ σ : Setoid (Fin n)} (hm : IsMerge ρ σ) :
    IsMerge (eS ρ none) (eS σ none) := by
  refine ⟨fun x y hxy => leN hm.1 x y hxy, ?_, ?_⟩
  · intro he
    apply hm.2.1
    rw [← R1_eS ρ none, he, R1_eS]
  · intro x y x' y' h1 h2 h3 h4
    obtain ⟨i, j, rfl, rfl, hij, hnij⟩ := newN h1 h2
    obtain ⟨i', j', rfl, rfl, hij', hnij'⟩ := newN h3 h4
    rw [eS_cs_cs]
    exact hm.2.2 _ _ _ _ hij hnij hij' hnij'

theorem merge_eSN_eSS {ρ σ : Setoid (Fin n)} (hm : IsMerge ρ σ) {a b j : Fin n}
    (hab : σ.r a b) (hnab : ¬ ρ.r a b) (hja : σ.r j a) :
    IsMerge (eS ρ none) (eS σ (some j)) := by
  have key : ∀ x y, (eS σ (some j)).r x y → ¬ (eS ρ none).r x y → σ.r (rep j x) a := by
    intro x y h1 h2
    induction x using Fin.lastCases with
    | last => rw [rep_last]; exact hja
    | cast i =>
      rw [rep_cs]
      induction y using Fin.lastCases with
      | last => rw [eSS_cs_last] at h1; exact s_trans _ h1 hja
      | cast i' =>
        rw [eS_cs_cs] at h1 h2
        exact hm.2.2 _ _ _ _ h1 h2 hab hnab
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    induction x using Fin.lastCases with
    | last =>
      induction y using Fin.lastCases with
      | last => exact s_refl _ _
      | cast i => exact absurd h (eSN_last_cs _ _)
    | cast i =>
      induction y using Fin.lastCases with
      | last => exact absurd h (eSN_cs_last _ _)
      | cast i' =>
        rw [eS_cs_cs] at h ⊢
        exact hm.1 h
  · intro he
    have h1 : (eS σ (some j)).r (Fin.last n) j.castSucc := (eSS_last_cs _ _ _).2 (s_refl' σ j)
    rw [← he] at h1
    exact eSN_last_cs _ _ h1
  · intro x y x' y' h1 h2 h3 h4
    rw [eSS_rep]
    exact s_trans _ (key x y h1 h2) (s_symm _ (key x' y' h3 h4))

theorem merge_eSN_eSS_inv {ρ σ : Setoid (Fin n)} {a b j : Fin n}
    (hm : IsMerge (eS ρ none) (eS σ (some j))) (hab : σ.r a b) (hnab : ¬ ρ.r a b) :
    σ.r a j := by
  have h1 : (eS σ (some j)).r a.castSucc b.castSucc := (eS_cs_cs _ _ _ _).2 hab
  have h2 : ¬ (eS ρ none).r a.castSucc b.castSucc := fun h => hnab ((eS_cs_cs _ _ _ _).1 h)
  have h3 : (eS σ (some j)).r (Fin.last n) j.castSucc := (eSS_last_cs _ _ _).2 (s_refl' σ j)
  have h4 : ¬ (eS ρ none).r (Fin.last n) j.castSucc := eSN_last_cs _ _
  have := hm.2.2 _ _ _ _ h1 h2 h3 h4
  rwa [eSS_cs_last] at this

/-! rate matrix -/

open Classical in
theorem Q_off (lam : ℕ → ℕ → ℝ) {m : ℕ} (π π' : Setoid (Fin m)) (h : π ≠ π') :
    rateMatrix lam m π π' =
      if IsMerge π π' then lam (numBlocks π) (numBlocks π - numBlocks π' + 1) else 0 := by
  unfold rateMatrix
  simp only
  rw [if_neg h]

theorem Q_rowsum (lam : ℕ → ℕ → ℝ) {m : ℕ} (π : Setoid (Fin m)) :
    ∑ π', rateMatrix lam m π π' = 0 := by
  classical
  set off : Setoid (Fin m) → ℝ := fun τ =>
    if IsMerge π τ then lam (numBlocks π) (numBlocks π - numBlocks τ + 1) else 0 with hoff
  have hd : rateMatrix lam m π π = -(∑ τ, if τ = π then 0 else off τ) := by
    unfold rateMatrix
    simp only [if_true]
    rw [hoff]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ π), hd]
  have : ∑ τ, (if τ = π then 0 else off τ) = ∑ τ ∈ Finset.univ.erase π, off τ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ π), if_pos rfl, zero_add]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [if_neg (Finset.ne_of_mem_erase hτ)]
  rw [this, neg_add_eq_zero]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  rw [Q_off lam π τ (Finset.ne_of_mem_erase hτ).symm]

theorem ne_of_R1 {π π' : Setoid (Fin (n+1))} (h : R1 π ≠ R1 π') : π ≠ π' := fun e => h (e ▸ rfl)

theorem case0 (lam : ℕ → ℕ → ℝ) (π : Setoid (Fin (n+1))) (σ : Setoid (Fin n))
    (hne : σ ≠ R1 π) (hm : ¬ IsMerge (R1 π) σ) :
    (∑ π', if R1 π' = σ then rateMatrix lam (n+1) π π' else 0) = 0 := by
  refine Finset.sum_eq_zero fun π' _ => ?_
  split_ifs with hr
  · rw [Q_off lam _ _ (ne_of_R1 (by rw [hr]; exact hne.symm)), if_neg]
    intro h
    apply hm
    have := merge_R1 h (by rw [hr]; exact hne.symm)
    rwa [hr] at this
  · rfl

theorem caseA (lam : ℕ → ℕ → ℝ) (ρ σ : Setoid (Fin n)) (j : Fin n) (hne : σ ≠ ρ)
    (hm : IsMerge ρ σ) :
    (∑ π', if R1 π' = σ then rateMatrix lam (n+1) (eS ρ (some j)) π' else 0) =
      rateMatrix lam n ρ σ := by
  rw [Finset.sum_eq_single (eS σ (some j))]
  · rw [if_pos (R1_eS σ _), Q_off lam _ _ (ne_of_R1 (by rw [R1_eS, R1_eS]; exact hne.symm)),
      Q_off lam ρ σ hne.symm, if_pos (merge_eSS j hm), if_pos hm, nb_eSS, nb_eSS]
  · intro π' _ hπ'
    split_ifs with hr
    · rw [Q_off lam _ _ (ne_of_R1 (by rw [R1_eS, hr]; exact hne.symm)), if_neg]
      intro hmm
      apply hπ'
      have hl : π'.r (Fin.last n) j.castSucc := hmm.1 ((eSS_last_cs ρ j j).2 (s_refl' ρ j))
      have e := decomp_some π' j hl
      rw [hr] at e
      exact e
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem caseB (lam : ℕ → ℕ → ℝ) (ρ σ : Setoid (Fin n)) (hm : IsMerge ρ σ) :
    (∑ π', if R1 π' = σ then rateMatrix lam (n+1) (eS ρ none) π' else 0) =
      lam (numBlocks ρ + 1) (numBlocks ρ - numBlocks σ + 1) +
        lam (numBlocks ρ + 1) (numBlocks ρ - numBlocks σ + 2) := by
  obtain ⟨a, b, hab, hnab⟩ := exists_new ρ σ hm.1 hm.2.1
  have hlt := nb_lt ρ σ hm.1 hm.2.1
  have hP : eS σ none ≠ eS σ (some a) := fun h =>
    eSN_last_cs σ a (by rw [h]; exact (eSS_last_cs σ a a).2 (s_refl' σ a))
  have hρσ : R1 (eS ρ none) ≠ σ := by rw [R1_eS]; exact hm.2.1
  rw [Finset.sum_eq_add (eS σ none) (eS σ (some a)) hP]
  · rw [if_pos (R1_eS _ _), if_pos (R1_eS _ _),
      Q_off lam _ _ (ne_of_R1 (by rw [R1_eS, R1_eS]; exact hm.2.1)),
      Q_off lam _ _ (ne_of_R1 (by rw [R1_eS, R1_eS]; exact hm.2.1)),
      if_pos (merge_eSN hm), if_pos (merge_eSN_eSS hm hab hnab (s_refl' σ a)),
      nb_eSN, nb_eSN, nb_eSS]
    congr 2 <;> omega
  · intro π' _ ⟨h1, h2⟩
    split_ifs with hr
    · rw [Q_off lam _ _ (ne_of_R1 (by rw [hr]; exact hρσ)), if_neg]
      intro hmm
      by_cases hl : ∃ j : Fin n, π'.r (Fin.last n) j.castSucc
      · obtain ⟨j, hj⟩ := hl
        have e := decomp_some π' j hj
        rw [hr] at e
        rw [e] at hmm
        have := merge_eSN_eSS_inv hmm hab hnab
        exact h2 (e.trans (eSS_congr σ j a (s_symm _ this)))
      · push Not at hl
        have e := decomp_none π' hl
        rw [hr] at e
        exact h1 e
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

theorem gen_off (lam : ℕ → ℕ → ℝ)
    (hrec : ∀ b k, 2 ≤ k → k ≤ b → lam b k = lam (b + 1) k + lam (b + 1) (k + 1))
    (π : Setoid (Fin (n+1))) (σ : Setoid (Fin n)) (hne : σ ≠ R1 π) :
    (∑ π', if R1 π' = σ then rateMatrix lam (n+1) π π' else 0) =
      rateMatrix lam n (R1 π) σ := by
  by_cases hm : IsMerge (R1 π) σ
  swap
  · rw [case0 lam π σ hne hm, Q_off lam _ _ hne.symm, if_neg hm]
  by_cases hl : ∃ j : Fin n, π.r (Fin.last n) j.castSucc
  · obtain ⟨j, hj⟩ := hl
    have e := decomp_some π j hj
    generalize R1 π = ρ at e hne hm ⊢
    subst e
    exact caseA lam ρ σ j hne hm
  · push Not at hl
    have e := decomp_none π hl
    generalize R1 π = ρ at e hne hm ⊢
    subst e
    rw [caseB lam ρ σ hm, Q_off lam ρ σ hne.symm, if_pos hm]
    have hlt := nb_lt ρ σ hm.1 hm.2.1
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        exact absurd (Setoid.ext fun a => a.elim0) hne
      · exact h
    have hpos := nb_pos σ hn
    rw [hrec (numBlocks ρ) (numBlocks ρ - numBlocks σ + 1) (by omega) (by omega)]

theorem gen (lam : ℕ → ℕ → ℝ)
    (hrec : ∀ b k, 2 ≤ k → k ≤ b → lam b k = lam (b + 1) k + lam (b + 1) (k + 1))
    (π : Setoid (Fin (n+1))) (σ : Setoid (Fin n)) :
    (∑ π', if R1 π' = σ then rateMatrix lam (n+1) π π' else 0) =
      rateMatrix lam n (R1 π) σ := by
  by_cases hσ : σ = R1 π
  · subst hσ
    have htot : ∑ σ', (∑ π', if R1 π' = σ' then rateMatrix lam (n+1) π π' else 0) = 0 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact Q_rowsum lam π
    have hq := Q_rowsum lam (R1 π)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (R1 π))] at htot hq
    have : ∑ σ' ∈ Finset.univ.erase (R1 π),
        (∑ π', if R1 π' = σ' then rateMatrix lam (n+1) π π' else 0) =
        ∑ σ' ∈ Finset.univ.erase (R1 π), rateMatrix lam n (R1 π) σ' :=
      Finset.sum_congr rfl fun σ' h => gen_off lam hrec π σ' (Finset.ne_of_mem_erase h)
    linarith
  · exact gen_off lam hrec π σ hσ

end Comb


section Main

theorem consistent_of_rec (lam : ℕ → ℕ → ℝ)
    (hrec : ∀ b k, 2 ≤ k → k ≤ b → lam b k = lam (b + 1) k + lam (b + 1) (k + 1)) :
    Consistent lam := by
  apply consistent_of_succ_core
  intro n π σ t ht
  let Rm : Matrix (Setoid (Fin (n+1))) (Setoid (Fin n)) ℝ :=
    Matrix.of fun π σ => if R1 π = σ then 1 else 0
  have hQ : rateMatrix lam (n+1) * Rm = Rm * rateMatrix lam n := by
    ext π σ
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Rm, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact gen lam hrec π σ
  have := congrFun (congrFun (exp_intertwine' _ _ Rm hQ t) π) σ
  rw [Matrix.mul_apply, Matrix.mul_apply] at this
  simp only [Rm, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
  exact this

theorem rec_of_consistent (lam : ℕ → ℕ → ℝ) (hc : Consistent lam) (b k : ℕ)
    (h2 : 2 ≤ k) (hkb : k ≤ b) : lam b k = lam (b + 1) k + lam (b + 1) (k + 1) := by
  let f' : Fin b → Fin (b - k + 1) := fun i => ⟨max i.val (k-1) - (k-1), by omega⟩
  let σk : Setoid (Fin b) := Setoid.ker f'
  let ρ0 : Setoid (Fin b) := Setoid.ker (id : Fin b → Fin b)
  have hσ : ∀ x y : Fin b, σk.r x y ↔ max x.val (k-1) - (k-1) = max y.val (k-1) - (k-1) := by
    intro x y
    show f' x = f' y ↔ _
    simp [f', Fin.ext_iff]
  have hρ : ∀ x y : Fin b, ρ0.r x y ↔ x = y := fun x y => Iff.rfl
  have nbσ : numBlocks σk = b - k + 1 := by
    rw [nb_eq, card_ker, Nat.card_eq_fintype_card, Fintype.card_fin]
    intro c
    refine ⟨⟨c.val + k - 1, by omega⟩, ?_⟩
    simp only [f', Fin.ext_iff]
    omega
  have nbρ : numBlocks ρ0 = b := by
    rw [nb_eq, card_ker _ Function.surjective_id, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hm : IsMerge ρ0 σk := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y h
      have : x = y := (hρ x y).1 h
      subst this
      exact s_refl' _ _
    · intro he
      have h01 : σk.r ⟨0, by omega⟩ ⟨1, by omega⟩ := by rw [hσ]; simp; omega
      rw [← he, hρ] at h01
      simp [Fin.ext_iff] at h01
    · intro x y x' y' h1 h2 h3 h4
      rw [hσ] at h1 h3 ⊢
      rw [hρ, Fin.ext_iff] at h2 h4
      omega
  set π : Setoid (Fin (b+1)) := eS ρ0 none with hπ
  have hcons := hc b (b+1) (Nat.lt_succ_self b) π σk
  have hR : restrictLE (Nat.lt_succ_self b).le π = ρ0 := R1_eS ρ0 none
  rw [hR] at hcons
  have hF : HasDerivAt (fun t : ℝ => ∑ π' : Setoid (Fin (b+1)),
      if restrictLE (Nat.lt_succ_self b).le π' = σk then
        NormedSpace.exp (t • rateMatrix lam (b+1)) π π' else 0)
      (∑ π' : Setoid (Fin (b+1)), if R1 π' = σk then rateMatrix lam (b+1) π π' else 0) 0 := by
    apply HasDerivAt.fun_sum
    intro π' _
    by_cases hr : R1 π' = σk
    · have hr' : restrictLE (Nat.lt_succ_self b).le π' = σk := hr
      simp only [hr', hr, if_true]
      exact hasDerivAt_exp_entry' _ _ _
    · have hr' : ¬ restrictLE (Nat.lt_succ_self b).le π' = σk := hr
      simp only [hr', hr, if_false]
      exact hasDerivAt_const _ _
  have hG := hasDerivAt_exp_entry' (rateMatrix lam b) ρ0 σk
  have h1 := (hF.hasDerivWithinAt (s := Set.Ici 0)).congr_of_mem
    (f₁ := fun t : ℝ => NormedSpace.exp (t • rateMatrix lam b) ρ0 σk)
    (fun t ht => (hcons t ht).symm) (Set.mem_Ici.2 le_rfl)
  have heq := (uniqueDiffOn_Ici (0:ℝ) 0 (Set.mem_Ici.2 le_rfl)).eq_deriv _ h1 hG.hasDerivWithinAt
  rw [hπ, caseB lam ρ0 σk hm, Q_off lam ρ0 σk hm.2.1, if_pos hm, nbσ, nbρ] at heq
  have e1 : b - (b - k + 1) + 1 = k := by omega
  have e2 : b - (b - k + 1) + 2 = k + 1 := by omega
  rw [e1, e2] at heq
  exact heq.symm

theorem lemma_18_consistent_iff_core (lam : ℕ → ℕ → ℝ) :
    Consistent lam ↔
      ∀ b k, 2 ≤ k → k ≤ b →
        lam b k = lam (b + 1) k + lam (b + 1) (k + 1) :=
  ⟨fun hc b k h2 hkb => rec_of_consistent lam hc b k h2 hkb, fun hrec => consistent_of_rec lam hrec⟩

end Main

end LambdaCoalescent.Rates

open LambdaCoalescent.Rates


theorem solution (lam : ℕ → ℕ → ℝ)
    (hlam : ∀ b k, 2 ≤ k → k ≤ b → 0 ≤ lam b k) :
    Consistent lam ↔
      ∀ b k, 2 ≤ k → k ≤ b →
        lam b k = lam (b + 1) k + lam (b + 1) (k + 1) := by
  exact lemma_18_consistent_iff_core lam
