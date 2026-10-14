-- Prove2me | solution 1 for LambdaCoalescent.Rates.lemma_18_bijection
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:10:07.792134+00:00
-- url     : https://prove2.me/submissions/95d09b99-d777-42d9-9098-48fc0e0a4fce

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


open MeasureTheory Filter Topology Finset
open scoped CompactlySupported

section Hausdorff

theorem iter_rec (μ : ℕ → ℕ → ℝ) (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (M : ℕ) :
    ∀ i j, μ i j = ∑ p ∈ antidiagonal M, (M.choose p.1 : ℝ) * μ (i + p.1) (j + p.2) := by
  induction M with
  | zero => intro i j; simp
  | succ M ih =>
    intro i j
    rw [Nat.sum_antidiagonal_succ]
    have e1 : ∀ p ∈ antidiagonal M, ((M+1).choose (p.1+1) : ℝ) * μ (i + (p.1+1)) (j + p.2) =
        (M.choose p.1 : ℝ) * μ (i + 1 + p.1) (j + p.2) +
          (M.choose (p.1+1) : ℝ) * μ (i + (p.1+1)) (j + p.2) := by
      intro p _
      rw [Nat.choose_succ_succ, Nat.cast_add, add_mul]
      congr 2; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
    have e2 : ((M+1).choose 0 : ℝ) * μ (i + 0) (j + (M+1)) +
        (∑ p ∈ antidiagonal M, (M.choose p.1 : ℝ) * μ (i + 1 + p.1) (j + p.2) +
          ∑ p ∈ antidiagonal M, (M.choose (p.1+1) : ℝ) * μ (i + (p.1+1)) (j + p.2)) =
        ∑ p ∈ antidiagonal M, (M.choose p.1 : ℝ) * μ (i + 1 + p.1) (j + p.2) +
          ∑ p ∈ antidiagonal (M+1), (M.choose p.1 : ℝ) * μ (i + p.1) (j + p.2) := by
      rw [Nat.sum_antidiagonal_succ (f := fun p => (M.choose p.1 : ℝ) * μ (i + p.1) (j + p.2))]
      simp only [Nat.choose_zero_right, Nat.cast_one]
      ring
    rw [e2, Nat.sum_antidiagonal_succ']
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_add]
    rw [← ih (i+1) j]
    have e3 : ∀ p ∈ antidiagonal M, (M.choose p.1 : ℝ) * μ (i + p.1) (j + (p.2 + 1)) =
        (M.choose p.1 : ℝ) * μ (i + p.1) (j + 1 + p.2) := by
      intro p _; congr 2; ring
    rw [Finset.sum_congr rfl e3, ← ih i (j+1), ← h]

theorem cast_descFactorial_prod (k i : ℕ) :
    (k.descFactorial i : ℝ) = ∏ r ∈ range i, ((k : ℝ) - r) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.descFactorial_succ, prod_range_succ, ← ih, Nat.cast_mul]
    rcases le_or_gt i k with hik | hik
    · rw [Nat.cast_sub hik]; ring
    · rw [(Nat.descFactorial_eq_zero_iff_lt).2 hik]; simp

theorem choose_mul_desc (N i a : ℕ) (h : i + a ≤ N) :
    N.choose (i + a) * (i + a).descFactorial i = N.descFactorial i * (N - i).choose a := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  have := Nat.choose_mul (n := N) (k := i + a) (s := i) (by omega)
  rw [show i + a - i = a by omega] at this
  calc N.choose (i + a) * (i.factorial * (i + a).choose i)
      = i.factorial * (N.choose (i + a) * (i + a).choose i) := by ring
    _ = i.factorial * (N.choose i * (N - i).choose a) := by rw [this]
    _ = _ := by ring

theorem moment_identity (μ : ℕ → ℕ → ℝ) (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1))
    (N i : ℕ) (hi : i ≤ N) :
    ∑ k ∈ range (N+1), (N.choose k : ℝ) * μ k (N - k) * (k.descFactorial i : ℝ) =
      (N.descFactorial i : ℝ) * μ i 0 := by
  rw [iter_rec μ h (N - i) i 0, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  rw [show N + 1 = i + (N - i + 1) by omega, sum_range_add]
  have hz : ∑ k ∈ range i, (N.choose k : ℝ) * μ k (N - k) *
      (k.descFactorial i : ℝ) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    rw [(Nat.descFactorial_eq_zero_iff_lt).2 (mem_range.1 hk)]; simp
  rw [hz, zero_add]
  refine sum_congr rfl fun a ha => ?_
  have ha' := mem_range.1 ha
  have hc := choose_mul_desc N i a (by omega)
  have hc' : (N.choose (i + a) : ℝ) * ((i + a).descFactorial i : ℝ) =
      (N.descFactorial i : ℝ) * ((N - i).choose a : ℝ) := by exact_mod_cast hc
  dsimp only
  rw [zero_add, show N - (i + a) = N - i - a by omega]
  linear_combination μ (i + a) (N - i - a) * hc'

noncomputable def wt (μ : ℕ → ℕ → ℝ) (N k : ℕ) : ℝ := (N.choose k : ℝ) * μ k (N - k)

noncomputable def LN (μ : ℕ → ℕ → ℝ) (N : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∑ k ∈ range (N+1), wt μ N k * g (k / N)

theorem wt_nonneg (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j) (N k : ℕ) : 0 ≤ wt μ N k :=
  mul_nonneg (Nat.cast_nonneg _) (hμ _ _)

theorem wt_sum (μ : ℕ → ℕ → ℝ) (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1)
    (N : ℕ) : ∑ k ∈ range (N+1), wt μ N k = 1 := by
  have := moment_identity μ h N 0 (Nat.zero_le _)
  simp only [Nat.descFactorial_zero, Nat.cast_one, mul_one, one_mul, h00] at this
  exact this

theorem prodbound (i : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (N : ℕ) (hN : 0 < N)
    (hiN : 2 * i ≤ N) :
    |x ^ i - ∏ r ∈ range i, (x - r / N) / (1 - r / N)| ≤ 2 * i * i / N ∧
      |∏ r ∈ range i, (x - r / N) / (1 - r / N)| ≤ 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hNr : (0:ℝ) < N := by exact_mod_cast hN
    have hi2 : 2 * (i:ℝ) ≤ N := by exact_mod_cast (by omega : 2 * i ≤ N)
    have hden : (1:ℝ) / 2 ≤ 1 - i / N := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)] at *
      have : (i:ℝ) / N ≤ 1 / 2 := by rw [div_le_iff₀ hNr]; linarith
      linarith
    have hdpos : 0 < 1 - (i:ℝ) / N := by linarith
    set y := (x - i / N) / (1 - i / N) with hy
    have hy1 : |y| ≤ 1 := by
      rw [hy, abs_div, abs_of_pos hdpos, div_le_one hdpos, abs_le]
      constructor
      · have : (i:ℝ) / N ≤ 1 / 2 := by rw [div_le_iff₀ hNr]; linarith
        linarith
      · linarith
    have hxy : |x - y| ≤ 2 * i / N := by
      have : x - y = (i / N) * (1 - x) / (1 - i / N) := by
        rw [hy, eq_div_iff hdpos.ne', sub_mul, div_mul_cancel₀ _ hdpos.ne']; ring
      rw [this, abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ i / N), abs_of_nonneg (by linarith : 0 ≤ 1 - x)]
      have h1 : (i:ℝ) / N * (1 - x) ≤ i / N := by
        have : 0 ≤ (i:ℝ) / N := by positivity
        nlinarith
      have h2 : (i:ℝ) / N ≤ 2 * i / N * (1 - i / N) := by
        have : 0 ≤ (i:ℝ) / N := by positivity
        rw [show 2 * (i:ℝ) / N = 2 * (i / N) by ring]
        nlinarith
      linarith
    rw [prod_range_succ, pow_succ]
    set P := ∏ r ∈ range i, (x - r / N) / (1 - r / N)
    constructor
    · have : x ^ i * x - P * y = (x ^ i - P) * x + P * (x - y) := by ring
      rw [this]
      calc |(x ^ i - P) * x + P * (x - y)| ≤ |(x ^ i - P) * x| + |P * (x - y)| := abs_add_le _ _
        _ ≤ 2 * i * i / N + 2 * i / N := by
          rw [abs_mul, abs_mul]
          gcongr
          · calc |x ^ i - P| * |x| ≤ |x ^ i - P| * 1 := by
                  gcongr; rw [abs_of_nonneg hx0]; exact hx1
              _ ≤ _ := by rw [mul_one]; exact ih1
          · calc |P| * |x - y| ≤ 1 * |x - y| := by gcongr
              _ ≤ _ := by rw [one_mul]; exact hxy
        _ ≤ 2 * ((i:ℕ) + 1 : ℕ) * ((i:ℕ) + 1 : ℕ) / N := by
          rw [← add_div, div_le_div_iff_of_pos_right hNr]
          push_cast
          nlinarith
    · rw [abs_mul]
      calc |P| * |y| ≤ 1 * 1 := by gcongr
        _ = 1 := by ring

theorem grid_prod (k i N : ℕ) (hiN : i ≤ N) (hN : 0 < N) :
    ∏ r ∈ range i, (((k:ℝ) / N) - r / N) / (1 - r / N) =
      (k.descFactorial i : ℝ) / (N.descFactorial i : ℝ) := by
  rw [cast_descFactorial_prod, cast_descFactorial_prod, ← prod_div_distrib]
  refine prod_congr rfl fun r hr => ?_
  have hr' : r < N := by have := mem_range.1 hr; omega
  have hNr : (N:ℝ) ≠ 0 := by positivity
  have hNr2 : (N:ℝ) - r ≠ 0 := by
    have : (r:ℝ) < N := by exact_mod_cast hr'
    linarith
  field_simp

theorem mono_bound (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1)
    (i N : ℕ) (hN : 0 < N) (hiN : 2 * i ≤ N) :
    |LN μ N (fun x => x ^ i) - μ i 0| ≤ 2 * i * i / N := by
  have hD : (N.descFactorial i : ℝ) ≠ 0 := by
    have : N.descFactorial i ≠ 0 := by
      rw [Ne, Nat.descFactorial_eq_zero_iff_lt]; omega
    exact_mod_cast this
  have hmom := moment_identity μ h N i (by omega)
  have hμi : μ i 0 = ∑ k ∈ range (N+1), wt μ N k *
      ∏ r ∈ range i, (((k:ℝ) / N) - r / N) / (1 - r / N) := by
    have : μ i 0 = (∑ k ∈ range (N+1), (N.choose k : ℝ) * μ k (N - k) *
        (k.descFactorial i : ℝ)) / (N.descFactorial i : ℝ) := by
      rw [hmom]; field_simp
    rw [this, sum_div]
    refine sum_congr rfl fun k _ => ?_
    rw [grid_prod k i N (by omega) hN, wt]
    ring
  rw [hμi, LN, ← sum_sub_distrib]
  calc |∑ k ∈ range (N+1), (wt μ N k * ((k:ℝ) / N) ^ i - wt μ N k *
        ∏ r ∈ range i, (((k:ℝ) / N) - r / N) / (1 - r / N))|
      ≤ ∑ k ∈ range (N+1), |wt μ N k * ((k:ℝ) / N) ^ i - wt μ N k *
        ∏ r ∈ range i, (((k:ℝ) / N) - r / N) / (1 - r / N)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (N+1), wt μ N k * (2 * i * i / N) := by
      refine sum_le_sum fun k hk => ?_
      have hk' : k ≤ N := by have := mem_range.1 hk; omega
      have hx0 : (0:ℝ) ≤ k / N := by positivity
      have hx1 : (k:ℝ) / N ≤ 1 := by
        rw [div_le_one (by exact_mod_cast hN)]; exact_mod_cast hk'
      rw [← mul_sub, abs_mul, abs_of_nonneg (wt_nonneg μ hμ N k)]
      gcongr
      · exact wt_nonneg μ hμ N k
      · exact (prodbound i _ hx0 hx1 N hN hiN).1
    _ = 2 * i * i / N := by rw [← sum_mul, wt_sum μ h h00, one_mul]

theorem mono_tendsto (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) (i : ℕ) :
    Tendsto (fun N => LN μ N (fun x => x ^ i)) atTop (𝓝 (μ i 0)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (2 * i * i : ℝ))
  filter_upwards [eventually_ge_atTop (2 * i + 1)] with N hN
  rw [Real.norm_eq_abs]
  exact mono_bound μ hμ h h00 i N (by omega) (by omega)

abbrev I01 : Set ℝ := Set.Icc (0:ℝ) 1

noncomputable def LF (μ : ℕ → ℕ → ℝ) (N : ℕ) (f : C(I01, ℝ)) : ℝ :=
  ∑ k ∈ range (N+1), wt μ N k * f (Set.projIcc 0 1 zero_le_one ((k:ℝ) / N))

theorem LF_eq (μ : ℕ → ℕ → ℝ) (N : ℕ) (f : C(I01, ℝ)) (g : ℝ → ℝ)
    (hfg : ∀ y : I01, f y = g y) : LF μ N f = LN μ N g := by
  unfold LF LN
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N := by have := mem_range.1 hk; omega
  have hmem : (k:ℝ) / N ∈ I01 := by
    refine ⟨by positivity, ?_⟩
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp
    · rw [div_le_one (by exact_mod_cast h0)]; exact_mod_cast hk'
  rw [Set.projIcc_of_mem _ hmem, hfg]

theorem LF_add (μ : ℕ → ℕ → ℝ) (N : ℕ) (f g : C(I01, ℝ)) :
    LF μ N (f + g) = LF μ N f + LF μ N g := by
  simp only [LF, ContinuousMap.add_apply, mul_add, sum_add_distrib]

theorem LF_sub (μ : ℕ → ℕ → ℝ) (N : ℕ) (f g : C(I01, ℝ)) :
    LF μ N (f - g) = LF μ N f - LF μ N g := by
  simp only [LF, ContinuousMap.sub_apply, mul_sub, sum_sub_distrib]

theorem LF_smul (μ : ℕ → ℕ → ℝ) (N : ℕ) (c : ℝ) (f : C(I01, ℝ)) :
    LF μ N (c • f) = c * LF μ N f := by
  simp only [LF, ContinuousMap.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun k _ => by ring

theorem LF_nonneg (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j) (N : ℕ) (f : C(I01, ℝ))
    (hf : ∀ y, 0 ≤ f y) : 0 ≤ LF μ N f :=
  sum_nonneg fun k _ => mul_nonneg (wt_nonneg μ hμ N k) (hf _)

theorem LF_abs_le (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) (N : ℕ) (f : C(I01, ℝ)) :
    |LF μ N f| ≤ ‖f‖ := by
  unfold LF
  calc |∑ k ∈ range (N+1), wt μ N k * f (Set.projIcc 0 1 zero_le_one ((k:ℝ) / N))|
      ≤ ∑ k ∈ range (N+1), |wt μ N k * f (Set.projIcc 0 1 zero_le_one ((k:ℝ) / N))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (N+1), wt μ N k * ‖f‖ := by
      refine sum_le_sum fun k _ => ?_
      rw [abs_mul, abs_of_nonneg (wt_nonneg μ hμ N k)]
      gcongr
      · exact wt_nonneg μ hμ N k
      · exact (Real.norm_eq_abs _ ▸ f.norm_coe_le_norm _)
    _ = ‖f‖ := by rw [← sum_mul, wt_sum μ h h00, one_mul]

theorem LF_poly_tendsto (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) (p : Polynomial ℝ) :
    Tendsto (fun N => LF μ N (p.toContinuousMapOn I01)) atTop
      (𝓝 (∑ d ∈ range (p.natDegree + 1), p.coeff d * μ d 0)) := by
  have e : ∀ N, LF μ N (p.toContinuousMapOn I01) =
      ∑ d ∈ range (p.natDegree + 1), p.coeff d * LN μ N (fun x => x ^ d) := by
    intro N
    rw [LF_eq μ N _ (fun x => p.eval x) (fun y => rfl)]
    unfold LN
    simp_rw [Polynomial.eval_eq_sum_range, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun d _ => sum_congr rfl fun k _ => by ring
  simp_rw [e]
  exact tendsto_finset_sum _ fun d _ => (mono_tendsto μ hμ h h00 d).const_mul _

theorem LF_cauchy (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) (f : C(I01, ℝ)) :
    CauchySeq (fun N => LF μ N f) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hf : f ∈ (polynomialFunctions I01).topologicalClosure := by
    rw [polynomialFunctions_closure_eq_top]; trivial
  rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe, Metric.mem_closure_iff] at hf
  obtain ⟨b, hb, hfb⟩ := hf (ε / 3) (by positivity)
  rw [polynomialFunctions_coe] at hb
  obtain ⟨p, rfl⟩ := hb
  have hc := (LF_poly_tendsto μ hμ h h00 p).cauchySeq
  rw [Metric.cauchySeq_iff'] at hc
  obtain ⟨N0, hN0⟩ := hc (ε / 3) (by positivity)
  refine ⟨N0, fun n hn => ?_⟩
  have h1 := hN0 n hn
  rw [Real.dist_eq] at h1 ⊢
  rw [dist_eq_norm] at hfb
  have a1 := LF_abs_le μ hμ h h00 n (f - Polynomial.toContinuousMapOnAlgHom I01 p)
  have a2 := LF_abs_le μ hμ h h00 N0 (f - Polynomial.toContinuousMapOnAlgHom I01 p)
  rw [LF_sub] at a1 a2
  have : Polynomial.toContinuousMapOnAlgHom I01 p = p.toContinuousMapOn I01 := rfl
  rw [this] at a1 a2 hfb
  set A := LF μ n f
  set B := LF μ n (p.toContinuousMapOn I01)
  set C := LF μ N0 (p.toContinuousMapOn I01)
  set D := LF μ N0 f
  have h3 := abs_add_three (A - B) (B - C) (C - D)
  rw [show A - B + (B - C) + (C - D) = A - D by ring] at h3
  calc |A - D| < ε / 3 + ε / 3 + ε / 3 := by rw [abs_sub_comm D C] at a2; linarith
    _ = ε := by ring

noncomputable def LamF (μ : ℕ → ℕ → ℝ) (f : C(I01, ℝ)) : ℝ :=
  limUnder atTop (fun N => LF μ N f)

theorem LamF_tendsto (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) (f : C(I01, ℝ)) :
    Tendsto (fun N => LF μ N f) atTop (𝓝 (LamF μ f)) := by
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (LF_cauchy μ hμ h h00 f)
  unfold LamF
  exact tendsto_nhds_limUnder ⟨a, ha⟩

section LamFProps
variable (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1)
include hμ h h00

theorem LamF_add (f g : C(I01, ℝ)) : LamF μ (f + g) = LamF μ f + LamF μ g := by
  refine tendsto_nhds_unique (LamF_tendsto μ hμ h h00 (f + g)) ?_
  simp_rw [LF_add]
  exact (LamF_tendsto μ hμ h h00 f).add (LamF_tendsto μ hμ h h00 g)

theorem LamF_sub (f g : C(I01, ℝ)) : LamF μ (f - g) = LamF μ f - LamF μ g := by
  refine tendsto_nhds_unique (LamF_tendsto μ hμ h h00 (f - g)) ?_
  simp_rw [LF_sub]
  exact (LamF_tendsto μ hμ h h00 f).sub (LamF_tendsto μ hμ h h00 g)

theorem LamF_smul (c : ℝ) (f : C(I01, ℝ)) : LamF μ (c • f) = c * LamF μ f := by
  refine tendsto_nhds_unique (LamF_tendsto μ hμ h h00 (c • f)) ?_
  simp_rw [LF_smul]
  exact (LamF_tendsto μ hμ h h00 f).const_mul c

theorem LamF_nonneg (f : C(I01, ℝ)) (hf : ∀ y, 0 ≤ f y) : 0 ≤ LamF μ f :=
  ge_of_tendsto' (LamF_tendsto μ hμ h h00 f) fun N => LF_nonneg μ hμ N f hf

end LamFProps

noncomputable def gfun (i j : ℕ) : C(I01, ℝ) :=
  ⟨fun y => (y:ℝ) ^ i * (1 - (y:ℝ)) ^ j, by fun_prop⟩

theorem LamF_g (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) :
    ∀ j i, LamF μ (gfun i j) = μ i j := by
  intro j
  induction j with
  | zero =>
    intro i
    refine tendsto_nhds_unique (LamF_tendsto μ hμ h h00 _) ?_
    have e : ∀ N, LF μ N (gfun i 0) = LN μ N (fun x => x ^ i) :=
      fun N => LF_eq μ N _ _ (fun y => by simp [gfun])
    simp_rw [e]
    exact mono_tendsto μ hμ h h00 i
  | succ j ih =>
    intro i
    have e : gfun i (j+1) = gfun i j - gfun (i+1) j := by
      ext y; simp only [gfun, ContinuousMap.coe_mk, ContinuousMap.sub_apply]; ring
    rw [e, LamF_sub μ hμ h h00, ih, ih, h i j]
    ring

noncomputable def LamC (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) :
    C_c(I01, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => LamF μ f.toContinuousMap
      map_add' := fun f g => LamF_add μ hμ h h00 f.toContinuousMap g.toContinuousMap
      map_smul' := fun c f => LamF_smul μ hμ h h00 c f.toContinuousMap }
    (fun f hf => LamF_nonneg μ hμ h h00 _ (fun y => by
      have := CompactlySupportedContinuousMap.le_def.1 hf y
      simpa using this))

theorem hausdorff_exists (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j) (h00 : μ 0 0 = 1)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) :
    ∃ F : Measure ℝ, IsProbabilityMeasure F ∧ F (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ i j, μ i j = ∫ x, x ^ i * (1 - x) ^ j ∂F := by
  set Λp := LamC μ hμ h h00
  set ν := RealRMK.rieszMeasure Λp
  have hg : ∀ i j, ∫ y, ((y:ℝ) ^ i * (1 - (y:ℝ)) ^ j) ∂ν = μ i j := by
    intro i j
    have := RealRMK.integral_rieszMeasure Λp
      (CompactlySupportedContinuousMap.continuousMapEquiv (gfun i j))
    rw [← LamF_g μ hμ h h00 j i]
    exact this
  have hν1 : ν Set.univ = 1 := by
    have := hg 0 0
    simp only [pow_zero, mul_one, integral_const, smul_eq_mul, h00] at this
    rw [measureReal_def, ENNReal.toReal_eq_one_iff] at this
    exact this
  refine ⟨ν.map Subtype.val, ?_, ?_, ?_⟩
  · constructor
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ, hν1]
  · rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc.compl]
    have : (Subtype.val ⁻¹' (Set.Icc (0:ℝ) 1)ᶜ : Set I01) = ∅ := by
      ext y; simp [y.2]
    rw [this, measure_empty]
  · intro i j
    rw [integral_map measurable_subtype_coe.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop)), hg]

theorem eq_24_iff_eq_25_core (μ : ℕ → ℕ → ℝ)
    (hμ : ∀ i j, 0 ≤ μ i j) (h00 : μ 0 0 = 1) :
    (∀ i j, μ i j = μ (i + 1) j + μ i (j + 1)) ↔
      ∃ F : Measure ℝ, IsProbabilityMeasure F ∧ F (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ i j, μ i j = ∫ x, x ^ i * (1 - x) ^ j ∂F := by
  constructor
  · exact hausdorff_exists μ hμ h00
  · rintro ⟨F, hF, hF0, hmom⟩ i j
    have hres : F.restrict (Set.Icc (0:ℝ) 1) = F := by
      apply Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff]
      exact hF0
    have hint : ∀ a b : ℕ, Integrable (fun x : ℝ => x ^ a * (1 - x) ^ b) F := by
      intro a b
      rw [← hres]
      exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
    rw [hmom, hmom, hmom, ← integral_add (hint _ _) (hint _ _)]
    congr 1
    funext x
    ring

end Hausdorff


section Bij

theorem lamOf_rec (Λ : Measure ℝ) [IsFiniteMeasure Λ] (b k : ℕ) (h2 : 2 ≤ k) (hkb : k ≤ b) :
    lamOf Λ b k = lamOf Λ (b+1) k + lamOf Λ (b+1) (k+1) := by
  unfold lamOf
  have hint : ∀ a c : ℕ, IntegrableOn (fun x : ℝ => x ^ a * (1 - x) ^ c) (Set.Icc 0 1) Λ :=
    fun a c => (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
  rw [show b + 1 - k = (b - k) + 1 by omega, show k + 1 - 2 = (k - 2) + 1 by omega,
    show b + 1 - (k + 1) = b - k by omega, ← integral_add (hint _ _) (hint _ _)]
  congr 1; funext x; ring

theorem lam_le (lam : ℕ → ℕ → ℝ) (hlam : ∀ b k, 2 ≤ k → k ≤ b → 0 ≤ lam b k)
    (hrec : ∀ b k, 2 ≤ k → k ≤ b → lam b k = lam (b + 1) k + lam (b + 1) (k + 1)) :
    ∀ b, 2 ≤ b → ∀ k, 2 ≤ k → k ≤ b → lam b k ≤ lam 2 2 := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => intro k h2 hk; rw [show k = 2 by omega]
  | succ b hb ih =>
    intro k h2 hk
    rcases Nat.lt_or_ge k (b + 1) with hkb | hkb
    · have e := hrec b k h2 (by omega)
      have := hlam (b+1) (k+1) (by omega) (by omega)
      have := ih k h2 (by omega)
      linarith
    · have e := hrec b b hb le_rfl
      have := hlam (b+1) b hb (by omega)
      have := ih b hb le_rfl
      rw [show k = b + 1 by omega]
      linarith

theorem measure_eq_of_moments (Λ1 Λ2 : Measure ℝ) [IsFiniteMeasure Λ1] [IsFiniteMeasure Λ2]
    (h1 : Λ1 (Set.Icc (0:ℝ) 1)ᶜ = 0) (h2 : Λ2 (Set.Icc (0:ℝ) 1)ᶜ = 0)
    (hm : ∀ i : ℕ, ∫ x in Set.Icc (0:ℝ) 1, x ^ i ∂Λ1 = ∫ x in Set.Icc (0:ℝ) 1, x ^ i ∂Λ2) :
    Λ1 = Λ2 := by
  have hr1 : Λ1.restrict (Set.Icc 0 1) = Λ1 :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h1)
  have hr2 : Λ2.restrict (Set.Icc 0 1) = Λ2 :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact h2)
  have hcont : ∀ (Λ : Measure ℝ) [IsFiniteMeasure Λ] (g : ℝ → ℝ), Continuous g →
      Integrable g (Λ.restrict (Set.Icc 0 1)) :=
    fun Λ _ g hg => hg.continuousOn.integrableOn_compact isCompact_Icc
  have hpoly : ∀ p : Polynomial ℝ, ∫ x in Set.Icc (0:ℝ) 1, p.eval x ∂Λ1 =
      ∫ x in Set.Icc (0:ℝ) 1, p.eval x ∂Λ2 := by
    intro p
    simp_rw [Polynomial.eval_eq_sum_range]
    rw [integral_finset_sum _ (fun d _ => hcont Λ1 _ (by fun_prop)),
      integral_finset_sum _ (fun d _ => hcont Λ2 _ (by fun_prop))]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [integral_const_mul, integral_const_mul, hm]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [← hr1, ← hr2]
  apply eq_of_forall_dist_le
  intro ε hε
  set R1 := Λ1.real (Set.Icc (0:ℝ) 1)
  set R2 := Λ2.real (Set.Icc (0:ℝ) 1)
  have hR1 : 0 ≤ R1 := measureReal_nonneg
  have hR2 : 0 ≤ R2 := measureReal_nonneg
  set M := R1 + R2 + 1 with hMdef
  have hM : 0 < M := by positivity
  let g : C(I01, ℝ) := ⟨fun y => f y, f.continuous.comp continuous_subtype_val⟩
  have hg : g ∈ (polynomialFunctions I01).topologicalClosure := by
    rw [polynomialFunctions_closure_eq_top]; trivial
  rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe, Metric.mem_closure_iff] at hg
  obtain ⟨b, hb, hgb⟩ := hg (ε / M) (by positivity)
  rw [polynomialFunctions_coe] at hb
  obtain ⟨p, rfl⟩ := hb
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1, ‖f x - p.eval x‖ ≤ ε / M := by
    intro x hx
    have := ContinuousMap.norm_coe_le_norm (g - Polynomial.toContinuousMapOnAlgHom I01 p) ⟨x, hx⟩
    rw [dist_eq_norm] at hgb
    have e : (g - Polynomial.toContinuousMapOnAlgHom I01 p) ⟨x, hx⟩ = f x - p.eval x := rfl
    rw [e] at this
    linarith
  have e1 : ‖∫ x in Set.Icc (0:ℝ) 1, f x ∂Λ1 - ∫ x in Set.Icc (0:ℝ) 1, p.eval x ∂Λ1‖ ≤
      ε / M * R1 := by
    rw [← integral_sub (f.integrable _) (hcont Λ1 _ (by fun_prop))]
    exact norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hpt
  have e2 : ‖∫ x in Set.Icc (0:ℝ) 1, f x ∂Λ2 - ∫ x in Set.Icc (0:ℝ) 1, p.eval x ∂Λ2‖ ≤
      ε / M * R2 := by
    rw [← integral_sub (f.integrable _) (hcont Λ2 _ (by fun_prop))]
    exact norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hpt
  rw [Real.norm_eq_abs] at e1 e2
  rw [Real.dist_eq, ← hpoly p] at *
  have key : ε / M * R1 + ε / M * R2 ≤ ε := by
    rw [← mul_add, div_mul_eq_mul_div, div_le_iff₀ hM]
    nlinarith
  have := abs_sub_le (∫ x in Set.Icc (0:ℝ) 1, f x ∂Λ1)
    (∫ x in Set.Icc (0:ℝ) 1, p.eval x ∂Λ1) (∫ x in Set.Icc (0:ℝ) 1, f x ∂Λ2)
  rw [abs_sub_comm (∫ x in Set.Icc (0:ℝ) 1, p.eval x ∂Λ1)] at this
  linarith

theorem lemma_18_bijection_core :
    (∀ Λ : Measure ℝ, IsFiniteMeasure Λ → Λ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      Consistent (lamOf Λ)) ∧
    (∀ lam : ℕ → ℕ → ℝ,
      (∀ b k, 2 ≤ k → k ≤ b → 0 ≤ lam b k) →
      Consistent lam →
      ∃! Λ : Measure ℝ,
        IsFiniteMeasure Λ ∧ Λ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
          ∀ b k, 2 ≤ k → k ≤ b → lam b k = lamOf Λ b k) := by
  refine ⟨fun Λ hΛ _ => (lemma_18_consistent_iff_core _).2
    (fun b k h2 hkb => lamOf_rec Λ b k h2 hkb), ?_⟩
  intro lam hlam hc
  have hrec := (lemma_18_consistent_iff_core lam).1 hc
  have hex : ∃ Λ : Measure ℝ, IsFiniteMeasure Λ ∧ Λ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ b k, 2 ≤ k → k ≤ b → lam b k = lamOf Λ b k := by
    rcases (hlam 2 2 le_rfl le_rfl).eq_or_lt with hc0 | hcpos
    · refine ⟨0, inferInstance, by simp, fun b k h2 hkb => ?_⟩
      have h1 := lam_le lam hlam hrec b (by omega) k h2 hkb
      have h3 := hlam b k h2 hkb
      simp only [lamOf, Measure.restrict_zero, integral_zero_measure]
      linarith
    · set c := lam 2 2 with hcdef
      let μ : ℕ → ℕ → ℝ := fun i j => lam (i + j + 2) (i + 2) / c
      have hμ : ∀ i j, 0 ≤ μ i j := fun i j =>
        div_nonneg (hlam _ _ (by omega) (by omega)) hcpos.le
      have h00 : μ 0 0 = 1 := by simp only [μ]; exact div_self hcpos.ne'
      have hr : ∀ i j, μ i j = μ (i + 1) j + μ i (j + 1) := by
        intro i j
        simp only [μ]
        rw [← add_div, show i + 1 + j + 2 = i + j + 2 + 1 by ring,
          show i + 1 + 2 = i + 2 + 1 by ring, show i + (j + 1) + 2 = i + j + 2 + 1 by ring,
          hrec (i + j + 2) (i + 2) (by omega) (by omega)]
        ring
      obtain ⟨F, hF, hF0, hmom⟩ := hausdorff_exists μ hμ h00 hr
      have hres : F.restrict (Set.Icc 0 1) = F :=
        Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hF0)
      refine ⟨ENNReal.ofReal c • F, ⟨?_⟩, ?_, fun b k h2 hkb => ?_⟩
      · rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
      · rw [Measure.smul_apply, hF0, smul_zero]
      · unfold lamOf
        rw [Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hcpos.le, hres,
          ← hmom (k - 2) (b - k)]
        simp only [μ, smul_eq_mul]
        rw [show k - 2 + (b - k) + 2 = b by omega, show k - 2 + 2 = k by omega]
        field_simp
  obtain ⟨Λ, hfin, h0, hl⟩ := hex
  refine ⟨Λ, ⟨hfin, h0, hl⟩, ?_⟩
  rintro Λ' ⟨hfin', h0', hl'⟩
  apply measure_eq_of_moments Λ' Λ h0' h0
  intro i
  have := (hl' (i + 2) (i + 2) (by omega) le_rfl).symm.trans (hl (i + 2) (i + 2) (by omega) le_rfl)
  unfold lamOf at this
  simpa using this

end Bij

end LambdaCoalescent.Rates

open LambdaCoalescent.Rates
open MeasureTheory

theorem solution :
    (∀ Λ : Measure ℝ, IsFiniteMeasure Λ → Λ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      Consistent (lamOf Λ)) ∧
    (∀ lam : ℕ → ℕ → ℝ,
      (∀ b k, 2 ≤ k → k ≤ b → 0 ≤ lam b k) →
      Consistent lam →
      ∃! Λ : Measure ℝ,
        IsFiniteMeasure Λ ∧ Λ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
          ∀ b k, 2 ≤ k → k ≤ b → lam b k = lamOf Λ b k) := by
  exact lemma_18_bijection_core
