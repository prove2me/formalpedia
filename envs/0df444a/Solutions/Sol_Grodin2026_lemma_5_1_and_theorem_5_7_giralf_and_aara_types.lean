-- Prove2me | solution 1 for Grodin2026.lemma_5_1_and_theorem_5_7_giralf_and_aara_types
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T17:23:28.470716+00:00
-- url     : https://prove2.me/submissions/e041c75a-ddde-4da2-859f-c39e60422fe3

import Definitions.Def_Grodin2026_Giralf

open Grodin2026

/-! ## Helper Lemmas for `insert` and `isort` (Examples 5.2 & 5.3) -/

private theorem insertCostTop_spec (p x : Nat) (l : List Nat) :
    (insertCostTop x l).2 = insertPure x l ∧
    (insertCostTop x l).2.length = l.length + 1 ∧
    (insertCostTop x l).1 + (insertCostTop x l).2.length * p ≤ l.length * (1 + p) + p := by
  induction l with
  | nil =>
      simp [insertCostTop, insertPure]
  | cons y ys ih =>
      rcases ih with ⟨h_val, h_len, h_cost⟩
      by_cases hxy : x ≤ y
      · simp only [insertCostTop, insertPure, hxy, ↓reduceIte, List.length_cons, true_and]
        calc 1 + (ys.length + 1 + 1) * p
          _ = 1 + ys.length * p + p + p := by
            rw [Nat.right_distrib, Nat.right_distrib]
            omega
          _ ≤ (ys.length + 1) * (1 + p) + p := by
            rw [Nat.right_distrib, Nat.left_distrib]
            omega
      · simp only [insertCostTop, insertPure, hxy, ↓reduceIte, List.length_cons]
        refine ⟨congrArg (List.cons y) h_val, congrArg (· + 1) h_len, ?_⟩
        rw [h_len] at h_cost ⊢
        calc 1 + (insertCostTop x ys).1 + (ys.length + 1 + 1) * p
          _ = 1 + ((insertCostTop x ys).1 + (ys.length + 1) * p) + p := by
            rw [Nat.right_distrib]
            omega
          _ ≤ 1 + (ys.length * (1 + p) + p) + p := by
            omega
          _ = (ys.length + 1) * (1 + p) + p := by
            rw [Nat.right_distrib]
            omega

private def insertGiralfJudgment (p x : Nat) :
    GiralfSemJudgment (CList1Comp (1 + p) Nat) (CList1Comp p Nat) p where
  hom_top := insertTopHom x
  hom_abs := insertAbsHom x
  lax_comm := fun ⟨c₀, l⟩ => by
    rcases insertCostTop_spec p x l with ⟨h_val, _, h_cost⟩
    refine ⟨?_, h_val⟩
    change c₀ + (insertCostTop x l).1 + (insertCostTop x l).2.length * p ≤
      p + (c₀ + l.length * (1 + p))
    omega

private theorem isortCostTop_spec (l : List Nat) :
    (isortCostTop l).2 = isortPure l ∧
    (isortCostTop l).2.length = l.length ∧
    (isortCostTop l).1 ≤ binom2 l.length := by
  induction l with
  | nil =>
      simp [isortCostTop, isortPure, binom2]
  | cons x xs ih =>
      rcases ih with ⟨h_val, h_len, h_cost⟩
      rcases insertCostTop_spec 0 x (isortCostTop xs).2 with ⟨h_ins_val, h_ins_len, h_ins_cost⟩
      simp only [isortCostTop, isortPure, List.length_cons, binom2]
      refine ⟨?_, ?_, ?_⟩
      · rw [h_ins_val, h_val]
      · rw [h_ins_len, h_len]
      · rw [h_len] at h_ins_cost
        omega

private def isortGiralfJudgment :
    GiralfSemJudgment (CList2Comp 0 1 Nat) (CList1Comp 0 Nat) 0 where
  hom_top := isortTopHom
  hom_abs := isortAbsHom
  lax_comm := fun ⟨c₀, l⟩ => by
    rcases isortCostTop_spec l with ⟨h_val, _, h_cost⟩
    refine ⟨?_, h_val⟩
    change c₀ + (isortCostTop l).1 + (isortCostTop l).2.length * 0 ≤
      0 + (c₀ + (l.length * 0 + binom2 l.length * 1))
    omega

/-! ## Helper Lemmas for `CList2Ind` and Theorem 5.7 -/

private theorem clist2Ind_credits_eq {α : Type} {p₁ p₂ : Nat} (t : CList2Ind α p₁ p₂) :
    t.credits = t.toList.length * p₁ + binom2 t.toList.length * p₂ := by
  induction t with
  | @nil c₁ c₂ =>
      simp [CList2Ind.credits, CList2Ind.toList, binom2]
  | @cons c₁ c₂ x tail ih =>
      simp only [CList2Ind.credits, CList2Ind.toList, List.length_cons, binom2]
      rw [ih]
      have h₁ : tail.toList.length * (c₂ + c₁) =
          tail.toList.length * c₂ + tail.toList.length * c₁ :=
        Nat.left_distrib tail.toList.length c₂ c₁
      have h₂ : (tail.toList.length + 1) * c₁ = tail.toList.length * c₁ + c₁ := by
        rw [Nat.right_distrib, Nat.one_mul]
      have h₃ : (tail.toList.length + binom2 tail.toList.length) * c₂ =
          tail.toList.length * c₂ + binom2 tail.toList.length * c₂ :=
        Nat.right_distrib tail.toList.length (binom2 tail.toList.length) c₂
      omega

private theorem clist2Ind_toList_ofList {α : Type} (l : List α) :
    ∀ c₁ c₂ : Nat, (CList2Ind.ofList c₁ c₂ l).toList = l := by
  induction l with
  | nil =>
      intro c₁ c₂
      rfl
  | cons x xs ih =>
      intro c₁ c₂
      simp [CList2Ind.ofList, CList2Ind.toList, ih (c₂ + c₁) c₂]

private theorem clist2Ind_ofList_toList {α : Type} {c₁ c₂ : Nat} (t : CList2Ind α c₁ c₂) :
    CList2Ind.ofList c₁ c₂ t.toList = t := by
  induction t with
  | nil => rfl
  | @cons c₁ c₂ x tail ih =>
      simp [CList2Ind.toList, CList2Ind.ofList, ih]

private theorem clist2ElemPotentialSum_eq {α : Type} (phi : α → Nat) {c₁ c₂ : Nat}
    (t : CList2Ind α c₁ c₂) :
    clist2ElemPotentialSum phi t = listPotentialSum phi t.toList := by
  induction t with
  | nil => rfl
  | cons x tail ih =>
      simp [clist2ElemPotentialSum, CList2Ind.toList, listPotentialSum, ih]

private def freeCompPotentialEquiv (X : Type) :
    CompEquiv (FreeComp X) (PotentialType X (fun _ => 0)) where
  toHom := {
    hom_top := CostHom.id (FreeCostAlg X)
    hom_abs := CostHom.id (FreeCostAlg X)
    comm := fun ⟨c, _⟩ => Prod.ext (Nat.add_zero c) rfl
  }
  invHom := {
    hom_top := CostHom.id (FreeCostAlg X)
    hom_abs := CostHom.id (FreeCostAlg X)
    comm := fun ⟨c, _⟩ => Prod.ext (Nat.add_zero c).symm rfl
  }
  left_inv := rfl
  right_inv := rfl

private def creditCompCongr (p : Nat) {A B : CompType} (e : CompEquiv A B) :
    CompEquiv (CreditComp p A) (CreditComp p B) where
  toHom := CreditComp.map p e.toHom
  invHom := CreditComp.map p e.invHom
  left_inv := by
    ext x
    · exact congrArg (fun h : CompHom A A => h.hom_top.fn x) e.left_inv
    · exact congrArg (fun h : CompHom A A => h.hom_abs.fn x) e.left_inv
  right_inv := by
    ext x
    · exact congrArg (fun h : CompHom B B => h.hom_top.fn x) e.right_inv
    · exact congrArg (fun h : CompHom B B => h.hom_abs.fn x) e.right_inv

private def creditPotentialEquiv (p : Nat) (X : Type) (Phi : X → Nat) :
    CompEquiv (CreditComp p (PotentialType X Phi)) (PotentialType X (fun x => p + Phi x)) where
  toHom := {
    hom_top := CostHom.id (FreeCostAlg X)
    hom_abs := CostHom.id (FreeCostAlg X)
    comm := fun ⟨c, x⟩ => by
      apply Prod.ext
      · change c + (p + Phi x) = p + (c + Phi x)
        omega
      · rfl
  }
  invHom := {
    hom_top := CostHom.id (FreeCostAlg X)
    hom_abs := CostHom.id (FreeCostAlg X)
    comm := fun ⟨c, x⟩ => by
      apply Prod.ext
      · change p + (c + Phi x) = c + (p + Phi x)
        omega
      · rfl
  }
  left_inv := rfl
  right_inv := rfl

private def sumCompCongr {A₁ A₂ B₁ B₂ : CompType}
    (e₁ : CompEquiv A₁ B₁) (e₂ : CompEquiv A₂ B₂) :
    CompEquiv (SumComp A₁ A₂) (SumComp B₁ B₂) where
  toHom := {
    hom_top := {
      fn := fun s =>
        match s with
        | .inl a₁ => .inl (e₁.toHom.hom_top.fn a₁)
        | .inr a₂ => .inr (e₂.toHom.hom_top.fn a₂)
      map_charge := fun c s =>
        match s with
        | .inl a₁ => congrArg Sum.inl (e₁.toHom.hom_top.map_charge c a₁)
        | .inr a₂ => congrArg Sum.inr (e₂.toHom.hom_top.map_charge c a₂)
      mono := by
        intro s₁ s₂ h
        cases s₁ <;> cases s₂
        · exact e₁.toHom.hom_top.mono h
        · exact False.elim h
        · exact False.elim h
        · exact e₂.toHom.hom_top.mono h
    }
    hom_abs := {
      fn := fun s =>
        match s with
        | .inl a₁ => .inl (e₁.toHom.hom_abs.fn a₁)
        | .inr a₂ => .inr (e₂.toHom.hom_abs.fn a₂)
      map_charge := fun c s =>
        match s with
        | .inl a₁ => congrArg Sum.inl (e₁.toHom.hom_abs.map_charge c a₁)
        | .inr a₂ => congrArg Sum.inr (e₂.toHom.hom_abs.map_charge c a₂)
      mono := by
        intro s₁ s₂ h
        cases s₁ <;> cases s₂
        · exact e₁.toHom.hom_abs.mono h
        · exact False.elim h
        · exact False.elim h
        · exact e₂.toHom.hom_abs.mono h
    }
    comm := fun s =>
      match s with
      | .inl a₁ => congrArg Sum.inl (e₁.toHom.comm a₁)
      | .inr a₂ => congrArg Sum.inr (e₂.toHom.comm a₂)
  }
  invHom := {
    hom_top := {
      fn := fun s =>
        match s with
        | .inl b₁ => .inl (e₁.invHom.hom_top.fn b₁)
        | .inr b₂ => .inr (e₂.invHom.hom_top.fn b₂)
      map_charge := fun c s =>
        match s with
        | .inl b₁ => congrArg Sum.inl (e₁.invHom.hom_top.map_charge c b₁)
        | .inr b₂ => congrArg Sum.inr (e₂.invHom.hom_top.map_charge c b₂)
      mono := by
        intro s₁ s₂ h
        cases s₁ <;> cases s₂
        · exact e₁.invHom.hom_top.mono h
        · exact False.elim h
        · exact False.elim h
        · exact e₂.invHom.hom_top.mono h
    }
    hom_abs := {
      fn := fun s =>
        match s with
        | .inl b₁ => .inl (e₁.invHom.hom_abs.fn b₁)
        | .inr b₂ => .inr (e₂.invHom.hom_abs.fn b₂)
      map_charge := fun c s =>
        match s with
        | .inl b₁ => congrArg Sum.inl (e₁.invHom.hom_abs.map_charge c b₁)
        | .inr b₂ => congrArg Sum.inr (e₂.invHom.hom_abs.map_charge c b₂)
      mono := by
        intro s₁ s₂ h
        cases s₁ <;> cases s₂
        · exact e₁.invHom.hom_abs.mono h
        · exact False.elim h
        · exact False.elim h
        · exact e₂.invHom.hom_abs.mono h
    }
    comm := fun s =>
      match s with
      | .inl b₁ => congrArg Sum.inl (e₁.invHom.comm b₁)
      | .inr b₂ => congrArg Sum.inr (e₂.invHom.comm b₂)
  }
  left_inv := by
    ext s
    · cases s with
      | inl a₁ =>
        exact congrArg Sum.inl
          (congrArg (fun h : CompHom A₁ A₁ => h.hom_top.fn a₁) e₁.left_inv)
      | inr a₂ =>
        exact congrArg Sum.inr
          (congrArg (fun h : CompHom A₂ A₂ => h.hom_top.fn a₂) e₂.left_inv)
    · cases s with
      | inl a₁ =>
        exact congrArg Sum.inl
          (congrArg (fun h : CompHom A₁ A₁ => h.hom_abs.fn a₁) e₁.left_inv)
      | inr a₂ =>
        exact congrArg Sum.inr
          (congrArg (fun h : CompHom A₂ A₂ => h.hom_abs.fn a₂) e₂.left_inv)
  right_inv := by
    ext s
    · cases s with
      | inl b₁ =>
        exact congrArg Sum.inl
          (congrArg (fun h : CompHom B₁ B₁ => h.hom_top.fn b₁) e₁.right_inv)
      | inr b₂ =>
        exact congrArg Sum.inr
          (congrArg (fun h : CompHom B₂ B₂ => h.hom_top.fn b₂) e₂.right_inv)
    · cases s with
      | inl b₁ =>
        exact congrArg Sum.inl
          (congrArg (fun h : CompHom B₁ B₁ => h.hom_abs.fn b₁) e₁.right_inv)
      | inr b₂ =>
        exact congrArg Sum.inr
          (congrArg (fun h : CompHom B₂ B₂ => h.hom_abs.fn b₂) e₂.right_inv)

private def sumPotentialEquiv (A B : AARAType) :
    CompEquiv
      (SumComp (PotentialType (aaraValues A) (aaraPotential A))
        (PotentialType (aaraValues B) (aaraPotential B)))
      (PotentialType (aaraValues (.sum A B)) (aaraPotential (.sum A B))) where
  toHom := {
    hom_top := {
      fn := fun s =>
        match s with
        | .inl (c, x) => (c, .inl x)
        | .inr (c, y) => (c, .inr y)
      map_charge := fun c s =>
        match s with
        | .inl (_, _) => rfl
        | .inr (_, _) => rfl
      mono := by
        intro s₁ s₂ h
        cases s₁ with
        | inl p₁ =>
          cases s₂ with
          | inl p₂ => exact ⟨h.1, congrArg Sum.inl h.2⟩
          | inr _ => exact False.elim h
        | inr p₁ =>
          cases s₂ with
          | inl _ => exact False.elim h
          | inr p₂ => exact ⟨h.1, congrArg Sum.inr h.2⟩
    }
    hom_abs := {
      fn := fun s =>
        match s with
        | .inl (c, x) => (c, .inl x)
        | .inr (c, y) => (c, .inr y)
      map_charge := fun c s =>
        match s with
        | .inl (_, _) => rfl
        | .inr (_, _) => rfl
      mono := by
        intro s₁ s₂ h
        cases s₁ with
        | inl p₁ =>
          cases s₂ with
          | inl p₂ => exact ⟨h.1, congrArg Sum.inl h.2⟩
          | inr _ => exact False.elim h
        | inr p₁ =>
          cases s₂ with
          | inl _ => exact False.elim h
          | inr p₂ => exact ⟨h.1, congrArg Sum.inr h.2⟩
    }
    comm := fun s =>
      match s with
      | .inl (_, _) => rfl
      | .inr (_, _) => rfl
  }
  invHom := {
    hom_top := {
      fn := fun ⟨c, s⟩ =>
        match s with
        | .inl x => .inl (c, x)
        | .inr y => .inr (c, y)
      map_charge := fun c ⟨_, s⟩ =>
        match s with
        | .inl _ => rfl
        | .inr _ => rfl
      mono := by
        rintro ⟨c₁, s₁⟩ ⟨c₂, s₂⟩ ⟨h, e⟩
        cases s₁ with
        | inl x₁ =>
          cases s₂ with
          | inl x₂ =>
            injection e with hx
            exact ⟨h, hx⟩
          | inr _ => contradiction
        | inr y₁ =>
          cases s₂ with
          | inl _ => contradiction
          | inr y₂ =>
            injection e with hy
            exact ⟨h, hy⟩
    }
    hom_abs := {
      fn := fun ⟨c, s⟩ =>
        match s with
        | .inl x => .inl (c, x)
        | .inr y => .inr (c, y)
      map_charge := fun c ⟨_, s⟩ =>
        match s with
        | .inl _ => rfl
        | .inr _ => rfl
      mono := by
        rintro ⟨c₁, s₁⟩ ⟨c₂, s₂⟩ ⟨h, e⟩
        cases s₁ with
        | inl x₁ =>
          cases s₂ with
          | inl x₂ =>
            injection e with hx
            exact ⟨h, hx⟩
          | inr _ => contradiction
        | inr y₁ =>
          cases s₂ with
          | inl _ => contradiction
          | inr y₂ =>
            injection e with hy
            exact ⟨h, hy⟩
    }
    comm := fun ⟨_, s⟩ =>
      match s with
      | .inl _ => rfl
      | .inr _ => rfl
  }
  left_inv := by
    ext s <;> {
      cases s with
      | inl p => rcases p with ⟨c, x⟩; rfl
      | inr p => rcases p with ⟨c, y⟩; rfl
    }
  right_inv := by
    ext p <;> {
      rcases p with ⟨c, s⟩
      cases s <;> rfl
    }

private def clist2PotentialEquiv (p₁ p₂ : Nat) (A : AARAType) :
    CompEquiv
      (PotentialType (CList2Ind (aaraValues A) p₁ p₂)
        (clist2IndTotalPotential (aaraPotential A)))
      (PotentialType (List (aaraValues A))
        (aaraPotential (.clist2 p₁ p₂ A))) where
  toHom := {
    hom_top := {
      fn := fun ⟨c, t⟩ => (c, t.toList)
      map_charge := fun _ ⟨_, _⟩ => rfl
      mono := fun ⟨h, e⟩ => ⟨h, congrArg CList2Ind.toList e⟩
    }
    hom_abs := {
      fn := fun ⟨c, t⟩ => (c, t.toList)
      map_charge := fun _ ⟨_, _⟩ => rfl
      mono := fun ⟨h, e⟩ => ⟨h, congrArg CList2Ind.toList e⟩
    }
    comm := fun ⟨c, t⟩ => by
      apply Prod.ext
      · change c + (t.toList.length * p₁ + binom2 t.toList.length * p₂ +
            listPotentialSum (aaraPotential A) t.toList) =
          c + (t.credits + clist2ElemPotentialSum (aaraPotential A) t)
        rw [clist2Ind_credits_eq t, clist2ElemPotentialSum_eq (aaraPotential A) t]
      · rfl
  }
  invHom := {
    hom_top := {
      fn := fun ⟨c, l⟩ => (c, CList2Ind.ofList p₁ p₂ l)
      map_charge := fun _ ⟨_, _⟩ => rfl
      mono := fun ⟨h, e⟩ => ⟨h, congrArg (CList2Ind.ofList p₁ p₂) e⟩
    }
    hom_abs := {
      fn := fun ⟨c, l⟩ => (c, CList2Ind.ofList p₁ p₂ l)
      map_charge := fun _ ⟨_, _⟩ => rfl
      mono := fun ⟨h, e⟩ => ⟨h, congrArg (CList2Ind.ofList p₁ p₂) e⟩
    }
    comm := fun ⟨c, l⟩ => by
      apply Prod.ext
      · change c + ((CList2Ind.ofList p₁ p₂ l).credits +
            clist2ElemPotentialSum (aaraPotential A) (CList2Ind.ofList p₁ p₂ l)) =
          c + (l.length * p₁ + binom2 l.length * p₂ +
            listPotentialSum (aaraPotential A) l)
        rw [clist2Ind_credits_eq (CList2Ind.ofList p₁ p₂ l),
          clist2ElemPotentialSum_eq (aaraPotential A) (CList2Ind.ofList p₁ p₂ l),
          clist2Ind_toList_ofList l p₁ p₂]
      · rfl
  }
  left_inv := by
    ext ⟨c, t⟩ <;> exact Prod.ext rfl (clist2Ind_ofList_toList t)
  right_inv := by
    ext ⟨c, l⟩ <;> exact Prod.ext rfl (clist2Ind_toList_ofList l p₁ p₂)

/-- Constructive equivalence $\mathsf{interpAARAType}\,A \simeq
\mathsf{Potential}(\Phi_A : \llbracket A \rrbracket \to \mathbb{N})$ by structural recursion on $A$
(Theorem 5.7). -/
private def aaraTypeCompEquiv : (A : AARAType) →
    CompEquiv (interpAARAType A) (PotentialType (aaraValues A) (aaraPotential A))
  | .free X => freeCompPotentialEquiv X
  | .top => freeCompPotentialEquiv PUnit
  | .tensor _ _ => CompEquiv.refl _
  | .sum A B =>
      CompEquiv.trans
        (sumCompCongr (aaraTypeCompEquiv A) (aaraTypeCompEquiv B))
        (sumPotentialEquiv A B)
  | .credit p A =>
      CompEquiv.trans
        (creditCompCongr p (aaraTypeCompEquiv A))
        (creditPotentialEquiv p (aaraValues A) (aaraPotential A))
  | .clist1 _ _ => CompEquiv.refl _
  | .clist2 p₁ p₂ A => clist2PotentialEquiv p₁ p₂ A

/-- Constructive proof of Milestone 5 (Lemma 5.1, Examples 5.2 & 5.3, Theorem 5.7). -/
theorem solution :
    (∀ {Delta B : CompType} {X : Type} {p q q₁ q₂ : Nat} (hq : q₂ + q₁ ≤ q)
       (e_rec : GiralfSemJudgment Delta B (q₂ + q₁))
       (e_sub : GiralfSemJudgment Delta (CList1Comp p X) q₁),
      ∃ paraState : GiralfSemJudgment Delta (ProdComp (DebitComp q₂ B) (CList1Comp p X)) q₁,
        (giralfPay hq (giralfProj1 paraState)).hom_top = e_rec.hom_top ∧
        (giralfProj2 paraState).hom_top = e_sub.hom_top) ∧
    (∀ (p x : Nat),
      (∀ l : List Nat,
        (insertCostTop x l).2 = insertPure x l ∧
        (insertCostTop x l).2.length = l.length + 1 ∧
        (insertCostTop x l).1 + (insertCostTop x l).2.length * p ≤ l.length * (1 + p) + p) ∧
      ∃ ins : GiralfSemJudgment (CList1Comp (1 + p) Nat) (CList1Comp p Nat) p,
        ins.hom_top = insertTopHom x ∧ ins.hom_abs = insertAbsHom x) ∧
    (∃ srt : GiralfSemJudgment (CList2Comp 0 1 Nat) (CList1Comp 0 Nat) 0,
      srt.hom_top = isortTopHom ∧ srt.hom_abs = isortAbsHom) ∧
    (∀ {α : Type} {p₁ p₂ : Nat} (t : CList2Ind α p₁ p₂),
      t.credits = t.toList.length * p₁ + binom2 t.toList.length * p₂) ∧
    (∀ A : AARAType,
      Nonempty (CompEquiv (interpAARAType A)
        (PotentialType (aaraValues A) (aaraPotential A)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Delta B X p q q₁ q₂ hq e_rec e_sub
    refine ⟨giralfPair (giralfGet (Nat.le_refl (q₂ + q₁)) e_rec) e_sub, rfl, rfl⟩
  · intro p x
    exact ⟨insertCostTop_spec p x, insertGiralfJudgment p x, rfl, rfl⟩
  · exact ⟨isortGiralfJudgment, rfl, rfl⟩
  · intro α p₁ p₂ t
    exact clist2Ind_credits_eq t
  · intro A
    exact ⟨aaraTypeCompEquiv A⟩
