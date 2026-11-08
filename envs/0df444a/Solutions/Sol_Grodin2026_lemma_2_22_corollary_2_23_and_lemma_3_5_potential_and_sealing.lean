-- Prove2me | solution 1 for Grodin2026.lemma_2_22_corollary_2_23_and_lemma_3_5_potential_and_sealing
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T17:23:27.037329+00:00
-- url     : https://prove2.me/submissions/d87265b1-4f1f-4fc1-af52-15ae54819318

import Definitions.Def_Grodin2026_Physicist

open Grodin2026

/-- Free cost algebra homomorphism induced by a value map $f : X \to Y$ and a cost function
$c : X \to \mathbb{N}$ sending $\mathsf{ret}\,x \mapsto \mathsf{charge}\langle c(x) \rangle(\mathsf{ret}(f(x)))$. -/
private def mkFreeCostHom {X Y : Type} (f : X → Y) (cost : X → Nat) :
    CostHom (FreeCostAlg X) (FreeCostAlg Y) where
  fn := fun p => (p.1 + cost p.2, f p.2)
  map_charge := fun c ⟨c₀, x⟩ => Prod.ext (Nat.add_assoc c c₀ (cost x)) rfl
  mono := fun ⟨h, e⟩ => ⟨by rw [e]; exact Nat.add_le_add_right h _, congrArg f e⟩

/-- Cost-aware batched queue enqueue homomorphism $A \multimap A$ (Example 2.20). -/
private def batchedQueueEnqueueHom (α : Type) (n : α) :
    CompHom (BatchedQueueComp α) (BatchedQueueComp α) where
  hom_top := enqueueCompTop n
  hom_abs := enqueueCompAbs n
  comm := fun ⟨c₀, l₁, l₂⟩ => by
    apply Prod.ext
    · change c₀ + (l₂.length + 1) = c₀ + l₂.length + 1
      omega
    · change queueChi (enqueueValTop n (l₁, l₂)) = enqueueValAbs n (queueChi (l₁, l₂))
      simp [queueChi, enqueueValTop, enqueueValAbs, List.append_assoc]

/-- Canonical bijection between Kleisli homomorphisms $A \multimap \mathsf{S}B$ and lax
homomorphisms $A \mathrel{\multimap\!\!\!\!+} B$ (§3.2). -/
private def kleisliSealEquiv (A B : CompType) :
    CompHom A (SealComp B) ≃ LaxCompHom A B where
  toFun := fun f => {
    hom_top := {
      fn := fun a => (f.hom_top.fn a).1.1
      map_charge := fun c a =>
        congrArg (fun p => p.1.1) (f.hom_top.map_charge c a)
      mono := fun h => (f.hom_top.mono h).1
    }
    hom_abs := f.hom_abs
    lax_comm := fun a => by
      have h_sub : B.abs.le (B.alpha.fn (f.hom_top.fn a).1.1) (f.hom_top.fn a).1.2 :=
        (f.hom_top.fn a).2
      have h_comm : (f.hom_top.fn a).1.2 = f.hom_abs.fn (A.alpha.fn a) :=
        f.comm a
      rw [h_comm] at h_sub
      exact h_sub
  }
  invFun := fun g => {
    hom_top := {
      fn := fun a => ⟨(g.hom_top.fn a, g.hom_abs.fn (A.alpha.fn a)), g.lax_comm a⟩
      map_charge := fun c a => by
        apply Subtype.ext
        apply Prod.ext
        · exact g.hom_top.map_charge c a
        · calc g.hom_abs.fn (A.alpha.fn (A.top.charge c a))
            _ = g.hom_abs.fn (A.abs.charge c (A.alpha.fn a)) :=
              congrArg g.hom_abs.fn (A.alpha.map_charge c a)
            _ = B.abs.charge c (g.hom_abs.fn (A.alpha.fn a)) :=
              g.hom_abs.map_charge c (A.alpha.fn a)
      mono := fun h => ⟨g.hom_top.mono h, g.hom_abs.mono (A.alpha.mono h)⟩
    }
    hom_abs := g.hom_abs
    comm := fun _ => rfl
  }
  left_inv := fun f => by
    ext a
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact (f.comm a).symm
    · rfl
  right_inv := fun g => by
    ext a <;> rfl

/-- Constructive proof of Milestone 3 (Example 2.20, Lemma 2.22, Corollary 2.23, Example 3.3, Lemma 3.5). -/
theorem solution :
    (∀ (α : Type),
      (∀ (q : BatchedQueueRep α) (n : α), 0 + queuePhi (enqueueValTop n q) = queuePhi q + 1) ∧
      ∃ enq : α → CompHom (BatchedQueueComp α) (BatchedQueueComp α),
        (∀ n : α, (enq n).hom_top = enqueueCompTop n) ∧
        ({ comp := BatchedQueueComp α
           empty_top := retFree ([], [])
           empty_abs := retFree []
           empty_comm := rfl
           enqueue := enq } : PhasedPreQueue α).absView = AmortizedQueueModel α) ∧
    (∀ {X Y : Type} (Phi_X : X → Nat) (Phi_Y : Y → Nat) (f : X → Y) (c_top c_abs : X → Nat),
      (∃ g : CompHom (PotentialType X Phi_X) (PotentialType Y Phi_Y),
        (∀ x : X, g.hom_top.fn (retFree x) = (c_top x, f x)) ∧
        (∀ x : X, g.hom_abs.fn (retFree x) = (c_abs x, f x))) ↔
      (∀ x : X, c_top x + Phi_Y (f x) = Phi_X x + c_abs x)) ∧
    (∀ (A B_top B_abs : CostAlg) (beta : CostHom B_top B_abs),
      (∀ f_top : CostHom A B_top,
        ∃ f : CompHom (ConstComp A) (AbstractionComp B_top B_abs beta),
          f.hom_top = f_top ∧ f.hom_abs = beta.comp f_top) ∧
      (∀ g_abs : CostHom B_abs A,
        ∃ g : CompHom (AbstractionComp B_top B_abs beta) (ConstComp A),
          g.hom_top = g_abs.comp beta ∧ g.hom_abs = g_abs)) ∧
    (∀ A B : CompType,
      Nonempty (CompHom A (SealComp B) ≃ LaxCompHom A B) ∧
      OpenComp (SealComp A) = OpenComp A) ∧
    (∀ {X Y : Type} (Phi_X : X → Nat) (Phi_Y : Y → Nat) (f : X → Y) (c_top c_abs : X → Nat),
      (∃ g : LaxCompHom (PotentialType X Phi_X) (PotentialType Y Phi_Y),
        (∀ x : X, g.hom_top.fn (retFree x) = (c_top x, f x)) ∧
        (∀ x : X, g.hom_abs.fn (retFree x) = (c_abs x, f x))) ↔
      (∀ x : X, c_top x + Phi_Y (f x) ≤ Phi_X x + c_abs x)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α
    refine ⟨?_, batchedQueueEnqueueHom α, fun _ => rfl, rfl⟩
    intro ⟨l₁, l₂⟩ n
    simp [queuePhi, enqueueValTop]
  · intro X Y Phi_X Phi_Y f c_top c_abs
    constructor
    · rintro ⟨g, h_top, h_abs⟩ x
      have h_comm := g.comm (retFree x)
      have h_lhs : (PotentialType Y Phi_Y).alpha.fn (g.hom_top.fn (retFree x)) =
          (c_top x + Phi_Y (f x), f x) := by
        rw [h_top x]
        rfl
      have h_rhs : g.hom_abs.fn ((PotentialType X Phi_X).alpha.fn (retFree x)) =
          (Phi_X x + c_abs x, f x) := by
        have h_phiX : (PotentialType X Phi_X).alpha.fn (retFree x) =
            (PotentialType X Phi_X).abs.charge (Phi_X x) (retFree x) :=
          Prod.ext (Nat.add_comm 0 (Phi_X x)) rfl
        rw [h_phiX, g.hom_abs.map_charge (Phi_X x) (retFree x), h_abs x]
        rfl
      rw [h_lhs, h_rhs] at h_comm
      exact congrArg Prod.fst h_comm
    · intro h_cons
      refine ⟨{
        hom_top := mkFreeCostHom f c_top
        hom_abs := mkFreeCostHom f c_abs
        comm := fun ⟨c₀, x⟩ => by
          apply Prod.ext
          · change c₀ + c_top x + Phi_Y (f x) = c₀ + Phi_X x + c_abs x
            have hx := h_cons x
            omega
          · rfl
      },
      fun x => Prod.ext (Nat.zero_add (c_top x)) rfl,
      fun x => Prod.ext (Nat.zero_add (c_abs x)) rfl⟩
  · intro A B_top B_abs beta
    refine ⟨?_, ?_⟩
    · intro f_top
      exact ⟨⟨f_top, beta.comp f_top, fun _ => rfl⟩, rfl, rfl⟩
    · intro g_abs
      exact ⟨⟨g_abs.comp beta, g_abs, fun _ => rfl⟩, rfl, rfl⟩
  · intro A B
    exact ⟨⟨kleisliSealEquiv A B⟩, rfl⟩
  · intro X Y Phi_X Phi_Y f c_top c_abs
    constructor
    · rintro ⟨g, h_top, h_abs⟩ x
      have h_lax := g.lax_comm (retFree x)
      have h_lhs : (PotentialType Y Phi_Y).alpha.fn (g.hom_top.fn (retFree x)) =
          (c_top x + Phi_Y (f x), f x) := by
        rw [h_top x]
        rfl
      have h_rhs : g.hom_abs.fn ((PotentialType X Phi_X).alpha.fn (retFree x)) =
          (Phi_X x + c_abs x, f x) := by
        have h_phiX : (PotentialType X Phi_X).alpha.fn (retFree x) =
            (PotentialType X Phi_X).abs.charge (Phi_X x) (retFree x) :=
          Prod.ext (Nat.add_comm 0 (Phi_X x)) rfl
        rw [h_phiX, g.hom_abs.map_charge (Phi_X x) (retFree x), h_abs x]
        rfl
      rw [h_lhs, h_rhs] at h_lax
      exact h_lax.1
    · intro h_lax_cons
      refine ⟨{
        hom_top := mkFreeCostHom f c_top
        hom_abs := mkFreeCostHom f c_abs
        lax_comm := fun ⟨c₀, x⟩ => by
          refine ⟨?_, rfl⟩
          change c₀ + c_top x + Phi_Y (f x) ≤ c₀ + Phi_X x + c_abs x
          have hx := h_lax_cons x
          omega
      },
      fun x => Prod.ext (Nat.zero_add (c_top x)) rfl,
      fun x => Prod.ext (Nat.zero_add (c_abs x)) rfl⟩
