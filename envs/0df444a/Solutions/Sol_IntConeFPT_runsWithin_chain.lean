-- Prove2me | solution 1 for IntConeFPT.runsWithin_chain
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:38:22.00595+00:00
-- url     : https://prove2.me/submissions/2b0f5061-8f91-4167-87d5-7e0dac78f2f3

import Definitions.Def_IntConeFPT_Machine

/- The sequential TM2 compiler below is adapted from Prove2Me submission
70c7eb16-aa64-45fc-9619-d6fd621972a7 for Turing.TM2ComputableInPolyTime.comp_of_polytime,
under Apache-2.0. We keep the actual-run bound rather than a global polynomial clock. -/
set_option autoImplicit true

open Turing

/-!
# Core of a general composition lemma for `Turing.TM2ComputableInPolyTime`

Given two machines `tm₁`, `tm₂` we build the stack/key/state packaging in which `tm₁` and `tm₂` can
run inside one machine:

* `Key := tm₁.K ⊕ (tm₂.K ⊕ Unit)` — the two machines' stacks plus one temporary stack (used to
  reverse the copied word, because stacks are LIFO);
* `Gam` — the corresponding (dependent) stack alphabets;
* `Lab := tm₁.Λ ⊕ (Unit ⊕ tm₂.Λ)` — the two label sets plus a copy-phase label;
* `Sta := tm₁.σ × (tm₂.σ × Option (tm₂.Γ tm₂.k₀))` — both internal states plus a one-symbol buffer.

`tr₁`/`tr₂` push each machine's statements through this packaging, and `stepAux_tr₁`/`stepAux_tr₂`
are the exact one-step commutation lemmas: one composite step simulates one step of the machine.
-/

namespace Turing

/-- Once a deterministic step function has halted, iterating it stays at `none`. -/
theorem iterate_none {α : Type*} (f : α → Option α) : ∀ m : ℕ,
    (flip bind f)^[m] (none : Option α) = none
  | 0 => rfl
  | m + 1 => by
      rw [Function.iterate_succ_apply]
      exact iterate_none f m

namespace CompCore

variable (tm₁ : FinTM2) (tm₂ : FinTM2)

/-- Stack index type of the composite. -/
abbrev Key : Type := tm₁.K ⊕ (tm₂.K ⊕ Unit)

/-- Stack alphabets of the composite. -/
abbrev Gam : Key tm₁ tm₂ → Type
  | .inl a => tm₁.Γ a
  | .inr (.inl b) => tm₂.Γ b
  | .inr (.inr _) => tm₂.Γ tm₂.k₀

/-- Label type of the composite: machine 1's labels, machine 2's labels, and one copy-phase label
(stored as `Unit`). -/
abbrev Lab : Type := tm₁.Λ ⊕ (Fin 2 ⊕ tm₂.Λ)

/-- Internal state of the composite: both machines' states plus a one-symbol buffer. -/
abbrev Sta : Type := tm₁.σ × (tm₂.σ × Option (tm₂.Γ tm₂.k₀))

/-- The stack contents of the composite as a dependent function. -/
def pack (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) : (k : Key tm₁ tm₂) → List (Gam tm₁ tm₂ k)
  | .inl a => S₁ a
  | .inr (.inl b) => S₂ b
  | .inr (.inr _) => T

theorem pack_update_left (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (k : tm₁.K) (x : List (tm₁.Γ k)) :
    Function.update (pack tm₁ tm₂ S₁ S₂ T) (Sum.inl k) x
      = pack tm₁ tm₂ (Function.update S₁ k x) S₂ T := by
  funext j
  rcases j with a | (b | u)
  · by_cases h : a = k
    · subst h; simp [pack]
    · simp only [pack, Function.update_of_ne (by simp [h] : (Sum.inl a : Key tm₁ tm₂) ≠ Sum.inl k),
        Function.update_of_ne h]
  · simp only [pack, Function.update_of_ne (by simp : (Sum.inr (Sum.inl b) : Key tm₁ tm₂) ≠ Sum.inl k)]
  · simp only [pack, Function.update_of_ne (by simp : (Sum.inr (Sum.inr u) : Key tm₁ tm₂) ≠ Sum.inl k)]

theorem pack_update_right (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (k : tm₂.K) (x : List (tm₂.Γ k)) :
    Function.update (pack tm₁ tm₂ S₁ S₂ T) (Sum.inr (Sum.inl k)) x
      = pack tm₁ tm₂ S₁ (Function.update S₂ k x) T := by
  funext j
  rcases j with a | (b | u)
  · simp only [pack, Function.update_of_ne (by simp : (Sum.inl a : Key tm₁ tm₂) ≠ Sum.inr (Sum.inl k))]
  · by_cases h : b = k
    · subst h; simp [pack]
    · have hne : ¬ ((Sum.inr (Sum.inl b) : Key tm₁ tm₂) = Sum.inr (Sum.inl k)) :=
        fun hh => h (by simpa using hh)
      rw [Function.update_of_ne (a := Sum.inr (Sum.inl b)) (a' := Sum.inr (Sum.inl k))
            (v := x) (f := pack tm₁ tm₂ S₁ S₂ T) hne]
      simp only [pack, Function.update_of_ne (a := b) (a' := k) (v := x) (f := S₂) h]
  · simp only [pack,
      Function.update_of_ne (by simp : (Sum.inr (Sum.inr u) : Key tm₁ tm₂) ≠ Sum.inr (Sum.inl k))]

theorem pack_update_tmp (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (x : List (tm₂.Γ tm₂.k₀)) :
    Function.update (pack tm₁ tm₂ S₁ S₂ T) (Sum.inr (Sum.inr ())) x
      = pack tm₁ tm₂ S₁ S₂ x := by
  funext j
  rcases j with a | (b | u)
  · simp only [pack,
      Function.update_of_ne (by simp : (Sum.inl a : Key tm₁ tm₂) ≠ Sum.inr (Sum.inr ()))]
  · simp only [pack,
      Function.update_of_ne (by simp : (Sum.inr (Sum.inl b) : Key tm₁ tm₂) ≠ Sum.inr (Sum.inr ()))]
  · simp only [pack]
    congr 1
    cases u
    rfl

/-- Label translation for machine 1: its own labels, and its halting label is turned into a jump to
the copy phase. -/
def lab₁ : Option tm₁.Λ → Option (Lab tm₁ tm₂)
  | none => some (Sum.inr (Sum.inl 0))
  | some l => some (Sum.inl l)

/-- Label translation for machine 2: its halting label stays a halting label. -/
def lab₂ : Option tm₂.Λ → Option (Lab tm₁ tm₂)
  | none => none
  | some l => some (Sum.inr (Sum.inr l))

/-- Reindex machine 1's statements into the composite. -/
def tr₁ : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .push k g q => .push (Sum.inl k) (fun s => g s.1) (tr₁ q)
  | .peek k g q => .peek (Sum.inl k) (fun s o => (g s.1 o, s.2)) (tr₁ q)
  | .pop k g q => .pop (Sum.inl k) (fun s o => (g s.1 o, s.2)) (tr₁ q)
  | .load g q => .load (fun s => (g s.1, s.2)) (tr₁ q)
  | .branch g q r => .branch (fun s => g s.1) (tr₁ q) (tr₁ r)
  | .goto g => .goto (fun s => Sum.inl (g s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inl 0))

/-- Reindex machine 2's statements into the composite. -/
def tr₂ : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .push k g q => .push (Sum.inr (Sum.inl k)) (fun s => g s.2.1) (tr₂ q)
  | .peek k g q => .peek (Sum.inr (Sum.inl k)) (fun s o => (s.1, (g s.2.1 o, s.2.2))) (tr₂ q)
  | .pop k g q => .pop (Sum.inr (Sum.inl k)) (fun s o => (s.1, (g s.2.1 o, s.2.2))) (tr₂ q)
  | .load g q => .load (fun s => (s.1, (g s.2.1, s.2.2))) (tr₂ q)
  | .branch g q r => .branch (fun s => g s.2.1) (tr₂ q) (tr₂ r)
  | .goto g => .goto (fun s => Sum.inr (Sum.inr (g s.2.1)))
  | .halt => .halt

theorem stepAux_tr₁ (q : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ) (v₁ : tm₁.σ) (v₂ : tm₂.σ)
    (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.stepAux (tr₁ tm₁ tm₂ q) (v₁, v₂, b) (pack tm₁ tm₂ S₁ S₂ T)
      = ⟨lab₁ tm₁ tm₂ (TM2.stepAux q v₁ S₁).l,
          ((TM2.stepAux q v₁ S₁).var, v₂, b),
          pack tm₁ tm₂ (TM2.stepAux q v₁ S₁).stk S₂ T⟩ := by
  induction q generalizing v₁ S₁ with
  | push k g q ih =>
      simp only [tr₁, TM2.stepAux, pack_update_left tm₁ tm₂]
      exact ih _ _
  | peek k g q ih =>
      simp only [tr₁, TM2.stepAux]
      exact ih _ _
  | pop k g q ih =>
      simp only [tr₁, TM2.stepAux, pack_update_left tm₁ tm₂]
      exact ih _ _
  | load g q ih =>
      simp only [tr₁, TM2.stepAux]
      exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v₁
      · simp only [tr₁, TM2.stepAux, hg, Bool.cond_false]
        exact ihr _ _
      · simp only [tr₁, TM2.stepAux, hg, Bool.cond_true]
        exact ihq _ _
  | goto g => simp only [tr₁, TM2.stepAux, lab₁]
  | halt => simp only [tr₁, TM2.stepAux, lab₁]

theorem stepAux_tr₂ (q : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ) (v₁ : tm₁.σ) (v₂ : tm₂.σ)
    (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.stepAux (tr₂ tm₁ tm₂ q) (v₁, v₂, b) (pack tm₁ tm₂ S₁ S₂ T)
      = ⟨lab₂ tm₁ tm₂ (TM2.stepAux q v₂ S₂).l,
          (v₁, ((TM2.stepAux q v₂ S₂).var, b)),
          pack tm₁ tm₂ S₁ (TM2.stepAux q v₂ S₂).stk T⟩ := by
  induction q generalizing v₂ S₂ with
  | push k g q ih =>
      simp only [tr₂, TM2.stepAux, pack_update_right tm₁ tm₂]
      exact ih _ _
  | peek k g q ih =>
      simp only [tr₂, TM2.stepAux]
      exact ih _ _
  | pop k g q ih =>
      simp only [tr₂, TM2.stepAux, pack_update_right tm₁ tm₂]
      exact ih _ _
  | load g q ih =>
      simp only [tr₂, TM2.stepAux]
      exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v₂
      · simp only [tr₂, TM2.stepAux, hg, Bool.cond_false]
        exact ihr _ _
      · simp only [tr₂, TM2.stepAux, hg, Bool.cond_true]
        exact ihq _ _
  | goto g => simp only [tr₂, TM2.stepAux, lab₂]
  | halt => simp only [tr₂, TM2.stepAux, lab₂]
end CompCore

end Turing


namespace Turing

namespace CompCore

variable (tm₁ : FinTM2) (tm₂ : FinTM2)

/-- Program of the composite: machine 1's code, the copy phase, then machine 2's code. -/
def compCode (copy : TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) :
    Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .inl l => tr₁ tm₁ tm₂ (tm₁.m l)
  | .inr (.inl _) => copy
  | .inr (.inr l) => tr₂ tm₁ tm₂ (tm₂.m l)

/-- The composite step function. -/
def compStep (copy : TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) :
    TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) →
      Option (TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) :=
  TM2.step (compCode tm₁ tm₂ copy)

/-- Embed machine 1's configuration into the composite. -/
def cfg₁ (c : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ) (v₂ : tm₂.σ) (b : Option (tm₂.Γ tm₂.k₀))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  ⟨lab₁ tm₁ tm₂ c.l, (c.var, v₂, b), pack tm₁ tm₂ c.stk S₂ T⟩

theorem step_cfg₁ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₁.Λ, M (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l))
    (v₂ : tm₂.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) {c c' : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ}
    (h : tm₁.step c = some c') :
    TM2.step M (cfg₁ tm₁ tm₂ c v₂ b S₂ T) = some (cfg₁ tm₁ tm₂ c' v₂ b S₂ T) := by
  obtain ⟨l, v₁, S₁⟩ := c
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have hh : c' = TM2.stepAux (tm₁.m l) v₁ S₁ := (Option.some.inj h).symm
      subst hh
      simp only [cfg₁, lab₁, hM, TM2.step.eq_2, FinTM2.step, stepAux_tr₁]

/-- Run lifting for machine 1: any `m`-step run of `tm₁` is an `m`-step run of the composite. -/
theorem iterate_cfg₁ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₁.Λ, M (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l))
    (v₂ : tm₂.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) :
    ∀ (m : ℕ) (c c' : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ),
      (flip bind tm₁.step)^[m] (some c) = some c' →
      (flip bind (TM2.step M))^[m] (some (cfg₁ tm₁ tm₂ c v₂ b S₂ T))
        = some (cfg₁ tm₁ tm₂ c' v₂ b S₂ T)
  | 0, c, c', h => by
      simp only [Function.iterate_zero, id_eq] at h
      have h' : c = c' := Option.some.inj h
      subst h'; rfl
  | m + 1, c, c', h => by
      rw [Function.iterate_succ_apply] at h ⊢
      rw [show (flip bind tm₁.step) (some c) = tm₁.step c from rfl] at h
      cases hstep : tm₁.step c with
      | none => rw [hstep] at h; exact absurd h (by rw [iterate_none]; simp)
      | some d =>
          rw [hstep] at h
          rw [show (flip bind (TM2.step M)) (some (cfg₁ tm₁ tm₂ c v₂ b S₂ T))
                = TM2.step M (cfg₁ tm₁ tm₂ c v₂ b S₂ T) from rfl,
              step_cfg₁ tm₁ tm₂ M hM v₂ b S₂ T hstep]
          exact iterate_cfg₁ M hM v₂ b S₂ T m d c' h

/-- Embed machine 2's configuration into the composite. -/
def cfg₂ (c : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ) (v₁ : tm₁.σ) (b : Option (tm₂.Γ tm₂.k₀))
    (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  ⟨lab₂ tm₁ tm₂ c.l, (v₁, (c.var, b)), pack tm₁ tm₂ S₁ c.stk T⟩

theorem step_cfg₂ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₂.Λ, M (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l))
    (v₁ : tm₁.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) {c c' : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ}
    (h : tm₂.step c = some c') :
    TM2.step M (cfg₂ tm₁ tm₂ c v₁ b S₁ T) = some (cfg₂ tm₁ tm₂ c' v₁ b S₁ T) := by
  obtain ⟨l, v₂, S₂⟩ := c
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have hh : c' = TM2.stepAux (tm₂.m l) v₂ S₂ := (Option.some.inj h).symm
      subst hh
      simp only [cfg₂, lab₂, hM, TM2.step.eq_2, FinTM2.step, stepAux_tr₂]

/-- Run lifting for machine 2. -/
theorem iterate_cfg₂ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₂.Λ, M (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l))
    (v₁ : tm₁.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) :
    ∀ (m : ℕ) (c c' : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ),
      (flip bind tm₂.step)^[m] (some c) = some c' →
      (flip bind (TM2.step M))^[m] (some (cfg₂ tm₁ tm₂ c v₁ b S₁ T))
        = some (cfg₂ tm₁ tm₂ c' v₁ b S₁ T)
  | 0, c, c', h => by
      simp only [Function.iterate_zero, id_eq] at h
      have h' : c = c' := Option.some.inj h
      subst h'; rfl
  | m + 1, c, c', h => by
      rw [Function.iterate_succ_apply] at h ⊢
      rw [show (flip bind tm₂.step) (some c) = tm₂.step c from rfl] at h
      cases hstep : tm₂.step c with
      | none => rw [hstep] at h; exact absurd h (by rw [iterate_none]; simp)
      | some d =>
          rw [hstep] at h
          rw [show (flip bind (TM2.step M)) (some (cfg₂ tm₁ tm₂ c v₁ b S₁ T))
                = TM2.step M (cfg₂ tm₁ tm₂ c v₁ b S₁ T) from rfl,
              step_cfg₂ tm₁ tm₂ M hM v₁ b S₁ T hstep]
          exact iterate_cfg₂ M hM v₁ b S₁ T m d c' h

end CompCore

end Turing


namespace Turing

namespace CompCore

variable (tm₁ : FinTM2) (tm₂ : FinTM2)
variable {βΓ : Type} [Inhabited βΓ]

/-- Copy pass 1: move `tm₁`'s output stack onto the temporary stack, through the two alphabets'
equivalences (this pass reverses the word, since stacks are LIFO). -/
def copyStmt₁ (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  .pop (Sum.inl tm₁.k₁) (fun v o => (v.1, (v.2.1, o.map (fun x => ia₂.invFun (oa₁ x)))))
    (.branch (fun v => v.2.2.isSome)
      (.push (Sum.inr (Sum.inr ()))
        (fun v => (v.2.2).getD (ia₂.invFun default))
        (.goto (fun _ => Sum.inr (Sum.inl 0))))
      (.goto (fun _ => Sum.inr (Sum.inl 1))))

/-- Copy pass 2: move the temporary stack onto `tm₂`'s input stack, restoring the order. -/
def copyStmt₂ (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  .pop (Sum.inr (Sum.inr ())) (fun v o => (v.1, (v.2.1, o)))
    (.branch (fun v => v.2.2.isSome)
      (.push (Sum.inr (Sum.inl tm₂.k₀))
        (fun v => (v.2.2).getD (ia₂.invFun default))
        (.goto (fun _ => Sum.inr (Sum.inl 1))))
      (.goto (fun _ => Sum.inr (Sum.inr tm₂.main))))

/-- The composite program: `tm₁`'s code, the two copy passes, `tm₂`'s code. -/
def compProg (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .inl l => tr₁ tm₁ tm₂ (tm₁.m l)
  | .inr (.inl 0) => copyStmt₁ tm₁ tm₂ oa₁ ia₂
  | .inr (.inl 1) => copyStmt₂ tm₁ tm₂ ia₂
  | .inr (.inr l) => tr₂ tm₁ tm₂ (tm₂.m l)

theorem compProg_inl (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) (l : tm₁.Λ) :
    compProg tm₁ tm₂ oa₁ ia₂ (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l) := rfl

theorem compProg_inr_inr (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (l : tm₂.Λ) :
    compProg tm₁ tm₂ oa₁ ia₂ (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l) := rfl

/-- One step of copy pass 1 on a nonempty source stack. -/
theorem step_copy₁_some (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (v : Sta tm₁ tm₂) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (x : tm₁.Γ tm₁.k₁) (xs : List (tm₁.Γ tm₁.k₁)) (hS₁ : S₁ tm₁.k₁ = x :: xs) :
    TM2.step (compProg tm₁ tm₂ oa₁ ia₂) ⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩
      = some ⟨some (Sum.inr (Sum.inl 0)), (v.1, (v.2.1, some (ia₂.invFun (oa₁ x)))),
          pack tm₁ tm₂ (Function.update S₁ tm₁.k₁ xs) S₂
            (ia₂.invFun (oa₁ x) :: T)⟩ := by
  simp only [compProg, copyStmt₁, TM2.step, TM2.stepAux, hS₁, Option.map_some,
    Option.isSome_some, Option.getD_some, cond_true, List.head?_cons, List.tail_cons,
    pack, pack_update_left, pack_update_tmp, pack_update_right]

/-- One step of copy pass 1 on an empty source stack. -/
theorem step_copy₁_nil (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (v : Sta tm₁ tm₂) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (hS₁ : S₁ tm₁.k₁ = []) :
    TM2.step (compProg tm₁ tm₂ oa₁ ia₂) ⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩
      = some ⟨some (Sum.inr (Sum.inl 1)), (v.1, (v.2.1, none)),
          pack tm₁ tm₂ S₁ S₂ T⟩ := by
  have hupd : Function.update S₁ tm₁.k₁ ([] : List (tm₁.Γ tm₁.k₁)) = S₁ := by
    rw [← hS₁]; exact Function.update_eq_self _ _
  rw [← hupd]
  simp [compProg, copyStmt₁, TM2.step, TM2.stepAux, pack, pack_update_tmp, pack_update_right,
    pack_update_left]

/-- One step of copy pass 2 on a nonempty temporary stack. -/
theorem step_copy₂_some (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (v : Sta tm₁ tm₂) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (x : tm₂.Γ tm₂.k₀) (xs : List (tm₂.Γ tm₂.k₀)) (hT : T = x :: xs) :
    TM2.step (compProg tm₁ tm₂ oa₁ ia₂) ⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ T⟩
      = some ⟨some (Sum.inr (Sum.inl 1)), (v.1, (v.2.1, some x)),
          pack tm₁ tm₂ S₁ (Function.update S₂ tm₂.k₀ (x :: S₂ tm₂.k₀)) xs⟩ := by
  subst hT
  simp [compProg, copyStmt₂, TM2.step, TM2.stepAux, pack, pack_update_tmp, pack_update_right,
    pack_update_left]

/-- One step of copy pass 2 on an empty temporary stack: the composite enters `tm₂`. -/
theorem step_copy₂_nil (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (v : Sta tm₁ tm₂) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) (hT : T = []) :
    TM2.step (compProg tm₁ tm₂ oa₁ ia₂) ⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ T⟩
      = some ⟨some (Sum.inr (Sum.inr tm₂.main)), (v.1, (v.2.1, none)),
          pack tm₁ tm₂ S₁ S₂ T⟩ := by
  subst hT
  simp only [compProg, copyStmt₂, TM2.step, TM2.stepAux, List.head?_nil, Option.map_none,
    Option.isSome_none, Bool.false_eq_true, cond_false, pack]
  rw [show ([] : List (tm₂.Γ tm₂.k₀)).tail = [] from rfl, pack_update_tmp]

end CompCore

end Turing

open StateTransition
namespace QMCExit

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ : Type*} {σ : Type*}

open Turing.TM2.Stmt

/-! ### Utilities on `EvalsToInTime` -/

/-- Chaining `EvalsToInTime` steps when the intermediate configuration is given explicitly. -/
def EvalsToInTime.trans' {α : Type*} {f : α → Option α} {a b : α} {c : Option α} {m₁ m₂ : ℕ}
    (h₁ : EvalsToInTime f a (some b) m₁) (h₂ : EvalsToInTime f b c m₂) :
    EvalsToInTime f a c (m₂ + m₁) :=
  EvalsToInTime.trans f m₁ m₂ a b c h₁ h₂

/-- Weakening the step bound. -/
def EvalsToInTime.mono {α : Type*} {f : α → Option α} {a : α} {b : Option α} {m m' : ℕ}
    (h : EvalsToInTime f a b m) (hm : m ≤ m') : EvalsToInTime f a b m' :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hm⟩

/-- `flip bind` of the step function of a TM2 machine is the step function itself. -/
theorem flip_bind_step (M : Λ → Turing.TM2.Stmt Γ Λ σ) (c : Turing.TM2.Cfg Γ Λ σ) :
    (flip bind (Turing.TM2.step M)) c = Turing.TM2.step M c := by
  rcases c with ⟨l, v, S⟩
  cases l <;> rfl

def EvalsToInTime.congr_cfg {α : Type*} {f : α → Option α} {a a' : α} {b b' : Option α} {m : ℕ}
    (ha : a = a') (hb : b = b') (h : EvalsToInTime f a b m) : EvalsToInTime f a' b' m := by
  subst ha; subst hb; exact h

/-! ### Bridge to `TM2OutputsInTime` -/

/-- A configuration-level run that ends in the (exact) halting configuration gives
`TM2OutputsInTime`. -/
def tm2OutputsInTime_of_cfg {tm : Turing.FinTM2} {l : List (tm.Γ tm.k₀)}
    {out : List (tm.Γ tm.k₁)} {n : ℕ} {c : tm.Cfg}
    (h : EvalsToInTime (Turing.TM2.step tm.m) (Turing.initList tm l) (some c) n)
    (hc : c = Turing.haltList tm out) : Turing.TM2OutputsInTime tm l (some out) n := by
  subst c
  unfold Turing.TM2OutputsInTime
  exact h

/-- Conversely, `TM2OutputsInTime` is a configuration-level run into `haltList`. -/
def cfg_of_tm2OutputsInTime {tm : Turing.FinTM2} {l : List (tm.Γ tm.k₀)}
    {out : List (tm.Γ tm.k₁)} {n : ℕ} (h : Turing.TM2OutputsInTime tm l (some out) n) :
    EvalsToInTime (Turing.TM2.step tm.m) (Turing.initList tm l) (some (Turing.haltList tm out)) n := by
  unfold Turing.TM2OutputsInTime at h
  exact h

/-- The stack family of the *initial* configuration, written exactly as `initList` writes it. -/
def initStacks (tm : Turing.FinTM2) (l : List (tm.Γ tm.k₀)) : ∀ k, List (tm.Γ k) :=
  fun k => @dite (List (tm.Γ k)) (k = tm.k₀) (tm.kDecidableEq k tm.k₀)
    (fun h => by rw [h]; exact l) fun _ => []

/-- A configuration with the main label, the initial state and the initial stack family *is*
`initList`. -/
theorem mk_initList {tm : Turing.FinTM2} {l : List (tm.Γ tm.k₀)} {v : tm.σ}
    {S : ∀ k, List (tm.Γ k)} (hv : v = tm.initialState) (hS : S = initStacks tm l) :
    (⟨some tm.main, v, S⟩ : tm.Cfg) = Turing.initList tm l := by
  subst hv
  subst hS
  rfl

/-- A program step that is a bare `goto`: one step, everything unchanged. -/
def goto_step {M : Λ → Turing.TM2.Stmt Γ Λ σ} {A B : Λ} (h : M A = goto (fun _ => B))
    (v : σ) (S : ∀ j, List (Γ j)) :
    EvalsToInTime (Turing.TM2.step M) ⟨some A, v, S⟩ (some ⟨some B, v, S⟩) 1 := by
  have hstep : Turing.TM2.step M ⟨some A, v, S⟩ = some ⟨some B, v, S⟩ := by
    show some (Turing.TM2.stepAux (M A) v S) = _
    rw [h]
    rfl
  exact ⟨⟨1, by rw [Function.iterate_one, flip_bind_step M, hstep]⟩, by simp⟩

/-- The stack family of the halting configuration, written with an explicit `if` and cast. -/
def haltStacks (tm : Turing.FinTM2) (out : List (tm.Γ tm.k₁)) : ∀ k, List (tm.Γ k) :=
  fun k => @dite (List (tm.Γ k)) (k = tm.k₁) (tm.kDecidableEq k tm.k₁)
    (fun h => by rw [h]; exact out) fun _ => []

/-- A configuration with the halting label, the initial state and the halting stack family *is*
`haltList`. -/
theorem mk_haltList {tm : Turing.FinTM2} {out : List (tm.Γ tm.k₁)} {v : tm.σ}
    {S : ∀ k, List (tm.Γ k)} (hv : v = tm.initialState) (hS : S = haltStacks tm out) :
    (⟨none, v, S⟩ : tm.Cfg) = Turing.haltList tm out := by
  subst hv
  subst hS
  rfl

/-! ### The final halt step -/

/-- A single `load (fun _ => v₀) halt` step halts with the state reset to `v₀`. -/
@[simp] theorem haltStacks_k1 (tm : FinTM2) (out : List (tm.Γ tm.k₁)) :
    haltStacks tm out tm.k₁ = out := by simp [haltStacks]

def tm2OutputsInTime_mono {tm : Turing.FinTM2} {l : List (tm.Γ tm.k₀)}
    {out : Option (List (tm.Γ tm.k₁))} {m m' : ℕ} (h : Turing.TM2OutputsInTime tm l out m)
    (hm : m ≤ m') : Turing.TM2OutputsInTime tm l out m' :=
  EvalsToInTime.mono h hm

end QMCExit



namespace Turing

namespace CompCore

variable {tm₁ : FinTM2} {tm₂ : FinTM2}
variable {βΓ : Type} [Inhabited βΓ]
/-- **Copy pass 1, whole word** (`EvalsToInTime` form): moves `L` from `tm₁`'s output stack onto the
temporary stack through the two alphabets' equivalences (reversing it) in `|L| + 1` steps. -/
noncomputable def copy₁_trace (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    ∀ (L : List (tm₁.Γ tm₁.k₁)) (v : Sta tm₁ tm₂)
      (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
      (T : List (tm₂.Γ tm₂.k₀)), S₁ tm₁.k₁ = L →
      EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
        ⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩
        (some ⟨some (Sum.inr (Sum.inl 1)), (v.1, (v.2.1, none)),
          pack tm₁ tm₂ (Function.update S₁ tm₁.k₁ []) S₂
            ((L.map (fun x => ia₂.invFun (oa₁ x))).reverse ++ T)⟩) (L.length + 1)
  | [], v, S₁, S₂, T, hL => by
      have hupd : Function.update S₁ tm₁.k₁ ([] : List (tm₁.Γ tm₁.k₁)) = S₁ := by
        rw [← hL]; exact Function.update_eq_self _ _
      rw [hupd]
      have hstep := step_copy₁_nil tm₁ tm₂ oa₁ ia₂ v S₁ S₂ T hL
      have this := QMCExit.flip_bind_step (compProg tm₁ tm₂ oa₁ ia₂)
        (⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      refine ⟨⟨1, ?_⟩, by simp⟩
      rw [Function.iterate_one, this]
      exact hstep
  | x :: xs, v, S₁, S₂, T, hL => by
      have hstep := step_copy₁_some tm₁ tm₂ oa₁ ia₂ v S₁ S₂ T x xs hL
      have this := QMCExit.flip_bind_step (compProg tm₁ tm₂ oa₁ ia₂)
        (⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      have e1 : EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
          ⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩
          (some ⟨some (Sum.inr (Sum.inl 0)), (v.1, (v.2.1, some (ia₂.invFun (oa₁ x)))),
            pack tm₁ tm₂ (Function.update S₁ tm₁.k₁ xs) S₂ (ia₂.invFun (oa₁ x) :: T)⟩) 1 := by
        refine ⟨⟨1, ?_⟩, by simp⟩
        rw [Function.iterate_one, this]
        exact hstep
      refine (QMCExit.EvalsToInTime.trans' e1 (copy₁_trace oa₁ ia₂ xs (v.1, (v.2.1, some (ia₂.invFun (oa₁ x))))
        (Function.update S₁ tm₁.k₁ xs) S₂ (ia₂.invFun (oa₁ x) :: T) (by simp)))
        |> QMCExit.EvalsToInTime.congr_cfg rfl (by
            simp only [List.map_cons, List.reverse_cons, List.map_append, List.append_assoc,
              List.singleton_append, List.append_nil, List.nil_append, Function.update_idem])
        |> fun h => QMCExit.EvalsToInTime.mono h (by simp only [List.length_cons]; omega)

/-- **Copy pass 2, whole word** (`EvalsToInTime` form). -/
noncomputable def copy₂_trace (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    ∀ (L : List (tm₂.Γ tm₂.k₀)) (v : Sta tm₁ tm₂)
      (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k)),
      EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
        ⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ L⟩
        (some ⟨some (Sum.inr (Sum.inr tm₂.main)), (v.1, (v.2.1, none)),
          pack tm₁ tm₂ S₁ (Function.update S₂ tm₂.k₀ (L.reverse ++ S₂ tm₂.k₀)) []⟩) (L.length + 1)
  | [], v, S₁, S₂ => by
      have hstep := step_copy₂_nil tm₁ tm₂ oa₁ ia₂ v S₁ S₂ [] rfl
      have this := QMCExit.flip_bind_step (compProg tm₁ tm₂ oa₁ ia₂)
        (⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ []⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      have hupd : Function.update S₂ tm₂.k₀ (([] : List (tm₂.Γ tm₂.k₀)).reverse ++ S₂ tm₂.k₀)
          = S₂ := by simp
      rw [hupd]
      refine ⟨⟨1, ?_⟩, by simp⟩
      rw [Function.iterate_one, this]
      exact hstep
  | x :: xs, v, S₁, S₂ => by
      have hstep := step_copy₂_some tm₁ tm₂ oa₁ ia₂ v S₁ S₂ (x :: xs) x xs rfl
      have this := QMCExit.flip_bind_step (compProg tm₁ tm₂ oa₁ ia₂)
        (⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ (x :: xs)⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      have e1 : EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
          ⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ (x :: xs)⟩
          (some ⟨some (Sum.inr (Sum.inl 1)), (v.1, (v.2.1, some x)),
            pack tm₁ tm₂ S₁ (Function.update S₂ tm₂.k₀ (x :: S₂ tm₂.k₀)) xs⟩) 1 := by
        refine ⟨⟨1, ?_⟩, by simp⟩
        rw [Function.iterate_one, this]
        exact hstep
      refine (QMCExit.EvalsToInTime.trans' e1 (copy₂_trace oa₁ ia₂ xs (v.1, (v.2.1, some x)) S₁
        (Function.update S₂ tm₂.k₀ (x :: S₂ tm₂.k₀))))
        |> QMCExit.EvalsToInTime.congr_cfg rfl (by
            simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
              Function.update_idem, Function.update_self])
        |> fun h => QMCExit.EvalsToInTime.mono h (by simp only [List.length_cons]; omega)

end CompCore

end Turing


/-! ### Growth and size bounds (from the swarm's `Growth.lean`) -/

attribute [instance] Turing.FinTM2.kDecidableEq Turing.FinTM2.kFin Turing.FinTM2.ΛFin
  Turing.FinTM2.σFin Turing.FinTM2.Γk₀Fin

namespace Turing

namespace TM2

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- The number of `push` statements executed inside a single statement chain.

A single `TM2.step` runs a whole chain (`push`/`peek`/`pop`/`load`/`branch` continue within the
same step), ending at `goto` or `halt`; `pushes` therefore bounds the number of symbols that a step
can add to the stacks. -/
def pushes : Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

variable [Fintype K] [DecidableEq K]

/-- Total number of symbols stored on all stacks. -/
def volume (s : (k : K) → List (Γ k)) : ℕ := ∑ k, (s k).length

theorem length_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    (fun j => (Function.update s k v j).length) =
      Function.update (fun j => (s j).length) k v.length := by
  funext j
  by_cases h : j = k
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h]

theorem volume_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    volume (Function.update s k v) + (s k).length = volume s + v.length := by
  classical
  unfold volume
  rw [length_update, Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hh := Finset.sum_erase_add (Finset.univ : Finset K) (fun j => (s j).length)
    (Finset.mem_univ k)
  rw [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volume (q : Stmt Γ Λ σ) (v : σ) (s : (k : K) → List (Γ k)) :
    volume (TM2.stepAux q v s).stk ≤ volume s + pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have hv := volume_update s k (g v :: s k)
      simp only [List.length_cons] at hv
      have hq := ih v (Function.update s k (g v :: s k))
      simp only [TM2.stepAux, pushes]
      omega
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      have hq := ih (g v (s k).head?) (Function.update s k (s k).tail)
      simp only [TM2.stepAux, pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simp only [TM2.stepAux, hg, Bool.cond_false, pushes]
        exact (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simp only [TM2.stepAux, hg, Bool.cond_true, pushes]
        exact (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _
  | halt => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _

end TM2

open TM2 in
/-- Number of symbols a machine can add to all of its stacks in one step, summed over its program. -/
noncomputable def FinTM2.growth (tm : FinTM2) : ℕ := ∑ l, TM2.pushes (tm.m l)

namespace FinTM2

variable (tm : FinTM2)

theorem flip_bind_none : (flip bind tm.step) (none : Option tm.Cfg) = none := rfl

theorem flip_bind_some (c : tm.Cfg) : (flip bind tm.step) (some c) = tm.step c := rfl

theorem step_volume {a b : tm.Cfg} (h : tm.step a = some b) :
    TM2.volume b.stk ≤ TM2.volume a.stk + tm.growth := by
  classical
  obtain ⟨l, v, s⟩ := a
  cases l with
  | none => exact absurd h (by simp [FinTM2.step, TM2.step])
  | some l =>
      have hb : b = TM2.stepAux (tm.m l) v s := (Option.some.inj h).symm
      rw [hb, FinTM2.growth]
      refine (TM2.stepAux_volume _ _ _).trans (Nat.add_le_add_left ?_ _)
      exact Finset.single_le_sum (f := fun x => TM2.pushes (tm.m x))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

theorem iterate_volume (tm : FinTM2) : ∀ (m : ℕ) (a b : tm.Cfg),
    (flip bind tm.step)^[m] (some a) = some b →
      TM2.volume b.stk ≤ TM2.volume a.stk + m * tm.growth
  | 0, a, b, h => by
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
      subst h; simp
  | m + 1, a, b, h => by
      rw [Function.iterate_succ_apply'] at h
      cases hprev : (flip bind tm.step)^[m] (some a) with
      | none => rw [hprev, tm.flip_bind_none] at h; exact absurd h (by simp)
      | some c =>
          rw [hprev, tm.flip_bind_some] at h
          have ih := iterate_volume tm m a c hprev
          have hs := tm.step_volume h
          have hmul : (m + 1) * tm.growth = m * tm.growth + tm.growth := Nat.succ_mul _ _
          rw [hmul]
          omega

theorem volume_initList (s : List (tm.Γ tm.k₀)) : TM2.volume (initList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₀]
  · simp [initList]
  · intro k _ hk
    simp only [initList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem volume_haltList (s : List (tm.Γ tm.k₁)) : TM2.volume (haltList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₁]
  · simp [haltList]
  · intro k _ hk
    simp only [haltList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

end FinTM2

end Turing

namespace StateTransition

variable {α : Type*}

/-- A step bound may always be weakened. -/
def EvalsToInTime.mono {f : α → Option α} {a : α} {b : Option α} {m m' : ℕ}
    (h : EvalsToInTime f a b m) (hm : m ≤ m') : EvalsToInTime f a b m' :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hm⟩

end StateTransition

namespace Turing

/-- **Output length bound for an arbitrary `FinTM2`.** If `tm` outputs `t` on input `s` within `n`
steps, then `t` has at most `s.length + n * growth` symbols. -/
theorem TM2OutputsInTime.output_length_le {tm : FinTM2} {s : List (tm.Γ tm.k₀)}
    {t : List (tm.Γ tm.k₁)} {n : ℕ}
    (h : TM2OutputsInTime tm s (some t) n) : t.length ≤ s.length + n * tm.growth := by
  have hvol := tm.iterate_volume h.steps (initList tm s) (haltList tm t) h.evals_in_steps
  rw [tm.volume_initList, tm.volume_haltList] at hvol
  exact hvol.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Turing
namespace Turing

namespace CompCore

open Polynomial

/-- `initStacks` is "put `l` on the input stack, nothing elsewhere". -/
theorem initStacks_eq_update (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    QMCExit.initStacks tm l = Function.update (fun k => ([] : List (tm.Γ k))) tm.k₀ l := by
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp [QMCExit.initStacks]
  · simp [QMCExit.initStacks, Function.update, h]

/-- Internal initial state of the composite. -/
def compInit (tm₁ tm₂ : FinTM2) : Sta tm₁ tm₂ :=
  (tm₁.initialState, (tm₂.initialState, none))

variable {tm₁ : FinTM2} {tm₂ : FinTM2}
variable {βΓ : Type} [Inhabited βΓ]

/-- **The composite machine**: run `tm₁`, copy its output onto `tm₂`'s input, run `tm₂`.
(An `abbrev`, so that its stack indices reduce definitionally.) -/
noncomputable abbrev compTM (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) : FinTM2 where
  K := Key tm₁ tm₂
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := Sum.inl tm₁.k₀
  k₁ := Sum.inr (Sum.inl tm₂.k₁)
  Γ := Gam tm₁ tm₂
  Λ := Lab tm₁ tm₂
  main := Sum.inl tm₁.main
  ΛFin := inferInstance
  σ := Sta tm₁ tm₂
  initialState := compInit tm₁ tm₂
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := compProg tm₁ tm₂ oa₁ ia₂

/-- The composite's input stack family is `pack` of `tm₁`'s. -/
theorem pack_initStacks (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (l : List (tm₁.Γ tm₁.k₀)) :
    pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []
      = QMCExit.initStacks (compTM oa₁ ia₂) l := by
  funext k
  rcases k with a | (b | u)
  · show QMCExit.initStacks tm₁ l a = QMCExit.initStacks (compTM oa₁ ia₂) l (Sum.inl a)
    unfold QMCExit.initStacks
    by_cases h : a = tm₁.k₀
    · subst h
      rw [dif_pos rfl, dif_pos rfl]
    · rw [dif_neg h, dif_neg (by simpa using h)]
  · show ([] : List (Gam tm₁ tm₂ (Sum.inr (Sum.inl b))))
        = QMCExit.initStacks (compTM oa₁ ia₂) l (Sum.inr (Sum.inl b))
    unfold QMCExit.initStacks
    rw [dif_neg (show (Sum.inr (Sum.inl b) : Key tm₁ tm₂) ≠ (compTM oa₁ ia₂).k₀ from
      by intro e; cases e)]
  · show ([] : List (Gam tm₁ tm₂ (Sum.inr (Sum.inr u))))
        = QMCExit.initStacks (compTM oa₁ ia₂) l (Sum.inr (Sum.inr u))
    unfold QMCExit.initStacks
    rw [dif_neg (show (Sum.inr (Sum.inr u) : Key tm₁ tm₂) ≠ (compTM oa₁ ia₂).k₀ from
      by intro e; cases e)]

/-- The composite's halting stack family is `pack` of `tm₂`'s. -/
theorem pack_haltStacks (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (u : List (tm₂.Γ tm₂.k₁)) :
    pack tm₁ tm₂ (fun _ => []) (QMCExit.haltStacks tm₂ u) []
      = QMCExit.haltStacks (compTM oa₁ ia₂) u := by
  funext k
  rcases k with a | (b | uu)
  · show ([] : List (Gam tm₁ tm₂ (Sum.inl a)))
        = QMCExit.haltStacks (compTM oa₁ ia₂) u (Sum.inl a)
    unfold QMCExit.haltStacks
    rw [dif_neg (show (Sum.inl a : Key tm₁ tm₂) ≠ (compTM oa₁ ia₂).k₁ from
      by intro e; cases e)]
  · show QMCExit.haltStacks tm₂ u b = QMCExit.haltStacks (compTM oa₁ ia₂) u (Sum.inr (Sum.inl b))
    unfold QMCExit.haltStacks
    by_cases h : b = tm₂.k₁
    · subst h
      rw [dif_pos rfl, dif_pos rfl]
    · rw [dif_neg h, dif_neg (by simpa using h)]
  · show ([] : List (Gam tm₁ tm₂ (Sum.inr (Sum.inr uu))))
        = QMCExit.haltStacks (compTM oa₁ ia₂) u (Sum.inr (Sum.inr uu))
    unfold QMCExit.haltStacks
    rw [dif_neg (show (Sum.inr (Sum.inr uu) : Key tm₁ tm₂) ≠ (compTM oa₁ ia₂).k₁ from
      by intro e; cases e)]

/-- The stack that copy pass 1 leaves behind is empty. -/
theorem update_haltStacks_self (t : List (tm₁.Γ tm₁.k₁)) :
    Function.update (QMCExit.haltStacks tm₁ t) tm₁.k₁ [] = fun _ => [] := by
  funext k
  by_cases h : k = tm₁.k₁
  · subst h; simp
  · rw [Function.update_of_ne h]
    simp [QMCExit.haltStacks, h]

/-- **Phase 1**: machine 1's run, lifted into the composite. -/
noncomputable def phase₁ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₁.Λ, M (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l))
    {l : List (tm₁.Γ tm₁.k₀)} {t : List (tm₁.Γ tm₁.k₁)} {N : ℕ}
    (h : TM2OutputsInTime tm₁ l (some t) N) :
    EvalsToInTime (TM2.step M)
      ⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []⟩
      (some ⟨some (Sum.inr (Sum.inl 0)), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.haltStacks tm₁ t) (fun _ => []) []⟩) N := by
  have h1 := iterate_cfg₁ (tm₁ := tm₁) (tm₂ := tm₂) (M := M) hM tm₂.initialState
    (none : Option (tm₂.Γ tm₂.k₀)) (fun _ => []) [] h.steps
    (Turing.initList tm₁ l) (Turing.haltList tm₁ t) h.evals_in_steps
  exact ⟨⟨h.steps, h1⟩, h.steps_le_m⟩

/-- **Phase 2**: machine 2's run, lifted into the composite. -/
noncomputable def phase₂ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₂.Λ, M (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l))
    {S₁ : (k : tm₁.K) → List (tm₁.Γ k)}
    {l : List (tm₂.Γ tm₂.k₀)} {u : List (tm₂.Γ tm₂.k₁)} {M' : ℕ}
    (h : TM2OutputsInTime tm₂ l (some u) M') :
    EvalsToInTime (TM2.step M)
      ⟨some (Sum.inr (Sum.inr tm₂.main)), compInit tm₁ tm₂,
        pack tm₁ tm₂ S₁ (QMCExit.initStacks tm₂ l) []⟩
      (some ⟨none, compInit tm₁ tm₂, pack tm₁ tm₂ S₁ (QMCExit.haltStacks tm₂ u) []⟩) M' := by
  have h1 := iterate_cfg₂ (tm₁ := tm₁) (tm₂ := tm₂) (M := M) hM tm₁.initialState
    (none : Option (tm₂.Γ tm₂.k₀)) S₁ [] h.steps
    (Turing.initList tm₂ l) (Turing.haltList tm₂ u) h.evals_in_steps
  exact ⟨⟨h.steps, h1⟩, h.steps_le_m⟩

/-- **The composite run**: machine 1, the two copy passes, machine 2. -/
noncomputable def comp_run (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    {l : List (tm₁.Γ tm₁.k₀)} {t : List (tm₁.Γ tm₁.k₁)} {u : List (tm₂.Γ tm₂.k₁)}
    {N M' : ℕ} (h₁ : TM2OutputsInTime tm₁ l (some t) N)
    (h₂ : TM2OutputsInTime tm₂ (t.map (fun x => ia₂.invFun (oa₁ x))) (some u) M') :
    EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
      ⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []⟩
      (some ⟨none, compInit tm₁ tm₂,
        pack tm₁ tm₂ (fun _ => []) (QMCExit.haltStacks tm₂ u) []⟩)
      (M' + ((t.length + 1) + ((t.length + 1) + N))) := by
  have hP1 := phase₁ (tm₁ := tm₁) (tm₂ := tm₂) (compProg tm₁ tm₂ oa₁ ia₂) (fun _ => rfl) h₁
  have hC1 := copy₁_trace (tm₁ := tm₁) (tm₂ := tm₂) oa₁ ia₂ t (compInit tm₁ tm₂)
    (QMCExit.haltStacks tm₁ t) (fun _ => []) [] (QMCExit.haltStacks_k1 tm₁ t)
  have hC2 := copy₂_trace (tm₁ := tm₁) (tm₂ := tm₂) oa₁ ia₂
    ((t.map (fun x => ia₂.invFun (oa₁ x))).reverse) (compInit tm₁ tm₂)
    (Function.update (QMCExit.haltStacks tm₁ t) tm₁.k₁ []) (fun _ => [])
  have hP2 := phase₂ (tm₁ := tm₁) (tm₂ := tm₂) (compProg tm₁ tm₂ oa₁ ia₂) (fun _ => rfl)
    (S₁ := Function.update (QMCExit.haltStacks tm₁ t) tm₁.k₁ []) h₂
  -- copy pass 1, with its endpoint written for copy pass 2
  have hC1' := hC1
  simp only [compInit, List.append_nil] at hC1'
  -- copy pass 2, with its endpoint written for machine 2
  have hC2' := hC2
  simp only [compInit, ← initStacks_eq_update, List.reverse_reverse, List.append_nil] at hC2'
  have hchain := QMCExit.EvalsToInTime.trans'
    (QMCExit.EvalsToInTime.trans' (QMCExit.EvalsToInTime.trans' hP1 hC1') hC2') hP2
  simpa only [update_haltStacks_self, List.length_reverse, List.length_map] using hchain

/-- The composite run, packaged as `TM2OutputsInTime` for `compTM`. -/
noncomputable def tm2OutputsInTime_comp (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ)
    (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    {l : List (tm₁.Γ tm₁.k₀)} {t : List (tm₁.Γ tm₁.k₁)} {u : List (tm₂.Γ tm₂.k₁)}
    {N M' : ℕ} (h₁ : TM2OutputsInTime tm₁ l (some t) N)
    (h₂ : TM2OutputsInTime tm₂ (t.map (fun x => ia₂.invFun (oa₁ x))) (some u) M') :
    TM2OutputsInTime (compTM oa₁ ia₂) l (some u)
      (M' + ((t.length + 1) + ((t.length + 1) + N))) := by
  have hrun := comp_run (tm₁ := tm₁) (tm₂ := tm₂) oa₁ ia₂ h₁ h₂
  have hstart : Turing.initList (compTM oa₁ ia₂) l =
      (⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []⟩ :
        TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) := by
    have h1 : Turing.initList (compTM oa₁ ia₂) l =
        (⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
          QMCExit.initStacks (compTM oa₁ ia₂) l⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) := rfl
    rw [h1, ← pack_initStacks]
  have hend : (⟨none, compInit tm₁ tm₂,
        pack tm₁ tm₂ (fun _ => []) (QMCExit.haltStacks tm₂ u) []⟩ :
        TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      = Turing.haltList (compTM oa₁ ia₂) u := by
    have h1 : Turing.haltList (compTM oa₁ ia₂) u =
        (⟨none, compInit tm₁ tm₂, QMCExit.haltStacks (compTM oa₁ ia₂) u⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) := rfl
    rw [h1, ← pack_haltStacks]
  have h := hrun
  rw [← hstart, hend] at h
  exact QMCExit.tm2OutputsInTime_of_cfg h rfl

end CompCore
end Turing

open IntConeFPT OnlineCRS.Combine

theorem solution (M N : Machine) :
    ∃ W : Machine, ∀ (x y z : List Sym) (T U : ℝ),
      RunsWithin M x y T → RunsWithin N y z U →
      RunsWithin W x z (T + U + 2 * (y.length + 1)) := by
  classical
  let W : Machine := ⟨Turing.CompCore.compTM M.outputAlphabet N.inputAlphabet,
    M.inputAlphabet, N.outputAlphabet⟩
  refine ⟨W, ?_⟩
  rintro x y z T U ⟨n,hn,⟨h₁⟩⟩ ⟨m,hm,⟨h₂⟩⟩
  have eqMap :
      (y.map M.outputAlphabet.invFun).map (fun v => N.inputAlphabet.invFun (M.outputAlphabet v))
        = y.map N.inputAlphabet.invFun := by
    simp only [List.map_map, Function.comp_def]
    congr 1; funext v
    exact congrArg N.inputAlphabet.invFun (M.outputAlphabet.apply_symm_apply v)
  have h := Turing.CompCore.tm2OutputsInTime_comp (tm₁ := M.tm) (tm₂ := N.tm)
    M.outputAlphabet N.inputAlphabet h₁ (eqMap ▸ h₂)
  refine ⟨_, ?_, ⟨h⟩⟩
  simp only [Nat.cast_add,List.length_map,Nat.cast_one]
  linarith
