-- Prove2me | solution 1 for HILL.PRG.inversion_checker_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-27T01:04:19.823776+00:00
-- url     : https://prove2.me/submissions/db303ddc-4084-4d5e-a532-5e7892fdfab8

import Definitions.Def_HILL_PRG_InversionCheck

/-
**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

The reverse implication is attributed to Levin (1987) by Håstad, Impagliazzo,
Levin and Luby, SIAM J. Comput. 28(4), 1999, Theorem 6.3.
Stack-growth and machine-simulation techniques adapt Lucas’s Apache-2.0
formalization of PvsNP.isPolyTime_comp, Prove2Me submission
8b9e413d-107f-462f-bfa0-5e255ca4b7e2.
-/


noncomputable section

namespace HILL.PRG.CheckerTM2

open Turing
open Turing.TM2.Stmt

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- A bit-string function together with its bounded multi-stack implementation. -/
structure Computer where
  fn : Bits → Bits
  impl : TM2ComputableInPolyTime (id : Bits → Bits) (id : Bits → Bits) fn

abbrev Machines := Fin 4 → Computer
abbrev machine (C : Machines) (j : Fin 4) := (C j).impl.tm
abbrev Key (C : Machines) := (Σ j : Fin 4, (machine C j).K) ⊕ Fin 9

instance (C : Machines) : DecidableEq (Key C) := inferInstanceAs
  (DecidableEq ((Σ j : Fin 4, (machine C j).K) ⊕ Fin 9))
instance (C : Machines) : Fintype (Key C) := inferInstanceAs
  (Fintype ((Σ j : Fin 4, (machine C j).K) ⊕ Fin 9))

def Alphabet (C : Machines) : Key C → Type
  | .inl ⟨j, k⟩ => (machine C j).Γ k
  | .inr _ => Bool

abbrev Memory (C : Machines) :=
  (∀ j : Fin 4, (machine C j).σ) × Option Bool × Option Bool × Bool

instance (C : Machines) : Fintype (Memory C) := inferInstanceAs
  (Fintype ((∀ j : Fin 4, (machine C j).σ) × Option Bool × Option Bool × Bool))

inductive Phase where
  | parse | clone | sendI | restorePayload | secI | secT | lengths
  | secL | takeY | sendE | secE | reverseE | equality
  deriving DecidableEq

instance : Fintype Phase := ⟨{.parse, .clone, .sendI, .restorePayload, .secI, .secT,
  .lengths, .secL, .takeY, .sendE, .secE, .reverseE, .equality}, by intro p; cases p <;> simp⟩

abbrev Label (C : Machines) :=
  (Σ j : Fin 4, (machine C j).Λ) ⊕ (Phase ⊕ Fin (Fintype.card (Key C) + 1))

instance (C : Machines) : Fintype (Label C) := inferInstanceAs
  (Fintype ((Σ j : Fin 4, (machine C j).Λ) ⊕
    (Phase ⊕ Fin (Fintype.card (Key C) + 1))))

abbrev Statement (C : Machines) := TM2.Stmt (Alphabet C) (Label C) (Memory C)
abbrev Store (C : Machines) := ∀ k : Key C, List (Alphabet C k)

def initialMemory (C : Machines) : Memory C :=
  (fun j => (machine C j).initialState, none, none, false)

def phaseLabel {C : Machines} (p : Phase) : Label C := .inr (.inl p)
def cleanLabel {C : Machines} (i : Fin (Fintype.card (Key C) + 1)) : Label C := .inr (.inr i)
def ckey {C : Machines} (i : Fin 9) : Key C := .inr i

def ikey (C : Machines) (j : Fin 4) : Key C := .inl ⟨j, (machine C j).k₀⟩
def okey (C : Machines) (j : Fin 4) : Key C := .inl ⟨j, (machine C j).k₁⟩

def ret (j : Fin 4) : Phase :=
  if j = 0 then .secT else if j = 1 then .lengths else if j = 2 then .takeY else .reverseE

def updateState (C : Machines) (v : Memory C) (j : Fin 4) (s : (machine C j).σ) : Memory C :=
  (Function.update v.1 j s, v.2.1, v.2.2.1, v.2.2.2)

def lift (C : Machines) (j : Fin 4) :
    TM2.Stmt (machine C j).Γ (machine C j).Λ (machine C j).σ → Statement C
  | .push k f q => .push (.inl ⟨j, k⟩) (fun v => f (v.1 j)) (lift C j q)
  | .peek k f q => .peek (.inl ⟨j, k⟩)
      (fun v x => updateState C v j (f (v.1 j) x)) (lift C j q)
  | .pop k f q => .pop (.inl ⟨j, k⟩)
      (fun v x => updateState C v j (f (v.1 j) x)) (lift C j q)
  | .load f q => .load (fun v => updateState C v j (f (v.1 j))) (lift C j q)
  | .branch p q₀ q₁ => .branch (fun v => p (v.1 j)) (lift C j q₀) (lift C j q₁)
  | .goto f => .goto (fun v => .inl ⟨j, f (v.1 j)⟩)
  | .halt => .goto (fun _ => phaseLabel (ret j))

def go {C : Machines} (p : Phase) : Statement C := .goto (fun _ => phaseLabel p)
def clean {C : Machines} : Statement C := .goto (fun _ => cleanLabel 0)
def call (C : Machines) (j : Fin 4) : Statement C := .goto (fun _ => .inl ⟨j, (machine C j).main⟩)

def temp0 {C : Machines} (v : Memory C) (b : Option Bool) : Memory C :=
  (v.1, b, v.2.2.1, v.2.2.2)
def temp1 {C : Machines} (v : Memory C) (b : Option Bool) : Memory C :=
  (v.1, v.2.1, b, v.2.2.2)
def acceptMemory {C : Machines} (v : Memory C) : Memory C :=
  (v.1, v.2.1, v.2.2.1, true)

def pop0 (C : Machines) (k : Key C) (decode : Alphabet C k → Bool) (q : Statement C) : Statement C :=
  .pop k (fun v b => temp0 v (b.map decode)) q
def pop1 (C : Machines) (k : Key C) (decode : Alphabet C k → Bool) (q : Statement C) : Statement C :=
  .pop k (fun v b => temp1 v (b.map decode)) q

def move (C : Machines) (src dst : Key C) (decode : Alphabet C src → Bool)
    (encode : Bool → Alphabet C dst) (p : Phase) (done : Statement C) : Statement C :=
  pop0 C src decode (.branch (fun v => v.2.1.isSome)
    (.push dst (fun v => encode (v.2.1.getD false)) (go p)) done)

def clone (C : Machines) (src dst₀ dst₁ : Key C) (decode : Alphabet C src → Bool)
    (encode₀ : Bool → Alphabet C dst₀) (encode₁ : Bool → Alphabet C dst₁)
    (p : Phase) (done : Statement C) : Statement C :=
  pop0 C src decode (.branch (fun v => v.2.1.isSome)
    (.push dst₀ (fun v => encode₀ (v.2.1.getD false))
      (.push dst₁ (fun v => encode₁ (v.2.1.getD false)) (go p))) done)

def controller (C : Machines) : Phase → Statement C
  | .parse => pop0 C (ckey 0) id
      (.branch (fun v => v.2.1 == some true)
        (.push (ckey 1) (fun _ => true) (go .parse))
        (.branch (fun v => v.2.1.isSome)
          (.pop (ckey 0) (fun v _ => temp0 v none) (go .clone))
          (.load (fun v => temp0 v none) (go .clone))))
  | .clone => clone C (ckey 0) (ckey 3) (ckey 4) id id id .clone (go .sendI)
  | .sendI => move C (ckey 3) (ikey C 0) id (C 0).impl.inputAlphabet.symm .sendI (go .restorePayload)
  | .restorePayload => move C (ckey 4) (ckey 3) id id .restorePayload
      (.push (ikey C 0) (fun _ => (C 0).impl.inputAlphabet.symm false) (go .secI))
  | .secI => clone C (ckey 1) (ikey C 0) (ckey 2) id (C 0).impl.inputAlphabet.symm id .secI (call C 0)
  | .secT => clone C (ckey 2) (ikey C 1) (ckey 1) id (C 1).impl.inputAlphabet.symm id .secT (call C 1)
  | .lengths => pop0 C (okey C 1) (C 1).impl.outputAlphabet
      (pop1 C (okey C 0) (C 0).impl.outputAlphabet
        (.branch (fun v => v.2.1.isSome && v.2.2.1.isSome)
          (.push (ckey 5) (fun v => v.2.2.1.getD false) (go .lengths))
          (.branch (fun v => v.2.1.isNone && v.2.2.1.isNone) (go .secL) clean)))
  | .secL => clone C (ckey 1) (ikey C 2) (ckey 2) id (C 2).impl.inputAlphabet.symm id .secL (call C 2)
  | .takeY => pop0 C (okey C 2) (C 2).impl.outputAlphabet
      (.branch (fun v => v.2.1.isSome)
        (pop1 C (ckey 3) id (.branch (fun v => v.2.2.1.isSome)
          (.push (ckey 6) (fun v => v.2.2.1.getD false) (go .takeY)) (go .sendE)))
        (go .sendE))
  | .sendE => move C (ckey 5) (ikey C 3) id (C 3).impl.inputAlphabet.symm .sendE
      (.push (ikey C 3) (fun _ => (C 3).impl.inputAlphabet.symm false)
        (.push (ikey C 3) (fun _ => (C 3).impl.inputAlphabet.symm false) (go .secE)))
  | .secE => move C (ckey 2) (ikey C 3) id (C 3).impl.inputAlphabet.symm .secE (call C 3)
  | .reverseE => move C (okey C 3) (ckey 7) (C 3).impl.outputAlphabet id .reverseE (go .equality)
  | .equality => pop0 C (ckey 7) id (pop1 C (ckey 6) id
      (.branch (fun v => v.2.1 == v.2.2.1)
        (.branch (fun v => v.2.1.isSome) (go .equality) (.load acceptMemory clean)) clean))

def cleanup (C : Machines) (i : Fin (Fintype.card (Key C) + 1)) : Statement C :=
  if h : i.val < Fintype.card (Key C) then
    pop0 C ((Fintype.equivFin (Key C)).symm ⟨i.val, h⟩) (fun _ => true)
      (.branch (fun v => v.2.1.isSome)
        (.goto (fun _ => cleanLabel i))
        (.goto (fun _ => cleanLabel ⟨i.val + 1, by omega⟩)))
  else
    .branch (fun v => v.2.2.2)
      (.load (fun _ => initialMemory C) (.push (ckey 8) (fun _ => true) .halt))
      (.load (fun _ => initialMemory C) .halt)

def program (C : Machines) : Label C → Statement C
  | .inl ⟨j, l⟩ => lift C j ((machine C j).m l)
  | .inr (.inl p) => controller C p
  | .inr (.inr i) => cleanup C i

def checker (C : Machines) : FinTM2 where
  K := Key C
  k₀ := ckey 0
  k₁ := ckey 8
  Γ := Alphabet C
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  Λ := Label C
  main := phaseLabel .parse
  σ := Memory C
  initialState := initialMemory C
  m := program C

end HILL.PRG.CheckerTM2
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false


noncomputable section
open Turing HILL.PRG HILL.PRG.CheckerTM2
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace WentaoHILLMachine

abbrev Locals (C : Machines) := ∀ j : Fin 4, ∀ k : (machine C j).K, List ((machine C j).Γ k)
abbrev Controls := Fin 9 → Bits
abbrev Config (C : Machines) := TM2.Cfg (Alphabet C) (Label C) (Memory C)

def pack (C : Machines) (Q : Locals C) (B : Controls) : Store C
  | .inl ⟨j, k⟩ => Q j k
  | .inr k => B k

@[simp] lemma pack_component (C : Machines) (Q : Locals C) (B : Controls)
    (j : Fin 4) (k : (machine C j).K) : pack C Q B (.inl ⟨j, k⟩) = Q j k := rfl

@[simp] lemma pack_control (C : Machines) (Q : Locals C) (B : Controls)
    (k : Fin 9) : pack C Q B (.inr k) = B k := rfl

lemma pack_update_component (C : Machines) (Q : Locals C) (B : Controls)
    (j : Fin 4) (k : (machine C j).K) (s : List ((machine C j).Γ k)) :
    Function.update (pack C Q B) (.inl ⟨j, k⟩) s =
      pack C (Function.update Q j (Function.update (Q j) k s)) B := by
  classical
  funext z
  rcases z with ⟨i, l⟩ | l
  · by_cases hij : i = j
    · subst i
      by_cases hlk : l = k
      · subst l; simp
      · have hkey : (.inl ⟨j, l⟩ : Key C) ≠ .inl ⟨j, k⟩ := by
          intro h
          exact hlk (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj h)).2)
        simp only [Function.update_of_ne hkey, pack_component,
          Function.update_self, Function.update_of_ne hlk]
    · have hkey : (.inl ⟨i, l⟩ : Key C) ≠ .inl ⟨j, k⟩ := by
        intro h
        exact hij ((Sigma.mk.inj_iff.mp (Sum.inl.inj h)).1)
      simp only [Function.update_of_ne hkey, pack_component, Function.update_of_ne hij]
  · have hkey : (.inr l : Key C) ≠ .inl ⟨j, k⟩ := Sum.inr_ne_inl
    simp only [Function.update_of_ne hkey, pack_control]

lemma pack_update_control (C : Machines) (Q : Locals C) (B : Controls)
    (k : Fin 9) (s : Bits) : Function.update (pack C Q B) (.inr k) s =
      pack C Q (Function.update B k s) := by
  funext z
  rcases z with ⟨j, l⟩ | l
  · simp
  · by_cases h : l = k
    · subst l; simp
    · simp [h]

@[simp] lemma state_current (C : Machines) (v : Memory C) (j : Fin 4) (s : (machine C j).σ) :
    (updateState C v j s).1 j = s := by simp [updateState]

@[simp] lemma state_overwrite (C : Machines) (v : Memory C) (j : Fin 4)
    (s t : (machine C j).σ) :
    updateState C (updateState C v j s) j t = updateState C v j t := by
  simp [updateState, Function.update_idem]

def embed (C : Machines) (j : Fin 4)
    (c : TM2.Cfg (machine C j).Γ (machine C j).Λ (machine C j).σ)
    (v : Memory C) (Q : Locals C) (B : Controls) : Config C :=
  ⟨match c.l with | some l => .some (.inl ⟨j, l⟩) | none => .some (phaseLabel (ret j)),
    updateState C v j c.var, pack C (Function.update Q j c.stk) B⟩

lemma stepAux_lift (C : Machines) (j : Fin 4)
    (q : TM2.Stmt (machine C j).Γ (machine C j).Λ (machine C j).σ)
    (s : (machine C j).σ) (S : ∀ k, List ((machine C j).Γ k))
    (v : Memory C) (Q : Locals C) (B : Controls) :
    TM2.stepAux (lift C j q) (updateState C v j s) (pack C (Function.update Q j S) B) =
      embed C j (TM2.stepAux q s S) v Q B := by
  induction q generalizing s S with
  | push k f q ih =>
    simp only [lift, TM2.stepAux, state_current]
    rw [pack_update_component]
    simp only [pack_component, Function.update_self, Function.update_idem]
    exact ih _ _
  | peek k f q ih =>
    simp only [lift, TM2.stepAux, state_current, pack_component,
      Function.update_self, state_overwrite]
    exact ih _ _
  | pop k f q ih =>
    simp only [lift, TM2.stepAux, state_current, pack_component,
      Function.update_self, state_overwrite]
    rw [pack_update_component]
    simp only [pack_component, Function.update_self, Function.update_idem]
    exact ih _ _
  | load f q ih =>
    simp only [lift, TM2.stepAux, state_current, state_overwrite]
    exact ih _ _
  | branch p q₀ q₁ ih₀ ih₁ =>
    simp only [lift, TM2.stepAux, state_current]
    cases h : p s
    · simpa [h] using ih₁ s S
    · simpa [h] using ih₀ s S
  | goto f => simp [lift, TM2.stepAux, embed]
  | halt => rfl

lemma iterate_none {α : Type} (f : α → Option α) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, show (flip bind f) none = none from rfl]
    exact ih

lemma run_embed (C : Machines) (j : Fin 4) (n : ℕ)
    (c d : TM2.Cfg (machine C j).Γ (machine C j).Λ (machine C j).σ)
    (v : Memory C) (Q : Locals C) (B : Controls)
    (h : (flip bind (machine C j).step)^[n] (some c) = some d) :
    (flip bind (checker C).step)^[n] (some (embed C j c v Q B)) =
      some (embed C j d v Q B) := by
  induction n generalizing c with
  | zero =>
    simp only [Function.iterate_zero, id_eq] at h ⊢
    obtain rfl := Option.some_inj.mp h
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    rcases c with ⟨l, s, S⟩
    cases l with
    | none =>
      exfalso
      rw [show (flip bind (machine C j).step) (some ⟨none, s, S⟩) = none from rfl,
        iterate_none _ n] at h
      simpa using h
    | some l =>
      have hs : (flip bind (checker C).step) (some (embed C j ⟨some l, s, S⟩ v Q B)) =
          some (embed C j (TM2.stepAux ((machine C j).m l) s S) v Q B) := by
        change some (TM2.stepAux (lift C j ((machine C j).m l))
          (updateState C v j s) (pack C (Function.update Q j S) B)) = _
        rw [stepAux_lift]
      rw [hs]
      exact ih _ h

end WentaoHILLMachine


/- Stack-growth arguments adapt Lucas's accepted PvsNP.isPolyTime_comp
formalization, submission 8b9e413d-107f-462f-bfa0-5e255ca4b7e2,
licensed Apache-2.0. The checker-specific polynomial envelope is developed here. -/

noncomputable section
open Turing HILL.PRG HILL.PRG.CheckerTM2
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace WentaoHILLResource

/-- The maximal number of pushes performed by a single statement. -/
def pushes {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0

/-- The total number of symbols stored on all stacks. -/
def totalSize {K : Type} [Fintype K] {Γ : K → Type} (S : ∀ k, List (Γ k)) : ℕ :=
  ∑ k : K, (S k).length

variable {K : Type} [Fintype K] [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

theorem totalSize_update (S : ∀ k, List (Γ k)) (i : K) (l : List (Γ i)) :
    totalSize (Function.update S i l) + (S i).length = totalSize S + l.length := by
  have h1 : ∀ j, (Function.update S i l j).length
      = Function.update (fun j => (S j).length) i l.length j := by
    intro j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  have h2 : totalSize (Function.update S i l) = l.length + ∑ j ∈ Finset.univ \ {i}, (S j).length := by
    unfold totalSize
    simp only [h1]
    exact Finset.sum_update_of_mem (Finset.mem_univ i) _ _
  have h3 : (S i).length + ∑ j ∈ Finset.univ.erase i, (S j).length = totalSize S := by
    unfold totalSize
    exact Finset.add_sum_erase Finset.univ (fun j => (S j).length) (Finset.mem_univ i)
  have h4 : Finset.univ \ ({i} : Finset K) = Finset.univ.erase i := by
    ext j; simp [Finset.mem_erase, and_comm]
  rw [h4] at h2
  omega

theorem totalSize_stepAux (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    totalSize (TM2.stepAux q v S).stk ≤ totalSize S + pushes q := by
  induction q generalizing v S with
  | push k f q ih =>
      have h := totalSize_update S k (f v :: S k)
      have := ih v (Function.update S k (f v :: S k))
      simp only [TM2.stepAux, pushes, List.length_cons] at *
      omega
  | peek k f q ih => simpa [TM2.stepAux, pushes] using ih _ _
  | pop k f q ih =>
      have h := totalSize_update S k (S k).tail
      have h2 : (S k).tail.length ≤ (S k).length := by cases S k <;> simp
      have := ih (f v (S k).head?) (Function.update S k (S k).tail)
      simp only [TM2.stepAux, pushes] at *
      omega
  | load a q ih => simpa [TM2.stepAux, pushes] using ih _ _
  | branch c q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.stepAux, pushes]
      cases hc : c v
      · have := ih₂ v S; simp; omega
      · have := ih₁ v S; simp; omega
  | goto l => simp [TM2.stepAux, pushes, totalSize]
  | halt => simp [TM2.stepAux, pushes, totalSize]



/-- The maximal number of pushes performed by a single step of the machine `M`. -/
def maxPushes (M : FinTM2) : ℕ := Finset.univ.sup fun l : M.Λ => pushes (M.m l)

theorem pushes_le_maxPushes (M : FinTM2) (l : M.Λ) : pushes (M.m l) ≤ maxPushes M :=
  Finset.le_sup (f := fun l : M.Λ => pushes (M.m l)) (Finset.mem_univ l)

theorem totalSize_step {M : FinTM2} {c c' : M.Cfg} (h : M.step c = some c') :
    totalSize c'.stk ≤ totalSize c.stk + maxPushes M := by
  obtain ⟨l, v, S⟩ := c
  match l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have hc' : c' = TM2.stepAux (M.m l) v S := by
        have : some c' = some (TM2.stepAux (M.m l) v S) := by
          simpa [FinTM2.step, TM2.step] using h.symm
        exact Option.some_inj.mp this
      subst hc'
      exact le_trans (totalSize_stepAux (M.m l) v S)
        (Nat.add_le_add_left (pushes_le_maxPushes M l) _)

theorem totalSize_iterate {M : FinTM2} (t : ℕ) (c c' : M.Cfg)
    (h : (flip bind M.step)^[t] (some c) = some c') :
    totalSize c'.stk ≤ totalSize c.stk + t * maxPushes M := by
  induction t generalizing c with
  | zero => simp only [Function.iterate_zero, id_eq, Option.some_inj] at h; subst h; simp
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      match hs : M.step c with
      | none =>
          rw [show (flip bind M.step) (some c) = none from hs] at h
          have hn : ∀ k : ℕ, (flip bind M.step)^[k] none = none := by
            intro k
            induction k with
            | zero => rfl
            | succ k ih => rw [Function.iterate_succ_apply]; exact ih
          rw [hn] at h
          exact absurd h (by simp)
      | some c₁ =>
          rw [show (flip bind M.step) (some c) = some c₁ from hs] at h
          have h1 := ih c₁ h
          have h2 := totalSize_step hs
          have : n * maxPushes M + maxPushes M = (n+1) * maxPushes M := by ring
          omega

/-- The stacks of the initial configuration. -/
theorem initList_stk (M : FinTM2) (s : List (M.Γ M.k₀)) :
    (initList M s).stk = Function.update (fun _ => []) M.k₀ s := by
  funext k
  by_cases h : k = M.k₀
  · subst h; simp [initList]
  · simp [initList, h]

/-- The stacks of a halting configuration. -/
theorem haltList_stk (M : FinTM2) (s : List (M.Γ M.k₁)) :
    (haltList M s).stk = Function.update (fun _ => []) M.k₁ s := by
  funext k
  by_cases h : k = M.k₁
  · subst h; simp [haltList]
  · simp [haltList, h]

theorem totalSize_empty {K : Type} [Fintype K] {Γ : K → Type} :
    totalSize (fun k => ([] : List (Γ k))) = 0 := by simp [totalSize]

theorem totalSize_initList (M : FinTM2) (s : List (M.Γ M.k₀)) :
    totalSize (initList M s).stk = s.length := by
  rw [initList_stk]
  have := totalSize_update (Γ := M.Γ) (fun _ => []) M.k₀ s
  simp only [totalSize_empty, List.length_nil] at this
  omega

theorem totalSize_haltList (M : FinTM2) (s : List (M.Γ M.k₁)) :
    totalSize (haltList M s).stk = s.length := by
  rw [haltList_stk]
  have := totalSize_update (Γ := M.Γ) (fun _ => []) M.k₁ s
  simp only [totalSize_empty, List.length_nil] at this
  omega


/-- Evaluation of a polynomial with natural-number coefficients is monotone. -/
theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using Nat.add_le_add hp hq
  | monomial n a =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

end WentaoHILLResource

namespace WentaoHILLResource

lemma computer_length (D : Computer) (w : Bits) :
    (D.fn w).length ≤ w.length + maxPushes D.impl.tm * D.impl.time.eval w.length := by
  have h := D.impl.outputsFun w
  have hg := totalSize_iterate h.steps _ _ h.evals_in_steps
  rw [totalSize_initList, totalSize_haltList] at hg
  simp only [id_eq, List.length_map] at hg
  have ht : h.steps ≤ D.impl.time.eval w.length := h.steps_le_m
  have hm := Nat.mul_le_mul_right (maxPushes D.impl.tm) ht
  nlinarith

def localBound (C : Machines) (j : Fin 4) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (maxPushes (machine C j)) * (C j).impl.time +
    (C j).impl.time + 2

def envelope (C : Machines) : Polynomial ℕ :=
  2 * Polynomial.X + 2 + ∑ j : Fin 4, localBound C j

lemma localBound_eval (C : Machines) (j : Fin 4) (n : ℕ) :
    (localBound C j).eval n = n + maxPushes (machine C j) * (C j).impl.time.eval n +
      (C j).impl.time.eval n + 2 := by simp [localBound]

lemma envelope_eval (C : Machines) (n : ℕ) :
    (envelope C).eval n = 2 * n + 2 + ∑ j : Fin 4, (localBound C j).eval n := by
  simp [envelope, Polynomial.eval_finsetSum]

lemma local_le_envelope (C : Machines) (j : Fin 4) (n : ℕ) :
    (localBound C j).eval n ≤ (envelope C).eval n := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 4 => (localBound C j).eval n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [envelope_eval]
  omega

lemma envelope_ge (C : Machines) (n : ℕ) : 2 * n + 2 ≤ (envelope C).eval n := by
  rw [envelope_eval]
  omega

lemma envelope_mono (C : Machines) : Monotone (envelope C).eval := by
  intro n m h
  exact eval_mono _ h

lemma time_le_envelope (C : Machines) (j : Fin 4) (n : ℕ) :
    (C j).impl.time.eval n ≤ (envelope C).eval n := by
  have h := local_le_envelope C j n
  rw [localBound_eval] at h
  omega

lemma length_le_envelope (C : Machines) (j : Fin 4) (w : Bits) :
    ((C j).fn w).length ≤ (envelope C).eval w.length := by
  have h := computer_length (C j) w
  change ((C j).fn w).length ≤ w.length + maxPushes (machine C j) * (C j).impl.time.eval w.length at h
  have hb := local_le_envelope C j w.length
  rw [localBound_eval] at hb
  exact h.trans (by omega)

end WentaoHILLResource


noncomputable section
open Turing HILL.PRG HILL.PRG.CheckerTM2 WentaoHILLMachine
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace WentaoHILLLoops

def config (C : Machines) (l : Label C) (v : Memory C) (S : Store C) : Config C := ⟨some l, v, S⟩

lemma move_loop (C : Machines) (src dst : Key C) (h : src ≠ dst)
    (decode : Alphabet C src → Bool) (encode : Bool → Alphabet C dst)
    (p : Phase) (done : Statement C)
    (hprog : program C (phaseLabel p) = move C src dst decode encode p done)
    (v : Memory C) (S : Store C) (xs : List (Alphabet C src)) (ys : List (Alphabet C dst)) :
    (flip bind (checker C).step)^[xs.length + 1]
        (some (config C (phaseLabel p) v (Function.update (Function.update S src xs) dst ys))) =
      some (TM2.stepAux done (temp0 v none)
        (Function.update (Function.update S src []) dst
          ((xs.map (encode ∘ decode)).reverse ++ ys))) := by
  classical
  induction xs generalizing v ys with
  | nil =>
    change some (TM2.stepAux (program C (phaseLabel p)) v _) = _
    rw [hprog]
    simp [move, pop0, TM2.stepAux, h, h.symm, temp0, Function.update_comm h]
  | cons x xs ih =>
    have hs : (flip bind (checker C).step)
        (some (config C (phaseLabel p) v (Function.update (Function.update S src (x :: xs)) dst ys))) =
        some (config C (phaseLabel p) (temp0 v (some (decode x)))
          (Function.update (Function.update S src xs) dst (encode (decode x) :: ys))) := by
      change some (TM2.stepAux (program C (phaseLabel p)) v _) = _
      rw [hprog]
      simp [move, pop0, TM2.stepAux, config, go, h, h.symm, temp0, Function.update_comm h]
    change (flip bind (checker C).step)^[xs.length + 1 + 1] _ = _
    rw [Function.iterate_succ_apply, hs, ih]
    simp [temp0, List.map_cons, List.reverse_cons, List.append_assoc]

lemma clone_loop (C : Machines) (src dst₀ dst₁ : Key C)
    (h₀ : src ≠ dst₀) (h₁ : src ≠ dst₁) (h₂ : dst₀ ≠ dst₁)
    (decode : Alphabet C src → Bool)
    (encode₀ : Bool → Alphabet C dst₀) (encode₁ : Bool → Alphabet C dst₁)
    (p : Phase) (done : Statement C)
    (hprog : program C (phaseLabel p) = clone C src dst₀ dst₁ decode encode₀ encode₁ p done)
    (v : Memory C) (S : Store C) (xs : List (Alphabet C src))
    (ys₀ : List (Alphabet C dst₀)) (ys₁ : List (Alphabet C dst₁)) :
    (flip bind (checker C).step)^[xs.length + 1]
        (some (config C (phaseLabel p) v
          (Function.update (Function.update (Function.update S src xs) dst₀ ys₀) dst₁ ys₁))) =
      some (TM2.stepAux done (temp0 v none)
        (Function.update (Function.update (Function.update S src []) dst₀
          ((xs.map (encode₀ ∘ decode)).reverse ++ ys₀)) dst₁
          ((xs.map (encode₁ ∘ decode)).reverse ++ ys₁))) := by
  classical
  induction xs generalizing v ys₀ ys₁ with
  | nil =>
    change some (TM2.stepAux (program C (phaseLabel p)) v _) = _
    rw [hprog]
    simp [clone, pop0, TM2.stepAux, h₀, h₀.symm, h₁, h₁.symm, h₂, h₂.symm, temp0,
      Function.update_comm h₀, Function.update_comm h₁, Function.update_comm h₂]
  | cons x xs ih =>
    have hs : (flip bind (checker C).step)
        (some (config C (phaseLabel p) v
          (Function.update (Function.update (Function.update S src (x :: xs)) dst₀ ys₀) dst₁ ys₁))) =
        some (config C (phaseLabel p) (temp0 v (some (decode x)))
          (Function.update (Function.update (Function.update S src xs) dst₀
            (encode₀ (decode x) :: ys₀)) dst₁ (encode₁ (decode x) :: ys₁))) := by
      change some (TM2.stepAux (program C (phaseLabel p)) v _) = _
      rw [hprog]
      simp [clone, pop0, TM2.stepAux, config, go, h₀, h₀.symm, h₁, h₁.symm, h₂, h₂.symm, temp0,
        Function.update_comm h₀, Function.update_comm h₁, Function.update_comm h₂]
    change (flip bind (checker C).step)^[xs.length + 1 + 1] _ = _
    rw [Function.iterate_succ_apply, hs, ih]
    simp [temp0, List.map_cons, List.reverse_cons, List.append_assoc]

lemma drain_loop (C : Machines) (src : Key C) (l : Label C) (done : Statement C)
    (hprog : program C l = pop0 C src (fun _ => true)
      (.branch (fun v => v.2.1.isSome) (.goto (fun _ => l)) done))
    (v : Memory C) (S : Store C) (xs : List (Alphabet C src)) :
    (flip bind (checker C).step)^[xs.length + 1]
        (some (config C l v (Function.update S src xs))) =
      some (TM2.stepAux done (temp0 v none) (Function.update S src [])) := by
  classical
  induction xs generalizing v with
  | nil =>
    change some (TM2.stepAux (program C l) v _) = _
    rw [hprog]
    simp [pop0, TM2.stepAux, temp0]
  | cons x xs ih =>
    have hs : (flip bind (checker C).step) (some (config C l v (Function.update S src (x :: xs)))) =
        some (config C l (temp0 v (some true)) (Function.update S src xs)) := by
      change some (TM2.stepAux (program C l) v _) = _
      rw [hprog]
      simp [pop0, TM2.stepAux, config, temp0]
    change (flip bind (checker C).step)^[xs.length + 1 + 1] _ = _
    rw [Function.iterate_succ_apply, hs, ih]
    rfl

lemma parse_loop (C : Machines) (v : Memory C) (S : Store C) (w z : Bits) :
    (flip bind (checker C).step)^[((w.takeWhile id).length) + 1]
        (some (config C (phaseLabel .parse) v
          (Function.update (Function.update S (ckey 0) w) (ckey 1) z))) =
      some (config C (phaseLabel .clone) (temp0 v none)
        (Function.update (Function.update S (ckey 0) (w.drop ((w.takeWhile id).length + 2)))
          (ckey 1) (List.replicate (w.takeWhile id).length true ++ z))) := by
  classical
  have hkey : (ckey 0 : Key C) ≠ ckey 1 := by simp [ckey]
  induction w generalizing v z with
  | nil =>
    change some (TM2.stepAux (program C (phaseLabel .parse)) v _) = _
    simp [program, controller, pop0, TM2.stepAux, config, go, phaseLabel, hkey, hkey.symm,
      temp0, Function.update_comm hkey]
  | cons b w ih =>
    cases b with
    | false =>
      change some (TM2.stepAux (program C (phaseLabel .parse)) v _) = _
      simp [program, controller, pop0, TM2.stepAux, config, go, phaseLabel, hkey, hkey.symm,
        temp0, Function.update_comm hkey, List.drop_one, Bool.cond_eq_ite]
    | true =>
      have hs : (flip bind (checker C).step)
          (some (config C (phaseLabel .parse) v
            (Function.update (Function.update S (ckey 0) (true :: w)) (ckey 1) z))) =
          some (config C (phaseLabel .parse) (temp0 v (some true))
            (Function.update (Function.update S (ckey 0) w) (ckey 1) (true :: z))) := by
        change some (TM2.stepAux (program C (phaseLabel .parse)) v _) = _
        simp [program, controller, pop0, TM2.stepAux, config, go, phaseLabel, hkey, hkey.symm,
          temp0, Function.update_comm hkey]
      simp only [List.takeWhile_cons_of_pos (show id true = true from rfl), List.length_cons]
      rw [Function.iterate_succ_apply, hs, ih]
      simp [temp0, List.drop_succ_cons, List.replicate_succ', List.append_assoc]

end WentaoHILLLoops


noncomputable section
open Turing HILL.PRG HILL.PRG.CheckerTM2 WentaoHILLMachine WentaoHILLLoops
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace WentaoHILLControl

def Run (C : Machines) (n : ℕ) (c d : Config C) : Prop :=
  ∃ k ≤ n, (flip bind (checker C).step)^[k] (some c) = some d

lemma Run.refl (C : Machines) (c : Config C) : Run C 0 c c := ⟨0, le_rfl, rfl⟩

lemma Run.of_eq (C : Machines) (n : ℕ) (c d : Config C)
    (h : (flip bind (checker C).step)^[n] (some c) = some d) : Run C n c d :=
  ⟨n, le_rfl, h⟩

lemma Run.trans {C : Machines} {m n : ℕ} {c d e : Config C}
    (h : Run C m c d) (h' : Run C n d e) : Run C (m+n) c e := by
  obtain ⟨r, hr, hs⟩ := h
  obtain ⟨s, ht, hu⟩ := h'
  refine ⟨r+s, Nat.add_le_add hr ht, ?_⟩
  rw [Nat.add_comm r s, Function.iterate_add_apply, hs, hu]

lemma Run.mono {C : Machines} {m n : ℕ} {c d : Config C}
    (h : Run C m c d) (hn : m ≤ n) : Run C n c d := by
  obtain ⟨r, hr, hs⟩ := h
  exact ⟨r, hr.trans hn, hs⟩

lemma Run.step {C : Machines} {c d : Config C}
    (h : (checker C).step c = some d) : Run C 1 c d := ⟨1, le_rfl, h⟩

@[simp] lemma flag_temp0 (C : Machines) (v : Memory C) (b : Option Bool) :
    (temp0 v b).2.2.2 = v.2.2.2 := rfl
@[simp] lemma flag_temp1 (C : Machines) (v : Memory C) (b : Option Bool) :
    (temp1 v b).2.2.2 = v.2.2.2 := rfl
@[simp] lemma states_temp0 (C : Machines) (v : Memory C) (b : Option Bool) :
    (temp0 v b).1 = v.1 := rfl
@[simp] lemma states_temp1 (C : Machines) (v : Memory C) (b : Option Bool) :
    (temp1 v b).1 = v.1 := rfl

lemma equality_loop (C : Machines) (v : Memory C) (S : Store C) (xs ys : Bits) :
    ∃ v' S', Run C (xs.length + ys.length + 1)
      (config C (phaseLabel .equality) v
        (Function.update (Function.update S (ckey 7) xs) (ckey 6) ys))
      (config C (cleanLabel 0) v' S') ∧
      v'.1 = v.1 ∧ v'.2.2.2 = (if xs = ys then true else v.2.2.2) := by
  classical
  have hk : (ckey 7 : Key C) ≠ ckey 6 := by simp [ckey]
  induction xs generalizing v ys with
  | nil =>
    cases ys with
    | nil =>
      refine ⟨acceptMemory (temp1 (temp0 v none) none),
        Function.update (Function.update S (ckey 7) []) (ckey 6) [], ?_, rfl, rfl⟩
      apply Run.step
      change some (TM2.stepAux (program C (phaseLabel .equality)) v _) = _
      simp [program, phaseLabel, cleanLabel, controller, pop0, pop1, TM2.stepAux, clean, config, temp0, temp1,
        acceptMemory, hk, hk.symm, Function.update_comm hk]
    | cons y ys =>
      refine ⟨temp1 (temp0 v none) (some y),
        Function.update (Function.update S (ckey 7) []) (ckey 6) ys, ?_, rfl, ?_⟩
      · apply Run.mono (Run.step ?_) (by omega)
        change some (TM2.stepAux (program C (phaseLabel .equality)) v _) = _
        simp [program, phaseLabel, cleanLabel, controller, pop0, pop1, TM2.stepAux, clean, config, temp0, temp1,
          hk, hk.symm, Function.update_comm hk]
      · simp [temp1, temp0]
  | cons x xs ih =>
    cases ys with
    | nil =>
      refine ⟨temp1 (temp0 v (some x)) none,
        Function.update (Function.update S (ckey 7) xs) (ckey 6) [], ?_, rfl, ?_⟩
      · apply Run.mono (Run.step ?_) (by simp only [List.length_nil, List.length_cons]; omega)
        change some (TM2.stepAux (program C (phaseLabel .equality)) v _) = _
        simp [program, phaseLabel, cleanLabel, controller, pop0, pop1, TM2.stepAux, clean, config, temp0, temp1,
          hk, hk.symm, Function.update_comm hk]
      · simp [temp1, temp0]
    | cons y ys =>
      by_cases hxy : x = y
      · subst y
        obtain ⟨v', S', hr, hv, hf⟩ := ih (temp1 (temp0 v (some x)) (some x)) ys
        refine ⟨v', S', ?_, hv, ?_⟩
        · apply Run.mono (Run.trans (Run.step ?_) hr) (by simp only [List.length_nil, List.length_cons]; omega)
          change some (TM2.stepAux (program C (phaseLabel .equality)) v _) = _
          simp [program, phaseLabel, cleanLabel, controller, pop0, pop1, TM2.stepAux, go, config, temp0, temp1,
            hk, hk.symm, Function.update_comm hk]
        · simpa [temp1, temp0] using hf
      · refine ⟨temp1 (temp0 v (some x)) (some y),
          Function.update (Function.update S (ckey 7) xs) (ckey 6) ys, ?_, rfl, ?_⟩
        · apply Run.mono (Run.step ?_) (by simp only [List.length_nil, List.length_cons]; omega)
          change some (TM2.stepAux (program C (phaseLabel .equality)) v _) = _
          simp [program, phaseLabel, cleanLabel, controller, pop0, pop1, TM2.stepAux, clean, config, temp0, temp1,
            hk, hk.symm, Function.update_comm hk, hxy, Bool.cond_eq_ite]
        · simp [temp1, temp0, hxy]

lemma lengths_loop (C : Machines) (v : Memory C) (S : Store C)
    (xs : List ((machine C 1).Γ (machine C 1).k₁))
    (ys : List ((machine C 0).Γ (machine C 0).k₁)) (zs : Bits) :
    ∃ v' S', Run C (xs.length + ys.length + 1)
      (config C (phaseLabel .lengths) v
        (Function.update (Function.update (Function.update S (okey C 1) xs)
          (okey C 0) ys) (ckey 5) zs))
      (config C (if xs.length = ys.length then phaseLabel .secL else cleanLabel 0) v' S') ∧
      v'.1 = v.1 ∧ v'.2.2.2 = v.2.2.2 ∧
      (xs.length = ys.length → S' =
        Function.update (Function.update (Function.update S (okey C 1) []) (okey C 0) [])
          (ckey 5) ((ys.map (C 0).impl.outputAlphabet).reverse ++ zs)) := by
  classical
  have h₀ : okey C 1 ≠ okey C 0 := by simp [okey]
  have h₁ : okey C 1 ≠ ckey 5 := by simp [okey, ckey]
  have h₂ : okey C 0 ≠ ckey 5 := by simp [okey, ckey]
  induction xs generalizing v ys zs with
  | nil =>
    cases ys with
    | nil =>
      refine ⟨temp1 (temp0 v none) none,
        Function.update (Function.update (Function.update S (okey C 1) []) (okey C 0) [])
          (ckey 5) zs, ?_, rfl, rfl, ?_⟩
      · apply Run.step
        change some (TM2.stepAux (program C (phaseLabel .lengths)) v _) = _
        simp [program, phaseLabel, cleanLabel, controller, pop0, pop1, TM2.stepAux,
          config, go, temp0, temp1, h₀.symm, h₁.symm, h₂.symm,
          Function.update_comm h₀, Function.update_comm h₁, Function.update_comm h₂]
      · intro _; simp
    | cons y ys =>
      refine ⟨temp1 (temp0 v none) (some ((C 0).impl.outputAlphabet y)),
        Function.update (Function.update (Function.update S (okey C 1) []) (okey C 0) ys)
          (ckey 5) zs, ?_, rfl, rfl, ?_⟩
      · apply Run.mono (Run.step ?_) (by simp only [List.length_nil, List.length_cons]; omega)
        change some (TM2.stepAux (program C (phaseLabel .lengths)) v _) = _
        simp [program, phaseLabel, cleanLabel, controller, pop0, pop1, TM2.stepAux,
          config, clean, temp0, temp1, h₀.symm, h₁.symm, h₂.symm,
          Function.update_comm h₀, Function.update_comm h₁, Function.update_comm h₂]
      · simp
  | cons x xs ih =>
    cases ys with
    | nil =>
      refine ⟨temp1 (temp0 v (some ((C 1).impl.outputAlphabet x))) none,
        Function.update (Function.update (Function.update S (okey C 1) xs) (okey C 0) [])
          (ckey 5) zs, ?_, rfl, rfl, ?_⟩
      · apply Run.mono (Run.step ?_) (by simp only [List.length_nil, List.length_cons]; omega)
        change some (TM2.stepAux (program C (phaseLabel .lengths)) v _) = _
        simp [program, phaseLabel, cleanLabel, controller, pop0, pop1, TM2.stepAux,
          config, clean, temp0, temp1, h₀.symm, h₁.symm, h₂.symm,
          Function.update_comm h₀, Function.update_comm h₁, Function.update_comm h₂]
      · simp
    | cons y ys =>
      obtain ⟨v', S', hr, hv, hf, hS⟩ := ih
        (temp1 (temp0 v (some ((C 1).impl.outputAlphabet x)))
          (some ((C 0).impl.outputAlphabet y))) ys (((C 0).impl.outputAlphabet y) :: zs)
      refine ⟨v', S', ?_, hv, hf, ?_⟩
      · apply Run.mono (Run.trans (Run.step ?_) (by simpa only [List.length_cons,
          Nat.add_left_inj] using hr)) (by simp only [List.length_cons]; omega)
        change some (TM2.stepAux (program C (phaseLabel .lengths)) v _) = _
        simp [program, phaseLabel, cleanLabel, controller, pop0, pop1, TM2.stepAux,
          config, go, temp0, temp1, h₀.symm, h₁.symm, h₂.symm,
          Function.update_comm h₀, Function.update_comm h₁, Function.update_comm h₂]
      · intro hlen
        have he : xs.length = ys.length := by simpa using hlen
        simpa [List.reverse_cons, List.append_assoc] using hS he

lemma takeY_loop (C : Machines) (v : Memory C) (S : Store C)
    (xs : List ((machine C 2).Γ (machine C 2).k₁)) (ys zs : Bits) :
    ∃ v' xs' ys', Run C (xs.length + ys.length + 1)
      (config C (phaseLabel .takeY) v
        (Function.update (Function.update (Function.update S (okey C 2) xs)
          (ckey 3) ys) (ckey 6) zs))
      (config C (phaseLabel .sendE) v'
        (Function.update (Function.update (Function.update S (okey C 2) xs') (ckey 3) ys')
          (ckey 6) ((ys.take xs.length).reverse ++ zs))) ∧
      v'.1 = v.1 ∧ v'.2.2.2 = v.2.2.2 := by
  classical
  have h₀ : okey C 2 ≠ ckey 3 := by simp [okey, ckey]
  have h₁ : okey C 2 ≠ ckey 6 := by simp [okey, ckey]
  have h₂ : (ckey 3 : Key C) ≠ ckey 6 := by simp [ckey]
  induction xs generalizing v ys zs with
  | nil =>
    refine ⟨temp0 v none, [], ys, ?_, rfl, rfl⟩
    apply Run.mono (Run.step ?_) (by simp only [List.length_nil]; omega)
    change some (TM2.stepAux (program C (phaseLabel .takeY)) v _) = _
    simp [program, phaseLabel, controller, pop0, TM2.stepAux, config, go, temp0,
      h₀.symm, h₁.symm, h₂.symm, Function.update_comm h₀,
      Function.update_comm h₁, Function.update_comm h₂]
  | cons x xs ih =>
    cases ys with
    | nil =>
      refine ⟨temp1 (temp0 v (some ((C 2).impl.outputAlphabet x))) none, xs, [], ?_, rfl, rfl⟩
      apply Run.mono (Run.step ?_) (by simp only [List.length_nil, List.length_cons]; omega)
      change some (TM2.stepAux (program C (phaseLabel .takeY)) v _) = _
      simp [program, phaseLabel, controller, pop0, pop1, TM2.stepAux, config, go, temp0,
        temp1, h₀.symm, h₁.symm, h₂.symm, Function.update_comm h₀,
        Function.update_comm h₁, Function.update_comm h₂]
    | cons y ys =>
      obtain ⟨v', xs', ys', hr, hv, hf⟩ := ih
        (temp1 (temp0 v (some ((C 2).impl.outputAlphabet x))) (some y)) ys (y :: zs)
      refine ⟨v', xs', ys', ?_, hv, hf⟩
      have he : (ys.take xs.length).reverse ++ y :: zs =
          ((y :: ys).take (x :: xs).length).reverse ++ zs := by
        simp [List.reverse_cons, List.append_assoc]
      rw [← he]
      apply Run.mono (Run.trans (Run.step ?_) hr) (by simp only [List.length_cons]; omega)
      change some (TM2.stepAux (program C (phaseLabel .takeY)) v _) = _
      simp [program, phaseLabel, controller, pop0, pop1, TM2.stepAux, config, go, temp0,
        temp1, h₀.symm, h₁.symm, h₂.symm, Function.update_comm h₀,
        Function.update_comm h₁, Function.update_comm h₂]

end WentaoHILLControl


noncomputable section
open Turing HILL.PRG HILL.PRG.CheckerTM2 WentaoHILLMachine WentaoHILLLoops
  WentaoHILLControl WentaoHILLResource
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace WentaoHILLCleanup

abbrev size (C : Machines) (S : Store C) := totalSize S

def Cleared (C : Machines) (i : ℕ) (S : Store C) : Prop :=
  ∀ k, ((Fintype.equivFin (Key C)) k).val < i → S k = []

lemma cleared_zero (C : Machines) (S : Store C) : Cleared C 0 S := by
  intro k h; omega

lemma cleared_all (C : Machines) (S : Store C) (h : Cleared C (Fintype.card (Key C)) S) :
    S = fun _ => [] := by
  funext k
  exact h k ((Fintype.equivFin (Key C)) k).isLt

lemma cleared_succ (C : Machines) (i : ℕ) (hi : i < Fintype.card (Key C))
    (S : Store C) (h : Cleared C i S) :
    Cleared C (i+1) (Function.update S ((Fintype.equivFin (Key C)).symm ⟨i, hi⟩) []) := by
  classical
  intro k hk
  by_cases he : k = (Fintype.equivFin (Key C)).symm ⟨i, hi⟩
  · subst k; simp
  · rw [Function.update_of_ne he]
    apply h
    have hne : ((Fintype.equivFin (Key C)) k).val ≠ i := by
      intro hf
      apply he
      apply (Fintype.equivFin (Key C)).injective
      simp only [Equiv.apply_symm_apply]
      exact Fin.ext hf
    omega

lemma halt_config (C : Machines) (w : Bits) :
    haltList (checker C) w =
      (⟨none, initialMemory C, Function.update (fun _ => []) (ckey 8) w⟩ : Config C) := by
  change (⟨none, initialMemory C, (haltList (checker C) w).stk⟩ : Config C) = _
  rw [haltList_stk]
  rfl

lemma cleanup_run (C : Machines) (i : Fin (Fintype.card (Key C) + 1))
    (v : Memory C) (S : Store C) (h : Cleared C i.val S) :
    Run C (size C S + (Fintype.card (Key C) - i.val) + 1)
      (config C (cleanLabel i) v S)
      (haltList (checker C) (if v.2.2.2 then [true] else [])) := by
  classical
  have aux : ∀ r : ℕ, ∀ (i : Fin (Fintype.card (Key C) + 1)),
      Fintype.card (Key C) - i.val = r → ∀ (v : Memory C) (S : Store C),
      Cleared C i.val S →
      Run C (size C S + r + 1) (config C (cleanLabel i) v S)
        (haltList (checker C) (if v.2.2.2 then [true] else [])) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro i hi v S h
      by_cases hit : i.val < Fintype.card (Key C)
      · let k : Key C := (Fintype.equivFin (Key C)).symm ⟨i.val, hit⟩
        let i' : Fin (Fintype.card (Key C) + 1) := ⟨i.val+1, by omega⟩
        have hp : program C (cleanLabel i) = pop0 C k (fun _ => true)
            (.branch (fun v => v.2.1.isSome) (.goto (fun _ => cleanLabel i))
              (.goto (fun _ => cleanLabel i'))) := by
          change cleanup C i = _
          rw [cleanup, dif_pos hit]
        have hd := drain_loop C k (cleanLabel i) (.goto (fun _ => cleanLabel i')) hp v S (S k)
        simp only [Function.update_eq_self] at hd
        change (flip bind (checker C).step)^[List.length (S k) + 1]
          (some (config C (cleanLabel i) v S)) =
          some (config C (cleanLabel i') (temp0 v none) (Function.update S k [])) at hd
        have he := cleared_succ C i.val hit S h
        have hnext := ih (Fintype.card (Key C) - i'.val) (by dsimp [i']; omega)
          i' rfl (temp0 v none) (Function.update S k []) he
        have hc := (Run.of_eq C _ _ _ hd).trans hnext
        have hs := totalSize_update S k []
        simp only [List.length_nil] at hs
        simpa only [flag_temp0] using hc.mono (by dsimp [size, i']; omega)
      · have heq : i.val = Fintype.card (Key C) := by omega
        have hr : r = 0 := by omega
        have hemp : S = fun _ => [] := cleared_all C S (by simpa [heq] using h)
        subst S
        have hs : (checker C).step (config C (cleanLabel i) v (fun _ => [])) =
            some (haltList (checker C) (if v.2.2.2 then [true] else [])) := by
          change some (TM2.stepAux (program C (cleanLabel i)) v _) = _
          simp only [program, cleanLabel, cleanup, hit, ↓reduceDIte, TM2.stepAux]
          cases hf : v.2.2.2 <;>
            simp [hf, halt_config, Function.update_eq_self]
        exact (Run.step hs).mono (by omega)
  exact aux _ i rfl v S h

end WentaoHILLCleanup


noncomputable section
open Turing HILL.PRG HILL.PRG.CheckerTM2 WentaoHILLMachine WentaoHILLControl
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace WentaoHILLCalls

def inputStore (C : Machines) (j : Fin 4) (w : Bits) :
    ∀ k, List ((machine C j).Γ k) :=
  (initList (machine C j) (w.map (C j).impl.inputAlphabet.symm)).stk

def outputStore (C : Machines) (j : Fin 4) (w : Bits) :
    ∀ k, List ((machine C j).Γ k) :=
  (haltList (machine C j) (w.map (C j).impl.outputAlphabet.symm)).stk

lemma updateState_same (C : Machines) (v : Memory C) (j : Fin 4)
    (h : v.1 j = (machine C j).initialState) :
    updateState C v j (machine C j).initialState = v := by
  rw [← h]
  simp [updateState, Function.update_eq_self]

lemma computer_call (C : Machines) (j : Fin 4) (w : Bits)
    (v : Memory C) (Q : Locals C) (B : Controls)
    (hmem : v.1 j = (machine C j).initialState)
    (hstk : Q j = inputStore C j w) :
    Run C ((C j).impl.time.eval w.length)
      ⟨some (.inl ⟨j, (machine C j).main⟩), v, pack C Q B⟩
      ⟨some (phaseLabel (ret j)), v,
        pack C (Function.update Q j (outputStore C j ((C j).fn w))) B⟩ := by
  have h := (C j).impl.outputsFun w
  have hr := run_embed C j h.steps _ _ v Q B h.evals_in_steps
  have hQ : Function.update Q j (inputStore C j w) = Q := by
    rw [← hstk, Function.update_eq_self]
  refine ⟨h.steps, h.steps_le_m, ?_⟩
  change (flip bind (checker C).step)^[h.steps]
    (some ⟨some (.inl ⟨j, (machine C j).main⟩),
      updateState C v j (machine C j).initialState,
      pack C (Function.update Q j (inputStore C j w)) B⟩) =
    some ⟨some (phaseLabel (ret j)), updateState C v j (machine C j).initialState,
      pack C (Function.update Q j (outputStore C j ((C j).fn w))) B⟩ at hr
  simpa only [updateState_same C v j hmem, hQ] using hr

end WentaoHILLCalls


noncomputable section
open Turing HILL.PRG HILL.PRG.CheckerTM2 WentaoHILLResource
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace WentaoHILLBound

def callBound (C : Machines) : Polynomial ℕ :=
  (envelope C).comp ((envelope C).comp ((envelope C).comp (envelope C)))

lemma envelope_increases (C : Machines) (n : ℕ) : n ≤ (envelope C).eval n := by
  have := envelope_ge C n
  omega

lemma all_calls_bounded (C : Machines) (m n : ℕ) (p : Bits)
    (hn : n ≤ m) (hp : p.length ≤ m) :
    let b := (callBound C).eval m
    let u := (C 0).fn (enc n p)
    (C 0).impl.time.eval (enc n p).length ≤ b ∧
    u.length ≤ b ∧
    (C 1).impl.time.eval n ≤ b ∧ ((C 1).fn (List.replicate n true)).length ≤ b ∧
    (C 2).impl.time.eval n ≤ b ∧ ((C 2).fn (List.replicate n true)).length ≤ b ∧
    (C 3).impl.time.eval (encAdvice n 0 u).length ≤ b ∧
    ((C 3).fn (encAdvice n 0 u)).length ≤ b ∧ m ≤ b := by
  let P := (envelope C).eval
  have hge : ∀ k, 2*k+2 ≤ P k := envelope_ge C
  have hinc : ∀ k, k ≤ P k := envelope_increases C
  have h01 := hinc m
  have h12 := hinc (P m)
  have h23 := hinc (P (P m))
  have h34 := hinc (P (P (P m)))
  have hi : (enc n p).length ≤ P m := by
    simp only [enc, List.length_append, List.length_replicate, List.length_cons]
    have := hge m
    omega
  have hit : (C 0).impl.time.eval (enc n p).length ≤ P (P m) := (time_le_envelope C 0 (enc n p).length).trans (envelope_mono C hi)
  have hil : ((C 0).fn (enc n p)).length ≤ P (P m) := (length_le_envelope C 0 (enc n p)).trans (envelope_mono C hi)
  have ht := (time_le_envelope C 1 n).trans (envelope_mono C hn)
  have hl := (time_le_envelope C 2 n).trans (envelope_mono C hn)
  have hto : ((C 1).fn (List.replicate n true)).length ≤ P m := by
    have h := length_le_envelope C 1 (List.replicate n true)
    simp only [List.length_replicate] at h
    exact h.trans (envelope_mono C hn)
  have hlo : ((C 2).fn (List.replicate n true)).length ≤ P m := by
    have h := length_le_envelope C 2 (List.replicate n true)
    simp only [List.length_replicate] at h
    exact h.trans (envelope_mono C hn)
  have he : (encAdvice n 0 ((C 0).fn (enc n p))).length ≤ P (P (P m)) := by
    have he_len : (encAdvice n 0 ((C 0).fn (enc n p))).length = n + 2 + ((C 0).fn (enc n p)).length := by simp [encAdvice, enc]; omega
    rw [he_len]
    have := hge (P (P m))
    omega
  have het := (time_le_envelope C 3 (encAdvice n 0 ((C 0).fn (enc n p))).length).trans
    (envelope_mono C he)
  have hel := (length_le_envelope C 3 (encAdvice n 0 ((C 0).fn (enc n p)))).trans
    (envelope_mono C he)
  simp only [callBound, Polynomial.eval_comp]
  change _ ≤ P (P (P (P m))) ∧ _
  exact ⟨hit.trans (h23.trans h34), hil.trans (h23.trans h34),
    ht.trans (h12.trans (h23.trans h34)), hto.trans (h12.trans (h23.trans h34)),
    hl.trans (h12.trans (h23.trans h34)), hlo.trans (h12.trans (h23.trans h34)),
    het, hel, h01.trans (h12.trans (h23.trans h34))⟩

end WentaoHILLBound


noncomputable section
open Turing HILL.PRG HILL.PRG.CheckerTM2 WentaoHILLMachine WentaoHILLLoops
  WentaoHILLControl WentaoHILLCalls WentaoHILLCleanup WentaoHILLResource WentaoHILLBound
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace WentaoHILLTransitions

lemma move_cc (C : Machines) (src dst : Fin 9) (h : src ≠ dst)
    (p : Phase) (done : Statement C)
    (hprog : program C (phaseLabel p) = move C (ckey src) (ckey dst) id id p done)
    (v : Memory C) (Q : Locals C) (B : Controls) (xs ys : Bits) :
    Run C (xs.length+1)
      (config C (phaseLabel p) v
        (pack C Q (Function.update (Function.update B src xs) dst ys)))
      (TM2.stepAux done (temp0 v none)
        (pack C Q (Function.update (Function.update B src []) dst (xs.reverse ++ ys)))) := by
  have hk : (ckey src : Key C) ≠ ckey dst := by simpa only [ckey, ne_eq, Sum.inr.injEq] using h
  apply Run.of_eq
  simpa only [ckey, pack_update_control, Function.comp_id, id_eq, List.map_id_fun] using
    move_loop C (ckey src) (ckey dst) hk id id p done hprog v (pack C Q B) xs ys

lemma clone_ccc (C : Machines) (src dst₀ dst₁ : Fin 9)
    (h₀ : src ≠ dst₀) (h₁ : src ≠ dst₁) (h₂ : dst₀ ≠ dst₁)
    (p : Phase) (done : Statement C)
    (hprog : program C (phaseLabel p) = clone C (ckey src) (ckey dst₀) (ckey dst₁) id id id p done)
    (v : Memory C) (Q : Locals C) (B : Controls) (xs ys₀ ys₁ : Bits) :
    Run C (xs.length+1)
      (config C (phaseLabel p) v
        (pack C Q (Function.update (Function.update (Function.update B src xs) dst₀ ys₀) dst₁ ys₁)))
      (TM2.stepAux done (temp0 v none)
        (pack C Q (Function.update (Function.update (Function.update B src []) dst₀
          (xs.reverse ++ ys₀)) dst₁ (xs.reverse ++ ys₁)))) := by
  have hk₀ : (ckey src : Key C) ≠ ckey dst₀ := by simpa only [ckey, ne_eq, Sum.inr.injEq] using h₀
  have hk₁ : (ckey src : Key C) ≠ ckey dst₁ := by simpa only [ckey, ne_eq, Sum.inr.injEq] using h₁
  have hk₂ : (ckey dst₀ : Key C) ≠ ckey dst₁ := by simpa only [ckey, ne_eq, Sum.inr.injEq] using h₂
  apply Run.of_eq
  simpa only [ckey, pack_update_control, Function.comp_id, id_eq, List.map_id_fun] using
    clone_loop C (ckey src) (ckey dst₀) (ckey dst₁) hk₀ hk₁ hk₂ id id id p done hprog
      v (pack C Q B) xs ys₀ ys₁

lemma move_ci (C : Machines) (src : Fin 9) (j : Fin 4)
    (p : Phase) (done : Statement C)
    (hprog : program C (phaseLabel p) = move C (ckey src) (ikey C j) id
      (C j).impl.inputAlphabet.symm p done)
    (v : Memory C) (Q : Locals C) (B : Controls) (xs : Bits)
    (ys : List ((machine C j).Γ (machine C j).k₀)) :
    Run C (xs.length+1)
      (config C (phaseLabel p) v
        (pack C (Function.update Q j (Function.update (Q j) (machine C j).k₀ ys))
          (Function.update B src xs)))
      (TM2.stepAux done (temp0 v none)
        (pack C (Function.update Q j (Function.update (Q j) (machine C j).k₀
          ((xs.map (C j).impl.inputAlphabet.symm).reverse ++ ys))) (Function.update B src []))) := by
  have hk : ckey src ≠ ikey C j := by simp [ckey, ikey]
  apply Run.of_eq
  have h := move_loop C (ckey src) (ikey C j) hk id (C j).impl.inputAlphabet.symm p done hprog
    v (pack C Q B) xs ys
  simpa only [ckey, ikey, pack_update_component, pack_update_control, Function.comp_id, id_eq] using h

lemma clone_cic (C : Machines) (src dst : Fin 9) (h : src ≠ dst) (j : Fin 4)
    (p : Phase) (done : Statement C)
    (hprog : program C (phaseLabel p) = clone C (ckey src) (ikey C j) (ckey dst) id
      (C j).impl.inputAlphabet.symm id p done)
    (v : Memory C) (Q : Locals C) (B : Controls) (xs zs : Bits)
    (ys : List ((machine C j).Γ (machine C j).k₀)) :
    Run C (xs.length+1)
      (config C (phaseLabel p) v
        (pack C (Function.update Q j (Function.update (Q j) (machine C j).k₀ ys))
          (Function.update (Function.update B src xs) dst zs)))
      (TM2.stepAux done (temp0 v none)
        (pack C (Function.update Q j (Function.update (Q j) (machine C j).k₀
          ((xs.map (C j).impl.inputAlphabet.symm).reverse ++ ys)))
          (Function.update (Function.update B src []) dst (xs.reverse ++ zs)))) := by
  have hk₀ : ckey src ≠ ikey C j := by simp [ckey, ikey]
  have hk₁ : (ckey src : Key C) ≠ ckey dst := by simpa only [ckey, ne_eq, Sum.inr.injEq] using h
  have hk₂ : ikey C j ≠ ckey dst := by simp [ckey, ikey]
  apply Run.of_eq
  simpa only [ckey, ikey, pack_update_component, pack_update_control, Function.comp_id, id_eq,
    List.map_id_fun] using clone_loop C (ckey src) (ikey C j) (ckey dst) hk₀ hk₁ hk₂ id
      (C j).impl.inputAlphabet.symm id p done hprog v (pack C Q B) xs ys zs

lemma call_context (C : Machines) (j : Fin 4) (w : Bits)
    (v : Memory C) (Q : Locals C) (B : Controls)
    (hmem : v.1 j = (machine C j).initialState) :
    Run C ((C j).impl.time.eval w.length)
      ⟨some (.inl ⟨j, (machine C j).main⟩), v,
        pack C (Function.update Q j (inputStore C j w)) B⟩
      ⟨some (phaseLabel (ret j)), v,
        pack C (Function.update Q j (outputStore C j ((C j).fn w))) B⟩ := by
  simpa only [Function.update_idem] using computer_call C j w v
    (Function.update Q j (inputStore C j w)) B hmem (by simp)

end WentaoHILLTransitions


noncomputable section
open Turing HILL.PRG HILL.PRG.CheckerTM2 WentaoHILLMachine WentaoHILLLoops
  WentaoHILLControl WentaoHILLCalls WentaoHILLCleanup WentaoHILLResource WentaoHILLBound
  WentaoHILLTransitions
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace WentaoHILLPrepare

def controls (w s₁ s₂ p a i y e o : Bits) : Controls := ![w,s₁,s₂,p,a,i,y,e,o]
def emptyLocals (C : Machines) : Locals C := fun _ _ => []

@[simp] lemma inputStore_eq (C : Machines) (j : Fin 4) (w : Bits) :
    inputStore C j w = Function.update (fun _ => []) (machine C j).k₀
      (w.map (C j).impl.inputAlphabet.symm) := initList_stk _ _
@[simp] lemma outputStore_eq (C : Machines) (j : Fin 4) (w : Bits) :
    outputStore C j w = Function.update (fun _ => []) (machine C j).k₁
      (w.map (C j).impl.outputAlphabet.symm) := haltList_stk _ _

lemma prepare_I (C : Machines) (w : Bits) :
    let n := (w.takeWhile id).length
    let p := w.drop (n+2)
    Run C (3*n + 3*p.length + 5) (initList (checker C) w)
      (⟨some (.inl ⟨0, (machine C 0).main⟩), temp0 (initialMemory C) none,
        pack C (Function.update (emptyLocals C) 0 (inputStore C 0 (enc n p)))
          (controls [] [] (List.replicate n true) p [] [] [] [] [])⟩ : Config C) := by
  classical
  dsimp only
  let n := (w.takeWhile id).length
  let p := w.drop (n+2)
  change Run C (3*n + 3*p.length + 5) _ _
  let u := List.replicate n true
  let Q := emptyLocals C
  let v := initialMemory C
  let B₀ := controls w [] [] [] [] [] [] [] []
  let B₁ := controls p u [] [] [] [] [] [] []
  let B₂ := controls [] u [] p.reverse p.reverse [] [] [] []
  let B₃ := controls [] u [] [] p.reverse [] [] [] []
  let B₄ := controls [] u [] p [] [] [] [] []
  let B₅ := controls [] [] u p [] [] [] [] []
  have hparse : Run C (n+1) (initList (checker C) w)
      (config C (phaseLabel .clone) (temp0 v none) (pack C Q B₁)) := by
    apply Run.of_eq
    have h := parse_loop C v (pack C Q (controls [] [] [] [] [] [] [] [] [])) w []
    have hinit : initList (checker C) w = config C (phaseLabel .parse) v
        (Function.update (Function.update (pack C Q (controls [] [] [] [] [] [] [] [] []))
          (ckey 0) w) (ckey 1) []) := by
      change (⟨some (phaseLabel .parse), v, (initList (checker C) w).stk⟩ : Config C) = _
      congr 1
      rw [initList_stk]
      funext k
      rcases k with ⟨j,k⟩ | k
      · simp [checker, ckey, pack, Q, emptyLocals]
      · fin_cases k <;> simp [checker, ckey, pack, controls, Function.update]
    rw [hinit]
    convert h using 1
    congr 2
    simp only [ckey, pack_update_control]
    congr 1
    funext k
    fin_cases k <;> simp [B₁, controls, u, p, n]
  have hclone : Run C (p.length+1)
      (config C (phaseLabel .clone) (temp0 v none) (pack C Q B₁))
      (config C (phaseLabel .sendI) (temp0 v none) (pack C Q B₂)) := by
    have h := clone_ccc C 0 3 4 (by decide) (by decide) (by decide) .clone
      (go .sendI) rfl (temp0 v none) Q B₁ p [] []
    convert h using 1 <;>
      simp only [TM2.stepAux, go, config, temp0]
    all_goals congr 2; funext k; fin_cases k <;> simp [B₁, B₂, controls]
  have hsend : Run C (p.length+1)
      (config C (phaseLabel .sendI) (temp0 v none) (pack C Q B₂))
      (config C (phaseLabel .restorePayload) (temp0 v none)
        (pack C (Function.update Q 0 (inputStore C 0 p)) B₃)) := by
    have h := move_ci C 3 0 .sendI (go .restorePayload) rfl (temp0 v none) Q B₂ p.reverse []
    simp only [List.length_reverse] at h
    convert h using 1 <;>
      simp only [TM2.stepAux, go, config, temp0]
    · congr 2
      · simp [Q, emptyLocals] <;> rfl
      · funext k; fin_cases k <;> simp [B₂, controls]
    · congr 2
      · simp [Q, emptyLocals, List.map_reverse] <;> rfl
      · funext k; fin_cases k <;> simp [B₂, B₃, controls]
  have hrestore : Run C (p.length+1)
      (config C (phaseLabel .restorePayload) (temp0 v none)
        (pack C (Function.update Q 0 (inputStore C 0 p)) B₃))
      (config C (phaseLabel .secI) (temp0 v none)
        (pack C (Function.update Q 0 (inputStore C 0 (false :: p))) B₄)) := by
    have h := move_cc C 4 3 (by decide) .restorePayload
      (.push (ikey C 0) (fun _ => (C 0).impl.inputAlphabet.symm false) (go .secI)) rfl
      (temp0 v none) (Function.update Q 0 (inputStore C 0 p)) B₃ p.reverse []
    simp only [List.length_reverse] at h
    convert h using 1 <;>
      simp only [TM2.stepAux, go, config, temp0, ikey, pack_update_component,
        pack_component, Function.update_self, Function.update_idem]
    · congr 2; funext k; fin_cases k <;> simp [B₃, controls]
    · congr 2
      · simp [Q, emptyLocals] <;> rfl
      · funext k; fin_cases k <;> simp [B₃, B₄, controls]
  have hsec : Run C (n+1)
      (config C (phaseLabel .secI) (temp0 v none)
        (pack C (Function.update Q 0 (inputStore C 0 (false :: p))) B₄))
      (⟨some (.inl ⟨0, (machine C 0).main⟩), temp0 v none,
        pack C (Function.update Q 0 (inputStore C 0 (enc n p))) B₅⟩ : Config C) := by
    have h := clone_cic C 1 2 (by decide) 0 .secI (call C 0) rfl (temp0 v none) Q B₄ u []
      ((false :: p).map (C 0).impl.inputAlphabet.symm)
    simp only [u, List.length_replicate] at h
    convert h using 1 <;>
      simp only [TM2.stepAux, call, config, temp0]
    · congr 2
      · simp [Q, emptyLocals] <;> rfl
      · funext k; fin_cases k <;> simp [B₄, controls, u]
    · congr 2
      · simp [Q, emptyLocals, u, enc, List.reverse_replicate, List.map_reverse,
          List.map_append] <;> rfl
      · funext k; fin_cases k <;> simp [B₄, B₅, controls, u]
  exact (hparse.trans (hclone.trans (hsend.trans (hrestore.trans hsec)))).mono (by omega)

lemma unary_prepare (C : Machines) (src dst : Fin 9) (h : src ≠ dst) (j : Fin 4)
    (p : Phase) (n : ℕ) (v : Memory C) (Q : Locals C) (B : Controls)
    (hQ : Q j = fun _ => []) (hsrc : B src = List.replicate n true) (hdst : B dst = [])
    (hprog : program C (phaseLabel p) = clone C (ckey src) (ikey C j) (ckey dst) id
      (C j).impl.inputAlphabet.symm id p (call C j)) :
    Run C (n+1) (config C (phaseLabel p) v (pack C Q B))
      (⟨some (.inl ⟨j, (machine C j).main⟩), temp0 v none,
        pack C (Function.update Q j (inputStore C j (List.replicate n true)))
          (Function.update (Function.update B src []) dst (List.replicate n true))⟩ : Config C) := by
  have hr := clone_cic C src dst h j p (call C j) hprog v Q B
    (List.replicate n true) [] []
  simp only [List.length_replicate] at hr
  have hq : Function.update Q j (Function.update (Q j) (machine C j).k₀ []) = Q := by
    rw [hQ, Function.update_eq_self, ← hQ, Function.update_eq_self]
  have hb : Function.update (Function.update B src (List.replicate n true)) dst [] = B := by
    rw [← hsrc, Function.update_eq_self, ← hdst, Function.update_eq_self]
  rw [hq, hb] at hr
  simpa [TM2.stepAux, call, hQ, List.map_reverse] using hr

lemma prepare_T (C : Machines) (n : ℕ) (p i : Bits) (v : Memory C)
    (Q : Locals C) (hQ : Q 1 = fun _ => []) :
    Run C (n+1)
      (config C (phaseLabel .secT) v
        (pack C Q (controls [] [] (List.replicate n true) p [] [] [] [] [])))
      (⟨some (.inl ⟨1, (machine C 1).main⟩), temp0 v none,
        pack C (Function.update Q 1 (inputStore C 1 (List.replicate n true)))
          (controls [] (List.replicate n true) [] p [] [] [] [] [])⟩ : Config C) := by
  have hr := unary_prepare C 2 1 (by decide) 1 .secT n v Q
    (controls [] [] (List.replicate n true) p [] [] [] [] []) hQ (by simp [controls])
    (by simp [controls]) rfl
  convert hr using 1
  congr 2
  funext k
  fin_cases k <;> simp [controls]

lemma prepare_L (C : Machines) (n : ℕ) (p i : Bits) (v : Memory C)
    (Q : Locals C) (hQ : Q 2 = fun _ => []) :
    Run C (n+1)
      (config C (phaseLabel .secL) v
        (pack C Q (controls [] (List.replicate n true) [] p [] i [] [] [])))
      (⟨some (.inl ⟨2, (machine C 2).main⟩), temp0 v none,
        pack C (Function.update Q 2 (inputStore C 2 (List.replicate n true)))
          (controls [] [] (List.replicate n true) p [] i [] [] [])⟩ : Config C) := by
  have hr := unary_prepare C 1 2 (by decide) 2 .secL n v Q
    (controls [] (List.replicate n true) [] p [] i [] [] []) hQ (by simp [controls])
    (by simp [controls]) rfl
  convert hr using 1
  congr 2
  funext k
  fin_cases k <;> simp [controls]

end WentaoHILLPrepare


noncomputable section
open Turing HILL.PRG HILL.PRG.CheckerTM2 WentaoHILLMachine WentaoHILLLoops
  WentaoHILLControl WentaoHILLCalls WentaoHILLCleanup WentaoHILLResource WentaoHILLBound
  WentaoHILLTransitions WentaoHILLPrepare
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace WentaoHILLStages

lemma check_lengths (C : Machines) (n : ℕ) (p i t : Bits) (v : Memory C) :
    ∃ v' S', Run C (t.length + i.length + 1)
      (config C (phaseLabel .lengths) v
        (pack C (Function.update (Function.update (emptyLocals C) 0 (outputStore C 0 i))
          1 (outputStore C 1 t)) (controls [] (List.replicate n true) [] p [] [] [] [] [])))
      (config C (if t.length = i.length then phaseLabel .secL else cleanLabel 0) v' S') ∧
      v'.1 = v.1 ∧ v'.2.2.2 = v.2.2.2 ∧
      (t.length = i.length → S' = pack C (emptyLocals C)
        (controls [] (List.replicate n true) [] p [] i.reverse [] [] [])) := by
  classical
  let B := controls [] (List.replicate n true) [] p [] [] [] [] []
  obtain ⟨v', S', hr, hv, hf, hs⟩ := lengths_loop C v (pack C (emptyLocals C) B)
    (t.map (C 1).impl.outputAlphabet.symm) (i.map (C 0).impl.outputAlphabet.symm) []
  simp only [List.length_map] at hr hs
  refine ⟨v', S', ?_, hv, hf, ?_⟩
  · convert hr using 1
    congr 2
    simp only [okey, ckey, pack_update_component, pack_update_control]
    congr 1
    · rw [Function.update_comm (by decide : (1 : Fin 4) ≠ 0)]
      simp [emptyLocals] <;> rfl
    · funext k; fin_cases k <;> simp [B, controls]
  · intro hlen
    rw [hs hlen]
    simp only [okey, ckey, pack_update_component, pack_update_control,
      List.map_map, Equiv.apply_symm_apply, List.map_id_fun, id_eq, List.append_nil]
    congr 1
    · funext j k
      fin_cases j <;> simp [emptyLocals]
      · change Function.update (fun x : (machine C 0).K =>
          ([] : List ((machine C 0).Γ x))) (machine C 0).k₁ [] k = []
        simp only [Function.update_eq_self]
      · change Function.update (fun x : (machine C 1).K =>
          ([] : List ((machine C 1).Γ x))) (machine C 1).k₁ [] k = []
        simp only [Function.update_eq_self]
    · funext k; fin_cases k <;> simp [B, controls]

lemma take_target (C : Machines) (n : ℕ) (p i l : Bits) (v : Memory C) :
    ∃ v' Q' p', Run C (l.length + p.length + 1)
      (config C (phaseLabel .takeY) v
        (pack C (Function.update (emptyLocals C) 2 (outputStore C 2 l))
          (controls [] [] (List.replicate n true) p [] i.reverse [] [] [])))
      (config C (phaseLabel .sendE) v'
        (pack C Q' (controls [] [] (List.replicate n true) p' [] i.reverse
          ((p.take l.length).reverse) [] []))) ∧
      v'.1 = v.1 ∧ v'.2.2.2 = v.2.2.2 ∧ Q' 3 = (fun _ => []) := by
  classical
  let B := controls [] [] (List.replicate n true) [] [] i.reverse [] [] []
  obtain ⟨v', xs', ys', hr, hv, hf⟩ := takeY_loop C v (pack C (emptyLocals C) B)
    (l.map (C 2).impl.outputAlphabet.symm) p []
  simp only [List.length_map, List.append_nil] at hr
  refine ⟨v', Function.update (emptyLocals C) 2
      (Function.update (fun _ => []) (machine C 2).k₁ xs'), ys', ?_, hv, hf, ?_⟩
  · convert hr using 1 <;>
      simp only [okey, ckey, pack_update_component, pack_update_control]
    · congr 2
      · simp [emptyLocals] <;> rfl
      · funext k; fin_cases k <;> simp [B, controls]
    · congr 2
      funext k; fin_cases k <;> simp [B, controls]
  · simp only [Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2)]
    rfl

end WentaoHILLStages


noncomputable section
open Turing HILL.PRG HILL.PRG.CheckerTM2 WentaoHILLMachine WentaoHILLLoops
  WentaoHILLControl WentaoHILLCalls WentaoHILLCleanup WentaoHILLResource WentaoHILLBound
  WentaoHILLTransitions WentaoHILLPrepare WentaoHILLStages
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace WentaoHILLFinish

lemma prepare_E (C : Machines) (n : ℕ) (p i y : Bits) (v : Memory C)
    (Q : Locals C) (hQ : Q 3 = fun _ => []) :
    Run C (i.length + n + 2)
      (config C (phaseLabel .sendE) v
        (pack C Q (controls [] [] (List.replicate n true) p [] i.reverse y.reverse [] [])))
      (⟨some (.inl ⟨3, (machine C 3).main⟩), temp0 v none,
        pack C (Function.update Q 3 (inputStore C 3 (encAdvice n 0 i)))
          (controls [] [] [] p [] [] y.reverse [] [])⟩ : Config C) := by
  classical
  let B₀ := controls [] [] (List.replicate n true) p [] i.reverse y.reverse [] []
  let B₁ := controls [] [] (List.replicate n true) p [] [] y.reverse [] []
  let B₂ := controls [] [] [] p [] [] y.reverse [] []
  have hs : Run C (i.length + 1) (config C (phaseLabel .sendE) v (pack C Q B₀))
      (config C (phaseLabel .secE) (temp0 v none)
        (pack C (Function.update Q 3 (inputStore C 3 (false :: false :: i))) B₁)) := by
    have hr := move_ci C 5 3 .sendE
      (.push (ikey C 3) (fun _ => (C 3).impl.inputAlphabet.symm false)
        (.push (ikey C 3) (fun _ => (C 3).impl.inputAlphabet.symm false) (go .secE)))
      rfl v Q B₀ i.reverse []
    simp only [List.length_reverse] at hr
    convert hr using 1 <;>
      simp only [TM2.stepAux, go, config, ikey, pack_update_component,
        pack_component, Function.update_self, Function.update_idem]
    · congr 2
      · rw [hQ, Function.update_eq_self, ← hQ, Function.update_eq_self]
      · funext k; fin_cases k <;> simp [B₀, controls]
    · congr 2
      · simp [hQ, List.map_reverse]
      · funext k; fin_cases k <;> simp [B₀, B₁, controls]
  have ht : Run C (n+1)
      (config C (phaseLabel .secE) (temp0 v none)
        (pack C (Function.update Q 3 (inputStore C 3 (false :: false :: i))) B₁))
      (⟨some (.inl ⟨3, (machine C 3).main⟩), temp0 v none,
        pack C (Function.update Q 3 (inputStore C 3 (encAdvice n 0 i))) B₂⟩ : Config C) := by
    have hr := move_ci C 2 3 .secE (call C 3) rfl (temp0 v none) Q B₁
      (List.replicate n true) ((false :: false :: i).map (C 3).impl.inputAlphabet.symm)
    simp only [List.length_replicate] at hr
    convert hr using 1 <;> simp only [TM2.stepAux, call, config, temp0]
    · congr 2
      · simp [hQ]
      · funext k; fin_cases k <;> simp [B₁, controls]
    · congr 2
      · simp [hQ, encAdvice, enc, List.map_append, List.map_reverse]
      · funext k; fin_cases k <;> simp [B₁, B₂, controls]
  exact (hs.trans ht).mono (by omega)

lemma finish_E (C : Machines) (p y e : Bits) (v : Memory C)
    (Q : Locals C) (hQ : Q 3 = fun _ => []) :
    ∃ v' S', Run C (2*e.length + y.length + 2)
      (config C (phaseLabel .reverseE) v
        (pack C (Function.update Q 3 (outputStore C 3 e))
          (controls [] [] [] p [] [] y.reverse [] [])))
      (config C (cleanLabel 0) v' S') ∧
      v'.1 = v.1 ∧ v'.2.2.2 = (if e = y then true else v.2.2.2) := by
  classical
  let B₀ := controls [] [] [] p [] [] y.reverse [] []
  let B₁ := controls [] [] [] p [] [] y.reverse e.reverse []
  have hr : Run C (e.length+1)
      (config C (phaseLabel .reverseE) v
        (pack C (Function.update Q 3 (outputStore C 3 e)) B₀))
      (config C (phaseLabel .equality) (temp0 v none) (pack C Q B₁)) := by
    have hk : okey C 3 ≠ ckey 7 := by simp [okey, ckey]
    have h := move_loop C (okey C 3) (ckey 7) hk (C 3).impl.outputAlphabet id
      .reverseE (go .equality) rfl v (pack C Q B₀)
      (e.map (C 3).impl.outputAlphabet.symm) []
    simp only [List.length_map] at h
    have hB₀ : Function.update B₀ 7 [] = B₀ := by
      funext k; fin_cases k <;> simp [B₀, controls]
    have hB₁ : Function.update B₀ 7 e.reverse = B₁ := by
      funext k; fin_cases k <;> simp [B₀, B₁, controls]
    have hQclear : Function.update Q 3 (Function.update (Q 3) (machine C 3).k₁ []) = Q := by
      rw [hQ, Function.update_eq_self, ← hQ, Function.update_eq_self]
    have hQout : Function.update Q 3 (outputStore C 3 e) =
        Function.update Q 3 (Function.update (Q 3) (machine C 3).k₁
          (e.map (C 3).impl.outputAlphabet.symm)) := by rw [outputStore_eq, hQ]
    apply Run.of_eq
    simpa only [TM2.stepAux, go, config, okey, ckey,
      pack_update_component, pack_update_control, List.map_map, Function.comp_def,
      Equiv.apply_symm_apply, id_eq, List.map_id_fun, List.map_id_fun', List.map_id, List.append_nil,
      hB₀, hB₁, hQclear, hQout] using h
  obtain ⟨v', S', he, hv, hf⟩ := equality_loop C (temp0 v none) (pack C Q B₁) e.reverse y.reverse
  have hh : Function.update (Function.update (pack C Q B₁) (ckey 7) e.reverse) (ckey 6) y.reverse =
      pack C Q B₁ := by
    simp only [ckey, pack_update_control]
    congr 1
    funext k; fin_cases k <;> simp [B₁, controls]
  rw [hh] at he
  refine ⟨v', S', (hr.trans he).mono (by simp only [List.length_reverse]; omega), hv, ?_⟩
  simpa using hf

end WentaoHILLFinish


noncomputable section
open Turing HILL.PRG HILL.PRG.CheckerTM2 WentaoHILLMachine WentaoHILLLoops
  WentaoHILLControl WentaoHILLCalls WentaoHILLCleanup WentaoHILLResource WentaoHILLBound
  WentaoHILLTransitions WentaoHILLPrepare WentaoHILLStages WentaoHILLFinish
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace WentaoHILLRun

lemma run_to_cleanup (C : Machines) (w : Bits) :
    ∃ v S, Run C (100 * (callBound C).eval w.length) (initList (checker C) w)
      (config C (cleanLabel 0) v S) ∧
      (if v.2.2.2 then [true] else []) =
        inversionChecker (C 1).fn (C 2).fn (C 3).fn (C 0).fn w := by
  classical
  let m := w.length
  let n := (w.takeWhile id).length
  let p := w.drop (n+2)
  let u := List.replicate n true
  let i := (C 0).fn (enc n p)
  let t := (C 1).fn u
  let l := (C 2).fn u
  let y := p.take l.length
  let e := (C 3).fn (encAdvice n 0 i)
  let b := (callBound C).eval m
  let v := initialMemory C
  let Q := emptyLocals C
  let QI := Function.update Q 0 (outputStore C 0 i)
  let QIT := Function.update QI 1 (outputStore C 1 t)
  let BI := controls [] [] u p [] [] [] [] []
  let BT := controls [] u [] p [] [] [] [] []
  have hbpos : 2 ≤ b := by
    have hb := envelope_ge C ((envelope C).eval ((envelope C).eval ((envelope C).eval m)))
    dsimp [b, callBound]
    simp only [Polynomial.eval_comp]
    omega
  have hn : n ≤ m := (List.takeWhile_sublist (l := w) id).length_le
  have hp : p.length ≤ m := by simp [p, m]
  have hy : y.length ≤ p.length := by simp [y]
  obtain ⟨hIs, hi, hTs, ht, hLs, hl, hEs, he, hm⟩ := all_calls_bounded C m n p hn hp
  change _ ≤ b at hIs hTs hLs
  change (C 3).impl.time.eval (encAdvice n 0 i).length ≤ b at hEs
  change i.length ≤ b at hi
  change t.length ≤ b at ht
  change l.length ≤ b at hl
  change e.length ≤ b at he
  change m ≤ b at hm
  have hstart : Run C (3*n + 3*p.length + 5) (initList (checker C) w)
      (⟨some (.inl ⟨0, (machine C 0).main⟩), v,
        pack C (Function.update Q 0 (inputStore C 0 (enc n p))) BI⟩ : Config C) := by
    simpa only [v, n, p, Q, BI, u, initialMemory, temp0] using prepare_I C w
  have hI : Run C ((C 0).impl.time.eval (enc n p).length)
      (⟨some (.inl ⟨0, (machine C 0).main⟩), v,
        pack C (Function.update Q 0 (inputStore C 0 (enc n p))) BI⟩ : Config C)
      (config C (phaseLabel .secT) v (pack C QI BI)) := by
    simpa [ret, QI, config] using call_context C 0 (enc n p) v Q BI rfl
  have hprepT : Run C (n+1) (config C (phaseLabel .secT) v (pack C QI BI))
      (⟨some (.inl ⟨1, (machine C 1).main⟩), v,
        pack C (Function.update QI 1 (inputStore C 1 u)) BT⟩ : Config C) := by
    simpa only [v, QI, BI, BT, Q, u, initialMemory, temp0] using prepare_T C n p i v QI (by simp [QI, Q, emptyLocals] <;> rfl)
  have hT : Run C ((C 1).impl.time.eval n)
      (⟨some (.inl ⟨1, (machine C 1).main⟩), v,
        pack C (Function.update QI 1 (inputStore C 1 u)) BT⟩ : Config C)
      (config C (phaseLabel .lengths) v (pack C QIT BT)) := by
    simpa [ret, QIT, u, config] using call_context C 1 u v QI BT rfl
  obtain ⟨vL, SL, hlen, hvL, hfL, hsL⟩ := check_lengths C n p i t v
  change Run C (t.length+i.length+1) (config C (phaseLabel .lengths) v (pack C QIT BT)) _ at hlen
  have hpre := hstart.trans (hI.trans (hprepT.trans (hT.trans hlen)))
  by_cases hlenEq : t.length = i.length
  · simp only [if_pos hlenEq] at hpre
    rw [hsL hlenEq] at hpre
    let BL := controls [] [] u p [] i.reverse [] [] []
    let v₁ := temp0 vL none
    have hprepL := prepare_L C n p i.reverse vL Q (by rfl)
    have hL := call_context C 2 u v₁ Q BL (by change vL.1 2 = _; rw [hvL]; rfl)
    have hL' : Run C ((C 2).impl.time.eval n)
        (⟨some (.inl ⟨2, (machine C 2).main⟩), v₁,
          pack C (Function.update Q 2 (inputStore C 2 u)) BL⟩ : Config C)
        (config C (phaseLabel .takeY) v₁
          (pack C (Function.update Q 2 (outputStore C 2 l)) BL)) := by
      simpa [ret, config, u] using hL
    obtain ⟨vE, QE, pE, htarget, hvE, hfE, hQE⟩ := take_target C n p i l v₁
    let BE := controls [] [] [] pE [] [] y.reverse [] []
    let v₂ := temp0 vE none
    have hprepE := prepare_E C n pE i y vE QE hQE
    have hE := call_context C 3 (encAdvice n 0 i) v₂ QE BE (by
      change vE.1 3 = _
      rw [hvE]
      change vL.1 3 = _
      rw [hvL]
      rfl)
    have hE' : Run C ((C 3).impl.time.eval (encAdvice n 0 i).length)
        (⟨some (.inl ⟨3, (machine C 3).main⟩), v₂,
          pack C (Function.update QE 3 (inputStore C 3 (encAdvice n 0 i))) BE⟩ : Config C)
        (config C (phaseLabel .reverseE) v₂
          (pack C (Function.update QE 3 (outputStore C 3 e)) BE)) := by
      simpa [ret, config] using hE
    obtain ⟨v', S', hfinish, hv', hf'⟩ := finish_E C pE y e v₂ QE hQE
    have hall := hpre.trans (hprepL.trans (hL'.trans (htarget.trans (hprepE.trans (hE'.trans hfinish)))))
    refine ⟨v', S', hall.mono ?_, ?_⟩
    · change _ ≤ 100*b
      omega
    · have hflag : v'.2.2.2 = (if e = y then true else false) := by
        rw [hf']
        change (if e = y then true else vE.2.2.2) = _
        rw [hfE]
        change (if e = y then true else vL.2.2.2) = _
        rw [hfL]
        rfl
      rw [hflag]
      have hlenEq' : i.length = t.length := hlenEq.symm
      change (if (if e = y then true else false) then [true] else []) =
        (if i.length = t.length ∧ e = y then [true] else [])
      simp [hlenEq']
  · simp only [if_neg hlenEq] at hpre
    refine ⟨vL, SL, hpre.mono ?_, ?_⟩
    · change _ ≤ 100*b
      omega
    · rw [hfL]
      have hne : i.length ≠ t.length := Ne.symm hlenEq
      change [] = (if i.length = t.length ∧ e = y then [true] else [])
      simp [hne]

end WentaoHILLRun


noncomputable section
open Turing HILL.PRG HILL.PRG.CheckerTM2 WentaoHILLMachine WentaoHILLLoops
  WentaoHILLControl WentaoHILLCalls WentaoHILLCleanup WentaoHILLResource WentaoHILLBound
  WentaoHILLTransitions WentaoHILLPrepare WentaoHILLStages WentaoHILLFinish WentaoHILLRun
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace WentaoHILLCertificate

def timeBound (C : Machines) : Polynomial ℕ :=
  Polynomial.C (100*(maxPushes (checker C)+1)) * callBound C + Polynomial.X +
    Polynomial.C (Fintype.card (Key C)+1)

lemma full_run (C : Machines) (w : Bits) :
    ∃ k ≤ (timeBound C).eval w.length,
      (flip bind (checker C).step)^[k] (some (initList (checker C) w)) =
        some (haltList (checker C)
          (inversionChecker (C 1).fn (C 2).fn (C 3).fn (C 0).fn w)) := by
  classical
  obtain ⟨v, S, ⟨r, hr, hs⟩, hout⟩ := run_to_cleanup C w
  have hsize := totalSize_iterate r _ _ hs
  rw [totalSize_initList] at hsize
  have hsize' := hsize.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right (maxPushes (checker C)) hr) w.length)
  change totalSize S ≤ w.length + 100 * (callBound C).eval w.length * maxPushes (checker C) at hsize'
  obtain ⟨s, hsc, hc⟩ := cleanup_run C 0 v S (cleared_zero C S)
  rw [hout] at hc
  refine ⟨r+s, ?_, ?_⟩
  · simp only [timeBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    change s ≤ totalSize S + (Fintype.card (Key C) - 0) + 1 at hsc
    have hnat := Nat.add_le_add hr hsc
    have hm : 100 * (callBound C).eval w.length +
        (totalSize S + (Fintype.card (Key C) - 0) + 1) ≤
        100 * (callBound C).eval w.length +
        (w.length + 100 * (callBound C).eval w.length * maxPushes (checker C) +
          Fintype.card (Key C) + 1) := by omega
    apply (hnat.trans hm).trans
    exact le_of_eq (by ring)
  · rw [Nat.add_comm r s, Function.iterate_add_apply, hs, hc]

noncomputable def computable (C : Machines) :
    TM2ComputableInPolyTime (id : Bits → Bits) (id : Bits → Bits)
      (inversionChecker (C 1).fn (C 2).fn (C 3).fn (C 0).fn) where
  tm := checker C
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timeBound C
  outputsFun w := Classical.choice (by
    obtain ⟨k, hk, hs⟩ := full_run C w
    refine ⟨⟨⟨k, ?_⟩, hk⟩⟩
    simpa [Equiv.refl] using hs)

end WentaoHILLCertificate

theorem solution (T L E I : Bits → Bits)
    (hT : PolyTimeComputable T) (hL : PolyTimeComputable L)
    (hE : PolyTimeComputable E) (hI : PolyTimeComputable I) :
    PolyTimeComputable (inversionChecker T L E I) := by
  obtain ⟨MT⟩ := hT
  obtain ⟨ML⟩ := hL
  obtain ⟨ME⟩ := hE
  obtain ⟨MI⟩ := hI
  let C : Machines := ![⟨I, MI⟩, ⟨T, MT⟩, ⟨L, ML⟩, ⟨E, ME⟩]
  exact ⟨WentaoHILLCertificate.computable C⟩

