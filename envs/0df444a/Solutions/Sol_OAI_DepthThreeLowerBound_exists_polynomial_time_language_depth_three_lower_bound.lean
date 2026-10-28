-- Prove2me | solution 1 for OAI.DepthThreeLowerBound.exists_polynomial_time_language_depth_three_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:30:04.389622+00:00
-- url     : https://prove2.me/submissions/c7ec9fe5-54cc-432e-a817-852be7f70a9a

import Mathlib
import Definitions.Def_DepthThree

namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI

universe uDepth1 uV uS uK uGamma uQ uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7 uDepth8 uDepth9 uDepth10 uDepth11 uDepth12 uDepth13 uDepth14 uDepth15 uDepth16 uDepth17 uDepth18 uDepth19 uDepth20 uDepth21 uDepth22 uDepth23 uDepth24 uDepth25 uDepth26 u v

section
section
namespace OAI

namespace DepthThreeLowerBound

abbrev TapeRegister := Fin 32

namespace TapeRegister

abbrev input : TapeRegister := 0
abbrev length : TapeRegister := 1
abbrev dataLength : TapeRegister := 2
abbrev ringDegree : TapeRegister := 3
abbrev coeffCount : TapeRegister := 4
abbrev candidate : TapeRegister := 5
abbrev powerTarget : TapeRegister := 6
abbrev powerScratch : TapeRegister := 7
abbrev requiredLength : TapeRegister := 8
abbrev loop0 : TapeRegister := 9
abbrev loop1 : TapeRegister := 10
abbrev loop2 : TapeRegister := 11
abbrev loop3 : TapeRegister := 12
abbrev loop4 : TapeRegister := 13
abbrev loop5 : TapeRegister := 14
abbrev dataBits : TapeRegister := 15
abbrev keyBits : TapeRegister := 16
abbrev polyBits : TapeRegister := 17
abbrev coeffBits : TapeRegister := 18
abbrev hashBits : TapeRegister := 19
abbrev accumBits : TapeRegister := 20
abbrev productBits : TapeRegister := 21
abbrev indexA : TapeRegister := 22
abbrev indexB : TapeRegister := 23
abbrev indexC : TapeRegister := 24
abbrev scratchA : TapeRegister := 25
abbrev scratchB : TapeRegister := 26
abbrev scratchC : TapeRegister := 27
abbrev savedCount : TapeRegister := 28
abbrev temp0 : TapeRegister := 29
abbrev temp1 : TapeRegister := 30
abbrev temp2 : TapeRegister := 31

end TapeRegister

inductive TapeAtom where
  | blank
  | home
  | delimiter (r : TapeRegister)
  | bit (b : Bool)
  | endMark
  deriving DecidableEq, Fintype, Inhabited

abbrev TapeMark := Fin 4

abbrev TapeSymbol := TapeAtom × (TapeMark → Bool)

def cleanAtom (a : TapeAtom) : TapeSymbol := (a, fun _ => false)

def blankSymbol : TapeSymbol := cleanAtom .blank

def rawInputSymbol (b : Bool) : TapeSymbol := cleanAtom (.bit b)

@[simp] theorem cleanAtom_atom (a : TapeAtom) : (cleanAtom a).1 = a := rfl

@[simp] theorem cleanAtom_mark (a : TapeAtom) (m : TapeMark) :
    (cleanAtom a).2 m = false := rfl

@[simp] theorem default_tapeSymbol : (default : TapeSymbol) = blankSymbol := rfl

theorem cleanAtom_injective : Function.Injective cleanAtom := by
  intro a b h
  exact congrArg Prod.fst h

theorem rawInputSymbol_injective : Function.Injective rawInputSymbol := by
  intro a b h
  have hab : TapeAtom.bit a = TapeAtom.bit b := congrArg Prod.fst h
  cases hab
  rfl

@[simp] theorem rawInputSymbol_ne_blank (b : Bool) : rawInputSymbol b ≠ blankSymbol := by
  intro h
  have hab : TapeAtom.bit b = TapeAtom.blank := congrArg Prod.fst h
  cases hab

abbrev TapeStore := TapeRegister → List Bool

def tapeRegisters : List TapeRegister := List.ofFn id

@[simp] theorem tapeRegisters_length : tapeRegisters.length = 32 := by
  simp [tapeRegisters]

@[simp] theorem mem_tapeRegisters (r : TapeRegister) : r ∈ tapeRegisters := by
  change r ∈ List.ofFn (fun i : TapeRegister => i)
  exact List.mem_ofFn.mpr ⟨r, rfl⟩

theorem tapeRegisters_nodup : tapeRegisters.Nodup := by
  exact List.nodup_ofFn_ofInjective (fun _ _ h => h)

def encodeInput (bits : List Bool) : List TapeSymbol := bits.map rawInputSymbol

@[simp] theorem encodeInput_length (bits : List Bool) :
    (encodeInput bits).length = bits.length := by
  simp [encodeInput]

def encodeBlock (σ : TapeStore) (r : TapeRegister) : List TapeSymbol :=
  cleanAtom (.delimiter r) :: encodeInput (σ r)

def encodeStore (σ : TapeStore) : List TapeSymbol :=
  cleanAtom .home :: (tapeRegisters.flatMap (encodeBlock σ) ++ [cleanAtom .endMark])

@[simp] theorem encodeBlock_length (σ : TapeStore) (r : TapeRegister) :
    (encodeBlock σ r).length = (σ r).length + 1 := by
  simp [encodeBlock]

theorem encodeBlocks_length (σ : TapeStore) (rs : List TapeRegister) :
    (rs.flatMap (encodeBlock σ)).length =
      rs.length + (rs.map (fun r => (σ r).length)).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
      simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem encodeStore_length (σ : TapeStore) :
    (encodeStore σ).length =
      34 + (tapeRegisters.map (fun r => (σ r).length)).sum := by
  simp [encodeStore, Nat.add_comm]
  simp only [← Nat.add_assoc]

@[simp] theorem encodeStore_head? (σ : TapeStore) :
    (encodeStore σ).head? = some (cleanAtom .home) := rfl

@[simp] theorem encodeStore_ne_nil (σ : TapeStore) : encodeStore σ ≠ [] := by
  simp [encodeStore]

theorem encodeInput_symbols {bits : List Bool} {s : TapeSymbol}
    (hs : s ∈ encodeInput bits) :
    (∃ b : Bool, s.1 = .bit b) ∧ ∀ m, s.2 m = false := by
  rcases List.mem_map.mp hs with ⟨b, _, rfl⟩
  exact ⟨⟨b, rfl⟩, fun _ => rfl⟩

theorem encodeBlock_symbols {σ : TapeStore} {r : TapeRegister} {s : TapeSymbol}
    (hs : s ∈ encodeBlock σ r) :
    s.1 ≠ .blank ∧ s.1 ≠ .home ∧ s.1 ≠ .endMark ∧ ∀ m, s.2 m = false := by
  rcases List.mem_cons.mp hs with hs | hs
  · subst s
    simp [cleanAtom]
  · obtain ⟨⟨b, hb⟩, hm⟩ := encodeInput_symbols hs
    exact ⟨by simp [hb], by simp [hb], by simp [hb], hm⟩

theorem encodeBlocks_symbols {σ : TapeStore} {rs : List TapeRegister} {s : TapeSymbol}
    (hs : s ∈ rs.flatMap (encodeBlock σ)) :
    s.1 ≠ .blank ∧ s.1 ≠ .home ∧ s.1 ≠ .endMark ∧ ∀ m, s.2 m = false := by
  rcases List.mem_flatMap.mp hs with ⟨r, _, hr⟩
  exact encodeBlock_symbols hr

theorem encodeStore_no_blank {σ : TapeStore} {s : TapeSymbol}
    (hs : s ∈ encodeStore σ) : s.1 ≠ .blank := by
  rcases List.mem_cons.mp hs with hs | hs
  · subst s
    simp [cleanAtom]
  · rcases List.mem_append.mp hs with hs | hs
    · exact (encodeBlocks_symbols hs).1
    · have hs' : s = cleanAtom .endMark := List.mem_singleton.mp hs
      subst s
      simp [cleanAtom]

theorem encodeStore_clean {σ : TapeStore} {s : TapeSymbol}
    (hs : s ∈ encodeStore σ) (m : TapeMark) : s.2 m = false := by
  rcases List.mem_cons.mp hs with hs | hs
  · subst s
    rfl
  · rcases List.mem_append.mp hs with hs | hs
    · exact (encodeBlocks_symbols hs).2.2.2 m
    · have hs' : s = cleanAtom .endMark := List.mem_singleton.mp hs
      subst s
      rfl

theorem encodeStore_tail_no_home {σ : TapeStore} {s : TapeSymbol}
    (hs : s ∈ (encodeStore σ).tail) : s.1 ≠ .home := by
  change s ∈ tapeRegisters.flatMap (encodeBlock σ) ++ [cleanAtom .endMark] at hs
  rcases List.mem_append.mp hs with hs | hs
  · exact (encodeBlocks_symbols hs).2.1
  · have hs' : s = cleanAtom .endMark := List.mem_singleton.mp hs
    subst s
    simp [cleanAtom]

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

namespace TapeWord

open Turing

variable {Γ : Type uDepth1} [Inhabited Γ]

@[simp] theorem head_mk₂_cons (L R : List Γ) (a : Γ) :
    (Tape.mk₂ L (a :: R)).head = a := rfl

@[simp] theorem move_right_mk₂_cons (L R : List Γ) (a : Γ) :
    (Tape.mk₂ L (a :: R)).move Dir.right = Tape.mk₂ (a :: L) R := rfl

@[simp] theorem write_mk₂_cons (L R : List Γ) (a b : Γ) :
    (Tape.mk₂ L (a :: R)).write b = Tape.mk₂ L (b :: R) := rfl

theorem move_right_iterate_mk₂_append («prefix» L R : List Γ) :
    (Tape.move Dir.right)^[«prefix».length] (Tape.mk₂ L («prefix» ++ R)) =
      Tape.mk₂ («prefix».reverse ++ L) R := by
  induction «prefix» generalizing L with
  | nil => rfl
  | cons a «prefix» ih =>
    rw [List.length_cons, List.cons_append, Function.iterate_succ_apply,
      move_right_mk₂_cons]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append] using ih (a :: L)

end TapeWord

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound



variable {V : Type uV}

namespace Literal


end Literal


namespace GateInput


end GateInput

namespace RawClause


end RawClause


namespace Circuit3





end Circuit3









attribute [instance] FiniteMultiTapeMachine.tapeFinite
  FiniteMultiTapeMachine.tapeDecidableEq FiniteMultiTapeMachine.alphabetInhabited
  FiniteMultiTapeMachine.alphabetFinite FiniteMultiTapeMachine.stateFinite

namespace FiniteMultiTapeMachine




end FiniteMultiTapeMachine


end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

@[simp] theorem runSteps_zero {S : Type uDepth1} (step : S → Option S) (c : Option S) :
    runSteps step 0 c = c := rfl

theorem runSteps_succ {S : Type uDepth2} (step : S → Option S) (n : ℕ) (c : Option S) :
    runSteps step (n + 1) c = (runSteps step n c).bind step := by
  exact Function.iterate_succ_apply' _ _ _

theorem runSteps_succ_left {S : Type uDepth3} (step : S → Option S) (n : ℕ)
    (c : Option S) :
    runSteps step (n + 1) c = runSteps step n (c.bind step) := by
  exact Function.iterate_succ_apply _ _ _

@[simp] theorem runSteps_none {S : Type uDepth4} (step : S → Option S) (n : ℕ) :
    runSteps step n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runSteps_succ, ih]; rfl

theorem runSteps_add {S : Type uDepth5} (step : S → Option S) (m n : ℕ) (c : Option S) :
    runSteps step (m + n) c = runSteps step m (runSteps step n c) := by
  exact Function.iterate_add_apply _ _ _ _

theorem runSteps_succ_eq_of_step_eq {S : Type uDepth6} {step : S → Option S}
    {a b : S} (h : step a = step b) (n : ℕ) :
    runSteps step (n + 1) (some a) = runSteps step (n + 1) (some b) := by
  rw [runSteps_succ_left, runSteps_succ_left]
  exact congrArg (runSteps step n) h

theorem runSteps_eq_of_step_eq {S : Type uDepth7} {step : S → Option S}
    {a b : S} (h : step a = step b) {n : ℕ} (hn : 0 < n) :
    runSteps step n (some a) = runSteps step n (some b) := by
  cases n with
  | zero => exact False.elim ((Nat.not_lt_zero 0) hn)
  | succ n => exact runSteps_succ_eq_of_step_eq h n

def RunsIn {S : Type uDepth8} (step : S → Option S) (a b : S) (bound : ℕ) : Prop :=
  ∃ n ≤ bound, runSteps step n (some a) = some b

theorem RunsIn.refl {S : Type uDepth9} (step : S → Option S) (a : S) :
    RunsIn step a a 0 :=
  ⟨0, le_refl 0, rfl⟩

theorem RunsIn.single {S : Type uDepth10} {step : S → Option S} {a b : S}
    (h : step a = some b) : RunsIn step a b 1 :=
  ⟨1, le_refl 1, h⟩

theorem RunsIn.mono {S : Type uDepth11} {step : S → Option S} {a b : S} {m n : ℕ}
    (h : RunsIn step a b m) (hmn : m ≤ n) : RunsIn step a b n := by
  obtain ⟨k, hk, he⟩ := h
  exact ⟨k, hk.trans hmn, he⟩

theorem RunsIn.trans {S : Type uDepth12} {step : S → Option S} {a b c : S} {m n : ℕ}
    (h₁ : RunsIn step a b m) (h₂ : RunsIn step b c n) :
    RunsIn step a c (m + n) := by
  obtain ⟨k₁, hk₁, he₁⟩ := h₁
  obtain ⟨k₂, hk₂, he₂⟩ := h₂
  refine ⟨k₂ + k₁, ?_, ?_⟩
  · simpa only [Nat.add_comm] using Nat.add_le_add hk₂ hk₁
  · rw [runSteps_add, he₁]
    exact he₂

structure FiniteMachine where
  Γ : Type
  [alphabetInhabited : Inhabited Γ]
  [alphabetFinite : Fintype Γ]
  Λ : Type
  [stateInhabited : Inhabited Λ]
  [stateFinite : Fintype Λ]
  inputSymbol : Bool → Γ
  input_injective : Function.Injective inputSymbol
  input_ne_blank : ∀ b, inputSymbol b ≠ default
  code : Turing.TM0.Machine Γ Λ
  accept : Λ → Bool

attribute [instance] FiniteMachine.alphabetInhabited FiniteMachine.alphabetFinite
  FiniteMachine.stateInhabited FiniteMachine.stateFinite

def HaltsIn (M : FiniteMachine) (input : List Bool) (output : Bool) (time : ℕ) : Prop :=
  ∃ k ≤ time, ∃ c : Turing.TM0.Cfg M.Γ M.Λ,
    runSteps (Turing.TM0.step M.code) k
      (some (Turing.TM0.init (input.map M.inputSymbol))) = some c ∧
    Turing.TM0.step M.code c = none ∧ M.accept c.q = output

def PolynomialTimeDecider (f : List Bool → Bool) : Prop :=
  ∃ M : FiniteMachine, ∃ C a : ℕ, 0 < C ∧ 0 < a ∧
    ∀ w, HaltsIn M w (f w) (C * (w.length + 1) ^ a)

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

deriving instance DecidableEq, Inhabited for HeadMove

instance : Fintype HeadMove where
  elems := { .left, .stay, .right }
  complete := by
    intro m
    cases m <;> simp

@[simp] theorem HeadMove.apply_left {Γ : Type uDepth1} [Inhabited Γ] (t : Turing.Tape Γ) :
    HeadMove.left.apply t = t.move Turing.Dir.left := rfl

@[simp] theorem HeadMove.apply_stay {Γ : Type uDepth2} [Inhabited Γ] (t : Turing.Tape Γ) :
    HeadMove.stay.apply t = t := rfl

@[simp] theorem HeadMove.apply_right {Γ : Type uDepth3} [Inhabited Γ] (t : Turing.Tape Γ) :
    HeadMove.right.apply t = t.move Turing.Dir.right := rfl

theorem multiTapeStep_eq_some {K : Type uDepth4} {Γ : Type uDepth5} {Q : Type uDepth6} [Inhabited Γ]
    {code : MultiTapeCode K Γ Q} {c : MultiTapeCfg K Γ Q}
    {q : Q} {writes : K → Γ} {moves : K → HeadMove}
    (h : code c.q (fun k => (c.tapes k).head) = some (q, writes, moves)) :
    multiTapeStep code c = some (multiTapeUpdate c q writes moves) := by
  simp only [multiTapeStep, h, Option.map_some]

@[simp] theorem multiTapeStep_eq_none_iff {K : Type uDepth7} {Γ : Type uDepth8} {Q : Type uDepth9} [Inhabited Γ]
    (code : MultiTapeCode K Γ Q) (c : MultiTapeCfg K Γ Q) :
    multiTapeStep code c = none ↔ code c.q (fun k => (c.tapes k).head) = none := by
  unfold multiTapeStep
  cases h : code c.q (fun k => (c.tapes k).head) <;> simp

namespace FiniteMultiTapeMachine

@[simp] theorem init_q (M : FiniteMultiTapeMachine) (input : List Bool) :
    (M.init input).q = M.initialState := rfl

@[simp] theorem init_inputTape (M : FiniteMultiTapeMachine) (input : List Bool) :
    (M.init input).tapes M.inputTape = Turing.Tape.mk₁ (input.map M.inputSymbol) := by
  simp [init]

theorem init_otherTape (M : FiniteMultiTapeMachine) (input : List Bool)
    (k : M.K) (hk : k ≠ M.inputTape) :
    (M.init input).tapes k = Turing.Tape.mk₁ [] := by
  simp [init, hk]

end FiniteMultiTapeMachine

theorem multiTapeHaltsIn_iff_runsIn (M : FiniteMultiTapeMachine) (input : List Bool)
    (output : Bool) (time : ℕ) :
    MultiTapeHaltsIn M input output time ↔
      ∃ c : M.Cfg, RunsIn M.step (M.init input) c time ∧
        M.step c = none ∧ M.accept c.q = output := by
  constructor
  · rintro ⟨k, hk, c, hrun, hhalt, hout⟩
    exact ⟨c, ⟨k, hk, hrun⟩, hhalt, hout⟩
  · rintro ⟨c, ⟨k, hk, hrun⟩, hhalt, hout⟩
    exact ⟨k, hk, c, hrun, hhalt, hout⟩

theorem MultiTapeHaltsIn.mono {M : FiniteMultiTapeMachine} {input : List Bool}
    {output : Bool} {m n : ℕ} (h : MultiTapeHaltsIn M input output m) (hmn : m ≤ n) :
    MultiTapeHaltsIn M input output n := by
  obtain ⟨k, hk, c, hrun, hhalt, hout⟩ := h
  exact ⟨k, hk.trans hmn, c, hrun, hhalt, hout⟩

def MultiTapePolynomialTimeDecider (f : List Bool → Bool) : Prop :=
  ∃ M : FiniteMultiTapeMachine, ∃ C a : ℕ, 0 < C ∧ 0 < a ∧
    ∀ w, MultiTapeHaltsIn M w (f w) (C * (w.length + 1) ^ a)

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

open Turing

abbrev TapeHeads := TapeRegister → TapeSymbol
abbrev TapeMoves := TapeRegister → HeadMove
abbrev TapeTapes := TapeRegister → Tape TapeSymbol
abbrev TapeMultiCfg (Q : Type uDepth1) := MultiTapeCfg TapeRegister TapeSymbol Q
abbrev TapeMultiProgram (Q : Type uDepth2) :=
  Q → TapeHeads → Option (Q × TapeHeads × TapeMoves)

def wordTape (bits : List Bool) : Tape TapeSymbol :=
  Tape.mk₁ (cleanAtom .home :: (encodeInput bits ++ [cleanAtom .endMark]))

def cursorTape (before after : List Bool) : Tape TapeSymbol :=
  Tape.mk₂ ((encodeInput before).reverse ++ [cleanAtom .home])
    (encodeInput after ++ [cleanAtom .endMark])

@[simp] theorem wordTape_head (bits : List Bool) :
    (wordTape bits).head = cleanAtom .home := rfl

@[simp] theorem cursorTape_head_cons (before after : List Bool) (b : Bool) :
    (cursorTape before (b :: after)).head = rawInputSymbol b := rfl

@[simp] theorem cursorTape_head_nil (before : List Bool) :
    (cursorTape before []).head = cleanAtom .endMark := rfl

@[simp] theorem wordTape_right (bits : List Bool) :
    (wordTape bits).move Dir.right = cursorTape [] bits := rfl

theorem cursorTape_right (before after : List Bool) (b : Bool) :
    (cursorTape before (b :: after)).move Dir.right =
      cursorTape (before ++ [b]) after := by
  simp only [cursorTape, encodeInput, List.map_append, List.map_cons, List.map_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, TapeWord.move_right_mk₂_cons]

namespace TapeMultiProgram

def step {Q : Type uDepth3} (P : TapeMultiProgram Q) : TapeMultiCfg Q → Option (TapeMultiCfg Q) :=
  multiTapeStep P

def cfg {Q : Type uDepth4} (q : Q) (T : TapeTapes) : TapeMultiCfg Q := ⟨q, T⟩

def heads (T : TapeTapes) : TapeHeads := fun r => (T r).head

def stayMoves : TapeMoves := fun _ => .stay

def moveOnly (r : TapeRegister) (d : HeadMove) : TapeMoves :=
  Function.update stayMoves r d

def writeOnly (r : TapeRegister) (symbol : TapeSymbol) (h : TapeHeads) : TapeHeads :=
  Function.update h r symbol

def jump {Q : Type uDepth5} (q : Q) (h : TapeHeads) :
    Option (Q × TapeHeads × TapeMoves) := some (q, h, stayMoves)

def move {Q : Type uDepth6} (r : TapeRegister) (d : HeadMove) (q : Q) (h : TapeHeads) :
    Option (Q × TapeHeads × TapeMoves) := some (q, h, moveOnly r d)

def writeMove {Q : Type uDepth7} (r : TapeRegister) (symbol : TapeSymbol)
    (d : HeadMove) (q : Q) (h : TapeHeads) :
    Option (Q × TapeHeads × TapeMoves) :=
  some (q, writeOnly r symbol h, moveOnly r d)

def isAtom (a : TapeAtom) (r : TapeRegister) (h : TapeHeads) : Bool :=
  decide ((h r).1 = a)

def machine {Q : Type} [Fintype Q] (P : TapeMultiProgram Q)
    (initial : Q) (accept : Q → Bool) : FiniteMultiTapeMachine where
  K := TapeRegister
  inputTape := TapeRegister.input
  Γ := TapeSymbol
  Q := Q
  initialState := initial
  inputSymbol := rawInputSymbol
  input_injective := rawInputSymbol_injective
  input_ne_blank := by simpa only [default_tapeSymbol] using rawInputSymbol_ne_blank
  code := P
  accept := accept

end TapeMultiProgram
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

namespace TapeWord

open Turing

variable {Γ : Type uDepth1} [Inhabited Γ]

@[simp] theorem move_left_mk₂_cons (L R : List Γ) (a : Γ) :
    (Tape.mk₂ (a :: L) R).move Dir.left = Tape.mk₂ L (a :: R) :=
  Tape.move_left_mk' (ListBlank.mk (a :: L)) (ListBlank.mk R)

theorem move_left_iterate_mk₂_append («prefix» L R : List Γ) :
    (Tape.move Dir.left)^[«prefix».length] (Tape.mk₂ («prefix» ++ L) R) =
      Tape.mk₂ L («prefix».reverse ++ R) := by
  induction «prefix» generalizing R with
  | nil => rfl
  | cons a «prefix» ih =>
    rw [List.length_cons, List.cons_append, Function.iterate_succ_apply,
      move_left_mk₂_cons]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append] using ih (a :: R)

theorem move_left_iterate_reverse_mk₂ («prefix» L R : List Γ) :
    (Tape.move Dir.left)^[«prefix».length] (Tape.mk₂ («prefix».reverse ++ L) R) =
      Tape.mk₂ L («prefix» ++ R) := by
  simpa only [List.length_reverse, List.reverse_reverse] using
    move_left_iterate_mk₂_append «prefix».reverse L R

theorem move_right_then_left_mk₂_append («prefix» L R : List Γ) :
    (Tape.move Dir.left)^[«prefix».length]
        ((Tape.move Dir.right)^[«prefix».length] (Tape.mk₂ L («prefix» ++ R))) =
      Tape.mk₂ L («prefix» ++ R) := by
  rw [move_right_iterate_mk₂_append]
  exact move_left_iterate_reverse_mk₂ «prefix» L R

end TapeWord

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

open Turing

inductive InitState
  | start
  | home
  | prepare
  | scan
  | rewind
  | done
  deriving DecidableEq, Inhabited

instance : Fintype InitState where
  elems := {.start, .home, .prepare, .scan, .rewind, .done}
  complete := by
    intro state
    cases state <;> simp

private def initActive (r : TapeRegister) : Prop :=
  r = TapeRegister.input ∨ r = TapeRegister.length

private instance (r : TapeRegister) : Decidable (initActive r) :=
  inferInstanceAs (Decidable (r = TapeRegister.input ∨ r = TapeRegister.length))

def initializationCode : TapeMultiProgram InitState
  | .start, h => some (.home, h, fun _ => .left)
  | .home, _ => some (.prepare, fun _ => cleanAtom .home, fun _ => .right)
  | .prepare, h => some (.scan,
      (fun r => if initActive r then h r else cleanAtom .endMark),
      (fun r => if initActive r then .stay else .left))
  | .scan, h =>
      match (h TapeRegister.input).1 with
      | .bit _ => some (.scan,
          (fun r => if r = TapeRegister.length then rawInputSymbol true else h r),
          (fun r => if initActive r then .right else .stay))
      | .blank => some (.rewind,
          (fun r => if initActive r then cleanAtom .endMark else h r),
          fun _ => .stay)
      | _ => none
  | .rewind, h =>
      if (h TapeRegister.input).1 = .home then
        some (.done, h, fun _ => .stay)
      else some (.rewind, h, fun r => if initActive r then .left else .stay)
  | .done, _ => none

def rawInputTapes (bits : List Bool) : TapeTapes := fun r =>
  if r = TapeRegister.input then Tape.mk₁ (encodeInput bits) else Tape.mk₁ []

def initializedTapes (bits : List Bool) : TapeTapes := fun r =>
  if r = TapeRegister.input then wordTape bits
  else if r = TapeRegister.length then wordTape (List.replicate bits.length true)
  else wordTape []

@[simp] theorem initializedTapes_input (bits : List Bool) :
    initializedTapes bits TapeRegister.input = wordTape bits := by
  simp [initializedTapes]

@[simp] theorem initializedTapes_length (bits : List Bool) :
    initializedTapes bits TapeRegister.length =
      wordTape (List.replicate bits.length true) := by
  simp [initializedTapes, TapeRegister.input, TapeRegister.length]

theorem initializedTapes_other (bits : List Bool) (r : TapeRegister)
    (hi : r ≠ TapeRegister.input) (hl : r ≠ TapeRegister.length) :
    initializedTapes bits r = wordTape [] := by
  simp [initializedTapes, hi, hl]

@[simp] theorem initializedTapes_head (bits : List Bool) (r : TapeRegister) :
    (initializedTapes bits r).head = cleanAtom .home := by
  simp only [initializedTapes]
  split_ifs <;> exact wordTape_head _

private theorem init_step {q q' : InitState} {T U : TapeTapes}
    {writes : TapeHeads} {moves : TapeMoves}
    (hc : initializationCode q (fun r => (T r).head) = some (q', writes, moves))
    (ht : ∀ r, (moves r).apply ((T r).write (writes r)) = U r) :
    TapeMultiProgram.step initializationCode ⟨q, T⟩ = some ⟨q', U⟩ := by
  have hu : multiTapeUpdate (⟨q, T⟩ : TapeMultiCfg InitState) q' writes moves =
      ⟨q', U⟩ := by
    change MultiTapeCfg.mk q' (fun r => (moves r).apply ((T r).write (writes r))) = _
    exact congrArg (MultiTapeCfg.mk q') (funext ht)
  change multiTapeStep initializationCode _ = _
  rw [multiTapeStep_eq_some (code := initializationCode)
    (c := (⟨q, T⟩ : TapeMultiCfg InitState)) hc, hu]

private theorem init_raw_left {Γ : Type uDepth1} [Inhabited Γ] (R : List Γ) :
    (Tape.mk₁ R).move Dir.left = Tape.mk₂ [] (default :: R) :=
  Tape.move_left_mk' (ListBlank.mk ([] : List Γ)) (ListBlank.mk R)

private theorem init_write_nil {Γ : Type uDepth2} [Inhabited Γ] (L : List Γ) (a : Γ) :
    (Tape.mk₂ L []).write a = Tape.mk₂ L [a] := rfl

private def initHomeTapes (bits : List Bool) : TapeTapes := fun r =>
  Tape.mk₂ [cleanAtom .home] (if r = TapeRegister.input then encodeInput bits else [])

private def initScanTapes (left right : List Bool) : TapeTapes := fun r =>
  if r = TapeRegister.input then
    Tape.mk₂ (encodeInput left ++ [cleanAtom .home]) (encodeInput right)
  else if r = TapeRegister.length then
    Tape.mk₂ (List.replicate left.length (rawInputSymbol true) ++ [cleanAtom .home]) []
  else wordTape []

private def initRewindTapes (left right : List Bool) : TapeTapes := fun r =>
  if r = TapeRegister.input then
    Tape.mk₂ (encodeInput left ++ [cleanAtom .home])
      (encodeInput right ++ [cleanAtom .endMark])
  else if r = TapeRegister.length then
    Tape.mk₂ (List.replicate left.length (rawInputSymbol true) ++ [cleanAtom .home])
      (List.replicate right.length (rawInputSymbol true) ++ [cleanAtom .endMark])
  else wordTape []

private theorem initialization_start (bits : List Bool) :
    TapeMultiProgram.step initializationCode ⟨.start, rawInputTapes bits⟩ =
      some ⟨.home, fun r => (rawInputTapes bits r).move Dir.left⟩ := by
  apply init_step rfl
  intro r
  simp only [Tape.write_self, HeadMove.apply_left]

private theorem initialization_home (bits : List Bool) :
    TapeMultiProgram.step initializationCode
      ⟨.home, fun r => (rawInputTapes bits r).move Dir.left⟩ =
      some ⟨.prepare, initHomeTapes bits⟩ := by
  apply init_step rfl
  intro r
  by_cases hi : r = TapeRegister.input <;>
    simp [rawInputTapes, initHomeTapes, hi, init_raw_left,
      TapeWord.write_mk₂_cons, TapeWord.move_right_mk₂_cons]

private theorem initialization_prepare (bits : List Bool) :
    TapeMultiProgram.step initializationCode ⟨.prepare, initHomeTapes bits⟩ =
      some ⟨.scan, initScanTapes [] bits⟩ := by
  apply init_step rfl
  intro r
  by_cases hi : r = TapeRegister.input
  · subst r
    simp [initActive, initHomeTapes, initScanTapes, encodeInput]
  · by_cases hl : r = TapeRegister.length
    · subst r
      simp [initActive, initHomeTapes, initScanTapes, TapeRegister.input, TapeRegister.length]
    · simp [initActive, initHomeTapes, initScanTapes, hi, hl, init_write_nil,
        TapeWord.move_left_mk₂_cons, wordTape, encodeInput, Tape.mk₁]

private theorem initialization_scan_bit (left right : List Bool) (b : Bool) :
    TapeMultiProgram.step initializationCode ⟨.scan, initScanTapes left (b :: right)⟩ =
      some ⟨.scan, initScanTapes (b :: left) right⟩ := by
  apply init_step rfl
  intro r
  by_cases hi : r = TapeRegister.input
  · subst r
    simp [initActive, initScanTapes, encodeInput, TapeRegister.input,
      TapeRegister.length, TapeWord.move_right_mk₂_cons]
  · by_cases hl : r = TapeRegister.length
    · subst r
      simp [initActive, initScanTapes, TapeRegister.input, TapeRegister.length,
        init_write_nil, TapeWord.move_right_mk₂_cons, List.replicate_succ]
    · simp [initActive, initScanTapes, hi, hl, wordTape, Tape.mk₁,
        TapeWord.write_mk₂_cons]

private theorem initialization_scan_end (left : List Bool) :
    TapeMultiProgram.step initializationCode ⟨.scan, initScanTapes left []⟩ =
      some ⟨.rewind, initRewindTapes left []⟩ := by
  apply init_step (by rfl)
  intro r
  by_cases hi : r = TapeRegister.input
  · subst r
    simp [initActive, initScanTapes, initRewindTapes, encodeInput, init_write_nil]
  · by_cases hl : r = TapeRegister.length
    · subst r
      simp [initActive, initScanTapes, initRewindTapes, init_write_nil,
        TapeRegister.input, TapeRegister.length]
    · simp [initActive, initScanTapes, initRewindTapes, hi, hl, wordTape, Tape.mk₁,
        TapeWord.write_mk₂_cons]

private theorem initRewind_head_ne_home (left right : List Bool) :
    ((initRewindTapes left right TapeRegister.input).head).1 ≠ TapeAtom.home := by
  cases right <;> simp [initRewindTapes, encodeInput, rawInputSymbol, cleanAtom]

private theorem initialization_rewind_bit (left right : List Bool) (b : Bool) :
    TapeMultiProgram.step initializationCode ⟨.rewind, initRewindTapes (b :: left) right⟩ =
      some ⟨.rewind, initRewindTapes left (b :: right)⟩ := by
  apply init_step (writes := fun r => (initRewindTapes (b :: left) right r).head)
    (moves := fun r => if initActive r then .left else .stay) (by
      simp only [initializationCode, initRewind_head_ne_home, ↓reduceIte])
  intro r
  by_cases hi : r = TapeRegister.input
  · subst r
    simp [initActive, initRewindTapes, encodeInput, TapeWord.move_left_mk₂_cons]
  · by_cases hl : r = TapeRegister.length
    · subst r
      simp [initActive, initRewindTapes, TapeRegister.input, TapeRegister.length,
        List.replicate_succ, TapeWord.move_left_mk₂_cons]
    · simp [initActive, initRewindTapes, hi, hl, wordTape, Tape.mk₁,
        TapeWord.write_mk₂_cons]

private theorem initialization_rewind_home (right : List Bool) :
    TapeMultiProgram.step initializationCode ⟨.rewind, initRewindTapes [] right⟩ =
      some ⟨.rewind, initializedTapes right⟩ := by
  apply init_step (writes := fun r => (initRewindTapes [] right r).head)
    (moves := fun r => if initActive r then .left else .stay) (by
      simp only [initializationCode, initRewind_head_ne_home, ↓reduceIte])
  intro r
  by_cases hi : r = TapeRegister.input
  · subst r
    simp [initActive, initRewindTapes, initializedTapes, encodeInput,
      TapeWord.move_left_mk₂_cons, wordTape, Tape.mk₁]
  · by_cases hl : r = TapeRegister.length
    · subst r
      simp [initActive, initRewindTapes, initializedTapes, encodeInput,
        TapeRegister.input, TapeRegister.length, TapeWord.move_left_mk₂_cons,
        wordTape, Tape.mk₁]
    · simp [initActive, initRewindTapes, initializedTapes, hi, hl, wordTape, Tape.mk₁,
        TapeWord.write_mk₂_cons]

private theorem initialization_finish (bits : List Bool) :
    TapeMultiProgram.step initializationCode ⟨.rewind, initializedTapes bits⟩ =
      some ⟨.done, initializedTapes bits⟩ := by
  apply init_step (writes := fun r => (initializedTapes bits r).head)
    (moves := fun _ => .stay) (by simp [initializationCode])
  intro r
  simp only [Tape.write_self, HeadMove.apply_stay]

private theorem initialization_scan_runs (left right : List Bool) :
    RunsIn (TapeMultiProgram.step initializationCode)
      ⟨.scan, initScanTapes left right⟩
      ⟨.scan, initScanTapes (right.reverse ++ left) []⟩ right.length := by
  induction right generalizing left with
  | nil =>
      simpa using RunsIn.refl (TapeMultiProgram.step initializationCode)
        (⟨.scan, initScanTapes left []⟩ : TapeMultiCfg InitState)
  | cons b right ih =>
    have h := (RunsIn.single (initialization_scan_bit left right b)).trans (ih (b :: left))
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, Nat.add_comm] using h

private theorem initialization_rewind_runs (left right : List Bool) :
    RunsIn (TapeMultiProgram.step initializationCode)
      ⟨.rewind, initRewindTapes left right⟩
      ⟨.rewind, initializedTapes (left.reverse ++ right)⟩ (left.length + 1) := by
  induction left generalizing right with
  | nil => simpa using RunsIn.single (initialization_rewind_home right)
  | cons b left ih =>
    have h := (RunsIn.single (initialization_rewind_bit left right b)).trans (ih (b :: right))
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem initialization_runs (bits : List Bool) :
    RunsIn (TapeMultiProgram.step initializationCode)
      ⟨.start, rawInputTapes bits⟩ ⟨.done, initializedTapes bits⟩ (2 * bits.length + 6) := by
  have hsetup := ((RunsIn.single (initialization_start bits)).trans
    (RunsIn.single (initialization_home bits))).trans
    (RunsIn.single (initialization_prepare bits))
  have hscan := initialization_scan_runs [] bits
  simp only [List.append_nil] at hscan
  have hrewind := initialization_rewind_runs bits.reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hrewind
  have h := (((hsetup.trans hscan).trans
    (RunsIn.single (initialization_scan_end bits.reverse))).trans hrewind).trans
    (RunsIn.single (initialization_finish bits))
  exact h.mono (by omega)

@[simp] theorem initialization_done (T : TapeTapes) :
    TapeMultiProgram.step initializationCode ⟨.done, T⟩ = none := rfl

def initializationMachine : FiniteMultiTapeMachine :=
  TapeMultiProgram.machine initializationCode .start (fun _ => true)

@[simp] theorem initializationMachine_init (bits : List Bool) :
    initializationMachine.init bits = ⟨.start, rawInputTapes bits⟩ := rfl

theorem initializationMachine_halts (bits : List Bool) :
    MultiTapeHaltsIn initializationMachine bits true (2 * bits.length + 6) := by
  apply (multiTapeHaltsIn_iff_runsIn _ _ _ _).2
  refine ⟨⟨.done, initializedTapes bits⟩, ?_, ?_, rfl⟩
  · exact initialization_runs bits
  · exact initialization_done _

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

theorem runSteps_map_of_some {S : Type uDepth1} {T : Type uDepth2} {step : S → Option S}
    {next : T → Option T} (f : S → T)
    (hstep : ∀ a b, step a = some b → next (f a) = some (f b))
    {n : ℕ} {a b : S} (h : runSteps step n (some a) = some b) :
    runSteps next n (some (f a)) = some (f b) := by
  induction n generalizing a with
  | zero =>
      have hab : a = b := Option.some.inj h
      subst a
      rfl
  | succ n ih =>
      rw [runSteps_succ_left] at h ⊢
      cases he : step a with
      | none =>
          have hfalse : (none : Option S) = some b := by
            simpa only [Option.bind_some, he, runSteps_none] using h
          cases hfalse
      | some c =>
          have hc : runSteps step n (some c) = some b := by
            simpa only [Option.bind_some, he] using h
          simpa only [Option.bind_some, hstep a c he] using ih hc

theorem RunsIn.map {S : Type uDepth3} {T : Type uDepth4} {step : S → Option S} {next : T → Option T}
    (f : S → T)
    (hstep : ∀ a b, step a = some b → next (f a) = some (f b))
    {a b : S} {n : ℕ} (h : RunsIn step a b n) :
    RunsIn next (f a) (f b) n := by
  obtain ⟨k, hk, he⟩ := h
  exact ⟨k, hk, runSteps_map_of_some f hstep he⟩

namespace TapeMultiProgram

def mapCfg {Q : Type uDepth5} {R : Type uDepth6} (f : Q → R) (c : TapeMultiCfg Q) : TapeMultiCfg R :=
  ⟨f c.q, c.tapes⟩

theorem step_jump {Q : Type uDepth7} (P : TapeMultiProgram Q) (q q' : Q) (T : TapeTapes)
    (h : P q (heads T) = jump q' (heads T)) :
    P.step (cfg q T) = some (cfg q' T) := by
  have he := multiTapeStep_eq_some (c := cfg q T) (code := P) h
  simpa only [step, cfg, heads, jump, multiTapeUpdate, stayMoves,
    HeadMove.apply_stay, Turing.Tape.write_self] using he

theorem step_move {Q : Type uDepth8} (P : TapeMultiProgram Q) (q q' : Q)
    (T : TapeTapes) (r : TapeRegister) (d : HeadMove)
    (h : P q (heads T) = move r d q' (heads T)) :
    P.step (cfg q T) = some (cfg q' (Function.update T r (d.apply (T r)))) := by
  have he := multiTapeStep_eq_some (c := cfg q T) (code := P) h
  change P.step (cfg q T) = some (multiTapeUpdate (cfg q T) q'
    (heads T) (moveOnly r d)) at he
  rw [he]
  congr 1
  apply congrArg (cfg q')
  funext k
  by_cases hk : k = r
  · subst k
    simp [cfg, heads, moveOnly, Turing.Tape.write_self]
  · simp [cfg, heads, moveOnly, stayMoves, hk]

theorem step_writeMove {Q : Type uDepth9} (P : TapeMultiProgram Q) (q q' : Q)
    (T : TapeTapes) (r : TapeRegister) (symbol : TapeSymbol) (d : HeadMove)
    (h : P q (heads T) = writeMove r symbol d q' (heads T)) :
    P.step (cfg q T) =
      some (cfg q' (Function.update T r (d.apply ((T r).write symbol)))) := by
  have he := multiTapeStep_eq_some (c := cfg q T) (code := P) h
  change P.step (cfg q T) = some (multiTapeUpdate (cfg q T) q'
    (writeOnly r symbol (heads T)) (moveOnly r d)) at he
  rw [he]
  congr 1
  apply congrArg (cfg q')
  funext k
  by_cases hk : k = r
  · subst k
    simp [cfg, writeOnly, moveOnly]
  · simp [cfg, heads, writeOnly, moveOnly, stayMoves, hk]

theorem step_map {Q : Type uDepth10} {R : Type uDepth11} (P : TapeMultiProgram Q) (P' : TapeMultiProgram R)
    (f : Q → R)
    (hcode : ∀ q h q' writes moves,
      P q h = some (q', writes, moves) →
      P' (f q) h = some (f q', writes, moves))
    (a b : TapeMultiCfg Q) (h : P.step a = some b) :
    P'.step (mapCfg f a) = some (mapCfg f b) := by
  cases hp : P a.q (heads a.tapes) with
  | none =>
      have hn : P.step a = none := (multiTapeStep_eq_none_iff P a).2 hp
      have hfalse : (none : Option (TapeMultiCfg Q)) = some b := hn.symm.trans h
      cases hfalse
  | some out =>
      rcases out with ⟨q, writes, moves⟩
      have hb : b = multiTapeUpdate a q writes moves := by
        exact (Option.some.inj ((multiTapeStep_eq_some (c := a) (code := P) hp).symm.trans h)).symm
      subst b
      have he := multiTapeStep_eq_some (c := mapCfg f a) (code := P')
        (hcode a.q (heads a.tapes) q writes moves hp)
      simpa only [step, mapCfg, multiTapeUpdate, heads] using he

theorem runs_map {Q : Type uDepth12} {R : Type uDepth13} (P : TapeMultiProgram Q) (P' : TapeMultiProgram R)
    (f : Q → R)
    (hcode : ∀ q h q' writes moves,
      P q h = some (q', writes, moves) →
      P' (f q) h = some (f q', writes, moves))
    {a b : TapeMultiCfg Q} {n : ℕ} (h : RunsIn P.step a b n) :
    RunsIn P'.step (mapCfg f a) (mapCfg f b) n :=
  h.map (mapCfg f) (step_map P P' f hcode)

end TapeMultiProgram
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound
namespace TapeRouting

open TapeMultiProgram

def joinCode {Q : Type uDepth1} {R : Type uDepth2} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (entry : Q → R) : TapeMultiProgram (Q ⊕ R)
  | .inl q, h =>
      match P q h with
      | none => jump (.inr (entry q)) h
      | some (q', writes, moves) => some (.inl q', writes, moves)
  | .inr r, h => (B r h).map fun out => (.inr out.1, out.2)

theorem join_runs {Q : Type uDepth3} {R : Type uDepth4} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (entry : Q → R) {q q' : Q} {r : R} {T U V : TapeTapes} {m n : ℕ}
    (hP : RunsIn P.step (cfg q T) (cfg q' U) m)
    (hhalt : P q' (heads U) = none)
    (hB : RunsIn B.step (cfg (entry q') U) (cfg r V) n) :
    RunsIn (joinCode P B entry).step (cfg (.inl q) T) (cfg (.inr r) V) (m + 1 + n) := by
  have hp := runs_map P (joinCode P B entry) Sum.inl (by
    intro a h a' writes moves he
    simp only [joinCode, he]) hP
  have hlink := RunsIn.single (step_jump (joinCode P B entry)
    (.inl q') (.inr (entry q')) U (by simp only [joinCode, hhalt]))
  have hb := runs_map B (joinCode P B entry) Sum.inr (by
    intro a h a' writes moves he
    simp only [joinCode, he, Option.map_some]) hB
  exact (hp.trans hlink).trans hb

theorem join_done {Q : Type uDepth5} {R : Type uDepth6} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (entry : Q → R) (r : R) (h : TapeHeads) (hh : B r h = none) :
    joinCode P B entry (.inr r) h = none := by
  simp only [joinCode, hh, Option.map_none]

abbrev LoopState (Q : Type uDepth7) (R : Type uDepth8) := (Q ⊕ R) ⊕ Unit

def loopTest {Q : Type uDepth9} {R : Type uDepth10} (q : Q) : LoopState Q R := .inl (.inl q)
def loopBody {Q : Type uDepth11} {R : Type uDepth12} (r : R) : LoopState Q R := .inl (.inr r)
def loopDone {Q : Type uDepth13} {R : Type uDepth14} : LoopState Q R := .inr ()

def loopCode {Q : Type uDepth15} {R : Type uDepth16} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (testEntry : Q) (bodyEntry : R) (again : Q → Bool) : TapeMultiProgram (LoopState Q R)
  | .inl (.inl q), h =>
      match P q h with
      | none => jump (if again q then loopBody bodyEntry else loopDone) h
      | some (q', writes, moves) => some (loopTest q', writes, moves)
  | .inl (.inr r), h =>
      match B r h with
      | none => jump (loopTest testEntry) h
      | some (r', writes, moves) => some (loopBody r', writes, moves)
  | .inr _, _ => none

theorem loop_test_runs {Q : Type uDepth17} {R : Type uDepth18} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (testEntry : Q) (bodyEntry : R) (again : Q → Bool)
    {q q' : Q} {T U : TapeTapes} {m : ℕ}
    (h : RunsIn P.step (cfg q T) (cfg q' U) m) :
    RunsIn (loopCode P B testEntry bodyEntry again).step
      (cfg (loopTest q) T) (cfg (loopTest q') U) m :=
  runs_map P _ loopTest (by
    intro a h a' writes moves he
    simp only [loopCode, loopTest, he]) h

theorem loop_body_runs {Q : Type uDepth19} {R : Type uDepth20} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (testEntry : Q) (bodyEntry : R) (again : Q → Bool)
    {r r' : R} {T U : TapeTapes} {m : ℕ}
    (h : RunsIn B.step (cfg r T) (cfg r' U) m) :
    RunsIn (loopCode P B testEntry bodyEntry again).step
      (cfg (loopBody r) T) (cfg (loopBody r') U) m :=
  runs_map B _ loopBody (by
    intro a h a' writes moves he
    simp only [loopCode, loopBody, he]) h

theorem loop_exit {Q : Type uDepth21} {R : Type uDepth22} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (testEntry : Q) (bodyEntry : R) (again : Q → Bool)
    {q : Q} {T U : TapeTapes} {m : ℕ}
    (h : RunsIn P.step (cfg testEntry T) (cfg q U) m)
    (hhalt : P q (heads U) = none) (hstop : again q = false) :
    RunsIn (loopCode P B testEntry bodyEntry again).step
      (cfg (loopTest testEntry) T) (cfg loopDone U) (m + 1) := by
  have ht := loop_test_runs P B testEntry bodyEntry again h
  have he := RunsIn.single (step_jump (loopCode P B testEntry bodyEntry again)
    (loopTest q) loopDone U (by simp [loopCode, loopTest, hhalt, hstop]))
  exact ht.trans he

theorem loop_iter {Q : Type uDepth23} {R : Type uDepth24} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (testEntry : Q) (bodyEntry : R) (again : Q → Bool)
    {q : Q} {r : R} {T U V : TapeTapes} {m n : ℕ}
    (hP : RunsIn P.step (cfg testEntry T) (cfg q U) m)
    (hPhalt : P q (heads U) = none) (hgo : again q = true)
    (hB : RunsIn B.step (cfg bodyEntry U) (cfg r V) n)
    (hBhalt : B r (heads V) = none) :
    RunsIn (loopCode P B testEntry bodyEntry again).step
      (cfg (loopTest testEntry) T) (cfg (loopTest testEntry) V) (m + 1 + n + 1) := by
  have hp := loop_test_runs P B testEntry bodyEntry again hP
  have hcall := RunsIn.single (step_jump (loopCode P B testEntry bodyEntry again)
    (loopTest q) (loopBody bodyEntry) U (by simp [loopCode, loopTest, hPhalt, hgo]))
  have hb := loop_body_runs P B testEntry bodyEntry again hB
  have hreturn := RunsIn.single (step_jump (loopCode P B testEntry bodyEntry again)
    (loopBody r) (loopTest testEntry) V (by simp [loopCode, loopBody, hBhalt]))
  exact ((hp.trans hcall).trans hb).trans hreturn

@[simp] theorem loop_done {Q : Type uDepth25} {R : Type uDepth26} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (testEntry : Q) (bodyEntry : R) (again : Q → Bool) (h : TapeHeads) :
    loopCode P B testEntry bodyEntry again loopDone h = none := rfl

end TapeRouting
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

open Turing TapeMultiProgram

namespace TapeUnary

def counterTape (n : ℕ) : Tape TapeSymbol := wordTape (List.replicate n true)

private theorem blank_singleton :
    ListBlank.mk [blankSymbol] = ListBlank.mk ([] : List TapeSymbol) := by
  exact Quotient.sound' (Or.inr (show BlankExtends [] [blankSymbol] from ⟨1, rfl⟩))

theorem prepend_home (bits : List Bool) (b : Bool) :
    (((wordTape bits).write (rawInputSymbol b)).move Dir.left).write
      (cleanAtom .home) = wordTape (b :: bits) := rfl

theorem remove_home (bits : List Bool) (b : Bool) :
    (((wordTape (b :: bits)).write blankSymbol).move Dir.right).write
      (cleanAtom .home) = wordTape bits := by
  change Tape.mk' (ListBlank.mk [blankSymbol])
      (ListBlank.mk (cleanAtom .home :: (encodeInput bits ++ [cleanAtom .endMark]))) = _
  rw [blank_singleton]
  rfl

inductive IncState where
  | start
  | newHome
  | done
  deriving DecidableEq

instance : Fintype IncState where
  elems := {.start, .newHome, .done}
  complete := by
    intro state
    cases state <;> simp

def incProgram (r : TapeRegister) : TapeMultiProgram IncState
  | .start, h => writeMove r (rawInputSymbol true) .left .newHome h
  | .newHome, h => writeMove r (cleanAtom .home) .stay .done h
  | .done, _ => none

theorem increment_word (r : TapeRegister) (T : TapeTapes) (bits : List Bool)
    (hT : T r = wordTape bits) :
    RunsIn (incProgram r).step (cfg IncState.start T)
      (cfg IncState.done (Function.update T r (wordTape (true :: bits)))) 2 := by
  let middle := ((T r).write (rawInputSymbol true)).move Dir.left
  have h₁ := step_writeMove (incProgram r) IncState.start IncState.newHome
    T r (rawInputSymbol true) HeadMove.left rfl
  have h₂ := step_writeMove (incProgram r) IncState.newHome IncState.done
    (Function.update T r middle) r (cleanAtom .home) HeadMove.stay rfl
  have hmiddle : middle.write (cleanAtom .home) = wordTape (true :: bits) := by
    dsimp [middle]
    rw [hT, prepend_home]
  have h₁' : (incProgram r).step (cfg IncState.start T) =
      some (cfg IncState.newHome (Function.update T r middle)) := h₁
  have h₂' : (incProgram r).step
      (cfg IncState.newHome (Function.update T r middle)) =
      some (cfg IncState.done (Function.update T r (wordTape (true :: bits)))) := by
    simpa only [Function.update_self, HeadMove.apply_stay, Function.update_idem,
      hmiddle] using h₂
  exact (RunsIn.single h₁').trans (RunsIn.single h₂')

theorem increment (r : TapeRegister) (T : TapeTapes) (n : ℕ)
    (hT : T r = counterTape n) :
    RunsIn (incProgram r).step (cfg IncState.start T)
      (cfg IncState.done (Function.update T r (counterTape (n + 1)))) 2 := by
  simpa only [counterTape, List.replicate_succ] using increment_word r T
    (List.replicate n true) hT

inductive DecState where
  | start
  | inspect
  | eraseHome
  | newHome
  | done (wasPositive : Bool)
  deriving DecidableEq, Fintype

def decProgram (r : TapeRegister) : TapeMultiProgram DecState
  | .start, h => move r .right .inspect h
  | .inspect, h =>
      if isAtom .endMark r h then move r .left (.done false) h
      else move r .left .eraseHome h
  | .eraseHome, h => writeMove r blankSymbol .right .newHome h
  | .newHome, h => writeMove r (cleanAtom .home) .stay (.done true) h
  | .done _, _ => none

theorem decrement_empty (r : TapeRegister) (T : TapeTapes)
    (hT : T r = wordTape []) :
    RunsIn (decProgram r).step (cfg DecState.start T) (cfg (DecState.done false) T) 2 := by
  let U := Function.update T r ((T r).move Dir.right)
  have h₁ := step_move (decProgram r) DecState.start DecState.inspect T r
    HeadMove.right rfl
  have hhead : isAtom .endMark r (heads U) = true := by
    simp [U, heads, isAtom, hT, wordTape_right]
  have h₂ := step_move (decProgram r) DecState.inspect (DecState.done false) U r
    HeadMove.left (by simp [decProgram, hhead])
  have h₁' : (decProgram r).step (cfg DecState.start T) =
      some (cfg DecState.inspect U) := h₁
  have h₂' : (decProgram r).step (cfg DecState.inspect U) =
      some (cfg (DecState.done false) T) := by
    simpa only [U, Function.update_self, HeadMove.apply_left,
      Tape.move_right_left, Function.update_idem, Function.update_eq_self] using h₂
  exact (RunsIn.single h₁').trans (RunsIn.single h₂')

theorem decrement_cons (r : TapeRegister) (T : TapeTapes) (bits : List Bool)
    (b : Bool) (hT : T r = wordTape (b :: bits)) :
    RunsIn (decProgram r).step (cfg DecState.start T)
      (cfg (DecState.done true) (Function.update T r (wordTape bits))) 4 := by
  let U := Function.update T r ((T r).move Dir.right)
  let middle := ((T r).write blankSymbol).move Dir.right
  have h₁ := step_move (decProgram r) DecState.start DecState.inspect T r
    HeadMove.right rfl
  have hhead : isAtom .endMark r (heads U) = false := by
    simp [U, heads, isAtom, hT, wordTape_right, rawInputSymbol, cleanAtom]
  have h₂ := step_move (decProgram r) DecState.inspect DecState.eraseHome U r
    HeadMove.left (by simp [decProgram, hhead])
  have h₃ := step_writeMove (decProgram r) DecState.eraseHome DecState.newHome
    T r blankSymbol HeadMove.right rfl
  have h₄ := step_writeMove (decProgram r) DecState.newHome (DecState.done true)
    (Function.update T r middle) r (cleanAtom .home) HeadMove.stay rfl
  have hmiddle : middle.write (cleanAtom .home) = wordTape bits := by
    dsimp [middle]
    rw [hT, remove_home]
  have h₁' : (decProgram r).step (cfg DecState.start T) =
      some (cfg DecState.inspect U) := h₁
  have h₂' : (decProgram r).step (cfg DecState.inspect U) =
      some (cfg DecState.eraseHome T) := by
    simpa only [U, Function.update_self, HeadMove.apply_left,
      Tape.move_right_left, Function.update_idem, Function.update_eq_self] using h₂
  have h₃' : (decProgram r).step (cfg DecState.eraseHome T) =
      some (cfg DecState.newHome (Function.update T r middle)) := h₃
  have h₄' : (decProgram r).step (cfg DecState.newHome (Function.update T r middle)) =
      some (cfg (DecState.done true) (Function.update T r (wordTape bits))) := by
    simpa only [Function.update_self, HeadMove.apply_stay, Function.update_idem,
      hmiddle] using h₄
  exact ((RunsIn.single h₁').trans (RunsIn.single h₂')).trans
    ((RunsIn.single h₃').trans (RunsIn.single h₄'))

theorem decrement (r : TapeRegister) (T : TapeTapes) (n : ℕ)
    (hT : T r = counterTape n) :
    RunsIn (decProgram r).step (cfg DecState.start T)
      (cfg (DecState.done (decide (0 < n)))
        (Function.update T r (counterTape (n - 1)))) 4 := by
  cases n with
  | zero =>
      have h := (decrement_empty r T hT).mono (by decide : 2 ≤ 4)
      simpa only [Nat.zero_sub, Nat.lt_irrefl, decide_false, ← hT,
        Function.update_eq_self] using h
  | succ n =>
      simpa only [counterTape, List.replicate_succ, Nat.succ_sub_one,
        Nat.succ_pos, decide_true] using
        decrement_cons r T (List.replicate n true) true hT

end TapeUnary
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound
namespace TapeCopy

open Turing TapeMultiProgram

inductive State where
  | start
  | scan
  | rewind
  | done
  deriving DecidableEq, Inhabited

instance : Fintype State where
  elems := {.start, .scan, .rewind, .done}
  complete := by
    intro state
    cases state <;> simp

def onPair {α : Type uDepth1} (src dst : TapeRegister) (base : TapeRegister → α)
    (s d : α) : TapeRegister → α :=
  fun r => if r = src then s else if r = dst then d else base r

@[simp] theorem onPair_src {α : Type uDepth2} (src dst : TapeRegister)
    (base : TapeRegister → α) (s d : α) : onPair src dst base s d src = s := by
  simp [onPair]

@[simp] theorem onPair_dst {α : Type uDepth3} {src dst : TapeRegister} (hne : src ≠ dst)
    (base : TapeRegister → α) (s d : α) : onPair src dst base s d dst = d := by
  simp [onPair, Ne.symm hne]

theorem onPair_other {α : Type uDepth4} (src dst : TapeRegister)
    (base : TapeRegister → α) (s d : α) (r : TapeRegister)
    (hs : r ≠ src) (hd : r ≠ dst) : onPair src dst base s d r = base r := by
  simp [onPair, hs, hd]

def emit {Q : Type uDepth5} (src dst : TapeRegister) (q : Q) (h : TapeHeads)
    (s d : TapeSymbol) (m : HeadMove) : Option (Q × TapeHeads × TapeMoves) :=
  some (q, onPair src dst h s d, onPair src dst stayMoves m m)

def code (src dst : TapeRegister) : TapeMultiProgram State
  | .start, h => emit src dst .scan h (h src) (h dst) .right
  | .scan, h =>
      match (h src).1 with
      | .bit b => emit src dst .scan h (h src) (rawInputSymbol b) .right
      | .endMark => emit src dst .rewind h (h src) (cleanAtom .endMark) .stay
      | _ => none
  | .rewind, h =>
      if (h src).1 = .home then emit src dst .done h (h src) (h dst) .stay
      else emit src dst .rewind h (h src) (h dst) .left
  | .done, _ => none

theorem step_emit {Q : Type uDepth6} (P : TapeMultiProgram Q)
    {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (q q' : Q)
    (s d : TapeSymbol) (m : HeadMove)
    (h : P q (heads (onPair src dst T S D)) =
      emit src dst q' (heads (onPair src dst T S D)) s d m) :
    P.step (cfg q (onPair src dst T S D)) =
      some (cfg q' (onPair src dst T (m.apply (S.write s)) (m.apply (D.write d)))) := by
  have he := multiTapeStep_eq_some (c := cfg q (onPair src dst T S D))
    (code := P) h
  change P.step (cfg q (onPair src dst T S D)) =
    some (multiTapeUpdate (cfg q (onPair src dst T S D)) q'
      (onPair src dst (heads (onPair src dst T S D)) s d)
      (onPair src dst stayMoves m m)) at he
  rw [he]
  congr 1
  apply congrArg (cfg q')
  funext r
  by_cases hs : r = src
  · subst r
    simp [cfg, onPair]
  · by_cases hd : r = dst
    · subst r
      simp [cfg, onPair, Ne.symm hne]
    · simp [cfg, onPair, heads, stayMoves, hs, hd]

theorem step_start {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) :
    (code src dst).step (cfg .start (onPair src dst T S D)) =
      some (cfg .scan (onPair src dst T (S.move .right) (D.move .right))) := by
  have h := step_emit (code src dst) hne T S D .start .scan S.head D.head .right
    (by simp [code, heads, hne])
  simpa only [Tape.write_self, HeadMove.apply_right] using h

theorem step_scan_bit {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (b : Bool)
    (hS : S.head = rawInputSymbol b) :
    (code src dst).step (cfg .scan (onPair src dst T S D)) =
      some (cfg .scan (onPair src dst T (S.move .right)
        ((D.write (rawInputSymbol b)).move .right))) := by
  have h := step_emit (code src dst) hne T S D .scan .scan S.head (rawInputSymbol b) .right
    (by simp [code, heads, hS, rawInputSymbol, cleanAtom])
  simpa only [Tape.write_self, HeadMove.apply_right] using h

theorem step_scan_end {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (hS : S.head = cleanAtom .endMark) :
    (code src dst).step (cfg .scan (onPair src dst T S D)) =
      some (cfg .rewind (onPair src dst T S (D.write (cleanAtom .endMark)))) := by
  have h := step_emit (code src dst) hne T S D .scan .rewind S.head (cleanAtom .endMark) .stay
    (by simp [code, heads, hS, cleanAtom])
  simpa only [Tape.write_self, HeadMove.apply_stay] using h

theorem step_rewind_move {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (hS : S.head.1 ≠ .home) :
    (code src dst).step (cfg .rewind (onPair src dst T S D)) =
      some (cfg .rewind (onPair src dst T (S.move .left) (D.move .left))) := by
  have h := step_emit (code src dst) hne T S D .rewind .rewind S.head D.head .left
    (by simp [code, heads, hne, hS])
  simpa only [Tape.write_self, HeadMove.apply_left] using h

theorem step_rewind_home {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (hS : S.head.1 = .home) :
    (code src dst).step (cfg .rewind (onPair src dst T S D)) =
      some (cfg .done (onPair src dst T S D)) := by
  have h := step_emit (code src dst) hne T S D .rewind .done S.head D.head .stay
    (by simp [code, heads, hne, hS])
  simpa only [Tape.write_self, HeadMove.apply_stay] using h

theorem write_mk₂ (L R : List TapeSymbol) (a : TapeSymbol) :
    (Tape.mk₂ L R).write a = Tape.mk₂ L (a :: R.tail) := by
  cases R <;> rfl

theorem runs_scan {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (bits : List Bool) (L R : List TapeSymbol) (hR : R.tail = []) :
    RunsIn (code src dst).step
      (cfg .scan (onPair src dst T
        (Tape.mk₂ L (encodeInput bits ++ [cleanAtom .endMark])) (Tape.mk₂ L R)))
      (cfg .rewind (onPair src dst T
        (Tape.mk₂ ((encodeInput bits).reverse ++ L) [cleanAtom .endMark])
        (Tape.mk₂ ((encodeInput bits).reverse ++ L) [cleanAtom .endMark])))
      (bits.length + 1) := by
  induction bits generalizing L R with
  | nil =>
      have h := RunsIn.single (step_scan_end hne T
        (Tape.mk₂ L [cleanAtom .endMark]) (Tape.mk₂ L R) rfl)
      simpa only [encodeInput, List.map_nil, List.nil_append, List.reverse_nil,
        List.length_nil, Nat.zero_add, write_mk₂, hR] using h
  | cons b bits ih =>
      have hfirst := RunsIn.single (step_scan_bit hne T
        (Tape.mk₂ L (rawInputSymbol b :: (encodeInput bits ++ [cleanAtom .endMark])))
        (Tape.mk₂ L R) b rfl)
      have hrest := ih (rawInputSymbol b :: L) [] rfl
      simp only [write_mk₂, TapeWord.move_right_mk₂_cons, hR] at hfirst
      have hboth := hfirst.trans hrest
      simpa only [encodeInput, List.map_cons, List.cons_append, List.reverse_cons,
        List.append_assoc, List.nil_append, List.length_cons, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hboth

theorem runs_rewind {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (bits : List Bool) (a : TapeSymbol) (R : List TapeSymbol)
    (ha : a.1 ≠ .home) :
    RunsIn (code src dst).step
      (cfg .rewind (onPair src dst T
        (Tape.mk₂ (encodeInput bits ++ [cleanAtom .home]) (a :: R))
        (Tape.mk₂ (encodeInput bits ++ [cleanAtom .home]) (a :: R))))
      (cfg .done (onPair src dst T
        (Tape.mk₂ [] (cleanAtom .home :: ((encodeInput bits).reverse ++ a :: R)))
        (Tape.mk₂ [] (cleanAtom .home :: ((encodeInput bits).reverse ++ a :: R)))))
      (bits.length + 2) := by
  induction bits generalizing a R with
  | nil =>
      have hfirst := RunsIn.single (step_rewind_move hne T
        (Tape.mk₂ [cleanAtom .home] (a :: R))
        (Tape.mk₂ [cleanAtom .home] (a :: R)) ha)
      simp only [TapeWord.move_left_mk₂_cons] at hfirst
      have hlast := RunsIn.single (step_rewind_home hne T
        (Tape.mk₂ [] (cleanAtom .home :: a :: R))
        (Tape.mk₂ [] (cleanAtom .home :: a :: R)) rfl)
      simpa only [encodeInput, List.map_nil, List.nil_append, List.reverse_nil,
        List.length_nil, Nat.zero_add] using hfirst.trans hlast
  | cons b bits ih =>
      have hfirst := RunsIn.single (step_rewind_move hne T
        (Tape.mk₂ (rawInputSymbol b :: (encodeInput bits ++ [cleanAtom .home])) (a :: R))
        (Tape.mk₂ (rawInputSymbol b :: (encodeInput bits ++ [cleanAtom .home])) (a :: R)) ha)
      simp only [TapeWord.move_left_mk₂_cons] at hfirst
      have hrest := ih (rawInputSymbol b) (a :: R) (by simp [rawInputSymbol, cleanAtom])
      simpa only [encodeInput, List.map_cons, List.cons_append, List.reverse_cons,
        List.append_assoc, List.nil_append, List.length_cons, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hfirst.trans hrest

theorem runs_copy {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (bits : List Bool) :
    RunsIn (code src dst).step
      (cfg .start (onPair src dst T (wordTape bits) (wordTape [])))
      (cfg .done (onPair src dst T (wordTape bits) (wordTape bits)))
      (2 * bits.length + 4) := by
  have hstart := RunsIn.single (step_start hne T (wordTape bits) (wordTape []))
  have hscan := runs_scan hne T bits [cleanAtom .home] [cleanAtom .endMark] rfl
  have hback := runs_rewind hne T bits.reverse (cleanAtom .endMark) [] (by simp [cleanAtom])
  have hreverse : encodeInput bits.reverse = (encodeInput bits).reverse := by
    simp [encodeInput]
  simp only [hreverse, List.reverse_reverse, List.length_reverse] at hback
  have hstart' : RunsIn (code src dst).step
      (cfg .start (onPair src dst T (wordTape bits) (wordTape [])))
      (cfg .scan (onPair src dst T
        (Tape.mk₂ [cleanAtom .home] (encodeInput bits ++ [cleanAtom .endMark]))
        (Tape.mk₂ [cleanAtom .home] [cleanAtom .endMark]))) 1 := by
    simpa only [wordTape_right, cursorTape, encodeInput, List.map_nil,
      List.reverse_nil, List.nil_append] using hstart
  have hboth := (hstart'.trans hscan).trans hback
  simpa only [wordTape, Tape.mk₁, Nat.two_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hboth

@[simp] theorem step_done (src dst : TapeRegister) (T : TapeTapes) :
    (code src dst).step (cfg .done T) = none := rfl

end TapeCopy
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound
namespace TapeArithmetic

open TapeMultiProgram TapeRouting TapeUnary TapeCopy

theorem update_onPair_src {α : Type uDepth1} (src dst : TapeRegister)
    (T : TapeRegister → α) (s d s' : α) :
    Function.update (onPair src dst T s d) src s' = onPair src dst T s' d := by
  funext r
  by_cases h : r = src
  · subst r
    simp
  · simp [Function.update, onPair, h]

theorem update_onPair_dst {α : Type uDepth2} {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeRegister → α) (s d d' : α) :
    Function.update (onPair src dst T s d) dst d' = onPair src dst T s d' := by
  funext r
  by_cases hs : r = src
  · subst r
    simp [Function.update, onPair, hne]
  · by_cases hd : r = dst
    · subst r
      simp [Function.update, onPair, Ne.symm hne]
    · simp [Function.update, onPair, hs, hd]

def decPositive : DecState → Bool
  | .done b => b
  | _ => false

abbrev AddState := LoopState DecState IncState

def addProgram (counter destination : TapeRegister) : TapeMultiProgram AddState :=
  loopCode (decProgram counter) (incProgram destination)
    DecState.start IncState.start decPositive

def addStart : AddState := loopTest DecState.start
def addDone : AddState := loopDone

theorem runs_add {counter destination : TapeRegister} (hne : counter ≠ destination)
    (T : TapeTapes) (n m : ℕ) :
    RunsIn (addProgram counter destination).step
      (cfg addStart (onPair counter destination T (counterTape n) (counterTape m)))
      (cfg addDone (onPair counter destination T (counterTape 0) (counterTape (m + n))))
      (8 * n + 3) := by
  induction n generalizing m with
  | zero =>
      have hdec := decrement_empty counter
        (onPair counter destination T (counterTape 0) (counterTape m)) (by
          simp [counterTape])
      have he := loop_exit (decProgram counter) (incProgram destination)
        DecState.start IncState.start decPositive hdec rfl rfl
      simpa only [addProgram, addStart, addDone, Nat.mul_zero, Nat.zero_add,
        Nat.add_zero] using he
  | succ n ih =>
      have hdec := decrement_cons counter
        (onPair counter destination T (counterTape (n + 1)) (counterTape m))
        (List.replicate n true) true (by simp [counterTape, List.replicate_succ])
      simp only [update_onPair_src] at hdec
      have hinc := increment destination
        (onPair counter destination T (counterTape n) (counterTape m)) m (by
          simp [hne])
      simp only [update_onPair_dst hne] at hinc
      have hit := loop_iter (decProgram counter) (incProgram destination)
        DecState.start IncState.start decPositive hdec rfl rfl hinc rfl
      have hrest := ih (m + 1)
      have hall := hit.trans hrest
      have hacc : m + 1 + n = m + (n + 1) := by omega
      have htime : 4 + 1 + 2 + 1 + (8 * n + 3) = 8 * (n + 1) + 3 := by omega
      simpa only [addProgram, addStart, addDone, hacc, htime] using hall

@[simp] theorem add_done (counter destination : TapeRegister) (h : TapeHeads) :
    addProgram counter destination addDone h = none := rfl

end TapeArithmetic
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeMultiply

open TapeMultiProgram TapeRouting TapeUnary TapeCopy TapeArithmetic

def tapes (outer source scratch destination : TapeRegister) (T : TapeTapes)
    (n m k z : ℕ) : TapeTapes :=
  onPair outer source (onPair scratch destination T (counterTape k) (counterTape z))
    (counterTape n) (counterTape m)

@[simp] theorem tapes_outer (outer source scratch destination : TapeRegister)
    (T : TapeTapes) (n m k z : ℕ) :
    tapes outer source scratch destination T n m k z outer = counterTape n := by
  simp [tapes]

@[simp] theorem tapes_source {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (T : TapeTapes) (n m k z : ℕ) :
    tapes outer source scratch destination T n m k z source = counterTape m := by
  simp [tapes, hos]

@[simp] theorem tapes_scratch {outer source scratch destination : TapeRegister}
    (hoc : outer ≠ scratch) (hsc : source ≠ scratch) (T : TapeTapes) (n m k z : ℕ) :
    tapes outer source scratch destination T n m k z scratch = counterTape k := by
  simp [tapes, onPair, Ne.symm hoc, Ne.symm hsc]

@[simp] theorem tapes_destination {outer source scratch destination : TapeRegister}
    (hod : outer ≠ destination) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (T : TapeTapes) (n m k z : ℕ) :
    tapes outer source scratch destination T n m k z destination = counterTape z := by
  simp [tapes, onPair, Ne.symm hod, Ne.symm hsd, Ne.symm hcd]

theorem tapes_other (outer source scratch destination : TapeRegister)
    (T : TapeTapes) (n m k z : ℕ) (r : TapeRegister)
    (ho : r ≠ outer) (hs : r ≠ source) (hc : r ≠ scratch) (hd : r ≠ destination) :
    tapes outer source scratch destination T n m k z r = T r := by
  simp [tapes, onPair, ho, hs, hc, hd]

private theorem update_outer (outer source scratch destination : TapeRegister)
    (T : TapeTapes) (n m k z n' : ℕ) :
    Function.update (tapes outer source scratch destination T n m k z) outer
      (counterTape n') = tapes outer source scratch destination T n' m k z := by
  exact update_onPair_src outer source
    (onPair scratch destination T (counterTape k) (counterTape z))
    (counterTape n) (counterTape m) (counterTape n')

private theorem overlay_source_scratch {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hsc : source ≠ scratch)
    (T : TapeTapes) (n m k z m' k' : ℕ) :
    onPair source scratch (tapes outer source scratch destination T n m k z)
      (counterTape m') (counterTape k') =
      tapes outer source scratch destination T n m' k' z := by
  funext r
  by_cases ho : r = outer
  · subst r
    simp [tapes, onPair, hos, hoc]
  · by_cases hs : r = source
    · subst r
      simp [tapes, onPair, Ne.symm hos]
    · by_cases hc : r = scratch
      · subst r
        simp [tapes, onPair, Ne.symm hoc, Ne.symm hsc]
      · simp [tapes, onPair, ho, hs, hc]

private theorem overlay_scratch_destination {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination)
    (T : TapeTapes) (n m k z k' z' : ℕ) :
    onPair scratch destination (tapes outer source scratch destination T n m k z)
      (counterTape k') (counterTape z') =
      tapes outer source scratch destination T n m k' z' := by
  funext r
  by_cases ho : r = outer
  · subst r
    simp [tapes, onPair, hoc, hod]
  · by_cases hs : r = source
    · subst r
      simp [tapes, onPair, Ne.symm hos, hsc, hsd]
    · by_cases hc : r = scratch
      · subst r
        simp [tapes, onPair, Ne.symm hoc, Ne.symm hsc]
      · by_cases hd : r = destination <;>
          simp [tapes, onPair, ho, hs, hc, hd, Ne.symm hod, Ne.symm hsd]

abbrev BodyState := TapeCopy.State ⊕ AddState

def bodyProgram (source scratch destination : TapeRegister) : TapeMultiProgram BodyState :=
  joinCode (TapeCopy.code source scratch) (addProgram scratch destination)
    (fun _ => addStart)

def bodyStart : BodyState := .inl .start
def bodyDone : BodyState := .inr addDone

theorem runs_body {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (T : TapeTapes) (n m z : ℕ) :
    RunsIn (bodyProgram source scratch destination).step
      (cfg bodyStart (tapes outer source scratch destination T n m 0 z))
      (cfg bodyDone (tapes outer source scratch destination T n m 0 (z + m)))
      (10 * m + 8) := by
  have hcopy := runs_copy hsc (tapes outer source scratch destination T n m 0 z)
    (List.replicate m true)
  simp only [List.length_replicate] at hcopy
  change RunsIn (TapeCopy.code source scratch).step
    (cfg TapeCopy.State.start (onPair source scratch
      (tapes outer source scratch destination T n m 0 z) (counterTape m) (counterTape 0)))
    (cfg TapeCopy.State.done (onPair source scratch
      (tapes outer source scratch destination T n m 0 z) (counterTape m) (counterTape m)))
    (2 * m + 4) at hcopy
  simp only [overlay_source_scratch hos hoc hsc] at hcopy
  have hadd := runs_add hcd (tapes outer source scratch destination T n m m z) m z
  simp only [overlay_scratch_destination hos hoc hod hsc hsd] at hadd
  have h := join_runs (TapeCopy.code source scratch) (addProgram scratch destination)
    (fun _ => addStart) hcopy rfl hadd
  have htime : 2 * m + 4 + 1 + (8 * m + 3) = 10 * m + 8 := by omega
  simpa only [bodyProgram, bodyStart, bodyDone, htime] using h

@[simp] theorem body_done (source scratch destination : TapeRegister) (h : TapeHeads) :
    bodyProgram source scratch destination bodyDone h = none := rfl

abbrev State := LoopState DecState BodyState

def program (outer source scratch destination : TapeRegister) : TapeMultiProgram State :=
  loopCode (decProgram outer) (bodyProgram source scratch destination)
    DecState.start bodyStart decPositive

def start : State := loopTest DecState.start
def done : State := loopDone

theorem runs_mul {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (T : TapeTapes) (n m z : ℕ) :
    RunsIn (program outer source scratch destination).step
      (cfg start (tapes outer source scratch destination T n m 0 z))
      (cfg done (tapes outer source scratch destination T 0 m 0 (z + n * m)))
      (n * (10 * m + 14) + 3) := by
  induction n generalizing z with
  | zero =>
      have hdec := decrement_empty outer
        (tapes outer source scratch destination T 0 m 0 z) (by simp [counterTape])
      have h := loop_exit (decProgram outer) (bodyProgram source scratch destination)
        DecState.start bodyStart decPositive hdec rfl rfl
      simpa only [program, start, done, Nat.zero_mul, Nat.add_zero, Nat.zero_add] using h
  | succ n ih =>
      have hdec := decrement_cons outer
        (tapes outer source scratch destination T (n + 1) m 0 z)
        (List.replicate n true) true (by simp [counterTape, List.replicate_succ])
      change RunsIn (decProgram outer).step
        (cfg DecState.start (tapes outer source scratch destination T (n + 1) m 0 z))
        (cfg (DecState.done true) (Function.update
          (tapes outer source scratch destination T (n + 1) m 0 z) outer (counterTape n)))
        4 at hdec
      simp only [update_outer] at hdec
      have hbody := runs_body hos hoc hod hsc hsd hcd T n m z
      have hit := loop_iter (decProgram outer) (bodyProgram source scratch destination)
        DecState.start bodyStart decPositive hdec rfl rfl hbody rfl
      have hall := hit.trans (ih (z + m))
      have hacc : z + m + n * m = z + (n + 1) * m := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have htime : 4 + 1 + (10 * m + 8) + 1 + (n * (10 * m + 14) + 3) =
          (n + 1) * (10 * m + 14) + 3 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [program, start, done, hacc, htime] using hall

@[simp] theorem program_done (outer source scratch destination : TapeRegister) (h : TapeHeads) :
    program outer source scratch destination done h = none := rfl

end TapeMultiply
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapePower

open TapeMultiProgram TapeRouting TapeUnary TapeCopy
open scoped BigOperators

def State : ℕ → Type
  | 0 => Unit
  | k + 1 => TapeMultiply.State ⊕ State k

instance (k : ℕ) : Fintype (State k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih =>
      change Fintype (TapeMultiply.State ⊕ State k)
      letI := ih
      infer_instance

def start : (k : ℕ) → State k
  | 0 => ()
  | _ + 1 => .inl TapeMultiply.start

def done : (k : ℕ) → State k
  | 0 => ()
  | k + 1 => .inr (done k)

def program : (k : ℕ) → (outer source scratch destination : TapeRegister) →
    TapeMultiProgram (State k)
  | 0, _, _, _, _ => fun _ _ => none
  | k + 1, outer, source, scratch, destination =>
      joinCode (TapeMultiply.program outer source scratch destination)
        (program k destination source scratch outer) (fun _ => start k)

def resultTapes : ℕ → TapeRegister → TapeRegister → TapeRegister → TapeRegister →
    TapeTapes → ℕ → ℕ → TapeTapes
  | 0, outer, source, scratch, destination, T, n, m =>
      TapeMultiply.tapes outer source scratch destination T n m 0 0
  | k + 1, outer, source, scratch, destination, T, n, m =>
      resultTapes k destination source scratch outer T (n * m) m

def resultRegister : ℕ → TapeRegister → TapeRegister → TapeRegister
  | 0, outer, _ => outer
  | k + 1, outer, destination => resultRegister k destination outer

def cost : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, n, m => n * (10 * m + 14) + 3 + 1 + cost k (n * m) m

private theorem swap_tapes {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (T : TapeTapes) (n m : ℕ) :
    TapeMultiply.tapes outer source scratch destination T 0 m 0 n =
      TapeMultiply.tapes destination source scratch outer T n m 0 0 := by
  funext r
  by_cases ho : r = outer
  · subst r
    simp [TapeMultiply.tapes, onPair, hos, hoc, hod]
  · by_cases hs : r = source
    · subst r
      simp [TapeMultiply.tapes, onPair, Ne.symm hos, hsd]
    · by_cases hc : r = scratch
      · subst r
        simp [TapeMultiply.tapes, onPair, Ne.symm hoc, Ne.symm hsc, hcd]
      · by_cases hd : r = destination
        · subst r
          simp [TapeMultiply.tapes, onPair, Ne.symm hod, Ne.symm hsd, Ne.symm hcd]
        · simp [TapeMultiply.tapes, onPair, ho, hs, hc, hd]

theorem runs_power (k : ℕ) {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (T : TapeTapes) (n m : ℕ) :
    RunsIn (program k outer source scratch destination).step
      (cfg (start k) (TapeMultiply.tapes outer source scratch destination T n m 0 0))
      (cfg (done k) (resultTapes k outer source scratch destination T n m))
      (cost k n m) := by
  induction k generalizing outer source scratch destination n with
  | zero => exact RunsIn.refl _ _
  | succ k ih =>
      have hm := TapeMultiply.runs_mul hos hoc hod hsc hsd hcd T n m 0
      simp only [Nat.zero_add, swap_tapes hos hoc hod hsc hsd hcd] at hm
      have hr := ih (Ne.symm hsd) (Ne.symm hcd) (Ne.symm hod)
        hsc (Ne.symm hos) (Ne.symm hoc) (n * m)
      have h := join_runs (TapeMultiply.program outer source scratch destination)
        (program k destination source scratch outer) (fun _ => start k)
        hm rfl hr
      exact h

theorem program_done (k : ℕ) (outer source scratch destination : TapeRegister)
    (h : TapeHeads) : program k outer source scratch destination (done k) h = none := by
  induction k generalizing outer source scratch destination with
  | zero => rfl
  | succ k ih =>
      exact join_done _ _ _ (done k) h (ih destination source scratch outer)

theorem resultTapes_result (k : ℕ)
    (outer source scratch destination : TapeRegister) (T : TapeTapes) (n m : ℕ) :
    resultTapes k outer source scratch destination T n m
      (resultRegister k outer destination) = counterTape (n * m ^ k) := by
  induction k generalizing outer destination n with
  | zero => simp [resultTapes, resultRegister]
  | succ k ih =>
      rw [resultTapes, resultRegister, ih]
      congr 1
      rw [pow_succ]
      ring

theorem resultTapes_source (k : ℕ) {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hsd : source ≠ destination)
    (T : TapeTapes) (n m : ℕ) :
    resultTapes k outer source scratch destination T n m source = counterTape m := by
  induction k generalizing outer destination n with
  | zero => exact TapeMultiply.tapes_source hos T n m 0 0
  | succ k ih => exact ih (Ne.symm hsd) (Ne.symm hos) (n * m)

theorem resultTapes_scratch (k : ℕ) {outer source scratch destination : TapeRegister}
    (hoc : outer ≠ scratch) (hsc : source ≠ scratch) (hcd : scratch ≠ destination)
    (T : TapeTapes) (n m : ℕ) :
    resultTapes k outer source scratch destination T n m scratch = counterTape 0 := by
  induction k generalizing outer destination n with
  | zero => exact TapeMultiply.tapes_scratch hoc hsc T n m 0 0
  | succ k ih => exact ih (Ne.symm hcd) (Ne.symm hoc) (n * m)

theorem resultTapes_other (k : ℕ)
    (outer source scratch destination : TapeRegister) (T : TapeTapes) (n m : ℕ)
    (r : TapeRegister) (ho : r ≠ outer) (hs : r ≠ source)
    (hc : r ≠ scratch) (hd : r ≠ destination) :
    resultTapes k outer source scratch destination T n m r = T r := by
  induction k generalizing outer destination n with
  | zero => exact TapeMultiply.tapes_other _ _ _ _ _ _ _ _ _ _ ho hs hc hd
  | succ k ih => exact ih destination outer (n * m) hd ho

theorem cost_eq_sum (k n m : ℕ) :
    cost k n m = n * (10 * m + 14) * (∑ j ∈ Finset.range k, m ^ j) + 4 * k := by
  induction k generalizing n with
  | zero => simp [cost]
  | succ k ih =>
      rw [cost, ih, Finset.sum_range_succ']
      simp only [pow_zero, pow_succ]
      rw [← Finset.sum_mul]
      ring

end TapePower
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeErase

open Turing TapeMultiProgram

inductive State where
  | start
  | scan
  | erase
  | install
  | done
  deriving DecidableEq, Inhabited

instance : Fintype State where
  elems := {.start, .scan, .erase, .install, .done}
  complete := by
    intro state
    cases state <;> simp

def code (r : TapeRegister) : TapeMultiProgram State
  | .start, h => move r .right .scan h
  | .scan, h =>
      match (h r).1 with
      | .bit _ => move r .right .scan h
      | .endMark => jump .erase h
      | _ => none
  | .erase, h =>
      if (h r).1 = .home then move r .right .install h
      else writeMove r blankSymbol .left .erase h
  | .install, h => writeMove r (cleanAtom .endMark) .left .done h
  | .done, _ => none

theorem step_start (r : TapeRegister) (T : TapeTapes) (S : Tape TapeSymbol) :
    (code r).step (cfg .start (Function.update T r S)) =
      some (cfg .scan (Function.update T r (S.move .right))) := by
  have h := TapeMultiProgram.step_move (code r) .start .scan (Function.update T r S)
    r .right (by rfl)
  simpa only [Function.update_self, Function.update_idem, HeadMove.apply_right] using h

theorem step_scan_bit (r : TapeRegister) (T : TapeTapes) (S : Tape TapeSymbol)
    (b : Bool) (hS : S.head = rawInputSymbol b) :
    (code r).step (cfg .scan (Function.update T r S)) =
      some (cfg .scan (Function.update T r (S.move .right))) := by
  have h := TapeMultiProgram.step_move (code r) .scan .scan (Function.update T r S)
    r .right (by simp [code, heads, hS, rawInputSymbol, cleanAtom])
  simpa only [Function.update_self, Function.update_idem, HeadMove.apply_right] using h

theorem step_scan_end (r : TapeRegister) (T : TapeTapes) (S : Tape TapeSymbol)
    (hS : S.head = cleanAtom .endMark) :
    (code r).step (cfg .scan (Function.update T r S)) =
      some (cfg .erase (Function.update T r S)) := by
  exact TapeMultiProgram.step_jump (code r) .scan .erase (Function.update T r S)
    (by simp [code, heads, hS, cleanAtom])

theorem step_erase_symbol (r : TapeRegister) (T : TapeTapes) (S : Tape TapeSymbol)
    (hS : S.head.1 ≠ .home) :
    (code r).step (cfg .erase (Function.update T r S)) =
      some (cfg .erase (Function.update T r ((S.write blankSymbol).move .left))) := by
  have h := TapeMultiProgram.step_writeMove (code r) .erase .erase
    (Function.update T r S) r blankSymbol .left (by simp [code, heads, hS])
  simpa only [Function.update_self, Function.update_idem, HeadMove.apply_left] using h

theorem step_erase_home (r : TapeRegister) (T : TapeTapes) (S : Tape TapeSymbol)
    (hS : S.head.1 = .home) :
    (code r).step (cfg .erase (Function.update T r S)) =
      some (cfg .install (Function.update T r (S.move .right))) := by
  have h := TapeMultiProgram.step_move (code r) .erase .install
    (Function.update T r S) r .right (by simp [code, heads, hS])
  simpa only [Function.update_self, Function.update_idem, HeadMove.apply_right] using h

theorem step_install (r : TapeRegister) (T : TapeTapes) (S : Tape TapeSymbol) :
    (code r).step (cfg .install (Function.update T r S)) =
      some (cfg .done (Function.update T r
        ((S.write (cleanAtom .endMark)).move .left))) := by
  have h := TapeMultiProgram.step_writeMove (code r) .install .done
    (Function.update T r S) r (cleanAtom .endMark) .left (by rfl)
  simpa only [Function.update_self, Function.update_idem, HeadMove.apply_left] using h

theorem mk₂_append_blanks (L R : List TapeSymbol) (n : ℕ) :
    Tape.mk₂ L (R ++ List.replicate n blankSymbol) = Tape.mk₂ L R := by
  have h : ListBlank.mk (R ++ List.replicate n blankSymbol) = ListBlank.mk R := by
    apply Quotient.sound'
    exact Or.inr ⟨n, by simp only [default_tapeSymbol]⟩
  exact congrArg (Tape.mk' (ListBlank.mk L)) h

theorem runs_scan (r : TapeRegister) (T : TapeTapes) (bits : List Bool)
    (L : List TapeSymbol) :
    RunsIn (code r).step
      (cfg .scan (Function.update T r
        (Tape.mk₂ L (encodeInput bits ++ [cleanAtom .endMark]))))
      (cfg .erase (Function.update T r
        (Tape.mk₂ ((encodeInput bits).reverse ++ L) [cleanAtom .endMark])))
      (bits.length + 1) := by
  induction bits generalizing L with
  | nil =>
      have h := RunsIn.single (step_scan_end r T (Tape.mk₂ L [cleanAtom .endMark]) rfl)
      simpa only [encodeInput, List.map_nil, List.nil_append, List.reverse_nil,
        List.length_nil, Nat.zero_add] using h
  | cons b bits ih =>
      have hfirst := RunsIn.single (step_scan_bit r T
        (Tape.mk₂ L (rawInputSymbol b :: (encodeInput bits ++ [cleanAtom .endMark]))) b rfl)
      simp only [TapeWord.move_right_mk₂_cons] at hfirst
      have hrest := ih (rawInputSymbol b :: L)
      simpa only [encodeInput, List.map_cons, List.cons_append, List.reverse_cons,
        List.append_assoc, List.nil_append, List.length_cons, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hfirst.trans hrest

theorem runs_finish (r : TapeRegister) (T : TapeTapes) (n : ℕ) :
    RunsIn (code r).step
      (cfg .erase (Function.update T r
        (Tape.mk₂ [] (cleanAtom .home :: blankSymbol :: List.replicate n blankSymbol))))
      (cfg .done (Function.update T r (wordTape []))) 2 := by
  have hfirst := RunsIn.single (step_erase_home r T
    (Tape.mk₂ [] (cleanAtom .home :: blankSymbol :: List.replicate n blankSymbol)) rfl)
  simp only [TapeWord.move_right_mk₂_cons] at hfirst
  have hlast := RunsIn.single (step_install r T
    (Tape.mk₂ [cleanAtom .home] (blankSymbol :: List.replicate n blankSymbol)))
  simp only [TapeCopy.write_mk₂, List.tail_cons, TapeWord.move_left_mk₂_cons] at hlast
  have ht : Tape.mk₂ [] (cleanAtom .home :: cleanAtom .endMark ::
      List.replicate n blankSymbol) = wordTape [] := by
    exact mk₂_append_blanks [] [cleanAtom .home, cleanAtom .endMark] n
  rw [ht] at hlast
  exact hfirst.trans hlast

theorem runs_erase_back (r : TapeRegister) (T : TapeTapes) (bits : List Bool)
    (a : TapeSymbol) (n : ℕ) (ha : a.1 ≠ .home) :
    RunsIn (code r).step
      (cfg .erase (Function.update T r
        (Tape.mk₂ (encodeInput bits ++ [cleanAtom .home])
          (a :: List.replicate n blankSymbol))))
      (cfg .done (Function.update T r (wordTape []))) (bits.length + 3) := by
  induction bits generalizing a n with
  | nil =>
      have hfirst := RunsIn.single (step_erase_symbol r T
        (Tape.mk₂ [cleanAtom .home] (a :: List.replicate n blankSymbol)) ha)
      simp only [TapeCopy.write_mk₂, List.tail_cons, TapeWord.move_left_mk₂_cons] at hfirst
      simpa only [encodeInput, List.map_nil, List.nil_append, List.length_nil,
        Nat.zero_add] using hfirst.trans (runs_finish r T n)
  | cons b bits ih =>
      have hfirst := RunsIn.single (step_erase_symbol r T
        (Tape.mk₂ (rawInputSymbol b :: (encodeInput bits ++ [cleanAtom .home]))
          (a :: List.replicate n blankSymbol)) ha)
      simp only [TapeCopy.write_mk₂, List.tail_cons, TapeWord.move_left_mk₂_cons] at hfirst
      have hrest := ih (rawInputSymbol b) (n + 1) (by simp [rawInputSymbol, cleanAtom])
      simp only [List.replicate_succ] at hrest
      simpa only [encodeInput, List.map_cons, List.cons_append, List.length_cons,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hfirst.trans hrest

theorem runs_erase (r : TapeRegister) (T : TapeTapes) (bits : List Bool) :
    RunsIn (code r).step
      (cfg .start (Function.update T r (wordTape bits)))
      (cfg .done (Function.update T r (wordTape []))) (2 * bits.length + 5) := by
  have hstart := RunsIn.single (step_start r T (wordTape bits))
  have hscan := runs_scan r T bits [cleanAtom .home]
  have hback := runs_erase_back r T bits.reverse (cleanAtom .endMark) 0
    (by simp [cleanAtom])
  have hreverse : encodeInput bits.reverse = (encodeInput bits).reverse := by
    simp [encodeInput]
  simp only [hreverse, List.length_reverse, List.replicate_zero] at hback
  have hstart' : RunsIn (code r).step
      (cfg .start (Function.update T r (wordTape bits)))
      (cfg .scan (Function.update T r
        (Tape.mk₂ [cleanAtom .home] (encodeInput bits ++ [cleanAtom .endMark])))) 1 := by
    simpa only [wordTape_right, cursorTape, encodeInput, List.map_nil,
      List.reverse_nil, List.nil_append] using hstart
  simpa only [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hstart'.trans hscan).trans hback

@[simp] theorem step_done (r : TapeRegister) (T : TapeTapes) :
    (code r).step (cfg .done T) = none := rfl

end TapeErase
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeFill

open Turing TapeMultiProgram TapeRouting TapeUnary TapeCopy TapeArithmetic

def pushProgram (r : TapeRegister) (b : Bool) : TapeMultiProgram IncState
  | .start, h => writeMove r (rawInputSymbol b) .left .newHome h
  | .newHome, h => writeMove r (cleanAtom .home) .stay .done h
  | .done, _ => none

theorem runs_push (r : TapeRegister) (b : Bool) (T : TapeTapes) (bits : List Bool)
    (hT : T r = wordTape bits) :
    RunsIn (pushProgram r b).step (cfg IncState.start T)
      (cfg IncState.done (Function.update T r (wordTape (b :: bits)))) 2 := by
  let middle := ((T r).write (rawInputSymbol b)).move Dir.left
  have h₁ := step_writeMove (pushProgram r b) IncState.start IncState.newHome
    T r (rawInputSymbol b) HeadMove.left rfl
  have h₂ := step_writeMove (pushProgram r b) IncState.newHome IncState.done
    (Function.update T r middle) r (cleanAtom .home) HeadMove.stay rfl
  have hm : middle.write (cleanAtom .home) = wordTape (b :: bits) := by
    dsimp [middle]
    rw [hT, prepend_home]
  have h₁' : (pushProgram r b).step (cfg IncState.start T) =
      some (cfg IncState.newHome (Function.update T r middle)) := h₁
  have h₂' : (pushProgram r b).step (cfg IncState.newHome (Function.update T r middle)) =
      some (cfg IncState.done (Function.update T r (wordTape (b :: bits)))) := by
    simpa only [Function.update_self, HeadMove.apply_stay, Function.update_idem, hm] using h₂
  exact (RunsIn.single h₁').trans (RunsIn.single h₂')

abbrev FillState := LoopState DecState IncState

def fillProgram (counter destination : TapeRegister) (b : Bool) : TapeMultiProgram FillState :=
  loopCode (decProgram counter) (pushProgram destination b)
    DecState.start IncState.start decPositive

def fillStart : FillState := loopTest DecState.start
def fillDone : FillState := loopDone

theorem runs_fill {counter destination : TapeRegister} (hne : counter ≠ destination)
    (b : Bool) (T : TapeTapes) (n : ℕ) (bits : List Bool) :
    RunsIn (fillProgram counter destination b).step
      (cfg fillStart (onPair counter destination T (counterTape n) (wordTape bits)))
      (cfg fillDone (onPair counter destination T
        (counterTape 0) (wordTape (List.replicate n b ++ bits))))
      (8 * n + 3) := by
  induction n generalizing bits with
  | zero =>
      have hd := decrement_empty counter
        (onPair counter destination T (counterTape 0) (wordTape bits)) (by simp [counterTape])
      have he := loop_exit (decProgram counter) (pushProgram destination b)
        DecState.start IncState.start decPositive hd rfl rfl
      simpa only [fillProgram, fillStart, fillDone, List.replicate_zero, List.nil_append,
        Nat.mul_zero, Nat.zero_add] using he
  | succ n ih =>
      have hd := decrement_cons counter
        (onPair counter destination T (counterTape (n + 1)) (wordTape bits))
        (List.replicate n true) true (by simp [counterTape, List.replicate_succ])
      simp only [update_onPair_src] at hd
      have hp := runs_push destination b
        (onPair counter destination T (counterTape n) (wordTape bits)) bits (by simp [hne])
      simp only [update_onPair_dst hne] at hp
      have hit := loop_iter (decProgram counter) (pushProgram destination b)
        DecState.start IncState.start decPositive hd rfl rfl hp rfl
      have hrest := ih (b :: bits)
      have hall := hit.trans hrest
      have hword : List.replicate n b ++ b :: bits = List.replicate (n + 1) b ++ bits := by
        rw [List.replicate_succ']
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have htime : 4 + 1 + 2 + 1 + (8 * n + 3) = 8 * (n + 1) + 3 := by omega
      simpa only [fillProgram, fillStart, fillDone, hword, htime] using hall

@[simp] theorem fill_done (counter destination : TapeRegister) (b : Bool) (h : TapeHeads) :
    fillProgram counter destination b fillDone h = none := rfl

end TapeFill
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound
namespace TapeArray

open Turing TapeMultiProgram TapeCopy

inductive State where
  | start
  | scan
  | rewind (read : Bool)
  | done (read : Bool)
  deriving DecidableEq, Fintype, Inhabited

def code (index array : TapeRegister) (f : Bool → Bool) : TapeMultiProgram State
  | .start, h => emit index array .scan h (h index) (h array) .right
  | .scan, h =>
      match (h index).1 with
      | .bit true => emit index array .scan h (h index) (h array) .right
      | .endMark =>
          match (h array).1 with
          | .bit b => emit index array (.rewind b) h (h index) (rawInputSymbol (f b)) .stay
          | _ => none
      | _ => none
  | .rewind b, h =>
      if (h index).1 = .home then emit index array (.done b) h (h index) (h array) .stay
      else emit index array (.rewind b) h (h index) (h array) .left
  | .done _, _ => none

private theorem replicate_append_cons {α : Type uDepth1} (n : ℕ) (a : α) (L : List α) :
    List.replicate n a ++ a :: L = a :: (List.replicate n a ++ L) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons a) ih

theorem step_start {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) (I A : Tape TapeSymbol) :
    (code index array f).step (cfg .start (onPair index array T I A)) =
      some (cfg .scan (onPair index array T (I.move .right) (A.move .right))) := by
  have h := step_emit (code index array f) hne T I A .start .scan I.head A.head .right
    (by simp [code, heads, hne])
  simpa only [Tape.write_self, HeadMove.apply_right] using h

theorem step_scan_bit {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) (I A : Tape TapeSymbol)
    (hI : I.head = rawInputSymbol true) :
    (code index array f).step (cfg .scan (onPair index array T I A)) =
      some (cfg .scan (onPair index array T (I.move .right) (A.move .right))) := by
  have h := step_emit (code index array f) hne T I A .scan .scan I.head A.head .right
    (by simp [code, heads, hne, hI, rawInputSymbol, cleanAtom])
  simpa only [Tape.write_self, HeadMove.apply_right] using h

theorem step_scan_end {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) (I A : Tape TapeSymbol) (b : Bool)
    (hI : I.head = cleanAtom .endMark) (hA : A.head = rawInputSymbol b) :
    (code index array f).step (cfg .scan (onPair index array T I A)) =
      some (cfg (.rewind b) (onPair index array T I (A.write (rawInputSymbol (f b))))) := by
  have h := step_emit (code index array f) hne T I A .scan (.rewind b)
    I.head (rawInputSymbol (f b)) .stay
    (by simp [code, heads, hne, hI, hA, rawInputSymbol, cleanAtom])
  simpa only [Tape.write_self, HeadMove.apply_stay] using h

theorem step_rewind_move {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) (I A : Tape TapeSymbol) (b : Bool)
    (hI : I.head.1 ≠ .home) :
    (code index array f).step (cfg (.rewind b) (onPair index array T I A)) =
      some (cfg (.rewind b) (onPair index array T (I.move .left) (A.move .left))) := by
  have h := step_emit (code index array f) hne T I A (.rewind b) (.rewind b)
    I.head A.head .left (by simp [code, heads, hne, hI])
  simpa only [Tape.write_self, HeadMove.apply_left] using h

theorem step_rewind_home {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) (I A : Tape TapeSymbol) (b : Bool)
    (hI : I.head.1 = .home) :
    (code index array f).step (cfg (.rewind b) (onPair index array T I A)) =
      some (cfg (.done b) (onPair index array T I A)) := by
  have h := step_emit (code index array f) hne T I A (.rewind b) (.done b)
    I.head A.head .stay (by simp [code, heads, hne, hI])
  simpa only [Tape.write_self, HeadMove.apply_stay] using h

theorem runs_scan {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) («prefix» : List Bool)
    (LI LA R : List TapeSymbol) :
    RunsIn (code index array f).step
      (cfg .scan (onPair index array T
        (Tape.mk₂ LI (List.replicate «prefix».length (rawInputSymbol true) ++ [cleanAtom .endMark]))
        (Tape.mk₂ LA (encodeInput «prefix» ++ R))))
      (cfg .scan (onPair index array T
        (Tape.mk₂ (List.replicate «prefix».length (rawInputSymbol true) ++ LI) [cleanAtom .endMark])
        (Tape.mk₂ ((encodeInput «prefix»).reverse ++ LA) R)))
      «prefix».length := by
  induction «prefix» generalizing LI LA with
  | nil =>
      simpa only [List.length_nil, List.replicate_zero, List.nil_append,
        encodeInput, List.map_nil, List.reverse_nil] using
        RunsIn.refl (code index array f).step
          (cfg .scan (onPair index array T (Tape.mk₂ LI [cleanAtom .endMark]) (Tape.mk₂ LA R)))
  | cons a «prefix» ih =>
      have hfirst := RunsIn.single (step_scan_bit hne f T
        (Tape.mk₂ LI (rawInputSymbol true ::
          (List.replicate «prefix».length (rawInputSymbol true) ++ [cleanAtom .endMark])))
        (Tape.mk₂ LA (rawInputSymbol a :: (encodeInput «prefix» ++ R))) rfl)
      simp only [TapeWord.move_right_mk₂_cons] at hfirst
      have hrest := ih (rawInputSymbol true :: LI) (rawInputSymbol a :: LA)
      simpa only [List.length_cons, List.replicate_succ, encodeInput, List.map_cons,
        List.cons_append, List.reverse_cons, List.append_assoc, List.nil_append,
        replicate_append_cons, Nat.add_comm] using hfirst.trans hrest

theorem runs_rewind {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) (left : List Bool) (b : Bool)
    (i : TapeSymbol) (RI RA : List TapeSymbol) (hi : i.1 ≠ .home) :
    RunsIn (code index array f).step
      (cfg (.rewind b) (onPair index array T
        (Tape.mk₂ (List.replicate left.length (rawInputSymbol true) ++ [cleanAtom .home]) (i :: RI))
        (Tape.mk₂ (encodeInput left ++ [cleanAtom .home]) RA)))
      (cfg (.done b) (onPair index array T
        (Tape.mk₂ [] (cleanAtom .home ::
          (List.replicate left.length (rawInputSymbol true) ++ i :: RI)))
        (Tape.mk₂ [] (cleanAtom .home :: ((encodeInput left).reverse ++ RA)))))
      (left.length + 2) := by
  induction left generalizing i RI RA with
  | nil =>
      have hfirst := RunsIn.single (step_rewind_move hne f T
        (Tape.mk₂ [cleanAtom .home] (i :: RI)) (Tape.mk₂ [cleanAtom .home] RA) b hi)
      simp only [TapeWord.move_left_mk₂_cons] at hfirst
      have hlast := RunsIn.single (step_rewind_home hne f T
        (Tape.mk₂ [] (cleanAtom .home :: i :: RI))
        (Tape.mk₂ [] (cleanAtom .home :: RA)) b rfl)
      simpa only [List.length_nil, List.replicate_zero, List.nil_append,
        encodeInput, List.map_nil, List.reverse_nil, Nat.zero_add] using hfirst.trans hlast
  | cons a left ih =>
      have hfirst := RunsIn.single (step_rewind_move hne f T
        (Tape.mk₂ (rawInputSymbol true ::
          (List.replicate left.length (rawInputSymbol true) ++ [cleanAtom .home])) (i :: RI))
        (Tape.mk₂ (rawInputSymbol a :: (encodeInput left ++ [cleanAtom .home])) RA) b hi)
      simp only [TapeWord.move_left_mk₂_cons] at hfirst
      have hrest := ih (rawInputSymbol true) (i :: RI) (rawInputSymbol a :: RA)
        (by simp [rawInputSymbol, cleanAtom])
      simpa only [List.length_cons, List.replicate_succ, encodeInput, List.map_cons,
        List.cons_append, List.reverse_cons, List.append_assoc, List.nil_append,
        replicate_append_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using hfirst.trans hrest

theorem runs_modify {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) («prefix» suffix : List Bool) (b : Bool) :
    RunsIn (code index array f).step
      (cfg .start (onPair index array T
        (wordTape (List.replicate «prefix».length true)) (wordTape («prefix» ++ b :: suffix))))
      (cfg (.done b) (onPair index array T
        (wordTape (List.replicate «prefix».length true)) (wordTape («prefix» ++ f b :: suffix))))
      (2 * «prefix».length + 4) := by
  have hstart := RunsIn.single (step_start hne f T
    (wordTape (List.replicate «prefix».length true)) (wordTape («prefix» ++ b :: suffix)))
  have hscan := runs_scan hne f T «prefix» [cleanAtom .home] [cleanAtom .home]
    (rawInputSymbol b :: (encodeInput suffix ++ [cleanAtom .endMark]))
  have hwrite := RunsIn.single (step_scan_end hne f T
    (Tape.mk₂ (List.replicate «prefix».length (rawInputSymbol true) ++ [cleanAtom .home])
      [cleanAtom .endMark])
    (Tape.mk₂ ((encodeInput «prefix»).reverse ++ [cleanAtom .home])
      (rawInputSymbol b :: (encodeInput suffix ++ [cleanAtom .endMark]))) b rfl rfl)
  simp only [TapeWord.write_mk₂_cons] at hwrite
  have hback := runs_rewind hne f T «prefix».reverse b (cleanAtom .endMark) []
    (rawInputSymbol (f b) :: (encodeInput suffix ++ [cleanAtom .endMark]))
    (by simp [cleanAtom])
  have hreverse : encodeInput «prefix».reverse = (encodeInput «prefix»).reverse := by
    simp [encodeInput]
  simp only [hreverse, List.reverse_reverse, List.length_reverse] at hback
  have hstart' : RunsIn (code index array f).step
      (cfg .start (onPair index array T
        (wordTape (List.replicate «prefix».length true)) (wordTape («prefix» ++ b :: suffix))))
      (cfg .scan (onPair index array T
        (Tape.mk₂ [cleanAtom .home]
          (List.replicate «prefix».length (rawInputSymbol true) ++ [cleanAtom .endMark]))
        (Tape.mk₂ [cleanAtom .home]
          (encodeInput «prefix» ++ rawInputSymbol b :: (encodeInput suffix ++ [cleanAtom .endMark]))))) 1 := by
    simpa only [wordTape_right, cursorTape, encodeInput, List.map_append,
      List.map_replicate, List.map_cons, List.map_nil, List.reverse_nil,
      List.nil_append, List.append_assoc, List.cons_append] using hstart
  have hboth := ((hstart'.trans hscan).trans hwrite).trans hback
  simpa only [wordTape, Tape.mk₁, encodeInput, List.map_replicate, List.map_append,
    List.map_cons, List.append_assoc, List.cons_append, List.append_nil,
    Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hboth

theorem runs_read {index array : TapeRegister} (hne : index ≠ array)
    (T : TapeTapes) («prefix» suffix : List Bool) (b : Bool) :
    RunsIn (code index array id).step
      (cfg .start (onPair index array T
        (wordTape (List.replicate «prefix».length true)) (wordTape («prefix» ++ b :: suffix))))
      (cfg (.done b) (onPair index array T
        (wordTape (List.replicate «prefix».length true)) (wordTape («prefix» ++ b :: suffix))))
      (2 * «prefix».length + 4) :=
  runs_modify hne id T «prefix» suffix b

@[simp] theorem step_done (index array : TapeRegister) (f : Bool → Bool)
    (T : TapeTapes) (b : Bool) :
    (code index array f).step (cfg (.done b) T) = none := rfl

end TapeArray
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound
namespace TapeProductTerm

open TapeMultiProgram TapeCopy TapeRouting TapeArithmetic TapeUnary

theorem onPair_eq_self {src dst : TapeRegister} {T : TapeTapes}
    {S D : Turing.Tape TapeSymbol} (hS : T src = S) (hD : T dst = D) :
    onPair src dst T S D = T := by
  funext r
  by_cases hs : r = src
  · subst r
    simpa only [onPair_src] using hS.symm
  · by_cases hd : r = dst
    · subst r
      simp only [onPair, hs, ite_false, ite_true]
      exact hD.symm
    · simp [onPair, hs, hd]

theorem read_at {index array : TapeRegister} (hne : index ≠ array)
    (T : TapeTapes) («prefix» suffix : List Bool) (b : Bool)
    (hi : T index = counterTape «prefix».length)
    (ha : T array = wordTape («prefix» ++ b :: suffix)) :
    RunsIn (TapeArray.code index array id).step
      (cfg TapeArray.State.start T) (cfg (TapeArray.State.done b) T)
      (2 * «prefix».length + 4) := by
  have h := TapeArray.runs_read hne T «prefix» suffix b
  have hframe := onPair_eq_self hi ha
  dsimp only [counterTape] at hframe
  simpa only [counterTape, hframe] using h

theorem modify_at {index array : TapeRegister} (hne : index ≠ array)
    (f : Bool → Bool) (T : TapeTapes) («prefix» suffix : List Bool) (b : Bool)
    (hi : T index = counterTape «prefix».length)
    (ha : T array = wordTape («prefix» ++ b :: suffix)) :
    RunsIn (TapeArray.code index array f).step
      (cfg TapeArray.State.start T)
      (cfg (TapeArray.State.done b)
        (Function.update T array (wordTape («prefix» ++ f b :: suffix))))
      (2 * «prefix».length + 4) := by
  have h := TapeArray.runs_modify hne f T «prefix» suffix b
  have hframe := onPair_eq_self hi ha
  have hout : onPair index array T (counterTape «prefix».length)
      (wordTape («prefix» ++ f b :: suffix)) =
        Function.update T array (wordTape («prefix» ++ f b :: suffix)) := by
    rw [← update_onPair_dst hne T (counterTape «prefix».length)
      (wordTape («prefix» ++ b :: suffix)), hframe]
  dsimp only [counterTape] at hframe hout
  simpa only [counterTape, hframe, hout] using h

def carryCode {F : Type uDepth1} {Q : Type uDepth2} (P : F → TapeMultiProgram Q) : TapeMultiProgram (F × Q)
  | (flag, q), h => (P flag q h).map fun out => ((flag, out.1), out.2)

theorem carry_runs {F : Type uDepth3} {Q : Type uDepth4} (P : F → TapeMultiProgram Q) (flag : F)
    {q q' : Q} {T U : TapeTapes} {n : ℕ}
    (h : RunsIn (P flag).step (cfg q T) (cfg q' U) n) :
    RunsIn (carryCode P).step (cfg (flag, q) T) (cfg (flag, q') U) n :=
  runs_map (P flag) (carryCode P) (fun q => (flag, q)) (by
    intro a heads a' writes moves he
    simp only [carryCode, he, Option.map_some]) h

def readFlag : TapeArray.State → Bool
  | .done b => b
  | _ => false

abbrev ReadState := TapeArray.State ⊕ (Bool × TapeArray.State)
abbrev State := ReadState ⊕ ((Bool × Bool) × TapeArray.State)

def readProgram (i a j b : TapeRegister) : TapeMultiProgram ReadState :=
  joinCode (TapeArray.code i a id)
    (carryCode (fun _ : Bool => TapeArray.code j b id))
    (fun q => (readFlag q, TapeArray.State.start))

def termFlags : ReadState → (Bool × Bool)
  | .inr (a, q) => (a, readFlag q)
  | .inl _ => (false, false)

def updateProgram (k c : TapeRegister) : TapeMultiProgram ((Bool × Bool) × TapeArray.State) :=
  carryCode fun ab => TapeArray.code k c (fun old => Bool.xor old (ab.1 && ab.2))

def program (i a j b k c : TapeRegister) : TapeMultiProgram State :=
  joinCode (readProgram i a j b) (updateProgram k c)
    (fun q => (termFlags q, TapeArray.State.start))

def start : State := .inl (.inl TapeArray.State.start)
def done (a b old : Bool) : State := .inr ((a, b), TapeArray.State.done old)

theorem runs_product_term (i a j b k c : TapeRegister)
    (hia : i ≠ a) (hjb : j ≠ b) (hkc : k ≠ c)
    (T : TapeTapes) (pa sa pb sb pc sc : List Bool) (va vb old : Bool)
    (hi : T i = counterTape pa.length) (ha : T a = wordTape (pa ++ va :: sa))
    (hj : T j = counterTape pb.length) (hb : T b = wordTape (pb ++ vb :: sb))
    (hk : T k = counterTape pc.length) (hc : T c = wordTape (pc ++ old :: sc)) :
    RunsIn (program i a j b k c).step (cfg start T)
      (cfg (done va vb old)
        (Function.update T c (wordTape (pc ++ Bool.xor old (va && vb) :: sc))))
      (2 * (pa.length + pb.length + pc.length) + 14) := by
  have hra := read_at hia T pa sa va hi ha
  have hrb := read_at hjb T pb sb vb hj hb
  have hrb' := carry_runs (fun _ : Bool => TapeArray.code j b id) va hrb
  have hread := join_runs (TapeArray.code i a id)
    (carryCode (fun _ : Bool => TapeArray.code j b id))
    (fun q => (readFlag q, TapeArray.State.start)) hra rfl hrb'
  have hupdate := modify_at hkc (fun old => Bool.xor old (va && vb)) T pc sc old hk hc
  have hupdate' := carry_runs
    (fun ab : Bool × Bool => TapeArray.code k c (fun old => Bool.xor old (ab.1 && ab.2)))
    (va, vb) hupdate
  have hreadhalt : readProgram i a j b (.inr (va, TapeArray.State.done vb)) (heads T) = none := rfl
  have hall := join_runs (readProgram i a j b) (updateProgram k c)
    (fun q => (termFlags q, TapeArray.State.start)) hread hreadhalt hupdate'
  have htime : (2 * pa.length + 4 + 1 + (2 * pb.length + 4)) + 1 +
      (2 * pc.length + 4) = 2 * (pa.length + pb.length + pc.length) + 14 := by omega
  simpa only [program, start, done, htime] using hall

@[simp] theorem program_done (i a j b k c : TapeRegister) (va vb old : Bool) (h : TapeHeads) :
    program i a j b k c (done va vb old) h = none := rfl

end TapeProductTerm
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

open TapeMultiProgram TapeCopy TapeUnary TapeArithmetic TapeRouting

def storeTapes (σ : TapeStore) : TapeTapes := fun r => wordTape (σ r)

@[simp] theorem storeTapes_apply (σ : TapeStore) (r : TapeRegister) :
    storeTapes σ r = wordTape (σ r) := rfl

theorem storeTapes_update (σ : TapeStore) (r : TapeRegister) (bits : List Bool) :
    storeTapes (Function.update σ r bits) = Function.update (storeTapes σ) r (wordTape bits) := by
  funext s
  by_cases h : s = r
  · subst s
    simp [storeTapes]
  · simp [storeTapes, Function.update, h]

theorem onPair_eq_updates {α : Type uDepth1} {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeRegister → α) (S D : α) :
    onPair src dst T S D = Function.update (Function.update T src S) dst D := by
  funext r
  by_cases hs : r = src
  · subst r
    simp [onPair, Function.update, hne]
  · by_cases hd : r = dst
    · subst r
      simp [onPair, Function.update, Ne.symm hne]
    · simp [onPair, Function.update, hs, hd]

namespace TapeStoreRuns

theorem copy {src dst : TapeRegister} (hne : src ≠ dst) (σ : TapeStore)
    (hempty : σ dst = []) :
    RunsIn (TapeCopy.code src dst).step
      (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes (Function.update σ dst (σ src))))
      (2 * (σ src).length + 4) := by
  have h := TapeCopy.runs_copy hne (storeTapes σ) (σ src)
  have hi : onPair src dst (storeTapes σ) (wordTape (σ src)) (wordTape []) = storeTapes σ :=
    TapeProductTerm.onPair_eq_self rfl (by simp [hempty])
  have ho : onPair src dst (storeTapes σ) (wordTape (σ src)) (wordTape (σ src)) =
      storeTapes (Function.update σ dst (σ src)) := by
    rw [← update_onPair_dst hne (storeTapes σ) (wordTape (σ src)) (wordTape []), hi,
      storeTapes_update]
  simpa only [hi, ho] using h

theorem erase (r : TapeRegister) (σ : TapeStore) :
    RunsIn (TapeErase.code r).step
      (cfg TapeErase.State.start (storeTapes σ))
      (cfg TapeErase.State.done (storeTapes (Function.update σ r [])))
      (2 * (σ r).length + 5) := by
  have h := TapeErase.runs_erase r (storeTapes σ) (σ r)
  simpa only [← storeTapes_update, Function.update_eq_self] using h

theorem push (r : TapeRegister) (b : Bool) (σ : TapeStore) :
    RunsIn (TapeFill.pushProgram r b).step
      (cfg IncState.start (storeTapes σ))
      (cfg IncState.done (storeTapes (Function.update σ r (b :: σ r)))) 2 := by
  simpa only [storeTapes_update] using TapeFill.runs_push r b (storeTapes σ) (σ r) rfl

theorem add {counter destination : TapeRegister} (hne : counter ≠ destination)
    (σ : TapeStore) (n m : ℕ)
    (hc : σ counter = List.replicate n true)
    (hd : σ destination = List.replicate m true) :
    RunsIn (addProgram counter destination).step
      (cfg addStart (storeTapes σ))
      (cfg addDone (storeTapes
        (Function.update (Function.update σ counter []) destination (List.replicate (m + n) true))))
      (8 * n + 3) := by
  have h := runs_add hne (storeTapes σ) n m
  have hi : onPair counter destination (storeTapes σ) (counterTape n) (counterTape m) =
      storeTapes σ := TapeProductTerm.onPair_eq_self (by simp [hc, counterTape])
        (by simp [hd, counterTape])
  have ho : onPair counter destination (storeTapes σ) (counterTape 0) (counterTape (m + n)) =
      storeTapes (Function.update (Function.update σ counter []) destination (List.replicate (m + n) true)) := by
    rw [onPair_eq_updates hne]
    simp only [storeTapes_update, counterTape, List.replicate_zero]
  simpa only [hi, ho] using h

theorem fill {counter destination : TapeRegister} (hne : counter ≠ destination)
    (b : Bool) (σ : TapeStore) (n : ℕ) (hc : σ counter = List.replicate n true) :
    RunsIn (TapeFill.fillProgram counter destination b).step
      (cfg TapeFill.fillStart (storeTapes σ))
      (cfg TapeFill.fillDone (storeTapes (Function.update (Function.update σ counter [])
        destination (List.replicate n b ++ σ destination))))
      (8 * n + 3) := by
  have h := TapeFill.runs_fill hne b (storeTapes σ) n (σ destination)
  have hi : onPair counter destination (storeTapes σ) (counterTape n)
      (wordTape (σ destination)) = storeTapes σ :=
    TapeProductTerm.onPair_eq_self (by simp [hc, counterTape]) rfl
  have ho : onPair counter destination (storeTapes σ) (counterTape 0)
      (wordTape (List.replicate n b ++ σ destination)) =
      storeTapes (Function.update (Function.update σ counter []) destination
        (List.replicate n b ++ σ destination)) := by
    rw [onPair_eq_updates hne]
    simp only [storeTapes_update, counterTape, List.replicate_zero]
  simpa only [hi, ho] using h

end TapeStoreRuns
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeUnaryCompareScan

open Turing TapeMultiProgram

inductive State where
  | beginR
  | beginS
  | scan
  | advanceS
  | done (result : Ordering)
  deriving DecidableEq, Fintype, Inhabited

def result (m n : ℕ) : Ordering :=
  if m < n then .lt else if m = n then .eq else .gt

@[simp] theorem result_succ (m n : ℕ) : result (m + 1) (n + 1) = result m n := by
  simp only [result, Nat.succ_lt_succ_iff, Nat.succ.injEq]

theorem result_eq_lt_iff (m n : ℕ) : result m n = .lt ↔ m < n := by
  by_cases h : m < n
  · simp [result, h]
  · by_cases he : m = n <;> simp [result, h, he]

theorem result_eq_eq_iff (m n : ℕ) : result m n = .eq ↔ m = n := by
  by_cases h : m < n
  · simp [result, h, Nat.ne_of_lt h]
  · by_cases he : m = n <;> simp [result, h, he]

theorem result_eq_gt_iff (m n : ℕ) : result m n = .gt ↔ n < m := by
  by_cases h : m < n
  · have hn : ¬n < m := Nat.not_lt_of_ge h.le
    simp [result, h, hn]
  · by_cases he : m = n
    · subst n
      simp [result]
    · have hn : n < m := lt_of_le_of_ne (Nat.le_of_not_gt h) (Ne.symm he)
      simp [result, h, he, hn]

def unaryCursor (k n : ℕ) : Tape TapeSymbol :=
  cursorTape (List.replicate k true) (List.replicate n true)

@[simp] theorem unaryCursor_head_zero (k : ℕ) :
    (unaryCursor k 0).head = cleanAtom .endMark := rfl

@[simp] theorem unaryCursor_head_succ (k n : ℕ) :
    (unaryCursor k (n + 1)).head = rawInputSymbol true := rfl

theorem unaryCursor_right (k n : ℕ) :
    (unaryCursor k (n + 1)).move Dir.right = unaryCursor (k + 1) n := by
  unfold unaryCursor
  rw [List.replicate_succ, cursorTape_right, ← List.replicate_succ']

def pairTapes (r s : TapeRegister) (T : TapeTapes)
    (R S : Tape TapeSymbol) : TapeTapes :=
  Function.update (Function.update T r R) s S

@[simp] theorem pairTapes_r {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (R S : Tape TapeSymbol) : pairTapes r s T R S r = R := by
  simp [pairTapes, hrs]

@[simp] theorem pairTapes_s (r s : TapeRegister)
    (T : TapeTapes) (R S : Tape TapeSymbol) : pairTapes r s T R S s = S := by
  simp [pairTapes]

theorem pairTapes_other (r s : TapeRegister) (T : TapeTapes)
    (R S : Tape TapeSymbol) (j : TapeRegister) (hjr : j ≠ r) (hjs : j ≠ s) :
    pairTapes r s T R S j = T j := by
  simp [pairTapes, hjr, hjs]

theorem update_pairTapes_r {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (R S R' : Tape TapeSymbol) :
    Function.update (pairTapes r s T R S) r R' = pairTapes r s T R' S := by
  unfold pairTapes
  rw [Function.update_comm (Ne.symm hrs), Function.update_idem]

theorem update_pairTapes_s (r s : TapeRegister)
    (T : TapeTapes) (R S S' : Tape TapeSymbol) :
    Function.update (pairTapes r s T R S) s S' = pairTapes r s T R S' := by
  simp only [pairTapes, Function.update_idem]

def scanTapes (r s : TapeRegister) (T : TapeTapes) (k m n : ℕ) : TapeTapes :=
  pairTapes r s T (unaryCursor k m) (unaryCursor k n)

theorem scanTapes_other (r s : TapeRegister) (T : TapeTapes) (k m n : ℕ)
    (j : TapeRegister) (hjr : j ≠ r) (hjs : j ≠ s) :
    scanTapes r s T k m n j = T j :=
  pairTapes_other r s T _ _ j hjr hjs

def code (r s : TapeRegister) : TapeMultiProgram State
  | .beginR, h => move r .right .beginS h
  | .beginS, h => move s .right .scan h
  | .scan, h =>
      if isAtom .endMark r h then
        if isAtom .endMark s h then jump (.done .eq) h
        else jump (.done .lt) h
      else if isAtom .endMark s h then jump (.done .gt) h
      else move r .right .advanceS h
  | .advanceS, h => move s .right .scan h
  | .done _, _ => none

theorem step_scan_zero_zero {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (k : ℕ) :
    (code r s).step (cfg .scan (scanTapes r s T k 0 0)) =
      some (cfg (.done .eq) (scanTapes r s T k 0 0)) := by
  apply step_jump
  simp [code, isAtom, heads, scanTapes, hrs, cleanAtom]

theorem step_scan_zero_succ {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (k n : ℕ) :
    (code r s).step (cfg .scan (scanTapes r s T k 0 (n + 1))) =
      some (cfg (.done .lt) (scanTapes r s T k 0 (n + 1))) := by
  apply step_jump
  simp [code, isAtom, heads, scanTapes, hrs, rawInputSymbol, cleanAtom]

theorem step_scan_succ_zero {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (k m : ℕ) :
    (code r s).step (cfg .scan (scanTapes r s T k (m + 1) 0)) =
      some (cfg (.done .gt) (scanTapes r s T k (m + 1) 0)) := by
  apply step_jump
  simp [code, isAtom, heads, scanTapes, hrs, rawInputSymbol, cleanAtom]

theorem step_scan_succ_succ {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (k m n : ℕ) :
    (code r s).step (cfg .scan (scanTapes r s T k (m + 1) (n + 1))) =
      some (cfg .advanceS (pairTapes r s T
        (unaryCursor (k + 1) m) (unaryCursor k (n + 1)))) := by
  have h := step_move (code r s) State.scan State.advanceS
    (scanTapes r s T k (m + 1) (n + 1)) r HeadMove.right
    (by simp [code, isAtom, heads, scanTapes, hrs, rawInputSymbol, cleanAtom])
  simpa only [scanTapes, pairTapes_r hrs, HeadMove.apply_right,
    unaryCursor_right, update_pairTapes_r hrs] using h

theorem step_advanceS (r s : TapeRegister) (T : TapeTapes)
    (R S : Tape TapeSymbol) :
    (code r s).step (cfg .advanceS (pairTapes r s T R S)) =
      some (cfg .scan (pairTapes r s T R (S.move Dir.right))) := by
  have h := step_move (code r s) State.advanceS State.scan
    (pairTapes r s T R S) s HeadMove.right rfl
  simpa only [pairTapes_s, HeadMove.apply_right, update_pairTapes_s] using h

theorem runs_scan {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (k m n : ℕ) :
    RunsIn (code r s).step (cfg .scan (scanTapes r s T k m n))
      (cfg (.done (result m n))
        (scanTapes r s T (k + min m n) (m - min m n) (n - min m n)))
      (2 * min m n + 1) := by
  induction m generalizing k n with
  | zero =>
      cases n with
      | zero =>
          simpa [result] using RunsIn.single (step_scan_zero_zero hrs T k)
      | succ n =>
          simpa [result] using RunsIn.single (step_scan_zero_succ hrs T k n)
  | succ m ih =>
      cases n with
      | zero =>
          simpa [result] using RunsIn.single (step_scan_succ_zero hrs T k m)
      | succ n =>
          have h₁ := RunsIn.single (step_scan_succ_succ hrs T k m n)
          have h₂ : RunsIn (code r s).step
              (cfg .advanceS (pairTapes r s T
                (unaryCursor (k + 1) m) (unaryCursor k (n + 1))))
              (cfg .scan (scanTapes r s T (k + 1) m n)) 1 := by
            simpa only [unaryCursor_right, scanTapes] using
              RunsIn.single (step_advanceS r s T
                (unaryCursor (k + 1) m) (unaryCursor k (n + 1)))
          have h := (h₁.trans h₂).trans (ih (k + 1) n)
          have hbound : (1 + 1) + (2 * min m n + 1) ≤
              2 * min (m + 1) (n + 1) + 1 := by
            rw [Nat.succ_min_succ]
            omega
          simpa only [Nat.succ_min_succ, Nat.succ_sub_succ, result_succ,
            Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using h.mono hbound

theorem runs_entry {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (m n : ℕ)
    (hR : T r = wordTape (List.replicate m true))
    (hS : T s = wordTape (List.replicate n true)) :
    RunsIn (code r s).step (cfg .beginR T)
      (cfg .scan (scanTapes r s T 0 m n)) 2 := by
  let U := Function.update T r ((T r).move Dir.right)
  have h₁ := step_move (code r s) State.beginR State.beginS T r HeadMove.right rfl
  have h₂ := step_move (code r s) State.beginS State.scan U s HeadMove.right rfl
  have h₁' : (code r s).step (cfg .beginR T) = some (cfg .beginS U) := h₁
  have h₂' : (code r s).step (cfg .beginS U) =
      some (cfg .scan (scanTapes r s T 0 m n)) := by
    simpa only [U, Function.update_of_ne (Ne.symm hrs), hR, hS,
      HeadMove.apply_right, wordTape_right, scanTapes, pairTapes, unaryCursor,
      List.replicate_zero] using h₂
  exact (RunsIn.single h₁').trans (RunsIn.single h₂')

theorem runs_compare {r s : TapeRegister} (hrs : r ≠ s)
    (T : TapeTapes) (m n : ℕ)
    (hR : T r = wordTape (List.replicate m true))
    (hS : T s = wordTape (List.replicate n true)) :
    RunsIn (code r s).step (cfg .beginR T)
      (cfg (.done (result m n))
        (scanTapes r s T (min m n) (m - min m n) (n - min m n)))
      (2 * min m n + 3) := by
  have h : RunsIn (code r s).step (cfg .beginR T)
      (cfg (.done (result m n))
        (scanTapes r s T (min m n) (m - min m n) (n - min m n)))
      (2 + (2 * min m n + 1)) := by
    simpa only [Nat.zero_add] using
      (runs_entry hrs T m n hR hS).trans (runs_scan hrs T 0 m n)
  exact h.mono (by omega)

theorem prefix_append_left (m n : ℕ) :
    List.replicate (min m n) true ++ List.replicate (m - min m n) true =
      List.replicate m true := by
  rw [List.replicate_append_replicate, Nat.add_sub_of_le (Nat.min_le_left m n)]

theorem prefix_append_right (m n : ℕ) :
    List.replicate (min m n) true ++ List.replicate (n - min m n) true =
      List.replicate n true := by
  rw [List.replicate_append_replicate, Nat.add_sub_of_le (Nat.min_le_right m n)]

@[simp] theorem step_done (r s : TapeRegister) (T : TapeTapes) (o : Ordering) :
    (code r s).step (cfg (.done o) T) = none := rfl

end TapeUnaryCompareScan
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

open Turing TapeMultiProgram

theorem cursorTape_left_nil (after : List Bool) :
    (cursorTape [] after).move Dir.left = wordTape after :=
  TapeWord.move_left_mk₂_cons [] (encodeInput after ++ [cleanAtom .endMark])
    (cleanAtom .home)

theorem cursorTape_left_append (before after : List Bool) (b : Bool) :
    (cursorTape (before ++ [b]) after).move Dir.left =
      cursorTape before (b :: after) := by
  simp only [cursorTape, encodeInput, List.map_append, List.map_cons, List.map_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, TapeWord.move_left_mk₂_cons]

namespace TapeRewind

inductive State
  | run
  | done
  deriving DecidableEq, Inhabited

instance : Fintype State where
  elems := {.run, .done}
  complete := by
    intro state
    cases state <;> simp

def program (r : TapeRegister) : TapeMultiProgram State
  | .run, h => if isAtom .home r h then jump .done h else move r .left .run h
  | .done, _ => none

theorem step_cursor (r : TapeRegister) (T : TapeTapes) (before after : List Bool) :
    (program r).step (cfg .run (Function.update T r (cursorTape before after))) =
      some (cfg .run (Function.update T r ((cursorTape before after).move Dir.left))) := by
  have h := step_move (program r) .run .run
    (Function.update T r (cursorTape before after)) r .left (by
      cases after <;> simp [program, isAtom, heads, rawInputSymbol, cleanAtom])
  simpa only [Function.update_self, Function.update_idem, HeadMove.apply_left] using h

theorem step_home (r : TapeRegister) (T : TapeTapes) (bits : List Bool) :
    (program r).step (cfg .run (Function.update T r (wordTape bits))) =
      some (cfg .done (Function.update T r (wordTape bits))) := by
  apply step_jump
  simp [program, isAtom, heads]

theorem runs_cursor (r : TapeRegister) (T : TapeTapes) (before after : List Bool) :
    RunsIn (program r).step
      (cfg .run (Function.update T r (cursorTape before after)))
      (cfg .done (Function.update T r (wordTape (before ++ after))))
      (before.length + 2) := by
  induction before using List.reverseRecOn generalizing after with
  | nil =>
      have h₁ := RunsIn.single (step_cursor r T [] after)
      rw [cursorTape_left_nil] at h₁
      have h₂ := RunsIn.single (step_home r T after)
      simpa only [List.nil_append, List.length_nil, Nat.zero_add] using h₁.trans h₂
  | append_singleton before b ih =>
      have h₁ := RunsIn.single (step_cursor r T (before ++ [b]) after)
      rw [cursorTape_left_append] at h₁
      have h₂ := ih (b :: after)
      simpa only [List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using h₁.trans h₂

end TapeRewind
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

open TapeMultiProgram

namespace TapeUnaryCompare

inductive State
  | scan (q : TapeUnaryCompareScan.State)
  | rewindR (result : Ordering)
  | rewindS (result : Ordering)
  | done (result : Ordering)
  deriving DecidableEq, Fintype, Inhabited

def scanState : TapeUnaryCompareScan.State → State
  | .done o => .rewindR o
  | q => .scan q

def rewindRState (o : Ordering) : TapeRewind.State → State
  | .run => .rewindR o
  | .done => .rewindS o

def rewindSState (o : Ordering) : TapeRewind.State → State
  | .run => .rewindS o
  | .done => .done o

def mapInstruction {Q : Type uDepth1} {R : Type uDepth2} (f : Q → R)
    (instruction : Option (Q × TapeHeads × TapeMoves)) :
    Option (R × TapeHeads × TapeMoves) :=
  instruction.map fun out => (f out.1, out.2.1, out.2.2)

def program (r s : TapeRegister) : TapeMultiProgram State
  | .scan q, h => mapInstruction scanState (TapeUnaryCompareScan.code r s q h)
  | .rewindR o, h => mapInstruction (rewindRState o) (TapeRewind.program r .run h)
  | .rewindS o, h => mapInstruction (rewindSState o) (TapeRewind.program s .run h)
  | .done _, _ => none

theorem scan_code (r s : TapeRegister) (q : TapeUnaryCompareScan.State)
    (h : TapeHeads) (q' : TapeUnaryCompareScan.State) (writes : TapeHeads)
    (moves : TapeMoves)
    (hc : TapeUnaryCompareScan.code r s q h = some (q', writes, moves)) :
    program r s (scanState q) h = some (scanState q', writes, moves) := by
  cases q with
  | beginR =>
      simp only [scanState, program, hc, mapInstruction, Option.map_some]
  | beginS =>
      simp only [scanState, program, hc, mapInstruction, Option.map_some]
  | scan =>
      simp only [scanState, program, hc, mapInstruction, Option.map_some]
  | advanceS =>
      simp only [scanState, program, hc, mapInstruction, Option.map_some]
  | done o => simp [TapeUnaryCompareScan.code] at hc

theorem rewindR_code (r s : TapeRegister) (o : Ordering) (q : TapeRewind.State)
    (h : TapeHeads) (q' : TapeRewind.State) (writes : TapeHeads) (moves : TapeMoves)
    (hc : TapeRewind.program r q h = some (q', writes, moves)) :
    program r s (rewindRState o q) h = some (rewindRState o q', writes, moves) := by
  cases q with
  | run =>
      simp only [rewindRState, program, hc, mapInstruction, Option.map_some]
  | done => simp [TapeRewind.program] at hc

theorem rewindS_code (r s : TapeRegister) (o : Ordering) (q : TapeRewind.State)
    (h : TapeHeads) (q' : TapeRewind.State) (writes : TapeHeads) (moves : TapeMoves)
    (hc : TapeRewind.program s q h = some (q', writes, moves)) :
    program r s (rewindSState o q) h = some (rewindSState o q', writes, moves) := by
  cases q with
  | run =>
      simp only [rewindSState, program, hc, mapInstruction, Option.map_some]
  | done => simp [TapeRewind.program] at hc

theorem runs_rewindR (r s : TapeRegister) (o : Ordering) (T : TapeTapes)
    (before after : List Bool) :
    RunsIn (program r s).step
      (cfg (.rewindR o) (Function.update T r (cursorTape before after)))
      (cfg (.rewindS o) (Function.update T r (wordTape (before ++ after))))
      (before.length + 2) := by
  simpa only [mapCfg, cfg, rewindRState] using
    runs_map (TapeRewind.program r) (program r s) (rewindRState o)
      (rewindR_code r s o) (TapeRewind.runs_cursor r T before after)

theorem runs_rewindS (r s : TapeRegister) (o : Ordering) (T : TapeTapes)
    (before after : List Bool) :
    RunsIn (program r s).step
      (cfg (.rewindS o) (Function.update T s (cursorTape before after)))
      (cfg (.done o) (Function.update T s (wordTape (before ++ after))))
      (before.length + 2) := by
  simpa only [mapCfg, cfg, rewindSState] using
    runs_map (TapeRewind.program s) (program r s) (rewindSState o)
      (rewindS_code r s o) (TapeRewind.runs_cursor s T before after)

theorem runs_compare {r s : TapeRegister} (hrs : r ≠ s) (T : TapeTapes) (m n : ℕ)
    (hR : T r = wordTape (List.replicate m true))
    (hS : T s = wordTape (List.replicate n true)) :
    RunsIn (program r s).step (cfg (.scan .beginR) T)
      (cfg (.done (TapeUnaryCompareScan.result m n)) T) (4 * min m n + 7) := by
  let k := min m n
  let o := TapeUnaryCompareScan.result m n
  let T₂ := Function.update T s (TapeUnaryCompareScan.unaryCursor k (n - k))
  have hsplitR : k + (m - k) = m := by
    have hk : k ≤ m := Nat.min_le_left m n
    omega
  have hsplitS : k + (n - k) = n := by
    have hk : k ≤ n := Nat.min_le_right m n
    omega
  have hscan : RunsIn (program r s).step (cfg (.scan .beginR) T)
      (cfg (.rewindR o) (TapeUnaryCompareScan.scanTapes r s T k (m-k) (n-k)))
      (2*k+3) := by
    simpa only [mapCfg, cfg, scanState] using
      runs_map (TapeUnaryCompareScan.code r s) (program r s) scanState
        (scan_code r s) (TapeUnaryCompareScan.runs_compare hrs T m n hR hS)
  have hstartR : Function.update T₂ r (TapeUnaryCompareScan.unaryCursor k (m-k)) =
      TapeUnaryCompareScan.scanTapes r s T k (m-k) (n-k) := by
    exact (Function.update_comm hrs _ _ T).symm
  have hendR : Function.update T₂ r
      (wordTape (List.replicate k true ++ List.replicate (m-k) true)) = T₂ := by
    apply Function.update_eq_self_iff.mpr
    simp only [List.replicate_append_replicate, hsplitR]
    simpa only [T₂, Function.update_of_ne hrs] using hR.symm
  have hrewindR := runs_rewindR r s o T₂ (List.replicate k true)
    (List.replicate (m-k) true)
  change RunsIn (program r s).step
    (cfg (.rewindR o) (Function.update T₂ r (TapeUnaryCompareScan.unaryCursor k (m-k))))
    (cfg (.rewindS o) (Function.update T₂ r
      (wordTape (List.replicate k true ++ List.replicate (m-k) true))))
    ((List.replicate k true).length + 2) at hrewindR
  rw [hstartR, hendR, List.length_replicate] at hrewindR
  have hendS : Function.update T s
      (wordTape (List.replicate k true ++ List.replicate (n-k) true)) = T := by
    apply Function.update_eq_self_iff.mpr
    simpa only [List.replicate_append_replicate, hsplitS] using hS.symm
  have hrewindS := runs_rewindS r s o T (List.replicate k true)
    (List.replicate (n-k) true)
  rw [hendS, List.length_replicate] at hrewindS
  have hrun := (hscan.trans hrewindR).trans hrewindS
  have hbound : (2*k+3+(k+2))+(k+2) = 4 * min m n + 7 := by omega
  simpa only [hbound] using hrun

theorem runs_compare_linear {r s : TapeRegister} (hrs : r ≠ s) (T : TapeTapes)
    (m n : ℕ) (hR : T r = wordTape (List.replicate m true))
    (hS : T s = wordTape (List.replicate n true)) :
    RunsIn (program r s).step (cfg (.scan .beginR) T)
      (cfg (.done (TapeUnaryCompareScan.result m n)) T) (7 * (m+n+1)) := by
  apply (runs_compare hrs T m n hR hS).mono
  have hmin := Nat.min_le_left m n
  omega

end TapeUnaryCompare
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapePowerCompare

open TapeMultiProgram TapeRouting TapeUnary TapeCopy

theorem resultTapes_eq_frame (k : ℕ)
    (outer source scratch destination : TapeRegister) (T : TapeTapes) (n m : ℕ) :
    TapePower.resultTapes k outer source scratch destination T n m =
      TapeMultiply.tapes (TapePower.resultRegister k outer destination) source scratch
        (TapePower.resultRegister k destination outer) T (n * m ^ k) m 0 0 := by
  induction k generalizing outer destination n with
  | zero => simp [TapePower.resultTapes, TapePower.resultRegister]
  | succ k ih =>
      change TapePower.resultTapes k destination source scratch outer T (n * m) m =
        TapeMultiply.tapes (TapePower.resultRegister k destination outer) source scratch
          (TapePower.resultRegister k outer destination) T (n * m ^ (k + 1)) m 0 0
      rw [ih]
      congr 1
      rw [pow_succ]
      ring

theorem resultRegister_pair (k : ℕ) (outer destination : TapeRegister) :
    (TapePower.resultRegister k outer destination = outer ∧
      TapePower.resultRegister k destination outer = destination) ∨
    (TapePower.resultRegister k outer destination = destination ∧
      TapePower.resultRegister k destination outer = outer) := by
  induction k with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ k ih =>
      rcases ih with h | h
      · exact Or.inr ⟨h.2, h.1⟩
      · exact Or.inl ⟨h.2, h.1⟩

theorem resultRegister_ne (k : ℕ) {outer destination target : TapeRegister}
    (hot : outer ≠ target) (hdt : destination ≠ target) :
    TapePower.resultRegister k outer destination ≠ target := by
  rcases resultRegister_pair k outer destination with h | h
  · simpa only [h.1] using hot
  · simpa only [h.1] using hdt

private theorem frame_store {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (σ : TapeStore) (n m : ℕ)
    (hs : σ source = List.replicate m true) (hc : σ scratch = [])
    (hd : σ destination = []) :
    TapeMultiply.tapes outer source scratch destination (storeTapes σ) n m 0 0 =
      storeTapes (Function.update σ outer (List.replicate n true)) := by
  funext r
  by_cases ho : r = outer
  · subst r
    simp [TapeMultiply.tapes, storeTapes, counterTape]
  · by_cases hr : r = source
    · subst r
      simp [TapeMultiply.tapes, onPair, storeTapes, Function.update, Ne.symm hos,
        hs, counterTape]
    · by_cases hr' : r = scratch
      · subst r
        simp [TapeMultiply.tapes, onPair, storeTapes, Function.update, Ne.symm hoc,
          Ne.symm hsc, hc, counterTape]
      · by_cases hr'' : r = destination
        · subst r
          simp [TapeMultiply.tapes, onPair, storeTapes, Function.update, Ne.symm hod,
            Ne.symm hsd, Ne.symm hcd, hd, counterTape]
        · simp [TapeMultiply.tapes, onPair, storeTapes, Function.update, ho, hr, hr', hr'']

def outputStore (k : ℕ) (outer destination : TapeRegister) (σ : TapeStore) (c : ℕ) :
    TapeStore :=
  Function.update σ (TapePower.resultRegister k outer destination) (List.replicate (c ^ k) true)

theorem result_store (k : ℕ) {outer source scratch destination : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (σ : TapeStore) (c : ℕ) (ho : σ outer = [])
    (hs : σ source = List.replicate c true) (hc : σ scratch = [])
    (hd : σ destination = []) :
    TapePower.resultTapes k outer source scratch destination (storeTapes σ) 1 c =
      storeTapes (outputStore k outer destination σ c) := by
  rw [resultTapes_eq_frame]
  simp only [Nat.one_mul]
  unfold outputStore
  rcases resultRegister_pair k outer destination with ⟨hr, hr'⟩ | ⟨hr, hr'⟩
  · rw [hr, hr']
    exact frame_store hos hoc hod hsc hsd hcd σ (c ^ k) c hs hc hd
  · rw [hr, hr']
    exact frame_store (Ne.symm hsd) (Ne.symm hcd) (Ne.symm hod)
      hsc (Ne.symm hos) (Ne.symm hoc) σ (c ^ k) c hs hc ho

@[simp] theorem outputStore_result (k : ℕ) (outer destination : TapeRegister)
    (σ : TapeStore) (c : ℕ) :
    outputStore k outer destination σ c (TapePower.resultRegister k outer destination) =
      List.replicate (c ^ k) true := by
  simp [outputStore]

theorem outputStore_other (k : ℕ) (outer destination : TapeRegister)
    (σ : TapeStore) (c : ℕ) (r : TapeRegister)
    (hr : r ≠ TapePower.resultRegister k outer destination) :
    outputStore k outer destination σ c r = σ r := by
  simp [outputStore, Function.update, hr]

theorem outputStore_clear (k : ℕ) (outer destination : TapeRegister)
    (σ : TapeStore) (c : ℕ) (ho : σ outer = []) (hd : σ destination = []) :
    Function.update (outputStore k outer destination σ c)
      (TapePower.resultRegister k outer destination) [] = σ := by
  unfold outputStore
  rw [Function.update_idem]
  apply Function.update_eq_self_iff.mpr
  rcases resultRegister_pair k outer destination with h | h
  · simpa only [h.1] using ho.symm
  · simpa only [h.1] using hd.symm

abbrev State (k : ℕ) := IncState ⊕ (TapePower.State k ⊕ TapeUnaryCompare.State)

def program (k : ℕ) (outer source scratch destination target : TapeRegister) :
    TapeMultiProgram (State k) :=
  joinCode (incProgram outer)
    (joinCode (TapePower.program k outer source scratch destination)
      (TapeUnaryCompare.program (TapePower.resultRegister k outer destination) target)
      (fun _ => TapeUnaryCompare.State.scan .beginR))
    (fun _ => Sum.inl (TapePower.start k))

def start (k : ℕ) : State k := .inl IncState.start
def done (k : ℕ) (o : Ordering) : State k := .inr (.inr (.done o))

def cost (k c D : ℕ) : ℕ :=
  2 + 1 + TapePower.cost k 1 c + 1 + (4 * min (c ^ k) D + 7)

theorem runs_compare (k : ℕ) {outer source scratch destination target : TapeRegister}
    (hos : outer ≠ source) (hoc : outer ≠ scratch) (hod : outer ≠ destination)
    (hsc : source ≠ scratch) (hsd : source ≠ destination) (hcd : scratch ≠ destination)
    (hot : outer ≠ target) (hdt : destination ≠ target)
    (σ : TapeStore) (c D : ℕ) (ho : σ outer = [])
    (hs : σ source = List.replicate c true) (hc : σ scratch = [])
    (hd : σ destination = []) (ht : σ target = List.replicate D true) :
    RunsIn (program k outer source scratch destination target).step
      (cfg (start k) (storeTapes σ))
      (cfg (done k (TapeUnaryCompareScan.result (c ^ k) D))
        (storeTapes (outputStore k outer destination σ c))) (cost k c D) := by
  have hinc := increment outer (storeTapes σ) 0 (by simp [storeTapes, counterTape, ho])
  have hi : TapeMultiply.tapes outer source scratch destination (storeTapes σ) 1 c 0 0 =
      Function.update (storeTapes σ) outer (counterTape 1) := by
    simpa only [storeTapes_update, counterTape] using
      (frame_store hos hoc hod hsc hsd hcd σ 1 c hs hc hd)
  have hp := TapePower.runs_power k hos hoc hod hsc hsd hcd (storeTapes σ) 1 c
  rw [hi, result_store k hos hoc hod hsc hsd hcd σ c ho hs hc hd] at hp
  have hr : TapePower.resultRegister k outer destination ≠ target :=
    resultRegister_ne k hot hdt
  have hcmp := TapeUnaryCompare.runs_compare hr
    (storeTapes (outputStore k outer destination σ c)) (c ^ k) D
    (by simp [storeTapes])
    (by simp [storeTapes, outputStore, Function.update, Ne.symm hr, ht])
  have hpowerCompare := join_runs (TapePower.program k outer source scratch destination)
    (TapeUnaryCompare.program (TapePower.resultRegister k outer destination) target)
    (fun _ => TapeUnaryCompare.State.scan .beginR)
    hp (TapePower.program_done k outer source scratch destination _) hcmp
  have h := join_runs (incProgram outer)
    (joinCode (TapePower.program k outer source scratch destination)
      (TapeUnaryCompare.program (TapePower.resultRegister k outer destination) target)
      (fun _ => TapeUnaryCompare.State.scan .beginR))
    (fun _ => Sum.inl (TapePower.start k)) hinc rfl hpowerCompare
  simpa only [program, start, done, cost, Nat.add_assoc] using h

@[simp] theorem program_done (k : ℕ)
    (outer source scratch destination target : TapeRegister) (o : Ordering) (h : TapeHeads) :
    program k outer source scratch destination target (done k o) h = none := rfl

end TapePowerCompare
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeSearchBody

open TapeMultiProgram TapeRouting TapeUnary

def amount (two : Bool) : ℕ := if two then 2 else 1
def incrementCost (two : Bool) : ℕ := if two then 5 else 3

abbrev IncrementState := IncState ⊕ IncState

def tailProgram (two : Bool) (candidate : TapeRegister) : TapeMultiProgram IncState :=
  if two then incProgram candidate else fun _ _ => none

def incrementProgram (two : Bool) (candidate : TapeRegister) :
    TapeMultiProgram IncrementState :=
  joinCode (incProgram candidate) (tailProgram two candidate) (fun _ => IncState.start)

def incrementStart : IncrementState := .inl .start
def incrementDone (two : Bool) : IncrementState :=
  .inr (if two then IncState.done else IncState.start)

private theorem increment_store (r : TapeRegister) (σ : TapeStore) (c : ℕ)
    (hc : σ r = List.replicate c true) :
    RunsIn (incProgram r).step (cfg IncState.start (storeTapes σ))
      (cfg IncState.done
        (storeTapes (Function.update σ r (List.replicate (c + 1) true)))) 2 := by
  have h := increment r (storeTapes σ) c (by simp [storeTapes, counterTape, hc])
  simpa only [storeTapes_update, counterTape] using h

theorem runs_increment (two : Bool) (r : TapeRegister) (σ : TapeStore) (c : ℕ)
    (hc : σ r = List.replicate c true) :
    RunsIn (incrementProgram two r).step (cfg incrementStart (storeTapes σ))
      (cfg (incrementDone two)
        (storeTapes (Function.update σ r (List.replicate (c + amount two) true))))
      (incrementCost two) := by
  have hfirst := increment_store r σ c hc
  cases two with
  | false =>
      have hrest := RunsIn.refl (tailProgram false r).step
        (cfg IncState.start (storeTapes (Function.update σ r (List.replicate (c + 1) true))))
      have h := join_runs (incProgram r) (tailProgram false r)
        (fun _ => IncState.start) hfirst rfl hrest
      exact h
  | true =>
      have hsecond := increment_store r (Function.update σ r (List.replicate (c + 1) true))
        (c + 1) (by simp)
      simp only [Function.update_idem] at hsecond
      have h := join_runs (incProgram r) (tailProgram true r)
        (fun _ => IncState.start) hfirst rfl hsecond
      have ha : c + 1 + 1 = c + 2 := by omega
      simpa only [IncrementState, incrementProgram, incrementStart, incrementDone,
        amount, incrementCost, ite_true, ha] using h

@[simp] theorem increment_done (two : Bool) (r : TapeRegister) (h : TapeHeads) :
    incrementProgram two r (incrementDone two) h = none := by
  cases two <;> rfl

abbrev State := TapeErase.State ⊕ IncrementState

def program (k : ℕ) (two : Bool) (outer destination candidate : TapeRegister) :
    TapeMultiProgram State :=
  joinCode (TapeErase.code (TapePower.resultRegister k outer destination))
    (incrementProgram two candidate) (fun _ => incrementStart)

def start : State := .inl .start
def done (two : Bool) : State := .inr (incrementDone two)

def cost (k : ℕ) (two : Bool) (c : ℕ) : ℕ :=
  2 * c ^ k + 5 + 1 + incrementCost two

theorem runs_body (k : ℕ) (two : Bool) (outer destination candidate : TapeRegister)
    (σ : TapeStore) (c : ℕ) (ho : σ outer = []) (hd : σ destination = [])
    (hc : σ candidate = List.replicate c true) :
    RunsIn (program k two outer destination candidate).step
      (cfg start (storeTapes (TapePowerCompare.outputStore k outer destination σ c)))
      (cfg (done two)
        (storeTapes (Function.update σ candidate (List.replicate (c + amount two) true))))
      (cost k two c) := by
  have he := TapeStoreRuns.erase (TapePower.resultRegister k outer destination)
    (TapePowerCompare.outputStore k outer destination σ c)
  simp only [TapePowerCompare.outputStore_result, List.length_replicate,
    TapePowerCompare.outputStore_clear k outer destination σ c ho hd] at he
  have hi := runs_increment two candidate σ c hc
  have h := join_runs (TapeErase.code (TapePower.resultRegister k outer destination))
    (incrementProgram two candidate) (fun _ => incrementStart) he rfl hi
  exact h

@[simp] theorem program_done (k : ℕ) (two : Bool)
    (outer destination candidate : TapeRegister) (h : TapeHeads) :
    program k two outer destination candidate (done two) h = none := by
  exact join_done _ _ _ (incrementDone two) h (increment_done two candidate h)

end TapeSearchBody
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

def dataDimension (n : ℕ) : ℕ := n / 5

theorem five_mul_dataDimension_le (n : ℕ) : 5 * dataDimension n ≤ n := by
  unfold dataDimension
  omega

theorem lt_five_mul_dataDimension_add_five (n : ℕ) :
    n < 5 * dataDimension n + 5 := by
  unfold dataDimension
  omega

theorem dataDimension_eq_zero_iff (n : ℕ) : dataDimension n = 0 ↔ n < 5 := by
  unfold dataDimension
  omega

theorem hashDimension_exists (d : ℕ) (hd : 0 < d) :
    ∃ r : ℕ, 0 < r ∧ d ^ 2 ≤ r ^ 3 :=
  ⟨d, hd, Nat.pow_le_pow_right hd (by decide)⟩

def hashDimension (d : ℕ) : ℕ :=
  if hd : d = 0 then 0
  else Nat.find (hashDimension_exists d (Nat.pos_of_ne_zero hd))

@[simp] theorem hashDimension_zero : hashDimension 0 = 0 := by
  simp [hashDimension]

theorem hashDimension_spec {d : ℕ} (hd : 0 < d) :
    0 < hashDimension d ∧ d ^ 2 ≤ hashDimension d ^ 3 := by
  rw [hashDimension, dite_eq_right (Nat.ne_of_gt hd)]
  exact Nat.find_spec (hashDimension_exists d hd)

theorem hashDimension_pos {d : ℕ} (hd : 0 < d) : 0 < hashDimension d :=
  (hashDimension_spec hd).1

theorem hashDimension_cube_bound (d : ℕ) : d ^ 2 ≤ hashDimension d ^ 3 := by
  by_cases hd : d = 0
  · subst d
    simp
  · exact (hashDimension_spec (Nat.pos_of_ne_zero hd)).2

theorem hashDimension_minimal {d r : ℕ} (hd : 0 < d)
    (hr : 0 < r) (hcube : d ^ 2 ≤ r ^ 3) : hashDimension d ≤ r := by
  rw [hashDimension, dite_eq_right (Nat.ne_of_gt hd)]
  exact Nat.find_min' _ ⟨hr, hcube⟩

theorem hashDimension_le (d : ℕ) : hashDimension d ≤ d := by
  by_cases hd : d = 0
  · subst d
    simp
  · have hd' := Nat.pos_of_ne_zero hd
    exact hashDimension_minimal hd' hd' (Nat.pow_le_pow_right hd' (by decide))

theorem hashDimension_le_iff {d r : ℕ} (hd : 0 < d) :
    hashDimension d ≤ r ↔ 0 < r ∧ d ^ 2 ≤ r ^ 3 := by
  constructor
  · intro hr
    exact ⟨lt_of_lt_of_le (hashDimension_pos hd) hr,
      Nat.le_trans (hashDimension_cube_bound d) (Nat.pow_le_pow_left hr 3)⟩
  · rintro ⟨hr, hcube⟩
    exact hashDimension_minimal hd hr hcube

theorem nat_le_sixth_power (j : ℕ) : j ≤ j ^ 6 := by
  by_cases hj : j = 0
  · subst j
    simp
  · simpa only [Nat.pow_one] using
      (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hj) (show 1 ≤ 6 by decide))

theorem sixth_power_le_implies_le {j d : ℕ} (hj : j ^ 6 ≤ d) : j ≤ d :=
  Nat.le_trans (nat_le_sixth_power j) hj

def independenceOrder (d : ℕ) : ℕ :=
  Nat.findGreatest (fun t => Even t ∧ t ^ 6 ≤ d) d

@[simp] theorem independenceOrder_zero : independenceOrder 0 = 0 := rfl

theorem independenceOrder_spec (d : ℕ) :
    Even (independenceOrder d) ∧ independenceOrder d ^ 6 ≤ d := by
  exact Nat.findGreatest_spec (P := fun t => Even t ∧ t ^ 6 ≤ d)
    (Nat.zero_le d) ⟨⟨0, rfl⟩, by simp⟩

theorem independenceOrder_even (d : ℕ) : Even (independenceOrder d) :=
  (independenceOrder_spec d).1

theorem independenceOrder_pow_le (d : ℕ) : independenceOrder d ^ 6 ≤ d :=
  (independenceOrder_spec d).2

theorem independenceOrder_le (d : ℕ) : independenceOrder d ≤ d :=
  Nat.findGreatest_le d

theorem independenceOrder_greatest {d j : ℕ} (hj : Even j) (hpow : j ^ 6 ≤ d) :
    j ≤ independenceOrder d :=
  Nat.le_findGreatest (sixth_power_le_implies_le hpow) ⟨hj, hpow⟩

theorem independenceOrder_two_le_iff (d : ℕ) :
    2 ≤ independenceOrder d ↔ 64 ≤ d := by
  constructor
  · intro ht
    calc
      64 = (2 : ℕ) ^ 6 := rfl
      _ ≤ independenceOrder d ^ 6 := Nat.pow_le_pow_left ht 6
      _ ≤ d := independenceOrder_pow_le d
  · intro hd
    exact independenceOrder_greatest ⟨1, rfl⟩ (show (2 : ℕ) ^ 6 ≤ d from hd)

theorem independenceOrder_eq_zero_iff (d : ℕ) :
    independenceOrder d = 0 ↔ d < 64 := by
  have ht := independenceOrder_two_le_iff d
  obtain ⟨k, hk⟩ := independenceOrder_even d
  constructor <;> intro h <;> omega

theorem independenceOrder_next_pow_gt (d : ℕ) :
    d < (independenceOrder d + 2) ^ 6 := by
  by_contra h
  have hpow : (independenceOrder d + 2) ^ 6 ≤ d := Nat.le_of_not_gt h
  have heven : Even (independenceOrder d + 2) := by
    obtain ⟨k, hk⟩ := independenceOrder_even d
    exact ⟨k + 1, by omega⟩
  have hle := independenceOrder_greatest heven hpow
  omega

theorem independenceOrder_eq_iff (d j : ℕ) :
    independenceOrder d = j ↔
      Even j ∧ j ^ 6 ≤ d ∧ ∀ k : ℕ, Even k → k ^ 6 ≤ d → k ≤ j := by
  constructor
  · intro h
    subst j
    exact ⟨independenceOrder_even d, independenceOrder_pow_le d,
      fun _ hk hp => independenceOrder_greatest hk hp⟩
  · rintro ⟨hj, hp, hmax⟩
    exact le_antisymm (hmax _ (independenceOrder_even d) (independenceOrder_pow_le d))
      (independenceOrder_greatest hj hp)

theorem independenceOrder_dataDimension_two_le_iff (n : ℕ) :
    2 ≤ independenceOrder (dataDimension n) ↔ 320 ≤ n := by
  rw [independenceOrder_two_le_iff]
  unfold dataDimension
  omega

def hashBlockLength (d : ℕ) : ℕ := d + hashDimension d - 1

def hashOffset (d : ℕ) : ℕ := d

def polynomialOffset (d : ℕ) : ℕ := hashOffset d + hashBlockLength d

def coefficientsOffset (d : ℕ) : ℕ := polynomialOffset d + hashDimension d

def coefficientOffset (d j : ℕ) : ℕ := coefficientsOffset d + j * hashDimension d

def blockLen (d : ℕ) : ℕ :=
  coefficientsOffset d + independenceOrder d * hashDimension d

theorem polynomialOffset_eq (d : ℕ) :
    polynomialOffset d = d + (d + hashDimension d - 1) := rfl

theorem coefficientsOffset_eq (d : ℕ) :
    coefficientsOffset d = d + (d + hashDimension d - 1) + hashDimension d := rfl

theorem blockLen_eq_sum (d : ℕ) :
    blockLen d = d + (d + hashDimension d - 1) + hashDimension d +
      independenceOrder d * hashDimension d := rfl

theorem blockLen_eq {d : ℕ} (hd : 0 < d) :
    blockLen d = 2 * d + (independenceOrder d + 2) * hashDimension d - 1 := by
  rw [blockLen_eq_sum]
  simp only [Nat.add_mul]
  omega

theorem hashBlockLength_pos {d : ℕ} (hd : 0 < d) : 0 < hashBlockLength d := by
  have hr := hashDimension_pos hd
  unfold hashBlockLength
  omega

theorem hashOffset_le_polynomialOffset (d : ℕ) : hashOffset d ≤ polynomialOffset d := by
  unfold polynomialOffset
  omega

theorem polynomialOffset_le_coefficientsOffset (d : ℕ) :
    polynomialOffset d ≤ coefficientsOffset d := by
  unfold coefficientsOffset
  omega

theorem coefficientsOffset_le_blockLen (d : ℕ) : coefficientsOffset d ≤ blockLen d := by
  unfold blockLen
  omega

@[simp] theorem coefficientOffset_zero (d : ℕ) :
    coefficientOffset d 0 = coefficientsOffset d := by
  simp [coefficientOffset]

theorem coefficientOffset_succ (d j : ℕ) :
    coefficientOffset d (j + 1) = coefficientOffset d j + hashDimension d := by
  simp only [coefficientOffset, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

theorem coefficientOffset_last (d : ℕ) :
    coefficientOffset d (independenceOrder d) = blockLen d := rfl

theorem coefficientOffset_mono (d : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    coefficientOffset d j ≤ coefficientOffset d k :=
  Nat.add_le_add_left (Nat.mul_le_mul_right (hashDimension d) hjk) _

theorem hash_index_lt {d i s : ℕ} (hi : i < hashDimension d) (hs : s < d) :
    i + s < hashBlockLength d := by
  unfold hashBlockLength
  omega

theorem hash_absolute_index_lt {d i s : ℕ}
    (hi : i < hashDimension d) (hs : s < d) :
    hashOffset d + (i + s) < polynomialOffset d :=
  Nat.add_lt_add_left (hash_index_lt hi hs) _

theorem polynomial_index_lt {d i : ℕ} (hi : i < hashDimension d) :
    polynomialOffset d + i < coefficientsOffset d :=
  Nat.add_lt_add_left hi _

theorem coefficient_index_lt {d j i : ℕ}
    (hj : j < independenceOrder d) (hi : i < hashDimension d) :
    coefficientOffset d j + i < blockLen d := by
  have hmul := Nat.mul_le_mul_right (hashDimension d) (Nat.succ_le_of_lt hj)
  simp only [Nat.succ_mul] at hmul
  unfold coefficientOffset blockLen
  omega

theorem blockLen_le_quad (d : ℕ) : blockLen d ≤ d * d + 4 * d := by
  have hr := hashDimension_le d
  have hmul := Nat.mul_le_mul (independenceOrder_le d) hr
  rw [blockLen_eq_sum]
  omega

theorem blockLen_le_four_mul_sub_one {d : ℕ} (hd : 0 < d) (hlt : d < 64) :
    blockLen d ≤ 4 * d - 1 := by
  rw [blockLen_eq hd, (independenceOrder_eq_zero_iff d).mpr hlt]
  have hr := hashDimension_le d
  simp only [Nat.zero_add]
  omega

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

theorem cube_lt_iff_lt_hashDimension (d r : ℕ) :
    r ^ 3 < d ^ 2 ↔ r < hashDimension d := by
  by_cases hd : d = 0
  · subst d
    simp
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    constructor
    · intro h
      by_contra hn
      have hle : hashDimension d ≤ r := Nat.le_of_not_gt hn
      have hc := Nat.le_trans (hashDimension_cube_bound d)
        (Nat.pow_le_pow_left hle 3)
      omega
    · intro h
      by_contra hn
      have hc : d ^ 2 ≤ r ^ 3 := Nat.le_of_not_gt hn
      have hr : 0 < r := by
        by_contra hz
        have he : r = 0 := by omega
        have hp : 0 < d ^ 2 := Nat.pow_pos hdpos
        simp only [he, Nat.zero_pow (by decide : 0 < 3)] at hc
        omega
      have hm := hashDimension_minimal hdpos hr hc
      omega

theorem next_sixth_le_iff_lt_independenceOrder (d k : ℕ) (hk : Even k) :
    (k + 2) ^ 6 ≤ d ↔ k < independenceOrder d := by
  have hnext : Even (k + 2) := by
    obtain ⟨a, ha⟩ := hk
    exact ⟨a + 1, by omega⟩
  constructor
  · intro hp
    have hm := independenceOrder_greatest hnext hp
    omega
  · intro hlt
    have ht := independenceOrder_even d
    have hle : k + 2 ≤ independenceOrder d := by
      obtain ⟨a, ha⟩ := hk
      obtain ⟨b, hb⟩ := ht
      omega
    exact Nat.le_trans (Nat.pow_le_pow_left hle 6) (independenceOrder_pow_le d)

theorem cube_search_candidate_le_data {d r : ℕ} (h : r ≤ hashDimension d) : r ≤ d :=
  Nat.le_trans h (hashDimension_le d)

theorem sixth_search_candidate_le_data {d k : ℕ} (h : k ≤ independenceOrder d) : k ≤ d :=
  Nat.le_trans h (independenceOrder_le d)

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapePowerSearch

open TapeMultiProgram TapeRouting TapeUnary

abbrev Registers := Fin 5 ↪ TapeRegister

def candidateStore (R : Registers) (σ : TapeStore) (c : ℕ) : TapeStore :=
  Function.update σ (R 1) (List.replicate c true)

def flag (k : ℕ) (again : Ordering → Bool) : TapePowerCompare.State k → Bool
  | .inr (.inr (.done o)) => again o
  | _ => false

abbrev State (k : ℕ) := LoopState (TapePowerCompare.State k) TapeSearchBody.State

def program (k : ℕ) (two : Bool) (again : Ordering → Bool) (R : Registers) :
    TapeMultiProgram (State k) :=
  loopCode (TapePowerCompare.program k (R 0) (R 1) (R 2) (R 3) (R 4))
    (TapeSearchBody.program k two (R 0) (R 3) (R 1))
    (TapePowerCompare.start k) TapeSearchBody.start (flag k again)

def start (k : ℕ) : State k := loopTest (TapePowerCompare.start k)
def done (k : ℕ) : State k := loopDone

def cost (k : ℕ) (two : Bool) (D : ℕ) : ℕ → ℕ → ℕ
  | 0, c => TapePowerCompare.cost k c D + 1
  | fuel + 1, c => TapePowerCompare.cost k c D + 1 + TapeSearchBody.cost k two c + 1 +
      cost k two D fuel (c + TapeSearchBody.amount two)

private theorem runs_test (k : ℕ) (R : Registers) (σ : TapeStore) (c D : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate D true) :
    RunsIn (TapePowerCompare.program k (R 0) (R 1) (R 2) (R 3) (R 4)).step
      (cfg (TapePowerCompare.start k) (storeTapes (candidateStore R σ c)))
      (cfg (TapePowerCompare.done k (TapeUnaryCompareScan.result (c ^ k) D))
        (storeTapes (TapePowerCompare.outputStore k (R 0) (R 3)
          (candidateStore R σ c) c))) (TapePowerCompare.cost k c D) := by
  apply TapePowerCompare.runs_compare k (outer := R 0) (source := R 1)
    (scratch := R 2) (destination := R 3) (target := R 4)
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (candidateStore R σ c) c D
  · simpa [candidateStore, R.injective.ne (by decide : (0 : Fin 5) ≠ 1)] using ho
  · simp [candidateStore]
  · simpa [candidateStore, R.injective.ne (by decide : (2 : Fin 5) ≠ 1)] using hs
  · simpa [candidateStore, R.injective.ne (by decide : (3 : Fin 5) ≠ 1)] using hd
  · simpa [candidateStore, R.injective.ne (by decide : (4 : Fin 5) ≠ 1)] using ht

theorem runs_search (k : ℕ) (two : Bool) (again : Ordering → Bool) (R : Registers)
    (σ : TapeStore) (D fuel c : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate D true)
    (hgo : ∀ j < fuel, again (TapeUnaryCompareScan.result
      ((c + TapeSearchBody.amount two * j) ^ k) D) = true)
    (hstop : again (TapeUnaryCompareScan.result
      ((c + TapeSearchBody.amount two * fuel) ^ k) D) = false) :
    RunsIn (program k two again R).step
      (cfg (start k) (storeTapes (candidateStore R σ c)))
      (cfg (done k) (storeTapes (TapePowerCompare.outputStore k (R 0) (R 3)
        (candidateStore R σ (c + TapeSearchBody.amount two * fuel))
        (c + TapeSearchBody.amount two * fuel))))
      (cost k two D fuel c) := by
  induction fuel generalizing c with
  | zero =>
      have htst := runs_test k R σ c D ho hs hd ht
      have he := loop_exit
        (TapePowerCompare.program k (R 0) (R 1) (R 2) (R 3) (R 4))
        (TapeSearchBody.program k two (R 0) (R 3) (R 1))
        (TapePowerCompare.start k) TapeSearchBody.start (flag k again)
        htst rfl (by simpa only [flag, TapePowerCompare.done, Nat.mul_zero,
          Nat.add_zero] using hstop)
      simpa only [program, start, done, cost, Nat.mul_zero, Nat.add_zero] using he
  | succ fuel ih =>
      have htst := runs_test k R σ c D ho hs hd ht
      have hb := TapeSearchBody.runs_body k two (R 0) (R 3) (R 1)
        (candidateStore R σ c) c
        (by simpa [candidateStore, R.injective.ne (by decide : (0 : Fin 5) ≠ 1)] using ho)
        (by simpa [candidateStore, R.injective.ne (by decide : (3 : Fin 5) ≠ 1)] using hd)
        (by simp [candidateStore])
      simp only [candidateStore, Function.update_idem] at hb
      have hi := loop_iter
        (TapePowerCompare.program k (R 0) (R 1) (R 2) (R 3) (R 4))
        (TapeSearchBody.program k two (R 0) (R 3) (R 1))
        (TapePowerCompare.start k) TapeSearchBody.start (flag k again)
        htst rfl (by simpa only [flag, TapePowerCompare.done, Nat.mul_zero,
          Nat.add_zero] using hgo 0 (Nat.zero_lt_succ _))
        hb (TapeSearchBody.program_done k two (R 0) (R 3) (R 1) _)
      have hshift (j : ℕ) :
          c + TapeSearchBody.amount two + TapeSearchBody.amount two * j =
            c + TapeSearchBody.amount two * (j + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have hr := ih (c + TapeSearchBody.amount two)
        (by
          intro j hj
          rw [hshift]
          exact hgo (j + 1) (Nat.succ_lt_succ hj))
        (by rw [hshift]; exact hstop)
      have h := hi.trans hr
      simpa only [program, start, done, cost, candidateStore, hshift] using h

@[simp] theorem program_done (k : ℕ) (two : Bool) (again : Ordering → Bool)
    (R : Registers) (h : TapeHeads) : program k two again R (done k) h = none := rfl

def continueLt (o : Ordering) : Bool := decide (o = .lt)
def continueLe (o : Ordering) : Bool := !decide (o = .gt)

theorem continueLt_result (a b : ℕ) :
    continueLt (TapeUnaryCompareScan.result a b) = decide (a < b) := by
  simp [continueLt, TapeUnaryCompareScan.result_eq_lt_iff]

theorem continueLe_result (a b : ℕ) :
    continueLe (TapeUnaryCompareScan.result a b) = decide (a ≤ b) := by
  by_cases h : a ≤ b
  · have hnot : ¬ b < a := by omega
    simp [continueLe, TapeUnaryCompareScan.result_eq_gt_iff, h, hnot]
  · have hlt : b < a := by omega
    simp [continueLe, TapeUnaryCompareScan.result_eq_gt_iff, h, hlt]

theorem runs_cube (R : Registers) (σ : TapeStore) (d : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate (d ^ 2) true) :
    RunsIn (program 3 false continueLt R).step
      (cfg (start 3) (storeTapes (candidateStore R σ 0)))
      (cfg (done 3) (storeTapes (TapePowerCompare.outputStore 3 (R 0) (R 3)
        (candidateStore R σ (hashDimension d)) (hashDimension d))))
      (cost 3 false (d ^ 2) (hashDimension d) 0) := by
  have h := runs_search 3 false continueLt R σ (d ^ 2) (hashDimension d) 0
    ho hs hd ht
    (by
      intro j hj
      have hjp := (cube_lt_iff_lt_hashDimension d j).2 hj
      simpa [TapeSearchBody.amount, continueLt_result] using hjp)
    (by
      have hp := hashDimension_cube_bound d
      simp [TapeSearchBody.amount, continueLt_result, Nat.not_lt.mpr hp])
  simpa [TapeSearchBody.amount] using h

theorem runs_sixth_boundary (R : Registers) (σ : TapeStore) (d : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate d true) :
    RunsIn (program 6 true continueLe R).step
      (cfg (start 6) (storeTapes (candidateStore R σ 0)))
      (cfg (done 6) (storeTapes (TapePowerCompare.outputStore 6 (R 0) (R 3)
        (candidateStore R σ (independenceOrder d + 2)) (independenceOrder d + 2))))
      (cost 6 true d (independenceOrder d / 2 + 1) 0) := by
  have htEven := independenceOrder_even d
  have hterminal : 2 * (independenceOrder d / 2 + 1) = independenceOrder d + 2 := by
    obtain ⟨a, ha⟩ := htEven
    omega
  have h := runs_search 6 true continueLe R σ d (independenceOrder d / 2 + 1) 0
    ho hs hd ht
    (by
      intro j hj
      have hjle : 2 * j ≤ independenceOrder d := by omega
      have hp := Nat.le_trans (Nat.pow_le_pow_left hjle 6) (independenceOrder_pow_le d)
      simpa [TapeSearchBody.amount, continueLe_result] using hp)
    (by
      have hp := independenceOrder_next_pow_gt d
      simp [TapeSearchBody.amount, continueLe_result, hterminal, Nat.not_le.mpr hp])
  simpa [TapeSearchBody.amount, hterminal] using h

end TapePowerSearch
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeParameterSearch

open TapeMultiProgram TapeRouting TapeUnary TapePowerSearch

private theorem erase_output (k : ℕ) (R : Registers) (σ : TapeStore) (c : ℕ)
    (ho : σ (R 0) = []) (hd : σ (R 3) = []) :
    RunsIn (TapeErase.code (TapePower.resultRegister k (R 0) (R 3))).step
      (cfg TapeErase.State.start (storeTapes (TapePowerCompare.outputStore k (R 0) (R 3)
        (candidateStore R σ c) c)))
      (cfg TapeErase.State.done (storeTapes (candidateStore R σ c))) (2 * c ^ k + 5) := by
  have h := TapeStoreRuns.erase (TapePower.resultRegister k (R 0) (R 3))
    (TapePowerCompare.outputStore k (R 0) (R 3) (candidateStore R σ c) c)
  have ho' : candidateStore R σ c (R 0) = [] := by
    simpa [candidateStore, R.injective.ne (by decide : (0 : Fin 5) ≠ 1)] using ho
  have hd' : candidateStore R σ c (R 3) = [] := by
    simpa [candidateStore, R.injective.ne (by decide : (3 : Fin 5) ≠ 1)] using hd
  simpa only [TapePowerCompare.outputStore_result, List.length_replicate,
    TapePowerCompare.outputStore_clear k (R 0) (R 3) (candidateStore R σ c) c ho' hd'] using h

private theorem decrement_candidate (R : Registers) (σ : TapeStore) (c : ℕ) :
    RunsIn (decProgram (R 1)).step
      (cfg DecState.start (storeTapes (candidateStore R σ (c + 1))))
      (cfg (DecState.done true) (storeTapes (candidateStore R σ c))) 4 := by
  have h := decrement_cons (R 1) (storeTapes (candidateStore R σ (c + 1)))
    (List.replicate c true) true (by
      simp [storeTapes, candidateStore, List.replicate_succ])
  have he : Function.update (storeTapes (candidateStore R σ (c + 1))) (R 1)
      (wordTape (List.replicate c true)) = storeTapes (candidateStore R σ c) := by
    rw [← storeTapes_update]
    simp [candidateStore]
  simpa only [he] using h

abbrev CubeState := TapePowerSearch.State 3 ⊕ TapeErase.State

def cubeProgram (R : Registers) : TapeMultiProgram CubeState :=
  joinCode (TapePowerSearch.program 3 false continueLt R)
    (TapeErase.code (TapePower.resultRegister 3 (R 0) (R 3)))
    (fun _ => TapeErase.State.start)

def cubeStart : CubeState := .inl (TapePowerSearch.start 3)
def cubeDone : CubeState := .inr .done

def cubeCost (d : ℕ) : ℕ :=
  TapePowerSearch.cost 3 false (d ^ 2) (hashDimension d) 0 + 1 +
    (2 * (hashDimension d) ^ 3 + 5)

theorem runs_cube (R : Registers) (σ : TapeStore) (d : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate (d ^ 2) true) :
    RunsIn (cubeProgram R).step
      (cfg cubeStart (storeTapes (candidateStore R σ 0)))
      (cfg cubeDone (storeTapes (candidateStore R σ (hashDimension d))))
      (cubeCost d) := by
  have hc := TapePowerSearch.runs_cube R σ d ho hs hd ht
  have he := erase_output 3 R σ (hashDimension d) ho hd
  exact join_runs _ _ _ hc rfl he

@[simp] theorem cube_done (R : Registers) (h : TapeHeads) :
    cubeProgram R cubeDone h = none := rfl

abbrev DecreaseState := DecState ⊕ DecState

def decreaseProgram (R : Registers) : TapeMultiProgram DecreaseState :=
  joinCode (decProgram (R 1)) (decProgram (R 1)) (fun _ => DecState.start)

def decreaseStart : DecreaseState := .inl .start
def decreaseDone : DecreaseState := .inr (.done true)

theorem runs_decrease (R : Registers) (σ : TapeStore) (c : ℕ) :
    RunsIn (decreaseProgram R).step
      (cfg decreaseStart (storeTapes (candidateStore R σ (c + 2))))
      (cfg decreaseDone (storeTapes (candidateStore R σ c))) 9 := by
  have h₁ := decrement_candidate R σ (c + 1)
  have h₂ := decrement_candidate R σ c
  have h := join_runs (decProgram (R 1)) (decProgram (R 1))
    (fun _ => DecState.start) h₁ rfl h₂
  have he : c + 1 + 1 = c + 2 := by omega
  simpa only [decreaseProgram, decreaseStart, decreaseDone, he] using h

abbrev CleanupState := TapeErase.State ⊕ DecreaseState

def cleanupProgram (R : Registers) : TapeMultiProgram CleanupState :=
  joinCode (TapeErase.code (TapePower.resultRegister 6 (R 0) (R 3)))
    (decreaseProgram R) (fun _ => decreaseStart)

def cleanupStart : CleanupState := .inl .start
def cleanupDone : CleanupState := .inr decreaseDone

theorem runs_cleanup (R : Registers) (σ : TapeStore) (c : ℕ)
    (ho : σ (R 0) = []) (hd : σ (R 3) = []) :
    RunsIn (cleanupProgram R).step
      (cfg cleanupStart (storeTapes (TapePowerCompare.outputStore 6 (R 0) (R 3)
        (candidateStore R σ (c + 2)) (c + 2))))
      (cfg cleanupDone (storeTapes (candidateStore R σ c)))
      (2 * (c + 2) ^ 6 + 5 + 1 + 9) := by
  have he := erase_output 6 R σ (c + 2) ho hd
  have hd := runs_decrease R σ c
  exact join_runs _ _ _ he rfl hd

abbrev SixthState := TapePowerSearch.State 6 ⊕ CleanupState

def sixthProgram (R : Registers) : TapeMultiProgram SixthState :=
  joinCode (TapePowerSearch.program 6 true continueLe R) (cleanupProgram R)
    (fun _ => cleanupStart)

def sixthStart : SixthState := .inl (TapePowerSearch.start 6)
def sixthDone : SixthState := .inr cleanupDone

def sixthCost (d : ℕ) : ℕ :=
  TapePowerSearch.cost 6 true d (independenceOrder d / 2 + 1) 0 + 1 +
    (2 * (independenceOrder d + 2) ^ 6 + 5 + 1 + 9)

theorem runs_sixth (R : Registers) (σ : TapeStore) (d : ℕ)
    (ho : σ (R 0) = []) (hs : σ (R 2) = []) (hd : σ (R 3) = [])
    (ht : σ (R 4) = List.replicate d true) :
    RunsIn (sixthProgram R).step
      (cfg sixthStart (storeTapes (candidateStore R σ 0)))
      (cfg sixthDone (storeTapes (candidateStore R σ (independenceOrder d))))
      (sixthCost d) := by
  have hs := TapePowerSearch.runs_sixth_boundary R σ d ho hs hd ht
  have hc := runs_cleanup R σ (independenceOrder d) ho hd
  exact join_runs _ _ _ hs rfl hc

@[simp] theorem sixth_done (R : Registers) (h : TapeHeads) :
    sixthProgram R sixthDone h = none := rfl

end TapeParameterSearch
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeDivideFive

open TapeMultiProgram TapeUnary TapeCopy TapeArithmetic

inductive State where
  | dec (phase : Fin 5) (q : DecState)
  | inc (q : IncState)
  | done (remainder : Fin 5)
  deriving DecidableEq, Fintype

def nextPhase (phase : Fin 5) : Fin 5 :=
  ⟨(phase.val + 1) % 5, Nat.mod_lt _ (by decide)⟩

def residue (n : ℕ) : Fin 5 := ⟨n % 5, Nat.mod_lt _ (by decide)⟩

def program (counter destination : TapeRegister) : TapeMultiProgram State
  | .dec phase q, h =>
      match decProgram counter q h with
      | some (q', writes, moves) => some (.dec phase q', writes, moves)
      | none =>
          match q with
          | .done false => jump (.done phase) h
          | .done true =>
              if phase.val = 4 then jump (.inc .start) h
              else jump (.dec (nextPhase phase) .start) h
          | _ => none
  | .inc q, h =>
      match incProgram destination q h with
      | some (q', writes, moves) => some (.inc q', writes, moves)
      | none => jump (.dec 0 .start) h
  | .done _, _ => none

private theorem dec_runs (counter destination : TapeRegister) (phase : Fin 5)
    {a b : DecState} {T U : TapeTapes} {n : ℕ}
    (h : RunsIn (decProgram counter).step (cfg a T) (cfg b U) n) :
    RunsIn (program counter destination).step
      (cfg (.dec phase a) T) (cfg (.dec phase b) U) n := by
  have he := runs_map (decProgram counter) (program counter destination)
    (State.dec phase) (by
      intro q heads q' writes moves hc
      simp only [program, hc]) h
  exact he

private theorem inc_runs (counter destination : TapeRegister)
    {a b : IncState} {T U : TapeTapes} {n : ℕ}
    (h : RunsIn (incProgram destination).step (cfg a T) (cfg b U) n) :
    RunsIn (program counter destination).step
      (cfg (.inc a) T) (cfg (.inc b) U) n := by
  have he := runs_map (incProgram destination) (program counter destination)
    State.inc (by
      intro q heads q' writes moves hc
      simp only [program, hc]) h
  exact he

theorem runs_phase {counter destination : TapeRegister} (hne : counter ≠ destination)
    (T : TapeTapes) (n m : ℕ) (phase : Fin 5) :
    RunsIn (program counter destination).step
      (cfg (.dec phase .start)
        (onPair counter destination T (counterTape n) (counterTape m)))
      (cfg (.done (residue (phase.val + n)))
        (onPair counter destination T (counterTape 0)
          (counterTape (m + (phase.val + n) / 5))))
      (8 * n + 3) := by
  induction n generalizing m phase with
  | zero =>
      have hd := decrement_empty counter
        (onPair counter destination T (counterTape 0) (counterTape m))
        (by simp [counterTape])
      have hrun := dec_runs counter destination phase hd
      have hj := step_jump (program counter destination)
        (.dec phase (.done false)) (.done phase)
        (onPair counter destination T (counterTape 0) (counterTape m)) rfl
      have hall := hrun.trans (RunsIn.single hj)
      have hr : residue phase.val = phase := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt phase.is_lt
      simpa only [Nat.add_zero, Nat.mul_zero, Nat.zero_add,
        Nat.div_eq_of_lt phase.is_lt, hr] using hall
  | succ n ih =>
      have hd := decrement_cons counter
        (onPair counter destination T (counterTape (n + 1)) (counterTape m))
        (List.replicate n true) true (by simp [counterTape, List.replicate_succ])
      simp only [update_onPair_src] at hd
      have hrun := dec_runs counter destination phase hd
      have hpBound := phase.is_lt
      by_cases hp : phase.val = 4
      · have hj := step_jump (program counter destination)
          (.dec phase (.done true)) (.inc .start)
          (onPair counter destination T (counterTape n) (counterTape m))
          (by simp [program, decProgram, hp])
        have hi := increment destination
          (onPair counter destination T (counterTape n) (counterTape m)) m
          (by simp [hne])
        simp only [update_onPair_dst hne] at hi
        have hinc := inc_runs counter destination hi
        have hk := step_jump (program counter destination) (.inc .done)
          (.dec 0 .start)
          (onPair counter destination T (counterTape n) (counterTape (m + 1))) rfl
        have hall := (((hrun.trans (RunsIn.single hj)).trans hinc).trans
          (RunsIn.single hk)).trans (ih (m + 1) 0)
        have hv : m + 1 + n / 5 = m + (phase.val + (n + 1)) / 5 := by omega
        have hr : residue (phase.val + (n + 1)) = residue n := by
          apply Fin.ext
          dsimp [residue]
          omega
        have ht : 4 + 1 + 2 + 1 + (8 * n + 3) = 8 * (n + 1) + 3 := by omega
        simpa only [Fin.val_zero, Nat.zero_add, hv, hr, ht] using hall
      · have hphase : phase.val + 1 < 5 := by omega
        have hnext : (nextPhase phase).val = phase.val + 1 :=
          Nat.mod_eq_of_lt hphase
        have hj := step_jump (program counter destination)
          (.dec phase (.done true)) (.dec (nextPhase phase) .start)
          (onPair counter destination T (counterTape n) (counterTape m))
          (by simp [program, decProgram, hp])
        have hall := (hrun.trans (RunsIn.single hj)).trans (ih m (nextPhase phase))
        have hv : (nextPhase phase).val + n = phase.val + (n + 1) := by omega
        have ht : 4 + 1 + (8 * n + 3) ≤ 8 * (n + 1) + 3 := by omega
        simpa only [hv] using hall.mono ht

theorem runs_divide {counter destination : TapeRegister} (hne : counter ≠ destination)
    (T : TapeTapes) (n m : ℕ) :
    RunsIn (program counter destination).step
      (cfg (.dec 0 .start)
        (onPair counter destination T (counterTape n) (counterTape m)))
      (cfg (.done (residue n))
        (onPair counter destination T (counterTape 0) (counterTape (m + n / 5))))
      (8 * n + 3) := by
  simpa only [Fin.val_zero, Nat.zero_add] using runs_phase hne T n m 0

@[simp] theorem done_halts (counter destination : TapeRegister) (r : Fin 5)
    (h : TapeHeads) : program counter destination (.done r) h = none := rfl

end TapeDivideFive
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeParameters

open TapeMultiProgram TapeRouting TapeUnary TapeCopy

def cubeRegisters : TapePowerSearch.Registers where
  toFun i := if i = 0 then 7 else if i = 1 then 3 else if i = 2 then 9
    else if i = 3 then 5 else 6
  inj' := by intro i j; fin_cases i <;> fin_cases j <;> decide

def sixthRegisters : TapePowerSearch.Registers where
  toFun i := if i = 0 then 7 else if i = 1 then 4 else if i = 2 then 9
    else if i = 3 then 5 else 2
  inj' := by intro i j; fin_cases i <;> fin_cases j <;> decide

@[simp] theorem cubeRegisters_zero : cubeRegisters 0 = 7 := rfl
@[simp] theorem cubeRegisters_one : cubeRegisters 1 = 3 := rfl
@[simp] theorem cubeRegisters_two : cubeRegisters 2 = 9 := rfl
@[simp] theorem cubeRegisters_three : cubeRegisters 3 = 5 := rfl
@[simp] theorem cubeRegisters_four : cubeRegisters 4 = 6 := rfl
@[simp] theorem sixthRegisters_zero : sixthRegisters 0 = 7 := rfl
@[simp] theorem sixthRegisters_one : sixthRegisters 1 = 4 := rfl
@[simp] theorem sixthRegisters_two : sixthRegisters 2 = 9 := rfl
@[simp] theorem sixthRegisters_three : sixthRegisters 3 = 5 := rfl
@[simp] theorem sixthRegisters_four : sixthRegisters 4 = 2 := rfl

def dataStore (σ : TapeStore) (n : ℕ) : TapeStore :=
  Function.update σ 2 (List.replicate (dataDimension n) true)

def outputStore (σ : TapeStore) (n : ℕ) : TapeStore :=
  Function.update
    (Function.update (dataStore σ n) 3 (List.replicate (hashDimension (dataDimension n)) true))
    4 (List.replicate (independenceOrder (dataDimension n)) true)

@[simp] theorem outputStore_data (σ : TapeStore) (n : ℕ) :
    outputStore σ n 2 = List.replicate (dataDimension n) true := by
  simp [outputStore, dataStore]

@[simp] theorem outputStore_hash (σ : TapeStore) (n : ℕ) :
    outputStore σ n 3 = List.replicate (hashDimension (dataDimension n)) true := by
  simp [outputStore]

@[simp] theorem outputStore_order (σ : TapeStore) (n : ℕ) :
    outputStore σ n 4 = List.replicate (independenceOrder (dataDimension n)) true := by
  simp [outputStore]

theorem outputStore_other (σ : TapeStore) (n : ℕ) (r : TapeRegister)
    (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) : outputStore σ n r = σ r := by
  simp [outputStore, dataStore, Function.update, h2, h3, h4]

abbrev LengthState := TapeCopy.State ⊕ TapeDivideFive.State

def lengthProgram : TapeMultiProgram LengthState :=
  joinCode (TapeCopy.code 1 5) (TapeDivideFive.program 5 2)
    (fun _ => TapeDivideFive.State.dec 0 .start)

def lengthStart : LengthState := .inl .start
def lengthDone (n : ℕ) : LengthState := .inr (.done (TapeDivideFive.residue n))

theorem runs_length (σ : TapeStore) (n : ℕ)
    (h1 : σ 1 = List.replicate n true) (h2 : σ 2 = []) (h5 : σ 5 = []) :
    RunsIn lengthProgram.step (cfg lengthStart (storeTapes σ))
      (cfg (lengthDone n) (storeTapes (dataStore σ n))) (10 * n + 8) := by
  let copied := Function.update σ 5 (List.replicate n true)
  have hcopy := TapeStoreRuns.copy (src := 1) (dst := 5) (by decide) σ h5
  simp only [h1, List.length_replicate] at hcopy
  have hi : onPair 5 2 (storeTapes copied) (counterTape n) (counterTape 0) =
      storeTapes copied :=
    TapeProductTerm.onPair_eq_self (by simp [copied, storeTapes, counterTape])
      (by simp [copied, storeTapes, counterTape, h2])
  have hrestore : Function.update copied 5 [] = σ := by
    dsimp [copied]
    rw [Function.update_idem]
    exact Function.update_eq_self_iff.mpr h5.symm
  have ho : onPair 5 2 (storeTapes copied) (counterTape 0) (counterTape (n / 5)) =
      storeTapes (dataStore σ n) := by
    have he : onPair 5 2 (storeTapes copied) (counterTape 0) (counterTape (n / 5)) =
        storeTapes (Function.update (Function.update copied 5 []) 2
          (List.replicate (n / 5) true)) := by
      rw [onPair_eq_updates (by decide : (5 : TapeRegister) ≠ 2)]
      simp only [storeTapes_update, counterTape, List.replicate_zero]
    simpa only [hrestore, dataStore, dataDimension] using he
  have hdivide := TapeDivideFive.runs_divide (counter := 5) (destination := 2)
    (by decide) (storeTapes copied) n 0
  simp only [Nat.zero_add, hi, ho] at hdivide
  have h := join_runs (TapeCopy.code 1 5) (TapeDivideFive.program 5 2)
    (fun _ => TapeDivideFive.State.dec 0 .start) hcopy rfl hdivide
  have hc : 2 * n + 4 + 1 + (8 * n + 3) = 10 * n + 8 := by omega
  simpa only [lengthProgram, lengthStart, lengthDone, copied, hc] using h

abbrev SquareState := IncState ⊕ TapePower.State 2

def squareProgram : TapeMultiProgram SquareState :=
  joinCode (incProgram 6) (TapePower.program 2 6 2 7 5) (fun _ => TapePower.start 2)

def squareStart : SquareState := .inl .start
def squareDone : SquareState := .inr (TapePower.done 2)
def squareCost (d : ℕ) : ℕ := 2 + 1 + TapePower.cost 2 1 d

theorem runs_square (σ : TapeStore) (d : ℕ)
    (h2 : σ 2 = List.replicate d true) (h5 : σ 5 = [])
    (h6 : σ 6 = []) (h7 : σ 7 = []) :
    RunsIn squareProgram.step (cfg squareStart (storeTapes σ))
      (cfg squareDone (storeTapes (Function.update σ 6 (List.replicate (d ^ 2) true))))
      (squareCost d) := by
  have hinc := increment 6 (storeTapes σ) 0 (by simp [storeTapes, counterTape, h6])
  have hinner : onPair 7 5 (storeTapes σ) (counterTape 0) (counterTape 0) =
      storeTapes σ := TapeProductTerm.onPair_eq_self
        (by simp [storeTapes, counterTape, h7]) (by simp [storeTapes, counterTape, h5])
  have houter : onPair 6 2 (storeTapes σ) (counterTape 0) (counterTape d) =
      storeTapes σ := TapeProductTerm.onPair_eq_self
        (by simp [storeTapes, counterTape, h6]) (by simp [storeTapes, counterTape, h2])
  have hi : TapeMultiply.tapes 6 2 7 5 (storeTapes σ) 1 d 0 0 =
      Function.update (storeTapes σ) 6 (counterTape 1) := by
    unfold TapeMultiply.tapes
    rw [hinner]
    simpa only [houter] using
      (TapeArithmetic.update_onPair_src 6 2 (storeTapes σ)
        (counterTape 0) (counterTape d) (counterTape 1)).symm
  have hp := TapePower.runs_power 2 (outer := 6) (source := 2) (scratch := 7)
    (destination := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (storeTapes σ) 1 d
  have ho := TapePowerCompare.result_store 2 (outer := 6) (source := 2) (scratch := 7)
    (destination := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) σ d h6 h2 h7 h5
  change TapePower.resultTapes 2 6 2 7 5 (storeTapes σ) 1 d =
    storeTapes (Function.update σ 6 (List.replicate (d ^ 2) true)) at ho
  rw [hi, ho] at hp
  exact join_runs _ _ _ hinc rfl hp

abbrev FinishState := TapeErase.State ⊕ TapeParameterSearch.SixthState

def finishProgram : TapeMultiProgram FinishState :=
  joinCode (TapeErase.code 6) (TapeParameterSearch.sixthProgram sixthRegisters)
    (fun _ => TapeParameterSearch.sixthStart)

def finishStart : FinishState := .inl .start
def finishDone : FinishState := .inr TapeParameterSearch.sixthDone

abbrev RootsState := TapeParameterSearch.CubeState ⊕ FinishState

def rootsProgram : TapeMultiProgram RootsState :=
  joinCode (TapeParameterSearch.cubeProgram cubeRegisters) finishProgram (fun _ => finishStart)

def rootsStart : RootsState := .inl TapeParameterSearch.cubeStart
def rootsDone : RootsState := .inr finishDone

abbrev WorkState := SquareState ⊕ RootsState

def workProgram : TapeMultiProgram WorkState :=
  joinCode squareProgram rootsProgram (fun _ => rootsStart)

def workStart : WorkState := .inl squareStart
def workDone : WorkState := .inr rootsDone

abbrev State := LengthState ⊕ WorkState

def program : TapeMultiProgram State :=
  joinCode lengthProgram workProgram (fun _ => workStart)

def start : State := .inl lengthStart
def done : State := .inr workDone

def cost (n : ℕ) : ℕ :=
  10 * n + 2 * (dataDimension n) ^ 2 + 20 + TapePower.cost 2 1 (dataDimension n) +
    TapeParameterSearch.cubeCost (dataDimension n) +
    TapeParameterSearch.sixthCost (dataDimension n)

private theorem candidate_zero (R : TapePowerSearch.Registers) (σ : TapeStore)
    (h : σ (R 1) = []) : TapePowerSearch.candidateStore R σ 0 = σ := by
  change Function.update σ (R 1) [] = σ
  exact Function.update_eq_self_iff.mpr h.symm

theorem runs_parameters (σ : TapeStore) (n : ℕ)
    (h1 : σ 1 = List.replicate n true)
    (h2 : σ 2 = []) (h3 : σ 3 = []) (h4 : σ 4 = [])
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h7 : σ 7 = []) (h9 : σ 9 = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (outputStore σ n))) (cost n) := by
  let d := dataDimension n
  let σD := dataStore σ n
  let σS := Function.update σD 6 (List.replicate (d ^ 2) true)
  let σC := Function.update σS 3 (List.replicate (hashDimension d) true)
  let σR := Function.update σD 3 (List.replicate (hashDimension d) true)
  have hlength := runs_length σ n h1 h2 h5
  have hsquare := runs_square σD d (by simp [σD, dataStore, d])
    (by simpa [σD, dataStore] using h5) (by simpa [σD, dataStore] using h6)
    (by simpa [σD, dataStore] using h7)
  have hcube := TapeParameterSearch.runs_cube cubeRegisters σS d
    (by simpa [σS, σD, dataStore] using h7)
    (by simpa [σS, σD, dataStore] using h9)
    (by simpa [σS, σD, dataStore] using h5)
    (by simp [σS])
  have hc0 : TapePowerSearch.candidateStore cubeRegisters σS 0 = σS :=
    candidate_zero cubeRegisters σS (by simpa [σS, σD, dataStore] using h3)
  rw [hc0] at hcube
  change RunsIn (TapeParameterSearch.cubeProgram cubeRegisters).step
    (cfg TapeParameterSearch.cubeStart (storeTapes σS))
    (cfg TapeParameterSearch.cubeDone (storeTapes σC))
    (TapeParameterSearch.cubeCost d) at hcube
  have herase := TapeStoreRuns.erase 6 σC
  have hclear : Function.update σC 6 [] = σR := by
    funext r
    by_cases hr : r = 6
    · subst r
      simp [σR, σD, dataStore, h6]
    · simp [σC, σR, σS, Function.update, hr]
  have hc6 : σC 6 = List.replicate (d ^ 2) true := by simp [σC, σS]
  rw [hclear, hc6, List.length_replicate] at herase
  have hsixth := TapeParameterSearch.runs_sixth sixthRegisters σR d
    (by simpa [σR, σD, dataStore] using h7)
    (by simpa [σR, σD, dataStore] using h9)
    (by simpa [σR, σD, dataStore] using h5)
    (by simp [σR, σD, dataStore, d])
  have hs0 : TapePowerSearch.candidateStore sixthRegisters σR 0 = σR :=
    candidate_zero sixthRegisters σR (by simpa [σR, σD, dataStore] using h4)
  rw [hs0] at hsixth
  change RunsIn (TapeParameterSearch.sixthProgram sixthRegisters).step
    (cfg TapeParameterSearch.sixthStart (storeTapes σR))
    (cfg TapeParameterSearch.sixthDone (storeTapes (outputStore σ n)))
    (TapeParameterSearch.sixthCost d) at hsixth
  have hfinish := join_runs (TapeErase.code 6) (TapeParameterSearch.sixthProgram sixthRegisters)
    (fun _ => TapeParameterSearch.sixthStart) herase rfl hsixth
  have hroots := join_runs (TapeParameterSearch.cubeProgram cubeRegisters) finishProgram
    (fun _ => finishStart) hcube rfl hfinish
  have hwork := join_runs squareProgram rootsProgram (fun _ => rootsStart) hsquare rfl hroots
  have h := join_runs lengthProgram workProgram (fun _ => workStart) hlength rfl hwork
  apply h.mono
  dsimp only [cost, squareCost, d]
  omega

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeParameters
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeParameterCost

open scoped BigOperators

private theorem pow_bound {c k : ℕ} (hk : k ≤ 7) : c ^ k ≤ (c + 1) ^ 7 :=
  Nat.le_trans (Nat.pow_le_pow_left (Nat.le_succ c) k)
    (Nat.pow_le_pow_right (Nat.succ_pos c) hk)

private theorem power_positive (c : ℕ) : 1 ≤ (c + 1) ^ 7 :=
  Nat.pow_pos (Nat.succ_pos c)

theorem power_cost {k : ℕ} (hk : k ≤ 6) (c : ℕ) :
    TapePower.cost k 1 c ≤ 108 * (c + 1) ^ 7 := by
  have hs : (∑ j ∈ Finset.range k, c ^ j) ≤ 6 * (c + 1) ^ 6 := by
    calc
      (∑ j ∈ Finset.range k, c ^ j) ≤ ∑ _j ∈ Finset.range k, (c + 1) ^ 6 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk := Finset.mem_range.mp hj
        exact Nat.le_trans (Nat.pow_le_pow_left (Nat.le_succ c) j)
          (Nat.pow_le_pow_right (Nat.succ_pos c) (by omega : j ≤ 6))
      _ = k * (c + 1) ^ 6 := by simp
      _ ≤ 6 * (c + 1) ^ 6 := Nat.mul_le_mul_right _ hk
  have hc : 10 * c + 14 ≤ 14 * (c + 1) := by omega
  have hp := power_positive c
  calc
    TapePower.cost k 1 c = (10 * c + 14) * (∑ j ∈ Finset.range k, c ^ j) + 4 * k := by
      rw [TapePower.cost_eq_sum, Nat.one_mul]
    _ ≤ (10 * c + 14) * (6 * (c + 1) ^ 6) + 24 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hs) (by omega)
    _ ≤ (14 * (c + 1)) * (6 * (c + 1) ^ 6) + 24 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) _
    _ = 84 * (c + 1) ^ 7 + 24 := by ring
    _ ≤ 108 * (c + 1) ^ 7 := by omega

theorem compare_cost {k : ℕ} (hk : k ≤ 6) (c D : ℕ) :
    TapePowerCompare.cost k c D ≤ 124 * (c + 1) ^ 7 := by
  have hp := power_cost hk c
  have hmin := Nat.le_trans (Nat.min_le_left (c ^ k) D) (pow_bound (by omega : k ≤ 7))
  have hpos := power_positive c
  unfold TapePowerCompare.cost
  omega

theorem body_cost {k : ℕ} (hk : k ≤ 6) (two : Bool) (c : ℕ) :
    TapeSearchBody.cost k two c ≤ 16 * (c + 1) ^ 7 := by
  have hp : c ^ k ≤ (c + 1) ^ 7 := pow_bound (by omega)
  have hpos := power_positive c
  cases two <;> simp [TapeSearchBody.cost, TapeSearchBody.incrementCost] <;> omega

theorem search_cost {k : ℕ} (hk : k ≤ 6) (two : Bool) (D fuel c B : ℕ)
    (hc : c + TapeSearchBody.amount two * fuel ≤ B) :
    TapePowerSearch.cost k two D fuel c ≤ (fuel + 1) * 144 * (B + 1) ^ 7 := by
  induction fuel generalizing c with
  | zero =>
      have hcB : c ≤ B := by simpa using hc
      have hp : (c + 1) ^ 7 ≤ (B + 1) ^ 7 :=
        Nat.pow_le_pow_left (Nat.add_le_add_right hcB 1) 7
      have hcmp := Nat.le_trans (compare_cost hk c D) (Nat.mul_le_mul_left 124 hp)
      have hpos := power_positive B
      simp only [TapePowerSearch.cost, Nat.zero_add, Nat.one_mul]
      omega
  | succ fuel ih =>
      have hcB : c ≤ B := by omega
      have hnext : c + TapeSearchBody.amount two + TapeSearchBody.amount two * fuel ≤ B := by
        rw [Nat.mul_succ] at hc
        omega
      have hr := ih (c + TapeSearchBody.amount two) hnext
      have hp : (c + 1) ^ 7 ≤ (B + 1) ^ 7 :=
        Nat.pow_le_pow_left (Nat.add_le_add_right hcB 1) 7
      have hcmp := Nat.le_trans (compare_cost hk c D) (Nat.mul_le_mul_left 124 hp)
      have hb := Nat.le_trans (body_cost hk two c) (Nat.mul_le_mul_left 16 hp)
      have hpos := power_positive B
      have hprefix : TapePowerCompare.cost k c D + 1 + TapeSearchBody.cost k two c + 1 ≤
          144 * (B + 1) ^ 7 := by omega
      calc
        TapePowerSearch.cost k two D (fuel + 1) c ≤
            144 * (B + 1) ^ 7 + (fuel + 1) * 144 * (B + 1) ^ 7 :=
          Nat.add_le_add hprefix hr
        _ = (fuel + 1 + 1) * 144 * (B + 1) ^ 7 := by ring

theorem cube_cost (d : ℕ) : TapeParameterSearch.cubeCost d ≤ 200 * (d + 3) ^ 8 := by
  have hr := hashDimension_le d
  have hs := search_cost (by decide : 3 ≤ 6) false (d ^ 2) (hashDimension d) 0 d
    (by simpa [TapeSearchBody.amount] using hr)
  have hprod : (hashDimension d + 1) * 144 * (d + 1) ^ 7 ≤ 144 * (d + 1) ^ 8 := by
    calc
      _ ≤ (d + 1) * 144 * (d + 1) ^ 7 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.add_le_add_right hr 1))
      _ = _ := by ring
  have hs' := Nat.le_trans hs hprod
  have hbase : (d + 1) ^ 8 ≤ (d + 3) ^ 8 := Nat.pow_le_pow_left (by omega) 8
  have hsearch := Nat.le_trans hs' (Nat.mul_le_mul_left 144 hbase)
  have hp : (hashDimension d) ^ 3 ≤ (d + 3) ^ 8 :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega : hashDimension d ≤ d + 3) 3)
      (Nat.pow_le_pow_right (by omega : 0 < d + 3) (by decide : 3 ≤ 8))
  have hpos : 1 ≤ (d + 3) ^ 8 := Nat.pow_pos (by omega)
  unfold TapeParameterSearch.cubeCost
  omega

theorem sixth_cost (d : ℕ) : TapeParameterSearch.sixthCost d ≤ 200 * (d + 3) ^ 8 := by
  have ht := independenceOrder_le d
  have he := independenceOrder_even d
  have hterminal : 2 * (independenceOrder d / 2 + 1) = independenceOrder d + 2 := by
    obtain ⟨a, ha⟩ := he
    omega
  have hs := search_cost (by decide : 6 ≤ 6) true d
    (independenceOrder d / 2 + 1) 0 (d + 2)
    (by simp [TapeSearchBody.amount]; omega)
  have hprod : (independenceOrder d / 2 + 1 + 1) * 144 * (d + 2 + 1) ^ 7 ≤
      144 * (d + 3) ^ 8 := by
    calc
      _ ≤ (d + 3) * 144 * (d + 3) ^ 7 := by
        apply Nat.mul_le_mul
        · exact Nat.mul_le_mul_right 144 (by omega)
        · apply Nat.pow_le_pow_left
          omega
      _ = _ := by ring
  have hsearch := Nat.le_trans hs hprod
  have hp : (independenceOrder d + 2) ^ 6 ≤ (d + 3) ^ 8 :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega : independenceOrder d + 2 ≤ d + 3) 6)
      (Nat.pow_le_pow_right (by omega : 0 < d + 3) (by decide : 6 ≤ 8))
  have hpos : 1 ≤ (d + 3) ^ 8 := Nat.pow_pos (by omega)
  unfold TapeParameterSearch.sixthCost
  omega

end TapeParameterCost
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeParameters

theorem cost_le (n : ℕ) : cost n ≤ 600 * (n + 3) ^ 8 := by
  have hd : dataDimension n ≤ n := Nat.div_le_self n 5
  have hbase : (dataDimension n + 3) ^ 8 ≤ (n + 3) ^ 8 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right hd 3) 8
  have hc := Nat.le_trans (TapeParameterCost.cube_cost (dataDimension n))
    (Nat.mul_le_mul_left 200 hbase)
  have hs := Nat.le_trans (TapeParameterCost.sixth_cost (dataDimension n))
    (Nat.mul_le_mul_left 200 hbase)
  have hpbase : (dataDimension n + 1) ^ 7 ≤ (n + 3) ^ 8 :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega : dataDimension n + 1 ≤ n + 3) 7)
      (Nat.pow_le_pow_right (by omega : 0 < n + 3) (by decide : 7 ≤ 8))
  have hp := Nat.le_trans (TapeParameterCost.power_cost (by decide : 2 ≤ 6)
    (dataDimension n)) (Nat.mul_le_mul_left 108 hpbase)
  have hn : n ≤ (n + 3) ^ 8 := by
    calc
      n ≤ n + 3 := by omega
      _ = (n + 3) ^ 1 := by simp
      _ ≤ (n + 3) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hd2 : (dataDimension n) ^ 2 ≤ (n + 3) ^ 8 :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega : dataDimension n ≤ n + 3) 2)
      (Nat.pow_le_pow_right (by omega : 0 < n + 3) (by decide : 2 ≤ 8))
  have hpos : 1 ≤ (n + 3) ^ 8 := Nat.pow_pos (by omega)
  unfold cost
  omega

end TapeParameters
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeCopyAdd

open TapeMultiProgram TapeRouting TapeArithmetic

abbrev State := TapeCopy.State ⊕ AddState

def program (src scratch dst : TapeRegister) : TapeMultiProgram State :=
  joinCode (TapeCopy.code src scratch) (addProgram scratch dst) (fun _ => addStart)

def start : State := .inl .start
def done : State := .inr addDone

@[simp] theorem program_done (src scratch dst : TapeRegister) (h : TapeHeads) :
    program src scratch dst done h = none := rfl

theorem runs_add {src scratch dst : TapeRegister}
    (hsc : src ≠ scratch) (hcd : scratch ≠ dst) (σ : TapeStore) (n m : ℕ)
    (hn : σ src = List.replicate n true) (hm : σ dst = List.replicate m true)
    (hc : σ scratch = []) :
    RunsIn (program src scratch dst).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ dst (List.replicate (m + n) true))))
      (10 * n + 8) := by
  let τ := Function.update σ scratch (List.replicate n true)
  have hcopy := TapeStoreRuns.copy hsc σ hc
  have hcopy' : RunsIn (TapeCopy.code src scratch).step
      (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes τ)) (2 * n + 4) := by
    simpa only [hn, List.length_replicate] using hcopy
  have hadd := TapeStoreRuns.add hcd τ n m
    (by simp [τ]) (by simp [τ, hm, Ne.symm hcd])
  have hclear : Function.update τ scratch [] = σ := by
    dsimp [τ]
    rw [Function.update_idem, ← hc, Function.update_eq_self]
  rw [hclear] at hadd
  have hall := join_runs (TapeCopy.code src scratch) (addProgram scratch dst)
    (fun _ => addStart) hcopy' rfl hadd
  have hcost : (2 * n + 4) + 1 + (8 * n + 3) = 10 * n + 8 := by omega
  simpa only [program, start, done, hcost] using hall

end TapeCopyAdd
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeInputGuard

open TapeMultiProgram TapeRouting TapeUnary TapeCopy

def requiredLength (d r t : ℕ) : ℕ := d + (d + r - 1) + r + t * r

theorem requiredLength_parameters (d : ℕ) :
    requiredLength d (hashDimension d) (independenceOrder d) = blockLen d := rfl

def outputStore (σ : TapeStore) (d r t : ℕ) : TapeStore :=
  Function.update σ 8 (List.replicate (requiredLength d r t) true)

@[simp] theorem outputStore_length (σ : TapeStore) (d r t : ℕ) :
    outputStore σ d r t 8 = List.replicate (requiredLength d r t) true := by
  simp [outputStore]

theorem outputStore_other (σ : TapeStore) (d r t : ℕ) (q : TapeRegister)
    (hq : q ≠ 8) : outputStore σ d r t q = σ q := by
  simp [outputStore, Function.update, hq]

abbrev ProductState := TapeCopy.State ⊕ TapeMultiply.State

def productProgram : TapeMultiProgram ProductState :=
  joinCode (TapeCopy.code 4 5) (TapeMultiply.program 5 3 6 8)
    (fun _ => TapeMultiply.start)

def productStart : ProductState := .inl .start
def productDone : ProductState := .inr TapeMultiply.done

theorem runs_product (σ : TapeStore) (t r z : ℕ)
    (h3 : σ 3 = List.replicate r true) (h4 : σ 4 = List.replicate t true)
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h8 : σ 8 = List.replicate z true) :
    RunsIn productProgram.step (cfg productStart (storeTapes σ))
      (cfg productDone (storeTapes (Function.update σ 8 (List.replicate (z + t*r) true))))
      (t * (10*r + 14) + 2*t + 8) := by
  let τ := Function.update σ 5 (List.replicate t true)
  have hc := TapeStoreRuns.copy (src := 4) (dst := 5) (by decide) σ h5
  have hc' : RunsIn (TapeCopy.code 4 5).step (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes τ)) (2*t+4) := by
    simpa only [τ, h4, List.length_replicate] using hc
  have hin : TapeMultiply.tapes 5 3 6 8 (storeTapes σ) t r 0 z = storeTapes τ := by
    funext q
    by_cases hq5 : q = 5
    · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, τ, counterTape]
    · by_cases hq3 : q = 3
      · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, τ, counterTape, h3]
      · by_cases hq6 : q = 6
        · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, τ, counterTape, h6]
        · by_cases hq8 : q = 8
          · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, τ, counterTape, h8]
          · simp [TapeMultiply.tapes, onPair, storeTapes, τ, hq5, hq3, hq6, hq8]
  have hout : TapeMultiply.tapes 5 3 6 8 (storeTapes σ) 0 r 0 (z+t*r) =
      storeTapes (Function.update σ 8 (List.replicate (z+t*r) true)) := by
    funext q
    by_cases hq5 : q = 5
    · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, counterTape, h5]
    · by_cases hq3 : q = 3
      · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, counterTape, h3]
      · by_cases hq6 : q = 6
        · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, counterTape, h6]
        · by_cases hq8 : q = 8
          · subst q; simp [TapeMultiply.tapes, onPair, storeTapes, counterTape]
          · simp [TapeMultiply.tapes, onPair, storeTapes, Function.update,
              hq5, hq3, hq6, hq8]
  have hm := TapeMultiply.runs_mul (outer := 5) (source := 3) (scratch := 6)
    (destination := 8) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (storeTapes σ) t r z
  rw [hin, hout] at hm
  have h := join_runs (TapeCopy.code 4 5) (TapeMultiply.program 5 3 6 8)
    (fun _ => TapeMultiply.start) hc' rfl hm
  have ht : (2*t+4)+1+(t*(10*r+14)+3) = t*(10*r+14)+2*t+8 := by omega
  simpa only [productProgram, productStart, productDone, ht] using h

abbrev RingSumState := TapeCopyAdd.State ⊕ TapeCopyAdd.State
def ringSumProgram : TapeMultiProgram RingSumState :=
  joinCode (TapeCopyAdd.program 3 5 8) (TapeCopyAdd.program 3 5 8)
    (fun _ => TapeCopyAdd.start)
def ringSumStart : RingSumState := .inl TapeCopyAdd.start
def ringSumDone : RingSumState := .inr TapeCopyAdd.done

abbrev AddSumState := TapeCopyAdd.State ⊕ RingSumState
def addSumProgram : TapeMultiProgram AddSumState :=
  joinCode (TapeCopyAdd.program 2 5 8) ringSumProgram (fun _ => ringSumStart)
def addSumStart : AddSumState := .inl TapeCopyAdd.start
def addSumDone : AddSumState := .inr ringSumDone

abbrev SumState := TapeCopy.State ⊕ AddSumState
def sumProgram : TapeMultiProgram SumState :=
  joinCode (TapeCopy.code 2 8) addSumProgram (fun _ => addSumStart)
def sumStart : SumState := .inl .start
def sumDone : SumState := .inr addSumDone

theorem runs_sum (σ : TapeStore) (d r : ℕ)
    (h2 : σ 2 = List.replicate d true) (h3 : σ 3 = List.replicate r true)
    (h5 : σ 5 = []) (h8 : σ 8 = []) :
    RunsIn sumProgram.step (cfg sumStart (storeTapes σ))
      (cfg sumDone (storeTapes (Function.update σ 8 (List.replicate (d+d+r+r) true))))
      (12*d+20*r+31) := by
  let σ1 := Function.update σ 8 (List.replicate d true)
  let σ2 := Function.update σ 8 (List.replicate (d+d) true)
  let σ3 := Function.update σ 8 (List.replicate (d+d+r) true)
  have hc := TapeStoreRuns.copy (src := 2) (dst := 8) (by decide) σ h8
  have hc' : RunsIn (TapeCopy.code 2 8).step (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes σ1)) (2*d+4) := by
    simpa only [σ1, h2, List.length_replicate] using hc
  have ha := TapeCopyAdd.runs_add (src := 2) (scratch := 5) (dst := 8)
    (by decide) (by decide) σ1 d d (by simp [σ1, h2]) (by simp [σ1]) (by simp [σ1, h5])
  have ha' : RunsIn (TapeCopyAdd.program 2 5 8).step
      (cfg TapeCopyAdd.start (storeTapes σ1)) (cfg TapeCopyAdd.done (storeTapes σ2))
      (10*d+8) := by simpa only [σ1, σ2, Function.update_idem] using ha
  have hb := TapeCopyAdd.runs_add (src := 3) (scratch := 5) (dst := 8)
    (by decide) (by decide) σ2 r (d+d) (by simp [σ2, h3]) (by simp [σ2])
    (by simp [σ2, h5])
  have hb' : RunsIn (TapeCopyAdd.program 3 5 8).step
      (cfg TapeCopyAdd.start (storeTapes σ2)) (cfg TapeCopyAdd.done (storeTapes σ3))
      (10*r+8) := by simpa only [σ2, σ3, Function.update_idem] using hb
  have he := TapeCopyAdd.runs_add (src := 3) (scratch := 5) (dst := 8)
    (by decide) (by decide) σ3 r (d+d+r) (by simp [σ3, h3]) (by simp [σ3])
    (by simp [σ3, h5])
  simp only [σ3, Function.update_idem] at he
  have hr := join_runs (TapeCopyAdd.program 3 5 8) (TapeCopyAdd.program 3 5 8)
    (fun _ => TapeCopyAdd.start) hb' rfl he
  have hd := join_runs (TapeCopyAdd.program 2 5 8) ringSumProgram
    (fun _ => ringSumStart) ha' rfl hr
  have h := join_runs (TapeCopy.code 2 8) addSumProgram
    (fun _ => addSumStart) hc' rfl hd
  have ht : (2*d+4)+1+((10*d+8)+1+((10*r+8)+1+(10*r+8))) =
      12*d+20*r+31 := by omega
  simpa only [sumProgram, sumStart, sumDone, addSumProgram, addSumStart, addSumDone,
    ringSumProgram, ringSumStart, ringSumDone, ht] using h

abbrev TailState := DecState ⊕ ProductState
def tailProgram : TapeMultiProgram TailState :=
  joinCode (decProgram 8) productProgram (fun _ => productStart)
def tailStart : TailState := .inl .start
def tailDone : TailState := .inr productDone

abbrev LengthState := SumState ⊕ TailState
def lengthProgram : TapeMultiProgram LengthState :=
  joinCode sumProgram tailProgram (fun _ => tailStart)
def lengthStart : LengthState := .inl sumStart
def lengthDone : LengthState := .inr tailDone

def lengthCost (d r t : ℕ) : ℕ := 12*d+20*r+16*t+10*(t*r)+45

theorem runs_length (σ : TapeStore) (d r t : ℕ)
    (h2 : σ 2 = List.replicate d true) (h3 : σ 3 = List.replicate r true)
    (h4 : σ 4 = List.replicate t true) (h5 : σ 5 = []) (h6 : σ 6 = [])
    (h8 : σ 8 = []) :
    RunsIn lengthProgram.step (cfg lengthStart (storeTapes σ))
      (cfg lengthDone (storeTapes (outputStore σ d r t))) (lengthCost d r t) := by
  let z := d+d+r+r
  let σS := Function.update σ 8 (List.replicate z true)
  let σD := Function.update σ 8 (List.replicate (z-1) true)
  have hs := runs_sum σ d r h2 h3 h5 h8
  have hd := decrement 8 (storeTapes σS) z (by simp [σS, storeTapes, counterTape])
  have hd' : RunsIn (decProgram 8).step (cfg DecState.start (storeTapes σS))
      (cfg (DecState.done (decide (0 < z))) (storeTapes σD)) 4 := by
    simpa only [σS, σD, ← storeTapes_update, counterTape, Function.update_idem] using hd
  have hp := runs_product σD t r (z-1) (by simp [σD, h3]) (by simp [σD, h4])
    (by simp [σD, h5]) (by simp [σD, h6]) (by simp [σD])
  have hz : z-1 = d+(d+r-1)+r := by dsimp [z]; omega
  have ho : Function.update σD 8 (List.replicate (z-1+t*r) true) =
      outputStore σ d r t := by
    simp only [σD, Function.update_idem, outputStore, requiredLength, hz]
  rw [ho] at hp
  have htail := join_runs (decProgram 8) productProgram (fun _ => productStart) hd' rfl hp
  have h := join_runs sumProgram tailProgram (fun _ => tailStart) hs rfl htail
  have ht : (12*d+20*r+31)+1+(4+1+(t*(10*r+14)+2*t+8)) =
      lengthCost d r t := by unfold lengthCost; ring
  simpa only [lengthProgram, lengthStart, lengthDone, tailProgram, tailStart, tailDone,
    σS, z, ht] using h

@[simp] theorem lengthProgram_done (h : TapeHeads) : lengthProgram lengthDone h = none := rfl

end TapeInputGuard
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

structure ParsedInput where
  dataSize : ℕ
  ringDegree : ℕ
  coefficientCount : ℕ
  data : Fin dataSize → Bool
  hashSeed : Fin (dataSize + ringDegree - 1) → Bool
  polynomial : Fin ringDegree → Bool
  coefficients : Fin coefficientCount → Fin ringDegree → Bool

def decodeInput (w : List Bool) : ParsedInput where
  dataSize := dataDimension w.length
  ringDegree := hashDimension (dataDimension w.length)
  coefficientCount := independenceOrder (dataDimension w.length)
  data i := w.getD i.val false
  hashSeed i := w.getD (hashOffset (dataDimension w.length) + i.val) false
  polynomial i := w.getD (polynomialOffset (dataDimension w.length) + i.val) false
  coefficients j i :=
    w.getD (coefficientOffset (dataDimension w.length) j.val + i.val) false

def InputFits (w : List Bool) : Prop :=
  0 < dataDimension w.length ∧
    2 ≤ independenceOrder (dataDimension w.length) ∧
      blockLen (dataDimension w.length) ≤ w.length

instance (w : List Bool) : Decidable (InputFits w) := by
  unfold InputFits
  infer_instance

def parseInput (w : List Bool) : Option ParsedInput :=
  if InputFits w then some (decodeInput w) else none

theorem parseInput_of_fits {w : List Bool} (h : InputFits w) :
    parseInput w = some (decodeInput w) := by
  simp only [parseInput, ite_eq_left h]

theorem parseInput_of_not_fits {w : List Bool} (h : ¬InputFits w) :
    parseInput w = none := by
  simp only [parseInput, ite_eq_right h]

theorem parseInput_eq_some_iff (w : List Bool) (q : ParsedInput) :
    parseInput w = some q ↔ InputFits w ∧ decodeInput w = q := by
  by_cases h : InputFits w
  · simp [parseInput, h]
  · simp [parseInput, h]

theorem parseInput_eq_none_iff (w : List Bool) :
    parseInput w = none ↔ ¬InputFits w := by
  by_cases h : InputFits w
  · simp [parseInput, h]
  · simp [parseInput, h]

theorem decodeInput_dataSize (w : List Bool) :
    (decodeInput w).dataSize = dataDimension w.length := rfl

theorem decodeInput_ringDegree (w : List Bool) :
    (decodeInput w).ringDegree = hashDimension (dataDimension w.length) := rfl

theorem decodeInput_coefficientCount (w : List Bool) :
    (decodeInput w).coefficientCount = independenceOrder (dataDimension w.length) := rfl

theorem data_read_lt (w : List Bool) (i : Fin (dataDimension w.length)) :
    i.val < w.length :=
  Nat.lt_of_lt_of_le i.isLt (Nat.div_le_self w.length 5)

theorem hash_read_lt {w : List Bool} (h : InputFits w)
    (i : Fin (dataDimension w.length + hashDimension (dataDimension w.length) - 1)) :
    hashOffset (dataDimension w.length) + i.val < w.length := by
  have hi : hashOffset (dataDimension w.length) + i.val <
      polynomialOffset (dataDimension w.length) :=
    Nat.add_lt_add_left i.isLt _
  exact Nat.lt_of_lt_of_le hi (Nat.le_trans (polynomialOffset_le_coefficientsOffset _)
    (Nat.le_trans (coefficientsOffset_le_blockLen _) h.2.2))

theorem polynomial_read_lt {w : List Bool} (h : InputFits w)
    (i : Fin (hashDimension (dataDimension w.length))) :
    polynomialOffset (dataDimension w.length) + i.val < w.length :=
  Nat.lt_of_lt_of_le (polynomial_index_lt i.isLt)
    (Nat.le_trans (coefficientsOffset_le_blockLen _) h.2.2)

theorem coefficient_read_lt {w : List Bool} (h : InputFits w)
    (j : Fin (independenceOrder (dataDimension w.length)))
    (i : Fin (hashDimension (dataDimension w.length))) :
    coefficientOffset (dataDimension w.length) j.val + i.val < w.length :=
  Nat.lt_of_lt_of_le (coefficient_index_lt j.isLt i.isLt) h.2.2

theorem decoded_ringDegree_pos {w : List Bool} (h : InputFits w) :
    0 < (decodeInput w).ringDegree :=
  hashDimension_pos h.1

theorem decoded_coefficientCount_two_le {w : List Bool} (h : InputFits w) :
    2 ≤ (decodeInput w).coefficientCount :=
  h.2.1

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeInputGuard

open TapeMultiProgram TapeRouting TapeUnary

def positiveResult : TapeUnaryCompare.State → Bool
  | .done o => decide (o = .gt)
  | _ => false

def atLeastResult : TapeUnaryCompare.State → Bool
  | .done o => decide (o ≠ .lt)
  | _ => false

def atMostResult : TapeUnaryCompare.State → Bool
  | .done o => decide (o ≠ .gt)
  | _ => false

@[simp] theorem positiveResult_result (d : ℕ) :
    positiveResult (.done (TapeUnaryCompareScan.result d 0)) = decide (0 < d) := by
  simp [positiveResult, TapeUnaryCompareScan.result_eq_gt_iff]

@[simp] theorem atLeastResult_result (t : ℕ) :
    atLeastResult (.done (TapeUnaryCompareScan.result t 2)) = decide (2 ≤ t) := by
  simp [atLeastResult, TapeUnaryCompareScan.result_eq_lt_iff]
  omega

@[simp] theorem atMostResult_result (L n : ℕ) :
    atMostResult (.done (TapeUnaryCompareScan.result L n)) = decide (L ≤ n) := by
  simp [atMostResult, TapeUnaryCompareScan.result_eq_gt_iff]

inductive CheckState where
  | data (q : TapeUnaryCompare.State)
  | order (dataOK : Bool) (q : TapeUnaryCompare.State)
  | space (smallOK : Bool) (q : TapeUnaryCompare.State)
  | clear (accepted : Bool) (q : TapeErase.State)
  | done (accepted : Bool)
  deriving DecidableEq, Fintype

def checkProgram : TapeMultiProgram CheckState
  | .data q, h =>
      match TapeUnaryCompare.program 2 5 q h with
      | some out => some (.data out.1, out.2)
      | none => jump (.order (positiveResult q) (.scan .beginR)) h
  | .order b q, h =>
      match TapeUnaryCompare.program 4 6 q h with
      | some out => some (.order b out.1, out.2)
      | none => jump (.space (b && atLeastResult q) (.scan .beginR)) h
  | .space b q, h =>
      match TapeUnaryCompare.program 8 1 q h with
      | some out => some (.space b out.1, out.2)
      | none => jump (.clear (b && atMostResult q) .start) h
  | .clear b q, h =>
      match TapeErase.code 6 q h with
      | some out => some (.clear b out.1, out.2)
      | none => jump (.done b) h
  | .done _, _ => none

def checkStart : CheckState := .data (.scan .beginR)

theorem runs_checks (σ : TapeStore) (n d t L : ℕ)
    (h1 : σ 1 = List.replicate n true) (h2 : σ 2 = List.replicate d true)
    (h4 : σ 4 = List.replicate t true) (h5 : σ 5 = [])
    (h6 : σ 6 = List.replicate 2 true) (h8 : σ 8 = List.replicate L true) :
    RunsIn checkProgram.step (cfg checkStart (storeTapes σ))
      (cfg (.done (decide (0 < d ∧ 2 ≤ t ∧ L ≤ n)))
        (storeTapes (Function.update σ 6 []))) (4*n+42) := by
  let od := TapeUnaryCompareScan.result d 0
  let ot := TapeUnaryCompareScan.result t 2
  let oL := TapeUnaryCompareScan.result L n
  let bd := positiveResult (.done od)
  let bt := bd && atLeastResult (.done ot)
  let bL := bt && atMostResult (.done oL)
  have hd := TapeUnaryCompare.runs_compare (r := 2) (s := 5) (by decide)
    (storeTapes σ) d 0 (by simp [storeTapes, h2]) (by simp [storeTapes, h5])
  simp only [Nat.min_zero, Nat.mul_zero, Nat.zero_add] at hd
  have hd' := runs_map (TapeUnaryCompare.program 2 5) checkProgram CheckState.data (by
    intro q h q' writes moves he
    simp only [checkProgram, he]) hd
  have hdl := RunsIn.single (step_jump checkProgram (.data (.done od))
    (.order bd (.scan .beginR)) (storeTapes σ) rfl)
  have ht := TapeUnaryCompare.runs_compare (r := 4) (s := 6) (by decide)
    (storeTapes σ) t 2 (by simp [storeTapes, h4]) (by simp [storeTapes, h6])
  have ht0 := ht.mono (show 4 * min t 2 + 7 ≤ 15 by
    have hm := Nat.min_le_right t 2
    omega)
  have ht' := runs_map (TapeUnaryCompare.program 4 6) checkProgram (CheckState.order bd) (by
    intro q h q' writes moves he
    simp only [checkProgram, he]) ht0
  have htl := RunsIn.single (step_jump checkProgram (.order bd (.done ot))
    (.space bt (.scan .beginR)) (storeTapes σ) rfl)
  have hL := TapeUnaryCompare.runs_compare (r := 8) (s := 1) (by decide)
    (storeTapes σ) L n (by simp [storeTapes, h8]) (by simp [storeTapes, h1])
  have hL0 := hL.mono (show 4 * min L n + 7 ≤ 4*n+7 by
    have hm := Nat.min_le_right L n
    omega)
  have hL' := runs_map (TapeUnaryCompare.program 8 1) checkProgram (CheckState.space bt) (by
    intro q h q' writes moves he
    simp only [checkProgram, he]) hL0
  have hLl := RunsIn.single (step_jump checkProgram (.space bt (.done oL))
    (.clear bL .start) (storeTapes σ) rfl)
  have he := TapeStoreRuns.erase 6 σ
  simp only [h6, List.length_replicate] at he
  have he' := runs_map (TapeErase.code 6) checkProgram (CheckState.clear bL) (by
    intro q h q' writes moves heq
    simp only [checkProgram, heq]) he
  have hel := RunsIn.single (step_jump checkProgram (.clear bL .done) (.done bL)
    (storeTapes (Function.update σ 6 [])) rfl)
  have hall := ((((((hd'.trans hdl).trans ht').trans htl).trans hL').trans hLl).trans he').trans hel
  have hb : bL = decide (0 < d ∧ 2 ≤ t ∧ L ≤ n) := by
    simp [bL, bt, bd, od, ot, oL, Bool.and_assoc]
  have hc : ((((((7+1)+15)+1)+(4*n+7))+1)+(2*2+5))+1 = 4*n+42 := by omega
  simpa only [mapCfg, cfg, checkStart, hb, hc] using hall

abbrev TwoState := IncState ⊕ IncState
def twoProgram : TapeMultiProgram TwoState :=
  joinCode (incProgram 6) (incProgram 6) (fun _ => IncState.start)
def twoStart : TwoState := .inl .start
def twoDone : TwoState := .inr .done

theorem runs_two (σ : TapeStore) (h6 : σ 6 = []) :
    RunsIn twoProgram.step (cfg twoStart (storeTapes σ))
      (cfg twoDone (storeTapes (Function.update σ 6 (List.replicate 2 true)))) 5 := by
  let σ1 := Function.update σ 6 (List.replicate 1 true)
  have h1 := increment 6 (storeTapes σ) 0 (by simp [storeTapes, counterTape, h6])
  have h1' : RunsIn (incProgram 6).step (cfg IncState.start (storeTapes σ))
      (cfg IncState.done (storeTapes σ1)) 2 := by
    simpa only [σ1, storeTapes_update, counterTape] using h1
  have h2 := increment 6 (storeTapes σ1) 1 (by simp [σ1, storeTapes, counterTape])
  have h2' : RunsIn (incProgram 6).step (cfg IncState.start (storeTapes σ1))
      (cfg IncState.done (storeTapes (Function.update σ 6 (List.replicate 2 true)))) 2 := by
    simpa only [σ1, ← storeTapes_update, counterTape, Function.update_idem] using h2
  exact join_runs (incProgram 6) (incProgram 6) (fun _ => IncState.start) h1' rfl h2'

abbrev TestState := TwoState ⊕ CheckState
def testProgram : TapeMultiProgram TestState :=
  joinCode twoProgram checkProgram (fun _ => checkStart)
def testStart : TestState := .inl twoStart
def testDone (b : Bool) : TestState := .inr (.done b)

theorem runs_test (σ : TapeStore) (n d t L : ℕ)
    (h1 : σ 1 = List.replicate n true) (h2 : σ 2 = List.replicate d true)
    (h4 : σ 4 = List.replicate t true) (h5 : σ 5 = []) (h6 : σ 6 = [])
    (h8 : σ 8 = List.replicate L true) :
    RunsIn testProgram.step (cfg testStart (storeTapes σ))
      (cfg (testDone (decide (0 < d ∧ 2 ≤ t ∧ L ≤ n))) (storeTapes σ)) (4*n+48) := by
  let τ := Function.update σ 6 (List.replicate 2 true)
  have htwo := runs_two σ h6
  have hc := runs_checks τ n d t L (by simp [τ, h1]) (by simp [τ, h2])
    (by simp [τ, h4]) (by simp [τ, h5]) (by simp [τ]) (by simp [τ, h8])
  have hrestore : Function.update τ 6 [] = σ := by
    dsimp [τ]
    rw [Function.update_idem, ← h6, Function.update_eq_self]
  rw [hrestore] at hc
  have h := join_runs twoProgram checkProgram (fun _ => checkStart) htwo rfl hc
  have ht : 5+1+(4*n+42) = 4*n+48 := by omega
  simpa only [testProgram, testStart, testDone, ht] using h

abbrev State := LengthState ⊕ TestState
def program : TapeMultiProgram State :=
  joinCode lengthProgram testProgram (fun _ => testStart)
def start : State := .inl lengthStart
def done (accepted : Bool) : State := .inr (testDone accepted)

def cost (n d r t : ℕ) : ℕ := lengthCost d r t + 4*n + 49

theorem cost_eq (n d r t : ℕ) :
    cost n d r t = 12*d + 20*r + 16*t + 10*(t*r) + 4*n + 94 := by
  unfold cost lengthCost
  omega

theorem cost_le_square (n d r t : ℕ) (hd : d ≤ n+1) (hr : r ≤ n+1) (ht : t ≤ n+1) :
    cost n d r t ≤ 200 * (n+1)^2 := by
  rw [cost_eq]
  have hm : t*r ≤ (n+1)*(n+1) := Nat.mul_le_mul ht hr
  nlinarith

theorem cost_parameters_le (n : ℕ) :
    cost n (dataDimension n) (hashDimension (dataDimension n))
      (independenceOrder (dataDimension n)) ≤ 200 * (n+1)^2 := by
  have hd : dataDimension n ≤ n+1 := by unfold dataDimension; omega
  exact cost_le_square n _ _ _ hd ((hashDimension_le _).trans hd)
    ((independenceOrder_le _).trans hd)

theorem runs_guard (σ : TapeStore) (n d r t : ℕ)
    (h1 : σ 1 = List.replicate n true) (h2 : σ 2 = List.replicate d true)
    (h3 : σ 3 = List.replicate r true) (h4 : σ 4 = List.replicate t true)
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h8 : σ 8 = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg (done (decide (0 < d ∧ 2 ≤ t ∧ requiredLength d r t ≤ n)))
        (storeTapes (outputStore σ d r t))) (cost n d r t) := by
  have hl := runs_length σ d r t h2 h3 h4 h5 h6 h8
  have ht := runs_test (outputStore σ d r t) n d t (requiredLength d r t)
    (by simp [outputStore, h1]) (by simp [outputStore, h2])
    (by simp [outputStore, h4]) (by simp [outputStore, h5])
    (by simp [outputStore, h6]) (by simp [outputStore])
  have h := join_runs lengthProgram testProgram (fun _ => testStart) hl rfl ht
  have hc : lengthCost d r t + 1 + (4*n+48) = cost n d r t := by
    unfold cost
    omega
  simpa only [program, start, done, hc] using h

theorem runs_inputFits (w : List Bool) (σ : TapeStore)
    (h1 : σ 1 = List.replicate w.length true)
    (h2 : σ 2 = List.replicate (dataDimension w.length) true)
    (h3 : σ 3 = List.replicate (hashDimension (dataDimension w.length)) true)
    (h4 : σ 4 = List.replicate (independenceOrder (dataDimension w.length)) true)
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h8 : σ 8 = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg (done (decide (InputFits w)))
        (storeTapes (outputStore σ (dataDimension w.length)
          (hashDimension (dataDimension w.length)) (independenceOrder (dataDimension w.length)))))
      (cost w.length (dataDimension w.length) (hashDimension (dataDimension w.length))
        (independenceOrder (dataDimension w.length))) := by
  have hguard : decide (InputFits w) =
      decide (0 < dataDimension w.length ∧
        2 ≤ independenceOrder (dataDimension w.length) ∧
        requiredLength (dataDimension w.length) (hashDimension (dataDimension w.length))
          (independenceOrder (dataDimension w.length)) ≤ w.length) := by
    apply decide_eq_decide.mpr
    simp only [InputFits, requiredLength_parameters]
  rw [hguard]
  exact runs_guard σ w.length (dataDimension w.length) (hashDimension (dataDimension w.length))
    (independenceOrder (dataDimension w.length)) h1 h2 h3 h4 h5 h6 h8

theorem runs_inputFits_quadratic (w : List Bool) (σ : TapeStore)
    (h1 : σ 1 = List.replicate w.length true)
    (h2 : σ 2 = List.replicate (dataDimension w.length) true)
    (h3 : σ 3 = List.replicate (hashDimension (dataDimension w.length)) true)
    (h4 : σ 4 = List.replicate (independenceOrder (dataDimension w.length)) true)
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h8 : σ 8 = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg (done (decide (InputFits w)))
        (storeTapes (outputStore σ (dataDimension w.length)
          (hashDimension (dataDimension w.length)) (independenceOrder (dataDimension w.length)))))
      (200 * (w.length+1)^2) :=
  (runs_inputFits w σ h1 h2 h3 h4 h5 h6 h8).mono (cost_parameters_le w.length)

@[simp] theorem program_done (b : Bool) (h : TapeHeads) : program (done b) h = none := rfl

end TapeInputGuard
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeParse

open TapeMultiProgram TapeRouting

def inputStore (w : List Bool) : TapeStore := fun r =>
  if r = TapeRegister.input then w
  else if r = TapeRegister.length then List.replicate w.length true else []

theorem initializedTapes_eq_store (w : List Bool) :
    initializedTapes w = storeTapes (inputStore w) := by
  funext r
  unfold initializedTapes storeTapes inputStore
  split_ifs <;> rfl

def outputStore (w : List Bool) : TapeStore :=
  TapeInputGuard.outputStore (TapeParameters.outputStore (inputStore w) w.length)
    (dataDimension w.length) (hashDimension (dataDimension w.length))
    (independenceOrder (dataDimension w.length))

@[simp] theorem outputStore_input (w : List Bool) : outputStore w 0 = w := by
  simp [outputStore, TapeInputGuard.outputStore, TapeParameters.outputStore,
    TapeParameters.dataStore, inputStore, TapeRegister.input]

@[simp] theorem outputStore_data (w : List Bool) :
    outputStore w 2 = List.replicate (dataDimension w.length) true := by
  simp [outputStore, TapeInputGuard.outputStore]

@[simp] theorem outputStore_hash (w : List Bool) :
    outputStore w 3 = List.replicate (hashDimension (dataDimension w.length)) true := by
  simp [outputStore, TapeInputGuard.outputStore]

@[simp] theorem outputStore_order (w : List Bool) :
    outputStore w 4 = List.replicate (independenceOrder (dataDimension w.length)) true := by
  simp [outputStore, TapeInputGuard.outputStore]

theorem outputStore_empty (w : List Bool) (r : TapeRegister)
    (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3)
    (h4 : r ≠ 4) (h8 : r ≠ 8) : outputStore w r = [] := by
  simp [outputStore, TapeInputGuard.outputStore, TapeParameters.outputStore,
    TapeParameters.dataStore, inputStore, TapeRegister.input, TapeRegister.length,
    Function.update, h0, h1, h2, h3, h4, h8]

abbrev WorkState := TapeParameters.State ⊕ TapeInputGuard.State

def workProgram : TapeMultiProgram WorkState :=
  joinCode TapeParameters.program TapeInputGuard.program (fun _ => TapeInputGuard.start)

def workStart : WorkState := .inl TapeParameters.start
def workDone (accepted : Bool) : WorkState := .inr (TapeInputGuard.done accepted)

abbrev State := InitState ⊕ WorkState

def program : TapeMultiProgram State :=
  joinCode initializationCode workProgram (fun _ => workStart)

def start : State := .inl InitState.start
def done (accepted : Bool) : State := .inr (workDone accepted)

def acceptFlag : State → Bool
  | .inr (.inr (.inr (.inr (.done b)))) => b
  | _ => false

@[simp] theorem acceptFlag_done (b : Bool) : acceptFlag (done b) = b := rfl

@[simp] theorem program_done (b : Bool) (h : TapeHeads) : program (done b) h = none := rfl

theorem runs_parse (w : List Bool) :
    RunsIn program.step (cfg start (rawInputTapes w))
      (cfg (done (decide (InputFits w))) (storeTapes (outputStore w)))
      (1000 * (w.length + 3) ^ 8) := by
  let σ := inputStore w
  let τ := TapeParameters.outputStore σ w.length
  have hi := initialization_runs w
  rw [initializedTapes_eq_store] at hi
  have hp := TapeParameters.runs_parameters σ w.length
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [σ, inputStore, TapeRegister.input, TapeRegister.length])
  have hp' := hp.mono (TapeParameters.cost_le w.length)
  have hg := TapeInputGuard.runs_inputFits_quadratic w τ
    (by simp [τ, σ, TapeParameters.outputStore, TapeParameters.dataStore,
      inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [τ]) (by simp [τ]) (by simp [τ])
    (by simp [τ, σ, TapeParameters.outputStore, TapeParameters.dataStore,
      inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [τ, σ, TapeParameters.outputStore, TapeParameters.dataStore,
      inputStore, TapeRegister.input, TapeRegister.length])
    (by simp [τ, σ, TapeParameters.outputStore, TapeParameters.dataStore,
      inputStore, TapeRegister.input, TapeRegister.length])
  have hw := join_runs TapeParameters.program TapeInputGuard.program
    (fun _ => TapeInputGuard.start) hp' (by simp) hg
  have hall := join_runs initializationCode workProgram (fun _ => workStart) hi rfl hw
  apply hall.mono
  have hquad : (w.length + 1) ^ 2 ≤ (w.length + 3) ^ 8 :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega : w.length + 1 ≤ w.length + 3) 2)
      (Nat.pow_le_pow_right (by omega : 0 < w.length + 3) (by decide : 2 ≤ 8))
  have hn : w.length ≤ (w.length + 3) ^ 8 := by
    calc
      w.length ≤ w.length + 3 := by omega
      _ = (w.length + 3) ^ 1 := by simp
      _ ≤ (w.length + 3) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpos : 1 ≤ (w.length + 3) ^ 8 := Nat.pow_pos (by omega)
  omega

end TapeParse
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

inductive InputBlockKind where
  | data
  | hash
  | polynomial
  | coefficients
  deriving DecidableEq

instance : Fintype InputBlockKind where
  elems := {.data, .hash, .polynomial, .coefficients}
  complete := by
    intro kind
    cases kind <;> simp

def inputBlockOffset (n : ℕ) : InputBlockKind → ℕ
  | .data => 0
  | .hash => hashOffset (dataDimension n)
  | .polynomial => polynomialOffset (dataDimension n)
  | .coefficients => coefficientsOffset (dataDimension n)

def inputBlockLength (n : ℕ) : InputBlockKind → ℕ
  | .data => dataDimension n
  | .hash => hashBlockLength (dataDimension n)
  | .polynomial => hashDimension (dataDimension n)
  | .coefficients => independenceOrder (dataDimension n) * hashDimension (dataDimension n)

def inputBlockData (w : List Bool) (kind : InputBlockKind) : List Bool :=
  (w.drop (inputBlockOffset w.length kind)).take (inputBlockLength w.length kind)

theorem inputBlock_end_le {w : List Bool} (h : InputFits w) (kind : InputBlockKind) :
    inputBlockOffset w.length kind + inputBlockLength w.length kind ≤ w.length := by
  cases kind with
  | data =>
    simpa only [inputBlockOffset, inputBlockLength, Nat.zero_add, dataDimension] using
      Nat.div_le_self w.length 5
  | hash =>
    change polynomialOffset (dataDimension w.length) ≤ w.length
    exact (polynomialOffset_le_coefficientsOffset _).trans
      ((coefficientsOffset_le_blockLen _).trans h.2.2)
  | polynomial =>
    change coefficientsOffset (dataDimension w.length) ≤ w.length
    exact (coefficientsOffset_le_blockLen _).trans h.2.2
  | coefficients =>
    exact h.2.2

theorem inputBlock_offset_le {w : List Bool} (h : InputFits w) (kind : InputBlockKind) :
    inputBlockOffset w.length kind ≤ w.length := by
  have hb := inputBlock_end_le h kind
  omega

theorem inputBlock_prefix_length {w : List Bool} (h : InputFits w)
    (kind : InputBlockKind) :
    (w.take (inputBlockOffset w.length kind)).length = inputBlockOffset w.length kind :=
  List.length_take_of_le (inputBlock_offset_le h kind)

theorem inputBlockData_length {w : List Bool} (h : InputFits w) (kind : InputBlockKind) :
    (inputBlockData w kind).length = inputBlockLength w.length kind := by
  unfold inputBlockData
  rw [List.length_take, List.length_drop]
  apply Nat.min_eq_left
  have hb := inputBlock_end_le h kind
  omega

theorem inputBlock_reconstruct (w : List Bool) (kind : InputBlockKind) :
    w = w.take (inputBlockOffset w.length kind) ++ inputBlockData w kind ++
      w.drop (inputBlockOffset w.length kind + inputBlockLength w.length kind) := by
  calc
    w = w.take (inputBlockOffset w.length kind) ++
        w.drop (inputBlockOffset w.length kind) :=
      (List.take_append_drop _ _).symm
    _ = w.take (inputBlockOffset w.length kind) ++
        ((w.drop (inputBlockOffset w.length kind)).take (inputBlockLength w.length kind) ++
          (w.drop (inputBlockOffset w.length kind)).drop (inputBlockLength w.length kind)) :=
      congrArg (fun tail => w.take (inputBlockOffset w.length kind) ++ tail)
        (List.take_append_drop _ _).symm
    _ = _ := by simp only [inputBlockData, List.drop_drop, List.append_assoc]

theorem inputBlockData_getD (w : List Bool) (kind : InputBlockKind) {i : ℕ}
    (hi : i < inputBlockLength w.length kind) :
    (inputBlockData w kind).getD i false =
      w.getD (inputBlockOffset w.length kind + i) false := by
  simp only [inputBlockData, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hi, List.getElem?_drop]

theorem inputBlockData_data_nat (w : List Bool) {i : ℕ}
    (hi : i < dataDimension w.length) :
    (inputBlockData w .data).getD i false = (decodeInput w).data ⟨i, hi⟩ := by
  simpa only [inputBlockOffset, Nat.zero_add, decodeInput] using
    inputBlockData_getD w .data hi

theorem inputBlockData_data (w : List Bool) (i : Fin (dataDimension w.length)) :
    (inputBlockData w .data).getD i.val false = (decodeInput w).data i :=
  inputBlockData_data_nat w i.isLt

theorem inputBlockData_hash_nat (w : List Bool) {i : ℕ}
    (hi : i < hashBlockLength (dataDimension w.length)) :
    (inputBlockData w .hash).getD i false = (decodeInput w).hashSeed ⟨i, hi⟩ := by
  simpa only [inputBlockOffset, decodeInput] using inputBlockData_getD w .hash hi

theorem inputBlockData_hash (w : List Bool)
    (i : Fin (hashBlockLength (dataDimension w.length))) :
    (inputBlockData w .hash).getD i.val false = (decodeInput w).hashSeed i :=
  inputBlockData_hash_nat w i.isLt

theorem inputBlockData_polynomial_nat (w : List Bool) {i : ℕ}
    (hi : i < hashDimension (dataDimension w.length)) :
    (inputBlockData w .polynomial).getD i false = (decodeInput w).polynomial ⟨i, hi⟩ := by
  simpa only [inputBlockOffset, decodeInput] using inputBlockData_getD w .polynomial hi

theorem inputBlockData_polynomial (w : List Bool)
    (i : Fin (hashDimension (dataDimension w.length))) :
    (inputBlockData w .polynomial).getD i.val false = (decodeInput w).polynomial i :=
  inputBlockData_polynomial_nat w i.isLt

theorem inputBlock_coefficient_index_lt {n j i : ℕ}
    (hj : j < independenceOrder (dataDimension n))
    (hi : i < hashDimension (dataDimension n)) :
    j * hashDimension (dataDimension n) + i < inputBlockLength n .coefficients := by
  have hmul := Nat.mul_le_mul_right (hashDimension (dataDimension n))
    (Nat.succ_le_of_lt hj)
  simp only [Nat.succ_mul] at hmul
  change j * hashDimension (dataDimension n) + i <
    independenceOrder (dataDimension n) * hashDimension (dataDimension n)
  omega

theorem inputBlockData_coefficients_nat (w : List Bool) {j i : ℕ}
    (hj : j < independenceOrder (dataDimension w.length))
    (hi : i < hashDimension (dataDimension w.length)) :
    (inputBlockData w .coefficients).getD
        (j * hashDimension (dataDimension w.length) + i) false =
      (decodeInput w).coefficients ⟨j, hj⟩ ⟨i, hi⟩ := by
  simpa only [inputBlockOffset, decodeInput, coefficientOffset, Nat.add_assoc] using
    inputBlockData_getD w .coefficients (inputBlock_coefficient_index_lt hj hi)

theorem inputBlockData_coefficients (w : List Bool)
    (j : Fin (independenceOrder (dataDimension w.length)))
    (i : Fin (hashDimension (dataDimension w.length))) :
    (inputBlockData w .coefficients).getD
        (j.val * hashDimension (dataDimension w.length) + i.val) false =
      (decodeInput w).coefficients j i :=
  inputBlockData_coefficients_nat w j.isLt i.isLt

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeProductLength

open TapeMultiProgram TapeRouting TapeUnary TapeCopy

abbrev State := TapeCopy.State ⊕ TapeMultiply.State

def program : TapeMultiProgram State :=
  joinCode (TapeCopy.code 4 5) (TapeMultiply.program 5 3 6 30)
    (fun _ => TapeMultiply.start)

def start : State := .inl TapeCopy.State.start
def done : State := .inr TapeMultiply.done

def outputStore (σ : TapeStore) (n m : ℕ) : TapeStore :=
  Function.update σ 30 (List.replicate (n * m) true)

@[simp] theorem outputStore_destination (σ : TapeStore) (n m : ℕ) :
    outputStore σ n m 30 = List.replicate (n * m) true := by
  simp [outputStore]

theorem outputStore_other (σ : TapeStore) (n m : ℕ) (r : TapeRegister)
    (hr : r ≠ 30) : outputStore σ n m r = σ r := by
  simp [outputStore, Function.update, hr]

def cost (n m : ℕ) : ℕ := n * (10 * m + 16) + 8

private theorem frame_store (σ : TapeStore) (n m z : ℕ)
    (h3 : σ 3 = List.replicate m true) (h6 : σ 6 = []) :
    TapeMultiply.tapes 5 3 6 30 (storeTapes σ) n m 0 z =
      storeTapes (Function.update (Function.update σ 5 (List.replicate n true))
        30 (List.replicate z true)) := by
  funext r
  by_cases h5 : r = 5
  · subst r
    simp [TapeMultiply.tapes, onPair, storeTapes, counterTape]
  · by_cases hs : r = 3
    · subst r
      simp [TapeMultiply.tapes, onPair, storeTapes, counterTape, h3]
    · by_cases hc : r = 6
      · subst r
        simp [TapeMultiply.tapes, onPair, storeTapes, counterTape, h6]
      · by_cases hd : r = 30
        · subst r
          simp [TapeMultiply.tapes, onPair, storeTapes, counterTape]
        · simp [TapeMultiply.tapes, onPair, storeTapes, Function.update,
            h5, hs, hc, hd]

theorem runs_product (σ : TapeStore) (n m : ℕ)
    (h4 : σ 4 = List.replicate n true) (h3 : σ 3 = List.replicate m true)
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h30 : σ 30 = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (outputStore σ n m))) (cost n m) := by
  let copied := Function.update σ 5 (List.replicate n true)
  have hcopy := TapeStoreRuns.copy (src := 4) (dst := 5) (by decide) σ h5
  simp only [h4, List.length_replicate] at hcopy
  have hi : TapeMultiply.tapes 5 3 6 30 (storeTapes σ) n m 0 0 =
      storeTapes copied := by
    calc
      TapeMultiply.tapes 5 3 6 30 (storeTapes σ) n m 0 0 =
          storeTapes (Function.update copied 30 []) := by
        simpa only [copied, List.replicate_zero] using frame_store σ n m 0 h3 h6
      _ = storeTapes copied := by
        apply congrArg storeTapes
        apply Function.update_eq_self_iff.mpr
        simp [copied, h30]
  have hrestore : Function.update σ 5 [] = σ :=
    Function.update_eq_self_iff.mpr h5.symm
  have ho : TapeMultiply.tapes 5 3 6 30 (storeTapes σ) 0 m 0 (n * m) =
      storeTapes (outputStore σ n m) := by
    simpa only [List.replicate_zero, hrestore, outputStore] using
      frame_store σ 0 m (n * m) h3 h6
  have hmul := TapeMultiply.runs_mul (outer := 5) (source := 3) (scratch := 6)
    (destination := 30) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (storeTapes σ) n m 0
  simp only [Nat.zero_add, hi, ho] at hmul
  have h := join_runs (TapeCopy.code 4 5) (TapeMultiply.program 5 3 6 30)
    (fun _ => TapeMultiply.start) hcopy rfl hmul
  have htime : 2 * n + 4 + 1 + (n * (10 * m + 14) + 3) =
      n * (10 * m + 16) + 8 := by
    have hcoeff : 10 * m + 16 = (10 * m + 14) + 2 := by omega
    rw [hcoeff, Nat.mul_add n (10 * m + 14) 2]
    omega
  simpa only [program, start, done, cost, htime] using h

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeProductLength
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeInputPrepare

open TapeMultiProgram TapeRouting TapeUnary

abbrev SumMinusState := TapeCopy.State ⊕ (TapeCopyAdd.State ⊕ DecState)

def sumMinusProgram (dst : TapeRegister) : TapeMultiProgram SumMinusState :=
  joinCode (TapeCopy.code 2 dst)
    (joinCode (TapeCopyAdd.program 3 31 dst) (decProgram dst) (fun _ => .start))
    (fun _ => .inl TapeCopyAdd.start)

def sumMinusStart : SumMinusState := .inl .start

def sumMinusDone (d r : ℕ) : SumMinusState :=
  .inr (.inr (.done (decide (0 < d + r))))

@[simp] theorem sumMinusProgram_done (dst : TapeRegister) (d r : ℕ) (h : TapeHeads) :
    sumMinusProgram dst (sumMinusDone d r) h = none := rfl

private theorem runs_decrement (dst : TapeRegister) (σ : TapeStore) (n : ℕ)
    (hn : σ dst = List.replicate n true) :
    RunsIn (decProgram dst).step (cfg DecState.start (storeTapes σ))
      (cfg (.done (decide (0 < n)))
        (storeTapes (Function.update σ dst (List.replicate (n - 1) true)))) 4 := by
  have h := TapeUnary.decrement dst (storeTapes σ) n (by simp [storeTapes, hn, counterTape])
  simpa only [storeTapes_update, counterTape] using h

theorem runs_sumMinus {dst : TapeRegister}
    (h2 : (2 : TapeRegister) ≠ dst) (h3 : (3 : TapeRegister) ≠ dst)
    (h31 : (31 : TapeRegister) ≠ dst) (σ : TapeStore) (d r : ℕ)
    (hd : σ 2 = List.replicate d true) (hr : σ 3 = List.replicate r true)
    (he : σ dst = []) (hc : σ 31 = []) :
    RunsIn (sumMinusProgram dst).step (cfg sumMinusStart (storeTapes σ))
      (cfg (sumMinusDone d r)
        (storeTapes (Function.update σ dst (List.replicate (d + r - 1) true))))
      (2 * d + 10 * r + 18) := by
  let copied := Function.update σ dst (List.replicate d true)
  let added := Function.update σ dst (List.replicate (d + r) true)
  have hcopy := TapeStoreRuns.copy h2 σ he
  simp only [hd, List.length_replicate] at hcopy
  have hadd := TapeCopyAdd.runs_add (src := 3) (scratch := 31) (dst := dst)
    (by decide) h31 copied r d (by simp [copied, h3, hr])
    (by simp [copied]) (by simp [copied, h31, hc])
  have hadd' : RunsIn (TapeCopyAdd.program 3 31 dst).step
      (cfg TapeCopyAdd.start (storeTapes copied))
      (cfg TapeCopyAdd.done (storeTapes added)) (10 * r + 8) := by
    simpa only [copied, added, Function.update_idem] using hadd
  have hdec := runs_decrement dst added (d + r) (by simp [added])
  have hdec' : RunsIn (decProgram dst).step
      (cfg DecState.start (storeTapes added))
      (cfg (.done (decide (0 < d + r)))
        (storeTapes (Function.update σ dst (List.replicate (d + r - 1) true)))) 4 := by
    simpa only [added, Function.update_idem] using hdec
  have htail := join_runs (TapeCopyAdd.program 3 31 dst) (decProgram dst)
    (fun _ => DecState.start) hadd' rfl hdec'
  have h := join_runs (TapeCopy.code 2 dst)
    (joinCode (TapeCopyAdd.program 3 31 dst) (decProgram dst) (fun _ => DecState.start))
    (fun _ => .inl TapeCopyAdd.start) hcopy rfl htail
  have hcost : 2 * d + 4 + 1 + (10 * r + 8 + 1 + 4) =
      2 * d + 10 * r + 18 := by omega
  simpa only [sumMinusProgram, sumMinusStart, sumMinusDone, hcost] using h

abbrev OffsetState := SumMinusState ⊕ TapeCopyAdd.State

def offsetProgram : TapeMultiProgram OffsetState :=
  joinCode (sumMinusProgram 29) (TapeCopyAdd.program 2 31 29)
    (fun _ => TapeCopyAdd.start)

def offsetStart : OffsetState := .inl sumMinusStart
def offsetDone : OffsetState := .inr TapeCopyAdd.done

@[simp] theorem offsetProgram_done (h : TapeHeads) : offsetProgram offsetDone h = none := rfl

theorem runs_offset (σ : TapeStore) (d r : ℕ)
    (hd : σ 2 = List.replicate d true) (hr : σ 3 = List.replicate r true)
    (he : σ 29 = []) (hc : σ 31 = []) :
    RunsIn offsetProgram.step (cfg offsetStart (storeTapes σ))
      (cfg offsetDone
        (storeTapes (Function.update σ 29 (List.replicate (d + (d + r - 1)) true))))
      (12 * d + 10 * r + 27) := by
  let τ := Function.update σ 29 (List.replicate (d + r - 1) true)
  have hs := runs_sumMinus (dst := 29) (by decide) (by decide) (by decide)
    σ d r hd hr he hc
  have ha := TapeCopyAdd.runs_add (src := 2) (scratch := 31) (dst := 29)
    (by decide) (by decide) τ d (d + r - 1)
    (by simp [τ, hd]) (by simp [τ]) (by simp [τ, hc])
  have ha' : RunsIn (TapeCopyAdd.program 2 31 29).step
      (cfg TapeCopyAdd.start (storeTapes τ))
      (cfg TapeCopyAdd.done
        (storeTapes (Function.update σ 29 (List.replicate (d + (d + r - 1)) true))))
      (10 * d + 8) := by
    simpa only [τ, Function.update_idem, Nat.add_comm (d + r - 1) d] using ha
  have h := join_runs (sumMinusProgram 29) (TapeCopyAdd.program 2 31 29)
    (fun _ => TapeCopyAdd.start) hs rfl ha'
  have hcost : 2 * d + 10 * r + 18 + 1 + (10 * d + 8) =
      12 * d + 10 * r + 27 := by omega
  simpa only [offsetProgram, offsetStart, offsetDone, hcost] using h

def terminalProgram : TapeMultiProgram Unit := fun _ _ => none

abbrev HashState := TapeCopy.State ⊕ (SumMinusState ⊕ Unit)

def hashProgram : TapeMultiProgram HashState :=
  joinCode (TapeCopy.code 2 29)
    (joinCode (sumMinusProgram 30) terminalProgram (fun _ => ()))
    (fun _ => .inl sumMinusStart)

def hashStart : HashState := .inl .start
def hashDone : HashState := .inr (.inr ())

abbrev PolynomialState := OffsetState ⊕ TapeCopy.State

def polynomialProgram : TapeMultiProgram PolynomialState :=
  joinCode offsetProgram (TapeCopy.code 3 30) (fun _ => TapeCopy.State.start)

def polynomialStart : PolynomialState := .inl offsetStart
def polynomialDone : PolynomialState := .inr .done

abbrev CoefficientsState := OffsetState ⊕ (TapeCopyAdd.State ⊕ TapeProductLength.State)

def coefficientsProgram : TapeMultiProgram CoefficientsState :=
  joinCode offsetProgram
    (joinCode (TapeCopyAdd.program 3 31 29) TapeProductLength.program
      (fun _ => TapeProductLength.start))
    (fun _ => .inl TapeCopyAdd.start)

def coefficientsStart : CoefficientsState := .inl offsetStart
def coefficientsDone : CoefficientsState := .inr (.inr TapeProductLength.done)

def State : InputBlockKind → Type
  | .data => TapeCopy.State
  | .hash => HashState
  | .polynomial => PolynomialState
  | .coefficients => CoefficientsState

instance (kind : InputBlockKind) : Fintype (State kind) := by
  cases kind <;> dsimp [State] <;> infer_instance

def program : (kind : InputBlockKind) → TapeMultiProgram (State kind)
  | .data => TapeCopy.code 2 30
  | .hash => hashProgram
  | .polynomial => polynomialProgram
  | .coefficients => coefficientsProgram

def start : (kind : InputBlockKind) → State kind
  | .data => .start
  | .hash => hashStart
  | .polynomial => polynomialStart
  | .coefficients => coefficientsStart

def done : (kind : InputBlockKind) → State kind
  | .data => .done
  | .hash => hashDone
  | .polynomial => polynomialDone
  | .coefficients => coefficientsDone

def outputStore (σ : TapeStore) (n : ℕ) (kind : InputBlockKind) : TapeStore :=
  Function.update
    (Function.update σ 29 (List.replicate (inputBlockOffset n kind) true))
    30 (List.replicate (inputBlockLength n kind) true)

@[simp] theorem outputStore_offset (σ : TapeStore) (n : ℕ) (kind : InputBlockKind) :
    outputStore σ n kind 29 = List.replicate (inputBlockOffset n kind) true := by
  simp [outputStore]

@[simp] theorem outputStore_length (σ : TapeStore) (n : ℕ) (kind : InputBlockKind) :
    outputStore σ n kind 30 = List.replicate (inputBlockLength n kind) true := by
  simp [outputStore]

theorem outputStore_other (σ : TapeStore) (n : ℕ) (kind : InputBlockKind)
    (s : TapeRegister) (h29 : s ≠ 29) (h30 : s ≠ 30) :
    outputStore σ n kind s = σ s := by
  simp [outputStore, Function.update, h29, h30]

def cost (n : ℕ) : InputBlockKind → ℕ :=
  let d := dataDimension n
  let r := hashDimension d
  let t := independenceOrder d
  fun kind => match kind with
    | .data => 2 * d + 4
    | .hash => 4 * d + 10 * r + 24
    | .polynomial => 12 * d + 12 * r + 32
    | .coefficients => 12 * d + 20 * r + 45 + t * (10 * r + 16)

private theorem runs_hash (σ : TapeStore) (d r : ℕ)
    (hd : σ 2 = List.replicate d true) (hr : σ 3 = List.replicate r true)
    (h29 : σ 29 = []) (h30 : σ 30 = []) (h31 : σ 31 = []) :
    RunsIn hashProgram.step (cfg hashStart (storeTapes σ))
      (cfg hashDone (storeTapes (Function.update
        (Function.update σ 29 (List.replicate d true))
        30 (List.replicate (d + r - 1) true)))) (4 * d + 10 * r + 24) := by
  let τ := Function.update σ 29 (List.replicate d true)
  have hc := TapeStoreRuns.copy (src := 2) (dst := 29) (by decide) σ h29
  simp only [hd, List.length_replicate] at hc
  have hs := runs_sumMinus (dst := 30) (by decide) (by decide) (by decide) τ d r
    (by simp [τ, hd]) (by simp [τ, hr]) (by simp [τ, h30]) (by simp [τ, h31])
  have hz := RunsIn.refl terminalProgram.step
    (cfg () (storeTapes (Function.update τ 30 (List.replicate (d + r - 1) true))))
  have htail := join_runs (sumMinusProgram 30) terminalProgram (fun _ => ()) hs rfl hz
  have h := join_runs (TapeCopy.code 2 29)
    (joinCode (sumMinusProgram 30) terminalProgram (fun _ => ()))
    (fun _ => .inl sumMinusStart) hc rfl htail
  have hcost : 2 * d + 4 + 1 + (2 * d + 10 * r + 18 + 1 + 0) =
      4 * d + 10 * r + 24 := by omega
  simpa only [hashProgram, hashStart, hashDone, τ, hcost] using h

private theorem runs_polynomial (σ : TapeStore) (d r : ℕ)
    (hd : σ 2 = List.replicate d true) (hr : σ 3 = List.replicate r true)
    (h29 : σ 29 = []) (h30 : σ 30 = []) (h31 : σ 31 = []) :
    RunsIn polynomialProgram.step (cfg polynomialStart (storeTapes σ))
      (cfg polynomialDone (storeTapes (Function.update
        (Function.update σ 29 (List.replicate (d + (d + r - 1)) true))
        30 (List.replicate r true)))) (12 * d + 12 * r + 32) := by
  let τ := Function.update σ 29 (List.replicate (d + (d + r - 1)) true)
  have ho := runs_offset σ d r hd hr h29 h31
  have hc := TapeStoreRuns.copy (src := 3) (dst := 30) (by decide) τ (by simp [τ, h30])
  have hs : τ 3 = List.replicate r true := by simp [τ, hr]
  simp only [hs, List.length_replicate] at hc
  have h := join_runs offsetProgram (TapeCopy.code 3 30)
    (fun _ => TapeCopy.State.start) ho rfl hc
  have hcost : 12 * d + 10 * r + 27 + 1 + (2 * r + 4) =
      12 * d + 12 * r + 32 := by omega
  simpa only [polynomialProgram, polynomialStart, polynomialDone, τ, hcost] using h

private theorem runs_coefficients (σ : TapeStore) (d r t : ℕ)
    (hd : σ 2 = List.replicate d true) (hr : σ 3 = List.replicate r true)
    (ht : σ 4 = List.replicate t true) (h29 : σ 29 = []) (h30 : σ 30 = [])
    (h31 : σ 31 = []) (h5 : σ 5 = []) (h6 : σ 6 = []) :
    RunsIn coefficientsProgram.step (cfg coefficientsStart (storeTapes σ))
      (cfg coefficientsDone (storeTapes (Function.update
        (Function.update σ 29 (List.replicate (d + (d + r - 1) + r) true))
        30 (List.replicate (t * r) true))))
      (12 * d + 20 * r + 45 + t * (10 * r + 16)) := by
  let τ := Function.update σ 29 (List.replicate (d + (d + r - 1)) true)
  let υ := Function.update σ 29 (List.replicate (d + (d + r - 1) + r) true)
  have ho := runs_offset σ d r hd hr h29 h31
  have ha := TapeCopyAdd.runs_add (src := 3) (scratch := 31) (dst := 29)
    (by decide) (by decide) τ r (d + (d + r - 1))
    (by simp [τ, hr]) (by simp [τ]) (by simp [τ, h31])
  have ha' : RunsIn (TapeCopyAdd.program 3 31 29).step
      (cfg TapeCopyAdd.start (storeTapes τ))
      (cfg TapeCopyAdd.done (storeTapes υ)) (10 * r + 8) := by
    simpa only [τ, υ, Function.update_idem] using ha
  have hp := TapeProductLength.runs_product υ t r (by simp [υ, ht])
    (by simp [υ, hr]) (by simp [υ, h5]) (by simp [υ, h6]) (by simp [υ, h30])
  have htail := join_runs (TapeCopyAdd.program 3 31 29) TapeProductLength.program
    (fun _ => TapeProductLength.start) ha' rfl hp
  have h := join_runs offsetProgram
    (joinCode (TapeCopyAdd.program 3 31 29) TapeProductLength.program
      (fun _ => TapeProductLength.start))
    (fun _ => .inl TapeCopyAdd.start) ho rfl htail
  have hcost : 12 * d + 10 * r + 27 + 1 + (10 * r + 8 + 1 +
      (t * (10 * r + 16) + 8)) = 12 * d + 20 * r + 45 + t * (10 * r + 16) := by omega
  simpa only [coefficientsProgram, coefficientsStart, coefficientsDone,
    TapeProductLength.outputStore, TapeProductLength.cost, υ, hcost] using h

theorem runs_prepare (σ : TapeStore) (n : ℕ) (kind : InputBlockKind)
    (hd : σ 2 = List.replicate (dataDimension n) true)
    (hr : σ 3 = List.replicate (hashDimension (dataDimension n)) true)
    (ht : σ 4 = List.replicate (independenceOrder (dataDimension n)) true)
    (h29 : σ 29 = []) (h30 : σ 30 = []) (h31 : σ 31 = [])
    (h5 : σ 5 = []) (h6 : σ 6 = []) (_h7 : σ 7 = []) :
    RunsIn (program kind).step (cfg (start kind) (storeTapes σ))
      (cfg (done kind) (storeTapes (outputStore σ n kind))) (cost n kind) := by
  cases kind with
  | data =>
      have h := TapeStoreRuns.copy (src := 2) (dst := 30) (by decide) σ h30
      have he : Function.update σ 29 [] = σ := Function.update_eq_self_iff.mpr h29.symm
      simpa only [State, program, start, done, outputStore, inputBlockOffset, inputBlockLength,
        cost, List.replicate_zero, he, hd, List.length_replicate] using h
  | hash =>
      simpa only [State, program, start, done, outputStore, inputBlockOffset, inputBlockLength,
        hashOffset, hashBlockLength, cost] using
        runs_hash σ (dataDimension n) (hashDimension (dataDimension n)) hd hr h29 h30 h31
  | polynomial =>
      simpa only [State, program, start, done, outputStore, inputBlockOffset, inputBlockLength,
        polynomialOffset, hashOffset, hashBlockLength, cost] using
        runs_polynomial σ (dataDimension n) (hashDimension (dataDimension n)) hd hr h29 h30 h31
  | coefficients =>
      simpa only [State, program, start, done, outputStore, inputBlockOffset, inputBlockLength,
        coefficientsOffset, polynomialOffset, hashOffset, hashBlockLength, cost] using
        runs_coefficients σ (dataDimension n) (hashDimension (dataDimension n))
          (independenceOrder (dataDimension n)) hd hr ht h29 h30 h31 h5 h6

theorem cost_le (n : ℕ) (kind : InputBlockKind) : cost n kind ≤ 128 * (n + 1) ^ 2 := by
  have hd : dataDimension n ≤ n := Nat.div_le_self n 5
  have hr : hashDimension (dataDimension n) ≤ n :=
    Nat.le_trans (hashDimension_le (dataDimension n)) hd
  have ht : independenceOrder (dataDimension n) ≤ n :=
    Nat.le_trans (independenceOrder_le (dataDimension n)) hd
  have hp : independenceOrder (dataDimension n) *
      (10 * hashDimension (dataDimension n) + 16) ≤ n * (10 * n + 16) :=
    Nat.mul_le_mul ht (by omega)
  cases kind <;> dsimp [cost] <;> nlinarith

@[simp] theorem program_done (kind : InputBlockKind) (h : TapeHeads) :
    program kind (done kind) h = none := by
  cases kind <;> rfl

end TapeInputPrepare
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeReadPush

open TapeMultiProgram TapeRouting TapeUnary TapeCopy TapeArithmetic

abbrev State := TapeArray.State ⊕ (Bool × TapeUnary.IncState)

def program (index source destination : TapeRegister) : TapeMultiProgram State :=
  joinCode (TapeArray.code index source id)
    (TapeProductTerm.carryCode (fun b : Bool => TapeFill.pushProgram destination b))
    (fun q => (TapeProductTerm.readFlag q, TapeUnary.IncState.start))

def start : State := .inl TapeArray.State.start

def done (b : Bool) : State := .inr (b, TapeUnary.IncState.done)

theorem runs_read_push {index source : TapeRegister} (hne : index ≠ source)
    (destination : TapeRegister) (T : TapeTapes)
    («prefix» suffix acc : List Bool) (b : Bool)
    (hi : T index = counterTape «prefix».length)
    (hs : T source = wordTape («prefix» ++ b :: suffix))
    (hd : T destination = wordTape acc) :
    RunsIn (program index source destination).step (cfg start T)
      (cfg (done b) (Function.update T destination (wordTape (b :: acc))))
      (2 * «prefix».length + 7) := by
  have hread := TapeProductTerm.read_at hne T «prefix» suffix b hi hs
  have hpush := TapeFill.runs_push destination b T acc hd
  have hcarry := TapeProductTerm.carry_runs
    (fun b : Bool => TapeFill.pushProgram destination b) b hpush
  have hall := join_runs (TapeArray.code index source id)
    (TapeProductTerm.carryCode (fun b : Bool => TapeFill.pushProgram destination b))
    (fun q => (TapeProductTerm.readFlag q, TapeUnary.IncState.start)) hread rfl hcarry
  have htime : (2 * «prefix».length + 4) + 1 + 2 = 2 * «prefix».length + 7 := by omega
  simpa only [program, start, done, htime] using hall

@[simp] theorem program_done (index source destination : TapeRegister)
    (b : Bool) (h : TapeHeads) :
    program index source destination (done b) h = none := rfl

theorem runs_store {index source : TapeRegister} (hne : index ≠ source)
    (destination : TapeRegister) (σ : TapeStore) («prefix» suffix : List Bool) (b : Bool)
    (hi : σ index = List.replicate «prefix».length true)
    (hs : σ source = «prefix» ++ b :: suffix) :
    RunsIn (program index source destination).step (cfg start (storeTapes σ))
      (cfg (done b) (storeTapes (Function.update σ destination (b :: σ destination))))
      (2 * «prefix».length + 7) := by
  have h := runs_read_push hne destination (storeTapes σ) «prefix» suffix (σ destination) b
    (by simp only [storeTapes_apply, hi, counterTape])
    (by simp only [storeTapes_apply, hs]) rfl
  simpa only [storeTapes_update] using h

end TapeReadPush
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeInputBlockLoop

open TapeMultiProgram TapeCopy TapeRouting TapeUnary TapeArithmetic

abbrev Registers := Fin 5 ↪ TapeRegister

abbrev source (R : Registers) := R 0
abbrev index (R : Registers) := R 1
abbrev count (R : Registers) := R 2
abbrev scratch (R : Registers) := R 3
abbrev destination (R : Registers) := R 4

@[simp] theorem register_eq (R : Registers) (i j : Fin 5) :
    R i = R j ↔ i = j := R.injective.eq_iff

theorem index_ne_source (R : Registers) : index R ≠ source R := by
  simp [index, source]

def blockStore (R : Registers) (σ : TapeStore) (pos remaining : ℕ)
    (bits : List Bool) : TapeStore :=
  Function.update
    (Function.update (Function.update σ (count R) (List.replicate remaining true))
      (index R) (List.replicate pos true)) (destination R) bits

@[simp] theorem blockStore_source (R : Registers) (σ : TapeStore)
    (pos remaining : ℕ) (bits : List Bool) :
    blockStore R σ pos remaining bits (source R) = σ (source R) := by
  simp [blockStore, source, index, count, destination]

@[simp] theorem blockStore_index (R : Registers) (σ : TapeStore)
    (pos remaining : ℕ) (bits : List Bool) :
    blockStore R σ pos remaining bits (index R) = List.replicate pos true := by
  simp [blockStore, index, count, destination]

@[simp] theorem blockStore_count (R : Registers) (σ : TapeStore)
    (pos remaining : ℕ) (bits : List Bool) :
    blockStore R σ pos remaining bits (count R) = List.replicate remaining true := by
  simp [blockStore, index, count, destination]

@[simp] theorem blockStore_destination (R : Registers) (σ : TapeStore)
    (pos remaining : ℕ) (bits : List Bool) :
    blockStore R σ pos remaining bits (destination R) = bits := by
  simp [blockStore]

@[simp] theorem update_blockStore_count (R : Registers) (σ : TapeStore)
    (pos remaining remaining' : ℕ) (bits : List Bool) :
    Function.update (blockStore R σ pos remaining bits) (count R)
      (List.replicate remaining' true) = blockStore R σ pos remaining' bits := by
  funext q
  by_cases hc : q = count R <;> by_cases hi : q = index R <;>
    by_cases hd : q = destination R <;>
    simp_all [blockStore, Function.update, count, index, destination]

@[simp] theorem update_blockStore_index (R : Registers) (σ : TapeStore)
    (pos pos' remaining : ℕ) (bits : List Bool) :
    Function.update (blockStore R σ pos remaining bits) (index R)
      (List.replicate pos' true) = blockStore R σ pos' remaining bits := by
  funext q
  by_cases hc : q = count R <;> by_cases hi : q = index R <;>
    by_cases hd : q = destination R <;>
    simp_all [blockStore, Function.update, count, index, destination]

@[simp] theorem update_blockStore_destination (R : Registers) (σ : TapeStore)
    (pos remaining : ℕ) (bits bits' : List Bool) :
    Function.update (blockStore R σ pos remaining bits) (destination R) bits' =
      blockStore R σ pos remaining bits' := by
  simp only [blockStore, Function.update_idem]

abbrev BodyState := DecState ⊕ TapeReadPush.State

def bodyProgram (R : Registers) : TapeMultiProgram BodyState :=
  joinCode (decProgram (index R))
    (TapeReadPush.program (index R) (source R) (destination R))
    (fun _ => TapeReadPush.start)

def bodyStart : BodyState := .inl DecState.start
def bodyDone (b : Bool) : BodyState := .inr (TapeReadPush.done b)

@[simp] theorem body_done (R : Registers) (b : Bool) (h : TapeHeads) :
    bodyProgram R (bodyDone b) h = none := rfl

theorem runs_body (R : Registers) (σ : TapeStore) («prefix» suffix acc : List Bool)
    (b : Bool) (remaining : ℕ)
    (hsource : σ (source R) = «prefix» ++ b :: suffix) :
    RunsIn (bodyProgram R).step
      (cfg bodyStart (storeTapes
        (blockStore R σ («prefix».length + 1) remaining acc)))
      (cfg (bodyDone b) (storeTapes
        (blockStore R σ «prefix».length remaining (b :: acc))))
      (2 * «prefix».length + 12) := by
  have hd := decrement (index R)
    (storeTapes (blockStore R σ («prefix».length + 1) remaining acc))
    («prefix».length + 1) (by simp [counterTape])
  have hd' : RunsIn (decProgram (index R)).step
      (cfg DecState.start (storeTapes (blockStore R σ («prefix».length + 1) remaining acc)))
      (cfg (DecState.done true) (storeTapes (blockStore R σ «prefix».length remaining acc))) 4 := by
    simpa only [Nat.add_sub_cancel, Nat.zero_lt_succ, decide_true,
      counterTape, ← storeTapes_update, update_blockStore_index] using hd
  have hp := TapeReadPush.runs_store (index_ne_source R) (destination R)
    (blockStore R σ «prefix».length remaining acc) «prefix» suffix b
    (by simp) (by simpa using hsource)
  have hp' : RunsIn
      (TapeReadPush.program (index R) (source R) (destination R)).step
      (cfg TapeReadPush.start (storeTapes (blockStore R σ «prefix».length remaining acc)))
      (cfg (TapeReadPush.done b)
        (storeTapes (blockStore R σ «prefix».length remaining (b :: acc))))
      (2 * «prefix».length + 7) := by
    simpa only [blockStore_destination, update_blockStore_destination] using hp
  have hall := join_runs (decProgram (index R))
    (TapeReadPush.program (index R) (source R) (destination R))
    (fun _ => TapeReadPush.start) hd' rfl hp'
  have ht : 4 + 1 + (2 * «prefix».length + 7) = 2 * «prefix».length + 12 := by omega
  simpa only [bodyProgram, bodyStart, bodyDone, ht] using hall

abbrev State := LoopState DecState BodyState

def program (R : Registers) : TapeMultiProgram State :=
  loopCode (decProgram (count R)) (bodyProgram R)
    DecState.start bodyStart decPositive

def start : State := loopTest DecState.start
def done : State := loopDone

@[simp] theorem program_done (R : Registers) (h : TapeHeads) :
    program R done h = none := rfl

theorem runs_block (R : Registers) (σ : TapeStore)
    («prefix» block suffix acc : List Bool)
    (hsource : σ (source R) = «prefix» ++ block ++ suffix) :
    RunsIn (program R).step
      (cfg start (storeTapes
        (blockStore R σ («prefix».length + block.length) block.length acc)))
      (cfg done (storeTapes (blockStore R σ «prefix».length 0 (block ++ acc))))
      (block.length * (2 * «prefix».length + block.length + 17) + 3) := by
  induction block using List.reverseRecOn generalizing suffix acc with
  | nil =>
    have hd := decrement_empty (count R)
      (storeTapes (blockStore R σ «prefix».length 0 acc)) (by simp [])
    have he := loop_exit (decProgram (count R)) (bodyProgram R)
      DecState.start bodyStart decPositive hd rfl rfl
    simpa only [program, start, done, List.length_nil, List.nil_append,
      Nat.add_zero, Nat.zero_mul, Nat.zero_add] using he
  | append_singleton block b ih =>
    have hd := decrement (count R)
      (storeTapes (blockStore R σ («prefix».length + block.length + 1)
        (block.length + 1) acc)) (block.length + 1) (by simp [counterTape])
    have hd' : RunsIn (decProgram (count R)).step
        (cfg DecState.start (storeTapes (blockStore R σ
          («prefix».length + block.length + 1) (block.length + 1) acc)))
        (cfg (DecState.done true) (storeTapes (blockStore R σ
          («prefix».length + block.length + 1) block.length acc))) 4 := by
      simpa only [Nat.add_sub_cancel, Nat.zero_lt_succ, decide_true,
        counterTape, ← storeTapes_update, update_blockStore_count] using hd
    have hs : σ (source R) = («prefix» ++ block) ++ b :: suffix := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hsource
    have hb := runs_body R σ («prefix» ++ block) suffix acc b block.length hs
    simp only [List.length_append] at hb
    have hit := loop_iter (decProgram (count R)) (bodyProgram R)
      DecState.start bodyStart decPositive hd' rfl rfl hb (by simp)
    have hs' : σ (source R) = «prefix» ++ block ++ (b :: suffix) := hs
    have hrest := ih (b :: suffix) (b :: acc) hs'
    have hall := hit.trans hrest
    have ht : 4 + 1 + (2 * («prefix».length + block.length) + 12) + 1 +
        (block.length * (2 * «prefix».length + block.length + 17) + 3) =
        (block.length + 1) * (2 * «prefix».length + (block.length + 1) + 17) + 3 := by
      ring
    have hi : «prefix».length + (block.length + 1) = «prefix».length + block.length + 1 := by
      omega
    simpa only [program, start, done, List.length_append, List.length_singleton,
      List.append_assoc, List.cons_append, List.nil_append, hi, ht] using hall

end TapeInputBlockLoop
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeInputBlocks

open TapeMultiProgram TapeCopy TapeRouting TapeUnary TapeArithmetic
open TapeInputBlockLoop

abbrev PrepareState := TapeCopy.State ⊕ AddState

def prepareProgram (R : Registers) : TapeMultiProgram PrepareState :=
  joinCode (TapeCopy.code (count R) (scratch R))
    (addProgram (scratch R) (index R)) (fun _ => addStart)

def prepareStart : PrepareState := .inl TapeCopy.State.start
def prepareDone : PrepareState := .inr addDone

abbrev State := PrepareState ⊕ TapeInputBlockLoop.State

def program (R : Registers) : TapeMultiProgram State :=
  joinCode (prepareProgram R) (TapeInputBlockLoop.program R)
    (fun _ => TapeInputBlockLoop.start)

def start : State := .inl prepareStart
def done : State := .inr TapeInputBlockLoop.done

@[simp] theorem prepare_done (R : Registers) (h : TapeHeads) :
    prepareProgram R prepareDone h = none := rfl

@[simp] theorem program_done (R : Registers) (h : TapeHeads) :
    program R done h = none := rfl

theorem runs_prepare (R : Registers) (σ : TapeStore) (offset len : ℕ)
    (hi : σ (index R) = List.replicate offset true)
    (hc : σ (count R) = List.replicate len true)
    (hs : σ (scratch R) = []) :
    RunsIn (prepareProgram R).step (cfg prepareStart (storeTapes σ))
      (cfg prepareDone (storeTapes
        (Function.update σ (index R) (List.replicate (offset + len) true))))
      (10 * len + 8) := by
  have hcs : count R ≠ scratch R := by simp [count, scratch]
  have hsi : scratch R ≠ index R := by simp [scratch, index]
  let U := Function.update σ (scratch R) (List.replicate len true)
  have hcopy := TapeStoreRuns.copy hcs σ hs
  have hcopy' : RunsIn (TapeCopy.code (count R) (scratch R)).step
      (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes U)) (2 * len + 4) := by
    simpa only [hc, List.length_replicate] using hcopy
  have hadd := TapeStoreRuns.add hsi U len offset
    (by simp [U]) (by simp [U, hi, Ne.symm hsi])
  have hclear : Function.update U (scratch R) [] = σ := by
    dsimp [U]
    rw [Function.update_idem, ← hs, Function.update_eq_self]
  have hadd' : RunsIn (addProgram (scratch R) (index R)).step
      (cfg addStart (storeTapes U))
      (cfg addDone (storeTapes
        (Function.update σ (index R) (List.replicate (offset + len) true))))
      (8 * len + 3) := by
    simpa only [hclear] using hadd
  have hall := join_runs (TapeCopy.code (count R) (scratch R))
    (addProgram (scratch R) (index R)) (fun _ => addStart) hcopy' rfl hadd'
  have ht : (2 * len + 4) + 1 + (8 * len + 3) = 10 * len + 8 := by omega
  simpa only [prepareProgram, prepareStart, prepareDone, ht] using hall

theorem blockStore_prepared (R : Registers) (σ : TapeStore) (offset len : ℕ)
    (acc : List Bool) (hc : σ (count R) = List.replicate len true)
    (hd : σ (destination R) = acc) :
    blockStore R σ (offset + len) len acc =
      Function.update σ (index R) (List.replicate (offset + len) true) := by
  funext q
  by_cases hq : q = destination R <;> by_cases hi : q = index R <;>
    by_cases hk : q = count R <;>
    simp_all [blockStore, Function.update, count, index, destination]

theorem blockStore_finished (R : Registers) (σ : TapeStore) (offset : ℕ)
    (bits : List Bool) (hi : σ (index R) = List.replicate offset true) :
    blockStore R σ offset 0 bits =
      Function.update (Function.update σ (count R) []) (destination R) bits := by
  funext q
  by_cases hq : q = destination R <;> by_cases hk : q = count R <;>
    by_cases hj : q = index R <;>
    simp_all [blockStore, Function.update, count, index, destination]

theorem runs_extract (R : Registers) (σ : TapeStore)
    («prefix» block suffix acc : List Bool)
    (hinput : σ (source R) = «prefix» ++ block ++ suffix)
    (hi : σ (index R) = List.replicate «prefix».length true)
    (hc : σ (count R) = List.replicate block.length true)
    (hs : σ (scratch R) = [])
    (hd : σ (destination R) = acc) :
    RunsIn (program R).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ (count R) [])
        (destination R) (block ++ acc))))
      (block.length * (2 * «prefix».length + block.length + 27) + 12) := by
  have hp := runs_prepare R σ «prefix».length block.length hi hc hs
  have hb := TapeInputBlockLoop.runs_block R σ «prefix» block suffix acc hinput
  rw [blockStore_prepared R σ «prefix».length block.length acc hc hd,
    blockStore_finished R σ «prefix».length (block ++ acc) hi] at hb
  have hall := join_runs (prepareProgram R) (TapeInputBlockLoop.program R)
    (fun _ => TapeInputBlockLoop.start) hp (by simp) hb
  have ht : (10 * block.length + 8) + 1 +
      (block.length * (2 * «prefix».length + block.length + 17) + 3) =
      block.length * (2 * «prefix».length + block.length + 27) + 12 := by ring
  simpa only [program, start, done, ht] using hall

def outputRegister : InputBlockKind → TapeRegister
  | .data => TapeRegister.dataBits
  | .hash => TapeRegister.keyBits
  | .polynomial => TapeRegister.polyBits
  | .coefficients => TapeRegister.coeffBits

def canonicalRegisters (kind : InputBlockKind) : Registers where
  toFun i := match i.val with
    | 0 => TapeRegister.input
    | 1 => TapeRegister.temp0
    | 2 => TapeRegister.temp1
    | 3 => TapeRegister.temp2
    | _ => outputRegister kind
  inj' := by cases kind <;> decide

@[simp] theorem canonical_source (kind : InputBlockKind) :
    source (canonicalRegisters kind) = TapeRegister.input := rfl

@[simp] theorem canonical_index (kind : InputBlockKind) :
    index (canonicalRegisters kind) = TapeRegister.temp0 := rfl

@[simp] theorem canonical_count (kind : InputBlockKind) :
    count (canonicalRegisters kind) = TapeRegister.temp1 := rfl

@[simp] theorem canonical_scratch (kind : InputBlockKind) :
    scratch (canonicalRegisters kind) = TapeRegister.temp2 := rfl

@[simp] theorem canonical_destination (kind : InputBlockKind) :
    destination (canonicalRegisters kind) = outputRegister kind := rfl

def canonicalProgram (kind : InputBlockKind) : TapeMultiProgram State :=
  program (canonicalRegisters kind)

@[simp] theorem canonical_done (kind : InputBlockKind) (h : TapeHeads) :
    canonicalProgram kind done h = none := rfl

theorem canonical_cost_le {w : List Bool} (hfit : InputFits w) (kind : InputBlockKind) :
    inputBlockLength w.length kind *
        (2 * inputBlockOffset w.length kind + inputBlockLength w.length kind + 27) + 12 ≤
      w.length * (3 * w.length + 27) + 12 := by
  have hend := inputBlock_end_le hfit kind
  have hlen : inputBlockLength w.length kind ≤ w.length := by omega
  apply Nat.add_le_add_right _ 12
  exact Nat.mul_le_mul hlen (by omega)

theorem runs_canonical_block (kind : InputBlockKind) (σ : TapeStore) (w : List Bool)
    (hfit : InputFits w) (hw : σ TapeRegister.input = w)
    (hi : σ TapeRegister.temp0 = List.replicate (inputBlockOffset w.length kind) true)
    (hc : σ TapeRegister.temp1 = List.replicate (inputBlockLength w.length kind) true)
    (hs : σ TapeRegister.temp2 = []) (hd : σ (outputRegister kind) = []) :
    RunsIn (canonicalProgram kind).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ TapeRegister.temp1 [])
        (outputRegister kind) (inputBlockData w kind))))
      (inputBlockLength w.length kind *
        (2 * inputBlockOffset w.length kind + inputBlockLength w.length kind + 27) + 12) := by
  have hall := runs_extract (canonicalRegisters kind) σ
    (w.take (inputBlockOffset w.length kind)) (inputBlockData w kind)
    (w.drop (inputBlockOffset w.length kind + inputBlockLength w.length kind)) []
    (by simpa only [canonical_source, hw] using inputBlock_reconstruct w kind)
    (by simpa only [canonical_index, inputBlock_prefix_length hfit kind] using hi)
    (by simpa only [canonical_count, inputBlockData_length hfit kind] using hc)
    (by simpa only [canonical_scratch] using hs)
    (by simpa only [canonical_destination] using hd)
  simpa only [canonicalProgram, canonical_count, canonical_destination,
    List.append_nil, inputBlock_prefix_length hfit kind,
    inputBlockData_length hfit kind] using hall

theorem runs_data (σ : TapeStore) (w : List Bool) (hfit : InputFits w)
    (hw : σ TapeRegister.input = w) (hi : σ TapeRegister.temp0 = [])
    (hc : σ TapeRegister.temp1 = List.replicate (dataDimension w.length) true)
    (hs : σ TapeRegister.temp2 = []) (hd : σ TapeRegister.dataBits = []) :
    RunsIn (canonicalProgram .data).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ TapeRegister.temp1 [])
        TapeRegister.dataBits (inputBlockData w .data))))
      (dataDimension w.length * (dataDimension w.length + 27) + 12) := by
  simpa only [inputBlockOffset, inputBlockLength, outputRegister, Nat.mul_zero,
    Nat.zero_add] using runs_canonical_block .data σ w hfit hw hi hc hs hd

theorem runs_hash (σ : TapeStore) (w : List Bool) (hfit : InputFits w)
    (hw : σ TapeRegister.input = w)
    (hi : σ TapeRegister.temp0 =
      List.replicate (hashOffset (dataDimension w.length)) true)
    (hc : σ TapeRegister.temp1 =
      List.replicate (hashBlockLength (dataDimension w.length)) true)
    (hs : σ TapeRegister.temp2 = []) (hd : σ TapeRegister.keyBits = []) :
    RunsIn (canonicalProgram .hash).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ TapeRegister.temp1 [])
        TapeRegister.keyBits (inputBlockData w .hash))))
      (hashBlockLength (dataDimension w.length) *
        (2 * hashOffset (dataDimension w.length) +
          hashBlockLength (dataDimension w.length) + 27) + 12) :=
  runs_canonical_block .hash σ w hfit hw hi hc hs hd

theorem runs_polynomial (σ : TapeStore) (w : List Bool) (hfit : InputFits w)
    (hw : σ TapeRegister.input = w)
    (hi : σ TapeRegister.temp0 =
      List.replicate (polynomialOffset (dataDimension w.length)) true)
    (hc : σ TapeRegister.temp1 =
      List.replicate (hashDimension (dataDimension w.length)) true)
    (hs : σ TapeRegister.temp2 = []) (hd : σ TapeRegister.polyBits = []) :
    RunsIn (canonicalProgram .polynomial).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ TapeRegister.temp1 [])
        TapeRegister.polyBits (inputBlockData w .polynomial))))
      (hashDimension (dataDimension w.length) *
        (2 * polynomialOffset (dataDimension w.length) +
          hashDimension (dataDimension w.length) + 27) + 12) :=
  runs_canonical_block .polynomial σ w hfit hw hi hc hs hd

theorem runs_coefficients (σ : TapeStore) (w : List Bool) (hfit : InputFits w)
    (hw : σ TapeRegister.input = w)
    (hi : σ TapeRegister.temp0 =
      List.replicate (coefficientsOffset (dataDimension w.length)) true)
    (hc : σ TapeRegister.temp1 = List.replicate
      (independenceOrder (dataDimension w.length) * hashDimension (dataDimension w.length)) true)
    (hs : σ TapeRegister.temp2 = []) (hd : σ TapeRegister.coeffBits = []) :
    RunsIn (canonicalProgram .coefficients).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ TapeRegister.temp1 [])
        TapeRegister.coeffBits (inputBlockData w .coefficients))))
      ((independenceOrder (dataDimension w.length) * hashDimension (dataDimension w.length)) *
        (2 * coefficientsOffset (dataDimension w.length) +
          independenceOrder (dataDimension w.length) * hashDimension (dataDimension w.length) +
          27) + 12) :=
  runs_canonical_block .coefficients σ w hfit hw hi hc hs hd

end TapeInputBlocks
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeDecodeBlock

open TapeMultiProgram TapeRouting

abbrev FinishState := TapeInputBlocks.State ⊕ TapeErase.State

def finishProgram (kind : InputBlockKind) : TapeMultiProgram FinishState :=
  joinCode (TapeInputBlocks.canonicalProgram kind) (TapeErase.code TapeRegister.temp0)
    (fun _ => TapeErase.State.start)

def finishStart : FinishState := .inl TapeInputBlocks.start
def finishDone : FinishState := .inr TapeErase.State.done

abbrev State (kind : InputBlockKind) := TapeInputPrepare.State kind ⊕ FinishState

def program (kind : InputBlockKind) : TapeMultiProgram (State kind) :=
  joinCode (TapeInputPrepare.program kind) (finishProgram kind) (fun _ => finishStart)

def start (kind : InputBlockKind) : State kind := .inl (TapeInputPrepare.start kind)
def done (kind : InputBlockKind) : State kind := .inr finishDone

@[simp] theorem program_done (kind : InputBlockKind) (h : TapeHeads) :
    program kind (done kind) h = none := rfl

def outputStore (σ : TapeStore) (w : List Bool) (kind : InputBlockKind) : TapeStore :=
  Function.update σ (TapeInputBlocks.outputRegister kind) (inputBlockData w kind)

theorem runs_block (σ : TapeStore) (w : List Bool) (kind : InputBlockKind)
    (hfit : InputFits w) (hw : σ TapeRegister.input = w)
    (hd : σ 2 = List.replicate (dataDimension w.length) true)
    (hr : σ 3 = List.replicate (hashDimension (dataDimension w.length)) true)
    (ht : σ 4 = List.replicate (independenceOrder (dataDimension w.length)) true)
    (h29 : σ 29 = []) (h30 : σ 30 = []) (h31 : σ 31 = [])
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h7 : σ 7 = [])
    (hout : σ (TapeInputBlocks.outputRegister kind) = []) :
    RunsIn (program kind).step (cfg (start kind) (storeTapes σ))
      (cfg (done kind) (storeTapes (outputStore σ w kind)))
      (200 * (w.length + 1) ^ 2) := by
  let τ := TapeInputPrepare.outputStore σ w.length kind
  let υ := Function.update (Function.update τ TapeRegister.temp1 [])
    (TapeInputBlocks.outputRegister kind) (inputBlockData w kind)
  have hp := TapeInputPrepare.runs_prepare σ w.length kind hd hr ht h29 h30 h31 h5 h6 h7
  have hi : τ TapeRegister.temp0 = List.replicate (inputBlockOffset w.length kind) true := by
    simp [τ, TapeInputPrepare.outputStore, TapeRegister.temp0]
  have hc : τ TapeRegister.temp1 = List.replicate (inputBlockLength w.length kind) true := by
    simp [τ, TapeInputPrepare.outputStore, TapeRegister.temp1]
  have hx := TapeInputBlocks.runs_canonical_block kind τ w hfit
    (by simpa [τ, TapeInputPrepare.outputStore, TapeRegister.input] using hw) hi hc
    (by simpa [τ, TapeInputPrepare.outputStore, TapeRegister.temp2] using h31)
    (by cases kind <;> simpa [τ, TapeInputPrepare.outputStore,
      TapeInputBlocks.outputRegister, TapeRegister.dataBits, TapeRegister.keyBits,
      TapeRegister.polyBits, TapeRegister.coeffBits] using hout)
  have he := TapeStoreRuns.erase TapeRegister.temp0 υ
  have hindex : υ TapeRegister.temp0 =
      List.replicate (inputBlockOffset w.length kind) true := by
    cases kind <;> simp [υ, τ, TapeInputPrepare.outputStore,
      TapeInputBlocks.outputRegister, TapeRegister.temp0, TapeRegister.temp1,
      TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits]
  have hrestore : Function.update υ TapeRegister.temp0 [] = outputStore σ w kind := by
    funext q
    cases kind <;> by_cases hq29 : q = 29 <;> by_cases hq30 : q = 30 <;>
      simp_all [υ, τ, TapeInputPrepare.outputStore, outputStore,
        TapeInputBlocks.outputRegister, TapeRegister.temp0, TapeRegister.temp1,
        TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits,
        Function.update_apply]
  rw [hrestore, hindex, List.length_replicate] at he
  have hf := join_runs (TapeInputBlocks.canonicalProgram kind)
    (TapeErase.code TapeRegister.temp0) (fun _ => TapeErase.State.start) hx rfl he
  have hall := join_runs (TapeInputPrepare.program kind) (finishProgram kind)
    (fun _ => finishStart) hp (by simp) hf
  apply hall.mono
  have hpbound := TapeInputPrepare.cost_le w.length kind
  have hxbound := TapeInputBlocks.canonical_cost_le hfit kind
  have hobound := inputBlock_offset_le hfit kind
  nlinarith [Nat.zero_le (w.length ^ 2)]

end TapeDecodeBlock
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeDecodeBlocks

open TapeMultiProgram TapeRouting

abbrev TailState := TapeDecodeBlock.State .polynomial ⊕ TapeDecodeBlock.State .coefficients

def tailProgram : TapeMultiProgram TailState :=
  joinCode (TapeDecodeBlock.program .polynomial) (TapeDecodeBlock.program .coefficients)
    (fun _ => TapeDecodeBlock.start .coefficients)

def tailStart : TailState := .inl (TapeDecodeBlock.start .polynomial)
def tailDone : TailState := .inr (TapeDecodeBlock.done .coefficients)

abbrev RestState := TapeDecodeBlock.State .hash ⊕ TailState

def restProgram : TapeMultiProgram RestState :=
  joinCode (TapeDecodeBlock.program .hash) tailProgram (fun _ => tailStart)

def restStart : RestState := .inl (TapeDecodeBlock.start .hash)
def restDone : RestState := .inr tailDone

abbrev State := TapeDecodeBlock.State .data ⊕ RestState

def program : TapeMultiProgram State :=
  joinCode (TapeDecodeBlock.program .data) restProgram (fun _ => restStart)

def start : State := .inl (TapeDecodeBlock.start .data)
def done : State := .inr restDone

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

def outputStore (σ : TapeStore) (w : List Bool) : TapeStore :=
  TapeDecodeBlock.outputStore
    (TapeDecodeBlock.outputStore
      (TapeDecodeBlock.outputStore (TapeDecodeBlock.outputStore σ w .data) w .hash)
      w .polynomial) w .coefficients

@[simp] theorem outputStore_block (σ : TapeStore) (w : List Bool) (kind : InputBlockKind) :
    outputStore σ w (TapeInputBlocks.outputRegister kind) = inputBlockData w kind := by
  cases kind <;> simp [outputStore, TapeDecodeBlock.outputStore,
    TapeInputBlocks.outputRegister, TapeRegister.dataBits, TapeRegister.keyBits,
    TapeRegister.polyBits, TapeRegister.coeffBits]

theorem outputStore_other (σ : TapeStore) (w : List Bool) (q : TapeRegister)
    (h15 : q ≠ 15) (h16 : q ≠ 16) (h17 : q ≠ 17) (h18 : q ≠ 18) :
    outputStore σ w q = σ q := by
  simp [outputStore, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister,
    TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits,
    TapeRegister.coeffBits, Function.update, h15, h16, h17, h18]

theorem runs_decode (σ : TapeStore) (w : List Bool)
    (hfit : InputFits w) (hw : σ TapeRegister.input = w)
    (hd : σ 2 = List.replicate (dataDimension w.length) true)
    (hr : σ 3 = List.replicate (hashDimension (dataDimension w.length)) true)
    (ht : σ 4 = List.replicate (independenceOrder (dataDimension w.length)) true)
    (h29 : σ 29 = []) (h30 : σ 30 = []) (h31 : σ 31 = [])
    (h5 : σ 5 = []) (h6 : σ 6 = []) (h7 : σ 7 = [])
    (h15 : σ 15 = []) (h16 : σ 16 = []) (h17 : σ 17 = []) (h18 : σ 18 = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (outputStore σ w))) (804 * (w.length + 1) ^ 2) := by
  let σ1 := TapeDecodeBlock.outputStore σ w .data
  let σ2 := TapeDecodeBlock.outputStore σ1 w .hash
  let σ3 := TapeDecodeBlock.outputStore σ2 w .polynomial
  have h0 := TapeDecodeBlock.runs_block σ w .data hfit hw hd hr ht
    h29 h30 h31 h5 h6 h7 h15
  have h1 := TapeDecodeBlock.runs_block σ1 w .hash hfit
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using hw)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using hd)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using hr)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using ht)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h29)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h30)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h31)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h5)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h6)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h7)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h16)
  have h2 := TapeDecodeBlock.runs_block σ2 w .polynomial hfit
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using hw)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using hd)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using hr)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using ht)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h29)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h30)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h31)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h5)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h6)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h7)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h17)
  have h3 := TapeDecodeBlock.runs_block σ3 w .coefficients hfit
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using hw)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using hd)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using hr)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using ht)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h29)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h30)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h31)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h5)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h6)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h7)
    (by simpa [σ1, σ2, σ3, TapeDecodeBlock.outputStore, TapeInputBlocks.outputRegister, TapeRegister.input, TapeRegister.dataBits, TapeRegister.keyBits, TapeRegister.polyBits, TapeRegister.coeffBits] using h18)
  have htail := join_runs (TapeDecodeBlock.program .polynomial)
    (TapeDecodeBlock.program .coefficients) (fun _ => TapeDecodeBlock.start .coefficients)
    h2 (by simp) h3
  have hrest := join_runs (TapeDecodeBlock.program .hash) tailProgram
    (fun _ => tailStart) h1 (by simp) htail
  have hall := join_runs (TapeDecodeBlock.program .data) restProgram
    (fun _ => restStart) h0 (by simp) hrest
  apply hall.mono
  have hpos : 1 ≤ (w.length + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  omega

end TapeDecodeBlocks
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeDecodeParsed

open TapeMultiProgram

def outputStore (w : List Bool) : TapeStore :=
  TapeDecodeBlocks.outputStore (TapeParse.outputStore w) w

@[simp] theorem outputStore_block (w : List Bool) (kind : InputBlockKind) :
    outputStore w (TapeInputBlocks.outputRegister kind) = inputBlockData w kind :=
  TapeDecodeBlocks.outputStore_block _ _ _

theorem outputStore_other (w : List Bool) (q : TapeRegister)
    (h15 : q ≠ 15) (h16 : q ≠ 16) (h17 : q ≠ 17) (h18 : q ≠ 18) :
    outputStore w q = TapeParse.outputStore w q :=
  TapeDecodeBlocks.outputStore_other _ _ _ h15 h16 h17 h18

@[simp] theorem outputStore_data (w : List Bool) :
    outputStore w 2 = List.replicate (dataDimension w.length) true := by
  rw [outputStore_other w 2 (by decide) (by decide) (by decide) (by decide)]
  exact TapeParse.outputStore_data w

@[simp] theorem outputStore_hash (w : List Bool) :
    outputStore w 3 = List.replicate (hashDimension (dataDimension w.length)) true := by
  rw [outputStore_other w 3 (by decide) (by decide) (by decide) (by decide)]
  exact TapeParse.outputStore_hash w

@[simp] theorem outputStore_order (w : List Bool) :
    outputStore w 4 = List.replicate (independenceOrder (dataDimension w.length)) true := by
  rw [outputStore_other w 4 (by decide) (by decide) (by decide) (by decide)]
  exact TapeParse.outputStore_order w

theorem outputStore_empty (w : List Bool) (q : TapeRegister)
    (h0 : q ≠ 0) (h1 : q ≠ 1) (h2 : q ≠ 2) (h3 : q ≠ 3)
    (h4 : q ≠ 4) (h8 : q ≠ 8) (h15 : q ≠ 15) (h16 : q ≠ 16)
    (h17 : q ≠ 17) (h18 : q ≠ 18) : outputStore w q = [] := by
  rw [outputStore_other w q h15 h16 h17 h18]
  exact TapeParse.outputStore_empty w q h0 h1 h2 h3 h4 h8

theorem runs_decode (w : List Bool) (hfit : InputFits w) :
    RunsIn TapeDecodeBlocks.program.step
      (cfg TapeDecodeBlocks.start (storeTapes (TapeParse.outputStore w)))
      (cfg TapeDecodeBlocks.done (storeTapes (outputStore w)))
      (804 * (w.length + 1) ^ 2) := by
  apply TapeDecodeBlocks.runs_decode _ w hfit
  · exact TapeParse.outputStore_input w
  · exact TapeParse.outputStore_data w
  · exact TapeParse.outputStore_hash w
  · exact TapeParse.outputStore_order w
  all_goals apply TapeParse.outputStore_empty <;> decide

end TapeDecodeParsed
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHashInitialize

open TapeMultiProgram TapeRouting TapeRegister

abbrev State := TapeCopy.State ⊕ TapeFill.FillState

def program : TapeMultiProgram State :=
  joinCode (TapeCopy.code ringDegree scratchA) (TapeFill.fillProgram scratchA hashBits false)
    (fun _ => TapeFill.fillStart)

def start : State := .inl TapeCopy.State.start
def done : State := .inr TapeFill.fillDone

theorem runs_initialize (σ : TapeStore) (r : ℕ)
    (hr : σ ringDegree = List.replicate r true)
    (hs : σ scratchA = []) (hh : σ hashBits = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ hashBits (List.replicate r false))))
      (10 * r + 8) := by
  let τ := Function.update σ scratchA (σ ringDegree)
  have hcopy := TapeStoreRuns.copy (by decide : ringDegree ≠ scratchA) σ hs
  have hfill := TapeStoreRuns.fill (by decide : scratchA ≠ hashBits) false τ r
    (by simp [τ, hr])
  have hall := join_runs (TapeCopy.code ringDegree scratchA)
    (TapeFill.fillProgram scratchA hashBits false) (fun _ => TapeFill.fillStart)
    hcopy rfl hfill
  have hstore : Function.update (Function.update τ scratchA []) hashBits
      (List.replicate r false ++ τ hashBits) =
        Function.update σ hashBits (List.replicate r false) := by
    have hreset : Function.update τ scratchA [] = σ := by
      simp only [τ, Function.update_idem, ← hs, Function.update_eq_self]
    rw [hreset]
    simp [τ, hh, hashBits, scratchA]
  have htime : 2 * r + 4 + 1 + (8 * r + 3) = 10 * r + 8 := by omega
  simpa only [program, start, done, hstore, hr, List.length_replicate, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashInitialize
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound
namespace BinaryAlgebra

abbrev F2 := ZMod 2

def boolEquivF2 : Bool ≃ F2 := finTwoEquiv.symm

def bitValue (b : Bool) : F2 := boolEquivF2 b

def fieldBit (a : F2) : Bool := boolEquivF2.symm a

@[simp] theorem bitValue_false : bitValue false = 0 := rfl

@[simp] theorem bitValue_true : bitValue true = 1 := rfl

@[simp] theorem fieldBit_zero : fieldBit 0 = false := rfl

@[simp] theorem fieldBit_one : fieldBit 1 = true := rfl

@[simp] theorem fieldBit_bitValue (b : Bool) : fieldBit (bitValue b) = b :=
  boolEquivF2.symm_apply_apply b

@[simp] theorem bitValue_fieldBit (a : F2) : bitValue (fieldBit a) = a :=
  boolEquivF2.apply_symm_apply a

theorem bitValue_injective : Function.Injective bitValue :=
  boolEquivF2.injective

theorem bitValue_surjective : Function.Surjective bitValue :=
  boolEquivF2.surjective

theorem bitValue_xor (a b : Bool) :
    bitValue (Bool.xor a b) = bitValue a + bitValue b := by
  cases a <;> cases b <;> decide

theorem bitValue_and (a b : Bool) :
    bitValue (a && b) = bitValue a * bitValue b := by
  cases a <;> cases b <;> decide

theorem bitValue_not (a : Bool) : bitValue (!a) = 1 + bitValue a := by
  cases a <;> decide

@[simp] theorem bitValue_eq_zero_iff (b : Bool) : bitValue b = 0 ↔ b = false := by
  cases b <;> decide

@[simp] theorem bitValue_eq_one_iff (b : Bool) : bitValue b = 1 ↔ b = true := by
  cases b <;> decide

theorem eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  obtain ⟨b, rfl⟩ := boolEquivF2.surjective a
  cases b <;> decide

@[simp] theorem fieldBit_eq_false_iff (a : F2) : fieldBit a = false ↔ a = 0 := by
  obtain ⟨b, rfl⟩ := boolEquivF2.surjective a
  cases b <;> decide

@[simp] theorem fieldBit_eq_true_iff (a : F2) : fieldBit a = true ↔ a = 1 := by
  obtain ⟨b, rfl⟩ := boolEquivF2.surjective a
  cases b <;> decide

def bitsEquivF2 (V : Type uDepth1) : (V → Bool) ≃ (V → F2) where
  toFun x i := bitValue (x i)
  invFun x i := fieldBit (x i)
  left_inv x := funext fun i => fieldBit_bitValue (x i)
  right_inv x := funext fun i => bitValue_fieldBit (x i)

@[simp] theorem bitsEquivF2_apply (V : Type uDepth2) (x : V → Bool) (i : V) :
    bitsEquivF2 V x i = bitValue (x i) := rfl

@[simp] theorem bitsEquivF2_symm_apply (V : Type uDepth3) (x : V → F2) (i : V) :
    (bitsEquivF2 V).symm x i = fieldBit (x i) := rfl

end BinaryAlgebra
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators
open Polynomial

namespace DepthThreeLowerBound.BinaryAlgebra

def pack {r : ℕ} (v : Fin r → ZMod 2) : Polynomial (ZMod 2) :=
  ∑ i : Fin r, Polynomial.monomial i.val (v i)

theorem degree_pack_lt {r : ℕ} (v : Fin r → ZMod 2) :
    (pack v).degree < (r : WithBot ℕ) := by
  simpa only [pack, Polynomial.C_mul_X_pow_eq_monomial] using
    (Polynomial.degree_sum_fin_lt v)

@[simp] theorem coeff_pack {r : ℕ} (v : Fin r → ZMod 2) (i : Fin r) :
    (pack v).coeff i.val = v i := by
  classical
  simp only [pack, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Fin.val_eq_val, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ i)]

theorem coeff_pack_of_le {r : ℕ} (v : Fin r → ZMod 2) {j : ℕ} (hj : r ≤ j) :
    (pack v).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_degree_lt
    ((degree_pack_lt v).trans_le (WithBot.coe_le_coe.mpr hj))

theorem coeff_pack_nat {r : ℕ} (v : Fin r → ZMod 2) (j : ℕ) :
    (pack v).coeff j = if h : j < r then v ⟨j, h⟩ else 0 := by
  by_cases hj : j < r
  · rw [dite_eq_left hj]
    exact coeff_pack v ⟨j, hj⟩
  · rw [dite_eq_right hj]
    exact coeff_pack_of_le v (Nat.le_of_not_lt hj)

theorem pack_injective {r : ℕ} :
    Function.Injective (pack : (Fin r → ZMod 2) → Polynomial (ZMod 2)) := by
  intro v w h
  funext i
  simpa only [coeff_pack] using congrArg (fun f : Polynomial (ZMod 2) => f.coeff i.val) h

@[simp] theorem pack_zero {r : ℕ} : pack (0 : Fin r → ZMod 2) = 0 := by
  simp [pack]

@[simp] theorem pack_add {r : ℕ} (v w : Fin r → ZMod 2) :
    pack (v + w) = pack v + pack w := by
  simp only [pack, Pi.add_apply, map_add, Finset.sum_add_distrib]

@[simp] theorem pack_smul {r : ℕ} (c : ZMod 2) (v : Fin r → ZMod 2) :
    pack (c • v) = c • pack v := by
  simp only [pack, Pi.smul_apply, map_smul, Finset.smul_sum]

theorem pack_coeff_of_degree_lt {r : ℕ} (f : Polynomial (ZMod 2))
    (hf : f.degree < (r : WithBot ℕ)) :
    pack (fun i : Fin r => f.coeff i.val) = f := by
  unfold pack
  calc
    (∑ i : Fin r, Polynomial.monomial i.val (f.coeff i.val)) =
        f.sum (fun i c => Polynomial.monomial i c) :=
      Polynomial.sum_fin (fun i c => Polynomial.monomial i c)
        (fun i => Polynomial.monomial_zero_right i) hf
    _ = f := Polynomial.sum_monomial_eq f

def inputPolynomial {r : ℕ} (v : Fin r → ZMod 2) : Polynomial (ZMod 2) :=
  Polynomial.X ^ r + pack v

theorem inputPolynomial_monic {r : ℕ} (v : Fin r → ZMod 2) :
    (inputPolynomial v).Monic :=
  Polynomial.monic_X_pow_add (degree_pack_lt v)

@[simp] theorem inputPolynomial_degree {r : ℕ} (v : Fin r → ZMod 2) :
    (inputPolynomial v).degree = (r : WithBot ℕ) := by
  have h : (pack v).degree < (Polynomial.X ^ r : Polynomial (ZMod 2)).degree := by
    simpa only [Polynomial.degree_X_pow] using degree_pack_lt v
  simpa only [inputPolynomial, Polynomial.degree_X_pow] using
    Polynomial.degree_add_eq_left_of_degree_lt h

@[simp] theorem inputPolynomial_natDegree {r : ℕ} (v : Fin r → ZMod 2) :
    (inputPolynomial v).natDegree = r := by
  have h : (pack v).degree < (Polynomial.X ^ r : Polynomial (ZMod 2)).degree := by
    simpa only [Polynomial.degree_X_pow] using degree_pack_lt v
  simpa only [inputPolynomial, Polynomial.natDegree_X_pow] using
    Polynomial.natDegree_add_eq_left_of_degree_lt h

theorem inputPolynomial_ne_zero {r : ℕ} (v : Fin r → ZMod 2) :
    inputPolynomial v ≠ 0 :=
  (inputPolynomial_monic v).ne_zero

@[simp] theorem inputPolynomial_coeff_lt {r : ℕ} (v : Fin r → ZMod 2) (i : Fin r) :
    (inputPolynomial v).coeff i.val = v i := by
  rw [inputPolynomial, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    ite_eq_right (Nat.ne_of_lt i.is_lt), zero_add, coeff_pack]

@[simp] theorem inputPolynomial_coeff_leading {r : ℕ} (v : Fin r → ZMod 2) :
    (inputPolynomial v).coeff r = 1 := by
  rw [inputPolynomial, Polynomial.coeff_add, Polynomial.coeff_X_pow_self,
    coeff_pack_of_le v (Nat.le_refl r), add_zero]

theorem inputPolynomial_coeff_of_gt {r : ℕ} (v : Fin r → ZMod 2)
    {j : ℕ} (hj : r < j) : (inputPolynomial v).coeff j = 0 := by
  apply Polynomial.coeff_eq_zero_of_degree_lt
  rw [inputPolynomial_degree]
  exact WithBot.coe_lt_coe.mpr hj

def inputPolynomialBits {r : ℕ} (p : Fin r → Bool) : Polynomial (ZMod 2) :=
  inputPolynomial (fun i => bitValue (p i))

theorem inputPolynomialBits_monic {r : ℕ} (p : Fin r → Bool) :
    (inputPolynomialBits p).Monic :=
  inputPolynomial_monic _

@[simp] theorem inputPolynomialBits_degree {r : ℕ} (p : Fin r → Bool) :
    (inputPolynomialBits p).degree = (r : WithBot ℕ) :=
  inputPolynomial_degree _

@[simp] theorem inputPolynomialBits_natDegree {r : ℕ} (p : Fin r → Bool) :
    (inputPolynomialBits p).natDegree = r :=
  inputPolynomial_natDegree _

@[simp] theorem inputPolynomialBits_coeff_lt {r : ℕ} (p : Fin r → Bool) (i : Fin r) :
    (inputPolynomialBits p).coeff i.val = bitValue (p i) :=
  inputPolynomial_coeff_lt _ _

@[simp] theorem inputPolynomialBits_coeff_leading {r : ℕ} (p : Fin r → Bool) :
    (inputPolynomialBits p).coeff r = 1 :=
  inputPolynomial_coeff_leading _

end DepthThreeLowerBound.BinaryAlgebra

end

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

open BinaryAlgebra

abbrev BitWord (n : ℕ) := Fin n → Bool

noncomputable def wordPoly {n : ℕ} (a : BitWord n) : Polynomial (ZMod 2) :=
  BinaryAlgebra.pack (fun i => BinaryAlgebra.bitValue (a i))

def wordXor {n : ℕ} (a b : BitWord n) : BitWord n :=
  fun i => Bool.xor (a i) (b i)

def wordGet {n : ℕ} (a : BitWord n) (i : ℕ) : Bool :=
  if h : i < n then a ⟨i, h⟩ else false

def shiftModulus {r m : ℕ} (p : BitWord r) (s : ℕ) : BitWord m :=
  fun i => if i.val = s + r then true
    else if h : s ≤ i.val ∧ i.val < s + r then
      p ⟨i.val - s, by omega⟩
    else false

@[simp] theorem wordGet_fin {n : ℕ} (a : BitWord n) (i : Fin n) :
    wordGet a i.val = a i := by
  simp [wordGet, i.is_lt]

theorem wordGet_of_lt {n : ℕ} (a : BitWord n) {i : ℕ} (hi : i < n) :
    wordGet a i = a ⟨i, hi⟩ := by
  simp [wordGet, hi]

theorem wordGet_of_le {n : ℕ} (a : BitWord n) {i : ℕ} (hi : n ≤ i) :
    wordGet a i = false := by
  simp [wordGet, Nat.not_lt.mpr hi]

@[simp] theorem wordGet_wordXor {n : ℕ} (a b : BitWord n) (i : ℕ) :
    wordGet (wordXor a b) i = Bool.xor (wordGet a i) (wordGet b i) := by
  by_cases hi : i < n <;> simp [wordGet, wordXor, hi]

theorem coeff_wordPoly {n : ℕ} (a : BitWord n) (i : ℕ) :
    (wordPoly a).coeff i = BinaryAlgebra.bitValue (wordGet a i) := by
  rw [wordPoly, BinaryAlgebra.coeff_pack_nat]
  by_cases hi : i < n <;> simp [wordGet, hi]

@[simp] theorem coeff_wordPoly_fin {n : ℕ} (a : BitWord n) (i : Fin n) :
    (wordPoly a).coeff i.val = BinaryAlgebra.bitValue (a i) := by
  rw [coeff_wordPoly, wordGet_fin]

theorem wordPoly_injective {n : ℕ} :
    Function.Injective (wordPoly : BitWord n → Polynomial (ZMod 2)) := by
  intro a b h
  funext i
  apply BinaryAlgebra.bitValue_injective
  simpa only [coeff_wordPoly_fin] using
    congrArg (fun f : Polynomial (ZMod 2) => f.coeff i.val) h

@[simp] theorem wordPoly_zero (n : ℕ) :
    wordPoly (fun _ : Fin n => false) = 0 := by
  change BinaryAlgebra.pack (0 : Fin n → ZMod 2) = 0
  exact BinaryAlgebra.pack_zero

theorem wordPoly_xor {n : ℕ} (a b : BitWord n) :
    wordPoly (wordXor a b) = wordPoly a + wordPoly b := by
  unfold wordPoly wordXor
  simp only [BinaryAlgebra.bitValue_xor]
  exact BinaryAlgebra.pack_add
    (fun i => BinaryAlgebra.bitValue (a i))
    (fun i => BinaryAlgebra.bitValue (b i))

theorem degree_wordPoly_lt {n : ℕ} (a : BitWord n) :
    (wordPoly a).degree < (n : WithBot ℕ) :=
  BinaryAlgebra.degree_pack_lt _

theorem degree_wordPoly_lt_of_zero_tail {n r : ℕ} (a : BitWord n)
    (h : ∀ i : ℕ, r ≤ i → wordGet a i = false) :
    (wordPoly a).degree < (r : WithBot ℕ) := by
  apply (Polynomial.degree_lt_iff_coeff_zero (wordPoly a) r).2
  intro i hi
  rw [coeff_wordPoly, h i hi, BinaryAlgebra.bitValue_false]

theorem degree_wordPoly_lt_of_tail_false {n r : ℕ} (a : BitWord n)
    (h : ∀ i : Fin n, r ≤ i.val → a i = false) :
    (wordPoly a).degree < (r : WithBot ℕ) := by
  apply degree_wordPoly_lt_of_zero_tail
  intro i hi
  by_cases hin : i < n
  · rw [wordGet_of_lt a hin]
    exact h ⟨i, hin⟩ hi
  · exact wordGet_of_le a (Nat.le_of_not_lt hin)

theorem inputPolynomialBits_eq_wordPoly {r : ℕ} (p : BitWord r) :
    BinaryAlgebra.inputPolynomialBits p = Polynomial.X ^ r + wordPoly p := rfl

@[simp] theorem shiftModulus_top {r m : ℕ} (p : BitWord r) (s : ℕ)
    (h : s + r < m) :
    shiftModulus (m := m) p s ⟨s + r, h⟩ = true := by
  simp [shiftModulus]

theorem shiftModulus_above {r m : ℕ} (p : BitWord r) (s : ℕ)
    (i : Fin m) (h : s + r < i.val) :
    shiftModulus p s i = false := by
  have he : i.val ≠ s + r := by omega
  have hn : ¬ (s ≤ i.val ∧ i.val < s + r) := by omega
  simp [shiftModulus, he, hn]

theorem wordPoly_shiftModulus {r m : ℕ} (p : BitWord r) (s : ℕ)
    (hm : s + r < m) :
    wordPoly (shiftModulus (m := m) p s) =
      Polynomial.X ^ s * BinaryAlgebra.inputPolynomialBits p := by
  ext i
  rw [coeff_wordPoly, Polynomial.coeff_X_pow_mul']
  by_cases hs : s ≤ i
  · rw [ite_eq_left hs]
    by_cases he : i = s + r
    · subst i
      have hsub : s + r - s = r := by omega
      rw [hsub, BinaryAlgebra.inputPolynomialBits_coeff_leading]
      simp [wordGet, shiftModulus, hm]
    · by_cases hl : i < s + r
      · have hi : i < m := hl.trans hm
        have hsub : i - s < r := by omega
        have hc := BinaryAlgebra.inputPolynomialBits_coeff_lt p ⟨i - s, hsub⟩
        change (BinaryAlgebra.inputPolynomialBits p).coeff (i - s) = _ at hc
        rw [hc]
        simp [wordGet, shiftModulus, hi, he, hs, hl]
      · have hsub : r < i - s := by omega
        have hz : (BinaryAlgebra.inputPolynomialBits p).coeff (i - s) = 0 :=
          BinaryAlgebra.inputPolynomial_coeff_of_gt _ hsub
        rw [hz]
        by_cases hi : i < m
        · simp [wordGet, shiftModulus, hi, he, hl]
        · simp [wordGet, hi]
  · rw [ite_eq_right hs]
    have he : i ≠ s + r := by omega
    by_cases hi : i < m
    · simp [wordGet, shiftModulus, hi, he, hs]
    · simp [wordGet, hi]

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

open scoped BigOperators

def xorBits (xs : List Bool) : Bool := xs.foldr Bool.xor false

@[simp] theorem xorBits_nil : xorBits [] = false := rfl

@[simp] theorem xorBits_cons (x : Bool) (xs : List Bool) :
    xorBits (x :: xs) = Bool.xor x (xorBits xs) := rfl

theorem bitValue_xorBits (xs : List Bool) :
    BinaryAlgebra.bitValue (xorBits xs) = (xs.map BinaryAlgebra.bitValue).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change BinaryAlgebra.bitValue (Bool.xor x (xorBits xs)) =
        BinaryAlgebra.bitValue x + (xs.map BinaryAlgebra.bitValue).sum
      rw [BinaryAlgebra.bitValue_xor, ih]

theorem bitValue_xorBits_ofFn {n : ℕ} (f : Fin n → Bool) :
    BinaryAlgebra.bitValue (xorBits (List.ofFn f)) =
      ∑ i : Fin n, BinaryAlgebra.bitValue (f i) := by
  simp only [bitValue_xorBits, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

def wordConvolve {r s : ℕ} (a : BitWord r) (b : BitWord s) : BitWord (r + s) :=
  fun k => xorBits (List.ofFn fun i : Fin r =>
    xorBits (List.ofFn fun j : Fin s =>
      if i.val + j.val = k.val then a i && b j else false))

theorem coeff_wordPoly_mul {r s : ℕ} (a : BitWord r) (b : BitWord s) (k : ℕ) :
    (wordPoly a * wordPoly b).coeff k =
      ∑ i : Fin r, ∑ j : Fin s,
        if i.val + j.val = k then
          BinaryAlgebra.bitValue (a i) * BinaryAlgebra.bitValue (b j)
        else 0 := by
  classical
  simp only [wordPoly, BinaryAlgebra.pack, Finset.sum_mul_sum,
    Polynomial.monomial_mul_monomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]

theorem wordPoly_convolve {r s : ℕ} (a : BitWord r) (b : BitWord s) :
    wordPoly (wordConvolve a b) = wordPoly a * wordPoly b := by
  ext k
  rw [coeff_wordPoly, coeff_wordPoly_mul]
  by_cases hk : k < r + s
  · rw [wordGet_of_lt _ hk]
    simp only [wordConvolve, bitValue_xorBits_ofFn, apply_ite,
      BinaryAlgebra.bitValue_and, BinaryAlgebra.bitValue_false]
  · rw [wordGet_of_le _ (Nat.le_of_not_lt hk), BinaryAlgebra.bitValue_false]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hsum : i.val + j.val < r + s := Nat.add_lt_add i.is_lt j.is_lt
    have hne : i.val + j.val ≠ k := by omega
    simp [hne]

def wordList {n : ℕ} (a : BitWord n) : List Bool := List.ofFn a

def listWord (n : ℕ) (xs : List Bool) : BitWord n :=
  fun i => xs.getD i.val false

@[simp] theorem wordList_length {n : ℕ} (a : BitWord n) :
    (wordList a).length = n := List.length_ofFn

theorem wordList_getD {n : ℕ} (a : BitWord n) (i : ℕ) :
    (wordList a).getD i false = wordGet a i := by
  by_cases hi : i < n <;> simp [wordList, wordGet, hi]

@[simp] theorem listWord_wordList {n : ℕ} (a : BitWord n) :
    listWord n (wordList a) = a := by
  funext i
  change (wordList a).getD i.val false = a i
  rw [wordList_getD, wordGet_fin]

theorem wordList_listWord_length (xs : List Bool) :
    wordList (listWord xs.length xs) = xs := by
  apply List.ext_getElem
  · simp [wordList]
  · intro i _ hi
    simp [wordList, listWord, List.getElem?_eq_getElem hi]

theorem wordList_listWord {n : ℕ} (xs : List Bool) (h : xs.length = n) :
    wordList (listWord n xs) = xs := by
  subst n
  exact wordList_listWord_length xs

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

open BinaryAlgebra
open Polynomial

def wordFreeze {n : ℕ} (a : BitWord n) : BitWord n :=
  listWord n (wordList a)

@[simp] theorem wordFreeze_eq {n : ℕ} (a : BitWord n) : wordFreeze a = a :=
  listWord_wordList a

def cancelStep {r m : ℕ} (p : BitWord r) (k : ℕ) (a : BitWord m) : BitWord m :=
  if h : r ≤ k ∧ k < m then
    if a ⟨k, h.2⟩ = true then
      wordFreeze (wordXor a (shiftModulus p (k - r)))
    else a
  else a

theorem cancelStep_above {r m : ℕ} (p : BitWord r) (k : ℕ)
    (a : BitWord m) (i : Fin m) (hi : k < i.val) :
    cancelStep p k a i = a i := by
  by_cases hk : r ≤ k ∧ k < m
  · by_cases ha : a ⟨k, hk.2⟩ = true
    · have hs : k - r + r < i.val := by omega
      simp [cancelStep, hk, ha, wordXor, shiftModulus_above p (k - r) i hs]
    · simp [cancelStep, hk, ha]
  · simp [cancelStep, hk]

theorem cancelStep_at {r m : ℕ} (p : BitWord r) (a : BitWord m)
    (i : Fin m) (hi : r ≤ i.val) : cancelStep p i.val a i = false := by
  have hk : r ≤ i.val ∧ i.val < m := ⟨hi, i.is_lt⟩
  have hs : i.val - r + r = i.val := by omega
  by_cases ha : a i = true
  · simp [cancelStep, hk, ha, wordXor, shiftModulus, hs]
  · have hf : a i = false := Bool.eq_false_of_not_eq_true ha
    simp [cancelStep, hk, ha]

theorem wordPoly_cancelStep_mod {r m : ℕ} (p : BitWord r)
    (k : ℕ) (a : BitWord m) :
    wordPoly (cancelStep p k a) %ₘ inputPolynomialBits p =
      wordPoly a %ₘ inputPolynomialBits p := by
  by_cases hk : r ≤ k ∧ k < m
  · by_cases ha : a ⟨k, hk.2⟩ = true
    · have hs : k - r + r < m := by omega
      simp only [cancelStep, dite_eq_left hk, ite_eq_left ha, wordFreeze_eq,
        wordPoly_xor, wordPoly_shiftModulus p (k - r) hs,
        Polynomial.add_modByMonic,
        Polynomial.mul_self_modByMonic (inputPolynomialBits_monic p), add_zero]
    · simp [cancelStep, hk, ha]
  · simp [cancelStep, hk]

def reduceLoop {r m : ℕ} (p : BitWord r) : ℕ → BitWord m → BitWord m
  | 0, a => a
  | k + 1, a => reduceLoop p k (cancelStep p k a)

theorem wordPoly_reduceLoop_mod {r m : ℕ} (p : BitWord r)
    (k : ℕ) (a : BitWord m) :
    wordPoly (reduceLoop p k a) %ₘ inputPolynomialBits p =
      wordPoly a %ₘ inputPolynomialBits p := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    exact (ih (cancelStep p k a)).trans (wordPoly_cancelStep_mod p k a)

theorem reduceLoop_tail_false {r m : ℕ} (p : BitWord r) (k : ℕ)
    (a : BitWord m)
    (ha : ∀ i : Fin m, r ≤ i.val → k ≤ i.val → a i = false) :
    ∀ i : Fin m, r ≤ i.val → reduceLoop p k a i = false := by
  induction k generalizing a with
  | zero =>
    intro i hi
    exact ha i hi (Nat.zero_le _)
  | succ k ih =>
    apply ih (cancelStep p k a)
    intro i hri hki
    by_cases hlt : k < i.val
    · rw [cancelStep_above p k a i hlt]
      exact ha i hri (by omega)
    · have he : k = i.val := by omega
      subst k
      exact cancelStep_at p a i hri

def wordResize {m : ℕ} (r : ℕ) (a : BitWord m) : BitWord r :=
  fun i => wordGet a i.val

theorem wordPoly_resize_of_tail_false {r m : ℕ} (a : BitWord m)
    (ha : ∀ i : Fin m, r ≤ i.val → a i = false) :
    wordPoly (wordResize r a) = wordPoly a := by
  ext i
  rw [coeff_wordPoly, coeff_wordPoly]
  apply congrArg bitValue
  by_cases hi : i < r
  · simp [wordGet, wordResize, hi]
  · rw [wordGet_of_le _ (Nat.le_of_not_lt hi)]
    by_cases hm : i < m
    · rw [wordGet_of_lt a hm, ha ⟨i, hm⟩ (Nat.le_of_not_lt hi)]
    · rw [wordGet_of_le a (Nat.le_of_not_lt hm)]

def wordReduce {r m : ℕ} (p : BitWord r) (a : BitWord m) : BitWord r :=
  wordFreeze (wordResize r (reduceLoop p m a))

theorem wordPoly_reduce {r m : ℕ} (p : BitWord r) (a : BitWord m) :
    wordPoly (wordReduce p a) = wordPoly a %ₘ inputPolynomialBits p := by
  have ht : ∀ i : Fin m, r ≤ i.val → reduceLoop p m a i = false :=
    reduceLoop_tail_false p m a (by
      intro i _ hi
      exact False.elim (Nat.not_le.mpr i.is_lt hi))
  have hd : (wordPoly (reduceLoop p m a)).degree <
      (inputPolynomialBits p).degree := by
    rw [inputPolynomialBits_degree]
    exact degree_wordPoly_lt_of_tail_false _ ht
  have hs := (Polynomial.modByMonic_eq_self_iff
    (inputPolynomialBits_monic p)).2 hd
  calc
    wordPoly (wordReduce p a) = wordPoly (reduceLoop p m a) := by
      simp only [wordReduce, wordFreeze_eq]
      exact wordPoly_resize_of_tail_false _ ht
    _ = wordPoly (reduceLoop p m a) %ₘ inputPolynomialBits p := hs.symm
    _ = wordPoly a %ₘ inputPolynomialBits p := wordPoly_reduceLoop_mod p m a

def wordMulMod {r : ℕ} (p a b : BitWord r) : BitWord r :=
  wordReduce p (wordConvolve a b)

theorem wordPoly_mulMod {r : ℕ} (p a b : BitWord r) :
    wordPoly (wordMulMod p a b) =
      (wordPoly a * wordPoly b) %ₘ inputPolynomialBits p := by
  rw [wordMulMod, wordPoly_reduce, wordPoly_convolve]

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound.BinaryHash

open scoped BigOperators

abbrev F2 := BinaryAlgebra.F2
abbrev Data (d : ℕ) := Fin d → F2
abbrev Seed (d r : ℕ) := Fin (d + r - 1) → F2
abbrev Output (r : ℕ) := Fin r → F2

def sumIndex {d r : ℕ} (i : Fin r) (s : Fin d) : Fin (d + r - 1) :=
  ⟨i.val + s.val, by have := i.isLt; have := s.isLt; omega⟩

@[simp] theorem sumIndex_val {d r : ℕ} (i : Fin r) (s : Fin d) :
    (sumIndex i s).val = i.val + s.val := rfl

theorem sumIndex_left_injective {d r : ℕ} (s : Fin d) :
    Function.Injective (fun i : Fin r => sumIndex i s) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simpa only [sumIndex_val, Nat.add_right_cancel_iff] using hval

def hashF2 {d r : ℕ} (u : Seed d r) (x : Data d) : Output r :=
  fun i => ∑ s : Fin d, u (sumIndex i s) * x s

@[simp] theorem hashF2_apply {d r : ℕ} (u : Seed d r) (x : Data d) (i : Fin r) :
    hashF2 u x i = ∑ s : Fin d, u (sumIndex i s) * x s := rfl

@[simp] theorem hashF2_zero_data {d r : ℕ} (u : Seed d r) :
    hashF2 u 0 = 0 := by
  funext i
  simp [hashF2]

@[simp] theorem hashF2_zero_seed {d r : ℕ} (x : Data d) :
    hashF2 (0 : Seed d r) x = 0 := by
  funext i
  simp [hashF2]

theorem hashF2_add_data {d r : ℕ} (u : Seed d r) (x y : Data d) :
    hashF2 u (x + y) = hashF2 u x + hashF2 u y := by
  funext i
  simp [hashF2, mul_add, Finset.sum_add_distrib]

theorem hashF2_sub_data {d r : ℕ} (u : Seed d r) (x y : Data d) :
    hashF2 u (x - y) = hashF2 u x - hashF2 u y := by
  funext i
  simp [hashF2, mul_sub, Finset.sum_sub_distrib]

theorem hashF2_add_seed {d r : ℕ} (u v : Seed d r) (x : Data d) :
    hashF2 (u + v) x = hashF2 u x + hashF2 v x := by
  funext i
  simp [hashF2, add_mul, Finset.sum_add_distrib]

theorem hashF2_sub_seed {d r : ℕ} (u v : Seed d r) (x : Data d) :
    hashF2 (u - v) x = hashF2 u x - hashF2 v x := by
  funext i
  simp [hashF2, sub_mul, Finset.sum_sub_distrib]

def hashBool {d r : ℕ} (u : Fin (d + r - 1) → Bool) (x : Fin d → Bool) :
    Fin r → Bool :=
  fun i => BinaryAlgebra.fieldBit
    (hashF2 (fun j => BinaryAlgebra.bitValue (u j))
      (fun s => BinaryAlgebra.bitValue (x s)) i)

@[simp] theorem bitValue_hashBool {d r : ℕ}
    (u : Fin (d + r - 1) → Bool) (x : Fin d → Bool) (i : Fin r) :
    BinaryAlgebra.bitValue (hashBool u x i) =
      hashF2 (fun j => BinaryAlgebra.bitValue (u j))
        (fun s => BinaryAlgebra.bitValue (x s)) i := by
  simp [hashBool]

theorem bitsEquivF2_hashBool {d r : ℕ}
    (u : Fin (d + r - 1) → Bool) (x : Fin d → Bool) :
    BinaryAlgebra.bitsEquivF2 (Fin r) (hashBool u x) =
      hashF2 (BinaryAlgebra.bitsEquivF2 (Fin (d + r - 1)) u)
        (BinaryAlgebra.bitsEquivF2 (Fin d) x) := by
  funext i
  exact bitValue_hashBool u x i

end DepthThreeLowerBound.BinaryHash

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

noncomputable section

open scoped BigOperators

namespace ParsedInput

def hashPolynomial (q : ParsedInput) : Polynomial (ZMod 2) :=
  BinaryAlgebra.pack fun i =>
    BinaryAlgebra.bitValue (BinaryHash.hashBool q.hashSeed q.data i)

def coefficientPolynomial (q : ParsedInput) (j : Fin q.coefficientCount) :
    Polynomial (ZMod 2) :=
  BinaryAlgebra.pack fun i => BinaryAlgebra.bitValue (q.coefficients j i)

def modulus (q : ParsedInput) : Polynomial (ZMod 2) :=
  BinaryAlgebra.inputPolynomialBits q.polynomial

theorem modulus_monic (q : ParsedInput) : q.modulus.Monic :=
  BinaryAlgebra.inputPolynomialBits_monic q.polynomial

theorem modulus_degree (q : ParsedInput) :
    q.modulus.degree = (q.ringDegree : WithBot ℕ) :=
  BinaryAlgebra.inputPolynomialBits_degree q.polynomial

def evaluationPolynomial (q : ParsedInput) : Polynomial (ZMod 2) :=
  ∑ j : Fin q.coefficientCount,
    q.coefficientPolynomial j * q.hashPolynomial ^ j.val

def evaluationRemainder (q : ParsedInput) : Polynomial (ZMod 2) :=
  q.evaluationPolynomial %ₘ q.modulus

theorem evaluationRemainder_degree_lt (q : ParsedInput) :
    q.evaluationRemainder.degree < (q.ringDegree : WithBot ℕ) := by
  rw [evaluationRemainder, ← q.modulus_degree]
  exact Polynomial.degree_modByMonic_lt _ q.modulus_monic

def evaluate (q : ParsedInput) : Bool :=
  decide (q.evaluationRemainder.coeff 0 = 0)

theorem evaluate_eq_true_iff (q : ParsedInput) :
    q.evaluate = true ↔ q.evaluationRemainder.coeff 0 = 0 := by
  simp only [evaluate, decide_eq_true_eq]

end ParsedInput

def language (w : List Bool) : Bool :=
  match parseInput w with
  | none => false
  | some q => q.evaluate

theorem language_of_not_fits {w : List Bool} (h : ¬InputFits w) :
    language w = false := by
  simp only [language, parseInput_of_not_fits h]

theorem language_of_fits {w : List Bool} (h : InputFits w) :
    language w = (decodeInput w).evaluate := by
  simp only [language, parseInput_of_fits h]

theorem language_eq_true_iff (w : List Bool) :
    language w = true ↔
      InputFits w ∧ (decodeInput w).evaluationRemainder.coeff 0 = 0 := by
  by_cases h : InputFits w
  · rw [language_of_fits h, ParsedInput.evaluate_eq_true_iff]
    simp only [h, true_and]
  · rw [language_of_not_fits h]
    simp only [Bool.false_eq_true, h, false_and]

end

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

open scoped BigOperators
open BinaryAlgebra
open Polynomial

theorem mul_remainder_modByMonic (a b p : Polynomial (ZMod 2)) (hp : p.Monic) :
    (a * (b %ₘ p)) %ₘ p = (a * b) %ₘ p := by
  symm
  calc
    (a * b) %ₘ p = (a * (b %ₘ p + p * (b /ₘ p))) %ₘ p := by
      rw [Polynomial.modByMonic_add_div b p]
    _ = (a * (b %ₘ p)) %ₘ p := by
      rw [mul_add, Polynomial.add_modByMonic]
      have hz : (a * (p * (b /ₘ p))) %ₘ p = 0 := by
        rw [← mul_assoc, mul_comm a p, mul_assoc,
          Polynomial.self_mul_modByMonic hp]
      rw [hz, add_zero]

theorem wordPoly_mod_self {r : ℕ} (p a : BitWord r) :
    wordPoly a %ₘ inputPolynomialBits p = wordPoly a := by
  apply (Polynomial.modByMonic_eq_self_iff (inputPolynomialBits_monic p)).2
  rw [inputPolynomialBits_degree]
  exact degree_wordPoly_lt a

def wordHorner {r : ℕ} (p h : BitWord r) :
    (t : ℕ) → (Fin t → BitWord r) → BitWord r
  | 0, _ => fun _ => false
  | t + 1, b => wordFreeze (wordXor (b 0)
      (wordMulMod p h (wordHorner p h t (fun i => b i.succ))))

theorem wordPoly_horner {r : ℕ} (p h : BitWord r) (t : ℕ)
    (b : Fin t → BitWord r) :
    wordPoly (wordHorner p h t b) =
      (∑ j : Fin t, wordPoly (b j) * wordPoly h ^ j.val) %ₘ
        inputPolynomialBits p := by
  induction t with
  | zero => simp [wordHorner]
  | succ t ih =>
    have hsum :
        (∑ j : Fin (t + 1), wordPoly (b j) * wordPoly h ^ j.val) =
          wordPoly (b 0) + wordPoly h *
            ∑ j : Fin t, wordPoly (b j.succ) * wordPoly h ^ j.val := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      rw [Finset.mul_sum]
      apply congrArg (fun z : Polynomial (ZMod 2) => wordPoly (b 0) + z)
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [wordHorner, wordFreeze_eq, wordPoly_xor, wordPoly_mulMod,
      ih, mul_remainder_modByMonic _ _ _ (inputPolynomialBits_monic p),
      hsum, Polynomial.add_modByMonic, wordPoly_mod_self]

def wordHash {d r : ℕ} (u : BitWord (d + r - 1)) (x : BitWord d) : BitWord r :=
  wordFreeze fun i =>
    xorBits (List.ofFn fun s : Fin d => u (BinaryHash.sumIndex i s) && x s)

theorem wordHash_eq {d r : ℕ} (u : BitWord (d + r - 1)) (x : BitWord d) :
    wordHash u x = BinaryHash.hashBool u x := by
  funext i
  apply bitValue_injective
  simp only [wordHash, wordFreeze_eq, bitValue_xorBits_ofFn, bitValue_and,
    BinaryHash.bitValue_hashBool, BinaryHash.hashF2]

def multiplyBitLists (r : ℕ) (p a b : List Bool) : List Bool :=
  wordList (wordMulMod (listWord r p) (listWord r a) (listWord r b))

@[simp] theorem multiplyBitLists_length (r : ℕ) (p a b : List Bool) :
    (multiplyBitLists r p a b).length = r := by
  simp [multiplyBitLists]

theorem multiplyBitLists_correct (r : ℕ) (p a b : List Bool) :
    wordPoly (listWord r (multiplyBitLists r p a b)) =
      (wordPoly (listWord r a) * wordPoly (listWord r b)) %ₘ
        inputPolynomialBits (listWord r p) := by
  simp only [multiplyBitLists, listWord_wordList, wordPoly_mulMod]

def hornerBitLists (r : ℕ) (p h : List Bool) (b : List (List Bool)) : List Bool :=
  wordList (wordHorner (listWord r p) (listWord r h) b.length
    (fun j => listWord r (b.getD j.val [])))

@[simp] theorem hornerBitLists_length (r : ℕ) (p h : List Bool)
    (b : List (List Bool)) : (hornerBitLists r p h b).length = r := by
  simp [hornerBitLists]

theorem hornerBitLists_correct (r : ℕ) (p h : List Bool) (b : List (List Bool)) :
    wordPoly (listWord r (hornerBitLists r p h b)) =
      (∑ j : Fin b.length, wordPoly (listWord r (b.getD j.val [])) *
        wordPoly (listWord r h) ^ j.val) %ₘ inputPolynomialBits (listWord r p) := by
  simp only [hornerBitLists, listWord_wordList, wordPoly_horner]

namespace ParsedInput

def evaluationBits (q : ParsedInput) : BitWord q.ringDegree :=
  wordHorner q.polynomial (wordHash q.hashSeed q.data)
    q.coefficientCount q.coefficients

theorem wordPoly_evaluationBits (q : ParsedInput) :
    wordPoly q.evaluationBits = q.evaluationRemainder := by
  rw [evaluationBits, wordPoly_horner, wordHash_eq]
  rfl

def evaluateBits (q : ParsedInput) : Bool :=
  !(wordGet q.evaluationBits 0)

theorem evaluateBits_eq (q : ParsedInput) : q.evaluateBits = q.evaluate := by
  have hc : bitValue (wordGet q.evaluationBits 0) =
      q.evaluationRemainder.coeff 0 := by
    rw [← coeff_wordPoly, wordPoly_evaluationBits]
  apply Bool.eq_iff_iff.mpr
  rw [evaluate_eq_true_iff]
  unfold evaluateBits
  rw [← hc, bitValue_eq_zero_iff]
  cases wordGet q.evaluationBits 0 <;> decide

end ParsedInput

def languageBits (w : List Bool) : Bool :=
  match parseInput w with
  | none => false
  | some q => q.evaluateBits

theorem languageBits_eq_language (w : List Bool) : languageBits w = language w := by
  unfold languageBits language
  cases parseInput w with
  | none => rfl
  | some q => exact q.evaluateBits_eq

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

def xorScan : Bool → List Bool → Bool
  | acc, [] => acc
  | acc, b :: bs => xorScan (Bool.xor acc b) bs

@[simp] theorem xorScan_nil (acc : Bool) : xorScan acc [] = acc := rfl

theorem xorScan_step (acc b : Bool) (bs : List Bool) :
    xorScan acc (b :: bs) = xorScan (Bool.xor acc b) bs := rfl

theorem xorScan_eq (acc : Bool) (bs : List Bool) :
    xorScan acc bs = Bool.xor acc (xorBits bs) := by
  induction bs generalizing acc with
  | nil => simp [xorScan]
  | cons b bs ih =>
    simp only [xorScan, xorBits_cons, ih, Bool.xor_assoc]

theorem xorBits_append (a b : List Bool) :
    xorBits (a ++ b) = Bool.xor (xorBits a) (xorBits b) := by
  induction a with
  | nil => simp
  | cons x a ih =>
    simp only [List.cons_append, xorBits_cons, ih, Bool.xor_assoc]

theorem xorScan_prefix_invariant (done todo : List Bool) :
    xorScan (xorBits done) todo = xorBits (done ++ todo) := by
  rw [xorScan_eq, xorBits_append]

theorem ofFn_nat_eq_map_range {α : Type uDepth1} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

def convolutionRow (a b : List Bool) (i k : ℕ) : List Bool :=
  (List.range b.length).map fun j =>
    if i + j = k then a.getD i false && b.getD j false else false

def convolutionRows (a b : List Bool) (k : ℕ) : List Bool :=
  (List.range a.length).map fun i => xorBits (convolutionRow a b i k)

def convolutionBit (a b : List Bool) (k : ℕ) : Bool :=
  xorBits (convolutionRows a b k)

theorem convolutionRow_scan (a b : List Bool) (i k : ℕ) :
    xorScan false (convolutionRow a b i k) = xorBits (convolutionRow a b i k) := by
  simp [xorScan_eq]

theorem convolutionRows_scan (a b : List Bool) (k : ℕ) :
    xorScan false (convolutionRows a b k) = convolutionBit a b k := by
  simp [xorScan_eq, convolutionBit]

theorem convolutionBit_eq_wordConvolve (a b : List Bool) (k : ℕ)
    (hk : k < a.length + b.length) :
    convolutionBit a b k =
      wordConvolve (listWord a.length a) (listWord b.length b) ⟨k, hk⟩ := by
  unfold convolutionBit convolutionRows convolutionRow wordConvolve listWord
  simp only [← ofFn_nat_eq_map_range]

def convolveBitLists (a b : List Bool) : List Bool :=
  (List.range (a.length + b.length)).map (convolutionBit a b)

@[simp] theorem convolveBitLists_length (a b : List Bool) :
    (convolveBitLists a b).length = a.length + b.length := by
  simp [convolveBitLists]

theorem convolveBitLists_eq (a b : List Bool) :
    convolveBitLists a b =
      wordList (wordConvolve (listWord a.length a) (listWord b.length b)) := by
  unfold convolveBitLists wordList
  rw [← ofFn_nat_eq_map_range]
  apply congrArg List.ofFn
  funext i
  exact convolutionBit_eq_wordConvolve a b i.val i.is_lt

theorem hornerBitLists_nil (r : ℕ) (p h : List Bool) :
    hornerBitLists r p h [] = wordList (fun _ : Fin r => false) := rfl

theorem hornerBitLists_cons (r : ℕ) (p h b : List Bool) (bs : List (List Bool)) :
    hornerBitLists r p h (b :: bs) =
      wordList (wordXor (listWord r b)
        (wordMulMod (listWord r p) (listWord r h)
          (listWord r (hornerBitLists r p h bs)))) := by
  simp [hornerBitLists, wordHorner]

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

def xorListAt (c : List Bool) (k : ℕ) (v : Bool) : List Bool :=
  c.set k (Bool.xor (c.getD k false) v)

@[simp] theorem xorListAt_length (c : List Bool) (k : ℕ) (v : Bool) :
    (xorListAt c k v).length = c.length := by
  simp [xorListAt]

theorem xorListAt_getD (c : List Bool) (j : ℕ) (v : Bool)
    (hj : j < c.length) (k : ℕ) :
    (xorListAt c j v).getD k false =
      Bool.xor (c.getD k false) (if j = k then v else false) := by
  by_cases h : j = k
  · subst k
    simp [xorListAt, List.getElem?_set_self hj]
  · simp [xorListAt, h, List.getElem?_set_ne h]

theorem xorListAt_split («prefix» suffix : List Bool) (old v : Bool) :
    xorListAt («prefix» ++ old :: suffix) «prefix».length v =
      «prefix» ++ Bool.xor old v :: suffix := by
  unfold xorListAt
  rw [List.getD_append_right «prefix» (old :: suffix) false «prefix».length le_rfl]
  simp

def convolutionUpdateRow (a b : List Bool) (i : ℕ) :
    List ℕ → List Bool → List Bool
  | [], c => c
  | j :: js, c => convolutionUpdateRow a b i js
      (xorListAt c (i + j) (a.getD i false && b.getD j false))

@[simp] theorem convolutionUpdateRow_nil (a b : List Bool) (i : ℕ) (c : List Bool) :
    convolutionUpdateRow a b i [] c = c := rfl

theorem convolutionUpdateRow_step (a b : List Bool) (i j : ℕ)
    (js : List ℕ) (c : List Bool) :
    convolutionUpdateRow a b i (j :: js) c =
      convolutionUpdateRow a b i js
        (xorListAt c (i + j) (a.getD i false && b.getD j false)) := rfl

@[simp] theorem convolutionUpdateRow_length (a b : List Bool) (i : ℕ)
    (js : List ℕ) (c : List Bool) :
    (convolutionUpdateRow a b i js c).length = c.length := by
  induction js generalizing c with
  | nil => rfl
  | cons j js ih =>
      rw [convolutionUpdateRow_step, ih, xorListAt_length]

theorem convolutionUpdateRow_getD (a b : List Bool) (i : ℕ)
    (js : List ℕ) (c : List Bool) (k : ℕ)
    (hbound : ∀ j ∈ js, i + j < c.length) :
    (convolutionUpdateRow a b i js c).getD k false =
      Bool.xor (c.getD k false)
        (xorBits (js.map fun j =>
          if i + j = k then a.getD i false && b.getD j false else false)) := by
  induction js generalizing c with
  | nil => simp
  | cons j js ih =>
      have hj : i + j < c.length := hbound j (by simp)
      have hrest : ∀ j' ∈ js, i + j' <
          (xorListAt c (i + j) (a.getD i false && b.getD j false)).length := by
        intro j' hj'
        rw [xorListAt_length]
        exact hbound j' (List.mem_cons_of_mem j hj')
      rw [convolutionUpdateRow_step, ih _ hrest,
        xorListAt_getD c (i + j) (a.getD i false && b.getD j false) hj k]
      simp only [List.map_cons, xorBits_cons, Bool.xor_assoc]

def convolutionUpdateRows (a b : List Bool) : List ℕ → List Bool → List Bool
  | [], c => c
  | i :: is, c => convolutionUpdateRows a b is
      (convolutionUpdateRow a b i (List.range b.length) c)

@[simp] theorem convolutionUpdateRows_nil (a b : List Bool) (c : List Bool) :
    convolutionUpdateRows a b [] c = c := rfl

theorem convolutionUpdateRows_step (a b : List Bool) (i : ℕ)
    (is : List ℕ) (c : List Bool) :
    convolutionUpdateRows a b (i :: is) c =
      convolutionUpdateRows a b is
        (convolutionUpdateRow a b i (List.range b.length) c) := rfl

@[simp] theorem convolutionUpdateRows_length (a b : List Bool)
    (is : List ℕ) (c : List Bool) :
    (convolutionUpdateRows a b is c).length = c.length := by
  induction is generalizing c with
  | nil => rfl
  | cons i is ih =>
      rw [convolutionUpdateRows_step, ih, convolutionUpdateRow_length]

theorem convolutionUpdateRows_getD (a b : List Bool)
    (is : List ℕ) (c : List Bool) (k : ℕ)
    (hbound : ∀ i ∈ is, ∀ j < b.length, i + j < c.length) :
    (convolutionUpdateRows a b is c).getD k false =
      Bool.xor (c.getD k false)
        (xorBits (is.map fun i => xorBits (convolutionRow a b i k))) := by
  induction is generalizing c with
  | nil => simp
  | cons i is ih =>
      have hcols : ∀ j ∈ List.range b.length, i + j < c.length := by
        intro j hj
        exact hbound i (by simp) j (List.mem_range.mp hj)
      have hrest : ∀ i' ∈ is, ∀ j < b.length, i' + j <
          (convolutionUpdateRow a b i (List.range b.length) c).length := by
        intro i' hi' j hj
        rw [convolutionUpdateRow_length]
        exact hbound i' (List.mem_cons_of_mem i hi') j hj
      rw [convolutionUpdateRows_step, ih _ hrest,
        convolutionUpdateRow_getD a b i (List.range b.length) c k hcols]
      simp only [List.map_cons, xorBits_cons, convolutionRow, Bool.xor_assoc]

def convolveByUpdates (a b : List Bool) : List Bool :=
  convolutionUpdateRows a b (List.range a.length)
    (List.replicate (a.length + b.length) false)

@[simp] theorem convolveByUpdates_length (a b : List Bool) :
    (convolveByUpdates a b).length = a.length + b.length := by
  simp [convolveByUpdates]

theorem convolutionUpdate_index_lt (a b : List Bool) {i j : ℕ}
    (hi : i < a.length) (hj : j < b.length) :
    i + j < a.length + b.length :=
  Nat.add_lt_add hi hj

theorem convolveByUpdates_getD (a b : List Bool) (k : ℕ) :
    (convolveByUpdates a b).getD k false = convolutionBit a b k := by
  have hbound : ∀ i ∈ List.range a.length, ∀ j < b.length,
      i + j < (List.replicate (a.length + b.length) false).length := by
    intro i hi j hj
    simpa only [List.length_replicate] using
      convolutionUpdate_index_lt a b (List.mem_range.mp hi) hj
  unfold convolveByUpdates
  rw [convolutionUpdateRows_getD a b (List.range a.length)
    (List.replicate (a.length + b.length) false) k hbound]
  simp [convolutionBit, convolutionRows]

theorem convolveByUpdates_eq (a b : List Bool) :
    convolveByUpdates a b = convolveBitLists a b := by
  apply List.ext_getElem
  · simp
  · intro k hk hl
    have hk' : k < a.length + b.length := by
      simpa only [convolveBitLists_length] using hl
    have hleft := convolveByUpdates_getD a b k
    have hright : (convolveBitLists a b).getD k false = convolutionBit a b k := by
      simp [convolveBitLists, List.getElem?_range hk']
    rw [List.getD_eq_getElem _ _ hk] at hleft
    rw [List.getD_eq_getElem _ _ hl] at hright
    exact hleft.trans hright.symm

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeNaturalAccess

open TapeMultiProgram TapeUnary

theorem take_length (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (xs.take i).length = i := List.length_take_of_le hi.le

theorem split (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    xs = xs.take i ++ xs.getD i false :: xs.drop (i + 1) := by
  rw [List.getD_eq_getElem _ _ hi, ← List.drop_eq_getElem_cons hi,
    List.take_append_drop]

theorem xorListAt_eq_split (xs : List Bool) (i : ℕ) (hi : i < xs.length)
    (v : Bool) :
    xorListAt xs i v =
      xs.take i ++ Bool.xor (xs.getD i false) v :: xs.drop (i + 1) := by
  calc
    xorListAt xs i v = xorListAt
        (xs.take i ++ xs.getD i false :: xs.drop (i + 1)) (xs.take i).length v := by
      rw [take_length xs i hi, ← split xs i hi]
    _ = _ := xorListAt_split _ _ _ _

theorem read (index array : TapeRegister) (hne : index ≠ array)
    (σ : TapeStore) (i : ℕ) (hi : σ index = List.replicate i true)
    (hib : i < (σ array).length) :
    RunsIn (TapeArray.code index array id).step
      (cfg TapeArray.State.start (storeTapes σ))
      (cfg (TapeArray.State.done ((σ array).getD i false)) (storeTapes σ))
      (2 * i + 4) := by
  have h := TapeProductTerm.read_at hne (storeTapes σ)
    ((σ array).take i) ((σ array).drop (i + 1)) ((σ array).getD i false)
    (by simp only [storeTapes_apply, hi, counterTape, take_length _ _ hib])
    (congrArg wordTape (split _ _ hib))
  simpa only [take_length _ _ hib] using h

theorem xorAt (index array : TapeRegister) (hne : index ≠ array)
    (σ : TapeStore) (i : ℕ) (v : Bool) (hi : σ index = List.replicate i true)
    (hib : i < (σ array).length) :
    RunsIn (TapeArray.code index array (fun old => Bool.xor old v)).step
      (cfg TapeArray.State.start (storeTapes σ))
      (cfg (TapeArray.State.done ((σ array).getD i false))
        (storeTapes (Function.update σ array (xorListAt (σ array) i v))))
      (2 * i + 4) := by
  have h := TapeProductTerm.modify_at hne (fun old => Bool.xor old v) (storeTapes σ)
    ((σ array).take i) ((σ array).drop (i + 1)) ((σ array).getD i false)
    (by simp only [storeTapes_apply, hi, counterTape, take_length _ _ hib])
    (congrArg wordTape (split _ _ hib))
  simpa only [take_length _ _ hib, storeTapes_update, xorListAt_eq_split _ _ hib] using h

theorem productTerm (ia a ib b ic c : TapeRegister)
    (hia : ia ≠ a) (hib : ib ≠ b) (hic : ic ≠ c)
    (σ : TapeStore) (i j k : ℕ)
    (hi : σ ia = List.replicate i true)
    (hj : σ ib = List.replicate j true)
    (hk : σ ic = List.replicate k true)
    (hAi : i < (σ a).length) (hBj : j < (σ b).length) (hCk : k < (σ c).length) :
    RunsIn (TapeProductTerm.program ia a ib b ic c).step
      (cfg TapeProductTerm.start (storeTapes σ))
      (cfg (TapeProductTerm.done ((σ a).getD i false) ((σ b).getD j false)
          ((σ c).getD k false))
        (storeTapes (Function.update σ c
          (xorListAt (σ c) k ((σ a).getD i false && (σ b).getD j false)))))
      (2 * (i + j + k) + 14) := by
  have h := TapeProductTerm.runs_product_term ia a ib b ic c hia hib hic (storeTapes σ)
    ((σ a).take i) ((σ a).drop (i + 1))
    ((σ b).take j) ((σ b).drop (j + 1))
    ((σ c).take k) ((σ c).drop (k + 1))
    ((σ a).getD i false) ((σ b).getD j false) ((σ c).getD k false)
    (by simp only [storeTapes_apply, hi, counterTape, take_length _ _ hAi])
    (congrArg wordTape (split _ _ hAi))
    (by simp only [storeTapes_apply, hj, counterTape, take_length _ _ hBj])
    (congrArg wordTape (split _ _ hBj))
    (by simp only [storeTapes_apply, hk, counterTape, take_length _ _ hCk])
    (congrArg wordTape (split _ _ hCk))
  simpa only [take_length _ _ hAi, take_length _ _ hBj, take_length _ _ hCk,
    storeTapes_update, xorListAt_eq_split _ _ hCk] using h

end TapeNaturalAccess
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHashStep

open TapeMultiProgram TapeRouting TapeUnary TapeRegister

abbrev State := TapeProductTerm.State ⊕ IncState

def program : TapeMultiProgram State :=
  joinCode (TapeProductTerm.program indexA keyBits indexB dataBits indexC hashBits)
    (incProgram indexA) (fun _ => IncState.start)

def start : State := .inl TapeProductTerm.start
def done : State := .inr IncState.done

def resultStore (σ : TapeStore) (i j : ℕ) : TapeStore :=
  Function.update (Function.update σ hashBits
    (xorListAt (σ hashBits) i ((σ keyBits).getD (i + j) false && (σ dataBits).getD j false)))
    indexA (List.replicate (i + j + 1) true)

theorem runs_step (σ : TapeStore) (i j : ℕ)
    (ha : σ indexA = List.replicate (i + j) true)
    (hb : σ indexB = List.replicate j true)
    (hc : σ indexC = List.replicate i true)
    (hkey : i + j < (σ keyBits).length)
    (hdata : j < (σ dataBits).length) (hout : i < (σ hashBits).length) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (resultStore σ i j))) (4 * i + 4 * j + 17) := by
  let τ := Function.update σ hashBits
    (xorListAt (σ hashBits) i ((σ keyBits).getD (i + j) false && (σ dataBits).getD j false))
  have hterm := TapeNaturalAccess.productTerm indexA keyBits indexB dataBits indexC hashBits
    (by decide) (by decide) (by decide) σ (i + j) j i ha hb hc hkey hdata hout
  have hinc := increment indexA (storeTapes τ) (i + j) (by
    simp [τ, ha, counterTape, indexA, hashBits])
  have hinc' : RunsIn (incProgram indexA).step (cfg IncState.start (storeTapes τ))
      (cfg IncState.done (storeTapes (resultStore σ i j))) 2 := by
    simpa only [resultStore, τ, storeTapes_update, counterTape] using hinc
  have hall := join_runs
    (TapeProductTerm.program indexA keyBits indexB dataBits indexC hashBits)
    (incProgram indexA) (fun _ => IncState.start) hterm rfl hinc'
  have htime : 2 * ((i + j) + j + i) + 14 + 1 + 2 = 4 * i + 4 * j + 17 := by omega
  simpa only [program, start, done, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashStep
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound
namespace TapeForLoop

open TapeMultiProgram TapeRouting TapeUnary

abbrev BodyState (Q : Type uDepth1) := Q ⊕ IncState
abbrev State (Q : Type uDepth2) := LoopState TapeUnaryCompare.State (BodyState Q)

def bodyProgram {Q : Type uDepth3} (r : TapeRegister) (P : TapeMultiProgram Q) :
    TapeMultiProgram (BodyState Q) :=
  joinCode P (incProgram r) (fun _ => IncState.start)

def bodyStart {Q : Type uDepth4} (q : Q) : BodyState Q := .inl q

def bodyDone {Q : Type uDepth5} : BodyState Q := .inr .done

def again : TapeUnaryCompare.State → Bool
  | .done .lt => true
  | _ => false

def program {Q : Type uDepth6} (r s : TapeRegister) (P : TapeMultiProgram Q)
    (qStart : Q) : TapeMultiProgram (State Q) :=
  loopCode (TapeUnaryCompare.program r s) (bodyProgram r P)
    (.scan .beginR) (bodyStart qStart) again

def start {Q : Type uDepth7} : State Q := loopTest (.scan .beginR)

def done {Q : Type uDepth8} : State Q := loopDone

@[simp] theorem body_done {Q : Type uDepth9} (r : TapeRegister) (P : TapeMultiProgram Q)
    (h : TapeHeads) : bodyProgram r P bodyDone h = none := rfl

@[simp] theorem program_done {Q : Type uDepth10} (r s : TapeRegister)
    (P : TapeMultiProgram Q) (qStart : Q) (h : TapeHeads) :
    program r s P qStart done h = none := rfl

theorem runs_body {Q : Type uDepth11} (r : TapeRegister) (P : TapeMultiProgram Q)
    (qStart qDone : Q) (T U : TapeTapes) (j B : ℕ)
    (hU : U r = counterTape (j + 1))
    (hbody : RunsIn P.step (cfg qStart T)
      (cfg qDone (Function.update U r (counterTape j))) B)
    (hhalt : P qDone (heads (Function.update U r (counterTape j))) = none) :
    RunsIn (bodyProgram r P).step (cfg (bodyStart qStart) T)
      (cfg bodyDone U) (B + 3) := by
  have hi := increment r (Function.update U r (counterTape j)) j
    (Function.update_self _ _ _)
  have hu : Function.update (Function.update U r (counterTape j)) r
      (counterTape (j + 1)) = U := by
    rw [Function.update_idem]
    exact Function.update_eq_self_iff.mpr hU.symm
  rw [hu] at hi
  have h := join_runs P (incProgram r) (fun _ => IncState.start) hbody hhalt hi
  simpa only [bodyProgram, bodyStart, bodyDone, Nat.add_assoc] using h

theorem runs_iteration {Q : Type uDepth12} {r s : TapeRegister} (hrs : r ≠ s)
    (P : TapeMultiProgram Q) (qStart qDone : Q) (T U : TapeTapes) (j n B : ℕ)
    (hj : j < n) (hR : T r = counterTape j) (hS : T s = counterTape n)
    (hU : U r = counterTape (j + 1))
    (hbody : RunsIn P.step (cfg qStart T)
      (cfg qDone (Function.update U r (counterTape j))) B)
    (hhalt : P qDone (heads (Function.update U r (counterTape j))) = none) :
    RunsIn (program r s P qStart).step (cfg start T) (cfg start U)
      (B + 4 * j + 12) := by
  have ht := TapeUnaryCompare.runs_compare hrs T j n hR hS
  have ho := (TapeUnaryCompareScan.result_eq_lt_iff j n).mpr hj
  rw [Nat.min_eq_left hj.le, ho] at ht
  have hb := runs_body r P qStart qDone T U j B hU hbody hhalt
  have h := loop_iter (TapeUnaryCompare.program r s) (bodyProgram r P)
    (.scan .beginR) (bodyStart qStart) again ht rfl rfl hb rfl
  exact h.mono (by omega)

theorem runs_exit {Q : Type uDepth13} {r s : TapeRegister} (hrs : r ≠ s)
    (P : TapeMultiProgram Q) (qStart : Q) (T : TapeTapes) (n : ℕ)
    (hR : T r = counterTape n) (hS : T s = counterTape n) :
    RunsIn (program r s P qStart).step (cfg start T) (cfg done T) (4 * n + 8) := by
  have ht := TapeUnaryCompare.runs_compare hrs T n n hR hS
  have ho := (TapeUnaryCompareScan.result_eq_eq_iff n n).mpr rfl
  rw [Nat.min_self, ho] at ht
  have h := loop_exit (TapeUnaryCompare.program r s) (bodyProgram r P)
    (.scan .beginR) (bodyStart qStart) again ht rfl rfl
  exact h.mono (by omega)

theorem runs {Q : Type uDepth14} {r s : TapeRegister} (hrs : r ≠ s)
    (P : TapeMultiProgram Q) (qStart qDone : Q) (σ : ℕ → TapeTapes) (n B : ℕ)
    (hindex : ∀ j ≤ n, σ j r = counterTape j)
    (hbound : ∀ j ≤ n, σ j s = counterTape n)
    (hbody : ∀ j < n, RunsIn P.step (cfg qStart (σ j))
      (cfg qDone (Function.update (σ (j + 1)) r (counterTape j))) B)
    (hhalt : ∀ h, P qDone h = none) (i : ℕ) (hi : i ≤ n) :
    RunsIn (program r s P qStart).step (cfg start (σ i)) (cfg done (σ n))
      ((n - i) * (B + 4 * n + 12) + (4 * n + 8)) := by
  refine Nat.decreasingInduction (motive := fun j _ =>
    RunsIn (program r s P qStart).step (cfg start (σ j)) (cfg done (σ n))
      ((n - j) * (B + 4 * n + 12) + (4 * n + 8))) ?_ ?_ hi
  · intro j hj ih
    have hjn : j ≤ n := hj.le
    have hstep := runs_iteration hrs P qStart qDone (σ j) (σ (j + 1)) j n B hj
      (hindex j hjn) (hbound j hjn) (hindex (j + 1) hj)
      (hbody j hj) (hhalt _)
    have hstep' := hstep.mono (show B + 4 * j + 12 ≤ B + 4 * n + 12 by omega)
    have hall := hstep'.trans ih
    have hd : n - j = (n - (j + 1)) + 1 := by omega
    apply hall.mono
    rw [hd, Nat.add_mul, Nat.one_mul]
    omega
  · simpa only [Nat.sub_self, Nat.zero_mul, Nat.zero_add] using
      runs_exit hrs P qStart (σ n) n (hindex n (Nat.le_refl n))
        (hbound n (Nat.le_refl n))

theorem runs_zero {Q : Type uDepth15} {r s : TapeRegister} (hrs : r ≠ s)
    (P : TapeMultiProgram Q) (qStart qDone : Q) (σ : ℕ → TapeTapes) (n B : ℕ)
    (hindex : ∀ j ≤ n, σ j r = counterTape j)
    (hbound : ∀ j ≤ n, σ j s = counterTape n)
    (hbody : ∀ j < n, RunsIn P.step (cfg qStart (σ j))
      (cfg qDone (Function.update (σ (j + 1)) r (counterTape j))) B)
    (hhalt : ∀ h, P qDone h = none) :
    RunsIn (program r s P qStart).step (cfg start (σ 0)) (cfg done (σ n))
      (n * (B + 4 * n + 12) + (4 * n + 8)) := by
  simpa only [Nat.sub_zero] using
    runs hrs P qStart qDone σ n B hindex hbound hbody hhalt 0 (Nat.zero_le n)

end TapeForLoop
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

def hashUpdateRow (u x : List Bool) (i : ℕ) : List ℕ → List Bool → List Bool
  | [], c => c
  | j :: js, c => hashUpdateRow u x i js
      (xorListAt c i (u.getD (i + j) false && x.getD j false))

@[simp] theorem hashUpdateRow_nil (u x : List Bool) (i : ℕ) (c : List Bool) :
    hashUpdateRow u x i [] c = c := rfl

theorem hashUpdateRow_step (u x : List Bool) (i j : ℕ)
    (js : List ℕ) (c : List Bool) :
    hashUpdateRow u x i (j :: js) c = hashUpdateRow u x i js
      (xorListAt c i (u.getD (i + j) false && x.getD j false)) := rfl

@[simp] theorem hashUpdateRow_length (u x : List Bool) (i : ℕ)
    (js : List ℕ) (c : List Bool) :
    (hashUpdateRow u x i js c).length = c.length := by
  induction js generalizing c with
  | nil => rfl
  | cons j js ih => rw [hashUpdateRow_step, ih, xorListAt_length]

theorem hashUpdateRow_append (u x : List Bool) (i : ℕ)
    (js ks : List ℕ) (c : List Bool) :
    hashUpdateRow u x i (js ++ ks) c =
      hashUpdateRow u x i ks (hashUpdateRow u x i js c) := by
  induction js generalizing c with
  | nil => rfl
  | cons j js ih =>
      simp only [List.cons_append, hashUpdateRow_step, ih]

theorem hashUpdateRow_getD (u x : List Bool) (i : ℕ)
    (js : List ℕ) (c : List Bool) (k : ℕ) (hi : i < c.length) :
    (hashUpdateRow u x i js c).getD k false =
      Bool.xor (c.getD k false)
        (if i = k then xorBits (js.map fun j =>
          u.getD (i + j) false && x.getD j false) else false) := by
  induction js generalizing c with
  | nil => simp
  | cons j js ih =>
      have hi' : i <
          (xorListAt c i (u.getD (i + j) false && x.getD j false)).length := by
        simpa only [xorListAt_length] using hi
      rw [hashUpdateRow_step, ih _ hi',
        xorListAt_getD c i (u.getD (i + j) false && x.getD j false) hi k]
      by_cases hik : i = k <;>
        simp [hik, List.map_cons, xorBits_cons]

theorem hashUpdateRow_getD_self (u x : List Bool) (i : ℕ)
    (js : List ℕ) (c : List Bool) (hi : i < c.length) :
    (hashUpdateRow u x i js c).getD i false =
      Bool.xor (c.getD i false)
        (xorBits (js.map fun j => u.getD (i + j) false && x.getD j false)) := by
  simpa only [ite_eq_left rfl, ite_true] using hashUpdateRow_getD u x i js c i hi

theorem hashUpdateRow_getD_ne (u x : List Bool) (i : ℕ)
    (js : List ℕ) (c : List Bool) (k : ℕ) (hi : i < c.length) (hik : i ≠ k) :
    (hashUpdateRow u x i js c).getD k false = c.getD k false := by
  simpa only [ite_eq_right hik, Bool.xor_false] using hashUpdateRow_getD u x i js c k hi

def hashRowBit (u x : List Bool) (i : ℕ) : Bool :=
  xorBits ((List.range x.length).map fun j =>
    u.getD (i + j) false && x.getD j false)

def hashUpdateRows (u x : List Bool) : List ℕ → List Bool → List Bool
  | [], c => c
  | i :: is, c => hashUpdateRows u x is
      (hashUpdateRow u x i (List.range x.length) c)

@[simp] theorem hashUpdateRows_nil (u x : List Bool) (c : List Bool) :
    hashUpdateRows u x [] c = c := rfl

theorem hashUpdateRows_step (u x : List Bool) (i : ℕ)
    (is : List ℕ) (c : List Bool) :
    hashUpdateRows u x (i :: is) c = hashUpdateRows u x is
      (hashUpdateRow u x i (List.range x.length) c) := rfl

@[simp] theorem hashUpdateRows_length (u x : List Bool)
    (is : List ℕ) (c : List Bool) :
    (hashUpdateRows u x is c).length = c.length := by
  induction is generalizing c with
  | nil => rfl
  | cons i is ih => rw [hashUpdateRows_step, ih, hashUpdateRow_length]

theorem hashUpdateRows_append (u x : List Bool)
    (is ks : List ℕ) (c : List Bool) :
    hashUpdateRows u x (is ++ ks) c =
      hashUpdateRows u x ks (hashUpdateRows u x is c) := by
  induction is generalizing c with
  | nil => rfl
  | cons i is ih =>
      simp only [List.cons_append, hashUpdateRows_step, ih]

theorem hashUpdateRows_getD (u x : List Bool)
    (is : List ℕ) (c : List Bool) (k : ℕ)
    (hbound : ∀ i ∈ is, i < c.length) :
    (hashUpdateRows u x is c).getD k false =
      Bool.xor (c.getD k false)
        (xorBits (is.map fun i => if i = k then hashRowBit u x i else false)) := by
  induction is generalizing c with
  | nil => simp
  | cons i is ih =>
      have hi : i < c.length := hbound i (by simp)
      have hrest : ∀ i' ∈ is,
          i' < (hashUpdateRow u x i (List.range x.length) c).length := by
        intro i' hi'
        rw [hashUpdateRow_length]
        exact hbound i' (List.mem_cons_of_mem i hi')
      rw [hashUpdateRows_step, ih _ hrest,
        hashUpdateRow_getD u x i (List.range x.length) c k hi]
      simp only [hashRowBit, List.map_cons, xorBits_cons, Bool.xor_assoc]

theorem hashUpdateRow_range'_append (u x : List Bool) (i s m n : ℕ) (c : List Bool) :
    hashUpdateRow u x i (List.range' s (m + n)) c =
      hashUpdateRow u x i (List.range' (s + m) n)
        (hashUpdateRow u x i (List.range' s m) c) := by
  rw [← List.range'_append_1, hashUpdateRow_append]

theorem hashUpdateRow_range'_prefix (u x : List Bool) (i s m n : ℕ)
    (c : List Bool) (hm : m ≤ n) :
    hashUpdateRow u x i (List.range' (s + m) (n - m))
        (hashUpdateRow u x i (List.range' s m) c) =
      hashUpdateRow u x i (List.range' s n) c := by
  rw [← hashUpdateRow_range'_append, Nat.add_sub_of_le hm]

theorem hashUpdateRow_range'_step (u x : List Bool) (i s n : ℕ) (c : List Bool) :
    hashUpdateRow u x i (List.range' s (n + 1)) c =
      hashUpdateRow u x i (List.range' (s + 1) n)
        (xorListAt c i (u.getD (i + s) false && x.getD s false)) := by
  rw [List.range'_succ, hashUpdateRow_step]

theorem hashUpdateRow_range'_snoc (u x : List Bool) (i s n : ℕ) (c : List Bool) :
    hashUpdateRow u x i (List.range' s (n + 1)) c =
      xorListAt (hashUpdateRow u x i (List.range' s n) c) i
        (u.getD (i + (s + n)) false && x.getD (s + n) false) := by
  rw [List.range'_concat, hashUpdateRow_append]
  simp only [Nat.one_mul, hashUpdateRow_step, hashUpdateRow_nil]

theorem hashUpdateRows_range'_append (u x : List Bool) (s m n : ℕ) (c : List Bool) :
    hashUpdateRows u x (List.range' s (m + n)) c =
      hashUpdateRows u x (List.range' (s + m) n)
        (hashUpdateRows u x (List.range' s m) c) := by
  rw [← List.range'_append_1, hashUpdateRows_append]

theorem hashUpdateRows_range'_prefix (u x : List Bool) (s m n : ℕ)
    (c : List Bool) (hm : m ≤ n) :
    hashUpdateRows u x (List.range' (s + m) (n - m))
        (hashUpdateRows u x (List.range' s m) c) =
      hashUpdateRows u x (List.range' s n) c := by
  rw [← hashUpdateRows_range'_append, Nat.add_sub_of_le hm]

theorem hashUpdateRows_range'_step (u x : List Bool) (s n : ℕ) (c : List Bool) :
    hashUpdateRows u x (List.range' s (n + 1)) c =
      hashUpdateRows u x (List.range' (s + 1) n)
        (hashUpdateRow u x s (List.range x.length) c) := by
  rw [List.range'_succ, hashUpdateRows_step]

theorem hashUpdateRows_range'_snoc (u x : List Bool) (s n : ℕ) (c : List Bool) :
    hashUpdateRows u x (List.range' s (n + 1)) c =
      hashUpdateRow u x (s + n) (List.range x.length)
        (hashUpdateRows u x (List.range' s n) c) := by
  rw [List.range'_concat, hashUpdateRows_append]
  simp only [Nat.one_mul, hashUpdateRows_step, hashUpdateRows_nil]

theorem hashUpdateRow_range_succ (u x : List Bool) (i j : ℕ) (c : List Bool) :
    hashUpdateRow u x i (List.range (j + 1)) c =
      xorListAt (hashUpdateRow u x i (List.range j) c) i
        (u.getD (i + j) false && x.getD j false) := by
  simpa only [List.range_eq_range', Nat.zero_add] using
    hashUpdateRow_range'_snoc u x i 0 j c

theorem hashUpdateRows_range_succ (u x : List Bool) (i : ℕ) (c : List Bool) :
    hashUpdateRows u x (List.range (i + 1)) c =
      hashUpdateRow u x i (List.range x.length)
        (hashUpdateRows u x (List.range i) c) := by
  simpa only [List.range_eq_range', Nat.zero_add] using
    hashUpdateRows_range'_snoc u x 0 i c

theorem hashReadIndex_lt {d r i j : ℕ} (hi : i < r) (hj : j < d) :
    i + j < d + r - 1 := by omega

private theorem xorBits_map_single_index (is : List ℕ) (hn : is.Nodup)
    (k : ℕ) (f : ℕ → Bool) :
    xorBits (is.map fun i => if i = k then f i else false) =
      if k ∈ is then f k else false := by
  induction is with
  | nil => simp
  | cons i is ih =>
      have hnodup := List.nodup_cons.mp hn
      rw [List.map_cons, xorBits_cons, ih hnodup.2]
      by_cases hik : i = k
      · subst i
        simp [hnodup.1]
      · simp [hik, Ne.symm hik]

theorem hashUpdateRows_getD_nodup (u x : List Bool)
    (is : List ℕ) (c : List Bool) (k : ℕ)
    (hbound : ∀ i ∈ is, i < c.length) (hn : is.Nodup) :
    (hashUpdateRows u x is c).getD k false =
      Bool.xor (c.getD k false) (if k ∈ is then hashRowBit u x k else false) := by
  rw [hashUpdateRows_getD u x is c k hbound,
    xorBits_map_single_index is hn k (hashRowBit u x)]

def hashByUpdates (r : ℕ) (u x : List Bool) : List Bool :=
  hashUpdateRows u x (List.range r) (List.replicate r false)

@[simp] theorem hashByUpdates_length (r : ℕ) (u x : List Bool) :
    (hashByUpdates r u x).length = r := by simp [hashByUpdates]

theorem hashByUpdates_getD (r : ℕ) (u x : List Bool) (k : ℕ) :
    (hashByUpdates r u x).getD k false =
      if k < r then hashRowBit u x k else false := by
  have hbound : ∀ i ∈ List.range r, i < (List.replicate r false).length := by
    intro i hi
    simpa only [List.length_replicate] using List.mem_range.mp hi
  unfold hashByUpdates
  rw [hashUpdateRows_getD_nodup u x (List.range r) (List.replicate r false)
    k hbound List.nodup_range]
  simp

theorem hashRowBit_ofFn {d r : ℕ} (u : BitWord (d + r - 1)) (x : BitWord d)
    (i : Fin r) :
    hashRowBit (List.ofFn u) (List.ofFn x) i.val = wordHash u x i := by
  unfold hashRowBit
  rw [List.length_ofFn, ← ofFn_nat_eq_map_range]
  simp only [wordHash, wordFreeze_eq]
  apply congrArg xorBits
  apply congrArg List.ofFn
  funext j
  have hu : i.val + j.val < d + r - 1 := (BinaryHash.sumIndex i j).is_lt
  change ((wordList u).getD (i.val + j.val) false && (wordList x).getD j.val false) =
    (u (BinaryHash.sumIndex i j) && x j)
  simp only [wordList_getD, wordGet_of_lt u hu, wordGet_fin, BinaryHash.sumIndex]

theorem hashByUpdates_ofFn_eq {d r : ℕ} (u : BitWord (d + r - 1)) (x : BitWord d) :
    hashByUpdates r (List.ofFn u) (List.ofFn x) = List.ofFn (wordHash u x) := by
  apply List.ext_getElem
  · simp
  · intro k hk hl
    have hkr : k < r := by simpa only [List.length_ofFn] using hl
    have hleft := hashByUpdates_getD r (List.ofFn u) (List.ofFn x) k
    rw [ite_eq_left hkr, List.getD_eq_getElem _ _ hk] at hleft
    simpa using hleft.trans (hashRowBit_ofFn u x ⟨k, hkr⟩)

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHashInner

open TapeMultiProgram TapeUnary TapeRegister

abbrev State := TapeForLoop.State TapeHashStep.State

def program : TapeMultiProgram State :=
  TapeForLoop.program indexB dataLength TapeHashStep.program TapeHashStep.start

def start : State := TapeForLoop.start
def done : State := TapeForLoop.done

def progressStore (σ : TapeStore) (i j : ℕ) : TapeStore :=
  Function.update (Function.update (Function.update σ hashBits
    (hashUpdateRow (σ keyBits) (σ dataBits) i (List.range j) (σ hashBits)))
    indexA (List.replicate (i + j) true)) indexB (List.replicate j true)

theorem progress_zero (σ : TapeStore) (i : ℕ)
    (ha : σ indexA = List.replicate i true) (hb : σ indexB = []) :
    progressStore σ i 0 = σ := by
  simp only [progressStore, List.range_zero, hashUpdateRow_nil,
    Function.update_eq_self, Nat.add_zero, List.replicate_zero, ← ha, ← hb]

theorem progress_step (σ : TapeStore) (i j : ℕ) :
    TapeHashStep.resultStore (progressStore σ i j) i j =
      Function.update (progressStore σ i (j + 1)) indexB (List.replicate j true) := by
  funext r
  by_cases hb : r = indexB
  · subst r
    simp [TapeHashStep.resultStore, progressStore, indexA, indexB, hashBits]
  · by_cases ha : r = indexA
    · subst r
      simp [TapeHashStep.resultStore, progressStore, indexA, indexB, Nat.add_assoc]
    · by_cases hh : r = hashBits
      · subst r
        simp [TapeHashStep.resultStore, progressStore, hashUpdateRow_range_succ,
          indexA, indexB, hashBits, keyBits, dataBits]
      · simp [TapeHashStep.resultStore, progressStore, hb, ha, hh]

theorem runs_inner (σ : TapeStore) (i d r : ℕ)
    (hi : i < r) (hd : σ dataLength = List.replicate d true)
    (ha : σ indexA = List.replicate i true) (hb : σ indexB = [])
    (hc : σ indexC = List.replicate i true)
    (hkey : (σ keyBits).length = d + r - 1)
    (hdata : (σ dataBits).length = d) (hout : (σ hashBits).length = r) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (progressStore σ i d)))
      (d * (4 * i + 8 * d + 29) + 4 * d + 8) := by
  let τ : ℕ → TapeTapes := fun j => storeTapes (progressStore σ i j)
  have hindex : ∀ j ≤ d, τ j indexB = counterTape j := by
    intro j hj
    simp [τ, progressStore, counterTape]
  have hbound : ∀ j ≤ d, τ j dataLength = counterTape d := by
    intro j hj
    simp [τ, progressStore, counterTape, hd, dataLength, indexA, indexB, hashBits]
  have hbody : ∀ j < d, RunsIn TapeHashStep.program.step
      (cfg TapeHashStep.start (τ j))
      (cfg TapeHashStep.done (Function.update (τ (j + 1)) indexB (counterTape j)))
      (4 * i + 4 * d + 17) := by
    intro j hj
    have hkey' : i + j < (progressStore σ i j keyBits).length := by
      simpa [progressStore, keyBits, indexA, indexB, hashBits, hkey] using
        (hashReadIndex_lt hi hj)
    have hdata' : j < (progressStore σ i j dataBits).length := by
      simpa [progressStore, dataBits, indexA, indexB, hashBits, hdata] using hj
    have hout' : i < (progressStore σ i j hashBits).length := by
      simpa [progressStore, indexA, indexB, hashBits, hout] using hi
    have hs := TapeHashStep.runs_step (progressStore σ i j) i j
      (by simp [progressStore, indexA, indexB])
      (by simp [progressStore])
      (by simp [progressStore, hc, indexA, indexB, indexC, hashBits])
      hkey' hdata' hout'
    have hs' := hs.mono (show 4 * i + 4 * j + 17 ≤ 4 * i + 4 * d + 17 by omega)
    simpa only [τ, progress_step, storeTapes_update, counterTape] using hs'
  have hall := TapeForLoop.runs_zero (by decide : indexB ≠ dataLength)
    TapeHashStep.program TapeHashStep.start TapeHashStep.done τ d (4 * i + 4 * d + 17)
    hindex hbound hbody TapeHashStep.program_done
  have htime : d * (4 * i + 4 * d + 17 + 4 * d + 12) + (4 * d + 8) =
      d * (4 * i + 8 * d + 29) + 4 * d + 8 := by ring
  simpa only [program, start, done, τ, progress_zero σ i ha hb, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashInner
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHashRow

open TapeMultiProgram TapeRouting TapeRegister

abbrev RunState := TapeCopy.State ⊕ TapeHashInner.State
abbrev ClearState := RunState ⊕ TapeErase.State
abbrev State := ClearState ⊕ TapeErase.State

def runProgram : TapeMultiProgram RunState :=
  joinCode (TapeCopy.code indexC indexA) TapeHashInner.program
    (fun _ => TapeHashInner.start)

def clearProgram : TapeMultiProgram ClearState :=
  joinCode runProgram (TapeErase.code indexA) (fun _ => TapeErase.State.start)

def program : TapeMultiProgram State :=
  joinCode clearProgram (TapeErase.code indexB) (fun _ => TapeErase.State.start)

def start : State := .inl (.inl (.inl TapeCopy.State.start))
def done : State := .inr TapeErase.State.done

def resultStore (σ : TapeStore) (i d : ℕ) : TapeStore :=
  Function.update σ hashBits
    (hashUpdateRow (σ keyBits) (σ dataBits) i (List.range d) (σ hashBits))

theorem runs_row (σ : TapeStore) (i d r : ℕ)
    (hi : i < r) (hd : σ dataLength = List.replicate d true)
    (ha : σ indexA = []) (hb : σ indexB = [])
    (hc : σ indexC = List.replicate i true)
    (hkey : (σ keyBits).length = d + r - 1)
    (hdata : (σ dataBits).length = d) (hout : (σ hashBits).length = r) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (resultStore σ i d)))
      (d * (4 * i + 8 * d + 29) + 4 * i + 8 * d + 25) := by
  let τ := Function.update σ indexA (σ indexC)
  let τ₁ := TapeHashInner.progressStore τ i d
  let τ₂ := Function.update τ₁ indexA []
  let τ₃ := Function.update τ₂ indexB []
  have hcopy := TapeStoreRuns.copy (by decide : indexC ≠ indexA) σ ha
  have hinner := TapeHashInner.runs_inner τ i d r hi
    (by simp [τ, hd, dataLength, indexA])
    (by simp [τ, hc])
    (by simp [τ, hb, indexA, indexB])
    (by simp [τ, hc, indexA, indexC])
    (by simpa [τ, indexA, keyBits] using hkey)
    (by simpa [τ, indexA, dataBits] using hdata)
    (by simpa [τ, indexA, hashBits] using hout)
  have hrun := join_runs (TapeCopy.code indexC indexA) TapeHashInner.program
    (fun _ => TapeHashInner.start) hcopy rfl hinner
  have heraseA := TapeStoreRuns.erase indexA τ₁
  have hclear := join_runs runProgram (TapeErase.code indexA)
    (fun _ => TapeErase.State.start) hrun rfl heraseA
  have heraseB := TapeStoreRuns.erase indexB τ₂
  have hall := join_runs clearProgram (TapeErase.code indexB)
    (fun _ => TapeErase.State.start) hclear rfl heraseB
  have hstore : τ₃ = resultStore σ i d := by
    funext q
    by_cases hB : q = indexB
    · subst q
      simp [τ₃, resultStore, hb, indexB, hashBits]
    · by_cases hA : q = indexA
      · subst q
        simp [τ₃, τ₂, resultStore, ha, indexA, indexB, hashBits]
      · by_cases hH : q = hashBits
        · subst q
          simp [τ₃, τ₂, τ₁, TapeHashInner.progressStore, τ, resultStore,
            indexA, indexB, hashBits, keyBits, dataBits]
        · simp [τ₃, τ₂, τ₁, TapeHashInner.progressStore, τ, resultStore, hB, hA, hH]
  have hlenC : (σ indexC).length = i := by simp [hc]
  have hlenA : (τ₁ indexA).length = i + d := by
    simp [τ₁, TapeHashInner.progressStore, indexA, indexB]
  have hlenB : (τ₂ indexB).length = d := by
    simp [τ₂, τ₁, TapeHashInner.progressStore, indexA, indexB]
  have htime : ((2 * i + 4 + 1 + (d * (4 * i + 8 * d + 29) + 4 * d + 8)) +
      1 + (2 * (i + d) + 5)) + 1 + (2 * d + 5) =
      d * (4 * i + 8 * d + 29) + 4 * i + 8 * d + 25 := by ring
  have hall' : RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes τ₃))
      (d * (4 * i + 8 * d + 29) + 4 * i + 8 * d + 25) := by
    simpa only [program, start, done, hlenC, hlenA, hlenB, htime] using hall
  simpa only [hstore] using hall'

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashRow
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHashOuter

open TapeMultiProgram TapeUnary TapeRegister

abbrev State := TapeForLoop.State TapeHashRow.State

def program : TapeMultiProgram State :=
  TapeForLoop.program indexC ringDegree TapeHashRow.program TapeHashRow.start

def start : State := TapeForLoop.start
def done : State := TapeForLoop.done

def progressStore (σ : TapeStore) (i : ℕ) : TapeStore :=
  Function.update (Function.update σ hashBits
    (hashUpdateRows (σ keyBits) (σ dataBits) (List.range i) (σ hashBits)))
    indexC (List.replicate i true)

theorem progress_zero (σ : TapeStore) (hc : σ indexC = []) :
    progressStore σ 0 = σ := by
  simp only [progressStore, List.range_zero, hashUpdateRows_nil,
    Function.update_eq_self, List.replicate_zero, ← hc]

theorem progress_step (σ : TapeStore) (i d : ℕ) (hd : (σ dataBits).length = d) :
    TapeHashRow.resultStore (progressStore σ i) i d =
      Function.update (progressStore σ (i + 1)) indexC (List.replicate i true) := by
  funext q
  by_cases hc : q = indexC
  · subst q
    simp [TapeHashRow.resultStore, progressStore, indexC, hashBits]
  · by_cases hh : q = hashBits
    · subst q
      simp [TapeHashRow.resultStore, progressStore, hashUpdateRows_range_succ, hd,
        indexC, hashBits, keyBits, dataBits]
    · simp [TapeHashRow.resultStore, progressStore, hc, hh]

theorem row_cost_le (i d r : ℕ) (hi : i ≤ r) :
    d * (4 * i + 8 * d + 29) + 4 * i + 8 * d + 25 ≤
      64 * (d + r + 1) ^ 2 := by
  have hm := Nat.mul_le_mul_left d
    (show 4 * i + 8 * d + 29 ≤ 4 * r + 8 * d + 29 by omega)
  have hfirst : d * (4 * i + 8 * d + 29) + 4 * i + 8 * d + 25 ≤
      d * (4 * r + 8 * d + 29) + 4 * r + 8 * d + 25 := by omega
  apply hfirst.trans
  nlinarith [Nat.zero_le (d * r)]

theorem runs_outer (σ : TapeStore) (d r : ℕ)
    (hd : σ dataLength = List.replicate d true)
    (hr : σ ringDegree = List.replicate r true)
    (ha : σ indexA = []) (hb : σ indexB = []) (hc : σ indexC = [])
    (hkey : (σ keyBits).length = d + r - 1)
    (hdata : (σ dataBits).length = d) (hout : (σ hashBits).length = r) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (progressStore σ r)))
      (r * (64 * (d + r + 1) ^ 2 + 4 * r + 12) + (4 * r + 8)) := by
  let τ : ℕ → TapeTapes := fun i => storeTapes (progressStore σ i)
  have hindex : ∀ i ≤ r, τ i indexC = counterTape i := by
    intro i hi
    simp [τ, progressStore, counterTape]
  have hbound : ∀ i ≤ r, τ i ringDegree = counterTape r := by
    intro i hi
    simp [τ, progressStore, counterTape, hr, ringDegree, indexC, hashBits]
  have hbody : ∀ i < r, RunsIn TapeHashRow.program.step
      (cfg TapeHashRow.start (τ i))
      (cfg TapeHashRow.done (Function.update (τ (i + 1)) indexC (counterTape i)))
      (64 * (d + r + 1) ^ 2) := by
    intro i hi
    have hs := TapeHashRow.runs_row (progressStore σ i) i d r hi
      (by simp [progressStore, hd, dataLength, indexC, hashBits])
      (by simp [progressStore, ha, indexA, indexC, hashBits])
      (by simp [progressStore, hb, indexB, indexC, hashBits])
      (by simp [progressStore])
      (by simpa [progressStore, keyBits, indexC, hashBits] using hkey)
      (by simpa [progressStore, dataBits, indexC, hashBits] using hdata)
      (by simp [progressStore, hout, indexC, hashBits])
    have hs' := hs.mono (row_cost_le i d r hi.le)
    simpa only [τ, progress_step σ i d hdata, storeTapes_update, counterTape] using hs'
  have hall := TapeForLoop.runs_zero (by decide : indexC ≠ ringDegree)
    TapeHashRow.program TapeHashRow.start TapeHashRow.done τ r (64 * (d + r + 1) ^ 2)
    hindex hbound hbody TapeHashRow.program_done
  simpa only [program, start, done, τ, progress_zero σ hc] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashOuter
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHash

open TapeMultiProgram TapeRouting TapeRegister

abbrev State := TapeHashInitialize.State ⊕ TapeHashOuter.State

def program : TapeMultiProgram State :=
  joinCode TapeHashInitialize.program TapeHashOuter.program (fun _ => TapeHashOuter.start)

def start : State := .inl TapeHashInitialize.start
def done : State := .inr TapeHashOuter.done

def resultStore (σ : TapeStore) (r : ℕ) : TapeStore :=
  Function.update (Function.update σ hashBits (hashByUpdates r (σ keyBits) (σ dataBits)))
    indexC (List.replicate r true)

theorem cost_le (d r : ℕ) :
    10 * r + 8 + 1 + (r * (64 * (d + r + 1) ^ 2 + 4 * r + 12) + (4 * r + 8)) ≤
      200 * (d + r + 1) ^ 3 := by
  let N := d + r + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hr : r ≤ N := by dsimp [N]; omega
  have hsq : N ≤ N ^ 2 := by
    have h := Nat.mul_le_mul_left N hN
    simpa only [Nat.mul_one, pow_two] using h
  have hterm : 64 * N ^ 2 + 4 * r + 12 ≤ 80 * N ^ 2 := by nlinarith
  have hprod := Nat.mul_le_mul hr hterm
  have hprod' : r * (64 * N ^ 2 + 4 * r + 12) ≤ 80 * N ^ 3 := by
    calc
      _ ≤ N * (80 * N ^ 2) := hprod
      _ = _ := by ring
  have hcube : N ≤ N ^ 3 := by
    have h := Nat.mul_le_mul_left N (show 1 ≤ N ^ 2 by omega)
    calc
      N ≤ N * N ^ 2 := by simpa only [Nat.mul_one] using h
      _ = N ^ 3 := by ring
  change 10 * r + 8 + 1 + (r * (64 * N ^ 2 + 4 * r + 12) + (4 * r + 8)) ≤ 200 * N ^ 3
  nlinarith

theorem runs_hash (σ : TapeStore) (d r : ℕ)
    (hd : σ dataLength = List.replicate d true)
    (hr : σ ringDegree = List.replicate r true)
    (ha : σ indexA = []) (hb : σ indexB = []) (hc : σ indexC = [])
    (hs : σ scratchA = []) (hh : σ hashBits = [])
    (hkey : (σ keyBits).length = d + r - 1) (hdata : (σ dataBits).length = d) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (resultStore σ r))) (200 * (d + r + 1) ^ 3) := by
  let τ := Function.update σ hashBits (List.replicate r false)
  have hinit := TapeHashInitialize.runs_initialize σ r hr hs hh
  have houter := TapeHashOuter.runs_outer τ d r
    (by simp [τ, hd, dataLength, hashBits])
    (by simp [τ, hr, ringDegree, hashBits])
    (by simp [τ, ha, indexA, hashBits])
    (by simp [τ, hb, indexB, hashBits])
    (by simp [τ, hc, indexC, hashBits])
    (by simpa [τ, keyBits, hashBits] using hkey)
    (by simpa [τ, dataBits, hashBits] using hdata)
    (by simp [τ])
  have hall := join_runs TapeHashInitialize.program TapeHashOuter.program
    (fun _ => TapeHashOuter.start) hinit rfl houter
  have hstore : TapeHashOuter.progressStore τ r = resultStore σ r := by
    funext q
    by_cases hc' : q = indexC
    · subst q
      simp [TapeHashOuter.progressStore, resultStore]
    · by_cases hh' : q = hashBits
      · subst q
        simp [TapeHashOuter.progressStore, resultStore, hashByUpdates, τ,
          indexC, hashBits, keyBits, dataBits]
      · simp [TapeHashOuter.progressStore, resultStore, τ, hc', hh']
  have hbounded := hall.mono (cost_le d r)
  simpa only [program, start, done, hstore] using hbounded

theorem runs_wordHash (σ : TapeStore) {d r : ℕ}
    (u : BitWord (d + r - 1)) (x : BitWord d)
    (hd : σ dataLength = List.replicate d true)
    (hr : σ ringDegree = List.replicate r true)
    (ha : σ indexA = []) (hb : σ indexB = []) (hc : σ indexC = [])
    (hs : σ scratchA = []) (hh : σ hashBits = [])
    (hkey : σ keyBits = List.ofFn u) (hdata : σ dataBits = List.ofFn x) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update (Function.update σ hashBits
        (List.ofFn (wordHash u x))) indexC (List.replicate r true))))
      (200 * (d + r + 1) ^ 3) := by
  have h := runs_hash σ d r hd hr ha hb hc hs hh
    (by simp [hkey]) (by simp [hdata])
  simpa only [resultStore, hkey, hdata, hashByUpdates_ofFn_eq] using h

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHash
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHashClean

open TapeMultiProgram TapeRouting TapeRegister

abbrev State := TapeHash.State ⊕ TapeErase.State

def program : TapeMultiProgram State :=
  joinCode TapeHash.program (TapeErase.code indexC) (fun _ => TapeErase.State.start)

def start : State := .inl TapeHash.start
def done : State := .inr TapeErase.State.done

theorem cost_le (d r : ℕ) :
    200 * (d + r + 1) ^ 3 + 1 + (2 * r + 5) ≤ 210 * (d + r + 1) ^ 3 := by
  let N := d + r + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hr : r < N := by dsimp [N]; omega
  have hsq : N ≤ N ^ 2 := by
    simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left N hN
  have hcube : N ≤ N ^ 3 := by
    have h := Nat.mul_le_mul_left N (show 1 ≤ N ^ 2 by omega)
    calc
      N ≤ N * N ^ 2 := by simpa only [Nat.mul_one] using h
      _ = N ^ 3 := by ring
  change 200 * N ^ 3 + 1 + (2 * r + 5) ≤ 210 * N ^ 3
  nlinarith

theorem runs_wordHash (σ : TapeStore) {d r : ℕ}
    (u : BitWord (d + r - 1)) (x : BitWord d)
    (hd : σ dataLength = List.replicate d true)
    (hr : σ ringDegree = List.replicate r true)
    (ha : σ indexA = []) (hb : σ indexB = []) (hc : σ indexC = [])
    (hs : σ scratchA = []) (hh : σ hashBits = [])
    (hkey : σ keyBits = List.ofFn u) (hdata : σ dataBits = List.ofFn x) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ hashBits (List.ofFn (wordHash u x)))))
      (210 * (d + r + 1) ^ 3) := by
  let τ := Function.update (Function.update σ hashBits (List.ofFn (wordHash u x)))
    indexC (List.replicate r true)
  have hhash := TapeHash.runs_wordHash σ u x hd hr ha hb hc hs hh hkey hdata
  have herase := TapeStoreRuns.erase indexC τ
  have hall := join_runs TapeHash.program (TapeErase.code indexC)
    (fun _ => TapeErase.State.start) hhash rfl herase
  have hC : (Function.update σ hashBits (List.ofFn (wordHash u x))) indexC = [] := by
    simp [hc, indexC, hashBits]
  have hstore : Function.update τ indexC [] =
      Function.update σ hashBits (List.ofFn (wordHash u x)) := by
    simp only [τ, Function.update_idem, ← hC, Function.update_eq_self]
  have hlen : (τ indexC).length = r := by simp [τ]
  have hall' : RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ hashBits (List.ofFn (wordHash u x)))))
      (200 * (d + r + 1) ^ 3 + 1 + (2 * r + 5)) := by
    simpa only [program, start, done, hstore, hlen] using hall
  exact hall'.mono (cost_le d r)

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeHashClean
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHornerExtract

open TapeMultiProgram TapeRouting TapeRegister TapeInputBlockLoop

def registers : Registers where
  toFun i := match i.val with
    | 0 => coeffBits
    | 1 => loop3
    | 2 => loop4
    | 3 => loop5
    | _ => scratchB
  inj' := by decide

abbrev State := TapeCopy.State ⊕ TapeInputBlockLoop.State

def program : TapeMultiProgram State :=
  joinCode (TapeCopy.code ringDegree loop4) (TapeInputBlockLoop.program registers)
    (fun _ => TapeInputBlockLoop.start)

def start : State := .inl TapeCopy.State.start
def done : State := .inr TapeInputBlockLoop.done

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

theorem runs_extract (σ : TapeStore) («prefix» block suffix : List Bool) (r : ℕ)
    (hsource : σ coeffBits = «prefix» ++ block ++ suffix)
    (hcursor : σ loop3 = List.replicate («prefix».length + r) true)
    (hdegree : σ ringDegree = List.replicate r true)
    (hblock : block.length = r) (hcount : σ loop4 = [])
    (hdest : σ scratchB = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update
        (Function.update σ loop3 (List.replicate «prefix».length true)) scratchB block)))
      (r * (2 * «prefix».length + r + 19) + 8) := by
  let U := Function.update σ loop4 (List.replicate r true)
  have hc := TapeStoreRuns.copy (src := ringDegree) (dst := loop4) (by decide) σ hcount
  have hc' : RunsIn (TapeCopy.code ringDegree loop4).step
      (cfg TapeCopy.State.start (storeTapes σ)) (cfg TapeCopy.State.done (storeTapes U))
      (2 * r + 4) := by
    simpa only [hdegree, List.length_replicate] using hc
  have hb := TapeInputBlockLoop.runs_block registers σ «prefix» block suffix [] hsource
  have hi : blockStore registers σ («prefix».length + block.length) block.length [] = U := by
    funext q
    by_cases h4 : q = loop4 <;> by_cases h3 : q = loop3 <;>
      by_cases hd : q = scratchB <;>
      simp_all [blockStore, registers, count, index, destination, U, Function.update_apply,
        loop4, loop3, scratchB]
  have ho : blockStore registers σ «prefix».length 0 (block ++ []) =
      Function.update (Function.update σ loop3 (List.replicate «prefix».length true))
        scratchB block := by
    funext q
    by_cases h4 : q = loop4 <;> by_cases h3 : q = loop3 <;>
      by_cases hd : q = scratchB <;>
      simp_all [blockStore, registers, count, index, destination, Function.update_apply]
  rw [hi, ho, hblock] at hb
  have hall := join_runs (TapeCopy.code ringDegree loop4)
    (TapeInputBlockLoop.program registers) (fun _ => TapeInputBlockLoop.start) hc' rfl hb
  have ht : (2 * r + 4) + 1 + (r * (2 * «prefix».length + r + 17) + 3) =
      r * (2 * «prefix».length + r + 19) + 8 := by ring
  simpa only [program, start, done, ht] using hall

end TapeHornerExtract
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeConvolutionStep

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

abbrev SetupState := TapeCopy.State ⊕ TapeCopy.State
abbrev SumState := SetupState ⊕ AddState
abbrev TermState := SumState ⊕ TapeProductTerm.State
abbrev ClearState := TermState ⊕ TapeErase.State
abbrev State := ClearState ⊕ IncState

def copyIndices : TapeMultiProgram SetupState :=
  joinCode (TapeCopy.code indexA indexC) (TapeCopy.code indexB scratchA)
    (fun _ => TapeCopy.State.start)

def sumIndices : TapeMultiProgram SumState :=
  joinCode copyIndices (addProgram scratchA indexC) (fun _ => addStart)

def term : TapeMultiProgram TermState :=
  joinCode sumIndices
    (TapeProductTerm.program indexA hashBits indexB accumBits indexC productBits)
    (fun _ => TapeProductTerm.start)

def clear : TapeMultiProgram ClearState :=
  joinCode term (TapeErase.code indexC) (fun _ => TapeErase.State.start)

def program : TapeMultiProgram State :=
  joinCode clear (incProgram indexB) (fun _ => IncState.start)

def start : State := .inl (.inl (.inl (.inl (.inl TapeCopy.State.start))))
def done : State := .inr IncState.done

def resultStore (σ : TapeStore) (j : ℕ) (out : List Bool) : TapeStore :=
  Function.update (Function.update σ productBits out) indexB (List.replicate (j + 1) true)

theorem runs_step (σ : TapeStore) (pa sa pb sb pc sc : List Bool) (a b old : Bool)
    (hi : σ indexA = List.replicate pa.length true)
    (hj : σ indexB = List.replicate pb.length true)
    (hk : σ indexC = []) (hs : σ scratchA = [])
    (ha : σ hashBits = pa ++ a :: sa) (hb : σ accumBits = pb ++ b :: sb)
    (hc : σ productBits = pc ++ old :: sc) (hlen : pc.length = pa.length + pb.length) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (resultStore σ pb.length
        (pc ++ Bool.xor old (a && b) :: sc))))
      (8 * pa.length + 16 * pb.length + 37) := by
  let σ₁ := Function.update σ indexC (σ indexA)
  let σ₂ := Function.update σ₁ scratchA (σ₁ indexB)
  let σ₃ := Function.update (Function.update σ₂ scratchA []) indexC
    (List.replicate (pa.length + pb.length) true)
  let σ₄ := Function.update σ₃ productBits (pc ++ Bool.xor old (a && b) :: sc)
  let σ₅ := Function.update σ₄ indexC []
  let σ₆ := Function.update σ₅ indexB (List.replicate (pb.length + 1) true)
  have hcopyA := TapeStoreRuns.copy (by decide : indexA ≠ indexC) σ hk
  have hcopyB := TapeStoreRuns.copy (by decide : indexB ≠ scratchA) σ₁ (by
    simp [σ₁, hs, indexC, scratchA])
  have hsetup := join_runs (TapeCopy.code indexA indexC) (TapeCopy.code indexB scratchA)
    (fun _ => TapeCopy.State.start) hcopyA rfl hcopyB
  have hadd := TapeStoreRuns.add (by decide : scratchA ≠ indexC) σ₂ pb.length pa.length
    (by simp [σ₂, σ₁, hj, indexB, indexC])
    (by simp [σ₂, σ₁, hi, scratchA, indexC])
  have hsum := join_runs copyIndices (addProgram scratchA indexC)
    (fun _ => addStart) hsetup rfl hadd
  have hprod := TapeProductTerm.runs_product_term
    indexA hashBits indexB accumBits indexC productBits
    (by decide) (by decide) (by decide) (storeTapes σ₃)
    pa sa pb sb pc sc a b old
    (by simp [σ₃, σ₂, σ₁, hi, counterTape, indexA, indexB, indexC, scratchA])
    (by simp [σ₃, σ₂, σ₁, ha, hashBits, indexC, scratchA])
    (by simp [σ₃, σ₂, σ₁, hj, counterTape, indexA, indexB, indexC, scratchA])
    (by simp [σ₃, σ₂, σ₁, hb, accumBits, indexC, scratchA])
    (by simp [σ₃, counterTape, hlen])
    (by simp [σ₃, σ₂, σ₁, hc, productBits, indexC, scratchA])
  have hprod' : RunsIn
      (TapeProductTerm.program indexA hashBits indexB accumBits indexC productBits).step
      (cfg TapeProductTerm.start (storeTapes σ₃))
      (cfg (TapeProductTerm.done a b old) (storeTapes σ₄))
      (2 * (pa.length + pb.length + pc.length) + 14) := by
    simpa only [σ₄, storeTapes_update] using hprod
  have hterm := join_runs sumIndices
    (TapeProductTerm.program indexA hashBits indexB accumBits indexC productBits)
    (fun _ => TapeProductTerm.start) hsum rfl hprod'
  have herase := TapeStoreRuns.erase indexC σ₄
  have hclear := join_runs term (TapeErase.code indexC)
    (fun _ => TapeErase.State.start) hterm rfl herase
  have hinc := increment indexB (storeTapes σ₅) pb.length (by
    simp [σ₅, σ₄, σ₃, σ₂, σ₁, counterTape, hj, indexB, indexC, scratchA, productBits])
  have hinc' : RunsIn (incProgram indexB).step (cfg IncState.start (storeTapes σ₅))
      (cfg IncState.done (storeTapes σ₆)) 2 := by
    simpa only [σ₆, storeTapes_update, counterTape] using hinc
  have hall := join_runs clear (incProgram indexB) (fun _ => IncState.start) hclear rfl hinc'
  have hstore : σ₆ = resultStore σ pb.length (pc ++ Bool.xor old (a && b) :: sc) := by
    funext r
    by_cases hp : r = productBits
    · subst r
      simp [σ₆, σ₅, σ₄, resultStore, indexB, indexC, productBits]
    · by_cases hj' : r = indexB
      · subst r
        simp [σ₆, resultStore]
      · by_cases hk' : r = indexC
        · subst r
          simp [σ₆, σ₅, resultStore, hk, indexB, indexC, productBits]
        · by_cases hs' : r = scratchA
          · subst r
            simp [σ₆, σ₅, σ₄, σ₃, resultStore, hs, indexB, indexC, scratchA, productBits]
          · simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, resultStore, hp, hj', hk', hs']
  have hlenA : (σ indexA).length = pa.length := by simp [hi]
  have hlenB : (σ₁ indexB).length = pb.length := by simp [σ₁, hj, indexB, indexC]
  have hlenK : (σ₄ indexC).length = pa.length + pb.length := by
    simp [σ₄, σ₃, productBits, indexC]
  have htime : (((2 * pa.length + 4 + 1 + (2 * pb.length + 4)) + 1 +
      (8 * pb.length + 3)) + 1 + (2 * (pa.length + pb.length + pc.length) + 14)) +
      1 + (2 * (pa.length + pb.length) + 5) + 1 + 2 =
        8 * pa.length + 16 * pb.length + 37 := by omega
  simpa only [program, start, done, hstore, hlenA, hlenB, hlenK, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeConvolutionStep
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeConvolutionRow

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

abbrev State := LoopState DecState TapeConvolutionStep.State

def program : TapeMultiProgram State :=
  loopCode (decProgram loop1) TapeConvolutionStep.program
    DecState.start TapeConvolutionStep.start decPositive

def start : State := loopTest DecState.start
def done : State := loopDone

def frame (σ : TapeStore) (remaining column : ℕ) (out : List Bool) : TapeStore :=
  fun r => if r = loop1 then List.replicate remaining true
    else if r = indexB then List.replicate column true
    else if r = productBits then out else σ r

@[simp] theorem frame_counter (σ : TapeStore) (n j : ℕ) (out : List Bool) :
    frame σ n j out loop1 = List.replicate n true := by simp [frame]

@[simp] theorem frame_index (σ : TapeStore) (n j : ℕ) (out : List Bool) :
    frame σ n j out indexB = List.replicate j true := by simp [frame, loop1, indexB]

@[simp] theorem frame_output (σ : TapeStore) (n j : ℕ) (out : List Bool) :
    frame σ n j out productBits = out := by simp [frame, loop1, indexB, productBits]

theorem update_counter (σ : TapeStore) (n n' j : ℕ) (out : List Bool) :
    Function.update (frame σ n j out) loop1 (List.replicate n' true) = frame σ n' j out := by
  funext r
  by_cases hr : r = loop1
  · subst r
    simp
  · simp [frame, Function.update, hr]

theorem resultStore_frame (σ : TapeStore) (n j : ℕ) (out out' : List Bool) :
    TapeConvolutionStep.resultStore (frame σ n j out) j out' = frame σ n (j + 1) out' := by
  funext r
  by_cases hr : r = indexB
  · subst r
    simp [TapeConvolutionStep.resultStore]
  · by_cases hp : r = productBits
    · subst r
      simp [TapeConvolutionStep.resultStore, indexB, productBits]
    · simp [TapeConvolutionStep.resultStore, Function.update, frame, hr, hp]

theorem runs_step (σ : TapeStore) (i j : ℕ)
    (hi : σ indexA = List.replicate i true) (hj : σ indexB = List.replicate j true)
    (hk : σ indexC = []) (hs : σ scratchA = [])
    (ha : i < (σ hashBits).length) (hb : j < (σ accumBits).length)
    (hc : i + j < (σ productBits).length) :
    RunsIn TapeConvolutionStep.program.step
      (cfg TapeConvolutionStep.start (storeTapes σ))
      (cfg TapeConvolutionStep.done (storeTapes
        (TapeConvolutionStep.resultStore σ j
          (xorListAt (σ productBits) (i + j)
            ((σ hashBits).getD i false && (σ accumBits).getD j false)))))
      (8 * i + 16 * j + 37) := by
  have h := TapeConvolutionStep.runs_step σ
    ((σ hashBits).take i) ((σ hashBits).drop (i + 1))
    ((σ accumBits).take j) ((σ accumBits).drop (j + 1))
    ((σ productBits).take (i + j)) ((σ productBits).drop (i + j + 1))
    ((σ hashBits).getD i false) ((σ accumBits).getD j false)
    ((σ productBits).getD (i + j) false)
    (by simpa only [TapeNaturalAccess.take_length _ _ ha] using hi)
    (by simpa only [TapeNaturalAccess.take_length _ _ hb] using hj) hk hs
    (TapeNaturalAccess.split _ _ ha) (TapeNaturalAccess.split _ _ hb)
    (TapeNaturalAccess.split _ _ hc)
    (by simp only [TapeNaturalAccess.take_length _ _ ha,
      TapeNaturalAccess.take_length _ _ hb, TapeNaturalAccess.take_length _ _ hc])
  simpa only [TapeNaturalAccess.take_length _ _ ha, TapeNaturalAccess.take_length _ _ hb,
    TapeNaturalAccess.xorListAt_eq_split _ _ hc] using h

theorem runs_row (σ : TapeStore) (a b : List Bool) (i j n : ℕ) (out : List Bool)
    (hA : σ hashBits = a) (hB : σ accumBits = b)
    (hI : σ indexA = List.replicate i true)
    (hK : σ indexC = []) (hS : σ scratchA = [])
    (hi : i < a.length) (hj : j + n ≤ b.length)
    (hsize : a.length + b.length ≤ out.length) :
    RunsIn program.step (cfg start (storeTapes (frame σ n j out)))
      (cfg done (storeTapes (frame σ 0 (j + n)
        (convolutionUpdateRow a b i (List.range' j n) out))))
      (n * (8 * a.length + 16 * b.length + 43) + 3) := by
  induction n generalizing j out with
  | zero =>
      have hd := decrement_empty loop1 (storeTapes (frame σ 0 j out)) (by
        simp [])
      have he := loop_exit (decProgram loop1) TapeConvolutionStep.program
        DecState.start TapeConvolutionStep.start decPositive hd rfl rfl
      simpa only [program, start, done, List.range'_zero, convolutionUpdateRow_nil,
        Nat.add_zero, Nat.zero_mul, Nat.zero_add] using he
  | succ n ih =>
      have hj' : j < b.length := by omega
      have hij : i + j < out.length := by omega
      let out' := xorListAt out (i + j) (a.getD i false && b.getD j false)
      have hd := decrement_cons loop1 (storeTapes (frame σ (n + 1) j out))
        (List.replicate n true) true (by simp [List.replicate_succ])
      have hd' : RunsIn (decProgram loop1).step
          (cfg DecState.start (storeTapes (frame σ (n + 1) j out)))
          (cfg (DecState.done true) (storeTapes (frame σ n j out))) 4 := by
        simpa only [← storeTapes_update, update_counter] using hd
      have hAf : frame σ n j out hashBits = a := by
        simp [frame, hA, hashBits, loop1, indexB, productBits]
      have hBf : frame σ n j out accumBits = b := by
        simp [frame, hB, accumBits, loop1, indexB, productBits]
      have ht := runs_step (frame σ n j out) i j
        (by simp [frame, hI, indexA, loop1, indexB, productBits])
        (by simp) (by simp [frame, hK, indexC, loop1, indexB, productBits])
        (by simp [frame, hS, scratchA, loop1, indexB, productBits])
        (by simpa [frame, hA, hashBits, loop1, indexB, productBits] using hi)
        (by simpa [frame, hB, accumBits, loop1, indexB, productBits] using hj')
        (by simpa using hij)
      have ht' : RunsIn TapeConvolutionStep.program.step
          (cfg TapeConvolutionStep.start (storeTapes (frame σ n j out)))
          (cfg TapeConvolutionStep.done (storeTapes (frame σ n (j + 1) out')))
          (8 * i + 16 * j + 37) := by
        simpa only [frame_output, hAf, hBf, resultStore_frame, out'] using ht
      have hit := loop_iter (decProgram loop1) TapeConvolutionStep.program
        DecState.start TapeConvolutionStep.start decPositive hd' rfl rfl ht' rfl
      have hit' := hit.mono (show 4 + 1 + (8 * i + 16 * j + 37) + 1 ≤
          8 * a.length + 16 * b.length + 43 by omega)
      have hrest := ih (j + 1) out' (by omega) (by simpa [out'] using hsize)
      have hall := hit'.trans hrest
      have htime : (8 * a.length + 16 * b.length + 43) +
          (n * (8 * a.length + 16 * b.length + 43) + 3) =
          (n + 1) * (8 * a.length + 16 * b.length + 43) + 3 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hindex : j + 1 + n = j + (n + 1) := by omega
      simpa only [program, start, done, List.range'_succ, convolutionUpdateRow_step,
        htime, hindex, out'] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeConvolutionRow
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeConvolutionRows

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

abbrev ReadState := TapeCopy.State ⊕ TapeConvolutionRow.State
abbrev ClearState := ReadState ⊕ TapeErase.State
abbrev BodyState := ClearState ⊕ IncState

def readProgram : TapeMultiProgram ReadState :=
  joinCode (TapeCopy.code ringDegree loop1) TapeConvolutionRow.program
    (fun _ => TapeConvolutionRow.start)

def clearProgram : TapeMultiProgram ClearState :=
  joinCode readProgram (TapeErase.code indexB) (fun _ => TapeErase.State.start)

def bodyProgram : TapeMultiProgram BodyState :=
  joinCode clearProgram (incProgram indexA) (fun _ => IncState.start)

def bodyStart : BodyState := .inl (.inl (.inl TapeCopy.State.start))
def bodyDone : BodyState := .inr IncState.done

def bodyResult (σ : TapeStore) (i : ℕ) (out : List Bool) : TapeStore :=
  Function.update (Function.update σ productBits out) indexA (List.replicate (i + 1) true)

theorem runs_body (σ : TapeStore) (a b out : List Bool) (i : ℕ)
    (hA : σ hashBits = a) (hB : σ accumBits = b)
    (hI : σ indexA = List.replicate i true) (hJ : σ indexB = [])
    (hCount : σ ringDegree = List.replicate b.length true) (hLoop : σ loop1 = [])
    (hK : σ indexC = []) (hS : σ scratchA = []) (hOut : σ productBits = out)
    (hi : i < a.length) (hsize : a.length + b.length ≤ out.length) :
    RunsIn bodyProgram.step (cfg bodyStart (storeTapes σ))
      (cfg bodyDone (storeTapes (bodyResult σ i
        (convolutionUpdateRow a b i (List.range' 0 b.length) out))))
      (b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 17) := by
  let out' := convolutionUpdateRow a b i (List.range' 0 b.length) out
  let ρ := TapeConvolutionRow.frame σ 0 b.length out'
  have hcopy := TapeStoreRuns.copy (by decide : ringDegree ≠ loop1) σ hLoop
  have hrow := TapeConvolutionRow.runs_row σ a b i 0 b.length out
    hA hB hI hK hS hi (by omega) hsize
  have hentry : TapeConvolutionRow.frame σ b.length 0 out =
      Function.update σ loop1 (σ ringDegree) := by
    funext r
    by_cases hl : r = loop1
    · subst r
      simp [hCount]
    · by_cases hj : r = indexB
      · subst r
        simp [TapeConvolutionRow.frame, hJ, loop1, indexB]
      · by_cases hp : r = productBits
        · subst r
          simp [TapeConvolutionRow.frame, hOut, productBits, loop1, indexB]
        · simp [TapeConvolutionRow.frame, Function.update, hl, hj, hp]
  have hrow' : RunsIn TapeConvolutionRow.program.step
      (cfg TapeConvolutionRow.start (storeTapes (Function.update σ loop1 (σ ringDegree))))
      (cfg TapeConvolutionRow.done (storeTapes ρ))
      (b.length * (8 * a.length + 16 * b.length + 43) + 3) := by
    simpa only [hentry, Nat.zero_add, ρ, out'] using hrow
  have hread := join_runs (TapeCopy.code ringDegree loop1) TapeConvolutionRow.program
    (fun _ => TapeConvolutionRow.start) hcopy rfl hrow'
  have herase := TapeStoreRuns.erase indexB ρ
  have hclean : Function.update ρ indexB [] = Function.update σ productBits out' := by
    funext r
    by_cases hj : r = indexB
    · subst r
      simp [Function.update, hJ, indexB, productBits]
    · by_cases hl : r = loop1
      · subst r
        simp [ρ, Function.update, hLoop, loop1, indexB, productBits]
      · by_cases hp : r = productBits
        · subst r
          simp [ρ, Function.update, productBits, indexB]
        · simp [ρ, TapeConvolutionRow.frame, Function.update, hj, hl, hp]
  have hclear := join_runs readProgram (TapeErase.code indexB)
    (fun _ => TapeErase.State.start) hread rfl herase
  have hinc := increment indexA (storeTapes (Function.update σ productBits out')) i (by
    simp [hI, counterTape, indexA, productBits])
  have hinc' : RunsIn (incProgram indexA).step
      (cfg IncState.start (storeTapes (Function.update ρ indexB [])))
      (cfg IncState.done (storeTapes (bodyResult σ i out'))) 2 := by
    simpa only [hclean, bodyResult, storeTapes_update, counterTape] using hinc
  have hall := join_runs clearProgram (incProgram indexA) (fun _ => IncState.start)
    hclear rfl hinc'
  have hlenCopy : (σ ringDegree).length = b.length := by simp [hCount]
  have hlenErase : (ρ indexB).length = b.length := by simp [ρ]
  have htime : (2 * b.length + 4 + 1 +
      (b.length * (8 * a.length + 16 * b.length + 43) + 3)) + 1 +
      (2 * b.length + 5) + 1 + 2 =
      b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 17 := by omega
  simpa only [bodyProgram, bodyStart, bodyDone, hlenCopy, hlenErase, htime, out'] using hall

@[simp] theorem body_done (h : TapeHeads) : bodyProgram bodyDone h = none := rfl

abbrev State := LoopState DecState BodyState

def program : TapeMultiProgram State :=
  loopCode (decProgram loop0) bodyProgram DecState.start bodyStart decPositive

def start : State := loopTest DecState.start
def done : State := loopDone

def frame (σ : TapeStore) (remaining row : ℕ) (out : List Bool) : TapeStore :=
  fun r => if r = loop0 then List.replicate remaining true
    else if r = indexA then List.replicate row true
    else if r = productBits then out else σ r

@[simp] theorem frame_counter (σ : TapeStore) (n i : ℕ) (out : List Bool) :
    frame σ n i out loop0 = List.replicate n true := by simp [frame]

@[simp] theorem frame_index (σ : TapeStore) (n i : ℕ) (out : List Bool) :
    frame σ n i out indexA = List.replicate i true := by simp [frame, loop0, indexA]

@[simp] theorem frame_output (σ : TapeStore) (n i : ℕ) (out : List Bool) :
    frame σ n i out productBits = out := by simp [frame, loop0, indexA, productBits]

theorem update_counter (σ : TapeStore) (n n' i : ℕ) (out : List Bool) :
    Function.update (frame σ n i out) loop0 (List.replicate n' true) = frame σ n' i out := by
  funext r
  by_cases hr : r = loop0
  · subst r
    simp
  · simp [frame, Function.update, hr]

theorem bodyResult_frame (σ : TapeStore) (n i : ℕ) (out out' : List Bool) :
    bodyResult (frame σ n i out) i out' = frame σ n (i + 1) out' := by
  funext r
  by_cases hr : r = indexA
  · subst r
    simp [bodyResult]
  · by_cases hp : r = productBits
    · subst r
      simp [bodyResult, indexA, productBits]
    · simp [bodyResult, Function.update, frame, hr, hp]

theorem runs_rows (σ : TapeStore) (a b : List Bool) (i n : ℕ) (out : List Bool)
    (hA : σ hashBits = a) (hB : σ accumBits = b)
    (hJ : σ indexB = []) (hCount : σ ringDegree = List.replicate b.length true)
    (hLoop : σ loop1 = []) (hK : σ indexC = []) (hS : σ scratchA = [])
    (hi : i + n ≤ a.length) (hsize : a.length + b.length ≤ out.length) :
    RunsIn program.step (cfg start (storeTapes (frame σ n i out)))
      (cfg done (storeTapes (frame σ 0 (i + n)
        (convolutionUpdateRows a b (List.range' i n) out))))
      (n * (b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 23) + 3) := by
  induction n generalizing i out with
  | zero =>
      have hd := decrement_empty loop0 (storeTapes (frame σ 0 i out)) (by simp [])
      have he := loop_exit (decProgram loop0) bodyProgram DecState.start bodyStart
        decPositive hd rfl rfl
      simpa only [program, start, done, List.range'_zero, convolutionUpdateRows_nil,
        Nat.add_zero, Nat.zero_mul, Nat.zero_add] using he
  | succ n ih =>
      have hi' : i < a.length := by omega
      let out' := convolutionUpdateRow a b i (List.range' 0 b.length) out
      have hd := decrement_cons loop0 (storeTapes (frame σ (n + 1) i out))
        (List.replicate n true) true (by simp [List.replicate_succ])
      have hd' : RunsIn (decProgram loop0).step
          (cfg DecState.start (storeTapes (frame σ (n + 1) i out)))
          (cfg (DecState.done true) (storeTapes (frame σ n i out))) 4 := by
        simpa only [← storeTapes_update, update_counter] using hd
      have hb := runs_body (frame σ n i out) a b out i
        (by simp [frame, hA, hashBits, loop0, indexA, productBits])
        (by simp [frame, hB, accumBits, loop0, indexA, productBits])
        (by simp) (by simp [frame, hJ, indexB, loop0, indexA, productBits])
        (by simp [frame, hCount, ringDegree, loop0, indexA, productBits])
        (by simp [frame, hLoop, loop1, loop0, indexA, productBits])
        (by simp [frame, hK, indexC, loop0, indexA, productBits])
        (by simp [frame, hS, scratchA, loop0, indexA, productBits])
        (by simp) hi' hsize
      have hb' : RunsIn bodyProgram.step
          (cfg bodyStart (storeTapes (frame σ n i out)))
          (cfg bodyDone (storeTapes (frame σ n (i + 1) out')))
          (b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 17) := by
        simpa only [bodyResult_frame, out'] using hb
      have hit := loop_iter (decProgram loop0) bodyProgram DecState.start bodyStart
        decPositive hd' rfl rfl hb' rfl
      have hrest := ih (i + 1) out' (by omega) (by simpa [out'] using hsize)
      have hall := hit.trans hrest
      have htime : 4 + 1 +
          (b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 17) + 1 +
          (n * (b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 23) + 3) =
          (n + 1) * (b.length * (8 * a.length + 16 * b.length + 43) + 4 * b.length + 23) + 3 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hindex : i + 1 + n = i + (n + 1) := by omega
      simpa only [program, start, done, List.range'_succ, convolutionUpdateRows_step,
        ← List.range_eq_range', htime, hindex, out'] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeConvolutionRows
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeConvolutionPrepare

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

abbrev CopyState := TapeCopy.State ⊕ TapeCopy.State
abbrev AddState := CopyState ⊕ TapeArithmetic.AddState
abbrev FillState := AddState ⊕ TapeFill.FillState
abbrev State := FillState ⊕ TapeCopy.State

def copies : TapeMultiProgram CopyState :=
  joinCode (TapeCopy.code ringDegree loop0) (TapeCopy.code ringDegree loop1)
    (fun _ => TapeCopy.State.start)

def addition : TapeMultiProgram AddState :=
  joinCode copies (addProgram loop1 loop0) (fun _ => addStart)

def filling : TapeMultiProgram FillState :=
  joinCode addition (TapeFill.fillProgram loop0 productBits false) (fun _ => TapeFill.fillStart)

def program : TapeMultiProgram State :=
  joinCode filling (TapeCopy.code ringDegree loop0) (fun _ => TapeCopy.State.start)

def start : State := .inl (.inl (.inl (.inl TapeCopy.State.start)))
def done : State := .inr TapeCopy.State.done

theorem runs_prepare (σ : TapeStore) (r : ℕ)
    (hr : σ ringDegree = List.replicate r true)
    (hL0 : σ loop0 = []) (hL1 : σ loop1 = [])
    (hI : σ indexA = []) (hOut : σ productBits = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (TapeConvolutionRows.frame σ r 0 (List.replicate (r + r) false))))
      (30 * r + 22) := by
  let σ₁ := Function.update σ loop0 (σ ringDegree)
  let σ₂ := Function.update σ₁ loop1 (σ₁ ringDegree)
  let σ₃ := Function.update (Function.update σ₂ loop1 []) loop0 (List.replicate (r + r) true)
  let σ₄ := Function.update (Function.update σ₃ loop0 []) productBits (List.replicate (r + r) false)
  let σ₅ := Function.update σ₄ loop0 (σ₄ ringDegree)
  have hcopy0 := TapeStoreRuns.copy (by decide : ringDegree ≠ loop0) σ hL0
  have hcopy1 := TapeStoreRuns.copy (by decide : ringDegree ≠ loop1) σ₁ (by
    simp [σ₁, hL1, loop0, loop1])
  have hc := join_runs (TapeCopy.code ringDegree loop0) (TapeCopy.code ringDegree loop1)
    (fun _ => TapeCopy.State.start) hcopy0 rfl hcopy1
  have hadd := TapeStoreRuns.add (by decide : loop1 ≠ loop0) σ₂ r r
    (by simp [σ₂, σ₁, hr, ringDegree, loop0])
    (by simp [σ₂, σ₁, hr, loop0, loop1])
  have ha := join_runs copies (addProgram loop1 loop0) (fun _ => addStart) hc rfl hadd
  have hfill := TapeStoreRuns.fill (by decide : loop0 ≠ productBits) false σ₃ (r + r) (by
    simp [σ₃])
  have hfill' : RunsIn (TapeFill.fillProgram loop0 productBits false).step
      (cfg TapeFill.fillStart (storeTapes σ₃)) (cfg TapeFill.fillDone (storeTapes σ₄))
      (8 * (r + r) + 3) := by
    simpa only [σ₄, show σ₃ productBits = [] by
      simp [σ₃, σ₂, σ₁, hOut, loop0, loop1, productBits], List.append_nil] using hfill
  have hf := join_runs addition (TapeFill.fillProgram loop0 productBits false)
    (fun _ => TapeFill.fillStart) ha rfl hfill'
  have hlast := TapeStoreRuns.copy (by decide : ringDegree ≠ loop0) σ₄ (by
    simp [σ₄, loop0, productBits])
  have hall := join_runs filling (TapeCopy.code ringDegree loop0)
    (fun _ => TapeCopy.State.start) hf rfl hlast
  have hstore : σ₅ = TapeConvolutionRows.frame σ r 0 (List.replicate (r + r) false) := by
    funext k
    by_cases h0 : k = loop0
    · subst k
      simp [σ₅, σ₄, σ₃, σ₂, σ₁, hr, ringDegree, loop0, loop1, productBits]
    · by_cases hp : k = productBits
      · subst k
        simp [σ₅, σ₄, TapeConvolutionRows.frame, loop0, indexA, productBits]
      · by_cases h1 : k = loop1
        · subst k
          simp [σ₅, σ₄, σ₃, TapeConvolutionRows.frame, hL1, loop0, loop1, indexA, productBits]
        · by_cases hi : k = indexA
          · subst k
            simp [σ₅, σ₄, σ₃, σ₂, σ₁, TapeConvolutionRows.frame, hI,
              loop0, loop1, indexA, productBits]
          · simp [σ₅, σ₄, σ₃, σ₂, σ₁, TapeConvolutionRows.frame, h0, hp, h1, hi]
  have hl0 : (σ ringDegree).length = r := by simp [hr]
  have hl1 : (σ₁ ringDegree).length = r := by simp [σ₁, hr, ringDegree, loop0]
  have hlf : (σ₄ ringDegree).length = r := by
    simp [σ₄, σ₃, σ₂, σ₁, hr, ringDegree, loop0, loop1, productBits]
  have htime : ((2 * r + 4 + 1 + (2 * r + 4)) + 1 + (8 * r + 3)) +
      1 + (8 * (r + r) + 3) + 1 + (2 * r + 4) = 30 * r + 22 := by omega
  dsimp only [σ₅] at hstore
  simpa only [program, start, done, hstore, hl0, hl1, hlf, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeConvolutionPrepare
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeConvolve

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

abbrev WorkState := TapeConvolutionPrepare.State ⊕ TapeConvolutionRows.State
abbrev State := WorkState ⊕ TapeErase.State

def work : TapeMultiProgram WorkState :=
  joinCode TapeConvolutionPrepare.program TapeConvolutionRows.program
    (fun _ => TapeConvolutionRows.start)

def program : TapeMultiProgram State :=
  joinCode work (TapeErase.code indexA) (fun _ => TapeErase.State.start)

def start : State := .inl (.inl TapeConvolutionPrepare.start)
def done : State := .inr TapeErase.State.done

def cost (r : ℕ) : ℕ := r * (r * (24 * r + 43) + 4 * r + 23) + 32 * r + 32

theorem runs_convolve (σ : TapeStore) (a b : List Bool) (r : ℕ)
    (hA : σ hashBits = a) (hB : σ accumBits = b)
    (hlenA : a.length = r) (hlenB : b.length = r)
    (hCount : σ ringDegree = List.replicate r true)
    (hL0 : σ loop0 = []) (hL1 : σ loop1 = [])
    (hI : σ indexA = []) (hJ : σ indexB = [])
    (hK : σ indexC = []) (hS : σ scratchA = []) (hOut : σ productBits = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ productBits (convolveBitLists a b))))
      (cost r) := by
  have hp := TapeConvolutionPrepare.runs_prepare σ r hCount hL0 hL1 hI hOut
  have hr := TapeConvolutionRows.runs_rows σ a b 0 r (List.replicate (r + r) false)
    hA hB hJ (by simpa only [hlenB] using hCount) hL1 hK hS (by omega) (by simp [hlenA, hlenB])
  have hout : convolutionUpdateRows a b (List.range' 0 r) (List.replicate (r + r) false) =
      convolveBitLists a b := by
    rw [← convolveByUpdates_eq]
    simp only [convolveByUpdates, hlenA, hlenB, List.range_eq_range']
  have hr' : RunsIn TapeConvolutionRows.program.step
      (cfg TapeConvolutionRows.start
        (storeTapes (TapeConvolutionRows.frame σ r 0 (List.replicate (r + r) false))))
      (cfg TapeConvolutionRows.done
        (storeTapes (TapeConvolutionRows.frame σ 0 r (convolveBitLists a b))))
      (r * (r * (8 * r + 16 * r + 43) + 4 * r + 23) + 3) := by
    simpa only [Nat.zero_add, hout, hlenA, hlenB] using hr
  have hw := join_runs TapeConvolutionPrepare.program TapeConvolutionRows.program
    (fun _ => TapeConvolutionRows.start) hp rfl hr'
  let ρ := TapeConvolutionRows.frame σ 0 r (convolveBitLists a b)
  have he := TapeStoreRuns.erase indexA ρ
  have hall := join_runs work (TapeErase.code indexA) (fun _ => TapeErase.State.start) hw rfl he
  have hframe : Function.update ρ indexA [] = Function.update σ productBits (convolveBitLists a b) := by
    funext k
    by_cases hi : k = indexA
    · subst k
      simp [hI, indexA, productBits]
    · by_cases hl : k = loop0
      · subst k
        simp [ρ, Function.update, hL0, indexA, loop0, productBits]
      · by_cases hp : k = productBits
        · subst k
          simp [ρ, Function.update, indexA, productBits]
        · simp [ρ, TapeConvolutionRows.frame, Function.update, hi, hl, hp]
  have hlen : (ρ indexA).length = r := by simp [ρ]
  have hlinear : 8 * r + 16 * r + 43 = 24 * r + 43 := by omega
  have htime : (30 * r + 22 + 1 +
      (r * (r * (8 * r + 16 * r + 43) + 4 * r + 23) + 3)) + 1 + (2 * r + 5) = cost r := by
    rw [hlinear]
    unfold cost
    omega
  simpa only [program, start, done, hframe, hlen, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeConvolve
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeRemainderSetup

open TapeMultiProgram TapeRouting TapeRegister

def preparedStore (σ : TapeStore) (r s : ℕ) : TapeStore :=
  Function.update (Function.update (Function.update σ
    indexB (List.replicate (s + r) true)) indexC (List.replicate s true))
    loop1 (List.replicate r true)

def clearIndices (σ : TapeStore) : TapeStore :=
  Function.update (Function.update (Function.update σ indexA []) indexB []) indexC []

@[simp] theorem preparedStore_indexB (σ : TapeStore) (r s : ℕ) :
    preparedStore σ r s indexB = List.replicate (s + r) true := by
  simp [preparedStore, indexB, indexC, loop1]

@[simp] theorem preparedStore_indexC (σ : TapeStore) (r s : ℕ) :
    preparedStore σ r s indexC = List.replicate s true := by
  simp [preparedStore, indexC, loop1]

@[simp] theorem preparedStore_loop1 (σ : TapeStore) (r s : ℕ) :
    preparedStore σ r s loop1 = List.replicate r true := by
  simp [preparedStore]

theorem preparedStore_other (σ : TapeStore) (r s : ℕ) (q : TapeRegister)
    (hB : q ≠ indexB) (hC : q ≠ indexC) (hL : q ≠ loop1) :
    preparedStore σ r s q = σ q := by
  simp [preparedStore, Function.update, hB, hC, hL]

@[simp] theorem clearIndices_indexA (σ : TapeStore) : clearIndices σ indexA = [] := by
  simp [clearIndices, indexA, indexB, indexC]

@[simp] theorem clearIndices_indexB (σ : TapeStore) : clearIndices σ indexB = [] := by
  simp [clearIndices, indexB, indexC]

@[simp] theorem clearIndices_indexC (σ : TapeStore) : clearIndices σ indexC = [] := by
  simp [clearIndices]

theorem clearIndices_other (σ : TapeStore) (q : TapeRegister)
    (hA : q ≠ indexA) (hB : q ≠ indexB) (hC : q ≠ indexC) :
    clearIndices σ q = σ q := by
  simp [clearIndices, Function.update, hA, hB, hC]

abbrev SetupState := TapeCopy.State ⊕ (TapeCopy.State ⊕
  (TapeCopyAdd.State ⊕ TapeCopy.State))

def setupProgram : TapeMultiProgram SetupState :=
  joinCode (TapeCopy.code loop0 indexB)
    (joinCode (TapeCopy.code loop0 indexC)
      (joinCode (TapeCopyAdd.program ringDegree scratchA indexB)
        (TapeCopy.code ringDegree loop1) (fun _ => TapeCopy.State.start))
      (fun _ => .inl TapeCopyAdd.start))
    (fun _ => .inl TapeCopy.State.start)

def setupStart : SetupState := .inl .start
def setupDone : SetupState := .inr (.inr (.inr .done))

@[simp] theorem setupProgram_done (h : TapeHeads) :
    setupProgram setupDone h = none := rfl

theorem runs_setup (σ : TapeStore) (r s : ℕ)
    (hLoop0 : σ loop0 = List.replicate s true)
    (hDegree : σ ringDegree = List.replicate r true)
    (hLoop1 : σ loop1 = []) (_hA : σ indexA = [])
    (hB : σ indexB = []) (hC : σ indexC = []) (hScratch : σ scratchA = []) :
    RunsIn setupProgram.step (cfg setupStart (storeTapes σ))
      (cfg setupDone (storeTapes (preparedStore σ r s))) (4 * s + 12 * r + 23) := by
  let τB := Function.update σ indexB (List.replicate s true)
  let τC := Function.update τB indexC (List.replicate s true)
  let τD := Function.update τC indexB (List.replicate (s + r) true)
  let τL := Function.update τD loop1 (List.replicate r true)
  have hfirst : RunsIn (TapeCopy.code loop0 indexB).step
      (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes τB)) (2 * s + 4) := by
    simpa only [hLoop0, List.length_replicate] using
      TapeStoreRuns.copy (show loop0 ≠ indexB by decide) σ hB
  have hLoop0B : τB loop0 = List.replicate s true := by
    simp [τB, hLoop0, loop0, indexB]
  have hsecond : RunsIn (TapeCopy.code loop0 indexC).step
      (cfg TapeCopy.State.start (storeTapes τB))
      (cfg TapeCopy.State.done (storeTapes τC)) (2 * s + 4) := by
    have h := TapeStoreRuns.copy (show loop0 ≠ indexC by decide) τB
      (by simp [τB, hC, indexB, indexC])
    simpa only [hLoop0B, List.length_replicate] using h
  have hthird : RunsIn (TapeCopyAdd.program ringDegree scratchA indexB).step
      (cfg TapeCopyAdd.start (storeTapes τC))
      (cfg TapeCopyAdd.done (storeTapes τD)) (10 * r + 8) := by
    exact TapeCopyAdd.runs_add (by decide) (by decide) τC r s
      (by simp [τC, τB, hDegree, ringDegree, indexB, indexC])
      (by simp [τC, τB, indexB, indexC])
      (by simp [τC, τB, hScratch, scratchA, indexB, indexC])
  have hDegreeD : τD ringDegree = List.replicate r true := by
    simp [τD, τC, τB, hDegree, ringDegree, indexB, indexC]
  have hfourth : RunsIn (TapeCopy.code ringDegree loop1).step
      (cfg TapeCopy.State.start (storeTapes τD))
      (cfg TapeCopy.State.done (storeTapes τL)) (2 * r + 4) := by
    have h := TapeStoreRuns.copy (show ringDegree ≠ loop1 by decide) τD
      (by simp [τD, τC, τB, hLoop1, loop1, indexB, indexC])
    simpa only [hDegreeD, List.length_replicate] using h
  have hlast := join_runs (TapeCopyAdd.program ringDegree scratchA indexB)
    (TapeCopy.code ringDegree loop1) (fun _ => TapeCopy.State.start)
    hthird rfl hfourth
  have hrest := join_runs (TapeCopy.code loop0 indexC)
    (joinCode (TapeCopyAdd.program ringDegree scratchA indexB)
      (TapeCopy.code ringDegree loop1) (fun _ => TapeCopy.State.start))
    (fun _ => Sum.inl TapeCopyAdd.start) hsecond rfl hlast
  have hall := join_runs (TapeCopy.code loop0 indexB)
    (joinCode (TapeCopy.code loop0 indexC)
      (joinCode (TapeCopyAdd.program ringDegree scratchA indexB)
        (TapeCopy.code ringDegree loop1) (fun _ => TapeCopy.State.start))
      (fun _ => Sum.inl TapeCopyAdd.start))
    (fun _ => Sum.inl TapeCopy.State.start) hfirst rfl hrest
  have houtput : τL = preparedStore σ r s := by
    funext q
    by_cases hL : q = loop1
    · subst q
      simp [τL, preparedStore]
    · by_cases hC' : q = indexC
      · subst q
        simp [τL, τD, τC, τB, preparedStore, loop1, indexB, indexC]
      · by_cases hB' : q = indexB
        · subst q
          simp [τL, τD, τC, τB, preparedStore, loop1, indexB, indexC]
        · simp [τL, τD, τC, τB, preparedStore, Function.update, hL, hC', hB']
  have htime : (2 * s + 4) + 1 +
      ((2 * s + 4) + 1 + ((10 * r + 8) + 1 + (2 * r + 4))) =
      4 * s + 12 * r + 23 := by omega
  simpa only [setupProgram, setupStart, setupDone, houtput, htime] using hall

abbrev CleanupState := TapeErase.State ⊕ (TapeErase.State ⊕ TapeErase.State)

def cleanupProgram : TapeMultiProgram CleanupState :=
  joinCode (TapeErase.code indexA)
    (joinCode (TapeErase.code indexB) (TapeErase.code indexC)
      (fun _ => TapeErase.State.start))
    (fun _ => .inl TapeErase.State.start)

def cleanupStart : CleanupState := .inl .start
def cleanupDone : CleanupState := .inr (.inr .done)

@[simp] theorem cleanupProgram_done (h : TapeHeads) :
    cleanupProgram cleanupDone h = none := rfl

theorem runs_cleanup (σ : TapeStore) (r s : ℕ)
    (hA : σ indexA = List.replicate r true)
    (hB : σ indexB = List.replicate (s + r) true)
    (hC : σ indexC = List.replicate (s + r) true) :
    RunsIn cleanupProgram.step (cfg cleanupStart (storeTapes σ))
      (cfg cleanupDone (storeTapes (clearIndices σ))) (4 * s + 6 * r + 17) := by
  let τA := Function.update σ indexA []
  let τB := Function.update τA indexB []
  have hfirst : RunsIn (TapeErase.code indexA).step
      (cfg TapeErase.State.start (storeTapes σ))
      (cfg TapeErase.State.done (storeTapes τA)) (2 * r + 5) := by
    simpa only [hA, List.length_replicate] using TapeStoreRuns.erase indexA σ
  have hB' : τA indexB = List.replicate (s + r) true := by
    simp [τA, hB, indexA, indexB]
  have hsecond : RunsIn (TapeErase.code indexB).step
      (cfg TapeErase.State.start (storeTapes τA))
      (cfg TapeErase.State.done (storeTapes τB)) (2 * (s + r) + 5) := by
    simpa only [hB', List.length_replicate] using TapeStoreRuns.erase indexB τA
  have hC' : τB indexC = List.replicate (s + r) true := by
    simp [τB, τA, hC, indexA, indexB, indexC]
  have hthird : RunsIn (TapeErase.code indexC).step
      (cfg TapeErase.State.start (storeTapes τB))
      (cfg TapeErase.State.done (storeTapes (clearIndices σ))) (2 * (s + r) + 5) := by
    have hclear : Function.update τB indexC [] = clearIndices σ := rfl
    simpa only [hC', List.length_replicate, hclear] using TapeStoreRuns.erase indexC τB
  have hrest := join_runs (TapeErase.code indexB) (TapeErase.code indexC)
    (fun _ => TapeErase.State.start) hsecond rfl hthird
  have hall := join_runs (TapeErase.code indexA)
    (joinCode (TapeErase.code indexB) (TapeErase.code indexC)
      (fun _ => TapeErase.State.start))
    (fun _ => Sum.inl TapeErase.State.start) hfirst rfl hrest
  have htime : (2 * r + 5) + 1 +
      ((2 * (s + r) + 5) + 1 + (2 * (s + r) + 5)) =
      4 * s + 6 * r + 17 := by omega
  simpa only [cleanupProgram, cleanupStart, cleanupDone, htime] using hall

end TapeRemainderSetup
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeCancelStep

open TapeMultiProgram TapeRouting TapeUnary TapeProductTerm TapeRegister

abbrev ReadState := TapeArray.State ⊕ (Bool × TapeArray.State)
abbrev FirstState := ReadState ⊕ IncState
abbrev State := FirstState ⊕ IncState

def readProgram (v : Bool) : TapeMultiProgram ReadState :=
  joinCode (TapeArray.code indexA polyBits id)
    (carryCode fun b : Bool => TapeArray.code indexC productBits
      (fun old => Bool.xor old (v && b)))
    (fun q => (readFlag q, TapeArray.State.start))

def firstProgram (v : Bool) : TapeMultiProgram FirstState :=
  joinCode (readProgram v) (incProgram indexA) (fun _ => IncState.start)

def program (v : Bool) : TapeMultiProgram State :=
  joinCode (firstProgram v) (incProgram indexC) (fun _ => IncState.start)

def start : State := .inl (.inl (.inl TapeArray.State.start))
def done : State := .inr IncState.done

def resultStore (σ : TapeStore) (j k : ℕ) (out : List Bool) : TapeStore :=
  Function.update (Function.update (Function.update σ productBits out)
    indexA (List.replicate (j + 1) true)) indexC (List.replicate (k + 1) true)

theorem runs_step (v : Bool) (σ : TapeStore) (j k : ℕ)
    (hA : σ indexA = List.replicate j true)
    (hC : σ indexC = List.replicate k true)
    (hj : j < (σ polyBits).length) (hk : k < (σ productBits).length) :
    RunsIn (program v).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (resultStore σ j k
        (xorListAt (σ productBits) k (v && (σ polyBits).getD j false)))))
      (2 * j + 2 * k + 15) := by
  let b := (σ polyBits).getD j false
  let out := xorListAt (σ productBits) k (v && b)
  let σ₁ := Function.update σ productBits out
  let σ₂ := Function.update σ₁ indexA (List.replicate (j + 1) true)
  have hr := TapeNaturalAccess.read indexA polyBits (by decide) σ j hA hj
  have hx := TapeNaturalAccess.xorAt indexC productBits (by decide) σ k (v && b) hC hk
  have hxc := carry_runs
    (fun b : Bool => TapeArray.code indexC productBits (fun old => Bool.xor old (v && b))) b hx
  have hread := join_runs (TapeArray.code indexA polyBits id)
    (carryCode fun b : Bool => TapeArray.code indexC productBits
      (fun old => Bool.xor old (v && b)))
    (fun q => (readFlag q, TapeArray.State.start)) hr rfl hxc
  have ha := increment indexA (storeTapes σ₁) j (by
    simp [σ₁, counterTape, hA, indexA, productBits])
  have ha' : RunsIn (incProgram indexA).step
      (cfg IncState.start (storeTapes σ₁)) (cfg IncState.done (storeTapes σ₂)) 2 := by
    simpa only [σ₂, storeTapes_update, counterTape] using ha
  have hfirst := join_runs (readProgram v) (incProgram indexA)
    (fun _ => IncState.start) hread rfl ha'
  have hc := increment indexC (storeTapes σ₂) k (by
    simp [σ₂, σ₁, counterTape, hC, indexC, indexA, productBits])
  have hc' : RunsIn (incProgram indexC).step
      (cfg IncState.start (storeTapes σ₂))
      (cfg IncState.done (storeTapes (resultStore σ j k out))) 2 := by
    simpa only [resultStore, σ₂, σ₁, storeTapes_update, counterTape] using hc
  have hall := join_runs (firstProgram v) (incProgram indexC)
    (fun _ => IncState.start) hfirst rfl hc'
  have ht : (2 * j + 4 + 1 + (2 * k + 4)) + 1 + 2 + 1 + 2 =
      2 * j + 2 * k + 15 := by omega
  simpa only [program, start, done, out, b, ht] using hall

@[simp] theorem program_done (v : Bool) (h : TapeHeads) : program v done h = none := rfl

end TapeCancelStep
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

def modulusUpdateLoop (p : List Bool) (v : Bool) (shift : ℕ) : ℕ → List Bool → List Bool
  | 0, c => c
  | j + 1, c => xorListAt (modulusUpdateLoop p v shift j c)
      (shift + j) (v && p.getD j false)

@[simp] theorem modulusUpdateLoop_zero (p : List Bool) (v : Bool)
    (shift : ℕ) (c : List Bool) : modulusUpdateLoop p v shift 0 c = c := rfl

theorem modulusUpdateLoop_step (p : List Bool) (v : Bool) (shift j : ℕ) (c : List Bool) :
    modulusUpdateLoop p v shift (j + 1) c =
      xorListAt (modulusUpdateLoop p v shift j c) (shift + j) (v && p.getD j false) := rfl

@[simp] theorem modulusUpdateLoop_length (p : List Bool) (v : Bool)
    (shift j : ℕ) (c : List Bool) :
    (modulusUpdateLoop p v shift j c).length = c.length := by
  induction j with
  | zero => rfl
  | succ j ih => rw [modulusUpdateLoop_step, xorListAt_length, ih]

theorem modulusUpdateLoop_getD (p : List Bool) (v : Bool) (shift j : ℕ)
    (c : List Bool) (hbound : shift + j ≤ c.length) (k : ℕ) :
    (modulusUpdateLoop p v shift j c).getD k false =
      Bool.xor (c.getD k false)
        (if shift ≤ k ∧ k < shift + j then v && p.getD (k - shift) false else false) := by
  revert hbound
  induction j with
  | zero =>
      intro hbound
      have hk : ¬(shift ≤ k ∧ k < shift + 0) := by omega
      simp only [modulusUpdateLoop_zero, ite_eq_right hk, Bool.xor_false]
  | succ j ih =>
      intro hbound
      have hj : shift + j < (modulusUpdateLoop p v shift j c).length := by
        rw [modulusUpdateLoop_length]
        omega
      rw [modulusUpdateLoop_step, xorListAt_getD _ _ _ hj k, ih (by omega)]
      by_cases he : shift + j = k
      · have hprev : ¬(shift ≤ k ∧ k < shift + j) := by omega
        have hnext : shift ≤ k ∧ k < shift + (j + 1) := by omega
        have hsub : k - shift = j := by omega
        simp [he, hnext, hsub]
      · have hrange : (shift ≤ k ∧ k < shift + (j + 1)) ↔
            (shift ≤ k ∧ k < shift + j) := by omega
        simp only [ite_eq_right he, Bool.xor_false, hrange]

theorem modulusUpdateLoop_above (p : List Bool) (v : Bool) (shift j : ℕ)
    (c : List Bool) (hbound : shift + j ≤ c.length) (k : ℕ) (hk : shift + j ≤ k) :
    (modulusUpdateLoop p v shift j c).getD k false = c.getD k false := by
  rw [modulusUpdateLoop_getD p v shift j c hbound k]
  have hnot : ¬(shift ≤ k ∧ k < shift + j) := by omega
  simp only [ite_eq_right hnot, Bool.xor_false]

theorem modulusUpdateLoop_high (p : List Bool) (v : Bool) (shift : ℕ)
    (c : List Bool) (hbound : shift + p.length ≤ c.length) :
    (modulusUpdateLoop p v shift p.length c).getD (shift + p.length) false =
      c.getD (shift + p.length) false :=
  modulusUpdateLoop_above p v shift p.length c hbound _ le_rfl

def cancelByUpdates (p c : List Bool) (shift : ℕ) : List Bool :=
  (modulusUpdateLoop p (c.getD (shift + p.length) false) shift p.length c).set
    (shift + p.length) false

@[simp] theorem cancelByUpdates_length (p c : List Bool) (shift : ℕ) :
    (cancelByUpdates p c shift).length = c.length := by
  simp [cancelByUpdates]

theorem cancelByUpdates_getD (p c : List Bool) (shift : ℕ)
    (hbound : shift + p.length < c.length) (k : ℕ) :
    (cancelByUpdates p c shift).getD k false =
      if shift + p.length = k then false else
        Bool.xor (c.getD k false)
          (if shift ≤ k ∧ k < shift + p.length then
            c.getD (shift + p.length) false && p.getD (k - shift) false else false) := by
  have ht : shift + p.length <
      (modulusUpdateLoop p (c.getD (shift + p.length) false) shift p.length c).length := by
    simpa only [modulusUpdateLoop_length] using hbound
  by_cases he : shift + p.length = k
  · subst k
    rw [ite_eq_left rfl]
    unfold cancelByUpdates
    exact List.getD_eq_getElem?_getD.trans
      (congrArg (fun o : Option Bool => o.getD false)
        (List.getElem?_set_self (a := false) ht))
  · have hset : (cancelByUpdates p c shift).getD k false =
        (modulusUpdateLoop p (c.getD (shift + p.length) false) shift p.length c).getD k false := by
      simp only [cancelByUpdates, List.getD_eq_getElem?_getD, List.getElem?_set_ne he]
    rw [hset, modulusUpdateLoop_getD _ _ _ _ _ (Nat.le_of_lt hbound) k, ite_eq_right he]

def reduceByUpdates (p : List Bool) : ℕ → List Bool → List Bool
  | 0, c => c
  | s + 1, c => reduceByUpdates p s (cancelByUpdates p c s)

@[simp] theorem reduceByUpdates_zero (p c : List Bool) : reduceByUpdates p 0 c = c := rfl

theorem reduceByUpdates_step (p c : List Bool) (s : ℕ) :
    reduceByUpdates p (s + 1) c = reduceByUpdates p s (cancelByUpdates p c s) := rfl

@[simp] theorem reduceByUpdates_length (p c : List Bool) (s : ℕ) :
    (reduceByUpdates p s c).length = c.length := by
  induction s generalizing c with
  | zero => rfl
  | succ s ih => rw [reduceByUpdates_step, ih, cancelByUpdates_length]

theorem cancelStep_read {r m : ℕ} (p : BitWord r) (a : BitWord m)
    (shift : ℕ) (hbound : shift + r < m) (i : Fin m) :
    cancelStep p (shift + r) a i =
      if shift + r = i.val then false else
        Bool.xor (a i)
          (if shift ≤ i.val ∧ i.val < shift + r then
            a ⟨shift + r, hbound⟩ && wordGet p (i.val - shift) else false) := by
  by_cases he : shift + r = i.val
  · rw [ite_eq_left he, he]
    exact cancelStep_at p a i (by omega)
  · have hk : r ≤ shift + r ∧ shift + r < m := ⟨by omega, hbound⟩
    have hsub : shift + r - r = shift := by omega
    by_cases ht : a ⟨shift + r, hbound⟩ = true
    · by_cases hw : shift ≤ i.val ∧ i.val < shift + r
      · have hj : i.val - shift < r := by omega
        simp [cancelStep, hk, ht, wordXor, shiftModulus, hsub,
          he, Ne.symm he, hw, wordGet, hj]
      · simp [cancelStep, hk, ht, wordXor, shiftModulus, hsub,
          he, Ne.symm he, hw]
    · have hf : a ⟨shift + r, hbound⟩ = false := Bool.eq_false_of_not_eq_true ht
      simp [cancelStep, hk, ht, he]

theorem cancelByUpdates_eq_cancelStep {r m : ℕ} (p : BitWord r) (a : BitWord m)
    (shift : ℕ) (hbound : shift + r < m) :
    cancelByUpdates (wordList p) (wordList a) shift =
      wordList (cancelStep p (shift + r) a) := by
  have hw : listWord m (cancelByUpdates (wordList p) (wordList a) shift) =
      cancelStep p (shift + r) a := by
    funext i
    change (cancelByUpdates (wordList p) (wordList a) shift).getD i.val false = _
    rw [cancelByUpdates_getD _ _ _ (by simpa only [wordList_length] using hbound)]
    rw [cancelStep_read p a shift hbound i]
    simp only [wordList_length, wordList_getD, wordGet_fin, wordGet_of_lt a hbound]
  calc
    cancelByUpdates (wordList p) (wordList a) shift =
        wordList (listWord m (cancelByUpdates (wordList p) (wordList a) shift)) :=
      (wordList_listWord _ (by simp)).symm
    _ = wordList (cancelStep p (shift + r) a) := congrArg wordList hw

theorem reduceLoop_below {r m : ℕ} (p : BitWord r) (k : ℕ) (a : BitWord m)
    (hk : k ≤ r) : reduceLoop p k a = a := by
  revert hk
  induction k generalizing a with
  | zero => intro hk; rfl
  | succ k ih =>
      intro hk
      have hskip : ¬(r ≤ k ∧ k < m) := by omega
      simpa only [reduceLoop, cancelStep, dite_eq_right hskip] using ih a (by omega)

theorem reduceByUpdates_word_eq {r m : ℕ} (p : BitWord r) (s : ℕ)
    (a : BitWord m) (hbound : r + s ≤ m) :
    reduceByUpdates (wordList p) s (wordList a) =
      wordList (reduceLoop p (r + s) a) := by
  revert hbound
  induction s generalizing a with
  | zero =>
      intro hbound
      simp only [reduceByUpdates_zero, Nat.add_zero, reduceLoop_below p r a le_rfl]
  | succ s ih =>
      intro hbound
      have hs : s + r < m := by omega
      have hs' : r + s ≤ m := by omega
      have hnext : r + (s + 1) = (r + s) + 1 := by omega
      calc
        reduceByUpdates (wordList p) (s + 1) (wordList a) =
            reduceByUpdates (wordList p) s (wordList (cancelStep p (s + r) a)) := by
          rw [reduceByUpdates_step, cancelByUpdates_eq_cancelStep p a s hs]
        _ = wordList (reduceLoop p (r + s) (cancelStep p (s + r) a)) := ih _ hs'
        _ = wordList (reduceLoop p (r + (s + 1)) a) := by
          rw [hnext, reduceLoop, Nat.add_comm s r]

theorem reduceByUpdates_eq_reduceLoop (p c : List Bool) (s : ℕ)
    (hbound : p.length + s ≤ c.length) :
    reduceByUpdates p s c =
      wordList (reduceLoop (listWord p.length p) (p.length + s) (listWord c.length c)) := by
  simpa only [wordList_listWord_length] using
    reduceByUpdates_word_eq (listWord p.length p) s (listWord c.length c) hbound

theorem reduceByUpdates_tail_false (p c : List Bool) (s : ℕ)
    (hfull : p.length + s = c.length) (i : ℕ) (hi : p.length ≤ i) :
    (reduceByUpdates p s c).getD i false = false := by
  rw [reduceByUpdates_eq_reduceLoop p c s (by omega), hfull, wordList_getD]
  by_cases him : i < c.length
  · rw [wordGet_of_lt _ him]
    exact reduceLoop_tail_false (listWord p.length p) c.length (listWord c.length c)
      (by
        intro j _ hj
        exact False.elim (Nat.not_le.mpr j.is_lt hj)) ⟨i, him⟩ hi
  · exact wordGet_of_le _ (Nat.le_of_not_lt him)

theorem wordList_wordResize_take {r m : ℕ} (a : BitWord m) (hr : r ≤ m) :
    wordList (wordResize r a) = (wordList a).take r := by
  apply List.ext_getElem
  · simp only [wordList_length, List.length_take, Nat.min_eq_left hr]
  · intro i hi hj
    have hir : i < r := by simpa only [wordList_length] using hi
    have hleft : (wordList (wordResize r a)).getD i false = wordGet a i := by
      rw [wordList_getD, wordGet_of_lt _ hir]
      rfl
    have hright : ((wordList a).take r).getD i false = wordGet a i := by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hir] using
        wordList_getD a i
    rw [List.getD_eq_getElem _ false hi] at hleft
    rw [List.getD_eq_getElem _ false hj] at hright
    exact hleft.trans hright.symm

theorem reduceByUpdates_take_eq_wordReduce (p c : List Bool)
    (hwidth : c.length = p.length + p.length) :
    (reduceByUpdates p p.length c).take p.length =
      wordList (wordReduce (listWord p.length p) (listWord c.length c)) := by
  rw [reduceByUpdates_eq_reduceLoop p c p.length (by omega), ← hwidth]
  rw [wordReduce, wordFreeze_eq, wordList_wordResize_take _ (by omega)]

theorem reduceByUpdates_convolve_eq_multiplyBitLists (r : ℕ) (p a b : List Bool)
    (hp : p.length = r) (ha : a.length = r) (hb : b.length = r) :
    (reduceByUpdates p r (convolveBitLists a b)).take r = multiplyBitLists r p a b := by
  have hwidth : (convolveBitLists a b).length = p.length + p.length := by
    simp only [convolveBitLists_length, ha, hb, hp]
  have h := reduceByUpdates_take_eq_wordReduce p (convolveBitLists a b) hwidth
  rw [convolveBitLists_length, hp] at h
  rw [convolveBitLists_eq, ha, hb] at h ⊢
  simpa only [listWord_wordList, multiplyBitLists, wordMulMod] using h

theorem reduceByUpdates_convolveByUpdates_eq_multiplyBitLists (r : ℕ)
    (p a b : List Bool) (hp : p.length = r) (ha : a.length = r) (hb : b.length = r) :
    (reduceByUpdates p r (convolveByUpdates a b)).take r = multiplyBitLists r p a b := by
  rw [convolveByUpdates_eq]
  exact reduceByUpdates_convolve_eq_multiplyBitLists r p a b hp ha hb

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeCancelRow

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

abbrev State := LoopState DecState TapeCancelStep.State

def program (v : Bool) : TapeMultiProgram State :=
  loopCode (decProgram loop1) (TapeCancelStep.program v)
    DecState.start TapeCancelStep.start decPositive

def start : State := loopTest DecState.start
def done : State := loopDone

def frame (σ : TapeStore) (n j shift : ℕ) (out : List Bool) : TapeStore :=
  fun r => if r = loop1 then List.replicate n true
    else if r = indexA then List.replicate j true
    else if r = indexC then List.replicate (shift + j) true
    else if r = productBits then out else σ r

@[simp] theorem frame_counter (σ : TapeStore) (n j s : ℕ) (out : List Bool) :
    frame σ n j s out loop1 = List.replicate n true := by simp [frame]
@[simp] theorem frame_indexA (σ : TapeStore) (n j s : ℕ) (out : List Bool) :
    frame σ n j s out indexA = List.replicate j true := by simp [frame, loop1, indexA]
@[simp] theorem frame_indexC (σ : TapeStore) (n j s : ℕ) (out : List Bool) :
    frame σ n j s out indexC = List.replicate (s + j) true := by
  simp [frame, loop1, indexA, indexC]
@[simp] theorem frame_output (σ : TapeStore) (n j s : ℕ) (out : List Bool) :
    frame σ n j s out productBits = out := by
  simp [frame, loop1, indexA, indexC, productBits]

theorem update_counter (σ : TapeStore) (n n' j s : ℕ) (out : List Bool) :
    Function.update (frame σ n j s out) loop1 (List.replicate n' true) =
      frame σ n' j s out := by
  funext r
  by_cases hr : r = loop1
  · subst r
    simp
  · simp [frame, Function.update, hr]

theorem resultStore_frame (σ : TapeStore) (n j s : ℕ) (out out' : List Bool) :
    TapeCancelStep.resultStore (frame σ n j s out) j (s + j) out' =
      frame σ n (j + 1) s out' := by
  funext r
  by_cases hc : r = indexC
  · subst r
    simp [TapeCancelStep.resultStore, Nat.add_assoc]
  · by_cases ha : r = indexA
    · subst r
      simp [TapeCancelStep.resultStore, indexA, indexC]
    · by_cases hp : r = productBits
      · subst r
        simp [TapeCancelStep.resultStore, indexA, indexC, productBits]
      · simp [TapeCancelStep.resultStore, Function.update, frame, hc, ha, hp]

theorem runs_row (v : Bool) (σ : TapeStore) (p c : List Bool) (s j n : ℕ)
    (hP : σ polyBits = p) (hj : j + n ≤ p.length) (hsize : s + p.length ≤ c.length) :
    RunsIn (program v).step
      (cfg start (storeTapes (frame σ n j s (modulusUpdateLoop p v s j c))))
      (cfg done (storeTapes (frame σ 0 (j + n) s (modulusUpdateLoop p v s (j + n) c))))
      (n * (2 * s + 4 * p.length + 21) + 3) := by
  induction n generalizing j with
  | zero =>
      have hd := decrement_empty loop1
        (storeTapes (frame σ 0 j s (modulusUpdateLoop p v s j c))) (by simp [])
      have he := loop_exit (decProgram loop1) (TapeCancelStep.program v)
        DecState.start TapeCancelStep.start decPositive hd rfl rfl
      simpa only [program, start, done, Nat.add_zero, Nat.zero_mul, Nat.zero_add] using he
  | succ n ih =>
      let out := modulusUpdateLoop p v s j c
      let out' := modulusUpdateLoop p v s (j + 1) c
      have hd := decrement_cons loop1 (storeTapes (frame σ (n + 1) j s out))
        (List.replicate n true) true (by simp [List.replicate_succ])
      have hd' : RunsIn (decProgram loop1).step
          (cfg DecState.start (storeTapes (frame σ (n + 1) j s out)))
          (cfg (DecState.done true) (storeTapes (frame σ n j s out))) 4 := by
        simpa only [← storeTapes_update, update_counter] using hd
      have hPf : frame σ n j s out polyBits = p := by
        simp [frame, hP, polyBits, loop1, indexA, indexC, productBits]
      have ht := TapeCancelStep.runs_step v (frame σ n j s out) j (s + j)
        (by simp) (by simp) (by rw [hPf]; omega)
        (by simp only [frame_output, out, modulusUpdateLoop_length]; omega)
      have ht' : RunsIn (TapeCancelStep.program v).step
          (cfg TapeCancelStep.start (storeTapes (frame σ n j s out)))
          (cfg TapeCancelStep.done (storeTapes (frame σ n (j + 1) s out')))
          (2 * j + 2 * (s + j) + 15) := by
        simpa only [frame_output, hPf, resultStore_frame, out', modulusUpdateLoop_step, out] using ht
      have hit := loop_iter (decProgram loop1) (TapeCancelStep.program v)
        DecState.start TapeCancelStep.start decPositive hd' rfl rfl ht' rfl
      have hit' := hit.mono (show 4 + 1 + (2 * j + 2 * (s + j) + 15) + 1 ≤
          2 * s + 4 * p.length + 21 by omega)
      have hrest := ih (j + 1) (by omega)
      have hall := hit'.trans hrest
      have htime : (2 * s + 4 * p.length + 21) +
          (n * (2 * s + 4 * p.length + 21) + 3) =
          (n + 1) * (2 * s + 4 * p.length + 21) + 3 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hindex : j + 1 + n = j + (n + 1) := by omega
      simpa only [program, start, done, htime, hindex, out, out'] using hall

@[simp] theorem program_done (v : Bool) (h : TapeHeads) : program v done h = none := rfl

end TapeCancelRow
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeCancel

open TapeMultiProgram TapeRouting TapeUnary TapeProductTerm TapeRegister

abbrev ReadState := TapeArray.State ⊕ (Bool × TapeCancelRow.State)
abbrev ClearState := ReadState ⊕ TapeArray.State
abbrev State := ClearState ⊕ Unit

def readProgram : TapeMultiProgram ReadState :=
  joinCode (TapeArray.code indexB productBits id)
    (carryCode TapeCancelRow.program) (fun q => (readFlag q, TapeCancelRow.start))

def clearProgram : TapeMultiProgram ClearState :=
  joinCode readProgram (TapeArray.code indexC productBits (fun _ => false))
    (fun _ => TapeArray.State.start)

def haltProgram : TapeMultiProgram Unit := fun _ _ => none

def program : TapeMultiProgram State :=
  joinCode clearProgram haltProgram (fun _ => ())

def start : State := .inl (.inl (.inl TapeArray.State.start))
def done : State := .inr ()

def resultStore (σ : TapeStore) (r s : ℕ) (out : List Bool) : TapeStore :=
  TapeCancelRow.frame σ 0 r s out

def cost (s r : ℕ) : ℕ := r * (2 * s + 4 * r + 21) + 4 * (s + r) + 14

theorem set_eq_split (xs : List Bool) (i : ℕ) (hi : i < xs.length) (b : Bool) :
    xs.set i b = xs.take i ++ b :: xs.drop (i + 1) := by
  calc
    xs.set i b = (xs.take i ++ xs.getD i false :: xs.drop (i + 1)).set
        (xs.take i).length b := by
      rw [TapeNaturalAccess.take_length xs i hi, ← TapeNaturalAccess.split xs i hi]
    _ = _ := by simp

theorem clear_at (σ : TapeStore) (i : ℕ)
    (hi : σ indexC = List.replicate i true) (hib : i < (σ productBits).length) :
    RunsIn (TapeArray.code indexC productBits (fun _ => false)).step
      (cfg TapeArray.State.start (storeTapes σ))
      (cfg (TapeArray.State.done ((σ productBits).getD i false))
        (storeTapes (Function.update σ productBits ((σ productBits).set i false))))
      (2 * i + 4) := by
  have h := modify_at (by decide : indexC ≠ productBits) (fun _ => false) (storeTapes σ)
    ((σ productBits).take i) ((σ productBits).drop (i + 1)) ((σ productBits).getD i false)
    (by simp only [storeTapes_apply, hi, counterTape, TapeNaturalAccess.take_length _ _ hib])
    (congrArg wordTape (TapeNaturalAccess.split _ _ hib))
  simpa only [TapeNaturalAccess.take_length _ _ hib, storeTapes_update,
    set_eq_split _ _ hib] using h

theorem update_output (σ : TapeStore) (r s : ℕ) (out out' : List Bool) :
    Function.update (resultStore σ r s out) productBits out' = resultStore σ r s out' := by
  funext q
  by_cases hq : q = productBits
  · subst q
    simp [resultStore]
  · simp [resultStore, TapeCancelRow.frame, Function.update, hq]

theorem runs_cancel (σ : TapeStore) (p c : List Bool) (s : ℕ)
    (hP : σ polyBits = p) (hOut : σ productBits = c)
    (hLoop : σ loop1 = List.replicate p.length true) (hA : σ indexA = [])
    (hB : σ indexB = List.replicate (s + p.length) true)
    (hC : σ indexC = List.replicate s true) (hbound : s + p.length < c.length) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (resultStore σ p.length s (cancelByUpdates p c s))))
      (cost s p.length) := by
  let v := c.getD (s + p.length) false
  let out := modulusUpdateLoop p v s p.length c
  let ρ := resultStore σ p.length s out
  have hr := TapeNaturalAccess.read indexB productBits (by decide) σ (s + p.length) hB
    (by simpa only [hOut] using hbound)
  have hrow := TapeCancelRow.runs_row v σ p c s 0 p.length hP (by omega) hbound.le
  have hentry : TapeCancelRow.frame σ p.length 0 s c = σ := by
    funext q
    by_cases hl : q = loop1
    · subst q
      simp [hLoop]
    · by_cases ha : q = indexA
      · subst q
        simp [hA]
      · by_cases hc : q = indexC
        · subst q
          simp [hC]
        · by_cases ho : q = productBits
          · subst q
            simp [hOut]
          · simp [TapeCancelRow.frame, hl, ha, hc, ho]
  have hrow' : RunsIn (TapeCancelRow.program v).step
      (cfg TapeCancelRow.start (storeTapes σ))
      (cfg TapeCancelRow.done (storeTapes ρ))
      (p.length * (2 * s + 4 * p.length + 21) + 3) := by
    simpa only [modulusUpdateLoop_zero, Nat.zero_add, hentry, ρ, resultStore, out] using hrow
  have hcarr := carry_runs TapeCancelRow.program v hrow'
  have hread := join_runs (TapeArray.code indexB productBits id)
    (carryCode TapeCancelRow.program) (fun q => (readFlag q, TapeCancelRow.start))
    (q' := TapeArray.State.done v)
    (by simpa only [hOut] using hr) rfl hcarr
  have hclear := clear_at ρ (s + p.length) (by simp [ρ, resultStore]) (by
    simp only [ρ, resultStore, TapeCancelRow.frame_output, out, modulusUpdateLoop_length]
    exact hbound)
  have hclear' : RunsIn (TapeArray.code indexC productBits (fun _ => false)).step
      (cfg TapeArray.State.start (storeTapes ρ))
      (cfg (TapeArray.State.done (out.getD (s + p.length) false))
        (storeTapes (resultStore σ p.length s (cancelByUpdates p c s))))
      (2 * (s + p.length) + 4) := by
    have hρout : ρ productBits = out := by simp [ρ, resultStore]
    simpa only [hρout, ρ, update_output, cancelByUpdates, out, v] using hclear
  have hboth := join_runs readProgram (TapeArray.code indexC productBits (fun _ => false))
    (fun _ => TapeArray.State.start) hread rfl hclear'
  have hhalt : RunsIn haltProgram.step
      (cfg () (storeTapes (resultStore σ p.length s (cancelByUpdates p c s))))
      (cfg () (storeTapes (resultStore σ p.length s (cancelByUpdates p c s)))) 0 := RunsIn.refl _ _
  have hall := join_runs clearProgram haltProgram (fun _ => ()) hboth rfl hhalt
  have htime : ((2 * (s + p.length) + 4 + 1 +
      (p.length * (2 * s + 4 * p.length + 21) + 3)) + 1 +
      (2 * (s + p.length) + 4)) + 1 + 0 = cost s p.length := by
    unfold cost
    omega
  simpa only [State, program, start, done, htime, Nat.add_zero] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeCancel
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeRemainderOuter

open TapeMultiProgram TapeRouting TapeUnary TapeArithmetic TapeRegister

def ScratchEmpty (σ : TapeStore) : Prop :=
  σ loop1 = [] ∧ σ indexA = [] ∧ σ indexB = [] ∧ σ indexC = [] ∧ σ scratchA = []

abbrev BodyState := TapeRemainderSetup.SetupState ⊕
  (TapeCancel.State ⊕ TapeRemainderSetup.CleanupState)

def tailProgram : TapeMultiProgram (TapeCancel.State ⊕ TapeRemainderSetup.CleanupState) :=
  joinCode TapeCancel.program TapeRemainderSetup.cleanupProgram
    (fun _ => TapeRemainderSetup.cleanupStart)

def bodyProgram : TapeMultiProgram BodyState :=
  joinCode TapeRemainderSetup.setupProgram tailProgram (fun _ => .inl TapeCancel.start)

def bodyStart : BodyState := .inl TapeRemainderSetup.setupStart
def bodyDone : BodyState := .inr (.inr TapeRemainderSetup.cleanupDone)

def bodyCost (s r : ℕ) : ℕ :=
  (4*s + 12*r + 23) + 1 + (TapeCancel.cost s r + 1 + (4*s + 6*r + 17))

@[simp] theorem bodyProgram_done (h : TapeHeads) : bodyProgram bodyDone h = none := by
  simp [bodyProgram, bodyDone, tailProgram, joinCode,
    TapeRemainderSetup.cleanupProgram_done]

theorem cleanup_result (σ : TapeStore) (r s : ℕ) (out : List Bool)
    (hclean : ScratchEmpty σ) :
    TapeRemainderSetup.clearIndices
      (TapeCancel.resultStore (TapeRemainderSetup.preparedStore σ r s) r s out) =
      Function.update σ productBits out := by
  rcases hclean with ⟨hL, hA, hB, hC, hW⟩
  funext q
  by_cases ha : q = indexA
  · subst q
    simp [TapeRemainderSetup.clearIndices, Function.update,
      hA, indexA, indexB, indexC, productBits]
  · by_cases hb : q = indexB
    · subst q
      simp [TapeRemainderSetup.clearIndices, Function.update,
        hB, indexB, indexC, productBits]
    · by_cases hc : q = indexC
      · subst q
        simp [TapeRemainderSetup.clearIndices, Function.update,
          hC, indexC, productBits]
      · by_cases hl : q = loop1
        · subst q
          simp [TapeRemainderSetup.clearIndices, TapeCancel.resultStore,
            TapeCancelRow.frame, Function.update,
            hL, loop1, indexA, indexB, indexC, productBits]
        · by_cases hp : q = productBits
          · subst q
            simp [TapeRemainderSetup.clearIndices, TapeCancel.resultStore,
              TapeCancelRow.frame, Function.update,
              loop1, indexA, indexB, indexC, productBits]
          · simp [TapeRemainderSetup.clearIndices, TapeCancel.resultStore,
              TapeCancelRow.frame, TapeRemainderSetup.preparedStore, Function.update,
              ha, hb, hc, hl, hp]

theorem runs_body (σ : TapeStore) (p c : List Bool) (s : ℕ)
    (hP : σ polyBits = p) (hOut : σ productBits = c)
    (hDegree : σ ringDegree = List.replicate p.length true)
    (hLoop0 : σ loop0 = List.replicate s true) (hclean : ScratchEmpty σ)
    (hbound : s + p.length < c.length) :
    RunsIn bodyProgram.step (cfg bodyStart (storeTapes σ))
      (cfg bodyDone (storeTapes (Function.update σ productBits (cancelByUpdates p c s))))
      (bodyCost s p.length) := by
  rcases hclean with ⟨hL, hA, hB, hC, hW⟩
  let τ := TapeRemainderSetup.preparedStore σ p.length s
  let out := cancelByUpdates p c s
  let ρ := TapeCancel.resultStore τ p.length s out
  have hsetup := TapeRemainderSetup.runs_setup σ p.length s hLoop0 hDegree hL hA hB hC hW
  have hcancel := TapeCancel.runs_cancel τ p c s
    (by simp [τ, TapeRemainderSetup.preparedStore, hP,
      indexB, indexC, loop1, polyBits])
    (by simp [τ, TapeRemainderSetup.preparedStore, hOut,
      indexB, indexC, loop1, productBits])
    (by simp [τ, TapeRemainderSetup.preparedStore])
    (by simp [τ, TapeRemainderSetup.preparedStore, hA,
      indexB, indexC, loop1, indexA])
    (by simp [τ, TapeRemainderSetup.preparedStore, indexB, indexC, loop1])
    (by simp [τ, TapeRemainderSetup.preparedStore, indexC, loop1]) hbound
  have hcleanup := TapeRemainderSetup.runs_cleanup ρ p.length s
    (by simp [ρ, TapeCancel.resultStore])
    (by simp [ρ, TapeCancel.resultStore, TapeCancelRow.frame, τ,
      TapeRemainderSetup.preparedStore, loop1, indexA, indexB, indexC, productBits])
    (by simp [ρ, TapeCancel.resultStore])
  have hfinal : TapeRemainderSetup.clearIndices ρ = Function.update σ productBits out :=
    cleanup_result σ p.length s out ⟨hL, hA, hB, hC, hW⟩
  rw [hfinal] at hcleanup
  have htail := join_runs TapeCancel.program TapeRemainderSetup.cleanupProgram
    (fun _ => TapeRemainderSetup.cleanupStart) hcancel (TapeCancel.program_done _) hcleanup
  have hall := join_runs TapeRemainderSetup.setupProgram tailProgram
    (fun _ => .inl TapeCancel.start) hsetup
    (TapeRemainderSetup.setupProgram_done _) htail
  simpa only [bodyProgram, bodyStart, bodyDone, bodyCost, out] using hall

def iterationCost (r : ℕ) : ℕ := r * (6*r + 21) + 34*r + 62

theorem bodyCost_le (s r : ℕ) (hs : s ≤ r) :
    4 + 1 + bodyCost s r + 1 ≤ iterationCost r := by
  have hmul := Nat.mul_le_mul_left (2*r) hs
  unfold bodyCost TapeCancel.cost iterationCost
  nlinarith

abbrev State := LoopState DecState BodyState

def program : TapeMultiProgram State :=
  loopCode (decProgram loop0) bodyProgram DecState.start bodyStart decPositive

def start : State := loopTest DecState.start
def done : State := loopDone

def frame (σ : TapeStore) (k : ℕ) (out : List Bool) : TapeStore :=
  fun q => if q = loop0 then List.replicate k true
    else if q = productBits then out else σ q

@[simp] theorem frame_counter (σ : TapeStore) (k : ℕ) (out : List Bool) :
    frame σ k out loop0 = List.replicate k true := by simp [frame]

@[simp] theorem frame_output (σ : TapeStore) (k : ℕ) (out : List Bool) :
    frame σ k out productBits = out := by simp [frame, loop0, productBits]

@[simp] theorem frame_poly (σ : TapeStore) (k : ℕ) (out : List Bool) :
    frame σ k out polyBits = σ polyBits := by simp [frame, loop0, productBits, polyBits]

@[simp] theorem frame_degree (σ : TapeStore) (k : ℕ) (out : List Bool) :
    frame σ k out ringDegree = σ ringDegree := by
  simp [frame, loop0, productBits, ringDegree]

theorem frame_clean (σ : TapeStore) (k : ℕ) (out : List Bool)
    (h : ScratchEmpty σ) : ScratchEmpty (frame σ k out) := by
  simpa [ScratchEmpty, frame, loop0, loop1, indexA, indexB, indexC, scratchA, productBits]
    using h

theorem update_counter (σ : TapeStore) (k k' : ℕ) (out : List Bool) :
    Function.update (frame σ k out) loop0 (List.replicate k' true) = frame σ k' out := by
  funext q
  by_cases h : q = loop0
  · subst q
    simp
  · simp [frame, Function.update, h]

theorem update_output (σ : TapeStore) (k : ℕ) (out out' : List Bool) :
    Function.update (frame σ k out) productBits out' = frame σ k out' := by
  funext q
  by_cases h : q = productBits
  · subst q
    simp
  · simp [frame, Function.update, h]

theorem runs_loop (σ : TapeStore) (p c : List Bool) (k : ℕ)
    (hP : σ polyBits = p)
    (hDegree : σ ringDegree = List.replicate p.length true)
    (hclean : ScratchEmpty σ) (hk : k ≤ p.length) (hsize : k + p.length ≤ c.length) :
    RunsIn program.step (cfg start (storeTapes (frame σ k c)))
      (cfg done (storeTapes (frame σ 0 (reduceByUpdates p k c))))
      (k * iterationCost p.length + 3) := by
  induction k generalizing c with
  | zero =>
      have hd := decrement_empty loop0 (storeTapes (frame σ 0 c)) (by simp)
      have he := loop_exit (decProgram loop0) bodyProgram DecState.start bodyStart
        decPositive hd rfl rfl
      simpa only [program, start, done, reduceByUpdates_zero, Nat.zero_mul, Nat.zero_add]
        using he
  | succ k ih =>
      let out := cancelByUpdates p c k
      have hd := decrement_cons loop0 (storeTapes (frame σ (k+1) c))
        (List.replicate k true) true (by simp [List.replicate_succ])
      have hd' : RunsIn (decProgram loop0).step
          (cfg DecState.start (storeTapes (frame σ (k+1) c)))
          (cfg (DecState.done true) (storeTapes (frame σ k c))) 4 := by
        simpa only [← storeTapes_update, update_counter] using hd
      have hb := runs_body (frame σ k c) p c k (by simpa using hP) (by simp)
        (by simpa using hDegree) (by simp) (frame_clean σ k c hclean) (by omega)
      have hb' : RunsIn bodyProgram.step (cfg bodyStart (storeTapes (frame σ k c)))
          (cfg bodyDone (storeTapes (frame σ k out))) (bodyCost k p.length) := by
        simpa only [update_output, out] using hb
      have hit := loop_iter (decProgram loop0) bodyProgram DecState.start bodyStart
        decPositive hd' rfl rfl hb' (bodyProgram_done _)
      have hit' := hit.mono (bodyCost_le k p.length (by omega))
      have hrest := ih out (by omega) (by simp only [out, cancelByUpdates_length]; omega)
      have hall := hit'.trans hrest
      have htime : iterationCost p.length + (k * iterationCost p.length + 3) =
          (k+1) * iterationCost p.length + 3 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [program, start, done, reduceByUpdates_step, out, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeRemainderOuter
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeRemainder

open TapeMultiProgram TapeRouting TapeRegister

abbrev State := TapeCopy.State ⊕ TapeRemainderOuter.State

def program : TapeMultiProgram State :=
  joinCode (TapeCopy.code ringDegree loop0) TapeRemainderOuter.program
    (fun _ => TapeRemainderOuter.start)

def start : State := .inl TapeCopy.State.start
def done : State := .inr TapeRemainderOuter.done

def cost (r : ℕ) : ℕ := r * TapeRemainderOuter.iterationCost r + 2*r + 8

theorem cost_le (r : ℕ) : cost r ≤ 100 * (r+1)^3 := by
  unfold cost TapeRemainderOuter.iterationCost
  nlinarith [Nat.zero_le (r*r), Nat.zero_le (r*r*r)]

theorem input_frame (σ : TapeStore) (c : List Bool) (r : ℕ)
    (hOut : σ productBits = c) :
    Function.update σ loop0 (List.replicate r true) = TapeRemainderOuter.frame σ r c := by
  funext q
  by_cases hl : q = loop0
  · subst q
    simp
  · by_cases hp : q = productBits
    · subst q
      simp [hOut, loop0, productBits]
    · simp [TapeRemainderOuter.frame, Function.update, hl, hp]

theorem output_frame (σ : TapeStore) (out : List Bool) (hLoop0 : σ loop0 = []) :
    TapeRemainderOuter.frame σ 0 out = Function.update σ productBits out := by
  funext q
  by_cases hl : q = loop0
  · subst q
    simp [hLoop0, loop0, productBits]
  · by_cases hp : q = productBits
    · subst q
      simp
    · simp [TapeRemainderOuter.frame, Function.update, hl, hp]

theorem runs_remainder (σ : TapeStore) (p c : List Bool)
    (hP : σ polyBits = p) (hOut : σ productBits = c)
    (hDegree : σ ringDegree = List.replicate p.length true)
    (hWidth : c.length = 2*p.length)
    (hLoop0 : σ loop0 = []) (hLoop1 : σ loop1 = [])
    (hA : σ indexA = []) (hB : σ indexB = []) (hC : σ indexC = [])
    (hScratch : σ scratchA = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes
        (Function.update σ productBits (reduceByUpdates p p.length c)))) (cost p.length) := by
  have hcopy := TapeStoreRuns.copy (by decide : ringDegree ≠ loop0) σ hLoop0
  have hcopy' : RunsIn (TapeCopy.code ringDegree loop0).step
      (cfg TapeCopy.State.start (storeTapes σ))
      (cfg TapeCopy.State.done (storeTapes (TapeRemainderOuter.frame σ p.length c)))
      (2*p.length+4) := by
    simpa only [hDegree, List.length_replicate, input_frame σ c p.length hOut] using hcopy
  have hloop := TapeRemainderOuter.runs_loop σ p c p.length hP hDegree
    ⟨hLoop1, hA, hB, hC, hScratch⟩ le_rfl (by omega)
  rw [output_frame σ _ hLoop0] at hloop
  have hall := join_runs (TapeCopy.code ringDegree loop0) TapeRemainderOuter.program
    (fun _ => TapeRemainderOuter.start) hcopy' rfl hloop
  have htime : (2*p.length+4)+1+(p.length*TapeRemainderOuter.iterationCost p.length+3) =
      cost p.length := by unfold cost; omega
  simpa only [program, start, done, htime] using hall

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

end TapeRemainder
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHornerTake

open TapeMultiProgram TapeRouting TapeRegister TapeInputBlockLoop

def registers : Registers where
  toFun i := match i.val with
    | 0 => productBits
    | 1 => indexA
    | 2 => loop1
    | 3 => scratchA
    | _ => accumBits
  inj' := by decide

abbrev PrepareState := TapeErase.State ⊕ TapeCopy.State
abbrev WorkState := PrepareState ⊕ TapeInputBlocks.State
abbrev State := WorkState ⊕ TapeErase.State

def prepare : TapeMultiProgram PrepareState :=
  joinCode (TapeErase.code accumBits) (TapeCopy.code ringDegree loop1)
    (fun _ => TapeCopy.State.start)

def work : TapeMultiProgram WorkState :=
  joinCode prepare (TapeInputBlocks.program registers) (fun _ => TapeInputBlocks.start)

def program : TapeMultiProgram State :=
  joinCode work (TapeErase.code productBits) (fun _ => TapeErase.State.start)

def start : State := .inl (.inl (.inl TapeErase.State.start))
def done : State := .inr TapeErase.State.done

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

theorem runs_take (σ : TapeStore) (a c : List Bool) (r : ℕ)
    (hacc : σ accumBits = a) (hprod : σ productBits = c)
    (hlenA : a.length = r) (hlenC : c.length = 2 * r)
    (hdegree : σ ringDegree = List.replicate r true)
    (hcount : σ loop1 = []) (hindex : σ indexA = []) (hscratch : σ scratchA = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update
        (Function.update σ accumBits (c.take r)) productBits [])))
      (r * (r + 27) + 8 * r + 29) := by
  let U := Function.update σ accumBits []
  let V := Function.update U loop1 (List.replicate r true)
  let W := Function.update U accumBits (c.take r)
  have he := TapeStoreRuns.erase accumBits σ
  have he' : RunsIn (TapeErase.code accumBits).step
      (cfg TapeErase.State.start (storeTapes σ)) (cfg TapeErase.State.done (storeTapes U))
      (2 * r + 5) := by
    simpa only [hacc, hlenA] using he
  have hc := TapeStoreRuns.copy (src := ringDegree) (dst := loop1) (by decide) U
    (by simp [U, hcount, accumBits, loop1])
  have hc' : RunsIn (TapeCopy.code ringDegree loop1).step
      (cfg TapeCopy.State.start (storeTapes U)) (cfg TapeCopy.State.done (storeTapes V))
      (2 * r + 4) := by
    simpa [V, U, hdegree, ringDegree, accumBits] using hc
  have hp := join_runs (TapeErase.code accumBits) (TapeCopy.code ringDegree loop1)
    (fun _ => TapeCopy.State.start) he' rfl hc'
  have hlen : (c.take r).length = r := by
    apply List.length_take_of_le
    omega
  have hb := TapeInputBlocks.runs_extract registers V [] (c.take r) (c.drop r) []
    (by simp [registers, source, V, U, hprod, productBits, loop1, accumBits])
    (by simp [registers, index, V, U, hindex, indexA, loop1, accumBits])
    (by simp [registers, count, V, hlen])
    (by simp [registers, scratch, V, U, hscratch, scratchA, loop1, accumBits])
    (by simp [registers, destination, V, U, loop1, accumBits])
  have hout : Function.update (Function.update V (count registers) [])
      (destination registers) (c.take r ++ []) = W := by
    funext q
    by_cases hl : q = loop1 <;> by_cases ha : q = accumBits <;>
      simp_all [V, U, W, count, destination, registers, Function.update_apply]
  have hb' : RunsIn (TapeInputBlocks.program registers).step
      (cfg TapeInputBlocks.start (storeTapes V)) (cfg TapeInputBlocks.done (storeTapes W))
      (r * (r + 27) + 12) := by
    simpa only [hout, hlen, List.length_nil, Nat.mul_zero, Nat.zero_add] using hb
  have hw := join_runs prepare (TapeInputBlocks.program registers)
    (fun _ => TapeInputBlocks.start) hp rfl hb'
  have hclear := TapeStoreRuns.erase productBits W
  have hclear' : RunsIn (TapeErase.code productBits).step
      (cfg TapeErase.State.start (storeTapes W))
      (cfg TapeErase.State.done (storeTapes (Function.update W productBits [])))
      (4 * r + 5) := by
    simpa [W, U, hprod, hlenC, productBits, accumBits, ← Nat.mul_assoc] using hclear
  have hall := join_runs work (TapeErase.code productBits)
    (fun _ => TapeErase.State.start) hw rfl hclear'
  have hfinal : Function.update W productBits [] =
      Function.update (Function.update σ accumBits (c.take r)) productBits [] := by
    simp only [W, U, Function.update_idem]
  have ht : ((2 * r + 5 + 1 + (2 * r + 4)) + 1 + (r * (r + 27) + 12)) +
      1 + (4 * r + 5) = r * (r + 27) + 8 * r + 29 := by omega
  have ht' : ((2 * r + 5 + 1 + (2 * r + 4)) + 1 + (r * (r + 27) + 12)) +
      1 + (4 * r + 5) ≤ r * (r + 27) + 8 * r + 29 := ht.le
  have h := hall.mono ht'
  simpa only [program, start, done, hfinal] using h

end TapeHornerTake
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHornerMultiply

open TapeMultiProgram TapeRouting TapeRegister

structure Workspace (σ : TapeStore) (r : ℕ) : Prop where
  degree : σ ringDegree = List.replicate r true
  loop0_empty : σ loop0 = []
  loop1_empty : σ loop1 = []
  indexA_empty : σ indexA = []
  indexB_empty : σ indexB = []
  indexC_empty : σ indexC = []
  scratch_empty : σ scratchA = []
  product_empty : σ productBits = []

abbrev WorkState := TapeConvolve.State ⊕ TapeRemainder.State
abbrev State := WorkState ⊕ TapeHornerTake.State

def work : TapeMultiProgram WorkState :=
  joinCode TapeConvolve.program TapeRemainder.program (fun _ => TapeRemainder.start)

def program : TapeMultiProgram State :=
  joinCode work TapeHornerTake.program (fun _ => TapeHornerTake.start)

def start : State := .inl (.inl TapeConvolve.start)
def done : State := .inr TapeHornerTake.done

def cost (r : ℕ) : ℕ :=
  TapeConvolve.cost r + TapeRemainder.cost r + r * (r + 27) + 8 * r + 31

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

theorem runs_multiply (σ : TapeStore) (p h a : List Bool) (r : ℕ)
    (hW : Workspace σ r) (hP : σ polyBits = p) (hH : σ hashBits = h)
    (hA : σ accumBits = a) (hp : p.length = r) (hh : h.length = r)
    (ha : a.length = r) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ accumBits (multiplyBitLists r p h a))))
      (cost r) := by
  let c := convolveBitLists h a
  let U := Function.update σ productBits c
  let v := reduceByUpdates p r c
  let V := Function.update σ productBits v
  have hc := TapeConvolve.runs_convolve σ h a r hH hA hh ha hW.degree
    hW.loop0_empty hW.loop1_empty hW.indexA_empty hW.indexB_empty
    hW.indexC_empty hW.scratch_empty hW.product_empty
  have hc' : RunsIn TapeConvolve.program.step (cfg TapeConvolve.start (storeTapes σ))
      (cfg TapeConvolve.done (storeTapes U)) (TapeConvolve.cost r) := hc
  have hr := TapeRemainder.runs_remainder U p c
    (by simp [U, hP, polyBits, productBits]) (by simp [U])
    (by simp [U, hp, hW.degree, ringDegree, productBits])
    (by simp [c, hp, hh, ha, Nat.two_mul])
    (by simp [U, hW.loop0_empty, loop0, productBits])
    (by simp [U, hW.loop1_empty, loop1, productBits])
    (by simp [U, hW.indexA_empty, indexA, productBits])
    (by simp [U, hW.indexB_empty, indexB, productBits])
    (by simp [U, hW.indexC_empty, indexC, productBits])
    (by simp [U, hW.scratch_empty, scratchA, productBits])
  have hr' : RunsIn TapeRemainder.program.step (cfg TapeRemainder.start (storeTapes U))
      (cfg TapeRemainder.done (storeTapes V)) (TapeRemainder.cost r) := by
    simpa only [U, V, v, hp, Function.update_idem] using hr
  have hw := join_runs TapeConvolve.program TapeRemainder.program
    (fun _ => TapeRemainder.start) hc' rfl hr'
  have hvlen : v.length = 2 * r := by
    simp [v, c, reduceByUpdates_length, hh, ha, Nat.two_mul]
  have ht := TapeHornerTake.runs_take V a v r
    (by simp [V, hA, accumBits, productBits]) (by simp [V]) ha hvlen
    (by simp [V, hW.degree, ringDegree, productBits])
    (by simp [V, hW.loop1_empty, loop1, productBits])
    (by simp [V, hW.indexA_empty, indexA, productBits])
    (by simp [V, hW.scratch_empty, scratchA, productBits])
  have hv : v.take r = multiplyBitLists r p h a :=
    reduceByUpdates_convolve_eq_multiplyBitLists r p h a hp hh ha
  have hfinal : Function.update (Function.update V accumBits (v.take r)) productBits [] =
      Function.update σ accumBits (multiplyBitLists r p h a) := by
    funext q
    by_cases hprod : q = productBits <;> by_cases hacc : q = accumBits <;>
      simp_all [V, Function.update, hW.product_empty, accumBits, productBits]
  rw [hfinal] at ht
  have hall := join_runs work TapeHornerTake.program (fun _ => TapeHornerTake.start) hw rfl ht
  have htime : (TapeConvolve.cost r + 1 + TapeRemainder.cost r) + 1 +
      (r * (r + 27) + 8 * r + 29) = cost r := by unfold cost; omega
  simpa only [program, start, done, htime] using hall

end TapeHornerMultiply
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeXor

open Turing TapeMultiProgram TapeCopy

inductive State where
  | start
  | scan
  | rewind
  | done
  deriving DecidableEq, Inhabited

instance : Fintype State where
  elems := {.start, .scan, .rewind, .done}
  complete := by
    intro state
    cases state <;> simp

def start : State := .start
def done : State := .done

def program (src dst : TapeRegister) : TapeMultiProgram State
  | .start, h => emit src dst .scan h (h src) (h dst) .right
  | .scan, h =>
      match (h src).1, (h dst).1 with
      | .bit a, .bit b =>
          emit src dst .scan h (h src) (rawInputSymbol (Bool.xor a b)) .right
      | .endMark, .endMark => emit src dst .rewind h (h src) (h dst) .stay
      | _, _ => none
  | .rewind, h =>
      if (h src).1 = .home then emit src dst .done h (h src) (h dst) .stay
      else emit src dst .rewind h (h src) (h dst) .left
  | .done, _ => none

@[simp] theorem program_done (src dst : TapeRegister) (h : TapeHeads) :
    program src dst done h = none := rfl

theorem step_start {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) :
    (program src dst).step (cfg .start (onPair src dst T S D)) =
      some (cfg .scan (onPair src dst T (S.move .right) (D.move .right))) := by
  have h := step_emit (program src dst) hne T S D .start .scan S.head D.head .right
    (by simp [program, heads, hne])
  simpa only [Tape.write_self, HeadMove.apply_right] using h

theorem step_scan_bit {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (a b : Bool)
    (hS : S.head = rawInputSymbol a) (hD : D.head = rawInputSymbol b) :
    (program src dst).step (cfg .scan (onPair src dst T S D)) =
      some (cfg .scan (onPair src dst T (S.move .right)
        ((D.write (rawInputSymbol (Bool.xor a b))).move .right))) := by
  have h := step_emit (program src dst) hne T S D .scan .scan
    S.head (rawInputSymbol (Bool.xor a b)) .right
    (by simp [program, heads, hne, hS, hD, rawInputSymbol, cleanAtom])
  simpa only [Tape.write_self, HeadMove.apply_right] using h

theorem step_scan_end {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol)
    (hS : S.head = cleanAtom .endMark) (hD : D.head = cleanAtom .endMark) :
    (program src dst).step (cfg .scan (onPair src dst T S D)) =
      some (cfg .rewind (onPair src dst T S D)) := by
  have h := step_emit (program src dst) hne T S D .scan .rewind S.head D.head .stay
    (by simp [program, heads, hne, hS, hD, cleanAtom])
  simpa only [Tape.write_self, HeadMove.apply_stay] using h

theorem step_rewind_move {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (hS : S.head.1 ≠ .home) :
    (program src dst).step (cfg .rewind (onPair src dst T S D)) =
      some (cfg .rewind (onPair src dst T (S.move .left) (D.move .left))) := by
  have h := step_emit (program src dst) hne T S D .rewind .rewind S.head D.head .left
    (by simp [program, heads, hne, hS])
  simpa only [Tape.write_self, HeadMove.apply_left] using h

theorem step_rewind_home {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (S D : Tape TapeSymbol) (hS : S.head.1 = .home) :
    (program src dst).step (cfg .rewind (onPair src dst T S D)) =
      some (cfg .done (onPair src dst T S D)) := by
  have h := step_emit (program src dst) hne T S D .rewind .done S.head D.head .stay
    (by simp [program, heads, hne, hS])
  simpa only [Tape.write_self, HeadMove.apply_stay] using h

theorem runs_scan {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (a b : List Bool) (LS LD : List TapeSymbol)
    (hlen : a.length = b.length) :
    RunsIn (program src dst).step
      (cfg .scan (onPair src dst T
        (Tape.mk₂ LS (encodeInput a ++ [cleanAtom .endMark]))
        (Tape.mk₂ LD (encodeInput b ++ [cleanAtom .endMark]))))
      (cfg .rewind (onPair src dst T
        (Tape.mk₂ ((encodeInput a).reverse ++ LS) [cleanAtom .endMark])
        (Tape.mk₂ ((encodeInput (List.zipWith Bool.xor a b)).reverse ++ LD)
          [cleanAtom .endMark])))
      (a.length + 1) := by
  induction a generalizing b LS LD with
  | nil =>
      cases b with
      | nil =>
          have h := RunsIn.single (step_scan_end hne T
            (Tape.mk₂ LS [cleanAtom .endMark])
            (Tape.mk₂ LD [cleanAtom .endMark]) rfl rfl)
          simpa only [encodeInput, List.map_nil, List.nil_append, List.reverse_nil,
            List.length_nil, Nat.zero_add, List.zipWith_nil_left] using h
      | cons y ys => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons x xs ih =>
      cases b with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons y ys =>
          have htail : xs.length = ys.length := Nat.succ.inj hlen
          have hfirst := RunsIn.single (step_scan_bit hne T
            (Tape.mk₂ LS (rawInputSymbol x :: (encodeInput xs ++ [cleanAtom .endMark])))
            (Tape.mk₂ LD (rawInputSymbol y :: (encodeInput ys ++ [cleanAtom .endMark])))
            x y rfl rfl)
          simp only [TapeWord.write_mk₂_cons, TapeWord.move_right_mk₂_cons] at hfirst
          have hrest := ih ys (rawInputSymbol x :: LS)
            (rawInputSymbol (Bool.xor x y) :: LD) htail
          simpa only [encodeInput, List.map_cons, List.cons_append, List.reverse_cons,
            List.append_assoc, List.nil_append, List.length_cons, List.zipWith_cons_cons,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hfirst.trans hrest

theorem runs_rewind {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (a b : List Bool) (c : TapeSymbol) (RS RD : List TapeSymbol)
    (hlen : a.length = b.length) (hc : c.1 ≠ .home) :
    RunsIn (program src dst).step
      (cfg .rewind (onPair src dst T
        (Tape.mk₂ (encodeInput a ++ [cleanAtom .home]) (c :: RS))
        (Tape.mk₂ (encodeInput b ++ [cleanAtom .home]) RD)))
      (cfg .done (onPair src dst T
        (Tape.mk₂ [] (cleanAtom .home :: ((encodeInput a).reverse ++ c :: RS)))
        (Tape.mk₂ [] (cleanAtom .home :: ((encodeInput b).reverse ++ RD)))))
      (a.length + 2) := by
  induction a generalizing b c RS RD with
  | nil =>
      cases b with
      | nil =>
          have hfirst := RunsIn.single (step_rewind_move hne T
            (Tape.mk₂ [cleanAtom .home] (c :: RS))
            (Tape.mk₂ [cleanAtom .home] RD) hc)
          simp only [TapeWord.move_left_mk₂_cons] at hfirst
          have hlast := RunsIn.single (step_rewind_home hne T
            (Tape.mk₂ [] (cleanAtom .home :: c :: RS))
            (Tape.mk₂ [] (cleanAtom .home :: RD)) rfl)
          simpa only [encodeInput, List.map_nil, List.nil_append, List.reverse_nil,
            List.length_nil, Nat.zero_add] using hfirst.trans hlast
      | cons y ys => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons x xs ih =>
      cases b with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons y ys =>
          have htail : xs.length = ys.length := Nat.succ.inj hlen
          have hfirst := RunsIn.single (step_rewind_move hne T
            (Tape.mk₂ (rawInputSymbol x :: (encodeInput xs ++ [cleanAtom .home])) (c :: RS))
            (Tape.mk₂ (rawInputSymbol y :: (encodeInput ys ++ [cleanAtom .home])) RD) hc)
          simp only [TapeWord.move_left_mk₂_cons] at hfirst
          have hrest := ih ys (rawInputSymbol x) (c :: RS) (rawInputSymbol y :: RD)
            htail (by simp [rawInputSymbol, cleanAtom])
          simpa only [encodeInput, List.map_cons, List.cons_append, List.reverse_cons,
            List.append_assoc, List.nil_append, List.length_cons, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc] using hfirst.trans hrest

theorem runs_xor {src dst : TapeRegister} (hne : src ≠ dst)
    (T : TapeTapes) (a b : List Bool) (hlen : a.length = b.length) :
    RunsIn (program src dst).step
      (cfg start (onPair src dst T (wordTape a) (wordTape b)))
      (cfg done (onPair src dst T (wordTape a) (wordTape (List.zipWith Bool.xor a b))))
      (2 * a.length + 4) := by
  have hstart := RunsIn.single (step_start hne T (wordTape a) (wordTape b))
  have hscan := runs_scan hne T a b [cleanAtom .home] [cleanAtom .home] hlen
  have hzip : (List.zipWith Bool.xor a b).length = a.length := by
    simp only [List.length_zipWith, ← hlen, min_self]
  have hback := runs_rewind hne T a.reverse (List.zipWith Bool.xor a b).reverse
    (cleanAtom .endMark) [] [cleanAtom .endMark]
    (by simp only [List.length_reverse, hzip]) (by simp [cleanAtom])
  have hreverse (l : List Bool) : encodeInput l.reverse = (encodeInput l).reverse := by
    simp [encodeInput]
  simp only [hreverse, List.reverse_reverse, List.length_reverse] at hback
  have hstart' : RunsIn (program src dst).step
      (cfg .start (onPair src dst T (wordTape a) (wordTape b)))
      (cfg .scan (onPair src dst T
        (Tape.mk₂ [cleanAtom .home] (encodeInput a ++ [cleanAtom .endMark]))
        (Tape.mk₂ [cleanAtom .home] (encodeInput b ++ [cleanAtom .endMark])))) 1 := by
    simpa only [wordTape_right, cursorTape, encodeInput, List.map_nil,
      List.reverse_nil, List.nil_append] using hstart
  have hboth := (hstart'.trans hscan).trans hback
  have htime : (1 + (a.length + 1)) + (a.length + 2) = 2 * a.length + 4 := by omega
  simpa only [start, done, wordTape, Tape.mk₁, htime] using hboth

theorem runs_store {src dst : TapeRegister} (hne : src ≠ dst)
    (σ : TapeStore) (a b : List Bool) (hsrc : σ src = a) (hdst : σ dst = b)
    (hlen : a.length = b.length) :
    RunsIn (program src dst).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ dst (List.zipWith Bool.xor a b))))
      (2 * a.length + 4) := by
  have h := runs_xor hne (storeTapes σ) a b hlen
  have hi : onPair src dst (storeTapes σ) (wordTape a) (wordTape b) = storeTapes σ :=
    TapeProductTerm.onPair_eq_self (by simp only [storeTapes_apply, hsrc])
      (by simp only [storeTapes_apply, hdst])
  have ho : onPair src dst (storeTapes σ) (wordTape a)
      (wordTape (List.zipWith Bool.xor a b)) =
        storeTapes (Function.update σ dst (List.zipWith Bool.xor a b)) := by
    rw [← TapeArithmetic.update_onPair_dst hne (storeTapes σ) (wordTape a) (wordTape b),
      hi, storeTapes_update]
  simpa only [hi, ho] using h

theorem wordList_xor {n : ℕ} (a b : BitWord n) :
    wordList (wordXor a b) = List.zipWith Bool.xor (wordList a) (wordList b) := by
  apply List.ext_getElem
  · simp only [wordList_length, List.length_zipWith, min_self]
  · intro i hi hj
    simp only [wordList, wordXor, List.getElem_zipWith, List.getElem_ofFn]

theorem runs_wordStore {src dst : TapeRegister} (hne : src ≠ dst)
    (σ : TapeStore) {n : ℕ} (a b : BitWord n)
    (hsrc : σ src = wordList a) (hdst : σ dst = wordList b) :
    RunsIn (program src dst).step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ dst (wordList (wordXor a b)))))
      (2 * n + 4) := by
  have h := runs_store hne σ (wordList a) (wordList b) hsrc hdst
    (by simp only [wordList_length])
  simpa only [wordList_length, ← wordList_xor] using h

end TapeXor
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

def hornerStep (r : ℕ) (p h b a : List Bool) : List Bool :=
  List.zipWith Bool.xor b (multiplyBitLists r p h a)

theorem hornerStep_length (r : ℕ) (p h b a : List Bool) (hb : b.length = r) :
    (hornerStep r p h b a).length = r := by
  simp only [hornerStep, List.length_zipWith, multiplyBitLists_length, hb, min_self]

theorem hornerStep_eq_word (r : ℕ) (p h b a : List Bool) (hb : b.length = r) :
    hornerStep r p h b a =
      wordList (wordXor (listWord r b)
        (wordMulMod (listWord r p) (listWord r h) (listWord r a))) := by
  have hx (u v : BitWord r) :
      List.zipWith Bool.xor (wordList u) (wordList v) = wordList (wordXor u v) := by
    apply List.ext_getElem
    · simp only [wordList_length, List.length_zipWith, min_self]
    · intro i hi hj
      simp only [wordList, wordXor, List.getElem_zipWith, List.getElem_ofFn]
  have heq := hx (listWord r b)
    (wordMulMod (listWord r p) (listWord r h) (listWord r a))
  simpa only [wordList_listWord b hb, hornerStep, multiplyBitLists] using heq

def hornerFrom (r : ℕ) (p h : List Bool) (bs : List (List Bool))
    (a : List Bool) : List Bool :=
  bs.foldr (hornerStep r p h) a

@[simp] theorem hornerFrom_nil (r : ℕ) (p h a : List Bool) :
    hornerFrom r p h [] a = a := rfl

theorem hornerFrom_cons (r : ℕ) (p h b : List Bool) (bs : List (List Bool))
    (a : List Bool) :
    hornerFrom r p h (b :: bs) a = hornerStep r p h b (hornerFrom r p h bs a) := rfl

theorem hornerFrom_append (r : ℕ) (p h : List Bool)
    (bs cs : List (List Bool)) (a : List Bool) :
    hornerFrom r p h (bs ++ cs) a =
      hornerFrom r p h bs (hornerFrom r p h cs a) := by
  simp only [hornerFrom, List.foldr_append]

theorem hornerFrom_append_singleton (r : ℕ) (p h : List Bool)
    (bs : List (List Bool)) (b a : List Bool) :
    hornerFrom r p h (bs ++ [b]) a =
      hornerFrom r p h bs (hornerStep r p h b a) := by
  rw [hornerFrom_append, hornerFrom_cons, hornerFrom_nil]

theorem hornerFrom_length (r : ℕ) (p h : List Bool)
    (bs : List (List Bool)) (a : List Bool) (ha : a.length = r)
    (hbs : ∀ b ∈ bs, b.length = r) :
    (hornerFrom r p h bs a).length = r := by
  cases bs with
  | nil => exact ha
  | cons b bs =>
      rw [hornerFrom_cons]
      exact hornerStep_length r p h b _ (hbs b (by simp))

theorem hornerFrom_zero_eq_hornerBitLists (r : ℕ) (p h : List Bool)
    (bs : List (List Bool)) (hbs : ∀ b ∈ bs, b.length = r) :
    hornerFrom r p h bs (List.replicate r false) = hornerBitLists r p h bs := by
  revert hbs
  induction bs with
  | nil =>
      intro hbs
      simp only [hornerFrom_nil, hornerBitLists_nil, wordList, List.ofFn_const]
  | cons b bs ih =>
      intro hbs
      have hb : b.length = r := hbs b (by simp)
      have htail : ∀ c ∈ bs, c.length = r :=
        fun c hc => hbs c (List.mem_cons_of_mem b hc)
      rw [hornerFrom_cons, ih htail, hornerStep_eq_word r p h b _ hb,
        hornerBitLists_cons]

theorem block_flatten_length {α : Type uDepth1} (r : ℕ) (bs : List (List α))
    (hbs : ∀ b ∈ bs, b.length = r) : bs.flatten.length = bs.length * r := by
  revert hbs
  induction bs with
  | nil => intro hbs; simp
  | cons b bs ih =>
      intro hbs
      have hb : b.length = r := hbs b (by simp)
      have htail : ∀ c ∈ bs, c.length = r :=
        fun c hc => hbs c (List.mem_cons_of_mem b hc)
      simp only [List.flatten_cons, List.length_append, List.length_cons, hb, ih htail]
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_comm]

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHornerBody

open TapeMultiProgram TapeRouting TapeRegister TapeHornerMultiply

abbrev ProductState := TapeHornerExtract.State ⊕ TapeHornerMultiply.State
abbrev WorkState := ProductState ⊕ TapeXor.State
abbrev State := WorkState ⊕ TapeErase.State

def product : TapeMultiProgram ProductState :=
  joinCode TapeHornerExtract.program TapeHornerMultiply.program
    (fun _ => TapeHornerMultiply.start)

def work : TapeMultiProgram WorkState :=
  joinCode product (TapeXor.program scratchB accumBits) (fun _ => TapeXor.start)

def program : TapeMultiProgram State :=
  joinCode work (TapeErase.code scratchB) (fun _ => TapeErase.State.start)

def start : State := .inl (.inl (.inl TapeHornerExtract.start))
def done : State := .inr TapeErase.State.done

def cost (r offset : ℕ) : ℕ :=
  r * (2 * offset + r + 19) + TapeHornerMultiply.cost r + 4 * r + 20

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

theorem runs_body (σ : TapeStore) (p h a «prefix» b suffix : List Bool) (r : ℕ)
    (hW : Workspace σ r) (hP : σ polyBits = p) (hH : σ hashBits = h)
    (hA : σ accumBits = a) (hp : p.length = r) (hh : h.length = r)
    (ha : a.length = r) (hb : b.length = r)
    (hsource : σ coeffBits = «prefix» ++ b ++ suffix)
    (hcursor : σ loop3 = List.replicate («prefix».length + r) true)
    (hcount : σ loop4 = []) (hbuffer : σ scratchB = []) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update
        (Function.update σ loop3 (List.replicate «prefix».length true))
        accumBits (hornerStep r p h b a)))) (cost r «prefix».length) := by
  let U := Function.update (Function.update σ loop3 (List.replicate «prefix».length true))
    scratchB b
  let V := Function.update U accumBits (multiplyBitLists r p h a)
  let W := Function.update V accumBits (hornerStep r p h b a)
  have he := TapeHornerExtract.runs_extract σ «prefix» b suffix r hsource hcursor
    hW.degree hb hcount hbuffer
  have hU : Workspace U r := by
    rcases hW with ⟨hd, h0, h1, hi, hj, hk, hs, ho⟩
    constructor <;>
      simp_all [U, Function.update, loop3, scratchB, ringDegree, loop0, loop1,
        indexA, indexB, indexC, scratchA, productBits]
  have hm := TapeHornerMultiply.runs_multiply U p h a r hU
    (by simp [U, hP, polyBits, loop3, scratchB])
    (by simp [U, hH, hashBits, loop3, scratchB])
    (by simp [U, hA, accumBits, loop3, scratchB]) hp hh ha
  have hprod := join_runs TapeHornerExtract.program TapeHornerMultiply.program
    (fun _ => TapeHornerMultiply.start) he rfl hm
  have hx := TapeXor.runs_store (src := scratchB) (dst := accumBits) (by decide)
    V b (multiplyBitLists r p h a)
    (by simp [V, U, scratchB, accumBits]) (by simp [V])
    (by simp [hb])
  have hx' : RunsIn (TapeXor.program scratchB accumBits).step
      (cfg TapeXor.start (storeTapes V)) (cfg TapeXor.done (storeTapes W))
      (2 * r + 4) := by
    simpa only [W, hornerStep, hb] using hx
  have hw := join_runs product (TapeXor.program scratchB accumBits)
    (fun _ => TapeXor.start) hprod rfl hx'
  have hclear := TapeStoreRuns.erase scratchB W
  have hclear' : RunsIn (TapeErase.code scratchB).step
      (cfg TapeErase.State.start (storeTapes W))
      (cfg TapeErase.State.done (storeTapes (Function.update W scratchB [])))
      (2 * r + 5) := by
    simpa [W, V, U, hb, scratchB, accumBits] using hclear
  have hall := join_runs work (TapeErase.code scratchB)
    (fun _ => TapeErase.State.start) hw rfl hclear'
  have hfinal : Function.update W scratchB [] =
      Function.update (Function.update σ loop3 (List.replicate «prefix».length true))
        accumBits (hornerStep r p h b a) := by
    funext q
    by_cases hb' : q = scratchB <;> by_cases ha' : q = accumBits <;>
      by_cases hl : q = loop3 <;>
      simp_all [W, V, U, Function.update, scratchB, accumBits, loop3]
  have htime : ((r * (2 * «prefix».length + r + 19) + 8 + 1 +
      TapeHornerMultiply.cost r) + 1 + (2 * r + 4)) + 1 + (2 * r + 5) =
      cost r «prefix».length := by unfold cost; omega
  simpa only [program, start, done, hfinal, htime] using hall

end TapeHornerBody
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHornerLoop

open TapeMultiProgram TapeRouting TapeRegister TapeUnary TapeArithmetic TapeHornerMultiply

abbrev State := LoopState DecState TapeHornerBody.State

def program : TapeMultiProgram State :=
  loopCode (decProgram loop2) TapeHornerBody.program DecState.start TapeHornerBody.start
    decPositive

def start : State := loopTest DecState.start
def done : State := loopDone

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

def frame (σ : TapeStore) (remaining offset : ℕ) (a : List Bool) : TapeStore :=
  Function.update (Function.update (Function.update σ loop2 (List.replicate remaining true))
    loop3 (List.replicate offset true)) accumBits a

@[simp] theorem frame_count (σ : TapeStore) (k j : ℕ) (a : List Bool) :
    frame σ k j a loop2 = List.replicate k true := by
  simp [frame, loop2, loop3, accumBits]

@[simp] theorem frame_cursor (σ : TapeStore) (k j : ℕ) (a : List Bool) :
    frame σ k j a loop3 = List.replicate j true := by
  simp [frame, loop2, loop3, accumBits]

@[simp] theorem frame_accum (σ : TapeStore) (k j : ℕ) (a : List Bool) :
    frame σ k j a accumBits = a := by simp [frame]

theorem frame_workspace (σ : TapeStore) (k j r : ℕ) (a : List Bool)
    (hW : Workspace σ r) : Workspace (frame σ k j a) r := by
  rcases hW with ⟨hd, h0, h1, hi, hj, hk, hs, ho⟩
  constructor <;>
    simp_all [frame, Function.update, loop2, loop3, accumBits, ringDegree, loop0, loop1,
      indexA, indexB, indexC, scratchA, productBits]

@[simp] theorem update_frame_count (σ : TapeStore) (k k' j : ℕ) (a : List Bool) :
    Function.update (frame σ k j a) loop2 (List.replicate k' true) = frame σ k' j a := by
  funext q
  by_cases h2 : q = loop2 <;> by_cases h3 : q = loop3 <;> by_cases ha : q = accumBits <;>
    simp_all [frame, Function.update, loop2, loop3, accumBits]

@[simp] theorem update_frame_cursor (σ : TapeStore) (k j j' : ℕ) (a : List Bool) :
    Function.update (frame σ k j a) loop3 (List.replicate j' true) = frame σ k j' a := by
  funext q
  by_cases h3 : q = loop3 <;> by_cases ha : q = accumBits <;>
    simp_all [frame, Function.update, loop2, loop3, accumBits]

@[simp] theorem update_frame_accum (σ : TapeStore) (k j : ℕ) (a b : List Bool) :
    Function.update (frame σ k j a) accumBits b = frame σ k j b := by
  simp only [frame, Function.update_idem]

theorem body_cost_mono (r m n : ℕ) (hmn : m ≤ n) :
    TapeHornerBody.cost r m ≤ TapeHornerBody.cost r n := by
  have hm : r * (2 * m + r + 19) ≤ r * (2 * n + r + 19) :=
    Nat.mul_le_mul_left r (by omega)
  unfold TapeHornerBody.cost
  omega

theorem runs_loop (σ : TapeStore) (p h : List Bool) (bs : List (List Bool))
    (suffix a : List Bool) (r N : ℕ)
    (hW : Workspace σ r) (hP : σ polyBits = p) (hH : σ hashBits = h)
    (hp : p.length = r) (hh : h.length = r) (ha : a.length = r)
    (hblocks : ∀ b ∈ bs, b.length = r)
    (hsource : σ coeffBits = bs.flatten ++ suffix)
    (hN : bs.flatten.length ≤ N) (hcount : σ loop4 = []) (hbuffer : σ scratchB = []) :
    RunsIn program.step
      (cfg start (storeTapes (frame σ bs.length bs.flatten.length a)))
      (cfg done (storeTapes (frame σ 0 0 (hornerFrom r p h bs a))))
      (bs.length * (TapeHornerBody.cost r N + 6) + 3) := by
  induction bs using List.reverseRecOn generalizing suffix a with
  | nil =>
      have hd := decrement_empty loop2 (storeTapes (frame σ 0 0 a))
        (by simp [])
      have he := loop_exit (decProgram loop2) TapeHornerBody.program
        DecState.start TapeHornerBody.start decPositive hd rfl rfl
      simpa [program, start, done] using he
  | append_singleton bs b ih =>
      have hb : b.length = r := hblocks b (by simp)
      have hbs : ∀ c ∈ bs, c.length = r := fun c hc =>
        hblocks c (List.mem_append_left [b] hc)
      have hlen : (bs ++ [b]).flatten.length = bs.flatten.length + r := by
        simp [hb]
      have hsrc : σ coeffBits = bs.flatten ++ b ++ suffix := by
        simpa only [List.flatten_append, List.flatten_singleton] using hsource
      have hNb : bs.flatten.length ≤ N := by rw [hlen] at hN; omega
      have hd := decrement loop2
        (storeTapes (frame σ (bs.length + 1) (bs.flatten.length + r) a))
        (bs.length + 1) (by simp [counterTape])
      have hd' : RunsIn (decProgram loop2).step
          (cfg DecState.start (storeTapes (frame σ (bs.length + 1) (bs.flatten.length + r) a)))
          (cfg (DecState.done true) (storeTapes (frame σ bs.length (bs.flatten.length + r) a))) 4 := by
        simpa only [Nat.add_sub_cancel, Nat.zero_lt_succ, decide_true,
          counterTape, ← storeTapes_update, update_frame_count] using hd
      have hbody := TapeHornerBody.runs_body
        (frame σ bs.length (bs.flatten.length + r) a) p h a bs.flatten b suffix r
        (frame_workspace σ _ _ r a hW)
        (by simp [frame, hP, polyBits, loop2, loop3, accumBits])
        (by simp [frame, hH, hashBits, loop2, loop3, accumBits])
        (by simp) hp hh ha hb
        (by simp [frame, hsrc, coeffBits, loop2, loop3, accumBits])
        (by simp)
        (by simp [frame, hcount, loop4, loop2, loop3, accumBits])
        (by simp [frame, hbuffer, scratchB, loop2, loop3, accumBits])
      simp only [update_frame_cursor, update_frame_accum] at hbody
      have hbody' := hbody.mono (body_cost_mono r bs.flatten.length N hNb)
      have hit := loop_iter (decProgram loop2) TapeHornerBody.program
        DecState.start TapeHornerBody.start decPositive hd' rfl rfl hbody' rfl
      have hsrc' : σ coeffBits = bs.flatten ++ (b ++ suffix) := by
        simpa only [List.append_assoc] using hsrc
      have hrest := ih (suffix := b ++ suffix) (a := hornerStep r p h b a)
        (hornerStep_length r p h b a hb) hbs hsrc' hNb
      have hall := hit.trans hrest
      have ht : (4 + 1 + TapeHornerBody.cost r N + 1) +
          (bs.length * (TapeHornerBody.cost r N + 6) + 3) =
          (bs.length + 1) * (TapeHornerBody.cost r N + 6) + 3 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [program, start, done, List.length_append, List.length_singleton, hlen,
        hornerFrom_append_singleton, ht] using hall

end TapeHornerLoop
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHornerPrepare

open TapeMultiProgram TapeRouting TapeRegister TapeUnary TapeHornerMultiply

structure Clean (σ : TapeStore) : Prop where
  count : σ loop2 = []
  cursor : σ loop3 = []
  countScratch : σ loop4 = []
  mulScratch : σ loop5 = []
  coefficient : σ scratchB = []
  accumulator : σ accumBits = []

abbrev ZeroState := TapeCopy.State ⊕ TapeFill.FillState
abbrev CountState := ZeroState ⊕ TapeCopy.State
abbrev CursorState := CountState ⊕ TapeCopy.State
abbrev State := CursorState ⊕ TapeMultiply.State

def zeroProgram : TapeMultiProgram ZeroState :=
  joinCode (TapeCopy.code ringDegree scratchA) (TapeFill.fillProgram scratchA accumBits false)
    (fun _ => TapeFill.fillStart)

def countProgram : TapeMultiProgram CountState :=
  joinCode zeroProgram (TapeCopy.code coeffCount loop2) (fun _ => TapeCopy.State.start)

def cursorProgram : TapeMultiProgram CursorState :=
  joinCode countProgram (TapeCopy.code coeffCount loop4) (fun _ => TapeCopy.State.start)

def program : TapeMultiProgram State :=
  joinCode cursorProgram (TapeMultiply.program loop4 ringDegree loop5 loop3)
    (fun _ => TapeMultiply.start)

def start : State := .inl (.inl (.inl (.inl TapeCopy.State.start)))
def done : State := .inr TapeMultiply.done

def cost (r t : ℕ) : ℕ := t * (10 * r + 18) + 10 * r + 22

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

theorem runs_zero (σ : TapeStore) (r : ℕ)
    (hr : σ ringDegree = List.replicate r true)
    (hs : σ scratchA = []) (ha : σ accumBits = []) :
    RunsIn zeroProgram.step (cfg (.inl TapeCopy.State.start) (storeTapes σ))
      (cfg (.inr TapeFill.fillDone)
        (storeTapes (Function.update σ accumBits (List.replicate r false)))) (10 * r + 8) := by
  let U := Function.update σ scratchA (σ ringDegree)
  have hc := TapeStoreRuns.copy (by decide : ringDegree ≠ scratchA) σ hs
  have hf := TapeStoreRuns.fill (by decide : scratchA ≠ accumBits) false U r
    (by simp [U, hr])
  have hall := join_runs (TapeCopy.code ringDegree scratchA)
    (TapeFill.fillProgram scratchA accumBits false) (fun _ => TapeFill.fillStart) hc rfl hf
  have hfinal : Function.update (Function.update U scratchA []) accumBits
      (List.replicate r false ++ U accumBits) =
      Function.update σ accumBits (List.replicate r false) := by
    have hu : Function.update U scratchA [] = σ := by
      simp only [U, Function.update_idem, ← hs, Function.update_eq_self]
    rw [hu]
    simp [U, ha, accumBits, scratchA]
  have ht : 2 * r + 4 + 1 + (8 * r + 3) = 10 * r + 8 := by omega
  simpa only [zeroProgram, hfinal, hr, List.length_replicate, ht] using hall

theorem runs_prepare (σ : TapeStore) (r t : ℕ) (hW : Workspace σ r) (hC : Clean σ)
    (ht : σ coeffCount = List.replicate t true) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (TapeHornerLoop.frame σ t (t * r) (List.replicate r false))))
      (cost r t) := by
  let U := Function.update σ accumBits (List.replicate r false)
  let V := Function.update U loop2 (List.replicate t true)
  let W := Function.update V loop4 (List.replicate t true)
  have hz := runs_zero σ r hW.degree hW.scratch_empty hC.accumulator
  have hc := TapeStoreRuns.copy (by decide : coeffCount ≠ loop2) U
    (by simp [U, hC.count, accumBits, loop2])
  have hc' : RunsIn (TapeCopy.code coeffCount loop2).step
      (cfg TapeCopy.State.start (storeTapes U)) (cfg TapeCopy.State.done (storeTapes V))
      (2 * t + 4) := by
    simpa [V, U, ht, coeffCount, accumBits] using hc
  have hzc := join_runs zeroProgram (TapeCopy.code coeffCount loop2)
    (fun _ => TapeCopy.State.start) hz rfl hc'
  have hmcopy := TapeStoreRuns.copy (by decide : coeffCount ≠ loop4) V
    (by simp [V, U, hC.countScratch, loop4, loop2, accumBits])
  have hmcopy' : RunsIn (TapeCopy.code coeffCount loop4).step
      (cfg TapeCopy.State.start (storeTapes V)) (cfg TapeCopy.State.done (storeTapes W))
      (2 * t + 4) := by
    simpa [W, V, U, ht, coeffCount, loop2, accumBits] using hmcopy
  have hp := join_runs countProgram (TapeCopy.code coeffCount loop4)
    (fun _ => TapeCopy.State.start) hzc rfl hmcopy'
  have hm := TapeMultiply.runs_mul
    (outer := loop4) (source := ringDegree) (scratch := loop5) (destination := loop3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (storeTapes V) t r 0
  have hi : TapeMultiply.tapes loop4 ringDegree loop5 loop3 (storeTapes V) t r 0 0 =
      storeTapes W := by
    funext q
    by_cases h4 : q = loop4 <;> by_cases hd : q = ringDegree <;>
      by_cases h5 : q = loop5 <;> by_cases h3 : q = loop3 <;>
      simp_all [TapeMultiply.tapes, TapeCopy.onPair, storeTapes, counterTape,
        W, V, U, Function.update, hW.degree, hC.mulScratch, hC.cursor,
        loop4, ringDegree, loop5, loop3, loop2, accumBits]
  have ho : TapeMultiply.tapes loop4 ringDegree loop5 loop3 (storeTapes V) 0 r 0 (0 + t * r) =
      storeTapes (Function.update V loop3 (List.replicate (t * r) true)) := by
    funext q
    by_cases h4 : q = loop4 <;> by_cases hd : q = ringDegree <;>
      by_cases h5 : q = loop5 <;> by_cases h3 : q = loop3 <;>
      simp_all [TapeMultiply.tapes, TapeCopy.onPair, storeTapes, counterTape,
        V, U, Function.update, hW.degree, hC.countScratch, hC.mulScratch,
        loop4, ringDegree, loop5, loop3, loop2, accumBits]
  rw [hi, ho] at hm
  have hall := join_runs cursorProgram (TapeMultiply.program loop4 ringDegree loop5 loop3)
    (fun _ => TapeMultiply.start) hp rfl hm
  have hfinal : Function.update V loop3 (List.replicate (t * r) true) =
      TapeHornerLoop.frame σ t (t * r) (List.replicate r false) := by
    funext q
    by_cases h2 : q = loop2 <;> by_cases h3 : q = loop3 <;> by_cases ha : q = accumBits <;>
      simp_all [V, U, TapeHornerLoop.frame, Function.update, loop2, loop3, accumBits]
  have htime : ((10 * r + 8 + 1 + (2 * t + 4)) + 1 + (2 * t + 4)) +
      1 + (t * (10 * r + 14) + 3) = cost r t := by
    unfold cost
    ring
  simpa only [program, start, done, hfinal, htime] using hall

end TapeHornerPrepare
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeHorner

open TapeMultiProgram TapeRouting TapeRegister TapeHornerMultiply

abbrev State := TapeHornerPrepare.State ⊕ TapeHornerLoop.State

def program : TapeMultiProgram State :=
  joinCode TapeHornerPrepare.program TapeHornerLoop.program (fun _ => TapeHornerLoop.start)

def start : State := .inl TapeHornerPrepare.start
def done : State := .inr TapeHornerLoop.done

def cost (r t : ℕ) : ℕ :=
  TapeHornerPrepare.cost r t + t * (TapeHornerBody.cost r (t * r) + 6) + 4

@[simp] theorem program_done (h : TapeHeads) : program done h = none := rfl

theorem cost_le (r t : ℕ) : cost r t ≤ 1000 * (r + t + 1) ^ 4 := by
  unfold cost TapeHornerPrepare.cost TapeHornerBody.cost TapeHornerMultiply.cost
    TapeConvolve.cost TapeRemainder.cost TapeRemainderOuter.iterationCost
  ring_nf
  omega

theorem runs_horner (σ : TapeStore) (p h : List Bool) (blocks : List (List Bool)) (r : ℕ)
    (hW : Workspace σ r) (hC : TapeHornerPrepare.Clean σ)
    (hP : σ polyBits = p) (hH : σ hashBits = h)
    (hB : σ coeffBits = blocks.flatten)
    (hT : σ coeffCount = List.replicate blocks.length true)
    (hp : p.length = r) (hh : h.length = r)
    (hblocks : ∀ b ∈ blocks, b.length = r) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg done (storeTapes (Function.update σ accumBits (hornerBitLists r p h blocks))))
      (cost r blocks.length) := by
  have hlen := block_flatten_length r blocks hblocks
  have hpref := TapeHornerPrepare.runs_prepare σ r blocks.length hW hC hT
  have hl := TapeHornerLoop.runs_loop σ p h blocks [] (List.replicate r false)
    r (blocks.length * r) hW hP hH hp hh (by simp) hblocks
    (by simpa only [List.append_nil] using hB) (by omega) hC.countScratch hC.coefficient
  rw [hlen, hornerFrom_zero_eq_hornerBitLists r p h blocks hblocks] at hl
  have hfinal : TapeHornerLoop.frame σ 0 0 (hornerBitLists r p h blocks) =
      Function.update σ accumBits (hornerBitLists r p h blocks) := by
    funext q
    by_cases h2 : q = loop2 <;> by_cases h3 : q = loop3 <;> by_cases ha : q = accumBits <;>
      simp_all [TapeHornerLoop.frame, Function.update, hC.count, hC.cursor,
        loop2, loop3, accumBits]
  rw [hfinal] at hl
  have hall := join_runs TapeHornerPrepare.program TapeHornerLoop.program
    (fun _ => TapeHornerLoop.start) hpref rfl hl
  have ht : TapeHornerPrepare.cost r blocks.length + 1 +
      (blocks.length * (TapeHornerBody.cost r (blocks.length * r) + 6) + 3) =
      cost r blocks.length := by unfold cost; omega
  simpa only [program, start, done, ht] using hall

end TapeHorner
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeOutput

open TapeMultiProgram TapeRouting

abbrev State := TapeArray.State ⊕ Bool

def haltProgram : TapeMultiProgram Bool := fun _ _ => none

def acceptFlag : TapeArray.State → Bool
  | .done b => !b
  | _ => false

def program : TapeMultiProgram State :=
  joinCode (TapeArray.code TapeRegister.indexA TapeRegister.accumBits id)
    haltProgram acceptFlag

def start : State := .inl .start
def done (answer : Bool) : State := .inr answer

@[simp] theorem program_done (answer : Bool) (h : TapeHeads) :
    program (done answer) h = none := rfl

theorem runs_output (σ : TapeStore) (b : Bool) (tail : List Bool)
    (hi : σ TapeRegister.indexA = [])
    (ha : σ TapeRegister.accumBits = b :: tail) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg (done (!b)) (storeTapes σ)) 5 := by
  have hr := TapeProductTerm.read_at
    (index := TapeRegister.indexA) (array := TapeRegister.accumBits)
    (by decide) (storeTapes σ) [] tail b
    (by simp [storeTapes, TapeUnary.counterTape, hi])
    (by simp [storeTapes, ha])
  have hh := join_runs (TapeArray.code TapeRegister.indexA TapeRegister.accumBits id)
    haltProgram acceptFlag hr rfl
    (RunsIn.refl haltProgram.step (cfg (!b) (storeTapes σ)))
  simpa only [State, program, start, done, acceptFlag, List.length_nil, Nat.mul_zero,
    Nat.zero_add, Nat.add_zero] using hh

end TapeOutput
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

private theorem list_eq_ofFn_of_getD {n : ℕ} (xs : List Bool) (f : Fin n → Bool)
    (hlen : xs.length = n) (hread : ∀ i, xs.getD i.val false = f i) :
    xs = List.ofFn f := by
  have heq : listWord n xs = f := by
    funext i
    exact hread i
  exact (wordList_listWord xs hlen).symm.trans (congrArg wordList heq)

theorem inputBlockData_data_length {w : List Bool} (hfit : InputFits w) :
    (inputBlockData w .data).length = (decodeInput w).dataSize :=
  inputBlockData_length hfit .data

theorem inputBlockData_hash_length {w : List Bool} (hfit : InputFits w) :
    (inputBlockData w .hash).length =
      (decodeInput w).dataSize + (decodeInput w).ringDegree - 1 :=
  inputBlockData_length hfit .hash

theorem inputBlockData_polynomial_length {w : List Bool} (hfit : InputFits w) :
    (inputBlockData w .polynomial).length = (decodeInput w).ringDegree :=
  inputBlockData_length hfit .polynomial

theorem inputBlockData_coefficients_length {w : List Bool} (hfit : InputFits w) :
    (inputBlockData w .coefficients).length =
      (decodeInput w).coefficientCount * (decodeInput w).ringDegree :=
  inputBlockData_length hfit .coefficients

theorem decoded_ringDegree_ne_zero {w : List Bool} (hfit : InputFits w) :
    (decodeInput w).ringDegree ≠ 0 :=
  Nat.ne_of_gt (decoded_ringDegree_pos hfit)

theorem inputBlockData_data_eq_ofFn {w : List Bool} (hfit : InputFits w) :
    inputBlockData w .data = List.ofFn (decodeInput w).data :=
  list_eq_ofFn_of_getD _ _ (inputBlockData_data_length hfit)
    (inputBlockData_data w)

theorem inputBlockData_hash_eq_ofFn {w : List Bool} (hfit : InputFits w) :
    inputBlockData w .hash = List.ofFn (decodeInput w).hashSeed :=
  list_eq_ofFn_of_getD _ _ (inputBlockData_hash_length hfit)
    (inputBlockData_hash w)

theorem inputBlockData_polynomial_eq_ofFn {w : List Bool} (hfit : InputFits w) :
    inputBlockData w .polynomial = List.ofFn (decodeInput w).polynomial :=
  list_eq_ofFn_of_getD _ _ (inputBlockData_polynomial_length hfit)
    (inputBlockData_polynomial w)

def decodedCoefficientBlocks (w : List Bool) : List (List Bool) :=
  List.ofFn fun j => List.ofFn ((decodeInput w).coefficients j)

@[simp] theorem decodedCoefficientBlocks_length (w : List Bool) :
    (decodedCoefficientBlocks w).length = (decodeInput w).coefficientCount := by
  simp only [decodedCoefficientBlocks, List.length_ofFn]

theorem decodedCoefficientBlocks_row_length (w : List Bool) :
    ∀ b ∈ decodedCoefficientBlocks w, b.length = (decodeInput w).ringDegree := by
  intro b hb
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
  exact List.length_ofFn

@[simp] theorem decodedCoefficientBlocks_flatten_length (w : List Bool) :
    (decodedCoefficientBlocks w).flatten.length =
      (decodeInput w).coefficientCount * (decodeInput w).ringDegree := by
  rw [block_flatten_length _ _ (decodedCoefficientBlocks_row_length w),
    decodedCoefficientBlocks_length]

theorem inputBlockData_coefficients_eq_flatten {w : List Bool} (hfit : InputFits w) :
    inputBlockData w .coefficients = (decodedCoefficientBlocks w).flatten := by
  have heq : inputBlockData w .coefficients = List.ofFn
      (fun i : Fin ((decodeInput w).coefficientCount * (decodeInput w).ringDegree) =>
        (inputBlockData w .coefficients).getD i.val false) :=
    list_eq_ofFn_of_getD _ _ (inputBlockData_coefficients_length hfit) (fun _ => rfl)
  rw [heq, List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  apply congrArg List.ofFn
  funext i
  exact inputBlockData_coefficients w j i

theorem hornerBitLists_ofFn {r t : ℕ} (p h : BitWord r) (b : Fin t → BitWord r) :
    hornerBitLists r (List.ofFn p) (List.ofFn h) (List.ofFn fun j => List.ofFn (b j)) =
      List.ofFn (wordHorner p h t b) := by
  have hp : listWord r (List.ofFn p) = p := listWord_wordList p
  have hh : listWord r (List.ofFn h) = h := listWord_wordList h
  have hb : (fun j : Fin t => listWord r
      ((List.ofFn fun j => List.ofFn (b j)).getD j.val [])) = b := by
    funext j
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left j.isLt,
      Option.getD_some]
    exact listWord_wordList (b j)
  unfold hornerBitLists
  rw [List.length_ofFn]
  simp only [hp, hh, hb]
  rfl

theorem hashByUpdates_inputBlocks {w : List Bool} (hfit : InputFits w) :
    hashByUpdates (decodeInput w).ringDegree
        (inputBlockData w .hash) (inputBlockData w .data) =
      List.ofFn (wordHash (decodeInput w).hashSeed (decodeInput w).data) := by
  rw [inputBlockData_hash_eq_ofFn hfit, inputBlockData_data_eq_ofFn hfit]
  exact hashByUpdates_ofFn_eq _ _

theorem hornerBitLists_inputBlocks {w : List Bool} (hfit : InputFits w) :
    hornerBitLists (decodeInput w).ringDegree (inputBlockData w .polynomial)
        (hashByUpdates (decodeInput w).ringDegree
          (inputBlockData w .hash) (inputBlockData w .data))
        (decodedCoefficientBlocks w) =
      List.ofFn (decodeInput w).evaluationBits := by
  rw [inputBlockData_polynomial_eq_ofFn hfit, hashByUpdates_inputBlocks hfit]
  exact hornerBitLists_ofFn _ _ _

theorem hornerFrom_inputBlocks {w : List Bool} (hfit : InputFits w) :
    hornerFrom (decodeInput w).ringDegree (inputBlockData w .polynomial)
        (hashByUpdates (decodeInput w).ringDegree
          (inputBlockData w .hash) (inputBlockData w .data))
        (decodedCoefficientBlocks w)
        (List.replicate (decodeInput w).ringDegree false) =
      List.ofFn (decodeInput w).evaluationBits := by
  rw [hornerFrom_zero_eq_hornerBitLists _ _ _ _ (decodedCoefficientBlocks_row_length w)]
  exact hornerBitLists_inputBlocks hfit

theorem evaluateBits_eq_final_bit {w : List Bool} (hfit : InputFits w) :
    (decodeInput w).evaluateBits =
      !((hornerBitLists (decodeInput w).ringDegree (inputBlockData w .polynomial)
        (hashByUpdates (decodeInput w).ringDegree
          (inputBlockData w .hash) (inputBlockData w .data))
        (decodedCoefficientBlocks w)).getD 0 false) := by
  rw [hornerBitLists_inputBlocks hfit]
  change Bool.not (wordGet (decodeInput w).evaluationBits 0) =
    Bool.not ((wordList (decodeInput w).evaluationBits).getD 0 false)
  rw [wordList_getD]

theorem language_eq_final_bit {w : List Bool} (hfit : InputFits w) :
    language w =
      !((hornerBitLists (decodeInput w).ringDegree (inputBlockData w .polynomial)
        (hashByUpdates (decodeInput w).ringDegree
          (inputBlockData w .hash) (inputBlockData w .data))
        (decodedCoefficientBlocks w)).getD 0 false) := by
  simpa only [language, parseInput_of_fits hfit] using
    ((ParsedInput.evaluateBits_eq (decodeInput w)).symm.trans
      (evaluateBits_eq_final_bit hfit))

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace TapeEvaluation

open TapeMultiProgram TapeRouting TapeRegister

structure Prepared (σ : TapeStore) (w : List Bool) : Prop where
  workspace : TapeHornerMultiply.Workspace σ (decodeInput w).ringDegree
  clean : TapeHornerPrepare.Clean σ
  data_length : σ dataLength = List.replicate (decodeInput w).dataSize true
  coefficient_count : σ coeffCount = List.replicate (decodeInput w).coefficientCount true
  data_bits : σ dataBits = inputBlockData w .data
  key_bits : σ keyBits = inputBlockData w .hash
  polynomial_bits : σ polyBits = inputBlockData w .polynomial
  coefficient_bits : σ coeffBits = inputBlockData w .coefficients
  hash_empty : σ hashBits = []

abbrev WorkState := TapeHashClean.State ⊕ TapeHorner.State
abbrev State := WorkState ⊕ TapeOutput.State

def work : TapeMultiProgram WorkState :=
  joinCode TapeHashClean.program TapeHorner.program (fun _ => TapeHorner.start)

def program : TapeMultiProgram State :=
  joinCode work TapeOutput.program (fun _ => TapeOutput.start)

def start : State := .inl (.inl TapeHashClean.start)
def done (answer : Bool) : State := .inr (TapeOutput.done answer)

def acceptFlag : State → Bool
  | .inr (.inr b) => b
  | _ => false

@[simp] theorem acceptFlag_done (b : Bool) : acceptFlag (done b) = b := rfl
@[simp] theorem program_done (b : Bool) (h : TapeHeads) : program (done b) h = none := rfl

def hashWord (w : List Bool) : List Bool :=
  List.ofFn (wordHash (decodeInput w).hashSeed (decodeInput w).data)

def evaluationWord (w : List Bool) : List Bool := List.ofFn (decodeInput w).evaluationBits

def outputStore (σ : TapeStore) (w : List Bool) : TapeStore :=
  Function.update (Function.update σ hashBits (hashWord w)) accumBits (evaluationWord w)

def cost (w : List Bool) : ℕ :=
  210 * ((decodeInput w).dataSize + (decodeInput w).ringDegree + 1) ^ 3 +
    TapeHorner.cost (decodeInput w).ringDegree (decodeInput w).coefficientCount + 7

theorem cost_le (w : List Bool) : cost w ≤ 20000 * (w.length + 1) ^ 4 := by
  let d := (decodeInput w).dataSize
  let r := (decodeInput w).ringDegree
  let t := (decodeInput w).coefficientCount
  let N := w.length + 1
  have hd : d ≤ w.length := by
    have h := five_mul_dataDimension_le w.length
    change dataDimension w.length ≤ w.length
    omega
  have hr : r ≤ d := hashDimension_le d
  have ht : t ≤ d := independenceOrder_le d
  have h3 := Nat.pow_le_pow_left (show d + r + 1 ≤ 2 * N by dsimp [N]; omega) 3
  have h4 := Nat.pow_le_pow_left (show r + t + 1 ≤ 2 * N by dsimp [N]; omega) 4
  have h34 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right (by dsimp [N]; omega) (by decide)
  have h14 : 1 ≤ N ^ 4 := by
    simpa using Nat.pow_le_pow_left (show 1 ≤ N by dsimp [N]; omega) 4
  have hH := TapeHorner.cost_le r t
  simp only [mul_pow, show (2 : ℕ) ^ 3 = 8 by decide] at h3
  simp only [mul_pow, show (2 : ℕ) ^ 4 = 16 by decide] at h4
  change 210 * (d + r + 1) ^ 3 + TapeHorner.cost r t + 7 ≤ 20000 * N ^ 4
  omega

theorem runs_evaluate_cost (w : List Bool) (σ : TapeStore)
    (hfit : InputFits w) (hprep : Prepared σ w) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg (done (language w)) (storeTapes (outputStore σ w))) (cost w) := by
  let q := decodeInput w
  let H := hashWord w
  let E := evaluationWord w
  let U := Function.update σ hashBits H
  let V := outputStore σ w
  have hhash := TapeHashClean.runs_wordHash σ q.hashSeed q.data
    hprep.data_length hprep.workspace.degree hprep.workspace.indexA_empty
    hprep.workspace.indexB_empty hprep.workspace.indexC_empty
    hprep.workspace.scratch_empty hprep.hash_empty
    (hprep.key_bits.trans (inputBlockData_hash_eq_ofFn hfit))
    (hprep.data_bits.trans (inputBlockData_data_eq_ofFn hfit))
  have hW : TapeHornerMultiply.Workspace U q.ringDegree := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [U, ringDegree, hashBits] using hprep.workspace.degree
    · simpa [U, loop0, hashBits] using hprep.workspace.loop0_empty
    · simpa [U, loop1, hashBits] using hprep.workspace.loop1_empty
    · simpa [U, indexA, hashBits] using hprep.workspace.indexA_empty
    · simpa [U, indexB, hashBits] using hprep.workspace.indexB_empty
    · simpa [U, indexC, hashBits] using hprep.workspace.indexC_empty
    · simpa [U, scratchA, hashBits] using hprep.workspace.scratch_empty
    · simpa [U, productBits, hashBits] using hprep.workspace.product_empty
  have hC : TapeHornerPrepare.Clean U := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [U, loop2, hashBits] using hprep.clean.count
    · simpa [U, loop3, hashBits] using hprep.clean.cursor
    · simpa [U, loop4, hashBits] using hprep.clean.countScratch
    · simpa [U, loop5, hashBits] using hprep.clean.mulScratch
    · simpa [U, scratchB, hashBits] using hprep.clean.coefficient
    · simpa [U, accumBits, hashBits] using hprep.clean.accumulator
  have hhorner := TapeHorner.runs_horner U (inputBlockData w .polynomial) H
    (decodedCoefficientBlocks w) q.ringDegree hW hC
    (by simp [U, hprep.polynomial_bits, polyBits, hashBits]) (by simp [U])
    (by simpa [U, hprep.coefficient_bits, coeffBits, hashBits] using
      inputBlockData_coefficients_eq_flatten hfit)
    (by simpa [U, decodedCoefficientBlocks_length, coeffCount, hashBits] using
      hprep.coefficient_count)
    (inputBlockData_polynomial_length hfit) (by simp [H, hashWord, q])
    (decodedCoefficientBlocks_row_length w)
  have hsemantic : hornerBitLists q.ringDegree (inputBlockData w .polynomial) H
      (decodedCoefficientBlocks w) = E := by
    simpa only [hashByUpdates_inputBlocks hfit, H, E, hashWord, evaluationWord, q] using
      hornerBitLists_inputBlocks hfit
  have hhorner' : RunsIn TapeHorner.program.step (cfg TapeHorner.start (storeTapes U))
      (cfg TapeHorner.done (storeTapes V)) (TapeHorner.cost q.ringDegree q.coefficientCount) := by
    simpa only [hsemantic, decodedCoefficientBlocks_length, V, outputStore, U, E, H] using hhorner
  have hwork := join_runs TapeHashClean.program TapeHorner.program
    (fun _ => TapeHorner.start) hhash rfl hhorner'
  have hlen : E.length = q.ringDegree := by simp [E, evaluationWord, q]
  have hpos : 0 < E.length := by rw [hlen]; exact decoded_ringDegree_pos hfit
  have hsplit : E = E.getD 0 false :: E.drop 1 := by
    simpa using TapeNaturalAccess.split E 0 hpos
  have hout := TapeOutput.runs_output V (E.getD 0 false) (E.drop 1)
    (by simp [V, outputStore, hprep.workspace.indexA_empty, indexA, hashBits, accumBits])
    (by simpa [V, outputStore, E] using hsplit)
  have hlanguage : language w = !(E.getD 0 false) := by
    have hl := language_eq_final_bit hfit
    rw [hashByUpdates_inputBlocks hfit] at hl
    change language w = !((hornerBitLists q.ringDegree
      (inputBlockData w .polynomial) H (decodedCoefficientBlocks w)).getD 0 false) at hl
    simpa only [hsemantic] using hl
  rw [← hlanguage] at hout
  have hall := join_runs work TapeOutput.program (fun _ => TapeOutput.start) hwork rfl hout
  have htime : (210 * (q.dataSize + q.ringDegree + 1) ^ 3 + 1 +
      TapeHorner.cost q.ringDegree q.coefficientCount) + 1 + 5 = cost w := by
    unfold cost
    dsimp [q]
    omega
  simpa only [program, start, done, htime, V] using hall

theorem runs_evaluate (w : List Bool) (σ : TapeStore)
    (hfit : InputFits w) (hprep : Prepared σ w) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg (done (language w)) (storeTapes (outputStore σ w)))
      (20000 * (w.length + 1) ^ 4) :=
  (runs_evaluate_cost w σ hfit hprep).mono (cost_le w)

end TapeEvaluation
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound
namespace TapeBranch

open TapeMultiProgram

abbrev State (Q : Type uDepth1) (R : Type uDepth2) := Q ⊕ (R ⊕ Unit)

def test {Q : Type uDepth3} {R : Type uDepth4} (q : Q) : State Q R := .inl q
def body {Q : Type uDepth5} {R : Type uDepth6} (r : R) : State Q R := .inr (.inl r)
def rejected {Q : Type uDepth7} {R : Type uDepth8} : State Q R := .inr (.inr ())

def program {Q : Type uDepth9} {R : Type uDepth10} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (entry : R) (accept : Q → Bool) : TapeMultiProgram (State Q R)
  | .inl q, h =>
      match P q h with
      | none => jump (if accept q then body entry else rejected) h
      | some (q', writes, moves) => some (test q', writes, moves)
  | .inr (.inl r), h => (B r h).map fun out => (body out.1, out.2)
  | .inr (.inr _), _ => none

@[simp] theorem rejected_halts {Q : Type uDepth11} {R : Type uDepth12} (P : TapeMultiProgram Q)
    (B : TapeMultiProgram R) (entry : R) (accept : Q → Bool) (h : TapeHeads) :
    program P B entry accept rejected h = none := rfl

theorem body_halts {Q : Type uDepth13} {R : Type uDepth14} (P : TapeMultiProgram Q)
    (B : TapeMultiProgram R) (entry : R) (accept : Q → Bool)
    (r : R) (h : TapeHeads) (hr : B r h = none) :
    program P B entry accept (body r) h = none := by
  simp only [program, body, hr, Option.map_none]

theorem runs_test {Q : Type uDepth15} {R : Type uDepth16} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (entry : R) (accept : Q → Bool) {q q' : Q} {T U : TapeTapes} {m : ℕ}
    (h : RunsIn P.step (cfg q T) (cfg q' U) m) :
    RunsIn (program P B entry accept).step (cfg (test q) T) (cfg (test q') U) m :=
  runs_map P _ test (by
    intro a heads a' writes moves he
    simp only [program, test, he]) h

theorem runs_reject {Q : Type uDepth17} {R : Type uDepth18} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (entry : R) (accept : Q → Bool) {q q' : Q} {T U : TapeTapes} {m : ℕ}
    (h : RunsIn P.step (cfg q T) (cfg q' U) m)
    (hhalt : P q' (heads U) = none) (hno : accept q' = false) :
    RunsIn (program P B entry accept).step (cfg (test q) T) (cfg rejected U) (m + 1) := by
  have ht := runs_test P B entry accept h
  have he := RunsIn.single (step_jump (program P B entry accept) (test q') rejected U
    (by simp [program, test, hhalt, hno]))
  exact ht.trans he

theorem runs_accept {Q : Type uDepth19} {R : Type uDepth20} (P : TapeMultiProgram Q) (B : TapeMultiProgram R)
    (entry : R) (accept : Q → Bool) {q q' : Q} {r : R} {T U V : TapeTapes} {m n : ℕ}
    (hP : RunsIn P.step (cfg q T) (cfg q' U) m)
    (hhalt : P q' (heads U) = none) (hyes : accept q' = true)
    (hB : RunsIn B.step (cfg entry U) (cfg r V) n) :
    RunsIn (program P B entry accept).step (cfg (test q) T) (cfg (body r) V)
      (m + 1 + n) := by
  have ht := runs_test P B entry accept hP
  have he := RunsIn.single (step_jump (program P B entry accept) (test q') (body entry) U
    (by simp [program, test, hhalt, hyes]))
  have hb := runs_map B (program P B entry accept) body (by
    intro a heads a' writes moves hcode
    simp only [program, body, hcode, Option.map_some]) hB
  exact (ht.trans he).trans hb

end TapeBranch
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace MachineLanguage

open TapeMultiProgram TapeRouting TapeRegister

theorem decoded_prepared (w : List Bool) :
    TapeEvaluation.Prepared (TapeDecodeParsed.outputStore w) w := by
  constructor
  · constructor
    · exact TapeDecodeParsed.outputStore_hash w
    all_goals apply TapeDecodeParsed.outputStore_empty <;> decide
  · constructor
    all_goals apply TapeDecodeParsed.outputStore_empty <;> decide
  · exact TapeDecodeParsed.outputStore_data w
  · exact TapeDecodeParsed.outputStore_order w
  · exact TapeDecodeParsed.outputStore_block w .data
  · exact TapeDecodeParsed.outputStore_block w .hash
  · exact TapeDecodeParsed.outputStore_block w .polynomial
  · exact TapeDecodeParsed.outputStore_block w .coefficients
  · apply TapeDecodeParsed.outputStore_empty <;> decide

abbrev BodyState := TapeDecodeBlocks.State ⊕ TapeEvaluation.State

def bodyProgram : TapeMultiProgram BodyState :=
  joinCode TapeDecodeBlocks.program TapeEvaluation.program (fun _ => TapeEvaluation.start)

def bodyStart : BodyState := .inl TapeDecodeBlocks.start
def bodyDone (answer : Bool) : BodyState := .inr (TapeEvaluation.done answer)

@[simp] theorem bodyProgram_done (answer : Bool) (h : TapeHeads) :
    bodyProgram (bodyDone answer) h = none := rfl

theorem runs_body (w : List Bool) (hfit : InputFits w) :
    RunsIn bodyProgram.step (cfg bodyStart (storeTapes (TapeParse.outputStore w)))
      (cfg (bodyDone (language w)) (storeTapes
        (TapeEvaluation.outputStore (TapeDecodeParsed.outputStore w) w)))
      (21000 * (w.length + 1) ^ 4) := by
  have hd := TapeDecodeParsed.runs_decode w hfit
  have he := TapeEvaluation.runs_evaluate w (TapeDecodeParsed.outputStore w)
    hfit (decoded_prepared w)
  have hall := join_runs TapeDecodeBlocks.program TapeEvaluation.program
    (fun _ => TapeEvaluation.start) hd (by simp) he
  apply hall.mono
  have h24 : (w.length + 1) ^ 2 ≤ (w.length + 1) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hpos : 1 ≤ (w.length + 1) ^ 4 := Nat.pow_pos (Nat.succ_pos _)
  omega

abbrev State := TapeBranch.State TapeParse.State BodyState

def program : TapeMultiProgram State :=
  TapeBranch.program TapeParse.program bodyProgram bodyStart TapeParse.acceptFlag

def start : State := TapeBranch.test TapeParse.start

def acceptFlag : State → Bool
  | .inr (.inl (.inr q)) => TapeEvaluation.acceptFlag q
  | _ => false

private instance stateFintype : Fintype State := by
  letI : Fintype TapeParse.State := inferInstance
  letI : Fintype TapeDecodeBlocks.State := inferInstance
  letI : Fintype TapeHornerMultiply.WorkState := inferInstance
  letI : Fintype TapeHorner.State := inferInstance
  infer_instance

def machine : FiniteMultiTapeMachine := TapeMultiProgram.machine program start acceptFlag

@[simp] theorem machine_init (w : List Bool) :
    machine.init w = cfg start (rawInputTapes w) := rfl

theorem halts (w : List Bool) :
    MultiTapeHaltsIn machine w (language w) (24000 * (w.length + 3) ^ 8) := by
  apply (multiTapeHaltsIn_iff_runsIn machine w (language w) _).2
  have hp := TapeParse.runs_parse w
  have hpos : 1 ≤ (w.length + 3) ^ 8 := Nat.pow_pos (by omega)
  by_cases hfit : InputFits w
  · have hflag : decide (InputFits w) = true := by simp [hfit]
    rw [hflag] at hp
    have hb := runs_body w hfit
    have hall := TapeBranch.runs_accept TapeParse.program bodyProgram bodyStart
      TapeParse.acceptFlag hp (by simp) (by simp) hb
    refine ⟨cfg (TapeBranch.body (bodyDone (language w)))
      (storeTapes (TapeEvaluation.outputStore (TapeDecodeParsed.outputStore w) w)),
      hall.mono ?_, ?_, ?_⟩
    · have h48 : (w.length + 1) ^ 4 ≤ (w.length + 3) ^ 8 :=
        Nat.le_trans (Nat.pow_le_pow_left (by omega : w.length + 1 ≤ w.length + 3) 4)
          (Nat.pow_le_pow_right (by omega : 0 < w.length + 3) (by decide : 4 ≤ 8))
      omega
    · apply (multiTapeStep_eq_none_iff program _).2
      exact TapeBranch.body_halts _ _ _ _ _ _ (by simp)
    · change acceptFlag (TapeBranch.body (bodyDone (language w))) = language w
      simp [acceptFlag, TapeBranch.body, bodyDone]
  · have hflag : decide (InputFits w) = false := by simp [hfit]
    rw [hflag] at hp
    have hall := TapeBranch.runs_reject TapeParse.program bodyProgram bodyStart
      TapeParse.acceptFlag hp (by simp) (by simp)
    refine ⟨cfg TapeBranch.rejected (storeTapes (TapeParse.outputStore w)),
      hall.mono ?_, ?_, ?_⟩
    · omega
    · apply (multiTapeStep_eq_none_iff program _).2
      exact TapeBranch.rejected_halts _ _ _ _ _
    · change false = language w
      exact (language_of_not_fits hfit).symm

theorem cost_le_standard (n : ℕ) :
    24000 * (n + 3) ^ 8 ≤ (24000 * 3 ^ 8) * (n + 1) ^ 8 := by
  calc
    24000 * (n + 3) ^ 8 ≤ 24000 * (3 * (n + 1)) ^ 8 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 8)
    _ = _ := by rw [mul_pow]; ring

theorem polynomial_time : MultiTapePolynomialTimeDecider language := by
  refine ⟨machine, 24000 * 3 ^ 8, 8, by decide, by decide, ?_⟩
  intro w
  exact (halts w).mono (cost_le_standard w.length)

end MachineLanguage

theorem language_polynomial_time : MultiTapePolynomialTimeDecider language :=
  MachineLanguage.polynomial_time

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

abbrev Clause (V : Type uDepth1) := Finset (Literal V)
abbrev CNF (V : Type uDepth2) := List (Clause V)

variable {V : Type uDepth3}

namespace Literal

def compl (l : Literal V) : Literal V := (l.1, !l.2)

@[simp] theorem eval_eq_true (l : Literal V) (x : Cube V) :
    l.eval x = true ↔ x l.1 = l.2 := by simp [eval]

@[simp] theorem compl_compl (l : Literal V) : l.compl.compl = l := by
  cases l with
  | mk v b => cases b <;> rfl

@[simp] theorem eval_compl (l : Literal V) (x : Cube V) :
    l.compl.eval x = !(l.eval x) := by
  rcases l with ⟨v, b⟩
  cases b <;> cases h : x v <;> simp [compl, eval, h]

end Literal

namespace Clause

noncomputable def eval (C : Clause V) (x : Cube V) : Bool := by
  classical
  exact decide (∃ l ∈ C, l.eval x = true)

noncomputable def scope (C : Clause V) : Finset V := by
  classical
  exact C.image Prod.fst

noncomputable def width (C : Clause V) : ℕ := C.scope.card

def Normalized (C : Clause V) : Prop :=
  ∀ v, (v, false) ∈ C → (v, true) ∈ C → False

@[simp] theorem eval_eq_true (C : Clause V) (x : Cube V) :
    C.eval x = true ↔ ∃ l ∈ C, x l.1 = l.2 := by
  classical
  simp [eval]

@[simp] theorem eval_empty (x : Cube V) : (∅ : Clause V).eval x = false := by
  simp [eval]

@[simp] theorem scope_empty : (∅ : Clause V).scope = ∅ := by
  classical
  simp [scope]

@[simp] theorem width_empty : (∅ : Clause V).width = 0 := by
  simp [width]

@[simp] theorem eval_singleton (l : Literal V) (x : Cube V) :
    ({l} : Clause V).eval x = l.eval x := by
  classical
  simp [eval, Literal.eval]

theorem eval_mono {C D : Clause V} (h : C ⊆ D) {x : Cube V}
    (hx : C.eval x = true) : D.eval x = true := by
  rw [eval_eq_true] at hx ⊢
  obtain ⟨l, hl, hx⟩ := hx
  exact ⟨l, h hl, hx⟩

theorem Normalized.subset {C D : Clause V} (hD : D.Normalized) (h : C ⊆ D) :
    C.Normalized := by
  intro v hf ht
  exact hD v (h hf) (h ht)

theorem Normalized.fst_injOn {C : Clause V} (h : C.Normalized) :
    Set.InjOn Prod.fst (↑C : Set (Literal V)) := by
  rintro ⟨v, b⟩ hb ⟨w, c⟩ hc hv
  change v = w at hv
  subst w
  cases b <;> cases c
  · rfl
  · exact (h v hb hc).elim
  · exact (h v hc hb).elim
  · rfl

theorem Normalized.card_eq_width {C : Clause V} (h : C.Normalized) :
    C.card = C.width := by
  classical
  exact (Finset.card_image_of_injOn h.fst_injOn).symm

theorem scope_mono {C D : Clause V} (h : C ⊆ D) : C.scope ⊆ D.scope := by
  classical
  exact Finset.image_subset_image h

theorem width_mono {C D : Clause V} (h : C ⊆ D) : C.width ≤ D.width :=
  Finset.card_le_card (scope_mono h)

end Clause

namespace CNF

noncomputable def eval (H : CNF V) (x : Cube V) : Bool := by
  classical
  exact decide (∀ C ∈ H, C.eval x = true)

def WidthAtMost (H : CNF V) (b : ℕ) : Prop := ∀ C ∈ H, C.width ≤ b

def Normalized (H : CNF V) : Prop := ∀ C ∈ H, C.Normalized

@[simp] theorem eval_eq_true (H : CNF V) (x : Cube V) :
    H.eval x = true ↔ ∀ C ∈ H, C.eval x = true := by
  classical
  simp [eval]

@[simp] theorem eval_nil (x : Cube V) : CNF.eval ([] : CNF V) x = true := by
  simp [eval]

@[simp] theorem eval_cons (C : Clause V) (H : CNF V) (x : Cube V) :
    CNF.eval (C :: H) x = (C.eval x && H.eval x) := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [eval_eq_true, Bool.and_eq_true, eval_eq_true]
  constructor
  · intro h
    exact ⟨h C (by simp), fun D hD => h D (by simp [hD])⟩
  · rintro ⟨hc, hH⟩ D hD
    rcases List.mem_cons.mp hD with hD | hD
    · simpa only [hD] using hc
    · exact hH D hD

@[simp] theorem eval_append (H J : CNF V) (x : Cube V) :
    (H ++ J).eval x = (H.eval x && J.eval x) := by
  induction H with
  | nil => simp
  | cons C H ih => simp [ih, Bool.and_assoc]

theorem eval_antitone {H J : CNF V} (h : H ⊆ J) {x : Cube V}
    (hx : J.eval x = true) : H.eval x = true := by
  rw [eval_eq_true] at hx ⊢
  exact fun C hC => hx C (h hC)

theorem WidthAtMost.mono {H : CNF V} {b c : ℕ} (h : H.WidthAtMost b)
    (hbc : b ≤ c) : H.WidthAtMost c := fun C hC => (h C hC).trans hbc

end CNF

def indicator (b : Bool) : ℝ := if b then 1 else 0
def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem indicator_false : indicator false = 0 := rfl
@[simp] theorem indicator_true : indicator true = 1 := rfl
@[simp] theorem sign_false : sign false = -1 := rfl
@[simp] theorem sign_true : sign true = 1 := rfl

@[simp] theorem indicator_and (b c : Bool) :
    indicator (b && c) = indicator b * indicator c := by
  cases b <;> cases c <;> simp [indicator]

theorem indicator_nonneg (b : Bool) : 0 ≤ indicator b := by
  cases b <;> simp [indicator]

theorem indicator_le_one (b : Bool) : indicator b ≤ 1 := by
  cases b <;> simp [indicator]

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

abbrev Restriction (V : Type uDepth1) := V → Option Bool
abbrev Live {V : Type uDepth2} (σ : Restriction V) := {v : V // σ v = none}

def fill {V : Type uDepth3} (σ : Restriction V) (z : Cube (Live σ)) : Cube V :=
  fun v => if h : σ v = none then z ⟨v, h⟩ else (σ v).getD false

@[simp] theorem fill_live {V : Type uDepth4} (σ : Restriction V) (z : Cube (Live σ))
    (v : Live σ) : fill σ z v.val = z v := by
  simp [fill, v.property]

@[simp] theorem fill_fixed {V : Type uDepth5} (σ : Restriction V) (z : Cube (Live σ))
    (v : V) (b : Bool) (h : σ v = some b) : fill σ z v = b := by
  simp [fill, h]

def finiteAvg {Ω : Type uDepth6} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, f ω

section Averages

variable {Ω : Type uDepth7} {Λ : Type uDepth8} [Fintype Ω] [Fintype Λ]

theorem finiteAvg_congr {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) :
    finiteAvg f = finiteAvg g := by
  unfold finiteAvg
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => h ω)

@[simp] theorem finiteAvg_zero : finiteAvg (fun _ : Ω => (0 : ℝ)) = 0 := by
  simp [finiteAvg]

theorem finiteAvg_add (f g : Ω → ℝ) :
    finiteAvg (fun ω => f ω + g ω) = finiteAvg f + finiteAvg g := by
  simp [finiteAvg, Finset.sum_add_distrib, mul_add]

theorem finiteAvg_sub (f g : Ω → ℝ) :
    finiteAvg (fun ω => f ω - g ω) = finiteAvg f - finiteAvg g := by
  simp [finiteAvg, Finset.sum_sub_distrib, mul_sub]

theorem finiteAvg_const_mul (c : ℝ) (f : Ω → ℝ) :
    finiteAvg (fun ω => c * f ω) = c * finiteAvg f := by
  unfold finiteAvg
  rw [← Finset.mul_sum]
  ring

theorem finiteAvg_mul_const (f : Ω → ℝ) (c : ℝ) :
    finiteAvg (fun ω => f ω * c) = finiteAvg f * c := by
  unfold finiteAvg
  rw [← Finset.sum_mul]
  ring

theorem finiteAvg_sum {ι : Type uDepth9} (s : Finset ι) (f : ι → Ω → ℝ) :
    finiteAvg (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, finiteAvg (f i) := by
  classical
  simp only [finiteAvg, Finset.mul_sum]
  exact Finset.sum_comm

theorem finiteAvg_nonneg {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ finiteAvg f := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun ω _ => h ω))

theorem finiteAvg_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    finiteAvg f ≤ finiteAvg g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ω _ => h ω))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem finiteAvg_abs_le (f : Ω → ℝ) :
    |finiteAvg f| ≤ finiteAvg (fun ω => |f ω|) := by
  unfold finiteAvg
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs f Finset.univ)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

@[simp] theorem finiteAvg_const [Nonempty Ω] (c : ℝ) :
    finiteAvg (fun _ : Ω => c) = c := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [finiteAvg, nsmul_eq_mul, hc]

theorem finiteAvg_equiv (e : Ω ≃ Λ) (f : Λ → ℝ) :
    finiteAvg (fun ω => f (e ω)) = finiteAvg f := by
  unfold finiteAvg
  rw [Fintype.card_congr e, e.sum_comp f]

theorem finiteAvg_comm (f : Ω → Λ → ℝ) :
    finiteAvg (fun ω => finiteAvg (f ω)) =
      finiteAvg (fun l => finiteAvg (fun ω => f ω l)) := by
  simp only [finiteAvg, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro ω hω
  ring

theorem finiteAvg_product (f : Ω × Λ → ℝ) :
    finiteAvg f = finiteAvg (fun ω => finiteAvg (fun l => f (ω, l))) := by
  simp only [finiteAvg, Fintype.card_prod, Nat.cast_mul, mul_inv,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem finiteAvg_pi_prod {ι : Type uDepth10} [Fintype ι]
    {κ : ι → Type uDepth21} [∀ i, Fintype (κ i)] (f : ∀ i, κ i → ℝ) :
    finiteAvg (fun x : ∀ i, κ i => ∏ i, f i (x i)) =
      ∏ i, finiteAvg (f i) := by
  classical
  unfold finiteAvg
  rw [Fintype.card_pi, Nat.cast_prod, ← Fintype.prod_sum]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end Averages

def restrictionCoordinateWeight (p : ℝ) : Option Bool → ℝ
  | none => p
  | some _ => (1 - p) / 2

def restrictionWeight {V : Type uDepth11} [Fintype V] (p : ℝ) (σ : Restriction V) : ℝ :=
  ∏ v, restrictionCoordinateWeight p (σ v)

def restrictionAvg {V : Type uDepth12} [Fintype V] (p : ℝ)
    (F : Restriction V → ℝ) : ℝ :=
  ∑ σ, restrictionWeight p σ * F σ

@[simp] theorem restrictionCoordinateWeight_sum (p : ℝ) :
    (∑ a : Option Bool, restrictionCoordinateWeight p a) = 1 := by
  simp [Fintype.sum_option, restrictionCoordinateWeight]
  ring

theorem restrictionCoordinateWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : Option Bool) : 0 ≤ restrictionCoordinateWeight p a := by
  cases a with
  | none => exact hp
  | some b => exact div_nonneg (sub_nonneg.mpr hp1) (by norm_num)

theorem restrictionWeight_nonneg {V : Type uDepth13} [Fintype V] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (σ : Restriction V) :
    0 ≤ restrictionWeight p σ := by
  exact Finset.prod_nonneg (fun v _ => restrictionCoordinateWeight_nonneg hp hp1 (σ v))

@[simp] theorem restrictionWeight_sum {V : Type uDepth14} [Fintype V] (p : ℝ) :
    (∑ σ : Restriction V, restrictionWeight p σ) = 1 := by
  classical
  unfold restrictionWeight
  rw [← Fintype.prod_sum]
  simp only [restrictionCoordinateWeight_sum, Finset.prod_const_one]

@[simp] theorem restrictionAvg_const {V : Type uDepth15} [Fintype V] (p c : ℝ) :
    restrictionAvg p (fun _ : Restriction V => c) = c := by
  simp [restrictionAvg, ← Finset.sum_mul]

theorem restrictionAvg_nonneg {V : Type uDepth16} [Fintype V] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) {F : Restriction V → ℝ}
    (hF : ∀ σ, 0 ≤ F σ) : 0 ≤ restrictionAvg p F := by
  exact Finset.sum_nonneg (fun σ _ =>
    mul_nonneg (restrictionWeight_nonneg hp hp1 σ) (hF σ))

theorem restrictionAvg_mono {V : Type uDepth17} [Fintype V] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) {F G : Restriction V → ℝ}
    (h : ∀ σ, F σ ≤ G σ) : restrictionAvg p F ≤ restrictionAvg p G := by
  exact Finset.sum_le_sum (fun σ _ =>
    mul_le_mul_of_nonneg_left (h σ) (restrictionWeight_nonneg hp hp1 σ))

theorem restrictionAvg_add {V : Type uDepth18} [Fintype V] (p : ℝ)
    (F G : Restriction V → ℝ) :
    restrictionAvg p (fun σ => F σ + G σ) = restrictionAvg p F + restrictionAvg p G := by
  simp [restrictionAvg, mul_add, Finset.sum_add_distrib]

theorem restrictionAvg_const_mul {V : Type uDepth19} [Fintype V] (p c : ℝ)
    (F : Restriction V → ℝ) :
    restrictionAvg p (fun σ => c * F σ) = c * restrictionAvg p F := by
  simp [restrictionAvg, Finset.mul_sum, mul_left_comm]

theorem restrictionAvg_abs_le {V : Type uDepth20} [Fintype V] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (F : Restriction V → ℝ) :
    |restrictionAvg p F| ≤ restrictionAvg p (fun σ => |F σ|) := by
  unfold restrictionAvg
  calc
    _ ≤ ∑ σ, |restrictionWeight p σ * F σ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [abs_mul, abs_of_nonneg (restrictionWeight_nonneg hp hp1 σ)]

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped Classical

namespace DepthThreeLowerBound

open Finset

def TupleNoSingleton {Z : Type uDepth1} [DecidableEq Z] {n : ℕ}
    (a : Fin n → Z) : Prop :=
  ∀ z, (univ.filter (fun i => a i = z)).card ≠ 1

theorem tuple_singleton_of_not {Z : Type uDepth2} [DecidableEq Z] {n : ℕ}
    (a : Fin n → Z) (h : ¬ TupleNoSingleton a) :
    ∃ i₀, ∀ i, a i = a i₀ → i = i₀ := by
  classical
  simp only [TupleNoSingleton, not_forall, not_not] at h
  obtain ⟨z, hz⟩ := h
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hz
  have hmem : i₀ ∈ univ.filter (fun i => a i = z) := by
    rw [hi₀]
    exact mem_singleton_self i₀
  have ha₀ : a i₀ = z := (mem_filter.mp hmem).2
  refine ⟨i₀, fun i hi => ?_⟩
  have himem : i ∈ univ.filter (fun j => a j = z) :=
    mem_filter.mpr ⟨mem_univ i, hi.trans ha₀⟩
  rw [hi₀] at himem
  exact mem_singleton.mp himem

theorem tuple_support_card_le_half {Z : Type uDepth3} [DecidableEq Z]
    (h : ℕ) (a : Fin (2 * h) → Z) (hns : TupleNoSingleton a) :
    (univ.image a).card ≤ h := by
  classical
  have hfiber : ∀ z ∈ (univ : Finset (Fin (2 * h))).image a,
      2 ≤ (univ.filter (fun i => a i = z)).card := by
    intro z hz
    obtain ⟨i, hi, hiz⟩ := mem_image.mp hz
    have hpos : 0 < (univ.filter (fun j => a j = z)).card :=
      card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, hiz⟩⟩
    have hne := hns z
    omega
  have htwice : 2 * (univ.image a).card ≤ 2 * h := by
    simpa only [card_univ, Fintype.card_fin] using
      (Finset.mul_card_image_le_card (f := a)
        (univ : Finset (Fin (2 * h))) 2 hfiber)
  omega

theorem tuple_factor_through {Z : Type uDepth4} [Nonempty Z] [DecidableEq Z]
    {n h : ℕ} (a : Fin n → Z) (hcard : (univ.image a).card ≤ h) :
    ∃ (f : Fin h → Z) (g : Fin n → Fin h), (fun i => f (g i)) = a := by
  classical
  let s : Finset Z := univ.image a
  have hsize : Fintype.card ↥s ≤ Fintype.card (Fin h) := by
    simpa [s] using hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hsize
  let f : Fin h → Z := Function.extend e Subtype.val
    (fun _ => Classical.choice (inferInstance : Nonempty Z))
  let g : Fin n → Fin h := fun i =>
    e ⟨a i, Finset.mem_image_of_mem a (mem_univ i)⟩
  refine ⟨f, g, funext fun i => ?_⟩
  exact e.injective.extend_apply Subtype.val
    (fun _ => Classical.choice (inferInstance : Nonempty Z))
    ⟨a i, Finset.mem_image_of_mem a (mem_univ i)⟩

theorem card_noSingleton_tuples_le {Z : Type uDepth5} [Fintype Z] [Nonempty Z]
    [DecidableEq Z] (h : ℕ) :
    (univ.filter (fun a : Fin (2 * h) → Z => TupleNoSingleton a)).card ≤
      (Fintype.card Z) ^ h * h ^ (2 * h) := by
  classical
  let encode : (Fin h → Z) × (Fin (2 * h) → Fin h) → (Fin (2 * h) → Z) :=
    fun p i => p.1 (p.2 i)
  have hsub : univ.filter (fun a : Fin (2 * h) → Z => TupleNoSingleton a) ⊆
      univ.image encode := by
    intro a ha
    have hns := (mem_filter.mp ha).2
    obtain ⟨f, g, hfg⟩ := tuple_factor_through a (tuple_support_card_le_half h a hns)
    exact mem_image.mpr ⟨(f, g), mem_univ _, hfg⟩
  calc
    _ ≤ (univ.image encode).card := card_le_card hsub
    _ ≤ (univ : Finset ((Fin h → Z) × (Fin (2 * h) → Fin h))).card :=
      card_image_le
    _ = (Fintype.card Z) ^ h * h ^ (2 * h) := by simp

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

def UniformBitsUpTo {Ω : Type uDepth1} {Z : Type uDepth2} [Fintype Ω] [DecidableEq Z]
    (t : ℕ) (bits : Ω → Z → Bool) : Prop :=
  ∀ s : Finset Z, s.card ≤ t → ∀ F : (↥s → Bool) → ℝ,
    finiteAvg (fun ω => F (fun z => bits ω z.val)) = finiteAvg F

@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

theorem abs_sign_mul_indicator_le_one (b c : Bool) :
    |sign b * indicator c| ≤ 1 := by
  cases b <;> cases c <;> norm_num [sign, indicator]

def flipCoordinate {A : Type uDepth3} [DecidableEq A] (a₀ : A) :
    (A → Bool) ≃ (A → Bool) where
  toFun x a := if a = a₀ then !(x a) else x a
  invFun x a := if a = a₀ then !(x a) else x a
  left_inv x := by
    funext a
    by_cases h : a = a₀ <;> simp [h]
  right_inv x := by
    funext a
    by_cases h : a = a₀ <;> simp [h]

theorem uniform_product_zero_of_singleton {A : Type uDepth4} {I : Type uDepth5}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (a : I → A) (w : I → ℝ) (i₀ : I)
    (hunique : ∀ i, a i = a i₀ → i = i₀) :
    finiteAvg (fun x : A → Bool => ∏ i, sign (x (a i)) * w i) = 0 := by
  let F : (A → Bool) → ℝ := fun x => ∏ i, sign (x (a i)) * w i
  let e := flipCoordinate (a i₀)
  have hflip (x : A → Bool) : F (e x) = -F x := by
    have hother : (∏ i ∈ Finset.univ.erase i₀, sign ((e x) (a i)) * w i) =
        ∏ i ∈ Finset.univ.erase i₀, sign (x (a i)) * w i := by
      apply Finset.prod_congr rfl
      intro i hi
      have hne : a i ≠ a i₀ := fun h => (Finset.mem_erase.mp hi).1 (hunique i h)
      simp [e, flipCoordinate, hne]
    have hat : sign ((e x) (a i₀)) * w i₀ = -(sign (x (a i₀)) * w i₀) := by
      simp [e, flipCoordinate]
    change (∏ i, sign ((e x) (a i)) * w i) = -(∏ i, sign (x (a i)) * w i)
    rw [← Finset.mul_prod_erase Finset.univ
        (fun i => sign ((e x) (a i)) * w i) (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase Finset.univ
        (fun i => sign (x (a i)) * w i) (Finset.mem_univ i₀), hat, hother]
    ring
  have havg : finiteAvg F = -finiteAvg F := by
    calc
      finiteAvg F = finiteAvg (fun x => F (e x)) := (finiteAvg_equiv e F).symm
      _ = finiteAvg (fun x => (-1) * F x) := by
        apply finiteAvg_congr
        intro x
        rw [hflip]
        ring
      _ = -finiteAvg F := by rw [finiteAvg_const_mul]; ring
  change finiteAvg F = 0
  linarith

theorem tuple_product_avg_zero {Ω : Type uDepth6} {Z : Type uDepth7} [Fintype Ω] [DecidableEq Z]
    {t : ℕ} (bits : Ω → Z → Bool) (hdist : UniformBitsUpTo t bits)
    (a : Fin t → Z) (w : Fin t → ℝ) (hns : ¬ TupleNoSingleton a) :
    finiteAvg (fun ω => ∏ i, sign (bits ω (a i)) * w i) = 0 := by
  classical
  obtain ⟨i₀, hi₀⟩ := tuple_singleton_of_not a hns
  let s : Finset Z := Finset.univ.image a
  let a' : Fin t → ↥s := fun i =>
    ⟨a i, Finset.mem_image_of_mem a (Finset.mem_univ i)⟩
  have hs : s.card ≤ t := by
    simpa [s] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := a))
  have huniq : ∀ i, a' i = a' i₀ → i = i₀ := by
    intro i hi
    exact hi₀ i (congrArg Subtype.val hi)
  calc
    finiteAvg (fun ω => ∏ i, sign (bits ω (a i)) * w i) =
        finiteAvg (fun x : ↥s → Bool => ∏ i, sign (x (a' i)) * w i) :=
      hdist s hs (fun x => ∏ i, sign (x (a' i)) * w i)
    _ = 0 := uniform_product_zero_of_singleton a' w i₀ huniq

theorem sign_indicator_product_le_one {I : Type uDepth8} [Fintype I]
    (b c : I → Bool) : (∏ i, sign (b i) * indicator (c i)) ≤ 1 := by
  calc
    _ ≤ |∏ i, sign (b i) * indicator (c i)| := le_abs_self _
    _ = ∏ i, |sign (b i) * indicator (c i)| := Finset.abs_prod _ _
    _ ≤ 1 := Finset.prod_le_one
      (fun _ _ => abs_nonneg _) (fun i _ => abs_sign_mul_indicator_le_one (b i) (c i))

theorem even_moment_le {Ω : Type uDepth9} {Z : Type uDepth10} [Fintype Ω] [Nonempty Ω]
    [Fintype Z] [Nonempty Z] [DecidableEq Z] (h : ℕ)
    (bits : Ω → Z → Bool) (hdist : UniformBitsUpTo (2 * h) bits)
    (J : Z → Bool) :
    finiteAvg (fun ω => |∑ z, sign (bits ω z) * indicator (J z)| ^ (2 * h)) ≤
      (Fintype.card Z : ℝ) ^ h * (h : ℝ) ^ (2 * h) := by
  classical
  have hexpand : finiteAvg
      (fun ω => |∑ z, sign (bits ω z) * indicator (J z)| ^ (2 * h)) =
      ∑ a : Fin (2 * h) → Z,
        finiteAvg (fun ω => ∏ i, sign (bits ω (a i)) * indicator (J (a i))) := by
    calc
      _ = finiteAvg (fun ω => ∑ a : Fin (2 * h) → Z,
          ∏ i, sign (bits ω (a i)) * indicator (J (a i))) := by
        apply finiteAvg_congr
        intro ω
        rw [show |∑ z, sign (bits ω z) * indicator (J z)| ^ (2 * h) =
            (∑ z, sign (bits ω z) * indicator (J z)) ^ (2 * h) by
          simp only [pow_mul, sq_abs]]
        exact Fintype.sum_pow _ _
      _ = _ := finiteAvg_sum Finset.univ _
  have hterm (a : Fin (2 * h) → Z) :
      finiteAvg (fun ω => ∏ i, sign (bits ω (a i)) * indicator (J (a i))) ≤
        if TupleNoSingleton a then (1 : ℝ) else 0 := by
    by_cases ha : TupleNoSingleton a
    · simp only [ite_eq_left ha]
      calc
        _ ≤ finiteAvg (fun _ : Ω => (1 : ℝ)) :=
          finiteAvg_mono (fun ω => sign_indicator_product_le_one
            (fun i => bits ω (a i)) (fun i => J (a i)))
        _ = 1 := finiteAvg_const 1
    · rw [ite_eq_right ha, tuple_product_avg_zero bits hdist a (fun i => indicator (J (a i))) ha]
  calc
    _ = _ := hexpand
    _ ≤ ∑ a : Fin (2 * h) → Z, if TupleNoSingleton a then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun a _ => hterm a)
    _ = ((Finset.univ.filter (fun a : Fin (2 * h) → Z => TupleNoSingleton a)).card : ℝ) :=
      Finset.sum_boole _ _
    _ ≤ ((Fintype.card Z) ^ h * h ^ (2 * h) : ℕ) := by
      exact_mod_cast (card_noSingleton_tuples_le (Z := Z) h)
    _ = (Fintype.card Z : ℝ) ^ h * (h : ℝ) ^ (2 * h) := by push_cast; rfl

theorem even_moment_le_manuscript {Ω : Type uDepth11} {Z : Type uDepth12} [Fintype Ω] [Nonempty Ω]
    [Fintype Z] [Nonempty Z] [DecidableEq Z] (h : ℕ)
    (bits : Ω → Z → Bool) (hdist : UniformBitsUpTo (2 * h) bits)
    (J : Z → Bool) :
    finiteAvg (fun ω => |∑ z, sign (bits ω z) * indicator (J z)| ^ (2 * h)) ≤
      ((2 * h : ℕ) : ℝ) ^ (2 * h) * (Fintype.card Z : ℝ) ^ h := by
  have hh : (h : ℝ) ≤ ((2 * h : ℕ) : ℝ) := by exact_mod_cast (show h ≤ 2 * h by omega)
  calc
    _ ≤ (Fintype.card Z : ℝ) ^ h * (h : ℝ) ^ (2 * h) :=
      even_moment_le h bits hdist J
    _ ≤ (Fintype.card Z : ℝ) ^ h * ((2 * h : ℕ) : ℝ) ^ (2 * h) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg h) hh _) (by positivity)
    _ = _ := mul_comm _ _

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

def finiteProb {Ω : Type uDepth1} [Fintype Ω] (P : Ω → Prop) : ℝ :=
  finiteAvg (fun ω => if P ω then 1 else 0)

variable {Ω : Type uDepth2} {Λ : Type uDepth3} [Fintype Ω] [Fintype Λ]

theorem finiteProb_nonneg (P : Ω → Prop) : 0 ≤ finiteProb P := by
  apply finiteAvg_nonneg
  intro ω
  split_ifs <;> norm_num

theorem finiteProb_le_one [Nonempty Ω] (P : Ω → Prop) : finiteProb P ≤ 1 := by
  have h : finiteProb P ≤ finiteAvg (fun _ : Ω => (1 : ℝ)) := by
    apply finiteAvg_mono
    intro ω
    split_ifs <;> norm_num
  simpa using h

theorem finiteProb_mono {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    finiteProb P ≤ finiteProb Q := by
  apply finiteAvg_mono
  intro ω
  by_cases hp : P ω
  · simp [hp, h ω hp]
  · simp only [hp, ite_false]
    split_ifs <;> norm_num

theorem finiteAvg_exists_le [Nonempty Ω] (f : Ω → ℝ) :
    ∃ ω, f ω ≤ finiteAvg f := by
  obtain ⟨ω, hω, hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨ω, ?_⟩
  have h := finiteAvg_mono (fun x => hmin x (Finset.mem_univ x))
  simpa using h

theorem finiteAvg_exists_le_of_le [Nonempty Ω] (f : Ω → ℝ) (c : ℝ)
    (h : finiteAvg f ≤ c) : ∃ ω, f ω ≤ c := by
  obtain ⟨ω, hω⟩ := finiteAvg_exists_le f
  exact ⟨ω, hω.trans h⟩

theorem finiteProb_gt_le {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω)
    {a : ℝ} (ha : 0 < a) :
    finiteProb (fun ω => a < f ω) ≤ finiteAvg f / a := by
  have h : finiteAvg (fun ω => a * (if a < f ω then 1 else 0)) ≤ finiteAvg f := by
    apply finiteAvg_mono
    intro ω
    by_cases hω : a < f ω
    · simpa [hω] using hω.le
    · simpa [hω] using hf ω
  rw [finiteAvg_const_mul] at h
  apply (le_div_iff₀ ha).mpr
  simpa only [finiteProb, mul_comm] using h

theorem finiteProb_exists_le_sum {ι : Type uDepth4} (s : Finset ι) (P : ι → Ω → Prop) :
    finiteProb (fun ω => ∃ i ∈ s, P i ω) ≤ ∑ i ∈ s, finiteProb (P i) := by
  have h : finiteProb (fun ω => ∃ i ∈ s, P i ω) ≤
      finiteAvg (fun ω => ∑ i ∈ s, if P i ω then (1 : ℝ) else 0) := by
    apply finiteAvg_mono
    intro ω
    by_cases he : ∃ i ∈ s, P i ω
    · obtain ⟨i, hi, hPi⟩ := he
      have hs : (if P i ω then (1 : ℝ) else 0) ≤
          ∑ j ∈ s, if P j ω then (1 : ℝ) else 0 := by
        apply Finset.single_le_sum _ hi
        intro j hj
        split_ifs <;> norm_num
      simpa [show ∃ i ∈ s, P i ω from ⟨i, hi, hPi⟩, hPi] using hs
    · simp only [he, ite_false]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> norm_num
  simpa only [finiteAvg_sum, finiteProb] using h

theorem finiteProb_abs_gt_le_moment (f : Ω → ℝ) (t : ℕ) (ht : 0 < t)
    (a C : ℝ) (ha : 0 < a)
    (hM : finiteAvg (fun ω => |f ω| ^ t) ≤ C) :
    finiteProb (fun ω => a < |f ω|) ≤ C / a ^ t := by
  have he : finiteProb (fun ω => a < |f ω|) ≤
      finiteProb (fun ω => a ^ t < |f ω| ^ t) := by
    apply finiteProb_mono
    intro ω hω
    exact pow_lt_pow_left₀ hω ha.le (Nat.ne_of_gt ht)
  have hmark := finiteProb_gt_le (fun ω => pow_nonneg (abs_nonneg (f ω)) t)
    (pow_pos ha t)
  exact he.trans (hmark.trans (div_le_div_of_nonneg_right hM (pow_nonneg ha.le t)))

theorem finiteAvg_restrictionAvg {V : Type uDepth5} [Fintype V] (p : ℝ)
    (F : Ω → Restriction V → ℝ) :
    finiteAvg (fun ω => restrictionAvg p (F ω)) =
      restrictionAvg p (fun σ => finiteAvg (fun ω => F ω σ)) := by
  unfold restrictionAvg
  rw [finiteAvg_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact finiteAvg_const_mul _ _

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

variable {V : Type uDepth1}

namespace Clause

theorem eval_true_of_not_normalized {C : Clause V} (h : ¬ C.Normalized)
    (x : Cube V) : C.eval x = true := by
  classical
  apply (eval_eq_true C x).mpr
  by_contra hx
  apply h
  intro v hf ht
  cases hv : x v
  · exact hx ⟨(v, false), hf, hv⟩
  · exact hx ⟨(v, true), ht, hv⟩

noncomputable def forbiddenValue (C : Clause V) (v : V) : Bool := by
  classical
  exact decide ((v, false) ∈ C)

theorem forbiddenValue_ne_literal {C : Clause V} (hC : C.Normalized)
    {l : Literal V} (hl : l ∈ C) : C.forbiddenValue l.1 ≠ l.2 := by
  classical
  rcases l with ⟨v, b⟩
  cases b
  · simp [forbiddenValue, hl]
  · have hf : (v, false) ∉ C := fun hf => hC v hf hl
    simp [forbiddenValue, hf]

theorem eval_eq_false_iff (C : Clause V) (x : Cube V) :
    C.eval x = false ↔ ∀ l ∈ C, x l.1 ≠ l.2 := by
  classical
  constructor
  · intro hx l hl he
    have ht := (eval_eq_true C x).mpr ⟨l, hl, he⟩
    simp [hx] at ht
  · intro hx
    cases he : C.eval x
    · rfl
    · obtain ⟨l, hl, hxl⟩ := (eval_eq_true C x).mp he
      exact (hx l hl hxl).elim

theorem eval_eq_false_iff_forbidden {C : Clause V} (hC : C.Normalized)
    (x : Cube V) :
    C.eval x = false ↔ ∀ v ∈ C.scope, x v = C.forbiddenValue v := by
  classical
  rw [eval_eq_false_iff]
  constructor
  · intro hx v hv
    obtain ⟨⟨w, b⟩, hl, hval⟩ := Finset.mem_image.mp hv
    change w = v at hval
    subst v
    have hxb := hx (w, b) hl
    have hfb := forbiddenValue_ne_literal hC hl
    cases hxx : x w <;> cases hff : C.forbiddenValue w <;> cases b <;>
      simp_all
  · intro hx l hl
    have hv : l.1 ∈ C.scope := Finset.mem_image_of_mem Prod.fst hl
    rw [hx l.1 hv]
    exact forbiddenValue_ne_literal hC hl

noncomputable def violation (C : Clause V) (x : Cube V) : Bool := !(C.eval x)

@[simp] theorem violation_eq_true (C : Clause V) (x : Cube V) :
    C.violation x = true ↔ C.eval x = false := by
  cases h : C.eval x <;> simp [violation, h]

theorem violation_eq_true_iff_forbidden {C : Clause V} (hC : C.Normalized)
    (x : Cube V) :
    C.violation x = true ↔ ∀ v ∈ C.scope, x v = C.forbiddenValue v := by
  rw [violation_eq_true, eval_eq_false_iff_forbidden hC]

end Clause

namespace CNF

noncomputable def normalize (H : CNF V) : CNF V := by
  classical
  exact H.filter fun C => decide C.Normalized

@[simp] theorem mem_normalize {H : CNF V} {C : Clause V} :
    C ∈ H.normalize ↔ C ∈ H ∧ C.Normalized := by
  classical
  simp [normalize]

theorem normalize_normalized (H : CNF V) : H.normalize.Normalized := by
  intro C hC
  exact (mem_normalize.mp hC).2

theorem normalize_widthAtMost {H : CNF V} {b : ℕ} (hH : H.WidthAtMost b) :
    H.normalize.WidthAtMost b := by
  intro C hC
  exact hH C (mem_normalize.mp hC).1

@[simp] theorem eval_normalize (H : CNF V) (x : Cube V) :
    H.normalize.eval x = H.eval x := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [eval_eq_true, eval_eq_true]
  constructor
  · intro hx C hC
    by_cases hn : C.Normalized
    · exact hx C (mem_normalize.mpr ⟨hC, hn⟩)
    · exact Clause.eval_true_of_not_normalized hn x
  · intro hx C hC
    exact hx C (mem_normalize.mp hC).1

end CNF

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped Classical

namespace DepthThreeLowerBound

abbrev SparseClauseCode (V : Type uDepth1) (b : ℕ) := Fin b → Option (Literal V)
abbrev SparseTestCode (V : Type uDepth2) (b L : ℕ) := Fin L → Option (SparseClauseCode V b)

namespace SparseClauseCode

def decode {V : Type uDepth3} [Fintype V] {b : ℕ} (c : SparseClauseCode V b) : Clause V :=
  Finset.univ.filter (fun l => ∃ i, c i = some l)

@[simp] theorem mem_decode {V : Type uDepth4} [Fintype V] {b : ℕ}
    (c : SparseClauseCode V b) (l : Literal V) :
    l ∈ c.decode ↔ ∃ i, c i = some l := by
  simp [decode]

@[simp] theorem decode_none {V : Type uDepth5} [Fintype V] (b : ℕ) :
    decode (fun _ : Fin b => (none : Option (Literal V))) = ∅ := by
  ext l
  simp

theorem exists_decode_of_card_le {V : Type uDepth6} [Fintype V]
    (C : Clause V) {b : ℕ} (hC : C.card ≤ b) :
    ∃ c : SparseClauseCode V b, c.decode = C := by
  have hsize : Fintype.card ↥C ≤ Fintype.card (Fin b) := by simpa using hC
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hsize
  let c : SparseClauseCode V b :=
    Function.extend e (fun l : ↥C => some l.val) (fun _ => none)
  refine ⟨c, ?_⟩
  ext l
  rw [mem_decode]
  constructor
  · rintro ⟨i, hi⟩
    change Function.extend e (fun l : ↥C => some l.val) (fun _ => none) i = some l at hi
    rw [Function.extend_def] at hi
    split_ifs at hi with hex
    · have heq : (Classical.choose hex).val = l := Option.some.inj hi
      exact heq ▸ (Classical.choose hex).property
  · intro hl
    refine ⟨e ⟨l, hl⟩, ?_⟩
    exact e.injective.extend_apply (fun l : ↥C => some l.val) (fun _ => none) ⟨l, hl⟩

theorem exists_decode_of_normalized {V : Type uDepth7} [Fintype V]
    (C : Clause V) {b : ℕ} (hn : C.Normalized) (hw : C.width ≤ b) :
    ∃ c : SparseClauseCode V b, c.decode = C :=
  exists_decode_of_card_le C (hn.card_eq_width.trans_le hw)

theorem card_eq {V : Type uDepth8} [Fintype V] (b : ℕ) :
    Fintype.card (SparseClauseCode V b) = (2 * Fintype.card V + 1) ^ b := by
  simp [SparseClauseCode, Literal, Nat.mul_comm]

end SparseClauseCode

namespace SparseTestCode

def decode {V : Type uDepth9} [Fintype V] {b : ℕ} :
    {L : ℕ} → SparseTestCode V b L → CNF V
  | 0, _ => []
  | _ + 1, c =>
      match c 0 with
      | none => decode (fun i => c i.succ)
      | some d => d.decode :: decode (fun i => c i.succ)

def eval {V : Type uDepth10} [Fintype V] {b L : ℕ}
    (c : SparseTestCode V b L) (x : Cube V) : Bool := c.decode.eval x

@[simp] theorem decode_cons_none {V : Type uDepth11} [Fintype V] {b L : ℕ}
    (c : SparseTestCode V b L) : decode (Fin.cons none c) = c.decode := by
  simp [decode]

@[simp] theorem decode_cons_some {V : Type uDepth12} [Fintype V] {b L : ℕ}
    (d : SparseClauseCode V b) (c : SparseTestCode V b L) :
    decode (Fin.cons (some d) c) = d.decode :: c.decode := by
  simp [decode]

@[simp] theorem decode_none {V : Type uDepth13} [Fintype V] (b L : ℕ) :
    decode (fun _ : Fin L => (none : Option (SparseClauseCode V b))) = [] := by
  induction L with
  | zero => rfl
  | succ L ih => simpa [decode] using ih

@[simp] theorem eval_none {V : Type uDepth14} [Fintype V] (b L : ℕ) (x : Cube V) :
    eval (fun _ : Fin L => (none : Option (SparseClauseCode V b))) x = true := by
  simp [eval]

theorem eval_cons_empty {V : Type uDepth15} [Fintype V] {b L : ℕ}
    (c : SparseTestCode V b L) (x : Cube V) :
    eval (Fin.cons (some (fun _ : Fin b => (none : Option (Literal V)))) c) x = false := by
  simp [eval]

theorem exists_decode_of_normalized {V : Type uDepth16} [Fintype V]
    (H : CNF V) (b : ℕ) :
    ∀ L, H.Normalized → H.WidthAtMost b → H.length ≤ L →
      ∃ c : SparseTestCode V b L, c.decode = H := by
  induction H with
  | nil =>
      intro L _ _ _
      exact ⟨fun _ => none, decode_none b L⟩
  | cons C H ih =>
      intro L hn hw hlen
      cases L with
      | zero => simp at hlen
      | succ L =>
          have hnC : C.Normalized := hn C (by simp)
          have hwC : C.width ≤ b := hw C (by simp)
          obtain ⟨d, hd⟩ := SparseClauseCode.exists_decode_of_normalized C hnC hwC
          have hnH : CNF.Normalized H := fun D hD => hn D (by simp [hD])
          have hwH : CNF.WidthAtMost H b := fun D hD => hw D (by simp [hD])
          have hlenH : H.length ≤ L := Nat.le_of_succ_le_succ hlen
          obtain ⟨c, hc⟩ := ih L hnH hwH hlenH
          refine ⟨Fin.cons (some d) c, ?_⟩
          rw [decode_cons_some, hd, hc]

theorem exists_eval_eq {V : Type uDepth17} [Fintype V]
    (H : CNF V) {b L : ℕ} (hw : H.WidthAtMost b) (hlen : H.length ≤ L) :
    ∃ c : SparseTestCode V b L, ∀ x, c.eval x = H.eval x := by
  have hnormlen : H.normalize.length ≤ H.length := by
    unfold CNF.normalize
    exact List.length_filter_le _ _
  obtain ⟨c, hc⟩ := exists_decode_of_normalized H.normalize b L
    (CNF.normalize_normalized H) (CNF.normalize_widthAtMost hw) (hnormlen.trans hlen)
  refine ⟨c, fun x => ?_⟩
  change c.decode.eval x = H.eval x
  rw [hc, CNF.eval_normalize]

theorem card_eq {V : Type uDepth18} [Fintype V] (b L : ℕ) :
    Fintype.card (SparseTestCode V b L) = ((2 * Fintype.card V + 1) ^ b + 1) ^ L := by
  simp only [SparseTestCode, SparseClauseCode, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_option, Literal, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]

end SparseTestCode

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound.AlgebraFiniteFibers

variable {A : Type uDepth1} {B : Type uDepth2} [AddCommGroup A] [AddCommGroup B]

def fiberEquivKernel (L : A →+ B) (hL : Function.Surjective L) (b : B) :
    {a : A // L a = b} ≃ {a : A // L a = 0} := by
  let x : A := Classical.choose (hL b)
  have hx : L x = b := Classical.choose_spec (hL b)
  exact {
    toFun := fun a => ⟨a.val - x, by rw [map_sub, a.property, hx, sub_self]⟩
    invFun := fun a => ⟨a.val + x, by rw [map_add, a.property, hx, zero_add]⟩
    left_inv := by
      intro a
      apply Subtype.ext
      exact sub_add_cancel a.val x
    right_inv := by
      intro a
      apply Subtype.ext
      exact add_sub_cancel_right a.val x
  }

variable [Fintype A] [instFintypeB : Fintype B] [instDecidableEqA : DecidableEq A] [DecidableEq B]

theorem card_fiber_eq
    {A : Type uDepth1}
    {B : Type uDepth2}
    [AddCommGroup A]
    [AddCommGroup B]
    [Fintype A]
    [Fintype B]
    [DecidableEq A]
    [DecidableEq B]
    (L : A →+ B) (hL : Function.Surjective L) (b : B) :
    Fintype.card {a : A // L a = b} = Fintype.card {a : A // L a = 0} :=
  Fintype.card_congr (fiberEquivKernel L hL b)

theorem card_filter_fiber_eq (L : A →+ B) (hL : Function.Surjective L) (b : B) :
    (Finset.univ.filter (fun a : A => L a = b)).card =
      (Finset.univ.filter (fun a : A => L a = 0)).card := by
  simpa only [Fintype.card_subtype] using card_fiber_eq L hL b

theorem card_eq_mul_card_kernel (L : A →+ B) (hL : Function.Surjective L) :
    Fintype.card A = Fintype.card B * Fintype.card {a : A // L a = 0} := by
  calc
    Fintype.card A = ∑ b : B, Fintype.card {a : A // L a = b} := by
      simpa using
        (Fintype.sum_fiberwise' (fun a : A => L a) (fun _ : B => (1 : ℕ))).symm
    _ = ∑ _b : B, Fintype.card {a : A // L a = 0} := by
      exact Finset.sum_congr rfl (fun b _ => card_fiber_eq L hL b)
    _ = Fintype.card B * Fintype.card {a : A // L a = 0} := by simp

theorem sum_comp (L : A →+ B) (hL : Function.Surjective L) (f : B → ℝ) :
    (∑ a : A, f (L a)) =
      (Fintype.card {a : A // L a = 0} : ℝ) * ∑ b : B, f b := by
  calc
    (∑ a : A, f (L a)) = ∑ b : B, ∑ _a : {a : A // L a = b}, f b :=
      (Fintype.sum_fiberwise' (fun a : A => L a) f).symm
    _ = ∑ b : B, (Fintype.card {a : A // L a = 0} : ℝ) * f b := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        card_fiber_eq L hL b]
    _ = (Fintype.card {a : A // L a = 0} : ℝ) * ∑ b : B, f b :=
      (Finset.mul_sum Finset.univ f _).symm

theorem finiteAvg_comp (L : A →+ B) (hL : Function.Surjective L) (f : B → ℝ) :
    finiteAvg (fun a : A => f (L a)) = finiteAvg f := by
  let : Nonempty {a : A // L a = 0} := ⟨⟨0, map_zero L⟩⟩
  have hk : (Fintype.card {a : A // L a = 0} : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card {a : A // L a = 0} ≠ 0)
  unfold finiteAvg
  rw [card_eq_mul_card_kernel L hL, Nat.cast_mul, sum_comp L hL f, mul_inv]
  calc
    (Fintype.card B : ℝ)⁻¹ * (Fintype.card {a : A // L a = 0} : ℝ)⁻¹ *
        ((Fintype.card {a : A // L a = 0} : ℝ) * ∑ b : B, f b) =
        (Fintype.card B : ℝ)⁻¹ *
          ((Fintype.card {a : A // L a = 0} : ℝ)⁻¹ *
            (Fintype.card {a : A // L a = 0} : ℝ)) * ∑ b : B, f b := by ring
    _ = (Fintype.card B : ℝ)⁻¹ * ∑ b : B, f b := by
      rw [inv_mul_cancel₀ hk, mul_one]

end DepthThreeLowerBound.AlgebraFiniteFibers

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Polynomial

namespace DepthThreeLowerBound
namespace Interpolation

variable {F : Type uDepth1} {ι : Type uDepth2}

def coeffEval [CommSemiring F] (t : ℕ) (a : ι → F) :
    (Fin t → F) →ₗ[F] (ι → F) where
  toFun β i := ∑ j : Fin t, β j * a i ^ (j : ℕ)
  map_add' β γ := by
    funext i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c β := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
      RingHom.id_apply]

@[simp] theorem coeffEval_apply [CommSemiring F] (t : ℕ) (a : ι → F)
    (β : Fin t → F) (i : ι) :
    coeffEval t a β i = ∑ j : Fin t, β j * a i ^ (j : ℕ) := rfl

theorem coeffEval_surjective [Field F] [Fintype ι] {t : ℕ} (a : ι → F)
    (hsize : Fintype.card ι ≤ t) (ha : Function.Injective a) :
    Function.Surjective (coeffEval t a) := by
  classical
  intro v
  let p : F[X] := Lagrange.interpolate Finset.univ a v
  have hinj : Set.InjOn a (↑(Finset.univ : Finset ι) : Set ι) :=
    fun _ _ _ _ hij => ha hij
  have hp : p ∈ Polynomial.degreeLT F (Fintype.card ι) := by
    apply Polynomial.mem_degreeLT.mpr
    simpa only [Finset.card_univ] using Lagrange.degree_interpolate_lt v hinj
  have hpt : p ∈ Polynomial.degreeLT F t := Polynomial.degreeLT_mono hsize hp
  refine ⟨Polynomial.degreeLTEquiv F t ⟨p, hpt⟩, ?_⟩
  funext i
  change (∑ j : Fin t,
    Polynomial.degreeLTEquiv F t ⟨p, hpt⟩ j * a i ^ (j : ℕ)) = v i
  rw [← Polynomial.eval_eq_sum_degreeLTEquiv hpt]
  exact Lagrange.eval_interpolate_at_node v hinj (Finset.mem_univ i)

section FiniteField

variable [Field F] [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
variable {t : ℕ} (a : ι → F)
variable (hsize : Fintype.card ι ≤ t) (ha : Function.Injective a)

include hsize ha

theorem card_coeffEval_fiber_mul (v : ι → F) :
    Fintype.card F ^ Fintype.card ι *
      Fintype.card {β : Fin t → F // coeffEval t a β = v} =
        Fintype.card F ^ t := by
  classical
  let L := (coeffEval t a).toAddMonoidHom
  have hL : Function.Surjective L := coeffEval_surjective a hsize ha
  have hcard := AlgebraFiniteFibers.card_eq_mul_card_kernel L hL
  rw [← AlgebraFiniteFibers.card_fiber_eq L hL v] at hcard
  simp only [Fintype.card_fun, Fintype.card_fin] at hcard
  simp only [Fintype.card_eq_nat_card] at hcard ⊢
  simpa only [L, LinearMap.toAddMonoidHom_coe] using hcard.symm

theorem card_coeffEval_fiber (v : ι → F) :
    Fintype.card {β : Fin t → F // coeffEval t a β = v} =
      Fintype.card F ^ (t - Fintype.card ι) := by
  apply Nat.eq_of_mul_eq_mul_left
    (pow_pos (Fintype.card_pos (α := F)) (Fintype.card ι))
  calc
    Fintype.card F ^ Fintype.card ι *
        Fintype.card {β : Fin t → F // coeffEval t a β = v} =
        Fintype.card F ^ t := card_coeffEval_fiber_mul a hsize ha v
    _ = Fintype.card F ^ (Fintype.card ι + (t - Fintype.card ι)) := by
      rw [Nat.add_sub_of_le hsize]
    _ = Fintype.card F ^ Fintype.card ι *
        Fintype.card F ^ (t - Fintype.card ι) := pow_add _ _ _

theorem finiteAvg_coeffEval (Φ : (ι → F) → ℝ) :
    finiteAvg (fun β : Fin t → F => Φ (coeffEval t a β)) = finiteAvg Φ := by
  classical
  exact AlgebraFiniteFibers.finiteAvg_comp (coeffEval t a).toAddMonoidHom
    (coeffEval_surjective a hsize ha) Φ

end FiniteField

end Interpolation
end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound
namespace Interpolation

open BinaryAlgebra

variable {F : Type uDepth1} {ι : Type uDepth2}
variable [Field F] [Module F2 F]

def bitEval (ell : F →ₗ[F2] F2) (t : ℕ) (a : ι → F) :
    (Fin t → F) →+ (ι → F2) where
  toFun β i := ell (coeffEval t a β i)
  map_zero' := by
    funext i
    simp only [map_zero, Pi.zero_apply]
  map_add' β γ := by
    funext i
    simp only [map_add, Pi.add_apply]

@[simp] theorem bitEval_apply (ell : F →ₗ[F2] F2) (t : ℕ) (a : ι → F)
    (β : Fin t → F) (i : ι) :
    bitEval ell t a β i = ell (∑ j : Fin t, β j * a i ^ (j : ℕ)) := rfl

theorem functional_surjective (ell : F →ₗ[F2] F2) (hOne : ell 1 = 1) :
    Function.Surjective ell := by
  intro b
  refine ⟨b • (1 : F), ?_⟩
  simp only [map_smul, hOne, smul_eq_mul, mul_one]

theorem bitEval_surjective [Fintype ι] (ell : F →ₗ[F2] F2) (hOne : ell 1 = 1)
    {t : ℕ} (a : ι → F) (hsize : Fintype.card ι ≤ t)
    (ha : Function.Injective a) : Function.Surjective (bitEval ell t a) := by
  intro b
  obtain ⟨β, hβ⟩ := coeffEval_surjective a hsize ha (fun i => b i • (1 : F))
  refine ⟨β, ?_⟩
  funext i
  change ell (coeffEval t a β i) = b i
  rw [hβ]
  simp only [map_smul, hOne, smul_eq_mul, mul_one]

def coefficientBits (ell : F →ₗ[F2] F2) (t : ℕ) (a : ι → F)
    (β : Fin t → F) : ι → Bool :=
  fun i => fieldBit (bitEval ell t a β i)

def acceptEval (ell : F →ₗ[F2] F2) (t : ℕ) (a : ι → F)
    (β : Fin t → F) : ι → Bool :=
  fun i => !(coefficientBits ell t a β i)

@[simp] theorem acceptEval_eq_true (ell : F →ₗ[F2] F2) (t : ℕ) (a : ι → F)
    (β : Fin t → F) (i : ι) :
    acceptEval ell t a β i = true ↔
      ell (∑ j : Fin t, β j * a i ^ (j : ℕ)) = 0 := by
  simp [acceptEval, coefficientBits]

def complementEquiv (ι : Type uDepth3) : (ι → Bool) ≃ (ι → Bool) where
  toFun b i := !(b i)
  invFun b i := !(b i)
  left_inv b := by funext i; exact Bool.not_not (b i)
  right_inv b := by funext i; exact Bool.not_not (b i)

section Finite

variable [Fintype F] [Fintype ι] [DecidableEq ι]
variable (ell : F →ₗ[F2] F2) (hOne : ell 1 = 1)
variable {t : ℕ} (a : ι → F) (hsize : Fintype.card ι ≤ t)
variable (ha : Function.Injective a)

include hOne hsize ha

theorem finiteAvg_bitEval (Φ : (ι → F2) → ℝ) :
    finiteAvg (fun β : Fin t → F => Φ (bitEval ell t a β)) = finiteAvg Φ := by
  classical
  exact AlgebraFiniteFibers.finiteAvg_comp (bitEval ell t a)
    (bitEval_surjective ell hOne a hsize ha) Φ

theorem finiteAvg_coefficientBits (Φ : (ι → Bool) → ℝ) :
    finiteAvg (fun β : Fin t → F => Φ (coefficientBits ell t a β)) =
      finiteAvg Φ := by
  calc
    finiteAvg (fun β : Fin t → F => Φ (coefficientBits ell t a β)) =
        finiteAvg (fun b : ι → F2 => Φ ((bitsEquivF2 ι).symm b)) :=
      finiteAvg_bitEval ell hOne a hsize ha
        (fun b : ι → F2 => Φ ((bitsEquivF2 ι).symm b))
    _ = finiteAvg Φ := finiteAvg_equiv (bitsEquivF2 ι).symm Φ

theorem finiteAvg_acceptEval (Φ : (ι → Bool) → ℝ) :
    finiteAvg (fun β : Fin t → F => Φ (acceptEval ell t a β)) =
      finiteAvg Φ := by
  calc
    finiteAvg (fun β : Fin t → F => Φ (acceptEval ell t a β)) =
        finiteAvg (fun b : ι → Bool => Φ (complementEquiv ι b)) :=
      finiteAvg_coefficientBits ell hOne a hsize ha
        (fun b : ι → Bool => Φ (complementEquiv ι b))
    _ = finiteAvg Φ := finiteAvg_equiv (complementEquiv ι) Φ

end Finite

section FiberCounts

variable [Fintype F] [DecidableEq F] [Fintype ι]
variable (ell : F →ₗ[F2] F2) (hOne : ell 1 = 1)
variable {t : ℕ} (a : ι → F) (hsize : Fintype.card ι ≤ t)
variable (ha : Function.Injective a)

include hOne hsize ha

theorem card_bitEval_fiber_mul (b : ι → F2) :
    2 ^ Fintype.card ι *
      Fintype.card {β : Fin t → F // bitEval ell t a β = b} =
        Fintype.card F ^ t := by
  classical
  have hL := bitEval_surjective ell hOne a hsize ha
  have hcard := AlgebraFiniteFibers.card_eq_mul_card_kernel (bitEval ell t a) hL
  rw [← AlgebraFiniteFibers.card_fiber_eq (bitEval ell t a) hL b] at hcard
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using hcard.symm

theorem card_bitEval_fiber {r : ℕ} (hr : 1 ≤ r)
    (hcard : Fintype.card F = 2 ^ r) (b : ι → F2) :
    Fintype.card {β : Fin t → F // bitEval ell t a β = b} =
      2 ^ (r * t - Fintype.card ι) := by
  have hn : Fintype.card ι ≤ r * t := calc
    Fintype.card ι ≤ t := hsize
    _ = 1 * t := (one_mul t).symm
    _ ≤ r * t := Nat.mul_le_mul_right t hr
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < (2 : ℕ)) _)
  calc
    2 ^ Fintype.card ι *
        Fintype.card {β : Fin t → F // bitEval ell t a β = b} =
        Fintype.card F ^ t := card_bitEval_fiber_mul ell hOne a hsize ha b
    _ = 2 ^ (r * t) := by rw [hcard, pow_mul]
    _ = 2 ^ (Fintype.card ι + (r * t - Fintype.card ι)) := by
      rw [Nat.add_sub_of_le hn]
    _ = 2 ^ Fintype.card ι * 2 ^ (r * t - Fintype.card ι) := pow_add _ _ _

end FiberCounts

theorem finiteAvg_acceptEval_finset [Fintype F] {Z : Type uDepth4} [DecidableEq Z]
    (ell : F →ₗ[F2] F2) (hOne : ell 1 = 1) {t : ℕ} (a : Z → F)
    (s : Finset Z) (hsize : s.card ≤ t)
    (ha : Set.InjOn a (↑s : Set Z)) (Φ : (s → Bool) → ℝ) :
    finiteAvg (fun β : Fin t → F => Φ (fun z : s => acceptEval ell t a β z)) =
      finiteAvg Φ := by
  classical
  apply finiteAvg_acceptEval ell hOne (fun z : s => a z)
    (by simpa only [Fintype.card_coe] using hsize)
  intro x y hxy
  exact Subtype.ext (ha x.property y.property hxy)

end Interpolation
end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

theorem finiteProb_abs_avg_gt_le {Ω : Type uDepth1} {Z : Type uDepth2} [Fintype Ω] [Nonempty Ω]
    [Fintype Z] [Nonempty Z] [DecidableEq Z]
    (h : ℕ) (hh : 0 < h) (bits : Ω → Z → Bool)
    (hdist : UniformBitsUpTo (2 * h) bits) (J : Z → Bool)
    (δ : ℝ) (hδ : 0 < δ) :
    finiteProb (fun ω => δ < |finiteAvg (fun z => sign (bits ω z) * indicator (J z))|) ≤
      (((2 * h : ℕ) : ℝ) ^ (2 * h) * (Fintype.card Z : ℝ) ^ h) /
        (δ * (Fintype.card Z : ℝ)) ^ (2 * h) := by
  have hN : 0 < (Fintype.card Z : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnorm (ω : Ω) :
      |finiteAvg (fun z => sign (bits ω z) * indicator (J z))| =
        |∑ z, sign (bits ω z) * indicator (J z)| / (Fintype.card Z : ℝ) := by
    rw [finiteAvg, abs_mul, abs_inv, abs_of_nonneg hN.le, div_eq_inv_mul]
  have hevent :
      finiteProb (fun ω => δ < |finiteAvg (fun z => sign (bits ω z) * indicator (J z))|) ≤
      finiteProb (fun ω => δ * (Fintype.card Z : ℝ) <
        |∑ z, sign (bits ω z) * indicator (J z)|) := by
    apply finiteProb_mono
    intro ω hω
    rw [hnorm ω] at hω
    exact (lt_div_iff₀ hN).mp hω
  exact hevent.trans (finiteProb_abs_gt_le_moment
    (fun ω => ∑ z, sign (bits ω z) * indicator (J z))
    (2 * h) (Nat.mul_pos (by decide) hh)
    (δ * (Fintype.card Z : ℝ))
    (((2 * h : ℕ) : ℝ) ^ (2 * h) * (Fintype.card Z : ℝ) ^ h)
    (mul_pos hδ hN) (even_moment_le_manuscript h bits hdist J))

def sparseMomentBound (m b L h : ℕ) (δ : ℝ) : ℝ :=
  ((((2 * m + 1) ^ b + 1) ^ L : ℕ) : ℝ) *
    ((((2 * h : ℕ) : ℝ) ^ (2 * h) * ((2 ^ m : ℕ) : ℝ) ^ h) /
      (δ * ((2 ^ m : ℕ) : ℝ)) ^ (2 * h))

theorem finiteProb_sparse_codes_gt_le {Ω : Type uDepth3} {V : Type uDepth4} [Fintype Ω] [Nonempty Ω]
    [Fintype V] (b L h : ℕ) (hh : 0 < h)
    (bits : Ω → Cube V → Bool) (hdist : UniformBitsUpTo (2 * h) bits)
    (δ : ℝ) (hδ : 0 < δ) :
    finiteProb (fun ω => ∃ c : SparseTestCode V b L,
      δ < |finiteAvg (fun x => sign (bits ω x) * indicator (c.eval x))|) ≤
      sparseMomentBound (Fintype.card V) b L h δ := by
  let P : SparseTestCode V b L → Ω → Prop := fun c ω =>
    δ < |finiteAvg (fun x => sign (bits ω x) * indicator (c.eval x))|
  let B : ℝ :=
    (((2 * h : ℕ) : ℝ) ^ (2 * h) * (Fintype.card (Cube V) : ℝ) ^ h) /
      (δ * (Fintype.card (Cube V) : ℝ)) ^ (2 * h)
  have hsingle (c : SparseTestCode V b L) : finiteProb (P c) ≤ B :=
    finiteProb_abs_avg_gt_le h hh bits hdist c.eval δ hδ
  calc
    _ ≤ ∑ c : SparseTestCode V b L, finiteProb (P c) := by
      simpa only [P, Finset.mem_univ, true_and] using
        (finiteProb_exists_le_sum (Finset.univ : Finset (SparseTestCode V b L)) P)
    _ ≤ ∑ _c : SparseTestCode V b L, B :=
      Finset.sum_le_sum (fun c _ => hsingle c)
    _ = (Fintype.card (SparseTestCode V b L) : ℝ) * B := by
      simp [nsmul_eq_mul]
    _ = sparseMomentBound (Fintype.card V) b L h δ := by
      simp [B, sparseMomentBound, Cube,
        Fintype.card_bool, mul_comm]

theorem finiteProb_sparse_cnfs_gt_le {Ω : Type uDepth5} {V : Type uDepth6} [Fintype Ω] [Nonempty Ω]
    [Fintype V] (b L h : ℕ) (hh : 0 < h)
    (bits : Ω → Cube V → Bool) (hdist : UniformBitsUpTo (2 * h) bits)
    (δ : ℝ) (hδ : 0 < δ) :
    finiteProb (fun ω => ∃ H : CNF V, H.WidthAtMost b ∧ H.length ≤ L ∧
      δ < |finiteAvg (fun x => sign (bits ω x) * indicator (H.eval x))|) ≤
      sparseMomentBound (Fintype.card V) b L h δ := by
  apply le_trans _ (finiteProb_sparse_codes_gt_le b L h hh bits hdist δ hδ)
  apply finiteProb_mono
  rintro ω ⟨H, hw, hlen, hbad⟩
  obtain ⟨c, hc⟩ := SparseTestCode.exists_eval_eq H hw hlen
  refine ⟨c, ?_⟩
  simpa only [hc] using hbad

theorem acceptEval_uniformBitsUpTo {F : Type uDepth7} {Z : Type uDepth8} [Field F]
    [Module BinaryAlgebra.F2 F] [Fintype F] [DecidableEq Z]
    (ell : F →ₗ[BinaryAlgebra.F2] BinaryAlgebra.F2) (hOne : ell 1 = 1)
    (t : ℕ) (a : Z → F) (ha : Function.Injective a) :
    UniformBitsUpTo t (Interpolation.acceptEval ell t a) := by
  intro s hs Φ
  exact Interpolation.finiteAvg_acceptEval_finset ell hOne a s hs
    (fun _ _ _ _ hxy => ha hxy) Φ

theorem coefficient_sparse_cnfs_gt_le {F : Type uDepth9} {V : Type uDepth10} [Field F]
    [Module BinaryAlgebra.F2 F] [Fintype F] [Fintype V]
    (ell : F →ₗ[BinaryAlgebra.F2] BinaryAlgebra.F2) (hOne : ell 1 = 1)
    (a : Cube V → F) (ha : Function.Injective a)
    (b L h : ℕ) (hh : 0 < h) (δ : ℝ) (hδ : 0 < δ) :
    finiteProb (fun β : Fin (2 * h) → F =>
      ∃ H : CNF V, H.WidthAtMost b ∧ H.length ≤ L ∧
        δ < |finiteAvg (fun x =>
          sign (Interpolation.acceptEval ell (2 * h) a β x) * indicator (H.eval x))|) ≤
      sparseMomentBound (Fintype.card V) b L h δ := by
  exact finiteProb_sparse_cnfs_gt_le b L h hh _
    (acceptEval_uniformBitsUpTo ell hOne (2 * h) a ha) δ hδ

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

open Filter
open scoped Topology

namespace DepthThreeLowerBound

noncomputable def binaryEntropy (x : ℝ) : ℝ :=
  -(x * Real.log x + (1 - x) * Real.log (1 - x)) / Real.log 2

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy]

@[simp] theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy]

theorem binaryEntropy_mul_log_two (x : ℝ) :
    binaryEntropy x * Real.log 2 =
      -(x * Real.log x + (1 - x) * Real.log (1 - x)) := by
  exact div_mul_cancel₀ _ (ne_of_gt (Real.log_pos one_lt_two))

theorem binaryEntropy_nonneg {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    0 ≤ binaryEntropy x := by
  apply div_nonneg
  · exact neg_nonneg.mpr (add_nonpos
      (Real.mul_log_nonpos hx₀ hx₁)
      (Real.mul_log_nonpos (sub_nonneg.mpr hx₁) (sub_le_self _ hx₀)))
  · exact (Real.log_pos one_lt_two).le

theorem continuous_binaryEntropy : Continuous binaryEntropy := by
  unfold binaryEntropy
  exact ((Real.continuous_mul_log.add
    (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).neg).div_const _

theorem tendsto_binaryEntropy_reciprocal :
    Tendsto (fun r : ℕ => binaryEntropy (1 / (r : ℝ))) atTop (𝓝 0) := by
  simpa only [binaryEntropy_zero, Function.comp_def] using
    (continuous_binaryEntropy.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat

theorem exists_integer_entropy_threshold (F : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ, 2 ≤ r ∧ (F : ℝ) * binaryEntropy (1 / (r : ℝ)) ≤ ε := by
  have hlim : Tendsto (fun r : ℕ => (F : ℝ) * binaryEntropy (1 / (r : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul tendsto_binaryEntropy_reciprocal :
        Tendsto (fun r : ℕ => (F : ℝ) * binaryEntropy (1 / (r : ℝ)))
          atTop (𝓝 ((F : ℝ) * 0)))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds hε))
  exact ⟨max N 2, le_max_right _ _, (hN _ (le_max_left _ _)).le⟩

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

variable {V : Type uDepth1}
variable [instDecidableEqV : DecidableEq V]

def clausesOfSize (A : Finset (Clause V)) (u : ℕ) : Finset (Clause V) :=
  A.filter (fun C => C.card = u)

def literalOccurrences (A : Finset (Clause V)) (u : ℕ) (l : Literal V) : ℕ := by
  classical
  exact ((clausesOfSize A u).filter (fun C => l ∈ C)).card

@[simp] theorem mem_clausesOfSize
    {V : Type uDepth1}
    [DecidableEq V]
    {A : Finset (Clause V)} {u : ℕ} {C : Clause V} :
    C ∈ clausesOfSize A u ↔ C ∈ A ∧ C.card = u := by
  simp [clausesOfSize]

theorem clausesOfSize_subset
    {V : Type uDepth1}
    [DecidableEq V]
    (A : Finset (Clause V)) (u : ℕ) :
    clausesOfSize A u ⊆ A := Finset.filter_subset _ _

theorem clausesOfSize_mono
    {V : Type uDepth1}
    [DecidableEq V]
    {A B : Finset (Clause V)} (h : A ⊆ B) (u : ℕ) :
    clausesOfSize A u ⊆ clausesOfSize B u :=
  Finset.filter_subset_filter _ h

theorem clausesOfSize_eq_self
    {V : Type uDepth1}
    [DecidableEq V]
    (A : Finset (Clause V)) (u : ℕ)
    (h : ∀ C ∈ A, C.card = u) : clausesOfSize A u = A :=
  Finset.filter_eq_self.mpr h

theorem clausesOfSize_eq_empty
    {V : Type uDepth1}
    [DecidableEq V]
    (A : Finset (Clause V)) (u : ℕ)
    (h : ∀ C ∈ A, C.card ≠ u) : clausesOfSize A u = ∅ := by
  exact Finset.filter_eq_empty_iff.mpr (fun C hC => h C hC)

theorem literalOccurrences_mono {A B : Finset (Clause V)} (h : A ⊆ B)
    (u : ℕ) (l : Literal V) : literalOccurrences A u l ≤ literalOccurrences B u l := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ (clausesOfSize_mono h u))

theorem literalOccurrences_le_card (A : Finset (Clause V)) (u : ℕ) (l : Literal V) :
    literalOccurrences A u l ≤ (clausesOfSize A u).card := by
  classical
  exact Finset.card_filter_le _ _

theorem literalOccurrences_one_le (A : Finset (Clause V)) (l : Literal V) :
    literalOccurrences A 1 l ≤ 1 := by
  classical
  unfold literalOccurrences
  apply Finset.card_le_one.mpr
  intro C hC D hD
  obtain ⟨hCA, hlC⟩ := Finset.mem_filter.mp hC
  obtain ⟨hDA, hlD⟩ := Finset.mem_filter.mp hD
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (mem_clausesOfSize.mp hCA).2
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp (mem_clausesOfSize.mp hDA).2
  rw [hc] at hlC
  rw [hd] at hlD
  have hcd : c = d := (Finset.mem_singleton.mp hlC).symm.trans
    (Finset.mem_singleton.mp hlD)
  rw [hc, hd, hcd]

theorem clausesOfSize_union (A B : Finset (Clause V)) (u : ℕ) :
    clausesOfSize (A ∪ B) u = clausesOfSize A u ∪ clausesOfSize B u := by
  classical
  exact Finset.filter_union _ _ _

theorem literalOccurrences_union_le (A B : Finset (Clause V)) (u : ℕ) (l : Literal V) :
    literalOccurrences (A ∪ B) u l ≤
      literalOccurrences A u l + literalOccurrences B u l := by
  classical
  unfold literalOccurrences
  rw [clausesOfSize_union, Finset.filter_union]
  exact Finset.card_union_le _ _

theorem clausesOfSize_card_le [Fintype V] (A : Finset (Clause V)) (u n : ℕ)
    (hne : ∀ C ∈ clausesOfSize A u, C.Nonempty)
    (hocc : ∀ l, literalOccurrences A u l ≤ n) :
    (clausesOfSize A u).card ≤ (2 * Fintype.card V) * n := by
  classical
  calc
    (clausesOfSize A u).card = ∑ _C ∈ clausesOfSize A u, 1 :=
      Finset.card_eq_sum_ones _
    _ ≤ ∑ C ∈ clausesOfSize A u, C.card :=
      Finset.sum_le_sum (fun C hC => (hne C hC).card_pos)
    _ ≤ Fintype.card (Literal V) * n := Finset.sum_card_le hocc
    _ = (2 * Fintype.card V) * n := by
      simp only [Literal, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]

theorem subsumed_by_clause_card_le (A : Finset (Clause V)) (u n : ℕ)
    (hocc : ∀ l, literalOccurrences A u l ≤ n)
    (D : Clause V) (hD : D.Nonempty) :
    ((clausesOfSize A u).filter (fun C => D ⊆ C)).card ≤ n := by
  classical
  obtain ⟨l, hl⟩ := hD
  have hsub : (clausesOfSize A u).filter (fun C => D ⊆ C) ⊆
      (clausesOfSize A u).filter (fun C => l ∈ C) := by
    intro C hC
    obtain ⟨hCA, hDC⟩ := Finset.mem_filter.mp hC
    exact Finset.mem_filter.mpr ⟨hCA, hDC hl⟩
  exact (Finset.card_le_card hsub).trans (hocc l)

theorem deleted_clausesOfSize_card_le (A B R : Finset (Clause V)) (u n : ℕ)
    (hne : ∀ D ∈ B, D.Nonempty)
    (hocc : ∀ l, literalOccurrences A u l ≤ n)
    (hsub : R ⊆ clausesOfSize A u)
    (hcover : ∀ C ∈ R, ∃ D ∈ B, D ⊆ C) :
    R.card ≤ B.card * n := by
  classical
  let receiver := fun D : Clause V => (clausesOfSize A u).filter (fun C => D ⊆ C)
  have hR : R ⊆ B.biUnion receiver := by
    intro C hC
    obtain ⟨D, hDB, hDC⟩ := hcover C hC
    exact Finset.mem_biUnion.mpr
      ⟨D, hDB, Finset.mem_filter.mpr ⟨hsub hC, hDC⟩⟩
  exact (Finset.card_le_card hR).trans
    (Finset.card_biUnion_le_card_mul B receiver n
      (fun D hD => subsumed_by_clause_card_le A u n hocc D (hne D hD)))

def subsumedOfSize (A B : Finset (Clause V)) (u : ℕ) : Finset (Clause V) := by
  classical
  exact (clausesOfSize A u).filter (fun C => ∃ D ∈ B, D ⊆ C)

theorem subsumedOfSize_card_le (A B : Finset (Clause V)) (u n : ℕ)
    (hne : ∀ D ∈ B, D.Nonempty)
    (hocc : ∀ l, literalOccurrences A u l ≤ n) :
    (subsumedOfSize A B u).card ≤ B.card * n := by
  classical
  apply deleted_clausesOfSize_card_le A B (subsumedOfSize A B u) u n hne hocc
  · exact Finset.filter_subset _ _
  · intro C hC
    exact (Finset.mem_filter.mp hC).2

theorem clausesOfSize_update_balance
    (A B : Finset (Clause V)) (u : ℕ) (hfresh : Disjoint A B) :
    (clausesOfSize (B ∪ A.filter (fun C => ¬ ∃ D ∈ B, D ⊆ C)) u).card +
        (subsumedOfSize A B u).card =
      (clausesOfSize A u).card + (clausesOfSize B u).card := by
  classical
  let P := fun C : Clause V => ∃ D ∈ B, D ⊆ C
  let S := (clausesOfSize A u).filter (fun C => ¬ P C)
  have hdecomp : clausesOfSize (B ∪ A.filter (fun C => ¬ P C)) u =
      clausesOfSize B u ∪ S := by
    ext C
    simp only [clausesOfSize, Finset.mem_filter, Finset.mem_union, S]
    constructor
    · rintro ⟨hC, hsize⟩
      rcases hC with hCB | ⟨hCA, hP⟩
      · exact Or.inl ⟨hCB, hsize⟩
      · exact Or.inr ⟨⟨hCA, hsize⟩, hP⟩
    · rintro (⟨hCB, hsize⟩ | ⟨⟨hCA, hsize⟩, hP⟩)
      · exact ⟨Or.inl hCB, hsize⟩
      · exact ⟨Or.inr ⟨hCA, hP⟩, hsize⟩
  have hdisj : Disjoint (clausesOfSize B u) S := by
    apply Finset.disjoint_left.mpr
    intro C hCB hCS
    exact Finset.disjoint_left.mp hfresh
      (Finset.mem_filter.mp (Finset.mem_filter.mp hCS).1).1
      (Finset.mem_filter.mp hCB).1
  have hpartition : (subsumedOfSize A B u).card + S.card =
      (clausesOfSize A u).card := by
    change ((clausesOfSize A u).filter P).card +
      ((clausesOfSize A u).filter (fun C => ¬ P C)).card = _
    have hfilters : Disjoint ((clausesOfSize A u).filter P)
        ((clausesOfSize A u).filter (fun C => ¬ P C)) := by
      apply Finset.disjoint_left.mpr
      intro C hC hC'
      exact (Finset.mem_filter.mp hC').2 (Finset.mem_filter.mp hC).2
    rw [← Finset.card_union_of_disjoint hfilters]
    apply congrArg Finset.card
    ext C
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hPC : P C <;> simp [hPC]
  change (clausesOfSize (B ∪ A.filter (fun C => ¬ P C)) u).card +
      (subsumedOfSize A B u).card = _
  rw [hdecomp, Finset.card_union_of_disjoint hdisj]
  calc
    (clausesOfSize B u).card + S.card + (subsumedOfSize A B u).card =
        ((subsumedOfSize A B u).card + S.card) + (clausesOfSize B u).card := by
      simp only [Nat.add_comm, Nat.add_left_comm]
    _ = _ := by rw [hpartition]

theorem literalOccurrences_update_le (A B : Finset (Clause V))
    (u : ℕ) (l : Literal V) :
    literalOccurrences (B ∪ A.filter (fun C => ¬ ∃ D ∈ B, D ⊆ C)) u l ≤
      literalOccurrences A u l + literalOccurrences B u l := by
  classical
  have hsub : B ∪ A.filter (fun C => ¬ ∃ D ∈ B, D ⊆ C) ⊆ A ∪ B := by
    intro C hC
    rcases Finset.mem_union.mp hC with hCB | hCA
    · exact Finset.mem_union.mpr (Or.inr hCB)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp hCA).1)
  exact (literalOccurrences_mono hsub u l).trans
    (literalOccurrences_union_le A B u l)

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

open scoped BigOperators

variable {α : Type uDepth1} [DecidableEq α]

def Sunflower (family : Finset (Finset α)) (core : Finset α) : Prop :=
  ∀ A ∈ family, ∀ B ∈ family, A ≠ B → A ∩ B = core

namespace Sunflower

variable {family : Finset (Finset α)} {core A B : Finset α} {i : ℕ}

theorem mono (h : Sunflower family core) {sub : Finset (Finset α)}
    (hsub : sub ⊆ family) : Sunflower sub core := by
  intro A hA B hB hne
  exact h A (hsub hA) B (hsub hB) hne

theorem core_subset (h : Sunflower family core) (hcard : 2 ≤ family.card)
    (hA : A ∈ family) : core ⊆ A := by
  obtain ⟨B, hB, hBA⟩ : ∃ B ∈ family, B ≠ A := by
    obtain ⟨B, hB, C, hC, hBC⟩ := Finset.one_lt_card.mp (by omega : 1 < family.card)
    by_cases hBA : B = A
    · exact ⟨C, hC, fun hCA => hBC (hBA.trans hCA.symm)⟩
    · exact ⟨B, hB, hBA⟩
  rw [← h A hA B hB hBA.symm]
  exact Finset.inter_subset_left

theorem core_card_lt (h : Sunflower family core) (hcard : 2 ≤ family.card)
    (uniform : ∀ A ∈ family, A.card = i) : core.card < i := by
  obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp (by omega : 1 < family.card)
  by_contra hn
  have hCA : core = A := Finset.eq_of_subset_of_card_le (h.core_subset hcard hA)
    (by rw [uniform A hA]; omega)
  have hCB : core = B := Finset.eq_of_subset_of_card_le (h.core_subset hcard hB)
    (by rw [uniform B hB]; omega)
  exact hAB (hCA.symm.trans hCB)

theorem petal_card (h : Sunflower family core) (hcard : 2 ≤ family.card)
    (uniform : ∀ A ∈ family, A.card = i) (hA : A ∈ family) :
    (A \ core).card = i - core.card := by
  have hcore_inter : core ∩ A = core := by
    ext x
    exact ⟨fun hx => (Finset.mem_inter.mp hx).1,
      fun hx => Finset.mem_inter.mpr ⟨hx, h.core_subset hcard hA hx⟩⟩
  rw [Finset.card_sdiff, hcore_inter, uniform A hA]

theorem petal_nonempty (h : Sunflower family core) (hcard : 2 ≤ family.card)
    (uniform : ∀ A ∈ family, A.card = i) (hA : A ∈ family) :
    (A \ core).Nonempty := by
  apply Finset.card_pos.mp
  rw [h.petal_card hcard uniform hA]
  exact Nat.sub_pos_of_lt (h.core_card_lt hcard uniform)

theorem petal_card_lt (h : Sunflower family core) (hcard : 2 ≤ family.card)
    (uniform : ∀ A ∈ family, A.card = i) (hc : core.Nonempty)
    (hA : A ∈ family) : (A \ core).card < i := by
  rw [h.petal_card hcard uniform hA]
  have hcpos := Finset.card_pos.mpr hc
  have hclt := h.core_card_lt hcard uniform
  omega

theorem petals_disjoint (h : Sunflower family core) (hA : A ∈ family)
    (hB : B ∈ family) (hne : A ≠ B) : Disjoint (A \ core) (B \ core) := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  obtain ⟨hxA, hxc⟩ := Finset.mem_sdiff.mp hxA
  obtain ⟨hxB, _⟩ := Finset.mem_sdiff.mp hxB
  apply hxc
  rw [← h A hA B hB hne]
  exact Finset.mem_inter.mpr ⟨hxA, hxB⟩

theorem petal_injective (h : Sunflower family core) (hcard : 2 ≤ family.card) :
    Set.InjOn (fun A => A \ core) (↑family : Set (Finset α)) := by
  intro A hA B hB heq
  calc
    A = (A \ core) ∪ core := (Finset.sdiff_union_of_subset (h.core_subset hcard hA)).symm
    _ = (B \ core) ∪ core := congrArg (fun D => D ∪ core) heq
    _ = B := Finset.sdiff_union_of_subset (h.core_subset hcard hB)

theorem card_petals (h : Sunflower family core) (hcard : 2 ≤ family.card) :
    (family.image (fun A => A \ core)).card = family.card :=
  Finset.card_image_of_injOn (h.petal_injective hcard)

end Sunflower

private def eraseContaining (family : Finset (Finset α)) (x : α) :
    Finset (Finset α) :=
  (family.filter (fun A => x ∈ A)).image (fun A => A.erase x)

private theorem eraseContaining_card (family : Finset (Finset α)) (x : α) :
    (eraseContaining family x).card = (family.filter (fun A => x ∈ A)).card := by
  apply Finset.card_image_of_injOn
  intro A hA B hB heq
  have hxA := (Finset.mem_filter.mp hA).2
  have hxB := (Finset.mem_filter.mp hB).2
  calc
    A = insert x (A.erase x) := (Finset.insert_erase hxA).symm
    _ = insert x (B.erase x) := congrArg (insert x) heq
    _ = B := Finset.insert_erase hxB

private theorem eraseContaining_uniform (family : Finset (Finset α)) (x : α)
    (i : ℕ) (uniform : ∀ A ∈ family, A.card = i + 1) :
    ∀ B ∈ eraseContaining family x, B.card = i := by
  intro B hB
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨hA, hxA⟩ := Finset.mem_filter.mp hA
  rw [Finset.card_erase_of_mem hxA, uniform A hA]
  omega

private theorem lift_erased_sunflower (family : Finset (Finset α)) (x : α)
    {sub : Finset (Finset α)} {core : Finset α}
    (hsub : sub ⊆ eraseContaining family x) (hs : Sunflower sub core) :
    ∃ lifted ⊆ family, lifted.card = sub.card ∧ Sunflower lifted (insert x core) := by
  have hrestore : ∀ B ∈ sub, insert x B ∈ family ∧ x ∉ B := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp (hsub hB)
    obtain ⟨hA, hxA⟩ := Finset.mem_filter.mp hA
    exact ⟨by simpa only [Finset.insert_erase hxA] using hA, by simp⟩
  refine ⟨sub.image (insert x), ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact (hrestore B hB).1
  · apply Finset.card_image_of_injOn
    intro A hA B hB heq
    have he := congrArg (fun D : Finset α => D.erase x) heq
    simpa only [Finset.erase_insert (hrestore A hA).2,
      Finset.erase_insert (hrestore B hB).2] using he
  · intro A hA B hB hne
    obtain ⟨A₁, hA₁, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_image.mp hB
    have hAB : A₁ ≠ B₁ := fun heq => hne (congrArg (insert x) heq)
    rw [← Finset.insert_inter_distrib, hs A₁ hA₁ B₁ hB₁ hAB]

theorem finite_uniform_sunflower (family : Finset (Finset α)) (s r : ℕ)
    (hr : 2 ≤ r) (uniform : ∀ A ∈ family, A.card = s)
    (large : s.factorial * (r - 1) ^ s < family.card) :
    ∃ sub ⊆ family, sub.card = r ∧ ∃ core, Sunflower sub core := by
  classical
  induction s generalizing family with
  | zero =>
      have hsub : family ⊆ {∅} := by
        intro A hA
        have hzero : A = ∅ := Finset.card_eq_zero.mp (uniform A hA)
        simp only [Finset.mem_singleton, hzero]
      have hsmall : family.card ≤ 1 := by simpa using Finset.card_le_card hsub
      simp only [Nat.factorial_zero, pow_zero, mul_one] at large
      omega
  | succ s ih =>
      let candidates := family.powerset.filter (fun M => Sunflower M (∅ : Finset α))
      have hcandidates : candidates.Nonempty := by
        refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
        intro A hA
        simp at hA
      obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image candidates Finset.card hcandidates
      obtain ⟨hMpow, hMs⟩ := Finset.mem_filter.mp hM
      have hMsub : M ⊆ family := Finset.mem_powerset.mp hMpow
      by_cases hrM : r ≤ M.card
      · obtain ⟨sub, hsub, hcard⟩ := Finset.exists_subset_card_eq hrM
        exact ⟨sub, hsub.trans hMsub, hcard, ∅, hMs.mono hsub⟩
      · have hMcard : M.card ≤ r - 1 := by omega
        let U : Finset α := M.biUnion id
        have hUcard : U.card ≤ (s + 1) * (r - 1) := by
          calc
            U.card ≤ ∑ A ∈ M, A.card := Finset.card_biUnion_le
            _ = ∑ _A ∈ M, (s + 1) := by
              apply Finset.sum_congr rfl
              intro A hA
              exact uniform A (hMsub hA)
            _ = M.card * (s + 1) := by simp
            _ ≤ (r - 1) * (s + 1) := Nat.mul_le_mul_right _ hMcard
            _ = (s + 1) * (r - 1) := Nat.mul_comm _ _
        have hmeet : ∀ A ∈ family, ∃ x, x ∈ A ∧ x ∈ U := by
          intro A hA
          by_contra hnone
          have hAM : A ∉ M := by
            intro hAM
            have hpos : 0 < A.card := by rw [uniform A hA]; omega
            obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
            exact hnone ⟨x, hx, Finset.mem_biUnion.mpr ⟨A, hAM, hx⟩⟩
          have hinter : ∀ B ∈ M, A ∩ B = ∅ := by
            intro B hB
            ext x
            constructor
            · intro hx
              obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
              exact (hnone ⟨x, hxA, Finset.mem_biUnion.mpr ⟨B, hB, hxB⟩⟩).elim
            · simp
          have hinsert : Sunflower (insert A M) (∅ : Finset α) := by
            intro B hB C hC hBC
            rcases Finset.mem_insert.mp hB with rfl | hBM
            · rcases Finset.mem_insert.mp hC with rfl | hCM
              · exact (hBC rfl).elim
              · exact hinter C hCM
            · rcases Finset.mem_insert.mp hC with rfl | hCM
              · simpa only [Finset.inter_comm] using hinter B hBM
              · exact hMs B hBM C hCM hBC
          have hinsertmem : insert A M ∈ candidates := by
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_powerset.mpr ?_, hinsert⟩
            intro B hB
            rcases Finset.mem_insert.mp hB with rfl | hB
            · exact hA
            · exact hMsub hB
          have hbad := hmax (insert A M) hinsertmem
          simp [hAM] at hbad
        obtain ⟨A₀, hA₀⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) large)
        have hA₀pos : 0 < A₀.card := by rw [uniform A₀ hA₀]; omega
        obtain ⟨x₀, _hx₀⟩ := Finset.card_pos.mp hA₀pos
        let f : Finset α → α := fun A =>
          if h : ∃ x, x ∈ A ∧ x ∈ U then h.choose else x₀
        have hf : ∀ A ∈ family, f A ∈ A ∧ f A ∈ U := by
          intro A hA
          dsimp only [f]
          rw [dite_eq_left (hmeet A hA)]
          exact (hmeet A hA).choose_spec
        have hprod : U.card * (s.factorial * (r - 1) ^ s) < family.card := by
          calc
            U.card * (s.factorial * (r - 1) ^ s) ≤
                ((s + 1) * (r - 1)) * (s.factorial * (r - 1) ^ s) :=
              Nat.mul_le_mul_right _ hUcard
            _ = (s + 1).factorial * (r - 1) ^ (s + 1) := by
              rw [Nat.factorial_succ, pow_succ]
              ring
            _ < family.card := large
        obtain ⟨x, _hxU, hxmany⟩ :=
          Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
            (fun A hA => (hf A hA).2) hprod
        have hfiber : (family.filter (fun A => f A = x)) ⊆
            family.filter (fun A => x ∈ A) := by
          intro A hA
          obtain ⟨hA, hfx⟩ := Finset.mem_filter.mp hA
          exact Finset.mem_filter.mpr ⟨hA, hfx ▸ (hf A hA).1⟩
        have herasedlarge : s.factorial * (r - 1) ^ s < (eraseContaining family x).card := by
          rw [eraseContaining_card]
          exact hxmany.trans_le (Finset.card_le_card hfiber)
        obtain ⟨sub, hsub, hsubcard, core, hs⟩ :=
          ih (eraseContaining family x) (eraseContaining_uniform family x s uniform) herasedlarge
        obtain ⟨lifted, hlifted, hcard, hlifts⟩ := lift_erased_sunflower family x hsub hs
        exact ⟨lifted, hlifted, hcard.trans hsubcard, insert x core, hlifts⟩

theorem no_nonempty_core_sunflower_occurrence_le (family : Finset (Finset α))
    (i r : ℕ) (hr : 2 ≤ r) (uniform : ∀ A ∈ family, A.card = i + 1)
    (hno : ∀ sub ⊆ family, sub.card = r →
      ∀ core, core.Nonempty → ¬ Sunflower sub core) (x : α) :
    (family.filter (fun A => x ∈ A)).card ≤ i.factorial * (r - 1) ^ i := by
  classical
  by_contra hn
  have hlarge : i.factorial * (r - 1) ^ i < (eraseContaining family x).card := by
    rw [eraseContaining_card]
    omega
  obtain ⟨sub, hsub, hcard, core, hs⟩ :=
    finite_uniform_sunflower (eraseContaining family x) i r hr
      (eraseContaining_uniform family x i uniform) hlarge
  obtain ⟨lifted, hlifted, hliftedcard, hlifts⟩ := lift_erased_sunflower family x hsub hs
  exact hno lifted hlifted (hliftedcard.trans hcard) (insert x core)
    (Finset.insert_nonempty x core) hlifts

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [instDecidableEqV : DecidableEq V]

def sparseBatchUpdate (A B : Finset (Clause V)) : Finset (Clause V) := by
  classical
  exact B ∪ A.filter (fun C => ¬ ∃ D ∈ B, D ⊆ C)

@[simp] theorem mem_sparseBatchUpdate {A B : Finset (Clause V)} {C : Clause V} :
    C ∈ sparseBatchUpdate A B ↔ C ∈ B ∨ (C ∈ A ∧ ¬ ∃ D ∈ B, D ⊆ C) := by
  classical
  simp only [sparseBatchUpdate, Finset.mem_union, Finset.mem_filter]

theorem batch_subset_sparseBatchUpdate (A B : Finset (Clause V)) :
    B ⊆ sparseBatchUpdate A B := fun _ h => mem_sparseBatchUpdate.mpr (Or.inl h)

theorem sparseBatchUpdate_subset_union (A B : Finset (Clause V)) :
    sparseBatchUpdate A B ⊆ B ∪ A := by
  classical
  intro C hC
  rcases mem_sparseBatchUpdate.mp hC with hB | ⟨hA, _⟩
  · exact Finset.mem_union.mpr (Or.inl hB)
  · exact Finset.mem_union.mpr (Or.inr hA)

theorem sparseBatchUpdate_mono_left {A A' B : Finset (Clause V)} (h : A ⊆ A') :
    sparseBatchUpdate A B ⊆ sparseBatchUpdate A' B := by
  intro C hC
  rcases mem_sparseBatchUpdate.mp hC with hB | ⟨hA, hn⟩
  · exact mem_sparseBatchUpdate.mpr (Or.inl hB)
  · exact mem_sparseBatchUpdate.mpr (Or.inr ⟨h hA, hn⟩)

theorem sparseBatchUpdate_dominates (A B : Finset (Clause V)) {C : Clause V}
    (hC : C ∈ A) : ∃ D ∈ sparseBatchUpdate A B, D ⊆ C := by
  classical
  by_cases h : ∃ D ∈ B, D ⊆ C
  · obtain ⟨D, hD, hDC⟩ := h
    exact ⟨D, batch_subset_sparseBatchUpdate A B hD, hDC⟩
  · exact ⟨C, mem_sparseBatchUpdate.mpr (Or.inr ⟨hC, h⟩), Finset.Subset.refl _⟩

theorem sparseBatchUpdate_satisfies (A B : Finset (Clause V)) (x : Cube V) :
    (∀ C ∈ sparseBatchUpdate A B, C.eval x = true) ↔
      (∀ C ∈ A, C.eval x = true) ∧ (∀ D ∈ B, D.eval x = true) := by
  classical
  constructor
  · intro h
    refine ⟨?_, fun D hD => h D (batch_subset_sparseBatchUpdate A B hD)⟩
    intro C hC
    obtain ⟨D, hD, hDC⟩ := sparseBatchUpdate_dominates A B hC
    exact Clause.eval_mono hDC (h D hD)
  · rintro ⟨hA, hB⟩ C hC
    rcases mem_sparseBatchUpdate.mp hC with hC | ⟨hC, _⟩
    · exact hB C hC
    · exact hA C hC

private theorem bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

structure SparseState (V : Type uDepth2) where
  active : Finset (Clause V)
  side : Finset (Literal V)
  added : Finset (Clause V)

namespace SparseState

def toCNF (s : SparseState V) : CNF V :=
  s.active.toList ++ s.side.toList.map (fun l => {l})

def eval (s : SparseState V) (x : Cube V) : Bool := s.toCNF.eval x

structure Valid (s : SparseState V) (b : ℕ) : Prop where
  normalized : ∀ C ∈ s.active, C.Normalized
  nonempty : ∀ C ∈ s.active, C.Nonempty
  antichain : ∀ C ∈ s.active, ∀ D ∈ s.active, C ⊆ D → C = D
  width_le : ∀ C ∈ s.active, C.width ≤ b
  added_subset : s.added ⊆ s.active

@[simp] theorem eval_eq_true
    {V : Type uDepth1}
    [DecidableEq V]
    (s : SparseState V) (x : Cube V) :
    s.eval x = true ↔
      (∀ C ∈ s.active, C.eval x = true) ∧ (∀ l ∈ s.side, l.eval x = true) := by
  classical
  change CNF.eval (s.active.toList ++ s.side.toList.map (fun l => ({l} : Clause V))) x = true ↔ _
  rw [CNF.eval_eq_true]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro C hC
      exact h C (List.mem_append.mpr (Or.inl (Finset.mem_toList.mpr hC)))
    · intro l hl
      have hunit := h {l} (List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨l, Finset.mem_toList.mpr hl, rfl⟩)))
      simpa only [Clause.eval_singleton] using hunit
  · rintro ⟨hA, hS⟩ C hC
    rcases List.mem_append.mp hC with hC | hC
    · exact hA C (Finset.mem_toList.mp hC)
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hC
      simpa only [Clause.eval_singleton] using hS l (Finset.mem_toList.mp hl)

def batchUpdate (s : SparseState V) (B : Finset (Clause V)) : SparseState V where
  active := sparseBatchUpdate s.active B
  side := s.side
  added := sparseBatchUpdate s.added B

@[simp] theorem batchUpdate_active (s : SparseState V) (B : Finset (Clause V)) :
    (s.batchUpdate B).active = sparseBatchUpdate s.active B := rfl

@[simp] theorem batchUpdate_side (s : SparseState V) (B : Finset (Clause V)) :
    (s.batchUpdate B).side = s.side := rfl

@[simp] theorem batchUpdate_added (s : SparseState V) (B : Finset (Clause V)) :
    (s.batchUpdate B).added = sparseBatchUpdate s.added B := rfl

theorem eval_batchUpdate_eq_true (s : SparseState V) (B : Finset (Clause V))
    (x : Cube V) :
    (s.batchUpdate B).eval x = true ↔ s.eval x = true ∧ ∀ C ∈ B, C.eval x = true := by
  rw [eval_eq_true, eval_eq_true]
  change ((∀ C ∈ sparseBatchUpdate s.active B, C.eval x = true) ∧
      (∀ l ∈ s.side, l.eval x = true)) ↔ _
  rw [sparseBatchUpdate_satisfies]
  constructor
  · rintro ⟨⟨hA, hB⟩, hS⟩
    exact ⟨⟨hA, hS⟩, hB⟩
  · rintro ⟨⟨hA, hS⟩, hB⟩
    exact ⟨⟨hA, hB⟩, hS⟩

end SparseState

structure InsertionBatch (s : SparseState V) (i : ℕ) where
  clauses : Finset (Clause V)
  size : ℕ
  nonempty : clauses.Nonempty
  size_pos : 0 < size
  size_lt : size < i
  uniform : ∀ D ∈ clauses, D.card = size
  subclause : ∀ D ∈ clauses, ∃ A ∈ s.active, D ⊂ A
  pairwise_disjoint : ∀ D ∈ clauses, ∀ E ∈ clauses, D ≠ E → Disjoint D E

namespace InsertionBatch

variable {s : SparseState V} {i b : ℕ}

theorem clause_nonempty
    {V : Type uDepth1}
    [DecidableEq V]
    {s : DepthThreeLowerBound.SparseState V}
    {i : ℕ}
    (B : InsertionBatch s i) (D : Clause V)
    (hD : D ∈ B.clauses) : D.Nonempty :=
  Finset.card_pos.mp (by rw [B.uniform D hD]; exact B.size_pos)

theorem antichain (B : InsertionBatch s i) :
    ∀ D ∈ B.clauses, ∀ E ∈ B.clauses, D ⊆ E → D = E := by
  classical
  intro D hD E hE hDE
  by_contra hne
  obtain ⟨l, hl⟩ := B.clause_nonempty D hD
  exact Finset.disjoint_left.mp (B.pairwise_disjoint D hD E hE hne) hl (hDE hl)

theorem fresh
    {V : Type uDepth1}
    [DecidableEq V]
    {s : DepthThreeLowerBound.SparseState V}
    {i : ℕ}
    {b : ℕ}
    (B : InsertionBatch s i) (hs : s.Valid b) :
    ∀ D ∈ B.clauses, ∀ A ∈ s.active, ¬ A ⊆ D := by
  intro D hD A hA hAD
  obtain ⟨E, hE, hDE⟩ := B.subclause D hD
  have hAE : A = E := hs.antichain A hA E hE (hAD.trans hDE.1)
  apply hDE.2
  simpa only [hAE] using hAD

theorem not_mem_active (B : InsertionBatch s i) (hs : s.Valid b)
    {D : Clause V} (hD : D ∈ B.clauses) : D ∉ s.active :=
  fun hA => B.fresh hs D hD D hA (Finset.Subset.refl _)

theorem disjoint_active (B : InsertionBatch s i) (hs : s.Valid b) :
    Disjoint s.active B.clauses := by
  classical
  exact Finset.disjoint_left.mpr (fun D hA hB => B.not_mem_active hs hB hA)

theorem disjoint_added (B : InsertionBatch s i) (hs : s.Valid b) :
    Disjoint s.added B.clauses := by
  classical
  exact Finset.disjoint_left.mpr
    (fun D hA hB => B.not_mem_active hs hB (hs.added_subset hA))

theorem removed_strict (B : InsertionBatch s i) (hs : s.Valid b)
    {C : Clause V} (hC : C ∈ s.active)
    (hnot : C ∉ sparseBatchUpdate s.active B.clauses) :
    ∃ D ∈ B.clauses, D ⊂ C := by
  classical
  have hex : ∃ D ∈ B.clauses, D ⊆ C := by
    by_contra hnone
    exact hnot (mem_sparseBatchUpdate.mpr (Or.inr ⟨hC, hnone⟩))
  obtain ⟨D, hD, hDC⟩ := hex
  exact ⟨D, hD, hDC, B.fresh hs D hD C hC⟩

theorem normalized
    {V : Type uDepth1}
    [DecidableEq V]
    {s : DepthThreeLowerBound.SparseState V}
    {i : ℕ}
    {b : ℕ}
    (B : InsertionBatch s i) (hs : s.Valid b)
    {D : Clause V} (hD : D ∈ B.clauses) : D.Normalized := by
  obtain ⟨A, hA, hDA⟩ := B.subclause D hD
  exact (hs.normalized A hA).subset hDA.1

theorem width_le
    {V : Type uDepth1}
    [DecidableEq V]
    {s : DepthThreeLowerBound.SparseState V}
    {i : ℕ}
    {b : ℕ}
    (B : InsertionBatch s i) (hs : s.Valid b)
    {D : Clause V} (hD : D ∈ B.clauses) : D.width ≤ b := by
  obtain ⟨A, hA, hDA⟩ := B.subclause D hD
  exact (Clause.width_mono hDA.1).trans (hs.width_le A hA)

theorem valid_batchUpdate (B : InsertionBatch s i) (hs : s.Valid b) :
    (s.batchUpdate B.clauses).Valid b := by
  classical
  refine ⟨?_, ?_, ?_, ?_, sparseBatchUpdate_mono_left hs.added_subset⟩
  · intro C hC
    rcases mem_sparseBatchUpdate.mp hC with hB | ⟨hA, _⟩
    · exact B.normalized hs hB
    · exact hs.normalized C hA
  · intro C hC
    rcases mem_sparseBatchUpdate.mp hC with hB | ⟨hA, _⟩
    · exact B.clause_nonempty C hB
    · exact hs.nonempty C hA
  · intro C hC D hD hCD
    rcases mem_sparseBatchUpdate.mp hC with hCB | ⟨hCA, hCnot⟩
    · rcases mem_sparseBatchUpdate.mp hD with hDB | ⟨hDA, hDnot⟩
      · exact B.antichain C hCB D hDB hCD
      · exact (hDnot ⟨C, hCB, hCD⟩).elim
    · rcases mem_sparseBatchUpdate.mp hD with hDB | ⟨hDA, hDnot⟩
      · exact (B.fresh hs D hDB C hCA hCD).elim
      · exact hs.antichain C hCA D hDA hCD
  · intro C hC
    rcases mem_sparseBatchUpdate.mp hC with hB | ⟨hA, _⟩
    · exact B.width_le hs hB
    · exact hs.width_le C hA

theorem literal_occurrences_le_one (B : InsertionBatch s i) (u : ℕ)
    (l : Literal V) : literalOccurrences B.clauses u l ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro D hD E hE
  obtain ⟨hDsize, hlD⟩ := Finset.mem_filter.mp hD
  obtain ⟨hEsize, hlE⟩ := Finset.mem_filter.mp hE
  have hDB := (mem_clausesOfSize.mp hDsize).1
  have hEB := (mem_clausesOfSize.mp hEsize).1
  by_contra hne
  exact Finset.disjoint_left.mp (B.pairwise_disjoint D hDB E hEB hne) hlD hlE

@[simp] theorem added_eq (B : InsertionBatch s i) :
    (s.batchUpdate B.clauses).added = sparseBatchUpdate s.added B.clauses := rfl

end InsertionBatch

section SignedSunflower

structure SignedSunflower (s : SparseState V) (i r : ℕ) where
  family : Finset (Clause V)
  core : Clause V
  subset_active : family ⊆ s.active
  card_family : family.card = r
  two_le : 2 ≤ r
  uniform : ∀ A ∈ family, A.card = i
  core_nonempty : core.Nonempty
  sunflower : Sunflower family core

namespace SignedSunflower

variable {s : SparseState V} {i r b : ℕ}

theorem card_family_ge_two (f : SignedSunflower s i r) : 2 ≤ f.family.card := by
  rw [f.card_family]
  exact f.two_le

theorem family_nonempty (f : SignedSunflower s i r) : f.family.Nonempty :=
  Finset.card_pos.mp (by have := f.card_family_ge_two; omega)

theorem size_ge_two (f : SignedSunflower s i r) : 2 ≤ i := by
  have hc := Finset.card_pos.mpr f.core_nonempty
  have hi := f.sunflower.core_card_lt f.card_family_ge_two f.uniform
  omega

theorem size_le (f : SignedSunflower s i r) (hs : s.Valid b) : i ≤ b := by
  obtain ⟨A, hA⟩ := f.family_nonempty
  rw [← f.uniform A hA, (hs.normalized A (f.subset_active hA)).card_eq_width]
  exact hs.width_le A (f.subset_active hA)

def petals (f : SignedSunflower s i r) : Finset (Clause V) :=
  f.family.image (fun A => A \ f.core)

@[simp] theorem mem_petals (f : SignedSunflower s i r) (D : Clause V) :
    D ∈ f.petals ↔ ∃ A ∈ f.family, A \ f.core = D := Finset.mem_image

def coreBatch (f : SignedSunflower s i r) : InsertionBatch s i where
  clauses := {f.core}
  size := f.core.card
  nonempty := Finset.singleton_nonempty _
  size_pos := Finset.card_pos.mpr f.core_nonempty
  size_lt := f.sunflower.core_card_lt f.card_family_ge_two f.uniform
  uniform := by intro D hD; simp only [Finset.mem_singleton.mp hD]
  subclause := by
    intro D hD
    have hDcore : D = f.core := Finset.mem_singleton.mp hD
    subst D
    obtain ⟨A, hA⟩ := f.family_nonempty
    refine ⟨A, f.subset_active hA, f.sunflower.core_subset f.card_family_ge_two hA, ?_⟩
    intro hAC
    have hle := Finset.card_le_card hAC
    have hlt := f.sunflower.core_card_lt f.card_family_ge_two f.uniform
    rw [f.uniform A hA] at hle
    omega
  pairwise_disjoint := by
    intro D hD E hE hne
    exact (hne ((Finset.mem_singleton.mp hD).trans (Finset.mem_singleton.mp hE).symm)).elim

def petalBatch (f : SignedSunflower s i r) : InsertionBatch s i where
  clauses := f.petals
  size := i - f.core.card
  nonempty := by
    obtain ⟨A, hA⟩ := f.family_nonempty
    exact ⟨A \ f.core, Finset.mem_image.mpr ⟨A, hA, rfl⟩⟩
  size_pos := Nat.sub_pos_of_lt (f.sunflower.core_card_lt f.card_family_ge_two f.uniform)
  size_lt := by
    have hc := Finset.card_pos.mpr f.core_nonempty
    have hi := f.sunflower.core_card_lt f.card_family_ge_two f.uniform
    omega
  uniform := by
    intro D hD
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hD
    exact f.sunflower.petal_card f.card_family_ge_two f.uniform hA
  subclause := by
    intro D hD
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hD
    refine ⟨A, f.subset_active hA, Finset.sdiff_subset, ?_⟩
    intro hAsub
    have hle := Finset.card_le_card hAsub
    have hlt := f.sunflower.petal_card_lt f.card_family_ge_two f.uniform f.core_nonempty hA
    rw [f.uniform A hA] at hle
    omega
  pairwise_disjoint := by
    intro D hD E hE hne
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hE
    apply f.sunflower.petals_disjoint hA hB
    intro hAB
    exact hne (congrArg (fun C => C \ f.core) hAB)

def batch (f : SignedSunflower s i r) (choice : Bool) : InsertionBatch s i :=
  if choice then f.petalBatch else f.coreBatch

def coreBranch (f : SignedSunflower s i r) : SparseState V :=
  s.batchUpdate f.coreBatch.clauses

def petalBranch (f : SignedSunflower s i r) : SparseState V :=
  { s.batchUpdate f.petalBatch.clauses with side := s.side ∪ f.core.image Literal.compl }

def branch (f : SignedSunflower s i r) (choice : Bool) : SparseState V :=
  if choice then f.petalBranch else f.coreBranch

@[simp] theorem branch_active (f : SignedSunflower s i r) (choice : Bool) :
    (f.branch choice).active = sparseBatchUpdate s.active (f.batch choice).clauses := by
  cases choice <;> rfl

@[simp] theorem branch_added (f : SignedSunflower s i r) (choice : Bool) :
    (f.branch choice).added = sparseBatchUpdate s.added (f.batch choice).clauses := by
  cases choice <;> rfl

theorem batch_card (f : SignedSunflower s i r) (choice : Bool) :
    (f.batch choice).clauses.card = if choice then r else 1 := by
  cases choice
  · exact Finset.card_singleton _
  · exact (f.sunflower.card_petals f.card_family_ge_two).trans f.card_family

theorem coreBranch_valid (f : SignedSunflower s i r) (hs : s.Valid b) :
    f.coreBranch.Valid b := f.coreBatch.valid_batchUpdate hs

theorem petalBranch_valid (f : SignedSunflower s i r) (hs : s.Valid b) :
    f.petalBranch.Valid b := by
  have h := f.petalBatch.valid_batchUpdate hs
  exact ⟨h.normalized, h.nonempty, h.antichain, h.width_le, h.added_subset⟩

theorem branch_valid (f : SignedSunflower s i r) (choice : Bool) (hs : s.Valid b) :
    (f.branch choice).Valid b := by
  cases choice
  · exact f.coreBranch_valid hs
  · exact f.petalBranch_valid hs

theorem core_false_iff_complement_units (C : Clause V) (x : Cube V) :
    C.eval x = false ↔ ∀ l ∈ C.image Literal.compl, l.eval x = true := by
  constructor
  · intro hC l hl
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
    have haf : a.eval x = false := by
      cases hax : a.eval x
      · rfl
      · have hCt : C.eval x = true :=
          (Clause.eval_eq_true C x).mpr ⟨a, ha, (Literal.eval_eq_true a x).mp hax⟩
        exact (Bool.false_ne_true (hC.symm.trans hCt)).elim
    simp only [Literal.eval_compl, haf, Bool.not_false]
  · intro h
    cases hC : C.eval x
    · rfl
    · obtain ⟨a, ha, hax⟩ := (Clause.eval_eq_true C x).mp hC
      have hat : a.eval x = true := (Literal.eval_eq_true a x).mpr hax
      have hbad := h a.compl (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      simp only [Literal.eval_compl, hat, Bool.not_true] at hbad
      exact (Bool.false_ne_true hbad).elim

theorem petals_true_of_core_false (f : SignedSunflower s i r) (x : Cube V)
    (hA : ∀ C ∈ s.active, C.eval x = true) (hC : f.core.eval x = false) :
    ∀ P ∈ f.petals, P.eval x = true := by
  intro P hP
  obtain ⟨A, hAfamily, rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨l, hlA, hlx⟩ := (Clause.eval_eq_true A x).mp (hA A (f.subset_active hAfamily))
  have hlnot : l ∉ f.core := by
    intro hlcore
    have htrue := (Clause.eval_eq_true f.core x).mpr ⟨l, hlcore, hlx⟩
    exact Bool.false_ne_true (hC.symm.trans htrue)
  exact (Clause.eval_eq_true (A \ f.core) x).mpr
    ⟨l, Finset.mem_sdiff.mpr ⟨hlA, hlnot⟩, hlx⟩

theorem eval_coreBranch (f : SignedSunflower s i r) (x : Cube V) :
    f.coreBranch.eval x = (s.eval x && f.core.eval x) := by
  apply bool_eq_of_true_iff
  change (s.batchUpdate {f.core}).eval x = true ↔ _
  rw [SparseState.eval_batchUpdate_eq_true, Bool.and_eq_true]
  simp only [Finset.mem_singleton, forall_eq]

theorem eval_petalBranch (f : SignedSunflower s i r) (x : Cube V) :
    f.petalBranch.eval x = (s.eval x && !(f.core.eval x)) := by
  apply bool_eq_of_true_iff
  rw [SparseState.eval_eq_true, Bool.and_eq_true, SparseState.eval_eq_true]
  change ((∀ C ∈ sparseBatchUpdate s.active f.petals, C.eval x = true) ∧
      (∀ l ∈ s.side ∪ f.core.image Literal.compl, l.eval x = true)) ↔ _
  rw [sparseBatchUpdate_satisfies]
  constructor
  · rintro ⟨⟨hA, _hP⟩, hS⟩
    have hc : f.core.eval x = false :=
      (core_false_iff_complement_units f.core x).mpr
        (fun l hl => hS l (Finset.mem_union.mpr (Or.inr hl)))
    refine ⟨⟨hA, fun l hl => hS l (Finset.mem_union.mpr (Or.inl hl))⟩, ?_⟩
    simp only [hc, Bool.not_false]
  · rintro ⟨⟨hA, hS⟩, hnot⟩
    have hc : f.core.eval x = false := by
      cases he : f.core.eval x <;> simp_all
    refine ⟨⟨hA, f.petals_true_of_core_false x hA hc⟩, ?_⟩
    intro l hl
    rcases Finset.mem_union.mp hl with hl | hl
    · exact hS l hl
    · exact (core_false_iff_complement_units f.core x).mp hc l hl

theorem branch_indicator (f : SignedSunflower s i r) (x : Cube V) :
    indicator (s.eval x) = indicator (f.coreBranch.eval x) +
      indicator (f.petalBranch.eval x) := by
  rw [f.eval_coreBranch, f.eval_petalBranch]
  cases s.eval x <;> cases f.core.eval x <;> simp

theorem branch_disjoint (f : SignedSunflower s i r) (x : Cube V) :
    ¬ (f.coreBranch.eval x = true ∧ f.petalBranch.eval x = true) := by
  rw [f.eval_coreBranch, f.eval_petalBranch]
  cases s.eval x <;> cases f.core.eval x <;> simp

end SignedSunflower
end SignedSunflower

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

open scoped BigOperators

variable {V : Type uDepth1} [DecidableEq V]

structure SparseNumerics (r e D : ℕ → ℕ) (b : ℕ) : Prop where
  r_ge_two : ∀ i, 2 ≤ i → i ≤ b → 2 ≤ r i
  e_one : e 1 = 1
  e_succ : ∀ i, 1 ≤ i → i + 1 ≤ b →
    e (i + 1) = i.factorial * (r (i + 1) - 1) ^ i
  D_eq : ∀ i, 1 ≤ i → i ≤ b →
    D i = (e i + 1) * (2 + ∑ v ∈ Finset.Ico 1 i, D v)

theorem sparse_occurrence_le_of_no_sunflower
    {r e D : ℕ → ℕ} {b : ℕ} (hnum : SparseNumerics r e D b)
    (s : SparseState V) (u : ℕ) (hu : 1 ≤ u) (hub : u ≤ b)
    (hno : ¬ Nonempty (SignedSunflower s u (r u))) (l : Literal V) :
    literalOccurrences s.active u l ≤ e u := by
  classical
  cases u with
  | zero => omega
  | succ i =>
      by_cases hi : i = 0
      · subst i
        simpa only [hnum.e_one] using literalOccurrences_one_le s.active l
      · have hi1 : 1 ≤ i := by omega
        have hr : 2 ≤ r (i + 1) := hnum.r_ge_two _ (by omega) hub
        rw [hnum.e_succ i hi1 hub]
        apply no_nonempty_core_sunflower_occurrence_le
          (clausesOfSize s.active (i + 1)) i (r (i + 1)) hr
          (fun C hC => (mem_clausesOfSize.mp hC).2)
        intro sub hsub hcard core hcore hflower
        apply hno
        exact ⟨{
          family := sub
          core := core
          subset_active := hsub.trans (clausesOfSize_subset s.active (i + 1))
          card_family := hcard
          two_le := hr
          uniform := fun C hC => (mem_clausesOfSize.mp (hsub hC)).2
          core_nonempty := hcore
          sunflower := hflower
        }⟩

structure SparseStep (r : ℕ → ℕ) (s t : SparseState V) where
  size : ℕ
  selected : SignedSunflower s size (r size)
  minimal : ∀ j, 2 ≤ j → j < size →
    ¬ Nonempty (SignedSunflower s j (r j))
  choice : Bool
  target : t = selected.branch choice

namespace SparseStep

noncomputable def batch {r : ℕ → ℕ} {s t : SparseState V}
    (step : SparseStep r s t) : InsertionBatch s step.size :=
  step.selected.batch step.choice

theorem target_active {r : ℕ → ℕ} {s t : SparseState V}
    (step : SparseStep r s t) :
    t.active = sparseBatchUpdate s.active step.batch.clauses := by
  exact (congrArg (fun q : SparseState V => q.active) step.target).trans
    (step.selected.branch_active step.choice)

theorem target_added {r : ℕ → ℕ} {s t : SparseState V}
    (step : SparseStep r s t) :
    t.added = sparseBatchUpdate s.added step.batch.clauses := by
  exact (congrArg (fun q : SparseState V => q.added) step.target).trans
    (step.selected.branch_added step.choice)

theorem valid {r : ℕ → ℕ} {s t : SparseState V} {b : ℕ}
    (step : SparseStep r s t) (hs : s.Valid b) : t.Valid b := by
  rw [step.target]
  exact step.selected.branch_valid step.choice hs

theorem fresh_added {r : ℕ → ℕ} {s t : SparseState V} {b : ℕ}
    (step : SparseStep r s t) (hs : s.Valid b) :
    Disjoint s.added step.batch.clauses := by
  classical
  apply Finset.disjoint_left.mpr
  intro C hCa hCB
  exact step.batch.fresh hs C hCB C (hs.added_subset hCa) (Finset.Subset.refl C)

theorem batch_size_count {r : ℕ → ℕ} {s t : SparseState V}
    (step : SparseStep r s t) (u : ℕ) :
    (clausesOfSize step.batch.clauses u).card =
      if step.batch.size = u then step.batch.clauses.card else 0 := by
  classical
  by_cases h : step.batch.size = u
  · have hself : clausesOfSize step.batch.clauses u = step.batch.clauses :=
      clausesOfSize_eq_self _ _ (fun C hC => (step.batch.uniform C hC).trans h)
    rw [ite_eq_left h, hself]
  · have hempty : clausesOfSize step.batch.clauses u = ∅ := by
      apply clausesOfSize_eq_empty
      intro C hC
      rw [step.batch.uniform C hC]
      exact h
    rw [ite_eq_right h, hempty, Finset.card_empty]

theorem removed_eq_empty_of_le {r : ℕ → ℕ} {s t : SparseState V} {b : ℕ}
    (step : SparseStep r s t) (hs : s.Valid b) (u : ℕ)
    (hu : u ≤ step.batch.size) : subsumedOfSize s.added step.batch.clauses u = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hC
  obtain ⟨hC, D, hDB, hDC⟩ := Finset.mem_filter.mp hC
  obtain ⟨hCa, hCu⟩ := mem_clausesOfSize.mp hC
  have hsize : C.card ≤ D.card := by rw [hCu, step.batch.uniform D hDB]; exact hu
  have heq : D = C := Finset.eq_of_subset_of_card_le hDC hsize
  subst D
  exact step.batch.fresh hs C hDB C (hs.added_subset hCa) (Finset.Subset.refl C)

theorem update_balance {r : ℕ → ℕ} {s t : SparseState V} {b : ℕ}
    (step : SparseStep r s t) (hs : s.Valid b) (u : ℕ) :
    (clausesOfSize t.added u).card + (subsumedOfSize s.added step.batch.clauses u).card =
      (clausesOfSize s.added u).card +
        if step.batch.size = u then step.batch.clauses.card else 0 := by
  rw [step.target_added, ← step.batch_size_count u]
  exact clausesOfSize_update_balance s.added step.batch.clauses u (step.fresh_added hs)

end SparseStep

inductive SparsePath (r : ℕ → ℕ) (start : SparseState V) : SparseState V → Type _
  | nil : SparsePath r start start
  | snoc {s t : SparseState V} (path : SparsePath r start s)
      (step : SparseStep r s t) : SparsePath r start t

namespace SparsePath

variable {r e D : ℕ → ℕ} {b : ℕ} {start finish : SparseState V}

def length : {finish : SparseState V} → SparsePath r start finish → ℕ
  | _, .nil => 0
  | _, .snoc path _ => length path + 1

noncomputable def insertions :
    {finish : SparseState V} → SparsePath r start finish → ℕ → ℕ
  | _, .nil, _ => 0
  | _, .snoc path step, u =>
      insertions path u + if step.batch.size = u then step.batch.clauses.card else 0

def processed : {finish : SparseState V} → SparsePath r start finish → ℕ → ℕ
  | _, .nil, _ => 0
  | _, .snoc path step, i => processed path i + if step.size = i then 1 else 0

def petalSteps : {finish : SparseState V} → SparsePath r start finish → ℕ → ℕ
  | _, .nil, _ => 0
  | _, .snoc path step, i =>
      petalSteps path i + if step.size = i ∧ step.choice = true then 1 else 0

theorem valid (path : SparsePath r start finish) (hstart : start.Valid b) :
    finish.Valid b := by
  induction path with
  | nil => exact hstart
  | snoc path step ih => exact step.valid ih

@[simp] theorem insertions_nil (u : ℕ) :
    (SparsePath.nil : SparsePath r start start).insertions u = 0 := rfl

@[simp] theorem insertions_snoc {s t : SparseState V}
    (path : SparsePath r start s) (step : SparseStep r s t) (u : ℕ) :
    (path.snoc step).insertions u =
      path.insertions u + if step.batch.size = u then step.batch.clauses.card else 0 := rfl

theorem insertions_sum_snoc {s t : SparseState V}
    (path : SparsePath r start s) (step : SparseStep r s t) (u : ℕ) :
    (∑ v ∈ Finset.Ico 1 u, (path.snoc step).insertions v) =
      (∑ v ∈ Finset.Ico 1 u, path.insertions v) +
        if step.batch.size < u then step.batch.clauses.card else 0 := by
  classical
  simp only [insertions_snoc, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_Ico, Nat.succ_le_iff.mpr step.batch.size_pos, true_and]

theorem added_occurrence_bound (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) :
    ∀ u, 1 ≤ u → u ≤ b → ∀ l,
      literalOccurrences finish.added u l ≤ e u + 1 := by
  classical
  induction path with
  | nil =>
      intro u hu hub l
      simp [hadded, literalOccurrences, clausesOfSize]
  | @snoc s t path step ih =>
      intro u hu hub l
      have hs := path.valid hstart
      have hupdate := literalOccurrences_update_le s.added step.batch.clauses u l
      change literalOccurrences (sparseBatchUpdate s.added step.batch.clauses) u l ≤ _ at hupdate
      rw [← step.target_added] at hupdate
      by_cases hsize : step.batch.size = u
      · have hlt : u < step.size := hsize ▸ step.batch.size_lt
        have hpre := sparse_occurrence_le_of_no_sunflower hnum s u hu hub
          (fun hflower => step.minimal u (by
            have hflower_size : 2 ≤ u := (Classical.choice hflower).size_ge_two
            exact hflower_size) hlt hflower) l
        have hadd := literalOccurrences_mono hs.added_subset u l
        have hbatch := step.batch.literal_occurrences_le_one u l
        omega
      · have hempty : clausesOfSize step.batch.clauses u = ∅ := by
          apply clausesOfSize_eq_empty
          intro C hC
          rw [step.batch.uniform C hC]
          exact hsize
        have hzero : literalOccurrences step.batch.clauses u l = 0 := by
          simp [literalOccurrences, hempty]
        have hprev := ih u hu hub l
        omega

theorem online_insertion_bound (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) :
    ∀ u, 1 ≤ u → u ≤ b →
      path.insertions u ≤ (clausesOfSize finish.added u).card +
        (e u + 1) * ∑ v ∈ Finset.Ico 1 u, path.insertions v := by
  classical
  induction path with
  | nil =>
      intro u hu hub
      simp [hadded, clausesOfSize]
  | @snoc s t path step ih =>
      intro u hu hub
      have hs := path.valid hstart
      have hbalance := step.update_balance hs u
      have hprev := ih u hu hub
      have hocc := path.added_occurrence_bound hnum hstart hadded u hu hub
      have hremoved := subsumedOfSize_card_le s.added step.batch.clauses u (e u + 1)
        (fun C hC => step.batch.clause_nonempty C hC) hocc
      rw [insertions_snoc, insertions_sum_snoc]
      by_cases hlt : step.batch.size < u
      · have hne : step.batch.size ≠ u := Nat.ne_of_lt hlt
        simp only [ite_eq_right hne, ite_eq_left hlt, Nat.add_zero] at hbalance ⊢
        nlinarith
      · have hremoved_zero := step.removed_eq_empty_of_le hs u (Nat.le_of_not_gt hlt)
        rw [hremoved_zero, Finset.card_empty, Nat.add_zero] at hbalance
        simp only [ite_eq_right hlt, Nat.add_zero]
        omega

theorem insertion_recurrence [Fintype V] (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) (u : ℕ) (hu : 1 ≤ u) (hub : u ≤ b) :
    path.insertions u ≤ (e u + 1) *
      (2 * Fintype.card V + ∑ v ∈ Finset.Ico 1 u, path.insertions v) := by
  have hv := path.valid hstart
  have hsurvive := clausesOfSize_card_le finish.added u (e u + 1)
    (fun C hC => hv.nonempty C (hv.added_subset (mem_clausesOfSize.mp hC).1))
    (path.added_occurrence_bound hnum hstart hadded u hu hub)
  have honline := path.online_insertion_bound hnum hstart hadded u hu hub
  nlinarith

theorem length_le_insertions (path : SparsePath r start finish)
    (hstart : start.Valid b) :
    path.length ≤ ∑ u ∈ Finset.Ico 1 b, path.insertions u := by
  induction path with
  | nil => simp [length]
  | @snoc s t path step ih =>
      have hbatch : 0 < step.batch.clauses.card := step.batch.nonempty.card_pos
      have hsize : step.batch.size < b :=
        step.batch.size_lt.trans_le (step.selected.size_le (path.valid hstart))
      change path.length + 1 ≤ _
      rw [insertions_sum_snoc, ite_eq_left hsize]
      omega

theorem processed_le_insertions (path : SparsePath r start finish) (i : ℕ) :
    path.processed i ≤ ∑ u ∈ Finset.Ico 1 i, path.insertions u := by
  induction path with
  | nil => simp [processed]
  | @snoc s t path step ih =>
      have hbatch : 0 < step.batch.clauses.card := step.batch.nonempty.card_pos
      change path.processed i + (if step.size = i then 1 else 0) ≤ _
      rw [insertions_sum_snoc]
      by_cases hi : step.size = i
      · have hsize : step.batch.size < i := hi ▸ step.batch.size_lt
        simp only [ite_eq_left hi, ite_eq_left hsize]
        omega
      · simp only [ite_eq_right hi, Nat.add_zero]
        split <;> omega

theorem petalSteps_mul_le_insertions (path : SparsePath r start finish) (i : ℕ) :
    r i * path.petalSteps i ≤ ∑ u ∈ Finset.Ico 1 i, path.insertions u := by
  induction path with
  | nil => simp [petalSteps]
  | @snoc s t path step ih =>
      change r i * (path.petalSteps i +
        if step.size = i ∧ step.choice = true then 1 else 0) ≤ _
      rw [insertions_sum_snoc]
      by_cases hi : step.size = i ∧ step.choice = true
      · have hsize : step.batch.size < i := hi.1 ▸ step.batch.size_lt
        have hcard : step.batch.clauses.card = r i := by
          simp only [SparseStep.batch, step.selected.batch_card, hi.2, ↓reduceIte, hi.1]
        simp only [ite_eq_left hi, ite_eq_left hsize, Nat.mul_add, Nat.mul_one, hcard]
        omega
      · simp only [ite_eq_right hi, Nat.add_zero]
        split <;> omega

end SparsePath

theorem sparse_insertion_budget_of_recurrence
    (r e D N : ℕ → ℕ) (b m : ℕ) (hnum : SparseNumerics r e D b)
    (hN : ∀ u, 1 ≤ u → u ≤ b →
      N u ≤ (e u + 1) * (2 * m + ∑ v ∈ Finset.Ico 1 u, N v)) :
    ∀ u, 1 ≤ u → u ≤ b → N u ≤ D u * m := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
      intro hu hub
      have hsum : (∑ v ∈ Finset.Ico 1 u, N v) ≤
          (∑ v ∈ Finset.Ico 1 u, D v) * m := by
        calc
          (∑ v ∈ Finset.Ico 1 u, N v) ≤
              ∑ v ∈ Finset.Ico 1 u, D v * m := by
            apply Finset.sum_le_sum
            intro v hv
            have hv' := Finset.mem_Ico.mp hv
            exact ih v hv'.2 hv'.1 (le_trans (Nat.le_of_lt hv'.2) hub)
          _ = _ := (Finset.sum_mul _ _ _).symm
      calc
        N u ≤ (e u + 1) * (2 * m + ∑ v ∈ Finset.Ico 1 u, N v) := hN u hu hub
        _ ≤ (e u + 1) * (2 * m + (∑ v ∈ Finset.Ico 1 u, D v) * m) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_left hsum _)
        _ = D u * m := by
          rw [hnum.D_eq u hu hub, ← Nat.add_mul, Nat.mul_assoc]

namespace SparsePath

variable {r e D : ℕ → ℕ} {b : ℕ} {start finish : SparseState V}

theorem insertion_budget [Fintype V] (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) (u : ℕ) (hu : 1 ≤ u) (hub : u ≤ b) :
    path.insertions u ≤ D u * Fintype.card V :=
  sparse_insertion_budget_of_recurrence r e D path.insertions b (Fintype.card V) hnum
    (path.insertion_recurrence hnum hstart hadded) u hu hub

theorem insertion_sum_budget [Fintype V] (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) (i : ℕ) (hi : i ≤ b + 1) :
    (∑ u ∈ Finset.Ico 1 i, path.insertions u) ≤
      (∑ u ∈ Finset.Ico 1 i, D u) * Fintype.card V := by
  calc
    (∑ u ∈ Finset.Ico 1 i, path.insertions u) ≤
        ∑ u ∈ Finset.Ico 1 i, D u * Fintype.card V := by
      apply Finset.sum_le_sum
      intro u hu
      have hu' := Finset.mem_Ico.mp hu
      exact path.insertion_budget hnum hstart hadded u hu'.1 (by omega)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem length_budget [Fintype V] (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) :
    path.length ≤ (∑ u ∈ Finset.Ico 1 b, D u) * Fintype.card V :=
  (path.length_le_insertions hstart).trans
    (path.insertion_sum_budget hnum hstart hadded b (by omega))

theorem processed_budget [Fintype V] (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) (i : ℕ) (hi : i ≤ b) :
    path.processed i ≤ (∑ u ∈ Finset.Ico 1 i, D u) * Fintype.card V :=
  (path.processed_le_insertions i).trans
    (path.insertion_sum_budget hnum hstart hadded i (by omega))

theorem petalSteps_budget [Fintype V] (path : SparsePath r start finish)
    (hnum : SparseNumerics r e D b) (hstart : start.Valid b)
    (hadded : start.added = ∅) (i : ℕ) (hi : i ≤ b) :
    r i * path.petalSteps i ≤ (∑ u ∈ Finset.Ico 1 i, D u) * Fintype.card V :=
  (path.petalSteps_mul_le_insertions i).trans
    (path.insertion_sum_budget hnum hstart hadded i (by omega))

end SparsePath

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace DepthThreeLowerBound

open scoped BigOperators

structure SparseLevel where
  r : ℕ
  e : ℕ
  D : ℕ
  F : ℕ

private def nextSparseLevel (ε : ℝ) (hε : 0 < ε) (i : ℕ)
    (previous : SparseLevel) : SparseLevel :=
  let F := previous.F + previous.D
  let r := Classical.choose (exists_integer_entropy_threshold F hε)
  let e := i.factorial * (r - 1) ^ i
  ⟨r, e, (e + 1) * (2 + F), F⟩

def sparseLevel (ε : ℝ) (hε : 0 < ε) : ℕ → SparseLevel
  | 0 => ⟨2, 0, 0, 0⟩
  | 1 => ⟨2, 1, 4, 0⟩
  | n + 2 => nextSparseLevel ε hε (n + 1) (sparseLevel ε hε (n + 1))

def sparseR (ε : ℝ) (hε : 0 < ε) (i : ℕ) : ℕ := (sparseLevel ε hε i).r
def sparseE (ε : ℝ) (hε : 0 < ε) (i : ℕ) : ℕ := (sparseLevel ε hε i).e
def sparseD (ε : ℝ) (hε : 0 < ε) (i : ℕ) : ℕ := (sparseLevel ε hε i).D
def sparseF (ε : ℝ) (hε : 0 < ε) (i : ℕ) : ℕ := (sparseLevel ε hε i).F

variable (ε : ℝ) (hε : 0 < ε)

@[simp] theorem sparseE_zero : sparseE ε hε 0 = 0 := rfl
@[simp] theorem sparseD_zero : sparseD ε hε 0 = 0 := rfl
@[simp] theorem sparseF_zero : sparseF ε hε 0 = 0 := rfl
@[simp] theorem sparseE_one : sparseE ε hε 1 = 1 := rfl
@[simp] theorem sparseD_one : sparseD ε hε 1 = 4 := rfl
@[simp] theorem sparseF_one : sparseF ε hε 1 = 0 := rfl

theorem sparseR_succ_succ (n : ℕ) :
    sparseR ε hε (n + 2) = Classical.choose
      (exists_integer_entropy_threshold (sparseF ε hε (n + 1) + sparseD ε hε (n + 1)) hε) :=
  rfl

theorem sparseF_succ_succ (n : ℕ) :
    sparseF ε hε (n + 2) = sparseF ε hε (n + 1) + sparseD ε hε (n + 1) := rfl

theorem sparseE_succ_succ (n : ℕ) :
    sparseE ε hε (n + 2) = (n + 1).factorial * (sparseR ε hε (n + 2) - 1) ^ (n + 1) :=
  rfl

theorem sparseD_succ_succ (n : ℕ) :
    sparseD ε hε (n + 2) =
      (sparseE ε hε (n + 2) + 1) * (2 + sparseF ε hε (n + 2)) := rfl

theorem sparseR_ge_two (i : ℕ) : 2 ≤ sparseR ε hε i := by
  cases i with
  | zero => exact le_rfl
  | succ i =>
      cases i with
      | zero => exact le_rfl
      | succ n =>
          rw [sparseR_succ_succ]
          exact (Classical.choose_spec
            (exists_integer_entropy_threshold
              (sparseF ε hε (n + 1) + sparseD ε hε (n + 1)) hε)).1

theorem sparseF_eq_sum_Ico (i : ℕ) :
    sparseF ε hε i = ∑ v ∈ Finset.Ico 1 i, sparseD ε hε v := by
  induction i with
  | zero => simp
  | succ i ih =>
      cases i with
      | zero => simp
      | succ n =>
          rw [sparseF_succ_succ, ih]
          exact (Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1) (sparseD ε hε)).symm

theorem sparseE_succ (i : ℕ) (hi : 1 ≤ i) :
    sparseE ε hε (i + 1) = i.factorial * (sparseR ε hε (i + 1) - 1) ^ i := by
  cases i with
  | zero => omega
  | succ n => exact sparseE_succ_succ ε hε n

theorem sparseD_eq (i : ℕ) (hi : 1 ≤ i) :
    sparseD ε hε i =
      (sparseE ε hε i + 1) * (2 + ∑ v ∈ Finset.Ico 1 i, sparseD ε hε v) := by
  cases i with
  | zero => omega
  | succ i =>
      cases i with
      | zero => simp
      | succ n => rw [sparseD_succ_succ, sparseF_eq_sum_Ico]

theorem sparseE_pos (i : ℕ) (hi : 1 ≤ i) : 0 < sparseE ε hε i := by
  cases i with
  | zero => omega
  | succ i =>
      cases i with
      | zero => simp
      | succ n =>
          rw [sparseE_succ_succ]
          have hr := sparseR_ge_two ε hε (n + 2)
          exact Nat.mul_pos (Nat.factorial_pos _) (pow_pos (by omega) _)

theorem sparseD_pos (i : ℕ) (hi : 1 ≤ i) : 0 < sparseD ε hε i := by
  rw [sparseD_eq ε hε i hi]
  exact Nat.mul_pos (by omega) (by omega)

theorem sparse_entropy_bound (i : ℕ) (hi : 2 ≤ i) :
    (sparseF ε hε i : ℝ) * binaryEntropy (1 / (sparseR ε hε i : ℝ)) ≤ ε := by
  cases i with
  | zero => omega
  | succ i =>
      cases i with
      | zero => omega
      | succ n =>
          rw [sparseF_succ_succ, sparseR_succ_succ]
          exact (Classical.choose_spec
            (exists_integer_entropy_threshold
              (sparseF ε hε (n + 1) + sparseD ε hε (n + 1)) hε)).2

theorem sparseNumerics (b : ℕ) :
    SparseNumerics (sparseR ε hε) (sparseE ε hε) (sparseD ε hε) b where
  r_ge_two i _ _ := sparseR_ge_two ε hε i
  e_one := sparseE_one ε hε
  e_succ i hi _ := sparseE_succ ε hε i hi
  D_eq i hi _ := sparseD_eq ε hε i hi

def sparseM (b : ℕ) : ℕ := 2 + 2 * ∑ i ∈ Finset.Icc 1 b, sparseE ε hε i

theorem sparseM_eq (b : ℕ) :
    sparseM ε hε b = 2 + 2 * ∑ i ∈ Finset.Icc 1 b, sparseE ε hε i := rfl

theorem sparseM_pos (b : ℕ) : 0 < sparseM ε hε b := by
  unfold sparseM
  omega

theorem sparse_tolerance_pos {b : ℕ} {η : ℝ} (hb : 1 ≤ b) (hη : 0 < η) :
    0 < η / (b : ℝ) := by
  apply div_pos hη
  exact_mod_cast (show 0 < b by omega)

theorem exists_sparse_numerics (b : ℕ) (η : ℝ) (hb : 1 ≤ b) (hη : 0 < η) :
    ∃ (r e D F : ℕ → ℕ) (M : ℕ),
      SparseNumerics r e D b ∧
      (∀ i, 2 ≤ r i) ∧ F 0 = 0 ∧ F 1 = 0 ∧
      (∀ i, F i = ∑ v ∈ Finset.Ico 1 i, D v) ∧
      (∀ i, 2 ≤ i → i ≤ b →
        (F i : ℝ) * binaryEntropy (1 / (r i : ℝ)) ≤ η / (b : ℝ)) ∧
      M = 2 + 2 * ∑ i ∈ Finset.Icc 1 b, e i ∧ 0 < M := by
  let δ := η / (b : ℝ)
  have hδ : 0 < δ := sparse_tolerance_pos hb hη
  exact ⟨sparseR δ hδ, sparseE δ hδ, sparseD δ hδ, sparseF δ hδ,
    sparseM δ hδ b, sparseNumerics δ hδ b, sparseR_ge_two δ hδ,
    sparseF_zero δ hδ, sparseF_one δ hδ, sparseF_eq_sum_Ico δ hδ,
    fun i hi _ => sparse_entropy_bound δ hδ i hi, sparseM_eq δ hδ b,
    sparseM_pos δ hδ b⟩

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

open scoped BigOperators

def trueCount {N : ℕ} (z : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun i => z i = true).card

theorem trueCount_le {N : ℕ} (z : Fin N → Bool) : trueCount z ≤ N := by
  simpa only [trueCount, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin N)))
      (p := fun i => z i = true))

theorem trueCount_cast {N : ℕ} (z : Fin N → Bool) :
    (trueCount z : ℝ) = ∑ i, if z i = true then (1 : ℝ) else 0 := by
  exact Finset.natCast_card_filter (fun i => z i = true) Finset.univ

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


open scoped BigOperators

namespace DepthThreeLowerBound

inductive SparseDecisionTree (Label : Type uDepth1) where
  | leaf : SparseDecisionTree Label
  | node : Label → SparseDecisionTree Label → SparseDecisionTree Label →
      SparseDecisionTree Label

namespace SparseDecisionTree

variable {Label : Type uDepth2}

def Leaf : SparseDecisionTree Label → Type
  | .leaf => Unit
  | .node _ l r => Leaf l ⊕ Leaf r

@[instance_reducible]
private def leafFintype : (t : SparseDecisionTree Label) → Fintype t.Leaf
  | .leaf => inferInstanceAs (Fintype Unit)
  | .node _ l r => by
      change Fintype (Leaf l ⊕ Leaf r)
      letI := leafFintype l
      letI := leafFintype r
      infer_instance

instance (t : SparseDecisionTree Label) : Fintype t.Leaf := leafFintype t

def stream [DecidableEq Label] : (t : SparseDecisionTree Label) →
    t.Leaf → Label → List Bool
  | .leaf, _, _ => []
  | .node a l _, .inl p, i =>
      if i = a then false :: stream l p i else stream l p i
  | .node a _ r, .inr p, i =>
      if i = a then true :: stream r p i else stream r p i

def streamBit [DecidableEq Label] (t : SparseDecisionTree Label)
    (p : t.Leaf) (i : Label) (k : ℕ) : Bool :=
  (t.stream p i).getD k false

def padded [DecidableEq Label] (t : SparseDecisionTree Label) (N : Label → ℕ)
    (p : t.Leaf) (i : Label) (k : Fin (N i)) : Bool :=
  t.streamBit p i k

theorem streamBit_injective [DecidableEq Label] (t : SparseDecisionTree Label) :
    Function.Injective t.streamBit := by
  induction t with
  | leaf =>
      intro p q _
      exact Subsingleton.elim (α := Unit) p q
  | node a l r ihl ihr =>
      intro p q h
      cases p with
      | inl p =>
          cases q with
          | inl q =>
              have hpq : p = q := ihl (by
                funext i k
                by_cases hi : i = a
                · subst i
                  simpa only [streamBit, stream, ite_eq_left rfl, ite_true, List.getD_cons_succ] using
                    congrFun (congrFun h a) (k + 1)
                · simpa only [streamBit, stream, ite_eq_right hi] using
                    congrFun (congrFun h i) k)
              exact congrArg Sum.inl hpq
          | inr q =>
              have hfalse : False := by
                simpa only [streamBit, stream, ite_eq_left rfl, ite_true, List.getD_cons_zero,
                  Bool.false_eq_true] using congrFun (congrFun h a) 0
              exact hfalse.elim
      | inr p =>
          cases q with
          | inl q =>
              have hfalse : False := by
                simpa only [streamBit, stream, ite_eq_left rfl, ite_true, List.getD_cons_zero,
                  Bool.true_eq_false] using congrFun (congrFun h a) 0
              exact hfalse.elim
          | inr q =>
              have hpq : p = q := ihr (by
                funext i k
                by_cases hi : i = a
                · subst i
                  simpa only [streamBit, stream, ite_eq_left rfl, ite_true, List.getD_cons_succ] using
                    congrFun (congrFun h a) (k + 1)
                · simpa only [streamBit, stream, ite_eq_right hi] using
                    congrFun (congrFun h i) k)
              exact congrArg Sum.inr hpq

theorem padded_injective [DecidableEq Label] (t : SparseDecisionTree Label)
    (N : Label → ℕ) (hN : ∀ (p : t.Leaf) i, (t.stream p i).length ≤ N i) :
    Function.Injective (t.padded N) := by
  intro p q h
  apply t.streamBit_injective
  funext i k
  by_cases hk : k < N i
  · exact congrFun (congrFun h i) ⟨k, hk⟩
  · have hNk : N i ≤ k := Nat.le_of_not_gt hk
    change (t.stream p i).getD k false = (t.stream q i).getD k false
    rw [List.getD_eq_default _ _ ((hN p i).trans hNk),
      List.getD_eq_default _ _ ((hN q i).trans hNk)]

private theorem sum_getD_false (N : ℕ) (xs : List Bool) (h : xs.length ≤ N) :
    (∑ j : Fin N, if xs.getD j.val false = true then (1 : ℕ) else 0) =
      xs.count true := by
  induction N generalizing xs with
  | zero => cases xs <;> simp_all
  | succ N ih =>
      cases xs with
      | nil => simp
      | cons b xs =>
          have hx : xs.length ≤ N := Nat.le_of_succ_le_succ h
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]
          rw [ih xs hx]
          cases b <;> simp [Nat.add_comm]

theorem trueCount_getD (xs : List Bool) (N : ℕ) (h : xs.length ≤ N) :
    trueCount (fun j : Fin N => xs.getD j.val false) = xs.count true := by
  unfold trueCount
  exact (Finset.natCast_card_filter (R := ℕ)
    (fun j : Fin N => xs.getD j.val false = true) Finset.univ).trans
      (sum_getD_false N xs h)

theorem padded_trueCount [DecidableEq Label] (t : SparseDecisionTree Label)
    (N : Label → ℕ) (p : t.Leaf) (i : Label)
    (h : (t.stream p i).length ≤ N i) :
    trueCount (t.padded N p i) = (t.stream p i).count true :=
  trueCount_getD (t.stream p i) (N i) h

theorem card_le_prod_admitted [DecidableEq Label] [Fintype Label]
    (t : SparseDecisionTree Label) (N : Label → ℕ)
    (hN : ∀ (p : t.Leaf) i, (t.stream p i).length ≤ N i)
    (admitted : (i : Label) → Finset (Fin (N i) → Bool))
    (hmem : ∀ (p : t.Leaf) i, t.padded N p i ∈ admitted i) :
    Fintype.card t.Leaf ≤ ∏ i, (admitted i).card := by
  classical
  let enc : t.Leaf → ((i : Label) → {w // w ∈ admitted i}) :=
    fun p i => ⟨t.padded N p i, hmem p i⟩
  have henc : Function.Injective enc := by
    intro p q h
    apply t.padded_injective N hN
    funext i
    exact congrArg Subtype.val (congrFun h i)
  simpa only [Fintype.card_pi, Fintype.card_coe] using
    (Fintype.card_le_of_injective enc henc)

theorem card_le_prod_lowWeight [DecidableEq Label] [Fintype Label]
    (t : SparseDecisionTree Label) (N r : Label → ℕ)
    (hN : ∀ (p : t.Leaf) i, (t.stream p i).length ≤ N i)
    (hones : ∀ (p : t.Leaf) i, r i * (t.stream p i).count true ≤ N i) :
    Fintype.card t.Leaf ≤
      ∏ i, (Finset.univ.filter (fun w : Fin (N i) → Bool =>
        r i * trueCount w ≤ N i)).card := by
  classical
  apply t.card_le_prod_admitted N hN
  intro p i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [t.padded_trueCount N p i (hN p i)]
  exact hones p i

end SparseDecisionTree

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace DepthThreeLowerBound

open scoped BigOperators

variable {V : Type uDepth1} [DecidableEq V]

def SparseEligible (r : ℕ → ℕ) (s : SparseState V) : Prop :=
  ∃ i, Nonempty (SignedSunflower s i (r i))

def SparseTerminal (r : ℕ → ℕ) (s : SparseState V) : Prop :=
  ∀ i, ¬ Nonempty (SignedSunflower s i (r i))

theorem sparseTerminal_of_not_eligible {r : ℕ → ℕ} {s : SparseState V}
    (h : ¬ SparseEligible r s) : SparseTerminal r s :=
  fun i hi => h ⟨i, hi⟩

structure SparseSelection (r : ℕ → ℕ) (s : SparseState V) where
  size : ℕ
  selected : SignedSunflower s size (r size)
  minimal : ∀ j, 2 ≤ j → j < size →
    ¬ Nonempty (SignedSunflower s j (r j))

def sparseSelect (r : ℕ → ℕ) (s : SparseState V) (h : SparseEligible r s) :
    SparseSelection r s := by
  classical
  exact {
    size := Nat.find h
    selected := Classical.choice (Nat.find_spec h)
    minimal := fun _ _ hj => Nat.find_min h hj }

namespace SparseSelection

variable {r : ℕ → ℕ} {s : SparseState V} {b : ℕ}

def branch (c : SparseSelection r s) (choice : Bool) : SparseState V :=
  c.selected.branch choice

def step (c : SparseSelection r s) (choice : Bool) :
    SparseStep r s (c.branch choice) where
  size := c.size
  selected := c.selected
  minimal := c.minimal
  choice := choice
  target := rfl

def label (c : SparseSelection r s) (hs : s.Valid b) : Fin (b + 1) :=
  ⟨c.size, Nat.lt_succ_of_le (c.selected.size_le hs)⟩

theorem branch_valid (c : SparseSelection r s) (hs : s.Valid b) (choice : Bool) :
    (c.branch choice).Valid b := c.selected.branch_valid choice hs

theorem branch_eval_imp (c : SparseSelection r s) (choice : Bool) (x : Cube V)
    (h : (c.branch choice).eval x = true) : s.eval x = true := by
  cases choice
  · change c.selected.coreBranch.eval x = true at h
    rw [c.selected.eval_coreBranch, Bool.and_eq_true] at h
    exact h.1
  · change c.selected.petalBranch.eval x = true at h
    rw [c.selected.eval_petalBranch, Bool.and_eq_true] at h
    exact h.1

end SparseSelection

namespace SparsePath

variable {r : ℕ → ℕ} {start middle finish : SparseState V}

def prepend (step : SparseStep r start middle) :
    {finish : SparseState V} → SparsePath r middle finish → SparsePath r start finish
  | _, .nil => .snoc .nil step
  | _, .snoc path next => .snoc (path.prepend step) next

theorem length_prepend (step : SparseStep r start middle)
    (path : SparsePath r middle finish) :
    (path.prepend step).length = 1 + path.length := by
  induction path with
  | nil => rfl
  | snoc path next ih => simp only [prepend, length, ih, Nat.add_assoc]

theorem processed_prepend (step : SparseStep r start middle)
    (path : SparsePath r middle finish) (i : ℕ) :
    (path.prepend step).processed i =
      (if step.size = i then 1 else 0) + path.processed i := by
  induction path with
  | nil => simp only [prepend, processed, Nat.zero_add, Nat.add_zero]
  | snoc path next ih => simp only [prepend, processed, ih, Nat.add_assoc]

theorem petalSteps_prepend (step : SparseStep r start middle)
    (path : SparsePath r middle finish) (i : ℕ) :
    (path.prepend step).petalSteps i =
      (if step.size = i ∧ step.choice = true then 1 else 0) + path.petalSteps i := by
  induction path with
  | nil => simp only [prepend, petalSteps, Nat.zero_add, Nat.add_zero]
  | snoc path next ih => simp only [prepend, petalSteps, ih, Nat.add_assoc]

end SparsePath

structure SparseTreeResult (r : ℕ → ℕ) (b : ℕ) (start : SparseState V) (fuel : ℕ) where
  tree : SparseDecisionTree (Fin (b + 1))
  finish : tree.Leaf → SparseState V
  path : (p : tree.Leaf) → SparsePath r start (finish p)
  terminal_or_exhausted : ∀ p, SparseTerminal r (finish p) ∨ (path p).length = fuel
  stream_length : ∀ p i, (tree.stream p i).length = (path p).processed i.val
  stream_ones : ∀ p i, (tree.stream p i).count true = (path p).petalSteps i.val
  leaf_eval_imp : ∀ p x, (finish p).eval x = true → start.eval x = true
  indicator_eq_sum : ∀ x, indicator (start.eval x) = ∑ p, indicator ((finish p).eval x)
  disjoint : ∀ p q, p ≠ q → ∀ x,
    ¬ ((finish p).eval x = true ∧ (finish q).eval x = true)

namespace SparseTreeResult

variable {r : ℕ → ℕ} {b fuel : ℕ} {s : SparseState V}

private def stop (r : ℕ → ℕ) (b : ℕ) (s : SparseState V) (fuel : ℕ)
    (h : SparseTerminal r s ∨ fuel = 0) : SparseTreeResult r b s fuel where
  tree := .leaf
  finish := fun _ => s
  path := fun _ => .nil
  terminal_or_exhausted := by
    intro _
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by simp only [SparsePath.length, h])
  stream_length := by intros; rfl
  stream_ones := by intros; rfl
  leaf_eval_imp := by intros _ _ h; exact h
  indicator_eq_sum := by
    intro x
    change indicator (s.eval x) = ∑ _ : Unit, indicator (s.eval x)
    exact (Fintype.sum_unique (fun _ : Unit => indicator (s.eval x))).symm
  disjoint := by intro p q hpq; exact (hpq (Subsingleton.elim (α := Unit) p q)).elim

private def join (c : SparseSelection r s) (hs : s.Valid b)
    (left : SparseTreeResult r b (c.branch false) fuel)
    (right : SparseTreeResult r b (c.branch true) fuel) :
    SparseTreeResult r b s (fuel + 1) where
  tree := .node (c.label hs) left.tree right.tree
  finish := Sum.elim left.finish right.finish
  path := fun p => match p with
    | .inl p => (left.path p).prepend (c.step false)
    | .inr p => (right.path p).prepend (c.step true)
  terminal_or_exhausted := by
    intro p
    cases p with
    | inl p =>
        rcases left.terminal_or_exhausted p with h | h
        · exact Or.inl h
        · exact Or.inr (by
            change ((left.path p).prepend (c.step false)).length = fuel + 1
            rw [SparsePath.length_prepend, h, Nat.add_comm])
    | inr p =>
        rcases right.terminal_or_exhausted p with h | h
        · exact Or.inl h
        · exact Or.inr (by
            change ((right.path p).prepend (c.step true)).length = fuel + 1
            rw [SparsePath.length_prepend, h, Nat.add_comm])
  stream_length := by
    intro p i
    cases p with
    | inl p =>
        by_cases hi : i = c.label hs
        · subst i
          simp [SparseDecisionTree.stream, SparsePath.processed_prepend,
            SparseSelection.step, SparseSelection.label, left.stream_length, Nat.add_comm]
        · have hiv : c.size ≠ i.val := by
            intro he
            exact hi (Fin.ext he.symm)
          simp [SparseDecisionTree.stream, hi, SparsePath.processed_prepend,
            SparseSelection.step, hiv, left.stream_length]
    | inr p =>
        by_cases hi : i = c.label hs
        · subst i
          simp [SparseDecisionTree.stream, SparsePath.processed_prepend,
            SparseSelection.step, SparseSelection.label, right.stream_length, Nat.add_comm]
        · have hiv : c.size ≠ i.val := by
            intro he
            exact hi (Fin.ext he.symm)
          simp [SparseDecisionTree.stream, hi, SparsePath.processed_prepend,
            SparseSelection.step, hiv, right.stream_length]
  stream_ones := by
    intro p i
    cases p with
    | inl p =>
        by_cases hi : i = c.label hs
        · subst i
          simp [SparseDecisionTree.stream, SparsePath.petalSteps_prepend,
            SparseSelection.step, SparseSelection.label, left.stream_ones]
        · have hiv : c.size ≠ i.val := by
            intro he
            exact hi (Fin.ext he.symm)
          simp [SparseDecisionTree.stream, hi, SparsePath.petalSteps_prepend,
            SparseSelection.step, hiv, left.stream_ones]
    | inr p =>
        by_cases hi : i = c.label hs
        · subst i
          simp [SparseDecisionTree.stream, SparsePath.petalSteps_prepend,
            SparseSelection.step, SparseSelection.label, right.stream_ones, Nat.add_comm]
        · have hiv : c.size ≠ i.val := by
            intro he
            exact hi (Fin.ext he.symm)
          simp [SparseDecisionTree.stream, hi, SparsePath.petalSteps_prepend,
            SparseSelection.step, hiv, right.stream_ones]
  leaf_eval_imp := by
    intro p x hp
    cases p with
    | inl p => exact c.branch_eval_imp false x (left.leaf_eval_imp p x hp)
    | inr p => exact c.branch_eval_imp true x (right.leaf_eval_imp p x hp)
  indicator_eq_sum := by
    intro x
    change indicator (s.eval x) =
      ∑ p : left.tree.Leaf ⊕ right.tree.Leaf,
        indicator ((Sum.elim left.finish right.finish p).eval x)
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← left.indicator_eq_sum x, ← right.indicator_eq_sum x]
    exact c.selected.branch_indicator x
  disjoint := by
    intro p q hpq x hpqx
    cases p with
    | inl p =>
        cases q with
        | inl q =>
            exact left.disjoint p q (fun h => hpq (congrArg Sum.inl h)) x hpqx
        | inr q =>
            exact c.selected.branch_disjoint x
              ⟨left.leaf_eval_imp p x hpqx.1, right.leaf_eval_imp q x hpqx.2⟩
    | inr p =>
        cases q with
        | inl q =>
            exact c.selected.branch_disjoint x
              ⟨left.leaf_eval_imp q x hpqx.2, right.leaf_eval_imp p x hpqx.1⟩
        | inr q =>
            exact right.disjoint p q (fun h => hpq (congrArg Sum.inr h)) x hpqx

def build (r : ℕ → ℕ) (b : ℕ) :
    (fuel : ℕ) → (s : SparseState V) → s.Valid b → SparseTreeResult r b s fuel
  | 0, s, _ => stop r b s 0 (Or.inr rfl)
  | fuel + 1, s, hs => by
      classical
      exact if h : SparseEligible r s then
        let c := sparseSelect r s h
        join c hs
          (build r b fuel (c.branch false) (c.branch_valid hs false))
          (build r b fuel (c.branch true) (c.branch_valid hs true))
      else stop r b s (fuel + 1) (Or.inl (sparseTerminal_of_not_eligible h))

end SparseTreeResult

def sparseTreeFuel [Fintype V] (D : ℕ → ℕ) (b : ℕ) : ℕ :=
  (∑ u ∈ Finset.Ico 1 b, D u) * Fintype.card V

def sparseTree [Fintype V] (r D : ℕ → ℕ) (b : ℕ) (s : SparseState V)
    (hs : s.Valid b) : SparseTreeResult r b s (sparseTreeFuel (V := V) D b) :=
  SparseTreeResult.build r b (sparseTreeFuel (V := V) D b) s hs

theorem sparseTree_terminal [Fintype V] {r e D : ℕ → ℕ} {b : ℕ}
    (hnum : SparseNumerics r e D b) (s : SparseState V) (hs : s.Valid b)
    (hadded : s.added = ∅) (p : (sparseTree r D b s hs).tree.Leaf) :
    SparseTerminal r ((sparseTree r D b s hs).finish p) := by
  classical
  let T := sparseTree r D b s hs
  rcases T.terminal_or_exhausted p with ht | hlen
  · exact ht
  · intro i hi
    let c := sparseSelect r (T.finish p) ⟨i, hi⟩
    have hbound := ((T.path p).snoc (c.step false)).length_budget hnum hs hadded
    change (T.path p).length + 1 ≤ sparseTreeFuel (V := V) D b at hbound
    rw [hlen] at hbound
    exact Nat.not_succ_le_self _ hbound

theorem sparseTree_stream_length [Fintype V] {r e D : ℕ → ℕ} {b : ℕ}
    (hnum : SparseNumerics r e D b) (s : SparseState V) (hs : s.Valid b)
    (hadded : s.added = ∅) (p : (sparseTree r D b s hs).tree.Leaf) (i : Fin (b + 1)) :
    ((sparseTree r D b s hs).tree.stream p i).length ≤
      (∑ u ∈ Finset.Ico 1 i.val, D u) * Fintype.card V := by
  rw [(sparseTree r D b s hs).stream_length]
  exact ((sparseTree r D b s hs).path p).processed_budget hnum hs hadded i.val
    (Nat.le_of_lt_succ i.isLt)

theorem sparseTree_stream_ones [Fintype V] {r e D : ℕ → ℕ} {b : ℕ}
    (hnum : SparseNumerics r e D b) (s : SparseState V) (hs : s.Valid b)
    (hadded : s.added = ∅) (p : (sparseTree r D b s hs).tree.Leaf) (i : Fin (b + 1)) :
    r i.val * ((sparseTree r D b s hs).tree.stream p i).count true ≤
      (∑ u ∈ Finset.Ico 1 i.val, D u) * Fintype.card V := by
  rw [(sparseTree r D b s hs).stream_ones]
  exact ((sparseTree r D b s hs).path p).petalSteps_budget hnum hs hadded i.val
    (Nat.le_of_lt_succ i.isLt)

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace DepthThreeLowerBound

open scoped BigOperators

theorem finite_card_le_of_uniform_weight_lower_bound {α : Type uDepth1} [Fintype α]
    (A : Finset α) (w : α → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a ≤ 1)
    (hlower : ∀ a ∈ A, δ ≤ w a) : (A.card : ℝ) ≤ 1 / δ := by
  classical
  have hcard : (A.card : ℝ) * δ ≤ 1 := by
    calc
      (A.card : ℝ) * δ = ∑ _a ∈ A, δ := by simp
      _ ≤ ∑ a ∈ A, w a := Finset.sum_le_sum hlower
      _ ≤ ∑ a, w a := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun a _ _ => hw a)
      _ ≤ 1 := hsum
  exact (le_div_iff₀ hδ).2 hcard

def bernoulliStringWeight {N : ℕ} (x : ℝ) (z : Fin N → Bool) : ℝ :=
  ∏ i, if z i = true then x else 1 - x

theorem bernoulliStringWeight_pos {N : ℕ} {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) (z : Fin N → Bool) : 0 < bernoulliStringWeight x z := by
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact hx
  · exact sub_pos.mpr hx1

theorem sum_bernoulliStringWeight (N : ℕ) (x : ℝ) :
    ∑ z : Fin N → Bool, bernoulliStringWeight x z = 1 := by
  have hbit : (∑ b : Bool, if b = true then x else 1 - x) = 1 := by
    simp [Fintype.univ_bool]
  calc
    (∑ z : Fin N → Bool, bernoulliStringWeight x z) =
        ∏ _i : Fin N, ∑ b : Bool, if b = true then x else 1 - x :=
      (Fintype.prod_sum (fun (_i : Fin N) (b : Bool) =>
        if b = true then x else 1 - x)).symm
    _ = 1 := by simp only [hbit, Finset.prod_const_one]

theorem log_bernoulliStringWeight {N : ℕ} {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) (z : Fin N → Bool) :
    Real.log (bernoulliStringWeight x z) =
      (N : ℝ) * Real.log (1 - x) +
        (trueCount z : ℝ) * (Real.log x - Real.log (1 - x)) := by
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      (if z i = true then x else 1 - x) ≠ 0 := by
    intro i _
    split_ifs
    · exact ne_of_gt hx
    · exact ne_of_gt (sub_pos.mpr hx1)
  rw [bernoulliStringWeight, Real.log_prod hne]
  calc
    (∑ i : Fin N, Real.log (if z i = true then x else 1 - x)) =
        ∑ i : Fin N, (Real.log (1 - x) +
          (if z i = true then (1 : ℝ) else 0) *
            (Real.log x - Real.log (1 - x))) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    _ = (N : ℝ) * Real.log (1 - x) +
        (trueCount z : ℝ) * (Real.log x - Real.log (1 - x)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← trueCount_cast]
      simp

theorem bernoulliStringWeight_lower_bound {N : ℕ} {x : ℝ}
    (hx : 0 < x) (hxhalf : x ≤ 1 / 2) (z : Fin N → Bool)
    (hz : (trueCount z : ℝ) ≤ (N : ℝ) * x) :
    Real.exp (-((N : ℝ) * binaryEntropy x * Real.log 2)) ≤
      bernoulliStringWeight x z := by
  have hx1 : x < 1 := by linarith
  have hc : Real.log x - Real.log (1 - x) ≤ 0 := by
    apply sub_nonpos.mpr
    apply Real.log_le_log hx
    linarith
  have hmul := mul_le_mul_of_nonpos_right hz hc
  have hlog : -((N : ℝ) * binaryEntropy x * Real.log 2) ≤
      Real.log (bernoulliStringWeight x z) := by
    rw [log_bernoulliStringWeight hx hx1]
    calc
      -((N : ℝ) * binaryEntropy x * Real.log 2) =
          (N : ℝ) * Real.log (1 - x) +
            ((N : ℝ) * x) * (Real.log x - Real.log (1 - x)) := by
        rw [mul_assoc, binaryEntropy_mul_log_two]
        ring
      _ ≤ (N : ℝ) * Real.log (1 - x) +
          (trueCount z : ℝ) * (Real.log x - Real.log (1 - x)) :=
        add_le_add_right hmul _
  calc
    Real.exp (-((N : ℝ) * binaryEntropy x * Real.log 2)) ≤
        Real.exp (Real.log (bernoulliStringWeight x z)) :=
      Real.exp_le_exp.mpr hlog
    _ = bernoulliStringWeight x z :=
      Real.exp_log (bernoulliStringWeight_pos hx hx1 z)

def sparseBinaryStrings (N : ℕ) (x : ℝ) : Finset (Fin N → Bool) := by
  classical
  exact Finset.univ.filter fun z => (trueCount z : ℝ) ≤ (N : ℝ) * x

theorem card_sparse_binary_strings_le (N : ℕ) {x : ℝ}
    (hx : 0 < x) (hxhalf : x ≤ 1 / 2) :
    ((sparseBinaryStrings N x).card : ℝ) ≤
      (2 : ℝ) ^ ((N : ℝ) * binaryEntropy x) := by
  classical
  have hx1 : x < 1 := by linarith
  have h := finite_card_le_of_uniform_weight_lower_bound
    (sparseBinaryStrings N x) (bernoulliStringWeight x)
    (Real.exp_pos (-((N : ℝ) * binaryEntropy x * Real.log 2)))
    (fun z => (bernoulliStringWeight_pos hx hx1 z).le)
    (sum_bernoulliStringWeight N x).le
    (fun z hz => bernoulliStringWeight_lower_bound hx hxhalf z
      (Finset.mem_filter.mp hz).2)
  calc
    ((sparseBinaryStrings N x).card : ℝ) ≤
        1 / Real.exp (-((N : ℝ) * binaryEntropy x * Real.log 2)) := h
    _ = Real.exp ((N : ℝ) * binaryEntropy x * Real.log 2) := by
      rw [one_div, Real.exp_neg, inv_inv]
    _ = (2 : ℝ) ^ ((N : ℝ) * binaryEntropy x) := by
      rw [Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num)]
      congr 1
      ring

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

open scoped BigOperators

namespace SparseDecisionTree

variable {Label : Type uDepth1} [DecidableEq Label] [Fintype Label]

theorem card_le_entropy_sum (t : SparseDecisionTree Label) (N r : Label → ℕ)
    (hr : ∀ i, 2 ≤ r i)
    (hN : ∀ (p : t.Leaf) i, (t.stream p i).length ≤ N i)
    (hones : ∀ (p : t.Leaf) i, r i * (t.stream p i).count true ≤ N i) :
    (Fintype.card t.Leaf : ℝ) ≤
      (2 : ℝ) ^ (∑ i, (N i : ℝ) * binaryEntropy (1 / (r i : ℝ))) := by
  classical
  let admitted (i : Label) := sparseBinaryStrings (N i) (1 / (r i : ℝ))
  have hrpos (i : Label) : (0 : ℝ) < r i := by
    have htwo : (2 : ℝ) ≤ r i := by exact_mod_cast hr i
    linarith
  have hhalf (i : Label) : (1 : ℝ) / r i ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (hrpos i) (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [one_mul] using (show (2 : ℝ) ≤ r i by exact_mod_cast hr i)
  have hmem : ∀ (p : t.Leaf) i, t.padded N p i ∈ admitted i := by
    intro p i
    have hcast : (r i : ℝ) * ((t.stream p i).count true : ℝ) ≤ N i := by
      exact_mod_cast hones p i
    have hbound : ((t.stream p i).count true : ℝ) ≤
        (N i : ℝ) * (1 / (r i : ℝ)) := by
      rw [mul_one_div]
      apply (le_div_iff₀ (hrpos i)).mpr
      simpa only [mul_comm] using hcast
    simp only [admitted, sparseBinaryStrings, Finset.mem_filter, Finset.mem_univ,
      true_and, t.padded_trueCount N p i (hN p i)]
    exact hbound
  have hnat := t.card_le_prod_admitted N hN admitted hmem
  have hreal : (Fintype.card t.Leaf : ℝ) ≤ ∏ i, ((admitted i).card : ℝ) := by
    exact_mod_cast hnat
  calc
    (Fintype.card t.Leaf : ℝ) ≤ ∏ i, ((admitted i).card : ℝ) := hreal
    _ ≤ ∏ i, (2 : ℝ) ^ ((N i : ℝ) * binaryEntropy (1 / (r i : ℝ))) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Nat.cast_nonneg _
      · intro i _
        exact card_sparse_binary_strings_le (N i) (one_div_pos.mpr (hrpos i)) (hhalf i)
    _ = _ := (Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)
      (fun i => (N i : ℝ) * binaryEntropy (1 / (r i : ℝ))) Finset.univ).symm

theorem card_le_of_entropy_budget (t : SparseDecisionTree Label) (N r : Label → ℕ)
    (hr : ∀ i, 2 ≤ r i)
    (hN : ∀ (p : t.Leaf) i, (t.stream p i).length ≤ N i)
    (hones : ∀ (p : t.Leaf) i, r i * (t.stream p i).count true ≤ N i)
    {B : ℝ} (hbudget : (∑ i, (N i : ℝ) * binaryEntropy (1 / (r i : ℝ))) ≤ B) :
    (Fintype.card t.Leaf : ℝ) ≤ (2 : ℝ) ^ B :=
  (t.card_le_entropy_sum N r hr hN hones).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hbudget)

end SparseDecisionTree

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

variable {α : Type uDepth1}

noncomputable def sparseMinimalFamily (A : Finset (Finset α)) : Finset (Finset α) := by
  classical
  exact A.filter (fun C => ∀ D ∈ A, D ⊆ C → C ⊆ D)

theorem mem_sparseMinimalFamily {A : Finset (Finset α)} {C : Finset α} :
    C ∈ sparseMinimalFamily A ↔ C ∈ A ∧ ∀ D ∈ A, D ⊆ C → C ⊆ D := by
  classical
  simp only [sparseMinimalFamily, Finset.mem_filter]

theorem sparseMinimalFamily_subset (A : Finset (Finset α)) :
    sparseMinimalFamily A ⊆ A := by
  intro C hC
  exact (mem_sparseMinimalFamily.mp hC).1

theorem sparseMinimalFamily_antichain (A : Finset (Finset α)) :
    ∀ C ∈ sparseMinimalFamily A, ∀ D ∈ sparseMinimalFamily A, C ⊆ D → C = D := by
  intro C hC D hD hCD
  apply Finset.Subset.antisymm hCD
  exact (mem_sparseMinimalFamily.mp hD).2 C
    (sparseMinimalFamily_subset A hC) hCD

theorem exists_mem_sparseMinimalFamily_subset {A : Finset (Finset α)}
    {C : Finset α} (hC : C ∈ A) :
    ∃ D ∈ sparseMinimalFamily A, D ⊆ C := by
  classical
  let candidates := A.filter (fun D => D ⊆ C)
  have hne : candidates.Nonempty := by
    refine ⟨C, ?_⟩
    exact Finset.mem_filter.mpr ⟨hC, Finset.Subset.refl _⟩
  obtain ⟨D, hD, hmin⟩ := candidates.exists_min_image Finset.card hne
  have hDA : D ∈ A := (Finset.mem_filter.mp hD).1
  have hDC : D ⊆ C := (Finset.mem_filter.mp hD).2
  refine ⟨D, mem_sparseMinimalFamily.mpr ⟨hDA, ?_⟩, hDC⟩
  intro E hEA hED
  have hEc : E ∈ candidates :=
    Finset.mem_filter.mpr ⟨hEA, Finset.Subset.trans hED hDC⟩
  have hEq : E = D := Finset.eq_of_subset_of_card_le hED (hmin E hEc)
  exact Finset.subset_of_eq hEq.symm

theorem forall_sparseMinimalFamily_iff (A : Finset (Finset α))
    (P : Finset α → Prop)
    (hP : ∀ {C D}, C ⊆ D → P C → P D) :
    (∀ C ∈ sparseMinimalFamily A, P C) ↔ ∀ C ∈ A, P C := by
  constructor
  · intro h C hC
    obtain ⟨D, hD, hDC⟩ := exists_mem_sparseMinimalFamily_subset hC
    exact hP hDC (h D hD)
  · intro h C hC
    exact h C (sparseMinimalFamily_subset A hC)

theorem sparseMinimalFamily_empty :
    sparseMinimalFamily (∅ : Finset (Finset α)) = ∅ := by
  classical
  simp [sparseMinimalFamily]

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

variable {V : Type uDepth1}

theorem Clause.eval_of_not_normalized {C : Clause V} (hC : ¬ C.Normalized)
    (x : Cube V) : C.eval x = true := by
  classical
  by_contra hx
  apply hC
  intro v hf ht
  cases hv : x v with
  | false => exact hx (Clause.eval_eq_true C x |>.mpr ⟨(v, false), hf, hv⟩)
  | true => exact hx (Clause.eval_eq_true C x |>.mpr ⟨(v, true), ht, hv⟩)

theorem CNF.eval_of_empty_mem {H : CNF V} (hH : ∅ ∈ H) (x : Cube V) :
    H.eval x = false := by
  cases hx : H.eval x with
  | false => rfl
  | true =>
    have he := (CNF.eval_eq_true H x).mp hx ∅ hH
    simp only [Clause.eval_empty, Bool.false_eq_true] at he

noncomputable def sparseNormalizedFamily (H : CNF V) : Finset (Clause V) := by
  classical
  exact H.toFinset.filter Clause.Normalized

theorem mem_sparseNormalizedFamily {H : CNF V} {C : Clause V} :
    C ∈ sparseNormalizedFamily H ↔ C ∈ H ∧ C.Normalized := by
  classical
  simp [sparseNormalizedFamily]

theorem sparseNormalizedFamily_eval (H : CNF V) (x : Cube V) :
    CNF.eval (sparseNormalizedFamily H).toList x = H.eval x := by
  classical
  apply bool_eq_of_true_iff
  simp only [CNF.eval_eq_true, Finset.mem_toList]
  constructor
  · intro h C hC
    by_cases hn : C.Normalized
    · exact h C (mem_sparseNormalizedFamily.mpr ⟨hC, hn⟩)
    · exact Clause.eval_of_not_normalized hn x
  · intro h C hC
    exact h C (mem_sparseNormalizedFamily.mp hC).1

theorem sparseMinimalFamily_eval (A : Finset (Clause V)) (x : Cube V) :
    CNF.eval (sparseMinimalFamily A).toList x = CNF.eval A.toList x := by
  classical
  apply bool_eq_of_true_iff
  simp only [CNF.eval_eq_true, Finset.mem_toList]
  exact forall_sparseMinimalFamily_iff A (fun C => Clause.eval C x = true)
    (fun hCD hx => Clause.eval_mono hCD hx)

structure SparseNormalization (H : CNF V) (b : ℕ) where
  active : Finset (Clause V)
  normalized : ∀ C ∈ active, C.Normalized
  nonempty : ∀ C ∈ active, C.Nonempty
  antichain : ∀ C ∈ active, ∀ D ∈ active, C ⊆ D → C = D
  width_le : ∀ C ∈ active, C.width ≤ b
  eval_eq : ∀ x, CNF.eval active.toList x = H.eval x

noncomputable def sparseNormalizeOfNoEmpty (H : CNF V) {b : ℕ}
    (hwidth : H.WidthAtMost b) (hempty : (∅ : Clause V) ∉ H) :
    SparseNormalization H b where
  active := sparseMinimalFamily (sparseNormalizedFamily H)
  normalized := by
    intro C hC
    exact (mem_sparseNormalizedFamily.mp
      (sparseMinimalFamily_subset _ hC)).2
  nonempty := by
    intro C hC
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hzero
    apply hempty
    have hCH := (mem_sparseNormalizedFamily.mp
      (sparseMinimalFamily_subset _ hC)).1
    simpa only [hzero] using hCH
  antichain := sparseMinimalFamily_antichain _
  width_le := by
    intro C hC
    exact hwidth C ((mem_sparseNormalizedFamily.mp
      (sparseMinimalFamily_subset _ hC)).1)
  eval_eq := by
    intro x
    exact (sparseMinimalFamily_eval (sparseNormalizedFamily H) x).trans
      (sparseNormalizedFamily_eval H x)

theorem exists_sparseNormalization_or_false (H : CNF V) {b : ℕ}
    (hwidth : H.WidthAtMost b) :
    (∀ x, H.eval x = false) ∨ Nonempty (SparseNormalization H b) := by
  classical
  by_cases hempty : (∅ : Clause V) ∈ H
  · exact Or.inl (CNF.eval_of_empty_mem hempty)
  · exact Or.inr ⟨sparseNormalizeOfNoEmpty H hwidth hempty⟩

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace DepthThreeLowerBound

open scoped BigOperators

variable {V : Type uDepth1} [instDecidableEqV : DecidableEq V]

namespace SparseNormalization

def toState {H : CNF V} {b : ℕ} (N : SparseNormalization H b) : SparseState V where
  active := N.active
  side := ∅
  added := ∅

theorem toState_valid
    {V : Type uDepth1}
    [DecidableEq V]
    {H : CNF V} {b : ℕ} (N : SparseNormalization H b) :
    N.toState.Valid b where
  normalized := N.normalized
  nonempty := N.nonempty
  antichain := N.antichain
  width_le := N.width_le
  added_subset := Finset.empty_subset _

@[simp] theorem toState_added
    {V : Type uDepth1}
    [DecidableEq V]
    {H : CNF V} {b : ℕ} (N : SparseNormalization H b) :
    N.toState.added = ∅ := rfl

theorem toState_eval
    {V : Type uDepth1}
    [DecidableEq V]
    {H : CNF V} {b : ℕ} (N : SparseNormalization H b)
    (x : Cube V) : N.toState.eval x = H.eval x := by
  simpa only [SparseState.eval, SparseState.toCNF, toState, Finset.toList_empty,
    List.map_nil, List.append_nil] using N.eval_eq x

end SparseNormalization

namespace SparseState

theorem toCNF_normalized
    {V : Type uDepth1}
    [DecidableEq V]
    (s : SparseState V) {b : ℕ}
    (hs : s.Valid b) : s.toCNF.Normalized := by
  intro C hC
  rcases List.mem_append.mp hC with hactive | hside
  · exact hs.normalized C (Finset.mem_toList.mp hactive)
  · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hside
    intro v hf ht
    have heq := (Finset.mem_singleton.mp hf).trans (Finset.mem_singleton.mp ht).symm
    have hfalse : (false : Bool) = true := congrArg Prod.snd heq
    cases hfalse

theorem toCNF_widthAtMost
    {V : Type uDepth1}
    [DecidableEq V]
    (s : SparseState V) {b : ℕ}
    (hs : s.Valid b) (hb : 1 ≤ b) : s.toCNF.WidthAtMost b := by
  intro C hC
  rcases List.mem_append.mp hC with hactive | hside
  · exact hs.width_le C (Finset.mem_toList.mp hactive)
  · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hside
    simpa [Clause.width, Clause.scope] using hb

@[simp] theorem toCNF_length
    {V : Type uDepth1}
    [DecidableEq V]
    (s : SparseState V) :
    s.toCNF.length = s.active.card + s.side.card := by
  simp [toCNF]

theorem active_card_eq_sum_sizes
    {V : Type uDepth1}
    [DecidableEq V]
    (s : SparseState V) {b : ℕ} (hs : s.Valid b) :
    s.active.card = ∑ u ∈ Finset.Icc 1 b, (clausesOfSize s.active u).card := by
  apply Finset.card_eq_sum_card_fiberwise
  intro C hC
  apply Finset.mem_Icc.mpr
  constructor
  · exact (hs.nonempty C hC).card_pos
  · rw [(hs.normalized C hC).card_eq_width]
    exact hs.width_le C hC

theorem active_card_le_of_terminal [Fintype V] (s : SparseState V)
    {r e D : ℕ → ℕ} {b : ℕ} (hs : s.Valid b)
    (hnum : SparseNumerics r e D b)
    (hterminal : ∀ i, ¬ Nonempty (SignedSunflower s i (r i))) :
    s.active.card ≤ (2 * Fintype.card V) * ∑ u ∈ Finset.Icc 1 b, e u := by
  rw [s.active_card_eq_sum_sizes hs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  obtain ⟨hu1, hub⟩ := Finset.mem_Icc.mp hu
  apply clausesOfSize_card_le
  · intro C hC
    exact hs.nonempty C (mem_clausesOfSize.mp hC).1
  · intro l
    exact sparse_occurrence_le_of_no_sunflower hnum s u hu1 hub (hterminal u) l

theorem toCNF_length_le_of_terminal [Fintype V] (s : SparseState V)
    {r e D : ℕ → ℕ} {b : ℕ} (hs : s.Valid b)
    (hnum : SparseNumerics r e D b)
    (hterminal : ∀ i, ¬ Nonempty (SignedSunflower s i (r i))) :
    s.toCNF.length ≤
      (2 + 2 * ∑ u ∈ Finset.Icc 1 b, e u) * Fintype.card V := by
  have hside : s.side.card ≤ 2 * Fintype.card V := by
    have h := Finset.card_le_univ s.side
    simpa only [Literal, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using h
  rw [s.toCNF_length]
  calc
    s.active.card + s.side.card ≤
        (2 * Fintype.card V) * (∑ u ∈ Finset.Icc 1 b, e u) +
          2 * Fintype.card V :=
      Nat.add_le_add (s.active_card_le_of_terminal hs hnum hterminal) hside
    _ = _ := by ring

end SparseState

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace DepthThreeLowerBound

open scoped BigOperators


theorem sparse_entropy_sum_budget (b m : ℕ) (η : ℝ) (hb : 1 ≤ b) (hη : 0 < η)
    (r F : ℕ → ℕ) (hF0 : F 0 = 0) (hF1 : F 1 = 0)
    (hbound : ∀ i, 2 ≤ i → i ≤ b →
      (F i : ℝ) * binaryEntropy (1 / (r i : ℝ)) ≤ η / (b : ℝ)) :
    (∑ i : Fin (b + 1), ((F i.val * m : ℕ) : ℝ) *
      binaryEntropy (1 / (r i.val : ℝ))) ≤ η * (m : ℝ) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hδ : 0 ≤ η / (b : ℝ) := (div_pos hη hbpos).le
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, hF0, Nat.cast_zero, zero_mul, zero_add,
    Fin.val_succ]
  calc
    (∑ i : Fin b, ((F (i.val + 1) * m : ℕ) : ℝ) *
        binaryEntropy (1 / (r (i.val + 1) : ℝ))) ≤
        ∑ _i : Fin b, (m : ℝ) * (η / (b : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : (F (i.val + 1) : ℝ) *
          binaryEntropy (1 / (r (i.val + 1) : ℝ)) ≤ η / (b : ℝ) := by
        by_cases hi1 : i.val + 1 = 1
        · simpa only [hi1, hF1, Nat.cast_zero, zero_mul] using hδ
        · exact hbound _ (by omega) (Nat.succ_le_of_lt i.isLt)
      simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg m)
    _ = η * (m : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [ne_of_gt hbpos]

structure SparsePartition {V : Type u} [Fintype V]
    (H : CNF V) (b M : ℕ) (η : ℝ) where
  count : ℕ
  piece : Fin count → CNF V
  normalized : ∀ i, (piece i).Normalized
  width_le : ∀ i, (piece i).WidthAtMost b
  clauses_le : ∀ i, (piece i).length ≤ M * Fintype.card V
  disjoint : ∀ i j, i ≠ j → ∀ x,
    ¬ ((piece i).eval x = true ∧ (piece j).eval x = true)
  indicator_eq_sum : ∀ x, indicator (H.eval x) =
    ∑ i, indicator ((piece i).eval x)
  count_le : (count : ℝ) ≤ (2 : ℝ) ^ (η * (Fintype.card V : ℝ))

theorem exists_sparse_partition_constant (b : ℕ) (η : ℝ)
    (hb : 1 ≤ b) (hη : 0 < η) :
    ∃ M : ℕ, 0 < M ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (H : CNF V),
        H.WidthAtMost b → Nonempty (SparsePartition H b M η) := by
  classical
  obtain ⟨r, e, D, F, M, hnum, hr, hF0, hF1, hFsum, hentropy, hM, hMpos⟩ :=
    exists_sparse_numerics b η hb hη
  refine ⟨M, hMpos, ?_⟩
  intro V _ _ H hwidth
  rcases exists_sparseNormalization_or_false H hwidth with hfalse | hA
  · refine ⟨{
      count := 0
      piece := fun i => Fin.elim0 i
      normalized := fun i => Fin.elim0 i
      width_le := fun i => Fin.elim0 i
      clauses_le := fun i => Fin.elim0 i
      disjoint := fun i => Fin.elim0 i
      indicator_eq_sum := ?_
      count_le := ?_
    }⟩
    · intro x
      simp [hfalse x]
    · simpa only [Nat.cast_zero] using
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (η * (Fintype.card V : ℝ)))
  · let A : SparseNormalization H b := Classical.choice hA
    let s := A.toState
    have hs : s.Valid b := A.toState_valid
    have hadded : s.added = ∅ := rfl
    let T := sparseTree r D b s hs
    let eqv := Fintype.equivFin T.tree.Leaf
    have hcount : (Fintype.card T.tree.Leaf : ℝ) ≤
        (2 : ℝ) ^ (η * (Fintype.card V : ℝ)) := by
      apply T.tree.card_le_of_entropy_budget
        (fun i => F i.val * Fintype.card V) (fun i => r i.val)
      · intro i
        exact hr i.val
      · intro p i
        rw [hFsum]
        exact sparseTree_stream_length hnum s hs hadded p i
      · intro p i
        rw [hFsum]
        exact sparseTree_stream_ones hnum s hs hadded p i
      · exact sparse_entropy_sum_budget b (Fintype.card V) η hb hη r F hF0 hF1 hentropy
    refine ⟨{
      count := Fintype.card T.tree.Leaf
      piece := fun i => (T.finish (eqv.symm i)).toCNF
      normalized := ?_
      width_le := ?_
      clauses_le := ?_
      disjoint := ?_
      indicator_eq_sum := ?_
      count_le := hcount
    }⟩
    · intro i
      exact (T.finish (eqv.symm i)).toCNF_normalized ((T.path (eqv.symm i)).valid hs)
    · intro i
      exact (T.finish (eqv.symm i)).toCNF_widthAtMost
        ((T.path (eqv.symm i)).valid hs) hb
    · intro i
      rw [hM]
      exact (T.finish (eqv.symm i)).toCNF_length_le_of_terminal
        ((T.path (eqv.symm i)).valid hs) hnum
        (sparseTree_terminal hnum s hs hadded (eqv.symm i))
    · intro i j hij x
      exact T.disjoint (eqv.symm i) (eqv.symm j)
        (fun h => hij (eqv.symm.injective h)) x
    · intro x
      change indicator (H.eval x) =
        ∑ i, indicator ((T.finish (eqv.symm i)).eval x)
      calc
        indicator (H.eval x) = indicator (s.eval x) :=
          congrArg indicator (A.toState_eval x).symm
        _ = ∑ p, indicator ((T.finish p).eval x) := T.indicator_eq_sum x
        _ = ∑ i, indicator ((T.finish (eqv.symm i)).eval x) := by
          simpa only [Equiv.symm_apply_apply] using
            eqv.sum_comp (fun i => indicator ((T.finish (eqv.symm i)).eval x))

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V]

def narrowTests (b : ℕ) : Finset (Cube V → Bool) := by
  classical
  exact Finset.univ.filter fun J => ∃ H : CNF V, H.WidthAtMost b ∧ H.eval = J

@[simp] theorem mem_narrowTests_iff (b : ℕ) (J : Cube V → Bool) :
    J ∈ narrowTests b ↔ ∃ H : CNF V, H.WidthAtMost b ∧ H.eval = J := by
  classical
  simp [narrowTests]

theorem eval_mem_narrowTests (b : ℕ) (H : CNF V) (hH : H.WidthAtMost b) :
    H.eval ∈ narrowTests b :=
  (mem_narrowTests_iff b H.eval).mpr ⟨H, hH, rfl⟩

theorem narrowTests_true_mem (b : ℕ) :
    (fun _ : Cube V => true) ∈ narrowTests b := by
  apply (mem_narrowTests_iff b _).mpr
  refine ⟨[], ?_, ?_⟩
  · simp [CNF.WidthAtMost]
  · funext x
    exact CNF.eval_nil x

theorem narrowTests_false_mem (b : ℕ) :
    (fun _ : Cube V => false) ∈ narrowTests b := by
  apply (mem_narrowTests_iff b _).mpr
  refine ⟨[∅], ?_, ?_⟩
  · simp [CNF.WidthAtMost]
  · funext x
    simp

theorem narrowTests_nonempty (b : ℕ) : (narrowTests (V := V) b).Nonempty :=
  ⟨_, narrowTests_true_mem b⟩

def corr (b : ℕ) (G : Cube V → ℝ) : ℝ :=
  (narrowTests b).sup' (narrowTests_nonempty b)
    (fun J => |finiteAvg (fun x => G x * indicator (J x))|)

theorem abs_table_corr_le (b : ℕ) (G : Cube V → ℝ)
    (J : Cube V → Bool) (hJ : J ∈ narrowTests b) :
    |finiteAvg (fun x => G x * indicator (J x))| ≤ corr b G :=
  Finset.le_sup' (fun J : Cube V → Bool => |finiteAvg (fun x => G x * indicator (J x))|) hJ

theorem abs_corr_le (b : ℕ) (G : Cube V → ℝ) (H : CNF V)
    (hH : H.WidthAtMost b) :
    |finiteAvg (fun x => G x * indicator (H.eval x))| ≤ corr b G :=
  abs_table_corr_le b G H.eval (eval_mem_narrowTests b H hH)

theorem abs_mean_le_corr (b : ℕ) (G : Cube V → ℝ) :
    |finiteAvg G| ≤ corr b G := by
  simpa using abs_table_corr_le b G (fun _ => true) (narrowTests_true_mem b)

theorem corr_nonneg (b : ℕ) (G : Cube V → ℝ) : 0 ≤ corr b G :=
  (abs_nonneg (finiteAvg G)).trans (abs_mean_le_corr b G)

theorem corr_le_of_forall (b : ℕ) (G : Cube V → ℝ) (c : ℝ)
    (h : ∀ H : CNF V, H.WidthAtMost b →
      |finiteAvg (fun x => G x * indicator (H.eval x))| ≤ c) :
    corr b G ≤ c := by
  apply Finset.sup'_le
  intro J hJ
  obtain ⟨H, hH, rfl⟩ := (mem_narrowTests_iff b J).mp hJ
  exact h H hH

theorem corr_attained (b : ℕ) (G : Cube V → ℝ) :
    ∃ H : CNF V, H.WidthAtMost b ∧
      corr b G = |finiteAvg (fun x => G x * indicator (H.eval x))| := by
  obtain ⟨J, hJ, heq⟩ := Finset.exists_mem_eq_sup' (narrowTests_nonempty (V := V) b)
    (fun J => |finiteAvg (fun x => G x * indicator (J x))|)
  obtain ⟨H, hH, rfl⟩ := (mem_narrowTests_iff b J).mp hJ
  exact ⟨H, hH, heq⟩

theorem corr_le_abs_mean (b : ℕ) (G : Cube V → ℝ) :
    corr b G ≤ finiteAvg (fun x => |G x|) := by
  apply corr_le_of_forall
  intro H _
  apply (finiteAvg_abs_le _).trans
  apply finiteAvg_mono
  intro x
  rw [abs_mul, abs_of_nonneg (indicator_nonneg (H.eval x))]
  exact mul_le_of_le_one_right (abs_nonneg _) (indicator_le_one _)

theorem corr_linearCombination_identity {ι : Type uDepth2} (s : Finset ι)
    (c : ι → ℝ) (H : ι → CNF V) (G : Cube V → ℝ) :
    finiteAvg (fun x => G x * ∑ i ∈ s, c i * indicator ((H i).eval x)) =
      ∑ i ∈ s, c i * finiteAvg (fun x => G x * indicator ((H i).eval x)) := by
  calc
    _ = finiteAvg (fun x => ∑ i ∈ s, c i * (G x * indicator ((H i).eval x))) := by
      apply finiteAvg_congr
      intro x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_left_comm _ _ _
    _ = ∑ i ∈ s, finiteAvg (fun x => c i * (G x * indicator ((H i).eval x))) :=
      finiteAvg_sum s _
    _ = _ := Finset.sum_congr rfl (fun i _ => finiteAvg_const_mul _ _)

theorem abs_corr_linearCombination_le {ι : Type uDepth3} (s : Finset ι)
    (c : ι → ℝ) (H : ι → CNF V) (b : ℕ) (G : Cube V → ℝ)
    (hH : ∀ i ∈ s, (H i).WidthAtMost b) :
    |finiteAvg (fun x => G x * ∑ i ∈ s, c i * indicator ((H i).eval x))| ≤
      (∑ i ∈ s, |c i|) * corr b G := by
  rw [corr_linearCombination_identity]
  calc
    _ ≤ ∑ i ∈ s, |c i * finiteAvg (fun x => G x * indicator ((H i).eval x))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |c i| * |finiteAvg (fun x => G x * indicator ((H i).eval x))| := by
      simp only [abs_mul]
    _ ≤ ∑ i ∈ s, |c i| * corr b G := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (abs_corr_le b G (H i) (hH i hi)) (abs_nonneg _)
    _ = (∑ i ∈ s, |c i|) * corr b G := (Finset.sum_mul _ _ _).symm

theorem abs_corr_convex_mixture_le {ι : Type uDepth4} (s : Finset ι)
    (w : ι → ℝ) (H : ι → CNF V) (b : ℕ) (G : Cube V → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hH : ∀ i ∈ s, (H i).WidthAtMost b) :
    |finiteAvg (fun x => G x * ∑ i ∈ s, w i * indicator ((H i).eval x))| ≤
      corr b G := by
  have hwabs : (∑ i ∈ s, |w i|) = 1 := by
    calc
      _ = ∑ i ∈ s, w i :=
        Finset.sum_congr rfl (fun i hi => abs_of_nonneg (hw i hi))
      _ = 1 := hsum
  simpa only [hwabs, one_mul] using abs_corr_linearCombination_le s w H b G hH

theorem abs_corr_uniform_mixture_le {ι : Type uDepth5} [Fintype ι] [Nonempty ι]
    (H : ι → CNF V) (b : ℕ) (G : Cube V → ℝ)
    (hH : ∀ i, (H i).WidthAtMost b) :
    |finiteAvg (fun x => G x * finiteAvg (fun i => indicator ((H i).eval x)))| ≤
      corr b G := by
  have hlin :
      finiteAvg (fun x => G x * finiteAvg (fun i => indicator ((H i).eval x))) =
        finiteAvg (fun i => finiteAvg (fun x => G x * indicator ((H i).eval x))) := by
    calc
      _ = finiteAvg (fun x => finiteAvg (fun i => G x * indicator ((H i).eval x))) :=
        finiteAvg_congr (fun x => (finiteAvg_const_mul (G x) _).symm)
      _ = _ := finiteAvg_comm _
  rw [hlin]
  calc
    _ ≤ finiteAvg (fun i => |finiteAvg (fun x => G x * indicator ((H i).eval x))|) :=
      finiteAvg_abs_le _
    _ ≤ finiteAvg (fun _ : ι => corr b G) :=
      finiteAvg_mono (fun i => abs_corr_le b G (H i) (hH i))
    _ = corr b G := finiteAvg_const _

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace DepthThreeLowerBound

open scoped BigOperators Classical


namespace SparsePartition

variable {V : Type u} [Fintype V]

theorem correlation_eq_sum {H : CNF V} {b M : ℕ} {η : ℝ}
    (P : SparsePartition H b M η) (G : Cube V → ℝ) :
    finiteAvg (fun x => G x * indicator (H.eval x)) =
      ∑ i, finiteAvg (fun x => G x * indicator ((P.piece i).eval x)) := by
  calc
    finiteAvg (fun x => G x * indicator (H.eval x)) =
        finiteAvg (fun x => ∑ i, G x * indicator ((P.piece i).eval x)) := by
      apply finiteAvg_congr
      intro x
      rw [P.indicator_eq_sum x, Finset.mul_sum]
    _ = _ := finiteAvg_sum Finset.univ
      (fun i x => G x * indicator ((P.piece i).eval x))

theorem abs_correlation_le {H : CNF V} {b M : ℕ} {η δ : ℝ}
    (P : SparsePartition H b M η) (G : Cube V → ℝ) (hδ : 0 ≤ δ)
    (hpiece : ∀ i, |finiteAvg (fun x => G x * indicator ((P.piece i).eval x))| ≤ δ) :
    |finiteAvg (fun x => G x * indicator (H.eval x))| ≤
      (2 : ℝ) ^ (η * (Fintype.card V : ℝ)) * δ := by
  rw [P.correlation_eq_sum G]
  calc
    |∑ i, finiteAvg (fun x => G x * indicator ((P.piece i).eval x))| ≤
        ∑ i, |finiteAvg (fun x => G x * indicator ((P.piece i).eval x))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin P.count, δ := Finset.sum_le_sum (fun i _ => hpiece i)
    _ = (P.count : ℝ) * δ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right P.count_le hδ

end SparsePartition

theorem exists_sparse_correlation_transfer (b : ℕ) (η : ℝ)
    (hb : 1 ≤ b) (hη : 0 < η) :
    ∃ M : ℕ, 0 < M ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Cube V → ℝ) (δ : ℝ),
        0 ≤ δ →
        (∀ H : CNF V, H.Normalized → H.WidthAtMost b →
          H.length ≤ M * Fintype.card V →
          |finiteAvg (fun x => G x * indicator (H.eval x))| ≤ δ) →
        corr b G ≤ (2 : ℝ) ^ (η * (Fintype.card V : ℝ)) * δ := by
  obtain ⟨M, hM, hpartition⟩ := exists_sparse_partition_constant b η hb hη
  refine ⟨M, hM, ?_⟩
  intro V _ _ G δ hδ htests
  apply corr_le_of_forall
  intro H hH
  obtain ⟨P⟩ := hpartition V H hH
  apply P.abs_correlation_le G hδ
  intro i
  exact Eq.mp
    (congrArg (fun inst : Fintype (Cube V) =>
      |@finiteAvg (Cube V) inst (fun x => G x * indicator ((P.piece i).eval x))| ≤ δ)
      (Subsingleton.elim _ _))
    (htests (P.piece i) (P.normalized i) (P.width_le i) (P.clauses_le i))

theorem exists_sparse_correlation_constant (b : ℕ) (hb : 1 ≤ b) :
    ∃ M : ℕ, 0 < M ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Cube V → ℝ),
        (∀ H : CNF V, H.Normalized → H.WidthAtMost b →
          H.length ≤ M * Fintype.card V →
          |finiteAvg (fun x => G x * indicator (H.eval x))| ≤
            (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4)) →
        corr b G ≤ (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 8) := by
  obtain ⟨M, hM, htransfer⟩ := exists_sparse_correlation_transfer b (1 / 8) hb (by norm_num)
  refine ⟨M, hM, ?_⟩
  intro V _ _ G htests
  have h := htransfer V G ((2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4))
    (Real.rpow_nonneg (by norm_num) _) htests
  calc
    corr b G ≤ (2 : ℝ) ^ ((1 / 8) * (Fintype.card V : ℝ)) *
        (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4) := h
    _ = (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 8) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound.BinaryHash

open scoped BigOperators

theorem exists_last_nonzero {d : ℕ} (w : Data d) (hw : w ≠ 0) :
    ∃ s : Fin d, w s ≠ 0 ∧ ∀ a : Fin d, s.val < a.val → w a = 0 := by
  classical
  have hex : ∃ a : Fin d, w a ≠ 0 := by
    by_contra h
    apply hw
    funext a
    by_contra ha
    exact h ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hex
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun a : Fin d => w a ≠ 0) Fin.val
      ⟨a, by simp [ha]⟩
  refine ⟨s, (Finset.mem_filter.mp hs).2, ?_⟩
  intro b hsb
  by_contra hb
  have hle := hmax b (by simp [hb])
  omega

noncomputable def lastIndex {d : ℕ} (w : Data d) (hw : w ≠ 0) : Fin d :=
  (exists_last_nonzero w hw).choose

theorem lastIndex_nonzero {d : ℕ} (w : Data d) (hw : w ≠ 0) :
    w (lastIndex w hw) ≠ 0 :=
  (exists_last_nonzero w hw).choose_spec.1

theorem zero_after_lastIndex {d : ℕ} (w : Data d) (hw : w ≠ 0)
    (a : Fin d) (ha : (lastIndex w hw).val < a.val) : w a = 0 :=
  (exists_last_nonzero w hw).choose_spec.2 a ha

theorem data_dim_pos {d : ℕ} (w : Data d) (hw : w ≠ 0) : 0 < d :=
  Nat.zero_le (lastIndex w hw).val |>.trans_lt (lastIndex w hw).isLt

def Nonpivot {d r : ℕ} (w : Data d) (hw : w ≠ 0) :=
  {j : Fin (d + r - 1) // ¬ ∃ i : Fin r, sumIndex i (lastIndex w hw) = j}

noncomputable instance {d r : ℕ} (w : Data d) (hw : w ≠ 0) :
    Fintype (Nonpivot (r := r) w hw) := by
  classical
  unfold Nonpivot
  infer_instance

theorem card_nonpivot {d r : ℕ} (w : Data d) (hw : w ≠ 0) :
    Fintype.card (Nonpivot (r := r) w hw) = d - 1 := by
  classical
  have hp : Fintype.card
      {j : Fin (d + r - 1) // ∃ i : Fin r, sumIndex i (lastIndex w hw) = j} = r := by
    let e : Fin r ≃
        {j : Fin (d + r - 1) // ∃ i : Fin r, sumIndex i (lastIndex w hw) = j} :=
      Equiv.ofInjective (fun i : Fin r => sumIndex i (lastIndex w hw))
        (sumIndex_left_injective (lastIndex w hw))
    simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm
  calc
    Fintype.card (Nonpivot (r := r) w hw) = Fintype.card
        {j : Fin (d + r - 1) // ¬ ∃ i : Fin r, sumIndex i (lastIndex w hw) = j} :=
      Fintype.card_congr (Equiv.refl _)
    _ = (d + r - 1) - r := by
      rw [Fintype.card_subtype_compl, hp, Fintype.card_fin]
    _ = d - 1 := by
      have hd := data_dim_pos w hw
      omega

def triangularMap {d r : ℕ} (w : Data d) (hw : w ≠ 0) (u : Seed d r) :
    Output r × (Nonpivot (r := r) w hw → F2) :=
  (hashF2 u w, fun j => u j.val)

theorem triangularMap_injective {d r : ℕ} (w : Data d) (hw : w ≠ 0) :
    Function.Injective (triangularMap (r := r) w hw) := by
  classical
  intro u v huv
  have hhash : hashF2 u w = hashF2 v w := congrArg Prod.fst huv
  have hfree : (fun j : Nonpivot (r := r) w hw => u j.val) =
      (fun j : Nonpivot (r := r) w hw => v j.val) := congrArg Prod.snd huv
  have heq : ∀ n : ℕ, ∀ j : Fin (d + r - 1), j.val = n → u j = v j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      by_cases hp : ∃ i : Fin r, sumIndex i (lastIndex w hw) = j
      · obtain ⟨i, rfl⟩ := hp
        have hrow : (∑ a : Fin d,
            (u (sumIndex i a) - v (sumIndex i a)) * w a) = 0 := by
          calc
            (∑ a : Fin d, (u (sumIndex i a) - v (sumIndex i a)) * w a) =
                hashF2 u w i - hashF2 v w i := by
                  simp only [hashF2, sub_mul, Finset.sum_sub_distrib]
            _ = 0 := sub_eq_zero.mpr (congrFun hhash i)
        have hsingle : (∑ a : Fin d,
            (u (sumIndex i a) - v (sumIndex i a)) * w a) =
            (u (sumIndex i (lastIndex w hw)) -
              v (sumIndex i (lastIndex w hw))) * w (lastIndex w hw) := by
          apply Finset.sum_eq_single_of_mem (lastIndex w hw) (Finset.mem_univ _)
          intro a _ ha
          by_cases hlt : a.val < (lastIndex w hw).val
          · have hidx : (sumIndex i a).val < n := by
              simp only [sumIndex_val] at hj ⊢
              omega
            rw [ih (sumIndex i a).val hidx (sumIndex i a) rfl, sub_self, zero_mul]
          · have hne : a.val ≠ (lastIndex w hw).val := by
              intro he
              exact ha (Fin.ext he)
            have hgt : (lastIndex w hw).val < a.val := by omega
            rw [zero_after_lastIndex w hw a hgt, mul_zero]
        rw [hsingle] at hrow
        exact sub_eq_zero.mp ((mul_eq_zero.mp hrow).resolve_right (lastIndex_nonzero w hw))
      · exact congrFun hfree ⟨j, hp⟩
  exact funext fun j => heq j.val j rfl

theorem triangularMap_bijective {d r : ℕ} (w : Data d) (hw : w ≠ 0) :
    Function.Bijective (triangularMap (r := r) w hw) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨triangularMap_injective w hw, ?_⟩
  have hd := data_dim_pos w hw
  simp only [Seed, Output, Fintype.card_prod, Fintype.card_fun,
    F2, BinaryAlgebra.F2, ZMod.card, Fintype.card_fin, card_nonpivot]
  rw [← pow_add]
  congr 1
  omega

noncomputable def triangularEquiv {d r : ℕ} (w : Data d) (hw : w ≠ 0) :
    Seed d r ≃ Output r × (Nonpivot (r := r) w hw → F2) :=
  Equiv.ofBijective (triangularMap w hw) (triangularMap_bijective w hw)

@[simp] theorem triangularEquiv_fst {d r : ℕ} (w : Data d) (hw : w ≠ 0)
    (u : Seed d r) : (triangularEquiv w hw u).1 = hashF2 u w := rfl

@[simp] theorem triangularEquiv_snd {d r : ℕ} (w : Data d) (hw : w ≠ 0)
    (u : Seed d r) (j : Nonpivot (r := r) w hw) :
    (triangularEquiv w hw u).2 j = u j.val := rfl

end DepthThreeLowerBound.BinaryHash

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace BinaryHash

noncomputable section

variable {d r : ℕ}

def hashF2_fiberEquiv (w : Data d) (hw : w ≠ 0) (a : Output r) :
    {u : Seed d r // hashF2 u w = a} ≃ (Nonpivot (r := r) w hw → F2) where
  toFun u := (triangularEquiv (r := r) w hw u.1).2
  invFun b := ⟨(triangularEquiv (r := r) w hw).symm (a, b), by
    rw [← triangularEquiv_fst w hw]
    exact congrArg Prod.fst
      ((triangularEquiv (r := r) w hw).apply_symm_apply (a, b))⟩
  left_inv u := by
    apply Subtype.ext
    apply (triangularEquiv (r := r) w hw).injective
    change (triangularEquiv (r := r) w hw)
      ((triangularEquiv (r := r) w hw).symm
        (a, (triangularEquiv (r := r) w hw u.1).2)) =
      triangularEquiv (r := r) w hw u.1
    rw [Equiv.apply_symm_apply]
    exact Prod.ext ((triangularEquiv_fst w hw u.1).trans u.2).symm rfl
  right_inv b := by
    change ((triangularEquiv (r := r) w hw)
      ((triangularEquiv (r := r) w hw).symm (a, b))).2 = b
    rw [Equiv.apply_symm_apply]

theorem hashF2_fiber_card (w : Data d) (hw : w ≠ 0) (a : Output r) :
    Fintype.card {u : Seed d r // hashF2 u w = a} = 2 ^ (d - 1) := by
  classical
  calc
    Fintype.card {u : Seed d r // hashF2 u w = a} =
        Fintype.card (Nonpivot (r := r) w hw → F2) :=
      Fintype.card_congr (hashF2_fiberEquiv w hw a)
    _ = 2 ^ (d - 1) := by
      change Fintype.card (Nonpivot (r := r) w hw → ZMod 2) = 2 ^ (d - 1)
      rw [Fintype.card_fun, ZMod.card, card_nonpivot (r := r) w hw]

theorem hashF2_surjective (w : Data d) (hw : w ≠ 0) :
    Function.Surjective (fun u : Seed d r => hashF2 u w) := by
  intro a
  let u : {u : Seed d r // hashF2 u w = a} :=
    (hashF2_fiberEquiv w hw a).symm (fun _ => 0)
  exact ⟨u.1, u.2⟩

def hashF2_collisionEquiv (x y : Data d) :
    {u : Seed d r // hashF2 u x = hashF2 u y} ≃
      {u : Seed d r // hashF2 u (x - y) = 0} :=
  Equiv.subtypeEquivRight fun u => by
    rw [hashF2_sub_data, sub_eq_zero]

theorem hashF2_collision_card (x y : Data d) (hxy : x ≠ y) :
    Fintype.card {u : Seed d r // hashF2 u x = hashF2 u y} = 2 ^ (d - 1) := by
  calc
    Fintype.card {u : Seed d r // hashF2 u x = hashF2 u y} =
        Fintype.card {u : Seed d r // hashF2 u (x - y) = 0} :=
      Fintype.card_congr (hashF2_collisionEquiv (r := r) x y)
    _ = 2 ^ (d - 1) :=
      hashF2_fiber_card (x - y) (sub_ne_zero.mpr hxy) 0

end

end BinaryHash
end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound.BinaryHash

open BinaryAlgebra

variable {d r : ℕ}

abbrev OutsideData (T : Finset (Fin d)) := {i : Fin d // i ∉ T} → F2

def coordinateCube (T : Finset (Fin d)) (rho : OutsideData T) : Set (Data d) :=
  {x | ∀ i (hi : i ∉ T), x i = rho ⟨i, hi⟩}

def SupportedOn (T : Finset (Fin d)) (w : Data d) : Prop :=
  ∀ i, i ∉ T → w i = 0

def coordinateCubeExtend (T : Finset (Fin d)) (rho : OutsideData T)
    (z : T → F2) : Data d :=
  fun i => if hi : i ∈ T then z ⟨i, hi⟩ else rho ⟨i, hi⟩

theorem coordinateCubeExtend_mem (T : Finset (Fin d)) (rho : OutsideData T)
    (z : T → F2) : coordinateCubeExtend T rho z ∈ coordinateCube T rho := by
  intro i hi
  simp [coordinateCubeExtend, hi]

def coordinateCubeEquiv (T : Finset (Fin d)) (rho : OutsideData T) :
    (coordinateCube T rho) ≃ (T → F2) where
  toFun x := fun i => x.val i.val
  invFun z := ⟨coordinateCubeExtend T rho z, coordinateCubeExtend_mem T rho z⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ T
    · simp [coordinateCubeExtend, hi]
    · simpa [coordinateCubeExtend, hi] using (x.property i hi).symm
  right_inv z := by
    funext i
    simp [coordinateCubeExtend, i.property]

def supportedDataEquiv (T : Finset (Fin d)) :
    {w : Data d // SupportedOn T w} ≃ (T → F2) where
  toFun w := fun i => w.val i.val
  invFun z := ⟨coordinateCubeExtend T 0 z, coordinateCubeExtend_mem T 0 z⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ T
    · simp [coordinateCubeExtend, hi]
    · simpa [coordinateCubeExtend, hi] using (w.property i hi).symm
  right_inv z := by
    funext i
    simp [coordinateCubeExtend, i.property]

@[simp] theorem supportedOn_zero (T : Finset (Fin d)) :
    SupportedOn T (0 : Data d) := by
  intro i hi
  rfl

theorem supportedOn_sub_of_mem {T : Finset (Fin d)} {rho : OutsideData T}
    {x y : Data d} (hx : x ∈ coordinateCube T rho)
    (hy : y ∈ coordinateCube T rho) : SupportedOn T (x - y) := by
  intro i hi
  change x i - y i = 0
  rw [hx i hi, hy i hi, sub_self]

theorem add_mem_coordinateCube {T : Finset (Fin d)} {rho : OutsideData T}
    {x w : Data d} (hx : x ∈ coordinateCube T rho) (hw : SupportedOn T w) :
    x + w ∈ coordinateCube T rho := by
  intro i hi
  change x i + w i = rho ⟨i, hi⟩
  rw [hw i hi, add_zero, hx i hi]

theorem not_injOn_coordinateCube_iff (u : Seed d r) (T : Finset (Fin d))
    (rho : OutsideData T) :
    ¬ Set.InjOn (hashF2 u) (coordinateCube T rho) ↔
      ∃ w : Data d, SupportedOn T w ∧ w ≠ 0 ∧ hashF2 u w = 0 := by
  classical
  constructor
  · intro h
    simp only [Set.InjOn] at h
    push Not at h
    obtain ⟨x, hx, y, hy, hxy, hne⟩ := h
    refine ⟨x - y, supportedOn_sub_of_mem hx hy, sub_ne_zero.mpr hne, ?_⟩
    rw [hashF2_sub_data, hxy, sub_self]
  · rintro ⟨w, hw, hne, hkernel⟩ hinj
    let x : Data d := coordinateCubeExtend T rho 0
    have hx : x ∈ coordinateCube T rho := coordinateCubeExtend_mem T rho 0
    have hxw : x + w ∈ coordinateCube T rho := add_mem_coordinateCube hx hw
    have hhash : hashF2 u (x + w) = hashF2 u x := by
      rw [hashF2_add_data, hkernel, add_zero]
    have heq : x + w = x + 0 := by simpa using hinj hxw hx hhash
    exact hne (add_left_cancel heq)

theorem not_injOn_coordinateCube_iff_of_outside (u : Seed d r)
    (T : Finset (Fin d)) (rho sigma : OutsideData T) :
    (¬ Set.InjOn (hashF2 u) (coordinateCube T rho)) ↔
      ¬ Set.InjOn (hashF2 u) (coordinateCube T sigma) := by
  rw [not_injOn_coordinateCube_iff, not_injOn_coordinateCube_iff]

def supportedVectors (T : Finset (Fin d)) : Finset (Data d) := by
  classical
  exact Finset.univ.filter (SupportedOn T)

@[simp] theorem mem_supportedVectors (T : Finset (Fin d)) (w : Data d) :
    w ∈ supportedVectors T ↔ SupportedOn T w := by
  classical
  simp [supportedVectors]

theorem supportedVectors_card (T : Finset (Fin d)) :
    (supportedVectors T).card = 2 ^ T.card := by
  classical
  calc
    (supportedVectors T).card = Fintype.card {w : Data d // SupportedOn T w} := by
      simpa [supportedVectors] using (Fintype.card_subtype (SupportedOn T)).symm
    _ = Fintype.card (T → F2) := Fintype.card_congr (supportedDataEquiv T)
    _ = 2 ^ T.card := by
      change Fintype.card (T → ZMod 2) = 2 ^ T.card
      rw [Fintype.card_fun, ZMod.card, Fintype.card_coe]

def nonzeroSupportedVectors (T : Finset (Fin d)) : Finset (Data d) :=
  (supportedVectors T).erase 0

@[simp] theorem mem_nonzeroSupportedVectors (T : Finset (Fin d)) (w : Data d) :
    w ∈ nonzeroSupportedVectors T ↔ SupportedOn T w ∧ w ≠ 0 := by
  classical
  simp [nonzeroSupportedVectors, and_comm]

theorem nonzeroSupportedVectors_card (T : Finset (Fin d)) :
    (nonzeroSupportedVectors T).card = 2 ^ T.card - 1 := by
  classical
  rw [nonzeroSupportedVectors, Finset.card_erase_of_mem, supportedVectors_card]
  exact (mem_supportedVectors T 0).mpr (supportedOn_zero T)

def kernelSeeds (w : Data d) : Finset (Seed d r) := by
  classical
  exact Finset.univ.filter (fun u => hashF2 u w = 0)

@[simp] theorem mem_kernelSeeds (w : Data d) (u : Seed d r) :
    u ∈ kernelSeeds w ↔ hashF2 u w = 0 := by
  classical
  simp [kernelSeeds]

theorem kernelSeeds_card (w : Data d) (hw : w ≠ 0) :
    (kernelSeeds (r := r) w).card = 2 ^ (d - 1) := by
  classical
  calc
    (kernelSeeds (r := r) w).card =
        Fintype.card {u : Seed d r // hashF2 u w = 0} := by
      simpa [kernelSeeds] using
        (Fintype.card_subtype (fun u : Seed d r => hashF2 u w = 0)).symm
    _ = 2 ^ (d - 1) := hashF2_fiber_card w hw 0

def badSeeds (T : Finset (Fin d)) (rho : OutsideData T) : Finset (Seed d r) := by
  classical
  exact Finset.univ.filter (fun u => ¬ Set.InjOn (hashF2 u) (coordinateCube T rho))

@[simp] theorem mem_badSeeds (T : Finset (Fin d)) (rho : OutsideData T)
    (u : Seed d r) :
    u ∈ badSeeds T rho ↔ ¬ Set.InjOn (hashF2 u) (coordinateCube T rho) := by
  classical
  simp [badSeeds]

theorem badSeeds_eq_biUnion (T : Finset (Fin d)) (rho : OutsideData T) :
    badSeeds (r := r) T rho =
      (nonzeroSupportedVectors T).biUnion (fun w => kernelSeeds (r := r) w) := by
  classical
  ext u
  simp only [mem_badSeeds, Finset.mem_biUnion, mem_nonzeroSupportedVectors,
    mem_kernelSeeds, and_assoc]
  exact not_injOn_coordinateCube_iff u T rho

theorem badSeeds_eq_of_outside (T : Finset (Fin d)) (rho sigma : OutsideData T) :
    badSeeds (r := r) T rho = badSeeds T sigma := by
  rw [badSeeds_eq_biUnion, badSeeds_eq_biUnion]

theorem badSeeds_card_le (T : Finset (Fin d)) (rho : OutsideData T) :
    (badSeeds (r := r) T rho).card ≤ (2 ^ T.card - 1) * 2 ^ (d - 1) := by
  classical
  rw [badSeeds_eq_biUnion]
  calc
    ((nonzeroSupportedVectors T).biUnion (fun w => kernelSeeds (r := r) w)).card ≤
        ∑ w ∈ nonzeroSupportedVectors T, (kernelSeeds (r := r) w).card :=
      Finset.card_biUnion_le
    _ = ∑ _w ∈ nonzeroSupportedVectors T, 2 ^ (d - 1) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact kernelSeeds_card w ((mem_nonzeroSupportedVectors T w).mp hw).2
    _ = (2 ^ T.card - 1) * 2 ^ (d - 1) := by
      simp [nonzeroSupportedVectors_card]

theorem injOn_coordinateCube_empty (u : Seed d r) (rho : OutsideData (∅ : Finset (Fin d))) :
    Set.InjOn (hashF2 u) (coordinateCube ∅ rho) := by
  intro x hx y hy hxy
  funext i
  exact (hx i (by simp)).trans (hy i (by simp)).symm

@[simp] theorem badSeeds_empty (rho : OutsideData (∅ : Finset (Fin d))) :
    badSeeds (r := r) ∅ rho = ∅ := by
  classical
  ext u
  simp [injOn_coordinateCube_empty]

theorem badSeeds_card_eq_zero_of_card_eq_zero (T : Finset (Fin d))
    (rho : OutsideData T) (hT : T.card = 0) : (badSeeds (r := r) T rho).card = 0 := by
  have h : T = ∅ := Finset.card_eq_zero.mp hT
  subst T
  simp

@[simp] theorem badSeeds_zero_data (T : Finset (Fin 0)) (rho : OutsideData T) :
    badSeeds (r := r) T rho = ∅ := by
  have hT : T = ∅ := Finset.eq_empty_of_isEmpty T
  subst T
  exact badSeeds_empty rho

theorem injOn_coordinateCube_zero_output_iff (u : Seed d 0)
    (T : Finset (Fin d)) (rho : OutsideData T) :
    Set.InjOn (hashF2 u) (coordinateCube T rho) ↔ T = ∅ := by
  classical
  constructor
  · intro hinj
    by_contra hT
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    let w : Data d := fun i => if i = j then 1 else 0
    have hsupport : SupportedOn T w := by
      intro i hi
      have hij : i ≠ j := by
        intro h
        apply hi
        simpa [h] using hj
      simp [w, hij]
    have hnonzero : w ≠ 0 := by
      intro h
      have h10 : (1 : F2) = 0 := by simpa [w] using congrFun h j
      exact one_ne_zero h10
    have hkernel : hashF2 u w = 0 := by
      funext i
      exact Fin.elim0 i
    exact ((not_injOn_coordinateCube_iff u T rho).mpr
      ⟨w, hsupport, hnonzero, hkernel⟩) hinj
  · intro hT
    subst T
    exact injOn_coordinateCube_empty u rho

theorem badSeeds_zero_output (T : Finset (Fin d)) (rho : OutsideData T) :
    badSeeds (r := 0) T rho = if T = ∅ then ∅ else Finset.univ := by
  classical
  ext u
  by_cases hT : T = ∅
  · subst T
    simp
  · simp [mem_badSeeds, injOn_coordinateCube_zero_output_iff, hT]

end DepthThreeLowerBound.BinaryHash

end

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound.BinaryHash

open BinaryAlgebra

variable {d r : ℕ}

theorem hashBool_eq_iff (u : Fin (d + r - 1) → Bool)
    (x : Fin d → Bool) (a : Fin r → Bool) :
    hashBool u x = a ↔
      hashF2 (bitsEquivF2 (Fin (d + r - 1)) u) (bitsEquivF2 (Fin d) x) =
        bitsEquivF2 (Fin r) a := by
  rw [← bitsEquivF2_hashBool]
  exact (bitsEquivF2 (Fin r)).injective.eq_iff.symm

theorem hashBool_collision_iff (u : Fin (d + r - 1) → Bool)
    (x y : Fin d → Bool) :
    hashBool u x = hashBool u y ↔
      hashF2 (bitsEquivF2 (Fin (d + r - 1)) u) (bitsEquivF2 (Fin d) x) =
        hashF2 (bitsEquivF2 (Fin (d + r - 1)) u) (bitsEquivF2 (Fin d) y) := by
  rw [← bitsEquivF2_hashBool, ← bitsEquivF2_hashBool]
  exact (bitsEquivF2 (Fin r)).injective.eq_iff.symm

def hashBool_fiberEquiv (x : Fin d → Bool) (a : Fin r → Bool) :
    {u : Fin (d + r - 1) → Bool // hashBool u x = a} ≃
      {u : Seed d r // hashF2 u (bitsEquivF2 (Fin d) x) =
        bitsEquivF2 (Fin r) a} :=
  Equiv.subtypeEquiv (bitsEquivF2 (Fin (d + r - 1)))
    (fun u => hashBool_eq_iff u x a)

theorem hashBool_fiber_card (x : Fin d → Bool) (hx : x ≠ fun _ => false)
    (a : Fin r → Bool) :
    Fintype.card {u : Fin (d + r - 1) → Bool // hashBool u x = a} = 2 ^ (d - 1) := by
  classical
  have hnonzero : bitsEquivF2 (Fin d) x ≠ 0 := by
    intro h
    apply hx
    funext i
    apply bitValue_injective
    simpa using congrFun h i
  exact (Fintype.card_congr (hashBool_fiberEquiv x a)).trans
    (hashF2_fiber_card (bitsEquivF2 (Fin d) x) hnonzero (bitsEquivF2 (Fin r) a))

def hashBool_collisionEquiv (x y : Fin d → Bool) :
    {u : Fin (d + r - 1) → Bool // hashBool u x = hashBool u y} ≃
      {u : Seed d r // hashF2 u (bitsEquivF2 (Fin d) x) =
        hashF2 u (bitsEquivF2 (Fin d) y)} :=
  Equiv.subtypeEquiv (bitsEquivF2 (Fin (d + r - 1)))
    (fun u => hashBool_collision_iff u x y)

theorem hashBool_collision_card (x y : Fin d → Bool) (hxy : x ≠ y) :
    Fintype.card {u : Fin (d + r - 1) → Bool // hashBool u x = hashBool u y} =
      2 ^ (d - 1) := by
  classical
  exact (Fintype.card_congr (hashBool_collisionEquiv (r := r) x y)).trans
    (hashF2_collision_card (bitsEquivF2 (Fin d) x) (bitsEquivF2 (Fin d) y)
      (fun h => hxy ((bitsEquivF2 (Fin d)).injective h)))

def boolCoordinateCube (T : Finset (Fin d)) (rho : {i : Fin d // i ∉ T} → Bool) :
    Set (Fin d → Bool) :=
  {x | ∀ i (hi : i ∉ T), x i = rho ⟨i, hi⟩}

theorem mem_boolCoordinateCube_iff (T : Finset (Fin d))
    (rho : {i : Fin d // i ∉ T} → Bool) (x : Fin d → Bool) :
    x ∈ boolCoordinateCube T rho ↔
      bitsEquivF2 (Fin d) x ∈ coordinateCube T (fun i => bitValue (rho i)) := by
  constructor
  · intro hx i hi
    change bitValue (x i) = bitValue (rho ⟨i, hi⟩)
    exact congrArg bitValue (hx i hi)
  · intro hx i hi
    exact bitValue_injective (hx i hi)

theorem injOn_hashBool_iff (u : Fin (d + r - 1) → Bool)
    (T : Finset (Fin d)) (rho : {i : Fin d // i ∉ T} → Bool) :
    Set.InjOn (hashBool u) (boolCoordinateCube T rho) ↔
      Set.InjOn (hashF2 (bitsEquivF2 (Fin (d + r - 1)) u))
        (coordinateCube T (fun i => bitValue (rho i))) := by
  constructor
  · intro hinj x hx y hy hxy
    obtain ⟨a, rfl⟩ := (bitsEquivF2 (Fin d)).surjective x
    obtain ⟨b, rfl⟩ := (bitsEquivF2 (Fin d)).surjective y
    have hab := hinj ((mem_boolCoordinateCube_iff T rho a).mpr hx)
      ((mem_boolCoordinateCube_iff T rho b).mpr hy)
      ((hashBool_collision_iff u a b).mpr hxy)
    exact congrArg (bitsEquivF2 (Fin d)) hab
  · intro hinj x hx y hy hxy
    apply (bitsEquivF2 (Fin d)).injective
    exact hinj ((mem_boolCoordinateCube_iff T rho x).mp hx)
      ((mem_boolCoordinateCube_iff T rho y).mp hy)
      ((hashBool_collision_iff u x y).mp hxy)

def hashBool_badSeedEquiv (T : Finset (Fin d))
    (rho : {i : Fin d // i ∉ T} → Bool) :
    {u : Fin (d + r - 1) → Bool // ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)} ≃
      {u : Seed d r // ¬ Set.InjOn (hashF2 u)
        (coordinateCube T (fun i => bitValue (rho i)))} :=
  Equiv.subtypeEquiv (bitsEquivF2 (Fin (d + r - 1)))
    (fun u => not_congr (injOn_hashBool_iff u T rho))

open scoped Classical in
theorem hashBool_badSeed_card_le (T : Finset (Fin d))
    (rho : {i : Fin d // i ∉ T} → Bool) :
    Fintype.card
      {u : Fin (d + r - 1) → Bool // ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)} ≤
        (2 ^ T.card - 1) * 2 ^ (d - 1) := by
  classical
  calc
    Fintype.card
        {u : Fin (d + r - 1) → Bool // ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)} =
      Fintype.card {u : Seed d r // ¬ Set.InjOn (hashF2 u)
        (coordinateCube T (fun i => bitValue (rho i)))} :=
          Fintype.card_congr (hashBool_badSeedEquiv (r := r) T rho)
    _ = (badSeeds (r := r) T (fun i => bitValue (rho i))).card := by
      simp only [badSeeds, Fintype.card_subtype]
    _ ≤ (2 ^ T.card - 1) * 2 ^ (d - 1) := badSeeds_card_le T _

end DepthThreeLowerBound.BinaryHash

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

open scoped BigOperators

variable {V : Type uDepth1} [Fintype V]

def bernoulliWeight (p : ℝ) (R : Finset V) : ℝ :=
  p ^ R.card * (1 - p) ^ (Fintype.card V - R.card)

theorem bernoulliWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (R : Finset V) : 0 ≤ bernoulliWeight p R := by
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem bernoulliWeight_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (R : Finset V) : 0 < bernoulliWeight p R := by
  exact mul_pos (pow_pos hp0 _) (pow_pos (sub_pos.mpr hp1) _)

theorem sum_bernoulliWeight (p : ℝ) :
    ∑ R : Finset V, bernoulliWeight p R = 1 := by
  classical
  have hp : p + (1 - p) = 1 := by ring
  simpa only [bernoulliWeight, hp, Finset.prod_const, Finset.card_compl, one_pow]
    using (Fintype.prod_add (fun _ : V => p) (fun _ : V => 1 - p)).symm

variable [DecidableEq V]

theorem bernoulliWeight_disjoint_balance (p : ℝ) (R D : Finset V)
    (hRD : Disjoint R D) :
    bernoulliWeight p (R ∪ D) * (1 - p) ^ D.card =
      bernoulliWeight p R * p ^ D.card := by
  have hcard : R.card + D.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hRD]
    exact (R ∪ D).card_le_univ
  have hD : D.card ≤ Fintype.card V - R.card :=
    Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hcard)
  have hsplit : Fintype.card V - R.card =
      (Fintype.card V - (R.card + D.card)) + D.card := by
    rw [← Nat.sub_sub, Nat.sub_add_cancel hD]
  unfold bernoulliWeight
  rw [Finset.card_union_of_disjoint hRD, hsplit, pow_add, pow_add]
  ring

theorem bernoulliWeight_disjoint_union {p : ℝ} (_hp0 : 0 < p) (hp1 : p < 1)
    (R D : Finset V) (hRD : Disjoint R D) :
    bernoulliWeight p (R ∪ D) * (2 : ℝ) ^ D.card =
      bernoulliWeight p R * (2 * p / (1 - p)) ^ D.card := by
  have hq : (1 - p) ^ D.card ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (sub_pos.mpr hp1))
  rw [div_pow, mul_pow, ← mul_div_assoc]
  apply (eq_div_iff hq).2
  calc
    (bernoulliWeight p (R ∪ D) * (2 : ℝ) ^ D.card) * (1 - p) ^ D.card =
        (bernoulliWeight p (R ∪ D) * (1 - p) ^ D.card) * (2 : ℝ) ^ D.card := by
          ring
    _ = (bernoulliWeight p R * p ^ D.card) * (2 : ℝ) ^ D.card := by
          rw [bernoulliWeight_disjoint_balance p R D hRD]
    _ = bernoulliWeight p R * ((2 : ℝ) ^ D.card * p ^ D.card) := by ring

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [instFintypeV : Fintype V] [instDecidableEqV : DecidableEq V]

def liveSet (σ : Restriction V) : Finset V :=
  Finset.univ.filter (fun v => σ v = none)

@[simp] theorem mem_liveSet
    {V : Type uDepth1}
    [instFintypeV : Fintype V]
    [DecidableEq V]
    (σ : Restriction V) (v : V) :
    v ∈ liveSet σ ↔ σ v = none := by
  simp [liveSet]

def maskRestriction (T : Finset V) (y : Cube V) : Restriction V :=
  fun v => if v ∈ T then none else some (y v)

@[simp] theorem maskRestriction_live
    {V : Type uDepth1}
    [Fintype V]
    [instDecidableEqV : DecidableEq V]
    (T : Finset V) (y : Cube V) (v : V)
    (hv : v ∈ T) : maskRestriction T y v = none := by
  simp [maskRestriction, hv]

@[simp] theorem maskRestriction_fixed
    {V : Type uDepth1}
    [Fintype V]
    [instDecidableEqV : DecidableEq V]
    (T : Finset V) (y : Cube V) (v : V)
    (hv : v ∉ T) : maskRestriction T y v = some (y v) := by
  simp [maskRestriction, hv]

@[simp] theorem liveSet_maskRestriction (T : Finset V) (y : Cube V) :
    liveSet (maskRestriction T y) = T := by
  ext v
  by_cases hv : v ∈ T <;> simp [liveSet, maskRestriction, hv]

@[simp] theorem fill_maskRestriction (T : Finset V) (y : Cube V) :
    fill (maskRestriction T y) (fun v => y v.val) = y := by
  funext v
  by_cases hv : v ∈ T
  · exact fill_live (maskRestriction T y) (fun w => y w.val)
      ⟨v, maskRestriction_live T y v hv⟩
  · exact fill_fixed (maskRestriction T y) (fun w => y w.val) v (y v)
      (maskRestriction_fixed T y v hv)

@[simp] theorem maskRestriction_fill (σ : Restriction V) (z : Cube (Live σ)) :
    maskRestriction (liveSet σ) (fill σ z) = σ := by
  funext v
  cases hv : σ v with
  | none => simp [maskRestriction, hv]
  | some b => simp [maskRestriction, hv]

def restrictionCoordinates (s : Σ σ : Restriction V, Cube (Live σ)) :
    Finset V × Cube V :=
  (liveSet s.1, fill s.1 s.2)

theorem restrictionCoordinates_injective :
    Function.Injective (restrictionCoordinates (V := V)) := by
  rintro ⟨σ, z⟩ ⟨τ, w⟩ h
  have hsets : liveSet σ = liveSet τ := congrArg Prod.fst h
  have hfills : fill σ z = fill τ w := congrArg Prod.snd h
  have hστ : σ = τ := by
    calc
      σ = maskRestriction (liveSet σ) (fill σ z) := (maskRestriction_fill σ z).symm
      _ = maskRestriction (liveSet τ) (fill τ w) := by rw [hsets, hfills]
      _ = τ := maskRestriction_fill τ w
  subst τ
  have hzw : z = w := by
    funext v
    simpa only [fill_live] using congrFun hfills v.val
  cases hzw
  rfl

theorem restrictionCoordinates_surjective :
    Function.Surjective (restrictionCoordinates (V := V)) := by
  rintro ⟨T, y⟩
  refine ⟨⟨maskRestriction T y, fun v => y v.val⟩, ?_⟩
  exact Prod.ext (liveSet_maskRestriction T y) (fill_maskRestriction T y)

def restrictionCoordinatesEquiv :
    (Σ σ : Restriction V, Cube (Live σ)) ≃ (Finset V × Cube V) :=
  Equiv.ofBijective restrictionCoordinates
    ⟨restrictionCoordinates_injective, restrictionCoordinates_surjective⟩

@[simp] theorem restrictionCoordinatesEquiv_apply
    (s : Σ σ : Restriction V, Cube (Live σ)) :
    restrictionCoordinatesEquiv s = (liveSet s.1, fill s.1 s.2) := rfl

@[simp] theorem card_live_maskRestriction (T : Finset V) (y : Cube V) :
    Fintype.card (Live (maskRestriction T y)) = T.card := by
  let e : Live (maskRestriction T y) ≃ ↥T :=
    Equiv.subtypeEquivRight (fun v => by
      by_cases hv : v ∈ T <;> simp [maskRestriction, hv])
  exact (Fintype.card_congr e).trans (Fintype.card_coe T)

theorem restrictionWeight_maskRestriction (p : ℝ) (T : Finset V) (y : Cube V) :
    restrictionWeight p (maskRestriction T y) =
      p ^ T.card * ((1 - p) / 2) ^ (Fintype.card V - T.card) := by
  classical
  have hprodLive :
      (∏ v ∈ T, restrictionCoordinateWeight p (maskRestriction T y v)) =
        p ^ T.card := by
    calc
      _ = ∏ _v ∈ T, p := by
        apply Finset.prod_congr rfl
        intro v hv
        simp [maskRestriction, hv, restrictionCoordinateWeight]
      _ = _ := by simp
  have hprodFixed :
      (∏ v ∈ Tᶜ, restrictionCoordinateWeight p (maskRestriction T y v)) =
        ((1 - p) / 2) ^ (Fintype.card V - T.card) := by
    calc
      _ = ∏ _v ∈ Tᶜ, ((1 - p) / 2) := by
        apply Finset.prod_congr rfl
        intro v hv
        have hv' : v ∉ T := Finset.mem_compl.mp hv
        simp [maskRestriction, hv', restrictionCoordinateWeight]
      _ = _ := by simp only [Finset.prod_const, Finset.card_compl]
  unfold restrictionWeight
  rw [← Finset.prod_mul_prod_compl T
    (fun v => restrictionCoordinateWeight p (maskRestriction T y v))]
  rw [hprodLive, hprodFixed]

theorem restriction_mask_joint_weight (p : ℝ) (T : Finset V) (y : Cube V) :
    restrictionWeight p (maskRestriction T y) *
        (Fintype.card (Cube (Live (maskRestriction T y))) : ℝ)⁻¹ =
      bernoulliWeight p T * (Fintype.card (Cube V) : ℝ)⁻¹ := by
  have hcLive : (Fintype.card (Cube (Live (maskRestriction T y))) : ℝ) =
      (2 : ℝ) ^ T.card := by
    simp [Cube]
  have hcV : (Fintype.card (Cube V) : ℝ) =
      (2 : ℝ) ^ Fintype.card V := by
    simp [Cube]
  rw [restrictionWeight_maskRestriction, hcLive, hcV]
  unfold bernoulliWeight
  calc
    _ = (p ^ T.card * (1 - p) ^ (Fintype.card V - T.card)) *
        (((2 : ℝ) ^ (Fintype.card V - T.card))⁻¹ *
          ((2 : ℝ) ^ T.card)⁻¹) := by
      rw [div_pow, div_eq_mul_inv]
      ring
    _ = _ := by
      rw [← mul_inv, ← pow_add, Nat.sub_add_cancel T.card_le_univ]

theorem restriction_fill_joint_weight (p : ℝ) (σ : Restriction V)
    (z : Cube (Live σ)) :
    restrictionWeight p σ * (Fintype.card (Cube (Live σ)) : ℝ)⁻¹ =
      bernoulliWeight p (liveSet σ) * (Fintype.card (Cube V) : ℝ)⁻¹ := by
  have h := restriction_mask_joint_weight p (liveSet σ) (fill σ z)
  simpa only [maskRestriction_fill] using h

theorem restrictionAvg_fill_coupling (p : ℝ)
    (F : Restriction V → Cube V → ℝ) :
    restrictionAvg p (fun σ => finiteAvg (fun z : Cube (Live σ) => F σ (fill σ z))) =
      ∑ T : Finset V, bernoulliWeight p T *
        finiteAvg (fun y : Cube V => F (maskRestriction T y) y) := by
  classical
  unfold restrictionAvg finiteAvg
  calc
    _ = ∑ σ : Restriction V, ∑ z : Cube (Live σ),
        (restrictionWeight p σ * (Fintype.card (Cube (Live σ)) : ℝ)⁻¹) *
          F σ (fill σ z) := by
      refine Finset.sum_congr ?_ ?_
      · ext σ
        simp only [Finset.mem_univ]
      · intro σ hσ
        dsimp only
        rw [← mul_assoc, Finset.mul_sum]
    _ = ∑ s : (Σ σ : Restriction V, Cube (Live σ)),
        (restrictionWeight p s.1 * (Fintype.card (Cube (Live s.1)) : ℝ)⁻¹) *
          F s.1 (fill s.1 s.2) := by
      exact (Fintype.sum_sigma'
        (fun (σ : Restriction V) (z : Cube (Live σ)) =>
          (restrictionWeight p σ * (Fintype.card (Cube (Live σ)) : ℝ)⁻¹) *
            F σ (fill σ z))).symm
    _ = ∑ Ty : Finset V × Cube V,
        (bernoulliWeight p Ty.1 * (Fintype.card (Cube V) : ℝ)⁻¹) *
          F (maskRestriction Ty.1 Ty.2) Ty.2 := by
      apply Fintype.sum_equiv (restrictionCoordinatesEquiv (V := V))
      rintro ⟨σ, z⟩
      change (restrictionWeight p σ * (Fintype.card (Cube (Live σ)) : ℝ)⁻¹) *
          F σ (fill σ z) =
        (bernoulliWeight p (liveSet σ) * (Fintype.card (Cube V) : ℝ)⁻¹) *
          F (maskRestriction (liveSet σ) (fill σ z)) (fill σ z)
      rw [restriction_fill_joint_weight p σ z, maskRestriction_fill]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro T hT
      dsimp only
      rw [← Finset.mul_sum]
      ring

theorem restrictionAvg_fill_reweight (p : ℝ)
    (F : Restriction V → Cube V → ℝ) :
    restrictionAvg p (fun σ => finiteAvg (fun z : Cube (Live σ) => F σ (fill σ z))) =
      finiteAvg (fun y : Cube V =>
        ∑ T : Finset V, bernoulliWeight p T * F (maskRestriction T y) y) := by
  rw [restrictionAvg_fill_coupling, finiteAvg_sum]
  apply Finset.sum_congr rfl
  intro T hT
  exact (finiteAvg_const_mul (bernoulliWeight p T)
    (fun y : Cube V => F (maskRestriction T y) y)).symm

theorem restrictionAvg_fill (p : ℝ) (F : Cube V → ℝ) :
    restrictionAvg p (fun σ => finiteAvg (fun z : Cube (Live σ) => F (fill σ z))) =
      finiteAvg F := by
  calc
    _ = ∑ T : Finset V, bernoulliWeight p T * finiteAvg F :=
      restrictionAvg_fill_coupling p (fun _ y => F y)
    _ = _ := by rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

theorem restrictionAvg_mask_sampler (p : ℝ) (F : Restriction V → ℝ) :
    restrictionAvg p F = ∑ T : Finset V, bernoulliWeight p T *
      finiteAvg (fun y : Cube V => F (maskRestriction T y)) := by
  simpa only [finiteAvg_const] using
    restrictionAvg_fill_coupling p (fun σ _ => F σ)

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

theorem finiteProb_eq_card_div {Ω : Type uDepth1} [Fintype Ω] (P : Ω → Prop) :
    finiteProb P = (Fintype.card {ω // P ω} : ℝ) / Fintype.card Ω := by
  simp [finiteProb, finiteAvg, Fintype.card_subtype, div_eq_mul_inv, mul_comm]

private theorem finiteProb_eq_card_div_decidable {Ω : Type uDepth2} [Fintype Ω]
    (P : Ω → Prop) [DecidablePred P] :
    finiteProb P = (Fintype.card {ω // P ω} : ℝ) / Fintype.card Ω := by
  rw [finiteProb_eq_card_div]
  exact congrArg (fun k : ℕ => (k : ℝ) / Fintype.card Ω)
    (congrArg (@Fintype.card {ω // P ω}) (Subsingleton.elim _ _))

namespace BinaryHash

variable {d r : ℕ}

private theorem normalize_hash_count (hd : 0 < d) (c : ℝ) :
    c * (2 : ℝ) ^ (d - 1) / (2 : ℝ) ^ (d + r - 1) = c / (2 : ℝ) ^ r := by
  have he : d + r - 1 = (d - 1) + r := by omega
  rw [he, pow_add, mul_comm c]
  exact mul_div_mul_left c _ (pow_ne_zero _ (by norm_num))

theorem hashBool_fiber_probability (x : Fin d → Bool)
    (hx : x ≠ fun _ => false) (a : Fin r → Bool) :
    finiteProb (fun u : Fin (d + r - 1) → Bool => hashBool u x = a) =
      ((2 : ℝ) ^ r)⁻¹ := by
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    subst d
    exact hx (Subsingleton.elim _ _)
  rw [finiteProb_eq_card_div_decidable
    (fun u : Fin (d + r - 1) → Bool => hashBool u x = a), hashBool_fiber_card x hx]
  have hc : (Fintype.card (Fin (d + r - 1) → Bool) : ℝ) =
      (2 : ℝ) ^ (d + r - 1) := by simp []
  rw [hc]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  simpa only [one_mul, one_div] using normalize_hash_count (r := r) hd 1

theorem hashBool_collision_probability (x y : Fin d → Bool) (hxy : x ≠ y) :
    finiteProb (fun u : Fin (d + r - 1) → Bool => hashBool u x = hashBool u y) =
      ((2 : ℝ) ^ r)⁻¹ := by
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    subst d
    exact hxy (Subsingleton.elim _ _)
  rw [finiteProb_eq_card_div_decidable
    (fun u : Fin (d + r - 1) → Bool => hashBool u x = hashBool u y),
    hashBool_collision_card x y hxy]
  have hc : (Fintype.card (Fin (d + r - 1) → Bool) : ℝ) =
      (2 : ℝ) ^ (d + r - 1) := by simp []
  rw [hc]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  simpa only [one_mul, one_div] using normalize_hash_count (r := r) hd 1

theorem hashBool_badSeed_probability_le (T : Finset (Fin d))
    (rho : {i : Fin d // i ∉ T} → Bool) :
    finiteProb (fun u : Fin (d + r - 1) → Bool =>
      ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)) ≤
        ((2 : ℝ) ^ T.card - 1) / (2 : ℝ) ^ r := by
  by_cases hd0 : d = 0
  · subst d
    have hT : T = ∅ := by
      ext i
      exact Fin.elim0 i
    have hinj (u : Fin (0 + r - 1) → Bool) :
        Set.InjOn (hashBool u) (boolCoordinateCube T rho) := by
      intro x hx y hy hxy
      exact Subsingleton.elim _ _
    simp [finiteProb, hinj, hT]
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  have hcount := hashBool_badSeed_card_le (r := r) T rho
  have hcast :
      (Fintype.card {u : Fin (d + r - 1) → Bool //
        ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)} : ℝ) ≤
      ((2 : ℕ) ^ T.card - 1 : ℕ) * (2 : ℝ) ^ (d - 1) := by
    exact_mod_cast hcount
  have hpow : 1 ≤ (2 : ℕ) ^ T.card := by
    have hp : 0 < (2 : ℕ) ^ T.card := pow_pos (by decide) _
    omega
  have hsub : (((2 : ℕ) ^ T.card - 1 : ℕ) : ℝ) =
      (2 : ℝ) ^ T.card - 1 := by
    rw [Nat.cast_sub hpow]
    simp
  have hc : (Fintype.card (Fin (d + r - 1) → Bool) : ℝ) =
      (2 : ℝ) ^ (d + r - 1) := by simp []
  rw [hsub] at hcast
  rw [finiteProb_eq_card_div_decidable
    (fun u : Fin (d + r - 1) → Bool =>
      ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)), hc]
  calc
    _ ≤ (((2 : ℝ) ^ T.card - 1) * (2 : ℝ) ^ (d - 1)) /
        (2 : ℝ) ^ (d + r - 1) :=
      div_le_div_of_nonneg_right hcast (by positivity)
    _ = _ := normalize_hash_count hd _

theorem hashBool_badSeed_probability_le_pow (T : Finset (Fin d))
    (rho : {i : Fin d // i ∉ T} → Bool) :
    finiteProb (fun u : Fin (d + r - 1) → Bool =>
      ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)) ≤
        (2 : ℝ) ^ T.card / (2 : ℝ) ^ r := by
  exact (hashBool_badSeed_probability_le T rho).trans
    (div_le_div_of_nonneg_right (by linarith) (by positivity))

def restrictionFixed (σ : Restriction (Fin d)) :
    {i : Fin d // i ∉ liveSet σ} → Bool :=
  fun i => (σ i.val).getD false

theorem fill_mem_boolCoordinateCube (σ : Restriction (Fin d)) (z : Cube (Live σ)) :
    fill σ z ∈ boolCoordinateCube (liveSet σ) (restrictionFixed σ) := by
  intro i hi
  have hn : σ i ≠ none := fun h => hi ((mem_liveSet σ i).mpr h)
  simp [fill, hn, restrictionFixed]

theorem range_fill_eq_boolCoordinateCube (σ : Restriction (Fin d)) :
    Set.range (fill σ) = boolCoordinateCube (liveSet σ) (restrictionFixed σ) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact fill_mem_boolCoordinateCube σ z
  · intro hx
    refine ⟨fun v => x v.val, ?_⟩
    funext i
    by_cases hi : σ i = none
    · simp [fill, hi]
    · have hnot : i ∉ liveSet σ := fun h => hi ((mem_liveSet σ i).mp h)
      simpa [fill, hi, restrictionFixed] using (hx i hnot).symm

theorem fill_injective (σ : Restriction (Fin d)) : Function.Injective (fill σ) := by
  intro z w h
  funext v
  simpa only [fill_live] using congrFun h v.val

theorem hashBool_fill_injective_iff (σ : Restriction (Fin d))
    (u : Fin (d + r - 1) → Bool) :
    Function.Injective (fun z : Cube (Live σ) => hashBool u (fill σ z)) ↔
      Set.InjOn (hashBool u) (boolCoordinateCube (liveSet σ) (restrictionFixed σ)) := by
  constructor
  · intro h x hx y hy hxy
    rw [← range_fill_eq_boolCoordinateCube] at hx hy
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    exact congrArg (fill σ) (h hxy)
  · intro h z w hzw
    apply fill_injective σ
    exact h (fill_mem_boolCoordinateCube σ z) (fill_mem_boolCoordinateCube σ w) hzw

theorem card_liveSet (σ : Restriction (Fin d)) :
    (liveSet σ).card = Fintype.card (Live σ) := by
  let e : Live σ ≃ ↥(liveSet σ) :=
    Equiv.subtypeEquivRight (fun i => (mem_liveSet σ i).symm)
  exact ((Fintype.card_congr e).trans (Fintype.card_coe (liveSet σ))).symm

theorem hashBool_restriction_failure_le (σ : Restriction (Fin d)) :
    finiteProb (fun u : Fin (d + r - 1) → Bool =>
      ¬ Function.Injective (fun z : Cube (Live σ) => hashBool u (fill σ z))) ≤
        ((2 : ℝ) ^ Fintype.card (Live σ) - 1) / (2 : ℝ) ^ r := by
  have he : finiteProb (fun u : Fin (d + r - 1) → Bool =>
      ¬ Function.Injective (fun z : Cube (Live σ) => hashBool u (fill σ z))) =
      finiteProb (fun u : Fin (d + r - 1) → Bool =>
        ¬ Set.InjOn (hashBool u) (boolCoordinateCube (liveSet σ) (restrictionFixed σ))) := by
    apply finiteAvg_congr
    intro u
    by_cases h : Set.InjOn (hashBool u) (boolCoordinateCube (liveSet σ) (restrictionFixed σ))
    · have h' := (hashBool_fill_injective_iff σ u).mpr h
      simp [h, h']
    · have h' := mt (hashBool_fill_injective_iff σ u).mp h
      simp [h, h']
  rw [he]
  simpa only [card_liveSet] using
    hashBool_badSeed_probability_le (r := r) (liveSet σ) (restrictionFixed σ)

theorem hashBool_restriction_failure_le_pow (σ : Restriction (Fin d)) :
    finiteProb (fun u : Fin (d + r - 1) → Bool =>
      ¬ Function.Injective (fun z : Cube (Live σ) => hashBool u (fill σ z))) ≤
        (2 : ℝ) ^ Fintype.card (Live σ) / (2 : ℝ) ^ r := by
  exact (hashBool_restriction_failure_le σ).trans
    (div_le_div_of_nonneg_right (by linarith) (by positivity))

end BinaryHash
end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators
open Polynomial

namespace DepthThreeLowerBound.BinaryAlgebra

def quotientRepresentative {P : Polynomial F2} (hP : P.Monic) :
    AdjoinRoot P →ₗ[F2] Polynomial F2 :=
  AdjoinRoot.modByMonicHom hP

@[simp] theorem quotientRepresentative_mk {P : Polynomial F2} (hP : P.Monic)
    (f : Polynomial F2) :
    quotientRepresentative hP (AdjoinRoot.mk P f) = f %ₘ P :=
  AdjoinRoot.modByMonicHom_mk hP f

theorem mk_quotientRepresentative {P : Polynomial F2} (hP : P.Monic)
    (z : AdjoinRoot P) :
    AdjoinRoot.mk P (quotientRepresentative hP z) = z :=
  AdjoinRoot.mk_leftInverse hP z

theorem degree_quotientRepresentative_lt {P : Polynomial F2} (hP : P.Monic)
    (z : AdjoinRoot P) :
    (quotientRepresentative hP z).degree < P.degree := by
  refine AdjoinRoot.induction_on P z ?_
  intro f
  rw [quotientRepresentative_mk]
  exact Polynomial.degree_modByMonic_lt f hP

theorem quotientRepresentative_one {P : Polynomial F2} (hP : P.Monic)
    (hdeg : 0 < P.natDegree) :
    quotientRepresentative hP (1 : AdjoinRoot P) = 1 := by
  have h : (1 : Polynomial F2).degree < P.degree := by
    rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree hP.ne_zero]
    exact WithBot.coe_lt_coe.mpr hdeg
  calc
    quotientRepresentative hP (1 : AdjoinRoot P) =
        quotientRepresentative hP (AdjoinRoot.mk P 1) := by rw [(AdjoinRoot.mk P).map_one]
    _ = (1 : Polynomial F2) %ₘ P := quotientRepresentative_mk hP 1
    _ = 1 := (Polynomial.modByMonic_eq_self_iff hP).mpr h

abbrev InputQuotient {r : ℕ} (p : Fin r → F2) :=
  AdjoinRoot (inputPolynomial p)

abbrev BitQuotient {r : ℕ} (p : Fin r → Bool) :=
  InputQuotient (fun i => bitValue (p i))

theorem pack_mod_inputPolynomial {r : ℕ} (p a : Fin r → F2) :
    pack a %ₘ inputPolynomial p = pack a := by
  apply (Polynomial.modByMonic_eq_self_iff (inputPolynomial_monic p)).mpr
  rw [inputPolynomial_degree]
  exact degree_pack_lt a

def encode {r : ℕ} (p : Fin r → F2) (a : Fin r → F2) : InputQuotient p :=
  AdjoinRoot.mk (inputPolynomial p) (pack a)

def coordinates {r : ℕ} (p : Fin r → F2) :
    InputQuotient p ≃ₗ[F2] (Fin r → F2) where
  toFun z i := (quotientRepresentative (inputPolynomial_monic p) z).coeff i.val
  invFun := encode p
  map_add' x y := by
    funext i
    simp only [map_add, Polynomial.coeff_add, Pi.add_apply]
  map_smul' c x := by
    funext i
    simp only [map_smul, Polynomial.coeff_smul, Pi.smul_apply, RingHom.id_apply]
  left_inv z := by
    have hd : (quotientRepresentative (inputPolynomial_monic p) z).degree <
        (r : WithBot ℕ) := by
      simpa only [inputPolynomial_degree] using
        degree_quotientRepresentative_lt (inputPolynomial_monic p) z
    change AdjoinRoot.mk (inputPolynomial p)
      (pack (fun i : Fin r =>
        (quotientRepresentative (inputPolynomial_monic p) z).coeff i.val)) = z
    rw [pack_coeff_of_degree_lt _ hd]
    exact mk_quotientRepresentative (inputPolynomial_monic p) z
  right_inv a := by
    funext i
    change (quotientRepresentative (inputPolynomial_monic p)
      (AdjoinRoot.mk (inputPolynomial p) (pack a))).coeff i.val = a i
    rw [quotientRepresentative_mk, pack_mod_inputPolynomial, coeff_pack]

@[simp] theorem coordinates_apply {r : ℕ} (p : Fin r → F2)
    (z : InputQuotient p) (i : Fin r) :
    coordinates p z i =
      (quotientRepresentative (inputPolynomial_monic p) z).coeff i.val := rfl

@[simp] theorem coordinates_symm_apply {r : ℕ} (p a : Fin r → F2) :
    (coordinates p).symm a = encode p a := rfl

@[simp] theorem coordinates_encode {r : ℕ} (p a : Fin r → F2) :
    coordinates p (encode p a) = a :=
  (coordinates p).apply_symm_apply a

@[simp] theorem encode_coordinates {r : ℕ} (p : Fin r → F2) (z : InputQuotient p) :
    encode p (coordinates p z) = z :=
  (coordinates p).symm_apply_apply z

theorem encode_injective {r : ℕ} (p : Fin r → F2) : Function.Injective (encode p) :=
  (coordinates p).symm.injective

theorem encode_surjective {r : ℕ} (p : Fin r → F2) : Function.Surjective (encode p) :=
  (coordinates p).symm.surjective

instance inputQuotientFintype {r : ℕ} (p : Fin r → F2) : Fintype (InputQuotient p) :=
  Fintype.ofEquiv (Fin r → F2) (coordinates p).toEquiv.symm

@[simp] theorem inputQuotient_card {r : ℕ} (p : Fin r → F2) :
    Fintype.card (InputQuotient p) = 2 ^ r := by
  rw [Fintype.card_congr (coordinates p).toEquiv, Fintype.card_fun,
    ZMod.card, Fintype.card_fin]

@[simp] theorem bitQuotient_card {r : ℕ} (p : Fin r → Bool) :
    Fintype.card (BitQuotient p) = 2 ^ r :=
  inputQuotient_card _

@[simp] theorem coordinates_mk {r : ℕ} (p : Fin r → F2)
    (f : Polynomial F2) (i : Fin r) :
    coordinates p (AdjoinRoot.mk (inputPolynomial p) f) i =
      (f %ₘ inputPolynomial p).coeff i.val := by
  rw [coordinates_apply, quotientRepresentative_mk]

@[simp] theorem encode_zero {r : ℕ} (p : Fin r → F2) :
    encode p (0 : Fin r → F2) = 0 := by
  rw [encode, pack_zero, map_zero]

@[simp] theorem encode_add {r : ℕ} (p a b : Fin r → F2) :
    encode p (a + b) = encode p a + encode p b := by
  simp only [encode, pack_add, map_add]

@[simp] theorem encode_smul {r : ℕ} (p : Fin r → F2) (c : F2) (a : Fin r → F2) :
    encode p (c • a) = c • encode p a := by
  change AdjoinRoot.mk (inputPolynomial p) (pack (c • a)) =
    c • AdjoinRoot.mk (inputPolynomial p) (pack a)
  rw [pack_smul, AdjoinRoot.smul_mk]

theorem coordinates_encode_mul {r : ℕ} (p a b : Fin r → F2) (i : Fin r) :
    coordinates p (encode p a * encode p b) i =
      ((pack a * pack b) %ₘ inputPolynomial p).coeff i.val := by
  change coordinates p
    (AdjoinRoot.mk (inputPolynomial p) (pack a) *
      AdjoinRoot.mk (inputPolynomial p) (pack b)) i = _
  rw [← map_mul, coordinates_mk]

theorem encode_mul {r : ℕ} (p a b : Fin r → F2) :
    encode p (fun i => ((pack a * pack b) %ₘ inputPolynomial p).coeff i.val) =
      encode p a * encode p b := by
  apply (coordinates p).injective
  rw [coordinates_encode]
  funext i
  exact (coordinates_encode_mul p a b i).symm

theorem coordinates_mul {r : ℕ} (p : Fin r → F2) (x y : InputQuotient p) (i : Fin r) :
    coordinates p (x * y) i =
      ((pack (coordinates p x) * pack (coordinates p y)) %ₘ inputPolynomial p).coeff i.val := by
  simpa only [encode_coordinates] using
    coordinates_encode_mul p (coordinates p x) (coordinates p y) i

theorem coordinates_one {r : ℕ} (p : Fin r → F2) (hr : 0 < r) (i : Fin r) :
    coordinates p (1 : InputQuotient p) i = if i.val = 0 then 1 else 0 := by
  rw [coordinates_apply, quotientRepresentative_one (inputPolynomial_monic p)
    (by simpa only [inputPolynomial_natDegree] using hr), Polynomial.coeff_one]

def degreeZero {P : Polynomial F2} (hP : P.Monic) : AdjoinRoot P →ₗ[F2] F2 :=
  (Polynomial.lcoeff F2 0).comp (quotientRepresentative hP)

@[simp] theorem degreeZero_apply {P : Polynomial F2} (hP : P.Monic)
    (z : AdjoinRoot P) :
    degreeZero hP z = (quotientRepresentative hP z).coeff 0 := rfl

@[simp] theorem degreeZero_mk {P : Polynomial F2} (hP : P.Monic) (f : Polynomial F2) :
    degreeZero hP (AdjoinRoot.mk P f) = (f %ₘ P).coeff 0 := by
  rw [degreeZero_apply, quotientRepresentative_mk]

theorem degreeZero_one {P : Polynomial F2} (hP : P.Monic) (hdeg : 0 < P.natDegree) :
    degreeZero hP (1 : AdjoinRoot P) = 1 := by
  rw [degreeZero_apply, quotientRepresentative_one hP hdeg, Polynomial.coeff_one_zero]

theorem degreeZero_surjective {P : Polynomial F2} (hP : P.Monic)
    (hdeg : 0 < P.natDegree) : Function.Surjective (degreeZero hP) := by
  intro c
  refine ⟨c • (1 : AdjoinRoot P), ?_⟩
  rw [map_smul, degreeZero_one hP hdeg, smul_eq_mul, mul_one]

theorem degreeZero_encode {r : ℕ} (p : Fin r → F2) (hr : 0 < r) (a : Fin r → F2) :
    degreeZero (inputPolynomial_monic p) (encode p a) = a ⟨0, hr⟩ := by
  rw [encode, degreeZero_mk, pack_mod_inputPolynomial]
  exact coeff_pack a ⟨0, hr⟩

theorem degreeZero_coordinates {r : ℕ} (p : Fin r → F2) (hr : 0 < r)
    (z : InputQuotient p) :
    degreeZero (inputPolynomial_monic p) z = coordinates p z ⟨0, hr⟩ := rfl

theorem degreeZero_sum_encode_pow {r t : ℕ} (p a : Fin r → F2)
    (beta : Fin t → Fin r → F2) :
    degreeZero (inputPolynomial_monic p)
        (∑ j : Fin t, encode p (beta j) * (encode p a) ^ j.val) =
      ((∑ j : Fin t, pack (beta j) * (pack a) ^ j.val) %ₘ inputPolynomial p).coeff 0 := by
  rw [← degreeZero_mk (inputPolynomial_monic p)
    (∑ j : Fin t, pack (beta j) * (pack a) ^ j.val)]
  congr 1
  simp only [encode, map_sum, map_mul, map_pow]

end DepthThreeLowerBound.BinaryAlgebra

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

def hardSliceSparseConstant (b : ℕ) (hb : 1 ≤ b) : ℕ :=
  Classical.choose (exists_sparse_correlation_constant.{0} b hb)

theorem hardSliceSparseConstant_pos (b : ℕ) (hb : 1 ≤ b) :
    0 < hardSliceSparseConstant b hb :=
  (Classical.choose_spec (exists_sparse_correlation_constant.{0} b hb)).1

theorem hardSliceSparseConstant_spec (b : ℕ) (hb : 1 ≤ b)
    (V : Type) [Fintype V] [DecidableEq V] (G : Cube V → ℝ)
    (htests : ∀ H : CNF V, H.Normalized → H.WidthAtMost b →
      H.length ≤ hardSliceSparseConstant b hb * Fintype.card V →
      |finiteAvg (fun x => G x * indicator (H.eval x))| ≤
        (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4)) :
    corr b G ≤ (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 8) :=
  (Classical.choose_spec (exists_sparse_correlation_constant.{0} b hb)).2 V G htests

theorem sparseMomentBound_nonneg (m b L h : ℕ) (δ : ℝ) :
    0 ≤ sparseMomentBound m b L h δ := by
  unfold sparseMomentBound
  apply mul_nonneg (Nat.cast_nonneg _)
  apply div_nonneg
  · positivity
  · rw [pow_mul]
    exact pow_nonneg (sq_nonneg (δ * ((2 ^ m : ℕ) : ℝ))) h

theorem coefficient_corr_failure_le {F V : Type} [Field F]
    [Module BinaryAlgebra.F2 F] [Fintype F] [Fintype V]
    (ell : F →ₗ[BinaryAlgebra.F2] BinaryAlgebra.F2) (hOne : ell 1 = 1)
    (a : Cube V → F) (ha : Function.Injective a)
    (b : ℕ) (hb : 1 ≤ b) (h : ℕ) (hh : 0 < h) :
    finiteProb (fun β : Fin (2 * h) → F =>
      ¬ corr b (fun x => sign (Interpolation.acceptEval ell (2 * h) a β x)) ≤
        (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 8)) ≤
      sparseMomentBound (Fintype.card V) b
        (hardSliceSparseConstant b hb * Fintype.card V) h
        ((2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4)) := by
  apply le_trans _ (coefficient_sparse_cnfs_gt_le ell hOne a ha b
    (hardSliceSparseConstant b hb * Fintype.card V) h hh
    ((2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4)) (Real.rpow_pos_of_pos (by norm_num) _))
  apply finiteProb_mono
  intro β hβ
  by_contra hnone
  apply hβ
  apply hardSliceSparseConstant_spec b hb V
  intro H _ hw hlen
  by_contra hfail
  exact hnone ⟨H, hw, hlen, lt_of_not_ge hfail⟩

theorem hash_coefficient_corr_failure_le {F V U : Type} [Field F]
    [Module BinaryAlgebra.F2 F] [Fintype F] [Fintype V]
    [Fintype U] [Nonempty U]
    (ell : F →ₗ[BinaryAlgebra.F2] BinaryAlgebra.F2) (hOne : ell 1 = 1)
    (a : U → Cube V → F) (b : ℕ) (hb : 1 ≤ b) (h : ℕ) (hh : 0 < h) :
    finiteProb (fun ω : U × (Fin (2 * h) → F) =>
      ¬ corr b (fun x => sign (Interpolation.acceptEval ell (2 * h) (a ω.1) ω.2 x)) ≤
        (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 8)) ≤
      finiteProb (fun u => ¬ Function.Injective (a u)) +
        sparseMomentBound (Fintype.card V) b
          (hardSliceSparseConstant b hb * Fintype.card V) h
          ((2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4)) := by
  let B := sparseMomentBound (Fintype.card V) b
    (hardSliceSparseConstant b hb * Fintype.card V) h
    ((2 : ℝ) ^ (-(Fintype.card V : ℝ) / 4))
  have hB : 0 ≤ B := sparseMomentBound_nonneg _ _ _ _ _
  change finiteAvg _ ≤ finiteProb _ + B
  rw [finiteAvg_product]
  calc
    _ ≤ finiteAvg (fun u : U => (if ¬ Function.Injective (a u) then 1 else 0) + B) := by
      apply finiteAvg_mono
      intro u
      by_cases hu : Function.Injective (a u)
      · simpa only [finiteProb, B, hu, not_true_eq_false, ite_false, zero_add] using
          coefficient_corr_failure_le ell hOne (a u) hu b hb h hh
      · have hone := finiteProb_le_one (fun β : Fin (2 * h) → F =>
          ¬ corr b (fun x => sign (Interpolation.acceptEval ell (2 * h) (a u) β x)) ≤
            (2 : ℝ) ^ (-(Fintype.card V : ℝ) / 8))
        simpa only [finiteProb, hu, not_false_eq_true, ite_true] using
          hone.trans (le_add_of_nonneg_right hB)
    _ = finiteProb (fun u => ¬ Function.Injective (a u)) + B := by
      rw [finiteAvg_add, finiteAvg_const]
      apply congrArg (fun z : ℝ => z + B)
      apply finiteAvg_congr
      intro u
      exact (ite_eq_ite _ _ _).mpr trivial

def encodedHash {d r : ℕ} (p : Fin r → Bool)
    (u : Fin (d + r - 1) → Bool) (x : Cube (Fin d)) : BinaryAlgebra.BitQuotient p :=
  BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
    (fun i => BinaryAlgebra.bitValue (BinaryHash.hashBool u x i))

theorem encodedHash_fill_injective {d r : ℕ} (p : Fin r → Bool)
    (u : Fin (d + r - 1) → Bool) (σ : Restriction (Fin d))
    (hu : Function.Injective (fun z : Cube (Live σ) => BinaryHash.hashBool u (fill σ z))) :
    Function.Injective (fun z : Cube (Live σ) => encodedHash p u (fill σ z)) := by
  intro x y hxy
  apply hu
  apply (BinaryAlgebra.bitsEquivF2 (Fin r)).injective
  exact BinaryAlgebra.encode_injective _ hxy

def hashAcceptance {d r : ℕ} (p : Fin r → Bool)
    [Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p))]
    (t : ℕ) (u : Fin (d + r - 1) → Bool)
    (β : Fin t → BinaryAlgebra.BitQuotient p) : Cube (Fin d) → Bool :=
  Interpolation.acceptEval
    (BinaryAlgebra.degreeZero (BinaryAlgebra.inputPolynomialBits_monic p)) t
    (encodedHash p u) β

theorem actual_hash_coefficient_failure_le {d r : ℕ} (p : Fin r → Bool)
    [Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p))]
    (hr : 0 < r) (σ : Restriction (Fin d))
    (b : ℕ) (hb : 1 ≤ b) (h : ℕ) (hh : 0 < h) :
    finiteProb (fun ω : (Fin (d + r - 1) → Bool) ×
        (Fin (2 * h) → BinaryAlgebra.BitQuotient p) =>
      ¬ corr b (fun z => sign (hashAcceptance p (2 * h) ω.1 ω.2 (fill σ z))) ≤
        (2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ) / 8)) ≤
      (2 : ℝ) ^ Fintype.card (Live σ) / (2 : ℝ) ^ r +
        sparseMomentBound (Fintype.card (Live σ)) b
          (hardSliceSparseConstant b hb * Fintype.card (Live σ)) h
          ((2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ) / 4)) := by
  let : Field (BinaryAlgebra.BitQuotient p) :=
    AdjoinRoot.instField (f := BinaryAlgebra.inputPolynomialBits p)
  let : Module BinaryAlgebra.F2 (BinaryAlgebra.BitQuotient p) :=
    inferInstanceAs (Module BinaryAlgebra.F2
      (AdjoinRoot (BinaryAlgebra.inputPolynomialBits p)))
  have hOne : BinaryAlgebra.degreeZero (BinaryAlgebra.inputPolynomialBits_monic p)
      (1 : BinaryAlgebra.BitQuotient p) = 1 :=
    BinaryAlgebra.degreeZero_one _ (by simpa using hr)
  have hhash : finiteProb (fun u : Fin (d + r - 1) → Bool =>
      ¬ Function.Injective (fun z : Cube (Live σ) => encodedHash p u (fill σ z))) ≤
      (2 : ℝ) ^ Fintype.card (Live σ) / (2 : ℝ) ^ r := by
    apply le_trans _ (BinaryHash.hashBool_restriction_failure_le_pow (r := r) σ)
    apply finiteProb_mono
    intro u hu hinj
    exact hu (encodedHash_fill_injective p u σ hinj)
  exact (hash_coefficient_corr_failure_le (F := BinaryAlgebra.BitQuotient p)
    (V := Live σ) (U := Fin (d + r - 1) → Bool)
    (BinaryAlgebra.degreeZero (BinaryAlgebra.inputPolynomialBits_monic p)) hOne
    (fun u z => encodedHash p u (fill σ z)) b hb h hh).trans
      (add_le_add_left hhash _)

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V] [DecidableEq V]

theorem restrictionAvg_pow_card_live (p a : ℝ) :
    restrictionAvg p (fun σ : Restriction V => a ^ Fintype.card (Live σ)) =
      (1 - p + p * a) ^ Fintype.card V := by
  rw [restrictionAvg_mask_sampler]
  calc
    _ = ∑ T : Finset V, (p * a) ^ T.card *
        (1 - p) ^ (Fintype.card V - T.card) := by
      apply Finset.sum_congr rfl
      intro T hT
      simp only [card_live_maskRestriction, finiteAvg_const, bernoulliWeight, mul_pow]
      ring
    _ = (p * a + (1 - p)) ^ Fintype.card V := by
      simpa only [Finset.prod_const, Finset.card_compl, Finset.card_univ] using
        (Fintype.prod_add (fun _ : V => p * a) (fun _ : V => 1 - p)).symm
    _ = _ := by congr 1 ; ring

theorem restrictionAvg_two_pow_live (p : ℝ) :
    restrictionAvg p (fun σ : Restriction V =>
      (2 : ℝ) ^ (Fintype.card (Live σ) : ℝ)) = (1 + p) ^ Fintype.card V := by
  calc
    _ = (1 - p + p * 2) ^ Fintype.card V := by
      simpa only [Real.rpow_natCast] using restrictionAvg_pow_card_live (V := V) p 2
    _ = _ := by congr 1 ; ring

theorem restrictionAvg_two_neg_pow_live (p : ℝ) :
    restrictionAvg p (fun σ : Restriction V =>
      (2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ))) = (1 - p / 2) ^ Fintype.card V := by
  simp_rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, ← inv_pow]
  rw [restrictionAvg_pow_card_live]
  congr 1 ; ring

theorem one_add_pow_le_exp (p : ℝ) (hp : 0 ≤ p) (n : ℕ) :
    (1 + p) ^ n ≤ Real.exp (p * n) := by
  calc
    _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (by linarith)
      (by linarith [Real.add_one_le_exp p]) n
    _ = Real.exp (p * n) := by rw [← Real.exp_nat_mul]; congr 1 ; ring

theorem one_sub_half_pow_le_exp (p : ℝ) (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p / 2) ^ n ≤ Real.exp (-(p * n) / 2) := by
  calc
    _ ≤ (Real.exp (-(p / 2))) ^ n := pow_le_pow_left₀ (by linarith)
      (Real.one_sub_le_exp_neg (p / 2)) n
    _ = Real.exp (-(p * n) / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1 ; ring

private theorem lower_tail_exponent (μ : ℝ) (hμ : 0 ≤ μ) :
    (2 : ℝ) ^ (μ / 2) * Real.exp (-μ / 2) ≤ (2 : ℝ) ^ (-μ / 16) := by
  simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log 2 ≤ (3 / 4 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hmul := mul_le_mul_of_nonneg_left hlog hμ
  nlinarith

private theorem upper_tail_exponent (μ : ℝ) (hμ : 0 ≤ μ) :
    (2 : ℝ) ^ (-(2 * μ)) * Real.exp μ ≤ (2 : ℝ) ^ (-μ / 16) := by
  simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmul := mul_le_mul_of_nonneg_left hlog hμ
  nlinarith

theorem restrictionAvg_lower_tail (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    restrictionAvg p (fun σ : Restriction V =>
      if (Fintype.card (Live σ) : ℝ) < (p * Fintype.card V) / 2 then 1 else 0) ≤
      (2 : ℝ) ^ (-(p * Fintype.card V) / 16) := by
  let μ : ℝ := p * Fintype.card V
  have hμ : 0 ≤ μ := mul_nonneg hp (Nat.cast_nonneg _)
  have hmajor : ∀ σ : Restriction V,
      (if (Fintype.card (Live σ) : ℝ) < μ / 2 then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (μ / 2) * (2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ)) := by
    intro σ
    by_cases hσ : (Fintype.card (Live σ) : ℝ) < μ / 2
    · rw [ite_eq_left hσ, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      exact Real.one_le_rpow (by norm_num) (by linarith)
    · rw [ite_eq_right hσ]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (by norm_num) _)
  calc
    _ ≤ restrictionAvg p (fun σ : Restriction V =>
        (2 : ℝ) ^ (μ / 2) * (2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ))) :=
      restrictionAvg_mono hp hp1 hmajor
    _ = (2 : ℝ) ^ (μ / 2) * (1 - p / 2) ^ Fintype.card V := by
      rw [restrictionAvg_const_mul, restrictionAvg_two_neg_pow_live]
    _ ≤ (2 : ℝ) ^ (μ / 2) * Real.exp (-μ / 2) :=
      mul_le_mul_of_nonneg_left (one_sub_half_pow_le_exp p hp1 _)
        (Real.rpow_nonneg (by norm_num) _)
    _ ≤ _ := lower_tail_exponent μ hμ

theorem restrictionAvg_upper_tail (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    restrictionAvg p (fun σ : Restriction V =>
      if 2 * (p * Fintype.card V) < (Fintype.card (Live σ) : ℝ) then 1 else 0) ≤
      (2 : ℝ) ^ (-(p * Fintype.card V) / 16) := by
  let μ : ℝ := p * Fintype.card V
  have hμ : 0 ≤ μ := mul_nonneg hp (Nat.cast_nonneg _)
  have hmajor : ∀ σ : Restriction V,
      (if 2 * μ < (Fintype.card (Live σ) : ℝ) then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-(2 * μ)) * (2 : ℝ) ^ (Fintype.card (Live σ) : ℝ) := by
    intro σ
    by_cases hσ : 2 * μ < (Fintype.card (Live σ) : ℝ)
    · rw [ite_eq_left hσ, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      exact Real.one_le_rpow (by norm_num) (by linarith)
    · rw [ite_eq_right hσ]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (by norm_num) _)
  calc
    _ ≤ restrictionAvg p (fun σ : Restriction V =>
        (2 : ℝ) ^ (-(2 * μ)) * (2 : ℝ) ^ (Fintype.card (Live σ) : ℝ)) :=
      restrictionAvg_mono hp hp1 hmajor
    _ = (2 : ℝ) ^ (-(2 * μ)) * (1 + p) ^ Fintype.card V := by
      rw [restrictionAvg_const_mul, restrictionAvg_two_pow_live]
    _ ≤ (2 : ℝ) ^ (-(2 * μ)) * Real.exp μ :=
      mul_le_mul_of_nonneg_left (one_add_pow_le_exp p hp _)
        (Real.rpow_nonneg (by norm_num) _)
    _ ≤ _ := upper_tail_exponent μ hμ

theorem restrictionAvg_outside_window (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    restrictionAvg p (fun σ : Restriction V =>
      if ¬((p * Fintype.card V) / 2 ≤ (Fintype.card (Live σ) : ℝ) ∧
        (Fintype.card (Live σ) : ℝ) ≤ 2 * (p * Fintype.card V)) then 1 else 0) ≤
      2 * (2 : ℝ) ^ (-(p * Fintype.card V) / 16) := by
  let μ : ℝ := p * Fintype.card V
  have hsplit : ∀ σ : Restriction V,
      (if ¬(μ / 2 ≤ (Fintype.card (Live σ) : ℝ) ∧
        (Fintype.card (Live σ) : ℝ) ≤ 2 * μ) then (1 : ℝ) else 0) ≤
      (if (Fintype.card (Live σ) : ℝ) < μ / 2 then (1 : ℝ) else 0) +
        (if 2 * μ < (Fintype.card (Live σ) : ℝ) then (1 : ℝ) else 0) := by
    intro σ
    by_cases hlo : (Fintype.card (Live σ) : ℝ) < μ / 2
    · by_cases hhi : 2 * μ < (Fintype.card (Live σ) : ℝ) <;>
        simp [hlo, hhi, not_le.mpr hlo]
    · have hlo' := le_of_not_gt hlo
      by_cases hhi : 2 * μ < (Fintype.card (Live σ) : ℝ)
      · simp [hlo, hhi, not_le.mpr hhi]
      · simp [hlo, hhi, hlo', le_of_not_gt hhi]
  calc
    _ ≤ restrictionAvg p (fun σ : Restriction V =>
        (if (Fintype.card (Live σ) : ℝ) < μ / 2 then (1 : ℝ) else 0) +
          (if 2 * μ < (Fintype.card (Live σ) : ℝ) then (1 : ℝ) else 0)) :=
      restrictionAvg_mono hp hp1 hsplit
    _ = restrictionAvg p (fun σ : Restriction V =>
          if (Fintype.card (Live σ) : ℝ) < μ / 2 then 1 else 0) +
        restrictionAvg p (fun σ : Restriction V =>
          if 2 * μ < (Fintype.card (Live σ) : ℝ) then 1 else 0) :=
      restrictionAvg_add p _ _
    _ ≤ (2 : ℝ) ^ (-μ / 16) + (2 : ℝ) ^ (-μ / 16) :=
      add_le_add (restrictionAvg_lower_tail p hp hp1) (restrictionAvg_upper_tail p hp hp1)
    _ = _ := by ring

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {Ω : Type uDepth2} [Fintype V] [instDecidableEqV : DecidableEq V]
  [Fintype Ω] [Nonempty Ω]

theorem exists_small_restriction_failure
    {V : Type uDepth1}
    {Ω : Type uDepth2}
    [Fintype V]
    [DecidableEq V]
    [Fintype Ω]
    [Nonempty Ω]
    {p δ η : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    (window : Restriction V → Prop) (good : Ω → Restriction V → Prop)
    (hfixed : ∀ σ, window σ → finiteProb (fun ω => ¬ good ω σ) ≤ δ)
    (hwindow : restrictionAvg p (fun σ => if ¬ window σ then 1 else 0) ≤ η) :
    ∃ ω : Ω,
      restrictionAvg p (fun σ => if ¬ (window σ ∧ good ω σ) then 1 else 0) ≤ η + δ := by
  have hpoint : ∀ σ : Restriction V,
      finiteAvg (fun ω : Ω => if ¬ (window σ ∧ good ω σ) then (1 : ℝ) else 0) ≤
        (if ¬ window σ then 1 else 0) + δ := by
    intro σ
    by_cases hσ : window σ
    · have hfixed' : finiteAvg (fun ω : Ω => if ¬ good ω σ then (1 : ℝ) else 0) ≤ δ := by
        calc
          _ = finiteProb (fun ω => ¬ good ω σ) := by
            apply finiteAvg_congr
            intro ω
            exact (ite_eq_ite _ _ _).mpr trivial
          _ ≤ δ := hfixed σ hσ
      simpa only [hσ, true_and, not_true_eq_false, ite_false, zero_add] using hfixed'
    · simpa only [hσ, false_and, not_false_eq_true, ite_true, finiteAvg_const]
        using (le_add_of_nonneg_right hδ : (1 : ℝ) ≤ 1 + δ)
  apply finiteAvg_exists_le_of_le
  calc
    _ = restrictionAvg p (fun σ =>
        finiteAvg (fun ω : Ω => if ¬ (window σ ∧ good ω σ) then 1 else 0)) :=
      finiteAvg_restrictionAvg p _
    _ ≤ restrictionAvg p (fun σ => (if ¬ window σ then 1 else 0) + δ) :=
      restrictionAvg_mono hp hp1 hpoint
    _ = restrictionAvg p (fun σ => if ¬ window σ then 1 else 0) + δ := by
      rw [restrictionAvg_add, restrictionAvg_const]
    _ ≤ η + δ := add_le_add_left hwindow δ

def restrictionWindow (p : ℝ) (σ : Restriction V) : Prop :=
  (p * Fintype.card V) / 2 ≤ (Fintype.card (Live σ) : ℝ) ∧
    (Fintype.card (Live σ) : ℝ) ≤ 2 * (p * Fintype.card V)

def goodRestriction (p ε : ℝ) (b : ℕ) (f : Cube V → Bool)
    (σ : Restriction V) : Prop :=
  restrictionWindow p σ ∧ corr b (fun z => sign (f (fill σ z))) ≤ ε

theorem goodRestriction_corr
    {V : Type uDepth1}
    [Fintype V]
    [DecidableEq V]
    {p ε : ℝ} {b : ℕ} {f : Cube V → Bool}
    {σ : Restriction V} (h : goodRestriction p ε b f σ) :
    corr b (fun z => sign (f (fill σ z))) ≤ ε := h.2

theorem exists_good_parameter {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (b : ℕ) (f : Ω → Cube V → Bool)
    (hfixed : ∀ σ : Restriction V, restrictionWindow p σ →
      finiteProb (fun ω =>
        ¬ corr b (fun z => sign (f ω (fill σ z))) ≤
          (2 : ℝ) ^ (-(p * Fintype.card V) / 16)) ≤
        2 * (2 : ℝ) ^ (-(p * Fintype.card V) / 16)) :
    ∃ ω : Ω,
      restrictionAvg p (fun σ => if ¬ goodRestriction p
        ((2 : ℝ) ^ (-(p * Fintype.card V) / 16)) b (f ω) σ then 1 else 0) ≤
      4 * (2 : ℝ) ^ (-(p * Fintype.card V) / 16) := by
  have hε : 0 ≤ (2 : ℝ) ^ (-(p * Fintype.card V) / 16) :=
    Real.rpow_nonneg (by norm_num) _
  have hwindow : restrictionAvg p (fun σ : Restriction V =>
      if ¬ restrictionWindow p σ then 1 else 0) ≤
      2 * (2 : ℝ) ^ (-(p * Fintype.card V) / 16) := by
    calc
      _ = restrictionAvg p (fun σ : Restriction V =>
          if ¬ ((p * Fintype.card V) / 2 ≤ (Fintype.card (Live σ) : ℝ) ∧
            (Fintype.card (Live σ) : ℝ) ≤ 2 * (p * Fintype.card V)) then 1 else 0) := by
        apply congrArg (restrictionAvg p)
        funext σ
        exact (ite_eq_ite _ _ _).mpr trivial
      _ ≤ _ := restrictionAvg_outside_window (V := V) p hp hp1
  obtain ⟨ω, hω⟩ := exists_small_restriction_failure hp hp1
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε)
    (restrictionWindow p)
    (fun ω σ => corr b (fun z => sign (f ω (fill σ z))) ≤
      (2 : ℝ) ^ (-(p * Fintype.card V) / 16))
    hfixed hwindow
  refine ⟨ω, ?_⟩
  have heq : restrictionAvg p (fun σ => if ¬ goodRestriction p
      ((2 : ℝ) ^ (-(p * Fintype.card V) / 16)) b (f ω) σ then 1 else 0) =
      restrictionAvg p (fun σ => if ¬ (restrictionWindow p σ ∧
        corr b (fun z => sign (f ω (fill σ z))) ≤
          (2 : ℝ) ^ (-(p * Fintype.card V) / 16)) then 1 else 0) := by
    apply congrArg (restrictionAvg p)
    funext σ
    exact (ite_eq_ite _ _ _).mpr trivial
  rw [heq]
  linarith

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

theorem actual_hash_coefficient_window_failure_le {d r h b : ℕ}
    (p : Fin r → Bool) [Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p))]
    (hr : 0 < r) (hb : 1 ≤ b) (hh : 0 < h) (q : ℝ)
    (σ : Restriction (Fin d)) (hσ : restrictionWindow q σ)
    (hbound :
      (2 : ℝ) ^ Fintype.card (Live σ) / (2 : ℝ) ^ r +
        sparseMomentBound (Fintype.card (Live σ)) b
          (hardSliceSparseConstant b hb * Fintype.card (Live σ)) h
          ((2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ) / 4)) ≤
      2 * (2 : ℝ) ^ (-(q * d) / 16)) :
    finiteProb (fun ω : (Fin (d + r - 1) → Bool) ×
        (Fin (2 * h) → BinaryAlgebra.BitQuotient p) =>
      ¬ corr b (fun z => sign (hashAcceptance p (2 * h) ω.1 ω.2 (fill σ z))) ≤
        (2 : ℝ) ^ (-(q * d) / 16)) ≤
      2 * (2 : ℝ) ^ (-(q * d) / 16) := by
  have hlow : (q * d) / 2 ≤ (Fintype.card (Live σ) : ℝ) := by
    simpa only [restrictionWindow, Fintype.card_fin] using hσ.1
  have hthreshold : (2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ) / 8) ≤
      (2 : ℝ) ^ (-(q * d) / 16) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  apply le_trans _ ((actual_hash_coefficient_failure_le p hr σ b hb h hh).trans hbound)
  apply finiteProb_mono
  intro ω hω hsmall
  exact hω (hsmall.trans hthreshold)

theorem exists_good_hash_coefficients {d r h b : ℕ}
    (p : Fin r → Bool) [Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p))]
    (hr : 0 < r) (hb : 1 ≤ b) (hh : 0 < h) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hbound : ∀ m : ℕ, (q * d) / 2 ≤ (m : ℝ) → (m : ℝ) ≤ 2 * (q * d) →
      (2 : ℝ) ^ m / (2 : ℝ) ^ r +
        sparseMomentBound m b (hardSliceSparseConstant b hb * m) h
          ((2 : ℝ) ^ (-(m : ℝ) / 4)) ≤ 2 * (2 : ℝ) ^ (-(q * d) / 16)) :
    ∃ (u : Fin (d + r - 1) → Bool) (β : Fin (2 * h) → BinaryAlgebra.BitQuotient p),
      restrictionAvg q (fun σ => if ¬ goodRestriction q
        ((2 : ℝ) ^ (-(q * d) / 16)) b (hashAcceptance p (2 * h) u β) σ
        then 1 else 0) ≤ 4 * (2 : ℝ) ^ (-(q * d) / 16) := by
  have hfixed (σ : Restriction (Fin d)) (hσ : restrictionWindow q σ) :
      finiteProb (fun ω : (Fin (d + r - 1) → Bool) ×
          (Fin (2 * h) → BinaryAlgebra.BitQuotient p) =>
        ¬ corr b (fun z => sign (hashAcceptance p (2 * h) ω.1 ω.2 (fill σ z))) ≤
          (2 : ℝ) ^ (-(q * d) / 16)) ≤
        2 * (2 : ℝ) ^ (-(q * d) / 16) := by
    apply actual_hash_coefficient_window_failure_le p hr hb hh q σ hσ
    apply hbound
    · simpa only [restrictionWindow, Fintype.card_fin] using hσ.1
    · simpa only [restrictionWindow, Fintype.card_fin] using hσ.2
  obtain ⟨ω, hω⟩ := exists_good_parameter hq hq1 b
    (fun ω : (Fin (d + r - 1) → Bool) × (Fin (2 * h) → BinaryAlgebra.BitQuotient p) =>
      hashAcceptance p (2 * h) ω.1 ω.2)
    (by simpa only [Fintype.card_fin] using hfixed)
  exact ⟨ω.1, ω.2, by simpa only [Fintype.card_fin] using hω⟩

def coefficientInputBits {r t : ℕ} (p : Fin r → Bool)
    (β : Fin t → BinaryAlgebra.BitQuotient p) : Fin t → Fin r → Bool :=
  fun j i => BinaryAlgebra.fieldBit
    (BinaryAlgebra.coordinates (fun i => BinaryAlgebra.bitValue (p i)) (β j) i)

@[simp] theorem encode_coefficientInputBits {r t : ℕ} (p : Fin r → Bool)
    (β : Fin t → BinaryAlgebra.BitQuotient p) (j : Fin t) :
    BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
      (fun i => BinaryAlgebra.bitValue (coefficientInputBits p β j i)) = β j := by
  simp only [coefficientInputBits, BinaryAlgebra.bitValue_fieldBit]
  exact BinaryAlgebra.encode_coordinates _ _

theorem hashAcceptance_coefficientInputBits {d r t : ℕ} (p : Fin r → Bool)
    [Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p))]
    (u : Fin (d + r - 1) → Bool) (β : Fin t → BinaryAlgebra.BitQuotient p) :
    hashAcceptance p t u
      (fun j => BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
        (fun i => BinaryAlgebra.bitValue (coefficientInputBits p β j i))) =
      hashAcceptance p t u β := by
  simp only [encode_coefficientInputBits]

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

namespace DepthThreeLowerBound

private theorem rpow_two_thirds_cube (d : ℕ) :
    ((d : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (d : ℝ) ^ 2 := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg d) (2 / 3 : ℝ) 3]
  norm_num

private theorem rpow_one_sixth_sixth (d : ℕ) :
    ((d : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = (d : ℝ) := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg d) (1 / 6 : ℝ) 6]
  norm_num

theorem hashDimension_rpow_lower (d : ℕ) :
    (d : ℝ) ^ (2 / 3 : ℝ) ≤ (hashDimension d : ℝ) := by
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0)
    (Nat.cast_nonneg (hashDimension d))
  rw [rpow_two_thirds_cube]
  exact_mod_cast hashDimension_cube_bound d

theorem hashDimension_rpow_lt_add_one (d : ℕ) (hd : 0 < d) :
    (hashDimension d : ℝ) < (d : ℝ) ^ (2 / 3 : ℝ) + 1 := by
  have hr := hashDimension_pos hd
  by_cases hrone : hashDimension d = 1
  · have hpos := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hd) (2 / 3 : ℝ)
    rw [hrone]
    norm_num only [Nat.cast_one]
    linarith
  · have hpredpos : 0 < hashDimension d - 1 := by omega
    have hpred : (hashDimension d - 1) ^ 3 < d ^ 2 := by
      by_contra h
      have hle := hashDimension_minimal hd hpredpos (Nat.le_of_not_gt h)
      omega
    have hpredreal : ((hashDimension d - 1 : ℕ) : ℝ) <
        (d : ℝ) ^ (2 / 3 : ℝ) := by
      apply lt_of_pow_lt_pow_left₀ 3 (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      rw [rpow_two_thirds_cube]
      exact_mod_cast hpred
    have hcast : ((hashDimension d - 1 : ℕ) : ℝ) =
        (hashDimension d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ hashDimension d)] ; norm_num
    rw [hcast] at hpredreal
    linarith

theorem hashDimension_rpow_upper (d : ℕ) (hd : 1 ≤ d) :
    (hashDimension d : ℝ) ≤ 2 * (d : ℝ) ^ (2 / 3 : ℝ) := by
  have hround := hashDimension_rpow_lt_add_one d (by omega)
  have hone : (1 : ℝ) ≤ (d : ℝ) ^ (2 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hd) (by norm_num)
  linarith

theorem independenceOrder_rpow_le (d : ℕ) :
    (independenceOrder d : ℝ) ≤ (d : ℝ) ^ (1 / 6 : ℝ) := by
  apply le_of_pow_le_pow_left₀ (by decide : (6 : ℕ) ≠ 0)
    (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  rw [rpow_one_sixth_sixth]
  exact_mod_cast independenceOrder_pow_le d

theorem rpow_lt_independenceOrder_add_two (d : ℕ) :
    (d : ℝ) ^ (1 / 6 : ℝ) < (independenceOrder d : ℝ) + 2 := by
  apply lt_of_pow_lt_pow_left₀ 6
    (by linarith [(Nat.cast_nonneg (independenceOrder d) :
      (0 : ℝ) ≤ (independenceOrder d : ℝ))] :
      (0 : ℝ) ≤ (independenceOrder d : ℝ) + 2)
  rw [rpow_one_sixth_sixth]
  exact_mod_cast independenceOrder_next_pow_gt d

theorem four_le_rpow_one_sixth (d : ℕ) (hd : 4096 ≤ d) :
    (4 : ℝ) ≤ (d : ℝ) ^ (1 / 6 : ℝ) := by
  apply le_of_pow_le_pow_left₀ (by decide : (6 : ℕ) ≠ 0)
    (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  rw [rpow_one_sixth_sixth]
  norm_num only [show (4 : ℝ) ^ 6 = 4096 by norm_num]
  exact_mod_cast hd

theorem half_rpow_le_independenceOrder (d : ℕ) (hd : 4096 ≤ d) :
    (d : ℝ) ^ (1 / 6 : ℝ) / 2 ≤ (independenceOrder d : ℝ) := by
  have hfour := four_le_rpow_one_sixth d hd
  have hnext := rpow_lt_independenceOrder_add_two d
  linarith

theorem independenceOrder_add_two_mul_hashDimension_le (d : ℕ) (hd : 4096 ≤ d) :
    (independenceOrder d + 2) * hashDimension d ≤ 3 * d := by
  have hdreal : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hdpos : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le zero_lt_one hdreal
  have ht := independenceOrder_rpow_le d
  have hr := hashDimension_rpow_upper d (by omega)
  have hfour := four_le_rpow_one_sixth d hd
  have hy : 0 ≤ (d : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hproduct : ((independenceOrder d : ℝ) + 2) * (hashDimension d : ℝ) ≤
      ((d : ℝ) ^ (1 / 6 : ℝ) + 2) * (2 * (d : ℝ) ^ (2 / 3 : ℝ)) :=
    mul_le_mul (by linarith) hr
      (Nat.cast_nonneg (hashDimension d)) (by linarith)
  have hslack : 0 ≤ ((d : ℝ) ^ (1 / 6 : ℝ) - 4) *
      ((d : ℝ) ^ (2 / 3 : ℝ)) :=
    mul_nonneg (by linarith) hy
  have hsum : (d : ℝ) ^ (1 / 6 : ℝ) * (d : ℝ) ^ (2 / 3 : ℝ) =
      (d : ℝ) ^ (5 / 6 : ℝ) := by
    rw [← Real.rpow_add hdpos]
    norm_num
  have hlast : (d : ℝ) ^ (5 / 6 : ℝ) ≤ (d : ℝ) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hdreal (by norm_num : (5 / 6 : ℝ) ≤ 1))
  have hreal : ((independenceOrder d : ℝ) + 2) * (hashDimension d : ℝ) ≤
      3 * (d : ℝ) := by
    nlinarith [hproduct, hslack, hsum, hlast]
  exact_mod_cast hreal

theorem blockLen_le_five_mul (d : ℕ) (hd : 4096 ≤ d) :
    blockLen d ≤ 5 * d := by
  have hprod := independenceOrder_add_two_mul_hashDimension_le d hd
  rw [blockLen_eq (by omega : 0 < d)]
  omega

theorem blockLen_dataDimension_le (n : ℕ) (hn : 20480 ≤ n) :
    blockLen (dataDimension n) ≤ n := by
  have hd : 4096 ≤ dataDimension n := by
    unfold dataDimension
    omega
  exact (blockLen_le_five_mul (dataDimension n) hd).trans (five_mul_dataDimension_le n)

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace DepthThreeLowerBound

def sparseEnvelope (b M B d : ℝ) : ℝ :=
  (2 * M * (1 + b * (Real.log (4 * B + 1) / Real.log 2))) / d ^ (1 / 6 : ℝ) +
    (M * b / Real.log 2) * (Real.log d / d ^ (1 / 6 : ℝ)) +
    (1 / (3 * B * Real.log 2)) * (Real.log d / Real.sqrt d)

theorem sparse_expression_le_envelope (b M B d m t : ℝ)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hB : 0 < B) (hd : 1 ≤ d)
    (hmlo : B * Real.sqrt d / 2 ≤ m) (hmhi : m ≤ 2 * B * Real.sqrt d)
    (htlo : d ^ (1 / 6 : ℝ) / 2 ≤ t) (hthi : t ≤ d ^ (1 / 6 : ℝ))
    (htone : 1 ≤ t) :
    M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) / t +
        (Real.log t / Real.log 2) / m ≤ sparseEnvelope b M B d := by
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hroot : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd
  have hrootpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hroot
  have hpowpos : 0 < d ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hdpos _
  have hhalfpos : 0 < B * Real.sqrt d / 2 := div_pos (mul_pos hB hrootpos) (by norm_num)
  have hmpos : 0 < m := hhalfpos.trans_le hmlo
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one htone
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < 4 * B + 1 := by linarith
  have harg : 2 * m + 1 ≤ (4 * B + 1) * Real.sqrt d := by nlinarith
  have hlog : Real.log (2 * m + 1) ≤ Real.log (4 * B + 1) + Real.log d / 2 := by
    calc
      Real.log (2 * m + 1) ≤ Real.log ((4 * B + 1) * Real.sqrt d) :=
        Real.log_le_log (by linarith) harg
      _ = Real.log (4 * B + 1) + Real.log d / 2 := by
        rw [Real.log_mul hCpos.ne' hrootpos.ne', Real.log_sqrt hdpos.le]
  have hnum0 : 0 ≤ M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) :=
    mul_nonneg hM (add_nonneg zero_le_one
      (mul_nonneg hb (div_nonneg (Real.log_nonneg (by linarith)) hlogtwo.le)))
  have hnum : M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) ≤
      M * (1 + b * ((Real.log (4 * B + 1) + Real.log d / 2) / Real.log 2)) :=
    mul_le_mul_of_nonneg_left
      (add_le_add_right
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog hlogtwo.le) hb) 1) hM
  have hfirst : M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) / t ≤
      (2 * M * (1 + b * (Real.log (4 * B + 1) / Real.log 2))) / d ^ (1 / 6 : ℝ) +
        (M * b / Real.log 2) * (Real.log d / d ^ (1 / 6 : ℝ)) := by
    calc
      M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) / t ≤
          M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) /
            (d ^ (1 / 6 : ℝ) / 2) :=
        div_le_div_of_nonneg_left hnum0 (div_pos hpowpos (by norm_num)) htlo
      _ ≤ M * (1 + b * ((Real.log (4 * B + 1) + Real.log d / 2) / Real.log 2)) /
          (d ^ (1 / 6 : ℝ) / 2) :=
        div_le_div_of_nonneg_right hnum (div_nonneg hpowpos.le (by norm_num))
      _ = _ := by
        field_simp [hpowpos.ne', hlogtwo.ne'] ; ring
  have hlogt : Real.log t ≤ (1 / 6 : ℝ) * Real.log d := by
    calc
      Real.log t ≤ Real.log (d ^ (1 / 6 : ℝ)) := Real.log_le_log htpos hthi
      _ = (1 / 6 : ℝ) * Real.log d := Real.log_rpow hdpos _
  have hsecond : (Real.log t / Real.log 2) / m ≤
      (1 / (3 * B * Real.log 2)) * (Real.log d / Real.sqrt d) := by
    calc
      (Real.log t / Real.log 2) / m ≤
          (Real.log t / Real.log 2) / (B * Real.sqrt d / 2) :=
        div_le_div_of_nonneg_left (div_nonneg (Real.log_nonneg htone) hlogtwo.le)
          hhalfpos hmlo
      _ ≤ (((1 / 6 : ℝ) * Real.log d) / Real.log 2) / (B * Real.sqrt d / 2) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hlogt hlogtwo.le) hhalfpos.le
      _ = _ := by
        field_simp [hB.ne', hrootpos.ne', hlogtwo.ne'] ; ring
  exact add_le_add hfirst hsecond

theorem tendsto_sparseEnvelope (b M B : ℝ) :
    Tendsto (sparseEnvelope b M B) atTop (𝓝 (0 : ℝ)) := by
  have hinv : Tendsto (fun d : ℝ => (d ^ (1 / 6 : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).inv_tendsto_atTop
  have hlog6 : Tendsto (fun d : ℝ => Real.log d / d ^ (1 / 6 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).tendsto_div_nhds_zero
  have hlog2 : Tendsto (fun d : ℝ => Real.log d / Real.sqrt d) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hfirst : Tendsto
      (fun d : ℝ => (2 * M * (1 + b * (Real.log (4 * B + 1) / Real.log 2))) /
        d ^ (1 / 6 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      hinv.const_mul (2 * M * (1 + b * (Real.log (4 * B + 1) / Real.log 2)))
  have hsecond : Tendsto
      (fun d : ℝ => (M * b / Real.log 2) * (Real.log d / d ^ (1 / 6 : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hlog6.const_mul (M * b / Real.log 2)
  have hthird : Tendsto
      (fun d : ℝ => (1 / (3 * B * Real.log 2)) * (Real.log d / Real.sqrt d))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hlog2.const_mul (1 / (3 * B * Real.log 2))
  unfold sparseEnvelope
  simpa only [add_zero] using (hfirst.add hsecond).add hthird

theorem uniform_sparse_condition (b M B : ℝ) (hb : 0 ≤ b) (hM : 0 ≤ M) (hB : 0 < B) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d : ℝ, (D : ℝ) ≤ d → ∀ m t : ℝ,
      B * Real.sqrt d / 2 ≤ m → m ≤ 2 * B * Real.sqrt d →
      d ^ (1 / 6 : ℝ) / 2 ≤ t → t ≤ d ^ (1 / 6 : ℝ) → 1 ≤ t →
      M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) / t +
        (Real.log t / Real.log 2) / m ≤ 1 / 8 := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    ((tendsto_sparseEnvelope b M B).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 8))
  obtain ⟨D, hD⟩ := exists_nat_ge (max 1 R)
  have hDone : (1 : ℝ) ≤ (D : ℝ) := (le_max_left 1 R).trans hD
  refine ⟨D, by exact_mod_cast hDone, ?_⟩
  intro d hd m t hmlo hmhi htlo hthi htone
  have hd1 : 1 ≤ d := hDone.trans hd
  have hRd : R ≤ d := (le_max_right 1 R).trans (hD.trans hd)
  exact (sparse_expression_le_envelope b M B d m t hb hM hB hd1
    hmlo hmhi htlo hthi htone).trans (hR d hRd).le

theorem hard_slice_tail_bounds (μ m r t : ℝ) (hμ : 0 ≤ μ)
    (hmlo : μ / 2 ≤ m) (hmhi : m ≤ 2 * μ)
    (hr : (33 / 16 : ℝ) * μ ≤ r) (ht : 1 ≤ t) :
    (2 : ℝ) ^ (m - r) ≤ (2 : ℝ) ^ (-μ / 16) ∧
      (2 : ℝ) ^ (-(m * t) / 8) ≤ (2 : ℝ) ^ (-μ / 16) := by
  constructor
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  · have hm : 0 ≤ m := by linarith
    have hprod : 0 ≤ m * (t - 1) := mul_nonneg hm (sub_nonneg.mpr ht)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith

theorem in_window_correlation_bound (μ m : ℝ) (hm : μ / 2 ≤ m) :
    (2 : ℝ) ^ (-m / 8) ≤ (2 : ℝ) ^ (-μ / 16) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace DepthThreeLowerBound

private theorem two_rpow_log_div (x : ℝ) (hx : 0 < x) :
    (2 : ℝ) ^ (Real.log x / Real.log 2) = x := by
  have htwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he : Real.log 2 * (Real.log x / Real.log 2) = Real.log x := by
    field_simp [htwo]
  rw [he, Real.exp_log hx]

theorem nat_pow_eq_two_rpow (x : ℝ) (hx : 0 < x) (n : ℕ) :
    x ^ n = (2 : ℝ) ^ ((n : ℝ) * (Real.log x / Real.log 2)) := by
  calc
    x ^ n = ((2 : ℝ) ^ (Real.log x / Real.log 2)) ^ n := by
      rw [two_rpow_log_div x hx]
    _ = (2 : ℝ) ^ ((Real.log x / Real.log 2) * (n : ℝ)) :=
      (Real.rpow_mul_natCast (by norm_num) _ n).symm
    _ = _ := by congr 1 ; ring

theorem sparse_count_le_two_rpow (m b L : ℕ) :
    ((2 * (m : ℝ) + 1) ^ b + 1) ^ L ≤
      (2 : ℝ) ^ ((L : ℝ) *
        (1 + (b : ℝ) * (Real.log (2 * (m : ℝ) + 1) / Real.log 2))) := by
  have hx : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hxone : 1 ≤ 2 * (m : ℝ) + 1 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hpow : 1 ≤ (2 * (m : ℝ) + 1) ^ b := one_le_pow₀ hxone
  calc
    _ ≤ (2 * (2 * (m : ℝ) + 1) ^ b) ^ L :=
      pow_le_pow_left₀ (by positivity) (by linarith) L
    _ = ((2 : ℝ) ^ (1 + (b : ℝ) *
        (Real.log (2 * (m : ℝ) + 1) / Real.log 2))) ^ L := by
      congr 1
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
        ← nat_pow_eq_two_rpow _ hx b]
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1 ; ring

theorem sparseTestCode_card_le_two_rpow {V : Type uDepth1} [Fintype V] (b L : ℕ) :
    (Fintype.card (SparseTestCode V b L) : ℝ) ≤
      (2 : ℝ) ^ ((L : ℝ) *
        (1 + (b : ℝ) * (Real.log (2 * (Fintype.card V : ℝ) + 1) / Real.log 2))) := by
  rw [SparseTestCode.card_eq]
  push_cast
  exact sparse_count_le_two_rpow (Fintype.card V) b L

theorem sparse_moment_union_le {V : Type uDepth2} [Fintype V] (b M t : ℕ)
    (hm : 0 < Fintype.card V) (ht : 0 < t)
    (hcond : (M : ℝ) *
        (1 + (b : ℝ) * (Real.log (2 * (Fintype.card V : ℝ) + 1) / Real.log 2)) /
          (t : ℝ) + (Real.log (t : ℝ) / Real.log 2) / (Fintype.card V : ℝ) ≤ 1 / 8) :
    (Fintype.card (SparseTestCode V b (M * Fintype.card V)) : ℝ) * (t : ℝ) ^ t *
        (2 : ℝ) ^ (-((Fintype.card V : ℝ) * (t : ℝ)) / 4) ≤
      (2 : ℝ) ^ (-((Fintype.card V : ℝ) * (t : ℝ)) / 8) := by
  let m : ℝ := Fintype.card V
  have hmpos : 0 < m := by
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast hm
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hmult := mul_le_mul_of_nonneg_right hcond (mul_nonneg hmpos.le htpos.le)
  have hclear : ((M : ℝ) *
        (1 + (b : ℝ) * (Real.log (2 * m + 1) / Real.log 2)) / (t : ℝ) +
        (Real.log (t : ℝ) / Real.log 2) / m) * (m * (t : ℝ)) =
      (M : ℝ) * m * (1 + (b : ℝ) * (Real.log (2 * m + 1) / Real.log 2)) +
        (t : ℝ) * (Real.log (t : ℝ) / Real.log 2) := by
    field_simp [hmpos.ne', htpos.ne']
  change ((M : ℝ) *
      (1 + (b : ℝ) * (Real.log (2 * m + 1) / Real.log 2)) / (t : ℝ) +
      (Real.log (t : ℝ) / Real.log 2) / m) * (m * (t : ℝ)) ≤
        (1 / 8 : ℝ) * (m * (t : ℝ)) at hmult
  rw [hclear] at hmult
  have hcount := sparseTestCode_card_le_two_rpow (V := V) b (M * Fintype.card V)
  calc
    _ ≤ (2 : ℝ) ^ (((M * Fintype.card V : ℕ) : ℝ) *
          (1 + (b : ℝ) * (Real.log (2 * m + 1) / Real.log 2))) * (t : ℝ) ^ t *
        (2 : ℝ) ^ (-(m * (t : ℝ)) / 4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcount (pow_nonneg (Nat.cast_nonneg t) t))
        (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (((M * Fintype.card V : ℕ) : ℝ) *
          (1 + (b : ℝ) * (Real.log (2 * m + 1) / Real.log 2)) +
          (t : ℝ) * (Real.log (t : ℝ) / Real.log 2) + -(m * (t : ℝ)) / 4) := by
      rw [nat_pow_eq_two_rpow (t : ℝ) htpos t,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      change (M : ℝ) * m *
        (1 + (b : ℝ) * (Real.log (2 * m + 1) / Real.log 2)) +
        (t : ℝ) * (Real.log (t : ℝ) / Real.log 2) + -(m * (t : ℝ)) / 4 ≤
          -(m * (t : ℝ)) / 8
      linarith

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace DepthThreeLowerBound

theorem sparseMomentBound_at_quarter (m b L h : ℕ) :
    sparseMomentBound m b L h ((2 : ℝ) ^ (-(m : ℝ) / 4)) =
      (Fintype.card (SparseTestCode (Fin m) b L) : ℝ) *
        ((2 * h : ℕ) : ℝ) ^ (2 * h) *
          (2 : ℝ) ^ (-((m : ℝ) * ((2 * h : ℕ) : ℝ)) / 4) := by
  have hbase : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ (m : ℝ) := by simp
  have hratio : ((2 ^ m : ℕ) : ℝ) ^ h /
      (((2 : ℝ) ^ (-(m : ℝ) / 4)) * ((2 ^ m : ℕ) : ℝ)) ^ (2 * h) =
        (2 : ℝ) ^ (-((m : ℝ) * ((2 * h : ℕ) : ℝ)) / 4) := by
    rw [hbase, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  have hcard : (Fintype.card (SparseTestCode (Fin m) b L) : ℝ) =
      ((((2 * m + 1) ^ b + 1) ^ L : ℕ) : ℝ) := by
    simp only [SparseTestCode.card_eq, Fintype.card_fin]
  unfold sparseMomentBound
  rw [← hcard, mul_div_assoc, hratio]
  ring

theorem sparseMomentBound_quarter_le (m b M h : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hcond : (M : ℝ) *
        (1 + (b : ℝ) * (Real.log (2 * (m : ℝ) + 1) / Real.log 2)) /
          ((2 * h : ℕ) : ℝ) + (Real.log ((2 * h : ℕ) : ℝ) / Real.log 2) /
            (m : ℝ) ≤ 1 / 8) :
    sparseMomentBound m b (M * m) h ((2 : ℝ) ^ (-(m : ℝ) / 4)) ≤
      (2 : ℝ) ^ (-((m : ℝ) * ((2 * h : ℕ) : ℝ)) / 8) := by
  rw [sparseMomentBound_at_quarter]
  simpa only [Fintype.card_fin] using
    sparse_moment_union_le (V := Fin m) b M (2 * h)
      (by simpa only [Fintype.card_fin] using hm)
      (Nat.mul_pos (by decide) hh)
      (by simpa only [Fintype.card_fin] using hcond)

theorem exists_hashDimension_dominates (B : ℝ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d : ℕ, D ≤ d →
      (33 / 16 : ℝ) * (B * Real.sqrt (d : ℝ)) ≤ (hashDimension d : ℝ) := by
  have hg : ∀ᶠ x : ℝ in atTop, (33 / 16 : ℝ) * B ≤ x ^ (1 / 6 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).eventually
      (eventually_ge_atTop ((33 / 16 : ℝ) * B))
  obtain ⟨R, hR⟩ := eventually_atTop.mp hg
  obtain ⟨D, hD⟩ := exists_nat_ge (max 1 R)
  have hDone : (1 : ℝ) ≤ (D : ℝ) := (le_max_left 1 R).trans hD
  refine ⟨D, by exact_mod_cast hDone, ?_⟩
  intro d hd
  have hDd : (D : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one (hDone.trans hDd)
  have hpower := hR (d : ℝ) ((le_max_right 1 R).trans (hD.trans hDd))
  calc
    _ = ((33 / 16 : ℝ) * B) * Real.sqrt (d : ℝ) := by ring
    _ ≤ (d : ℝ) ^ (1 / 6 : ℝ) * Real.sqrt (d : ℝ) :=
      mul_le_mul_of_nonneg_right hpower (Real.sqrt_nonneg _)
    _ = (d : ℝ) ^ (2 / 3 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hdpos]
      norm_num
    _ ≤ (hashDimension d : ℝ) := hashDimension_rpow_lower d

theorem hard_slice_error_bound_eventually (b M : ℕ) (B : ℝ) (hB : 0 < B) :
    ∃ D : ℕ, 4096 ≤ D ∧ ∀ d : ℕ, D ≤ d → ∀ m h : ℕ,
      B * Real.sqrt (d : ℝ) / 2 ≤ (m : ℝ) →
      (m : ℝ) ≤ 2 * (B * Real.sqrt (d : ℝ)) →
      2 * h = independenceOrder d →
      (2 : ℝ) ^ ((m : ℝ) - (hashDimension d : ℝ)) +
        sparseMomentBound m b (M * m) h ((2 : ℝ) ^ (-(m : ℝ) / 4)) ≤
          2 * (2 : ℝ) ^ (-(B * Real.sqrt (d : ℝ)) / 16) := by
  obtain ⟨Ds, hDs, hSparse⟩ := uniform_sparse_condition (b : ℝ) (M : ℝ) B
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hB
  obtain ⟨Dr, hDr, hHash⟩ := exists_hashDimension_dominates B
  refine ⟨max 4096 (max Ds Dr), le_max_left _ _, ?_⟩
  intro d hd m h hmlo hmhi heven
  have hd4096 : 4096 ≤ d := (le_max_left _ _).trans hd
  have hds : Ds ≤ d := (le_max_left Ds Dr).trans ((le_max_right _ _).trans hd)
  have hdr : Dr ≤ d := (le_max_right Ds Dr).trans ((le_max_right _ _).trans hd)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hμ : 0 < B * Real.sqrt (d : ℝ) := mul_pos hB (Real.sqrt_pos.2 hdpos)
  have hmpos : 0 < m := by
    have hmp : (0 : ℝ) < m := lt_of_lt_of_le (by linarith : 0 < B * Real.sqrt (d : ℝ) / 2) hmlo
    exact_mod_cast hmp
  have ht2 : 2 ≤ independenceOrder d := (independenceOrder_two_le_iff d).2 (by omega)
  have htone : (1 : ℝ) ≤ (independenceOrder d : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ independenceOrder d)
  have hh : 0 < h := by omega
  have hcond := hSparse (d : ℝ) (by exact_mod_cast hds)
    (m : ℝ) (independenceOrder d : ℝ) hmlo
    (by nlinarith [hmhi]) (half_rpow_le_independenceOrder d hd4096)
    (independenceOrder_rpow_le d) htone
  have hsparse : sparseMomentBound m b (M * m) h ((2 : ℝ) ^ (-(m : ℝ) / 4)) ≤
      (2 : ℝ) ^ (-((m : ℝ) * (independenceOrder d : ℝ)) / 8) := by
    simpa only [heven] using sparseMomentBound_quarter_le m b M h hmpos hh
      (by simpa only [heven] using hcond)
  have htails := hard_slice_tail_bounds (B * Real.sqrt (d : ℝ)) (m : ℝ)
    (hashDimension d : ℝ) (independenceOrder d : ℝ) hμ.le hmlo hmhi (hHash d hdr) htone
  calc
    _ ≤ (2 : ℝ) ^ ((m : ℝ) - (hashDimension d : ℝ)) +
        (2 : ℝ) ^ (-((m : ℝ) * (independenceOrder d : ℝ)) / 8) :=
      add_le_add_right hsparse _
    _ ≤ (2 : ℝ) ^ (-(B * Real.sqrt (d : ℝ)) / 16) +
        (2 : ℝ) ^ (-(B * Real.sqrt (d : ℝ)) / 16) := add_le_add htails.1 htails.2
    _ = _ := by ring

theorem hash_collision_ratio_eq (m r : ℕ) :
    (2 : ℝ) ^ m / (2 : ℝ) ^ r = (2 : ℝ) ^ ((m : ℝ) - (r : ℝ)) := by
  simpa only [Real.rpow_natCast] using
    (Real.rpow_sub (by norm_num : (0 : ℝ) < 2) (m : ℝ) (r : ℝ)).symm

theorem actual_hard_slice_error_bound_eventually (b : ℕ) (hb : 1 ≤ b)
    (B : ℝ) (hB : 0 < B) :
    ∃ D : ℕ, 4096 ≤ D ∧ ∀ d : ℕ, D ≤ d → ∀ m h : ℕ,
      B * Real.sqrt (d : ℝ) / 2 ≤ (m : ℝ) →
      (m : ℝ) ≤ 2 * (B * Real.sqrt (d : ℝ)) →
      2 * h = independenceOrder d →
      (2 : ℝ) ^ m / (2 : ℝ) ^ hashDimension d +
        sparseMomentBound m b (hardSliceSparseConstant b hb * m) h
          ((2 : ℝ) ^ (-(m : ℝ) / 4)) ≤
            2 * (2 : ℝ) ^ (-(B * Real.sqrt (d : ℝ)) / 16) := by
  obtain ⟨D, hD, hbound⟩ :=
    hard_slice_error_bound_eventually b (hardSliceSparseConstant b hb) B hB
  refine ⟨D, hD, ?_⟩
  intro d hd m h hmlo hmhi heven
  rw [hash_collision_ratio_eq]
  exact hbound d hd m h hmlo hmhi heven

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace DepthThreeLowerBound

theorem exists_factorial_tail_width (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ b : ℕ, 1 ≤ b ∧ ∀ k : ℕ,
      (∑ ℓ ∈ Finset.Ico (b + 1) (k + 1), Q ^ ℓ / (ℓ.factorial : ℝ)) ≤ 1 / 2 := by
  let a : ℕ → ℝ := fun ℓ => Q ^ ℓ / (ℓ.factorial : ℝ)
  have ha : ∀ ℓ, 0 ≤ a ℓ := fun ℓ =>
    div_nonneg (pow_nonneg hQ ℓ) (Nat.cast_nonneg _)
  have hs : Summable a := Real.summable_pow_div_factorial Q
  have ht : Tendsto (fun n : ℕ => (∑' ℓ, a ℓ) - ∑ ℓ ∈ Finset.range n, a ℓ)
      atTop (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun _ : ℕ => ∑' ℓ, a ℓ) atTop (𝓝 (∑' ℓ, a ℓ)) :=
      tendsto_const_nhds
    simpa only [sub_self] using hc.sub hs.hasSum.tendsto_sum_nat
  have he := ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨max 1 N, le_max_left _ _, ?_⟩
  intro k
  change (∑ ℓ ∈ Finset.Ico (max 1 N + 1) (k + 1), a ℓ) ≤ 1 / 2
  by_cases hk : max 1 N + 1 ≤ k + 1
  · rw [Finset.sum_Ico_eq_sub a hk]
    have hupper : (∑ ℓ ∈ Finset.range (k + 1), a ℓ) ≤ ∑' ℓ, a ℓ :=
      hs.sum_le_tsum _ (fun ℓ _ => ha ℓ)
    have htail := hN (max 1 N + 1)
      ((le_max_right 1 N).trans (Nat.le_succ _))
    exact (sub_le_sub_right hupper _).trans htail.le
  · rw [Finset.Ico_eq_empty_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hk)), Finset.sum_empty]
    norm_num

theorem div_five_ge (D n : ℕ) (h : 5 * D ≤ n) : D ≤ n / 5 := by
  omega

theorem input_div_five_scale (n : ℕ) (hn : 5 ≤ n) :
    0 < n / 5 ∧ n ≤ 9 * (n / 5) := by
  omega

theorem sqrt_input_div_five_le (n : ℕ) (hn : 5 ≤ n) :
    Real.sqrt (n : ℝ) ≤ 3 * Real.sqrt ((n / 5 : ℕ) : ℝ) := by
  have hscale : (n : ℝ) ≤ 9 * ((n / 5 : ℕ) : ℝ) := by
    exact_mod_cast (input_div_five_scale n hn).2
  have hsquare := Real.sq_sqrt (Nat.cast_nonneg (n / 5) : (0 : ℝ) ≤ (n / 5 : ℕ))
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · nlinarith

theorem circuit_size_scale (A : ℝ) (hA : 0 ≤ A) (n : ℕ) (hn : 5 ≤ n) :
    (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) ≤
      (2 : ℝ) ^ ((3 * A) * Real.sqrt ((n / 5 : ℕ) : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  calc
    A * Real.sqrt (n : ℝ) ≤ A * (3 * Real.sqrt ((n / 5 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (sqrt_input_div_five_le n hn) hA
    _ = (3 * A) * Real.sqrt ((n / 5 : ℕ) : ℝ) := by ring

theorem final_error_exponents (s d S : ℝ) (hS0 : 0 ≤ S)
    (hS : S ≤ (2 : ℝ) ^ (s * Real.sqrt d)) (k : ℕ)
    (hk : 3 * (s + 1) * Real.sqrt d ≤ (k : ℝ)) :
    6 * S * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt d) / 16) +
        S ^ 2 * (2 : ℝ) ^ (-(k : ℝ)) ≤
      6 * (2 : ℝ) ^ (-((3 * s + 4) * Real.sqrt d)) +
        (2 : ℝ) ^ (-((s + 3) * Real.sqrt d)) := by
  have hfirst : 6 * S * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt d) / 16) ≤
      6 * (2 : ℝ) ^ (-((3 * s + 4) * Real.sqrt d)) := by
    calc
      6 * S * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt d) / 16) ≤
          6 * (2 : ℝ) ^ (s * Real.sqrt d) *
            (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt d) / 16) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS (by norm_num))
          (Real.rpow_nonneg (by norm_num) _)
      _ = 6 * ((2 : ℝ) ^ (s * Real.sqrt d) *
          (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt d) / 16)) := by ring
      _ = 6 * (2 : ℝ) ^ (s * Real.sqrt d - (64 * (s + 1) * Real.sqrt d) / 16) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 2 ; ring
      _ = 6 * (2 : ℝ) ^ (-((3 * s + 4) * Real.sqrt d)) := by
        congr 2 ; ring
  have hSsq : S ^ 2 ≤ ((2 : ℝ) ^ (s * Real.sqrt d)) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hS hS hS0 (Real.rpow_nonneg (by norm_num) _)
  have hsecond : S ^ 2 * (2 : ℝ) ^ (-(k : ℝ)) ≤
      (2 : ℝ) ^ (-((s + 3) * Real.sqrt d)) := by
    calc
      S ^ 2 * (2 : ℝ) ^ (-(k : ℝ)) ≤
          ((2 : ℝ) ^ (s * Real.sqrt d)) ^ 2 * (2 : ℝ) ^ (-(k : ℝ)) :=
        mul_le_mul_of_nonneg_right hSsq (Real.rpow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ ((s * Real.sqrt d) * 2 + -(k : ℝ)) := by
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) (s * Real.sqrt d) 2]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] ; norm_num
      _ ≤ (2 : ℝ) ^ (-((s + 3) * Real.sqrt d)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [hk]
  exact add_le_add hfirst hsecond

theorem final_error_le (s d S : ℝ) (hs : 0 ≤ s) (hd : 4 ≤ d) (hS0 : 0 ≤ S)
    (hS : S ≤ (2 : ℝ) ^ (s * Real.sqrt d)) (k : ℕ)
    (hk : 3 * (s + 1) * Real.sqrt d ≤ (k : ℝ)) :
    6 * S * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt d) / 16) +
        S ^ 2 * (2 : ℝ) ^ (-(k : ℝ)) ≤ 5 / 128 := by
  have hroot : (2 : ℝ) ≤ Real.sqrt d := Real.le_sqrt_of_sq_le (by norm_num; exact hd)
  have hprod : 0 ≤ s * Real.sqrt d := mul_nonneg hs (Real.sqrt_nonneg d)
  have hfirst : (2 : ℝ) ^ (-((3 * s + 4) * Real.sqrt d)) ≤ (2 : ℝ) ^ (-8 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have hsecond : (2 : ℝ) ^ (-((s + 3) * Real.sqrt d)) ≤ (2 : ℝ) ^ (-6 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  calc
    _ ≤ 6 * (2 : ℝ) ^ (-((3 * s + 4) * Real.sqrt d)) +
        (2 : ℝ) ^ (-((s + 3) * Real.sqrt d)) := final_error_exponents s d S hS0 hS k hk
    _ ≤ 6 * (2 : ℝ) ^ (-8 : ℝ) + (2 : ℝ) ^ (-6 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num)) hsecond
    _ = 5 / 128 := by norm_num

theorem correlation_error_le (s d : ℝ) (hs : 0 ≤ s) (hd : 1 ≤ d) :
    6 * (2 : ℝ) ^ (-(4 * (s + 1) * Real.sqrt d)) ≤ 3 / 8 := by
  have hroot : (1 : ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd
  have hprod : 0 ≤ s * Real.sqrt d := mul_nonneg hs (Real.sqrt_nonneg d)
  have hp : (2 : ℝ) ^ (-(4 * (s + 1) * Real.sqrt d)) ≤ (2 : ℝ) ^ (-4 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  calc
    _ ≤ 6 * (2 : ℝ) ^ (-4 : ℝ) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 3 / 8 := by norm_num

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Finset
open scoped BigOperators

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [instDecidableEqV : DecidableEq V] [instDecidableEqI : DecidableEq I] [Fintype I]

def reverseEligible (scope : I → Finset V) (violation : I → Bool)
    (R : Finset V) : Finset I :=
  univ.filter fun i => violation i = true ∧ Disjoint (scope i) R

@[simp] theorem mem_reverseEligible
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]
    [DecidableEq I]
    [Fintype I]
    (scope : I → Finset V) (violation : I → Bool)
    (R : Finset V) (i : I) :
    i ∈ reverseEligible scope violation R ↔
      violation i = true ∧ Disjoint (scope i) R := by
  simp [reverseEligible]

def reverseBlocks (b : ℕ) (E : Finset V) : Finset (Finset V) :=
  E.powerset.filter fun D => b < D.card

@[simp] theorem mem_reverseBlocks
    {V : Type uDepth1}
    [DecidableEq V]
    (b : ℕ) (E D : Finset V) :
    D ∈ reverseBlocks b E ↔ D ⊆ E ∧ b < D.card := by
  simp [reverseBlocks]

def ReverseChoice (b : ℕ) (scope : I → Finset V) (violation : I → Bool)
    (R : Finset V) (i : I) (D : Finset V) : Prop :=
  i ∈ reverseEligible scope violation R ∧ D ∈ reverseBlocks b (scope i)

theorem ReverseChoice.disjoint {b : ℕ} {scope : I → Finset V}
    {violation : I → Bool} {R : Finset V} {i : I} {D : Finset V}
    (h : ReverseChoice b scope violation R i D) : Disjoint R D := by
  have hi := (mem_reverseEligible scope violation R i).mp h.1
  have hD := (mem_reverseBlocks b (scope i) D).mp h.2
  exact hi.2.symm.mono_right hD.1

theorem ReverseChoice.eligible_card_pos
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]
    [DecidableEq I]
    [Fintype I]
    {b : ℕ} {scope : I → Finset V}
    {violation : I → Bool} {R : Finset V} {i : I} {D : Finset V}
    (h : ReverseChoice b scope violation R i D) :
    0 < (reverseEligible scope violation R).card :=
  Finset.card_pos.mpr ⟨i, h.1⟩

def reverseChoiceWeight (α : ℝ) (scope : I → Finset V) (violation : I → Bool)
    (R D : Finset V) : ℝ :=
  α ^ D.card / ((reverseEligible scope violation R).card : ℝ)

theorem reverseChoiceWeight_nonneg
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]
    [DecidableEq I]
    [Fintype I]
    {α : ℝ} (hα : 0 ≤ α)
    (scope : I → Finset V) (violation : I → Bool) (R D : Finset V) :
    0 ≤ reverseChoiceWeight α scope violation R D :=
  div_nonneg (pow_nonneg hα _) (Nat.cast_nonneg _)

def reverseTheta (α : ℝ) (b k : ℕ) : ℝ :=
  ∑ l ∈ range (k + 1), if b < l then (k.choose l : ℝ) * α ^ l else 0

theorem reverseTheta_nonneg {α : ℝ} (hα : 0 ≤ α) (b k : ℕ) :
    0 ≤ reverseTheta α b k := by
  apply sum_nonneg
  intro l hl
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hα _)
  · exact le_rfl

def reverseBlockMass (α : ℝ) (b : ℕ) (E : Finset V) : ℝ :=
  ∑ D ∈ reverseBlocks b E, α ^ D.card

theorem reverseBlockMass_nonneg
    {V : Type uDepth1}
    [DecidableEq V]
    {α : ℝ} (hα : 0 ≤ α) (b : ℕ) (E : Finset V) :
    0 ≤ reverseBlockMass α b E :=
  sum_nonneg fun _ _ => pow_nonneg hα _

theorem reverseBlockMass_eq_theta
    {V : Type uDepth1}
    [DecidableEq V]
    (α : ℝ) (b : ℕ) (E : Finset V) :
    reverseBlockMass α b E = reverseTheta α b E.card := by
  unfold reverseBlockMass reverseBlocks
  rw [Finset.sum_filter, Finset.sum_powerset]
  unfold reverseTheta
  apply sum_congr rfl
  intro l hl
  rw [Finset.sum_powersetCard l E (fun n => if b < n then α ^ n else 0)]
  by_cases h : b < l <;> simp [h, nsmul_eq_mul]

theorem reverseTheta_mono_width {α : ℝ} (hα : 0 ≤ α) (b : ℕ)
    {e k : ℕ} (hek : e ≤ k) : reverseTheta α b e ≤ reverseTheta α b k := by
  unfold reverseTheta
  calc
    (∑ l ∈ range (e + 1), if b < l then (e.choose l : ℝ) * α ^ l else 0) ≤
        ∑ l ∈ range (e + 1), if b < l then (k.choose l : ℝ) * α ^ l else 0 := by
      apply sum_le_sum
      intro l hl
      by_cases h : b < l
      · simp only [h, ite_true]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hα _)
        exact Nat.cast_le.mpr (Nat.choose_le_choose l hek)
      · simp only [h, ite_false, le_refl]
    _ ≤ ∑ l ∈ range (k + 1), if b < l then (k.choose l : ℝ) * α ^ l else 0 := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono (Nat.add_le_add_right hek 1))
      intro l hl hle
      split_ifs
      · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hα _)
      · exact le_rfl

theorem reverseBlockMass_le_theta {α : ℝ} (hα : 0 ≤ α) (b : ℕ)
    (E : Finset V) {k : ℕ} (hE : E.card ≤ k) :
    reverseBlockMass α b E ≤ reverseTheta α b k := by
  rw [reverseBlockMass_eq_theta]
  exact reverseTheta_mono_width hα b hE

def reverseOneStep (α : ℝ) (b : ℕ) (scope : I → Finset V)
    (violation : I → Bool) (R : Finset V) : ℝ :=
  (∑ i ∈ reverseEligible scope violation R, reverseBlockMass α b (scope i)) /
    ((reverseEligible scope violation R).card : ℝ)

theorem sum_reverseBlockMass_le
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]
    [DecidableEq I]
    [Fintype I]
    {α : ℝ} (hα : 0 ≤ α) (b k : ℕ)
    (scope : I → Finset V) (hscope : ∀ i, (scope i).card ≤ k)
    (violation : I → Bool) (R : Finset V) :
    (∑ i ∈ reverseEligible scope violation R, reverseBlockMass α b (scope i)) ≤
      ((reverseEligible scope violation R).card : ℝ) * reverseTheta α b k := by
  calc
    _ ≤ ∑ i ∈ reverseEligible scope violation R, reverseTheta α b k :=
      sum_le_sum fun i hi => reverseBlockMass_le_theta hα b (scope i) (hscope i)
    _ = _ := by simp [nsmul_eq_mul]

theorem reverseOneStep_le_theta {α : ℝ} (hα : 0 ≤ α) (b k : ℕ)
    (scope : I → Finset V) (hscope : ∀ i, (scope i).card ≤ k)
    (violation : I → Bool) (R : Finset V) :
    reverseOneStep α b scope violation R ≤ reverseTheta α b k := by
  by_cases h : (reverseEligible scope violation R).Nonempty
  · have hc : (0 : ℝ) < (reverseEligible scope violation R).card := by
      exact Nat.cast_pos.mpr (Finset.card_pos.mpr h)
    apply (div_le_iff₀ hc).mpr
    simpa only [mul_comm] using sum_reverseBlockMass_le hα b k scope hscope violation R
  · have he : reverseEligible scope violation R = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simpa [reverseOneStep, he] using reverseTheta_nonneg hα b k

def reverseTotal (α : ℝ) (b : ℕ) (scope : I → Finset V)
    (violation : I → Bool) : ℕ → Finset V → ℝ
  | 0, _ => 1
  | s + 1, R =>
      if (reverseEligible scope violation R).Nonempty then
        (∑ i ∈ reverseEligible scope violation R,
          ∑ D ∈ reverseBlocks b (scope i),
            α ^ D.card * reverseTotal α b scope violation s (R ∪ D)) /
          ((reverseEligible scope violation R).card : ℝ)
      else 0

@[simp] theorem reverseTotal_zero
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]
    [DecidableEq I]
    [Fintype I]
    (α : ℝ) (b : ℕ) (scope : I → Finset V)
    (violation : I → Bool) (R : Finset V) :
    reverseTotal α b scope violation 0 R = 1 := rfl

theorem reverseTotal_succ_of_nonempty
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]
    [DecidableEq I]
    [Fintype I]
    (α : ℝ) (b : ℕ) (scope : I → Finset V)
    (violation : I → Bool) (s : ℕ) (R : Finset V)
    (h : (reverseEligible scope violation R).Nonempty) :
    reverseTotal α b scope violation (s + 1) R =
      (∑ i ∈ reverseEligible scope violation R,
        ∑ D ∈ reverseBlocks b (scope i),
          α ^ D.card * reverseTotal α b scope violation s (R ∪ D)) /
        ((reverseEligible scope violation R).card : ℝ) := by
  simp only [reverseTotal, h, ite_true]

theorem reverseTotal_succ_of_empty
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]
    [DecidableEq I]
    [Fintype I]
    (α : ℝ) (b : ℕ) (scope : I → Finset V)
    (violation : I → Bool) (s : ℕ) (R : Finset V)
    (h : reverseEligible scope violation R = ∅) :
    reverseTotal α b scope violation (s + 1) R = 0 := by
  simp [reverseTotal, h]

theorem reverseTotal_nonneg
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]
    [DecidableEq I]
    [Fintype I]
    {α : ℝ} (hα : 0 ≤ α) (b : ℕ)
    (scope : I → Finset V) (violation : I → Bool) (s : ℕ) (R : Finset V) :
    0 ≤ reverseTotal α b scope violation s R := by
  induction s generalizing R with
  | zero => simp
  | succ s ih =>
    simp only [reverseTotal]
    split_ifs
    · apply div_nonneg _ (Nat.cast_nonneg _)
      apply sum_nonneg
      intro i hi
      exact sum_nonneg fun D hD => mul_nonneg (pow_nonneg hα _) (ih (R ∪ D))
    · exact le_rfl

theorem reverseTotal_le_theta_pow {α : ℝ} (hα : 0 ≤ α) (b k : ℕ)
    (scope : I → Finset V) (hscope : ∀ i, (scope i).card ≤ k)
    (violation : I → Bool) (s : ℕ) (R : Finset V) :
    reverseTotal α b scope violation s R ≤ (reverseTheta α b k) ^ s := by
  have hθ : 0 ≤ reverseTheta α b k := reverseTheta_nonneg hα b k
  induction s generalizing R with
  | zero => simp
  | succ s ih =>
    by_cases h : (reverseEligible scope violation R).Nonempty
    · rw [reverseTotal_succ_of_nonempty α b scope violation s R h]
      have hc : (0 : ℝ) < (reverseEligible scope violation R).card := by
        exact Nat.cast_pos.mpr (Finset.card_pos.mpr h)
      apply (div_le_iff₀ hc).mpr
      calc
        (∑ i ∈ reverseEligible scope violation R,
            ∑ D ∈ reverseBlocks b (scope i),
              α ^ D.card * reverseTotal α b scope violation s (R ∪ D)) ≤
            ∑ i ∈ reverseEligible scope violation R,
              ∑ D ∈ reverseBlocks b (scope i), α ^ D.card * (reverseTheta α b k) ^ s := by
          apply sum_le_sum
          intro i hi
          exact sum_le_sum fun D hD =>
            mul_le_mul_of_nonneg_left (ih (R ∪ D)) (pow_nonneg hα _)
        _ = ∑ i ∈ reverseEligible scope violation R,
              reverseBlockMass α b (scope i) * (reverseTheta α b k) ^ s := by
          simp only [reverseBlockMass, Finset.sum_mul]
        _ ≤ ∑ i ∈ reverseEligible scope violation R,
              reverseTheta α b k * (reverseTheta α b k) ^ s := by
          apply sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right
            (reverseBlockMass_le_theta hα b (scope i) (hscope i)) (pow_nonneg hθ _)
        _ = (reverseTheta α b k) ^ (s + 1) *
              ((reverseEligible scope violation R).card : ℝ) := by
          simp only [Finset.sum_const, nsmul_eq_mul, pow_succ]
          ring
    · have he : reverseEligible scope violation R = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      rw [reverseTotal_succ_of_empty α b scope violation s R he]
      exact pow_nonneg hθ _

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

def liveProbability (B : ℝ) (d : ℕ) : ℝ := B / Real.sqrt (d : ℝ)

def degreeCutoff (s : ℝ) (d : ℕ) : ℕ :=
  Nat.ceil (3 * (s + 1) * Real.sqrt (d : ℝ))

def factorialBase (B s : ℝ) : ℝ := 4 * B * (3 * (s + 1) + 1)

theorem liveProbability_pos (B : ℝ) (hB : 0 < B) (d : ℕ) (hd : 0 < d) :
    0 < liveProbability B d :=
  div_pos hB (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd))

theorem liveProbability_mul_dimension (B : ℝ) (d : ℕ) (hd : 0 < d) :
    liveProbability B d * (d : ℝ) = B * Real.sqrt (d : ℝ) := by
  have hroot : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)).ne'
  unfold liveProbability
  calc
    B / Real.sqrt (d : ℝ) * (d : ℝ) =
        B / Real.sqrt (d : ℝ) * (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) := by
      rw [Real.mul_self_sqrt (Nat.cast_nonneg d)]
    _ = B * Real.sqrt (d : ℝ) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hroot]

theorem degreeCutoff_lower (s : ℝ) (d : ℕ) :
    3 * (s + 1) * Real.sqrt (d : ℝ) ≤ (degreeCutoff s d : ℝ) :=
  Nat.le_ceil _

theorem degreeCutoff_upper (s : ℝ) (hs : 0 ≤ s) (d : ℕ) (hd : 1 ≤ d) :
    (degreeCutoff s d : ℝ) ≤ (3 * (s + 1) + 1) * Real.sqrt (d : ℝ) := by
  have hroot : (1 : ℝ) ≤ Real.sqrt (d : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  have hnonneg : 0 ≤ 3 * (s + 1) * Real.sqrt (d : ℝ) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hceil := Nat.ceil_lt_add_one hnonneg
  change (degreeCutoff s d : ℝ) < 3 * (s + 1) * Real.sqrt (d : ℝ) + 1 at hceil
  nlinarith

theorem exists_liveProbability_threshold (B : ℝ) (hB : 0 < B) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d : ℕ, D ≤ d →
      0 < liveProbability B d ∧ liveProbability B d ≤ 1 / 2 := by
  obtain ⟨D, hD⟩ := exists_nat_ge (max (1 : ℝ) ((2 * B) ^ 2))
  have hDone : 1 ≤ D := by
    exact_mod_cast (le_max_left (1 : ℝ) ((2 * B) ^ 2)).trans hD
  refine ⟨D, hDone, ?_⟩
  intro d hd
  have hdone : 1 ≤ d := hDone.trans hd
  have hrootpos : 0 < Real.sqrt (d : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega : 0 < d))
  have hsq : (2 * B) ^ 2 ≤ (d : ℝ) :=
    ((le_max_right (1 : ℝ) ((2 * B) ^ 2)).trans hD).trans (Nat.cast_le.mpr hd)
  have hroot : 2 * B ≤ Real.sqrt (d : ℝ) := Real.le_sqrt_of_sq_le hsq
  refine ⟨liveProbability_pos B hB d (by omega), ?_⟩
  change B / Real.sqrt (d : ℝ) ≤ 1 / 2
  apply (div_le_iff₀ hrootpos).mpr
  linarith

theorem scaled_cutoff_le_factorialBase (B s : ℝ) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (d : ℕ) (hd : 1 ≤ d) (hp : liveProbability B d ≤ 1 / 2) :
    (2 * liveProbability B d / (1 - liveProbability B d)) *
      (degreeCutoff s d : ℝ) ≤ factorialBase B s := by
  have hrootpos : 0 < Real.sqrt (d : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega : 0 < d))
  have hp0 : 0 ≤ liveProbability B d := div_nonneg hB (Real.sqrt_nonneg _)
  have hα : 2 * liveProbability B d / (1 - liveProbability B d) ≤
      4 * liveProbability B d := by
    calc
      2 * liveProbability B d / (1 - liveProbability B d) ≤
          2 * liveProbability B d / (1 / 2) :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
      _ = 4 * liveProbability B d := by ring
  calc
    (2 * liveProbability B d / (1 - liveProbability B d)) *
        (degreeCutoff s d : ℝ) ≤
      (4 * liveProbability B d) * (degreeCutoff s d : ℝ) :=
        mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg _)
    _ ≤ (4 * liveProbability B d) *
        ((3 * (s + 1) + 1) * Real.sqrt (d : ℝ)) :=
      mul_le_mul_of_nonneg_left (degreeCutoff_upper s hs d hd) (by linarith)
    _ = factorialBase B s := by
      unfold liveProbability factorialBase
      field_simp [hrootpos.ne']

theorem reverseTheta_le_factorial_tail (α Q : ℝ) (hα : 0 ≤ α) (b k : ℕ)
    (hαk : α * (k : ℝ) ≤ Q) :
    reverseTheta α b k ≤
      ∑ ℓ ∈ Finset.Ico (b + 1) (k + 1), Q ^ ℓ / (ℓ.factorial : ℝ) := by
  have hset : (Finset.range (k + 1)).filter (fun ℓ => b < ℓ) =
      Finset.Ico (b + 1) (k + 1) := by
    ext ℓ
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  unfold reverseTheta
  rw [← Finset.sum_filter, hset]
  apply Finset.sum_le_sum
  intro ℓ hℓ
  calc
    (k.choose ℓ : ℝ) * α ^ ℓ ≤
        ((k : ℝ) ^ ℓ / (ℓ.factorial : ℝ)) * α ^ ℓ :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div ℓ k) (pow_nonneg hα _)
    _ = (α * (k : ℝ)) ^ ℓ / (ℓ.factorial : ℝ) := by
      rw [mul_pow]
      ring
    _ ≤ Q ^ ℓ / (ℓ.factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg hα (Nat.cast_nonneg k)) hαk ℓ)
        (Nat.cast_nonneg _)

theorem exists_final_parameter_width (B s : ℝ) (hB : 0 < B) (hs : 0 ≤ s) :
    ∃ b : ℕ, 1 ≤ b ∧ ∃ D : ℕ, 1 ≤ D ∧ ∀ d : ℕ, D ≤ d →
      0 < liveProbability B d ∧ liveProbability B d ≤ 1 / 2 ∧
      reverseTheta (2 * liveProbability B d / (1 - liveProbability B d))
        b (degreeCutoff s d) ≤ 1 / 2 := by
  have hQ : 0 ≤ factorialBase B s :=
    mul_nonneg (mul_nonneg (by norm_num) hB.le) (by linarith)
  obtain ⟨b, hb, htail⟩ := exists_factorial_tail_width (factorialBase B s) hQ
  obtain ⟨D, hD, hprob⟩ := exists_liveProbability_threshold B hB
  refine ⟨b, hb, D, hD, ?_⟩
  intro d hd
  obtain ⟨hp0, hphalf⟩ := hprob d hd
  refine ⟨hp0, hphalf, ?_⟩
  have hα : 0 ≤ 2 * liveProbability B d / (1 - liveProbability B d) :=
    div_nonneg (by linarith) (by linarith)
  exact (reverseTheta_le_factorial_tail _ _ hα b (degreeCutoff s d)
    (scaled_cutoff_le_factorialBase B s hB.le hs d (hD.trans hd) hphalf)).trans
      (htail (degreeCutoff s d))

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

theorem exists_monic_irreducible_natDegree_two (r : ℕ) (hr : 0 < r) :
    ∃ P : Polynomial (ZMod 2),
      P.Monic ∧ Irreducible P ∧ P.natDegree = r := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top
    (ZMod 2) (GaloisField 2 r)
  have hαint : IsIntegral (ZMod 2) α := IsIntegral.of_finite (ZMod 2) α
  refine ⟨minpoly (ZMod 2) α, minpoly.monic hαint,
    minpoly.irreducible hαint, ?_⟩
  exact ((Field.primitive_element_iff_minpoly_natDegree_eq
    (ZMod 2) α).mp hα).trans
      (GaloisField.finrank 2 (Nat.ne_of_gt hr))

theorem exists_monic_irreducible_degree_two (r : ℕ) (hr : 0 < r) :
    ∃ P : Polynomial (ZMod 2),
      P.Monic ∧ Irreducible P ∧ P.degree = (r : WithBot ℕ) := by
  obtain ⟨P, hP, hI, hdegree⟩ := exists_monic_irreducible_natDegree_two r hr
  refine ⟨P, hP, hI, ?_⟩
  rw [Polynomial.degree_eq_natDegree hP.ne_zero, hdegree]

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound
namespace BinaryAlgebra

def polynomialBits (P : Polynomial F2) (r : ℕ) : Fin r → Bool :=
  fun i => fieldBit (P.coeff i.val)

theorem inputPolynomialBits_polynomialBits (P : Polynomial F2) (hP : P.Monic)
    {r : ℕ} (hdegree : P.natDegree = r) :
    inputPolynomialBits (polynomialBits P r) = P := by
  ext j
  rcases lt_trichotomy j r with hj | rfl | hj
  · simpa only [polynomialBits, bitValue_fieldBit] using
      inputPolynomialBits_coeff_lt (polynomialBits P r) ⟨j, hj⟩
  · rw [inputPolynomialBits_coeff_leading]
    simpa only [hdegree] using hP.coeff_natDegree.symm
  · have hleft : (inputPolynomialBits (polynomialBits P r)).coeff j = 0 :=
      inputPolynomial_coeff_of_gt _ hj
    rw [hleft]
    symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    simpa only [hdegree] using hj

end BinaryAlgebra

theorem exists_irreducible_inputPolynomialBits (r : ℕ) (hr : 0 < r) :
    ∃ p : Fin r → Bool, Irreducible (BinaryAlgebra.inputPolynomialBits p) := by
  obtain ⟨P, hP, hI, hdegree⟩ := exists_monic_irreducible_natDegree_two r hr
  refine ⟨BinaryAlgebra.polynomialBits P r, ?_⟩
  rw [BinaryAlgebra.inputPolynomialBits_polynomialBits P hP hdegree]
  exact hI

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

namespace ParsedInput

abbrev QuotientRing (q : ParsedInput) := AdjoinRoot q.modulus

instance quotientRingFintype (q : ParsedInput) : Fintype q.QuotientRing :=
  BinaryAlgebra.inputQuotientFintype
    (fun i => BinaryAlgebra.bitValue (q.polynomial i))

def quotientHash (q : ParsedInput) : q.QuotientRing :=
  AdjoinRoot.mk q.modulus q.hashPolynomial

def quotientCoefficient (q : ParsedInput) (j : Fin q.coefficientCount) : q.QuotientRing :=
  AdjoinRoot.mk q.modulus (q.coefficientPolynomial j)

def quotientEvaluation (q : ParsedInput) : q.QuotientRing :=
  ∑ j : Fin q.coefficientCount, q.quotientCoefficient j * q.quotientHash ^ j.val

theorem quotientHash_eq_encode (q : ParsedInput) :
    q.quotientHash = BinaryAlgebra.encode
      (fun i => BinaryAlgebra.bitValue (q.polynomial i))
      (fun i => BinaryAlgebra.bitValue (BinaryHash.hashBool q.hashSeed q.data i)) := rfl

theorem quotientCoefficient_eq_encode (q : ParsedInput) (j : Fin q.coefficientCount) :
    q.quotientCoefficient j = BinaryAlgebra.encode
      (fun i => BinaryAlgebra.bitValue (q.polynomial i))
      (fun i => BinaryAlgebra.bitValue (q.coefficients j i)) := rfl

def coefficientBitsEquiv (q : ParsedInput) :
    (Fin q.ringDegree → Bool) ≃ q.QuotientRing :=
  (BinaryAlgebra.bitsEquivF2 (Fin q.ringDegree)).trans
    (BinaryAlgebra.coordinates
      (fun i => BinaryAlgebra.bitValue (q.polynomial i))).toEquiv.symm

@[simp] theorem coefficientBitsEquiv_apply (q : ParsedInput)
    (v : Fin q.ringDegree → Bool) :
    q.coefficientBitsEquiv v = BinaryAlgebra.encode
      (fun i => BinaryAlgebra.bitValue (q.polynomial i))
      (fun i => BinaryAlgebra.bitValue (v i)) := rfl

@[simp] theorem coefficientBitsEquiv_coefficient (q : ParsedInput)
    (j : Fin q.coefficientCount) :
    q.coefficientBitsEquiv (q.coefficients j) = q.quotientCoefficient j := rfl

@[simp] theorem quotientRing_card (q : ParsedInput) :
    Fintype.card q.QuotientRing = 2 ^ q.ringDegree :=
  BinaryAlgebra.bitQuotient_card q.polynomial

theorem quotientEvaluation_eq_mk (q : ParsedInput) :
    q.quotientEvaluation = AdjoinRoot.mk q.modulus q.evaluationPolynomial := by
  simp only [quotientEvaluation, evaluationPolynomial, quotientCoefficient, quotientHash,
    map_sum, map_mul, map_pow]

theorem representative_quotientEvaluation (q : ParsedInput) :
    BinaryAlgebra.quotientRepresentative q.modulus_monic q.quotientEvaluation =
      q.evaluationRemainder := by
  rw [quotientEvaluation_eq_mk, BinaryAlgebra.quotientRepresentative_mk]
  rfl

theorem degreeZero_quotientEvaluation (q : ParsedInput) :
    BinaryAlgebra.degreeZero q.modulus_monic q.quotientEvaluation =
      q.evaluationRemainder.coeff 0 := by
  rw [BinaryAlgebra.degreeZero_apply, representative_quotientEvaluation]

theorem quotient_degreeZero_one (q : ParsedInput) (hr : 0 < q.ringDegree) :
    BinaryAlgebra.degreeZero q.modulus_monic (1 : q.QuotientRing) = 1 := by
  apply BinaryAlgebra.degreeZero_one
  change 0 < (BinaryAlgebra.inputPolynomialBits q.polynomial).natDegree
  rw [BinaryAlgebra.inputPolynomialBits_natDegree]
  exact hr

theorem evaluate_eq_true_iff_degreeZero (q : ParsedInput) :
    q.evaluate = true ↔
      BinaryAlgebra.degreeZero q.modulus_monic q.quotientEvaluation = 0 := by
  rw [evaluate_eq_true_iff, degreeZero_quotientEvaluation]

end ParsedInput

theorem language_eq_true_iff_quotient (w : List Bool) :
    language w = true ↔ InputFits w ∧
      BinaryAlgebra.degreeZero (decodeInput w).modulus_monic
        (decodeInput w).quotientEvaluation = 0 := by
  rw [language_eq_true_iff, ParsedInput.degreeZero_quotientEvaluation]

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

variable {V : Type uDepth1} {W : Type uDepth2}

namespace GateInput

def subst (s : V → Sum W Bool) : GateInput V → GateInput W
  | .inl (v, b) => match s v with
    | .inl w => .inl (w, b)
    | .inr c => .inr (decide (c = b))
  | .inr b => .inr b

def assignment (s : V → Sum W Bool) (x : Cube W) : Cube V :=
  fun v => match s v with
    | .inl w => x w
    | .inr b => b

@[simp] theorem eval_subst (s : V → Sum W Bool) (l : GateInput V) (x : Cube W) :
    (subst s l).eval x = l.eval (assignment s x) := by
  cases l with
  | inl l =>
    rcases l with ⟨v, b⟩
    cases h : s v <;> simp [subst, eval, assignment, Literal.eval, h]
  | inr b => rfl

end GateInput

namespace RawClause

@[simp] theorem eval_eq_true (C : RawClause V) (x : Cube V) :
    C.eval x = true ↔ ∃ l ∈ C, l.eval x = true := by
  classical
  simp [eval]

@[simp] theorem eval_map_subst (s : V → Sum W Bool) (C : RawClause V)
    (x : Cube W) : RawClause.eval (C.map (GateInput.subst s)) x =
      C.eval (GateInput.assignment s x) := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [eval_eq_true, eval_eq_true]
  constructor
  · rintro ⟨a, ha, hx⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    exact ⟨l, hl, by simpa only [GateInput.eval_subst] using hx⟩
  · rintro ⟨l, hl, hx⟩
    refine ⟨GateInput.subst s l, List.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩
    simpa only [GateInput.eval_subst] using hx

end RawClause

namespace Circuit3

@[simp] theorem middleEval_eq_true (C : Circuit3 V) (j : Fin C.middleCount)
    (x : Cube V) : C.middleEval j x = true ↔
      ∀ i ∈ C.middle j, (C.bottom i).eval x = true := by
  classical
  simp [middleEval]

@[simp] theorem eval_eq_true (C : Circuit3 V) (x : Cube V) :
    C.eval x = true ↔ ∃ j ∈ C.top, C.middleEval j x = true := by
  classical
  simp [eval]

theorem bottomCount_le_gateCount (C : Circuit3 V) : C.bottomCount ≤ C.gateCount :=
  (Nat.le_add_right C.bottomCount C.middleCount).trans (Nat.le_succ _)

theorem middleCount_le_gateCount (C : Circuit3 V) : C.middleCount ≤ C.gateCount :=
  (Nat.le_add_left C.middleCount C.bottomCount).trans (Nat.le_succ _)

theorem middle_card_le_gateCount (C : Circuit3 V) (j : Fin C.middleCount) :
    (C.middle j).card ≤ C.gateCount := by
  exact (Finset.card_le_univ _).trans (by simpa using C.bottomCount_le_gateCount)

theorem top_card_le_gateCount (C : Circuit3 V) : C.top.card ≤ C.gateCount := by
  exact (Finset.card_le_univ _).trans (by simpa using C.middleCount_le_gateCount)

def subst (C : Circuit3 V) (s : V → Sum W Bool) : Circuit3 W where
  bottomCount := C.bottomCount
  middleCount := C.middleCount
  bottom i := (C.bottom i).map (GateInput.subst s)
  middle := C.middle
  top := C.top

@[simp] theorem gateCount_subst (C : Circuit3 V) (s : V → Sum W Bool) :
    (C.subst s).gateCount = C.gateCount := rfl

@[simp] theorem middleEval_subst (C : Circuit3 V) (s : V → Sum W Bool)
    (j : Fin C.middleCount) (x : Cube W) :
    (C.subst s).middleEval j x = C.middleEval j (GateInput.assignment s x) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [middleEval_eq_true, subst, RawClause.eval_map_subst]

@[simp] theorem eval_subst (C : Circuit3 V) (s : V → Sum W Bool) (x : Cube W) :
    (C.subst s).eval x = C.eval (GateInput.assignment s x) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [eval_eq_true, middleEval_eq_true, subst, RawClause.eval_map_subst]

theorem computes_subst (C : Circuit3 V) {f : Cube V → Bool} (h : C.Computes f)
    (s : V → Sum W Bool) :
    (C.subst s).Computes (fun x => f (GateInput.assignment s x)) := by
  intro x
  rw [eval_subst, h]

end Circuit3

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace DepthThreeLowerBound
namespace Interpolation

open BinaryAlgebra

def coefficientEncoding {r : ℕ} (p : Fin r → F2) (t : ℕ) :
    (Fin t → Fin r → Bool) ≃ (Fin t → InputQuotient p) :=
  Equiv.piCongrRight (fun _ =>
    (bitsEquivF2 (Fin r)).trans (coordinates p).toEquiv.symm)

@[simp] theorem coefficientEncoding_apply {r t : ℕ} (p : Fin r → F2)
    (β : Fin t → Fin r → Bool) (j : Fin t) :
    coefficientEncoding p t β j = encode p (fun i => bitValue (β j i)) := rfl

theorem finiteAvg_coefficientEncoding {r t : ℕ} (p : Fin r → F2)
    (Φ : (Fin t → InputQuotient p) → ℝ) :
    finiteAvg (fun β : Fin t → Fin r → Bool =>
      Φ (fun j => encode p (fun i => bitValue (β j i)))) = finiteAvg Φ :=
  finiteAvg_equiv (coefficientEncoding p t) Φ

theorem finiteAvg_degreeZero {r : ℕ} (p : Fin r → F2) (hr : 0 < r)
    (Φ : F2 → ℝ) :
    finiteAvg (fun z : InputQuotient p => Φ (degreeZero (inputPolynomial_monic p) z)) =
      finiteAvg Φ := by
  classical
  exact AlgebraFiniteFibers.finiteAvg_comp
    (degreeZero (inputPolynomial_monic p)).toAddMonoidHom
    (degreeZero_surjective (inputPolynomial_monic p)
      (by simpa only [inputPolynomial_natDegree] using hr)) Φ

section Irreducible

variable {r t : ℕ} (p : Fin r → F2)
variable [Fact (Irreducible (inputPolynomial p))]
variable (hr : 0 < r)
variable {ι : Type uDepth1} [Fintype ι] [DecidableEq ι]
variable (a : ι → InputQuotient p) (hsize : Fintype.card ι ≤ t)
variable (ha : Function.Injective a)

include hr hsize ha

theorem finiteAvg_quotient_acceptEval (Φ : (ι → Bool) → ℝ) :
    finiteAvg (fun β : Fin t → InputQuotient p =>
      Φ (acceptEval (degreeZero (inputPolynomial_monic p)) t a β)) = finiteAvg Φ := by
  exact finiteAvg_acceptEval (degreeZero (inputPolynomial_monic p))
    (degreeZero_one (inputPolynomial_monic p)
      (by simpa only [inputPolynomial_natDegree] using hr)) a hsize ha Φ

theorem finiteAvg_encoded_acceptEval (Φ : (ι → Bool) → ℝ) :
    finiteAvg (fun β : Fin t → Fin r → Bool =>
      Φ (acceptEval (degreeZero (inputPolynomial_monic p)) t a
        (fun j => encode p (fun i => bitValue (β j i))))) = finiteAvg Φ := by
  calc
    finiteAvg (fun β : Fin t → Fin r → Bool =>
        Φ (acceptEval (degreeZero (inputPolynomial_monic p)) t a
          (fun j => encode p (fun i => bitValue (β j i))))) =
        finiteAvg (fun β : Fin t → InputQuotient p =>
          Φ (acceptEval (degreeZero (inputPolynomial_monic p)) t a β)) :=
      finiteAvg_coefficientEncoding p
        (fun β : Fin t → InputQuotient p =>
          Φ (acceptEval (degreeZero (inputPolynomial_monic p)) t a β))
    _ = finiteAvg Φ := finiteAvg_quotient_acceptEval p hr a hsize ha Φ

end Irreducible

theorem finiteAvg_encoded_acceptEval_finset {r t : ℕ} (p : Fin r → F2)
    [Fact (Irreducible (inputPolynomial p))] (hr : 0 < r) {Z : Type uDepth2} [DecidableEq Z]
    (a : Z → InputQuotient p) (s : Finset Z) (hsize : s.card ≤ t)
    (ha : Set.InjOn a (↑s : Set Z)) (Φ : (s → Bool) → ℝ) :
    finiteAvg (fun β : Fin t → Fin r → Bool =>
      Φ (fun z : s => acceptEval (degreeZero (inputPolynomial_monic p)) t a
        (fun j => encode p (fun i => bitValue (β j i))) z)) = finiteAvg Φ := by
  classical
  apply finiteAvg_encoded_acceptEval p hr (fun z : s => a z)
    (by simpa only [Fintype.card_coe] using hsize)
  intro x y hxy
  exact Subtype.ext (ha x.property y.property hxy)

end Interpolation
end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

def parameterSlice {n d r t : ℕ}
    (u : Fin (d + r - 1) → Bool) (p : Fin r → Bool)
    (b : Fin t → Fin r → Bool) : Fin n → Sum (Fin d) Bool :=
  fun i =>
    if hd : i.val < d then .inl ⟨i.val, hd⟩
    else if hu : i.val - d < d + r - 1 then .inr (u ⟨i.val - d, hu⟩)
    else if hp : i.val - (d + (d + r - 1)) < r then
      .inr (p ⟨i.val - (d + (d + r - 1)), hp⟩)
    else if hb : (i.val - (d + (d + r - 1) + r)) / r < t then
      if hi : (i.val - (d + (d + r - 1) + r)) % r < r then
        .inr (b ⟨(i.val - (d + (d + r - 1) + r)) / r, hb⟩
          ⟨(i.val - (d + (d + r - 1) + r)) % r, hi⟩)
      else .inr false
    else .inr false

theorem parameterSlice_data {n d r t : ℕ}
    (u : Fin (d + r - 1) → Bool) (p : Fin r → Bool)
    (b : Fin t → Fin r → Bool) (i : Fin d) (hn : i.val < n) :
    parameterSlice u p b ⟨i.val, hn⟩ = Sum.inl i := by
  simp [parameterSlice, i.is_lt]

theorem parameterSlice_hash {n d r t : ℕ}
    (u : Fin (d + r - 1) → Bool) (p : Fin r → Bool)
    (b : Fin t → Fin r → Bool) (i : Fin (d + r - 1))
    (hn : d + i.val < n) :
    parameterSlice u p b ⟨d + i.val, hn⟩ = Sum.inr (u i) := by
  have hd : ¬d + i.val < d := by omega
  simp [parameterSlice, hd, i.is_lt]

theorem parameterSlice_polynomial {n d r t : ℕ}
    (u : Fin (d + r - 1) → Bool) (p : Fin r → Bool)
    (b : Fin t → Fin r → Bool) (i : Fin r)
    (hn : d + (d + r - 1) + i.val < n) :
    parameterSlice u p b ⟨d + (d + r - 1) + i.val, hn⟩ = Sum.inr (p i) := by
  have hd : ¬d + (d + r - 1) + i.val < d := by omega
  have hu : ¬d + (d + r - 1) + i.val - d < d + r - 1 := by omega
  simp [parameterSlice, hd, hu, i.is_lt]

theorem parameterSlice_coefficient {n d r t : ℕ}
    (u : Fin (d + r - 1) → Bool) (p : Fin r → Bool)
    (b : Fin t → Fin r → Bool) (j : Fin t) (i : Fin r)
    (hn : d + (d + r - 1) + r + j.val * r + i.val < n) :
    parameterSlice u p b
        ⟨d + (d + r - 1) + r + j.val * r + i.val, hn⟩ =
      Sum.inr (b j i) := by
  have hr : 0 < r := Nat.zero_lt_of_lt i.is_lt
  have hd : ¬d + (d + r - 1) + r + j.val * r + i.val < d := by omega
  have hu : ¬d + (d + r - 1) + r + j.val * r + i.val - d < d + r - 1 := by
    omega
  have hp : ¬d + (d + r - 1) + r + j.val * r + i.val -
      (d + (d + r - 1)) < r := by omega
  have hs : d + (d + r - 1) + r + j.val * r + i.val -
      (d + (d + r - 1) + r) = j.val * r + i.val := by omega
  have hdiv : (j.val * r + i.val) / r = j.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt i.is_lt,
      Nat.zero_add]
  have hmod : (j.val * r + i.val) % r = i.val := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.is_lt]
  simp [parameterSlice, hd, hu, hp, hs, hdiv, hmod, j.is_lt, i.is_lt]

theorem parameterSlice_suffix {n d r t : ℕ}
    (u : Fin (d + r - 1) → Bool) (p : Fin r → Bool)
    (b : Fin t → Fin r → Bool) (i : Fin n)
    (hi : d + (d + r - 1) + r + t * r ≤ i.val) :
    parameterSlice u p b i = Sum.inr false := by
  have hd : ¬i.val < d := by omega
  have hu : ¬i.val - d < d + r - 1 := by omega
  have hp : ¬i.val - (d + (d + r - 1)) < r := by omega
  by_cases hr : r = 0
  · simp only [parameterSlice, dite_eq_right hd, dite_eq_right hu, dite_eq_right hp]
    simp [hr]
  · have hr' : 0 < r := Nat.pos_of_ne_zero hr
    have hmul : t * r ≤ i.val - (d + (d + r - 1) + r) := by omega
    have hdiv : t ≤ (i.val - (d + (d + r - 1) + r)) / r :=
      (Nat.le_div_iff_mul_le hr').2 hmul
    simp [parameterSlice, hd, hu, hp, Nat.not_lt.mpr hdiv]

def sliceParsedInput (n : ℕ)
    (u : Fin (dataDimension n + hashDimension (dataDimension n) - 1) → Bool)
    (p : Fin (hashDimension (dataDimension n)) → Bool)
    (b : Fin (independenceOrder (dataDimension n)) →
      Fin (hashDimension (dataDimension n)) → Bool)
    (x : Fin (dataDimension n) → Bool) : ParsedInput where
  dataSize := dataDimension n
  ringDegree := hashDimension (dataDimension n)
  coefficientCount := independenceOrder (dataDimension n)
  data := x
  hashSeed := u
  polynomial := p
  coefficients := b

def canonicalSlice (n : ℕ)
    (u : Fin (dataDimension n + hashDimension (dataDimension n) - 1) → Bool)
    (p : Fin (hashDimension (dataDimension n)) → Bool)
    (b : Fin (independenceOrder (dataDimension n)) →
      Fin (hashDimension (dataDimension n)) → Bool) :
    Fin n → Sum (Fin (dataDimension n)) Bool := parameterSlice u p b

def canonicalSliceWord (n : ℕ)
    (u : Fin (dataDimension n + hashDimension (dataDimension n) - 1) → Bool)
    (p : Fin (hashDimension (dataDimension n)) → Bool)
    (b : Fin (independenceOrder (dataDimension n)) →
      Fin (hashDimension (dataDimension n)) → Bool)
    (x : Fin (dataDimension n) → Bool) : List Bool :=
  List.ofFn (GateInput.assignment (canonicalSlice n u p b) x)

@[simp] theorem canonicalSliceWord_length (n : ℕ) (u p b x) :
    (canonicalSliceWord n u p b x).length = n := List.length_ofFn

theorem canonicalSlice_first (n : ℕ) (u p b) (i : Fin (dataDimension n)) :
    canonicalSlice n u p b
      ⟨i.val, i.is_lt.trans_le (Nat.div_le_self n 5)⟩ = Sum.inl i :=
  parameterSlice_data u p b i _

theorem canonicalSlice_unused (n : ℕ) (u p b) (i : Fin n)
    (hi : blockLen (dataDimension n) ≤ i.val) :
    canonicalSlice n u p b i = Sum.inr false := by
  apply parameterSlice_suffix
  simpa only [blockLen_eq_sum] using hi

private theorem getD_ofFn_at {n : ℕ} (f : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, List.length_ofFn, hi]

theorem canonicalSliceWord_fits (n : ℕ) (u p b x)
    (hd : 0 < dataDimension n)
    (ht : 2 ≤ independenceOrder (dataDimension n))
    (hlen : blockLen (dataDimension n) ≤ n) :
    InputFits (canonicalSliceWord n u p b x) := by
  simpa only [InputFits, canonicalSliceWord_length] using And.intro hd (And.intro ht hlen)

theorem decodeInput_canonicalSliceWord (n : ℕ) (u p b x)
    (_hd : 0 < dataDimension n)
    (_ht : 2 ≤ independenceOrder (dataDimension n))
    (hlen : blockLen (dataDimension n) ≤ n) :
    decodeInput (canonicalSliceWord n u p b x) = sliceParsedInput n u p b x := by
  let readAtLength (m : ℕ) : ParsedInput :=
    { dataSize := dataDimension m
      ringDegree := hashDimension (dataDimension m)
      coefficientCount := independenceOrder (dataDimension m)
      data := fun i => (canonicalSliceWord n u p b x).getD i.val false
      hashSeed := fun i => (canonicalSliceWord n u p b x).getD
        (hashOffset (dataDimension m) + i.val) false
      polynomial := fun i => (canonicalSliceWord n u p b x).getD
        (polynomialOffset (dataDimension m) + i.val) false
      coefficients := fun j i => (canonicalSliceWord n u p b x).getD
        (coefficientOffset (dataDimension m) j.val + i.val) false }
  change readAtLength (canonicalSliceWord n u p b x).length = _
  rw [canonicalSliceWord_length]
  dsimp only [readAtLength, sliceParsedInput]
  congr 1
  · funext i
    have hi : i.val < n := i.is_lt.trans_le (Nat.div_le_self n 5)
    rw [canonicalSliceWord, getD_ofFn_at _ _ hi]
    simp [GateInput.assignment, canonicalSlice_first]
  · funext i
    have hi : hashOffset (dataDimension n) + i.val < n := by
      exact (Nat.add_lt_add_left i.is_lt _).trans_le
        ((polynomialOffset_le_coefficientsOffset _).trans
          ((coefficientsOffset_le_blockLen _).trans hlen))
    rw [canonicalSliceWord, getD_ofFn_at _ _ hi]
    have hi' : dataDimension n + i.val < n := by
      simpa only [hashOffset] using hi
    change GateInput.assignment (parameterSlice u p b) x
      ⟨dataDimension n + i.val, hi'⟩ = u i
    rw [GateInput.assignment, parameterSlice_hash]
  · funext i
    have hi : polynomialOffset (dataDimension n) + i.val < n := by
      exact (polynomial_index_lt i.is_lt).trans_le
        ((coefficientsOffset_le_blockLen _).trans hlen)
    rw [canonicalSliceWord, getD_ofFn_at _ _ hi]
    have hi' : dataDimension n +
        (dataDimension n + hashDimension (dataDimension n) - 1) + i.val < n := by
      simpa only [polynomialOffset_eq] using hi
    change GateInput.assignment (parameterSlice u p b) x
      ⟨dataDimension n + (dataDimension n + hashDimension (dataDimension n) - 1) +
        i.val, hi'⟩ = p i
    rw [GateInput.assignment, parameterSlice_polynomial]
  · funext j i
    have hi : coefficientOffset (dataDimension n) j.val + i.val < n := by
      exact (coefficient_index_lt j.is_lt i.is_lt).trans_le hlen
    rw [canonicalSliceWord, getD_ofFn_at _ _ hi]
    have hi' : dataDimension n +
        (dataDimension n + hashDimension (dataDimension n) - 1) +
        hashDimension (dataDimension n) + j.val * hashDimension (dataDimension n) +
        i.val < n := by
      simpa only [coefficientOffset, coefficientsOffset_eq] using hi
    change GateInput.assignment (parameterSlice u p b) x
      ⟨dataDimension n + (dataDimension n + hashDimension (dataDimension n) - 1) +
        hashDimension (dataDimension n) + j.val * hashDimension (dataDimension n) +
        i.val, hi'⟩ = b j i
    rw [GateInput.assignment, parameterSlice_coefficient]

theorem language_canonicalSliceWord (n : ℕ) (u p b x)
    (hd : 0 < dataDimension n)
    (ht : 2 ≤ independenceOrder (dataDimension n))
    (hlen : blockLen (dataDimension n) ≤ n) :
    language (canonicalSliceWord n u p b x) = (sliceParsedInput n u p b x).evaluate := by
  rw [language_of_fits (canonicalSliceWord_fits n u p b x hd ht hlen),
    decodeInput_canonicalSliceWord n u p b x hd ht hlen]

theorem language_ofFn_canonicalSlice (n : ℕ) (u p b x)
    (hd : 0 < dataDimension n)
    (ht : 2 ≤ independenceOrder (dataDimension n))
    (hlen : blockLen (dataDimension n) ≤ n) :
    language (List.ofFn (GateInput.assignment (canonicalSlice n u p b) x)) =
      (sliceParsedInput n u p b x).evaluate :=
  language_canonicalSliceWord n u p b x hd ht hlen

theorem language_canonicalSlice_quotient (n : ℕ) (u p b x)
    (hd : 0 < dataDimension n)
    (ht : 2 ≤ independenceOrder (dataDimension n))
    (hlen : blockLen (dataDimension n) ≤ n) :
    language (List.ofFn (GateInput.assignment (canonicalSlice n u p b) x)) = true ↔
      BinaryAlgebra.degreeZero (sliceParsedInput n u p b x).modulus_monic
        (sliceParsedInput n u p b x).quotientEvaluation = 0 := by
  rw [language_ofFn_canonicalSlice n u p b x hd ht hlen,
    ParsedInput.evaluate_eq_true_iff_degreeZero]

theorem language_canonicalSlice_acceptEval (n : ℕ)
    (u : Fin (dataDimension n + hashDimension (dataDimension n) - 1) → Bool)
    (p : Fin (hashDimension (dataDimension n)) → Bool)
    (b : Fin (independenceOrder (dataDimension n)) →
      Fin (hashDimension (dataDimension n)) → Bool)
    (x : Fin (dataDimension n) → Bool)
    [Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p))]
    (hd : 0 < dataDimension n)
    (ht : 2 ≤ independenceOrder (dataDimension n))
    (hlen : blockLen (dataDimension n) ≤ n) :
    language (List.ofFn (GateInput.assignment (canonicalSlice n u p b) x)) =
      Interpolation.acceptEval
        (BinaryAlgebra.degreeZero (BinaryAlgebra.inputPolynomialBits_monic p))
        (independenceOrder (dataDimension n))
        (fun y : Fin (dataDimension n) → Bool =>
          BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
            (fun i => BinaryAlgebra.bitValue (BinaryHash.hashBool u y i)))
        (fun j => BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
          (fun i => BinaryAlgebra.bitValue (b j i))) x := by
  apply Bool.eq_iff_iff.mpr
  exact (language_canonicalSlice_quotient n u p b x hd ht hlen).trans
    (Interpolation.acceptEval_eq_true
      (BinaryAlgebra.degreeZero (BinaryAlgebra.inputPolynomialBits_monic p))
      (independenceOrder (dataDimension n))
      (fun y : Fin (dataDimension n) → Bool =>
        BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
          (fun i => BinaryAlgebra.bitValue (BinaryHash.hashBool u y i)))
      (fun j => BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
        (fun i => BinaryAlgebra.bitValue (b j i))) x).symm

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

theorem exists_good_language_slice_eventually (b : ℕ) (hb : 1 ≤ b)
    (B : ℝ) (hB : 0 < B) :
    ∃ N : ℕ, 20480 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ α : Fin n → Sum (Fin (dataDimension n)) Bool,
        restrictionAvg (liveProbability B (dataDimension n)) (fun σ =>
          if ¬ goodRestriction (liveProbability B (dataDimension n))
            ((2 : ℝ) ^ (-(B * Real.sqrt (dataDimension n : ℝ)) / 16)) b
            (fun x => language (List.ofFn (GateInput.assignment α x))) σ
          then 1 else 0) ≤
          4 * (2 : ℝ) ^ (-(B * Real.sqrt (dataDimension n : ℝ)) / 16) := by
  obtain ⟨De, hDe, herr⟩ := actual_hard_slice_error_bound_eventually b hb B hB
  obtain ⟨Dp, hDp, hprob⟩ := exists_liveProbability_threshold B hB
  let D := max De Dp
  refine ⟨5 * D, ?_, ?_⟩
  · have hbig : 4096 ≤ D := hDe.trans (le_max_left _ _)
    omega
  intro n hn
  let d := dataDimension n
  have hDd : D ≤ d := by
    dsimp [d, dataDimension]
    omega
  have hde : De ≤ d := (le_max_left _ _).trans hDd
  have hdp : Dp ≤ d := (le_max_right _ _).trans hDd
  have hd4096 : 4096 ≤ d := hDe.trans hde
  have hdpos : 0 < d := by omega
  have hr : 0 < hashDimension d := hashDimension_pos hdpos
  have ht2 : 2 ≤ independenceOrder d := (independenceOrder_two_le_iff d).mpr (by omega)
  obtain ⟨h, hh⟩ := independenceOrder_even d
  have heven : 2 * h = independenceOrder d := by omega
  have hhpos : 0 < h := by omega
  obtain ⟨hq0, hqhalf⟩ := hprob d hdp
  have hq1 : liveProbability B d ≤ 1 := by linarith
  obtain ⟨p, hp⟩ := exists_irreducible_inputPolynomialBits (hashDimension d) hr
  let : Fact (Irreducible (BinaryAlgebra.inputPolynomialBits p)) := ⟨hp⟩
  have hbound (m : ℕ)
      (hmlo : (liveProbability B d * d) / 2 ≤ (m : ℝ))
      (hmhi : (m : ℝ) ≤ 2 * (liveProbability B d * d)) :
      (2 : ℝ) ^ m / (2 : ℝ) ^ hashDimension d +
        sparseMomentBound m b (hardSliceSparseConstant b hb * m) h
          ((2 : ℝ) ^ (-(m : ℝ) / 4)) ≤
        2 * (2 : ℝ) ^ (-(liveProbability B d * d) / 16) := by
    rw [liveProbability_mul_dimension B d hdpos] at hmlo hmhi ⊢
    exact herr d hde m h hmlo hmhi heven
  have hex : ∃ (u : Fin (d + hashDimension d - 1) → Bool)
      (β : Fin (independenceOrder d) → BinaryAlgebra.BitQuotient p),
      restrictionAvg (liveProbability B d) (fun σ =>
        if ¬ goodRestriction (liveProbability B d)
          ((2 : ℝ) ^ (-(B * Real.sqrt (d : ℝ)) / 16)) b
          (hashAcceptance p (independenceOrder d) u β) σ then 1 else 0) ≤
        4 * (2 : ℝ) ^ (-(B * Real.sqrt (d : ℝ)) / 16) := by
    rw [← heven]
    simpa only [liveProbability_mul_dimension B d hdpos] using
      exists_good_hash_coefficients p hr hb hhpos (liveProbability B d) hq0.le hq1 hbound
  obtain ⟨u, β, hβ⟩ := hex
  let c := coefficientInputBits p β
  let α : Fin n → Sum (Fin (dataDimension n)) Bool := canonicalSlice n u p c
  have hfit : blockLen d ≤ n :=
    (blockLen_le_five_mul d hd4096).trans (five_mul_dataDimension_le n)
  have heval : (fun x => language (List.ofFn (GateInput.assignment α x))) =
      hashAcceptance p (independenceOrder d) u β := by
    funext x
    rw [language_canonicalSlice_acceptEval n u p c x hdpos ht2 hfit]
    change hashAcceptance p (independenceOrder d) u
      (fun j => BinaryAlgebra.encode (fun i => BinaryAlgebra.bitValue (p i))
        (fun i => BinaryAlgebra.bitValue (coefficientInputBits p β j i))) x = _
    rw [hashAcceptance_coefficientInputBits]
  refine ⟨α, ?_⟩
  rw [heval]
  exact hβ

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

open scoped BigOperators

variable {V : Type uDepth1} {I : Type uDepth2} [DecidableEq V] [instDecidableEqI : DecidableEq I]

def revealed (scope : I → Finset V) (T : Finset V) (P : List I) : Finset V :=
  P.toFinset.biUnion fun i => scope i ∩ T

def residual (scope : I → Finset V) (T U : Finset V) (i : I) : Finset V :=
  scope i ∩ (T \ U)

@[simp] theorem revealed_nil (scope : I → Finset V) (T : Finset V) :
    revealed scope T [] = ∅ := by simp [revealed]

theorem mem_revealed (scope : I → Finset V) (T : Finset V) (P : List I) (v : V) :
    v ∈ revealed scope T P ↔ ∃ i ∈ P, v ∈ scope i ∧ v ∈ T := by
  simp [revealed]

theorem revealed_subset (scope : I → Finset V) (T : Finset V) (P : List I) :
    revealed scope T P ⊆ T := by
  intro v hv
  obtain ⟨i, hi, hv, ht⟩ := (mem_revealed scope T P v).mp hv
  exact ht

theorem revealed_mono (scope : I → Finset V) (T : Finset V) {P Q : List I}
    (h : P ⊆ Q) : revealed scope T P ⊆ revealed scope T Q := by
  intro v hv
  obtain ⟨i, hi, hv, ht⟩ := (mem_revealed scope T P v).mp hv
  exact (mem_revealed scope T Q v).mpr ⟨i, h hi, hv, ht⟩

@[simp] theorem revealed_snoc (scope : I → Finset V) (T : Finset V)
    (P : List I) (i : I) :
    revealed scope T (P ++ [i]) = revealed scope T P ∪ (scope i ∩ T) := by
  ext v
  simp only [mem_revealed, List.mem_append, List.mem_singleton,
    Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro ⟨j, hj, hv⟩
    rcases hj with hj | rfl
    · exact Or.inl ⟨j, hj, hv⟩
    · exact Or.inr hv
  · rintro (⟨j, hj, hv⟩ | hv)
    · exact ⟨j, Or.inl hj, hv⟩
    · exact ⟨i, Or.inr rfl, hv⟩

theorem residual_eq_sdiff
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [DecidableEq I]
    (scope : I → Finset V) (T U : Finset V) (i : I) :
    residual scope T U i = (scope i ∩ T) \ U := by
  ext v
  simp [residual, and_assoc]

theorem residual_eq_empty_of_mem {scope : I → Finset V} {T : Finset V}
    {P : List I} {i : I} (hi : i ∈ P) :
    residual scope T (revealed scope T P) i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [residual, Finset.mem_inter, Finset.mem_sdiff] at hv
  exact hv.2.2 ((mem_revealed scope T P v).mpr ⟨i, hi, hv.1, hv.2.1⟩)

theorem card_revealed_snoc (scope : I → Finset V) (T : Finset V)
    (P : List I) (i : I) :
    (revealed scope T (P ++ [i])).card =
      (revealed scope T P).card + (residual scope T (revealed scope T P) i).card := by
  rw [revealed_snoc, residual_eq_sdiff, Finset.union_comm]
  exact (Finset.card_sdiff_add_card (scope i ∩ T) (revealed scope T P)).symm.trans
    (Nat.add_comm _ _)

variable [Fintype I]

def hardIndices (scope : I → Finset V) (T : Finset V) (b : ℕ) (U : Finset V) :
    Finset I := Finset.univ.filter fun i => b < (residual scope T U i).card

@[simp] theorem mem_hardIndices
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [DecidableEq I]
    [Fintype I]
    (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (U : Finset V) (i : I) :
    i ∈ hardIndices scope T b U ↔ b < (residual scope T U i).card := by
  simp [hardIndices]

def paths (scope : I → Finset V) (T : Finset V) (b : ℕ) : ℕ → Finset (List I)
  | 0 => {[]}
  | n + 1 => (paths scope T b n).biUnion fun P =>
      (hardIndices scope T b (revealed scope T P)).image fun i => P ++ [i]

@[simp] theorem paths_zero (scope : I → Finset V) (T : Finset V) (b : ℕ) :
    paths scope T b 0 = {[]} := rfl

theorem paths_succ (scope : I → Finset V) (T : Finset V) (b n : ℕ) :
    paths scope T b (n + 1) = (paths scope T b n).biUnion fun P =>
      (hardIndices scope T b (revealed scope T P)).image fun i => P ++ [i] := rfl

@[simp] theorem mem_paths_zero (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (P : List I) : P ∈ paths scope T b 0 ↔ P = [] := by
  simp [paths]

theorem mem_paths_succ {scope : I → Finset V} {T : Finset V}
    {b n : ℕ} {P : List I} :
    P ∈ paths scope T b (n + 1) ↔
      ∃ Q ∈ paths scope T b n, ∃ i ∈ hardIndices scope T b (revealed scope T Q),
        Q ++ [i] = P := by
  simp only [paths_succ, Finset.mem_biUnion, Finset.mem_image]

theorem snoc_mem_paths (scope : I → Finset V) (T : Finset V)
    (b : ℕ) {n : ℕ} {P : List I} {i : I}
    (hP : P ∈ paths scope T b n)
    (hi : i ∈ hardIndices scope T b (revealed scope T P)) :
    P ++ [i] ∈ paths scope T b (n + 1) :=
  mem_paths_succ.mpr ⟨P, hP, i, hi, rfl⟩

theorem mem_paths_snoc_iff (scope : I → Finset V) (T : Finset V)
    (b n : ℕ) (P : List I) (i : I) :
    P ++ [i] ∈ paths scope T b (n + 1) ↔
      P ∈ paths scope T b n ∧ i ∈ hardIndices scope T b (revealed scope T P) := by
  constructor
  · intro h
    obtain ⟨Q, hQ, j, hj, heq⟩ := mem_paths_succ.mp h
    obtain ⟨hQP, hji⟩ := List.append_inj' heq rfl
    have hji' : j = i := by simpa using hji
    subst Q
    subst j
    exact ⟨hQ, hj⟩
  · rintro ⟨hP, hi⟩
    exact snoc_mem_paths scope T b hP hi

theorem length_of_mem_paths {scope : I → Finset V} {T : Finset V}
    {b : ℕ} {n : ℕ} {P : List I} (hP : P ∈ paths scope T b n) :
    P.length = n := by
  induction n generalizing P with
  | zero =>
      have h := (mem_paths_zero scope T b P).mp hP
      subst P
      rfl
  | succ n ih =>
      obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
      simp [ih hQ]

theorem take_mem_paths (scope : I → Finset V) (T : Finset V)
    (b : ℕ) {n : ℕ} {P : List I} (hP : P ∈ paths scope T b n)
    {k : ℕ} (hk : k ≤ n) : P.take k ∈ paths scope T b k := by
  induction n generalizing P k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp
  | succ n ih =>
      obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
      by_cases hkn : k ≤ n
      · rw [List.take_append_of_le_length (by simpa [length_of_mem_paths hQ]
          using hkn)]
        exact ih hQ hkn
      · have hk' : k = n + 1 := by omega
        subst k
        rw [List.take_of_length_le (by simp [length_of_mem_paths hQ])]
        exact snoc_mem_paths scope T b hQ hi

theorem not_mem_of_hard (scope : I → Finset V) (T : Finset V)
    (b : ℕ) {P : List I} {i : I}
    (hi : i ∈ hardIndices scope T b (revealed scope T P)) : i ∉ P := by
  intro hmem
  have hh := (mem_hardIndices scope T b (revealed scope T P) i).mp hi
  rw [residual_eq_empty_of_mem hmem, Finset.card_empty] at hh
  exact Nat.not_lt_zero _ hh

theorem nodup_of_mem_paths {scope : I → Finset V} {T : Finset V}
    {b : ℕ} {n : ℕ} {P : List I} (hP : P ∈ paths scope T b n) : P.Nodup := by
  induction n generalizing P with
  | zero =>
      have h := (mem_paths_zero scope T b P).mp hP
      subst P
      simp
  | succ n ih =>
      obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
      exact (ih hQ).append (List.nodup_singleton i)
        (List.disjoint_singleton.mpr (not_mem_of_hard scope T b hi))

theorem mul_le_revealed_card (scope : I → Finset V) (T : Finset V)
    (b : ℕ) {n : ℕ} {P : List I} (hP : P ∈ paths scope T b n) :
    n * (b + 1) ≤ (revealed scope T P).card := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
      obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
      rw [Nat.succ_mul, card_revealed_snoc]
      exact Nat.add_le_add (ih hQ)
        (Nat.succ_le_of_lt ((mem_hardIndices scope T b (revealed scope T Q) i).mp hi))

theorem length_mul_le_revealed_card (scope : I → Finset V) (T : Finset V)
    (b : ℕ) {n : ℕ} {P : List I} (hP : P ∈ paths scope T b n) :
    P.length * (b + 1) ≤ (revealed scope T P).card := by
  rw [length_of_mem_paths hP]
  exact mul_le_revealed_card scope T b hP

theorem paths_eq_empty_of_card_lt (scope : I → Finset V) (T : Finset V)
    (b n : ℕ) (hn : T.card < n * (b + 1)) : paths scope T b n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro P hP
  have hle := (mul_le_revealed_card scope T b hP).trans
    (Finset.card_le_card (revealed_subset scope T P))
  exact (Nat.not_lt_of_ge hle) hn

theorem paths_horizon_eq_empty (scope : I → Finset V) (T : Finset V) (b : ℕ) :
    paths scope T b (T.card / (b + 1) + 1) = ∅ := by
  apply paths_eq_empty_of_card_lt
  exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos b)).mp (Nat.lt_succ_self _)

theorem sum_paths_succ (scope : I → Finset V) (T : Finset V) (b n : ℕ)
    {M : Type uDepth3} [AddCommMonoid M] (f : List I → M) :
    ∑ P ∈ paths scope T b (n + 1), f P =
      ∑ P ∈ paths scope T b n,
        ∑ i ∈ hardIndices scope T b (revealed scope T P), f (P ++ [i]) := by
  have hd : Set.PairwiseDisjoint (↑(paths scope T b n) : Set (List I))
      (fun P => (hardIndices scope T b (revealed scope T P)).image
        (fun i => P ++ [i])) := by
    intro P hP Q hQ hne
    apply Finset.disjoint_left.mpr
    intro R hR₁ hR₂
    obtain ⟨i, hi, hiR⟩ := Finset.mem_image.mp hR₁
    obtain ⟨j, hj, hjR⟩ := Finset.mem_image.mp hR₂
    exact hne (List.append_inj_left' (hiR.trans hjR.symm) rfl)
  rw [paths_succ, Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_image
  intro i hi j hj hij
  have h := List.append_inj_right' hij rfl
  simpa using h

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

noncomputable section

open Finset
open scoped BigOperators

namespace DepthThreeLowerBound


variable {V : Type u} {I : Type v} [DecidableEq V] [instDecidableEqI : DecidableEq I] [instFintypeI : Fintype I]

def violationValue (violation : I → Bool) (i : I) : ℝ :=
  if violation i = true then 1 else 0

def totalCount (violation : I → Bool) : ℕ :=
  (univ.filter fun i => violation i = true).card

def easyCount (scope : I → Finset V) (T : Finset V) (b : ℕ)
    (violation : I → Bool) (U : Finset V) : ℕ :=
  (univ.filter fun i => (residual scope T U i).card ≤ b ∧ violation i = true).card

def coveredCount (scope : I → Finset V) (T : Finset V)
    (violation : I → Bool) (U : Finset V) : ℕ :=
  (univ.filter fun i => residual scope T U i = ∅ ∧ violation i = true).card

def pathNumerator (violation : I → Bool) (P : List I) : ℝ :=
  (P.map (violationValue violation)).prod

def pathDenominator (scope : I → Finset V) (T : Finset V) (b : ℕ)
    (violation : I → Bool) (P : List I) : ℝ :=
  P.reverseRecOn 1 fun Q i d => d * (easyCount scope T b violation
    (revealed scope T (Q ++ [i])) : ℝ)

def pathTerm (scope : I → Finset V) (T : Finset V) (b : ℕ)
    (violation : I → Bool) (P : List I) : ℝ :=
  pathNumerator violation P / pathDenominator scope T b violation P

def pathResidual (scope : I → Finset V) (T : Finset V) (b : ℕ)
    (violation : I → Bool) (P : List I) : ℝ :=
  P.reverseRecOn 0 fun Q i _ => pathNumerator violation (Q ++ [i]) /
    ((totalCount violation : ℝ) * pathDenominator scope T b violation Q)

@[simp] theorem pathNumerator_nil
    {I : Type v}
    [DecidableEq I]
    [Fintype I]
    (violation : I → Bool) :
    pathNumerator violation [] = 1 := by simp [pathNumerator]

@[simp] theorem pathNumerator_snoc
    {I : Type v}
    [DecidableEq I]
    [Fintype I]
    (violation : I → Bool) (P : List I) (i : I) :
    pathNumerator violation (P ++ [i]) =
      pathNumerator violation P * violationValue violation i := by
  simp [pathNumerator]

@[simp] theorem pathDenominator_nil (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) : pathDenominator scope T b violation [] = 1 := by
  simp [pathDenominator]

@[simp] theorem pathDenominator_snoc (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (P : List I) (i : I) :
    pathDenominator scope T b violation (P ++ [i]) =
      pathDenominator scope T b violation P *
        (easyCount scope T b violation (revealed scope T (P ++ [i])) : ℝ) := by
  simp [pathDenominator]

@[simp] theorem pathResidual_snoc (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (P : List I) (i : I) :
    pathResidual scope T b violation (P ++ [i]) =
      pathNumerator violation (P ++ [i]) /
        ((totalCount violation : ℝ) * pathDenominator scope T b violation P) := by
  simp [pathResidual]

theorem pathNumerator_ne_zero_iff
    {I : Type v}
    [DecidableEq I]
    [Fintype I]
    (violation : I → Bool) (P : List I) :
    pathNumerator violation P ≠ 0 ↔ ∀ i ∈ P, violation i = true := by
  induction P with
  | nil => simp [pathNumerator]
  | cons i P ih =>
      have hi : violationValue violation i ≠ 0 ↔ violation i = true := by
        cases h : violation i <;> simp [violationValue, h]
      simpa only [pathNumerator, List.map_cons, List.prod_cons, mul_ne_zero_iff,
        List.forall_mem_cons] using and_congr hi ih

theorem coveredCount_le_easyCount
    {V : Type u}
    {I : Type v}
    [DecidableEq V]
    [DecidableEq I]
    [instFintypeI : Fintype I]
    (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (U : Finset V) :
    coveredCount scope T violation U ≤ easyCount scope T b violation U := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨by rw [hi.1]; simp, hi.2⟩

theorem easyCount_le_totalCount
    {V : Type u}
    {I : Type v}
    [DecidableEq V]
    [DecidableEq I]
    [instFintypeI : Fintype I]
    (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (U : Finset V) :
    easyCount scope T b violation U ≤ totalCount violation := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.2

theorem length_le_coveredCount_of_support (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) {n : ℕ} {P : List I}
    (hP : P ∈ paths scope T b n) (hs : pathNumerator violation P ≠ 0) :
    P.length ≤ coveredCount scope T violation (revealed scope T P) := by
  have hnd := nodup_of_mem_paths hP
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro i hi
  have him : i ∈ P := List.mem_toFinset.mp hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨residual_eq_empty_of_mem him, (pathNumerator_ne_zero_iff violation P).mp hs i him⟩

theorem easyCount_pos_of_support (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) {n : ℕ} {P : List I}
    (hP : P ∈ paths scope T b (n + 1)) (hs : pathNumerator violation P ≠ 0) :
    0 < easyCount scope T b violation (revealed scope T P) := by
  have h := (length_le_coveredCount_of_support scope T b violation hP hs).trans
    (coveredCount_le_easyCount scope T b violation _)
  rw [length_of_mem_paths hP] at h
  exact (Nat.succ_pos n).trans_le h

theorem pathDenominator_pos_of_support (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) {n : ℕ} {P : List I}
    (hP : P ∈ paths scope T b n) (hs : pathNumerator violation P ≠ 0) :
    0 < pathDenominator scope T b violation P := by
  induction n generalizing P with
  | zero =>
      have he : P = [] := List.length_eq_zero_iff.mp (length_of_mem_paths hP)
      subst P
      simp
  | succ n ih =>
      obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
      have hQs : pathNumerator violation Q ≠ 0 := by
        exact (mul_ne_zero_iff.mp (by simpa only [pathNumerator_snoc] using hs)).1
      rw [pathDenominator_snoc]
      exact mul_pos (ih hQ hQs)
        (Nat.cast_pos.mpr (easyCount_pos_of_support scope T b violation hP hs))

private theorem cast_count
    {I : Type v}
    [DecidableEq I]
    [Fintype I]
    (violation : I → Bool) (s : Finset I) :
    ((s.filter fun i => violation i = true).card : ℝ) =
      ∑ i ∈ s, violationValue violation i := by
  simp [violationValue]

theorem totalCount_eq_easy_add_hard (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (U : Finset V) :
    (totalCount violation : ℝ) = (easyCount scope T b violation U : ℝ) +
      ∑ i ∈ hardIndices scope T b U, violationValue violation i := by
  have h := Finset.sum_filter_add_sum_filter_not (s := (univ : Finset I))
    (p := fun i => (residual scope T U i).card ≤ b) (violationValue violation)
  have heasy : (easyCount scope T b violation U : ℝ) =
      ∑ i ∈ univ.filter (fun i => (residual scope T U i).card ≤ b),
        violationValue violation i := by
    rw [← cast_count]
    simp [easyCount, Finset.filter_filter]
  rw [heasy]
  simpa only [totalCount, cast_count, hardIndices, not_le] using h.symm

theorem path_residual_identity (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) {n : ℕ} {P : List I}
    (hP : P ∈ paths scope T b (n + 1)) (hq : totalCount violation ≠ 0) :
    pathResidual scope T b violation P = pathTerm scope T b violation P -
      ∑ i ∈ hardIndices scope T b (revealed scope T P),
        pathResidual scope T b violation (P ++ [i]) := by
  by_cases hs : pathNumerator violation P = 0
  · obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
    simp only [pathResidual_snoc, pathTerm, hs, zero_div, pathNumerator_snoc,
      zero_mul, Finset.sum_const_zero, sub_zero]
  · have hd := ne_of_gt (pathDenominator_pos_of_support scope T b violation hP hs)
    have ha := ne_of_gt (Nat.cast_pos.mpr
      (easyCount_pos_of_support scope T b violation hP hs) :
        (0 : ℝ) < easyCount scope T b violation (revealed scope T P))
    have hqr : (totalCount violation : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
    have hext : (∑ i ∈ hardIndices scope T b (revealed scope T P),
        pathResidual scope T b violation (P ++ [i])) =
        pathNumerator violation P /
          ((totalCount violation : ℝ) * pathDenominator scope T b violation P) *
          ∑ i ∈ hardIndices scope T b (revealed scope T P), violationValue violation i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pathResidual_snoc, pathNumerator_snoc]
      ring
    rw [hext]
    have hcounts := totalCount_eq_easy_add_hard scope T b violation (revealed scope T P)
    have hsum : (∑ i ∈ hardIndices scope T b (revealed scope T P),
        violationValue violation i) = (totalCount violation : ℝ) -
          (easyCount scope T b violation (revealed scope T P) : ℝ) := by
      linarith
    rw [hsum]
    obtain ⟨Q, hQ, i, hi, rfl⟩ := mem_paths_succ.mp hP
    have hQnum : pathNumerator violation Q ≠ 0 :=
      (mul_ne_zero_iff.mp (by simpa only [pathNumerator_snoc] using hs)).1
    have hQden := ne_of_gt (pathDenominator_pos_of_support scope T b violation hQ hQnum)
    simp only [pathResidual_snoc, pathTerm, pathDenominator_snoc]
    have halg (z q d a : ℝ) (hq' : q ≠ 0) (hd' : d ≠ 0) (ha' : a ≠ 0) :
        z / (q * d) = z / (d * a) - z / (q * (d * a)) * (q - a) := by
      field_simp [hq', hd', ha']
      ; ring
    exact halg _ _ _ _ hqr hQden ha

theorem sum_path_residual_identity (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (n : ℕ) (hq : totalCount violation ≠ 0) :
    (∑ P ∈ paths scope T b (n + 1), pathResidual scope T b violation P) =
      (∑ P ∈ paths scope T b (n + 1), pathTerm scope T b violation P) -
        ∑ P ∈ paths scope T b (n + 2), pathResidual scope T b violation P := by
  calc
    _ = ∑ P ∈ paths scope T b (n + 1),
        (pathTerm scope T b violation P -
          ∑ i ∈ hardIndices scope T b (revealed scope T P),
            pathResidual scope T b violation (P ++ [i])) := by
      apply Finset.sum_congr rfl
      intro P hP
      exact path_residual_identity scope T b violation hP hq
    _ = _ := by
      rw [Finset.sum_sub_distrib,
        sum_paths_succ scope T b (n + 1) (pathResidual scope T b violation)]

theorem sum_initial_residual (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool)
    (he : easyCount scope T b violation ∅ = 0) (hq : totalCount violation ≠ 0) :
    (∑ P ∈ paths scope T b 1, pathResidual scope T b violation P) = 1 := by
  have hs (i : I) : pathResidual scope T b violation [i] =
      violationValue violation i / (totalCount violation : ℝ) := by
    change pathResidual scope T b violation ([] ++ [i]) = _
    rw [pathResidual_snoc, pathNumerator_snoc]
    simp
  have hcounts := totalCount_eq_easy_add_hard scope T b violation ∅
  have hsum : (∑ i ∈ hardIndices scope T b ∅, violationValue violation i) =
      (totalCount violation : ℝ) := by simpa [he] using hcounts.symm
  rw [show (1 : ℕ) = 0 + 1 by rfl, sum_paths_succ]
  simp only [paths, Finset.sum_singleton, revealed, List.toFinset_nil,
    Finset.biUnion_empty, List.nil_append, hs]
  rw [← Finset.sum_div, hsum, div_self (Nat.cast_ne_zero.mpr hq)]

theorem finite_alternating_telescoping (t r : ℕ → ℝ)
    (h : ∀ n, r (n + 1) = t (n + 1) - r (n + 2)) (N : ℕ) :
    (∑ j ∈ Finset.range N, (-1 : ℝ) ^ (j + 1) * t (j + 1)) =
      -r 1 + (-1 : ℝ) ^ N * r (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, h N]
      simp only [pow_succ]
      ring

theorem pathTerm_zero_of_totalCount_zero (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) {n : ℕ} {P : List I}
    (hP : P ∈ paths scope T b (n + 1)) (hq : totalCount violation = 0) :
    pathTerm scope T b violation P = 0 := by
  have hz : pathNumerator violation P = 0 := by
    by_contra hs
    have h := (length_le_coveredCount_of_support scope T b violation hP hs).trans
      ((coveredCount_le_easyCount scope T b violation _).trans
        (easyCount_le_totalCount scope T b violation _))
    rw [length_of_mem_paths hP, hq] at h
    omega
  simp [pathTerm, hz]

theorem finite_violation_expansion (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) :
    (if totalCount violation = 0 then (1 : ℝ) else 0) =
      (if easyCount scope T b violation ∅ = 0 then (1 : ℝ) else 0) *
        (1 + ∑ j ∈ Finset.range (T.card / (b + 1)),
          (-1 : ℝ) ^ (j + 1) *
            ∑ P ∈ paths scope T b (j + 1), pathTerm scope T b violation P) := by
  by_cases he : easyCount scope T b violation ∅ = 0
  · by_cases hq : totalCount violation = 0
    · have hz (j : ℕ) :
          (∑ P ∈ paths scope T b (j + 1), pathTerm scope T b violation P) = 0 := by
        apply Finset.sum_eq_zero
        intro P hP
        exact pathTerm_zero_of_totalCount_zero scope T b violation hP hq
      simp [he, hq, hz]
    · let t : ℕ → ℝ := fun j =>
        ∑ P ∈ paths scope T b j, pathTerm scope T b violation P
      let r : ℕ → ℝ := fun j =>
        ∑ P ∈ paths scope T b j, pathResidual scope T b violation P
      have hr : ∀ n, r (n + 1) = t (n + 1) - r (n + 2) :=
        fun n => sum_path_residual_identity scope T b violation n hq
      have hfirst : r 1 = 1 := sum_initial_residual scope T b violation he hq
      have hlast : r (T.card / (b + 1) + 1) = 0 := by
        dsimp [r]
        rw [paths_horizon_eq_empty]
        simp
      have htel := finite_alternating_telescoping t r hr (T.card / (b + 1))
      rw [hfirst, hlast, mul_zero, add_zero] at htel
      simp only [he, hq, ite_eq_left, ite_false, one_mul]
      change 0 = 1 + ∑ j ∈ Finset.range (T.card / (b + 1)),
        (-1 : ℝ) ^ (j + 1) * t (j + 1)
      rw [htel]
      norm_num
  · have hq : totalCount violation ≠ 0 := by
      intro hq
      apply he
      exact Nat.eq_zero_of_le_zero (hq ▸ easyCount_le_totalCount scope T b violation ∅)
    simp [he, hq]

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound


variable {V : Type u} {I : Type v} [DecidableEq V] [DecidableEq I] [Fintype I]

theorem pathDenominator_eq_prod_prefix (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (P : List I) :
    pathDenominator scope T b violation P =
      ∏ h : Fin P.length,
        (easyCount scope T b violation (revealed scope T (P.take (h.val + 1))) : ℝ) := by
  induction P using List.reverseRecOn with
  | nil => simp
  | append_singleton P i ih =>
      rw [pathDenominator_snoc, ih]
      rw [Fin.prod_univ_eq_prod_range
        (fun h : ℕ => (easyCount scope T b violation
          (revealed scope T (P.take (h + 1))) : ℝ)) P.length,
        Fin.prod_univ_eq_prod_range
          (fun h : ℕ => (easyCount scope T b violation
            (revealed scope T ((P ++ [i]).take (h + 1))) : ℝ)) (P ++ [i]).length]
      simp only [List.length_append, List.length_singleton, Finset.prod_range_succ]
      have hlast : (P ++ [i]).take (P.length + 1) = P ++ [i] :=
        List.take_of_length_le (by simp)
      rw [hlast]
      congr 1
      apply Finset.prod_congr rfl
      intro h hh
      rw [List.take_append_of_le_length
        (Nat.succ_le_of_lt (Finset.mem_range.mp hh))]

theorem pathNumerator_eq_indicator_support (violation : I → Bool) (P : List I) :
    pathNumerator violation P = if ∀ i ∈ P, violation i = true then 1 else 0 := by
  classical
  by_cases hs : ∀ i ∈ P, violation i = true
  · rw [ite_eq_left hs]
    unfold pathNumerator
    apply List.prod_eq_one
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    simp [violationValue, hs i hi]
  · rw [ite_eq_right hs]
    by_contra hne
    exact hs ((pathNumerator_ne_zero_iff violation P).mp hne)

theorem pathTerm_eq_support_prod_inv (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (violation : I → Bool) (P : List I) :
    pathTerm scope T b violation P =
      if ∀ i ∈ P, violation i = true then
        ∏ h : Fin P.length,
          (easyCount scope T b violation
            (revealed scope T (P.take (h.val + 1))) : ℝ)⁻¹
      else 0 := by
  classical
  by_cases hs : ∀ i ∈ P, violation i = true
  · simp only [pathTerm, pathNumerator_eq_indicator_support, ite_eq_left hs,
      pathDenominator_eq_prod_prefix, one_div, Finset.prod_inv_distrib]
  · simp only [pathTerm, pathNumerator_eq_indicator_support, ite_eq_right hs, zero_div]

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V]

def liveClause (σ : Restriction V) (C : Clause V) : Clause (Live σ) := by
  classical
  exact Finset.univ.filter fun l => ((l.1 : V), l.2) ∈ C

@[simp] theorem mem_liveClause (σ : Restriction V) (C : Clause V)
    (l : Literal (Live σ)) : l ∈ liveClause σ C ↔ ((l.1 : V), l.2) ∈ C := by
  classical
  simp [liveClause]

theorem liveClause_scope_image_subset (σ : Restriction V) (C : Clause V) :
    (liveClause σ C).scope.image Subtype.val ⊆ C.scope := by
  classical
  let : DecidableEq (Live σ) := Classical.decEq _
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨l, hl, hlw⟩ := Finset.mem_image.mp hw
  have hc : ((l.1 : V), l.2) ∈ C := (mem_liveClause σ C l).mp hl
  have hv : (l.1 : V) ∈ C.scope := Finset.mem_image_of_mem Prod.fst hc
  simpa only [hlw] using hv

theorem liveClause_width_le (σ : Restriction V) (C : Clause V) :
    (liveClause σ C).width ≤ C.width := by
  classical
  calc
    (liveClause σ C).width =
        ((liveClause σ C).scope.image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ C.scope.card := Finset.card_le_card (liveClause_scope_image_subset σ C)
    _ = C.width := rfl

theorem liveClause_normalized (σ : Restriction V) {C : Clause V}
    (hC : C.Normalized) : (liveClause σ C).Normalized := by
  intro v hf ht
  exact hC v.val ((mem_liveClause σ C (v, false)).mp hf)
    ((mem_liveClause σ C (v, true)).mp ht)

def restrictClause (σ : Restriction V) (C : Clause V) : Option (Clause (Live σ)) := by
  classical
  exact if ∃ l ∈ C, σ l.1 = some l.2 then none else some (liveClause σ C)

def residualClauseEval {W : Type uDepth2} (C : Option (Clause W)) (x : Cube W) : Bool :=
  match C with
  | none => true
  | some C => C.eval x

@[simp] theorem residualClauseEval_none {W : Type uDepth3} (x : Cube W) :
    residualClauseEval (none : Option (Clause W)) x = true := rfl

@[simp] theorem residualClauseEval_some {W : Type uDepth4} (C : Clause W) (x : Cube W) :
    residualClauseEval (some C) x = C.eval x := rfl

theorem restrictClause_eval (σ : Restriction V) (C : Clause V)
    (z : Cube (Live σ)) :
    residualClauseEval (restrictClause σ C) z = C.eval (fill σ z) := by
  classical
  by_cases hs : ∃ l ∈ C, σ l.1 = some l.2
  · simp only [restrictClause, ite_eq_left hs, residualClauseEval_none]
    symm
    obtain ⟨l, hl, hlσ⟩ := hs
    exact (Clause.eval_eq_true C (fill σ z)).mpr ⟨l, hl, fill_fixed σ z l.1 l.2 hlσ⟩
  · simp only [restrictClause, ite_eq_right hs, residualClauseEval_some]
    apply Bool.eq_iff_iff.mpr
    rw [Clause.eval_eq_true, Clause.eval_eq_true]
    constructor
    · rintro ⟨⟨v, b⟩, hl, hz⟩
      refine ⟨(v.val, b), (mem_liveClause σ C (v, b)).mp hl, ?_⟩
      exact (fill_live σ z v).trans hz
    · rintro ⟨⟨v, b⟩, hl, hz⟩
      have hv : σ v = none := by
        cases hσ : σ v with
        | none => rfl
        | some c =>
          have hcb : c = b := (fill_fixed σ z v c hσ).symm.trans hz
          have hf : ∃ l ∈ C, σ l.1 = some l.2 :=
            ⟨(v, b), hl, hσ.trans (congrArg some hcb)⟩
          exact (hs hf).elim
      refine ⟨(⟨v, hv⟩, b), (mem_liveClause σ C (⟨v, hv⟩, b)).mpr hl, ?_⟩
      exact (fill_live σ z ⟨v, hv⟩).symm.trans hz

theorem restrictClause_some_eq {σ : Restriction V} {C : Clause V}
    {D : Clause (Live σ)} (h : restrictClause σ C = some D) :
    D = liveClause σ C := by
  classical
  unfold restrictClause at h
  split at h
  · cases h
  · exact (Option.some.inj h).symm

theorem restrictClause_width_le {σ : Restriction V} {C : Clause V}
    {D : Clause (Live σ)} (h : restrictClause σ C = some D) : D.width ≤ C.width := by
  rw [restrictClause_some_eq h]
  exact liveClause_width_le σ C

theorem restrictClause_normalized {σ : Restriction V} {C : Clause V}
    {D : Clause (Live σ)} (hC : C.Normalized)
    (h : restrictClause σ C = some D) : D.Normalized := by
  rw [restrictClause_some_eq h]
  exact liveClause_normalized σ hC

@[simp] theorem restrictClause_empty (σ : Restriction V) :
    restrictClause σ (∅ : Clause V) = some ∅ := by
  classical
  simp [restrictClause, liveClause]

def residualCNF {W : Type uDepth5} (H : List (Option (Clause W))) : CNF W :=
  H.filterMap id

@[simp] theorem residualCNF_nil {W : Type uDepth6} :
    residualCNF ([] : List (Option (Clause W))) = [] := rfl

@[simp] theorem residualCNF_cons_none {W : Type uDepth7} (H : List (Option (Clause W))) :
    residualCNF (none :: H) = residualCNF H := rfl

@[simp] theorem residualCNF_cons_some {W : Type uDepth8} (C : Clause W)
    (H : List (Option (Clause W))) :
    residualCNF (some C :: H) = C :: residualCNF H := rfl

theorem residualCNF_eval_cons {W : Type uDepth9} (C : Option (Clause W))
    (H : List (Option (Clause W))) (x : Cube W) :
    (residualCNF (C :: H)).eval x =
      (residualClauseEval C x && (residualCNF H).eval x) := by
  cases C <;> simp

def restrictCNF (σ : Restriction V) (H : CNF V) : CNF (Live σ) :=
  H.filterMap (restrictClause σ)

@[simp] theorem restrictCNF_eval (σ : Restriction V) (H : CNF V)
    (z : Cube (Live σ)) : (restrictCNF σ H).eval z = H.eval (fill σ z) := by
  induction H with
  | nil => simp [restrictCNF]
  | cons C H ih =>
    have he := restrictClause_eval σ C z
    unfold restrictCNF at ih
    cases hr : restrictClause σ C with
    | none =>
      simp only [hr, residualClauseEval_none] at he
      simp [restrictCNF, hr, ← he, ih]
    | some D =>
      simp only [hr, residualClauseEval_some] at he
      simp [restrictCNF, hr, ← he, ih]

theorem restrictCNF_widthAtMost (σ : Restriction V) {H : CNF V} {b : ℕ}
    (hH : H.WidthAtMost b) : (restrictCNF σ H).WidthAtMost b := by
  intro D hD
  obtain ⟨C, hC, hCD⟩ := List.mem_filterMap.mp hD
  exact (restrictClause_width_le hCD).trans (hH C hC)

theorem restrictCNF_normalized (σ : Restriction V) {H : CNF V}
    (hH : H.Normalized) : (restrictCNF σ H).Normalized := by
  intro D hD
  obtain ⟨C, hC, hCD⟩ := List.mem_filterMap.mp hD
  exact restrictClause_normalized (hH C hC) hCD

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [instDecidableEqV : DecidableEq V] [instDecidableEqI : DecidableEq I] [instFintypeI : Fintype I]

theorem Clause.eval_eq_of_scope_agree
    {V : Type uDepth1}
    [DecidableEq V]
    (C : Clause V) (x y : Cube V)
    (h : ∀ v ∈ C.scope, x v = y v) : C.eval x = C.eval y := by
  classical
  let : DecidableEq V := Classical.decEq _
  apply Bool.eq_iff_iff.mpr
  rw [Clause.eval_eq_true, Clause.eval_eq_true]
  constructor
  · rintro ⟨l, hl, hx⟩
    exact ⟨l, hl, (h l.1 (Finset.mem_image_of_mem Prod.fst hl)).symm.trans hx⟩
  · rintro ⟨l, hl, hy⟩
    exact ⟨l, hl, (h l.1 (Finset.mem_image_of_mem Prod.fst hl)).trans hy⟩

theorem Clause.violation_eq_of_scope_agree (C : Clause V) (x y : Cube V)
    (h : ∀ v ∈ C.scope, x v = y v) : C.violation x = C.violation y := by
  unfold Clause.violation
  rw [Clause.eval_eq_of_scope_agree C x y h]

theorem simultaneous_violation_iff_cylinder
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]
    [instDecidableEqI : DecidableEq I]
    [Fintype I]
    (C : I → Clause V) (T : Finset V) (P : List I) (x y : Cube V)
    (hn : ∀ i ∈ P, (C i).Normalized)
    (hy : ∀ i ∈ P, (C i).violation y = true)
    (hout : ∀ v ∉ T, x v = y v) :
    (∀ i ∈ P, (C i).violation x = true) ↔
      ∀ v ∈ revealed (fun i => (C i).scope) T P, x v = y v := by
  constructor
  · intro hx v hv
    obtain ⟨i, hi, hvi, hvt⟩ := (mem_revealed (fun i => (C i).scope) T P v).mp hv
    have hxv := (Clause.violation_eq_true_iff_forbidden (hn i hi) x).mp
      (hx i hi) v hvi
    have hyv := (Clause.violation_eq_true_iff_forbidden (hn i hi) y).mp
      (hy i hi) v hvi
    exact hxv.trans hyv.symm
  · intro hxy i hi
    apply (Clause.violation_eq_true_iff_forbidden (hn i hi) x).mpr
    intro v hv
    have hsame : x v = y v := by
      by_cases ht : v ∈ T
      · exact hxy v ((mem_revealed (fun i => (C i).scope) T P v).mpr
          ⟨i, hi, hv, ht⟩)
      · exact hout v ht
    exact hsame.trans ((Clause.violation_eq_true_iff_forbidden (hn i hi) y).mp
      (hy i hi) v hv)

theorem violation_eq_of_covered
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instDecidableEqV : DecidableEq V]
    [DecidableEq I]
    [Fintype I]
    (C : I → Clause V) (T U : Finset V) (x y : Cube V) (i : I)
    (hc : residual (fun i => (C i).scope) T U i = ∅)
    (hU : ∀ v ∈ U, x v = y v) (hout : ∀ v ∉ T, x v = y v) :
    (C i).violation x = (C i).violation y := by
  apply Clause.violation_eq_of_scope_agree
  intro v hv
  by_cases ht : v ∈ T
  · have hu : v ∈ U := by
      by_contra hu
      have hm : v ∈ residual (fun i => (C i).scope) T U i := by
        simp [residual, hv, ht, hu]
      rw [hc] at hm
      exact Finset.notMem_empty v hm
    exact hU v hu
  · exact hout v ht

theorem coveredCount_eq_of_agree
    (C : I → Clause V) (T U : Finset V) (x y : Cube V)
    (hU : ∀ v ∈ U, x v = y v) (hout : ∀ v ∉ T, x v = y v) :
    coveredCount (fun i => (C i).scope) T (fun i => (C i).violation x) U =
      coveredCount (fun i => (C i).scope) T (fun i => (C i).violation y) U := by
  unfold coveredCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hc, hv⟩
    exact ⟨hc, (violation_eq_of_covered C T U x y i hc hU hout).symm.trans hv⟩
  · rintro ⟨hc, hv⟩
    exact ⟨hc, (violation_eq_of_covered C T U x y i hc hU hout).trans hv⟩

theorem coveredCount_eq_on_larger_cylinder
    (C : I → Clause V) (T U Z : Finset V) (x y : Cube V) (hUZ : U ⊆ Z)
    (hZ : ∀ v ∈ Z, x v = y v) (hout : ∀ v ∉ T, x v = y v) :
    coveredCount (fun i => (C i).scope) T (fun i => (C i).violation x) U =
      coveredCount (fun i => (C i).scope) T (fun i => (C i).violation y) U :=
  coveredCount_eq_of_agree C T U x y (fun v hv => hZ v (hUZ hv)) hout

def cylinderCNF (U : Finset V) (pattern : Cube V) : CNF V :=
  U.toList.map fun v => ({(v, pattern v)} : Clause V)

@[simp] theorem cylinderCNF_eval_eq_true
    {V : Type uDepth1}
    [DecidableEq V]
    (U : Finset V) (pattern x : Cube V) :
    (cylinderCNF U pattern).eval x = true ↔ ∀ v ∈ U, x v = pattern v := by
  classical
  simp [cylinderCNF, CNF.eval_eq_true]

theorem cylinderCNF_eval (U : Finset V) (pattern x : Cube V) :
    (cylinderCNF U pattern).eval x = decide (∀ v ∈ U, x v = pattern v) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [cylinderCNF_eval_eq_true, decide_eq_true_eq]

theorem cylinderCNF_widthAtMost
    {V : Type uDepth1}
    [DecidableEq V]
    (U : Finset V) (pattern : Cube V)
    {b : ℕ} (hb : 1 ≤ b) : (cylinderCNF U pattern).WidthAtMost b := by
  intro C hC
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hC
  simpa [Clause.width, Clause.scope] using hb

theorem cylinderCNF_normalized
    {V : Type uDepth1}
    [DecidableEq V]
    (U : Finset V) (pattern : Cube V) :
    (cylinderCNF U pattern).Normalized := by
  intro C hC
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hC
  intro w hf ht
  have hf' : (w, false) = (v, pattern v) := Finset.mem_singleton.mp hf
  have ht' : (w, true) = (v, pattern v) := Finset.mem_singleton.mp ht
  have : (false : Bool) = true := congrArg Prod.snd (hf'.trans ht'.symm)
  cases this

section ActualRestriction

variable [instFintypeV : Fintype V]

theorem fill_agree_outside_live
    {V : Type uDepth1}
    [DecidableEq V]
    [Fintype V]
    (σ : Restriction V) (x y : Cube (Live σ))
    (v : V) (hv : σ v ≠ none) : fill σ x v = fill σ y v := by
  simp [fill, hv]

theorem simultaneous_restricted_violation_iff
    (C : I → Clause V) (σ : Restriction V) (T : Finset V)
    (hT : ∀ v, v ∈ T ↔ σ v = none) (P : List I)
    (x y : Cube (Live σ)) (hn : ∀ i ∈ P, (C i).Normalized)
    (hy : ∀ i ∈ P, (C i).violation (fill σ y) = true) :
    (∀ i ∈ P, (C i).violation (fill σ x) = true) ↔
      ∀ v ∈ revealed (fun i => (C i).scope) T P, fill σ x v = fill σ y v := by
  apply simultaneous_violation_iff_cylinder C T P (fill σ x) (fill σ y) hn hy
  intro v hv
  apply fill_agree_outside_live
  intro he
  exact hv ((hT v).mpr he)

end ActualRestriction

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1}

def keptLiterals (R : Finset V) (C : Clause V) : Clause V :=
  C.filter fun l => l.1 ∈ R

@[simp] theorem mem_keptLiterals (R : Finset V) (C : Clause V) (l : Literal V) :
    l ∈ keptLiterals R C ↔ l ∈ C ∧ l.1 ∈ R := by
  simp [keptLiterals]

theorem keptLiterals_scope (R : Finset V) (C : Clause V) :
    (keptLiterals R C).scope = C.scope ∩ R := by
  ext v
  simp only [Clause.scope, Finset.mem_image, Finset.mem_inter, mem_keptLiterals]
  constructor
  · rintro ⟨l, ⟨hl, hR⟩, hv⟩
    exact ⟨⟨l, hl, hv⟩, hv ▸ hR⟩
  · rintro ⟨⟨l, hl, hv⟩, hR⟩
    exact ⟨l, ⟨hl, hv.symm ▸ hR⟩, hv⟩

theorem keptLiterals_width (R : Finset V) (C : Clause V) :
    (keptLiterals R C).width = (C.scope ∩ R).card := by
  rw [Clause.width, keptLiterals_scope]

def keepClause (R : Finset V) (pattern : Cube V) (C : Clause V) :
    Option (Clause V) :=
  if ∃ l ∈ C, l.1 ∉ R ∧ pattern l.1 = l.2 then none else some (keptLiterals R C)

theorem keepClause_eval (R : Finset V) (pattern x : Cube V) (C : Clause V)
    (hagree : ∀ v ∉ R, x v = pattern v) :
    residualClauseEval (keepClause R pattern C) x = C.eval x := by
  by_cases hs : ∃ l ∈ C, l.1 ∉ R ∧ pattern l.1 = l.2
  · simp only [keepClause, ite_eq_left hs, residualClauseEval_none]
    symm
    obtain ⟨l, hl, hout, hp⟩ := hs
    exact (Clause.eval_eq_true C x).mpr ⟨l, hl, (hagree l.1 hout).trans hp⟩
  · simp only [keepClause, ite_eq_right hs, residualClauseEval_some]
    apply Bool.eq_iff_iff.mpr
    rw [Clause.eval_eq_true, Clause.eval_eq_true]
    constructor
    · rintro ⟨l, hl, hx⟩
      exact ⟨l, ((mem_keptLiterals R C l).mp hl).1, hx⟩
    · rintro ⟨l, hl, hx⟩
      have hR : l.1 ∈ R := by
        by_cases hr : l.1 ∈ R
        · exact hr
        · exact (hs ⟨l, hl, hr, (hagree l.1 hr).symm.trans hx⟩).elim
      exact ⟨l, (mem_keptLiterals R C l).mpr ⟨hl, hR⟩, hx⟩

theorem keepClause_some_eq {R : Finset V} {pattern : Cube V}
    {C D : Clause V} (h : keepClause R pattern C = some D) :
    D = keptLiterals R C := by
  unfold keepClause at h
  split at h
  · cases h
  · exact (Option.some.inj h).symm

theorem keepClause_width {R : Finset V} {pattern : Cube V}
    {C D : Clause V} (h : keepClause R pattern C = some D) :
    D.width = (C.scope ∩ R).card := by
  rw [keepClause_some_eq h, keptLiterals_width]

theorem keepClause_normalized {R : Finset V} {pattern : Cube V}
    {C D : Clause V} (hC : C.Normalized) (h : keepClause R pattern C = some D) :
    D.Normalized := by
  rw [keepClause_some_eq h]
  exact hC.subset (Finset.filter_subset _ _)

section Restrict

variable [Fintype V]

def keptRestrictedClause (σ : Restriction V) (R : Finset V)
    (pattern : Cube V) (C : Clause V) : Option (Clause (Live σ)) :=
  (keepClause R pattern C).bind (restrictClause σ)

theorem residualClauseEval_bind_restrict (σ : Restriction V)
    (C : Option (Clause V)) (x : Cube (Live σ)) :
    residualClauseEval (C.bind (restrictClause σ)) x =
      residualClauseEval C (fill σ x) := by
  cases C with
  | none => rfl
  | some C => exact restrictClause_eval σ C x

theorem keptRestrictedClause_eval (σ : Restriction V) (R : Finset V)
    (pattern : Cube V) (C : Clause V) (x : Cube (Live σ))
    (hagree : ∀ v ∉ R, fill σ x v = pattern v) :
    residualClauseEval (keptRestrictedClause σ R pattern C) x =
      C.eval (fill σ x) := by
  rw [keptRestrictedClause, residualClauseEval_bind_restrict]
  exact keepClause_eval R pattern (fill σ x) C hagree

theorem keptRestrictedClause_width_le {σ : Restriction V} {R : Finset V}
    {pattern : Cube V} {C : Clause V} {D : Clause (Live σ)}
    (h : keptRestrictedClause σ R pattern C = some D) :
    D.width ≤ (C.scope ∩ R).card := by
  unfold keptRestrictedClause at h
  cases he : keepClause R pattern C with
  | none => simp [he] at h
  | some E =>
    have hr : restrictClause σ E = some D := by simpa [he] using h
    rw [← keepClause_width he]
    exact restrictClause_width_le hr

end Restrict

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V]

theorem finiteAvg_eq_pattern (U : Finset V) (σ : Cube V) :
    finiteAvg (fun x : Cube V =>
      if ∀ v ∈ U, x v = σ v then (1 : ℝ) else 0) =
      ((2 : ℝ) ^ U.card)⁻¹ := by
  classical
  let q : V → Bool → ℝ := fun v b => if v ∈ U → b = σ v then 1 else 0
  have hpoint (x : Cube V) :
      (if ∀ v ∈ U, x v = σ v then (1 : ℝ) else 0) = ∏ v, q v (x v) := by
    dsimp [q]
    rw [Fintype.prod_boole]
  have hcoordinate (v : V) :
      finiteAvg (q v) = if v ∈ U then (2 : ℝ)⁻¹ else 1 := by
    by_cases hv : v ∈ U
    · cases hσ : σ v <;>
        norm_num [q, hv, hσ, finiteAvg, Fintype.sum_bool]
    · simp [q, hv]
  calc
    _ = finiteAvg (fun x : Cube V => ∏ v, q v (x v)) := finiteAvg_congr hpoint
    _ = ∏ v, finiteAvg (q v) := finiteAvg_pi_prod q
    _ = ∏ v, if v ∈ U then (2 : ℝ)⁻¹ else 1 := by
      exact Finset.prod_congr rfl (fun v _ => hcoordinate v)
    _ = ((2 : ℝ) ^ U.card)⁻¹ := by
      rw [← Finset.prod_filter]
      have hfilter : Finset.univ.filter (fun v => v ∈ U) = U := by
        ext v
        simp
      rw [hfilter, Finset.prod_const, inv_pow]

theorem finiteAvg_indicator_eq_pattern (U : Finset V) (σ : Cube V) :
    finiteAvg (fun x : Cube V => indicator (decide (∀ v ∈ U, x v = σ v))) =
      ((2 : ℝ) ^ U.card)⁻¹ := by
  refine (finiteAvg_congr fun x => ?_).trans (finiteAvg_eq_pattern U σ)
  by_cases hx : ∀ v ∈ U, x v = σ v <;> simp [indicator, hx]

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [instFintypeV : Fintype V] [instFintypeI : Fintype I]

def pathCompatible (C : I → Clause V) (σ : Restriction V) (P : List I) : Prop :=
  ∃ z : Cube (Live σ), ∀ i ∈ P, (C i).violation (fill σ z) = true

def pathCenter (C : I → Clause V) (σ : Restriction V) (P : List I) : Cube (Live σ) :=
  if h : pathCompatible C σ P then Classical.choose h else fun _ => false

theorem pathCenter_support
    {V : Type uDepth1}
    {I : Type uDepth2}
    [Fintype V]
    [Fintype I]
    (C : I → Clause V) (σ : Restriction V) (P : List I)
    (h : pathCompatible C σ P) :
    ∀ i ∈ P, (C i).violation (fill σ (pathCenter C σ P)) = true := by
  unfold pathCenter
  rw [dite_eq_left h]
  exact Classical.choose_spec h

@[simp] theorem pathCompatible_nil
    {V : Type uDepth1}
    {I : Type uDepth2}
    [Fintype V]
    [Fintype I]
    (C : I → Clause V) (σ : Restriction V) :
    pathCompatible C σ [] := by
  exact ⟨fun _ => false, by simp⟩

def pathPrefixSet (C : I → Clause V) (σ : Restriction V) (P : List I)
    (h : Fin P.length) : Finset V :=
  revealed (fun i => (C i).scope) (liveSet σ) (P.take (h.val + 1))

def pathFinalSet (C : I → Clause V) (σ : Restriction V) (P : List I) : Finset V :=
  revealed (fun i => (C i).scope) (liveSet σ) P

def pathLiveSet (C : I → Clause V) (σ : Restriction V) (P : List I) :
    Finset (Live σ) :=
  Finset.univ.filter fun v => v.val ∈ pathFinalSet C σ P

def pathCoveredCount (C : I → Clause V) (σ : Restriction V) (P : List I)
    (h : Fin P.length) : ℕ :=
  coveredCount (fun i => (C i).scope) (liveSet σ)
    (fun i => (C i).violation (fill σ (pathCenter C σ P))) (pathPrefixSet C σ P h)

def pathWeight (C : I → Clause V) (σ : Restriction V) (P : List I) : ℝ :=
  ∏ h : Fin P.length, (pathCoveredCount C σ P h : ℝ)⁻¹

def pathCost (C : I → Clause V) (b : ℕ) (σ : Restriction V) (j : ℕ) : ℝ :=
  ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b j,
    if pathCompatible C σ P then pathWeight C σ P else 0

def restrictionCost (C : I → Clause V) (b : ℕ) (σ : Restriction V) : ℝ :=
  ∑ j ∈ Finset.range (Fintype.card V / (b + 1) + 1), pathCost C b σ j

theorem pathWeight_nonneg (C : I → Clause V) (σ : Restriction V) (P : List I) :
    0 ≤ pathWeight C σ P := by
  exact Finset.prod_nonneg fun h _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem pathCost_nonneg (C : I → Clause V) (b : ℕ) (σ : Restriction V) (j : ℕ) :
    0 ≤ pathCost C b σ j := by
  apply Finset.sum_nonneg
  intro P hP
  split
  · exact pathWeight_nonneg C σ P
  · exact le_rfl

theorem restrictionCost_nonneg (C : I → Clause V) (b : ℕ) (σ : Restriction V) :
    0 ≤ restrictionCost C b σ :=
  Finset.sum_nonneg fun j _ => pathCost_nonneg C b σ j

@[simp] theorem pathWeight_nil (C : I → Clause V) (σ : Restriction V) :
    pathWeight C σ [] = 1 := by simp [pathWeight]

@[simp] theorem pathCost_zero (C : I → Clause V) (b : ℕ) (σ : Restriction V) :
    pathCost C b σ 0 = 1 := by
  simp [pathCost, paths_zero]

theorem pathPrefixSet_subset_final
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instFintypeV : Fintype V]
    [Fintype I]
    (C : I → Clause V) (σ : Restriction V)
    (P : List I) (h : Fin P.length) :
    pathPrefixSet C σ P h ⊆ pathFinalSet C σ P :=
  revealed_mono (fun i => (C i).scope) (liveSet σ) (List.take_subset _ _)

theorem pathCoveredCount_pos (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    {n : ℕ} {P : List I}
    (hP : P ∈ paths (fun i => (C i).scope) (liveSet σ) b n)
    (hc : pathCompatible C σ P) (h : Fin P.length) :
    0 < pathCoveredCount C σ P h := by
  have hk : h.val + 1 ≤ n := by
    rw [← length_of_mem_paths hP]
    exact Nat.succ_le_of_lt h.isLt
  have hpref := take_mem_paths (fun i => (C i).scope) (liveSet σ) b hP hk
  have hs : pathNumerator
      (fun i => (C i).violation (fill σ (pathCenter C σ P)))
      (P.take (h.val + 1)) ≠ 0 := by
    apply (pathNumerator_ne_zero_iff _ _).mpr
    intro i hi
    exact pathCenter_support C σ P hc i ((List.take_subset _ _) hi)
  have hle := length_le_coveredCount_of_support (fun i => (C i).scope)
    (liveSet σ) b (fun i => (C i).violation (fill σ (pathCenter C σ P))) hpref hs
  rw [length_of_mem_paths hpref] at hle
  exact (Nat.succ_pos h.val).trans_le hle

theorem pathLiveSet_image
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instFintypeV : Fintype V]
    [Fintype I]
    (C : I → Clause V) (σ : Restriction V) (P : List I) :
    (pathLiveSet C σ P).image Subtype.val = pathFinalSet C σ P := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hw).2
  · intro hv
    have ht : v ∈ liveSet σ := revealed_subset (fun i => (C i).scope) (liveSet σ) P hv
    have hσ : σ v = none := by simpa [liveSet] using ht
    exact Finset.mem_image.mpr ⟨⟨v, hσ⟩, by simp [pathLiveSet, hv], rfl⟩

theorem pathLiveSet_card (C : I → Clause V) (σ : Restriction V) (P : List I) :
    (pathLiveSet C σ P).card = (pathFinalSet C σ P).card := by
  rw [← pathLiveSet_image C σ P]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

theorem path_support_iff_live_cylinder (C : I → Clause V) (σ : Restriction V)
    (P : List I) (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P)
    (x : Cube (Live σ)) :
    (∀ i ∈ P, (C i).violation (fill σ x) = true) ↔
      ∀ v ∈ pathLiveSet C σ P, x v = pathCenter C σ P v := by
  rw [simultaneous_restricted_violation_iff C σ (liveSet σ)
    (by intro v; simp [liveSet]) P x (pathCenter C σ P) hn
    (pathCenter_support C σ P hc)]
  constructor
  · intro h v hv
    have hval : v.val ∈ pathFinalSet C σ P := (Finset.mem_filter.mp hv).2
    simpa using h v.val hval
  · intro h v hv
    have ht : v ∈ liveSet σ := revealed_subset (fun i => (C i).scope) (liveSet σ) P hv
    have hσ : σ v = none := by simpa [liveSet] using ht
    have hv' : (⟨v, hσ⟩ : Live σ) ∈ pathLiveSet C σ P := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    simpa [fill, hσ] using h ⟨v, hσ⟩ hv'

theorem path_cylinder_probability (C : I → Clause V) (σ : Restriction V)
    (P : List I) (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P) :
    finiteAvg (fun x : Cube (Live σ) =>
      indicator (decide (∀ i ∈ P, (C i).violation (fill σ x) = true))) =
      ((2 : ℝ) ^ (pathFinalSet C σ P).card)⁻¹ := by
  simp_rw [path_support_iff_live_cylinder C σ P hn hc]
  calc
    _ = ((2 : ℝ) ^ (pathLiveSet C σ P).card)⁻¹ := by
      have havg (inst₁ inst₂ : Fintype (Cube (Live σ)))
          (f g : Cube (Live σ) → ℝ) (hfg : ∀ x, f x = g x) :
          @finiteAvg _ inst₁ f = @finiteAvg _ inst₂ g := by
        have hi : inst₁ = inst₂ := Subsingleton.elim _ _
        cases hi
        exact @finiteAvg_congr _ inst₁ f g hfg
      refine Eq.trans ?_
        (finiteAvg_indicator_eq_pattern (pathLiveSet C σ P) (pathCenter C σ P))
      apply havg
      intro x
      apply congrArg indicator
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
    _ = _ := by rw [pathLiveSet_card]

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [instFintypeI : Fintype I]

def intermediateIndices (scope : I → Finset V) (T : Finset V) (b : ℕ)
    (U : Finset V) : Finset I :=
  Finset.univ.filter fun i =>
    0 < (residual scope T U i).card ∧ (residual scope T U i).card ≤ b

@[simp] theorem mem_intermediateIndices (scope : I → Finset V) (T : Finset V)
    (b : ℕ) (U : Finset V) (i : I) :
    i ∈ intermediateIndices scope T b U ↔
      0 < (residual scope T U i).card ∧ (residual scope T U i).card ≤ b := by
  simp [intermediateIndices]

def intermediateCount (scope : I → Finset V) (T : Finset V) (b : ℕ)
    (violation : I → Bool) (U : Finset V) : ℕ :=
  ((intermediateIndices scope T b U).filter fun i => violation i = true).card

theorem easyCount_eq_covered_add_intermediate (scope : I → Finset V)
    (T : Finset V) (b : ℕ) (violation : I → Bool) (U : Finset V) :
    easyCount scope T b violation U = coveredCount scope T violation U +
      intermediateCount scope T b violation U := by
  let covered : Finset I := Finset.univ.filter fun i =>
    residual scope T U i = ∅ ∧ violation i = true
  let middle := (intermediateIndices scope T b U).filter fun i => violation i = true
  have hd : Disjoint covered middle := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have he : residual scope T U i = ∅ := (Finset.mem_filter.mp hi).2.1
    have hp : 0 < (residual scope T U i).card :=
      ((mem_intermediateIndices scope T b U i).mp (Finset.mem_filter.mp hj).1).1
    rw [he, Finset.card_empty] at hp
    exact Nat.not_lt_zero _ hp
  have hu : (Finset.univ.filter fun i =>
      (residual scope T U i).card ≤ b ∧ violation i = true) = covered ∪ middle := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      covered, middle, mem_intermediateIndices]
    constructor
    · rintro ⟨hle, hv⟩
      by_cases he : residual scope T U i = ∅
      · exact Or.inl ⟨he, hv⟩
      · have hp : 0 < (residual scope T U i).card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        exact Or.inr ⟨⟨hp, hle⟩, hv⟩
    · rintro (⟨he, hv⟩ | ⟨⟨hp, hle⟩, hv⟩)
      · exact ⟨by rw [he]; simp, hv⟩
      · exact ⟨hle, hv⟩
  change (Finset.univ.filter fun i =>
      (residual scope T U i).card ≤ b ∧ violation i = true).card =
    covered.card + middle.card
  rw [hu, Finset.card_union_of_disjoint hd]

theorem subtype_filter_card
    {I : Type uDepth2}
    [Fintype I]
    (s : Finset I) (p : I → Prop) [DecidablePred p] :
    ((Finset.univ : Finset s).filter fun i => p i.val).card = (s.filter p).card := by
  let a := (Finset.univ : Finset s).filter fun i => p i.val
  have ha : a.image Subtype.val = s.filter p := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr ⟨j.property, (Finset.mem_filter.mp hj).2⟩
    · intro hi
      obtain ⟨his, hip⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_image.mpr ⟨⟨i, his⟩, by simp [a, hip], rfl⟩
  rw [← ha]
  exact (Finset.card_image_of_injective a Subtype.val_injective).symm

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound


variable {L : Type u} [instFintypeL : Fintype L] [instDecidableEqL : DecidableEq L]

def permutationRank (π : Equiv.Perm L) (l : L) : Fin (Fintype.card L) :=
  Fintype.equivFin L (π l)

def IsFirst (S : Finset L) (π : Equiv.Perm L) (s : L) : Prop :=
  s ∈ S ∧ ∀ t ∈ S, permutationRank π s ≤ permutationRank π t

theorem permutationRank_injective
    {L : Type u}
    [instFintypeL : Fintype L]
    [DecidableEq L]
    (π : Equiv.Perm L) :
    Function.Injective (permutationRank π) :=
  (Fintype.equivFin L).injective.comp π.injective

theorem exists_isFirst
    {L : Type u}
    [instFintypeL : Fintype L]
    [DecidableEq L]
    (S : Finset L) (hS : S.Nonempty) (π : Equiv.Perm L) :
    ∃ s, IsFirst S π s := by
  obtain ⟨s, hs, hmin⟩ := S.exists_min_image (permutationRank π) hS
  exact ⟨s, hs, hmin⟩

theorem isFirst_unique {S : Finset L} {π : Equiv.Perm L} {s t : L}
    (hs : IsFirst S π s) (ht : IsFirst S π t) : s = t := by
  apply permutationRank_injective π
  exact le_antisymm (hs.2 t ht.1) (ht.2 s hs.1)

private theorem swap_mem_active
    {L : Type u}
    [Fintype L]
    [instDecidableEqL : DecidableEq L]
    {S : Finset L} {s t x : L}
    (hs : s ∈ S) (ht : t ∈ S) (hx : x ∈ S) : Equiv.swap s t x ∈ S := by
  by_cases hxs : x = s
  · subst x
    simpa only [Equiv.swap_apply_left] using ht
  by_cases hxt : x = t
  · subst x
    simpa only [Equiv.swap_apply_right] using hs
  rw [Equiv.swap_apply_of_ne_of_ne hxs hxt]
  exact hx

private def permutationInputSwap (s t : L) : Equiv.Perm (Equiv.Perm L) where
  toFun π := (Equiv.swap s t).trans π
  invFun π := (Equiv.swap s t).trans π
  left_inv π := by
    apply Equiv.ext
    intro x
    simp only [Equiv.trans_apply, Equiv.swap_apply_self]
  right_inv π := by
    apply Equiv.ext
    intro x
    simp only [Equiv.trans_apply, Equiv.swap_apply_self]

private theorem isFirst_inputSwap_iff (S : Finset L) (s t : L)
    (hs : s ∈ S) (ht : t ∈ S) (π : Equiv.Perm L) :
    IsFirst S ((Equiv.swap s t).trans π) t ↔ IsFirst S π s := by
  constructor
  · intro h
    refine ⟨hs, ?_⟩
    intro x hx
    have hmin := h.2 (Equiv.swap s t x) (swap_mem_active hs ht hx)
    simpa only [permutationRank, Equiv.trans_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_self] using hmin
  · intro h
    refine ⟨ht, ?_⟩
    intro x hx
    have hmin := h.2 (Equiv.swap s t x) (swap_mem_active hs ht hx)
    simpa only [permutationRank, Equiv.trans_apply, Equiv.swap_apply_right] using hmin

private theorem first_fiber_sum_eq (S : Finset L) {s t : L}
    (hs : s ∈ S) (ht : t ∈ S) :
    (∑ π : Equiv.Perm L, if IsFirst S π s then (1 : ℝ) else 0) =
      ∑ π : Equiv.Perm L, if IsFirst S π t then (1 : ℝ) else 0 := by
  refine Fintype.sum_equiv (permutationInputSwap s t) _ _ ?_
  intro π
  change (if IsFirst S π s then (1 : ℝ) else 0) =
    if IsFirst S ((Equiv.swap s t).trans π) t then (1 : ℝ) else 0
  rw [isFirst_inputSwap_iff S s t hs ht π]

private theorem sum_isFirst_indicator (S M : Finset L) (π : Equiv.Perm L) :
    (∑ s ∈ M, if IsFirst S π s then (1 : ℝ) else 0) =
      if ∃ s ∈ M, IsFirst S π s then (1 : ℝ) else 0 := by
  exact Finset.sum_ite_zero M (IsFirst S π)
    (fun s _ t _ hs ht => isFirst_unique hs ht) (1 : ℝ)

theorem permutation_first_ratio (S M : Finset L) (hS : S.Nonempty) (hMS : M ⊆ S) :
    ((∑ π : Equiv.Perm L, if ∃ s ∈ M, IsFirst S π s then (1 : ℝ) else 0) /
        (Fintype.card (Equiv.Perm L) : ℝ)) = (M.card : ℝ) / (S.card : ℝ) := by
  obtain ⟨s, hs⟩ := hS
  let q : ℝ := ∑ π : Equiv.Perm L, if IsFirst S π s then (1 : ℝ) else 0
  have hfiber (t : L) (ht : t ∈ S) :
      (∑ π : Equiv.Perm L, if IsFirst S π t then (1 : ℝ) else 0) = q :=
    first_fiber_sum_eq S ht hs
  have hsum (A : Finset L) (hAS : A ⊆ S) :
      (∑ π : Equiv.Perm L, if ∃ t ∈ A, IsFirst S π t then (1 : ℝ) else 0) =
        (A.card : ℝ) * q := by
    calc
      (∑ π : Equiv.Perm L, if ∃ t ∈ A, IsFirst S π t then (1 : ℝ) else 0) =
          ∑ π : Equiv.Perm L, ∑ t ∈ A, if IsFirst S π t then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro π _
        exact (sum_isFirst_indicator S A π).symm
      _ = ∑ t ∈ A, ∑ π : Equiv.Perm L, if IsFirst S π t then (1 : ℝ) else 0 :=
        Finset.sum_comm
      _ = ∑ _t ∈ A, q := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hfiber t (hAS ht)
      _ = (A.card : ℝ) * q := by simp [nsmul_eq_mul]
  have hone :
      (∑ π : Equiv.Perm L, if ∃ t ∈ S, IsFirst S π t then (1 : ℝ) else 0) =
        (Fintype.card (Equiv.Perm L) : ℝ) := by
    calc
      (∑ π : Equiv.Perm L, if ∃ t ∈ S, IsFirst S π t then (1 : ℝ) else 0) =
          ∑ _π : Equiv.Perm L, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro π _
        obtain ⟨t, ht⟩ := exists_isFirst S ⟨s, hs⟩ π
        exact ite_eq_left ⟨t, ht.1, ht⟩
      _ = (Fintype.card (Equiv.Perm L) : ℝ) := by simp
  have hmass : (S.card : ℝ) * q = (Fintype.card (Equiv.Perm L) : ℝ) :=
    (hsum S (fun _ hx => hx)).symm.trans hone
  have hS0 : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (show S.Nonempty from ⟨s, hs⟩)).ne'
  have hΩ0 : (Fintype.card (Equiv.Perm L) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm L) ≠ 0)
  rw [hsum M hMS]
  apply (div_eq_div_iff hΩ0 hS0).2
  rw [← hmass]
  ring

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound


variable {I : Type u} [Fintype I] [instDecidableEqI : DecidableEq I] {A : Type v}

def markerSelected (c : ℕ) (π : Equiv.Perm (I ⊕ Fin c)) : Finset I :=
  Finset.univ.filter fun i =>
    ∀ m : Fin c, permutationRank π (Sum.inl i) < permutationRank π (Sum.inr m)

@[simp] theorem mem_markerSelected
    {I : Type u}
    [Fintype I]
    [DecidableEq I]
    (c : ℕ) (π : Equiv.Perm (I ⊕ Fin c)) (i : I) :
    i ∈ markerSelected c π ↔
      ∀ m : Fin c, permutationRank π (Sum.inl i) < permutationRank π (Sum.inr m) := by
  simp [markerSelected]

def markerSample (C : I → A → Bool) (c : ℕ) (π : Equiv.Perm (I ⊕ Fin c))
    (x : A) : Bool :=
  decide (∀ i ∈ markerSelected c π, C i x = true)

@[simp] theorem markerSample_eq_true (C : I → A → Bool) (c : ℕ)
    (π : Equiv.Perm (I ⊕ Fin c)) (x : A) :
    markerSample C c π x = true ↔ ∀ i ∈ markerSelected c π, C i x = true := by
  simp [markerSample]

def markerBad (C : I → A → Bool) (x : A) : Finset I :=
  Finset.univ.filter fun i => C i x = false

def markerActive (C : I → A → Bool) (x : A) (c : ℕ) : Finset (I ⊕ Fin c) :=
  (markerBad C x).disjSum Finset.univ

def markerObjects (c : ℕ) : Finset (I ⊕ Fin c) :=
  (∅ : Finset I).disjSum Finset.univ

theorem markerActive_nonempty
    {I : Type u}
    [Fintype I]
    [DecidableEq I]
    {A : Type v}
    (C : I → A → Bool) (x : A) {c : ℕ} (hc : 0 < c) :
    (markerActive C x c).Nonempty := by
  refine ⟨Sum.inr ⟨0, hc⟩, ?_⟩
  simp [markerActive]

theorem markerObjects_subset
    {I : Type u}
    [Fintype I]
    [DecidableEq I]
    {A : Type v}
    (C : I → A → Bool) (x : A) (c : ℕ) :
    markerObjects (I := I) c ⊆ markerActive C x c := by
  intro s hs
  cases s with
  | inl i => simp [markerObjects] at hs
  | inr m => simp [markerActive]

theorem markerSample_iff_first_marker (C : I → A → Bool) (x : A)
    {c : ℕ} (hc : 0 < c) (π : Equiv.Perm (I ⊕ Fin c)) :
    markerSample C c π x = true ↔
      ∃ s ∈ markerObjects (I := I) c, IsFirst (markerActive C x c) π s := by
  constructor
  · intro hsample
    have hgood := (markerSample_eq_true C c π x).mp hsample
    obtain ⟨s, hs⟩ := exists_isFirst (markerActive C x c)
      (markerActive_nonempty C x hc) π
    cases s with
    | inr m => exact ⟨Sum.inr m, by simp [markerObjects], hs⟩
    | inl i =>
      have hbad : C i x = false := by simpa [markerActive, markerBad] using hs.1
      have hselected : i ∈ markerSelected c π := by
        apply (mem_markerSelected c π i).mpr
        intro m
        have hle := hs.2 (Sum.inr m) (by simp [markerActive])
        apply lt_of_le_of_ne hle
        intro heq
        have hlabels := permutationRank_injective π heq
        cases hlabels
      have htrue := hgood i hselected
      rw [hbad] at htrue
      cases htrue
  · rintro ⟨s, hs, hfirst⟩
    apply (markerSample_eq_true C c π x).mpr
    cases s with
    | inl i => simp [markerObjects] at hs
    | inr m =>
      intro i hi
      by_contra hnot
      have hbad : C i x = false := Bool.eq_false_of_not_eq_true hnot
      have hactive : Sum.inl i ∈ markerActive C x c := by
        simp [markerActive, markerBad, hbad]
      have hle := hfirst.2 (Sum.inl i) hactive
      have hlt := (mem_markerSelected c π i).mp hi m
      exact (not_lt_of_ge hle) hlt

theorem marker_mixture_ratio (C : I → A → Bool) (x : A) {c : ℕ} (hc : 0 < c) :
    finiteAvg (fun π : Equiv.Perm (I ⊕ Fin c) =>
      indicator (markerSample C c π x)) =
      (c : ℝ) / ((c : ℝ) + ((markerBad C x).card : ℝ)) := by
  classical
  calc
    finiteAvg (fun π : Equiv.Perm (I ⊕ Fin c) =>
        indicator (markerSample C c π x)) =
        (∑ π : Equiv.Perm (I ⊕ Fin c),
          if ∃ s ∈ markerObjects (I := I) c, IsFirst (markerActive C x c) π s
          then (1 : ℝ) else 0) / (Fintype.card (Equiv.Perm (I ⊕ Fin c)) : ℝ) := by
      unfold finiteAvg indicator
      simp_rw [markerSample_iff_first_marker C x hc]
      rw [div_eq_mul_inv, mul_comm]
    _ = ((markerObjects (I := I) c).card : ℝ) /
        ((markerActive C x c).card : ℝ) :=
      permutation_first_ratio (markerActive C x c) (markerObjects c)
        (markerActive_nonempty C x hc) (markerObjects_subset C x c)
    _ = (c : ℝ) / ((c : ℝ) + ((markerBad C x).card : ℝ)) := by
      simp [markerObjects, markerActive, Finset.card_disjSum, Nat.cast_add, add_comm]

theorem markerSample_of_all_true (C : I → A → Bool) (x : A) (c : ℕ)
    (π : Equiv.Perm (I ⊕ Fin c)) (hC : ∀ i, C i x = true) :
    markerSample C c π x = true := by
  apply (markerSample_eq_true C c π x).mpr
  exact fun i _ => hC i

theorem markerSample_of_isEmpty [IsEmpty I] (C : I → A → Bool) (x : A) (c : ℕ)
    (π : Equiv.Perm (I ⊕ Fin c)) : markerSample C c π x = true := by
  apply markerSample_of_all_true
  intro i
  exact isEmptyElim i

theorem marker_product_mixture_ratio {H : Type uDepth1} [Fintype H] [DecidableEq H]
    {J : H → Type uDepth2} [∀ h, Fintype (J h)] [∀ h, DecidableEq (J h)]
    (C : ∀ h, J h → A → Bool) (c : H → ℕ) (hc : ∀ h, 0 < c h) (x : A) :
    finiteAvg (fun π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h)) =>
      ∏ h, indicator (markerSample (C h) (c h) (π h) x)) =
      ∏ h, (c h : ℝ) / ((c h : ℝ) + ((markerBad (C h) x).card : ℝ)) := by
  calc
    _ = ∏ h, finiteAvg (fun π : Equiv.Perm (J h ⊕ Fin (c h)) =>
        indicator (markerSample (C h) (c h) π x)) := by
      convert finiteAvg_pi_prod (fun h (π : Equiv.Perm (J h ⊕ Fin (c h))) =>
        indicator (markerSample (C h) (c h) π x))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro h _
      exact marker_mixture_ratio (C h) x (hc h)

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [Fintype I] [instDecidableEqI : DecidableEq I]

theorem residualCNF_eval_eq_true (L : List (Option (Clause V))) (x : Cube V) :
    (residualCNF L).eval x = true ↔ ∀ C ∈ L, residualClauseEval C x = true := by
  induction L with
  | nil => simp
  | cons C L ih =>
    cases C <;> simp [ih, CNF.eval_cons]

theorem residualCNF_widthAtMost (L : List (Option (Clause V))) {b : ℕ}
    (h : ∀ C, some C ∈ L → C.width ≤ b) : (residualCNF L).WidthAtMost b := by
  intro C hC
  obtain ⟨D, hD, hDC⟩ := List.mem_filterMap.mp hC
  change D = some C at hDC
  subst D
  exact h C hD

def markerCNF (C : I → Option (Clause V)) (c : ℕ)
    (π : Equiv.Perm (I ⊕ Fin c)) : CNF V :=
  residualCNF ((markerSelected c π).toList.map C)

@[simp] theorem markerCNF_eval (C : I → Option (Clause V)) (c : ℕ)
    (π : Equiv.Perm (I ⊕ Fin c)) (x : Cube V) :
    (markerCNF C c π).eval x =
      markerSample (fun i x => residualClauseEval (C i) x) c π x := by
  apply Bool.eq_iff_iff.mpr
  rw [markerSample_eq_true]
  simp only [markerCNF, residualCNF_eval_eq_true, List.forall_mem_map,
    Finset.mem_toList]

theorem markerCNF_widthAtMost
    {V : Type uDepth1}
    {I : Type uDepth2}
    [Fintype I]
    [DecidableEq I]
    (C : I → Option (Clause V)) (c : ℕ)
    (π : Equiv.Perm (I ⊕ Fin c)) {b : ℕ}
    (h : ∀ i D, C i = some D → D.width ≤ b) :
    (markerCNF C c π).WidthAtMost b := by
  apply residualCNF_widthAtMost
  intro D hD
  obtain ⟨i, hi, hiD⟩ := List.mem_map.mp hD
  exact h i D hiD

theorem markerCNF_avg (C : I → Option (Clause V)) {c : ℕ} (hc : 0 < c)
    (x : Cube V) :
    finiteAvg (fun π : Equiv.Perm (I ⊕ Fin c) => indicator ((markerCNF C c π).eval x)) =
      (c : ℝ) / ((c : ℝ) +
        ((markerBad (fun i x => residualClauseEval (C i) x) x).card : ℝ)) := by
  simp_rw [markerCNF_eval]
  exact marker_mixture_ratio _ x hc

section Product

variable {H : Type uDepth3} [Fintype H] [instDecidableEqH : DecidableEq H]
    {J : H → Type uDepth4} [∀ h, Fintype (J h)] [insthDecidableEqJh : ∀ h, DecidableEq (J h)]

def markerProductCNF (C : ∀ h, J h → Option (Clause V)) (c : H → ℕ)
    (π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h))) : CNF V :=
  (Finset.univ : Finset H).toList.flatMap fun h => markerCNF (C h) (c h) (π h)

theorem markerProductCNF_eval_eq_true
    {V : Type uDepth1}
    {H : Type uDepth3}
    [Fintype H]
    [DecidableEq H]
    {J : H → Type uDepth4}
    [(h : H) → Fintype (J h)]
    [(h : H) → DecidableEq (J h)]
    (C : ∀ h, J h → Option (Clause V))
    (c : H → ℕ) (π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h))) (x : Cube V) :
    (markerProductCNF C c π).eval x = true ↔
      ∀ h, (markerCNF (C h) (c h) (π h)).eval x = true := by
  simp only [markerProductCNF, CNF.eval_eq_true, List.forall_mem_flatMap,
    Finset.mem_toList, Finset.mem_univ, forall_const]

theorem markerProductCNF_indicator (C : ∀ h, J h → Option (Clause V))
    (c : H → ℕ) (π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h))) (x : Cube V) :
    indicator ((markerProductCNF C c π).eval x) =
      ∏ h, indicator ((markerCNF (C h) (c h) (π h)).eval x) := by
  unfold indicator
  rw [Fintype.prod_boole]
  congr 1
  exact propext (markerProductCNF_eval_eq_true C c π x)

theorem markerProductCNF_widthAtMost
    {V : Type uDepth1}
    {H : Type uDepth3}
    [Fintype H]
    [DecidableEq H]
    {J : H → Type uDepth4}
    [(h : H) → Fintype (J h)]
    [insthDecidableEqJh : (h : H) → DecidableEq (J h)]
    (C : ∀ h, J h → Option (Clause V))
    (c : H → ℕ) (π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h))) {b : ℕ}
    (hC : ∀ h i D, C h i = some D → D.width ≤ b) :
    (markerProductCNF C c π).WidthAtMost b := by
  intro D hD
  obtain ⟨h, hh, hD⟩ := List.mem_flatMap.mp hD
  exact markerCNF_widthAtMost (C h) (c h) (π h) (hC h) D hD

theorem markerProductCNF_avg (C : ∀ h, J h → Option (Clause V))
    (c : H → ℕ) (hc : ∀ h, 0 < c h) (x : Cube V) :
    finiteAvg (fun π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h)) =>
      indicator ((markerProductCNF C c π).eval x)) =
      ∏ h, (c h : ℝ) / ((c h : ℝ) +
        ((markerBad (fun i x => residualClauseEval (C h i) x) x).card : ℝ)) := by
  simp_rw [markerProductCNF_indicator, markerCNF_eval]
  exact marker_product_mixture_ratio (fun h i x => residualClauseEval (C h i) x) c hc x

variable [instDecidableEqV : DecidableEq V]

def markerCylinderCNF (K : CNF V) (U : Finset V) (pattern : Cube V)
    (C : ∀ h, J h → Option (Clause V)) (c : H → ℕ)
    (π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h))) : CNF V :=
  (K ++ cylinderCNF U pattern) ++ markerProductCNF C c π

theorem markerCylinderCNF_widthAtMost (K : CNF V) (U : Finset V) (pattern : Cube V)
    (C : ∀ h, J h → Option (Clause V)) (c : H → ℕ)
    (π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h))) {b : ℕ} (hb : 1 ≤ b)
    (hK : K.WidthAtMost b) (hC : ∀ h i D, C h i = some D → D.width ≤ b) :
    (markerCylinderCNF K U pattern C c π).WidthAtMost b := by
  intro D hD
  rcases List.mem_append.mp hD with hD | hD
  · rcases List.mem_append.mp hD with hD | hD
    · exact hK D hD
    · exact cylinderCNF_widthAtMost U pattern hb D hD
  · exact markerProductCNF_widthAtMost C c π hC D hD

theorem markerCylinderCNF_avg
    {V : Type uDepth1}
    {H : Type uDepth3}
    [Fintype H]
    [instDecidableEqH : DecidableEq H]
    {J : H → Type uDepth4}
    [(h : H) → Fintype (J h)]
    [insthDecidableEqJh : (h : H) → DecidableEq (J h)]
    [DecidableEq V]
    (K : CNF V) (U : Finset V) (pattern x : Cube V)
    (C : ∀ h, J h → Option (Clause V)) (c : H → ℕ) (hc : ∀ h, 0 < c h) :
    finiteAvg (fun π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h)) =>
      indicator ((markerCylinderCNF K U pattern C c π).eval x)) =
      indicator (K.eval x) * indicator ((cylinderCNF U pattern).eval x) *
        ∏ h, (c h : ℝ) / ((c h : ℝ) +
          ((markerBad (fun i x => residualClauseEval (C h i) x) x).card : ℝ)) := by
  simp only [markerCylinderCNF, CNF.eval_append, indicator_and]
  rw [finiteAvg_const_mul, markerProductCNF_avg C c hc x]

theorem markerCylinderCNF_scaled_avg (K : CNF V) (U : Finset V) (pattern x : Cube V)
    (C : ∀ h, J h → Option (Clause V)) (c : H → ℕ) (hc : ∀ h, 0 < c h) :
    (∏ h, (c h : ℝ)⁻¹) *
      finiteAvg (fun π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h)) =>
        indicator ((markerCylinderCNF K U pattern C c π).eval x)) =
      indicator (K.eval x) * indicator ((cylinderCNF U pattern).eval x) *
        ∏ h, ((c h : ℝ) +
          ((markerBad (fun i x => residualClauseEval (C h i) x) x).card : ℝ))⁻¹ := by
  rw [markerCylinderCNF_avg K U pattern x C c hc]
  have hprod : (∏ h, (c h : ℝ)⁻¹) *
      (∏ h, (c h : ℝ) / ((c h : ℝ) +
        ((markerBad (fun i x => residualClauseEval (C h i) x) x).card : ℝ))) =
      ∏ h, ((c h : ℝ) +
        ((markerBad (fun i x => residualClauseEval (C h i) x) x).card : ℝ))⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro h hh
    have hcn : (c h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hc h))
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hcn, one_mul]
  calc
    _ = (indicator (K.eval x) * indicator ((cylinderCNF U pattern).eval x)) *
        ((∏ h, (c h : ℝ)⁻¹) *
          ∏ h, (c h : ℝ) / ((c h : ℝ) +
            ((markerBad (fun i x => residualClauseEval (C h i) x) x).card : ℝ))) := by ring
    _ = _ := by rw [hprod]

end Product

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [Fintype V] [Fintype I]

def pathIntermediateIndices (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (P : List I) (h : Fin P.length) : Finset I :=
  intermediateIndices (fun i => (C i).scope) (liveSet σ) b (pathPrefixSet C σ P h)

abbrev PathIntermediateIndex (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (P : List I) (h : Fin P.length) := ↥(pathIntermediateIndices C b σ P h)

def pathReducedClause (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (P : List I) (h : Fin P.length) (i : PathIntermediateIndex C b σ P h) :
    Option (Clause (Live σ)) :=
  keptRestrictedClause σ (liveSet σ \ pathFinalSet C σ P)
    (fill σ (pathCenter C σ P)) (C i.val)

theorem pathReducedClause_widthAtMost (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (P : List I) (h : Fin P.length)
    (i : PathIntermediateIndex C b σ P h) (D : Clause (Live σ))
    (hD : pathReducedClause C b σ P h i = some D) : D.width ≤ b := by
  have hd := keptRestrictedClause_width_le hD
  have hs : (C i.val).scope ∩ (liveSet σ \ pathFinalSet C σ P) ⊆
      residual (fun i => (C i).scope) (liveSet σ) (pathPrefixSet C σ P h) i.val := by
    intro v hv
    refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, ?_⟩
    obtain ⟨ht, hn⟩ := Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2
    exact Finset.mem_sdiff.mpr ⟨ht,
      fun hp => hn (pathPrefixSet_subset_final C σ P h hp)⟩
  have hi := (mem_intermediateIndices (fun i => (C i).scope) (liveSet σ) b
    (pathPrefixSet C σ P h) i.val).mp i.property
  exact hd.trans ((Finset.card_le_card hs).trans hi.2)

theorem path_fill_agree_outside_remainder (C : I → Clause V) (σ : Restriction V)
    (P : List I) (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P)
    (x : Cube (Live σ)) (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true) :
    ∀ v ∉ liveSet σ \ pathFinalSet C σ P,
      fill σ x v = fill σ (pathCenter C σ P) v := by
  have hZ := (simultaneous_restricted_violation_iff C σ (liveSet σ)
    (by intro v; simp [liveSet]) P x (pathCenter C σ P) hn
    (pathCenter_support C σ P hc)).mp hx
  intro v hv
  by_cases ht : v ∈ liveSet σ
  · have hz : v ∈ pathFinalSet C σ P := by
      by_contra hz
      exact hv (Finset.mem_sdiff.mpr ⟨ht, hz⟩)
    exact hZ v hz
  · apply fill_agree_outside_live
    intro hσ
    exact ht (by simp [liveSet, hσ])

theorem pathReducedClause_eval_on_support (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (P : List I) (hn : ∀ i ∈ P, (C i).Normalized)
    (hc : pathCompatible C σ P) (x : Cube (Live σ))
    (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true)
    (h : Fin P.length) (i : PathIntermediateIndex C b σ P h) :
    residualClauseEval (pathReducedClause C b σ P h i) x = (C i.val).eval (fill σ x) :=
  keptRestrictedClause_eval σ _ _ _ x
    (path_fill_agree_outside_remainder C σ P hn hc x hx)

theorem pathCoveredCount_eq_on_support (C : I → Clause V) (σ : Restriction V)
    (P : List I) (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P)
    (x : Cube (Live σ)) (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true)
    (h : Fin P.length) :
    coveredCount (fun i => (C i).scope) (liveSet σ)
      (fun i => (C i).violation (fill σ x)) (pathPrefixSet C σ P h) =
      pathCoveredCount C σ P h := by
  have hZ := (simultaneous_restricted_violation_iff C σ (liveSet σ)
    (by intro v; simp [liveSet]) P x (pathCenter C σ P) hn
    (pathCenter_support C σ P hc)).mp hx
  apply coveredCount_eq_on_larger_cylinder C (liveSet σ) (pathPrefixSet C σ P h)
    (pathFinalSet C σ P) (fill σ x) (fill σ (pathCenter C σ P))
    (pathPrefixSet_subset_final C σ P h) hZ
  intro v hv
  apply fill_agree_outside_live
  intro hσ
  exact hv (by simp [liveSet, hσ])

theorem pathMarkerBad_card (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (P : List I) (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P)
    (x : Cube (Live σ)) (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true)
    (h : Fin P.length) :
    (markerBad (fun i z => residualClauseEval (pathReducedClause C b σ P h i) z) x).card =
      intermediateCount (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) (pathPrefixSet C σ P h) := by
  have he : markerBad
      (fun i z => residualClauseEval (pathReducedClause C b σ P h i) z) x =
      (Finset.univ : Finset (PathIntermediateIndex C b σ P h)).filter
        (fun i => (C i.val).violation (fill σ x) = true) := by
    ext i
    simp only [markerBad, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [pathReducedClause_eval_on_support C b σ P hn hc x hx h i,
      Clause.violation_eq_true]
  rw [he]
  exact subtype_filter_card (pathIntermediateIndices C b σ P h)
    (fun i => (C i).violation (fill σ x) = true)

theorem path_easyCount_eq_marker_count (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (P : List I) (hn : ∀ i ∈ P, (C i).Normalized)
    (hc : pathCompatible C σ P) (x : Cube (Live σ))
    (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true) (h : Fin P.length) :
    easyCount (fun i => (C i).scope) (liveSet σ) b
      (fun i => (C i).violation (fill σ x)) (pathPrefixSet C σ P h) =
      pathCoveredCount C σ P h +
        (markerBad (fun i z => residualClauseEval (pathReducedClause C b σ P h i) z) x).card := by
  rw [easyCount_eq_covered_add_intermediate,
    pathCoveredCount_eq_on_support C σ P hn hc x hx h,
    pathMarkerBad_card C b σ P hn hc x hx h]

abbrev PathMarkerSample (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (P : List I) :=
  ∀ h : Fin P.length, Equiv.Perm
    (PathIntermediateIndex C b σ P h ⊕ Fin (pathCoveredCount C σ P h))

def pathMixtureCNF (C : I → Clause V) (b : ℕ) (σ : Restriction V) (P : List I)
    (K : CNF (Live σ)) (π : PathMarkerSample C b σ P) : CNF (Live σ) :=
  markerCylinderCNF K (pathLiveSet C σ P) (pathCenter C σ P)
    (pathReducedClause C b σ P) (pathCoveredCount C σ P) π

theorem pathMixtureCNF_widthAtMost (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (P : List I) (K : CNF (Live σ)) (hb : 1 ≤ b)
    (hK : K.WidthAtMost b) (π : PathMarkerSample C b σ P) :
    (pathMixtureCNF C b σ P K π).WidthAtMost b :=
  markerCylinderCNF_widthAtMost K _ _ _ _ π hb hK
    (pathReducedClause_widthAtMost C b σ P)

theorem pathMixture_scaled_average (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) {n : ℕ} {P : List I}
    (hP : P ∈ paths (fun i => (C i).scope) (liveSet σ) b n)
    (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P)
    (K : CNF (Live σ)) (x : Cube (Live σ)) :
    pathWeight C σ P *
      finiteAvg (fun π : PathMarkerSample C b σ P =>
        indicator ((pathMixtureCNF C b σ P K π).eval x)) =
      indicator (K.eval x) *
        (if ∀ i ∈ P, (C i).violation (fill σ x) = true then
          ∏ h : Fin P.length,
            (easyCount (fun i => (C i).scope) (liveSet σ) b
              (fun i => (C i).violation (fill σ x)) (pathPrefixSet C σ P h) : ℝ)⁻¹
          else 0) := by
  simp only [pathWeight, pathMixtureCNF]
  rw [markerCylinderCNF_scaled_avg K (pathLiveSet C σ P) (pathCenter C σ P) x
      (pathReducedClause C b σ P) (pathCoveredCount C σ P)
      (pathCoveredCount_pos C b σ hP hc)]
  by_cases hx : ∀ i ∈ P, (C i).violation (fill σ x) = true
  · have hZ := (path_support_iff_live_cylinder C σ P hn hc x).mp hx
    have hev : (cylinderCNF (pathLiveSet C σ P) (pathCenter C σ P)).eval x = true :=
      (cylinderCNF_eval_eq_true _ _ _).mpr hZ
    simp only [ite_eq_left hx, hev, indicator_true, mul_one]
    congr 1
    apply Finset.prod_congr rfl
    intro h hh
    rw [path_easyCount_eq_marker_count C b σ P hn hc x hx h, Nat.cast_add]
  · have hZ : ¬ ∀ v ∈ pathLiveSet C σ P, x v = pathCenter C σ P v :=
      fun hz => hx ((path_support_iff_live_cylinder C σ P hn hc x).mpr hz)
    have hev : (cylinderCNF (pathLiveSet C σ P) (pathCenter C σ P)).eval x = false := by
      cases he : (cylinderCNF (pathLiveSet C σ P) (pathCenter C σ P)).eval x
      · rfl
      · exact (hZ ((cylinderCNF_eval_eq_true _ _ _).mp he)).elim
    simp only [ite_eq_right hx, hev, indicator_false, mul_zero, zero_mul]

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [instFintypeV : Fintype V] [instFintypeI : Fintype I]

def indexedCNF (C : I → Clause V) : CNF V :=
  (Finset.univ : Finset I).toList.map C

@[simp] theorem indexedCNF_eval_eq_true
    {V : Type uDepth1}
    {I : Type uDepth2}
    [Fintype V]
    [instFintypeI : Fintype I]
    (C : I → Clause V) (x : Cube V) :
    (indexedCNF C).eval x = true ↔ ∀ i, (C i).eval x = true := by
  simp [indexedCNF, CNF.eval_eq_true]

theorem clauseViolationCount_zero_iff
    {V : Type uDepth1}
    {I : Type uDepth2}
    [Fintype V]
    [Fintype I]
    (C : I → Clause V) (x : Cube V) (S : Finset I) :
    (S.filter (fun i => (C i).violation x = true)).card = 0 ↔
      ∀ i ∈ S, (C i).eval x = true := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i hi
    have hn := h hi
    cases he : (C i).eval x
    · exact (hn ((Clause.violation_eq_true (C i) x).mpr he)).elim
    · rfl
  · intro h i hi hv
    have ht := h i hi
    have hf := (Clause.violation_eq_true (C i) x).mp hv
    rw [ht] at hf
    cases hf

theorem indexedCNF_eval_indicator (C : I → Clause V) (x : Cube V) :
    indicator ((indexedCNF C).eval x) =
      if totalCount (fun i => (C i).violation x) = 0 then (1 : ℝ) else 0 := by
  have he : (indexedCNF C).eval x = true ↔ totalCount (fun i => (C i).violation x) = 0 := by
    rw [indexedCNF_eval_eq_true]
    simp [totalCount]
  unfold indicator
  congr 1
  exact propext he

def easyBaseIndices (C : I → Clause V) (b : ℕ) (σ : Restriction V) : Finset I :=
  Finset.univ.filter fun i => ((C i).scope ∩ liveSet σ).card ≤ b

def easyBaseClause (C : I → Clause V) (σ : Restriction V) (i : I) :
    Option (Clause (Live σ)) :=
  keptRestrictedClause σ (liveSet σ) (fill σ (fun _ => false)) (C i)

theorem easyBaseClause_eval
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instFintypeV : Fintype V]
    [Fintype I]
    (C : I → Clause V) (σ : Restriction V) (i : I)
    (x : Cube (Live σ)) :
    residualClauseEval (easyBaseClause C σ i) x = (C i).eval (fill σ x) := by
  apply keptRestrictedClause_eval
  intro v hv
  apply fill_agree_outside_live
  intro hσ
  exact hv (by simp [liveSet, hσ])

def easyBaseCNF (C : I → Clause V) (b : ℕ) (σ : Restriction V) : CNF (Live σ) :=
  residualCNF ((easyBaseIndices C b σ).toList.map (easyBaseClause C σ))

theorem easyBaseCNF_widthAtMost (C : I → Clause V) (b : ℕ) (σ : Restriction V) :
    (easyBaseCNF C b σ).WidthAtMost b := by
  apply residualCNF_widthAtMost
  intro D hD
  obtain ⟨i, hi, hiD⟩ := List.mem_map.mp hD
  have hi' : i ∈ easyBaseIndices C b σ := by simpa using hi
  have hb : ((C i).scope ∩ liveSet σ).card ≤ b := (Finset.mem_filter.mp hi').2
  exact (keptRestrictedClause_width_le hiD).trans hb

theorem easyBaseCNF_eval_iff_all (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (x : Cube (Live σ)) :
    (easyBaseCNF C b σ).eval x = true ↔
      ∀ i ∈ easyBaseIndices C b σ, (C i).eval (fill σ x) = true := by
  change (residualCNF ((easyBaseIndices C b σ).toList.map (easyBaseClause C σ))).eval x = true ↔ _
  rw [residualCNF_eval_eq_true]
  constructor
  · intro h i hi
    have hm : easyBaseClause C σ i ∈
        (easyBaseIndices C b σ).toList.map (easyBaseClause C σ) :=
      List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩
    have hx := h _ hm
    rwa [easyBaseClause_eval] at hx
  · intro h D hD
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hD
    rw [easyBaseClause_eval]
    exact h i (by simpa using hi)

theorem easyBaseCNF_eval_eq_true (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (x : Cube (Live σ)) :
    (easyBaseCNF C b σ).eval x = true ↔
      easyCount (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) ∅ = 0 := by
  rw [easyBaseCNF_eval_iff_all]
  simp [easyCount, easyBaseIndices, residual]

theorem easyBaseCNF_eval_indicator (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (x : Cube (Live σ)) :
    indicator ((easyBaseCNF C b σ).eval x) =
      if easyCount (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) ∅ = 0 then (1 : ℝ) else 0 := by
  unfold indicator
  congr 1
  exact propext (easyBaseCNF_eval_eq_true C b σ x)

def cnfIndexFamily (H : CNF V) (i : Fin H.length) : Clause V := H.get i

theorem cnfIndexFamily_normalized
    {V : Type uDepth1}
    [Fintype V]
    {H : CNF V} (hH : H.Normalized)
    (i : Fin H.length) : (cnfIndexFamily H i).Normalized :=
  hH _ (List.get_mem H i)

theorem cnfIndexFamily_width
    {V : Type uDepth1}
    [Fintype V]
    {H : CNF V} {k : ℕ} (hH : H.WidthAtMost k)
    (i : Fin H.length) : (cnfIndexFamily H i).width ≤ k :=
  hH _ (List.get_mem H i)

@[simp] theorem indexedCNF_cnfIndexFamily_eval (H : CNF V) (x : Cube V) :
    (indexedCNF (cnfIndexFamily H)).eval x = H.eval x := by
  apply Bool.eq_iff_iff.mpr
  rw [indexedCNF_eval_eq_true, CNF.eval_eq_true]
  constructor
  · intro h C hC
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hC
    exact h i
  · intro h i
    exact h _ (List.get_mem H i)

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [Fintype V] [Fintype I]

theorem pathMixture_eq_pathTerm (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    {n : ℕ} {P : List I}
    (hP : P ∈ paths (fun i => (C i).scope) (liveSet σ) b n)
    (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P)
    (K : CNF (Live σ)) (x : Cube (Live σ)) :
    pathWeight C σ P *
      finiteAvg (fun π : PathMarkerSample C b σ P =>
        indicator ((pathMixtureCNF C b σ P K π).eval x)) =
      indicator (K.eval x) * pathTerm (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) P := by
  rw [pathTerm_eq_support_prod_inv]
  exact pathMixture_scaled_average C b σ hP hn hc K x

theorem pathTerm_zero_of_incompatible (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (P : List I) (hc : ¬ pathCompatible C σ P)
    (x : Cube (Live σ)) :
    pathTerm (fun i => (C i).scope) (liveSet σ) b
      (fun i => (C i).violation (fill σ x)) P = 0 := by
  have hs : ¬ ∀ i ∈ P, (C i).violation (fill σ x) = true :=
    fun hx => hc ⟨x, hx⟩
  rw [pathTerm_eq_support_prod_inv, ite_eq_right hs]

theorem abs_corr_pathTerm_le (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    {n : ℕ} {P : List I}
    (hP : P ∈ paths (fun i => (C i).scope) (liveSet σ) b n)
    (hn : ∀ i ∈ P, (C i).Normalized) (hb : 1 ≤ b)
    (K : CNF (Live σ)) (hK : K.WidthAtMost b) (G : Cube (Live σ) → ℝ) :
    |finiteAvg (fun x => G x * (indicator (K.eval x) *
      pathTerm (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) P))| ≤
      (if pathCompatible C σ P then pathWeight C σ P else 0) * corr b G := by
  by_cases hc : pathCompatible C σ P
  · rw [ite_eq_left hc]
    have hlin :
        finiteAvg (fun x => G x * (indicator (K.eval x) *
          pathTerm (fun i => (C i).scope) (liveSet σ) b
            (fun i => (C i).violation (fill σ x)) P)) =
        pathWeight C σ P * finiteAvg (fun x => G x *
          finiteAvg (fun π : PathMarkerSample C b σ P =>
            indicator ((pathMixtureCNF C b σ P K π).eval x))) := by
      calc
        _ = finiteAvg (fun x => pathWeight C σ P * (G x *
            finiteAvg (fun π : PathMarkerSample C b σ P =>
              indicator ((pathMixtureCNF C b σ P K π).eval x)))) := by
          apply finiteAvg_congr
          intro x
          rw [← pathMixture_eq_pathTerm C b σ hP hn hc K x]
          ring
        _ = _ := finiteAvg_const_mul _ _
    rw [hlin, abs_mul, abs_of_nonneg (pathWeight_nonneg C σ P)]
    apply mul_le_mul_of_nonneg_left _ (pathWeight_nonneg C σ P)
    have htransport (inst₁ inst₂ : Fintype (Cube (Live σ)))
        (f : Cube (Live σ) → ℝ) (c : ℝ)
        (h : |@finiteAvg _ inst₁ f| ≤ c) : |@finiteAvg _ inst₂ f| ≤ c := by
      have hi : inst₁ = inst₂ := Subsingleton.elim _ _
      cases hi
      exact h
    exact htransport _ _ _ _
      (abs_corr_uniform_mixture_le (pathMixtureCNF C b σ P K) b G
        (pathMixtureCNF_widthAtMost C b σ P K hb hK))
  · have hz : ∀ x : Cube (Live σ), pathTerm (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) P = 0 :=
      pathTerm_zero_of_incompatible C b σ P hc
    simp [hc, hz]

def pathLayer (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (K : CNF (Live σ)) (n : ℕ) (x : Cube (Live σ)) : ℝ :=
  indicator (K.eval x) *
    ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b n,
      pathTerm (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) P

theorem abs_corr_pathLayer_le (C : I → Clause V) (hn : ∀ i, (C i).Normalized)
    (b : ℕ) (hb : 1 ≤ b) (σ : Restriction V) (K : CNF (Live σ))
    (hK : K.WidthAtMost b) (n : ℕ) (G : Cube (Live σ) → ℝ) :
    |finiteAvg (fun x => G x * pathLayer C b σ K n x)| ≤
      pathCost C b σ n * corr b G := by
  have hlin : finiteAvg (fun x => G x * pathLayer C b σ K n x) =
      ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b n,
        finiteAvg (fun x => G x * (indicator (K.eval x) *
          pathTerm (fun i => (C i).scope) (liveSet σ) b
            (fun i => (C i).violation (fill σ x)) P)) := by
    calc
      _ = finiteAvg (fun x =>
          ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b n,
            G x * (indicator (K.eval x) *
              pathTerm (fun i => (C i).scope) (liveSet σ) b
                (fun i => (C i).violation (fill σ x)) P)) := by
        apply finiteAvg_congr
        intro x
        simp only [pathLayer, Finset.mul_sum]
      _ = _ := finiteAvg_sum _ _
  rw [hlin]
  calc
    _ ≤ ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b n,
        |finiteAvg (fun x => G x * (indicator (K.eval x) *
          pathTerm (fun i => (C i).scope) (liveSet σ) b
            (fun i => (C i).violation (fill σ x)) P))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b n,
        (if pathCompatible C σ P then pathWeight C σ P else 0) * corr b G := by
      apply Finset.sum_le_sum
      intro P hP
      exact abs_corr_pathTerm_le C b σ hP (fun i _ => hn i) hb K hK G
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem indexedCNF_restriction_expansion (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (x : Cube (Live σ)) :
    indicator ((indexedCNF C).eval (fill σ x)) =
      indicator ((easyBaseCNF C b σ).eval x) +
        ∑ j ∈ Finset.range ((liveSet σ).card / (b + 1)),
          (-1 : ℝ) ^ (j + 1) * pathLayer C b σ (easyBaseCNF C b σ) (j + 1) x := by
  have h := finite_violation_expansion (fun i => (C i).scope) (liveSet σ) b
    (fun i => (C i).violation (fill σ x))
  rw [← indexedCNF_eval_indicator C (fill σ x),
    ← easyBaseCNF_eval_indicator C b σ x] at h
  rw [h, mul_add, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [pathLayer]
  ring

theorem initial_and_live_path_cost_le (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) :
    1 + (∑ j ∈ Finset.range ((liveSet σ).card / (b + 1)), pathCost C b σ (j + 1)) ≤
      restrictionCost C b σ := by
  have hc : (liveSet σ).card / (b + 1) + 1 ≤ Fintype.card V / (b + 1) + 1 :=
    Nat.add_le_add_right (Nat.div_le_div_right (Finset.card_le_univ (liveSet σ))) 1
  calc
    _ = ∑ j ∈ Finset.range ((liveSet σ).card / (b + 1) + 1), pathCost C b σ j := by
      rw [Finset.sum_range_succ']
      simp only [pathCost_zero]
      ring
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hc)
      (fun j _ _ => pathCost_nonneg C b σ j)

theorem restricted_correlation_le_cost (C : I → Clause V)
    (b : ℕ) (hb : 1 ≤ b) (hn : ∀ i, (C i).Normalized)
    (σ : Restriction V) (G : Cube (Live σ) → ℝ) :
    |finiteAvg (fun x => G x * indicator ((indexedCNF C).eval (fill σ x)))| ≤
      restrictionCost C b σ * corr b G := by
  let K := easyBaseCNF C b σ
  let L := (liveSet σ).card / (b + 1)
  have hlin : finiteAvg (fun x => G x * indicator ((indexedCNF C).eval (fill σ x))) =
      finiteAvg (fun x => G x * indicator (K.eval x)) +
        ∑ j ∈ Finset.range L, (-1 : ℝ) ^ (j + 1) *
          finiteAvg (fun x => G x * pathLayer C b σ K (j + 1) x) := by
    calc
      _ = finiteAvg (fun x => G x * indicator (K.eval x) +
          ∑ j ∈ Finset.range L, (-1 : ℝ) ^ (j + 1) *
            (G x * pathLayer C b σ K (j + 1) x)) := by
        apply finiteAvg_congr
        intro x
        rw [indexedCNF_restriction_expansion, mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        rw [finiteAvg_add, finiteAvg_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        exact finiteAvg_const_mul _ _
  rw [hlin]
  calc
    _ ≤ |finiteAvg (fun x => G x * indicator (K.eval x))| +
        |∑ j ∈ Finset.range L, (-1 : ℝ) ^ (j + 1) *
          finiteAvg (fun x => G x * pathLayer C b σ K (j + 1) x)| := abs_add_le _ _
    _ ≤ corr b G + ∑ j ∈ Finset.range L,
        |(-1 : ℝ) ^ (j + 1) *
          finiteAvg (fun x => G x * pathLayer C b σ K (j + 1) x)| := by
      have htransport (inst₁ inst₂ : Fintype (Cube (Live σ)))
          (f : Cube (Live σ) → ℝ) (c : ℝ)
          (h : |@finiteAvg _ inst₁ f| ≤ c) : |@finiteAvg _ inst₂ f| ≤ c := by
        have hi : inst₁ = inst₂ := Subsingleton.elim _ _
        cases hi
        exact h
      apply add_le_add
      · exact htransport _ _ _ _ (abs_corr_le b G K (easyBaseCNF_widthAtMost C b σ))
      · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ corr b G + ∑ j ∈ Finset.range L, pathCost C b σ (j + 1) * corr b G := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j hj
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
        abs_corr_pathLayer_le C hn b hb σ K (easyBaseCNF_widthAtMost C b σ) (j + 1) G
    _ = (1 + ∑ j ∈ Finset.range L, pathCost C b σ (j + 1)) * corr b G := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ restrictionCost C b σ * corr b G :=
      mul_le_mul_of_nonneg_right (initial_and_live_path_cost_le C b σ) (corr_nonneg b G)

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open Finset
open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [DecidableEq V] [instDecidableEqI : DecidableEq I] [instFintypeI : Fintype I]

def pathRemainder (scope : I → Finset V) (T : Finset V) (P : List I) : Finset V :=
  T \ revealed scope T P

@[simp] theorem pathRemainder_nil
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [instDecidableEqI : DecidableEq I]
    [Fintype I]
    (scope : I → Finset V) (T : Finset V) :
    pathRemainder scope T [] = T := by simp [pathRemainder]

theorem coveredCount_eq_reverseEligible
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [DecidableEq I]
    [instFintypeI : Fintype I]
    (scope : I → Finset V) (T U : Finset V)
    (violation : I → Bool) :
    coveredCount scope T violation U = (reverseEligible scope violation (T \ U)).card := by
  unfold coveredCount reverseEligible
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, residual,
    Finset.disjoint_iff_inter_eq_empty]
  simp only [Finset.mem_filter_univ, and_comm]

def coveredPathWeight (scope : I → Finset V) (T : Finset V)
    (violation : I → Bool) (P : List I) : ℝ :=
  ∏ h : Fin P.length,
    (coveredCount scope T violation (revealed scope T (P.take (h.val + 1))) : ℝ)⁻¹

@[simp] theorem coveredPathWeight_nil (scope : I → Finset V) (T : Finset V)
    (violation : I → Bool) : coveredPathWeight scope T violation [] = 1 := by
  simp [coveredPathWeight]

theorem coveredPathWeight_nonneg (scope : I → Finset V) (T : Finset V)
    (violation : I → Bool) (P : List I) : 0 ≤ coveredPathWeight scope T violation P :=
  prod_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem coveredPathWeight_snoc (scope : I → Finset V) (T : Finset V)
    (violation : I → Bool) (P : List I) (i : I) :
    coveredPathWeight scope T violation (P ++ [i]) =
      coveredPathWeight scope T violation P *
        (coveredCount scope T violation (revealed scope T (P ++ [i])) : ℝ)⁻¹ := by
  unfold coveredPathWeight
  rw [Fin.prod_univ_eq_prod_range
      (fun h : ℕ => (coveredCount scope T violation
        (revealed scope T ((P ++ [i]).take (h + 1))) : ℝ)⁻¹) (P ++ [i]).length,
    Fin.prod_univ_eq_prod_range
      (fun h : ℕ => (coveredCount scope T violation
        (revealed scope T (P.take (h + 1))) : ℝ)⁻¹) P.length]
  rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
  congr 1
  · apply prod_congr rfl
    intro h hh
    rw [List.take_append_of_le_length (Nat.succ_le_of_lt (Finset.mem_range.mp hh))]
  · rw [List.take_of_length_le (by simp)]

theorem remainder_snoc_union_block
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [instDecidableEqI : DecidableEq I]
    [Fintype I]
    (scope : I → Finset V) (T : Finset V)
    (P : List I) (i : I) :
    pathRemainder scope T (P ++ [i]) ∪ residual scope T (revealed scope T P) i =
      pathRemainder scope T P := by
  ext v
  simp only [pathRemainder, revealed_snoc, residual,
    mem_union, mem_sdiff, mem_inter]
  tauto

theorem remainder_snoc_disjoint_block
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [instDecidableEqI : DecidableEq I]
    [Fintype I]
    (scope : I → Finset V) (T : Finset V)
    (P : List I) (i : I) :
    Disjoint (pathRemainder scope T (P ++ [i]))
      (residual scope T (revealed scope T P) i) := by
  apply disjoint_left.mpr
  intro v hR hD
  simp only [pathRemainder, revealed_snoc, mem_sdiff, mem_union, mem_inter] at hR
  simp only [residual, mem_inter, mem_sdiff] at hD
  exact hR.2 (Or.inr ⟨hD.1, hD.2.1⟩)

theorem scope_disjoint_remainder_snoc
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [instDecidableEqI : DecidableEq I]
    [Fintype I]
    (scope : I → Finset V) (T : Finset V)
    (P : List I) (i : I) : Disjoint (scope i) (pathRemainder scope T (P ++ [i])) := by
  apply disjoint_left.mpr
  intro v hi hR
  simp only [pathRemainder, revealed_snoc, mem_sdiff, mem_union, mem_inter] at hR
  exact hR.2 (Or.inr ⟨hi, hR.1⟩)

def reverseEncode (scope : I → Finset V) (T : Finset V) (P : List I) :
    List (I × Finset V) :=
  P.reverseRecOn [] fun Q i rec =>
    (i, residual scope T (revealed scope T Q) i) :: rec

@[simp] theorem reverseEncode_nil
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [instDecidableEqI : DecidableEq I]
    [Fintype I]
    (scope : I → Finset V) (T : Finset V) :
    reverseEncode scope T [] = [] := by simp [reverseEncode]

@[simp] theorem reverseEncode_snoc
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [instDecidableEqI : DecidableEq I]
    [Fintype I]
    (scope : I → Finset V) (T : Finset V)
    (P : List I) (i : I) :
    reverseEncode scope T (P ++ [i]) =
      (i, residual scope T (revealed scope T P) i) :: reverseEncode scope T P := by
  simp [reverseEncode]

def reverseStart (R : Finset V) (L : List (I × Finset V)) : Finset V :=
  L.foldl (fun S q => S ∪ q.2) R

@[simp] theorem reverseStart_nil
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [DecidableEq I]
    [Fintype I]
    (R : Finset V) : reverseStart R ([] : List (I × Finset V)) = R := rfl

@[simp] theorem reverseStart_cons
    {V : Type uDepth1}
    {I : Type uDepth2}
    [DecidableEq V]
    [DecidableEq I]
    [Fintype I]
    (R : Finset V) (i : I) (D : Finset V)
    (L : List (I × Finset V)) :
    reverseStart R ((i,D) :: L) = reverseStart (R ∪ D) L := rfl

theorem reverseStart_encode (scope : I → Finset V) (T : Finset V) (P : List I) :
    reverseStart (pathRemainder scope T P) (reverseEncode scope T P) = T := by
  induction P using List.reverseRecOn with
  | nil => simp
  | append_singleton P i ih =>
    rw [reverseEncode_snoc, reverseStart_cons, remainder_snoc_union_block]
    exact ih

theorem reverseEncode_indices (scope : I → Finset V) (T : Finset V) (P : List I) :
    (reverseEncode scope T P).map Prod.fst = P.reverse := by
  induction P using List.reverseRecOn with
  | nil => simp
  | append_singleton P i ih => simp [ih]

def encodePathPair (scope : I → Finset V) (x : Σ _T : Finset V, List I) :
    Σ _R : Finset V, List (I × Finset V) :=
  ⟨pathRemainder scope x.1 x.2, reverseEncode scope x.1 x.2⟩

theorem encodePathPair_injective (scope : I → Finset V) :
    Function.Injective (encodePathPair scope) := by
  rintro ⟨T,P⟩ ⟨S,Q⟩ h
  have hT := congrArg (fun x : Σ _R : Finset V, List (I × Finset V) =>
    reverseStart x.1 x.2) h
  have hP := congrArg (fun x : Σ _R : Finset V, List (I × Finset V) =>
    (x.2.map Prod.fst).reverse) h
  simp only [encodePathPair, reverseStart_encode] at hT
  simp only [encodePathPair, reverseEncode_indices, List.reverse_reverse] at hP
  subst S
  subst Q
  rfl

def reverseTraces (scope : I → Finset V) (violation : I → Bool) (b : ℕ) :
    ℕ → Finset V → Finset (List (I × Finset V))
  | 0, _ => {[]}
  | s + 1, R => (reverseEligible scope violation R).biUnion fun i =>
      (reverseBlocks b (scope i)).biUnion fun D =>
        (reverseTraces scope violation b s (R ∪ D)).image fun L => (i,D) :: L

@[simp] theorem mem_reverseTraces_zero (scope : I → Finset V) (violation : I → Bool)
    (b : ℕ) (R : Finset V) (L : List (I × Finset V)) :
    L ∈ reverseTraces scope violation b 0 R ↔ L = [] := by
  simp [reverseTraces]

theorem mem_reverseTraces_succ (scope : I → Finset V) (violation : I → Bool)
    (b s : ℕ) (R : Finset V) (L : List (I × Finset V)) :
    L ∈ reverseTraces scope violation b (s+1) R ↔
      ∃ i ∈ reverseEligible scope violation R,
        ∃ D ∈ reverseBlocks b (scope i),
          ∃ M ∈ reverseTraces scope violation b s (R ∪ D), (i,D)::M = L := by
  simp only [reverseTraces, mem_biUnion, mem_image]

theorem reverseEncode_mem (scope : I → Finset V) (violation : I → Bool)
    (b : ℕ) (T : Finset V) {j : ℕ} {P : List I}
    (hP : P ∈ paths scope T b j) (hs : ∀ i ∈ P, violation i = true) :
    reverseEncode scope T P ∈ reverseTraces scope violation b j (pathRemainder scope T P) := by
  induction j generalizing P with
  | zero =>
    have h := (mem_paths_zero scope T b P).mp hP
    subst P
    simp
  | succ j ih =>
    obtain ⟨Q,hQ,i,hi,rfl⟩ := mem_paths_succ.mp hP
    have hsQ : ∀ a ∈ Q, violation a = true := fun a ha => hs a (List.mem_append_left _ ha)
    have hsi : violation i = true := hs i (by simp)
    rw [reverseEncode_snoc]
    apply (mem_reverseTraces_succ scope violation b j _ _).mpr
    refine ⟨i, ?_, residual scope T (revealed scope T Q) i, ?_, reverseEncode scope T Q, ?_, rfl⟩
    · exact (mem_reverseEligible scope violation _ i).mpr
        ⟨hsi, scope_disjoint_remainder_snoc scope T Q i⟩
    · exact (mem_reverseBlocks b _ _).mpr
        ⟨Finset.inter_subset_left, (mem_hardIndices scope T b _ i).mp hi⟩
    · rw [remainder_snoc_union_block]
      exact ih hQ hsQ

def reverseTraceWeight (α : ℝ) (scope : I → Finset V) (violation : I → Bool) :
    Finset V → List (I × Finset V) → ℝ
  | _, [] => 1
  | R, (_,D)::L => reverseChoiceWeight α scope violation R D *
      reverseTraceWeight α scope violation (R ∪ D) L

theorem reverseTraceWeight_nonneg {α : ℝ} (hα : 0 ≤ α)
    (scope : I → Finset V) (violation : I → Bool) (R : Finset V)
    (L : List (I × Finset V)) : 0 ≤ reverseTraceWeight α scope violation R L := by
  induction L generalizing R with
  | nil => simp [reverseTraceWeight]
  | cons q L ih =>
    rcases q with ⟨i,D⟩
    exact mul_nonneg (reverseChoiceWeight_nonneg hα scope violation R D) (ih (R ∪ D))

theorem sum_reverseTraces_succ (scope : I → Finset V) (violation : I → Bool)
    (b s : ℕ) (R : Finset V) (f : List (I × Finset V) → ℝ) :
    (∑ L ∈ reverseTraces scope violation b (s+1) R, f L) =
      ∑ i ∈ reverseEligible scope violation R, ∑ D ∈ reverseBlocks b (scope i),
        ∑ L ∈ reverseTraces scope violation b s (R ∪ D), f ((i,D)::L) := by
  have hi : Set.PairwiseDisjoint (↑(reverseEligible scope violation R) : Set I)
      (fun i => (reverseBlocks b (scope i)).biUnion fun D =>
        (reverseTraces scope violation b s (R ∪ D)).image fun L => (i,D)::L) := by
    intro i hi k hk hik
    apply disjoint_left.mpr
    intro L hL hM
    obtain ⟨D,hD,hL⟩ := mem_biUnion.mp hL
    obtain ⟨E,hE,hM⟩ := mem_biUnion.mp hM
    obtain ⟨L',hL',heq⟩ := mem_image.mp hL
    obtain ⟨M',hM',heq'⟩ := mem_image.mp hM
    have hh := List.cons.inj (heq.trans heq'.symm)
    exact hik (congrArg Prod.fst hh.1)
  rw [reverseTraces, sum_biUnion hi]
  apply sum_congr rfl
  intro i hi
  have hD : Set.PairwiseDisjoint (↑(reverseBlocks b (scope i)) : Set (Finset V))
      (fun D => (reverseTraces scope violation b s (R ∪ D)).image fun L => (i,D)::L) := by
    intro D hD E hE hDE
    apply disjoint_left.mpr
    intro L hL hM
    obtain ⟨L',hL',heq⟩ := mem_image.mp hL
    obtain ⟨M',hM',heq'⟩ := mem_image.mp hM
    have hh := List.cons.inj (heq.trans heq'.symm)
    exact hDE (congrArg Prod.snd hh.1)
  rw [sum_biUnion hD]
  apply sum_congr rfl
  intro D hD
  exact sum_image fun L hL M hM h => (List.cons.inj h).2

theorem sum_reverseTraceWeight (α : ℝ) (scope : I → Finset V)
    (violation : I → Bool) (b j : ℕ) (R : Finset V) :
    (∑ L ∈ reverseTraces scope violation b j R, reverseTraceWeight α scope violation R L) =
      reverseTotal α b scope violation j R := by
  induction j generalizing R with
  | zero => simp [reverseTraces, reverseTraceWeight]
  | succ j ih =>
    rw [sum_reverseTraces_succ]
    simp_rw [reverseTraceWeight, ← Finset.mul_sum, ih]
    by_cases h : (reverseEligible scope violation R).Nonempty
    · rw [reverseTotal_succ_of_nonempty α b scope violation j R h,
        Finset.sum_div]
      apply sum_congr rfl
      intro i hi
      rw [Finset.sum_div]
      apply sum_congr rfl
      intro D hD
      unfold reverseChoiceWeight
      ring
    · have he := Finset.not_nonempty_iff_eq_empty.mp h
      rw [reverseTotal_succ_of_empty α b scope violation j R he, he]
      simp

variable [Fintype V]

theorem reverseEncode_weight (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (scope : I → Finset V) (violation : I → Bool) (T : Finset V) (P : List I) :
    bernoulliWeight p T * (2 : ℝ) ^ (revealed scope T P).card *
        coveredPathWeight scope T violation P =
      bernoulliWeight p (pathRemainder scope T P) *
        reverseTraceWeight (2*p/(1-p)) scope violation
          (pathRemainder scope T P) (reverseEncode scope T P) := by
  induction P using List.reverseRecOn with
  | nil => simp [reverseTraceWeight]
  | append_singleton P i ih =>
    let D := residual scope T (revealed scope T P) i
    let R := pathRemainder scope T (P ++ [i])
    have hR : R ∪ D = pathRemainder scope T P := remainder_snoc_union_block scope T P i
    have hdis : Disjoint R D := remainder_snoc_disjoint_block scope T P i
    have hbal := bernoulliWeight_disjoint_union hp0 hp1 R D hdis
    rw [hR] at hbal
    rw [coveredPathWeight_snoc, card_revealed_snoc, pow_add,
      coveredCount_eq_reverseEligible, reverseEncode_snoc]
    change bernoulliWeight p T *
        ((2 : ℝ) ^ (revealed scope T P).card * (2 : ℝ) ^ D.card) *
        (coveredPathWeight scope T violation P *
          ((reverseEligible scope violation R).card : ℝ)⁻¹) =
      bernoulliWeight p R *
        (reverseChoiceWeight (2*p/(1-p)) scope violation R D *
          reverseTraceWeight (2*p/(1-p)) scope violation (R ∪ D) (reverseEncode scope T P))
    rw [hR]
    calc
      _ = (bernoulliWeight p T * (2 : ℝ) ^ (revealed scope T P).card *
          coveredPathWeight scope T violation P) * (2 : ℝ)^D.card *
          ((reverseEligible scope violation R).card : ℝ)⁻¹ := by ring
      _ = (bernoulliWeight p (pathRemainder scope T P) * (2 : ℝ)^D.card) *
          reverseTraceWeight (2*p/(1-p)) scope violation (pathRemainder scope T P)
            (reverseEncode scope T P) * ((reverseEligible scope violation R).card : ℝ)⁻¹ := by
            rw [ih]
            ring
      _ = _ := by rw [hbal]; unfold reverseChoiceWeight; ring

def supportedForwardPairs (scope : I → Finset V) (violation : I → Bool) (b j : ℕ) :
    Finset (Σ _T : Finset V, List I) :=
  univ.sigma fun T => (paths scope T b j).filter fun P => ∀ i ∈ P, violation i = true

def indexedReverseTraces (scope : I → Finset V) (violation : I → Bool) (b j : ℕ) :
    Finset (Σ _R : Finset V, List (I × Finset V)) :=
  univ.sigma fun R => reverseTraces scope violation b j R

theorem encode_supported_mem (scope : I → Finset V) (violation : I → Bool) (b j : ℕ)
    {x : Σ _T : Finset V, List I} (hx : x ∈ supportedForwardPairs scope violation b j) :
    encodePathPair scope x ∈ indexedReverseTraces scope violation b j := by
  rcases x with ⟨T,P⟩
  have hh := mem_filter.mp (mem_sigma.mp hx).2
  exact mem_sigma.mpr ⟨mem_univ _, reverseEncode_mem scope violation b T hh.1 hh.2⟩

theorem weighted_supported_paths_le (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (b k : ℕ) (scope : I → Finset V) (hscope : ∀ i, (scope i).card ≤ k)
    (violation : I → Bool) (j : ℕ) :
    (∑ T : Finset V, bernoulliWeight p T *
      ∑ P ∈ paths scope T b j, if ∀ i ∈ P, violation i = true then
        (2 : ℝ) ^ (revealed scope T P).card * coveredPathWeight scope T violation P else 0) ≤
      (reverseTheta (2*p/(1-p)) b k) ^ j := by
  let α : ℝ := 2*p/(1-p)
  have hα : 0 ≤ α := div_nonneg (mul_nonneg (by norm_num) hp0.le) (sub_pos.mpr hp1).le
  let w : (Σ _R : Finset V, List (I × Finset V)) → ℝ := fun x =>
    bernoulliWeight p x.1 * reverseTraceWeight α scope violation x.1 x.2
  have hw : ∀ x, 0 ≤ w x := fun x => mul_nonneg
    (bernoulliWeight_nonneg hp0.le hp1.le x.1) (reverseTraceWeight_nonneg hα scope violation x.1 x.2)
  have hs : (supportedForwardPairs scope violation b j).image (encodePathPair scope) ⊆
      indexedReverseTraces scope violation b j := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact encode_supported_mem scope violation b j hy
  calc
    _ = ∑ x ∈ supportedForwardPairs scope violation b j, w (encodePathPair scope x) := by
      rw [supportedForwardPairs, Finset.sum_sigma]
      apply sum_congr rfl
      intro T hT
      rw [← Finset.sum_filter, Finset.mul_sum]
      apply sum_congr rfl
      intro P hP
      exact (mul_assoc _ _ _).symm.trans (reverseEncode_weight p hp0 hp1 scope violation T P)
    _ = ∑ x ∈ (supportedForwardPairs scope violation b j).image (encodePathPair scope), w x := by
      symm
      exact sum_image fun x hx y hy h => encodePathPair_injective scope h
    _ ≤ ∑ x ∈ indexedReverseTraces scope violation b j, w x :=
      sum_le_sum_of_subset_of_nonneg hs (fun x hx hn => hw x)
    _ = ∑ R : Finset V, bernoulliWeight p R * reverseTotal α b scope violation j R := by
      rw [indexedReverseTraces, Finset.sum_sigma]
      apply sum_congr rfl
      intro R hR
      change (∑ L ∈ reverseTraces scope violation b j R,
        bernoulliWeight p R * reverseTraceWeight α scope violation R L) = _
      rw [← Finset.mul_sum, sum_reverseTraceWeight]
    _ ≤ ∑ R : Finset V, bernoulliWeight p R * (reverseTheta α b k)^j := by
      apply sum_le_sum
      intro R hR
      exact mul_le_mul_of_nonneg_left
        (reverseTotal_le_theta_pow hα b k scope hscope violation j R)
        (bernoulliWeight_nonneg hp0.le hp1.le R)
    _ = _ := by rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [Fintype V] [Fintype I]

theorem pathCoveredCount_eq_of_support (C : I → Clause V) (σ : Restriction V)
    (P : List I) (x : Cube (Live σ))
    (hn : ∀ i ∈ P, (C i).Normalized)
    (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true)
    (h : Fin P.length) :
    pathCoveredCount C σ P h =
      coveredCount (fun i => (C i).scope) (liveSet σ)
        (fun i => (C i).violation (fill σ x)) (pathPrefixSet C σ P h) := by
  have hc : pathCompatible C σ P := ⟨x, hx⟩
  have hZ : ∀ v ∈ pathFinalSet C σ P,
      fill σ (pathCenter C σ P) v = fill σ x v := by
    exact (simultaneous_restricted_violation_iff C σ (liveSet σ)
      (fun v => mem_liveSet σ v) P (pathCenter C σ P) x hn hx).mp
        (pathCenter_support C σ P hc)
  unfold pathCoveredCount
  apply coveredCount_eq_on_larger_cylinder C (liveSet σ)
    (pathPrefixSet C σ P h) (pathFinalSet C σ P)
    (fill σ (pathCenter C σ P)) (fill σ x)
    (pathPrefixSet_subset_final C σ P h) hZ
  intro v hv
  exact fill_agree_outside_live σ (pathCenter C σ P) x v
    (by simpa only [mem_liveSet] using hv)

theorem pathWeight_eq_coveredPathWeight_of_support (C : I → Clause V)
    (σ : Restriction V) (P : List I) (x : Cube (Live σ))
    (hn : ∀ i ∈ P, (C i).Normalized)
    (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true) :
    pathWeight C σ P = coveredPathWeight (fun i => (C i).scope) (liveSet σ)
      (fun i => (C i).violation (fill σ x)) P := by
  unfold pathWeight coveredPathWeight
  apply Finset.prod_congr rfl
  intro h hh
  exact congrArg (fun n : ℕ => (n : ℝ)⁻¹)
    (pathCoveredCount_eq_of_support C σ P x hn hx h)

theorem pathWeight_eq_finiteAvg_supported (C : I → Clause V)
    (σ : Restriction V) (P : List I) (hn : ∀ i ∈ P, (C i).Normalized) :
    (if pathCompatible C σ P then pathWeight C σ P else 0) =
      finiteAvg (fun x : Cube (Live σ) =>
        if ∀ i ∈ P, (C i).violation (fill σ x) = true then
          (2 : ℝ) ^ (pathFinalSet C σ P).card *
            coveredPathWeight (fun i => (C i).scope) (liveSet σ)
              (fun i => (C i).violation (fill σ x)) P
        else 0) := by
  by_cases hc : pathCompatible C σ P
  · rw [ite_eq_left hc]
    symm
    calc
      _ = finiteAvg (fun x : Cube (Live σ) =>
          ((2 : ℝ) ^ (pathFinalSet C σ P).card * pathWeight C σ P) *
            indicator (decide (∀ i ∈ P, (C i).violation (fill σ x) = true))) := by
        apply finiteAvg_congr
        intro x
        by_cases hx : ∀ i ∈ P, (C i).violation (fill σ x) = true
        · rw [ite_eq_left hx, ← pathWeight_eq_coveredPathWeight_of_support C σ P x hn hx]
          rw [decide_eq_true hx, indicator_true, mul_one]
        · rw [ite_eq_right hx, decide_eq_false hx, indicator_false, mul_zero]
      _ = ((2 : ℝ) ^ (pathFinalSet C σ P).card * pathWeight C σ P) *
          ((2 : ℝ) ^ (pathFinalSet C σ P).card)⁻¹ := by
        rw [finiteAvg_const_mul, path_cylinder_probability C σ P hn hc]
      _ = pathWeight C σ P := by
        have htwo : (2 : ℝ) ^ (pathFinalSet C σ P).card ≠ 0 :=
          pow_ne_zero _ (by norm_num)
        calc
          _ = pathWeight C σ P *
              ((2 : ℝ) ^ (pathFinalSet C σ P).card *
                ((2 : ℝ) ^ (pathFinalSet C σ P).card)⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ htwo, mul_one]
  · rw [ite_eq_right hc]
    symm
    calc
      _ = finiteAvg (fun _ : Cube (Live σ) => (0 : ℝ)) := by
        apply finiteAvg_congr
        intro x
        have hx : ¬ ∀ i ∈ P, (C i).violation (fill σ x) = true :=
          fun hx => hc ⟨x, hx⟩
        simp only [ite_eq_right hx]
      _ = 0 := finiteAvg_zero

def fullAssignmentPathCost (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (j : ℕ) (y : Cube V) : ℝ :=
  ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b j,
    if ∀ i ∈ P, (C i).violation y = true then
      (2 : ℝ) ^ (pathFinalSet C σ P).card *
        coveredPathWeight (fun i => (C i).scope) (liveSet σ)
          (fun i => (C i).violation y) P
    else 0

theorem pathCost_eq_finiteAvg_supported (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (j : ℕ) (hn : ∀ i, (C i).Normalized) :
    pathCost C b σ j = finiteAvg (fun x : Cube (Live σ) =>
      fullAssignmentPathCost C b σ j (fill σ x)) := by
  unfold pathCost fullAssignmentPathCost
  rw [finiteAvg_sum]
  apply Finset.sum_congr rfl
  intro P hP
  exact pathWeight_eq_finiteAvg_supported C σ P (fun i _ => hn i)

theorem restrictionAvg_pathCost_reweight (C : I → Clause V) (p : ℝ)
    (b j : ℕ) (hn : ∀ i, (C i).Normalized) :
    restrictionAvg p (fun σ => pathCost C b σ j) =
      finiteAvg (fun y : Cube V =>
        ∑ T : Finset V, bernoulliWeight p T *
          fullAssignmentPathCost C b (maskRestriction T y) j y) := by
  calc
    _ = restrictionAvg p (fun σ => finiteAvg (fun x : Cube (Live σ) =>
        fullAssignmentPathCost C b σ j (fill σ x))) := by
      unfold restrictionAvg
      apply Finset.sum_congr rfl
      intro σ hσ
      exact congrArg (fun t : ℝ => restrictionWeight p σ * t)
        (pathCost_eq_finiteAvg_supported C b σ j hn)
    _ = _ := restrictionAvg_fill_reweight p
      (fun σ y => fullAssignmentPathCost C b σ j y)

theorem restrictionAvg_pathCost_le (C : I → Clause V) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (b k j : ℕ)
    (hn : ∀ i, (C i).Normalized) (hwidth : ∀ i, (C i).scope.card ≤ k) :
    restrictionAvg p (fun σ => pathCost C b σ j) ≤
      (reverseTheta (2 * p / (1 - p)) b k) ^ j := by
  rw [restrictionAvg_pathCost_reweight C p b j hn]
  calc
    _ ≤ finiteAvg (fun _ : Cube V => (reverseTheta (2 * p / (1 - p)) b k) ^ j) := by
      apply finiteAvg_mono
      intro y
      simpa only [fullAssignmentPathCost, pathFinalSet, liveSet_maskRestriction]
        using weighted_supported_paths_le p hp0 hp1 b k (fun i => (C i).scope)
          hwidth (fun i => (C i).violation y) j
    _ = _ := finiteAvg_const _

theorem restrictionAvg_restrictionCost_le_sum (C : I → Clause V) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (b k : ℕ)
    (hn : ∀ i, (C i).Normalized) (hwidth : ∀ i, (C i).scope.card ≤ k) :
    restrictionAvg p (fun σ => restrictionCost C b σ) ≤
      ∑ j ∈ Finset.range (Fintype.card V / (b + 1) + 1),
        (reverseTheta (2 * p / (1 - p)) b k) ^ j := by
  have hsum : restrictionAvg p (fun σ => restrictionCost C b σ) =
      ∑ j ∈ Finset.range (Fintype.card V / (b + 1) + 1),
        restrictionAvg p (fun σ => pathCost C b σ j) := by
    unfold restrictionAvg restrictionCost
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hsum]
  exact Finset.sum_le_sum fun j hj =>
    restrictionAvg_pathCost_le C p hp0 hp1 b k j hn hwidth

theorem restrictionAvg_restrictionCost_le (C : I → Clause V) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (b k : ℕ)
    (hn : ∀ i, (C i).Normalized) (hwidth : ∀ i, (C i).scope.card ≤ k)
    (hθ : reverseTheta (2 * p / (1 - p)) b k < 1) :
    restrictionAvg p (fun σ => restrictionCost C b σ) ≤
      (1 - reverseTheta (2 * p / (1 - p)) b k)⁻¹ := by
  have hα : 0 ≤ 2 * p / (1 - p) :=
    div_nonneg (mul_nonneg (by norm_num) hp0.le) (sub_nonneg.mpr hp1.le)
  have hθ0 := reverseTheta_nonneg hα b k
  refine (restrictionAvg_restrictionCost_le_sum C p hp0 hp1 b k hn hwidth).trans ?_
  simpa only [Nat.Ico_zero_eq_range, pow_zero, one_div] using
    (geom_sum_Ico_le_of_lt_one hθ0 hθ
      (m := 0) (n := Fintype.card V / (b + 1) + 1))

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V]

def restrictionTheta (k b : ℕ) (p : ℝ) : ℝ :=
  ∑ l ∈ Finset.Icc (b + 1) k, (k.choose l : ℝ) * (2 * p / (1 - p)) ^ l

theorem restrictionTheta_eq_reverseTheta (k b : ℕ) (p : ℝ) :
    restrictionTheta k b p = reverseTheta (2 * p / (1 - p)) b k := by
  have hs : (Finset.range (k + 1)).filter (fun l => b < l) = Finset.Icc (b + 1) k := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  unfold reverseTheta
  rw [← Finset.sum_filter, hs]
  rfl

def cnfRestrictionCost (H : CNF V) (b : ℕ) (σ : Restriction V) : ℝ :=
  restrictionCost (cnfIndexFamily H.normalize) b σ

theorem cnfRestrictionCost_nonneg (H : CNF V) (b : ℕ) (σ : Restriction V) :
    0 ≤ cnfRestrictionCost H b σ :=
  restrictionCost_nonneg (cnfIndexFamily H.normalize) b σ

theorem cnf_restricted_correlation_le_cost (H : CNF V) (b : ℕ) (hb : 1 ≤ b)
    (σ : Restriction V) (G : Cube (Live σ) → ℝ) :
    |finiteAvg (fun x => G x * indicator (H.eval (fill σ x)))| ≤
      cnfRestrictionCost H b σ * corr b G := by
  have hn : ∀ i, (cnfIndexFamily H.normalize i).Normalized :=
    cnfIndexFamily_normalized (CNF.normalize_normalized H)
  simpa only [cnfRestrictionCost, indexedCNF_cnfIndexFamily_eval, CNF.eval_normalize] using
    restricted_correlation_le_cost (cnfIndexFamily H.normalize) b hb hn σ G

theorem restrictionAvg_cnfRestrictionCost_le (H : CNF V) (b k : ℕ)
    (hH : H.WidthAtMost k) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hθ : restrictionTheta k b p < 1) :
    restrictionAvg p (cnfRestrictionCost H b) ≤ 1 / (1 - restrictionTheta k b p) := by
  have hn : ∀ i, (cnfIndexFamily H.normalize i).Normalized :=
    cnfIndexFamily_normalized (CNF.normalize_normalized H)
  have hw : ∀ i, (cnfIndexFamily H.normalize i).scope.card ≤ k :=
    cnfIndexFamily_width (CNF.normalize_widthAtMost hH)
  have ht : reverseTheta (2 * p / (1 - p)) b k < 1 := by
    simpa only [restrictionTheta_eq_reverseTheta] using hθ
  simpa +unfoldPartialApp only [cnfRestrictionCost, restrictionTheta_eq_reverseTheta, one_div] using
    restrictionAvg_restrictionCost_le (cnfIndexFamily H.normalize) p hp0 hp1 b k hn hw ht

theorem cnf_restriction_bound (H : CNF V) (b k : ℕ) (hb : 1 ≤ b)
    (hH : H.WidthAtMost k) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hθ : restrictionTheta k b p < 1) :
    ∃ W : Restriction V → ℝ,
      (∀ σ, 0 ≤ W σ) ∧
      restrictionAvg p W ≤ 1 / (1 - restrictionTheta k b p) ∧
      ∀ (σ : Restriction V) (G : Cube (Live σ) → ℝ),
        |finiteAvg (fun x => G x * indicator (H.eval (fill σ x)))| ≤ W σ * corr b G := by
  refine ⟨cnfRestrictionCost H b, cnfRestrictionCost_nonneg H b, ?_, ?_⟩
  · exact restrictionAvg_cnfRestrictionCost_le H b k hH p hp0 hp1 hθ
  · exact cnf_restricted_correlation_le_cost H b hb

theorem restrictionAvg_cnfRestrictionCost_le_two (H : CNF V) (b k : ℕ)
    (hH : H.WidthAtMost k) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hθ : restrictionTheta k b p ≤ 1 / 2) :
    restrictionAvg p (cnfRestrictionCost H b) ≤ 2 := by
  have ht : restrictionTheta k b p < 1 := by linarith
  have hd : 0 < 1 - restrictionTheta k b p := sub_pos.mpr ht
  refine (restrictionAvg_cnfRestrictionCost_le H b k hH p hp0 hp1 ht).trans ?_
  apply (div_le_iff₀ hd).mpr
  linarith

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V] [instDecidableEqV : DecidableEq V]

theorem restrictionAvg_mask_le
    {V : Type uDepth1}
    [Fintype V]
    [DecidableEq V]
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (W : Restriction V → ℝ) (hW : ∀ σ, 0 ≤ W σ)
    (good : Restriction V → Prop) :
    restrictionAvg p (fun σ => if good σ then W σ else 0) ≤ restrictionAvg p W := by
  apply restrictionAvg_mono hp hp1
  intro σ
  split_ifs
  · exact le_rfl
  · exact hW σ

theorem restrictionAvg_abs_le_split {p ε δ C : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε)
    (q W : Restriction V → ℝ) (good : Restriction V → Prop)
    (hW : ∀ σ, 0 ≤ W σ) (hmean : restrictionAvg p W ≤ C)
    (hgood : ∀ σ, good σ → |q σ| ≤ ε * W σ)
    (hunit : ∀ σ, |q σ| ≤ 1)
    (hbad : restrictionAvg p (fun σ => if ¬ good σ then 1 else 0) ≤ δ) :
    |restrictionAvg p q| ≤ ε * C + δ := by
  have hmask : restrictionAvg p (fun σ => if good σ then W σ else 0) ≤ C :=
    (restrictionAvg_mask_le hp hp1 W hW good).trans hmean
  calc
    |restrictionAvg p q| ≤ restrictionAvg p (fun σ => |q σ|) :=
      restrictionAvg_abs_le hp hp1 q
    _ ≤ restrictionAvg p (fun σ =>
        ε * (if good σ then W σ else 0) + (if ¬ good σ then 1 else 0)) := by
      apply restrictionAvg_mono hp hp1
      intro σ
      by_cases h : good σ
      · simpa only [h, ite_true, not_true_eq_false, ite_false, add_zero]
          using hgood σ h
      · simpa only [h, ite_false, not_false_eq_true, ite_true, mul_zero, zero_add]
          using hunit σ
    _ = ε * restrictionAvg p (fun σ => if good σ then W σ else 0) +
        restrictionAvg p (fun σ => if ¬ good σ then 1 else 0) := by
      rw [restrictionAvg_add, restrictionAvg_const_mul]
    _ ≤ ε * C + δ := add_le_add (mul_le_mul_of_nonneg_left hmask hε) hbad

theorem abs_finiteAvg_sign_indicator_le_one {Z : Type uDepth2} [Fintype Z]
    (f J : Cube Z → Bool) :
    |finiteAvg (fun x => sign (f x) * indicator (J x))| ≤ 1 := by
  calc
    _ ≤ finiteAvg (fun x => |sign (f x) * indicator (J x)|) := finiteAvg_abs_le _
    _ ≤ finiteAvg (fun _ : Cube Z => (1 : ℝ)) := by
      apply finiteAvg_mono
      intro x
      cases f x <;> cases J x <;> norm_num [sign, indicator]
    _ = 1 := finiteAvg_const _

theorem restriction_correlation_transfer {p ε δ C : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε)
    (f : Cube V → Bool) (H : CNF V) (b : ℕ)
    (good : Restriction V → Prop) (W : Restriction V → ℝ)
    (hW : ∀ σ, 0 ≤ W σ) (hmean : restrictionAvg p W ≤ C)
    (hdom : ∀ σ,
      |finiteAvg (fun z : Cube (Live σ) =>
        sign (f (fill σ z)) * indicator (H.eval (fill σ z)))| ≤
        W σ * corr b (fun z => sign (f (fill σ z))))
    (hgood : ∀ σ, good σ → corr b (fun z => sign (f (fill σ z))) ≤ ε)
    (hbad : restrictionAvg p (fun σ => if ¬ good σ then 1 else 0) ≤ δ) :
    |finiteAvg (fun x => sign (f x) * indicator (H.eval x))| ≤ ε * C + δ := by
  rw [← restrictionAvg_fill p (fun x => sign (f x) * indicator (H.eval x))]
  apply restrictionAvg_abs_le_split hp hp1 hε _ W good hW hmean
  · intro σ hσ
    calc
      _ ≤ W σ * corr b (fun z => sign (f (fill σ z))) := hdom σ
      _ ≤ W σ * ε := mul_le_mul_of_nonneg_left (hgood σ hσ) (hW σ)
      _ = ε * W σ := mul_comm _ _
  · intro σ
    calc
      _ ≤ finiteAvg (fun z : Cube (Live σ) =>
          |sign (f (fill σ z)) * indicator (H.eval (fill σ z))|) := finiteAvg_abs_le _
      _ ≤ finiteAvg (fun _ : Cube (Live σ) => (1 : ℝ)) := by
        apply finiteAvg_mono
        intro z
        cases f (fill σ z) <;> cases H.eval (fill σ z) <;> norm_num [sign, indicator]
      _ = 1 := finiteAvg_const _
  · exact hbad

theorem restriction_correlation_transfer_six {p ε : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε)
    (f : Cube V → Bool) (H : CNF V) (b : ℕ)
    (good : Restriction V → Prop) (W : Restriction V → ℝ)
    (hW : ∀ σ, 0 ≤ W σ) (hmean : restrictionAvg p W ≤ 2)
    (hdom : ∀ σ,
      |finiteAvg (fun z : Cube (Live σ) =>
        sign (f (fill σ z)) * indicator (H.eval (fill σ z)))| ≤
        W σ * corr b (fun z => sign (f (fill σ z))))
    (hgood : ∀ σ, good σ → corr b (fun z => sign (f (fill σ z))) ≤ ε)
    (hbad : restrictionAvg p (fun σ => if ¬ good σ then 1 else 0) ≤ 4 * ε) :
    |finiteAvg (fun x => sign (f x) * indicator (H.eval x))| ≤ 6 * ε := by
  have h := restriction_correlation_transfer hp hp1 hε f H b good W hW hmean
    hdom hgood hbad
  linarith

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V] [DecidableEq V]

theorem wide_correlation_of_good_restrictions {p ε : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    (b k : ℕ) (hb : 1 ≤ b) (hθ : restrictionTheta k b p ≤ 1 / 2)
    (f : Cube V → Bool)
    (hbad : restrictionAvg p (fun σ => if ¬ goodRestriction p ε b f σ then 1 else 0) ≤
      4 * ε) :
    ∀ H : CNF V, H.WidthAtMost k →
      |finiteAvg (fun x => sign (f x) * indicator (H.eval x))| ≤ 6 * ε := by
  intro H hH
  exact restriction_correlation_transfer_six hp0.le hp1.le hε f H b
    (goodRestriction p ε b f) (cnfRestrictionCost H b)
    (cnfRestrictionCost_nonneg H b)
    (restrictionAvg_cnfRestrictionCost_le_two H b k hH p hp0 hp1 hθ)
    (fun σ => by
      have htransport (inst₁ inst₂ : Fintype (Cube (Live σ)))
          (g : Cube (Live σ) → ℝ) (c : ℝ)
          (h : |@finiteAvg _ inst₁ g| ≤ c) : |@finiteAvg _ inst₂ g| ≤ c := by
        have hi : inst₁ = inst₂ := Subsingleton.elim _ _
        cases hi
        exact h
      exact htransport _ _ _ _
        (cnf_restricted_correlation_le_cost H b hb σ
          (fun z => sign (f (fill σ z)))))
    (fun _ h => goodRestriction_corr h) hbad

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

theorem exists_language_slice_small_correlations (s : ℝ) (hs : 0 ≤ s) :
    ∃ N : ℕ, 20480 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ α : Fin n → Sum (Fin (dataDimension n)) Bool,
        ∀ H : CNF (Fin (dataDimension n)),
          H.WidthAtMost (degreeCutoff s (dataDimension n)) →
          |finiteAvg (fun x =>
            sign (language (List.ofFn (GateInput.assignment α x))) * indicator (H.eval x))| ≤
            6 * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) / 16) := by
  let B : ℝ := 64 * (s + 1)
  have hB : 0 < B := by dsimp [B]; linarith
  obtain ⟨b, hb, D, hD, hparams⟩ := exists_final_parameter_width B s hB hs
  obtain ⟨Ng, hNg, hgood⟩ := exists_good_language_slice_eventually b hb B hB
  refine ⟨max Ng (5 * D), hNg.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hng : Ng ≤ n := (le_max_left _ _).trans hn
  have hnd : 5 * D ≤ n := (le_max_right _ _).trans hn
  have hDd : D ≤ dataDimension n := by unfold dataDimension; omega
  obtain ⟨hp0, hphalf, hθ⟩ := hparams (dataDimension n) hDd
  have hp1 : liveProbability B (dataDimension n) < 1 := by linarith
  have hθ' : restrictionTheta (degreeCutoff s (dataDimension n)) b
      (liveProbability B (dataDimension n)) ≤ 1 / 2 := by
    simpa only [restrictionTheta_eq_reverseTheta] using hθ
  obtain ⟨α, hα⟩ := hgood n hng
  refine ⟨α, ?_⟩
  exact wide_correlation_of_good_restrictions hp0 hp1
    (Real.rpow_nonneg (by norm_num) _) b (degreeCutoff s (dataDimension n)) hb hθ'
    (fun x => language (List.ofFn (GateInput.assignment α x))) hα

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


namespace DepthThreeLowerBound

variable {V : Type uDepth1}

namespace RawClause

def literalPart : GateInput V → Option (Literal V)
  | .inl l => some l
  | .inr _ => none

noncomputable def literals (C : RawClause V) : Clause V := by
  classical
  exact (C.filterMap literalPart).toFinset

@[simp] theorem mem_literals (C : RawClause V) (l : Literal V) :
    l ∈ C.literals ↔ Sum.inl l ∈ C := by
  classical
  simp only [literals, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, he⟩
    cases a with
    | inl k =>
      have hk : k = l := Option.some.inj he
      simpa [hk] using ha
    | inr b => simp [literalPart] at he
  · intro h
    exact ⟨.inl l, h, rfl⟩

theorem eval_true_iff (C : RawClause V) (x : Cube V) :
    C.eval x = true ↔ Sum.inr true ∈ C ∨ C.literals.eval x = true := by
  rw [eval_eq_true, Clause.eval_eq_true]
  constructor
  · rintro ⟨a, ha, hx⟩
    cases a with
    | inl l => exact Or.inr ⟨l, (mem_literals C l).mpr ha, (Literal.eval_eq_true l x).mp hx⟩
    | inr b =>
      change b = true at hx
      exact Or.inl (hx ▸ ha)
  · rintro (h | ⟨l, hl, hx⟩)
    · exact ⟨.inr true, h, rfl⟩
    · exact ⟨.inl l, (mem_literals C l).mp hl, (Literal.eval_eq_true l x).mpr hx⟩

noncomputable def normalize (C : RawClause V) : Option (Clause V) := by
  classical
  exact if Sum.inr true ∈ C ∨ ¬ C.literals.Normalized then none else some C.literals

theorem normalized_of_normalize_eq_some {C : RawClause V} {D : Clause V}
    (h : C.normalize = some D) : D.Normalized := by
  classical
  unfold normalize at h
  split at h
  · contradiction
  · rename_i hn
    have hCD : C.literals = D := Option.some.inj h
    rw [← hCD]
    exact Classical.not_not.mp (fun hbad => hn (Or.inr hbad))

theorem normalize_eval (C : RawClause V) (x : Cube V) :
    ((C.normalize).map (fun D => D.eval x)).getD true = C.eval x := by
  classical
  unfold normalize
  split
  · rename_i h
    have ht : C.eval x = true := by
      apply (eval_true_iff C x).mpr
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Clause.eval_true_of_not_normalized h x)
    simp [ht]
  · rename_i h
    have hc : Sum.inr true ∉ C := fun hc => h (Or.inl hc)
    change C.literals.eval x = C.eval x
    apply Bool.eq_iff_iff.mpr
    rw [eval_true_iff]
    simp [hc]

end RawClause

namespace Circuit3

noncomputable def middleCNF (C : Circuit3 V) (j : Fin C.middleCount) : CNF V :=
  (C.middle j).toList.filterMap fun i => (C.bottom i).normalize

theorem mem_middleCNF (C : Circuit3 V) (j : Fin C.middleCount) (D : Clause V) :
    D ∈ C.middleCNF j ↔ ∃ i ∈ C.middle j, (C.bottom i).normalize = some D := by
  simp [middleCNF, List.mem_filterMap]

theorem middleCNF_normalized (C : Circuit3 V) (j : Fin C.middleCount) :
    (C.middleCNF j).Normalized := by
  intro D hD
  obtain ⟨i, _, hi⟩ := (mem_middleCNF C j D).mp hD
  exact RawClause.normalized_of_normalize_eq_some hi

theorem middleCNF_length_le_bottomCount (C : Circuit3 V) (j : Fin C.middleCount) :
    (C.middleCNF j).length ≤ C.bottomCount := by
  calc
    (C.middleCNF j).length ≤ (C.middle j).toList.length := List.length_filterMap_le _ _
    _ = (C.middle j).card := Finset.length_toList _
    _ ≤ C.bottomCount := by simpa using Finset.card_le_univ (C.middle j)

theorem middleCNF_length_le_gateCount (C : Circuit3 V) (j : Fin C.middleCount) :
    (C.middleCNF j).length ≤ C.gateCount :=
  (C.middleCNF_length_le_bottomCount j).trans C.bottomCount_le_gateCount

@[simp] theorem eval_middleCNF (C : Circuit3 V) (j : Fin C.middleCount) (x : Cube V) :
    (C.middleCNF j).eval x = C.middleEval j x := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [CNF.eval_eq_true, middleEval_eq_true]
  constructor
  · intro hx i hi
    have he := (C.bottom i).normalize_eval x
    cases hn : (C.bottom i).normalize with
    | none => simpa [hn] using he.symm
    | some D =>
      have hD := hx D ((mem_middleCNF C j D).mpr ⟨i, hi, hn⟩)
      simpa [hn, hD] using he.symm
  · intro hx D hD
    obtain ⟨i, hi, hn⟩ := (mem_middleCNF C j D).mp hD
    have he := (C.bottom i).normalize_eval x
    simpa [hn, hx i hi] using he

theorem eval_eq_true_iff_middleCNF (C : Circuit3 V) (x : Cube V) :
    C.eval x = true ↔ ∃ j ∈ C.top, (C.middleCNF j).eval x = true := by
  simp only [eval_middleCNF, eval_eq_true]

theorem middleCNF_implies_output (C : Circuit3 V) {j : Fin C.middleCount}
    (hj : j ∈ C.top) {x : Cube V} (hx : (C.middleCNF j).eval x = true) :
    C.eval x = true := (eval_eq_true_iff_middleCNF C x).mpr ⟨j, hj, hx⟩

end Circuit3

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI


noncomputable section

attribute [local instance] Classical.propDecidable

namespace DepthThreeLowerBound

variable {V : Type uDepth1}

namespace Clause

theorem violation_probability [Fintype V] (C : Clause V) (hC : C.Normalized) :
    finiteAvg (fun x : Cube V => indicator (C.violation x)) =
      ((2 : ℝ) ^ C.width)⁻¹ := by
  have hpoint (x : Cube V) :
      indicator (C.violation x) =
        if ∀ v ∈ C.scope, x v = C.forbiddenValue v then (1 : ℝ) else 0 := by
    simp only [← eval_eq_false_iff_forbidden hC x]
    cases hx : C.eval x <;> simp [violation, indicator, hx]
  calc
    _ = finiteAvg (fun x : Cube V =>
        if ∀ v ∈ C.scope, x v = C.forbiddenValue v then (1 : ℝ) else 0) :=
      finiteAvg_congr hpoint
    _ = ((2 : ℝ) ^ C.width)⁻¹ := by
      simpa only [width] using finiteAvg_eq_pattern C.scope C.forbiddenValue

theorem false_probability [Fintype V] (C : Clause V) (hC : C.Normalized) :
    finiteAvg (fun x : Cube V => 1 - indicator (C.eval x)) =
      ((2 : ℝ) ^ C.width)⁻¹ := by
  refine (finiteAvg_congr fun x => ?_).trans (violation_probability C hC)
  cases hx : C.eval x <;> simp [violation, indicator, hx]

end Clause

namespace CNF

def deleteWide (H : CNF V) (k : ℕ) : CNF V :=
  H.filter fun C => decide (C.width ≤ k)

@[simp] theorem mem_deleteWide {H : CNF V} {k : ℕ} {C : Clause V} :
    C ∈ H.deleteWide k ↔ C ∈ H ∧ C.width ≤ k := by
  simp [deleteWide]

@[simp] theorem deleteWide_nil (k : ℕ) :
    CNF.deleteWide ([] : CNF V) k = [] := by
  simp [deleteWide]

@[simp] theorem deleteWide_cons (C : Clause V) (H : CNF V) (k : ℕ) :
    CNF.deleteWide (C :: H) k =
      if C.width ≤ k then C :: H.deleteWide k else H.deleteWide k := by
  by_cases hk : C.width ≤ k <;> simp [deleteWide, hk]

theorem deleteWide_widthAtMost (H : CNF V) (k : ℕ) :
    (H.deleteWide k).WidthAtMost k := by
  intro C hC
  exact (mem_deleteWide.mp hC).2

theorem deleteWide_normalized (H : CNF V) (hH : H.Normalized) (k : ℕ) :
    (H.deleteWide k).Normalized := by
  intro C hC
  exact hH C (mem_deleteWide.mp hC).1

theorem deleteWide_length_le (H : CNF V) (k : ℕ) :
    (H.deleteWide k).length ≤ H.length := by
  induction H with
  | nil => simp
  | cons C H ih =>
    rw [deleteWide_cons]
    by_cases hk : C.width ≤ k
    · simpa only [ite_eq_left hk, List.length_cons] using Nat.succ_le_succ ih
    · simpa only [ite_eq_right hk, List.length_cons] using ih.trans (Nat.le_succ H.length)

theorem eval_deleteWide_of_eval (H : CNF V) (k : ℕ) {x : Cube V}
    (hx : H.eval x = true) : (H.deleteWide k).eval x = true := by
  apply eval_antitone (J := H) ?_ hx
  intro C hC
  exact (mem_deleteWide.mp hC).1

theorem indicator_eval_le_deleteWide (H : CNF V) (k : ℕ) (x : Cube V) :
    indicator (H.eval x) ≤ indicator ((H.deleteWide k).eval x) := by
  cases hx : H.eval x
  · simpa only [hx, indicator_false] using indicator_nonneg ((H.deleteWide k).eval x)
  · have hd := eval_deleteWide_of_eval H k hx
    simp [hd]

theorem deletion_error_cons_le (C : Clause V) (H : CNF V) (k : ℕ) (x : Cube V) :
    indicator (CNF.eval (CNF.deleteWide (C :: H) k) x) - indicator (CNF.eval (C :: H) x) ≤
      (indicator ((H.deleteWide k).eval x) - indicator (H.eval x)) +
        if C.width ≤ k then 0 else 1 - indicator (C.eval x) := by
  have hm := indicator_eval_le_deleteWide H k x
  by_cases hk : C.width ≤ k
  · cases hc : C.eval x <;> cases hh : H.eval x <;>
      cases hd : (H.deleteWide k).eval x <;>
      norm_num [deleteWide_cons, hk, eval_cons, hc, hh, hd, indicator] at hm <;>
        norm_num [deleteWide_cons, hk, eval_cons, hc, hh, hd, indicator]
  · cases hc : C.eval x <;> cases hh : H.eval x <;>
      cases hd : (H.deleteWide k).eval x <;>
      norm_num [deleteWide_cons, hk, eval_cons, hc, hh, hd, indicator] at hm <;>
        norm_num [deleteWide_cons, hk, eval_cons, hc, hh, hd, indicator]

theorem deletion_error_bound [Fintype V] (H : CNF V) (hH : H.Normalized) (k : ℕ) :
    finiteAvg (fun x : Cube V =>
      indicator ((H.deleteWide k).eval x) - indicator (H.eval x)) ≤
      (H.length : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  revert hH
  induction H with
  | nil =>
    intro _
    simp
  | cons C H ih =>
    intro hH
    have hC : C.Normalized := hH C (by simp)
    have htail : CNF.Normalized H := fun D hD => hH D (by simp [hD])
    have hclause : finiteAvg (fun x : Cube V =>
        if C.width ≤ k then 0 else 1 - indicator (C.eval x)) ≤
        ((2 : ℝ) ^ k)⁻¹ := by
      by_cases hk : C.width ≤ k
      · simp only [ite_eq_left hk, finiteAvg_zero]
        exact inv_nonneg.mpr (pow_nonneg (by norm_num) k)
      · simp only [ite_eq_right hk]
        rw [Clause.false_probability C hC]
        have hkw : k ≤ C.width := Nat.le_of_lt (Nat.lt_of_not_ge hk)
        have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ C.width :=
          pow_le_pow_right₀ (by norm_num) hkw
        simpa only [one_div] using
          one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) k) hpow
    calc
      _ ≤ finiteAvg (fun x : Cube V =>
          (indicator (CNF.eval (CNF.deleteWide H k) x) - indicator (CNF.eval H x)) +
            if C.width ≤ k then 0 else 1 - indicator (C.eval x)) :=
        finiteAvg_mono (deletion_error_cons_le C H k)
      _ = finiteAvg (fun x : Cube V =>
          indicator (CNF.eval (CNF.deleteWide H k) x) - indicator (CNF.eval H x)) +
          finiteAvg (fun x : Cube V =>
            if C.width ≤ k then 0 else 1 - indicator (C.eval x)) :=
        finiteAvg_add _ _
      _ ≤ (H.length : ℝ) * ((2 : ℝ) ^ k)⁻¹ + ((2 : ℝ) ^ k)⁻¹ :=
        add_le_add (ih htail) hclause
      _ = ((C :: H).length : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

end CNF

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


noncomputable section
open scoped BigOperators

open scoped Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [instFintypeV : Fintype V]

namespace CNF

theorem mass_le_of_width_correlation (H : CNF V) (hH : H.Normalized)
    (f : Cube V → Bool) (hsupport : ∀ x, H.eval x = true → f x = true)
    (k : ℕ) (ε : ℝ)
    (hcorr : ∀ J : CNF V, J.WidthAtMost k →
      |finiteAvg (fun x : Cube V => sign (f x) * indicator (J.eval x))| ≤ ε) :
    finiteAvg (fun x : Cube V => indicator (H.eval x)) ≤
      ε + (H.length : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  let J := H.deleteWide k
  have hpoint (x : Cube V) : indicator (H.eval x) ≤
      sign (f x) * indicator (J.eval x) +
        (indicator (J.eval x) - indicator (H.eval x)) := by
    have hm := H.indicator_eval_le_deleteWide k x
    have hs := hsupport x
    change indicator (H.eval x) ≤ indicator (J.eval x) at hm
    cases hh : H.eval x <;> cases hj : J.eval x <;> cases hf : f x <;>
      simp_all [indicator, sign]
  calc
    _ ≤ finiteAvg (fun x : Cube V => sign (f x) * indicator (J.eval x) +
        (indicator (J.eval x) - indicator (H.eval x))) := finiteAvg_mono hpoint
    _ = finiteAvg (fun x : Cube V => sign (f x) * indicator (J.eval x)) +
        finiteAvg (fun x : Cube V => indicator (J.eval x) - indicator (H.eval x)) :=
      finiteAvg_add _ _
    _ ≤ |finiteAvg (fun x : Cube V => sign (f x) * indicator (J.eval x))| +
        finiteAvg (fun x : Cube V => indicator (J.eval x) - indicator (H.eval x)) :=
      add_le_add_left (le_abs_self _) _
    _ ≤ ε + (H.length : ℝ) * ((2 : ℝ) ^ k)⁻¹ :=
      add_le_add (hcorr J (H.deleteWide_widthAtMost k)) (H.deletion_error_bound hH k)

end CNF

namespace Circuit3

theorem indicator_output_le_sum_middle
    {V : Type uDepth1}
    [Fintype V]
    (C : Circuit3 V) (x : Cube V) :
    indicator (C.eval x) ≤ ∑ j ∈ C.top, indicator ((C.middleCNF j).eval x) := by
  classical
  cases h : C.eval x with
  | false =>
    simpa using Finset.sum_nonneg (fun j (_ : j ∈ C.top) =>
      indicator_nonneg ((C.middleCNF j).eval x))
  | true =>
    obtain ⟨j, hj, hx⟩ := (C.eval_eq_true_iff_middleCNF x).mp h
    have hb := Finset.single_le_sum
      (fun i (_ : i ∈ C.top) => indicator_nonneg ((C.middleCNF i).eval x)) hj
    simpa [hx] using hb

theorem acceptance_density_le (C : Circuit3 V) (f : Cube V → Bool)
    (hC : C.Computes f) (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hcorr : ∀ H : CNF V, H.WidthAtMost k →
      |finiteAvg (fun x : Cube V => sign (f x) * indicator (H.eval x))| ≤ ε) :
    finiteAvg (fun x : Cube V => indicator (f x)) ≤
      (C.gateCount : ℝ) * ε + (C.gateCount : ℝ) ^ 2 * ((2 : ℝ) ^ k)⁻¹ := by
  classical
  let q : ℝ := ((2 : ℝ) ^ k)⁻¹
  have hq : 0 ≤ q := inv_nonneg.mpr (pow_nonneg (by norm_num) _)
  have hm (j : Fin C.middleCount) (hj : j ∈ C.top) :
      finiteAvg (fun x : Cube V => indicator ((C.middleCNF j).eval x)) ≤
        ε + (C.gateCount : ℝ) * q := by
    have hs (x : Cube V) (hx : (C.middleCNF j).eval x = true) : f x = true := by
      rw [← hC x]
      exact C.middleCNF_implies_output hj hx
    have hfirst := (C.middleCNF j).mass_le_of_width_correlation
      (C.middleCNF_normalized j) f hs k ε hcorr
    refine hfirst.trans (add_le_add_right (mul_le_mul_of_nonneg_right ?_ hq) ε)
    exact_mod_cast C.middleCNF_length_le_gateCount j
  have hB : 0 ≤ ε + (C.gateCount : ℝ) * q :=
    add_nonneg hε (mul_nonneg (Nat.cast_nonneg _) hq)
  calc
    _ = finiteAvg (fun x : Cube V => indicator (C.eval x)) :=
      finiteAvg_congr (fun x => congrArg indicator (hC x).symm)
    _ ≤ finiteAvg (fun x : Cube V =>
        ∑ j ∈ C.top, indicator ((C.middleCNF j).eval x)) :=
      finiteAvg_mono (C.indicator_output_le_sum_middle)
    _ = ∑ j ∈ C.top, finiteAvg (fun x : Cube V =>
        indicator ((C.middleCNF j).eval x)) := finiteAvg_sum _ _
    _ ≤ ∑ j ∈ C.top, (ε + (C.gateCount : ℝ) * q) :=
      Finset.sum_le_sum hm
    _ = (C.top.card : ℝ) * (ε + (C.gateCount : ℝ) * q) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C.gateCount : ℝ) * (ε + (C.gateCount : ℝ) * q) := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast C.top_card_le_gateCount
    _ = _ := by dsimp [q]; ring

end Circuit3

end DepthThreeLowerBound

end

end OAI
end
end

section
section
namespace OAI


open scoped Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V]

theorem sign_eq_two_indicator_sub_one (b : Bool) :
    sign b = 2 * indicator b - 1 := by
  cases b <;> norm_num [sign, indicator]

theorem finiteAvg_sign (f : Cube V → Bool) :
    finiteAvg (fun x => sign (f x)) =
      2 * finiteAvg (fun x => indicator (f x)) - 1 := by
  calc
    _ = finiteAvg (fun x => 2 * indicator (f x) - 1) :=
      finiteAvg_congr (fun x => sign_eq_two_indicator_sub_one (f x))
    _ = _ := by rw [finiteAvg_sub, finiteAvg_const_mul, finiteAvg_const]

theorem acceptance_density_lower_of_sign_bound (f : Cube V → Bool) (ε : ℝ)
    (h : |finiteAvg (fun x => sign (f x))| ≤ ε) :
    (1 - ε) / 2 ≤ finiteAvg (fun x => indicator (f x)) := by
  have hl := (abs_le.mp h).1
  rw [finiteAvg_sign] at hl
  linarith

theorem acceptance_density_lower_of_width_correlation (f : Cube V → Bool)
    (k : ℕ) (ε : ℝ)
    (h : ∀ H : CNF V, H.WidthAtMost k →
      |finiteAvg (fun x : Cube V => sign (f x) * indicator (H.eval x))| ≤ ε) :
    (1 - ε) / 2 ≤ finiteAvg (fun x => indicator (f x)) := by
  apply acceptance_density_lower_of_sign_bound
  have he := h [] (by intro C hC; simp at hC)
  simpa using he

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

theorem circuit_lower_bound_of_small_cnf_correlations
    (d k : ℕ) (s : ℝ) (hs : 0 ≤ s) (hd : 4 ≤ d)
    (hk : 3 * (s + 1) * Real.sqrt (d : ℝ) ≤ (k : ℝ))
    (f : Cube (Fin d) → Bool)
    (hcorr : ∀ H : CNF (Fin d), H.WidthAtMost k →
      |finiteAvg (fun x : Cube (Fin d) => sign (f x) * indicator (H.eval x))| ≤
        6 * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt (d : ℝ)) / 16))
    (C : Circuit3 (Fin d)) (hC : C.Computes f) :
    (2 : ℝ) ^ (s * Real.sqrt (d : ℝ)) < (C.gateCount : ℝ) := by
  by_contra h
  have hsize : (C.gateCount : ℝ) ≤ (2 : ℝ) ^ (s * Real.sqrt (d : ℝ)) :=
    le_of_not_gt h
  let ε : ℝ := 6 * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt (d : ℝ)) / 16)
  have hε : 0 ≤ ε := mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  have hdReal : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hexponent : -(64 * (s + 1) * Real.sqrt (d : ℝ)) / 16 =
      -(4 * (s + 1) * Real.sqrt (d : ℝ)) := by ring
  have hsmall : ε ≤ 3 / 8 := by
    dsimp only [ε]
    rw [hexponent]
    exact correlation_error_le s (d : ℝ) hs (by linarith)
  have hlower : (1 - ε) / 2 ≤
      finiteAvg (fun x : Cube (Fin d) => indicator (f x)) := by
    convert acceptance_density_lower_of_width_correlation f k ε
      (fun H hH => by convert hcorr H hH)
  have hupper : finiteAvg (fun x : Cube (Fin d) => indicator (f x)) ≤
      (C.gateCount : ℝ) * ε + (C.gateCount : ℝ) ^ 2 * ((2 : ℝ) ^ k)⁻¹ := by
    convert C.acceptance_density_le f hC k ε hε
      (fun H hH => by convert hcorr H hH)
  have hinverse : (2 : ℝ) ^ (-(k : ℝ)) = ((2 : ℝ) ^ k)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hfinal := final_error_le s (d : ℝ) (C.gateCount : ℝ) hs hdReal
    (Nat.cast_nonneg _) hsize k hk
  have hupper' : finiteAvg (fun x : Cube (Fin d) => indicator (f x)) ≤ 5 / 128 := by
    calc
      _ ≤ (C.gateCount : ℝ) * ε + (C.gateCount : ℝ) ^ 2 * ((2 : ℝ) ^ k)⁻¹ := hupper
      _ = 6 * (C.gateCount : ℝ) *
          (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt (d : ℝ)) / 16) +
          (C.gateCount : ℝ) ^ 2 * (2 : ℝ) ^ (-(k : ℝ)) := by
        rw [hinverse]
        dsimp only [ε]
        ring
      _ ≤ 5 / 128 := hfinal
  linarith

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

theorem language_depth_three_gate_lower_bound (A : ℝ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : Circuit3 (Fin n),
      C.Computes (fun x => language (List.ofFn x)) →
      (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) < (C.gateCount : ℝ) := by
  have hs : 0 ≤ 3 * A := mul_nonneg (by norm_num) hA.le
  obtain ⟨N, hN, hslice⟩ := exists_language_slice_small_correlations (3 * A) hs
  refine ⟨N, ?_⟩
  intro n hn C hC
  have hnlarge : 20480 ≤ n := hN.trans hn
  have hd : 4 ≤ dataDimension n := by
    unfold dataDimension
    omega
  obtain ⟨α, hα⟩ := hslice n hn
  have hrestricted := circuit_lower_bound_of_small_cnf_correlations
    (dataDimension n) (degreeCutoff (3 * A) (dataDimension n))
    (3 * A) hs hd (degreeCutoff_lower (3 * A) (dataDimension n))
    (fun x => language (List.ofFn (GateInput.assignment α x))) hα
    (C.subst α) (C.computes_subst hC α)
  have hdata : (2 : ℝ) ^ ((3 * A) * Real.sqrt (dataDimension n : ℝ)) <
      (C.gateCount : ℝ) := by
    simpa only [Circuit3.gateCount_subst] using hrestricted
  exact (circuit_size_scale A hA.le n (by omega)).trans_lt hdata

end DepthThreeLowerBound

end OAI
end
end

section
section
namespace OAI

namespace DepthThreeLowerBound

theorem exists_polynomial_time_language_depth_three_lower_bound_oai :
    ∃ (L : List Bool → Bool) (M : FiniteMultiTapeMachine) (C a : ℕ),
      0 < C ∧ 0 < a ∧
      (∀ w : List Bool, MultiTapeHaltsIn M w (L w) (C * (w.length + 1) ^ a)) ∧
      ∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ D : Circuit3 (Fin n), D.Computes (fun x => L (List.ofFn x)) →
          (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) < (D.gateCount : ℝ) := by
  obtain ⟨M, C, a, hC, ha, hM⟩ := language_polynomial_time
  exact ⟨language, M, C, a, hC, ha, hM, language_depth_three_gate_lower_bound⟩

end DepthThreeLowerBound

end OAI
end
end

theorem solution : type_of% @OAI.DepthThreeLowerBound.exists_polynomial_time_language_depth_three_lower_bound_oai := @OAI.DepthThreeLowerBound.exists_polynomial_time_language_depth_three_lower_bound_oai
