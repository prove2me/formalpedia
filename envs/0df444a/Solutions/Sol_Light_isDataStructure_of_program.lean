-- Prove2me | solution 1 for Light.isDataStructure_of_program
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:29.422116+00:00
-- url     : https://prove2.me/submissions/3ae0a8d5-a646-4e87-b5ee-6e023b33f248

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Size
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Theorems.Thm_Light_fits_of_small
import Theorems.Thm_Light_ramSteps_le
import Theorems.Thm_Light_input_loadWords
import Theorems.Thm_Light_Compiler_compileProgram_correct
import Definitions.Def_WeightedCache3SUM_Alias_e0bdc711e9667f3c
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
import Theorems.Thm_ThreeSumApsp_WordRam_exec_mono
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil


section
open ThreeSumApsp.WordRam
namespace Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
private theorem ramSteps_mono (P : Program) (dec : Bool) {c c' : ℕ} (h : c ≤ c') :
    ramSteps P dec c ≤ ramSteps P dec c' :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _
private theorem ramSteps_le_of_le (P : Program) (dec : Bool) {c : ℕ} {T : ℝ} (h : (c : ℝ) ≤ T) :
    (ramSteps P dec c : ℝ) ≤ (timeConst P dec : ℝ) * T + timeConst P dec :=
  (ramSteps_le P dec c).trans (by gcongr)
private theorem lowCell_le (P : Program) (dec : Bool) (lim : Limits) :
    lowCell P dec lim ≤ timeConst P dec * lim.depth + timeConst P dec := by
  have hconst : lowCell P dec ⟨0, 0, 0⟩ ≤ timeConst P dec := by unfold timeConst; omega
  -- before any call the stack has 4 + (F + 1) cells; each level of calls adds F + 1
  have hstack₀ : 2 * (4 + (frameSize P + 1) * (0 + 1)) ≤ lowCell P dec ⟨0, 0, 0⟩ := le_max_left _ _
  have hstack : 2 * stackCells P lim
      = 2 * (frameSize P + 1) * lim.depth + 2 * (4 + (frameSize P + 1)) := by
    unfold stackCells mainFrame; ring
  have hframes : 2 * (frameSize P + 1) * lim.depth ≤ timeConst P dec * lim.depth :=
    Nat.mul_le_mul_right _ (by omega)
  -- the pool does not depend on the limits
  have hpool : 25 + 4 * dispPos P dec ≤ lowCell P dec ⟨0, 0, 0⟩ := le_max_right _ _
  exact max_le (by omega) (by omega)
private theorem far_of_space {P : Program} {dec : Bool} {lim : Limits} {len : ℕ} {S : ℝ} {a : ℤ}
    (hspace : (lim.space : ℝ) ≤ len + S) (hdepth : (lim.depth : ℝ) ≤ S)
    (ha : (a : ℝ) < -((timeConst P dec : ℝ) * S + timeConst P dec) ∨
      (len : ℝ) + ((timeConst P dec : ℝ) * S + timeConst P dec) < (a : ℝ)) :
    a < -(lowCell P dec lim : ℤ) ∨ (lim.space : ℤ) ≤ a := by
  have hS : 0 ≤ S := le_trans (by positivity) hdepth
  refine ha.imp (fun ha => ?_) fun ha => ?_
  · have hlow : (lowCell P dec lim : ℝ) ≤ (timeConst P dec : ℝ) * lim.depth + timeConst P dec := by
      exact_mod_cast lowCell_le P dec lim
    have : (a : ℝ) < -(lowCell P dec lim : ℝ) :=
      ha.trans_le (neg_le_neg (hlow.trans (by gcongr)))
    exact_mod_cast this
  · have h1 : (1 : ℝ) ≤ timeConst P dec := by
      exact_mod_cast (by unfold timeConst startCost; omega)
    -- space ≤ len + S ≤ len + (C S + C) < a
    have hCS : S ≤ (timeConst P dec : ℝ) * S := le_mul_of_one_le_left hS h1
    have : (lim.space : ℝ) ≤ (a : ℝ) := by linarith
    exact_mod_cast this
section run
variable {W : ℕ} {lim : Limits} {μ : ℕ → ℤ}
end run
private theorem Compiler.Holds.withQuery {W : ℕ} {lim : Limits} {μ : ℕ → ℤ} {c : ℤ → BitVec W}
    (h : Holds W lim μ c) {I J : ℕ} (hI : (I : ℤ) ≤ lim.word) (hJ : (J : ℤ) ≤ lim.word) :
    Input lim μ I J (withQuery c cARG1 cARG2 I J) where
  rep a := by
    simp only [WordRam.withQuery, cARG1, cARG2, show (a : ℤ) ≠ -1 by omega,
      show (a : ℤ) ≠ -2 by omega, if_false]
    exact h.rep a
  bounded := h.bounded
  arg1 := by simp [WordRam.withQuery, cARG1]
  arg2 := by simp [WordRam.withQuery, cARG1, cARG2]
  arg1_le := by rwa [abs_of_nonneg (by positivity)]
  arg2_le := by rwa [abs_of_nonneg (by positivity)]
private theorem serves_of_program {W : ℕ} {lim : Limits} {P : Program} {pQ : ℕ} {x : ThinPair}
    {DS : (ℕ → ℤ) → Prop} {T : ℝ} (hfit : Fits W lim (dispPos P false) (stackCells P lim))
    (hN : (x.N : ℤ) ≤ lim.word) (hq : AnswersQueries lim P pQ x T DS) :
    ∀ (qs : List (ℕ × ℕ)) (c : ℤ → BitVec W) (μ : ℕ → ℤ), DS μ → Holds W lim μ c →
      (∀ q ∈ qs, q.1 < x.N ∧ q.2 < x.N) →
      Serves (compileProgram P pQ false) cARG1 cARG2 cRESULT (ramSteps P false ⌊T⌋₊)
        (fun I J => if h : I < x.N ∧ J < x.N then (x.X * x.Y) ⟨I, h.1⟩ ⟨J, h.2⟩ else 0) c qs
  | [], _, _, _, _, _ => trivial
  | q :: rest, c, μ, hDS, hc, hqs => by
    obtain ⟨hI, hJ⟩ := hqs q (by simp)
    obtain ⟨σ', n, hex, hn, hval, hDS'⟩ := hq μ hDS ⟨q.1, hI⟩ ⟨q.2, hJ⟩
    obtain ⟨c', hrun, out⟩ := compileProgram_correct (dec := false) hex hfit
      (hc.withQuery (by omega) (by omega))
    refine ⟨c', exec_mono (c := ⟨0, _⟩) hrun (ramSteps_mono P false (Nat.le_floor hn)), ?_,
      serves_of_program hfit hN hq rest c' σ'.mem hDS' out.holds
        fun q' hq' => hqs q' (by simp [hq'])⟩
    rw [out.result, hval]
    simp only [hI, hJ, and_self, dite_true]
end Light
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
namespace Light
theorem _root_.solution {P : Program} {pPre pQ s k : ℕ} {extra : List ℤ}
    {dom : ThinPair → Prop} {Tp Sp Tq : ThinPair → ℝ}
    (h : ProgramIsDataStructure P pPre pQ s k extra dom Tp Sp Tq) :
    IsDataStructure (compileProgram P pPre false) (compileProgram P pQ false) cARG1 cARG2 cRESULT
      (slopeOf P false s k 2) extra dom
      (fun x => (timeConst P false : ℝ) * Tp x + timeConst P false)
      (fun x => (timeConst P false : ℝ) * Sp x + timeConst P false)
      (fun x => (timeConst P false : ℝ) * Tq x + timeConst P false) := by
  intro x hx W hadm
  obtain ⟨lim, DS, h⟩ := h x hx
  obtain ⟨σ₁, c₁, hex₁, hc₁, hDS₁⟩ := h.pre
  have hfit := fits_of_small P false h.small hadm (by simp) le_rfl
  obtain ⟨cfg, hrun, out⟩ :=
    compileProgram_correct hex₁ hfit (input_loadWords W h.small.nonneg h.input_fits)
  exact ⟨_, _, cfg, ramSteps_le_of_le P false hc₁,
    ramSteps_le_of_le P false (Nat.floor_le h.time_nonneg), hrun,
    fun a ha => out.far a (far_of_space h.space h.depth ha),
    fun qs hqs => serves_of_program hfit h.index_fits h.query qs cfg σ₁.mem hDS₁ out.holds hqs⟩
end Light
