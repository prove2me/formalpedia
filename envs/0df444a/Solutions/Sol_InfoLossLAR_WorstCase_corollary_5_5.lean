-- Prove2me | solution 1 for InfoLossLAR.WorstCase.corollary_5_5
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T23:29:25.40811+00:00
-- url     : https://prove2.me/submissions/f0196c0e-cc77-4d4b-abbd-ffc0b5113fd2

import Theorems.Thm_InfoLossLAR_WorstCase_theorem_4_2
import Theorems.Thm_InfoLossLAR_WorstCase_theorem_5_4
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_02
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_05
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_08
import Definitions.Def_InfoLossLAR_RuntimeBundle_01
import Definitions.Def_InfoLossLAR_RuntimeBundle_02
import Definitions.Def_InfoLossLAR_RuntimeBundle_03
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_Family
import Definitions.Def_InfoLossLAR_WorstCase_FixedT
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Mathlib
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Vector.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.Hom.Set
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic

set_option linter.all false

namespace AFT.RationalNumerics
end AFT.RationalNumerics

namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase

namespace Integration9_9
end Integration9_9

namespace Integration9_9.LARPlatformEncoding
end Integration9_9.LARPlatformEncoding

namespace Integration9_9.LARRankOneMachine
end Integration9_9.LARRankOneMachine

namespace Integration9_9.TM2OutputLength
end Integration9_9.TM2OutputLength

namespace Integration9_9.TM2PlatformSerialization
end Integration9_9.TM2PlatformSerialization

namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

namespace OAI.MetricKMedian.Binary.Automatic.Poly
end OAI.MetricKMedian.Binary.Automatic.Poly

namespace QMCNumericRuntime
end QMCNumericRuntime

/- Helper module Solutions.AdvantageBridgeArithmetic. -/
section P2MDyadicModule0

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- A natural-coefficient polynomial is bounded by its coefficient mass times its largest power. -/
theorem polynomial_eval_le_monomial (p : Polynomial ℕ) (n : ℕ) (hn : 1 ≤ n) :
    p.eval n ≤ p.eval 1 * n ^ p.natDegree := by
  calc
    p.eval n = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * n ^ i :=
      p.eval_eq_sum_range n
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * n ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _
        (pow_le_pow_right' hn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    _ = p.eval 1 * n ^ p.natDegree := by
      rw [← Finset.sum_mul]
      congr 1
      simpa using (p.eval_eq_sum_range 1).symm

/-- All multiplicative constants in a natural polynomial bound can be absorbed in one power. -/
theorem polyBoundedFn_eventually_le_power (f : ℕ → ℕ) (hf : PolyBoundedFn f) :
    ∃ k n₀ : ℕ, ∀ n ≥ n₀, f n ≤ n ^ k := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨p.natDegree + 1, max 1 (p.eval 1), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hcoef : p.eval 1 ≤ n := le_trans (le_max_right _ _) hn
  calc
    f n ≤ p.eval n := hp n
    _ ≤ p.eval 1 * n ^ p.natDegree := polynomial_eval_le_monomial p n hn1
    _ ≤ n * n ^ p.natDegree := Nat.mul_le_mul_right _ hcoef
    _ = n ^ (p.natDegree + 1) := by rw [pow_succ]; ac_rfl

end InfoLossLAR.WorstCase

end P2MDyadicModule0

/- Helper module Asymptotics. -/
section P2MDyadicModule1

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.GeneralBounds

open QAlgorithms.Complexity

open scoped Classical

theorem product_error {p k n : ℕ} (hn : 0 < n) (x : ℝ) (hx : x ≤ (n:ℝ)^p) :
    x * (n:ℝ)^(-((p+k : ℕ):ℝ)) ≤ (n:ℝ)^(-(k:ℝ)) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (n:ℝ)^p * (n:ℝ)^(-((p+k : ℕ):ℝ)) := mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hn'.le _)
    _ = _ := by
      rw [←Real.rpow_natCast (n:ℝ) p, ← Real.rpow_add hn']
      congr 1
      push_cast
      ring

theorem two_errors (k : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (n:ℝ)^(-((k+1:ℕ):ℝ)) + (n:ℝ)^(-((k+1:ℕ):ℝ)) ≤ (n:ℝ)^(-(k:ℝ)) := by
  calc
    _ = (2:ℝ) * (n:ℝ)^(-((k+1:ℕ):ℝ)) := by ring
    _ ≤ _ := by
      simpa only [pow_one,Nat.add_comm 1 k] using
        (product_error (p:=1) (k:=k) (n:=n) (by omega) 2 (by simpa using (show (2:ℝ) ≤ n by exact_mod_cast hn)))

theorem of_integers (f : ℕ → ℝ) (hzero : ∀ n, 0 ≤ f n)
    (h : ∀ k : ℕ, 1 ≤ k → ∃ cut, ∀ n ≥ cut, f n ≤ (n:ℝ)^(-(k:ℝ))) :
    Negligible f := by
  refine ⟨hzero,?_⟩
  intro c hc
  let k := ⌈c⌉₊ + 1
  obtain ⟨cut,hcut⟩ := h k (by simp [k])
  refine ⟨max 1 cut,?_⟩
  intro n hn
  apply (hcut n (by omega)).trans
  have hc' := Nat.le_ceil c
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega))
  dsimp [k]
  push_cast
  linarith

end InfoLossLAR.WorstCase.GeneralBounds

end P2MDyadicModule1

/- Helper module FiniteWork. -/
section P2MDyadicModule2

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace StockFinite

open Turing StateTransition Function

noncomputable section

variable {K Λ σ : Type} {Γ : K → Type} [Fintype σ] [DecidableEq K]

def writes : TM2.Stmt Γ Λ σ → Finset (Sigma Γ)
  | .push k f q => (Finset.univ.image fun v : σ => Sigma.mk k (f v)) ∪ writes q
  | .peek _ _ q | .pop _ _ q | .load _ q => writes q
  | .branch _ a b => writes a ∪ writes b
  | .goto _ | .halt => ∅

abbrev Letter (bound : Finset (Sigma Γ)) (k : K) := { x : Γ k // Sigma.mk k x ∈ bound }

instance finiteLetter (bound : Finset (Sigma Γ)) (k : K) : Fintype (Letter bound k) :=
  Fintype.ofInjective (fun a => (⟨Sigma.mk k a.val,a.property⟩ : ↥bound)) (by
    intro a b h
    apply Subtype.ext
    simpa using congrArg Subtype.val h)

def restrictStmt (bound : Finset (Sigma Γ)) :
    (q : TM2.Stmt Γ Λ σ) → writes q ⊆ bound → TM2.Stmt (Letter bound) Λ σ
  | .push k f q, h => .push k (fun v => ⟨f v,h (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩))⟩)
      (restrictStmt bound q (fun _ hx => h (Finset.mem_union_right _ hx)))
  | .peek k f q,h => .peek k (fun v x => f v (x.map Subtype.val)) (restrictStmt bound q h)
  | .pop k f q,h => .pop k (fun v x => f v (x.map Subtype.val)) (restrictStmt bound q h)
  | .load f q,h => .load f (restrictStmt bound q h)
  | .branch f a b,h => .branch f (restrictStmt bound a (fun _ hx => h (Finset.mem_union_left _ hx)))
      (restrictStmt bound b (fun _ hx => h (Finset.mem_union_right _ hx)))
  | .goto f,_ => .goto f
  | .halt,_ => .halt

def forget {bound : Finset (Sigma Γ)} (S : (k : K) → List (Letter bound k)) : (k : K) → List (Γ k) :=
  fun k => (S k).map Subtype.val

theorem forget_update {bound : Finset (Sigma Γ)} (S : (k : K) → List (Letter bound k))
    (k : K) (xs : List (Letter bound k)) :
    forget (update S k xs) = update (forget S) k (xs.map Subtype.val) := by
  funext j
  by_cases he : j=k
  · subst j
    simp [forget]
  · simp [forget,he]

def forgetCfg {bound : Finset (Sigma Γ)} (c : TM2.Cfg (Letter bound) Λ σ) : TM2.Cfg Γ Λ σ :=
  ⟨c.l,c.var,forget c.stk⟩

theorem restrictAux (bound : Finset (Sigma Γ)) (q : TM2.Stmt Γ Λ σ) (h : writes q ⊆ bound)
    (v : σ) (S : (k : K) → List (Letter bound k)) :
    forgetCfg (TM2.stepAux (restrictStmt bound q h) v S) = TM2.stepAux q v (forget S) := by
  induction q generalizing v S with
  | push k f q ih => rw [restrictStmt,TM2.stepAux,ih,forget_update]; rfl
  | peek k f q ih =>
    change writes q ⊆ bound at h
    simpa only [restrictStmt,TM2.stepAux,forget,List.head?_map] using
      ih h (f v ((S k).head?.map Subtype.val)) S
  | pop k f q ih =>
    change writes q ⊆ bound at h
    simpa only [restrictStmt,TM2.stepAux,forget_update,forget,List.head?_map,List.map_tail] using
      ih h (f v ((S k).head?.map Subtype.val)) (update S k (S k).tail)
  | load f q ih => exact ih h (f v) S
  | branch f a b ia ib => cases hf : f v <;> simp [restrictStmt,TM2.stepAux,hf,ia,ib]
  | goto f => rfl
  | halt => rfl

end

end StockFinite

end P2MDyadicModule2

/- Helper module Integration9_9.TM2PlatformSerialization. -/
section P2MDyadicModule3

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2PlatformSerialization

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open QAlgorithms.Complexity

open Polynomial

/-- A concrete Boolean-list program is a platform string-time certificate. -/
theorem polyTime_of_poly {f : Str → Str} (h : Poly f) : PolyTimeComputable f := by
  let P := (BooleanLists.packProgram.comp h.program).comp BooleanLists.unpackProgram
  exact ⟨(P.congr f (fun _ => rfl)).stock⟩

section RepeatedParser

variable {α : Type} [Coding α] [Inhabited α]

variable (read : Str → Str × α)

end RepeatedParser

end Integration9_9.TM2PlatformSerialization

end P2MDyadicModule3

/- Helper module Integration9_9.FairBitPadding. -/
section P2MDyadicModule4

set_option autoImplicit false

namespace Integration9_9.FairBitPadding

open InfoLossLAR.WorstCase

/-- Relabeling a finite uniform source by a bijection preserves every average. -/
theorem avg_equiv {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : avg (fun a => f (e a)) = avg f := by
  unfold avg
  rw [e.sum_comp, Fintype.card_congr e]

/-- Unused independent randomness has no effect on a finite average. -/
theorem avg_fst {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → ℝ) : avg (fun p : α × β => f p.1) = avg f := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [avg, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul, ← Finset.mul_sum]
  field_simp

/-- Padding a fair-bit tape by a fixed number of unused bits preserves its law. -/
theorem avg_prefix_add (n extra : ℕ) (f : (Fin n → Bool) → ℝ) :
    avg (fun tape : Fin (n+extra) → Bool => f (fun i => tape (Fin.castAdd extra i))) = avg f := by
  calc
    _ = avg (fun tape => (fun p : (Fin n → Bool) × (Fin extra → Bool) => f p.1)
          (splitEquiv n extra tape)) := rfl
    _ = avg (fun p : (Fin n → Bool) × (Fin extra → Bool) => f p.1) :=
      avg_equiv (splitEquiv n extra) (fun p => f p.1)
    _ = avg f := avg_fst f

/-- Any upper bound on the required random tape can be used as an exact tape length. -/
theorem avg_prefix {n m : ℕ} (h : n ≤ m) (f : (Fin n → Bool) → ℝ) :
    avg (fun tape : Fin m → Bool => f (fun i => tape (Fin.castLE h i))) = avg f := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa only [Fin.castLE, Fin.castAdd] using avg_prefix_add n extra f

end Integration9_9.FairBitPadding

end P2MDyadicModule4

/- Helper module Solutions.AdvantageBridgeCoinLayout. -/
section P2MDyadicModule5

set_option autoImplicit false

set_option maxHeartbeats 300000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase QAlgorithms.Complexity Function Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime LARPlatformEncoding LARRankOneMachine TM2PlatformSerialization

/-- The genuine coin-first input length is strictly increasing, even when
some coefficients of the fixed polynomial coin budget vanish. -/
theorem coinTotalLength_strictMono (budget : Polynomial ℕ) :
    StrictMono (fun n => budget.eval n+n) := by
  intro a b hab
  have hm := polynomial_eval_mono budget hab.le
  change budget.eval a+a<budget.eval b+b
  omega

theorem coinBaseLength_eq (budget : Polynomial ℕ) (coins input : Str)
    (hc : coins.length=budget.eval input.length) :
    coinBaseLength budget (coins++input)=input.length := by
  let candidates := (List.range ((coins++input).length+1)).filter
    (fun index => decide (budget.eval index+index=(coins++input).length))
  have hn : input.length∈candidates := by
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_range.mpr
      simp only [List.length_append,hc]
      omega
    · simp only [List.length_append,hc,decide_true]
  have hall : ∀ index∈candidates,index=input.length := by
    intro index hi
    have he := (List.mem_filter.mp hi).2
    have heq : budget.eval index+index=budget.eval input.length+input.length := by
      simpa only [decide_eq_true_eq,List.length_append,hc] using he
    exact (coinTotalLength_strictMono budget).injective heq
  cases h : candidates with
  | nil => simp [h] at hn
  | cons first rest =>
    have hf : first=input.length := hall first (by simp [h])
    change (candidates.head?).getD 0=input.length
    simp [h,hf]

theorem coinFirstPair_eq (budget : Polynomial ℕ) (coins input : Str)
    (hc : coins.length=budget.eval input.length) :
    coinFirstPair budget (coins++input)=encPair coins input := by
  unfold coinFirstPair
  rw [coinBaseLength_eq budget coins input hc,←hc]
  dsimp only
  rw [List.take_left,List.drop_left]

end Integration9_9.LARCoinLayout

end P2MDyadicModule5

/- Helper module Solutions.AdvantageBridgeNativeBlockAverage. -/
section P2MDyadicModule6

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.GenericBodySemantics

open InfoLossLAR.WorstCase QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

/-- The average on two independent finite sources is its exact nested average. -/
theorem avg_product {First Second : Type} [Fintype First] [Fintype Second]
    (test : First × Second → ℝ) : avg test=avg (fun first => avg (fun second => test (first,second))) := by
  simp only [avg,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,←Finset.sum_div]
  ring

end Integration9_9.GenericBodySemantics

end

end P2MDyadicModule6

/- Helper module Integration9_9.TM2NativeAffineBudget. -/
section P2MDyadicModule7

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2NativeAffineBudget

open QAlgorithms.Complexity InfoLossLAR.WorstCase LARPlatformEncoding

/-- A fixed sampler coin polynomial evaluated at an explicitly present unary
security parameter is monotone in that parameter. -/
theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

end Integration9_9.TM2NativeAffineBudget

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeRationalGramSchmidtNative. -/
section P2MDyadicModule8

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

theorem ticks_encoding_length (ticks : List Unit) : (enc ticks).length=ticks.length := by
  change (encodeList (fun _ : Unit => []) ticks).length=ticks.length
  induction ticks with
  | nil => rfl
  | cons head tail ih => simp only [EncodedList.cons_length,List.length_nil,List.length_cons,ih];omega

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule8

/- Helper module GuardForSimulation. -/
section P2MDyadicModule9

set_option autoImplicit false

set_option maxHeartbeats 1400000

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped Polynomial

namespace InfoLossLAR.WorstCase.NativeLLL

/-- A unary list whose length is exactly the length of the binary encoding. -/
def reflectedTicks {α : Type} [Coding α] (x : α) : List Unit :=
  (enc x).map fun _ => ()

@[simp] theorem reflectedTicks_length {α : Type} [Coding α] (x : α) :
    (reflectedTicks x).length = (enc x).length := by
  simp [reflectedTicks]

@[fun_prop] theorem reflectedTicks_poly {α : Type} [Coding α] : Poly (reflectedTicks (α := α)) := by
  have hp : Poly (enc (α := α)) :=
    ⟨BooleanLists.packProgram.recode (enc (α := α)) (fun _ => rfl) (fun _ => rfl)⟩
  apply Poly.list_map _ hp
  exact Automatic.Poly.const ()

/-- Each step keeps the old state whenever the new encoding would exceed the supplied cap. -/
def guardedStep {α : Type} [Coding α] (step : α → α) (input : List Unit × α) :
    List Unit × α :=
  let next := step input.2
  (input.1, if (reflectedTicks next).length ≤ input.1.length then next else input.2)

@[fun_prop] theorem guardedStep_poly {α : Type} [Coding α] (step : α → α) (hstep : Poly step) :
    Poly (guardedStep step) := by
  unfold guardedStep
  fun_prop

theorem guardState_length {α : Type} [Coding α] (state : List Unit × α) :
    (enc state).length = 2 * state.1.length + 1 + (enc state.2).length := by
  change (encodePair (encodeList enc) enc state).length = _
  rw [encodePair_length]
  change 2 * (enc state.1).length + 1 + _ = _
  rw [RationalGramSchmidt.Native.ticks_encoding_length]

private theorem guardedStep_length {α : Type} [Coding α] (step : α → α) (x : List Unit × α) :
    (enc (guardedStep step x)).length ≤ max (enc x).length (3 * x.1.length + 1) := by
  rw [guardState_length]
  dsimp only [guardedStep]
  split_ifs with h
  · rw [reflectedTicks_length] at h
    exact (show 2*x.1.length+1+(enc (step x.2)).length ≤ 3*x.1.length+1 by omega).trans
      (le_max_right _ _)
  · rw [← guardState_length]
    exact le_max_left _ _

/-- Fuel and the state cap are separate unary lists. Both count bits or steps. -/
def guardedFold {α : Type} [Coding α] (step : α → α)
    (input : List Unit × (List Unit × α)) : List Unit × α :=
  input.1.foldl (fun state _ => guardedStep step state) input.2

private theorem guardedFold_length {α : Type} [Coding α] (step : α → α)
    (fuel : List Unit) (state : List Unit × α) :
    (enc (guardedFold step (fuel,state))).length ≤
      max (enc state).length (3 * state.1.length + 1) := by
  induction fuel generalizing state with
  | nil => exact le_max_left _ _
  | cons t ts ih =>
    exact (ih (guardedStep step state)).trans <| max_le
      (guardedStep_length step state) (le_max_right _ _)

private theorem guardedFold_bound {α : Type} [Coding α] (step : α → α)
    (fuel : List Unit) (state : List Unit × α) (pre suffix : List Unit)
    (_hsplit : fuel = pre ++ suffix) :
    (enc (guardedFold step (pre,state))).length ≤
      (3*Polynomial.X+1 : Polynomial ℕ).eval (enc (fuel,state)).length := by
  have hstate : (enc state).length ≤ (enc (fuel,state)).length := by
    change (enc state).length ≤ (encodePair (encodeList enc) enc (fuel,state)).length
    rw [encodePair_length]
    change (enc state).length ≤ 2 * (encodeList (enc (α := Unit)) fuel).length + 1 + (enc state).length
    omega
  have hcap : state.1.length ≤ (enc (fuel,state)).length := by
    rw [guardState_length] at hstate
    omega
  apply (guardedFold_length step pre state).trans
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_one]
  omega

@[fun_prop] theorem guardedFold_poly {α : Type} [Coding α] (step : α → α) (hstep : Poly step) :
    Poly (guardedFold step) := by
  have h : Poly (fun x : (List Unit × α) × Unit => guardedStep step x.1) :=
    Poly.comp (guardedStep_poly step hstep) Poly.fst
  exact ⟨h.program.listFold () (3*Polynomial.X+1) (guardedFold_bound step)⟩

/-- The size guard preserves an unguarded trajectory whenever its states fit the cap. -/
theorem guardedFold_eq_iterate {α : Type} [Coding α] (step : α → α)
    (fuel cap : List Unit) (initial : α)
    (hsize : ∀ t, 1 ≤ t → t ≤ fuel.length → (enc ((step^[t]) initial)).length ≤ cap.length) :
    guardedFold step (fuel,cap,initial) = (cap, (step^[fuel.length]) initial) := by
  induction fuel generalizing initial with
  | nil => rfl
  | cons t ts ih =>
    have hnext : (enc (step initial)).length ≤ cap.length := by simpa using hsize 1 (by omega) (by simp)
    change guardedFold step (ts, guardedStep step (cap, initial)) = _
    have hguard : guardedStep step (cap, initial) = (cap, step initial) := by
      simp [guardedStep, hnext]
    rw [hguard]
    rw [ih]
    · simp only [List.length_cons, Function.iterate_succ_apply]
    · intro k _ hk
      rw [← Function.iterate_succ_apply]
      exact hsize (k + 1) (by omega) (by simpa using hk)

end InfoLossLAR.WorstCase.NativeLLL

end P2MDyadicModule9

/- Helper module StockData. -/
section P2MDyadicModule10

set_option autoImplicit false

namespace StockNative

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

instance stackFinite (M : FinTM2) : Fintype M.K := M.kFin

instance labelFinite (M : FinTM2) : Fintype M.Λ := M.ΛFin

instance stateFinite (M : FinTM2) : Fintype M.σ := M.σFin

def num {α : Type} [Fintype α] (a : α) : ℕ := (Fintype.equivFin α a).val

def table {α β : Type} [Fintype α] (g : α → β) : List β :=
  List.ofFn (fun i => g ((Fintype.equivFin α).symm i))

theorem table_lookup {α β : Type} [Fintype α] (g : α → β) (a : α) (d : β) :
    ((table g)[num a]?).getD d = g a := by
  simp [table,num]

theorem table_length {α β : Type} [Fintype α] (g : α → β) : (table g).length = Fintype.card α :=
  List.length_ofFn

abbrev Data := ℕ × ℕ × List (List ℕ)

def code (M : FinTM2) [∀ k, Fintype (M.Γ k)] (c : M.Cfg) : Data :=
  (num c.l, num c.var, table (fun k => (c.stk k).map num))

end

end StockNative

end P2MDyadicModule10

/- Helper module StockStep. -/
section P2MDyadicModule11

set_option autoImplicit false

set_option maxHeartbeats 500000

namespace StockNative

open Turing Function

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

private theorem num_inj {α : Type} [Fintype α] {x y : α} : num x = num y ↔ x = y := by
  exact ⟨fun h => (Fintype.equivFin α).injective (Fin.ext h), congrArg num⟩

private theorem table_map' {α β γ : Type} [Fintype α] (g : α → β) (h : β → γ) :
    (table g).map h = table (fun a => h (g a)) := by
  simp [table,List.map_ofFn,Function.comp_def]

private def restore (keys : List ℕ) (k : ℕ) (d : List ℕ × List (List ℕ)) : List (List ℕ) :=
  keys.map fun j => if j = k then d.1 else d.2[j]?.getD []

@[fun_prop] private theorem restore_poly (keys : List ℕ) (k : ℕ) : Poly (restore keys k) := by
  unfold restore
  fun_prop

private def stackAt (k : ℕ) (x : Data) : List ℕ := x.2.2[k]?.getD []

@[fun_prop] private theorem stackAt_poly (k : ℕ) : Poly (stackAt k) := by unfold stackAt; fun_prop

private def symAt (row : List ℕ) : ℕ :=
  if row.length = 0 then 0 else row.head?.getD 0 + 1

@[fun_prop] private theorem symAt_poly : Poly symAt := by unfold symAt; fun_prop

private def stateAfter {σ γ : Type} [Fintype σ] [Fintype γ] (f : σ → Option γ → σ)
    (data : ℕ × List ℕ) : ℕ :=
  let rows := table (fun v : σ => num (f v none) :: table (fun b : γ => num (f v (some b))))
  ((rows[data.1]?).getD [])[symAt data.2]?.getD 0

@[fun_prop] private theorem stateAfter_poly {σ γ : Type} [Fintype σ] [Fintype γ]
    (f : σ → Option γ → σ) : Poly (stateAfter f) := by unfold stateAfter; fun_prop

private theorem stateAfter_ok {σ γ : Type} [Fintype σ] [Fintype γ] (f : σ → Option γ → σ)
    (v : σ) (s : List γ) : stateAfter f (num v, s.map num) = num (f v s.head?) := by
  dsimp only [stateAfter]
  rw [table_lookup]
  cases s with
  | nil => rfl
  | cons a as =>
    simp only [List.map_cons,symAt,List.length_cons,Nat.add_one_ne_zero,↓reduceIte,
      List.head?_cons,Option.getD_some,List.getElem?_cons_succ,table_lookup]

variable (M : FinTM2) [∀ k, Fintype (M.Γ k)]

private def put (k : M.K) := restore (table (fun j : M.K => num j)) (num k)

omit [∀ k, Fintype (M.Γ k)] in
@[fun_prop] private theorem put_poly (k : M.K) : Poly (put M k) := restore_poly _ _

private theorem put_ok (k : M.K) (s : List (M.Γ k)) (S : ∀ j, List (M.Γ j)) :
    put M k (s.map num, table (fun j => (S j).map num)) =
      table (fun j => ((Function.update S k s) j).map num) := by
  rw [put,restore,table_map']
  apply congrArg table
  funext j
  by_cases hj : j=k
  · subst j
    simp
  · simp [hj,num_inj,table_lookup]

private def aux : M.Stmt → Data → Data
  | .push k f q, x =>
    let value := ((table (fun v => num (f v)))[x.2.1]?).getD 0
    aux q (x.1,x.2.1,put M k (value :: stackAt (num k) x,x.2.2))
  | .peek k f q, x =>
    aux q (x.1,stateAfter f (x.2.1,stackAt (num k) x),x.2.2)
  | .pop k f q, x =>
    let row := stackAt (num k) x
    aux q (x.1,stateAfter f (x.2.1,row),put M k (row.tail,x.2.2))
  | .load f q, x =>
    aux q (x.1,((table (fun v => num (f v)))[x.2.1]?).getD 0,x.2.2)
  | .branch f a b, x => if ((table f)[x.2.1]?).getD false then aux a x else aux b x
  | .goto f, x => (((table (fun v => num (some (f v))))[x.2.1]?).getD 0,x.2)
  | .halt, x => (num (none : Option M.Λ),x.2)

@[fun_prop] private theorem aux_poly (q : M.Stmt) : Poly (aux M q) := by
  change Poly (fun x => aux M q x)
  induction q with
  | push k f q ih => simp only [aux]; fun_prop
  | peek k f q ih => simp only [aux]; fun_prop
  | pop k f q ih => simp only [aux]; fun_prop
  | load f q ih => simp only [aux]; fun_prop
  | branch f a b ha hb => simp only [aux]; fun_prop
  | goto f => simp only [aux]; fun_prop
  | halt => simp only [aux]; fun_prop

private theorem aux_ok (q : M.Stmt) (lab : ℕ) (v : M.σ) (S : ∀ j, List (M.Γ j)) :
    aux M q (lab,num v,table (fun k => (S k).map num)) = code M (TM2.stepAux q v S) := by
  induction q generalizing lab v S with
  | push k f q ih =>
    simp only [aux,stackAt,table_lookup,TM2.stepAux]
    rw [← List.map_cons,put_ok,ih]
  | peek k f q ih =>
    simp only [aux,stackAt,table_lookup,stateAfter_ok,TM2.stepAux,ih]
  | pop k f q ih =>
    simp only [aux,stackAt,table_lookup,stateAfter_ok,TM2.stepAux]
    rw [← List.map_tail,put_ok,ih]
  | load f q ih => simp only [aux,table_lookup,TM2.stepAux,ih]
  | branch f a b ha hb =>
    simp only [aux,table_lookup,TM2.stepAux]
    cases f v <;> simp [ha,hb]
  | goto f => simp [aux,code,TM2.stepAux,table_lookup]
  | halt => rfl

private def action : Option M.Λ → Data → Data
  | none => id
  | some l => aux M (M.m l)

private theorem action_poly (l : Option M.Λ) : Poly (action M l) := by
  cases l with
  | none => exact Poly.identity
  | some l => exact aux_poly M (M.m l)

private theorem fixedTable_poly {α : Type} [Fintype α] (t : α → Data → Data) (ht : ∀ a, Poly (t a)) :
    Poly (fun x : Data => table fun a => t a x) := by
  have h (fs : List (Data → Data)) (hf : ∀ f ∈ fs, Poly f) : Poly (fun x : Data => fs.map (fun f => f x)) := by
    induction fs with
    | nil => exact OAI.MetricKMedian.Binary.Automatic.Poly.const (α := Data) ([] : List Data)
    | cons f fs ih =>
      have hhead := hf f List.mem_cons_self
      have htail := ih (fun g hg => hf g (List.mem_cons_of_mem f hg))
      simp only [List.map_cons]
      fun_prop
  have hk : ∀ f ∈ table t, Poly f := by
    intro f hf
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    exact ht _
  have H := h (table t) hk
  simpa only [table_map'] using H

def stepData (x : Data) : Data := ((table (fun l => action M l x))[x.1]?).getD (0,0,[])

theorem stepData_poly : Poly (stepData M) := by
  have h := fixedTable_poly (action M) (action_poly M)
  unfold stepData
  fun_prop

theorem stepData_correct (c : M.Cfg) : stepData M (code M c) = code M ((M.step c).getD c) := by
  rcases c with ⟨l,v,S⟩
  change ((table _)[num l]?).getD _ = _
  rw [table_lookup]
  cases l with
  | none => rfl
  | some l => exact aux_ok M (M.m l) _ v S

end

end StockNative

end P2MDyadicModule11

/- Helper module StockSize. -/
section P2MDyadicModule12

set_option autoImplicit false

namespace StockNative

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2OutputLength

noncomputable section

private def numWidth (α : Type) [Fintype α] : ℕ :=
  Finset.univ.sup (fun x : α => (enc (num x)).length)

private theorem numWidth_spec {α : Type} [Fintype α] (x : α) :
    (enc (num x)).length ≤ numWidth α :=
  Finset.le_sup (f := fun y : α => (enc (num y)).length) (Finset.mem_univ x)

private theorem encList_bound {α : Type} [Coding α] (xs : List α) (b : ℕ)
    (h : ∀ x ∈ xs, (enc x).length ≤ b) : (enc xs).length ≤ (2*b+1)*xs.length := by
  induction xs with
  | nil => simp [enc, Coding.encode, encodeList]
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    change (encodeList enc xs).length ≤ _ at ht
    change (encodeList enc (a :: xs)).length ≤ _
    rw [EncodedList.cons_length, List.length_cons, Nat.mul_succ]
    omega

theorem code_size (M : FinTM2) [∀ k, Fintype (M.Γ k)] :
    ∃ a b : ℕ, ∀ c : M.Cfg, (enc (code M c)).length ≤ a + b * stackSize c.stk := by
  let glyph := Finset.univ.sup (fun k : M.K => numWidth (M.Γ k))
  let kcount := Fintype.card M.K
  refine ⟨2*numWidth (Option M.Λ)+1+(2*numWidth M.σ+1)+kcount, (kcount*2)*(2*glyph+1), ?_⟩
  intro c
  let sx := stackSize c.stk
  let rows := table (fun k => (c.stk k).map num)
  have hrow (k : M.K) : (enc ((c.stk k).map num)).length ≤ (2*glyph+1)*sx := by
    have hg : numWidth (M.Γ k) ≤ glyph :=
      Finset.le_sup (f := fun j : M.K => numWidth (M.Γ j)) (Finset.mem_univ k)
    have h := encList_bound ((c.stk k).map num) glyph (by
      intro x hx
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
      exact (numWidth_spec v).trans hg)
    rw [List.length_map] at h
    exact h.trans (Nat.mul_le_mul_left _ (length_le_stackSize c.stk k))
  have hout : (enc rows).length ≤ (2*((2*glyph+1)*sx)+1)*kcount := by
    have h := encList_bound rows ((2*glyph+1)*sx) (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hrow _)
    simpa only [rows,table_length,kcount] using h
  have hl := numWidth_spec c.l
  have hs := numWidth_spec c.var
  change (encodePair enc (encodePair enc enc) (num c.l, num c.var, rows)).length ≤ _
  rw [encodePair_length,encodePair_length]
  dsimp only [Prod.fst,Prod.snd]
  calc
    _ ≤ 2*numWidth (Option M.Λ)+1+(2*numWidth M.σ+1) + (2*((2*glyph+1)*sx)+1)*kcount := by omega
    _ = _ := by dsimp only [sx]; ring

end

end StockNative

end P2MDyadicModule12

/- Helper module StockRunCore. -/
section P2MDyadicModule13

set_option autoImplicit false

namespace StockNative

open QAlgorithms.Complexity Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open InfoLossLAR.WorstCase.NativeLLL

open Integration9_9.TM2OutputLength

noncomputable section

def slots (p : Polynomial ℕ) (w : Str) : List Unit := List.replicate (p.eval w.length) ()

@[fun_prop] theorem slots_poly (p : Polynomial ℕ) : Poly (slots p) := by
  have h := Poly.comp (Integration9_9.TM2PolynomialBudget.polynomialSlots_poly p)
    (show Poly (fun w : Str => w.map (fun _ => ())) by fun_prop)
  unfold slots
  simpa only [Function.comp_def,List.length_map] using h

theorem code_iterate (M : FinTM2) [∀ k, Fintype (M.Γ k)] (n : ℕ) (c : M.Cfg) :
    ((stepData M)^[n]) (code M c) = code M (((fun x : M.Cfg => (M.step x).getD x)^[n]) c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepData_correct, ih]

def spaceCap (M : FinTM2) (a b : ℕ) (time : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C a + Polynomial.C b * (Polynomial.X + Polynomial.C (programPushBound M.m) * time)

def runData (M : FinTM2) [∀ k, Fintype (M.Γ k)] (init : Str → Data)
    (time cap : Polynomial ℕ) (w : Str) : Data :=
  (guardedFold (stepData M) (slots time w, slots cap w, init w)).2

@[fun_prop] theorem runData_poly (M : FinTM2) [∀ k, Fintype (M.Γ k)] (init : Str → Data)
    (hi : Poly init) (time cap : Polynomial ℕ) : Poly (runData M init time cap) := by
  have hs := guardedFold_poly _ (stepData_poly M)
  unfold runData
  fun_prop

end

end StockNative

end P2MDyadicModule13

/- Helper module StockIO. -/
section P2MDyadicModule14

set_option autoImplicit false

namespace StockNative

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

variable (M : FinTM2) [∀ k, Fintype (M.Γ k)]

def initData (ie : M.Γ M.k₀ ≃ Bool) (w : List Bool) : Data :=
  (num (some M.main), num M.initialState,
    (table fun k : M.K => decide (k = M.k₀)).map fun active =>
      if active then w.map (fun b => if b then num (ie.symm true) else num (ie.symm false)) else [])

@[fun_prop] theorem initData_poly (ie : M.Γ M.k₀ ≃ Bool) : Poly (initData M ie) := by
  unfold initData
  fun_prop

theorem initData_correct (ie : M.Γ M.k₀ ≃ Bool) (w : List Bool) :
    initData M ie w = code M (initList M (w.map ie.symm)) := by
  unfold initData code
  congr 1
  congr 1
  simp only [table, List.map_ofFn, Function.comp_def]
  apply congrArg List.ofFn
  funext i
  generalize (Fintype.equivFin M.K).symm i = k
  by_cases h : k = M.k₀
  · subst k
    simp only [initList, decide_true, if_true, dite_true]
    change _ = (w.map ie.symm).map num
    rw [List.map_map]
    apply List.map_congr_left
    intro b _
    cases b <;> rfl
  · simp [initList,h]

def outData (oe : M.Γ M.k₁ ≃ Bool) (x : Data) : List Bool :=
  (x.2.2[num M.k₁]?.getD []).map (fun sym => (table oe)[sym]?.getD false)

@[fun_prop] theorem outData_poly (oe : M.Γ M.k₁ ≃ Bool) : Poly (outData M oe) := by
  unfold outData
  fun_prop

theorem outData_correct (oe : M.Γ M.k₁ ≃ Bool) (os : List Bool) :
    outData M oe (code M (haltList M (os.map oe.symm))) = os := by
  simp only [outData,code,table_lookup]
  simp [haltList,List.map_map,Function.comp_def,table_lookup]

end

end StockNative

end P2MDyadicModule14

/- Helper module StockClock. -/
section P2MDyadicModule15

set_option autoImplicit false

namespace StockNative

open Turing StateTransition OAI.MetricKMedian.Binary Integration9_9.TM2OutputLength

def sticky (M : FinTM2) (c : M.Cfg) : M.Cfg := (M.step c).getD c

private theorem sticky_trace (M : FinTM2) {a b : M.Cfg} {k : ℕ} (h : Trace M.step k a b) :
    (sticky M)^[k] a = b := by
  induction h with
  | refl => rfl
  | cons hs _ ih => simpa only [Function.iterate_succ_apply,sticky,hs,Option.getD_some] using ih

theorem sticky_time (M : FinTM2) (a b : M.Cfg) (T : ℕ)
    (h : EvalsToInTime M.step a (some b) T) (hb : M.step b = none) :
    (sticky M)^[T] a = b := by
  have hs := sticky_trace M (Trace.of_inTime h)
  have he : T = (T - h.steps) + h.steps := by have := h.steps_le_m; omega
  rw [he,Function.iterate_add_apply,hs]
  exact Function.iterate_fixed (by simp only [sticky,hb,Option.getD_none] : sticky M b = b) _

theorem sticky_size (M : FinTM2) (c : M.Cfg) (k : ℕ) :
    stackSize (((sticky M)^[k]) c).stk ≤ stackSize c.stk + programPushBound M.m * k := by
  have lone (s : M.Cfg) : stackSize (sticky M s).stk ≤ stackSize s.stk + programPushBound M.m := by
    cases hs : M.step s with
    | none => simp only [sticky,hs,Option.getD_none]; exact Nat.le_add_right _ _
    | some t => simpa only [sticky,hs,Option.getD_some] using step_stackSize_le M.m s t hs
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Nat.mul_succ]
    exact (lone ((sticky M)^[k] c)).trans (by omega)

end StockNative

end P2MDyadicModule15

/- Helper module StockRun. -/
section P2MDyadicModule16

set_option autoImplicit false

namespace StockNative

open Turing StateTransition QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open InfoLossLAR.WorstCase.NativeLLL Integration9_9.TM2OutputLength

theorem poly_of_finite {f : Str → Str} (P : TM2ComputableInPolyTime (id : Str → Str) id f)
    [∀ k, Fintype (P.tm.Γ k)] : Poly f := by
  obtain ⟨a,b,hcode⟩ := code_size P.tm
  let cap := spaceCap P.tm a b P.time
  let run := runData P.tm (initData P.tm P.inputAlphabet) P.time cap
  have hp : Poly (fun w => outData P.tm P.outputAlphabet (run w)) :=
    Poly.comp (outData_poly _ _) (runData_poly _ _ (initData_poly _ _) _ _)
  have he (w : Str) : outData P.tm P.outputAlphabet (run w) = f w := by
    let start := initList P.tm (w.map P.inputAlphabet.symm)
    let finalState := haltList P.tm ((f w).map P.outputAlphabet.symm)
    have hstart : stackSize start.stk ≤ w.length := by
      simpa only [start,List.length_map] using initList_stackSize_le P.tm (w.map P.inputAlphabet.symm)
    have hsize (k : ℕ) (hk : k ≤ P.time.eval w.length) :
        (enc (((stepData P.tm)^[k]) (code P.tm start))).length ≤ cap.eval w.length := by
      rw [code_iterate]
      apply (hcode _).trans
      simp only [cap,spaceCap,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul_left
      exact (sticky_size P.tm start k).trans
        (Nat.add_le_add hstart (Nat.mul_le_mul_left _ hk))
    have hm : ((sticky P.tm)^[P.time.eval w.length]) start = finalState :=
      sticky_time P.tm start finalState _ (P.outputsFun w) rfl
    unfold run runData
    rw [initData_correct,guardedFold_eq_iterate]
    · simp only [slots,List.length_replicate]
      rw [code_iterate]
      change outData P.tm P.outputAlphabet (code P.tm (((sticky P.tm)^[P.time.eval w.length]) start)) = f w
      rw [hm]
      exact outData_correct _ _ _
    · intro k _ hk
      simp only [slots,List.length_replicate] at hk ⊢
      exact hsize k hk
  convert hp using 1
  exact (funext he).symm

end StockNative

end P2MDyadicModule16

/- Helper module Normalize. -/
section P2MDyadicModule17

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace StockFinite

open Turing StateTransition Function QAlgorithms.Complexity

noncomputable section

variable {f : Str → Str} (P : TM2ComputableInPolyTime (id : Str → Str) id f)

local instance controlFinite (m : FinTM2) : Fintype m.σ := m.σFin

local instance labelsFinite (m : FinTM2) : Fintype m.Λ := m.ΛFin

def alphabet : Finset (Sigma P.tm.Γ) :=
  Finset.univ.biUnion (fun l : P.tm.Λ => writes (P.tm.m l)) ∪
    Finset.univ.image (fun b : Bool => Sigma.mk P.tm.k₀ (P.inputAlphabet.symm b)) ∪
    Finset.univ.image (fun b : Bool => Sigma.mk P.tm.k₁ (P.outputAlphabet.symm b))

theorem alphabet_code (l : P.tm.Λ) : writes (P.tm.m l) ⊆ alphabet P := by
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,hx⟩))

theorem hasInput (x : P.tm.Γ P.tm.k₀) : Sigma.mk P.tm.k₀ x ∈ alphabet P := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨P.inputAlphabet x,Finset.mem_univ _,by simp⟩

theorem hasOutput (x : P.tm.Γ P.tm.k₁) : Sigma.mk P.tm.k₁ x ∈ alphabet P := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨P.outputAlphabet x,Finset.mem_univ _,by simp⟩

def machine : FinTM2 where
  K := P.tm.K
  kDecidableEq := P.tm.kDecidableEq
  kFin := P.tm.kFin
  k₀ := P.tm.k₀
  k₁ := P.tm.k₁
  Γ := Letter (alphabet P)
  Λ := P.tm.Λ
  ΛFin := P.tm.ΛFin
  main := P.tm.main
  σ := P.tm.σ
  initialState := P.tm.initialState
  σFin := P.tm.σFin
  Γk₀Fin := finiteLetter (alphabet P) _
  m l := restrictStmt (alphabet P) (P.tm.m l) (alphabet_code P l)

def inputEquiv : (machine P).Γ (machine P).k₀ ≃ Bool where
  toFun x := P.inputAlphabet x.val
  invFun b := ⟨P.inputAlphabet.symm b,hasInput P _⟩
  left_inv x := Subtype.ext (P.inputAlphabet.symm_apply_apply x.val)
  right_inv := P.inputAlphabet.apply_symm_apply

def outputEquiv : (machine P).Γ (machine P).k₁ ≃ Bool where
  toFun x := P.outputAlphabet x.val
  invFun b := ⟨P.outputAlphabet.symm b,hasOutput P _⟩
  left_inv x := Subtype.ext (P.outputAlphabet.symm_apply_apply x.val)
  right_inv := P.outputAlphabet.apply_symm_apply

theorem step_map (c : (machine P).Cfg) :
    ((machine P).step c).map forgetCfg = P.tm.step (forgetCfg c) := by
  obtain ⟨l,v,S⟩ := c
  cases l with
  | none => rfl
  | some l => exact congrArg some (restrictAux (alphabet P) (P.tm.m l) (alphabet_code P l) v S)

theorem forget_injective : Injective (forgetCfg (Γ := P.tm.Γ) (Λ := P.tm.Λ) (σ := P.tm.σ) (bound := alphabet P)) := by
  rintro ⟨l,v,S⟩ ⟨l',v',S'⟩ h
  obtain ⟨hl,hv,hs⟩ : l=l' ∧ v=v' ∧ forget S = forget S' := by simpa [forgetCfg] using h
  have hst : S=S' := by
    funext k
    exact List.map_injective_iff.mpr Subtype.val_injective (congrFun hs k)
  subst l'; subst v'; subst S'
  rfl

theorem iterate_map (n : ℕ) (c : Option (machine P).Cfg) :
    Option.map forgetCfg (((fun s : Option (machine P).Cfg => s.bind (machine P).step)^[n]) c) =
      ((fun s : Option P.tm.Cfg => s.bind P.tm.step)^[n]) (c.map forgetCfg) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply,ih]
    apply congrArg
    cases c with
    | none => rfl
    | some c => exact step_map P c

theorem init_forget (w : Str) :
    forgetCfg (initList (machine P) (w.map (inputEquiv P).symm)) =
      initList P.tm (w.map P.inputAlphabet.symm) := by
  apply congrArg (TM2.Cfg.mk (some P.tm.main) P.tm.initialState)
  funext k
  by_cases he : k = P.tm.k₀
  · subst k
    simp [initList,forget,machine,inputEquiv,List.map_map,Function.comp_def]
  · simp [initList,forget,machine,he]

theorem final_forget (w : Str) :
    forgetCfg (haltList (machine P) (w.map (outputEquiv P).symm)) =
      haltList P.tm (w.map P.outputAlphabet.symm) := by
  apply congrArg (TM2.Cfg.mk none P.tm.initialState)
  funext k
  by_cases he : k = P.tm.k₁
  · subst k
    simp [haltList,forget,machine,outputEquiv,List.map_map,Function.comp_def]
  · simp [haltList,forget,machine,he]

def finiteWitness : TM2ComputableInPolyTime (id : Str → Str) id f where
  tm := machine P
  inputAlphabet := inputEquiv P
  outputAlphabet := outputEquiv P
  time := P.time
  outputsFun w := by
    have hw := P.outputsFun w
    refine ⟨⟨hw.steps,?_⟩,hw.steps_le_m⟩
    apply Option.map_injective (forget_injective P)
    let init := initList (machine P) (w.map (inputEquiv P).symm)
    let stop := haltList (machine P) ((f w).map (outputEquiv P).symm)
    change Option.map forgetCfg (((fun s : Option (machine P).Cfg => s.bind (machine P).step)^[hw.steps]) (some init)) = some (forgetCfg stop)
    rw [iterate_map P hw.steps (some init)]
    change ((fun s : Option P.tm.Cfg => s.bind P.tm.step)^[hw.steps]) (some (forgetCfg (initList (machine P) (w.map (inputEquiv P).symm)))) =
      some (forgetCfg (haltList (machine P) ((f w).map (outputEquiv P).symm)))
    rw [init_forget P,final_forget P]
    exact hw.evals_in_steps

theorem normalize (h : PolyTimeComputable f) :
    ∃ Q : TM2ComputableInPolyTime (id : Str → Str) id f, ∀ k, Finite (Q.tm.Γ k) := by
  obtain ⟨P⟩ := h
  exact ⟨finiteWitness P,fun k => @Finite.of_fintype _ (finiteLetter (alphabet P) k)⟩

end

end StockFinite

end P2MDyadicModule17

/- Helper module GenAffine. -/
section P2MDyadicModule18

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.GeneralAffine

open QAlgorithms.Complexity Integration9_9 Integration9_9.LARPlatformEncoding

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators Classical

theorem stock_poly {f : Str → Str} (hf : PolyTimeComputable f) : Poly f := by
  classical
  obtain ⟨P,hP⟩ := StockFinite.normalize hf
  let (k : P.tm.K) : Fintype (P.tm.Γ k) := @Fintype.ofFinite _ (hP k)
  exact StockNative.poly_of_finite P

end InfoLossLAR.WorstCase.GeneralAffine

end

end P2MDyadicModule18

/- Helper module Once. -/
section P2MDyadicModule19

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.OneCall

open Integration9_9 LARPlatformEncoding QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators Classical

noncomputable section

def cost (m : Polynomial ℕ) (w : Str) := TM2NativeAffinePre.blockBits m (w.map (fun _=>()))

@[fun_prop] theorem cost_poly (m : Polynomial ℕ) : Poly (cost m) := by unfold cost; fun_prop

theorem cost_eq (m : Polynomial ℕ) (w : Str) : cost m w=m.eval w.length := by
  simp [cost,TM2NativeAffinePre.blockBits]

def inputs (w : Str) : Str × Str × Str :=
  let a:=readS w
  let b:=readS a.1
  (a.2,b.2,b.1)

@[fun_prop] theorem inputs_poly : Poly inputs := by unfold inputs; fun_prop

theorem inputs_eq (ρ w suffix : Str) : inputs (encPair ρ w ++ suffix) = (ρ,w,suffix) := by
  simp [inputs,encPair,List.append_assoc]

def takeBits (x : Str × ℕ) := x.1.take x.2

@[fun_prop] theorem takeBits_poly : Poly takeBits := QMCNumericRuntime.parser_take_poly

def dropBits (x : Str × ℕ) := x.1.drop x.2

@[fun_prop] theorem dropBits_poly : Poly dropBits := QMCNumericRuntime.parser_drop_poly

def parts (pre : Str → Str) (m₂ m₁ : Polynomial ℕ) (x : Str × Str) : Str × Str :=
  let outer := takeBits (x.1,cost m₂ x.2)
  let ow := encPair outer x.2
  let mid := pre ow
  let inner := takeBits (dropBits (x.1,cost m₂ x.2),cost m₁ mid)
  (ow,encPair inner mid)

@[fun_prop] theorem parts_poly (pre : Str → Str) (hp : Poly pre) (m₂ m₁ : Polynomial ℕ) : Poly (parts pre m₂ m₁) := by
  unfold parts
  fun_prop

def query (p₁ p₂ : Str → Str) (m₂ m₁ : Polynomial ℕ) (word : Str) : Str :=
  let v:=inputs word
  p₁ (parts p₂ m₂ m₁ (v.1,v.2.1)).2

@[fun_prop] theorem query_poly (p₁ p₂ : Str → Str) (h₁ : Poly p₁) (h₂ : Poly p₂) (m₂ m₁ : Polynomial ℕ) :
    Poly (query p₁ p₂ m₂ m₁) := by unfold query; fun_prop

def eventbit (word : Str) : Bool := word[0]?.getD false

@[fun_prop] theorem eventbit_poly : Poly eventbit := by
  change Poly (fun word : Str => word[0]?.getD false)
  fun_prop

theorem eventbit_eq (word : Str) : eventbit word = true ↔ word.head? = some true := by
  cases word with | nil => simp [eventbit] | cons b l => simp [eventbit]

def output (p₂ s₁ s₂ : Str → Str) (m₂ m₁ : Polynomial ℕ) (word : Str) : Str :=
  let v:=inputs word
  let ix:=parts p₂ m₂ m₁ (v.1,v.2.1)
  s₂ (ix.1 ++ [eventbit (s₁ (ix.2 ++ v.2.2))])

@[fun_prop] theorem output_poly (p₂ s₁ s₂ : Str → Str) (hp : Poly p₂) (h₁ : Poly s₁) (h₂ : Poly s₂)
    (m₂ m₁ : Polynomial ℕ) : Poly (output p₂ s₁ s₂ m₂ m₁) := by unfold output; fun_prop

def liftBit (test : Bool → Bool) (p : ℝ) : ℝ := (if test true then p else 0)+(if test false then 1-p else 0)

theorem output_action (s : Str → Str) (x : Str) (p : ℝ) :
    (if (s (x ++ [true])).head? = some true then p else 0) +
    (if (s (x ++ [false])).head? = some true then 1-p else 0) =
    liftBit (fun b => eventbit (s (x++[b]))) p := by
  simp only [liftBit,eventbit_eq]

theorem liftBit_comp (t s : Bool → Bool) (p : ℝ) :
    liftBit t (liftBit s p)=liftBit (t ∘ s) p := by
  cases ha : s true <;> cases hb : s false <;> cases hc : t true <;> cases hd : t false <;>
    simp only [liftBit,Function.comp_def,ha,hb,hc,hd,ite_true,ite_false,Bool.false_eq_true] <;> ring

theorem liftBit_avg {α : Type} [Fintype α] [Nonempty α] (f : α → ℝ) (t : Bool → Bool) :
    liftBit t (avg f)=avg (fun x=>liftBit t (f x)) := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  cases h₁ : t true <;> cases h₂ : t false <;>
    simp [liftBit,h₁,h₂,avg,Finset.sum_sub_distrib,Finset.sum_add_distrib,sub_div,add_div,hc]

theorem parts_eq (pre : Str → Str) (m₂ m₁ : Polynomial ℕ) (w a b : Str) (ha : a.length = m₂.eval w.length) :
    parts pre m₂ m₁ (a++b,w) = (encPair a w, encPair (b.take (m₁.eval (pre (encPair a w)).length)) (pre (encPair a w))) := by
  simp only [parts,takeBits,dropBits,cost_eq,←ha,List.take_left,List.drop_left]

theorem take_ofFn {l k : ℕ} (h : k ≤ l) (v : Fin l → Bool) :
    (List.ofFn v).take k= List.ofFn (fun i=>v (Fin.castLE h i)) := by
  apply List.ext_getElem <;> simp [h]

theorem avg_tapes (a b : ℕ) (f : Str → ℝ) :
    (avg fun tape : Fin (a+b) → Bool=>f (List.ofFn tape)) =
    avg fun v : Fin a → Bool=> avg fun z : Fin b → Bool => f (List.ofFn v++List.ofFn z) := by
  let q := fun pair : (Fin a → Bool) × (Fin b → Bool) => f (List.ofFn pair.1 ++ List.ofFn pair.2)
  rw [← GenericBodySemantics.avg_product (test:=q)]
  refine Eq.trans ?_ (FairBitPadding.avg_equiv (FairBitPadding.splitEquiv a b) q)
  apply congrArg avg
  funext tape
  apply congrArg f
  rw [List.ofFn_add]
  rfl

end

end InfoLossLAR.WorstCase.OneCall

end P2MDyadicModule19

/- Helper module OnceCompose. -/
section P2MDyadicModule20

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.OneCall

open Integration9_9 LARPlatformEncoding QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators Classical

noncomputable section

theorem trans {A B D : Family} (hAB : CallsOnce A B) (hBD : CallsOnce B D) : CallsOnce A D := by
  classical
  obtain ⟨p₂,s₂,m₂,hp₂,hs₂,h₂⟩:=hAB
  obtain ⟨p₁,s₁,m₁,hp₁,hs₁,h₁⟩:=hBD
  have pp₂:=GeneralAffine.stock_poly hp₂
  have ps₂:=GeneralAffine.stock_poly hs₂
  have pp₁:=GeneralAffine.stock_poly hp₁
  have ps₁:=GeneralAffine.stock_poly hs₁
  let hprep : Poly (fun w : Str => p₂ (LARCoinLayout.coinFirstPair m₂ w)) :=
    Poly.comp (f:=p₂) (g:=LARCoinLayout.coinFirstPair m₂) pp₂ (LARCoinLayout.coinFirstPair_poly m₂)
  let P:=LARCoinLayout.rawPolyProgram hprep
  let bound:=m₁.comp (P.sizeBound.comp (m₂+Polynomial.X))
  let total:=m₂+bound
  refine ⟨query p₁ p₂ m₂ m₁,output p₂ s₁ s₂ m₂ m₁,total,
    TM2PlatformSerialization.polyTime_of_poly (query_poly _ _ pp₁ pp₂ _ _),
    TM2PlatformSerialization.polyTime_of_poly (output_poly _ _ _ pp₂ ps₁ ps₂ _ _),?_⟩
  intro w
  let o:=m₂.eval w.length
  let k:=bound.eval w.length
  have hbudget (a : Fin o → Bool) : m₁.eval (p₂ (encPair (List.ofFn a) w)).length ≤ k := by
    have hh := P.length_bound (List.ofFn a ++ w)
    change (p₂ (LARCoinLayout.coinFirstPair m₂ (List.ofFn a ++ w))).length ≤ P.sizeBound.eval (List.ofFn a ++ w).length at hh
    rw [LARCoinLayout.coinFirstPair_eq _ _ _ (by simp [o]),List.length_append,List.length_ofFn] at hh
    apply (TM2NativeAffineBudget.eval_mono m₁ hh).trans_eq
    simp only [k,bound,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X,o]
  let tested (tape : Str) :=
      let x:= encPair tape w
      liftBit (fun bit => eventbit (output p₂ s₁ s₂ m₂ m₁ (x ++ [bit])))
        (acceptProb D (query p₁ p₂ m₂ m₁ x))
  simp_rw [output_action]
  change acceptProb A w = avg (fun tape : Fin (total.eval w.length) → Bool => tested (List.ofFn tape))
  have ht : total.eval w.length=o+k := Polynomial.eval_add
  rw [ht,avg_tapes]
  rw [h₂]
  apply congrArg avg
  funext a
  let outer:=encPair (List.ofFn a) w
  let mid:=p₂ outer
  let sout:=fun bit=>eventbit (s₂ (outer ++ [bit]))
  let c:=m₁.eval mid.length
  let test := fun z : Str =>
    let inner:= encPair z mid
    let sin:=fun bit=>eventbit (s₁ (inner ++ [bit]))
    liftBit sout (liftBit sin (acceptProb D (p₁ inner)))
  have htest (z : Fin k → Bool) : tested (List.ofFn a ++ List.ofFn z) =
      test ((List.ofFn z).take c) := by
    have ha : (List.ofFn a).length=m₂.eval w.length := by simp only [List.length_ofFn,o]
    have hq (t : Str) : inputs (encPair (List.ofFn a++List.ofFn z) w ++ t) = (List.ofFn a++List.ofFn z,w,t) := inputs_eq _ _ _
    have he : inputs (encPair (List.ofFn a++List.ofFn z) w) = (List.ofFn a++List.ofFn z,w,[]) := by simpa using hq []
    simp only [tested,query,output,hq,he,parts_eq _ _ _ _ _ _ ha]
    let inner := encPair ((List.ofFn z).take c) mid
    let sin := fun bit=>eventbit (s₁ (inner ++ [bit]))
    exact (liftBit_comp sout sin (acceptProb D (p₁ inner))).symm
  rw [output_action]
  change liftBit sout (acceptProb B mid) = _
  rw [h₁]
  simp_rw [output_action]
  rw [liftBit_avg]
  change (avg fun z : Fin c → Bool => test (List.ofFn z)) = _
  have hstep : ∀ z : Fin k → Bool, tested (List.ofFn a ++ List.ofFn z) = test (List.ofFn (fun i : Fin c => z (Fin.castLE (hbudget a) i))) := by
    intro z
    rw [htest, take_ofFn (hbudget a) z]
  simp_rw [hstep]
  exact (FairBitPadding.avg_prefix (hbudget a) (fun z=>test (List.ofFn z))).symm

end

end InfoLossLAR.WorstCase.OneCall

end P2MDyadicModule20

/- Helper module FiveFive. -/
section P2MDyadicModule21

set_option autoImplicit false

open InfoLossLAR.WorstCase QAlgorithms.Complexity

theorem solution (F : RoundingFamily) (hF : F.Efficient)
    (hAFT : F.AdmitsFixedOrderGaussianAFT) :
    (∀ c : ℕ, 1 ≤ c → ∀ t : ℕ → ℕ, (∀ lam, 1 ≤ t lam) → PolyBoundedFn t →
      ∀ D : Family, IsQPT D →
        ∃ B : Family, IsQPT B ∧ CallsOnce B D ∧
          ∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
            F.advLAR D lam (t lam) ≤
              (F.q lam : ℝ) * F.advGauss B lam (t lam) +
                (F.q lam : ℝ) * (t lam : ℝ) * (lam : ℝ) ^ (-(c : ℝ)) +
                ((F.q lam : ℝ) ^ F.N lam)⁻¹) ∧
    ((PolyBoundedFn F.q ∧ Negligible (fun lam => ((F.q lam : ℝ) ^ F.N lam)⁻¹) ∧
        ∀ B : Family, IsQPT B → ∀ t : ℕ → ℕ, (∀ lam, 1 ≤ t lam) → PolyBoundedFn t →
          Negligible fun lam => F.advGauss B lam (t lam)) →
      ∀ D : Family, IsQPT D → ∀ t : ℕ → ℕ, (∀ lam, 1 ≤ t lam) → PolyBoundedFn t →
        Negligible fun lam => F.advLAR D lam (t lam)) := by
  obtain ⟨hq,hnegl⟩ := theorem_5_4 F hF hAFT
  constructor
  · intro c hc t ht htp D hD
    obtain ⟨M,hM,honce₁,huzf⟩ := theorem_4_2 F hF D hD t ht htp
    obtain ⟨B,hB,honce₂,cut,hG⟩ := hq c hc M hM t ht htp
    refine ⟨B,hB,OneCall.trans honce₂ honce₁,max 1 cut,?_⟩
    intro n hn
    have hu := huzf n (by omega)
    have hg := mul_le_mul_of_nonneg_left (hG n (by omega)) (Nat.cast_nonneg (F.q n) : (0:ℝ) ≤ F.q n)
    linarith
  · rintro ⟨hqp,htail,hg⟩ D hD t ht htp
    obtain ⟨M,hM,honce,huzf⟩ := theorem_4_2 F hF D hD t ht htp
    obtain ⟨a,na,hqa⟩ := polyBoundedFn_eventually_le_power _ hqp
    have hm := hnegl hg M hM t ht htp
    apply GeneralBounds.of_integers _ (fun _=>abs_nonneg _)
    intro k hk
    obtain ⟨n₁,h₁⟩ := hm.2 (a+(k+1):ℕ) (by positivity)
    obtain ⟨n₂,h₂⟩ := htail.2 (k+1:ℕ) (by positivity)
    refine ⟨max 2 (max na (max n₁ n₂)),?_⟩
    intro n hn
    have hp := GeneralBounds.product_error (p:=a) (k:=k+1) (n:=n) (by omega) (F.q n) (by exact_mod_cast hqa n (by omega))
    have hmain := (mul_le_mul_of_nonneg_left (h₁ n (by omega)) (Nat.cast_nonneg (F.q n) : (0:ℝ) ≤ F.q n)).trans hp
    exact (huzf n (by omega)).trans ((add_le_add hmain (h₂ n (by omega))).trans (GeneralBounds.two_errors k (by omega)))

end P2MDyadicModule21
