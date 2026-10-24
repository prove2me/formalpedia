-- Prove2me | solution 1 for OAI.ExactFourier.win_to_fourier
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T22:10:33.449005+00:00
-- url     : https://prove2.me/submissions/9d4678a6-7e1c-452d-af52-ed387ee42ede

import Mathlib
import Definitions.Def_ExactFourier
import Definitions.Def_OAIQWEXF000

section
-- module Solutions.OAIQW_ExactFourier.PortMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe fourierU1 fourierU2

section

namespace ExactFourier

theorem rectangularShear_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (G H : Matrix ι κ ℂ) :
    rectangularShear G * rectangularShear H = rectangularShear (G + H) := by
  simp [rectangularShear, Matrix.fromBlocks_multiply, add_comm]

theorem rectangularShear_inv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (G : Matrix ι κ ℂ) :
    (rectangularShear G)⁻¹ = rectangularShear (-G) := by
  apply Matrix.inv_eq_right_inv
  rw [rectangularShear_mul]
  simp [rectangularShear, ← Matrix.fromBlocks_one]

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.LinearDAG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier

/-- Literal semantics of DAG composition, including preservation of every existing value. -/
theorem Program.eval_append {n m k l : ℕ} (p : Program n k) (q : Program m l)
    (f : Fin (m + 1) → Fin (n + 1 + k)) (x : Fin n → ℂ) (y : Fin m → ℂ)
    (hf : ∀ (i : Fin (m + 1)), p.eval x (f i) = (Fin.snoc y 0 : Fin (m + 1) → ℂ) i) :
    (∀ j, (p.append f q).eval x (keepIndex j) = p.eval x j) ∧
    (∀ i, (p.append f q).eval x (appendIndex f i) = q.eval y i) := by
  induction q with
  | nil =>
      constructor
      · intro j; rfl
      · intro i; simpa [Program.append, Program.eval] using hf i
  | @step l q g ih =>
      constructor
      · intro j
        simp only [Program.append, Program.eval, keepIndex_succ, Fin.snoc_castSucc]
        exact ih.1 j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · calc
            _ = (p.append f (q.step g)).eval x (Fin.last (n + 1 + (k + l))) :=
              congrArg ((p.append f (q.step g)).eval x) (appendIndex_last f)
            _ = _ := by
              simp only [Program.append, Program.eval, Nat.add_eq, Fin.snoc_last, Gate.eval_map]
              congr 1
              funext j
              exact ih.2 j
        · simp only [appendIndex_castSucc, Program.append, Program.eval, Fin.snoc_castSucc]
          exact ih.2 j

theorem Program.eval_zero {n k : ℕ} (p : Program n k) (x : Fin n → ℂ) :
    p.eval x ⟨n, by omega⟩ = 0 := by
  induction p with
  | nil => exact Fin.snoc_last _ _
  | @step k p g ih =>
      change (Fin.snoc (p.eval x) (g.eval (p.eval x)) : Fin (n + 1 + k + 1) → ℂ)
        (Fin.castSucc (⟨n, by omega⟩ : Fin (n + 1 + k))) = 0
      rw [Fin.snoc_castSucc, ih]

theorem LinearDAG.eval_comp {n a b : ℕ} (D : LinearDAG a b) (C : LinearDAG n a)
    (x : Fin n → ℂ) : (D.comp C).eval x = D.eval (C.eval x) := by
  have hf : ∀ (i : Fin (a + 1)), C.program.eval x
      ((Fin.snoc C.outputs (⟨n, by omega⟩ : Fin (n + 1 + C.size)) :
        Fin (a + 1) → Fin (n + 1 + C.size)) i) =
      (Fin.snoc (C.eval x) 0 : Fin (a + 1) → ℂ) i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using C.program.eval_zero x
    · simp [LinearDAG.eval]
  have he := C.program.eval_append D.program (Fin.snoc C.outputs ⟨n, by omega⟩) x (C.eval x) hf
  funext i
  exact he.2 (D.outputs i)

end ExactFourier

namespace ExactFourier

theorem LinearDAG.eval_layer {n a : ℕ} (g : Fin a → Gate (n + 1))
    (x : Fin n → ℂ) : (LinearDAG.layer g).eval x = fun i => (g i).eval (Fin.snoc x 0) := by
  funext i
  exact (Program.nil.eval_emit g x).2 i

end ExactFourier

namespace ExactFourier

private theorem foldColumns_size {n a : ℕ} (G : Matrix (Fin a) (Fin n) ℂ)
    (L : List (Fin n)) (C : LinearDAG n a) :
    (L.foldl (fun C j => C.addColumn j (fun i => G i j)) C).size =
      C.size + 2 * a * L.length := by
  induction L generalizing C with
  | nil => simp
  | cons j L ih =>
      rw [List.foldl_cons, ih]
      simp only [LinearDAG.addColumn, List.length_cons]
      ring

@[simp] theorem LinearDAG.size_matrix {n a : ℕ} (G : Matrix (Fin a) (Fin n) ℂ) :
    (LinearDAG.matrix n a G).size = 2 * a * n := by
  simp [LinearDAG.matrix, foldColumns_size, LinearDAG.wires]

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.StreamSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The same exact tensor index for scalar, polynomial, and series matrices.
The zero tensor power has one coordinate and is identity. -/
namespace ExactFourier
open scoped Kronecker BigOperators
open Triangular TensorTools
namespace TensorAxis

variable {α : Type} [Fintype α] [DecidableEq α]
variable {R S : Type} [CommSemiring R] [CommSemiring S]

theorem mul_power
    {α : Type} [Fintype α] [DecidableEq α] {R : Type} [CommSemiring R] (A B : Matrix α α R) (k : ℕ) :
    power A k * power B k = power (A*B) k := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    change (power A k ⊗ₖ A) * (power B k ⊗ₖ B) = _
    rw [← Matrix.mul_kronecker_mul,ih]
    rfl

end TensorAxis
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.CircuitExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier

theorem Program.eval_original {n k : ℕ} (p : Program n k) (x : Fin n → ℂ)
    (i : Fin (n+1)) : p.eval x (Fin.castAdd k i) = (Fin.snoc x 0 : Fin (n+1) → ℂ) i := by
  induction p with
  | nil => rfl
  | @step k p g ih =>
      change (Fin.snoc (p.eval x) (g.eval (p.eval x)) : Fin (n+1+k+1) → ℂ)
        (Fin.castSucc (Fin.castAdd k i)) = _
      rw [Fin.snoc_castSucc]
      exact ih

theorem LinearDAG.eval_fanout {n a b : ℕ}
    (C : LinearDAG n a) (D : LinearDAG n b) (x : Fin n → ℂ) :
    (C.fanout D).eval x = Fin.addCases (C.eval x) (D.eval x) := by
  have h := C.program.eval_append D.program (Fin.castAdd C.size) x x
    (fun i => C.program.eval_original x i)
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [LinearDAG.eval, LinearDAG.fanout, Fin.addCases_left] using h.1 (C.outputs j)
  · simpa only [LinearDAG.eval, LinearDAG.fanout, Fin.addCases_right] using h.2 (D.outputs j)

theorem LinearDAG.eval_withInputs {m n a : ℕ} (C : LinearDAG n a)
    (f : Fin n → Fin m) (x : Fin m → ℂ) : (C.withInputs f).eval x = C.eval (x ∘ f) := by
  rw [LinearDAG.withInputs, LinearDAG.eval_comp, LinearDAG.eval_wires]
  congr 1
  funext i
  simp only [Fin.snoc_castSucc, Function.comp_apply]

end ExactFourier

end

section
/-! Finite-index wrappers for the exact charged DAG model. These are used for the
state-clearing tensor-axis maps in the cascade and coefficient boundary cost. -/
namespace ExactFourier
open scoped BigOperators Kronecker

namespace TypedDAG
variable {ι κ τ υ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]

@[simp] theorem eval_comp (D : TypedDAG κ τ) (C : TypedDAG ι κ) (x : ι → ℂ) :
    (D.comp C).eval x = D.eval (C.eval x) := by
  funext j
  simp [eval, comp, LinearDAG.eval_comp, Function.comp_def]

@[simp] theorem eval_inputs (C : TypedDAG ι κ) (f : ι → τ) (x : τ → ℂ) :
    (C.inputs f).eval x = C.eval (x ∘ f) := by
  funext j
  simp [eval, inputs, LinearDAG.eval_withInputs, Function.comp_def]

@[simp] theorem eval_fanout (C : TypedDAG ι κ) (D : TypedDAG ι τ) (x : ι → ℂ) :
    (C.fanout D).eval x = Sum.elim (C.eval x) (D.eval x) := by
  funext j
  cases j <;> simp [eval, fanout, LinearDAG.eval_fanout, Function.comp_def]

@[simp] theorem size_matrix (A : Matrix κ ι ℂ) :
    (matrix A).size = 2 * Fintype.card κ * Fintype.card ι := LinearDAG.size_matrix _
@[simp] theorem eval_scale (c : κ → ℂ) (x : κ → ℂ) :
    (scale c).eval x = fun i => c i * x i := by
  funext i
  simp [eval, scale, LinearDAG.eval_layer, Gate.eval, Function.comp_def]

@[simp] theorem eval_addPair (x : κ ⊕ κ → ℂ) :
    (addPair (κ := κ)).eval x = fun i => x (Sum.inl i) + x (Sum.inr i) := by
  funext i
  simp [eval, addPair, LinearDAG.eval_layer, Gate.eval, Function.comp_def]

theorem size_stackFin (n : ℕ) (C : Fin n → TypedDAG ι κ) :
    (stackFin n C).size = ∑ i, (C i).size := by
  induction n with
  | zero => simp [stackFin]
  | succ n ih => simp [stackFin, ih, Fin.sum_univ_succ]

theorem eval_stackFin (n : ℕ) (C : Fin n → TypedDAG ι κ) (x : ι → ℂ) :
    (stackFin n C).eval x = fun j => (C j.1).eval x j.2 := by
  induction n with
  | zero => funext ⟨i,j⟩; exact Fin.elim0 i
  | succ n ih =>
    funext ⟨i,j⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [stackFin, ih]

@[simp] theorem size_stack (C : τ → TypedDAG ι κ) :
    (stack C).size = ∑ i, (C i).size := by
  rw [stack, size_outputs, size_stackFin]
  exact (Fintype.equivFin τ).symm.sum_comp (fun i => (C i).size)
@[simp] theorem eval_stack (C : τ → TypedDAG ι κ) (x : ι → ℂ) :
    (stack C).eval x = fun j => (C j.1).eval x j.2 := by
  simp [stack, eval_stackFin, Function.comp_def]

@[simp] theorem size_parallel (C : TypedDAG ι κ) :
    (C.parallel τ).size = Fintype.card τ * C.size := by simp [parallel]
@[simp] theorem eval_parallel (C : TypedDAG ι κ) (x : τ × ι → ℂ) :
    (C.parallel τ).eval x = fun j => C.eval (fun i => x (j.1,i)) j.2 := by
  simp [parallel, Function.comp_def]

@[simp] theorem size_tensor (C : TypedDAG ι κ) (D : TypedDAG τ υ) :
    (C.tensor D).size = Fintype.card ι * D.size + Fintype.card υ * C.size := by
  simp [tensor]

theorem eval_tensor (C : TypedDAG ι κ) (D : TypedDAG τ υ)
    (A : Matrix κ ι ℂ) (B : Matrix υ τ ℂ)
    (hC : ∀ x, C.eval x = A.mulVec x) (hD : ∀ x, D.eval x = B.mulVec x)
    (x : ι × τ → ℂ) : (C.tensor D).eval x = (A ⊗ₖ B).mulVec x := by
  funext j
  simp only [tensor, eval_outputs, eval_comp, eval_inputs, eval_parallel, Function.comp_apply,
    Prod.swap, hC, hD, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end TypedDAG
end ExactFourier

end

section
/-! Charged scalar DAGs for the tensor-axis local maps used in the cascade. -/
namespace ExactFourier
open scoped Kronecker
namespace TypedDAG
variable {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ]

variable {α : Type} [Fintype α] [DecidableEq α]

theorem eval_tensorPower
    {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℂ) (k : ℕ) (x : TensorAxis.Space α k → ℂ) :
    (tensorPower A k).eval x = (TensorAxis.power A k).mulVec x := by
  induction k with
  | zero => simp [tensorPower,TensorAxis.power]
  | succ k ih =>
    exact eval_tensor _ _ _ _ ih (eval_matrix A) x

theorem size_tensorPower (A : Matrix α α ℂ) (k : ℕ) :
    (tensorPower A k).size = 2*Fintype.card α*k*Fintype.card α^k := by
  induction k with
  | zero => simp [tensorPower]
  | succ k ih =>
    rw [tensorPower,size_tensor,ih,size_matrix,TensorAxis.card_space,pow_succ]
    ring

end TypedDAG
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.ClearedCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Radix-two algebra used by the scalar-convolution bound in the missing main
proof. This is the ordinary O(n log n) support algorithm, NOT a main saving. -/
namespace ExactFourier.RadixTwo
open scoped BigOperators
open Polynomial

theorem sum_even_odd {R : Type*} [AddCommMonoid R] (n : ℕ) (f : Fin (n+n) → R) :
    ∑ i, f i = (∑ i : Fin n, f (evenIndex n i)) + ∑ i : Fin n, f (oddIndex n i) := by
  rw [← Fintype.sum_equiv (parityEquiv n) (fun p => f (parityEquiv n p)) f (fun _ => rfl)]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  exact Finset.sum_add_distrib

theorem power_even (ω : ℂ) (r j : ℕ) : ω^(r*(2*j)) = (ω^2)^(r*j) := by
  rw [← pow_mul]
  congr 1
  ring

theorem power_odd (ω : ℂ) (r j : ℕ) : ω^(r*(2*j+1)) = ω^r * (ω^2)^(r*j) := by
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

theorem evalAt_split (n : ℕ) (ω : ℂ) (x : Fin (n+n) → ℂ) (r : ℕ) :
    evalAt (n+n) ω x r = evalAt n (ω^2) (x ∘ evenIndex n) r +
      ω^r * evalAt n (ω^2) (x ∘ oddIndex n) r := by
  rw [evalAt, sum_even_odd]
  simp only [evenIndex, oddIndex, power_even, power_odd, Function.comp_apply, evalAt,
    Finset.mul_sum, mul_assoc]

theorem evalAt_periodic (n : ℕ) (ω : ℂ) (hω : ω^n=1) (x : Fin n → ℂ) (r : ℕ) :
    evalAt n ω x (r+n) = evalAt n ω x r := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_mul, pow_add, pow_mul ω n j.val, hω, one_pow, mul_one]

theorem square_period {n : ℕ} (ω : ℂ) (hω : ω^n = -1) : (ω^2)^n = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, hω]
  norm_num

/-- First and second frequency halves are the sum and difference butterfly. -/
theorem eval_split (n : ℕ) (ω : ℂ) (hω : ω^n = -1) (x : Fin (n+n) → ℂ) :
    eval (n+n) ω x = Fin.addCases
      (fun i => eval n (ω^2) (x ∘ evenIndex n) i + ω^i.val * eval n (ω^2) (x ∘ oddIndex n) i)
      (fun i => eval n (ω^2) (x ∘ evenIndex n) i - ω^i.val * eval n (ω^2) (x ∘ oddIndex n) i) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [eval, Fin.val_castAdd, Fin.addCases_left] using evalAt_split n ω x j.val
  · simp only [eval, Fin.val_natAdd, Fin.addCases_right]
    rw [Nat.add_comm n j.val, evalAt_split,
      evalAt_periodic n (ω^2) (square_period ω hω),
      evalAt_periodic n (ω^2) (square_period ω hω), pow_add, hω]
    ring

/-- Orthogonality of the exact n-th root evaluation matrix. -/
theorem orthogonality {n : ℕ} (hn : 0<n) (ω : ℂ) (hω : IsPrimitiveRoot ω n)
    (i k : Fin n) :
    (∑ j : Fin n, (ω⁻¹)^(i.val*j.val) * ω^(k.val*j.val)) =
      if i=k then (n : ℂ) else 0 := by
  have hn0 := Nat.ne_of_gt hn
  have hω0 := hω.ne_zero hn0
  have he : ∀ j : Fin n, (ω⁻¹)^(i.val*j.val) * ω^(k.val*j.val) =
      (ω^k.val / ω^i.val)^j.val := by
    intro j
    simp only [div_eq_mul_inv, mul_pow, inv_pow, pow_mul]
    rw [mul_comm]
  simp only [he]
  by_cases hik : i=k
  · subst k
    simp [hω0]
  · rw [ite_eq_right hik, Fin.sum_univ_eq_sum_range]
    have hne : ω^k.val / ω^i.val ≠ 1 := by
      intro h
      have hh : ω^k.val = ω^i.val := (div_eq_one_iff_eq (pow_ne_zero _ hω0)).mp h
      exact hik ((Fin.ext (hω.pow_inj k.isLt i.isLt hh)).symm)
    rw [geom_sum_eq hne]
    have hp : (ω^k.val / ω^i.val)^n = 1 := by
      rw [div_pow, ← pow_mul, Nat.mul_comm k.val n, pow_mul, hω.pow_eq_one,
        ← pow_mul, Nat.mul_comm i.val n, pow_mul, hω.pow_eq_one]
      simp
    rw [hp]
    simp

/-- The inverse FFT uses the inverse root and one scalar normalization. -/
theorem eval_inverse {n : ℕ} (hn : 0<n) (ω : ℂ) (hω : IsPrimitiveRoot ω n)
    (x : Fin n → ℂ) :
    eval n ω⁻¹ (eval n ω x) = fun i => (n : ℂ) * x i := by
  classical
  funext i
  simp only [eval, evalAt, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul]
  have ho : ∀ k : Fin n,
      (∑ j : Fin n, (ω⁻¹)^(i.val*j.val) * ω^(j.val*k.val)) =
        if i=k then (n : ℂ) else 0 := by
    intro k
    simpa only [Nat.mul_comm k.val] using orthogonality hn ω hω i k
  simp only [ho]
  simp

/-- Polynomial evaluation of the vector of coefficients is exactly the DFT. -/
theorem eval_ofFn (n : ℕ) (ω : ℂ) (x : Fin n → ℂ) (i : Fin n) :
    (Polynomial.ofFn n x).eval (ω^i.val) = eval n ω x i := by
  classical
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, eval, evalAt, pow_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]

/-- Transform, multiply by precomputed scalar evaluations, inverse transform.
The only degree condition is that the product is represented by fewer than n
coefficients, so there is no wraparound. -/
theorem convolution_formula {n : ℕ} (hn : 0<n) (ω : ℂ) (hω : IsPrimitiveRoot ω n)
    (f g : ℂ[X]) (hfg : (f*g).natDegree < n) :
    eval n ω⁻¹ (fun i => (n : ℂ)⁻¹ * f.eval (ω^i.val) * g.eval (ω^i.val)) =
      fun i => (f*g).coeff i.val := by
  classical
  let y : Fin n → ℂ := fun i => (f*g).coeff i.val
  have hy : Polynomial.ofFn n y = f*g := by
    ext j
    by_cases hj : j<n
    · simp [Polynomial.ofFn_coeff_eq_val_of_lt _ hj, y]
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  have hev : (fun i : Fin n => f.eval (ω^i.val) * g.eval (ω^i.val)) = eval n ω y := by
    funext i
    rw [← Polynomial.eval_mul, ← hy, eval_ofFn]
  have hscale : ∀ (z : Fin n → ℂ) (c : ℂ),
      eval n ω⁻¹ (fun i => c*z i) = fun i => c*eval n ω⁻¹ z i := by
    intro z c
    funext i
    simp only [eval, evalAt, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [mul_assoc (n : ℂ)⁻¹]
  have hev' (i : Fin n) : f.eval (ω^i.val) * g.eval (ω^i.val) = eval n ω y i :=
    congrFun hev i
  simp_rw [hev']
  rw [hscale, eval_inverse hn ω hω]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  funext i
  simp [y, hnC]

end ExactFourier.RadixTwo

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.FFTCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The uniform scalar-convolution main dependency. All operations are charged;
truncated series and constants may vary with the requested length. -/
namespace ExactFourier.ScalarConvolution
open Polynomial CoefficientTime RadixTwo
open scoped BigOperators

/-- Inversion commutes exactly with truncated scalar multiplication. -/
theorem truncMatrix_inv (t : ℕ) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    (truncMatrix t f)⁻¹ = truncMatrix t f⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← truncMatrix_mul, PowerSeries.mul_inv_cancel _ hf, truncMatrix_one]

end ExactFourier.ScalarConvolution

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.MonomialFeedback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Embedded
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem complement_ne_pair (i j : α) (hij : i≠j) (a : complement (pair i j hij)) :
    a.val≠i ∧ a.val≠j := by
  constructor
  · intro h; exact a.property ⟨0,h.symm⟩
  · intro h; apply a.property; exact ⟨1,by simpa using h.symm⟩

theorem pair_matrix (i j : α) (hij : i≠j) (s t : ℂ) :
    matrix (pair i j hij) (!![1,s;t,1] : Matrix (Fin 2) (Fin 2) ℂ)=
      1+Matrix.single i j s+Matrix.single j i t := by
  ext a b
  obtain ⟨a,rfl⟩ := (coordinates (pair i j hij)).surjective a
  obtain ⟨b,rfl⟩ := (coordinates (pair i j hij)).surjective b
  have he (a b : Fin 2⊕complement (pair i j hij)) :
      matrix (pair i j hij) (!![1,s;t,1]) (coordinates (pair i j hij) a)
      (coordinates (pair i j hij) b)=
      Matrix.fromBlocks (!![1,s;t,1]) 0 0 (1 : Matrix (complement (pair i j hij)) (complement (pair i j hij)) ℂ) a b := by
    simp [matrix,Matrix.reindex_apply]
  rw [he]
  rcases a with a|a <;> rcases b with b|b
  · fin_cases a <;> fin_cases b <;> simp [Matrix.single,hij,Ne.symm hij]
  · have ha := complement_ne_pair i j hij b
    fin_cases a <;> simp [Matrix.single,Ne.symm ha.1,Ne.symm ha.2]
  · have ha := complement_ne_pair i j hij a
    fin_cases b <;> simp [Matrix.single,ha.1,ha.2,Ne.symm ha.1,Ne.symm ha.2]
  · have ha := complement_ne_pair i j hij a
    have hb := complement_ne_pair i j hij b
    simp [Matrix.single,Matrix.one_apply,Ne.symm ha.1,Ne.symm ha.2,Ne.symm hb.1,Ne.symm hb.2,Subtype.ext_iff]

end ExactFourier.Embedded

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.MonomialTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier.MonomialMatrix
open scoped Kronecker
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem tensor
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {A : Matrix α α ℂ} {B : Matrix β β ℂ}
    (hA : MonomialMatrix A) (hB : MonomialMatrix B) : MonomialMatrix (A⊗ₖB) := by
  obtain ⟨σ,d,hd,ha⟩ := hA
  obtain ⟨τ,e,he,hb⟩ := hB
  refine ⟨σ.prodCongr τ,fun j => d j.1*e j.2,fun j => mul_ne_zero (hd _) (he _),?_⟩
  rintro ⟨i,k⟩ ⟨j,l⟩
  simp only [Matrix.kronecker_apply,ha,hb,Equiv.prodCongr_apply]
  split_ifs <;> simp_all

end ExactFourier.MonomialMatrix

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.MultiWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Embedded
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem card_complement
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : β ↪ α) :
    Fintype.card β+Fintype.card (complement e)=Fintype.card α := by
  simpa using Fintype.card_congr (coordinates e)

/-- Complete a prescribed active-tuple matching with untouched spectator wires. -/
theorem exists_completion (e : β ↪ α) (f : β ↪ γ)
    (hcard : Fintype.card α≤Fintype.card γ) :
    ∃ g : α ↪ γ,e.trans g=f := by
  have hc : Fintype.card (complement e)≤Fintype.card (complement f) := by
    have he := card_complement e
    have hf := card_complement f
    omega
  obtain ⟨h⟩ := (Function.Embedding.nonempty_of_card_le hc)
  let s : (β⊕complement e) ↪ (β⊕complement f) := Function.Embedding.sumMap (Function.Embedding.refl _) h
  let g := (coordinates e).symm.toEmbedding.trans (s.trans (coordinates f).toEmbedding)
  refine ⟨g,?_⟩
  ext i
  change coordinates f (s ((coordinates e).symm (e i)))=f i
  rw [← coordinates_inl e i,Equiv.symm_apply_apply]
  rfl

variable {π : Type} [Fintype π] [DecidableEq π]
 {δ ε : π→Type} [∀ p,Fintype (δ p)] [∀ p,Fintype (ε p)]
 [∀ p,DecidableEq (δ p)] [∀ p,DecidableEq (ε p)]

theorem matrix_sigmaEmbed (e : ∀ p,δ p ↪ ε p) (A : ∀ p,Matrix (δ p) (δ p) ℂ) :
    matrix (sigmaEmbed e) (Matrix.blockDiagonal' A)=
      Matrix.blockDiagonal' (fun p=>matrix (e p) (A p)) := by
  classical
  ext ⟨p,a⟩ ⟨q,b⟩
  by_cases hpq : p=q
  · subst q
    rw [Matrix.blockDiagonal'_apply_eq]
    by_cases ha : a∈Set.range (e p)
    · obtain ⟨a,rfl⟩ := ha
      by_cases hb : b∈Set.range (e p)
      · obtain ⟨b,rfl⟩ := hb
        change matrix (sigmaEmbed e) (Matrix.blockDiagonal' A)
          (sigmaEmbed e ⟨p,a⟩) (sigmaEmbed e ⟨p,b⟩)=_
        rw [matrix_on,Matrix.blockDiagonal'_apply_eq,matrix_on]
      · rw [matrix_off_col (e p) _ _ _ hb,matrix_off_col]
        · simp
        · rintro ⟨⟨q,b'⟩,h⟩
          have hq := congrArg Sigma.fst h
          change q=p at hq
          subst q
          exact hb ⟨b',eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
    · rw [matrix_off_row (e p) _ _ _ ha,matrix_off_row]
      · simp
      · rintro ⟨⟨q,a'⟩,h⟩
        have hq := congrArg Sigma.fst h
        change q=p at hq
        subst q
        exact ha ⟨a',eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hpq]
    by_cases ha : (⟨p,a⟩ : Σ p,ε p)∈Set.range (sigmaEmbed e)
    · obtain ⟨i,hi⟩ := ha
      by_cases hb : (⟨q,b⟩ : Σ p,ε p)∈Set.range (sigmaEmbed e)
      · obtain ⟨j,hj⟩ := hb
        rw [← hi,← hj,matrix_on]
        apply Matrix.blockDiagonal'_apply_ne
        have hi' := congrArg Sigma.fst hi
        have hj' := congrArg Sigma.fst hj
        change i.1=p at hi'
        change j.1=q at hj'
        simpa [hi',hj'] using hpq
      · rw [matrix_off_col _ _ _ _ hb]
        simp [hpq]
    · rw [matrix_off_row _ _ _ _ ha]
      simp [hpq]

end ExactFourier.Embedded

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.WordScheduling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier
variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

theorem reindex_comp
    {α : Type} {β : Type} {γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (e : α≃β) (f : β≃γ) (M : Matrix α α ℂ) :
 Matrix.reindex f f (Matrix.reindex e e M)=Matrix.reindex (e.trans f) (e.trans f) M := rfl

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PiTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.PiTensor
variable {ι : Type} [Fintype ι] [DecidableEq ι]
 {D : ι→Type} [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]

theorem mul
    {ι : Type} [Fintype ι] [DecidableEq ι] {D : ι → Type} [(i : ι) → Fintype (D i)] [(i : ι) → DecidableEq (D i)] (A B : ∀ i,Matrix (D i) (D i) ℂ) : matrix (A*B)=matrix A*matrix B := by
 classical
 ext x y
 simp only [matrix,Pi.mul_apply,Matrix.mul_apply]
 simp_rw [← Finset.prod_mul_distrib]
 exact Fintype.prod_sum fun i j=>A i (x i) j*B i j (y i)

end ExactFourier.PiTensor

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.LiveSectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Packing
variable {α : Type} [Fintype α] [DecidableEq α]

theorem embeddedCall_eq {q w : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (e : Fin q↪Fin w) :
 embeddedCall A e=Embedded.matrix e A := by
 classical
 ext i j
 by_cases hi : ∃ a,e a=i
 · obtain ⟨a,rfl⟩ := hi
   by_cases hj : ∃ b,e b=j
   · obtain ⟨b,rfl⟩ := hj
     simp [embeddedCall,e.injective.eq_iff,Embedded.matrix_on]
   · rw [Embedded.matrix_off_col e A _ _ (by simpa [Set.mem_range] using hj)]
     have hij : e a≠j := fun h=>hj ⟨a,h⟩
     simp [embeddedCall,e.injective.eq_iff,hij]
     exact Finset.sum_eq_zero (fun b _=>by simp [show e b≠j from fun h=>hj ⟨b,h⟩])
 · rw [Embedded.matrix_off_row e A _ _ (by simpa [Set.mem_range] using hi)]
   have hz : (∑ a : Fin q,∑ b : Fin q,if e a=i then (if e b=j then A a b else 0) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro a _
    simp [show e a≠i from fun h=>hi ⟨a,h⟩]
   simp only [embeddedCall,hz,hi,not_false_eq_true,and_true,zero_add]

end ExactFourier.Packing

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.GraphBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier

namespace Layered
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
theorem unit {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) : IsUnit M := by
 induction h with
 | identity => exact isUnit_one
 | mono M hM => exact hM.unit M
 | pair M hM => exact hM
 | mul hM hN ihM ihN => exact ihM.mul ihN
 | reindex f hM ih => exact TensorTools.unit_reindex _ _ ih
 | sum hM hN ihM ihN => exact Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨ihM,ihN⟩
 | weaken h hde ih => exact ih

theorem parallel {M : Matrix α α ℂ} {N : Matrix β β ℂ} {d e : ℕ}
 (hM : Layered M d) (hN : Layered N e) :
 Layered (Matrix.fromBlocks M 0 0 N) (max d e) :=
 (hM.weaken (le_max_left _ _)).sum (hN.weaken (le_max_right _ _))

 theorem embed (e : α↪β) {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) :
 Layered (Embedded.matrix e M) d :=
 (h.sum (Layered.identity.weaken (Nat.zero_le d))).reindex (Embedded.coordinates e)
end Layered
end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.CircuitCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace CircuitCost
variable {α β : Type} [Fintype α] [Fintype β]

theorem optimal (M : Matrix β α ℂ) : ∃ C : TypedDAG α β,C.size=cost M ∧ Realizes C M := by
 classical
 exact Nat.find_spec (exists_size M)

theorem cost_le (M : Matrix β α ℂ) (C : TypedDAG α β) (hC : Realizes C M) : cost M≤C.size := by
 classical
 exact Nat.find_min' (exists_size M) ⟨C,rfl,hC⟩

variable [DecidableEq α] [DecidableEq β]
@[simp] theorem cost_one : cost (1 : Matrix α α ℂ)=0 := by
 apply Nat.eq_zero_of_le_zero
 have hh := cost_le (1 : Matrix α α ℂ) TypedDAG.identity (by intro x; simp)
 exact hh

theorem cost_mul
    {α : Type} [Fintype α] [DecidableEq α] (M N : Matrix α α ℂ) : cost (M*N)≤cost M+cost N := by
 obtain ⟨C,hC,hc⟩ := optimal M
 obtain ⟨D,hD,hd⟩ := optimal N
 have hh := cost_le (M*N) (C.comp D) (by
  intro x; rw [TypedDAG.eval_comp,hc,hd,Matrix.mulVec_mulVec])
 simpa [hC,hD,Nat.add_comm] using hh

theorem cost_reindex_le
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : α≃β) (M : Matrix α α ℂ) :
 cost (Matrix.reindex e e M)≤cost M := by
 obtain ⟨C,hC,hc⟩ := optimal M
 have hh := cost_le (Matrix.reindex e e M) ((C.inputs e).outputs e.symm) (by
  intro x
  ext j
  simp only [TypedDAG.eval_outputs,TypedDAG.eval_inputs,hc,Function.comp_apply,Matrix.mulVec,dotProduct,
   Matrix.reindex_apply,Matrix.submatrix_apply]
  simpa only [Equiv.symm_apply_apply] using e.sum_comp (fun i=>M (e.symm j) (e.symm i)*x i))
 simpa [hC] using hh

theorem cost_reindex (e : α≃β) (M : Matrix α α ℂ) : cost (Matrix.reindex e e M)=cost M := by
 apply le_antisymm (cost_reindex_le e M)
 have hh := cost_reindex_le e.symm (Matrix.reindex e e M)
 have he : Matrix.reindex e.symm e.symm (Matrix.reindex e e M)=M := by ext i j; simp [Matrix.reindex_apply]
 rw [he] at hh
 exact hh

theorem cost_monomial (M : Matrix α α ℂ) (hM : MonomialMatrix M) : cost M≤Fintype.card α := by
 obtain ⟨s,d,hd,hs⟩ := hM
 have hh := cost_le M ((TypedDAG.scale d).outputs s.symm) (by
  intro x
  ext i
  simp only [TypedDAG.eval_outputs,TypedDAG.eval_scale,Function.comp_apply,Matrix.mulVec,dotProduct]
  symm
  rw [Finset.sum_eq_single (s.symm i)]
  · simp [hs]
  · intro j hj hji
    have h : i≠s j := by intro he; exact hji (by rw [he,s.symm_apply_apply])
    simp [hs,h]
  · simp)
 simpa using hh

theorem cost_sum
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (N : Matrix β β ℂ) :
 cost (Matrix.fromBlocks M 0 0 N)≤cost M+cost N := by
 obtain ⟨C,hC,hc⟩ := optimal M
 obtain ⟨D,hD,hd⟩ := optimal N
 have hh := cost_le (Matrix.fromBlocks M 0 0 N) ((C.inputs Sum.inl).fanout (D.inputs Sum.inr)) (by
  intro x
  ext i
  cases i <;> simp [TypedDAG.eval_fanout,TypedDAG.eval_inputs,hc,hd,Matrix.mulVec,dotProduct,Fintype.sum_sum_type])
 simpa [hC,hD] using hh

theorem cost_tensor
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (N : Matrix β β ℂ) :
 cost (M⊗ₖN)≤Fintype.card β*cost M+Fintype.card α*cost N := by
 obtain ⟨C,hC,hc⟩ := optimal M
 obtain ⟨D,hD,hd⟩ := optimal N
 have hh := cost_le (M⊗ₖN) (C.tensor D) (TypedDAG.eval_tensor C D M N hc hd)
 simpa [hC,hD,Nat.add_comm] using hh
end CircuitCost
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier.Layered

theorem blocks_fin (n : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (d : ℕ) (hM : ∀ i,Layered (M i) d) :
 Layered (Matrix.blockDiagonal' M) d := by
 induction n with
 | zero =>
  have he : Matrix.blockDiagonal' M=(1 : Matrix (Σ i,D i) (Σ i,D i) ℂ) := by
   ext ⟨i,x⟩; exact Fin.elim0 i
  rw [he]
  exact identity.weaken (Nat.zero_le d)
 | succ n ih =>
  have h := (hM 0).sum (ih (fun i=>D i.succ) (fun i=>M i.succ) (fun i=>hM i.succ))
  have he : Matrix.reindex (sigmaFinSucc D).symm (sigmaFinSucc D).symm
   (Matrix.fromBlocks (M 0) 0 0 (Matrix.blockDiagonal' (fun i : Fin n=>M i.succ)))=
   Matrix.blockDiagonal' M := by
   ext ⟨i,x⟩ ⟨j,y⟩
   refine Fin.cases ?_ (fun i=>?_) i x <;> intro x <;>
    refine Fin.cases ?_ (fun j=>?_) j y <;> intro y <;>
    simp [Matrix.reindex_apply,sigmaFinSucc,Matrix.blockDiagonal'_apply,Fin.succ_ne_zero,eq_comm]
  rw [← he]
  exact h.reindex _

theorem blocks {σ : Type} [Fintype σ] [DecidableEq σ]
 (D : σ→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (d : ℕ) (hM : ∀ i,Layered (M i) d) :
 Layered (Matrix.blockDiagonal' M) d := by
 let e := (Fintype.equivFin σ).symm
 let f : (Σ i : Fin (Fintype.card σ),D (e i))≃(Σ i,D i) := Equiv.sigmaCongrLeft e
 have h := blocks_fin (Fintype.card σ) (fun i=>D (e i)) (fun i=>M (e i)) d (fun i=>hM (e i))
 have he : Matrix.reindex f f (Matrix.blockDiagonal' (fun i=>M (e i)))=Matrix.blockDiagonal' M := by
  ext x y
  obtain ⟨⟨i,x⟩,rfl⟩ := f.surjective x
  obtain ⟨⟨j,y⟩,rfl⟩ := f.surjective y
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  change Matrix.blockDiagonal' (fun i=>M (e i)) ⟨i,x⟩ ⟨j,y⟩ =
   Matrix.blockDiagonal' M ⟨e i,x⟩ ⟨e j,y⟩
  by_cases hij : i=j
  · subst j; simp [Matrix.blockDiagonal'_apply]
  · simp [Matrix.blockDiagonal'_apply,hij,e.injective.ne hij]
 rw [← he]
 exact h.reindex f

theorem blockDiagonal {α σ : Type} [Fintype α] [Fintype σ] [DecidableEq α] [DecidableEq σ]
 (M : σ→Matrix α α ℂ) (d : ℕ) (hM : ∀ i,Layered (M i) d) :
 Layered (Matrix.blockDiagonal M) d := by
 let e : (Σ _ : σ,α)≃(α×σ) := (Equiv.sigmaEquivProd σ α).trans (Equiv.prodComm σ α)
 have he : Matrix.reindex e e (Matrix.blockDiagonal' M)=Matrix.blockDiagonal M := by
  ext ⟨x,i⟩ ⟨y,j⟩
  simp [e,Matrix.reindex_apply,Matrix.blockDiagonal'_apply,Matrix.blockDiagonal]
 rw [← he]
 exact (blocks (fun _=>α) M d hM).reindex e

end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem two_reindex {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) (e f : α≃β) :
 Layered (Matrix.reindex e f M) (d+1) := by
 have hh := (h.reindex e).mul (Layered.mono (permM (f.symm.trans e))
   (permM_monomial _))
 have he : Matrix.reindex e e M * permM (f.symm.trans e)=Matrix.reindex e f M := by
  ext i j
  simp [mul_permM_apply,Matrix.reindex_apply]
 rw [he] at hh
 exact hh
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier

namespace Round
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
theorem one : Round (1 : Matrix α α ℂ) := mono _ MonomialMatrix.one

theorem joint_length
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : List (Matrix α α ℂ)) (N : List (Matrix β β ℂ)) (h : M.length=N.length) :
 (joint M N).length=M.length := by simp [joint,h]

theorem joint_prod (M : List (Matrix α α ℂ)) (N : List (Matrix β β ℂ)) (h : M.length=N.length) :
 (joint M N).prod=Matrix.fromBlocks M.prod 0 0 N.prod := by
 induction M generalizing N with
 | nil =>
  have hn : N=[] := List.length_eq_zero_iff.mp h.symm
  subst N
  simp [joint,Matrix.fromBlocks_one]
 | cons a M ih =>
  cases N with
  | nil => simp at h
  | cons b N =>
   simp only [joint,List.zipWith_cons_cons,List.prod_cons]
   rw [show (List.zipWith (fun X Y=>Matrix.fromBlocks X 0 0 Y) M N).prod=
    Matrix.fromBlocks M.prod 0 0 N.prod from ih N (by simpa using h)]
   simp [Matrix.fromBlocks_multiply]

theorem joint_all
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : List (Matrix α α ℂ)) (N : List (Matrix β β ℂ))
 (P : Matrix α α ℂ → Prop) (Q : Matrix β β ℂ → Prop)
 (R : Matrix (α⊕β) (α⊕β) ℂ → Prop)
 (hM : ∀ X∈M,P X) (hN : ∀ X∈N,Q X)
 (hR : ∀ X Y,P X → Q Y → R (Matrix.fromBlocks X 0 0 Y)) : ∀ X∈joint M N,R X := by
 induction M generalizing N with
 | nil => simp [joint]
 | cons a M ih =>
  cases N with
  | nil => simp [joint]
  | cons b N =>
   simp only [joint,List.zipWith_cons_cons,List.mem_cons]
   intro X hX
   rcases hX with rfl|hX
   · exact hR a b (hM a (by simp)) (hN b (by simp))
   · exact ih N (fun X hX=>hM X (by simp [hX]))
       (fun X hX=>hN X (by simp [hX])) X hX

theorem joint_rounds (M : List (Matrix α α ℂ)) (N : List (Matrix β β ℂ))
 (hM : ∀ X∈M,Round X) (hN : ∀ X∈N,Round X) : ∀ X∈joint M N,Round X :=
 joint_all M N Round Round Round hM hN (fun _ _ h h' => h.sum h')
end Round

namespace Layered
variable {α : Type} [Fintype α] [DecidableEq α]
/-- Finite lists of simultaneous rounds, with identity padding and no change of width. -/
theorem rounds {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) :
 ∃ L : List (Matrix α α ℂ),L.length=d ∧ L.prod=M ∧ ∀ X∈L,Round X := by
 induction h with
 | identity => exact ⟨[],rfl,rfl,by simp⟩
 | mono M hM => exact ⟨[M],rfl,by simp,by simpa using Round.mono M hM⟩
 | pair M hM => exact ⟨[M],rfl,by simp,by simpa using Round.pair M hM⟩
 | mul hM hN ihM ihN =>
  obtain ⟨L,hL,hp,hr⟩ := ihM
  obtain ⟨K,hK,hq,hs⟩ := ihN
  refine ⟨L++K,by simp [hL,hK],by simp [hp,hq],?_⟩
  intro X hX
  rcases List.mem_append.mp hX with hX|hX
  · exact hr X hX
  · exact hs X hX
 | reindex e hM ih =>
  obtain ⟨L,hL,hp,hr⟩ := ih
  refine ⟨L.map (Matrix.reindex e e),by simp [hL],?_,?_⟩
  · rw [← hp]
    exact (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom.map_list_prod L |>.symm
  · intro X hX
    obtain ⟨Y,hY,rfl⟩ := List.mem_map.mp hX
    exact (hr Y hY).reindex e
 | sum hM hN ihM ihN =>
  obtain ⟨L,hL,hp,hr⟩ := ihM
  obtain ⟨K,hK,hq,hs⟩ := ihN
  refine ⟨Round.joint L K,(Round.joint_length L K (hL.trans hK.symm)).trans hL,?_,Round.joint_rounds L K hr hs⟩
  rw [Round.joint_prod L K (hL.trans hK.symm),hp,hq]
 | @weaken _ _ _ _ d e h hde ih =>
  obtain ⟨L,hL,hp,hr⟩ := ih
  refine ⟨L++List.replicate (e-d) 1,by simp [hL]; omega,by simp [hp],?_⟩
  intro X hX
  rcases List.mem_append.mp hX with hX|hX
  · exact hr X hX
  · have hx : X=1 := (List.mem_replicate.mp hX).2
    rw [hx]; exact Round.one
end Layered
end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.TensorCostAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace CircuitCost
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem tensor_comm (M : Matrix α α ℂ) (N : Matrix β β ℂ) : cost (M⊗ₖN)=cost (N⊗ₖM) := by
 have he : Matrix.reindex (Equiv.prodComm α β) (Equiv.prodComm α β) (M⊗ₖN)=N⊗ₖM := by
  ext i j; exact mul_comm _ _
 rw [← he,cost_reindex]

theorem tensor_assoc (M : Matrix α α ℂ) (N : Matrix β β ℂ) (P : Matrix γ γ ℂ) :
 cost ((M⊗ₖN)⊗ₖP)=cost (M⊗ₖ(N⊗ₖP)) := by
 have he : Matrix.reindex (Equiv.prodAssoc α β γ) (Equiv.prodAssoc α β γ) ((M⊗ₖN)⊗ₖP)=M⊗ₖ(N⊗ₖP) := by
  ext i j; exact mul_assoc _ _ _
 rw [← he,cost_reindex]

theorem tensor_sum (M : Matrix α α ℂ) (N : Matrix β β ℂ) (P : Matrix γ γ ℂ) :
 cost (Matrix.fromBlocks M 0 0 N⊗ₖP)≤cost (M⊗ₖP)+cost (N⊗ₖP) := by
 have he : Matrix.reindex (Equiv.sumProdDistrib α β γ) (Equiv.sumProdDistrib α β γ)
   (Matrix.fromBlocks M 0 0 N⊗ₖP)=Matrix.fromBlocks (M⊗ₖP) 0 0 (N⊗ₖP) := by
  ext i j; cases i <;> cases j <;> simp [Matrix.reindex_apply,Equiv.sumProdDistrib]
 rw [← cost_reindex (Equiv.sumProdDistrib α β γ),he]
 exact cost_sum _ _

theorem tensor_one_le (M : Matrix α α ℂ) : cost (M⊗ₖ(1 : Matrix β β ℂ))≤Fintype.card β*cost M := by
 simpa using cost_tensor M (1 : Matrix β β ℂ)

theorem tensor_punit (M : Matrix α α ℂ) : cost (M⊗ₖ(1 : Matrix PUnit PUnit ℂ))=cost M := by
 have he : Matrix.reindex (Equiv.prodPUnit α) (Equiv.prodPUnit α) (M⊗ₖ(1 : Matrix PUnit PUnit ℂ))=M := by
  ext i j; simp [Matrix.reindex_apply]
 exact (cost_reindex (Equiv.prodPUnit α) _).symm.trans (congrArg cost he)

theorem tensor_exchange (M : Matrix α α ℂ) (N : Matrix β β ℂ) (P : Matrix γ γ ℂ) :
 cost ((M⊗ₖN)⊗ₖP)=cost ((M⊗ₖP)⊗ₖN) := by
 let e : ((α×β)×γ)≃((α×γ)×β) :=
  ((Equiv.prodAssoc α β γ).trans ((Equiv.refl α).prodCongr (Equiv.prodComm β γ))).trans (Equiv.prodAssoc α γ β).symm
 have he : Matrix.reindex e e ((M⊗ₖN)⊗ₖP)=(M⊗ₖP)⊗ₖN := by
  ext i j
  change (M i.1.1 j.1.1*N i.2 j.2)*P i.1.2 j.1.2=(M i.1.1 j.1.1*P i.1.2 j.1.2)*N i.2 j.2
  ring
 exact (cost_reindex e _).symm.trans (congrArg cost he)

end CircuitCost

namespace TensorAxis
variable {α : Type} [Fintype α] [DecidableEq α]

theorem power_entries
    {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) (k : ℕ) (x y : Space α k) :
 power M k x y=∏ i : Fin k,M (funCoordinates (α := α) k x i) (funCoordinates (α := α) k y i) := by
 induction k with
 | zero => simp [power,funCoordinates]
 | succ k ih =>
  change power M k x.1 y.1*M x.2 y.2=_
  rw [Fin.prod_univ_castSucc,ih]
  simp [funCoordinates]

theorem power_fun_reindex (M : Matrix α α ℂ) (k : ℕ) :
 Matrix.reindex (funCoordinates (α := α) k) (funCoordinates (α := α) k) (power M k)=
  fun x y=>∏i,M (x i) (y i) := by
 ext x y
 simp [Matrix.reindex_apply,power_entries]

theorem power_append
    {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) (k l : ℕ) :
 Matrix.reindex (appendCoordinates (α := α) k l) (appendCoordinates (α := α) k l) (power M (k+l))=
 power M k⊗ₖpower M l := by
 induction l with
 | zero => ext i j; simp [appendCoordinates,power,Matrix.reindex_apply]
 | succ l ih =>
  ext i j
  change power M (k+l) ((appendCoordinates (α := α) k l).symm (i.1,i.2.1))
   ((appendCoordinates (α := α) k l).symm (j.1,j.2.1))*M i.2.2 j.2.2=_
  have h := congrFun (congrFun ih (i.1,i.2.1)) (j.1,j.2.1)
  dsimp [Matrix.reindex_apply] at h
  rw [h]
  exact mul_assoc _ _ _

theorem power_reindex {β : Type} [Fintype β] [DecidableEq β] (e : α≃β) (M : Matrix α α ℂ) (k : ℕ) :
 ∃ f : Space α k≃Space β k,Matrix.reindex f f (power M k)=power (Matrix.reindex e e M) k := by
 induction k with
 | zero => exact ⟨Equiv.refl _,rfl⟩
 | succ k ih =>
  obtain ⟨f,hf⟩ := ih
  refine ⟨f.prodCongr e,?_⟩
  change Matrix.reindex (f.prodCongr e) (f.prodCongr e) (Matrix.kronecker (power M k) M)=_
  rw [ExactFourier.reindex_tensor,hf]
  rfl
end TensorAxis
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier.Amplification

theorem avg_mono {p : ℝ} (hp : 0≤p) (hp1 : p≤1) (f g : ℕ→ℝ) (j r : ℕ)
 (h : ∀ i, r ≤ i → i ≤ r+j → f i ≤ g i) : avg p f j r≤avg p g j r := by
 induction j generalizing r with
 | zero => exact h r le_rfl (by omega)
 | succ j ih =>
  dsimp only [avg]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hp
    apply ih (r+1)
    intro i hi hj; exact h i (by omega) (by omega)
  · apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply ih r
    intro i hi hj; exact h i hi (by omega)

theorem avg_const_mul (p C : ℝ) (f : ℕ→ℝ) (j r : ℕ) :
 avg p (fun i=>C*f i) j r=C*avg p f j r := by
 induction j generalizing r with
 | zero => rfl
 | succ j ih => simp only [avg,ih]; ring

theorem avg_rpow {p a : ℝ} (hp : 0≤p) (hp1 : p≤1) (ha : 0≤a) (ha1 : a≤1) (j r : ℕ) :
 avg p (fun i=>(i+1 : ℝ)^a) j r≤((r : ℝ)+p*j+1)^a := by
 induction j generalizing r with
 | zero => simp [avg]
 | succ j ih =>
  have hc := (Real.concaveOn_rpow ha ha1).2
   (show (r+1 : ℝ)+p*j+1∈Set.Ici (0:ℝ) from (show (0:ℝ) ≤ (r+1 : ℝ)+p*j+1 by positivity))
   (show (r : ℝ)+p*j+1∈Set.Ici (0:ℝ) from (show (0:ℝ) ≤ (r : ℝ)+p*j+1 by positivity))
   hp (show 0≤1-p by linarith) (by ring : p+(1-p)=1)
  simp only [smul_eq_mul] at hc
  have he : p*((r+1 : ℝ)+p*j+1)+(1-p)*((r : ℝ)+p*j+1)=(r : ℝ)+p*(j+1)+1 := by ring
  rw [he] at hc
  dsimp only [avg]
  have h1 := mul_le_mul_of_nonneg_left (ih (r+1)) hp
  have h2 := mul_le_mul_of_nonneg_left (ih r) (show 0≤1-p by linarith)
  push_cast at h1 ⊢
  exact (add_le_add h1 h2).trans hc
end ExactFourier.Amplification

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Amplification
open CircuitCost TensorAxis

variable {α δ : Type} [Fintype α] [Fintype δ] [DecidableEq α] [DecidableEq δ]

theorem cost_sectors (A : Matrix α α ℂ) (j r : ℕ) :
 cost (power (Matrix.fromBlocks A 0 0 (1 : Matrix δ δ ℂ)) j⊗ₖpower A r)≤
 sectorCost (fun k=>cost (power A k)) (Fintype.card δ) j r := by
 induction j generalizing r with
 | zero =>
  change cost ((1 : Matrix PUnit PUnit ℂ)⊗ₖpower A r)≤_
  rw [tensor_comm,tensor_punit]
  rfl
 | succ j ih =>
  let B := Matrix.fromBlocks A 0 0 (1 : Matrix δ δ ℂ)
  change cost ((power B j⊗ₖB)⊗ₖpower A r)≤_
  rw [tensor_exchange,tensor_comm]
  have h := tensor_sum A (1 : Matrix δ δ ℂ) (power B j⊗ₖpower A r)
  rw [tensor_comm A _,tensor_assoc,tensor_comm (1 : Matrix δ δ ℂ) _] at h
  have h1 := ih (r+1)
  have h2 := (tensor_one_le (β := δ) (power B j⊗ₖpower A r)).trans
    (Nat.mul_le_mul_left (Fintype.card δ) (ih r))
  exact h.trans (Nat.add_le_add h1 h2)

theorem cost_call_power (A : Matrix α α ℂ) (e : α ↪ δ) (j : ℕ) :
 cost (power (Embedded.matrix e A) j)≤
 sectorCost (fun k=>cost (power A k)) (Fintype.card (Embedded.complement e)) j 0 := by
 obtain ⟨f,hf⟩ := power_reindex (Embedded.coordinates e)
   (Matrix.fromBlocks A 0 0 (1 : Matrix (Embedded.complement e) (Embedded.complement e) ℂ)) j
 have h := cost_sectors (δ := Embedded.complement e) A j 0
 rw [power,tensor_punit] at h
 change cost (power (Matrix.reindex (Embedded.coordinates e) (Embedded.coordinates e) _) j) ≤ _
 rw [← hf,cost_reindex]
 exact h

theorem sectorCost_avg (l : ℕ→ℕ) {q s : ℕ} (hq : 0<q) (j r : ℕ) :
 (sectorCost l s j r : ℝ)=(q : ℝ)^r*(q+s : ℝ)^j *
 avg ((q : ℝ)/(q+s)) (fun i=>(l i : ℝ)/(q : ℝ)^i) j r := by
 have hq' : (q : ℝ)≠0 := by positivity
 have hQ : (q+s : ℝ)≠0 := by positivity
 induction j generalizing r with
 | zero => simp only [sectorCost,avg,pow_zero,mul_one]; field_simp
 | succ j ih =>
  simp only [sectorCost,Nat.cast_add,Nat.cast_mul,ih,avg,pow_succ]
  field_simp
  ring
end ExactFourier.Amplification

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace TensorAxis
variable {α : Type} [Fintype α] [DecidableEq α]
theorem power_group (A : Matrix α α ℂ) (b j : ℕ) :
 ∃ e : Space α (b*j)≃Space (Space α b) j,
 Matrix.reindex e e (power A (b*j))=power (power A b) j := by
 induction j with
 | zero => exact ⟨Equiv.refl _,rfl⟩
 | succ j ih =>
  obtain ⟨e,he⟩ := ih
  rw [Nat.mul_succ]
  refine ⟨(appendCoordinates (α := α) (b*j) b).trans (e.prodCongr (Equiv.refl _)),?_⟩
  rw [← reindex_comp,power_append]
  change Matrix.reindex (e.prodCongr (Equiv.refl _)) (e.prodCongr (Equiv.refl _))
   (Matrix.kronecker (power A (b*j)) (power A b))=_
  rw [reindex_tensor,he]
  rfl

theorem power_monomial (A : Matrix α α ℂ) (hA : MonomialMatrix A) (j : ℕ) :
 MonomialMatrix (power A j) := by
 induction j with
 | zero => exact MonomialMatrix.one
 | succ j ih => exact ih.tensor hA

theorem source_power_reindex {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (b : ℕ) :
 Matrix.reindex ((funCoordinates (α := Fin q) b).trans (tensorCoordinates q b).symm)
  ((funCoordinates (α := Fin q) b).trans (tensorCoordinates q b).symm) (power A b)=tensorPower A b := by
 rw [← reindex_comp,power_fun_reindex]
 ext i j
 rfl
end TensorAxis

namespace Amplification
open CircuitCost TensorAxis

theorem cost_group {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℂ) (b j : ℕ) :
 cost (power A (b*j))=cost (power (power A b) j) := by
 obtain ⟨e,he⟩ := power_group A b j
 rw [← he,cost_reindex]

theorem cost_reindexed_power {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
 (e : α≃β) (A : Matrix α α ℂ) (j : ℕ) :
 cost (power (Matrix.reindex e e A) j)=cost (power A j) := by
 obtain ⟨f,hf⟩ := power_reindex e A j
 rw [← hf,cost_reindex]

theorem complement_card {q Q : ℕ} (e : Fin q↪Fin Q) : Fintype.card (Embedded.complement e)=Q-q := by
 have hh := Fintype.card_congr (Embedded.coordinates e)
 simp only [Fintype.card_sum,Fintype.card_fin] at hh
 omega

theorem cost_word_power {q Q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ)
 (W : List (WordStep A Q)) (j : ℕ) :
 cost (power (wordMatrix W) j)≤W.length*Q^j+
 wordCalls W*sectorCost (fun k=>cost (power A k)) (Q-q) j 0 := by
 induction W with
 | nil => simp [wordMatrix,wordCalls]
 | cons s W ih =>
  have he : wordMatrix (s::W)=wordMatrix W*s.matrix := by
   simp [wordMatrix,List.prod_append]
  rw [he,← mul_power]
  have h := cost_mul (power (wordMatrix W) j) (power s.matrix j)
  apply h.trans
  cases s with
  | monomial M hM =>
   have hm := cost_monomial (power M j) (power_monomial M hM j)
   simp only [card_space,Fintype.card_fin] at hm
   simp only [WordStep.matrix] at h ⊢
   simp only [List.length_cons,wordCalls,List.map_cons,List.sum_cons,WordStep.calls,zero_add]
   change _≤(W.length+1)*Q^j+wordCalls W*sectorCost _ _ _ _
   nlinarith
  | call e =>
   have hc := cost_call_power A e j
   rw [complement_card] at hc
   simp only [WordStep.matrix,Packing.embeddedCall_eq]
   simp only [List.length_cons,wordCalls,List.map_cons,List.sum_cons,WordStep.calls]
   change _≤(W.length+1)*Q^j+(1+wordCalls W)*sectorCost _ _ _ _
   exact (Nat.add_le_add ih hc).trans (by simp only [Nat.add_mul,one_mul]; omega)
end Amplification
end ExactFourier

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier.Amplification
open CircuitCost TensorAxis

theorem normalized_add {q : ℕ} (hq : 0<q) (A : Matrix (Fin q) (Fin q) ℂ) (k l : ℕ) :
 normalizedCost A (k+l)≤normalizedCost A k+normalizedCost A l := by
 have hqR : (q : ℝ) ≠ 0 := by positivity
 have hc := cost_tensor (power A k) (power A l)
 rw [← power_append, cost_reindex] at hc
 simp only [card_space,Fintype.card_fin] at hc
 have hcR : (cost (power A (k+l)) : ℝ) ≤
   (q : ℝ)^l*(cost (power A k) : ℝ)+(q : ℝ)^k*(cost (power A l) : ℝ) := by exact_mod_cast hc
 dsimp only [normalizedCost]
 rw [div_le_iff₀ (by positivity : (0 : ℝ)<(q : ℝ)^(k+l))]
 have he : (cost (power A k) / (q : ℝ)^k + cost (power A l) / (q : ℝ)^l) * (q : ℝ)^(k+l) =
    (q : ℝ)^l*cost (power A k)+(q : ℝ)^k*cost (power A l) := by
  rw [pow_add]; field_simp
 rw [he]
 exact hcR

theorem normalized_linear {q : ℕ} (hq : 0<q) (A : Matrix (Fin q) (Fin q) ℂ) (k : ℕ) :
 normalizedCost A k≤2*q*k := by
 have hc := cost_le (power A k) (TypedDAG.tensorPower A k) (TypedDAG.eval_tensorPower A k)
 rw [TypedDAG.size_tensorPower,Fintype.card_fin] at hc
 have hcR : (cost (power A k) : ℝ)≤2*q*k*(q : ℝ)^k := by exact_mod_cast hc
 exact (div_le_iff₀ (by positivity : (0 : ℝ)<(q : ℝ)^k)).mpr hcR

theorem normalized_word {q b : ℕ} (hq : 0<q) (A : Matrix (Fin q) (Fin q) ℂ)
 (hb : 1≤b) (W : List (WordStep A (q^b))) (hW : wordMatrix W=tensorPower A b) (j : ℕ) :
 normalizedCost A (b*j) ≤ W.length+(wordCalls W : ℝ)*
 avg ((q : ℝ)/(q^b : ℕ)) (normalizedCost A) j 0 := by
 have hqQ : q≤q^b := Nat.le_self_pow (by omega : b≠0) q
 have hc := cost_word_power A W j
 rw [hW,← source_power_reindex,cost_reindexed_power,← cost_group] at hc
 have he : q+(q^b-q)=q^b := by omega
 have ha := sectorCost_avg (fun k=>cost (power A k)) (s := q^b-q) hq j 0
 simp only [pow_zero,one_mul] at ha
 have heR : (q : ℝ)+(q^b-q : ℕ)=(q^b : ℕ) := by exact_mod_cast he
 rw [heR] at ha
 have hcR : (cost (power A (b*j)) : ℝ)≤W.length*((q^b : ℕ) : ℝ)^j+
 (wordCalls W : ℝ)*(sectorCost (fun k=>cost (power A k)) (q^b-q) j 0 : ℝ) := by exact_mod_cast hc
 rw [ha] at hcR
 change (cost (power A (b*j)) : ℝ)/(q : ℝ)^(b*j) ≤
   W.length+(wordCalls W : ℝ)*avg ((q : ℝ)/(q^b : ℕ))
   (fun i => (cost (power A i) : ℝ)/(q : ℝ)^i) j 0
 rw [div_le_iff₀ (by positivity : (0 : ℝ)<(q : ℝ)^(b*j))]
 push_cast at hcR ⊢
 rw [pow_mul]
 nlinarith only [hcR]

theorem normalized_recurrence {q b : ℕ} (hq : 0<q) (A : Matrix (Fin q) (Fin q) ℂ)
 (hb : 1≤b) (W : List (WordStep A (q^b))) (hW : wordMatrix W=tensorPower A b) (k : ℕ) :
 normalizedCost A k ≤ (W.length+2*q*b : ℝ)+(wordCalls W : ℝ)*
 avg ((q : ℝ)/(q^b : ℕ)) (normalizedCost A) (k/b) 0 := by
 have hsum := normalized_add hq A (b*(k/b)) (k%b)
 rw [Nat.mul_comm b (k/b),Nat.div_add_mod'] at hsum
 rw [Nat.mul_comm (k/b) b] at hsum
 have hw := normalized_word hq A hb W hW (k/b)
 have hr := normalized_linear hq A (k%b)
 have hmod : ((k%b : ℕ) : ℝ)≤b := by exact_mod_cast (Nat.mod_lt k (by omega : 0<b)).le
 have hn : (0 : ℝ)≤2*q := by positivity
 nlinarith
end ExactFourier.Amplification

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.AmplificationMaster
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Filter Topology
namespace ExactFourier.Amplification

theorem saving_exponent {g ρ : ℝ} (hρ : 0<ρ) (hs : g*ρ<1) :
 ∃ a : ℝ,0<a ∧ a<1 ∧ g*ρ^a<1 := by
 have ht : Tendsto (fun a : ℝ=>g*ρ^a) (𝓝 1) (𝓝 (g*ρ)) := by
  simpa only [Real.rpow_one] using (tendsto_const_nhds (x := g)).mul (Real.continuousAt_const_rpow (b := 1) hρ.ne')
 have hv := ht.eventually_lt_const hs
 have hp : ∀ᶠ a : ℝ in 𝓝 1,0<a := Ioi_mem_nhds zero_lt_one
 obtain ⟨a,ha,ha0,haS⟩ := (hp.and hv).exists_lt
 exact ⟨a,ha0,ha,haS⟩

theorem recurrence_bound (f : ℕ→ℝ) {b : ℕ} {p g C₀ : ℝ}
 (hb : 2≤b) (hp : 0<p) (hp1 : p≤1) (hg : 0≤g) (hC₀ : 0≤C₀)
 (hs : g*(p/b)<1)
 (hf : ∀ k,f k≤C₀+g*avg p f (k/b) 0) :
 ∃ a C : ℝ,0<a ∧ a<1 ∧ 0<C ∧ ∀ k,f k≤C*(k+1 : ℝ)^a := by
 let ρ : ℝ := p/b
 have hbR : (0 : ℝ)<b := by exact_mod_cast (show 0<b by omega)
 have hρ : 0<ρ := div_pos hp hbR
 obtain ⟨a,ha0,ha1,haS⟩ := saving_exponent hρ hs
 obtain ⟨γ,hγ0,hγ1⟩ := exists_between haS
 have hlim : Tendsto (fun k : ℕ=>g*((ρ*k+1)/(k+1))^a) atTop (𝓝 (g*ρ^a)) := by
  have hbase : Tendsto (fun k : ℕ=>(ρ*k+1)/(k+1)) atTop (𝓝 ρ) := by
   simpa only [one_mul,div_one,add_comm] using
    (tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 1 ρ (show (1:ℝ)≠0 by norm_num))
  exact tendsto_const_nhds.mul ((Real.continuousAt_rpow_const ρ a (Or.inl hρ.ne')).tendsto.comp hbase)
 obtain ⟨k₀,hk₀⟩ := eventually_atTop.1 (hlim.eventually_lt_const hγ0)
 let K := max k₀ 1
 let S := ∑ i∈Finset.range K,max (f i) 0
 let C := C₀/(1-γ)+S+1
 have hγ : 0<1-γ := by linarith
 have hS : 0≤S := Finset.sum_nonneg (fun i hi=>le_max_right _ _)
 have hCdiv : 0≤C₀/(1-γ) := div_nonneg hC₀ hγ.le
 have hC : 0<C := by dsimp [C]; linarith
 have hCbase : C₀≤C*(1-γ) := by
  have he : C₀/(1-γ)*(1-γ)=C₀ := div_mul_cancel₀ _ hγ.ne'
  have hh : C₀/(1-γ)≤C := by dsimp [C]; linarith
  nlinarith
 refine ⟨a,C,ha0,ha1,hC,?_⟩
 intro k
 induction k using Nat.strong_induction_on with
 | h k ih =>
  have hpw : 1≤(k+1 : ℝ)^a := by
   exact Real.one_le_rpow (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith) ha0.le
  by_cases hk : k<K
  · have hsmall : f k≤S := by
     exact (le_max_left _ _).trans (Finset.single_le_sum (fun i hi=>le_max_right (f i) 0) (Finset.mem_range.mpr hk))
    have hSC : S≤C := by dsimp [C]; linarith
    exact (hsmall.trans hSC).trans (le_mul_of_one_le_right hC.le hpw)
  · have hkK : K≤k := by omega
    have hkpos : 0<k := by dsimp [K] at hkK; omega
    have hj : k/b<k := Nat.div_lt_self hkpos (by omega)
    have havg := avg_mono hp.le hp1 f (fun i=>C*(i+1 : ℝ)^a) (k/b) 0 (by
     intro i _ hi
     exact ih i (by omega))
    rw [avg_const_mul] at havg
    have havg2 := avg_rpow hp.le hp1 ha0.le ha1.le (k/b) 0
    simp only [Nat.cast_zero,zero_add] at havg2
    have hjp : p*(k/b : ℕ)≤ρ*k := by
     have hn : (k/b : ℕ)*b≤k := Nat.div_mul_le_self _ _
     have hn' : ((k/b : ℕ) : ℝ)*(b : ℝ)≤k := by exact_mod_cast hn
     dsimp [ρ]
     rw [div_mul_eq_mul_div]
     apply (le_div_iff₀ hbR).mpr
     nlinarith
    have hpow := Real.rpow_le_rpow (show 0≤p*(k/b : ℕ)+1 by positivity) (show p*(k/b : ℕ)+1 ≤ ρ*k+1 by linarith) ha0.le
    have hco := (hk₀ k (le_trans (le_max_left _ _) hkK)).le
    rw [Real.div_rpow (by positivity) (by positivity) a,← mul_div_assoc] at hco
    have hden : 0<(k+1 : ℝ)^a := Real.rpow_pos_of_pos (by positivity) _
    have hco' := (div_le_iff₀ hden).mp hco
    have hbound : f k≤C₀+g*(C*(ρ*k+1)^a) := by
     apply (hf k).trans
     exact add_le_add_right (mul_le_mul_of_nonneg_left (havg.trans
       (mul_le_mul_of_nonneg_left (havg2.trans hpow) hC.le)) hg) C₀
    have hCg := mul_le_mul_of_nonneg_left hco' hC.le
    have hlast : C₀+C*γ*(k+1 : ℝ)^a≤C*(k+1 : ℝ)^a := by
     have hh := mul_le_mul_of_nonneg_left hpw (mul_nonneg hC.le hγ.le)
     nlinarith
    nlinarith
end ExactFourier.Amplification

end
end

section
noncomputable section
namespace ExactFourier.Amplification
open CircuitCost TensorAxis
/-- Tensor amplification for the literal finite winning word, with charged scalars. -/
theorem tensor_amplification {q b : ℕ} (A : Matrix (Fin q) (Fin q) ℂ)
 (hb : 2≤b) (W : List (WordStep A (q^b))) (hW : wordMatrix W=tensorPower A b)
 (hw : wordCalls W<b*q^(b-1)) :
 ∃ a C : ℝ,0<a ∧ a<1 ∧ 0<C ∧ ∀ k,
 (cost (power A k) : ℝ)≤C*(q : ℝ)^k*(k+1 : ℝ)^a := by
 have hq : 0<q := by
  by_contra h
  have he : q=0 := by omega
  simp only [he,zero_pow (by omega : b-1≠0),mul_zero] at hw
  omega
 have hb0 : b≠0 := by omega
 have hbR : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
 have hqR : (0:ℝ)<q := by exact_mod_cast hq
 have hp : (0:ℝ)<(q : ℝ)/(q^b : ℕ) := by positivity
 have hp1 : (q : ℝ)/(q^b : ℕ)≤1 := by
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast Nat.le_self_pow hb0 q
 have hs : (wordCalls W : ℝ)*(((q : ℝ)/(q^b : ℕ))/b)<1 := by
  have hwR : (wordCalls W : ℝ)<b*(q : ℝ)^(b-1) := by exact_mod_cast hw
  have he : (q : ℝ)^b=(q : ℝ)^(b-1)*q := by
   conv_lhs => rw [show b=b-1+1 by omega,pow_succ]
  push_cast
  rw [he]
  field_simp
  nlinarith
 obtain ⟨a,C,ha0,ha1,hC,hbound⟩ := recurrence_bound (normalizedCost A) hb hp hp1
  (Nat.cast_nonneg _) (show (0:ℝ)≤W.length+2*q*b by positivity) hs
  (normalized_recurrence hq A (by omega) W hW)
 refine ⟨a,C,ha0,ha1,hC,fun k=>?_⟩
 have hh := (div_le_iff₀ (pow_pos hqR k)).mp (hbound k)
 nlinarith only [hh]
end ExactFourier.Amplification

end
end

section
noncomputable section
namespace ExactFourier
variable {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ)

variable {A} {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

namespace AFrame
theorem mono (M : Matrix α α ℂ) (hm : MonomialMatrix M) : AFrame A M :=
 ⟨1,M,AParallel.identity,hm,by simp⟩
theorem atom_mono (M : Matrix (Fin q) (Fin q) ℂ) (hm : MonomialMatrix M) : AFrame A (A*M) :=
 ⟨A,M,AParallel.atom,hm,rfl⟩
theorem sum {M : Matrix α α ℂ} {N : Matrix β β ℂ} (hM : AFrame A M) (hN : AFrame A N) :
 AFrame A (Matrix.fromBlocks M 0 0 N) := by
 obtain ⟨B,Q,hB,hQ,rfl⟩ := hM.exists_factors
 obtain ⟨C,R,hC,hR,rfl⟩ := hN.exists_factors
 exact ⟨_,_,hB.sum hC,hQ.directSum hR,by simp [Matrix.fromBlocks_multiply]⟩
end AFrame

namespace AGenerated
theorem identity (d : ℕ) : AGenerated A (1 : Matrix α α ℂ) d := by
 refine ⟨List.replicate d 1,by simp,by simp,?_⟩
 intro X hX
 have hx := (List.mem_replicate.mp hX).2
 rw [hx]; exact AFrame.mono _ MonomialMatrix.one

theorem frame {M : Matrix α α ℂ} (h : AFrame A M) : AGenerated A M 1 :=
 ⟨[M],rfl,by simp,by simpa using h⟩
theorem mono (M : Matrix α α ℂ) (hm : MonomialMatrix M) : AGenerated A M 1 := frame (AFrame.mono _ hm)

theorem mul {M N : Matrix α α ℂ} {d e : ℕ} (hM : AGenerated A M d) (hN : AGenerated A N e) :
 AGenerated A (M*N) (d+e) := by
 obtain ⟨L,hL,hp,hr⟩ := hM
 obtain ⟨K,hK,hq,hs⟩ := hN
 refine ⟨L++K,by simp [hL,hK],by simp [hp,hq],?_⟩
 intro X hX
 rcases List.mem_append.mp hX with hX|hX
 · exact hr X hX
 · exact hs X hX

theorem weaken {M : Matrix α α ℂ} {d e : ℕ} (h : AGenerated A M d) (hde : d≤e) : AGenerated A M e := by
 have hh := h.mul (identity (A := A) (α := α) (e-d))
 simpa only [mul_one,Nat.add_sub_of_le hde] using hh

theorem reindex {M : Matrix α α ℂ} {d : ℕ} (h : AGenerated A M d) (e : α≃β) :
 AGenerated A (Matrix.reindex e e M) d := by
 obtain ⟨L,hL,hp,hr⟩ := h
 refine ⟨L.map (Matrix.reindex e e),by simp [hL],?_,?_⟩
 · rw [← hp]
   exact (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom.map_list_prod L |>.symm
 · intro X hX
   obtain ⟨Y,hY,rfl⟩ := List.mem_map.mp hX
   exact (hr Y hY).reindex e

theorem sum {M : Matrix α α ℂ} {N : Matrix β β ℂ} {d : ℕ}
 (hM : AGenerated A M d) (hN : AGenerated A N d) : AGenerated A (Matrix.fromBlocks M 0 0 N) d := by
 obtain ⟨L,hL,hp,hr⟩ := hM
 obtain ⟨K,hK,hq,hs⟩ := hN
 refine ⟨Round.joint L K,(Round.joint_length L K (hL.trans hK.symm)).trans hL,?_,?_⟩
 · rw [Round.joint_prod L K (hL.trans hK.symm),hp,hq]
 · exact Round.joint_all L K (AFrame A) (AFrame A) (AFrame A) hr hs
      (fun _ _ h h' => h.sum h')

theorem embed {M : Matrix α α ℂ} {d : ℕ} (h : AGenerated A M d) (e : α↪β) :
 AGenerated A (Embedded.matrix e M) d :=
 (h.sum (identity d)).reindex (Embedded.coordinates e)

theorem from_pattern {M : Matrix (Fin q) (Fin q) ℂ} {h : ℕ}
 (hp : PositiveGeneration.Pattern A h M) : AGenerated A M (h+1) := by
 induction hp with
 | zero M hm => exact mono M hm
 | @succ h H hp M hm ih =>
  have hh := ih.mul (frame (AFrame.atom_mono M hm))
  simpa only [mul_assoc] using hh
end AGenerated
end ExactFourier

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace ParallelTensorCost
open CircuitCost TensorAxis
variable {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} {a C : ℝ}
 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem Good.reindex {M : Matrix α α ℂ} {m : ℕ} (hg : Good (A := A) (a := a) (C := C) M m)
 (e : α≃β) : Good (A := A) (a := a) (C := C) (Matrix.reindex e e M) m := by
 intro k
 have he := reindex_tensor e (Equiv.refl (Space (Fin q) k)) M (power A k)
 simp only [Matrix.reindex_refl_refl,Matrix.kronecker] at he
 rw [←he,cost_reindex,← Fintype.card_congr e]
 exact hg k

theorem Good.parallel (ha : 0≤a) (hC : 0≤C)
 {M : Matrix α α ℂ} {m : ℕ} (hg : Good (A := A) (a := a) (C := C) M m)
 {N : Matrix β β ℂ} (hN : AParallel A N) :
 Good (A := A) (a := a) (C := C) (M⊗ₖN) (m+1) := by
 induction hN with
 | @identity β _ _ =>
  intro k
  rw [tensor_exchange]
  have h1 : (cost ((M⊗ₖpower A k)⊗ₖ(1 : Matrix β β ℂ)) : ℝ)≤Fintype.card β*cost (M⊗ₖpower A k) := by
   exact_mod_cast tensor_one_le (β := β) (M⊗ₖpower A k)
  have h2 := mul_le_mul_of_nonneg_left (hg k) (Nat.cast_nonneg (Fintype.card β) : (0:ℝ)≤_)
  have hp : (m+k+1 : ℝ)^a≤(m+1+k+1 : ℝ)^a := Real.rpow_le_rpow (by positivity) (by linarith) ha
  have h3 := mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤C*Fintype.card α*Fintype.card β*(q : ℝ)^k by positivity)
  simp only [Fintype.card_prod,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  nlinarith only [h1,h2,h3]
 | atom =>
  intro k
  rw [tensor_exchange,tensor_assoc]
  change (cost (M⊗ₖpower A (k+1)) : ℝ)≤_
  have hh := hg (k+1)
  simpa [Fintype.card_prod,pow_succ,Nat.cast_add,Nat.cast_one,Nat.cast_mul,mul_assoc,mul_left_comm,mul_comm,add_assoc,add_left_comm,add_comm] using hh
 | @reindex β γ _ _ _ _ e N hN ih =>
  have he := reindex_tensor (Equiv.refl α) e M N
  simp only [Matrix.reindex_refl_refl,Matrix.kronecker] at he
  rw [←he]
  exact ih.reindex _
 | @sum β γ _ _ _ _ N P hN hP ihN ihP =>
  intro k
  have hcost : cost ((M⊗ₖMatrix.fromBlocks N 0 0 P)⊗ₖpower A k)≤
   cost ((M⊗ₖN)⊗ₖpower A k)+cost ((M⊗ₖP)⊗ₖpower A k) := by
   rw [tensor_exchange,tensor_comm]
   have hh := tensor_sum N P (M⊗ₖpower A k)
   rw [tensor_comm N,tensor_comm P,← tensor_exchange M N,← tensor_exchange M P] at hh
   exact hh
  have hh : (cost ((M⊗ₖMatrix.fromBlocks N 0 0 P)⊗ₖpower A k) : ℝ)≤
   cost ((M⊗ₖN)⊗ₖpower A k)+cost ((M⊗ₖP)⊗ₖpower A k) := by exact_mod_cast hcost
  have hn := ihN k
  have hp := ihP k
  simp only [Fintype.card_prod,Fintype.card_sum,Nat.cast_mul,Nat.cast_add] at hn hp ⊢
  nlinarith only [hh,hn,hp]

end ParallelTensorCost
end ExactFourier

end
end

section
noncomputable section
open scoped Kronecker
namespace ExactFourier
namespace PiTensor

theorem splitFirst_matrix {n : ℕ} (D : Fin (n+1)→Type)
 [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)] (M : ∀ i,Matrix (D i) (D i) ℂ) :
 Matrix.reindex (splitFirst D) (splitFirst D) (matrix M)=M 0⊗ₖmatrix (fun i : Fin n=>M i.succ) := by
 ext x y
 change (∏ i,M i (Fin.cases x.1 x.2 i) (Fin.cases y.1 y.2 i)) =
   M 0 x.1 y.1 * ∏ i : Fin n,M i.succ (x.2 i) (y.2 i)
 rw [Fin.prod_univ_succ]
 rfl

theorem monomial {ι : Type} [Fintype ι] [DecidableEq ι]
 {D : ι→Type} [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (hM : ∀ i,MonomialMatrix (M i)) : MonomialMatrix (matrix M) := by
 choose s d hd hs using hM
 refine ⟨Equiv.piCongrRight s,fun y=>∏ i,d i (y i),fun y=>Finset.prod_ne_zero_iff.mpr (fun i _=>hd i (y i)),?_⟩
 intro x y
 by_cases h : x=Equiv.piCongrRight s y
 · subst x
   simp [matrix,hs,Equiv.piCongrRight_apply]
 · rw [ite_eq_right h]
   obtain ⟨i,hi⟩ := Function.ne_iff.mp h
   apply Finset.prod_eq_zero (Finset.mem_univ i)
   have hi' : x i≠s i (y i) := hi
   simp [hs,hi']
end PiTensor

namespace ParallelTensorCost
open CircuitCost TensorAxis
variable {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} {a C : ℝ}
 (ha : 0≤a) (hC : 0≤C)
 (amp : ∀ k,(cost (power A k) : ℝ)≤C*(q : ℝ)^k*(k+1 : ℝ)^a)

include ha hC amp
theorem pi_good (n : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (hM : ∀ i,AParallel A (M i)) :
 Good (A := A) (a := a) (C := C) (PiTensor.matrix M) n := by
 induction n with
 | zero =>
  have he : PiTensor.matrix M=1 := by ext x y; simp [PiTensor.matrix,Matrix.one_apply,Subsingleton.elim x y]
  rw [he]
  intro k
  rw [tensor_comm]
  have hc : Fintype.card (∀ i : Fin 0,D i)=1 := Fintype.card_ofSubsingleton (fun i=>Fin.elim0 i)
  have hh : (cost (power A k⊗ₖ(1 : Matrix (∀ i,D i) (∀ i,D i) ℂ)) : ℝ)≤cost (power A k) := by
   exact_mod_cast (by simpa [hc] using tensor_one_le (β := ∀ i,D i) (power A k))
  simpa [hc] using hh.trans (amp k)
 | succ n ih =>
  have hg := ih (fun i=>D i.succ) (fun i=>M i.succ) (fun i=>hM i.succ)
  have hh := hg.parallel ha hC (hM 0)
  have he : Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
   (PiTensor.matrix (fun i : Fin n=>M i.succ)⊗ₖM 0)=M 0⊗ₖPiTensor.matrix (fun i : Fin n=>M i.succ) := by
   ext i j; exact mul_comm _ _
  have hh := hh.reindex (Equiv.prodComm _ _)
  rw [he,← PiTensor.splitFirst_matrix D M] at hh
  have hh := hh.reindex (PiTensor.splitFirst D).symm
  rw [reindex_inverse] at hh
  exact hh

theorem pi_cost (n : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (hM : ∀ i,AParallel A (M i)) :
 (cost (PiTensor.matrix M) : ℝ)≤C*Fintype.card (∀ i,D i)*(n+1 : ℝ)^a := by
 have hh := pi_good ha hC amp n D M hM 0
 simpa [power,tensor_punit] using hh
end ParallelTensorCost
end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PairFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier
namespace PairFamily
variable {σ τ α β : Type} [Fintype σ] [Fintype τ] [Fintype α] [Fintype β]
 [DecidableEq σ] [DecidableEq τ] [DecidableEq α] [DecidableEq β]

theorem sum_blocks
    {σ : Type} {τ : Type} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ] (H : σ→Matrix (Fin 2) (Fin 2) ℂ) (K : τ→Matrix (Fin 2) (Fin 2) ℂ) :
 Matrix.reindex sumEquiv sumEquiv (Matrix.blockDiagonal' (Sum.elim H K))=
 Matrix.fromBlocks (Matrix.blockDiagonal' H) 0 0 (Matrix.blockDiagonal' K) := by
 ext i j
 cases i with
 | inl i => cases j with
   | inl j => simp [Matrix.reindex_apply,sumEquiv,Matrix.blockDiagonal'_apply]
   | inr j => simp [Matrix.reindex_apply,sumEquiv,Matrix.blockDiagonal'_apply]
 | inr i => cases j with
   | inl j => simp [Matrix.reindex_apply,sumEquiv,Matrix.blockDiagonal'_apply]
   | inr j => simp [Matrix.reindex_apply,sumEquiv,Matrix.blockDiagonal'_apply]

theorem sub_blocks (S : Set σ) [DecidablePred (·∈S)]
 (H : σ→Matrix (Fin 2) (Fin 2) ℂ) :
 Embedded.matrix (subEmbedding S) (Matrix.blockDiagonal' (fun i : S=>H i))=
 Matrix.blockDiagonal' (fun i=>if i∈S then H i else 1) := by
 ext ⟨i,x⟩ ⟨j,y⟩
 by_cases hi : i∈S
 · by_cases hj : j∈S
   · change Embedded.matrix (subEmbedding S) _ (subEmbedding S ⟨⟨i,hi⟩,x⟩)
       (subEmbedding S ⟨⟨j,hj⟩,y⟩)=_
     rw [Embedded.matrix_on]
     by_cases hij : i=j
     · subst j; simp [hi]
     · simp [Matrix.blockDiagonal'_apply,hij,Subtype.ext_iff]
   · rw [Embedded.matrix_off_col]
     · have hij : i≠j := by rintro rfl; exact hj hi
       simp [Matrix.blockDiagonal'_apply,hij]
     · rintro ⟨⟨⟨j',hj'⟩,y'⟩,he⟩
       have := congrArg Sigma.fst he
       change j'=j at this
       exact hj (this ▸ hj')
 · rw [Embedded.matrix_off_row]
   · by_cases hij : i=j
     · subst j; simp [Matrix.blockDiagonal'_apply,hi,Matrix.one_apply]
     · simp [Matrix.blockDiagonal'_apply,hij]
   · rintro ⟨⟨⟨i',hi'⟩,x'⟩,he⟩
     have := congrArg Sigma.fst he
     change i'=i at this
     exact hi (this ▸ hi')

theorem split_blocks (S : Set σ) [DecidablePred (·∈S)]
 (H : σ→Matrix (Fin 2) (Fin 2) ℂ) :
 Matrix.blockDiagonal' H=
 Embedded.matrix (subEmbedding S) (Matrix.blockDiagonal' (fun i : S=>H i)) *
 Embedded.matrix (subEmbedding Sᶜ) (Matrix.blockDiagonal' (fun i : (Sᶜ : Set σ)=>H i)) := by
 rw [sub_blocks,sub_blocks,← Matrix.blockDiagonal'_mul]
 congr 1
 funext i
 by_cases hi : i∈S <;> simp [hi]
end PairFamily

attribute [instance] PairFamily.finite PairFamily.dec
namespace PairFamily
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
theorem empty_matrix : (empty : PairFamily α).matrix=1 := by
 have he : Matrix.blockDiagonal' (empty : PairFamily α).pairs=1 := by
  ext ⟨i,x⟩; exact Fin.elim0 i
 rw [matrix,he,Embedded.matrix_one]

theorem pair_matrix (H : Matrix (Fin 2) (Fin 2) ℂ) (hu : IsUnit H) : (pair H hu).matrix=H := by
 ext i j
 change Embedded.matrix (pair H hu).position _ ((pair H hu).position ⟨(0 : Fin 1),i⟩) ((pair H hu).position ⟨(0 : Fin 1),j⟩)=_
 rw [Embedded.matrix_on]
 change Matrix.blockDiagonal' (fun _ : Fin 1=>H) ⟨0,i⟩ ⟨0,j⟩=H i j
 simp

theorem reindex_matrix (P : PairFamily α) (e : α≃β) :
 (P.reindex e).matrix=Matrix.reindex e e P.matrix := by
 rw [matrix,reindex,← Embedded.matrix_comp,Embedded.matrix_equiv]
 rfl

theorem sum_matrix (P : PairFamily α) (Q : PairFamily β) :
 (P.sum Q).matrix=Matrix.fromBlocks P.matrix 0 0 Q.matrix := by
 rw [matrix,sum,← Embedded.matrix_comp,Embedded.matrix_equiv,sum_blocks,Embedded.matrix_sumMap]
 rfl

theorem card_le (P : PairFamily α) : 2*Fintype.card P.index≤Fintype.card α := by
 have h := Fintype.card_le_of_injective P.position P.position.injective
 simpa [Fintype.card_sigma,Nat.mul_comm] using h
end PairFamily

namespace Round
variable {α : Type} [Fintype α] [DecidableEq α]
theorem pair_rep {M : Matrix α α ℂ} (h : Round M) :
 ∃ P : PairFamily α,∃ Q : Matrix α α ℂ,MonomialMatrix Q ∧ M=P.matrix*Q := by
 induction h with
 | mono M h => exact ⟨PairFamily.empty,M,h,by rw [PairFamily.empty_matrix,one_mul]⟩
 | pair M h => exact ⟨PairFamily.pair M h,1,MonomialMatrix.one,by rw [PairFamily.pair_matrix,mul_one]⟩
 | reindex e h ih =>
  obtain ⟨P,Q,hQ,rfl⟩ := ih
  exact ⟨P.reindex e,Matrix.reindex e e Q,hQ.reindex e,by rw [PairFamily.reindex_matrix]; exact (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul _ _⟩
 | sum h h' ih ih' =>
  obtain ⟨P,Q,hQ,rfl⟩ := ih
  obtain ⟨P',Q',hQ',rfl⟩ := ih'
  exact ⟨P.sum P',Matrix.fromBlocks Q 0 0 Q',hQ.directSum hQ',by rw [PairFamily.sum_matrix]; simp [Matrix.fromBlocks_multiply]⟩
end Round
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier.AGenerated
variable {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}

theorem blocks_fin (n : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (d : ℕ) (hM : ∀ i,AGenerated A (M i) d) :
 AGenerated A (Matrix.blockDiagonal' M) d := by
 induction n with
 | zero =>
  have he : Matrix.blockDiagonal' M=(1 : Matrix (Σ i,D i) (Σ i,D i) ℂ) := by
   ext ⟨i,x⟩; exact Fin.elim0 i
  rw [he]
  exact identity d
 | succ n ih =>
  have h := (hM 0).sum (ih (fun i=>D i.succ) (fun i=>M i.succ) (fun i=>hM i.succ))
  have he : Matrix.reindex (sigmaFinSucc D).symm (sigmaFinSucc D).symm
   (Matrix.fromBlocks (M 0) 0 0 (Matrix.blockDiagonal' (fun i : Fin n=>M i.succ)))=
   Matrix.blockDiagonal' M := by
   ext ⟨i,x⟩ ⟨j,y⟩
   refine Fin.cases ?_ (fun i=>?_) i x <;> intro x <;>
    refine Fin.cases ?_ (fun j=>?_) j y <;> intro y <;>
    simp [Matrix.reindex_apply,sigmaFinSucc,Matrix.blockDiagonal'_apply,Fin.succ_ne_zero,eq_comm]
  rw [← he]
  exact h.reindex _

theorem blocks {σ : Type} [Fintype σ] [DecidableEq σ]
 (D : σ→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (d : ℕ) (hM : ∀ i,AGenerated A (M i) d) :
 AGenerated A (Matrix.blockDiagonal' M) d := by
 let e := (Fintype.equivFin σ).symm
 let f : (Σ i : Fin (Fintype.card σ),D (e i))≃(Σ i,D i) := Equiv.sigmaCongrLeft e
 have h := blocks_fin (Fintype.card σ) (fun i=>D (e i)) (fun i=>M (e i)) d (fun i=>hM (e i))
 have he : Matrix.reindex f f (Matrix.blockDiagonal' (fun i=>M (e i)))=Matrix.blockDiagonal' M := by
  ext x y
  obtain ⟨⟨i,x⟩,rfl⟩ := f.surjective x
  obtain ⟨⟨j,y⟩,rfl⟩ := f.surjective y
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  change Matrix.blockDiagonal' (fun i=>M (e i)) ⟨i,x⟩ ⟨j,y⟩ =
   Matrix.blockDiagonal' M ⟨e i,x⟩ ⟨e j,y⟩
  by_cases hij : i=j
  · subst j; simp [Matrix.blockDiagonal'_apply]
  · simp [Matrix.blockDiagonal'_apply,hij,e.injective.ne hij]
 rw [← he]
 exact h.reindex f

end ExactFourier.AGenerated

end
end

section
noncomputable section
namespace ExactFourier
namespace PairFamily
variable {q h : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
 (hq : 2≤q) (gen : ∀ M : Matrix (Fin q) (Fin q) ℂ,IsUnit M → PositiveGeneration.Pattern A h M)
variable {σ α : Type} [Fintype σ] [Fintype α] [DecidableEq σ] [DecidableEq α]

include hq gen
theorem one_batch (H : σ→Matrix (Fin 2) (Fin 2) ℂ) (hH : ∀ i,IsUnit (H i))
 (e : (Σ _ : σ,Fin 2) ↪ α) (hc : q*Fintype.card σ≤Fintype.card α) :
 AGenerated A (Embedded.matrix e (Matrix.blockDiagonal' H)) (h+1) := by
 let f : Fin 2 ↪ Fin q := Fin.castLEEmb hq
 let E := Embedded.sigmaEmbed (fun _ : σ=>f)
 obtain ⟨g,hg⟩ := Embedded.exists_completion E e (by simpa [Fintype.card_sigma,Nat.mul_comm] using hc)
 have hh := AGenerated.blocks (fun _ : σ=>Fin q) (fun i=>Embedded.matrix f (H i)) (h+1)
   (fun i=>AGenerated.from_pattern (gen _ (Embedded.unit f _ (hH i))))
 have hh := hh.embed g
 rw [← Embedded.matrix_sigmaEmbed,Embedded.matrix_comp,hg] at hh
 exact hh

theorem batches (b c : ℕ) (hc : q*c≤Fintype.card α)
 (H : σ→Matrix (Fin 2) (Fin 2) ℂ) (hH : ∀ i,IsUnit (H i))
 (e : (Σ _ : σ,Fin 2) ↪ α) (hs : Fintype.card σ≤b*c) :
 AGenerated A (Embedded.matrix e (Matrix.blockDiagonal' H)) (b*(h+1)) := by
 induction b generalizing σ with
 | zero =>
  have hs0 : Fintype.card σ=0 := by simpa using hs
  let : IsEmpty σ := Fintype.card_eq_zero_iff.mp hs0
  have he : Matrix.blockDiagonal' H=1 := by ext ⟨i,x⟩; exact isEmptyElim i
  rw [he,Embedded.matrix_one]
  exact AGenerated.identity _
 | succ b ih =>
  by_cases hs' : Fintype.card σ≤c
  · exact (one_batch hq gen H hH e ((Nat.mul_le_mul_left q hs').trans hc)).weaken
      (by nlinarith : h+1≤(b+1)*(h+1))
  · obtain ⟨S,hS,hSc⟩ := Finset.exists_subset_card_eq (show c≤(Finset.univ : Finset σ).card by simpa using (le_of_not_ge hs'))
    let T : Set σ := S
    have hT : Fintype.card T=c := by simpa [T] using hSc
    have hTc : Fintype.card (Tᶜ : Set σ)+c=Fintype.card σ := by
      rw [← hT]
      have ht : Fintype.card (Tᶜ : Set σ)=Fintype.card σ-Fintype.card T :=
        Fintype.card_subtype_compl (fun i=>i∈T)
      rw [ht]
      exact Nat.sub_add_cancel (Fintype.card_subtype_le _)
    have h1 := one_batch hq gen (fun i : T=>H i) (fun i=>hH i)
      ((subEmbedding T).trans e) (by simpa [hT] using hc)
    have h2 := ih (fun i : (Tᶜ : Set σ)=>H i) (fun i=>hH i)
      ((subEmbedding Tᶜ).trans e) (by nlinarith : Fintype.card (Tᶜ : Set σ)≤b*c)
    have he : Embedded.matrix e (Matrix.blockDiagonal' H)=
      Embedded.matrix ((subEmbedding T).trans e) (Matrix.blockDiagonal' (fun i : T=>H i)) *
      Embedded.matrix ((subEmbedding Tᶜ).trans e) (Matrix.blockDiagonal' (fun i : (Tᶜ : Set σ)=>H i)) := by
      rw [split_blocks T H,Embedded.matrix_mul,Embedded.matrix_comp,Embedded.matrix_comp]
    rw [he]
    convert h1.mul h2 using 1 ; ring

theorem generated (P : PairFamily α) (hr : 2*q≤Fintype.card α) :
 AGenerated A P.matrix (q*(h+1)) := by
 let c := Fintype.card α/q
 have hq0 : 0<q := lt_of_lt_of_le (by decide : 0<2) hq
 have hqc : q*c≤Fintype.card α := Nat.mul_div_le _ _
 have hs := P.card_le
 have hrem := Nat.mod_lt (Fintype.card α) hq0
 have hrdiv := Nat.div_add_mod (Fintype.card α) q
 have hbound : Fintype.card P.index≤q*c := by
  dsimp [c]
  nlinarith
 exact batches hq gen q c hqc P.pairs P.unit P.position hbound
end PairFamily

namespace Round
variable {q h : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]
theorem generated (hq : 2≤q)
 (gen : ∀ M : Matrix (Fin q) (Fin q) ℂ,IsUnit M → PositiveGeneration.Pattern A h M)
 {M : Matrix α α ℂ} (hM : Round M) (hr : 2*q≤Fintype.card α) :
 AGenerated A M (q*(h+1)+1) := by
 obtain ⟨P,Q,hQ,rfl⟩ := hM.pair_rep
 exact (P.generated hq gen hr).mul (AGenerated.mono Q hQ)
end Round

namespace Layered
variable {q h : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]
theorem generated (hq : 2≤q)
 (gen : ∀ M : Matrix (Fin q) (Fin q) ℂ,IsUnit M → PositiveGeneration.Pattern A h M)
 {M : Matrix α α ℂ} {d : ℕ} (hM : Layered M d) (hr : 2*q≤Fintype.card α) :
 AGenerated A M (d*(q*(h+1)+1)) := by
 obtain ⟨L,hL,rfl,hR⟩ := hM.rounds
 subst d
 clear hM
 induction L with
 | nil => simpa using AGenerated.identity (A := A) (α := α) 0
 | cons M L ih =>
  have h1 := (hR M (by simp)).generated hq gen hr
  have h2 := ih (fun X hX=>hR X (by simp [hX]))
  simpa [Nat.add_mul,Nat.add_comm] using h1.mul h2
end Layered
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier
namespace AGenerated
variable {q d : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]

theorem zero {M : Matrix α α ℂ} (h : AGenerated A M 0) : M=1 := by
 obtain ⟨L,hL,rfl,hR⟩ := h
 have he : L=[] := List.length_eq_zero_iff.mp hL
 simp [he]

theorem succ {M : Matrix α α ℂ} (h : AGenerated A M (d+1)) :
 ∃ X Y : Matrix α α ℂ,AFrame A X ∧ AGenerated A Y d ∧ M=X*Y := by
 obtain ⟨L,hL,hp,hR⟩ := h
 cases L with
 | nil => simp at hL
 | cons X L =>
  refine ⟨X,L.prod,hR X (by simp),⟨L,by simpa using hL,rfl,fun Y hY=>hR Y (by simp [hY])⟩,?_⟩
  simpa using hp.symm
end AGenerated

namespace ParallelTensorCost
open CircuitCost TensorAxis
variable {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} {a C : ℝ}
 (ha : 0≤a) (hC : 0≤C)
 (amp : ∀ k,(cost (power A k) : ℝ)≤C*(q : ℝ)^k*(k+1 : ℝ)^a)
include ha hC amp

theorem frames_cost (n : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (hM : ∀ i,AFrame A (M i)) :
 (cost (PiTensor.matrix M) : ℝ)≤C*Fintype.card (∀ i,D i)*(n+1 : ℝ)^a+Fintype.card (∀ i,D i) := by
 choose B Q hB hQ he using fun i=>(hM i).exists_factors
 have he' : M=B*Q := funext he
 rw [he',PiTensor.mul]
 have h1 : (cost (PiTensor.matrix B*PiTensor.matrix Q) : ℝ)≤cost (PiTensor.matrix B)+cost (PiTensor.matrix Q) :=
  by exact_mod_cast cost_mul (PiTensor.matrix B) (PiTensor.matrix Q)
 have h2 := pi_cost ha hC amp n D B hB
 have h3 : (cost (PiTensor.matrix Q) : ℝ)≤Fintype.card (∀ i,D i) := by
  exact_mod_cast cost_monomial (PiTensor.matrix Q) (PiTensor.monomial Q hQ)
 linarith

theorem generated_cost (n d : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (hM : ∀ i,AGenerated A (M i) d) :
 (cost (PiTensor.matrix M) : ℝ)≤d*(C*Fintype.card (∀ i,D i)*(n+1 : ℝ)^a+Fintype.card (∀ i,D i)) := by
 induction d generalizing M with
 | zero =>
  have he : M=1 := funext (fun i=>(hM i).zero)
  simp [he]
 | succ d ih =>
  choose X Y hX hY he using fun i=>(hM i).succ
  have he' : M=X*Y := funext he
  rw [he',PiTensor.mul]
  have h1 : (cost (PiTensor.matrix X*PiTensor.matrix Y) : ℝ)≤cost (PiTensor.matrix X)+cost (PiTensor.matrix Y) :=
    by exact_mod_cast cost_mul (PiTensor.matrix X) (PiTensor.matrix Y)
  have h2 := frames_cost ha hC amp n D X hX
  have h3 := ih Y hY
  push_cast
  nlinarith only [h1,h2,h3]

theorem layered_cost {h : ℕ} (hq : 2≤q)
 (gen : ∀ M : Matrix (Fin q) (Fin q) ℂ,IsUnit M → PositiveGeneration.Pattern A h M)
 (n d : ℕ) (D : Fin n→Type) [∀ i,Fintype (D i)] [∀ i,DecidableEq (D i)]
 (M : ∀ i,Matrix (D i) (D i) ℂ) (hM : ∀ i,Layered (M i) d)
 (hD : ∀ i,2*q≤Fintype.card (D i)) :
 (cost (PiTensor.matrix M) : ℝ)≤(d*(q*(h+1)+1) : ℕ)*
   (C*Fintype.card (∀ i,D i)*(n+1 : ℝ)^a+Fintype.card (∀ i,D i)) :=
 generated_cost ha hC amp n _ D M (fun i=>(hM i).generated hq gen (hD i))
end ParallelTensorCost
end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.MatrixRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier
variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
theorem reindex_mulVec
    {α : Type} {β : Type} {γ : Type} {δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (e : β≃δ) (f : α≃γ) (M : Matrix β α ℂ) (x : γ→ℂ) :
 (Matrix.reindex e f M).mulVec x=(M.mulVec (x∘f))∘e.symm := by
 funext i
 simp only [Matrix.mulVec,dotProduct,Matrix.reindex_apply,Matrix.submatrix_apply,Function.comp_apply]
 exact (f.sum_comp (fun j=>M (e.symm i) (f.symm j)*x j)).symm.trans (by simp)
end ExactFourier

end

section
noncomputable section
namespace ExactFourier.RadixTwo

theorem butterfly_layer (n : ℕ) (ω : ℂ) (hω : ω≠0) : Layered (butterfly n ω) 1 := by
 let M := fun i : Fin n=>(!![1,ω^i.val;1,-ω^i.val] : Matrix (Fin 2) (Fin 2) ℂ)
 have hm : ∀ i,IsUnit (M i) := by
  intro i
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_fin_two]
  change 1 * (-ω^i.val) - ω^i.val * 1 ≠ 0
  have hh := pow_ne_zero i.val hω
  intro he; apply hh; linear_combination -1/2 * he
 have h := (Layered.blockDiagonal M 1 (fun i=>Layered.pair (M i) (hm i))).reindex (twoProdEquiv (Fin n))
 have he : Matrix.reindex (twoProdEquiv (Fin n)) (twoProdEquiv (Fin n)) (Matrix.blockDiagonal M)=butterfly n ω := by
  ext i j
  cases i <;> cases j <;>
   simp [twoProdEquiv,Matrix.reindex_apply,Matrix.blockDiagonal,M,butterfly,Matrix.one_apply,Matrix.diagonal_apply]
 rw [he] at h
 exact h

theorem dft_step (n : ℕ) (ω : ℂ) (hω : ω^n = -1) : dft (n+n) ω=
 Matrix.reindex finSumFinEquiv (paritySumEquiv n)
 (butterfly n ω*Matrix.fromBlocks (dft n (ω^2)) 0 0 (dft n (ω^2))) := by
 apply Matrix.mulVec_injective
 funext x
 rw [reindex_mulVec]
 have he := eval_split n ω hω x
 change eval (n+n) ω x=_
 rw [he]
 rw [← Matrix.mulVec_mulVec]
 funext i
 obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
 cases i with
 | inl j =>
  simp only [finSumFinEquiv_apply_left, Fin.addCases_left, Function.comp_apply,
    finSumFinEquiv_symm_apply_castAdd]
  simp [butterfly,dft,eval,evalAt,Matrix.mulVec,dotProduct,Matrix.one_apply,Matrix.diagonal_apply]
 | inr j =>
  simp only [finSumFinEquiv_apply_right, Fin.addCases_right, Function.comp_apply,
    finSumFinEquiv_symm_apply_natAdd]
  simp [butterfly,dft,eval,evalAt,Matrix.mulVec,dotProduct,Matrix.one_apply,Matrix.diagonal_apply, sub_eq_add_neg]

theorem dft_layers (k : ℕ) (ω : ℂ) (hω : IsPrimitiveRoot ω (2^k)) :
 Layered (dft (2^k) ω) (2*k) := by
 induction k generalizing ω with
 | zero =>
  change Layered (dft 1 ω) 0
  have he : dft 1 ω=(1 : Matrix (Fin 1) (Fin 1) ℂ) := by
   ext i j; fin_cases i; fin_cases j
   simp [dft]
  rw [he]
  exact Layered.identity
 | succ k ih =>
  have hs : IsPrimitiveRoot (ω^2) (2^k) :=
   IsPrimitiveRoot.pow (pow_pos (by decide) _) hω (by rw [pow_succ]; omega)
  have hh : ω^(2^k) = -1 :=
   (IsPrimitiveRoot.pow (pow_pos (by decide) _) hω (by rw [pow_succ])).eq_neg_one_of_two_right
  have hF := (ih (ω^2) hs).sum (ih (ω^2) hs)
  have hB := butterfly_layer (2^k) ω (hω.ne_zero (by positivity))
  have h := (hB.mul hF).two_reindex finSumFinEquiv (paritySumEquiv (2^k))
  rw [← dft_step (2^k) ω hh] at h
  have he : 2^(k+1)=2^k+2^k := by rw [pow_succ]; omega
  rw [he]
  simpa only [show 1+2*k+1=2*(k+1) by omega] using h
end ExactFourier.RadixTwo

end
end

section
noncomputable section
namespace ExactFourier.NewtonFourier
open scoped BigOperators
open Polynomial

theorem newton_succ (ω : ℂ) (k : ℕ) : newton ω (k+1)=newton ω k*(X-C (ω^k)) := by
 simp [newton,Finset.prod_range_succ]
theorem H_succ (ω : ℂ) (i : ℕ) : H ω (i+1)=H ω i*(1-ω^(i+1)) := by simp [H,Finset.prod_range_succ]
theorem scale_succ (ω : ℂ) (k : ℕ) : scale ω (k+1)=scale ω k*(-ω^k) := by simp [scale,Finset.prod_range_succ]

theorem newton_monic (ω : ℂ) (k : ℕ) : (newton ω k).Monic := monic_prod_X_sub_C _ _
@[simp] theorem newton_natDegree (ω : ℂ) (k : ℕ) : (newton ω k).natDegree=k := by
 induction k with
 | zero => simp
 | succ k ih => rw [newton_succ,natDegree_mul (newton_monic ω k).ne_zero (monic_X_sub_C _).ne_zero,ih,natDegree_X_sub_C]

theorem newton_eval_zero (ω : ℂ) (i k : ℕ) (h : i < k) : (newton ω k).eval (ω^i)=0 := by
 simp only [newton,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
 exact Finset.prod_eq_zero (Finset.mem_range.mpr h) (sub_self _)

theorem eval_factor (ω : ℂ) (i k : ℕ) (hki : k ≤ i) :
 (newton ω k).eval (ω^i)*H ω (i-k)=scale ω k*H ω i := by
 induction k with
 | zero => simp
 | succ k ih =>
  have hik : k ≤ i := by omega
  have hs : i-k=(i-(k+1))+1 := by omega
  have hpow : ω^i=ω^k*ω^(i-k) := by rw [← pow_add,Nat.add_sub_of_le hik]
  have hh := ih hik
  rw [hs,H_succ] at hh
  rw [newton_succ,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,scale_succ]
  rw [hpow,hs]
  rw [hpow,hs] at hh
  linear_combination (-ω^k)*hh

theorem H_ne_zero {ω : ℂ} {n : ℕ} (hω : IsPrimitiveRoot ω n) {i : ℕ} (hi : i < n) : H ω i ≠ 0 := by
 apply Finset.prod_ne_zero_iff.mpr
 intro j hj
 apply sub_ne_zero.mpr
 exact (hω.pow_ne_one_of_pos_of_lt (by omega : j+1 ≠ 0) (by have := Finset.mem_range.mp hj; omega)).symm

theorem scale_ne_zero {ω : ℂ} (hω : ω ≠ 0) (k : ℕ) : scale ω k ≠ 0 := by
 apply Finset.prod_ne_zero_iff.mpr
 intro j hj
 exact neg_ne_zero.mpr (pow_ne_zero j hω)

theorem N_lower (n : ℕ) (ω : ℂ) : (N n ω).IsLowerTriangular := by
 intro i j hij
 exact newton_eval_zero ω i.val j.val hij

theorem P_upper (n : ℕ) (ω : ℂ) : (P n ω).IsUpperTriangular := by
 intro i j hij
 exact coeff_eq_zero_of_natDegree_lt (by simpa using hij)

theorem dft_mul_P (n : ℕ) (ω : ℂ) : RadixTwo.dft n ω * P n ω=N n ω := by
 have hh := Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
  (fun i : Fin n=>ω^i.val) (fun k : Fin n=>newton ω k.val) (fun k=>by simp)
 have he : Matrix.vandermonde (fun i : Fin n=>ω^i.val)=RadixTwo.dft n ω := by
  ext i j; simp [Matrix.vandermonde,RadixTwo.dft,pow_mul]
 rw [he] at hh
 exact hh.symm
end ExactFourier.NewtonFourier

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem inverse {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) : Layered M⁻¹ d := by
 induction h with
 | identity => simpa using (Layered.identity (α := _))
 | mono M hM => exact Layered.mono _ hM.inverse
 | pair M hM => exact Layered.pair _ (Matrix.isUnit_nonsing_inv_iff.mpr hM)
 | mul hM hN ihM ihN =>
  rw [Matrix.mul_inv_rev]
  simpa only [Nat.add_comm] using ihN.mul ihM
 | reindex f hM ih =>
  rw [MatrixSymmetry.inverse_reindex f _ hM.unit]
  exact ih.reindex f
 | sum hM hN ihM ihN =>
  rw [MatrixSymmetry.inverse_sum _ _ hM.unit hN.unit]
  exact ihM.sum ihN
 | weaken h hde ih => exact ih.weaken hde

theorem conjugate {M N : Matrix α α ℂ} {d e : ℕ} (hM : Layered M d) (hN : Layered N e) :
 Layered (M*N*M⁻¹) (2*d+e) := by
 simpa only [show d+e+d=2*d+e by omega] using (hM.mul hN).mul hM.inverse
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem rect_diagonal (c : α→ℂ) : Layered (rectangularShear (Matrix.diagonal c)) 1 := by
 let M := fun i : α=>(!![1,c i;0,1] : Matrix (Fin 2) (Fin 2) ℂ)
 have hm : ∀ i,IsUnit (M i) := by
  intro i
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  change IsUnit ((!![1,c i;0,1] : Matrix (Fin 2) (Fin 2) ℂ).det)
  simp
 have h := (blockDiagonal M 1 (fun i=>Layered.pair (M i) (hm i))).reindex (twoProdEquiv α)
 have he : Matrix.reindex (twoProdEquiv α) (twoProdEquiv α) (Matrix.blockDiagonal M)=
  rectangularShear (Matrix.diagonal c) := by
  ext i j
  cases i <;> cases j <;>
   simp [twoProdEquiv,Matrix.reindex_apply,Matrix.blockDiagonal,M,rectangularShear,Matrix.one_apply,Matrix.diagonal_apply]
 rw [he] at h
 exact h

theorem rect_add {G H : Matrix α β ℂ} {d e : ℕ}
 (hG : Layered (rectangularShear G) d) (hH : Layered (rectangularShear H) e) :
 Layered (rectangularShear (G+H)) (d+e) := by
 rw [← rectangularShear_mul]
 exact hG.mul hH

theorem rect_neg {G : Matrix α β ℂ} {d : ℕ}
 (hG : Layered (rectangularShear G) d) : Layered (rectangularShear (-G)) d := by
 rw [← rectangularShear_inv]
 exact hG.inverse

theorem rect_mul_right {M : Matrix β β ℂ} {G : Matrix α β ℂ} {d e : ℕ}
 (hM : Layered M d) (hG : Layered (rectangularShear G) e) :
 Layered (rectangularShear (G*M)) (2*d+e) := by
 let := hM.unit.invertible
 have h := ((identity.weaken (Nat.zero_le d)).sum hM.inverse).conjugate hG
 have he : Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 M⁻¹ * rectangularShear G *
  (Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 M⁻¹)⁻¹=rectangularShear (G*M) := by
  rw [MatrixSymmetry.inverse_sum _ _ isUnit_one hM.inverse.unit,Matrix.inv_inv_of_invertible]
  simp [rectangularShear,Matrix.fromBlocks_multiply,Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hM.unit)]
 rw [he] at h
 exact h
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem rect_first
    {α : Type} {β : Type} {γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (G : Matrix α β ℂ) :
 Matrix.reindex (Equiv.sumAssoc α β γ) (Equiv.sumAssoc α β γ)
  (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix γ γ ℂ)) =
 rectangularShear (Matrix.fromCols G (0 : Matrix α γ ℂ)) := by
 ext i j
 rcases i with i|(i|i) <;> rcases j with j|(j|j) <;>
  simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply]

theorem rect_last
    {α : Type} {β : Type} {γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (G : Matrix α γ ℂ) :
 Matrix.reindex (swapLast (α := α) (β := β) (γ := γ)) (swapLast (α := α) (β := β) (γ := γ))
  (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix β β ℂ)) =
 rectangularShear (Matrix.fromCols (0 : Matrix α β ℂ) G) := by
 ext i j
 rcases i with i|(i|i) <;> rcases j with j|(j|j) <;>
  simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply,swapLast]

theorem commutator_identity (G : Matrix α β ℂ) (H : Matrix β γ ℂ) :
 rectangularShear (Matrix.fromCols G (0 : Matrix α γ ℂ)) *
 Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 (rectangularShear H) *
 rectangularShear (Matrix.fromCols (-G) (0 : Matrix α γ ℂ)) *
 Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 (rectangularShear (-H)) =
 rectangularShear (Matrix.fromCols (0 : Matrix α β ℂ) (G*H)) := by
 simp only [rectangularShear,Matrix.fromBlocks_multiply,Matrix.mul_one,Matrix.one_mul,
  Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]
 ext i j
 rcases i with i|(i|i) <;> rcases j with j|(j|j) <;>
  simp [Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply,Finset.sum_add_distrib,
    Finset.sum_neg_distrib,add_mul]

theorem rect_product_stable {G : Matrix α β ℂ} {H : Matrix β γ ℂ} {d e : ℕ}
 (hG : Layered (rectangularShear G) d) (hH : Layered (rectangularShear H) e) :
 Layered (Matrix.fromBlocks (rectangularShear (G*H)) 0 0 (1 : Matrix β β ℂ)) (2*(d+e)) := by
 have hu := (hG.sum (identity.weaken (Nat.zero_le d))).reindex (Equiv.sumAssoc α β γ)
 rw [rect_first] at hu
 have hun := (hG.rect_neg.sum (identity.weaken (Nat.zero_le d))).reindex (Equiv.sumAssoc α β γ)
 rw [rect_first] at hun
 have hv := (identity.weaken (Nat.zero_le e) (α := α)).sum hH
 have hvn := (identity.weaken (Nat.zero_le e) (α := α)).sum hH.rect_neg
 have ht := ((hu.mul hv).mul hun).mul hvn
 rw [commutator_identity,←rect_last] at ht
 have hs := ht.reindex (swapLast (α := α) (β := β) (γ := γ)).symm
 simpa only [reindex_inverse,
  show d+e+d+e=2*(d+e) by omega] using hs
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem rect_transpose {G : Matrix α β ℂ} {d : ℕ}
 (hG : Layered (rectangularShear G) d) : Layered (rectangularShear G.transpose) d := by
 have h := hG.transpose.reindex (Equiv.sumComm α β)
 have he : Matrix.reindex (Equiv.sumComm α β) (Equiv.sumComm α β)
  (rectangularShear G).transpose=rectangularShear G.transpose := by
  ext i j
  cases i <;> cases j <;> simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply,eq_comm]
 rw [he] at h
 exact h

theorem embedded_injection (e : β↪α) :
 Embedded.matrix (e.sumMap (Function.Embedding.refl β))
 (rectangularShear (1 : Matrix β β ℂ)) =
 rectangularShear ((1 : Matrix α α ℂ).submatrix id e) := by
 classical
 let f := e.sumMap (Function.Embedding.refl β)
 have ho (i : α) (hi : i∉Set.range e) : (Sum.inl i : α⊕β)∉Set.range f := by
  rintro ⟨a,h⟩; cases a with
  | inl a => exact hi ⟨a,Sum.inl.inj h⟩
  | inr a => cases h
 ext i j
 rcases i with i|i <;> rcases j with j|j
 · by_cases hi : i∈Set.range e
   · obtain ⟨i,rfl⟩ := hi
     by_cases hj : j∈Set.range e
     · obtain ⟨j,rfl⟩ := hj
       change Embedded.matrix f _ (f (.inl i)) (f (.inl j))=_
       rw [Embedded.matrix_on]
       simp [rectangularShear,Matrix.one_apply,e.injective.eq_iff]
     · rw [Embedded.matrix_off_col f _ _ _ (ho j hj)]
       simp [rectangularShear,Matrix.one_apply]
   · rw [Embedded.matrix_off_row f _ _ _ (ho i hi)]
     simp [rectangularShear,Matrix.one_apply]
 · by_cases hi : i∈Set.range e
   · obtain ⟨i,rfl⟩ := hi
     change Embedded.matrix f _ (f (.inl i)) (f (.inr j))=_
     rw [Embedded.matrix_on]
     simp [rectangularShear,Matrix.one_apply,e.injective.eq_iff]
   · rw [Embedded.matrix_off_row f _ _ _ (ho i hi)]
     have hn : i≠e j := fun h=>hi ⟨j,h.symm⟩
     simp [rectangularShear,hn]
 · by_cases hj : j∈Set.range e
   · obtain ⟨j,rfl⟩ := hj
     change Embedded.matrix f _ (f (.inr i)) (f (.inl j))=_
     rw [Embedded.matrix_on]
     simp [rectangularShear]
   · rw [Embedded.matrix_off_col f _ _ _ (ho j hj)]
     simp [rectangularShear]
 · change Embedded.matrix f _ (f (.inr i)) (f (.inr j))=_
   rw [Embedded.matrix_on]
   simp [rectangularShear]

theorem rect_injection (e : β↪α) : Layered (rectangularShear ((1 : Matrix α α ℂ).submatrix id e)) 1 := by
 rw [← embedded_injection e]
 have h := rect_diagonal (fun _ : β=>(1 : ℂ))
 rw [Matrix.diagonal_one] at h
 exact h.embed _

theorem rect_projection (e : β↪α) : Layered (rectangularShear ((1 : Matrix α α ℂ).submatrix e id)) 1 := by
 simpa [Matrix.transpose_submatrix] using (rect_injection e).rect_transpose

theorem rect_submatrix_stable {M : Matrix γ γ ℂ} {d : ℕ}
 (hM : Layered M d) (e : α↪γ) (f : β↪γ) :
 Layered (Matrix.fromBlocks (rectangularShear (M.submatrix e f)) 0 0 (1 : Matrix γ γ ℂ)) (4*d+4) := by
 have hG := hM.rect_mul_right (rect_projection e)
 have h := hG.rect_product_stable (rect_injection f)
 have he : ((1 : Matrix γ γ ℂ).submatrix e id * M) * (1 : Matrix γ γ ℂ).submatrix id f=M.submatrix e f := by
  ext i j
  simp [Matrix.mul_apply,Matrix.one_apply]
 rw [he] at h
 simpa only [show 2*(2*d+1+1)=4*d+4 by omega] using h
end ExactFourier.Layered

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.RectStableAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Layered
variable {α β γ σ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype σ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq σ]

theorem stable_rect_add {G H : Matrix α β ℂ} {d e : ℕ}
 (hG : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) d)
 (hH : Layered (Matrix.fromBlocks (rectangularShear H) 0 0 (1 : Matrix σ σ ℂ)) e) :
 Layered (Matrix.fromBlocks (rectangularShear (G+H)) 0 0 (1 : Matrix σ σ ℂ)) (d+e) := by
 have h := hG.mul hH
 simpa [Matrix.fromBlocks_multiply,rectangularShear_mul] using h

theorem stable_rect_transpose {G : Matrix α β ℂ} {d : ℕ}
 (hG : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) d) :
 Layered (Matrix.fromBlocks (rectangularShear G.transpose) 0 0 (1 : Matrix σ σ ℂ)) d := by
 have h := hG.transpose.reindex ((Equiv.sumComm α β).sumCongr (Equiv.refl σ))
 have he : Matrix.reindex ((Equiv.sumComm α β).sumCongr (Equiv.refl σ))
   ((Equiv.sumComm α β).sumCongr (Equiv.refl σ))
   (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)).transpose=
   Matrix.fromBlocks (rectangularShear G.transpose) 0 0 (1 : Matrix σ σ ℂ) := by
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
    simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply,eq_comm]
 rw [he] at h
 exact h

theorem split_rows_left_matrix
    {α : Type} {β : Type} {γ : Type} {σ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype σ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq σ] (G : Matrix α γ ℂ) :
 Matrix.reindex (splitRowsLeft (β := β) (σ := σ)) (splitRowsLeft (β := β) (σ := σ))
  (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (β⊕σ) (β⊕σ) ℂ))=
 Matrix.fromBlocks (rectangularShear (Matrix.fromRows G (0 : Matrix β γ ℂ))) 0 0 (1 : Matrix σ σ ℂ) := by
 ext i j
 rcases i with ((i|i)|i)|i <;> rcases j with ((j|j)|j)|j <;>
  simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply,splitRowsLeft]

theorem split_rows_right_matrix
    {α : Type} {β : Type} {γ : Type} {σ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype σ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq σ] (H : Matrix β γ ℂ) :
 Matrix.reindex (splitRowsRight (α := α) (σ := σ)) (splitRowsRight (α := α) (σ := σ))
  (Matrix.fromBlocks (rectangularShear H) 0 0 (1 : Matrix (α⊕σ) (α⊕σ) ℂ))=
 Matrix.fromBlocks (rectangularShear (Matrix.fromRows (0 : Matrix α γ ℂ) H)) 0 0 (1 : Matrix σ σ ℂ) := by
 ext i j
 rcases i with ((i|i)|i)|i <;> rcases j with ((j|j)|j)|j <;>
  simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply,splitRowsLeft,splitRowsRight]

theorem stable_rect_split_rows {G : Matrix α γ ℂ} {H : Matrix β γ ℂ} {d e : ℕ}
 (hG : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (β⊕σ) (β⊕σ) ℂ)) d)
 (hH : Layered (Matrix.fromBlocks (rectangularShear H) 0 0 (1 : Matrix (α⊕σ) (α⊕σ) ℂ)) e) :
 Layered (Matrix.fromBlocks (rectangularShear (Matrix.fromRows G H)) 0 0 (1 : Matrix σ σ ℂ)) (d+e) := by
 have h1 := hG.reindex (splitRowsLeft (β := β) (σ := σ))
 have h2 := hH.reindex (splitRowsRight (α := α) (σ := σ))
 rw [split_rows_left_matrix] at h1
 rw [split_rows_right_matrix] at h2
 have h := h1.stable_rect_add h2
 have he : Matrix.fromRows G (0 : Matrix β γ ℂ)+Matrix.fromRows (0 : Matrix α γ ℂ) H=
  Matrix.fromRows G H := by ext i j; cases i <;> simp
 rw [he] at h
 exact h
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β σ τ α' β' σ' : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype τ]
 [Fintype α'] [Fintype β'] [Fintype σ']
 [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq τ]
 [DecidableEq α'] [DecidableEq β'] [DecidableEq σ']

theorem stable_reindex {G : Matrix α β ℂ} {d : ℕ}
 (h : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) d)
 (e : α≃α') (f : β≃β') (g : σ≃σ') :
 Layered (Matrix.fromBlocks (rectangularShear (Matrix.reindex e f G)) 0 0 (1 : Matrix σ' σ' ℂ)) d := by
 have hh := h.reindex ((e.sumCongr f).sumCongr g)
 have he : Matrix.reindex ((e.sumCongr f).sumCongr g) ((e.sumCongr f).sumCongr g)
  (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ))=
  Matrix.fromBlocks (rectangularShear (Matrix.reindex e f G)) 0 0 (1 : Matrix σ' σ' ℂ) := by
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
   simp [rectangularShear,Matrix.reindex_apply,Matrix.one_apply]
 rw [he] at hh
 exact hh

theorem stable_extra {G : Matrix α β ℂ} {d : ℕ}
 (h : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) d) :
 Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (σ⊕τ) (σ⊕τ) ℂ)) d := by
 have hh := (h.sum (identity.weaken (Nat.zero_le d))).reindex (Equiv.sumAssoc (α⊕β) σ τ)
 have he : Matrix.reindex (Equiv.sumAssoc (α⊕β) σ τ) (Equiv.sumAssoc (α⊕β) σ τ)
  (Matrix.fromBlocks (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) 0 0
   (1 : Matrix τ τ ℂ))=Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (σ⊕τ) (σ⊕τ) ℂ) := by
  ext i j
  rcases i with i|i|i <;> rcases j with j|j|j <;>
   simp [Matrix.reindex_apply,Matrix.one_apply]
 rw [he] at hh
 exact hh

theorem stable_scratch_mono {G : Matrix α β ℂ} {d s t : ℕ}
 (h : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (Fin s) (Fin s) ℂ)) d)
 (hst : s≤t) :
 Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (Fin t) (Fin t) ℂ)) d := by
 have hh := (h.stable_extra (τ := Fin (t-s))).stable_reindex (Equiv.refl α) (Equiv.refl β)
  (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hst)))
 simpa using hh

theorem stable_zero {G : Matrix α β ℂ} {d : ℕ}
 (h : Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (Fin 0) (Fin 0) ℂ)) d) :
 Layered (rectangularShear G) d := by
 have hh := h.reindex (Equiv.sumEmpty (α⊕β) (Fin 0))
 have he : Matrix.reindex (Equiv.sumEmpty (α⊕β) (Fin 0)) (Equiv.sumEmpty (α⊕β) (Fin 0))
  (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (Fin 0) (Fin 0) ℂ))=rectangularShear G := by
  ext i j; rfl
 rw [he] at hh
 exact hh

theorem stable_empty_rows (G : Matrix (Fin 0) β ℂ) (d : ℕ) :
 Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) d := by
 have he : Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)=1 := by
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
    simp [rectangularShear,Matrix.one_apply] ; exact Fin.elim0 ‹Fin 0›
 rw [he]
 exact identity.weaken (Nat.zero_le d)

theorem stable_empty_cols (G : Matrix α (Fin 0) ℂ) (d : ℕ) :
 Layered (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix σ σ ℂ)) d := by
 exact (stable_empty_rows G.transpose d (σ := σ)).stable_rect_transpose

theorem stable_rows_nat {a b e s d f : ℕ} (M : ℕ→ℕ→ℂ)
 (hG : Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin (b+s)) (Fin (b+s)) ℂ)) d)
 (hH : Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin b=>fun j : Fin e=>M (a+i.val) j.val))
  0 0 (1 : Matrix (Fin (a+s)) (Fin (a+s)) ℂ)) f) :
 Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin (a+b)=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin s) (Fin s) ℂ)) (d+f) := by
 have h1 := hG.stable_reindex (Equiv.refl _) (Equiv.refl _) finSumFinEquiv.symm
 have h2 := hH.stable_reindex (Equiv.refl _) (Equiv.refl _) finSumFinEquiv.symm
 change Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin b⊕Fin s) (Fin b⊕Fin s) ℂ)) d at h1
 change Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin b=>fun j : Fin e=>M (a+i.val) j.val))
  0 0 (1 : Matrix (Fin a⊕Fin s) (Fin a⊕Fin s) ℂ)) f at h2
 have hh := (h1.stable_rect_split_rows h2).stable_reindex finSumFinEquiv (Equiv.refl _) (Equiv.refl _)
 have he : Matrix.reindex finSumFinEquiv (Equiv.refl (Fin e))
  (Matrix.fromRows (fun i : Fin a=>fun j : Fin e=>M i.val j.val)
   (fun i : Fin b=>fun j : Fin e=>M (a+i.val) j.val))=
  (fun i : Fin (a+b)=>fun j : Fin e=>M i.val j.val) := by
  ext i j
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [Matrix.reindex_apply,Matrix.fromRows]
 rw [he] at hh
 exact hh
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

namespace SumLayered
 theorem single {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) : SumLayered M d 1 := by
  exact ⟨[M],by simp,by simp,by simpa⟩
 theorem weaken {M : Matrix α α ℂ} {d e c f : ℕ} (h : SumLayered M d c)
  (hde : d≤e) (hcf : c≤f) : SumLayered M e f := by
  obtain ⟨L,hL,he,hd⟩ := h
  exact ⟨L,hL.trans hcf,he,fun N hn=>(hd N hn).weaken hde⟩
 theorem add {M N : Matrix α α ℂ} {d c e : ℕ} (hM : SumLayered M d c) (hN : SumLayered N d e) :
  SumLayered (M+N) d (c+e) := by
  obtain ⟨L,hL,rfl,hd⟩ := hM
  obtain ⟨K,hK,rfl,he⟩ := hN
  refine ⟨L++K, ?_,by simp,?_⟩
  · simpa only [List.length_append] using Nat.add_le_add hL hK
  · intro M h; rcases List.mem_append.mp h with h|h
    · exact hd M h
    · exact he M h
 theorem transpose {M : Matrix α α ℂ} {d c : ℕ} (hM : SumLayered M d c) :
  SumLayered M.transpose d c := by
  obtain ⟨L,hL,rfl,hd⟩ := hM
  refine ⟨L.map Matrix.transpose,by simpa using hL,?_,?_⟩
  · clear hL hd
    induction L with
    | nil => simp
    | cons A L ih => simp [ih,Matrix.transpose_add]
  · intro M h; obtain ⟨N,hN,rfl⟩:=List.mem_map.mp h
    exact (hd N hN).transpose
 theorem mul {M N : Matrix α α ℂ} {d e c f : ℕ} (hM : SumLayered M d c) (hN : SumLayered N e f) :
  SumLayered (M*N) (d+e) (c*f) := by
  obtain ⟨L,hL,rfl,hd⟩ := hM
  obtain ⟨K,hK,rfl,he⟩ := hN
  let P := L.flatMap (fun A=>K.map (fun B=>A*B))
  have hlen : P.length=L.length*K.length := by
   dsimp [P]; induction L with
   | nil => simp
   | cons A L ih => simp [Nat.add_mul,Nat.add_comm]
  refine ⟨P,hlen.le.trans (Nat.mul_le_mul hL hK),?_,?_⟩
  · dsimp [P]
    clear hL hd hlen P hK he
    have hm (A : Matrix α α ℂ) : (K.map (fun B=>A*B)).sum=A*K.sum := by
     induction K with
     | nil => simp
     | cons B K ih => simp_all [mul_add]
    induction L with
    | nil => simp
    | cons A L ih => simp [ih,hm,add_mul]
  · intro M h
    obtain ⟨A,hA,h⟩:=List.mem_flatMap.mp h
    obtain ⟨B,hB,rfl⟩:=List.mem_map.mp h
    exact (hd A hA).mul (he B hB)

 theorem diagonal (c : α→ℂ) : SumLayered (Matrix.diagonal c) 1 2 := by
  classical
  obtain ⟨lam,hlam⟩ := Infinite.exists_notMem_finset (insert 0 (Finset.univ.image c))
  simp only [Finset.mem_insert,not_or] at hlam
  have h0 : lam≠0 := hlam.1
  have hc : ∀ i,c i-lam≠0 := by
   intro i h; apply hlam.2
   exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,sub_eq_zero.mp h⟩
  let A := Matrix.diagonal (fun i=>c i-lam)
  let B := Matrix.diagonal (fun _ : α=>lam)
  have he : A+B=Matrix.diagonal c := by ext i j; by_cases h : i=j <;> simp [A,B,h]
  rw [←he]
  exact (single (Layered.mono A (MonomialMatrix.diagonal _ hc))).add
    (single (Layered.mono B (MonomialMatrix.diagonal _ (fun _=>h0))))

 theorem submatrix_stable {M : Matrix γ γ ℂ} {d c : ℕ} (hM : SumLayered M d c)
  (e : α↪γ) (f : β↪γ) :
  Layered (Matrix.fromBlocks (rectangularShear (M.submatrix e f)) 0 0 (1 : Matrix γ γ ℂ)) (c*(4*d+4)) := by
  obtain ⟨L,hL,rfl,hd⟩:=hM
  have hh : ∀ L : List (Matrix γ γ ℂ), (∀ M∈L,Layered M d) →
   Layered (Matrix.fromBlocks (rectangularShear (L.sum.submatrix e f)) 0 0 (1 : Matrix γ γ ℂ)) (L.length*(4*d+4)) := by
   intro L h
   induction L with
   | nil =>
    simpa [rectangularShear] using (Layered.identity (α := (α⊕β)⊕γ))
   | cons M L ih =>
    have hM := (h M (by simp)).rect_submatrix_stable e f
    have hL := ih (fun N hn=>h N (by simp [hn]))
    have ht := hM.mul hL
    have he : Matrix.fromBlocks (rectangularShear (M.submatrix e f)) 0 0 (1 : Matrix γ γ ℂ) *
      Matrix.fromBlocks (rectangularShear (L.sum.submatrix e f)) 0 0 (1 : Matrix γ γ ℂ)=
      Matrix.fromBlocks (rectangularShear ((M+L.sum).submatrix e f)) 0 0 (1 : Matrix γ γ ℂ) := by
     simp [Matrix.fromBlocks_multiply,rectangularShear_mul,Matrix.submatrix_add]
    rw [he] at ht
    simpa [Nat.add_mul,Nat.add_comm] using ht
  exact (hh L hd).weaken (Nat.mul_le_mul_right _ hL)
end SumLayered
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier.RadixTwo
open Polynomial
open scoped BigOperators

theorem convolution_sumLayered (k : ℕ) (f : ℂ[X]) : SumLayered (convolutionMatrix k f) (4*k+1) 2 := by
 have hω : IsPrimitiveRoot (zeta (2^k)) (2^k) := Complex.isPrimitiveRoot_exp _ (by positivity)
 have h := ((SumLayered.single (dft_layers k _ hω.inv)).mul
  (SumLayered.diagonal (fun i : Fin (2^k)=>((2^k : ℕ) : ℂ)⁻¹*f.eval ((zeta (2^k))^i.val)))).mul
  (SumLayered.single (dft_layers k _ hω))
 simpa only [convolutionMatrix,show 2*k+1+2*k=4*k+1 by omega, Nat.one_mul,Nat.mul_one] using h

theorem convolution_mulVec (k : ℕ) (f : ℂ[X]) (x : Fin (2^k)→ℂ)
 (hx : (f*Polynomial.ofFn (2^k) x).natDegree < 2^k) :
 (convolutionMatrix k f).mulVec x =fun i=>(f*Polynomial.ofFn (2^k) x).coeff i.val := by
 have hω : IsPrimitiveRoot (zeta (2^k)) (2^k) := Complex.isPrimitiveRoot_exp _ (by positivity)
 have h := convolution_formula (by positivity : 0 < 2^k) _ hω f (Polynomial.ofFn (2^k) x) hx
 change eval (2^k) (zeta (2^k))⁻¹ _ = _ at h
 dsimp only [convolutionMatrix]
 rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
 change eval (2^k) (zeta (2^k))⁻¹ _=_
 rw [←h]
 congr 1
 funext i
 rw [Matrix.mulVec_diagonal]
 change _*eval (2^k) (zeta (2^k)) x i=_
 rw [eval_ofFn]

theorem ofFn_single {n : ℕ} (j : Fin n) :
 Polynomial.ofFn n (Pi.single j (1 : ℂ))=Polynomial.monomial j.val 1 := by
 ext i
 by_cases hi : i < n
 · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hi]
   simp [Polynomial.coeff_monomial,Pi.single_apply,Fin.ext_iff,eq_comm]
 · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
   have hn : j.val≠i := by have := j.isLt; omega
   simp [Polynomial.coeff_monomial,hn]

theorem convolution_entry (k : ℕ) (f : ℂ[X]) (i j : Fin (2^k))
 (hj : f.natDegree+j.val < 2^k) :
 convolutionMatrix k f i j=if j.val ≤ i.val then f.coeff (i.val-j.val) else 0 := by
 have hx : (f*Polynomial.ofFn (2^k) (Pi.single j (1 : ℂ))).natDegree < 2^k := by
  rw [ofFn_single]
  exact (Polynomial.natDegree_mul_le.trans (Nat.add_le_add_left (Polynomial.natDegree_monomial_le (1 : ℂ)) _)).trans_lt hj
 have h := congrFun (convolution_mulVec k f (Pi.single j 1) hx) i
 rw [Matrix.mulVec_single_one,ofFn_single] at h
 change convolutionMatrix k f i j = _ at h
 rw [h]
 rw [Polynomial.monomial_one_right_eq_X_pow,Polynomial.coeff_mul_X_pow']
end ExactFourier.RadixTwo

end
end

section
noncomputable section
namespace ExactFourier
open scoped BigOperators

theorem sum_initial {a n : ℕ} (h : a≤n) (f : Fin n→ℂ) :
 (∑i : Fin n,if i.val<a then f i else 0)=∑i : Fin a,f (initialEmbedding h i) := by
 classical
 let e:=initialEmbedding h
 have hi : Function.Injective e:=e.injective
 have hr : ∀ j : Fin n,j∈Finset.univ.image e ↔ j.val<a := by
  intro j
  constructor
  · intro hj; obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hj; exact i.isLt
  · intro hj; exact Finset.mem_image.mpr ⟨⟨j.val,hj⟩,Finset.mem_univ _,rfl⟩
 rw [←Finset.sum_image (fun i _ j _ he=>hi he)]
 rw [←Finset.sum_subset (Finset.subset_univ (Finset.univ.image e))]
 · apply Finset.sum_congr rfl
   intro j hj
   rw [ite_eq_left ((hr j).mp hj)]
 · intro j hj hn
   rw [ite_eq_right (mt ((hr j).mpr) hn)]

theorem compress_product {a b e n : ℕ} (ha : a≤n) (hb : b≤n) (he : e≤n)
 (M N : Matrix (Fin n) (Fin n) ℂ) :
 (M * Matrix.diagonal (fun i : Fin n=>if i.val<e then (1 : ℂ) else 0) * N).submatrix
  (initialEmbedding ha) (initialEmbedding hb)=
 (M.submatrix (initialEmbedding ha) (initialEmbedding he)) *
 (N.submatrix (initialEmbedding he) (initialEmbedding hb)) := by
 ext i j
 rw [Matrix.submatrix_apply,Matrix.mul_apply]
 simp only [Matrix.mul_diagonal]
 have h := sum_initial he (fun l=>M (initialEmbedding ha i) l*N l (initialEmbedding hb j))
 simpa [Matrix.mul_apply,Matrix.submatrix_apply,ite_mul,mul_ite] using h
end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.DisplacementKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.Displacement
open scoped BigOperators

theorem kernel_succ (v w : ℕ→ℂ) (i j : ℕ) :
 kernel v w (i+1) (j+1)=v (i+1)*w (j+1)+kernel v w i j := by
 rw [kernel,show min (i+1) (j+1)+1=(min i j+1)+1 by omega,Finset.sum_range_succ']
 simp only [Nat.add_sub_add_right,Nat.sub_zero]
 rw [kernel,add_comm]

theorem kernel_eq_mul (v w : ℕ→ℂ) (a e : ℕ) :
 (fun i : Fin a=>fun j : Fin e=>kernel v w i.val j.val)=lower v a e*(lower w e e).transpose := by
 ext i j
 rw [Matrix.mul_apply]
 simp only [lower,Matrix.transpose_apply]
 rw [Fin.sum_univ_eq_sum_range (fun l=>(if l ≤ i.val then v (i.val-l) else 0)*(if l ≤ j.val then w (j.val-l) else 0))]
 have hs : min i.val j.val+1 ≤ e := by have := j.isLt; omega
 have he : (∑l∈Finset.range e, (if l ≤ i.val then v (i.val-l) else 0)*(if l ≤ j.val then w (j.val-l) else 0))=
  ∑l∈Finset.range (min i.val j.val+1),v (i.val-l)*w (j.val-l) := by
  rw [←Finset.sum_subset (Finset.range_mono hs)]
  · apply Finset.sum_congr rfl
    intro l hl
    have hl' := Finset.mem_range.mp hl
    simp [show l ≤ i.val by omega,show l ≤ j.val by omega]
  · intro l hl hn
    have hn' : ¬l < min i.val j.val+1 := fun hh=>hn (Finset.mem_range.mpr hh)
    by_cases hi : l ≤ i.val
    · simp [hi,show ¬l ≤ j.val by omega]
    · simp [hi]
 simpa [lower,kernel,Matrix.transpose_apply] using he.symm

/-- The exact rank-three displacement reconstruction, with only the stated
interior outer-product recurrence; no analytic or generic-position premise. -/
theorem reconstruct (a e : ℕ) (ha : 0 < a) (he : 0 < e) (M : ℕ→ℕ→ℂ) (v w : ℕ→ℂ)
 (hrec : ∀ i j, i+1 < a → j+1 < e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) :
 let row := fun j=>M 0 j-v 0*w j
 let col := fun i=>if i=0 then 0 else M i 0-v i*w 0
 ∀ i j, i < a → j < e → M i j=kernel v w i j+kernel delta row i j+kernel col delta i j := by
 obtain ⟨rows, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
 obtain ⟨columns, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
 dsimp only
 intro i
 induction i with
 | zero =>
  intro j hi hj
  simp [delta]
 | succ i ih =>
  intro j hi hj
  cases j with
  | zero => simp [delta]
  | succ j =>
   rw [hrec i j hi hj,kernel_succ,kernel_succ,kernel_succ,ih j (by omega) (by omega)]
   simp only [delta,show i+1≠0 by omega,show j+1≠0 by omega,ite_false,zero_mul,mul_zero,zero_add]
   ring
end ExactFourier.Displacement

end
end

section
noncomputable section
namespace ExactFourier.Displacement
open Polynomial RadixTwo

theorem coeff_ofFn_extend (a : ℕ) (v : Fin a→ℂ) : (Polynomial.ofFn a v).coeff=extendVector v := by
 funext i
 by_cases hi : i < a
 · simp [Polynomial.ofFn_coeff_eq_val_of_lt _ hi,extendVector,hi]
 · simp [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega : a ≤ i),extendVector,hi]

theorem convolution_submatrix (a e k : ℕ) (ha : 0 < a) (h : a+e ≤ 2^k) (haL : a ≤ 2^k) (heL : e ≤ 2^k)
 (v : Fin a→ℂ) :
 (convolutionMatrix k (Polynomial.ofFn a v)).submatrix (initialEmbedding haL) (initialEmbedding heL)=lower (extendVector v) a e := by
 ext i j
 dsimp only [Matrix.submatrix_apply,lower]
 rw [convolution_entry]
 · rw [coeff_ofFn_extend]
   rfl
 · have hdeg:=Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ a) v
   have hj:=j.isLt
   change (Polynomial.ofFn a v).natDegree+j.val < 2^k
   omega

theorem fullKernel_sumLayered (k a e : ℕ) (v : Fin a→ℂ) (w : Fin e→ℂ) :
 SumLayered (fullKernel k a e v w) (8*k+3) 8 := by
 have h := ((convolution_sumLayered k (Polynomial.ofFn a v)).mul
  (SumLayered.diagonal (fun i : Fin (2^k)=>if i.val < e then 1 else 0))).mul
  (convolution_sumLayered k (Polynomial.ofFn e w)).transpose
 simpa only [fullKernel,show 4*k+1+1+(4*k+1)=8*k+3 by omega,show 2*2*2=8 by decide] using h

theorem kernel_submatrix (a e k : ℕ) (ha : 0 < a) (he : 0 < e) (h : 2*(a+e) ≤ 2^k)
 (v : Fin a→ℂ) (w : Fin e→ℂ) :
 (fullKernel k a e v w).submatrix (initialEmbedding (by omega : a ≤ 2^k)) (initialEmbedding (by omega : e ≤ 2^k))=
 (fun i : Fin a=>fun j : Fin e=>kernel (extendVector v) (extendVector w) i.val j.val) := by
 rw [kernel_eq_mul,fullKernel,compress_product (by omega) (by omega) (by omega : e ≤ 2^k)]
 rw [convolution_submatrix a e k ha (by omega) (by omega) (by omega)]
 have heq : ((convolutionMatrix k (Polynomial.ofFn e w)).transpose).submatrix
    (initialEmbedding (by omega : e ≤ 2^k)) (initialEmbedding (by omega : e ≤ 2^k))=
    (lower (extendVector w) e e).transpose := by
  rw [←Matrix.transpose_submatrix]
  rw [convolution_submatrix e e k he (by omega) (by omega) (by omega)]
 rw [heq]

end ExactFourier.Displacement

end
end

section
noncomputable section
namespace ExactFourier.Displacement

theorem kernel_congr (v v' w w' : ℕ→ℂ) (i j : ℕ)
 (hv : ∀ l, l ≤ i → v l=v' l) (hw : ∀ l, l ≤ j → w l=w' l) : kernel v w i j=kernel v' w' i j := by
 apply Finset.sum_congr rfl
 intro l hl
 rw [hv _ (Nat.sub_le _ _),hw _ (Nat.sub_le _ _)]

theorem kernel_restrict (v w : ℕ→ℂ) (a e : ℕ) (i : Fin a) (j : Fin e) :
 kernel (extendVector (fun u : Fin a=>v u.val)) (extendVector (fun v : Fin e=>w v.val)) i.val j.val=
 kernel v w i.val j.val := by
 apply kernel_congr
 · intro l hl; simp [extendVector,show l<a by have := i.isLt; omega]
 · intro l hl; simp [extendVector,show l<e by have := j.isLt; omega]

theorem stable_of_displacement (a e k : ℕ) (ha : 0<a) (he : 0<e) (h : 2*(a+e) ≤ 2^k)
 (M : ℕ→ℕ→ℂ) (v w : ℕ→ℂ)
 (hrec : ∀ i j,i+1<a → j+1<e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) :
 Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin (2^k)) (Fin (2^k)) ℂ)) (768*k+384) := by
 let row := fun j=>M 0 j-v 0*w j
 let col := fun i=>if i=0 then 0 else M i 0-v i*w 0
 let V:=fullKernel k a e (fun i=>v i.val) (fun j=>w j.val)
 let R:=fullKernel k a e (fun i=>delta i.val) (fun j=>row j.val)
 let C:=fullKernel k a e (fun i=>col i.val) (fun j=>delta j.val)
 have hL : SumLayered (V+R+C) (8*k+3) 24 :=
  ((fullKernel_sumLayered ..).add (fullKernel_sumLayered ..)).add (fullKernel_sumLayered ..)
 have heq : (V+R+C).submatrix (initialEmbedding (by omega : a ≤ 2^k)) (initialEmbedding (by omega : e ≤ 2^k))=
   (fun i : Fin a=>fun j : Fin e=>M i.val j.val) := by
  ext i j
  change V (initialEmbedding _ i) (initialEmbedding _ j) +
    R (initialEmbedding _ i) (initialEmbedding _ j) +
    C (initialEmbedding _ i) (initialEmbedding _ j) = _
  have hV := congr_fun (congr_fun (kernel_submatrix a e k ha he h (fun i=>v i.val) (fun j=>w j.val)) i) j
  have hR := congr_fun (congr_fun (kernel_submatrix a e k ha he h (fun i=>delta i.val) (fun j=>row j.val)) i) j
  have hC := congr_fun (congr_fun (kernel_submatrix a e k ha he h (fun i=>col i.val) (fun j=>delta j.val)) i) j
  change V _ _ = _ at hV
  change R _ _ = _ at hR
  change C _ _ = _ at hC
  rw [hV,hR,hC,kernel_restrict,kernel_restrict,kernel_restrict]
  exact (reconstruct a e ha he M v w hrec i.val j.val i.isLt j.isLt).symm
 have hs := hL.submatrix_stable (initialEmbedding (by omega : a ≤ 2^k)) (initialEmbedding (by omega : e ≤ 2^k))
 rw [heq] at hs
 simpa only [show 24*(4*(8*k+3)+4)=768*k+384 by omega] using hs
end ExactFourier.Displacement

end
end

section
noncomputable section
namespace ExactFourier.Displacement
open Layered

theorem small_stable (a e s c k : ℕ) (ha : a≤c) (he : e≤c)
 (hfft : 4*c≤2^k) (hspace : 2^k+2*c≤a+e+s)
 (M : ℕ→ℕ→ℂ) (v w : ℕ→ℂ)
 (hrec : ∀ i j,i+1<a → j+1<e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) :
 Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin s) (Fin s) ℂ)) (768*k+384) := by
 by_cases ha0 : a=0
 · subst a; exact stable_empty_rows _ _
 by_cases he0 : e=0
 · subst e; exact stable_empty_cols _ _
 exact (stable_of_displacement a e k (by omega) (by omega) (by omega) M v w hrec).stable_scratch_mono (by omega)

theorem row_chunks (p a e s c k : ℕ) (ha : a≤p*c) (he : e≤c)
 (hfft : 4*c≤2^k) (hspace : 2^k+2*c≤a+e+s)
 (M : ℕ→ℕ→ℂ) (v w : ℕ→ℂ)
 (hrec : ∀ i j,i+1<a → j+1<e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) :
 Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin s) (Fin s) ℂ)) (p*(768*k+384)) := by
 induction p generalizing a s M v with
 | zero =>
  have hz : a=0 := by omega
  subst a; exact stable_empty_rows _ _
 | succ p ih =>
  by_cases hac : a≤c
  · exact (small_stable a e s c k hac he hfft hspace M v w hrec).weaken (by
     have := Nat.le_mul_of_pos_left (768*k+384) (Nat.succ_pos p)
     omega)
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hac))
  have h1 := small_stable c e (b+s) c k (le_refl _) he hfft (by omega) M v w
   (fun i j hi hj=>hrec i j (by omega) hj)
  have h2 := ih b (c+s) (by nlinarith [ha]) (by omega)
   (fun i j=>M (c+i) j) (fun i=>v (c+i)) (by
    intro i j hi hj
    simpa only [Nat.add_assoc] using hrec (c+i) j (by omega) hj)
  have hh := stable_rows_nat M h1 h2
  convert hh using 1; first | rfl | ext i j | ring

theorem all_chunks (q p a e s c k : ℕ) (ha : a≤p*c) (he : e≤q*c)
 (hfft : 4*c≤2^k) (hspace : 2^k+2*c≤a+e+s)
 (M : ℕ→ℕ→ℂ) (v w : ℕ→ℂ)
 (hrec : ∀ i j,i+1<a → j+1<e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) :
 Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  0 0 (1 : Matrix (Fin s) (Fin s) ℂ)) (q*p*(768*k+384)) := by
 induction q generalizing e s M w with
 | zero =>
  have hz : e=0 := by omega
  subst e; exact stable_empty_cols _ _
 | succ q ih =>
  by_cases hec : e≤c
  · exact (row_chunks p a e s c k ha hec hfft hspace M v w hrec).weaken (by
     have := Nat.le_mul_of_pos_left (p*(768*k+384)) (Nat.succ_pos q)
     nlinarith)
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hec))
  have h1 := row_chunks p a c (b+s) c k ha (le_refl _) hfft (by omega) M v w
   (fun i j hi hj=>hrec i j hi (by omega))
  have h2 := ih b (c+s) (by nlinarith [he]) (by omega)
   (fun i j=>M i (c+j)) (fun j=>w (c+j)) (by
    intro i j hi hj
    simpa only [Nat.add_assoc] using hrec i (c+j) hi (by omega))
  have hh := stable_rows_nat (fun i j=>M j i) h1.stable_rect_transpose h2.stable_rect_transpose
  have hh := hh.stable_rect_transpose
  change Layered (Matrix.fromBlocks (rectangularShear (fun i : Fin a=>fun j : Fin (c+b)=>M i.val j.val))
   0 0 (1 : Matrix (Fin s) (Fin s) ℂ)) (p*(768*k+384)+q*p*(768*k+384)) at hh
  have hn : p*(768*k+384)+q*p*(768*k+384)=(q+1)*p*(768*k+384) := by ring
  rw [hn] at hh
  exact hh
end ExactFourier.Displacement

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem rect_single (i : α) (j : β) (c : ℂ) :
 Layered (rectangularShear (Matrix.single i j c)) 1 := by
 have hh : (Sum.inl i : α⊕β)≠Sum.inr j := by simp
 have h := (Layered.pair (!![1,c;0,1]) (by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  simp)).embed (Embedded.pair (Sum.inl i) (Sum.inr j) hh)
 rw [Embedded.pair_matrix] at h
 have he : (1 : Matrix (α⊕β) (α⊕β) ℂ)+Matrix.single (Sum.inl i) (Sum.inr j) c+
  Matrix.single (Sum.inr j) (Sum.inl i) 0=rectangularShear (Matrix.single i j c) := by
  ext a b
  cases a <;> cases b <;> simp [rectangularShear,Matrix.single,Matrix.one_apply]
 rw [he] at h
 exact h

theorem rect_finset_sum {τ : Type} (s : Finset τ) (G : τ→Matrix α β ℂ) (d : τ→ℕ)
 (h : ∀ i∈s,Layered (rectangularShear (G i)) (d i)) :
 Layered (rectangularShear (∑ i∈s,G i)) (∑ i∈s,d i) := by
 classical
 induction s using Finset.induction_on with
 | empty =>
  simp
  have he : rectangularShear (0 : Matrix α β ℂ)=1 := by
   ext i j; cases i <;> cases j <;> simp [rectangularShear,Matrix.one_apply]
  rw [he]
  exact identity
 | @insert a s ha ih =>
  rw [Finset.sum_insert ha,Finset.sum_insert ha]
  exact (h a (by simp)).rect_add (ih (fun i hi=>h i (by simp [hi])))

theorem rect_dense (G : Matrix α β ℂ) :
 Layered (rectangularShear G) (Fintype.card α*Fintype.card β) := by
 classical
 have hh := rect_finset_sum (Finset.univ : Finset (α×β))
  (fun ij=>Matrix.single ij.1 ij.2 (G ij.1 ij.2)) (fun _=>1)
  (fun ij _=>rect_single ij.1 ij.2 _)
 have he : (∑ ij : α×β,Matrix.single ij.1 ij.2 (G ij.1 ij.2))=G := by
  ext i j
  simp only [Matrix.sum_apply]
  simp [Matrix.single,Fintype.sum_prod_type,ite_and]
 simpa only [he,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,Fintype.card_prod] using hh
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.Displacement
open Layered
/-- Exact-width displacement shear; dirty scratch is borrowed internally. -/
theorem exact_width (a e : ℕ) (M : ℕ→ℕ→ℂ) (v w : ℕ→ℂ)
 (hrec : ∀ i j,i+1<a → j+1<e → M (i+1) (j+1)=M i j+v (i+1)*w (j+1)) :
 Layered (rectangularShear (fun i : Fin a=>fun j : Fin e=>M i.val j.val))
  (2097152*(Nat.log 2 (a+e)+1)) := by
 by_cases hr : a+e<16
 · exact (rect_dense _).weaken (by simp only [Fintype.card_fin]; nlinarith [Nat.zero_le (Nat.log 2 (a+e))])
 let c := (a+e)/16
 have hc : 0<c := Nat.div_pos (by omega) (by decide)
 have hc16 : 16*c≤a+e := by simpa [c,Nat.mul_comm] using Nat.div_mul_le_self (a+e) 16
 have hcupper : a+e<16*(c+1) := by
  have h := Nat.mod_lt (a+e) (by decide : 0<16)
  have hh := Nat.mod_add_div (a+e) 16
  dsimp [c]
  omega
 let k := Nat.log 2 (4*c)+1
 have hfft : 4*c≤2^k := by
  exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) (4*c))
 have hkpow : 2^k≤8*c := by
  have hh := Nat.pow_log_le_self 2 (by omega : 4*c≠0)
  dsimp [k]
  rw [pow_succ]
  omega
 have hk : k≤Nat.log 2 (a+e)+1 := by
  dsimp [k]
  exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) _
 have hh := all_chunks 32 32 a e 0 c k (by nlinarith) (by nlinarith) hfft (by omega) M v w hrec
 exact hh.stable_zero.weaken (by nlinarith)
end ExactFourier.Displacement

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.ToeplitzCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.ToeplitzLayers
open scoped BigOperators
open CoefficientTime

theorem cross_succ (s : ℕ) (h g : ℕ→ℂ) (i j : ℕ) (hi : s ≤ i) (hj : j+1 < s) :
 cross s h g (i+1) (j+1)=cross s h g i j-h (i+1-s)*g (s-(j+1)) := by
 have hs : s-j=(s-(j+1))+1 := by omega
 unfold cross
 rw [hs,Finset.sum_range_succ]
 simp only [Nat.add_sub_add_right]
 have he : i-j-(s-(j+1))=i+1-s := by omega
 rw [he]
 ring

theorem sum_upper_shift (s j : ℕ) (hj : j ≤  s) (f g : ℕ→ℂ) :
 (∑l∈Finset.range s,f l*(if j ≤  l then g (l-j) else 0))=
 ∑l∈Finset.range (s-j),f (j+l)*g l := by
 conv_lhs => rw [show s=j+(s-j) by omega,Finset.sum_range_add]
 have hz : (∑l∈Finset.range j,f l*(if j ≤  l then g (l-j) else 0))=0 := by
  apply Finset.sum_eq_zero
  intro l hl
  simp [show ¬j ≤  l by have := Finset.mem_range.mp hl; omega]
 rw [hz,zero_add]
 apply Finset.sum_congr rfl
 intro l hl
 simp

theorem cross_mul (s a : ℕ) (h g : PowerSeries ℂ) :
 lowerCross s a (PowerSeries.coeff · h) * truncMatrix s g =
 (fun i : Fin a=>fun j : Fin s=>cross s (PowerSeries.coeff · h) (PowerSeries.coeff · g) (s+i.val) j.val) := by
 ext i j
 simp only [Matrix.mul_apply,lowerCross,truncMatrix]
 rw [Fin.sum_univ_eq_sum_range (fun l=>PowerSeries.coeff (s+i.val-l) h *
  (if j.val ≤  l then PowerSeries.coeff (l-j.val) g else 0)) s,
  sum_upper_shift s j.val (Nat.le_of_lt j.isLt)
    (fun l=>PowerSeries.coeff (s+i.val-l) h) (fun l=>PowerSeries.coeff l g)]
 unfold cross
 apply Finset.sum_congr rfl
 intro l hl
 rw [Nat.sub_add_eq]

end ExactFourier.ToeplitzLayers

end
end

section
noncomputable section
namespace ExactFourier.ToeplitzLayers
open Layered CoefficientTime

theorem trunc_split (s a : ℕ) (f : PowerSeries ℂ) :
 Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (truncMatrix (s+a) f)=
 Matrix.fromBlocks (truncMatrix s f) 0 (lowerCross s a (PowerSeries.coeff · f)) (truncMatrix a f) := by
 ext i j
 rcases i with i|i <;> rcases j with j|j
 · simp [Matrix.reindex_apply,truncMatrix]
 · simp [Matrix.reindex_apply,truncMatrix,show ¬ s+j.val ≤ i.val by have := i.isLt; omega]
 · simp [Matrix.reindex_apply,truncMatrix,lowerCross,show j.val ≤ s+i.val by have := j.isLt; omega]
 · simp [Matrix.reindex_apply,truncMatrix,show s+i.val-(s+j.val)=i.val-j.val by omega]

theorem lower_shear {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
 {G : Matrix α β ℂ} {d : ℕ} (h : Layered (rectangularShear G) d) :
 Layered (Matrix.fromBlocks (1 : Matrix β β ℂ) 0 G (1 : Matrix α α ℂ)) d := by
 have hh := h.reindex (Equiv.sumComm α β)
 have he : Matrix.reindex (Equiv.sumComm α β) (Equiv.sumComm α β) (rectangularShear G)=
  Matrix.fromBlocks (1 : Matrix β β ℂ) 0 G (1 : Matrix α α ℂ) := by
  ext i j; cases i <;> cases j <;> rfl
 rw [he] at hh
 exact hh

theorem cross_layer (s a : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0) :
 Layered (Matrix.fromBlocks (1 : Matrix (Fin s) (Fin s) ℂ) 0
  (lowerCross s a (PowerSeries.coeff · f) * (truncMatrix s f)⁻¹)
  (1 : Matrix (Fin a) (Fin a) ℂ)) (2097152*(Nat.log 2 (a+s)+1)) := by
 rw [ScalarConvolution.truncMatrix_inv s f hf,cross_mul]
 apply lower_shear
 have hh := Displacement.exact_width a s
  (fun i j=>cross s (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹) (s+i) j)
  (fun i=>-PowerSeries.coeff (s+i-s) f) (fun j=>PowerSeries.coeff (s-j) f⁻¹)
  (by
   intro i j hi hj
   have ht := cross_succ s (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹) (s+i) j (by omega) hj
   simpa only [Nat.add_assoc,sub_eq_add_neg,neg_mul] using ht)
 exact hh

theorem recursion (s a d e : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f≠0)
 (hs : Layered (truncMatrix s f) d) (ha : Layered (truncMatrix a f) e) :
 Layered (truncMatrix (s+a) f) (2097152*(Nat.log 2 (a+s)+1)+max d e) := by
 have hc := cross_layer s a f hf
 have hh := hc.mul (hs.parallel ha)
 have he : Matrix.fromBlocks (1 : Matrix (Fin s) (Fin s) ℂ) 0
  (lowerCross s a (PowerSeries.coeff · f) * (truncMatrix s f)⁻¹) (1 : Matrix (Fin a) (Fin a) ℂ) *
  Matrix.fromBlocks (truncMatrix s f) 0 0 (truncMatrix a f)=
  Matrix.fromBlocks (truncMatrix s f) 0 (lowerCross s a (PowerSeries.coeff · f)) (truncMatrix a f) := by
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc,Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hs.unit)]
 rw [he,← trunc_split] at hh
 have hh := hh.reindex finSumFinEquiv
 have hh2 := reindex_inverse (e := finSumFinEquiv.symm) (truncMatrix (s+a) f)
 simp only [Equiv.symm_symm] at hh2
 rw [hh2] at hh
 exact hh
end ExactFourier.ToeplitzLayers

end
end

section
noncomputable section
namespace ExactFourier.ToeplitzLayers
open Layered CoefficientTime

theorem trunc_small (n : ℕ) (hn : n ≤ 1) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
 Layered (truncMatrix n f) 1 := by
 have he : truncMatrix n f=Matrix.diagonal (fun _=>PowerSeries.constantCoeff f) := by
  ext i j
  have hi : i.val=0 := by have := i.isLt; omega
  have hj : j.val=0 := by have := j.isLt; omega
  have hij : i=j := Fin.ext (hi.trans hj.symm)
  subst j
  simp [truncMatrix,PowerSeries.coeff_zero_eq_constantCoeff]
 rw [he]
 exact mono _ (MonomialMatrix.diagonal _ (fun _=>hf))

theorem trunc_layers_pow (k n : ℕ) (hn : n ≤ 2^k) (f : PowerSeries ℂ)
 (hf : PowerSeries.constantCoeff f ≠ 0) :
 Layered (truncMatrix n f) (4194304*(k+1)^2) := by
 induction k generalizing n with
 | zero => exact (trunc_small n (by simpa using hn) f hf).weaken (by norm_num)
 | succ k ih =>
  let s := min n (2^k)
  let a := n-s
  have hsn : s ≤ n := Nat.min_le_left _ _
  have hsa : s+a=n := Nat.add_sub_of_le hsn
  have hs : s ≤ 2^k := Nat.min_le_right _ _
  have ha : a ≤ 2^k := by
   dsimp [a,s]
   rw [pow_succ] at hn
   omega
  have hh := recursion s a _ _ f hf (ih s hs) (ih a ha)
  rw [hsa,max_self] at hh
  have hlog : Nat.log 2 (a+s) ≤ k+1 := by
   have he : a+s=n := by omega
   rw [he]
   exact (Nat.log_mono_right hn).trans (by rw [Nat.log_pow (by decide)])
  exact hh.weaken (by nlinarith)

theorem trunc_layers (n : ℕ) (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
 Layered (truncMatrix n f) (4194304*(Nat.log 2 n+2)^2) := by
 have hh := trunc_layers_pow (Nat.log 2 n+1) n
  (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) n)) f hf
 exact hh
end ExactFourier.ToeplitzLayers

end
end

section
noncomputable section
namespace ExactFourier.Layered
variable {ι : Type} [Fintype ι] [LinearOrder ι]
/-- Symmetric Gaussian factorization, avoiding an appeal to LDU uniqueness. -/
theorem symmetric_triangular {F P N : Matrix ι ι ℂ} {d : ℕ}
 (hN : Layered N d) (hP : IsUnit P) (hU : P.IsUpperTriangular)
 (hL : N.IsLowerTriangular) (hFP : F*P=N) (hF : F.transpose=F) :
 Layered F (2*d+1) := by
 let D := P.transpose*N
 have hDu : IsUnit D := ((Matrix.isUnit_transpose _).mpr hP).mul hN.unit
 have hDt : D.IsLowerTriangular := hU.transpose.mul hL
 have hsym : D.transpose=D := by
  dsimp [D]
  rw [Matrix.transpose_mul,← hFP,Matrix.transpose_mul,hF,Matrix.transpose_transpose]
  exact Matrix.mul_assoc _ _ _
 have hdiag : D=Matrix.diagonal (fun i=>D i i) := by
  ext i j
  by_cases hij : i=j
  · subst j; simp
  rw [Matrix.diagonal_apply_ne _ hij]
  rcases lt_or_gt_of_ne hij with hl|hl
  · exact hDt hl
  · have hh := hDt hl
    have he := congr_fun (congr_fun hsym i) j
    exact he.symm.trans hh
 have hDn : ∀ i,D i i≠0 := by
  rw [hdiag] at hDu
  intro i
  exact isUnit_iff_ne_zero.mp (Pi.isUnit_iff.mp (Matrix.isUnit_diagonal.mp hDu) i)
 have hDm : MonomialMatrix D := hdiag ▸ MonomialMatrix.diagonal _ hDn
 have ht : N.transpose=P.transpose*F := by rw [← hFP,Matrix.transpose_mul,hF]
 have hid : N*D⁻¹*N.transpose=F := by
  rw [ht]
  dsimp [D]
  rw [Matrix.mul_inv_rev]
  rw [← Matrix.mul_assoc N N⁻¹,Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hN.unit)]
  simp only [Matrix.one_mul,← Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp ((Matrix.isUnit_transpose _).mpr hP)),Matrix.one_mul]
 have hh := (hN.mul (Layered.mono _ hDm).inverse).mul hN.transpose
 rw [hid] at hh
 simpa only [show d+1+d=2*d+1 by omega] using hh
end ExactFourier.Layered

end
end

section
noncomputable section
namespace ExactFourier.NewtonFourier
open Layered CoefficientTime

theorem N_toeplitz {n : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω n) :
 N n ω=Matrix.diagonal (fun i : Fin n=>H ω i.val) * truncMatrix n (invH ω) *
  Matrix.diagonal (fun i : Fin n=>scale ω i.val) := by
 ext i j
 rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
 change (newton ω j.val).eval (ω^i.val)=H ω i.val *
  (if j.val ≤ i.val then PowerSeries.coeff (i.val-j.val) (invH ω) else 0) * scale ω j.val
 by_cases hij : j.val ≤ i.val
 · rw [ite_eq_left hij]
   simp only [invH,PowerSeries.coeff_mk]
   have hh := eval_factor ω i.val j.val hij
   have hH := H_ne_zero hω (show i.val-j.val < n by have := i.isLt; omega)
   apply (mul_right_cancel₀ hH)
   calc
    (newton ω j.val).eval (ω^i.val)*H ω (i.val-j.val)=scale ω j.val*H ω i.val := hh
    _ = (H ω i.val*(H ω (i.val-j.val))⁻¹*scale ω j.val)*H ω (i.val-j.val) := by field_simp
 · rw [ite_eq_right hij,mul_zero,zero_mul]
   exact newton_eval_zero ω i.val j.val (by omega)

theorem P_unit (n : ℕ) (ω : ℂ) : IsUnit (P n ω) := by
 apply (Matrix.isUnit_iff_isUnit_det _).mpr
 have hh := Matrix.det_matrixOfPolynomials (fun i : Fin n=>newton ω i.val)
  (fun i=>newton_natDegree ω i.val) (fun i=>newton_monic ω i.val)
 change (P n ω).det=1 at hh
 rw [hh]
 exact isUnit_one

theorem N_layers {n : ℕ} (hn : 0 < n) {ω : ℂ} (hω : IsPrimitiveRoot ω n) :
 Layered (N n ω) (4194304*(Nat.log 2 n+2)^2+2) := by
 rw [N_toeplitz hω]
 have h1 := Layered.mono _ (MonomialMatrix.diagonal (fun i : Fin n=>H ω i.val) (fun i=>H_ne_zero hω i.isLt))
 have h2 := ToeplitzLayers.trunc_layers n (invH ω) (by simp)
 have h3 := Layered.mono _ (MonomialMatrix.diagonal (fun i : Fin n=>scale ω i.val)
  (fun i=>scale_ne_zero (hω.ne_zero (by omega)) i.val))
 have hh := (h1.mul h2).mul h3
 simpa only [show 1+4194304*(Nat.log 2 n+2)^2+1=4194304*(Nat.log 2 n+2)^2+2 by omega] using hh

/-- Exact-width Fourier layer theorem, with an absolute constant and a stronger
quadratic logarithmic bound. -/
theorem dft_layers {n : ℕ} (hn : 0 < n) {ω : ℂ} (hω : IsPrimitiveRoot ω n) :
 Layered (RadixTwo.dft n ω) (8388608*(Nat.log 2 n+2)^2+5) := by
 have hh := (N_layers hn hω).symmetric_triangular (P_unit n ω) (P_upper n ω) (N_lower n ω)
  (dft_mul_P n ω) (by ext i j; simp [RadixTwo.dft,Nat.mul_comm])
 simpa only [show 2*(4194304*(Nat.log 2 n+2)^2+2)+1=8388608*(Nat.log 2 n+2)^2+5 by omega] using hh
end ExactFourier.NewtonFourier

end
end

section
noncomputable section
namespace ExactFourier
namespace FourierCRT
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem char_nat {n : ℕ} (ψ : AddChar (ZMod n) ℂ) (k : ℕ) : ψ (k : ZMod n)=ψ 1^k := by
 simpa [nsmul_eq_mul] using ψ.map_nsmul_eq_pow k 1

theorem root_primitive {n : ℕ} (ψ : AddChar (ZMod n) ℂ) (hi : Function.Injective ψ) :
 IsPrimitiveRoot (ψ 1) n := by
 constructor
 · rw [← char_nat,ZMod.natCast_self,ψ.map_zero_eq_one]
 · intro k hk
   apply (ZMod.natCast_eq_zero_iff k n).mp
   apply hi
   rw [char_nat,ψ.map_zero_eq_one,hk]

theorem singleAdd_injective
    {ι : Type} [Fintype ι] [DecidableEq ι] (r : ι→ℕ) (i : ι) : Function.Injective (singleAdd r i) := by
 intro x y h
 have hh := congrFun h i
 simpa [singleAdd] using hh

theorem sum_singleAdd (r : ι→ℕ) (x : ∀ i,ZMod (r i)) : ∑ i,singleAdd r i (x i)=x := by
 ext j
 simp only [Finset.sum_apply,singleAdd,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
 rw [Finset.sum_eq_single j]
 · simp
 · intro i hi hij
   simp [Function.update_of_ne (Ne.symm hij)]
 · simp

theorem char_sum {R : Type} [AddCommMonoid R] (ψ : AddChar R ℂ) (x : ι→R) :
 ψ (∑ i,x i)=∏ i,ψ (x i) := by
 have hh : ∀ s : Finset ι,ψ (∑ i∈s,x i)=∏ i∈s,ψ (x i) := by
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ψ.map_add_eq_mul,ih]
 exact hh Finset.univ

theorem component_injective (r : ι→ℕ) (hn : Pairwise (fun i j=>Nat.Coprime (r i) (r j)))
 [NeZero (∏ i,r i)] (i : ι) : Function.Injective (component r hn i) :=
 ZMod.injective_stdAddChar.comp ((ZMod.prodEquivPi r hn).symm.injective.comp (singleAdd_injective r i))

theorem character_factor (r : ι→ℕ) (hn : Pairwise (fun i j=>Nat.Coprime (r i) (r j)))
 [NeZero (∏ i,r i)] (x : ∀ i,ZMod (r i)) :
 ZMod.stdAddChar ((ZMod.prodEquivPi r hn).symm x)=∏ i,component r hn i (x i) := by
 let ψ := ZMod.stdAddChar.compAddMonoidHom (ZMod.prodEquivPi r hn).symm.toAddMonoidHom
 change ψ x=∏ i,ψ (singleAdd r i (x i))
 rw [← char_sum,sum_singleAdd]

theorem standard_root (n : ℕ) [NeZero n] : ZMod.stdAddChar (1 : ZMod n)=zeta n := by
 have hh := ZMod.stdAddChar_coe (N := n) (1 : ℤ)
 simpa [zeta] using hh

theorem factorization (r : ι→ℕ) (hr : ∀ i,0<r i)
 (hn : Pairwise (fun i j=>Nat.Coprime (r i) (r j))) :
 ∃ ω : ι→ℂ,(∀ i,IsPrimitiveRoot (ω i) (r i)) ∧
 ∃ e : Fin (∏ i,r i) ≃ (∀ i,Fin (r i)),
 Matrix.reindex e e (fourierMatrix (∏ i,r i))=
 PiTensor.matrix (fun i=>RadixTwo.dft (r i) (ω i)) := by
 let : ∀ i,NeZero (r i) := fun i=>⟨ne_of_gt (hr i)⟩
 let : NeZero (∏ i,r i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _=>ne_of_gt (hr i))⟩
 let c := ZMod.prodEquivPi r hn
 let e := (finZMod (∏ i,r i)).trans (c.toEquiv.trans (Equiv.piCongrRight (fun i=>(finZMod (r i)).symm)))
 refine ⟨fun i=>component r hn i 1,fun i=>root_primitive _ (component_injective r hn i),e,?_⟩
 ext x y
 obtain ⟨j,rfl⟩ := e.surjective x
 obtain ⟨k,rfl⟩ := e.surjective y
 simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
 have hj : c (j.val : ZMod (∏ i,r i))=fun i=>((e j i).val : ZMod (r i)) := by
  funext i
  change c _ i=(((finZMod (r i)).symm (c (j.val : ZMod (∏ i,r i)) i)).val : ZMod (r i))
  exact (finZMod (r i)).apply_symm_apply _ |>.symm
 have hk : c (k.val : ZMod (∏ i,r i))=fun i=>((e k i).val : ZMod (r i)) := by
  funext i
  change c _ i=(((finZMod (r i)).symm (c (k.val : ZMod (∏ i,r i)) i)).val : ZMod (r i))
  exact (finZMod (r i)).apply_symm_apply _ |>.symm
 have hprod : c (((j.val*k.val : ℕ) : ZMod (∏ i,r i)))=
     fun i=>(((e j i).val*(e k i).val : ℕ) : ZMod (r i)) := by
  rw [Nat.cast_mul,map_mul,hj,hk]
  ext i; simp
 have hh := character_factor r hn (fun i=>(((e j i).val*(e k i).val : ℕ) : ZMod (r i)))
 rw [← hprod,c.symm_apply_apply,char_nat,standard_root] at hh
 simpa only [PiTensor.matrix,RadixTwo.dft,fourierMatrix,char_nat] using hh
end FourierCRT
end ExactFourier

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.PrimeInventory
open Nat Real

theorem count_fourth (M : ℕ) (hM : 10≤M) : M≤Nat.primeCounting (M^4) := by
 have hm : (10:ℝ)≤M := by exact_mod_cast hM
 have hm0 : (0:ℝ)<M := by linarith
 have hs : (100:ℝ)≤(M : ℝ)^2 := by nlinarith
 have hn : (1:ℝ)<(M : ℝ)^4 := by nlinarith [sq_nonneg ((M : ℝ)^2-1)]
 have hlpos : 0<Real.log ((M : ℝ)^4) := Real.log_pos hn
 have hl : Real.log ((M : ℝ)^4)=4*Real.log M := by rw [Real.log_pow]; norm_num
 have hlog : Real.log (M : ℝ)≤M := (Real.log_le_sub_one_of_pos hm0).trans (by linarith)
 have hlog2 : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
 have hlog21 : Real.log 2≤1 := by linarith [Real.log_two_lt_d9]
 have hb : Real.log ((M : ℝ)^4+1)≤1+4*M := by
  have h1 := Real.log_le_log (by positivity : (0:ℝ)<(M : ℝ)^4+1)
    (show (M : ℝ)^4+1≤2*(M : ℝ)^4 by linarith)
  rw [Real.log_mul (by norm_num) (by positivity),hl] at h1
  linarith
 have hs4 : 100*(M : ℝ)^2≤(M : ℝ)^4 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (M : ℝ))]
 have hn1 : (M : ℝ)*Real.log ((M : ℝ)^4)≤(M : ℝ)^4*Real.log 2-Real.log ((M : ℝ)^4+1) := by
  rw [hl]
  have h1 := mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤4*M by positivity)
  have h2 := mul_le_mul_of_nonneg_left hlog2 (show (0:ℝ)≤(M : ℝ)^4 by positivity)
  nlinarith only [h1,h2,hb,hs4,hs,hm]
 have hh := Chebyshev.pi_ge (M^4)
 have hlower : (M : ℝ)≤((M : ℝ)^4*Real.log 2-Real.log ((M : ℝ)^4+1))/Real.log ((M : ℝ)^4) :=
  (le_div_iff₀ hlpos).mpr hn1
 have hh' : (M : ℝ)≤Nat.primeCounting (M^4) := by
  apply hlower.trans
  simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hh
 exact_mod_cast hh'

theorem family (q m : ℕ) : ∃ r : Fin m→ℕ,
 (∀ i,Nat.Prime (r i)) ∧ Function.Injective r ∧
 (∀ i,2*q≤r i) ∧ (∀ i,r i≤upper q m) := by
 let V := Nat.primesLE (upper q m)
 let S := V.filter (fun p=>2*q≤p)
 let T := V.filter (fun p=>¬2*q≤p)
 have hcard := Finset.card_filter_add_card_filter_not (s := V) (fun p=>2*q≤p)
 have ht : T.card≤2*q := by
  have hsub : T⊆Finset.range (2*q) := by
   intro p hp
   exact Finset.mem_range.mpr (lt_of_not_ge (Finset.mem_filter.mp hp).2)
  simpa only [Finset.card_range] using Finset.card_le_card hsub
 have hv : m+2*q≤V.card := by
  rw [show V=Nat.primesLE (upper q m) from rfl,Nat.primesLE_card_eq_primeCounting]
  have hh : m + 2*q ≤ m + 2*q + 10 := by omega
  exact hh.trans (count_fourth _ (by omega))
 have hs : m≤S.card := by change S.card+T.card=V.card at hcard; omega
 obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin m) (β := S) (by simpa using hs)
 refine ⟨fun i=>(e i).val,fun i=>?_,fun i j h=>e.injective (Subtype.ext h),fun i=>?_,fun i=>?_⟩
 · exact Nat.prime_of_mem_primesLE (Finset.mem_filter.mp (e i).property).1
 · exact (Finset.mem_filter.mp (e i).property).2
 · exact Nat.le_of_mem_primesLE (Finset.mem_filter.mp (e i).property).1

theorem family_coprime {m : ℕ} {r : Fin m→ℕ} (hr : ∀ i,Nat.Prime (r i))
 (hi : Function.Injective r) : Pairwise (fun i j=>Nat.Coprime (r i) (r j)) := by
 intro i j hij
 exact (Nat.coprime_primes (hr i) (hr j)).mpr (fun h=>hij (hi h))
end ExactFourier.PrimeInventory

end
end

section
noncomputable section
namespace ExactFourier.FourierTransfer
open CircuitCost

theorem depth_bound (q m : ℕ) :
 (depth q m : ℝ)≤536870917*(Real.log ((m:ℝ)+2*q+10)+1)^2 := by
 let x : ℝ := (m:ℝ)+2*q+10
 have hx : 1≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) q]
 have hl : 0≤Real.log x := Real.log_nonneg hx
 have hu : (PrimeInventory.upper q m : ℝ)=x^4 := by simp [PrimeInventory.upper,x]
 have hlog := Real.natLog_le_logb (PrimeInventory.upper q m) 2
 rw [hu,Real.logb,Real.log_pow] at hlog
 norm_num only [Nat.cast_ofNat] at hlog
 have h2 : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
 have h2p : 0<Real.log 2 := Real.log_pos (by norm_num)
 have hh : (Nat.log 2 (PrimeInventory.upper q m) : ℝ)≤8*Real.log x := by
  apply hlog.trans
  apply (div_le_iff₀ h2p).mpr
  nlinarith [mul_nonneg hl (sub_nonneg.mpr h2)]
 have hb : (Nat.log 2 (PrimeInventory.upper q m) : ℝ)+2≤8*(Real.log x+1) := by linarith
 have hb0 : 0≤(Nat.log 2 (PrimeInventory.upper q m) : ℝ)+2 := by positivity
 have hsq := sq_le_sq₀ hb0 (by positivity : 0≤8*(Real.log x+1)) |>.mpr hb
 change (depth q m : ℝ)≤536870917*(Real.log x+1)^2
 simp only [depth,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
 nlinarith [sq_nonneg (Real.log x)]

theorem family_cost {q h : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (hq : 2≤q)
 (gen : ∀ M : Matrix (Fin q) (Fin q) ℂ,IsUnit M → PositiveGeneration.Pattern A h M)
 {a C : ℝ} (ha : 0≤a) (hC : 0≤C)
 (amp : ∀ k,(cost (TensorAxis.power A k) : ℝ)≤C*(q : ℝ)^k*(k+1 : ℝ)^a)
 (m : ℕ) : ∃ n : ℕ,2^m≤n ∧
 (cost (fourierMatrix n) : ℝ)≤536870917*(q*(h+1)+1 : ℕ)*(C+1)*n*
   (Real.log ((m:ℝ)+2*q+10)+1)^2*((m:ℝ)+2*q+10)^a := by
 obtain ⟨r,hr,hi,hlo,hup⟩ := PrimeInventory.family q m
 obtain ⟨ω,hω,e,he⟩ := FourierCRT.factorization r (fun i=>(hr i).pos)
   (PrimeInventory.family_coprime hr hi)
 let n := ∏ i,r i
 have hn : 2^m≤n := by
  have hp := Finset.prod_le_prod' (fun i (_ : i∈(Finset.univ : Finset (Fin m)))=>(hr i).two_le)
  simpa [n] using hp
 have hlayer : ∀ i,Layered (RadixTwo.dft (r i) (ω i)) (depth q m) := by
  intro i
  apply (NewtonFourier.dft_layers (hr i).pos (hω i)).weaken
  dsimp [depth]
  have hh := Nat.log_mono_right (b := 2) (hup i)
  gcongr
 have hc := ParallelTensorCost.layered_cost ha hC amp hq gen m (depth q m)
   (fun i=>Fin (r i)) (fun i=>RadixTwo.dft (r i) (ω i)) hlayer
   (fun i=>by simpa using hlo i)
 rw [← he,CircuitCost.cost_reindex] at hc
 simp only [Fintype.card_pi,Fintype.card_fin] at hc
 let x : ℝ := (m:ℝ)+2*q+10
 have hx : 1≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) q]
 have hxm : (m:ℝ)+1≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) q]
 have hp := Real.rpow_le_rpow (by positivity : (0:ℝ)≤(m:ℝ)+1) hxm ha
 have hp1 : 1≤x^a := Real.one_le_rpow hx ha
 have hbudget : C*((m:ℝ)+1)^a+1≤(C+1)*x^a := by nlinarith
 have hd := depth_bound q m
 have hb0 : 0≤C*((m:ℝ)+1)^a+1 := by positivity
 refine ⟨n,hn,hc.trans ?_⟩
 change ((depth q m*(q*(h+1)+1) : ℕ):ℝ)*(C*(n:ℝ)*((m:ℝ)+1)^a+(n:ℝ))≤_
 calc
  _ = (depth q m : ℝ)*(q*(h+1)+1 : ℕ)*n*(C*((m:ℝ)+1)^a+1) := by push_cast; ring
  _ ≤ (536870917*(Real.log x+1)^2)*(q*(h+1)+1 : ℕ)*n*((C+1)*x^a) := by
   exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)) (Nat.cast_nonneg n)) hbudget hb0 (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Nat.cast_nonneg _)) (Nat.cast_nonneg n))
  _ = _ := by dsimp [x]; ring
end ExactFourier.FourierTransfer

end
end

section
noncomputable section
namespace ExactFourier.FourierTransfer
open Filter Topology Asymptotics

theorem log_square_littleO {a : ℝ} (ha : a<1) :
 (fun x : ℝ=>(Real.log x+1)^2)=o[atTop] (fun x : ℝ=>x^(1-a)) := by
 have hs : 0<1-a := by linarith
 have h2 := isLittleO_log_rpow_rpow_atTop (2 : ℝ) hs
 have h2' : (fun x : ℝ=>(Real.log x)^2)=o[atTop] (fun x : ℝ=>x^(1-a)) := by
  simpa only [Real.rpow_two] using h2
 have h1 := (isLittleO_log_rpow_atTop hs).const_mul_left (2 : ℝ)
 have h0 : (fun _ : ℝ=>(1:ℝ))=o[atTop] (fun x : ℝ=>x^(1-a)) := by
  apply (isLittleO_const_left_of_ne one_ne_zero).mpr
  simpa only [Real.norm_eq_abs,Function.comp_def] using tendsto_abs_atTop_atTop.comp (tendsto_rpow_atTop hs)
 exact ((h2'.add h1).add h0).congr_left (fun x=>by ring)

theorem log_power_ratio {a : ℝ} (ha : a<1) :
 Tendsto (fun x : ℝ=>(Real.log x+1)^2*x^a/x) atTop (𝓝 0) := by
 have ht := (log_square_littleO ha).tendsto_div_nhds_zero
 apply ht.congr'
 filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
 rw [Real.rpow_sub hx,Real.rpow_one]
 field_simp

theorem shifted_log_power_ratio {a c : ℝ} (ha : a<1) :
 Tendsto (fun m : ℕ=>(Real.log ((m:ℝ)+c)+1)^2*((m:ℝ)+c)^a/(m:ℝ)) atTop (𝓝 0) := by
 have ht : Tendsto (fun m : ℕ=>(m:ℝ)+c) atTop atTop :=
  (tendsto_atTop_add_const_right atTop c tendsto_id).comp tendsto_natCast_atTop_atTop
 have h1 := (log_power_ratio ha).comp ht
 have h2 : Tendsto (fun m : ℕ=>((m:ℝ)+c)/(m:ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1:ℝ))).add ((tendsto_const_nhds (x := c)).mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  apply (show Tendsto (fun m : ℕ=>1+c*(m:ℝ)⁻¹) atTop (𝓝 1) by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hm' : (m:ℝ)≠0 := by exact_mod_cast (ne_of_gt hm)
  field_simp
 have h := h1.mul h2
 apply (show Tendsto (fun m : ℕ=>((Real.log ((m:ℝ)+c)+1)^2*((m:ℝ)+c)^a/((m:ℝ)+c))*(((m:ℝ)+c)/(m:ℝ))) atTop (𝓝 0) by simpa using h).congr'
 filter_upwards [ht.eventually (eventually_gt_atTop (0:ℝ))] with m hm
 field_simp
end ExactFourier.FourierTransfer

end
end

section
noncomputable section
namespace ExactFourier.CircuitCost

theorem exists_circuit {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
 ∃ C : Circuit n,C.size=cost M ∧ C.Computes M := by
 obtain ⟨T,hT,ht⟩ := optimal M
 let e := Fintype.equivFin (Fin n)
 let D : LinearDAG n n := (T.circuit.withInputs e.symm).withOutputs e
 let C : Circuit n := ⟨D.size,D.program,D.outputs⟩
 refine ⟨C,?_,?_⟩
 · change D.size=cost M
   change (T.circuit.withInputs e.symm).size=cost M
   rw [LinearDAG.size_withInputs]
   exact hT
 · intro x
   change D.eval x=M.mulVec x
   rw [LinearDAG.eval_withOutputs,LinearDAG.eval_withInputs]
   exact ht x
end ExactFourier.CircuitCost

end
end

section
noncomputable section
namespace ExactFourier
open Filter Topology
open CircuitCost

/-- An actual finite win transfers to arbitrarily large exact Fourier DAGs,
with every scalar multiplication charged. -/
theorem win_to_fourier_oai (win : FiniteWinStatement) : MainStatement := by
 obtain ⟨q,A,hA,hn,b,hb,W,hW,hw⟩ := win
 have hn' : ¬MonomialMatrix A := hn
 obtain ⟨h,hh,gen⟩ := PositiveGeneration.positive_generation A hA hn'
 obtain ⟨a,C,ha,ha1,hC,amp⟩ := Amplification.tensor_amplification A hb W hW hw
 have hq : 2≤q := by
  obtain ⟨k,i,j,hij,_⟩ := PositiveGeneration.exists_nondiagonal_projector A hA hn'
  have hne : i.val≠j.val := fun e=>hij (Fin.ext e)
  have hi := i.isLt
  have hj := j.isLt
  omega
 intro c hc N₀ hN₀
 let K : ℝ := 536870917*(q*(h+1)+1 : ℕ)*(C+1)
 have hK : 0<K := by dsimp [K]; positivity
 have ht := (FourierTransfer.shifted_log_power_ratio (c := (2:ℝ)*q+10) ha1).const_mul K
 have hlim : Tendsto (fun m : ℕ=>K*(Real.log ((m:ℝ)+2*q+10)+1)^2*((m:ℝ)+2*q+10)^a/(m:ℝ)) atTop (𝓝 0) := by
  convert ht using 1 <;> try simp only [mul_zero]
  funext m
  simp only [add_assoc]
  ring
 have hsmall : ∀ᶠ m : ℕ in atTop,K*(Real.log ((m:ℝ)+2*q+10)+1)^2*((m:ℝ)+2*q+10)^a/(m:ℝ)<c :=
  hlim.eventually (eventually_lt_nhds hc)
 obtain ⟨m,hm,hmsmall⟩ := ((eventually_ge_atTop N₀).and hsmall).exists
 have hmpos : 0 < m := by omega
 have hmR : (0:ℝ)< m := by exact_mod_cast hmpos
 obtain ⟨n,hnpow,hncost⟩ := FourierTransfer.family_cost A hq gen ha.le hC.le amp m
 have hmn : m≤n := (Nat.le_of_lt (Nat.lt_two_pow_self (n := m))).trans hnpow
 have hnpos : 0 < n := hmpos.trans_le hmn
 have hnR : (0:ℝ)< n := by exact_mod_cast hnpos
 have hlog : (m:ℝ)≤Real.logb 2 (n:ℝ) := by
  have hp : (2:ℝ)^m≤(n:ℝ) := by exact_mod_cast hnpow
  have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by positivity : (0:ℝ)<(2:ℝ)^m) hp
  simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] using hl
 have hstrict : K*(Real.log ((m:ℝ)+2*q+10)+1)^2*((m:ℝ)+2*q+10)^a<c*(m:ℝ) :=
  (div_lt_iff₀ hmR).mp hmsmall
 have hcost : (cost (fourierMatrix n) : ℝ)<c*(n:ℝ)*Real.logb 2 (n:ℝ) := by
  calc
   _ ≤ (n:ℝ)*(K*(Real.log ((m:ℝ)+2*q+10)+1)^2*((m:ℝ)+2*q+10)^a) := by
    convert hncost using 1 ; dsimp [K] ; ring
   _ < (n:ℝ)*(c*(m:ℝ)) := mul_lt_mul_of_pos_left hstrict hnR
   _ ≤ c*(n:ℝ)*Real.logb 2 (n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlog (mul_nonneg hc.le hnR.le)
    nlinarith only [hh]
 obtain ⟨D,hD,hd⟩ := CircuitCost.exists_circuit (fourierMatrix n)
 exact ⟨n,hm.trans hmn,D,hd,by simpa only [hD] using hcost⟩
end ExactFourier

end
end

end OAI
end

theorem solution : type_of% @OAI.ExactFourier.win_to_fourier_oai := @OAI.ExactFourier.win_to_fourier_oai
