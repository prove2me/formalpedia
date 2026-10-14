-- Prove2me | solution 1 for OAI.ExactQuantumFactoring.outputState_normSq_sum
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T05:52:20.849605+00:00
-- url     : https://prove2.me/submissions/9cf67159-a306-44f8-b49d-4c6ef4e6705b

import Mathlib
import Definitions.Def_ExactQuantumFactoring

set_option autoImplicit false

open scoped BigOperators
open OAI.ExactQuantumFactoring
open scoped Matrix

namespace OAI.ExactQuantumFactoring.QF_Ua

/-- Finite matrix of a list-indexed function on `n` bits. -/
noncomputable def GM (M : List Bool → List Bool → ℂ) (n : ℕ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun u v => M (List.ofFn u) (List.ofFn v)

def IsU (M : List Bool → List Bool → ℂ) (n : ℕ) : Prop :=
  (GM M n)ᴴ * GM M n = 1

lemma isU_iff (M : List Bool → List Bool → ℂ) (n : ℕ) :
    IsU M n ↔ ∀ v v' : Fin n → Bool,
      ∑ u : Fin n → Bool, star (M (List.ofFn u) (List.ofFn v)) * M (List.ofFn u) (List.ofFn v')
        = if v = v' then 1 else 0 := by
  unfold IsU
  rw [← Matrix.ext_iff]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, GM]

lemma sum_cons (n : ℕ) (f : (Fin (n+1) → Bool) → ℂ) :
    ∑ u, f u = ∑ c : Bool, ∑ u : Fin n → Bool, f (Fin.cons c u) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma sum_zero (f : (Fin 0 → Bool) → ℂ) : ∑ u, f u = f Fin.elim0 := by
  rw [Fintype.sum_subsingleton _ Fin.elim0]

lemma ofFn_cons' {n : ℕ} (c : Bool) (u : Fin n → Bool) :
    List.ofFn (Fin.cons c u : Fin (n+1) → Bool) = c :: List.ofFn u := by
  rw [List.ofFn_succ]; simp

lemma sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma sqrt2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  intro h; have := sqrt2_sq; rw [h] at this; norm_num at this

lemma sum1 (f : (Fin 1 → Bool) → ℂ) : ∑ u, f u = ∑ a : Bool, f ![a] := by
  rw [sum_cons]; simp only [sum_zero]; rfl

lemma sum2 (f : (Fin 2 → Bool) → ℂ) : ∑ u, f u = ∑ a : Bool, ∑ b : Bool, f ![a, b] := by
  rw [sum_cons]; simp only [sum_cons, sum_zero]; rfl

lemma sum3 (f : (Fin 3 → Bool) → ℂ) :
    ∑ u, f u = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, f ![a, b, c] := by
  rw [sum_cons]; simp only [sum_cons, sum_zero]; rfl

lemma eta1 (v : Fin 1 → Bool) : v = ![v 0] := by
  ext i; fin_cases i; rfl
lemma eta2 (v : Fin 2 → Bool) : v = ![v 0, v 1] := by
  ext i; fin_cases i <;> rfl
lemma eta3 (v : Fin 3 → Bool) : v = ![v 0, v 1, v 2] := by
  ext i; fin_cases i <;> rfl

theorem not_isU : IsU Primitive.not.matrix 1 := by
  rw [isU_iff]
  intro v v'
  rw [eta1 v, eta1 v']
  generalize v 0 = x; generalize v' 0 = x'
  simp only [sum1, Matrix.vecCons_inj, List.ofFn_succ, List.ofFn_zero, Fintype.sum_bool,
    Primitive.matrix]
  cases x <;> cases x' <;> simp

theorem cnot_isU : IsU Primitive.cnot.matrix 2 := by
  rw [isU_iff]
  intro v v'
  rw [eta2 v, eta2 v']
  generalize v 0 = x; generalize v' 0 = x'; generalize v 1 = y; generalize v' 1 = y'
  simp only [sum2, Matrix.vecCons_inj, List.ofFn_succ, List.ofFn_zero, Fintype.sum_bool,
    Primitive.matrix]
  cases x <;> cases x' <;> cases y <;> cases y' <;> simp

theorem toffoli_isU : IsU Primitive.toffoli.matrix 3 := by
  rw [isU_iff]
  intro v v'
  rw [eta3 v, eta3 v']
  generalize v 0 = x; generalize v' 0 = x'; generalize v 1 = y; generalize v' 1 = y'
  generalize v 2 = z; generalize v' 2 = z'
  simp only [sum3, Matrix.vecCons_inj, List.ofFn_succ, List.ofFn_zero, Fintype.sum_bool,
    Primitive.matrix]
  cases x <;> cases x' <;> cases y <;> cases y' <;> cases z <;> cases z' <;> simp

theorem hadamard_isU : IsU Primitive.hadamard.matrix 1 := by
  rw [isU_iff]
  intro v v'
  rw [eta1 v, eta1 v']
  generalize v 0 = x; generalize v' 0 = x'
  simp only [sum1, Matrix.vecCons_inj, List.ofFn_succ, List.ofFn_zero, Fintype.sum_bool,
    Primitive.matrix]
  have h1 := sqrt2_sq
  have h2 := sqrt2_ne
  cases x <;> cases x' <;> simp [Complex.conj_ofReal] <;> field_simp
  all_goals first | linear_combination -h1 | linear_combination (0:ℂ) * h1

theorem phase_isU : IsU Primitive.phase.matrix 1 := by
  rw [isU_iff]
  intro v v'
  rw [eta1 v, eta1 v']
  generalize v 0 = x; generalize v' 0 = x'
  simp only [sum1, Matrix.vecCons_inj, List.ofFn_succ, List.ofFn_zero, Fintype.sum_bool,
    Primitive.matrix]
  cases x <;> cases x' <;> simp

theorem prim_isU (p : Primitive) : IsU p.matrix p.arity := by
  cases p
  · exact not_isU
  · exact cnot_isU
  · exact toffoli_isU
  · exact hadamard_isU
  · exact phase_isU

lemma GM_conjT (M : List Bool → List Bool → ℂ) (n : ℕ) :
    GM (fun a b => star (M b a)) n = (GM M n)ᴴ := by
  ext u v; simp [GM, Matrix.conjTranspose_apply]

lemma isU_conjT (M : List Bool → List Bool → ℂ) (n : ℕ) (h : IsU M n) :
    IsU (fun a b => star (M b a)) n := by
  unfold IsU at *
  rw [GM_conjT, Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.mp h

lemma base_isU (g : Gate) : IsU g.baseMatrix g.primitive.arity := by
  obtain ⟨p, inv, ctrl⟩ := g
  cases inv
  · have : Gate.baseMatrix ⟨p, false, ctrl⟩ = p.matrix := by
      funext a b; simp [Gate.baseMatrix]
    rw [this]; exact prim_isU p
  · have : Gate.baseMatrix ⟨p, true, ctrl⟩ = fun a b => star (p.matrix b a) := by
      funext a b; simp [Gate.baseMatrix]
    rw [this]; exact isU_conjT _ _ (prim_isU p)

lemma ctrl_isU (g : Gate) (hg : g.controlled = true) (n : ℕ) (h : IsU g.baseMatrix n) :
    IsU g.matrix (n + 1) := by
  rw [isU_iff] at *
  intro v v'
  induction v using Fin.consCases with | cons x t => ?_
  induction v' using Fin.consCases with | cons x' t' => ?_
  rw [sum_cons]
  simp only [List.ofFn_cons, Gate.matrix, hg, if_true, Fintype.sum_bool, Fin.cons_inj]
  cases x <;> cases x' <;> simp [List.ofFn_inj]
  · exact if_congr eq_comm rfl rfl
  · exact h t t'

lemma gate_isU (g : Gate) : IsU g.matrix g.arity := by
  obtain ⟨p, inv, ctrl⟩ := g
  cases ctrl
  · have h1 : Gate.matrix ⟨p, inv, false⟩ = Gate.baseMatrix ⟨p, inv, false⟩ := by
      funext a b; simp [Gate.matrix]
    have h2 : Gate.arity ⟨p, inv, false⟩ = p.arity := by simp [Gate.arity]
    rw [h1, h2]; exact base_isU _
  · have h2 : Gate.arity ⟨p, inv, true⟩ = p.arity + 1 := by simp [Gate.arity]
    rw [h2]; exact ctrl_isU _ rfl _ (base_isU _)

/-- `a` and `b` agree off the wires of `o`. -/
def Agree {q : ℕ} (o : Instruction q) (a b : Basis q) : Prop :=
  ∀ i : Fin q, (∀ j, o.wire j ≠ i) → a i = b i

lemma agree_symm {q : ℕ} (o : Instruction q) {a b : Basis q} (h : Agree o a b) : Agree o b a :=
  fun i hi => (h i hi).symm

lemma agree_trans {q : ℕ} (o : Instruction q) {a b c : Basis q} (h1 : Agree o a b)
    (h2 : Agree o b c) : Agree o a c :=
  fun i hi => (h1 i hi).trans (h2 i hi)

lemma matrix_of_agree {q : ℕ} (o : Instruction q) {a b : Basis q} (h : Agree o a b) :
    o.matrix a b = o.gate.matrix (List.ofFn (a ∘ o.wire)) (List.ofFn (b ∘ o.wire)) := by
  unfold Instruction.matrix
  exact if_pos h

lemma matrix_of_not_agree {q : ℕ} (o : Instruction q) {a b : Basis q} (h : ¬ Agree o a b) :
    o.matrix a b = 0 := by
  unfold Instruction.matrix
  exact if_neg h

/-- Reconstruct a basis state from its values on the wires and `b` elsewhere. -/
noncomputable def ext {q : ℕ} (o : Instruction q) (b : Basis q) (u : Fin o.gate.arity → Bool) :
    Basis q :=
  Function.extend o.wire u b

lemma ext_comp {q : ℕ} (o : Instruction q) (b : Basis q) (u : Fin o.gate.arity → Bool) :
    ext o b u ∘ o.wire = u := by
  funext j
  simp only [Function.comp, ext, o.distinct.extend_apply]

lemma agree_ext {q : ℕ} (o : Instruction q) (b : Basis q) (u : Fin o.gate.arity → Bool) :
    Agree o (ext o b u) b := by
  intro i hi
  unfold ext
  apply Function.extend_apply'
  rintro ⟨j, hj⟩
  exact hi j hj

lemma ext_of_agree {q : ℕ} (o : Instruction q) {a b : Basis q} (h : Agree o a b) :
    ext o b (a ∘ o.wire) = a := by
  funext i
  unfold ext
  by_cases hi : ∃ j, o.wire j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [o.distinct.extend_apply]
    rfl
  · rw [Function.extend_apply' _ _ _ hi]
    exact (h i (fun j hj => hi ⟨j, hj⟩)).symm

lemma ext_injective {q : ℕ} (o : Instruction q) (b : Basis q) :
    Function.Injective (ext o b) := by
  intro u u' h
  rw [← ext_comp o b u, ← ext_comp o b u', h]

theorem instr_col {q : ℕ} (o : Instruction q) (b b' : Basis q) :
    ∑ a, star (o.matrix a b) * o.matrix a b' = if b = b' then 1 else 0 := by
  by_cases hbb : Agree o b b'
  · have key : ∑ a, star (o.matrix a b) * o.matrix a b' =
        ∑ u : Fin o.gate.arity → Bool, star (o.gate.matrix (List.ofFn u) (List.ofFn (b ∘ o.wire)))
          * o.gate.matrix (List.ofFn u) (List.ofFn (b' ∘ o.wire)) := by
      symm
      apply Finset.sum_of_injOn (ext o b)
      · intro u _ u' _ h; exact ext_injective o b h
      · intro u _; exact Finset.mem_univ _
      · intro a _ ha
        have hna : ¬ Agree o a b := by
          intro hab
          apply ha
          exact ⟨a ∘ o.wire, by simp, ext_of_agree o hab⟩
        rw [matrix_of_not_agree o hna, star_zero, zero_mul]
      · intro u _
        rw [matrix_of_agree o (agree_ext o b u),
          matrix_of_agree o (agree_trans o (agree_ext o b u) hbb), ext_comp]
    rw [key, (isU_iff _ _).mp (gate_isU o.gate)]
    apply if_congr _ rfl rfl
    constructor
    · intro h
      funext i
      by_cases hi : ∃ j, o.wire j = i
      · obtain ⟨j, rfl⟩ := hi
        exact congrFun h j
      · exact hbb i (fun j hj => hi ⟨j, hj⟩)
    · intro h; rw [h]
  · have hne : b ≠ b' := by
      rintro rfl; exact hbb (fun i _ => rfl)
    rw [if_neg hne]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hab : Agree o a b
    · have hab' : ¬ Agree o a b' := fun h => hbb (agree_trans o (agree_symm o hab) h)
      rw [matrix_of_not_agree o hab', mul_zero]
    · rw [matrix_of_not_agree o hab, star_zero, zero_mul]

theorem instr_unitary {q : ℕ} (o : Instruction q) : o.matrixᴴ * o.matrix = 1 := by
  ext b b'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  exact instr_col o b b'

lemma normSq_sum_eq {n : Type*} [Fintype n] (v : n → ℂ) :
    ((∑ x, Complex.normSq (v x) : ℝ) : ℂ) = star v ⬝ᵥ v := by
  push_cast
  simp only [dotProduct, Pi.star_apply, Complex.normSq_eq_conj_mul_self, Complex.star_def]

lemma mulVec_normSq {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (hU : Uᴴ * U = 1) (v : n → ℂ) :
    ∑ x, Complex.normSq ((U *ᵥ v) x) = ∑ x, Complex.normSq (v x) := by
  apply Complex.ofReal_injective
  rw [normSq_sum_eq, normSq_sum_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

lemma foldl_normSq {q : ℕ} (l : List (Instruction q)) (ψ : State q) :
    ∑ x, Complex.normSq ((l.foldl (fun v o => o.matrix.mulVec v) ψ) x) =
      ∑ x, Complex.normSq (ψ x) := by
  induction l generalizing ψ with
  | nil => rfl
  | cons o l ih => rw [List.foldl_cons, ih, mulVec_normSq _ (instr_unitary o)]

end OAI.ExactQuantumFactoring.QF_Ua

theorem solution (c : Circuit) (ℓ N : ℕ) :
    ∑ x : Basis c.qubits, Complex.normSq (c.outputState ℓ N x) = 1 := by
  classical
  unfold Circuit.outputState Circuit.apply
  rw [OAI.ExactQuantumFactoring.QF_Ua.foldl_normSq]
  simp [apply_ite]
