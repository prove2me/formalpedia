-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.QuantumSampling.finite_filter_value_unnormalized
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:59:09.870467+00:00
-- url     : https://prove2.me/submissions/f18be76d-f8dd-413c-aa68-f61c2b3b5a81

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/SamplingStrategy.lean:L410-L437
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.QuantumSampling.finite_filter_value_unnormalized. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_filter_mass_bounds
import Theorems.Thm_OAI_ThresholdParallelRepetition_successProbability_le_one

-- ---- from OAI.Probability.EntangledGames.Basic ----
namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder

namespace ThresholdParallelRepetition

open scoped Kronecker
open Matrix

namespace Strategy
variable {X Y A B : Type} [Fintype A] [Fintype B]

lemma born_eq_quadratic (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    S.born x y a b =
      (star S.state ⬝ᵥ ((S.alice x a ⊗ₖ S.bob y b) *ᵥ S.state)).re := by
  simp only [born, dotProduct, Matrix.mulVec, Matrix.kroneckerMap_apply, Pi.star_apply,
    Finset.mul_sum, ← mul_assoc, Complex.re_sum]

end Strategy

namespace Strategy

end Strategy

lemma successProbability_le_value {x y a b : ℕ} (G : Game x y a b)
    (S : SingleStrategy x y a b) : successProbability G S ≤ entangledValue G := by
  exact le_csSup ⟨1, by rintro _ ⟨T, rfl⟩; exact successProbability_le_one G T⟩
    (Set.mem_range_self S)

end ThresholdParallelRepetition

end

end OAI

-- ---- from OAI.Probability.EntangledGames.HilbertSchmidt ----
namespace OAI

universe u_m u_n u_p u_q

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} [Fintype m] [Fintype n] [Fintype p]

lemma hsSq_nonneg (M : Matrix m n ℂ) : 0 ≤ hsSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

end ThresholdParallelRepetition.QuantumSampling

end

end OAI

-- ---- from OAI.Probability.EntangledGames.CoherentFilters ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_m u_n u_p u_ι u_q

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open ThresholdParallelRepetition.MeasurementTransport
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} [Fintype m] [Fintype n] [Fintype p]

lemma hsSq_smul (r : ℝ) (M : Matrix m n ℂ) : hsSq (r • M) = r^2*hsSq M := by
  simp only [hsSq, Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul,
    Complex.normSq_ofReal, ← Finset.mul_sum]
  congr 1
  ring
variable [DecidableEq m]
end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling

variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

lemma eval_real {C : Matrix m n ℂ} {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : eval C A B = (prob C A B : ℂ) := by
  have h := ((hA.kronecker hB).dotProduct_mulVec_nonneg (vec C))
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp h).2.symm

lemma eval_kronecker (C : Matrix m n ℂ) (D : Matrix p q ℂ)
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (E : Matrix p p ℂ) (F : Matrix q q ℂ) :
    eval (C ⊗ₖ D) (A ⊗ₖ E) (B ⊗ₖ F) = eval C A B * eval D E F := by
  simp only [eval_eq_trace, Matrix.conjTranspose_kronecker, ← Matrix.kroneckerMap_transpose,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

lemma prob_kronecker (C : Matrix m n ℂ) (D : Matrix p q ℂ)
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} {E : Matrix p p ℂ} {F : Matrix q q ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hE : E.PosSemidef) (hF : F.PosSemidef) :
    prob (C ⊗ₖ D) (A ⊗ₖ E) (B ⊗ₖ F) = prob C A B * prob D E F := by
  change (eval _ _ _).re = _
  rw [eval_kronecker, eval_real hA hB, eval_real hE hF,
    ← Complex.ofReal_mul, Complex.ofReal_re]

lemma hsSq_kronecker (C : Matrix m n ℂ) (D : Matrix p q ℂ) :
    hsSq (C ⊗ₖ D) = hsSq C * hsSq D := by
  classical
  simpa only [prob_one, Matrix.one_kronecker_one] using
    (prob_kronecker C D (A := 1) (B := 1) (E := 1) (F := 1)
      Matrix.PosSemidef.one Matrix.PosSemidef.one Matrix.PosSemidef.one Matrix.PosSemidef.one)

lemma eval_pullback (C : Matrix m n ℂ) (K : Matrix p m ℂ) (L : Matrix q n ℂ)
    (A : Matrix p p ℂ) (B : Matrix q q ℂ) :
    eval C (Kᴴ*A*K) (Lᴴ*B*L) = eval (K*C*Lᵀ) A B := by
  simp only [eval_eq_trace, Matrix.conjTranspose_mul, Matrix.transpose_mul,
    Matrix.conjTranspose_transpose, Matrix.transpose_conjTranspose,
    Matrix.mul_assoc]
  conv_rhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma prob_pullback (C : Matrix m n ℂ) (K : Matrix p m ℂ) (L : Matrix q n ℂ)
    (A : Matrix p p ℂ) (B : Matrix q q ℂ) :
    prob C (Kᴴ*A*K) (Lᴴ*B*L) = prob (K*C*Lᵀ) A B := by
  simp only [prob, eval_pullback]

end ThresholdParallelRepetition.QuantumSampling

end
end
end
end
end

end OAI

-- ---- from OAI.Probability.EntangledGames.SamplingStrategy ----
namespace OAI

universe u_n u_A u_m u_ι u_p u_q u_B

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped Kronecker

noncomputable section
namespace ThresholdParallelRepetition.QuantumSampling

variable {m : Type u_m} {n : Type u_n} {A : Type u_A} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype A]

lemma hsSq_tensorPower {m n : Type} [Fintype m] [Fintype n] (D : Matrix m n ℂ) (t : ℕ) :
    hsSq (tensorPower D t) = hsSq D ^ t := by
  induction t with
  | zero => simp [tensorPower, hsSq]
  | succ t ih => rw [tensorPower, hsSq_kronecker, ih, pow_succ']

lemma eval_submatrix {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (C : Matrix m n ℂ) (U : Matrix m m ℂ) (V : Matrix n n ℂ) (e : p ≃ m) (f : q ≃ n) :
    eval (C.submatrix e f) (U.submatrix e e) (V.submatrix f f) = eval C U V := by
  simp only [eval_eq_sum, Matrix.submatrix_apply]
  apply Fintype.sum_equiv e
  intro i
  apply Fintype.sum_equiv f
  intro j
  apply Fintype.sum_equiv e
  intro k
  exact Fintype.sum_equiv f _ _ (fun _ => rfl)

lemma exists_strategy_of_finite {m n X Y A B : Type}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n]
    [Fintype A] [Fintype B] (C : Matrix m n ℂ) (hC : hsSq C = 1)
    (P : X → POVM m A) (Q : Y → POVM n B) :
    ∃ S : Strategy X Y A B, ∀ x y a b, S.born x y a b = prob C ((P x).effect a) ((Q y).effect b) := by
  let e : Fin (Fintype.card m - 1 + 1) ≃ m :=
    (Fintype.equivFinOfCardEq (Nat.sub_add_cancel Fintype.card_pos).symm).symm
  let f : Fin (Fintype.card n - 1 + 1) ≃ n :=
    (Fintype.equivFinOfCardEq (Nat.sub_add_cancel Fintype.card_pos).symm).symm
  let S : Strategy X Y A B := {
    dimA := Fintype.card m - 1
    dimB := Fintype.card n - 1
    state := vec (C.submatrix e f)
    state_unit := by
      simp only [vec, Matrix.submatrix_apply, Fintype.sum_prod_type]
      rw [show (∑ i, ∑ j, Complex.normSq (C (e i) (f j))) = hsSq C by
        unfold hsSq
        apply Fintype.sum_equiv e
        intro i
        exact Fintype.sum_equiv f _ _ (fun _ => rfl)]
      exact hC
    alice := fun x a => ((P x).effect a).submatrix e e
    bob := fun y b => ((Q y).effect b).submatrix f f
    alice_pos := fun x a => ((P x).pos a).submatrix e
    bob_pos := fun y b => ((Q y).pos b).submatrix f
    alice_total := fun x => by
      calc
        _ = (∑ a, (P x).effect a).submatrix e e := by ext i j; simp [Matrix.sum_apply]
        _ = 1 := by rw [(P x).total, Matrix.submatrix_one_equiv]
    bob_total := fun y => by
      calc
        _ = (∑ b, (Q y).effect b).submatrix f f := by ext i j; simp [Matrix.sum_apply]
        _ = 1 := by rw [(Q y).total, Matrix.submatrix_one_equiv] }
  refine ⟨S, ?_⟩
  intro x y a b
  rw [Strategy.born_eq_quadratic]
  change prob (C.submatrix e f) (((P x).effect a).submatrix e e)
    (((Q y).effect b).submatrix f f) = _
  exact congrArg Complex.re (eval_submatrix C _ _ e f)

lemma prob_first_step_ge {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (C : Matrix m n ℂ) (D : Matrix p q ℂ) (hD : hsSq D = 1)
    {G F : Matrix m m ℂ} {H J : Matrix n n ℂ} {E : Matrix p p ℂ} {T : Matrix q q ℂ}
    (hG : G.PosSemidef) (hF : F.PosSemidef) (hH : H.PosSemidef) (hJ : J.PosSemidef)
    (hE : E.PosSemidef) (hT : T.PosSemidef) :
    prob C G H + prob C F J * prob D E T ≤
      prob (C ⊗ₖ D) (G ⊗ₖ 1 + F ⊗ₖ E) (H ⊗ₖ 1 + J ⊗ₖ T) := by
  rw [prob_add_left, prob_add_right, prob_add_right,
    prob_kronecker C D hG hH Matrix.PosSemidef.one Matrix.PosSemidef.one,
    prob_one, hD, mul_one, prob_kronecker C D hF hJ hE hT]
  have h1 := prob_nonneg (C := C ⊗ₖ D) (hG.kronecker Matrix.PosSemidef.one) (hJ.kronecker hT)
  have h2 := prob_nonneg (C := C ⊗ₖ D) (hF.kronecker hE) (hH.kronecker Matrix.PosSemidef.one)
  linarith

lemma firstSuccess_prob_succ {m n p q A B : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Fintype A] [Fintype B]
    (D : Matrix n q ℂ) (hD : hsSq D = 1) (P : POVM m A) (Q : POVM p B)
    (K : Matrix m n ℂ) (L : Matrix p q ℂ) (hK : Kᴴ*K ≤ 1) (hL : Lᴴ*L ≤ 1)
    (a₀ : A) (b₀ : B) (t : ℕ) (a : A) (b : B) :
    prob (K*D*Lᵀ) (P.effect a) (Q.effect b) +
      prob D (1-Kᴴ*K) (1-Lᴴ*L) *
        prob (tensorPower D t) ((firstSuccess P K hK a₀ t).effect a)
          ((firstSuccess Q L hL b₀ t).effect b) ≤
      prob (tensorPower D (t+1)) ((firstSuccess P K hK a₀ (t+1)).effect a)
        ((firstSuccess Q L hL b₀ (t+1)).effect b) := by
  change _ ≤ prob (D ⊗ₖ tensorPower D t)
    (P.pull K a ⊗ₖ 1 + (1-Kᴴ*K) ⊗ₖ (firstSuccess P K hK a₀ t).effect a)
    (Q.pull L b ⊗ₖ 1 + (1-Lᴴ*L) ⊗ₖ (firstSuccess Q L hL b₀ t).effect b)
  have hnorm : hsSq (tensorPower D t) = 1 := by rw [hsSq_tensorPower, hD, one_pow]
  have h := prob_first_step_ge D (tensorPower D t) hnorm (P.pull_pos K a)
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hK)) (Q.pull_pos L b)
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hL))
    ((firstSuccess P K hK a₀ t).pos a) ((firstSuccess Q L hL b₀ t).pos b)
  simpa only [POVM.pull, prob_pullback] using h

section Payoff
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype A] [Fintype B]

lemma prob_total (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) :
    ∑ a, ∑ b, prob C (P.effect a) (Q.effect b) = hsSq C := by
  simp_rw [← prob_sum_right, ← prob_sum_left, P.total, Q.total, prob_one]
lemma payoff_nonneg (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    0 ≤ payoff C P Q V := by
  apply Finset.sum_nonneg; intro a _
  apply Finset.sum_nonneg; intro b _
  split
  · exact prob_nonneg (P.pos a) (Q.pos b)
  · exact le_rfl
lemma payoff_le_hsSq (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    payoff C P Q V ≤ hsSq C := by
  rw [← prob_total C P Q]
  apply Finset.sum_le_sum; intro a _
  apply Finset.sum_le_sum; intro b _
  split
  · exact le_rfl
  · exact prob_nonneg (P.pos a) (Q.pos b)
end Payoff

lemma firstSuccess_prob_geometric {m n p q A B : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Fintype A] [Fintype B]
    (D : Matrix n q ℂ) (hD : hsSq D = 1) (P : POVM m A) (Q : POVM p B)
    (K : Matrix m n ℂ) (L : Matrix p q ℂ) (hK : Kᴴ*K ≤ 1) (hL : Lᴴ*L ≤ 1)
    (a₀ : A) (b₀ : B) (t : ℕ) (a : A) (b : B) :
    prob (K*D*Lᵀ) (P.effect a) (Q.effect b) *
      (∑ j ∈ Finset.range t, (prob D (1-Kᴴ*K) (1-Lᴴ*L))^j) ≤
      prob (tensorPower D t) ((firstSuccess P K hK a₀ t).effect a)
        ((firstSuccess Q L hL b₀ t).effect b) := by
  let z := prob D (1-Kᴴ*K) (1-Lᴴ*L)
  have hz : 0 ≤ z := prob_nonneg
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hK))
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hL))
  induction t with
  | zero =>
    simpa only [Finset.range_zero, Finset.sum_empty, mul_zero] using
      (prob_nonneg ((firstSuccess P K hK a₀ 0).pos a) ((firstSuccess Q L hL b₀ 0).pos b)
        (C := tensorPower D 0))
  | succ t ih =>
    calc
      _ = prob (K*D*Lᵀ) (P.effect a) (Q.effect b) + z *
          (prob (K*D*Lᵀ) (P.effect a) (Q.effect b) * ∑ j ∈ Finset.range t, z^j) := by
        change _ * (∑ j ∈ Finset.range (t+1), z^j) = _
        rw [Finset.sum_range_succ']
        simp only [pow_succ', ← Finset.mul_sum, pow_zero]
        ring
      _ ≤ prob (K*D*Lᵀ) (P.effect a) (Q.effect b) + z *
          prob (tensorPower D t) ((firstSuccess P K hK a₀ t).effect a)
            ((firstSuccess Q L hL b₀ t).effect b) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hz)
      _ ≤ _ := firstSuccess_prob_succ D hD P Q K L hK hL a₀ b₀ t a b

lemma firstSuccess_payoff_geometric {m n p q A B : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Fintype A] [Fintype B]
    (D : Matrix n q ℂ) (hD : hsSq D = 1) (P : POVM m A) (Q : POVM p B)
    (K : Matrix m n ℂ) (L : Matrix p q ℂ) (hK : Kᴴ*K ≤ 1) (hL : Lᴴ*L ≤ 1)
    (a₀ : A) (b₀ : B) (t : ℕ) (V : A → B → Bool) :
    payoff (K*D*Lᵀ) P Q V *
      (∑ j ∈ Finset.range t, (prob D (1-Kᴴ*K) (1-Lᴴ*L))^j) ≤
      payoff (tensorPower D t) (firstSuccess P K hK a₀ t) (firstSuccess Q L hL b₀ t) V := by
  simp only [payoff, Finset.sum_mul]
  apply Finset.sum_le_sum; intro a _
  apply Finset.sum_le_sum; intro b _
  split
  · exact firstSuccess_prob_geometric D hD P Q K L hK hL a₀ b₀ t a b
  · simp

lemma finite_filter_geometric_value {m n p q : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Nonempty n] [Nonempty q] {x y a b : ℕ} (G : Game x y a b)
    (D : Matrix n q ℂ) (hD : hsSq D = 1)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM p (Fin (b+1)))
    (K : Fin (x+1) → Matrix m n ℂ) (L : Fin (y+1) → Matrix p q ℂ)
    (hK : ∀ x, (K x)ᴴ*K x ≤ 1) (hL : ∀ y, (L y)ᴴ*L y ≤ 1) (t : ℕ) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      (payoff (K z.1*D*(L z.2)ᵀ) (P z.1) (Q z.2) (G.accepts z.1 z.2) *
        ∑ j ∈ Finset.range t, (prob D (1-(K z.1)ᴴ*K z.1) (1-(L z.2)ᴴ*L z.2))^j)) ≤
      entangledValue G := by
  have hnorm : hsSq (tensorPower D t) = 1 := by rw [hsSq_tensorPower, hD, one_pow]
  obtain ⟨S, hS⟩ := exists_strategy_of_finite (tensorPower D t) hnorm
    (fun x => firstSuccess (P x) (K x) (hK x) 0 t)
    (fun y => firstSuccess (Q y) (L y) (hL y) 0 t)
  apply le_trans ?_ (successProbability_le_value G S)
  unfold successProbability
  apply Finset.sum_le_sum; intro z _
  apply mul_le_mul_of_nonneg_left _ (G.questionProb_nonneg z)
  rw [Fintype.sum_prod_type]
  simp_rw [hS]
  exact firstSuccess_payoff_geometric D hD (P z.1) (Q z.2) (K z.1) (L z.2)
    (hK z.1) (hL z.2) 0 0 t (G.accepts z.1 z.2)

section FilterMass
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

omit [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q] in
lemma prob_sub_left (C : Matrix m n ℂ) (A A' : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C (A-A') B = prob C A B - prob C A' B := by
  simp only [prob, eval_eq_trace, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
omit [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q] in
lemma prob_sub_right (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B B' : Matrix n n ℂ) :
    prob C A (B-B') = prob C A B - prob C A B' := by
  simp only [prob, eval_eq_trace, Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

omit [DecidableEq n] [DecidableEq q] in
lemma prob_gram (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ) :
    prob D (Kᴴ*K) (Lᴴ*L) = hsSq (K*D*Lᵀ) := by
  simpa only [Matrix.mul_one, prob_one] using prob_pullback D K L (1 : Matrix m m ℂ) (1 : Matrix p p ℂ)
omit [Fintype p] [DecidableEq p] [DecidableEq n] in
lemma prob_left_gram (D : Matrix n q ℂ) (K : Matrix m n ℂ) :
    prob D (Kᴴ*K) 1 = hsSq (K*D) := by
  simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] using
    prob_gram D K (1 : Matrix q q ℂ)
omit [Fintype m] [DecidableEq m] [DecidableEq q] in
lemma prob_right_gram (D : Matrix n q ℂ) (L : Matrix p q ℂ) :
    prob D 1 (Lᴴ*L) = hsSq (D*Lᵀ) := by
  simpa only [Matrix.conjTranspose_one, Matrix.one_mul] using
    prob_gram D (1 : Matrix n n ℂ) L

lemma prob_fail (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ) :
    prob D (1-Kᴴ*K) (1-Lᴴ*L) =
      hsSq D - hsSq (K*D) - hsSq (D*Lᵀ) + hsSq (K*D*Lᵀ) := by
  rw [prob_sub_left, prob_sub_right, prob_sub_right, prob_one, prob_right_gram,
    prob_left_gram, prob_gram]
  ring

lemma prob_fail_le (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ)
    (hK : Kᴴ*K ≤ 1) (hL : Lᴴ*L ≤ 1) :
    prob D (1-Kᴴ*K) (1-Lᴴ*L) ≤ hsSq D := by
  rw [prob_fail]
  have h := (filter_mass_bounds D K L hK hL).1
  have hb := hsSq_nonneg (D*Lᵀ)
  linarith

lemma output_zero_of_fail_full (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ)
    (hK : Kᴴ*K ≤ 1) (hL : Lᴴ*L ≤ 1)
    (h : prob D (1-Kᴴ*K) (1-Lᴴ*L) = hsSq D) : hsSq (K*D*Lᵀ) = 0 := by
  rw [prob_fail] at h
  obtain ⟨h1,h2,_,_⟩ := filter_mass_bounds D K L hK hL
  have h0 := hsSq_nonneg (K*D*Lᵀ)
  linarith
end FilterMass

open Filter Topology
lemma geometric_contribution_tendsto {w z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hw : z = 1 → w = 0) :
    Tendsto (fun t : ℕ => w * ∑ j ∈ Finset.range t, z^j) atTop (𝓝 (w/(1-z))) := by
  by_cases hz : z = 1
  · simp only [hw hz, zero_mul, zero_div]
    exact tendsto_const_nhds
  · simpa only [div_eq_mul_inv] using
      ((hasSum_geometric_of_lt_one hz0 (lt_of_le_of_ne hz1 hz)).tendsto_sum_nat.const_mul w)

theorem finite_filter_value {m n p q : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Nonempty n] [Nonempty q] {x y a b : ℕ} (G : Game x y a b)
    (D : Matrix n q ℂ) (hD : hsSq D = 1)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM p (Fin (b+1)))
    (K : Fin (x+1) → Matrix m n ℂ) (L : Fin (y+1) → Matrix p q ℂ)
    (hK : ∀ x, (K x)ᴴ*K x ≤ 1) (hL : ∀ y, (L y)ᴴ*L y ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      (payoff (K z.1*D*(L z.2)ᵀ) (P z.1) (Q z.2) (G.accepts z.1 z.2) /
        (1-prob D (1-(K z.1)ᴴ*K z.1) (1-(L z.2)ᴴ*L z.2)))) ≤ entangledValue G := by
  apply le_of_tendsto' (x := atTop) (f := fun t : ℕ => ∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
    (payoff (K z.1*D*(L z.2)ᵀ) (P z.1) (Q z.2) (G.accepts z.1 z.2) *
       ∑ j ∈ Finset.range t, (prob D (1-(K z.1)ᴴ*K z.1) (1-(L z.2)ᴴ*L z.2))^j))
  · apply tendsto_finsetSum
    intro z _
    apply Filter.Tendsto.const_mul
    apply geometric_contribution_tendsto
    · exact prob_nonneg (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (hK z.1)))
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (hL z.2)))
    · rw [← hD]; exact prob_fail_le D (K z.1) (L z.2) (hK z.1) (hL z.2)
    · intro hz
      have hn := output_zero_of_fail_full D (K z.1) (L z.2) (hK z.1) (hL z.2) (hz.trans hD.symm)
      exact le_antisymm ((payoff_le_hsSq _ _ _ _).trans_eq hn) (payoff_nonneg _ _ _ _)
  · exact fun t => finite_filter_geometric_value G D hD P Q K L hK hL t

lemma prob_smul {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
    (r : ℝ) (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob (r • C) A B = r^2 * prob C A B := by
  simp only [prob, eval_eq_trace, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

lemma payoff_smul {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype A] [Fintype B] (r : ℝ) (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) : payoff (r • C) P Q V = r^2 * payoff C P Q V := by
  simp only [payoff, prob_smul, Finset.mul_sum, mul_ite, mul_zero]

theorem finite_filter_value_unnormalized {m n p q : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Nonempty n] [Nonempty q] {x y a b : ℕ} (G : Game x y a b)
    (D : Matrix n q ℂ) (hD : 0 < hsSq D)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM p (Fin (b+1)))
    (K : Fin (x+1) → Matrix m n ℂ) (L : Fin (y+1) → Matrix p q ℂ)
    (hK : ∀ x, (K x)ᴴ*K x ≤ 1) (hL : ∀ y, (L y)ᴴ*L y ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      (payoff (K z.1*D*(L z.2)ᵀ) (P z.1) (Q z.2) (G.accepts z.1 z.2) /
        (hsSq (K z.1*D) + hsSq (D*(L z.2)ᵀ) - hsSq (K z.1*D*(L z.2)ᵀ)))) ≤
      entangledValue G := by
  let r : ℝ := (Real.sqrt (hsSq D))⁻¹
  have hr : r^2 = (hsSq D)⁻¹ := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt hD.le]
  have hnorm : hsSq (r • D) = 1 := by
    rw [hsSq_smul, hr, inv_mul_cancel₀ hD.ne']
  have hv := finite_filter_value G (r • D) hnorm P Q K L hK hL
  convert hv using 1
  apply Finset.sum_congr rfl; intro z _
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul, payoff_smul, prob_smul, hr]
  have hden : (1 - (hsSq D)⁻¹ * prob D (1-(K z.1)ᴴ*K z.1) (1-(L z.2)ᴴ*L z.2)) =
      (hsSq D - prob D (1-(K z.1)ᴴ*K z.1) (1-(L z.2)ᴴ*L z.2)) / hsSq D := by
    field_simp
  rw [hden, inv_mul_eq_div, div_div_div_cancel_right₀ hD.ne', prob_fail]
  congr 1
  ring

end ThresholdParallelRepetition.QuantumSampling

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.QuantumSampling
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped Kronecker
open Filter Topology


theorem solution : type_of% @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.finite_filter_value_unnormalized := @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.finite_filter_value_unnormalized
