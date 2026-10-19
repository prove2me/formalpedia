-- Prove2me | solution 1 for OAI.EuclideanSteinitzBergstrom.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:21:37.222519+00:00
-- url     : https://prove2.me/submissions/fcf241ac-b15c-41bb-8492-14cb3cafaf39

import Mathlib
import Definitions.Def_SteinitzBergstrom
import Definitions.Def_OAIQWESB000
import Theorems.Thm_OAI_EuclideanSteinitz_Filter_applicationDomain_survival
import Theorems.Thm_OAI_EuclideanSteinitzBergstrom_signing_implies_ordering
import Theorems.Thm_OAI_ShiftedSections_adaptive_linear_equations

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.MatrixEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar potentials and spectral endpoint inequalities. -/

namespace EuclideanSteinitz.MatrixEnergy

open Matrix
open scoped MatrixOrder

section Scalar

lemma exponent_pos : 0 < exponent := by norm_num [exponent]

end Scalar

section RealMatrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma hermitian_dot (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (x y : ι → ℝ) : x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
  have ht : A.transpose = A := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  have hx : x ᵥ* A = A *ᵥ x := by simpa only [ht] using Matrix.vecMul_transpose A x
  rw [Matrix.dotProduct_mulVec, hx]

lemma le_of_square_le {S T : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hT : T.PosSemidef) (hst : S * S ≤ T * T) : S ≤ T := by
  let D := T - S
  have hD : D.IsHermitian := hT.1.sub hS.1
  change D.PosSemidef
  apply hD.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  let v : ι → ℝ := (hD.eigenvectorBasis i).ofLp
  let eig := hD.eigenvalues i
  have heig : D *ᵥ v = eig • v := hD.mulVec_eigenvectorBasis i
  have hv : v ⬝ᵥ v = 1 := by
    have hn := real_inner_self_eq_norm_sq (hD.eigenvectorBasis i)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      OrthonormalBasis.norm_eq_one, one_pow] using hn
  have hs : 0 ≤ v ⬝ᵥ (S *ᵥ v) := by
    simpa only [star_trivial] using hS.dotProduct_mulVec_nonneg v
  have ht : 0 ≤ v ⬝ᵥ (T *ᵥ v) := by
    simpa only [star_trivial] using hT.dotProduct_mulVec_nonneg v
  have hd : v ⬝ᵥ (T *ᵥ v) - v ⬝ᵥ (S *ᵥ v) = eig := by
    have hdv : v ⬝ᵥ (D *ᵥ v) = eig := by rw [heig, dotProduct_smul, hv]; simp
    simpa only [D, Matrix.sub_mulVec, dotProduct_sub] using hdv
  have hq : 0 ≤ v ⬝ᵥ ((T * T - S * S) *ᵥ v) := by
    simpa only [star_trivial] using (Matrix.le_iff.mp hst).dotProduct_mulVec_nonneg v
  have hid : T * T - S * S = T * D + D * S := by dsimp [D]; noncomm_ring
  have hformula : v ⬝ᵥ ((T * T - S * S) *ᵥ v) =
      eig * (v ⬝ᵥ (T *ᵥ v) + v ⬝ᵥ (S *ᵥ v)) := by
    rw [hid, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, dotProduct_smul,
      hermitian_dot D hD, heig, smul_dotProduct]
    simp only [smul_eq_mul]
    ring
  rw [hformula] at hq
  change 0 ≤ eig
  by_contra hh
  have hn : eig < 0 := lt_of_not_ge hh
  have hp : 0 < v ⬝ᵥ (T *ᵥ v) + v ⬝ᵥ (S *ᵥ v) := by linarith
  exact (not_lt_of_ge hq) (mul_neg_of_neg_of_pos hn hp)

lemma sqrt_le_sqrt {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hab : A ≤ B) : CFC.sqrt A ≤ CFC.sqrt B := by
  apply le_of_square_le (CFC.sqrt_nonneg A).posSemidef (CFC.sqrt_nonneg B).posSemidef
  simpa only [← sq, CFC.sq_sqrt A hA.nonneg, CFC.sq_sqrt B hB.nonneg] using hab

end RealMatrices
end EuclideanSteinitz.MatrixEnergy

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Gain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contraction and gain potentials for positive semidefinite matrices. -/

namespace EuclideanSteinitz.Gain
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gainConstant_pos : 0 < gainConstant := by
  unfold gainConstant
  exact mul_pos exponent_pos (Real.rpow_pos_of_pos (by norm_num) _)

end EuclideanSteinitz.Gain

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Telescoping matrix energy and trace budgets. -/

namespace EuclideanSteinitz.Energy
open Matrix MatrixEnergy Gain Spectral
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma incrementConstant_pos : 0 < incrementConstant := by
  have hc := gainConstant_pos
  unfold incrementConstant
  positivity

end EuclideanSteinitz.Energy

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Filter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric contraction updates and filtered matrix states. -/

namespace EuclideanSteinitz.Filter
open Matrix MatrixEnergy Gain Energy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
lemma mul_insert_transpose (R : Matrix ι κ ℝ) (b : ι → ℝ) (j : κ) :
    R * (insert b j).transpose = vecMulVec (fun i => R i j) b := by
  ext i k
  simp [Matrix.mul_apply, insert, Matrix.transpose_apply, vecMulVec_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma insert_mul_transpose_zero (R : Matrix ι κ ℝ) (b : ι → ℝ) (j : κ)
    (hR : ∀ i, R i j = 0) : insert b j * R.transpose = 0 := by
  apply Matrix.transpose_injective
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero,
    mul_insert_transpose]
  ext i k
  simp only [vecMulVec_apply, hR, zero_mul, Matrix.zero_apply]

omit [Fintype κ] [DecidableEq ι] in
lemma step_apply_column (p : Step ι κ) (R : Matrix ι κ ℝ) {j : κ}
    (hj : j ≠ p.j) (hR : ∀ i, R i j = 0) : ∀ i, p.apply R i j = 0 := by
  intro i
  simp [Step.apply, Matrix.mul_apply, insert, hj, hR]

lemma Step.coisometry {p : Step ι κ} (hp : p.Good) {R : Matrix ι κ ℝ}
    (hR : R * R.transpose = 1) (hf : ∀ i, R i p.j = 0) :
    p.apply R * (p.apply R).transpose = 1 := by
  have hz : R * (insert p.b p.j).transpose = 0 := by
    rw [mul_insert_transpose]
    ext i k
    simp [vecMulVec_apply, hf]
  have hz' := insert_mul_transpose_zero R p.b p.j hf
  have h₁ : p.C * R * (p.C * R).transpose = p.C * p.C.transpose := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc p.C R, ← Matrix.mul_assoc R, hR, Matrix.one_mul]
  have h₂ : p.C * R * (insert p.b p.j).transpose = 0 := by
    rw [Matrix.mul_assoc, hz, Matrix.mul_zero]
  have h₃ : insert p.b p.j * (p.C * R).transpose = 0 := by
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc, hz', Matrix.zero_mul]
  simpa only [Step.apply, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
    h₁, h₂, h₃, insert_mul_transpose, add_zero, zero_add] using hp.2

omit [Fintype κ] [DecidableEq ι] in
lemma Step.fresh_tail {p : Step ι κ} {ps : List (Step ι κ)} {R : Matrix ι κ ℝ}
    (hf : Fresh R (p :: ps)) (hd : ∀ r ∈ ps, p.j ≠ r.j) : Fresh (p.apply R) ps := by
  intro r hr
  exact step_apply_column p R (Ne.symm (hd r hr)) (hf r (List.mem_cons_of_mem p hr))

lemma run_coisometry {R : Matrix ι κ ℝ} (hR : R * R.transpose = 1)
    {ps : List (Step ι κ)} (hp : ∀ p ∈ ps, p.Good) (hf : Fresh R ps)
    (hd : (ps.map Step.j).Nodup) : run R ps * (run R ps).transpose = 1 := by
  induction ps generalizing R with
  | nil => exact hR
  | cons p ps ih =>
    have hd' := List.nodup_cons.mp hd
    have htail : ∀ r ∈ ps, p.j ≠ r.j := by
      intro r hr he
      apply hd'.1
      exact List.mem_map.mpr ⟨r, hr, he.symm⟩
    exact ih (Step.coisometry (hp p (List.mem_cons_self ..)) hR (hf p (List.mem_cons_self ..)))
      (fun r hr => hp r (List.mem_cons_of_mem p hr)) (Step.fresh_tail hf htail) hd'.2

end EuclideanSteinitz.Filter

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.FilterMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filtered moments, prefix bounds, and rank-one contractions. -/

section

namespace EuclideanSteinitz.Filter
open Matrix MatrixEnergy Gain Energy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq ι] in
lemma run_fresh_append {R : Matrix ι κ ℝ} {ps qs : List (Step ι κ)}
    (hf : Fresh R (ps++qs)) (hd : ((ps++qs).map Step.j).Nodup) : Fresh (run R ps) qs := by
  induction ps generalizing R with
  | nil => exact hf
  | cons p ps ih =>
    have hh := List.nodup_cons.mp hd
    apply ih (R := p.apply R) _ hh.2
    apply Step.fresh_tail hf
    intro q hq he
    exact hh.1 (List.mem_map.mpr ⟨q,hq,he.symm⟩)

omit [Fintype κ] [DecidableEq κ] in
lemma good_prefix {ps qs : List (Step ι κ)} (hp : ∀ p∈qs,p.Good) (h : ps <+: qs) :
    ∀ p∈ps,p.Good := fun p hp' => hp p (h.subset hp')

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma fresh_prefix {R : Matrix ι κ ℝ} {ps qs : List (Step ι κ)} (hf : Fresh R qs) (h : ps <+: qs) :
    Fresh R ps := fun p hp => hf p (h.subset hp)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma nodup_prefix {ps qs : List (Step ι κ)} (hd : (qs.map Step.j).Nodup) (h : ps <+: qs) :
    (ps.map Step.j).Nodup := (h.map _).sublist.nodup hd

end EuclideanSteinitz.Filter

end

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma vectorMass_nonneg (b : ι → ℝ) : 0≤vectorMass b := Finset.sum_nonneg fun i _ => sq_nonneg (b i)
omit [DecidableEq ι] in
lemma eta_pos (b : ι → ℝ) : 0<eta b := div_pos (by norm_num) (by linarith [Real.sqrt_nonneg (1-vectorMass b)])
omit [DecidableEq ι] in
lemma eta_le_one (b : ι → ℝ) : eta b≤1 := by unfold eta; apply (div_le_one (by positivity)).mpr; linarith [Real.sqrt_nonneg (1-vectorMass b)]

omit [DecidableEq ι] in
lemma eta_identity {b : ι → ℝ} (hb : vectorMass b≤1) : 2*eta b-eta b^2*vectorMass b=1 := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hb)
  have hpos : 0<1+Real.sqrt (1-vectorMass b) := by positivity
  unfold eta
  field_simp
  nlinarith

omit [DecidableEq ι] in
lemma rank_square (b : ι → ℝ) : vecMulVec b b*vecMulVec b b=vectorMass b • vecMulVec b b := by
  ext i j
  simp only [Matrix.mul_apply,vecMulVec_apply,Matrix.smul_apply,smul_eq_mul,vectorMass]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma symmetricContraction_transpose (b : ι → ℝ) : (symmetricContraction b).transpose=symmetricContraction b := by
  simp [symmetricContraction]

lemma symmetricContraction_square {b : ι → ℝ} (hb : vectorMass b≤1) :
    symmetricContraction b*symmetricContraction b+vecMulVec b b=1 := by
  unfold symmetricContraction
  simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,Matrix.smul_mul,Matrix.mul_smul,rank_square,smul_smul]
  have he := eta_identity hb
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  linear_combination -(vecMulVec b b i j) * he

lemma symmetricContraction_unit {b : ι → ℝ} (hb : vectorMass b<1) : IsUnit (symmetricContraction b) := by
  let t := eta b/(1-eta b*vectorMass b)
  have hd : 0<1-eta b*vectorMass b := by
    have h := mul_le_mul_of_nonneg_right (eta_le_one b) (vectorMass_nonneg b)
    linarith
  have ht : t-eta b-eta b*t*vectorMass b=0 := by
    dsimp [t]
    field_simp
    ring
  have hmul : symmetricContraction b*(1+t • vecMulVec b b)=1 := by
    unfold symmetricContraction
    simp only [Matrix.sub_mul,Matrix.mul_add,Matrix.one_mul,Matrix.mul_one,Matrix.smul_mul,Matrix.mul_smul,rank_square,smul_smul]
    ext i j
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    linear_combination (vecMulVec b b i j) * ht
  have hmul' : (1+t • vecMulVec b b)*symmetricContraction b=1 := by
    have hh := congrArg Matrix.transpose hmul
    simpa only [Matrix.transpose_mul,symmetricContraction_transpose,Matrix.transpose_add,Matrix.transpose_one,
      Matrix.transpose_smul,Matrix.transpose_vecMulVec] using hh
  exact ⟨⟨symmetricContraction b,1+t • vecMulVec b b,hmul,hmul'⟩,rfl⟩

lemma symmetricStep_good {b : ι → ℝ} (hb : vectorMass b<1) (j : κ) : (symmetricStep b j).Good := by
  refine ⟨symmetricContraction_unit hb,?_⟩
  change symmetricContraction b*(symmetricContraction b).transpose+vecMulVec b b=1
  rw [symmetricContraction_transpose]
  exact symmetricContraction_square hb.le

lemma contraction_loss {b : ι → ℝ} (hb : vectorMass b≤1) (x : ι → ℝ) :
    vectorMass x-vectorMass (symmetricContraction b*ᵥx)=(b ⬝ᵥ x)^2 := by
  have he := symmetricContraction_square hb
  have ht := symmetricContraction_transpose b
  have hgram : (symmetricContraction b).transpose*symmetricContraction b=1-vecMulVec b b := by
    rw [ht,← he]; abel
  have hh := congrArg (fun A : Matrix ι ι ℝ => x ⬝ᵥ(A*ᵥx)) hgram
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,
    Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub,Matrix.vecMulVec_mulVec,dotProduct_smul,op_smul_eq_mul] at hh
  rw [dotProduct_comm x b] at hh
  simp only [dotProduct,← pow_two] at hh
  unfold vectorMass
  simp only [dotProduct]
  nlinarith [hh]

lemma contraction_apply (b x : ι → ℝ) :
    symmetricContraction b*ᵥx = x-(eta b*(b ⬝ᵥ x)) • b := by
  unfold symmetricContraction
  rw [Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,op_smul_eq_mul]
  ring

end EuclideanSteinitz.Filter

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Predictor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Predictor-column energy and exact feedback cancellation. -/

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq ι] in
lemma predictorRows_get (R : Matrix ι κ ℝ) (L : List (Step ι κ)) (k : ℕ) (hk : k<L.length) :
    (predictorRows R L)[k]'(by rw [predictorRows_length]; exact hk) =
      rawRow (run R (L.take k)) (L[k].b) := by
  induction L generalizing R k with
  | nil => simp at hk
  | cons p ps ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simpa only [predictorRows,List.getElem_cons_succ,List.take_succ_cons,run] using
        ih (p.apply R) k (by simpa using hk)

omit [DecidableEq κ] in
lemma vectorMass_vecMul {R : Matrix ι κ ℝ} (hR : R*R.transpose=1) (b : ι → ℝ) :
    vectorMass (b ᵥ* R)=vectorMass b := by
  have hh := congrArg (fun A : Matrix ι ι ℝ => b ⬝ᵥ(A*ᵥb)) hR
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.mulVec_transpose,Matrix.one_mulVec] at hh
  simpa only [vectorMass,dotProduct,← pow_two] using hh

omit [DecidableEq κ] in
lemma rawRow_mass {R : Matrix ι κ ℝ} (hR : R*R.transpose=1) (b : ι → ℝ) :
    vectorMass (rawRow R b) ≤ vectorMass b := by
  have he : vectorMass (rawRow R b)=eta b^2*vectorMass (b ᵥ* R) := by
    unfold vectorMass rawRow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow]
    rfl
  rw [he,vectorMass_vecMul hR]
  have hh : eta b^2≤1 := by nlinarith [eta_pos b,eta_le_one b]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (vectorMass_nonneg b)

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma rawRow_zero_col (R : Matrix ι κ ℝ) (b : ι → ℝ) {j : κ} (h : ∀ i,R i j=0) :
    rawRow R b j=0 := by simp [rawRow,h,dotProduct]

omit [Fintype κ] in
lemma rawRow_loss {p : Step ι κ} (hs : p.C=symmetricContraction p.b) (hb : vectorMass p.b≤1)
    (R : Matrix ι κ ℝ) (hR : ∀ i,R i p.j=0) (j : κ) :
    rawRow R p.b j^2+vectorMass (fun i => p.apply R i j) ≤
      vectorMass (fun i => R i j)+(if p.j=j then vectorMass p.b else 0) := by
  have heta : eta p.b^2≤1 := by nlinarith [eta_pos p.b,eta_le_one p.b]
  by_cases hj : p.j=j
  · subst j
    have he : (fun i => p.apply R i p.j)=p.b := by
      ext i
      simp [Step.apply,Matrix.mul_apply,insert,hR]
    rw [he,rawRow_zero_col R p.b hR]
    simp [vectorMass,hR]
  · have he : (fun i => p.apply R i j)=symmetricContraction p.b*ᵥ(fun i => R i j) := by
      ext i
      simp [Step.apply,Matrix.mul_apply,insert,Ne.symm hj,hs,Matrix.mulVec,dotProduct]
    rw [he,ite_eq_right hj]
    have hh := contraction_loss hb (fun i => R i j)
    have hm := mul_le_mul_of_nonneg_right heta (sq_nonneg (p.b ⬝ᵥ fun i => R i j))
    simp only [rawRow,mul_pow]
    nlinarith

omit [Fintype κ] in
lemma predictor_column_budget {R : Matrix ι κ ℝ} {L : List (Step ι κ)}
    (hs : ∀ p∈L,p.C=symmetricContraction p.b) (hb : ∀ p∈L,vectorMass p.b≤1)
    (hf : Fresh R L) (hd : (L.map Step.j).Nodup) (j : κ) :
    ((predictorRows R L).map (fun m => m j^2)).sum + vectorMass (fun i => run R L i j) ≤
      vectorMass (fun i => R i j)+(L.map (fun p => if p.j=j then vectorMass p.b else 0)).sum := by
  induction L generalizing R with
  | nil => simp [predictorRows,run]
  | cons p ps ih =>
    have hd' := List.nodup_cons.mp hd
    have htail : ∀ r∈ps,p.j≠r.j := by
      intro r hr he
      exact hd'.1 (List.mem_map.mpr ⟨r,hr,he.symm⟩)
    have hh := ih (fun r hr => hs r (List.mem_cons_of_mem p hr))
      (fun r hr => hb r (List.mem_cons_of_mem p hr)) (Step.fresh_tail hf htail) hd'.2
    have hstep := rawRow_loss (hs p (List.mem_cons_self ..)) (hb p (List.mem_cons_self ..)) R (hf p (List.mem_cons_self ..)) j
    simp only [predictorRows,List.map_cons,List.sum_cons,run]
    linarith

omit [Fintype κ] [DecidableEq ι] in
lemma insertion_budget {L : List (Step ι κ)} (hd : (L.map Step.j).Nodup) {B : ℝ} (hB : 0≤B)
    (hb : ∀ p∈L,vectorMass p.b≤B) (j : κ) :
    (L.map (fun p => if p.j=j then vectorMass p.b else 0)).sum ≤ B := by
  induction L with
  | nil => simpa using hB
  | cons p ps ih =>
    have hd' := List.nodup_cons.mp hd
    by_cases hj : p.j=j
    · have ht : ∀ r∈ps,r.j≠j := by
        intro r hr he
        exact hd'.1 (List.mem_map.mpr ⟨r,hr,he.trans hj.symm⟩)
      have hz : (ps.map (fun p => if p.j=j then vectorMass p.b else 0)).sum=0 := by
        rw [List.sum_eq_zero]
        intro x hx
        obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
        simp [ht r hr]
      simpa only [List.map_cons,List.sum_cons,ite_eq_left hj,hz,add_zero] using hb p (List.mem_cons_self ..)
    · simpa only [List.map_cons,List.sum_cons,ite_eq_right hj,zero_add] using
        ih hd'.2 (fun r hr => hb r (List.mem_cons_of_mem p hr))

omit [Fintype κ] in
lemma predictor_column_bound {R : Matrix ι κ ℝ} {L : List (Step ι κ)}
    (hs : ∀ p∈L,p.C=symmetricContraction p.b) (hb : ∀ p∈L,vectorMass p.b≤1)
    (hf : Fresh R L) (hd : (L.map Step.j).Nodup) {B : ℝ} (hB : 0≤B)
    (hbB : ∀ p∈L,vectorMass p.b≤B) (j : κ) (hR : ∀ i,R i j=0) :
    ((predictorRows R L).map (fun m => m j^2)).sum ≤ B := by
  have hh := predictor_column_budget hs hb hf hd j
  have ht := insertion_budget hd hB hbB j
  have hz : vectorMass (fun i => R i j)=0 := by simp [vectorMass,hR]
  rw [hz,zero_add] at hh
  linarith [vectorMass_nonneg (fun i => run R L i j)]

lemma predictor_row_bound {R : Matrix ι κ ℝ} (hR : R*R.transpose=1) {L : List (Step ι κ)}
    (hp : ∀ p∈L,p.Good) (hf : Fresh R L) (hd : (L.map Step.j).Nodup)
    (k : ℕ) (hk : k<L.length) :
    vectorMass ((predictorRows R L)[k]'(by rw [predictorRows_length]; exact hk)) ≤ vectorMass (L[k].b) := by
  rw [predictorRows_get R L k hk]
  apply rawRow_mass
  exact run_coisometry hR (good_prefix hp (List.take_prefix k L)) (fresh_prefix hf (List.take_prefix k L))
    (nodup_prefix hd (List.take_prefix k L))

omit [Fintype κ] [DecidableEq ι] in
lemma predictor_future_zero {R : Matrix ι κ ℝ} {L : List (Step ι κ)}
    (hf : Fresh R L) (hd : (L.map Step.j).Nodup) (k l : ℕ) (hkl : k≤l) (hl : l<L.length) :
    ((predictorRows R L)[k]'(by rw [predictorRows_length]; omega)) (L[l].j)=0 := by
  rw [predictorRows_get R L k (hkl.trans_lt hl)]
  apply rawRow_zero_col
  have ht : Fresh (run R (L.take k)) (L.drop k) := run_fresh_append
    (by simpa only [List.take_append_drop] using hf) (by simpa only [List.take_append_drop] using hd)
  apply ht
  have he : (L.drop k)[l-k]'(by simp only [List.length_drop]; omega)=L[l] := by
    simp only [List.getElem_drop,Nat.add_sub_of_le hkl]
  rw [← he]
  exact List.getElem_mem _

end EuclideanSteinitz.Filter

end

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
lemma rowMap_apply (m : κ → ℝ) (x : EuclideanSpace ℝ κ) : rowMap m x=m ⬝ᵥ x := by
  change inner ℝ (WithLp.toLp 2 m) x=m ⬝ᵥ x
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  exact dotProduct_comm _ _
lemma rowMap_single (m : κ → ℝ) (j : κ) : rowMap m (EuclideanSpace.single j 1)=m j := by
  rw [rowMap_apply]
  simp [dotProduct,PiLp.single_apply]
lemma rowMatrix_norm (m : κ → ℝ) (x : EuclideanSpace ℝ κ) :
    ‖matrixMap (fun _ : Unit => m) x‖=|rowMap m x| := by
  have he : matrixMap (fun _ : Unit => m) x=EuclideanSpace.single () (rowMap m x) := by
    ext u
    cases u
    simp only [PiLp.single_apply,ite_true,rowMap_apply]
    rfl
  rw [he,PiLp.norm_single,Real.norm_eq_abs]

omit [DecidableEq ι] [DecidableEq κ] in
lemma rawRow_eval (R : Matrix ι κ ℝ) (b : ι → ℝ) (x : EuclideanSpace ℝ κ) :
    rowMap (rawRow R b) x=eta b*(b ⬝ᵥ (R*ᵥx)) := by
  rw [rowMap_apply,Matrix.dotProduct_mulVec]
  simp only [dotProduct,rawRow,Matrix.vecMul,← Finset.mul_sum,mul_assoc]

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma noiseRow_mass {ν : Type*} [Fintype ν] (m : ι⊕ν → ℝ) :
    vectorMass (noiseRow m)≤vectorMass m := by
  simp only [vectorMass,Fintype.sum_sum_type,noiseRow,Sum.elim_inl,Sum.elim_inr,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero,zero_add]
  linarith [Finset.sum_nonneg (fun i (_ : i∈(Finset.univ : Finset ι)) => sq_nonneg (m (Sum.inl i)))]

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
lemma noiseRow_eval {ν : Type*} [Fintype ν] [DecidableEq ν] (m : ι⊕ν → ℝ)
    (x : EuclideanSpace ℝ (ι⊕ν)) (hx : ∀ i,x (Sum.inl i)=0) : rowMap (noiseRow m) x=rowMap m x := by
  simp [rowMap_apply,dotProduct,Fintype.sum_sum_type,noiseRow,hx]

omit [DecidableEq ι] [Fintype ι] in
lemma insert_mulVec_eq (b : ι → ℝ) (j : κ) (x : κ → ℝ) : insert b j*ᵥx=(x j) • b := by
  ext i
  simp [insert,Matrix.mulVec,dotProduct,mul_comm]

lemma step_cancel {p : Step ι κ} (hs : p.C=symmetricContraction p.b) (R : Matrix ι κ ℝ)
    (x : EuclideanSpace ℝ κ) (ε : ℝ) (hx : x p.j=rowMap (rawRow R p.b) x+ε) :
    matrixMap (p.apply R) x=matrixMap R x+ε • WithLp.toLp 2 p.b := by
  apply WithLp.ofLp_injective
  change (p.C*R+insert p.b p.j)*ᵥ x=R*ᵥ x+ε • p.b
  rw [Matrix.add_mulVec,← Matrix.mulVec_mulVec,hs,contraction_apply,insert_mulVec_eq,hx,rawRow_eval]
  ext i
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma run_prefix_cancel {n : ℕ} (p : Fin n → Step ι κ) (R : Matrix ι κ ℝ)
    (x : EuclideanSpace ℝ κ) (ε : Fin n → ℝ)
    (hs : ∀ i,(p i).C=symmetricContraction (p i).b)
    (hx : ∀ i,x (p i).j=rowMap (rawRow (run R ((List.ofFn p).take i.val)) (p i).b) x+ε i)
    (k : ℕ) :
    matrixMap (run R ((List.ofFn p).take k)) x = matrixMap R x+
      ((List.ofFn (fun i => ε i • WithLp.toLp 2 (p i).b)).take k).sum := by
  induction n generalizing R k with
  | zero => simp [List.ofFn_zero,run]
  | succ n ih =>
    cases k with
    | zero => simp [run]
    | succ k =>
      have ht : ∀ i : Fin n,x (p i.succ).j=
          rowMap (rawRow (run ((p 0).apply R) ((List.ofFn (fun i : Fin n => p i.succ)).take i.val)) (p i.succ).b) x+ε i.succ := by
        intro i
        simpa only [List.ofFn_succ,Fin.val_succ,List.take_succ_cons,run] using hx i.succ
      have hrec := ih (fun i => p i.succ) ((p 0).apply R) (fun i => ε i.succ) (fun i => hs i.succ) ht k
      simp only [List.ofFn_succ,List.take_succ_cons,run,List.sum_cons]
      rw [hrec,step_cancel (hs 0) R x (ε 0) (by simpa only [Fin.val_zero,List.take_zero,run] using hx 0)]
      abel

end EuclideanSteinitz.Filter

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Survival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian path survival with slab and state constraints. -/

section

open Matrix MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient Gain Energy GaussianTail GaussianAR
variable {ι κ T : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Fintype T]

lemma epochFactor_ge_one : 1≤epochFactor := by
  unfold epochFactor
  linarith [gainConstant_pos]
lemma momentConstant_ge : 16≤ momentConstant := by
  unfold momentConstant
  linarith [incrementConstant_pos]
lemma survivalRadius_pos : 0<survivalRadius := by
  unfold survivalRadius
  linarith [momentConstant_ge]

end EuclideanSteinitz.Filter

end

section

open Matrix MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace GaussianAR
open GaussianTail EuclideanSteinitz.Coefficient EuclideanSteinitz.Filter
variable {ι κ J : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]  [Fintype J]
lemma slabRadius_pos : 0<slabRadius := by norm_num [slabRadius]

end GaussianAR

end

section

open Matrix GaussianTail MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient ScaleMatrix ScaleEnergy Energy GaussianAR
variable {ι κ T : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Fintype T]

lemma stateRadius_pos : 0 < stateRadius := mul_pos (by norm_num) survivalRadius_pos
lemma stateRate_nonneg : 0 ≤ stateRate := by unfold stateRate; linarith [epochFactor_ge_one]

end EuclideanSteinitz.Filter

end

section

open Matrix
open scoped BigOperators
namespace GaussianAR
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma evaluation_apply (r : ι → ℝ) (n : ℕ) (t : Fin (n+1))
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) (i : ι) :
    GaussianTail.matrixMap (evaluation r n t) x i =
      ∑ u : Fin (n+1),row (r i) t.val u.val*x (u,i) := by
  change (∑ u,evaluation r n t i u*x u)=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  simp only [evaluation,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma pathMatrix_apply (r : ι → ℝ) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) (t : Fin (n+1)) (i : ι) :
    GaussianTail.matrixMap (pathMatrix r n) x (t,i) =
      GaussianTail.matrixMap (evaluation r n t) x i := rfl

lemma path_initial (r : ι → ℝ) (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1)×ι)) (i : ι) :
    GaussianTail.matrixMap (pathMatrix r n) x (0,i)=x (0,i) := by
  rw [pathMatrix_apply,evaluation_apply]
  simp only [Fin.val_zero,row,ite_mul,one_mul,zero_mul,Fin.val_eq_zero_iff,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma path_step (r : ι → ℝ) (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1)×ι))
    (t : Fin n) (i : ι) :
    GaussianTail.matrixMap (pathMatrix r n) x (t.succ,i)=
      r i*GaussianTail.matrixMap (pathMatrix r n) x (t.castSucc,i)+
      Real.sqrt (1-(r i)^2)*x (t.succ,i) := by
  simp only [pathMatrix_apply,evaluation_apply,Fin.val_succ,Fin.val_castSucc,row,
    add_mul,ite_mul,zero_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
  congr 1
  have he (u : Fin (n+1)) : (u.val=t.val+1) ↔ u=t.succ := by
    exact (show (u.val=t.succ.val) ↔ u=t.succ from Fin.ext_iff.symm)
  simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma pathEquiv_apply (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) :
    pathEquiv r hr hr1 n x = GaussianTail.matrixMap (pathMatrix r n) x := by
  simp only [pathEquiv,LinearEquiv.coe_toContinuousLinearEquiv',LinearMap.equivOfIsUnitDet_apply]
  rfl

lemma pathEquiv_symm_initial (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) (i : ι) :
    (pathEquiv r hr hr1 n).symm x (0,i) = x (0,i) := by
  have hs := congrArg (fun x : EuclideanSpace ℝ (Fin (n+1)×ι) => x (0,i))
    ((pathEquiv r hr hr1 n).apply_symm_apply x)
  rw [pathEquiv_apply,path_initial] at hs
  exact hs

lemma pathEquiv_symm_step (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) (t : Fin n) (i : ι) :
    (pathEquiv r hr hr1 n).symm x (t.succ,i) =
      (x (t.succ,i)-r i*x (t.castSucc,i))/Real.sqrt (1-(r i)^2) := by
  have hpos : 0 < Real.sqrt (1-(r i)^2) := Real.sqrt_pos.mpr (by nlinarith [hr i,hr1 i])
  have hs := path_step r n ((pathEquiv r hr hr1 n).symm x) t i
  simp only [← pathEquiv_apply r hr hr1,(pathEquiv r hr hr1 n).apply_symm_apply] at hs
  apply (eq_div_iff hpos.ne').mpr
  linarith

lemma pathEquiv_det (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ) :
    (pathEquiv r hr hr1 n).toContinuousLinearMap.det=(∏ i,Real.sqrt (1-(r i)^2))^n := by
  change (pathEquiv r hr hr1 n).toLinearEquiv.toLinearMap.det=_
  simp only [pathEquiv,LinearEquiv.toLinearEquiv_toContinuousLinearEquiv,
    LinearMap.coe_equivOfIsUnitDet,pathMatrix_lin_det,pathMatrix_det]

end GaussianAR

end

section

open ProbabilityTheory
namespace GaussianAR

lemma transition_scalar {r w : ℝ} (hr : 0<r) (hr1 : r<1) (hw : w=(1-r^2)/r)
    (hw0 : 0≤w) (x y : ℝ) :
    (Real.sqrt (1-r^2))⁻¹ * gaussianPDFReal 0 1 ((y-r*x)/Real.sqrt (1-r^2)) ≤
      (Real.sqrt r)⁻¹ * gaussianPDFReal 0 ⟨w,hw0⟩ (y-x) * Real.exp ((x^2-y^2)/4) := by
  have hs : 0 < 1-r^2 := by nlinarith
  have hsr := Real.sqrt_pos.mpr hs
  have hrr := Real.sqrt_pos.mpr hr
  have hwpos : 0<w := by rw [hw]; positivity
  have hsqr := Real.sq_sqrt hr.le
  have hsqs := Real.sq_sqrt hs.le
  have hp := Real.pi_pos
  have hconst : (Real.sqrt (1-r^2))⁻¹*(Real.sqrt (2*Real.pi))⁻¹ =
      (Real.sqrt r)⁻¹*(Real.sqrt (2*Real.pi*w))⁻¹ := by
    rw [← mul_inv,← mul_inv]
    congr 1
    rw [← Real.sqrt_mul hs.le,← Real.sqrt_mul hr.le]
    congr 1
    rw [hw]
    field_simp
  have hexp : -(((y-r*x)/Real.sqrt (1-r^2))^2)/2 ≤
      -((y-x)^2)/(2*w)+(x^2-y^2)/4 := by
    rw [div_pow,hsqs,hw]
    have he : -((y-r*x)^2/(1-r^2))/2 + ((y-x)^2)/(2*((1-r^2)/r))-(x^2-y^2)/4 =
        -((1-r)^2*(x^2+y^2))/(4*(1-r^2)) := by field_simp; ring
    have hn : 0 ≤ ((1-r)^2*(x^2+y^2))/(4*(1-r^2)) := by positivity
    simp only [neg_div] at he ⊢
    linarith
  unfold gaussianPDFReal
  simp only [sub_zero, NNReal.coe_one, mul_one]
  change (Real.sqrt (1-r^2))⁻¹*((Real.sqrt (2*Real.pi))⁻¹ *
      Real.exp (-((y-r*x)/Real.sqrt (1-r^2))^2/2)) ≤
    (Real.sqrt r)⁻¹*((Real.sqrt (2*Real.pi*w))⁻¹*Real.exp (-(y-x)^2/(2*w)))*
      Real.exp ((x^2-y^2)/4)
  calc
    _ = ((Real.sqrt (1-r^2))⁻¹*(Real.sqrt (2*Real.pi))⁻¹)*
      Real.exp (-((y-r*x)/Real.sqrt (1-r^2))^2/2) := by ring
    _ ≤ ((Real.sqrt (1-r^2))⁻¹*(Real.sqrt (2*Real.pi))⁻¹)*
      Real.exp (-(y-x)^2/(2*w)+(x^2-y^2)/4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = _ := by rw [hconst,Real.exp_add]; ring

end GaussianAR

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.GaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal Gaussian kernels and their densities. -/

section

open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal
namespace GaussianKernel

variable {ι : Type*} [Fintype ι]

lemma pi_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    (Measure.pi fun i => gaussianReal 0 (v i)) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 (v i) (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal
      ((show Integrable (fun x : ι → ℝ => ∏ i, gaussianPDFReal 0 (v i) (x i)) volume from
        by simpa only [volume_pi] using Integrable.fintype_prod (fun i => integrable_gaussianPDFReal 0 (v i))).restrict)
      (ae_of_all _ fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 (v i) (x i))),
    volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (gaussianPDFReal_nonneg 0 (v i)))]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply_eq_integral 0 (hv i) (s i)).symm

lemma diagonalLaw_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    diagonalLaw v = volume.withDensity (fun x => ENNReal.ofReal (density v x)) := by
  apply Measure.ext
  intro s hs
  rw [diagonalLaw, Measure.map_apply (PiLp.volume_preserving_toLp ι).measurable hs,
    pi_density v hv, withDensity_apply _ (hs.preimage (PiLp.volume_preserving_toLp ι).measurable),
    withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage (PiLp.volume_preserving_toLp ι).measurable),
    ← lintegral_indicator hs]
  have he (x : ι → ℝ) :
      ((toLp 2) ⁻¹' s).indicator (fun x : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 (v i) (x i))) x =
      s.indicator (fun x => ENNReal.ofReal (density v x)) (toLp 2 x) := by
    by_cases hx : toLp 2 x ∈ s <;> simp [hx, density]
  simp_rw [he]
  exact (PiLp.volume_preserving_toLp ι).lintegral_comp
    ((density_continuous v).measurable.ennreal_ofReal.indicator hs)

lemma density_pos (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) (x : EuclideanSpace ℝ ι) :
    0 < density v x := by
  exact Finset.prod_pos fun i _ => gaussianPDFReal_pos 0 (v i) (x i) (hv i)

section Scale
variable [DecidableEq ι]

lemma scaleMap_apply (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) (i : ι) :
    scaleMap v x i = Real.sqrt (v i : ℝ) * x i := by
  change (Matrix.diagonal (fun i => Real.sqrt (v i : ℝ))).mulVec x.ofLp i = _
  simp only [Matrix.mulVec_diagonal]

lemma stdGaussian_map_scale (v : ι → ℝ≥0) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (scaleMap v) = diagonalLaw v := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (scaleMap v).measurable
    (PiLp.volume_preserving_toLp ι).measurable]
  have he : (scaleMap v) ∘ (toLp 2) =
      (toLp 2) ∘ (fun x : ι → ℝ => fun i => Real.sqrt (v i : ℝ)*x i) := by
    ext x i
    exact scaleMap_apply v (toLp 2 x) i
  rw [he, ← Measure.map_map (PiLp.volume_preserving_toLp ι).measurable (by fun_prop),
    Measure.pi_map_pi (f := fun i (x : ℝ) => Real.sqrt (v i : ℝ)*x)
      (fun i => (measurable_const.mul measurable_id).aemeasurable)]
  congr 1
  apply congrArg Measure.pi
  funext i
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt (v i).coe_nonneg]

end Scale

end GaussianKernel
open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal
namespace GaussianKernel
variable {ι : Type*} [Fintype ι]

lemma density_exp (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) :
    density v x = density v 0 * Real.exp (-(∑ i, (x i)^2 / (2*(v i : ℝ)))) := by
  simp only [density, gaussianPDFReal, sub_zero, PiLp.zero_apply, neg_zero,
    zero_pow (by decide : 2 ≠ 0), zero_div, Real.exp_zero, mul_one,
    Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.sum_neg_distrib, neg_div]

end GaussianKernel

end

section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace GaussianKernel
variable {ι : Type*} [Fintype ι]

lemma density_integrable (v : ι → ℝ≥0) : Integrable (density v) := by
  apply ((PiLp.volume_preserving_toLp ι).integrable_comp
    (density_continuous v).aestronglyMeasurable).mp
  change Integrable (fun x : ι → ℝ => ∏ i,gaussianPDFReal 0 (v i) (x i))
  simpa only [volume_pi] using Integrable.fintype_prod (fun i => integrable_gaussianPDFReal 0 (v i))

lemma stdGaussian_eq_density : stdGaussian (EuclideanSpace ℝ ι) =
    volume.withDensity (fun x => ENNReal.ofReal (density (fun _ : ι => 1) x)) := by
  rw [← diagonalLaw_density (fun _ : ι => 1) (fun _ => by simp)]
  exact map_pi_eq_stdGaussian.symm

lemma linear_image_density (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    {S : Set (EuclideanSpace ℝ ι)} (hS : MeasurableSet S) :
    (stdGaussian (EuclideanSpace ℝ ι)).map e S =
      ENNReal.ofReal (∫ x in S, |e.symm.toContinuousLinearMap.det| *
        density (fun _ => 1) (e.symm x)) := by
  rw [stdGaussian_eq_density]
  exact e.symm.toHomeomorph.toMeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_det_fderiv_mul
    volume hS (ae_of_all _ fun _ _ => density_nonneg _ _) (density_integrable _).integrableOn
    (fun x _ => e.symm.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)

end GaussianKernel

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.HeatL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Heat operators, weak coordinate derivatives, and Dirichlet energy. -/

section

open MeasureTheory FourierTransform Filter ComplexConjugate
open scoped Topology ComplexInnerProductSpace

namespace HeatL2

section Multiplier
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma inner_mulOp (m : X → ℂ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f g : Lp ℂ 2 μ) :
    ⟪f, mulOp m hm hb g⟫ = ∫ x, m x * (g x * conj (f x)) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mulOp_coe m hm hb g] with x hx
  rw [hx]
  simp only [RCLike.inner_apply]
  ring

end Multiplier
end HeatL2

namespace HeatL2
section Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_weight (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    {C : ℝ} (hb : ∀ᵐ x ∂volume, |m x| ≤ C) (f : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun x => m x * ‖f x‖^2) := by
  apply Integrable.mono' (((Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul C)
    (hm.mul ((Lp.aestronglyMeasurable f).norm.pow 2))
  filter_upwards [hb] with x hx
  simpa only [Pi.mul_apply, Pi.pow_apply, Real.norm_eq_abs, abs_mul, abs_pow, abs_norm] using
    mul_le_mul_of_nonneg_right hx (sq_nonneg ‖f x‖)

lemma spectralOp_fourier (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    (hb : ∀ x, |m x| ≤ 1) (f : Lp ℂ 2 (volume : Measure E)) :
    (fun x => (𝓕 (spectralOp m hm hb f) : Lp ℂ 2 (volume : Measure E)) x) =ᵐ[volume] fun x => (m x : ℂ) * (𝓕 f) x := by
  change ((Lp.fourierTransformₗᵢ E ℂ) ((Lp.fourierTransformₗᵢ E ℂ).symm _) : E → ℂ) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact mulOp_coe (fun x => (m x : ℂ))
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hm) (C := 1)
    (Filter.Eventually.of_forall fun x => by simpa using hb x) (𝓕 f)

lemma spectralOp_inner (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    (hb : ∀ x, |m x| ≤ 1) (f : Lp ℂ 2 (volume : Measure E)) :
    ⟪f, spectralOp m hm hb f⟫ = ((∫ x, m x * ‖(𝓕 f) x‖^2 : ℝ) : ℂ) := by
  rw [← Lp.inner_fourier_eq, L2.inner_def]
  have he : (fun x => inner ℂ ((𝓕 f) x) ((𝓕 (spectralOp m hm hb f)) x)) =ᵐ[volume]
      fun x => ((m x * ‖(𝓕 f) x‖^2 : ℝ) : ℂ) := by
    filter_upwards [spectralOp_fourier m hm hb f] with x hx
    rw [hx]
    simp only [RCLike.inner_apply]
    rw [mul_assoc, RCLike.mul_conj]
    simp
  rw [integral_congr_ae he, integral_complex_ofReal]

lemma spectralOp_positive (m : E → ℝ) (hm : AEStronglyMeasurable m volume)
    (hb : ∀ x, |m x| ≤ 1) (hn : ∀ x, 0 ≤ m x) :
    (spectralOp m hm hb).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro f
  have he : ⟪spectralOp m hm hb f, f⟫ = ((∫ x, m x * ‖(𝓕 f) x‖^2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm, spectralOp_inner]
    simp
  rw [he]
  exact ⟨rfl, integral_nonneg fun x => mul_nonneg (hn x) (sq_nonneg _)⟩

lemma heat_inner (w : E → ℝ) (hw : AEStronglyMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure E)) :
    (⟪f, heat w hw hn f⟫).re = ‖f‖^2 - energy w f := by
  rw [heat, spectralOp_inner]
  simp only [Complex.ofReal_re]
  have hb : ∀ x, |1-Real.exp (-w x)| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hn x))))]
    linarith [Real.exp_pos (-w x)]
  have hint : Integrable (fun x => (1-Real.exp (-w x)) * ‖(𝓕 f) x‖^2) :=
    integrable_weight (fun x => 1-Real.exp (-w x))
      (aestronglyMeasurable_const.sub (Real.continuous_exp.comp_aestronglyMeasurable hw.neg))
      (Filter.Eventually.of_forall hb) (𝓕 f)
  rw [energy, ← Lp.norm_fourier_eq f, norm_sq_integral,
    ← integral_sub ((Lp.memLp (𝓕 f)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
      hint]
  congr 1
  ext x
  ring

lemma energy_nonneg (w : E → ℝ) (hn : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure E)) :
    0 ≤ energy w f := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hn x)))) (sq_nonneg _)

end Spectral
end HeatL2
namespace HeatL2

lemma loss_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ loss x := by
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx))

lemma loss_le_one (x : ℝ) : loss x ≤ 1 := by
  unfold loss
  linarith [Real.exp_pos (-x)]

end HeatL2

namespace HeatL2
section Mask
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma mask_coe (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    (mask D hD f : X → ℂ) =ᵐ[μ] D.indicator f := by
  filter_upwards [mulOp_coe (D.indicator (fun _ => (1 : ℂ)))
    (aestronglyMeasurable_const.indicator hD)
    (Filter.Eventually.of_forall (indicator_one_norm_le D)) f] with x hx
  change mulOp _ _ _ f x = _
  rw [hx]
  classical
  by_cases hx : x ∈ D <;> simp [hx]

lemma mask_norm_le (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    ‖mask D hD f‖ ≤ ‖f‖ := by
  apply le_trans (mulLp_norm_le (D.indicator (fun _ => (1 : ℂ)))
    (aestronglyMeasurable_const.indicator hD)
    (Filter.Eventually.of_forall (indicator_one_norm_le D)) f)
  simp only [one_mul, le_refl]

lemma mask_idempotent (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    mask D hD (mask D hD f) = mask D hD f := by
  apply Lp.ext
  filter_upwards [mask_coe D hD (mask D hD f), mask_coe D hD f] with x h₁ h₂
  classical
  by_cases hx : x ∈ D <;> simp_all

lemma mask_inner (D : Set X) (hD : MeasurableSet D) (f g : Lp ℂ 2 μ) :
    ⟪mask D hD f, g⟫ = ⟪f, mask D hD g⟫ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mask_coe D hD f, mask_coe D hD g] with x h₁ h₂
  classical
  by_cases hx : x ∈ D <;> simp [h₁, h₂, hx]

lemma mask_adjoint (D : Set X) (hD : MeasurableSet D) :
    (mask (μ := μ) D hD).adjoint = mask D hD := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (mask_inner D hD f g).symm

lemma mask_eq_self_iff (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    mask D hD f = f ↔ f ∈ supported D := by
  classical
  constructor
  · intro h
    have hc := mask_coe D hD f
    rw [h] at hc
    filter_upwards [hc] with x hx hnot
    simpa [hnot] using hx
  · intro h
    apply Lp.ext
    filter_upwards [mask_coe D hD f, h] with x hx hs
    by_cases hmem : x ∈ D <;> simp [hx, hmem, hs]

end Mask

section PositiveNorm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma positive_norm_le_iff (T : H →L[ℂ] H) (hT : T.IsPositive) {C : ℝ} (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ ∀ f, (⟪f, T f⟫).re ≤ C * ‖f‖^2 := by
  constructor
  · intro h f
    have he := (Complex.re_le_norm ⟪f, T f⟫).trans (norm_inner_le_norm f (T f))
    have hn := T.le_opNorm f
    have hm := mul_le_mul_of_nonneg_left (hn.trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg f))) (norm_nonneg f)
    nlinarith
  · intro h
    rw [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric]
    apply ciSup_le
    intro f
    have hre : (⟪T f, f⟫).re = (⟪f, T f⟫).re := inner_re_symm (𝕜 := ℂ) (T f) f
    change |(⟪T f, f⟫).re / ‖f‖^2| ≤ C
    have hnon : 0 ≤ (⟪T f, f⟫).re := hT.re_inner_nonneg_left f
    rw [abs_of_nonneg (div_nonneg hnon (sq_nonneg _)), hre]
    by_cases hf : f = 0
    · simpa [hf] using hC
    · exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hf))).mpr (h f)

lemma positive_exists_form_gt (T : H →L[ℂ] H) (hT : T.IsPositive) {C : ℝ}
    (hC : 0 ≤ C) (h : C < ‖T‖) : ∃ f, C * ‖f‖^2 < (⟪f, T f⟫).re := by
  by_contra hn
  push Not at hn
  exact (not_le_of_gt h) ((positive_norm_le_iff T hT hC).mpr hn)

end PositiveNorm

section Compressed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma heat_positive (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    (heat w hw hn).IsPositive := spectralOp_positive _ _ _ (fun _ => (Real.exp_pos _).le)

lemma compressedHeat_positive (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x) :
    (compressedHeat D hD w hw hn).IsPositive := by
  have hp := (heat_positive w hw hn).adjoint_conj (mask D hD)
  rwa [mask_adjoint] at hp

lemma compressedHeat_inner (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    (f : Lp ℂ 2 (volume : Measure E)) :
    (⟪f, compressedHeat D hD w hw hn f⟫).re =
      ‖mask D hD f‖^2 - energy w (mask D hD f) := by
  change (⟪f, mask D hD (heat w hw hn (mask D hD f))⟫).re = _
  rw [← mask_inner, heat_inner]

end Compressed
end HeatL2

namespace HeatL2
section Average
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma average_apply (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν]
    (f : Lp ℂ 2 (volume : Measure E)) : average A ν f = ∫ z, translate (A z) f ∂ν := rfl

lemma inner_average (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν]
    (f g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, average A ν f⟫ = ∫ ξ, (∫ z, phase (A z) ξ ∂ν) * ((𝓕 f) ξ * conj ((𝓕 g) ξ)) := by
  rw [average_apply, ← integral_inner (integrable_translate A ν f)]
  have hp : Integrable (fun ξ => (𝓕 f) ξ * conj ((𝓕 g) ξ)) (volume : Measure E) := by
    simpa only [RCLike.inner_apply] using L2.integrable_inner (𝕜 := ℂ) (𝓕 g) (𝓕 f)
  have hm : Continuous (fun p : F × E => phase (A p.1) p.2) :=
    (continuous_subtype_val.comp Real.continuous_fourierChar).comp
      ((A.continuous.comp continuous_fst).inner continuous_snd)
  have hi : Integrable (fun p : F × E => phase (A p.1) p.2 *
      ((𝓕 f) p.2 * conj ((𝓕 g) p.2))) (ν.prod volume) := by
    apply Integrable.mono' (hp.norm.comp_snd ν) (hm.aestronglyMeasurable.mul hp.aestronglyMeasurable.comp_snd)
    exact Filter.Eventually.of_forall fun p => by simp only [Pi.mul_apply, norm_mul, phase_norm, one_mul, le_refl]
  have hinner (z : F) : ⟪g, translate (A z) f⟫ =
      ∫ ξ, phase (A z) ξ * ((𝓕 f) ξ * conj ((𝓕 g) ξ)) := by
    rw [← Lp.inner_fourier_eq, fourier_translate]
    exact inner_mulOp _ _ _ _ _
  simp_rw [hinner]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => integral_mul_const _ _

omit [MeasurableSpace E] [BorelSpace E] in
lemma integral_phase_gaussian (A : F →L[ℝ] E) (ξ : E) :
    (∫ z, phase (A z) ξ ∂ProbabilityTheory.stdGaussian F) =
      (Real.exp (-gaussianSymbol A ξ) : ℂ) := by
  have he := ProbabilityTheory.charFun_stdGaussian ((2*Real.pi) • A.adjoint ξ)
  rw [charFun_apply] at he
  have hf : (fun z => phase (A z) ξ) = fun z =>
      Complex.exp ((inner ℝ z ((2*Real.pi) • A.adjoint ξ) : ℂ) * Complex.I) := by
    ext z
    rw [phase, Real.fourierChar_apply, inner_smul_right, A.adjoint_inner_right]
  rw [hf, he, gaussianSymbol, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma average_gaussian_eq_heat (A : F →L[ℝ] E) :
    average A (ProbabilityTheory.stdGaussian F) =
      heat (gaussianSymbol A) (gaussianSymbol_continuous A).aestronglyMeasurable
        (gaussianSymbol_nonneg A) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [inner_average]
  simp_rw [integral_phase_gaussian]
  rw [← Lp.inner_fourier_eq, L2.inner_def]
  apply integral_congr_ae
  have hb : ∀ ξ, |Real.exp (-gaussianSymbol A ξ)| ≤ 1 := by
    intro ξ
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (gaussianSymbol_nonneg A ξ))
  filter_upwards [spectralOp_fourier (fun ξ => Real.exp (-gaussianSymbol A ξ))
    (Real.continuous_exp.comp_aestronglyMeasurable (gaussianSymbol_continuous A).aestronglyMeasurable.neg)
    hb f] with ξ hξ
  change _ = inner ℂ ((𝓕 g) ξ) ((𝓕 (heat _ _ _ f)) ξ)
  rw [heat, hξ]
  simp only [RCLike.inner_apply]
  ring

end Average
end HeatL2

namespace HeatL2
section Energy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integrable_energy (w : E → ℝ) (hw : AEStronglyMeasurable w volume)
    (hn : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun ξ => loss (w ξ) * ‖(𝓕 f) ξ‖^2) := by
  apply integrable_weight (fun ξ => loss (w ξ))
    (aestronglyMeasurable_const.sub (Real.continuous_exp.comp_aestronglyMeasurable hw.neg))
    (C := 1) _ (𝓕 f)
  exact Filter.Eventually.of_forall fun ξ => by
    rw [abs_of_nonneg (loss_nonneg (hn ξ))]
    exact loss_le_one _

end Energy
end HeatL2

open MeasureTheory FourierTransform Filter ComplexConjugate
open scoped Topology ComplexInnerProductSpace

open MeasureTheory FourierTransform Filter ComplexConjugate
open scoped Topology ComplexInnerProductSpace

open MeasureTheory Filter ComplexConjugate
open scoped ComplexInnerProductSpace ENNReal

namespace HeatL2

section Kernel
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable (k : BoundedKernel X)

lemma kernelOp_coe (f : Lp ℂ 2 μ) : (kernelOp k f : X → ℂ) =ᵐ[μ] kernelFun k f := kernelLp_coe k f

lemma inner_one_eq_integral (f : Lp ℂ 2 μ) :
    ⟪(oneLp : Lp ℂ 2 μ), f⟫ = ∫ x, f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [oneLp_coe (μ := μ)] with x hx
  simp only [hx, RCLike.inner_apply, map_one, mul_one]

lemma pathMass_eq_integral (n : ℕ) :
    pathMass (μ := μ) k n = ∫ x, (((kernelOp (μ := μ) k ^ n) (oneLp : Lp ℂ 2 μ)) x).re ∂μ := by
  rw [pathMass, inner_one_eq_integral]
  have hr := integral_re ((Lp.memLp ((kernelOp k ^ n) (oneLp : Lp ℂ 2 μ))).integrable (by norm_num))
  simpa only [RCLike.re_eq_complex_re] using hr.symm

lemma pathMass_le (n : ℕ) :
    pathMass (μ := μ) k n ≤ ‖(oneLp : Lp ℂ 2 μ)‖^2 * ‖(kernelOp (μ := μ) k)‖^n := by
  unfold pathMass
  calc
    _ ≤ ‖⟪(oneLp : Lp ℂ 2 μ), (kernelOp k ^ n) oneLp⟫‖ := Complex.re_le_norm _
    _ ≤ ‖(oneLp : Lp ℂ 2 μ)‖ * ‖(kernelOp k ^ n) oneLp‖ := norm_inner_le_norm _ _
    _ ≤ ‖(oneLp : Lp ℂ 2 μ)‖ * (‖(kernelOp k ^ n : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)‖ * ‖(oneLp : Lp ℂ 2 μ)‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖(oneLp : Lp ℂ 2 μ)‖ * (‖(kernelOp (μ := μ) k)‖^n * ‖(oneLp : Lp ℂ 2 μ)‖) := by
      gcongr
      rcases n with _ | n
      · exact ContinuousLinearMap.norm_id_le
      · exact norm_pow_le' _ (Nat.succ_pos _)
    _ = _ := by ring

lemma inner_kernel (f g : Lp ℂ 2 μ) :
    ⟪f, kernelOp k g⟫ = ∫ x, ∫ y, (k.value (x,y) : ℂ) * g y * conj (f x) ∂μ ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [kernelOp_coe k g] with x hx
  simp only [RCLike.inner_apply, hx, kernelFun, integral_mul_const]

end Kernel
end HeatL2

open MeasureTheory Filter
open scoped ENNReal ComplexInnerProductSpace

namespace HeatL2

lemma le_of_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ n : ℕ, a^n ≤ C*b^n) : a ≤ b := by
  by_contra hn
  have hab : b < a := lt_of_not_ge hn
  have ha' : 0 < a := hb.trans_lt hab
  have hr : b/a < 1 := (div_lt_one ha').mpr hab
  have ht : Tendsto (fun n : ℕ => C*(b/a)^n) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hb ha) hr)
  have hh (n : ℕ) : 1 ≤ C*(b/a)^n := by
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos ha' n)]
    simpa only [one_mul] using h n
  have := ge_of_tendsto' ht hh
  linarith

section Kernel
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable (k : BoundedKernel X)

lemma norm_lower_of_pathMass_lower {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (h : ∀ n : ℕ, c*a^n ≤ pathMass (μ := μ) k n) : a ≤ ‖kernelOp (μ := μ) k‖ := by
  apply le_of_pow_le_const_mul_pow ha (norm_nonneg _) (C := ‖(oneLp : Lp ℂ 2 μ)‖^2/c)
  intro n
  have hn := (h n).trans (pathMass_le k n)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm c] using hn

end Kernel
end HeatL2

open MeasureTheory Filter
open scoped ComplexInnerProductSpace ENNReal
namespace HeatL2
section Restrict
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (D : Set X) (hD : MeasurableSet D)
lemma extendLp_coe (f : Lp ℂ 2 (μ.restrict D)) :
    (extendLp D hD f : X → ℂ) =ᵐ[μ] D.indicator f := MemLp.coeFn_toLp _
lemma extendLp_norm (f : Lp ℂ 2 (μ.restrict D)) : ‖extendLp D hD f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (extendLp_coe D hD f), eLpNorm_indicator_eq_eLpNorm_restrict hD]
lemma extendLp_supported (f : Lp ℂ 2 (μ.restrict D)) : extendLp D hD f ∈ supported D := by
  filter_upwards [extendLp_coe D hD f] with x hx hnot
  simp [hx, hnot]
lemma restrictLp_coe (f : Lp ℂ 2 μ) :
    (restrictLp D f : X → ℂ) =ᵐ[μ.restrict D] f := MemLp.coeFn_toLp _
lemma extend_restrict (f : Lp ℂ 2 μ) : extendLp D hD (restrictLp D f) = mask D hD f := by
  apply Lp.ext
  have hr := (ae_restrict_iff' hD).mp (restrictLp_coe D f)
  filter_upwards [extendLp_coe D hD (restrictLp D f), mask_coe D hD f, hr] with x h₁ h₂ h₃
  rw [h₁,h₂]
  by_cases hx : x ∈ D
  · simpa only [Set.indicator_of_mem hx] using h₃ hx
  · simp [hx]
end Restrict
end HeatL2

open MeasureTheory FourierTransform Filter Set
open scoped ComplexInnerProductSpace

open MeasureTheory ComplexConjugate
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2

section Spatial
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma inner_translate_integral (a : E) (f g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, translate a f⟫ = ∫ x, f (x+a) * conj (g x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [translate_coe a f] with x hx
  simp only [RCLike.inner_apply, hx]

omit [FiniteDimensional ℝ F] in
lemma integrable_translate_pair (A : F →L[ℝ] E) (ν : Measure F) [IsFiniteMeasure ν]
    (f g : Lp ℂ 2 (volume : Measure E)) :
    Integrable (fun p : F × E => f (p.2+A p.1) * conj (g p.2)) (ν.prod volume) := by
  have hm : StronglyMeasurable (fun p : F × E => f (p.2+A p.1) * conj (g p.2)) := by
    exact ((Lp.stronglyMeasurable f).comp_measurable (by fun_prop)).mul
      (continuous_star.comp_stronglyMeasurable ((Lp.stronglyMeasurable g).comp_measurable measurable_snd))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro z
    apply (L2.integrable_inner (𝕜 := ℂ) g (translate (A z) f)).congr
    filter_upwards [translate_coe (A z) f] with x hx
    simp only [RCLike.inner_apply, hx]
  · apply Integrable.mono' (integrable_const (‖f‖^2+‖g‖^2)) hm.norm.aestronglyMeasurable.integral_prod_right'
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hfi : Integrable (fun x => ‖f (x+A z)‖^2) volume := (measurePreserving_add_right volume (A z)).integrable_comp_of_integrable
      ((Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    have hgi := (Lp.memLp g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
    calc
      _ ≤ ∫ x, ‖f (x+A z)‖^2+‖g x‖^2 := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (hfi.add hgi)
        apply Filter.Eventually.of_forall
        intro x
        change ‖f (x+A z)*conj (g x)‖ ≤ ‖f (x+A z)‖^2+‖g x‖^2
        simp only [norm_mul, Complex.norm_conj]
        nlinarith [sq_nonneg (‖f (x+A z)‖-‖g x‖)]
      _ = _ := by
        rw [integral_add hfi hgi, integral_add_right_eq_self (fun x => ‖f x‖^2) (A z),
          ← norm_sq_integral, ← norm_sq_integral]

lemma inner_average_spatial (A : F →L[ℝ] E) (ν : Measure F) [IsProbabilityMeasure ν]
    (f g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, average A ν f⟫ = ∫ x, ∫ z, f (x+A z)*conj (g x) ∂ν := by
  rw [average_apply, ← integral_inner (integrable_translate A ν f)]
  simp_rw [inner_translate_integral]
  exact integral_integral_swap (integrable_translate_pair A ν f g)

end Spatial
section Density
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma inner_average_density (ν : Measure E) [IsProbabilityMeasure ν]
    (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (f g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, average (ContinuousLinearMap.id ℝ E) ν f⟫ =
      ∫ x, ∫ y, (p (y-x) : ℂ) * f y * conj (g x) := by
  rw [inner_average_spatial]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [hν, integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hpn _), ContinuousLinearMap.id_apply,
    Complex.real_smul, mul_assoc]
  have he (z : E) : (p z : ℂ)*(f (x+z)*conj (g x)) =
      (p ((z+x)-x) : ℂ)*(f (z+x)*conj (g x)) := by simp [add_comm]
  simp_rw [he]
  exact integral_add_right_eq_self (μ := (volume : Measure E))
    (fun y => (p (y-x) : ℂ)*(f y*conj (g x))) x

variable (D : Set E) (hD : MeasurableSet D)

lemma integral_extend_mul (f : Lp ℂ 2 (volume.restrict D)) (a : E → ℂ) :
    (∫ x, a x * (extendLp D hD f) x) = ∫ x in D, a x * f x := by
  calc
    _ = ∫ x, D.indicator (fun y => a y*f y) x := by
      apply integral_congr_ae
      filter_upwards [extendLp_coe D hD f] with x hx
      rw [hx]
      by_cases hxD : x ∈ D <;> simp [hxD]
    _ = _ := integral_indicator hD

lemma integral_extend_conj (f : Lp ℂ 2 (volume.restrict D)) (a : E → ℂ) :
    (∫ x, a x * conj ((extendLp D hD f) x)) = ∫ x in D, a x * conj (f x) := by
  calc
    _ = ∫ x, D.indicator (fun y => a y*conj (f y)) x := by
      apply integral_congr_ae
      filter_upwards [extendLp_coe D hD f] with x hx
      rw [hx]
      by_cases hxD : x ∈ D <;> simp [hxD]
    _ = _ := integral_indicator hD

lemma inner_extend (f : Lp ℂ 2 (volume.restrict D)) (g : Lp ℂ 2 (volume : Measure E)) :
    ⟪g, extendLp D hD f⟫ = ⟪restrictLp D g, f⟫ := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x in D, conj (g x)*f x := by
      simpa only [RCLike.inner_apply, mul_comm] using integral_extend_mul D hD f (fun x => conj (g x))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [restrictLp_coe D g] with x hx
      simp only [RCLike.inner_apply, hx, mul_comm]

lemma densityKernel_inner (ν : Measure E) [IsProbabilityMeasure ν]
    (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ p 0)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    [IsFiniteMeasure (volume.restrict D)] (f g : Lp ℂ 2 (volume.restrict D)) :
    ⟪extendLp D hD g, average (ContinuousLinearMap.id ℝ E) ν (extendLp D hD f)⟫ =
      ⟪g, kernelOp (densityKernel p hp hpn hpb) f⟫ := by
  rw [inner_average_density ν p hp hpn hν, inner_kernel]
  simp only [densityKernel]
  calc
    _ = ∫ x, (∫ y in D, (p (y-x) : ℂ)*f y)*conj ((extendLp D hD g) x) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      rw [integral_mul_const, integral_extend_mul D hD f]
    _ = ∫ x in D, (∫ y in D, (p (y-x) : ℂ)*f y)*conj (g x) :=
      integral_extend_conj D hD g _
    _ = _ := by simp only [integral_mul_const]

lemma extend_kernel_eq (ν : Measure E) [IsProbabilityMeasure ν]
    (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ p 0)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    [IsFiniteMeasure (volume.restrict D)] (f : Lp ℂ 2 (volume.restrict D)) :
    extendLp D hD (kernelOp (densityKernel p hp hpn hpb) f) =
      mask D hD (average (ContinuousLinearMap.id ℝ E) ν (extendLp D hD f)) := by
  apply ext_inner_left ℂ
  intro g
  rw [inner_extend, ← mask_inner, ← extend_restrict,
    densityKernel_inner D hD ν p hp hpn hpb hν]

include hD in
lemma restrictLp_norm_le (f : Lp ℂ 2 (volume : Measure E)) : ‖restrictLp D f‖ ≤ ‖f‖ := by
  rw [← extendLp_norm D hD (restrictLp D f), extend_restrict]
  exact mask_norm_le D hD f

lemma compressedAverage_kernel_norm (ν : Measure E) [IsProbabilityMeasure ν]
    (p : E → ℝ) (hp : Measurable p) (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ p 0)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    [IsFiniteMeasure (volume.restrict D)] :
    ‖mask D hD ∘L average (ContinuousLinearMap.id ℝ E) ν ∘L mask D hD‖ =
      ‖kernelOp (μ := volume.restrict D) (densityKernel p hp hpn hpb)‖ := by
  let T := mask D hD ∘L average (ContinuousLinearMap.id ℝ E) ν ∘L mask D hD
  let K := kernelOp (μ := volume.restrict D) (densityKernel p hp hpn hpb)
  change ‖T‖ = ‖K‖
  have he f : T f = extendLp D hD (K (restrictLp D f)) := by
    rw [extend_kernel_eq D hD ν p hp hpn hpb hν, extend_restrict]
    rfl
  have he' f : extendLp D hD (K f) = T (extendLp D hD f) := by
    rw [extend_kernel_eq D hD ν p hp hpn hpb hν]
    change _ = mask D hD (average _ ν (mask D hD (extendLp D hD f)))
    rw [(mask_eq_self_iff D hD _).mpr (extendLp_supported D hD f)]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    rw [he, extendLp_norm]
    exact (K.le_opNorm _).trans (mul_le_mul_of_nonneg_left (restrictLp_norm_le D hD f) (norm_nonneg _))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    rw [← extendLp_norm D hD (K f), he']
    simpa only [extendLp_norm] using T.le_opNorm (extendLp D hD f)

end Density
end HeatL2

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.PathLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian heat kernels and autoregressive path laws. -/

section

open MeasureTheory ProbabilityTheory WithLp
open scoped NNReal ENNReal RealInnerProductSpace
namespace GaussianKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma scaleMap_selfAdjoint (v : ι → ℝ≥0) : IsSelfAdjoint (scaleMap v) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  change y i * (scaleMap v x) i = (scaleMap v y) i * x i
  rw [scaleMap_apply, scaleMap_apply]
  ring

lemma symbol_eq (v : ι → ℝ≥0) : HeatL2.gaussianSymbol (scaleMap v) = symbol v := by
  ext ξ
  rw [HeatL2.gaussianSymbol, (scaleMap_selfAdjoint v).adjoint_eq,
    EuclideanSpace.real_norm_sq_eq]
  unfold symbol
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [PiLp.smul_apply, smul_eq_mul, scaleMap_apply, mul_pow,
    Real.sq_sqrt (v i).coe_nonneg]
  ring

lemma average_diagonal_eq (v : ι → ℝ≥0) :
    HeatL2.average (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) (diagonalLaw v) =
      HeatL2.average (scaleMap v) (stdGaussian (EuclideanSpace ℝ ι)) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [HeatL2.average_apply, HeatL2.average_apply, ← stdGaussian_map_scale v]
  change (∫ z, HeatL2.translate z f ∂(stdGaussian (EuclideanSpace ℝ ι)).map (scaleMap v)) = _
  exact integral_map (scaleMap v).measurable.aemeasurable
    (HeatL2.translate_continuous f).aestronglyMeasurable

lemma average_diagonal_heat (v : ι → ℝ≥0) :
    HeatL2.average (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) (diagonalLaw v) =
      HeatL2.heat (symbol v) (symbol_continuous v).aestronglyMeasurable (symbol_nonneg v) := by
  rw [average_diagonal_eq, HeatL2.average_gaussian_eq_heat]
  congr 1
  exact symbol_eq v

lemma kernel_norm_eq (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (D : Set (EuclideanSpace ℝ ι)) (hD : MeasurableSet D) [IsFiniteMeasure (volume.restrict D)] :
    ‖HeatL2.kernelOp (μ := volume.restrict D) (kernel v)‖ =
      ‖HeatL2.compressedHeat D hD (symbol v) (symbol_continuous v).aestronglyMeasurable (symbol_nonneg v)‖ := by
  unfold kernel
  rw [← HeatL2.compressedAverage_kernel_norm D hD (diagonalLaw v) (density v)
    (density_continuous v).measurable (density_nonneg v) (density_le_zero v)
    (diagonalLaw_density v hv), average_diagonal_heat]
  rfl

end GaussianKernel

open MeasureTheory ProbabilityTheory Set WithLp
open scoped NNReal ENNReal

end

section

open MeasureTheory Set Filter
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2

lemma integral_pi_fin_cons {X G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (μ : Measure X) [SigmaFinite μ]
    {n : ℕ} {f : (Fin (n+1) → X) → G} (hf : Integrable f (Measure.pi fun _ => μ)) :
    (∫ p, f p ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ x, ∫ p, f (Fin.cons x p) ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) 0
  have he : ∀ z : X × (Fin n → X), e.symm z = Fin.cons z.1 z.2 := by
    intro z
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e]
    · simp [e]
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  have hi : Integrable (fun z : X × (Fin n → X) => f (e.symm z)) (μ.prod (Measure.pi fun _ => μ)) :=
    hp.integrable_comp_of_integrable hf
  rw [← hp.integral_comp e.symm.measurableEmbedding f]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => integral_congr_ae
    (Filter.Eventually.of_forall fun p => congrArg f (he (x,p)))

section Chain
variable {X : Type*} [MeasurableSpace X] (k : BoundedKernel X)

lemma tailWeight_measurable (n : ℕ) : Measurable (fun z : X × (Fin n → X) => tailWeight k n z.1 z.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n hn =>
    exact (k.measurable.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).mul
      (hn.comp (((measurable_pi_apply 0).comp measurable_snd).prodMk
        (Measurable.of_eval fun (i : Fin n) => (measurable_pi_apply i.succ).comp measurable_snd)))

lemma tailWeight_nonneg (n : ℕ) (x : X) (p : Fin n → X) : 0 ≤ tailWeight k n x p := by
  induction n generalizing x with
  | zero => exact zero_le_one
  | succ n hn => exact mul_nonneg (k.nonneg _) (hn _ _)

lemma tailWeight_le (n : ℕ) (x : X) (p : Fin n → X) : tailWeight k n x p ≤ k.bound^n := by
  induction n generalizing x with
  | zero => exact le_rfl
  | succ n hn =>
    rw [tailWeight, pow_succ']
    exact mul_le_mul (k.le_bound _) (hn _ _) (tailWeight_nonneg k n _ _) k.bound_nonneg

lemma tailWeight_integrable {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) (x : X) :
    Integrable (tailWeight k n x) (Measure.pi fun _ : Fin n => μ) := by
  apply Integrable.mono' (integrable_const (k.bound^n))
    ((tailWeight_measurable k n).comp measurable_prodMk_left).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    change ‖tailWeight k n x p‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (tailWeight_nonneg k n x p)]
    exact tailWeight_le k n x p

lemma walk_zero (μ : Measure X) (x : X) : walk k μ 0 x = 1 := by
  simp [walk,tailWeight, Measure.real]

lemma walk_succ {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) (x : X) :
    walk k μ (n+1) x = ∫ y, k.value (x,y) * walk k μ n y ∂μ := by
  rw [walk, integral_pi_fin_cons μ (tailWeight_integrable k (n+1) x)]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun y => ?_
  simp only [tailWeight, Fin.cons_zero, Fin.cons_succ]
  rw [integral_const_mul]
  rfl

lemma kernel_pow_one_coe {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) :
    ((kernelOp (μ := μ) k ^ n) (oneLp : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x => (walk k μ n x : ℂ) := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self, walk_zero, Complex.ofReal_one] using oneLp_coe (μ := μ)
  | succ n hn =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [kernelOp_coe k ((kernelOp k ^ n) oneLp)] with x hx
    rw [hx, kernelFun, walk_succ]
    calc
      _ = ∫ y, ((k.value (x,y) * walk k μ n y : ℝ) : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hn] with y hy
        rw [hy, Complex.ofReal_mul]
      _ = _ := integral_complex_ofReal

lemma chainWeight_measurable (n : ℕ) : Measurable (chainWeight k n) := by
  let f : (Fin (n+1) → X) → X × (Fin n → X) := fun p => (p 0, fun i => p i.succ)
  have hf : Measurable f := by
    exact (measurable_pi_apply 0).prodMk
      (Measurable.of_eval fun (i : Fin n) => measurable_pi_apply i.succ)
  exact (tailWeight_measurable k n).comp hf

lemma chainWeight_integrable {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) :
    Integrable (chainWeight k n) (Measure.pi fun _ : Fin (n+1) => μ) := by
  apply Integrable.mono' (integrable_const (k.bound^n)) (chainWeight_measurable k n).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    change ‖tailWeight k n (p 0) (fun i => p i.succ)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (tailWeight_nonneg k n _ _)]
    exact tailWeight_le k n _ _

lemma pathMass_pi {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) :
    pathMass (μ := μ) k n = ∫ p, chainWeight k n p ∂Measure.pi (fun _ : Fin (n+1) => μ) := by
  rw [pathMass_eq_integral, integral_pi_fin_cons μ (chainWeight_integrable k n)]
  apply integral_congr_ae
  filter_upwards [kernel_pow_one_coe k n] with x hx
  rw [hx,Complex.ofReal_re]
  simp only [chainWeight,Fin.cons_zero,Fin.cons_succ]
  rfl

end Chain
end HeatL2

open MeasureTheory Set

end

section

open MeasureTheory
namespace HeatL2
variable {X : Type*} [MeasurableSpace X]

lemma chainWeight_prod (k : BoundedKernel X) (n : ℕ) (p : Fin (n+1) → X) :
    chainWeight k n p = ∏ t : Fin n,k.value (p t.castSucc,p t.succ) := by
  induction n with
  | zero => simp [chainWeight,tailWeight]
  | succ n ih =>
    change k.value (p 0,p (Fin.succ 0))*chainWeight k n (fun t => p t.succ)=_
    rw [ih,Fin.prod_univ_succ]
    congr 1

lemma fin_sum_differences {n : ℕ} (f : Fin (n+1) → ℝ) :
    (∑ t : Fin n,(f t.castSucc-f t.succ))=f 0-f (Fin.last n) := by
  rw [Finset.sum_sub_distrib]
  have ha := Fin.sum_univ_castSucc f
  have hb := Fin.sum_univ_succ f
  linarith

end HeatL2

end

section

open MeasureTheory WithLp Set
namespace GaussianAR

lemma measurePreserving_curry (T I : Type*) [Fintype T] [Fintype I] :
    MeasurePreserving (MeasurableEquiv.curry T I ℝ) := by
  apply MeasurePreserving.symm (MeasurableEquiv.curry T I ℝ).symm
  refine ⟨(MeasurableEquiv.curry T I ℝ).symm.measurable,?_⟩
  rw [volume_pi]
  apply (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (MeasurableEquiv.curry T I ℝ).symm.measurable (MeasurableSet.univ_pi hs)]
  have he : (MeasurableEquiv.curry T I ℝ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun t => Set.univ.pi (fun i => s (t,i))) := by ext x; simp
  rw [he,volume_pi,Measure.pi_pi]
  simp only [Measure.pi_pi,Fintype.prod_prod_type]

lemma unpack_apply {T I : Type*} [Fintype T] [Fintype I]
    (x : EuclideanSpace ℝ (T×I)) (t : T) (i : I) : unpack T I x t i=x (t,i) := rfl

lemma unpack_preserving (T I : Type*) [Fintype T] [Fintype I] :
    MeasurePreserving (unpack T I) := by
  have hp : MeasurePreserving (MeasurableEquiv.piCongrRight
      (fun _ : T => MeasurableEquiv.toLp 2 (I → ℝ))) := by
    refine ⟨(MeasurableEquiv.piCongrRight (fun _ : T => MeasurableEquiv.toLp 2 (I → ℝ))).measurable,?_⟩
    change (volume : Measure (T → I → ℝ)).map (fun x t => toLp 2 (x t)) =
      (volume : Measure (T → EuclideanSpace ℝ I))
    let : SigmaFinite ((volume : Measure (I → ℝ)).map (toLp 2)) := by
      rw [(PiLp.volume_preserving_toLp I).map_eq]
      infer_instance
    rw [volume_pi,Measure.pi_map_pi (fun _ => (PiLp.volume_preserving_toLp I).measurable.aemeasurable)]
    simp only [(PiLp.volume_preserving_toLp I).map_eq,← volume_pi]
  exact hp.comp ((measurePreserving_curry T I).comp (PiLp.volume_preserving_ofLp (T×I)))

end GaussianAR

end

section

open Matrix MeasureTheory ProbabilityTheory WithLp
open scoped RealInnerProductSpace ENNReal NNReal BigOperators
namespace GaussianAR
open GaussianKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma transition_nonneg (r : ι → ℝ) (x y : EuclideanSpace ℝ ι) : 0≤transition r x y := by
  apply Finset.prod_nonneg
  intro i _
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (gaussianPDFReal_nonneg _ _ _)

omit [DecidableEq ι] in
lemma transition_le (r : ι → ℝ) (hr : ∀ i,0<r i) (hr1 : ∀ i,r i<1)
    (w : ι → ℝ≥0) (hw : ∀ i,(w i:ℝ)=(1-(r i)^2)/r i) (x y : EuclideanSpace ℝ ι) :
    transition r x y ≤ (∏ i,(Real.sqrt (r i))⁻¹)*density w (y-x)*
      Real.exp ((‖x‖^2-‖y‖^2)/4) := by
  calc
    _ ≤ ∏ i, (Real.sqrt (r i))⁻¹ * gaussianPDFReal 0 (w i) (y i-x i) *
        Real.exp (((x i)^2-(y i)^2)/4) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (gaussianPDFReal_nonneg _ _ _)
      · intro i _
        exact transition_scalar (hr i) (hr1 i) (hw i) (w i).coe_nonneg (x i) (y i)
    _ = _ := by
      simp only [Finset.prod_mul_distrib,density,PiLp.sub_apply,← Real.exp_sum,
        ← Finset.sum_div,Finset.sum_sub_distrib,EuclideanSpace.real_norm_sq_eq]

lemma path_density_eq (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) :
    |(pathEquiv r hr hr1 n).symm.toContinuousLinearMap.det| *
      density (fun _ => 1) ((pathEquiv r hr hr1 n).symm x) =
    density (fun _ => 1) (unpack (Fin (n+1)) ι x 0) *
      ∏ t : Fin n,transition r (unpack (Fin (n+1)) ι x t.castSucc) (unpack (Fin (n+1)) ι x t.succ) := by
  have hd : (pathEquiv r hr hr1 n).symm.toContinuousLinearMap.det =
      ((∏ i,Real.sqrt (1-(r i)^2))^n)⁻¹ := by
    change (pathEquiv r hr hr1 n).toLinearEquiv.symm.toLinearMap.det=_
    rw [LinearEquiv.det_coe_symm]
    exact congrArg Inv.inv (pathEquiv_det r hr hr1 n)
  rw [hd,abs_of_nonneg (by positivity)]
  simp only [density,Fintype.prod_prod_type,Fin.prod_univ_succ,pathEquiv_symm_initial,
    pathEquiv_symm_step,transition,unpack_apply,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Finset.prod_inv_distrib,← inv_pow]
  ring

lemma path_density_le (r : ι → ℝ) (hr : ∀ i,0<r i) (hr1 : ∀ i,r i<1)
    (w : ι → ℝ≥0) (hw : ∀ i,(w i:ℝ)=(1-(r i)^2)/r i) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) :
    |(pathEquiv r (fun i => (hr i).le) hr1 n).symm.toContinuousLinearMap.det| *
      density (fun _ => 1) ((pathEquiv r (fun i => (hr i).le) hr1 n).symm x) ≤
    density (fun _ : ι => 1) 0 * (∏ i,(Real.sqrt (r i))⁻¹)^n *
      HeatL2.chainWeight (kernel w) n (unpack (Fin (n+1)) ι x) := by
  let p := unpack (Fin (n+1)) ι x
  rw [path_density_eq]
  change density (fun _ => 1) (p 0)*(∏ t : Fin n,transition r (p t.castSucc) (p t.succ))≤_
  have hp := Finset.prod_le_prod₀ (fun (t : Fin n) (_ : t∈Finset.univ) => transition_nonneg r (p t.castSucc) (p t.succ))
    (fun (t : Fin n) (_ : t∈Finset.univ) => transition_le r hr hr1 w hw (p t.castSucc) (p t.succ))
  apply (mul_le_mul_of_nonneg_left hp (density_nonneg _ _)).trans
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_sum,
    ← Finset.sum_div]
  rw [HeatL2.fin_sum_differences (fun t => ‖p t‖^2)]
  have hchain : (∏ t : Fin n,density w (p t.succ-p t.castSucc))=HeatL2.chainWeight (kernel w) n p := by
    rw [HeatL2.chainWeight_prod]; rfl
  rw [hchain,density_exp]
  have he : Real.exp (-(∑ i,(p 0 i)^2/(2*(1:ℝ≥0)))) *
      Real.exp ((‖p 0‖^2-‖p (Fin.last n)‖^2)/4) ≤ 1 := by
    rw [← Real.exp_add,Real.exp_le_one_iff]
    simp only [NNReal.coe_one,mul_one,← Finset.sum_div,← EuclideanSpace.real_norm_sq_eq]
    nlinarith [sq_nonneg ‖p 0‖,sq_nonneg ‖p (Fin.last n)‖]
  have hn : 0 ≤ density (fun _ : ι => 1) 0 * (∏ i,(Real.sqrt (r i))⁻¹)^n *
      HeatL2.chainWeight (kernel w) n p := by
    exact mul_nonneg (mul_nonneg (density_nonneg _ _) (by positivity)) (HeatL2.tailWeight_nonneg _ _ _ _)
  nlinarith [mul_le_mul_of_nonneg_left he hn]

end GaussianAR

end

section

open Matrix MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace NNReal ENNReal BigOperators
namespace GaussianAR
open GaussianKernel HeatL2 GaussianTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma survival_le_pathMass (r : ι → ℝ) (hr : ∀ i,0<r i) (hr1 : ∀ i,r i<1)
    (w : ι → ℝ≥0) (hw : ∀ i,(w i:ℝ)=(1-(r i)^2)/r i)
    (D : Set (EuclideanSpace ℝ ι)) (hD : MeasurableSet D) [IsFiniteMeasure (volume.restrict D)]
    (n : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
      {x | ∀ t : Fin (n+1), matrixMap (evaluation r n t) x ∈ D} ≤
      density (fun _ : ι => 1) 0 * (∏ i,(Real.sqrt (r i))⁻¹)^n *
        pathMass (μ := volume.restrict D) (kernel w) n := by
  let P : Set (Fin (n+1) → EuclideanSpace ℝ ι) := univ.pi (fun _ => D)
  let S := (unpack (Fin (n+1)) ι) ⁻¹' P
  let e := pathEquiv r (fun i => (hr i).le) hr1 n
  have hP : MeasurableSet P := MeasurableSet.univ_pi (fun _ => hD)
  have hS : MeasurableSet S := hP.preimage (unpack (Fin (n+1)) ι).measurable
  have heq : e ⁻¹' S = {x | ∀ t : Fin (n+1),matrixMap (evaluation r n t) x ∈ D} := by
    ext x
    change (∀ t ∈ univ,unpack (Fin (n+1)) ι (e x) t ∈ D) ↔ _
    have he (t : Fin (n+1)) : unpack (Fin (n+1)) ι (e x) t = matrixMap (evaluation r n t) x := by
      ext i
      rw [unpack_apply,pathEquiv_apply,pathMatrix_apply]
    simp only [he,mem_univ,forall_const,mem_ofPred_eq]
  have hprob : (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
      {x | ∀ t : Fin (n+1),matrixMap (evaluation r n t) x ∈ D} =
      ∫ x in S, |e.symm.toContinuousLinearMap.det| *density (fun _ => 1) (e.symm x) := by
    rw [Measure.real,← heq,← Measure.map_apply e.continuous.measurable hS,
      linear_image_density e hS,ENNReal.toReal_ofReal]
    exact integral_nonneg (fun x => mul_nonneg (abs_nonneg _) (density_nonneg _ _))
  have hchain : Integrable (chainWeight (kernel w) n) (volume.restrict P) := by
    simpa only [P,volume_pi,Measure.restrict_pi_pi] using
      (chainWeight_integrable (kernel w) (μ := volume.restrict D) n)
  have hic : Integrable (fun x => chainWeight (kernel w) n (unpack (Fin (n+1)) ι x)) (volume.restrict S) :=
    ((unpack_preserving (Fin (n+1)) ι).restrict_preimage_emb
      (unpack (Fin (n+1)) ι).measurableEmbedding P).integrable_comp_of_integrable hchain
  rw [hprob]
  calc
    _ ≤ ∫ x in S, density (fun _ : ι => 1) 0 * (∏ i,(Real.sqrt (r i))⁻¹)^n *
        chainWeight (kernel w) n (unpack (Fin (n+1)) ι x) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (density_nonneg _ _))
        (hic.const_mul _)
      exact Filter.Eventually.of_forall (path_density_le r hr hr1 w hw n)
    _ = _ := by
      rw [integral_const_mul,(unpack_preserving (Fin (n+1)) ι).setIntegral_preimage_emb
        (unpack (Fin (n+1)) ι).measurableEmbedding]
      congr 1
      simp only [P,volume_pi,Measure.restrict_pi_pi,pathMass_pi]

end GaussianAR

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.HeatEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Survival-energy estimates and simultaneous diagonal separation. -/

section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Pointwise
namespace GaussianKernel
variable {ι : Type*} [Fintype ι]

lemma pdf_scale {s : ℝ≥0} (hs : 0<s) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 (s^2*v) ((s:ℝ)*x) = (s:ℝ)⁻¹*gaussianPDFReal 0 v x := by
  have hs' : 0<(s:ℝ) := hs
  have he : 2*Real.pi*((s:ℝ)^2*(v:ℝ))=(s:ℝ)^2*(2*Real.pi*(v:ℝ)) := by ring
  unfold gaussianPDFReal
  simp only [sub_zero,NNReal.coe_mul,NNReal.coe_pow,he,Real.sqrt_mul (sq_nonneg (s:ℝ)),
    Real.sqrt_sq hs'.le,mul_inv_rev]
  have hx : -(((s:ℝ)*x)^2)/(2*((s:ℝ)^2*(v:ℝ))) = -(x^2)/(2*(v:ℝ)) := by
    rw [mul_pow]
    field_simp
  rw [hx]
  ring

lemma density_scale {s : ℝ≥0} (hs : 0<s) (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) :
    density (fun i => s^2*v i) ((s:ℝ) • x) = ((s:ℝ)^(Fintype.card ι))⁻¹*density v x := by
  simp only [density,PiLp.smul_apply,smul_eq_mul,pdf_scale hs,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,inv_pow]

lemma chainWeight_scale {s : ℝ≥0} (hs : 0<s) (v : ι → ℝ≥0) (n : ℕ)
    (p : Fin (n+1) → EuclideanSpace ℝ ι) :
    HeatL2.chainWeight (kernel (fun i => s^2*v i)) n ((s:ℝ) • p) =
      (((s:ℝ)^(Fintype.card ι))⁻¹)^n*HeatL2.chainWeight (kernel v) n p := by
  rw [HeatL2.chainWeight_prod,HeatL2.chainWeight_prod]
  change (∏ t : Fin n,density (fun i => s^2*v i) ((s:ℝ)•p t.succ-(s:ℝ)•p t.castSucc))=_
  simp only [← smul_sub,density_scale hs,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]
  rfl

omit [Fintype ι] in
lemma pi_smul {T : Type*} (s : ℝ) (hs : s≠0) (D : Set (EuclideanSpace ℝ ι)) :
    (univ.pi (fun _ : T => s • D))=s • (univ.pi (fun _ : T => D)) := by
  ext p
  rw [mem_smul_set_iff_inv_smul_mem₀ hs]
  simp only [mem_pi,mem_univ,forall_const,Pi.smul_apply]
  exact forall_congr' fun t => mem_smul_set_iff_inv_smul_mem₀ hs D (p t)

lemma pathMass_scale {s : ℝ≥0} (hs : 0<s) (v : ι → ℝ≥0)
    (D : Set (EuclideanSpace ℝ ι)) (_hD : MeasurableSet D)
    [IsFiniteMeasure (volume.restrict D)] [IsFiniteMeasure (volume.restrict ((s:ℝ) • D))]
    (n : ℕ) :
    HeatL2.pathMass (μ := volume.restrict ((s:ℝ) • D)) (kernel (fun i => s^2*v i)) n =
      (s:ℝ)^(Fintype.card ι)*HeatL2.pathMass (μ := volume.restrict D) (kernel v) n := by
  classical
  have hs' : 0<(s:ℝ) := hs
  let P : Set (Fin (n+1) → EuclideanSpace ℝ ι) := univ.pi (fun _ => D)
  have hh := Measure.setIntegral_comp_smul_of_pos volume
    (HeatL2.chainWeight (kernel (fun i => s^2*v i)) n) P hs'
  simp only [chainWeight_scale hs,integral_const_mul,smul_eq_mul] at hh
  have hdim : Module.finrank ℝ (Fin (n+1) → EuclideanSpace ℝ ι) = (n+1)*Fintype.card ι := by
    simp [Module.finrank_pi_fintype]
  rw [hdim,show P=univ.pi (fun _ : Fin (n+1) => D) from rfl,← pi_smul (s:ℝ) hs'.ne'] at hh
  simp only [volume_pi,Measure.restrict_pi_pi,← HeatL2.pathMass_pi] at hh
  have hn : (s:ℝ)^((n+1)*Fintype.card ι)≠0 := pow_ne_zero _ hs'.ne'
  apply (mul_left_cancel₀ (a := ((s:ℝ)^((n+1)*Fintype.card ι))⁻¹) (inv_ne_zero hn))
  rw [← hh]
  rw [Nat.mul_comm (n+1),pow_mul,pow_succ,mul_inv_rev,← inv_pow]
  calc
    _ = (((s:ℝ)^(Fintype.card ι))^n)⁻¹*HeatL2.pathMass (μ := volume.restrict D) (kernel v) n *
        (((s:ℝ)^(Fintype.card ι))⁻¹*((s:ℝ)^(Fintype.card ι))) := by
      rw [inv_mul_cancel₀ (pow_ne_zero _ hs'.ne'),mul_one]
      simp only [inv_pow]
    _ = _ := by ring

end GaussianKernel

end

section

open MeasureTheory FourierTransform Set Filter ComplexConjugate
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2
section Rate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma energy_smul (w : E → ℝ) (c : ℂ) (f : Lp ℂ 2 (volume : Measure E)) :
    energy w (c • f) = ‖c‖^2 * energy w f := by
  unfold energy
  rw [fourier_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c (𝓕 f)] with x hx
  simp only [hx, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

lemma supported_smul (D : Set E) {f : Lp ℂ 2 (volume : Measure E)}
    (hf : f ∈ supported D) (c : ℂ) : c • f ∈ supported D := by
  filter_upwards [hf, Lp.coeFn_smul c f] with x hx he hn
  simp only [he, Pi.smul_apply, hx hn, smul_zero]

lemma form_le_norm (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {f : Lp ℂ 2 (volume : Measure E)} (hf : f ∈ supported D) :
    ‖f‖^2 - energy w f ≤ ‖compressedHeat D hD w hw hn‖ * ‖f‖^2 := by
  have hh := (positive_norm_le_iff _ (compressedHeat_positive D hD w hw hn)
    (norm_nonneg _)).mp le_rfl f
  rwa [compressedHeat_inner, (mask_eq_self_iff D hD f).mpr hf] at hh

lemma normalized_energy_lt (D : Set E) (w : E → ℝ)
    {f : Lp ℂ 2 (volume : Measure E)} (hfD : f ∈ supported D) (hfn : f ≠ 0)
    {C : ℝ} (hf : energy w f < C*‖f‖^2) :
    ∃ g : Lp ℂ 2 (volume : Measure E), g ∈ supported D ∧ ‖g‖=1 ∧ energy w g < C := by
  let c : ℂ := (‖f‖⁻¹ : ℝ)
  have hc : ‖c‖ = ‖f‖⁻¹ := by simp [c]
  have hnz : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hfn
  have hnorm : ‖c • f‖ = 1 := by rw [norm_smul, hc, inv_mul_cancel₀ hnz]
  refine ⟨c • f, supported_smul D hfD c, hnorm, ?_⟩
  rw [energy_smul, hc]
  have hp : 0 < (‖f‖⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hfn))
  calc
    _ < (‖f‖⁻¹)^2 * (C*‖f‖^2) := mul_lt_mul_of_pos_left hf hp
    _ = C*((‖f‖⁻¹)^2*‖f‖^2) := by ring
    _ = C := by rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hnz), mul_one]

lemma exists_supported_energy_lt (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {C : ℝ} (hC : 0 ≤ C) (h : C < ‖compressedHeat D hD w hw hn‖) :
    ∃ f : Lp ℂ 2 (volume : Measure E), f ∈ supported D ∧ ‖f‖ = 1 ∧ energy w f < 1-C := by
  obtain ⟨g,hg⟩ := positive_exists_form_gt _ (compressedHeat_positive D hD w hw hn) hC h
  rw [compressedHeat_inner] at hg
  let f := mask D hD g
  change C * ‖g‖^2 < ‖f‖^2 - energy w f at hg
  have hfg : ‖f‖^2 ≤ ‖g‖^2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (mask_norm_le D hD g)
  have hf : energy w f < (1-C)*‖f‖^2 := by
    have hh := mul_le_mul_of_nonneg_left hfg hC
    nlinarith
  have hfn : f ≠ 0 := by
    intro he
    have := energy_nonneg w hn f
    rw [he, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hf
    rw [he] at this
    linarith
  exact normalized_energy_lt D w
    ((mask_eq_self_iff D hD f).mp (mask_idempotent D hD g)) hfn hf

lemma compressed_norm_le_of_energy (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : AEStronglyMeasurable w volume) (hn : ∀ x, 0 ≤ w x)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f : Lp ℂ 2 (volume : Measure E), f ∈ supported D →
      ‖f‖=1 → 1 - energy w f ≤ C) :
    ‖compressedHeat D hD w hw hn‖ ≤ C := by
  by_contra! hg
  obtain ⟨f,hf,hfn,hfe⟩ := exists_supported_energy_lt D hD w hw hn hC hg
  linarith [h f hf hfn]

lemma compressed_norm_mono_symbol (D : Set E) (hD : MeasurableSet D)
    (w v : E → ℝ) (hw : AEStronglyMeasurable w volume) (hv : AEStronglyMeasurable v volume)
    (hwn : ∀ x, 0 ≤ w x) (hvn : ∀ x, 0 ≤ v x) (h : ∀ x, w x ≤ v x) :
    ‖compressedHeat D hD v hv hvn‖ ≤ ‖compressedHeat D hD w hw hwn‖ := by
  apply compressed_norm_le_of_energy D hD v hv hvn (norm_nonneg _)
  intro f hf hfn
  have hE : energy w f ≤ energy v f := by
    rw [energy,energy]
    apply integral_mono (integrable_energy w hw hwn f) (integrable_energy v hv hvn f)
    intro x
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg (h x))) 1
  have hh := form_le_norm D hD w hw hwn hf
  rw [hfn, one_pow, mul_one] at hh
  linarith

end Rate
end HeatL2

end

section

open MeasureTheory Set Filter
open scoped NNReal Topology
namespace HeatL2.Diagonal
variable {ι : Type*} [Fintype ι]

lemma symbol_mono {v w : ι → ℝ≥0} (h : ∀ i,v i≤w i) (ξ : EuclideanSpace ℝ ι) :
    GaussianKernel.symbol v ξ ≤ GaussianKernel.symbol w ξ := by
  unfold GaussianKernel.symbol
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (h i) (sq_nonneg _)) (by norm_num)

lemma bound_of_positive {D : Set (EuclideanSpace ℝ ι)} {hD : MeasurableSet D} {c : ℝ}
    (h : ∀ v : ι → ℝ≥0, (∀ i,0<v i) → Real.exp (-(c/2)*∑ i,(v i:ℝ)) ≤
      ‖compressedHeat D hD (GaussianKernel.symbol v)
        (GaussianKernel.symbol_continuous v).aestronglyMeasurable (GaussianKernel.symbol_nonneg v)‖) :
    Bound D hD c := by
  intro v
  have ht : Tendsto (fun ε : ℝ => Real.exp (-(c/2)*∑ i,((v i:ℝ)+ε))) (𝓝[>] 0)
      (𝓝 (Real.exp (-(c/2)*∑ i,(v i:ℝ)))) := by
    have hh : Continuous (fun ε : ℝ => Real.exp (-(c/2)*∑ i,((v i:ℝ)+ε))) := by fun_prop
    simpa using (hh.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0<ε := hε
  let w : ι → ℝ≥0 := fun i => ⟨(v i:ℝ)+ε,by positivity⟩
  have hp := h w (fun i => by change 0<(v i:ℝ)+ε; positivity)
  exact hp.trans (compressed_norm_mono_symbol D hD _ _
    (GaussianKernel.symbol_continuous v).aestronglyMeasurable
    (GaussianKernel.symbol_continuous w).aestronglyMeasurable
    (GaussianKernel.symbol_nonneg v) (GaussianKernel.symbol_nonneg w)
    (symbol_mono (fun i => by change (v i:ℝ)≤(v i:ℝ)+ε; linarith)))

lemma Bound.mono_const {D : Set (EuclideanSpace ℝ ι)} {hD : MeasurableSet D} {c d : ℝ}
    (h : Bound D hD c) (hcd : c≤d) : Bound D hD d := by
  intro v
  exact (Real.exp_le_exp.mpr (by
    have hh : 0≤∑ i,(v i:ℝ) := Finset.sum_nonneg fun i _ => (v i).coe_nonneg
    nlinarith)).trans (h v)

end HeatL2.Diagonal

end

section

open Matrix MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace NNReal ENNReal Pointwise
namespace GaussianAR
open GaussianKernel HeatL2 GaussianTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma scaled_kernel_norm_of_survival {s : ℝ≥0} (hs : 0<s)
    (r : ι → ℝ) (hr : ∀ i,0<r i) (hr1 : ∀ i,r i<1)
    (w : ι → ℝ≥0) (hw : ∀ i,(w i:ℝ)=(1-(r i)^2)/r i)
    (D : Set (EuclideanSpace ℝ ι)) (hD : MeasurableSet D)
    [IsFiniteMeasure (volume.restrict D)] [IsFiniteMeasure (volume.restrict ((s:ℝ) • D))]
    (a b : ℝ) (hsurv : ∀ n : ℕ, Real.exp (-a-b*n) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
        {x | ∀ t : Fin (n+1), matrixMap (evaluation r n t) x ∈ D}) :
    Real.exp (-b) / (∏ i,(Real.sqrt (r i))⁻¹) ≤
      ‖kernelOp (μ := volume.restrict ((s:ℝ) • D)) (kernel (fun i => s^2*w i))‖ := by
  have hρ : 0 < density (fun _ : ι => 1) 0 := density_pos _ (fun _ => by simp) _
  have hc : 0 < ∏ i,(Real.sqrt (r i))⁻¹ := Finset.prod_pos fun i _ =>
    inv_pos.mpr (Real.sqrt_pos.mpr (hr i))
  have hs' : 0<(s:ℝ) := hs
  apply norm_lower_of_pathMass_lower (kernel (fun i => s^2*w i)) (by positivity)
    (c := (s:ℝ)^(Fintype.card ι)*Real.exp (-a)/density (fun _ : ι => 1) 0) (by positivity)
  intro n
  rw [pathMass_scale hs w D hD n]
  have hn := (hsurv n).trans (survival_le_pathMass r hr hr1 w hw D hD n)
  have hex : Real.exp (-a-b*n)=Real.exp (-a)*(Real.exp (-b))^n := by
    rw [show -a-b*(n:ℝ)= -a+(-b)*n by ring,Real.exp_add,mul_comm (-b),Real.exp_nat_mul]
  rw [hex] at hn
  have hl : Real.exp (-a)/density (fun _ : ι => 1) 0 *
      (Real.exp (-b)/(∏ i,(Real.sqrt (r i))⁻¹))^n ≤ pathMass (μ := volume.restrict D) (kernel w) n := by
    apply (mul_le_mul_iff_left₀ (mul_pos hρ (pow_pos hc n))).mp
    convert hn using 1
    · calc
        _ = (Real.exp (-a)/density (fun _ : ι => 1) 0 * density (fun _ : ι => 1) 0) *
            ((Real.exp (-b))^n/(∏ i,(Real.sqrt (r i))⁻¹)^n * (∏ i,(Real.sqrt (r i))⁻¹)^n) := by
          rw [div_pow]; ring
        _ = _ := by rw [div_mul_cancel₀ _ hρ.ne',div_mul_cancel₀ _ (pow_ne_zero n hc.ne')]
    · ring
  simpa only [div_eq_mul_inv,mul_assoc] using
    mul_le_mul_of_nonneg_left hl (pow_nonneg hs'.le (Fintype.card ι))

lemma decay_sqrt_bound {q : ℝ} (_hq : 0 ≤ q) :
    (Real.sqrt ((1+q)⁻¹))⁻¹ ≤ Real.exp (q/2) := by
  rw [Real.sqrt_inv,inv_inv,Real.exp_half]
  exact Real.sqrt_le_sqrt (by linarith [Real.add_one_le_exp q])

lemma dilated_bound_of_survival {s : ℝ≥0} (hs : 0<s)
    (D : Set (EuclideanSpace ℝ ι)) (hD : MeasurableSet D)
    (hDs : MeasurableSet ((s:ℝ) • D))
    [IsFiniteMeasure (volume.restrict D)] [IsFiniteMeasure (volume.restrict ((s:ℝ) • D))]
    (B : ℝ) (hsurv : ∀ q : ι → ℝ, (∀ i,0<q i) → ∃ a : ℝ, ∀ n : ℕ,
      Real.exp (-a-B*(∑ i,q i)*n) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
        {x | ∀ t : Fin (n+1),matrixMap (evaluation (fun i => (1+q i)⁻¹) n t) x ∈ D}) :
    HeatL2.Diagonal.Bound ((s:ℝ) • D) hDs ((2*B+1)/(s:ℝ)^2) := by
  apply HeatL2.Diagonal.bound_of_positive
  intro v hv
  have hs' : 0<(s:ℝ) := hs
  let q : ι → ℝ := fun i => (v i:ℝ)/(s:ℝ)^2
  have hq : ∀ i,0<q i := fun i => div_pos (hv i) (sq_pos_of_pos hs')
  let r : ι → ℝ := fun i => (1+q i)⁻¹
  have hr : ∀ i,0<r i := fun i => inv_pos.mpr (by linarith [hq i])
  have hr1 : ∀ i,r i<1 := fun i => (inv_lt_one₀ (by linarith [hq i])).mpr (by linarith [hq i])
  let w : ι → ℝ≥0 := fun i => ⟨(1-(r i)^2)/r i,div_nonneg (by nlinarith [hr i,hr1 i]) (hr i).le⟩
  have hw : ∀ i,0<w i := fun i => by change 0<(1-(r i)^2)/r i; exact div_pos (by nlinarith [hr i,hr1 i]) (hr i)
  have hvar : ∀ i,v i≤ s^2*w i := by
    intro i
    change (v i:ℝ)≤(s:ℝ)^2*((1-(r i)^2)/r i)
    have he : (1-(r i)^2)/r i=q i*(2+q i)/(1+q i) := by
      dsimp only [r]
      field_simp [ne_of_gt (show 0<1+q i by linarith [hq i])]
      ring
    rw [he]
    have hqq : q i ≤ q i*(2+q i)/(1+q i) := by
      apply (le_div_iff₀ (by linarith [hq i])).mpr
      nlinarith [hq i]
    have hh := mul_le_mul_of_nonneg_left hqq (sq_nonneg (s:ℝ))
    simpa only [q,mul_div_cancel₀ _ (ne_of_gt (sq_pos_of_pos hs'))] using hh
  obtain ⟨a,ha⟩ := hsurv q hq
  have hn := scaled_kernel_norm_of_survival hs r hr hr1 w (fun _ => rfl) D hD a
    (B*(∑ i,q i)) (by simpa only [mul_assoc] using ha)
  rw [kernel_norm_eq _ (fun i => mul_ne_zero (pow_ne_zero _ hs.ne') (ne_of_gt (hw i))) _ hDs] at hn
  have hc : ∏ i,(Real.sqrt (r i))⁻¹ ≤ Real.exp ((∑ i,q i)/2) := by
    calc
      _ ≤ ∏ i,Real.exp (q i/2) := Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => decay_sqrt_bound (hq i).le)
      _ = _ := by rw [← Real.exp_sum]; congr 1; rw [Finset.sum_div]
  have hcp : 0<∏ i,(Real.sqrt (r i))⁻¹ := Finset.prod_pos fun i _ => by positivity
  have he : Real.exp (-(((2*B+1)/(s:ℝ)^2)/2)*(∑ i,(v i:ℝ))) =
      Real.exp (-(B*(∑ i,q i)))/Real.exp ((∑ i,q i)/2) := by
    rw [← Real.exp_sub]
    congr 1
    simp only [q,← Finset.sum_div]
    field_simp
    ring
  rw [he]
  exact (div_le_div_of_nonneg_left (Real.exp_pos _).le hcp hc).trans (hn.trans
    (compressed_norm_mono_symbol _ hDs _ _ (symbol_continuous v).aestronglyMeasurable
      (symbol_continuous (fun i => s^2*w i)).aestronglyMeasurable (symbol_nonneg v)
      (symbol_nonneg _) (HeatL2.Diagonal.symbol_mono hvar)))

end GaussianAR

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.FilteredBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filtered-body energy and the predictor slab budget. -/

section

open Matrix GaussianTail MeasureTheory ProbabilityTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Pointwise NNReal
namespace GaussianEvents
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype I]
lemma openConstraints_open (A : I → E →L[ℝ] F) (R : I → ℝ) : IsOpen (openConstraints A R) := by
  simp only [openConstraints,Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (A i).continuous.norm continuous_const
omit [Fintype I] in
lemma openConstraints_convex (A : I → E →L[ℝ] F) (R : I → ℝ) : Convex ℝ (openConstraints A R) := by
  have he : openConstraints A R = ⋂ i,(A i) ⁻¹' Metric.ball 0 (R i) := by
    ext x; simp [openConstraints,Metric.mem_ball,dist_zero_right]
  rw [he]
  exact convex_iInter fun i => (convex_ball (0:F) (R i)).linear_preimage (A i).toLinearMap
omit [Fintype I] in
lemma openConstraints_symmetric (A : I → E →L[ℝ] F) (R : I → ℝ) :
    ∀ x∈openConstraints A R,-x∈openConstraints A R := by
  intro x hx i
  simpa only [map_neg,norm_neg] using hx i
omit [Fintype I] in
lemma openConstraints_zero (A : I → E →L[ℝ] F) {R : I → ℝ} (hR : ∀ i,0<R i) :
    (0:E)∈openConstraints A R := by intro i; simpa only [map_zero,norm_zero] using hR i
end GaussianEvents

namespace EuclideanSteinitz.Filter
open GaussianAR GaussianEvents Coefficient
variable {ι κ T J : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Fintype T] [Fintype J] [Nonempty ι] [Nonempty κ]

lemma bodyRate_nonneg : 0≤bodyRate := by unfold bodyRate; linarith [stateRate_nonneg]

omit [DecidableEq ι] [Nonempty ι] [Nonempty κ] in
lemma applicationDomain_open (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    IsOpen (applicationDomain Rt H) :=
  ((openConstraints_open _ _).inter Metric.isOpen_ball).inter (openConstraints_open _ _)
omit [DecidableEq ι] [Nonempty ι] [Nonempty κ] [Fintype T] [Fintype J] in
lemma applicationDomain_convex (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    Convex ℝ (applicationDomain Rt H) :=
  ((openConstraints_convex _ _).inter (convex_ball _ _)).inter (openConstraints_convex _ _)
omit [DecidableEq ι] [Fintype T] [Fintype J] [Nonempty ι] [Nonempty κ] in
lemma applicationDomain_bounded (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    Bornology.IsBounded (applicationDomain Rt H) :=
  (Metric.isBounded_ball (x := (0:EuclideanSpace ℝ κ)) (r := _)).subset (fun _ hx => hx.1.2)
omit [DecidableEq ι] [Nonempty ι] [Nonempty κ] [Fintype T] [Fintype J] in
lemma applicationDomain_symmetric (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    ∀ x∈applicationDomain Rt H,-x∈applicationDomain Rt H := by
  intro x hx
  refine ⟨⟨openConstraints_symmetric _ _ x hx.1.1,?_⟩,openConstraints_symmetric _ _ x hx.2⟩
  simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hx.1.2
omit [DecidableEq ι] [Fintype T] [Fintype J] in
lemma applicationDomain_zero (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    (0:EuclideanSpace ℝ κ)∈applicationDomain Rt H := by
  have hι : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hκ : (0:ℝ)<Fintype.card κ := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨⟨openConstraints_zero _ (fun _ => mul_pos (mul_pos (by norm_num) stateRadius_pos) (Real.sqrt_pos.mpr hι)),?_⟩,openConstraints_zero _ (fun _ => mul_pos (by norm_num) slabRadius_pos)⟩
  simp only [Metric.mem_ball,dist_self]
  exact mul_pos (mul_pos (by norm_num) stateRadius_pos) (Real.sqrt_pos.mpr hκ)

lemma bodyScale_pos : 0 < bodyScale := by unfold bodyScale; linarith [bodyRate_nonneg]
lemma bodyScale_ge_one : 1 ≤ bodyScale := by unfold bodyScale; linarith [bodyRate_nonneg]
lemma bodyScale_bound : (2*bodyRate+1)/bodyScale^2 ≤ 1/10000 := by
  apply (div_le_iff₀ (sq_pos_of_pos bodyScale_pos)).mpr
  unfold bodyScale
  nlinarith [bodyRate_nonneg,sq_nonneg bodyRate]

lemma applicationDomain_good {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hf : Fresh R L) (hd : (L.map Step.j).Nodup)
    (ps : T → List (Step ι κ)) (hps : ∀ t,ps t <+: L)
    (H : J → Matrix Unit κ ℝ) (hH : ∀ j,squareMass (H j)≤1) (hcol : ∀ i,∑ j,(H j () i)^2≤1) :
    ShiftedSections.Good (bodyScale • applicationDomain (fun t => run R (ps t)) H) := by
  let D := applicationDomain (fun t => run R (ps t)) H
  let s : ℝ≥0 := ⟨bodyScale,bodyScale_pos.le⟩
  have ho := applicationDomain_open (fun t => run R (ps t)) H
  have hb := applicationDomain_bounded (fun t => run R (ps t)) H
  have hso := ho.smul₀ bodyScale_pos.ne'
  have hsb := hb.smul₀ bodyScale
  let : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict ((s:ℝ) • D)) := isFiniteMeasure_restrict.mpr hsb.measure_lt_top.ne
  refine ⟨?_,hso,hsb,(applicationDomain_convex _ _).smul bodyScale,?_,?_⟩
  · exact ⟨0,Set.mem_smul_set.mpr ⟨0,applicationDomain_zero _ _,smul_zero _⟩⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Set.mem_smul_set.mp hx
    exact Set.mem_smul_set.mpr ⟨-y,applicationDomain_symmetric _ _ y hy,smul_neg _ _⟩
  · have hh := dilated_bound_of_survival (s := s) bodyScale_pos D
      ho.measurableSet hso.measurableSet bodyRate
      (fun q hq => applicationDomain_survival hR hp hf hd ps hps H hH hcol hq)
    exact hh.mono_const bodyScale_bound

end EuclideanSteinitz.Filter

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.SigningData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized predictors and backward-forward shifted walks. -/

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
variable {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

omit [DecidableEq ν] in
lemma initialMatrix_coisometry : initialMatrix ι ν*(initialMatrix ι ν).transpose=1 := by
  simp [initialMatrix,Matrix.transpose_fromCols,Matrix.fromCols_mul_fromRows]
lemma initialMatrix_eval (x : EuclideanSpace ℝ (ι⊕ν)) (hx : ∀ i,x (Sum.inl i)=0) :
    matrixMap (initialMatrix ι ν) x=0 := by
  apply WithLp.ofLp_injective
  change (Matrix.fromCols 1 0)*ᵥx=0
  simp only [Matrix.fromCols_mulVec,Matrix.one_mulVec,Matrix.zero_mulVec,add_zero]
  exact funext hx

lemma familySteps_good {n : ℕ} {b : Fin n → ι → ℝ} (hb : ∀ i,vectorMass (b i)<1) :
    ∀ p∈familySteps b,p.Good := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact symmetricStep_good (hb i) _
lemma familySteps_symmetric {n : ℕ} (b : Fin n → ι → ℝ) :
    ∀ p∈familySteps b,p.C=symmetricContraction p.b := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  rfl
lemma familySteps_mass {n : ℕ} {b : Fin n → ι → ℝ} {B : ℝ} (hb : ∀ i,vectorMass (b i)≤B) :
    ∀ p∈familySteps b,vectorMass p.b≤B := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact hb i
lemma familySteps_fresh {n : ℕ} (b : Fin n → ι → ℝ) : Fresh (initialMatrix ι (Fin n)) (familySteps b) := by
  intro p hp k
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  simp [initialMatrix,symmetricStep]
lemma familySteps_nodup {n : ℕ} (b : Fin n → ι → ℝ) : ((familySteps b).map Step.j).Nodup := by
  simpa only [familySteps,List.map_ofFn,Function.comp_def,symmetricStep] using
    (List.nodup_ofFn.mpr (Sum.inr_injective : Function.Injective (Sum.inr : Fin n → ι⊕Fin n)))

lemma familyPredictor_form {n : ℕ} (b : Fin n → ι → ℝ) (i : Fin n) :
    familyPredictor b i=noiseRow (rawRow (run (initialMatrix ι (Fin n)) ((familySteps b).take i.val)) (b i)) := by
  unfold familyPredictor
  rw [predictorRows_get _ _ _ (by simpa only [familySteps,List.length_ofFn] using i.isLt)]
  simp only [familySteps,List.getElem_ofFn,symmetricStep]

lemma familyPredictor_future {n : ℕ} (b : Fin n → ι → ℝ) (i l : Fin n) (hil : i≤l) :
    familyPredictor b i (Sum.inr l)=0 := by
  have hh := predictor_future_zero (familySteps_fresh b) (familySteps_nodup b) i.val l.val hil
    (by simpa only [familySteps,List.length_ofFn] using l.isLt)
  simpa only [familyPredictor,noiseRow,Sum.elim_inr,familySteps,List.getElem_ofFn,symmetricStep] using hh

lemma familyPredictor_mass {n : ℕ} {b : Fin n → ι → ℝ} (hb : ∀ i,vectorMass (b i)<1) (i : Fin n) :
    vectorMass (familyPredictor b i)≤vectorMass (b i) := by
  apply (noiseRow_mass _).trans
  have hh := predictor_row_bound (initialMatrix_coisometry (ι := ι) (ν := Fin n))
    (familySteps_good hb) (familySteps_fresh b) (familySteps_nodup b) i.val
    (by simpa only [familySteps,List.length_ofFn] using i.isLt)
  simpa only [familySteps,List.getElem_ofFn,symmetricStep] using hh

lemma sum_getElem_of_length {α : Type*} (L : List α) {n : ℕ} (hL : L.length=n) (f : α → ℝ) :
    (∑ i : Fin n,f (L[i.val]'(by omega)))=(L.map f).sum := by
  subst n
  rw [← List.sum_ofFn,List.ofFn_getElem_eq_map]

lemma familyPredictor_column {n : ℕ} {b : Fin n → ι → ℝ} (hb : ∀ i,vectorMass (b i)<1)
    {B : ℝ} (hB : 0≤B) (hbB : ∀ i,vectorMass (b i)≤B) (k : ι⊕Fin n) :
    (∑ i,(familyPredictor b i k)^2)≤B := by
  cases k with
  | inl k => simpa only [familyPredictor,noiseRow,Sum.elim_inl,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero] using hB
  | inr k =>
    have hh := predictor_column_bound (familySteps_symmetric b) (familySteps_mass (fun i => (hb i).le))
      (familySteps_fresh b) (familySteps_nodup b) hB (familySteps_mass hbB) (Sum.inr k)
      (by intro i; simp [initialMatrix])
    have hlen : (predictorRows (initialMatrix ι (Fin n)) (familySteps b)).length=n := by
      rw [predictorRows_length]; simp [familySteps]
    simpa only [familyPredictor,noiseRow,Sum.elim_inr,sum_getElem_of_length _ hlen (fun m => m (Sum.inr k)^2)] using hh

lemma signingScale_pos : 0 < signingScale := div_pos (by norm_num) (mul_pos (mul_pos (by norm_num) bodyScale_pos) GaussianAR.slabRadius_pos)
lemma signingScale_lt_one : signingScale<1 := by
  unfold signingScale
  apply (div_lt_one (mul_pos (mul_pos (by norm_num) bodyScale_pos) GaussianAR.slabRadius_pos)).mpr
  have hs : 1≤GaussianAR.slabRadius := by norm_num [GaussianAR.slabRadius]
  nlinarith [bodyScale_ge_one]
lemma signingScale_cancel : 2*bodyScale*GaussianAR.slabRadius*signingScale=1/4 := by
  unfold signingScale
  field_simp [bodyScale_pos.ne',GaussianAR.slabRadius_pos.ne']
  ring

lemma normalizedPredictor_mass {n : ℕ} {b : Fin n → ι → ℝ}
    (hb : ∀ i,vectorMass (b i)≤ signingScale^2) (i : Fin n) : squareMass (normalizedPredictor b i)≤1 := by
  have hlt : ∀ i,vectorMass (b i)<1 := fun i => (hb i).trans_lt (by nlinarith [signingScale_pos,signingScale_lt_one])
  change (∑ _ : Unit,∑ k,(familyPredictor b i k/signingScale)^2)≤1
  simp only [Fintype.sum_unique,div_pow,← Finset.sum_div]
  apply (div_le_one (sq_pos_of_pos signingScale_pos)).mpr
  exact (familyPredictor_mass hlt i).trans (hb i)

lemma normalizedPredictor_column {n : ℕ} {b : Fin n → ι → ℝ}
    (hb : ∀ i,vectorMass (b i)≤ signingScale^2) (k : ι⊕Fin n) :
    (∑ i,(normalizedPredictor b i () k)^2)≤1 := by
  have hlt : ∀ i,vectorMass (b i)<1 := fun i => (hb i).trans_lt (by nlinarith [signingScale_pos,signingScale_lt_one])
  simp only [normalizedPredictor,div_pow,← Finset.sum_div]
  apply (div_le_one (sq_pos_of_pos signingScale_pos)).mpr
  exact familyPredictor_column hlt (sq_nonneg _) hb k

lemma normalizedPredictor_norm {n : ℕ} (b : Fin n → ι → ℝ) (i : Fin n) (x : EuclideanSpace ℝ (ι⊕Fin n)) :
    ‖matrixMap (normalizedPredictor b i) x‖=|rowMap (familyPredictor b i) x|/signingScale := by
  change ‖matrixMap (fun _ : Unit => fun k => familyPredictor b i k/signingScale) x‖=_
  rw [rowMatrix_norm,rowMap_apply,rowMap_apply]
  simp only [dotProduct,div_mul_eq_mul_div,← Finset.sum_div,abs_div,abs_of_pos signingScale_pos]

end EuclideanSteinitz.Filter

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Transference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive-forward and negative-reverse permutation transference. -/

section

namespace EuclideanSteinitzBergstrom

section Lists

variable {α E : Type*}

lemma sum_take_ofFn [AddCommMonoid E] {N : ℕ} (v : Fin N → E) (k : ℕ) :
    ((List.ofFn v).take k).sum =
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), v i := by
  induction N generalizing k with
  | zero => simp
  | succ N ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.ofFn_succ, List.take_succ_cons, List.sum_cons,
        Finset.sum_filter, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.zero_lt_succ, ite_true, Fin.val_succ,
        Nat.succ_lt_succ_iff]
      rw [ih]
      rw [Finset.sum_filter]

end Lists

end EuclideanSteinitzBergstrom

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Euclidean Steinitz–Bergström theorem with one absolute constant. -/

section

open Matrix GaussianTail MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Pointwise
namespace EuclideanSteinitz.Filter
open GaussianAR
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma filtered_signed_prefixes {n : ℕ} (b : Fin n → ι → ℝ)
    (hb : ∀ i, vectorMass (b i) ≤ signingScale^2) :
    ∃ ε : Fin n → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) ∧
      ∀ k : ℕ, k ≤ n →
        ‖∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), ε i • WithLp.toLp 2 (b i)‖ ≤
          (2*bodyScale*stateRadius)*Real.sqrt (Fintype.card ι) := by
  let R := initialMatrix ι (Fin n)
  let L := familySteps b
  let ps : Fin (n+1) → List (Step ι (ι⊕Fin n)) := fun t => L.take t.val
  let H := normalizedPredictor b
  let K := bodyScale • applicationDomain (fun t => run R (ps t)) H
  have hlt : ∀ i,vectorMass (b i)<1 := fun i =>
    (hb i).trans_lt (by nlinarith [signingScale_pos,signingScale_lt_one])
  have hg : ShiftedSections.Good K := applicationDomain_good initialMatrix_coisometry
    (familySteps_good hlt) (familySteps_fresh b) (familySteps_nodup b) ps
    (fun t => List.take_prefix t.val L) H (normalizedPredictor_mass hb) (normalizedPredictor_column hb)
  let m : Fin n → EuclideanSpace ℝ (ι⊕Fin n) →L[ℝ] ℝ := fun i => rowMap (familyPredictor b i)
  have hm : ∀ i l : Fin n,i≤l → m i (EuclideanSpace.single (Sum.inr l) 1)=0 := by
    intro i l hil
    rw [show m i=rowMap (familyPredictor b i) from rfl,rowMap_single,familyPredictor_future b i l hil]
  have hslab : ∀ x∈K,∀ i,|m i x|<1/4 := by
    intro x hx i
    obtain ⟨y,hy,rfl⟩ := Set.mem_smul_set.mp hx
    have hh := hy.2 i
    change ‖matrixMap (normalizedPredictor b i) y‖<2*slabRadius at hh
    rw [normalizedPredictor_norm] at hh
    have hh' := (div_lt_iff₀ signingScale_pos).mp hh
    change |rowMap (familyPredictor b i) (bodyScale • y)| < _
    rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos bodyScale_pos]
    have hf := mul_lt_mul_of_pos_left hh' bodyScale_pos
    have he : bodyScale*(2*slabRadius*signingScale)=1/4 := by
      nlinarith [signingScale_cancel]
    simpa only [he] using hf
  obtain ⟨ε,x,hε,hx,hxout,hxeq⟩ := ShiftedSections.adaptive_linear_equations
    (Sum.inr : Fin n → ι⊕Fin n) Sum.inr_injective m hm hg hslab
  have hx0 : ∀ i,x (Sum.inl i)=0 := by
    intro i
    exact hxout (Sum.inl i) (fun j => Sum.inl_ne_inr)
  have hxeq' : ∀ i,x (Sum.inr i)=rowMap (rawRow (run R (L.take i.val)) (b i)) x+ε i := by
    intro i
    have hh := hxeq i
    change x (Sum.inr i)=rowMap (familyPredictor b i) x+ε i at hh
    rw [familyPredictor_form,noiseRow_eval _ _ hx0] at hh
    exact hh
  have hcancel (k : ℕ) : matrixMap (run R (L.take k)) x=
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),ε i • WithLp.toLp 2 (b i) := by
    have hh := run_prefix_cancel (fun i => symmetricStep (b i) (Sum.inr i)) R x ε
      (fun _ => rfl) hxeq' k
    rw [initialMatrix_eval x hx0,zero_add,EuclideanSteinitzBergstrom.sum_take_ofFn] at hh
    exact hh
  refine ⟨ε,hε,fun k hk => ?_⟩
  rw [← hcancel k]
  obtain ⟨y,hy,rfl⟩ := Set.mem_smul_set.mp hx
  have hh := hy.1.1 (⟨k,by omega⟩ : Fin (n+1))
  change ‖matrixMap (run R (L.take k)) y‖ < 2*stateRadius*Real.sqrt (Fintype.card ι) at hh
  rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos bodyScale_pos]
  have hf := mul_lt_mul_of_pos_left hh bodyScale_pos
  nlinarith

end EuclideanSteinitz.Filter

namespace EuclideanSteinitzBergstrom
open EuclideanSteinitz.Filter GaussianAR

theorem signed_prefix_bound : SignedPrefixBound universalConstant := by
  classical
  intro d N hd _hN v hv
  let : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
  let b : Fin N → Fin d → ℝ := fun i => (signingScale • v i).ofLp
  have hb : ∀ i,vectorMass (b i) ≤ signingScale^2 := by
    intro i
    have he : vectorMass (b i)=‖signingScale • v i‖^2 := by
      exact (EuclideanSpace.real_norm_sq_eq (signingScale • v i)).symm
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos signingScale_pos,mul_pow]
    exact (mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg (v i),hv i] : ‖v i‖^2≤1)
      (sq_nonneg signingScale)).trans_eq (mul_one _)
  obtain ⟨ε,hε,hpref⟩ := filtered_signed_prefixes b hb
  refine ⟨ε,hε,fun k hk => ?_⟩
  have hh := hpref k hk
  have he : (∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k),ε i • WithLp.toLp 2 (b i))=
      signingScale • ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k),ε i • v i := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change ε i • (signingScale • v i)=signingScale • (ε i • v i)
    exact smul_comm _ _ _
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos signingScale_pos,Fintype.card_fin] at hh
  have hc : universalConstant*Real.sqrt d=(2*bodyScale*stateRadius*Real.sqrt d)/signingScale := by
    unfold universalConstant
    ring
  rw [hc]
  apply (le_div_iff₀ signingScale_pos).mpr
  nlinarith

theorem main_oai : ∃ C : ℝ, SignedPrefixBound C ∧ OrderingPrefixBound C :=
  ⟨universalConstant,signed_prefix_bound,signing_implies_ordering universalConstant signed_prefix_bound⟩

end EuclideanSteinitzBergstrom

end

end OAI
end

theorem solution : type_of% @OAI.EuclideanSteinitzBergstrom.main_oai := @OAI.EuclideanSteinitzBergstrom.main_oai
