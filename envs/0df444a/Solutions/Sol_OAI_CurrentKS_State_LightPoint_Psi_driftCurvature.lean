-- Prove2me | solution 1 for OAI.CurrentKS.State.LightPoint.Psi_driftCurvature
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:38.998728+00:00
-- url     : https://prove2.me/submissions/309e6fd3-9868-406a-8e4a-96c1f501ffdc

import Mathlib
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_CurrentKS_Variational_contDiffAt_value

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ScalarPsi
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open scoped ContDiff

lemma base_pos {x : ℝ} (hx : |x| < 1) : 0 < 1-x^2 := by
  have h := (abs_lt.mp hx)
  nlinarith [sq_nonneg x]

lemma psi_pos {x : ℝ} (hx : |x| < 1) : 0 < psi x :=
  Real.rpow_pos_of_pos (base_pos hx) _

lemma psi_cube {x : ℝ} (hx : |x| < 1) : psi x ^ 3 = 1-x^2 := by
  rw [psi, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (base_pos hx))]
  norm_num

lemma psi_sq {x : ℝ} (hx : |x| < 1) : psi x ^ 2 = (1-x^2) ^ (2/3 : ℝ) := by
  rw [psi, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (base_pos hx))]
  norm_num

lemma hasDerivAt_psi {x : ℝ} (hx : |x| < 1) : HasDerivAt psi (psi₁ x) x := by
  have hr := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).rpow_const
    (p := (1/3 : ℝ)) (Or.inl (ne_of_gt (base_pos hx)))
  convert hr using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  norm_num only [mul_one, zero_sub, Nat.cast_ofNat]
  simp only [id_eq, pow_one, Pi.sub_apply, Pi.pow_apply]
  rw [Real.rpow_neg (base_pos hx).le, ← psi_sq hx]
  unfold psi₁
  ring

lemma contDiffAt_psi {x : ℝ} (hx : |x| < 1) {n : WithTop ℕ∞} : ContDiffAt ℝ n psi x := by
  exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (base_pos hx))).comp x
    (contDiffAt_const.sub (contDiffAt_id.pow 2))

lemma hasDerivAt_psi₁ {x : ℝ} (hx : |x| < 1) : HasDerivAt psi₁ (-kappa x) x := by
  have hw : psi x ≠ 0 := ne_of_gt (psi_pos hx)
  have hp := hasDerivAt_psi hx
  have hd := ((hasDerivAt_id x).const_mul (-2)).div ((hp.pow 2).const_mul 3)
    (by positivity : (3 : ℝ) * psi x^2 ≠ 0)
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  unfold kappa psi₁
  have hc := psi_cube hx
  field_simp
  nlinarith [hc]

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_HermitianMat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.invH_val _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_one _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace

variable {d : ℕ}

open scoped Matrix.Norms.Frobenius

theorem matrix_inner (d : ℕ) (A B : Mat d) :
    inner ℂ A B = (B * Aᴴ).trace := by
  change inner ℂ (asL2 A) (asL2 B) = _
  simp only [asL2, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1

theorem inner_eq_trace (A B : H d) :
    inner ℝ A B = ((A : Mat d) * (B : Mat d)).trace.re := by
  change (inner ℂ (A : Mat d) (B : Mat d)).re = _
  rw [matrix_inner, A.property.eq, Matrix.trace_mul_comm]

@[simp] theorem inner_one (A : H d) : inner ℝ one A = realTrace A := by
  rw [inner_eq_trace, one_val, one_mul]
  rfl

@[simp] theorem inner_one' (A : H d) : inner ℝ A one = realTrace A := by
  rw [real_inner_comm]
  exact inner_one A

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_TraceCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

@[simp] lemma traceCLM_apply (A : H d) : traceCLM A = realTrace A := inner_one A

lemma psd_nonneg {A : H d} (hA : A ∈ psdCone d) : 0 ≤ A := hA.nonneg

lemma mem_psd_iff_nonneg (A : H d) : A ∈ psdCone d ↔ 0 ≤ A := by
  constructor
  · exact psd_nonneg
  · intro hA
    have hh : (0 : Mat d) ≤ (A : Mat d) := hA
    exact hh.posSemidef

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealTraceSum
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma psd_sum {ι : Type*} (s : Finset ι) (A : ι → H d) (hA : ∀ i ∈ s, A i ∈ psdCone d) :
    (∑ i ∈ s, A i) ∈ psdCone d := by
  exact (mem_psd_iff_nonneg _).mpr (Finset.sum_nonneg fun i hi => (mem_psd_iff_nonneg _).mp (hA i hi))

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Sandwich
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section L2Operator

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

lemma sandwich_psd (A U : H d) (hU : U ∈ psdCone d) : sandwich A U ∈ psdCone d := by
  have hh := hU.mul_mul_conjTranspose_same (A : Mat d)
  rw [A.property.eq] at hh
  exact hh

end L2Operator

section Frobenius

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma inner_sandwich (A U P : H d) :
    inner ℝ P (sandwich A U) = inner ℝ (sandwich A P) U := by
  rw [inner_eq_trace, inner_eq_trace]
  change ((P : Mat d) * ((A : Mat d) * (U : Mat d) * (A : Mat d))).trace.re =
    ((A : Mat d) * (P : Mat d) * (A : Mat d) * (U : Mat d)).trace.re
  rw [← mul_assoc, ← mul_assoc, Matrix.trace_mul_comm ((P : Mat d) * (A : Mat d) * (U : Mat d))]
  simp only [mul_assoc]

end Frobenius

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Coordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.State.line_zero _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r89073a_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma eta_apply (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (Z : H d) :
    eta c A x Z = ∑ i, (c * psi (x i)) • sandwich (A i) Z := by
  simp [eta]

lemma psi_bounds {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ psi x ∧ psi x ≤ 1 := by
  have hr : 0 ≤ 1-x^2 := by have hh := abs_le.mp hx; nlinarith
  exact ⟨Real.rpow_nonneg hr _, Real.rpow_le_one hr (by nlinarith [sq_nonneg x]) (by norm_num)⟩

lemma eta_positive {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) {x : Coordinates N} (hx : Cube x) :
    ∀ Z ∈ psdCone d, eta c A x Z ∈ psdCone d := by
  intro Z hZ
  rw [eta_apply]
  exact psd_sum _ _ fun i _ => psd_smul (sandwich_psd _ _ hZ) (mul_nonneg hc (psi_bounds (hx i)).1)

lemma eta_symmetric (c : ℝ) (A : Fin N → H d) (x : Coordinates N) : SymmetricMap (eta c A x) := by
  intro U V
  change inner ℝ U (eta c A x V) = inner ℝ (eta c A x U) V
  simp only [eta_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (c*psi (x i)) * inner ℝ U (sandwich (A i) V) :=
      real_inner_smul_right U (sandwich (A i) V) (c*psi (x i))
    _ = (c*psi (x i)) * inner ℝ (sandwich (A i) U) V := by rw [inner_sandwich]
    _ = _ := (real_inner_smul_left (sandwich (A i) U) V (c*psi (x i))).symm

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_CoarseBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealSubtypeMatMemSubmoduleH_p0
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupVars
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealVars
attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH
lemma contDiff_S (A : Fin N → H d) {n : WithTop ℕ∞} : ContDiff ℝ n (S A) := by
  apply ContDiff.sum
  intro i _
  exact (contDiff_apply ℝ ℝ i).smul contDiff_const

lemma contDiffAt_eta (c : ℝ) (A : Fin N → H d) {x : Coordinates N}
    (hx : ∀ i, |x i| < 1) {n : WithTop ℕ∞} : ContDiffAt ℝ n (eta c A) x := by
  apply ContDiffAt.sum
  intro i _
  have hp : ContDiffAt ℝ n (fun y : Coordinates N => psi (y i)) x :=
    (contDiffAt_psi (hx i)).comp x (contDiffAt_apply ℝ ℝ i x)
  have hc : ContDiffAt ℝ n (fun _ : Coordinates N => c) x := contDiffAt_const
  exact (hc.mul hp).smul (show ContDiffAt ℝ n (fun _ : Coordinates N => sandwichCLM (A i)) x from contDiffAt_const)

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Line
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Scalar Filter
open scoped BigOperators Topology

variable {N : ℕ}

lemma hasDerivAt_line_coord (x h : Coordinates N) (a : ℝ) (i : Fin N) :
    HasDerivAt (fun s => line x h s i) (h i) a := by
  have hh := (hasDerivAt_const a (x i)).add ((hasDerivAt_id a).mul_const (h i))
  simp only [zero_add,one_mul] at hh
  exact hh

lemma contDiff_line (x h : Coordinates N) {n : WithTop ℕ∞} : ContDiff ℝ n (line x h) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.add (contDiff_id.mul contDiff_const)

lemma eventually_line_interior (x h : Coordinates N) {a : ℝ}
    (hx : ∀ i, |line x h a i| < 1) : ∀ᶠ s in 𝓝 a, ∀ i, |line x h s i| < 1 := by
  apply Filter.eventually_all.mpr
  intro i
  exact ((hasDerivAt_line_coord x h a i).continuousAt.abs).eventually (eventually_lt_nhds (hx i))

lemma contDiffAt_penalty {x : Coordinates N} (hx : ∀ i, |x i| < 1) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n penalty x := by
  apply ContDiffAt.sum
  intro i _
  exact (contDiffAt_psi (hx i)).comp x (contDiffAt_apply ℝ ℝ i x)

lemma hasDerivAt_penalty_line (x h : Coordinates N) (a : ℝ) (hx : ∀ i, |line x h a i| < 1) :
    HasDerivAt (fun s => penalty (line x h s)) (penalty₁ (line x h a) h) a := by
  apply HasDerivAt.fun_sum
  intro i _
  exact (hasDerivAt_psi (hx i)).comp a (hasDerivAt_line_coord x h a i)

lemma hasDerivAt_penalty₁_line (x h : Coordinates N) (a : ℝ) (hx : ∀ i, |line x h a i| < 1) :
    HasDerivAt (fun s => penalty₁ (line x h s) h) (penalty₂ (line x h a) h) a := by
  apply HasDerivAt.fun_sum
  intro i _
  convert ((hasDerivAt_psi₁ (hx i)).comp a (hasDerivAt_line_coord x h a i)).mul_const (h i) using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  ring

lemma penalty_line_first (x h : Coordinates N) (hx : ∀ i, |x i| < 1) :
    deriv (fun s => penalty (line x h s)) 0 = penalty₁ x h := by
  simpa only [line_zero] using (hasDerivAt_penalty_line x h 0 (by simpa only [line_zero] using hx)).deriv

lemma penalty_line_second (x h : Coordinates N) (hx : ∀ i, |x i| < 1) :
    deriv (deriv (fun s => penalty (line x h s))) 0 = penalty₂ x h := by
  have he : deriv (fun s => penalty (line x h s)) =ᶠ[𝓝 (0 : ℝ)] fun s => penalty₁ (line x h s) h := by
    filter_upwards [eventually_line_interior x h (a := 0) (by simpa only [line_zero] using hx)] with s hs
    exact (hasDerivAt_penalty_line x h s hs).deriv
  rw [he.deriv_eq]
  simpa only [line_zero] using (hasDerivAt_penalty₁_line x h 0 (by simpa only [line_zero] using hx)).deriv

lemma second_deriv_add {f g : ℝ → ℝ} {a : ℝ} (hf : ContDiffAt ℝ 2 f a) (hg : ContDiffAt ℝ 2 g a) :
    deriv (deriv (fun s => f s+g s)) a = deriv (deriv f) a+deriv (deriv g) a := by
  simpa only [show (2 : ℕ) = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using iteratedDeriv_fun_add hf hg

lemma second_deriv_const_mul (c : ℝ) (f : ℝ → ℝ) (a : ℝ) :
    deriv (deriv (fun s => c*f s)) a = c*deriv (deriv f) a := by
  simpa only [show (2 : ℕ) = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using
    (iteratedDeriv_const_mul_field (n := 2) (x := a) c f)

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_StatePsi
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction CurrentKS.Covariance
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ} (p : LightPoint d N)

lemma contDiffAt_R [NeZero d] : ContDiffAt ℝ ∞ p.R p.x := by
  exact contDiffAt_value p.ε p.ε_pos (fun y => p.fixedPart+S p.A y) (eta 384 p.A) p.x
    (contDiffAt_const.add (contDiff_S p.A).contDiffAt) (contDiffAt_eta 384 p.A p.interior)
    (eta_positive (by norm_num) p.A (fun i => (p.interior i).le))
    (Filter.Eventually.of_forall fun y => eta_symmetric 384 p.A y) p.lower p.upper
    p.primal p.feasible p.minimal

lemma contDiffAt_R_line [NeZero d] (h : Coordinates N) :
    ContDiffAt ℝ ∞ (fun s => p.R (line p.x h s)) 0 := by
  have hh : ContDiffAt ℝ ∞ p.R (line p.x h 0) := by simpa only [line_zero] using p.contDiffAt_R
  exact hh.comp 0 (contDiff_line p.x h).contDiffAt

lemma contDiffAt_penalty_line (h : Coordinates N) :
    ContDiffAt ℝ ∞ (fun s => penalty (line p.x h s)) 0 := by
  have hh : ContDiffAt ℝ ∞ penalty (line p.x h 0) := by
    simpa only [line_zero] using (contDiffAt_penalty p.interior : ContDiffAt ℝ ∞ penalty p.x)
  exact hh.comp 0 (contDiff_line p.x h).contDiffAt

lemma Psi_first [NeZero d] (lam : ℝ) (h : Coordinates N) :
    deriv (fun s => p.Psi lam (line p.x h s)) 0 =
      deriv (fun s => p.R (line p.x h s)) 0+lam*penalty₁ p.x h := by
  have hP := (p.contDiffAt_penalty_line h).differentiableAt (by norm_num)
  change deriv (fun s => p.R (line p.x h s)+lam*penalty (line p.x h s)) 0 = _
  have hd := (((p.contDiffAt_R_line h).differentiableAt (by norm_num)).hasDerivAt.add
    (hP.hasDerivAt.const_mul lam)).deriv
  change deriv (fun s => p.R (line p.x h s)+lam*penalty (line p.x h s)) 0 = _ at hd
  rw [hd,penalty_line_first p.x h p.interior]

lemma Psi_second [NeZero d] (lam : ℝ) (h : Coordinates N) :
    deriv (deriv (fun s => p.Psi lam (line p.x h s))) 0 =
      deriv (deriv (fun s => p.R (line p.x h s))) 0+lam*penalty₂ p.x h := by
  have hR : ContDiffAt ℝ 2 (fun s => p.R (line p.x h s)) 0 :=
    (p.contDiffAt_R_line h).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hP : ContDiffAt ℝ 2 (fun s => penalty (line p.x h s)) 0 :=
    (p.contDiffAt_penalty_line h).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  change deriv (deriv (fun s => p.R (line p.x h s)+lam*penalty (line p.x h s))) 0 = _
  rw [second_deriv_add hR (contDiffAt_const.mul hP),second_deriv_const_mul,
    penalty_line_second p.x h p.interior]

lemma Psi_driftCurvature_oai [NeZero d] (lam : ℝ) (Γ : Covariance.Mat (2*N)) :
    p.driftCurvature (p.Psi lam) Γ = p.driftCurvature p.R Γ+lam*p.driftCurvature penalty Γ := by
  dsimp only [driftCurvature]
  rw [p.Psi_first]
  simp_rw [p.Psi_second,penalty_line_first p.x (p.mu Γ) p.interior,penalty_line_second p.x _ p.interior]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  ring

end
end CurrentKS.State.LightPoint

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.State.LightPoint.Psi_driftCurvature_oai := @OAI.CurrentKS.State.LightPoint.Psi_driftCurvature_oai
