-- Prove2me | solution 1 for OAI.CurrentKS.State.LightPoint.shifted_hessian_not_psd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:40.355215+00:00
-- url     : https://prove2.me/submissions/549d6e73-17b3-46d1-b2a9-b6b9b525bcf2

import Mathlib
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_CurrentKS_State_LightPoint_exists_descent_ensemble
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

lemma contDiffAt_psi {x : ℝ} (hx : |x| < 1) {n : WithTop ℕ∞} : ContDiffAt ℝ n psi x := by
  exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (base_pos hx))).comp x
    (contDiffAt_const.sub (contDiffAt_id.pow 2))

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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r7691b8_1 : NormedSpace ℝ (H d) := inferInstance
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
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_DerivLine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference

section
open Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma deriv_line {f : E → ℝ} {x h : E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (x+t • h)) :
    deriv (fun s : ℝ => f (x+s • h)) t = fderiv ℝ f (x+t • h) h := by
  have hh : HasDerivAt (fun s : ℝ => x+s • h) h t := by
    have hh := ((hasDerivAt_id t).smul_const h).const_add x
    simp only [one_smul] at hh
    exact hh
  exact (hf.hasFDerivAt.comp_hasDerivAt t hh).deriv

lemma deriv_line_eventually {f : E → ℝ} {x h : E} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x+t • h)) :
    deriv (fun s : ℝ => f (x+s • h)) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ f (x+s • h) h) := by
  have hh : HasDerivAt (fun s : ℝ => x+s • h) h t := by
    have hh := ((hasDerivAt_id t).smul_const h).const_add x
    simp only [one_smul] at hh
    exact hh
  have he : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 2 f (x+s • h) :=
    (hf.eventually (by norm_num)).filter_mono hh.continuousAt
  filter_upwards [he] with s hs
  exact deriv_line (hs.differentiableAt (by norm_num))

lemma deriv_fderiv_line {f : E → ℝ} {x h : E} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x+t • h)) :
    deriv (fun s : ℝ => fderiv ℝ f (x+s • h) h) t =
      fderiv ℝ (fderiv ℝ f) (x+t • h) h h := by
  have hh : HasDerivAt (fun s : ℝ => x+s • h) h t := by
    have hh := ((hasDerivAt_id t).smul_const h).const_add x
    simp only [one_smul] at hh
    exact hh
  have hfdc : ContDiffAt ℝ 1 (fderiv ℝ f) (x+t • h) :=
    hf.fderiv_right (by norm_num)
  have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (x+t • h)) (x+t • h) :=
    (hfdc.differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasDerivAt (fun s : ℝ => fderiv ℝ f (x+s • h))
      (fderiv ℝ (fderiv ℝ f) (x+t • h) h) t := hfd.comp_hasDerivAt t hh
  have hd : HasDerivAt (fun s : ℝ => fderiv ℝ f (x+s • h) h)
      (fderiv ℝ (fderiv ℝ f) (x+t • h) h h+fderiv ℝ f (x+t • h) 0) t :=
    hc.clm_apply (hasDerivAt_const t h)
  simpa only [map_zero,add_zero] using hd.deriv

lemma second_deriv_line {f : E → ℝ} {x h : E} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x+t • h)) :
    deriv (deriv (fun s : ℝ => f (x+s • h))) t =
      fderiv ℝ (fderiv ℝ f) (x+t • h) h h := by
  exact (deriv_line_eventually hf).deriv_eq.trans (deriv_fderiv_line hf)

end

open scoped BigOperators

variable {N : ℕ}

lemma coordinate_expansion (x : Fin N → ℝ) : x = ∑ i, x i • (Pi.single i (1:ℝ) : Fin N → ℝ) := by
  classical
  ext j
  simp [Pi.single_apply,Finset.sum_apply]

lemma linear_coordinates (L : (Fin N → ℝ) →L[ℝ] ℝ) (x : Fin N → ℝ) :
    L x = ∑ i,x i*L (Pi.single i (1:ℝ)) := by
  conv_lhs => rw [coordinate_expansion x]
  simp only [map_sum,map_smul,smul_eq_mul]

lemma linear_coordinate_bound (L : (Fin N → ℝ) →L[ℝ] ℝ) (x : Fin N → ℝ)
    {a C : ℝ} (_ha : 0 ≤ a) (hC : 0 ≤ C) (hx : ∀ i,|x i| ≤ C)
    (hL : ∀ i,|L (Pi.single i (1:ℝ))| ≤ a) : |L x| ≤ (N:ℝ)*a*C := by
  rw [linear_coordinates]
  calc
    _ ≤ ∑ i,|x i*L (Pi.single i (1:ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin N,C*a := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hx i) (hL i) (abs_nonneg _) hC
    _ = (N:ℝ)*a*C := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] <;> ring

end CurrentKS.Difference

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

lemma contDiffAt_penalty {x : Coordinates N} (hx : ∀ i, |x i| < 1) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n penalty x := by
  apply ContDiffAt.sum
  intro i _
  exact (contDiffAt_psi (hx i)).comp x (contDiffAt_apply ℝ ℝ i x)

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_StateIA
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction
open CurrentKS.Covariance CurrentKS.Movement Matrix WithLp
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d N : ℕ} (p : LightPoint d N)

lemma C1_ge_one : (1 : ℝ) ≤ p.C1 := le_max_left ..
lemma C1_pos : 0 < p.C1 := lt_of_lt_of_le (by norm_num) p.C1_ge_one

end
end CurrentKS.State.LightPoint

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

end
end CurrentKS.State.LightPoint

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_EnsembleForcesNegative
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
open scoped BigOperators

variable {N K : ℕ}

theorem ensemble_forces_negative (L : (Fin N → ℝ) →L[ℝ] ℝ)
    (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ)
    (μ : Fin N → ℝ) (dirs : Fin K → Fin N → ℝ)
    (test : (Fin N → ℝ) → ℝ) {lam a C : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hC : 0 < C) (hrel : lam=512*a*C^2)
    (hμ : ∀ i,|μ i| ≤ C) (hdirs : (∑ j,∑ i,dirs j i^2) ≤ 8*C*N)
    (hprogress : L μ+(1/2:ℝ)*(∑ j,B (dirs j) (dirs j)) ≤ -lam*N/(8*C))
    (hgrad : ∀ i,|L (Pi.single i (1:ℝ))| ≤ a)
    (herr : ∀ u,|test u-B u u| ≤ a/16*(∑ i,u i^2)) :
    ¬∀ u,test u+7*a*(∑ i,u i^2) ≥ 0 := by
  intro hpsd
  have hlinear := (abs_le.mp (linear_coordinate_bound L μ ha.le hC.le hμ hgrad)).1
  have hi (j : Fin K) : -((113/16:ℝ)*a)*(∑ i,dirs j i^2) ≤ B (dirs j) (dirs j) := by
    have he := (abs_le.mp (herr (dirs j))).2
    have hp := hpsd (dirs j)
    linarith
  have hsum := Finset.sum_le_sum (fun (j : Fin K) (_ : j ∈ Finset.univ) => hi j)
  rw [← Finset.mul_sum] at hsum
  have hh := mul_le_mul_of_nonneg_left hdirs (show 0≤(113/16:ℝ)*a by positivity)
  have he : -lam*(N:ℝ)/(8*C) = -64*a*C*N := by rw [hrel];field_simp <;> ring
  rw [he] at hprogress
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hp : 0<a*C*(N:ℝ) := by positivity
  nlinarith

end CurrentKS.Difference

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Difference
open scoped BigOperators Topology ContDiff

variable {d N : ℕ} (p : LightPoint d N)

lemma contDiffAt_Psi_two [NeZero d] (lam : ℝ) : ContDiffAt ℝ 2 (p.Psi lam) p.x := by
  exact p.contDiffAt_R.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)) |>.add
    (contDiffAt_const.mul (contDiffAt_penalty p.interior))

lemma Psi_deriv_coordinates [NeZero d] (lam : ℝ) (h : Coordinates N) :
    deriv (fun s => p.Psi lam (line p.x h s)) 0 = fderiv ℝ (p.Psi lam) p.x h := by
  have hf : DifferentiableAt ℝ (p.Psi lam) (p.x+(0:ℝ) • h) := by
    simpa only [zero_smul,add_zero] using (p.contDiffAt_Psi_two lam).differentiableAt (by norm_num)
  have hh := deriv_line (x:=p.x) (h:=h) (t:=0) hf
  simp only [zero_smul,add_zero] at hh
  exact hh

lemma Psi_second_coordinates [NeZero d] (lam : ℝ) (h : Coordinates N) :
    deriv (deriv (fun s => p.Psi lam (line p.x h s))) 0 =
      fderiv ℝ (fderiv ℝ (p.Psi lam)) p.x h h := by
  have hf : ContDiffAt ℝ 2 (p.Psi lam) (p.x+(0:ℝ) • h) := by
    simpa only [zero_smul,add_zero] using p.contDiffAt_Psi_two lam
  have hh := second_deriv_line (x:=p.x) (h:=h) (t:=0) hf
  simp only [zero_smul,add_zero] at hh
  exact hh

theorem shifted_hessian_not_psd_oai [NeZero d] [NeZero N] {lam a : ℝ}
    (ha : 0 < a) (hrel : lam=512*a*p.C1^2)
    (test : Coordinates N → ℝ)
    (hgrad : ∀ i,|fderiv ℝ (p.Psi lam) p.x (Pi.single i (1:ℝ))| ≤ a)
    (herr : ∀ u,|test u-fderiv ℝ (fderiv ℝ (p.Psi lam)) p.x u u| ≤ a/16*(∑ i,u i^2)) :
    ¬∀ u,test u+7*a*(∑ i,u i^2) ≥ 0 := by
  have hlam : 0 ≤ lam := by rw [hrel];positivity
  obtain ⟨Γ,_,hμ,hdirs,hprogress⟩ := p.exists_descent_ensemble lam hlam
  have he : p.driftCurvature (p.Psi lam) Γ =
      fderiv ℝ (p.Psi lam) p.x (p.mu Γ)+(1/2:ℝ)*
        (∑ j,fderiv ℝ (fderiv ℝ (p.Psi lam)) p.x (p.dirs Γ j) (p.dirs Γ j)) := by
    unfold driftCurvature
    simp_rw [p.Psi_deriv_coordinates,p.Psi_second_coordinates]
  rw [he] at hprogress
  exact ensemble_forces_negative (fderiv ℝ (p.Psi lam) p.x)
    (fderiv ℝ (fderiv ℝ (p.Psi lam)) p.x) (p.mu Γ) (p.dirs Γ) test
    (NeZero.pos N) ha p.C1_pos hrel hμ hdirs hprogress hgrad herr

end
end CurrentKS.State.LightPoint

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.State.LightPoint.shifted_hessian_not_psd_oai := @OAI.CurrentKS.State.LightPoint.shifted_hessian_not_psd_oai
