-- Prove2me | solution 1 for OAI.GAD.orthogonal_factor_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:20:17.283984+00:00
-- url     : https://prove2.me/submissions/534fd9a4-c252-47dd-b4b7-97e9b947e43a

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/Naimark.lean:L119-L140
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.orthogonal_factor_entropy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark
import Theorems.Thm_OAI_GAD_entropy_blockDiagonal
import Theorems.Thm_OAI_GAD_entropy_le_of_logDetShift_le

-- ---- from OAI.InformationTheory.AmplitudeDamping.SpectralEntropy ----
namespace OAI

universe u_1

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- Trace invariance under a unitary change of basis. -/
theorem trace_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp

/-- Spectral trace for any function on the finite real spectrum. -/
theorem trace_cfc_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, trace_unitary_conj]
  simp [Matrix.trace_diagonal, Function.comp_def]

theorem entropy_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  simp [entropy, trace_cfc_eq hA]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.LogDetEntropy ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder

open scoped BigOperators Topology
open Filter Set
namespace GAD

end GAD

open scoped BigOperators ComplexOrder MatrixOrder Topology
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

theorem entropy_eq_of_logDetShift_eq {κ : Type u_4} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace.re = B.trace.re)
    (hlog : ∀ r : ℝ, 0 < r → logDetShift r A = logDetShift r B) :
    entropy A = entropy B :=
  le_antisymm (entropy_le_of_logDetShift_le hA hB htrace (fun r hr ↦ (hlog r hr).le))
    (entropy_le_of_logDetShift_le hB hA htrace.symm (fun r hr ↦ (hlog r hr).ge))

/-- Nonzero spectra, including their entropy, agree for both rectangular Gram matrices. -/
theorem entropy_mul_conjTranspose {κ : Type u_5} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) : entropy (A * Aᴴ) = entropy (Aᴴ * A) := by
  apply entropy_eq_of_logDetShift_eq (Matrix.posSemidef_self_mul_conjTranspose A)
    (Matrix.posSemidef_conjTranspose_mul_self A)
  · exact congrArg Complex.re (Matrix.trace_mul_comm A Aᴴ)
  · intro r _
    dsimp only [logDetShift]
    congr 2
    simpa only [Matrix.smul_mul, Matrix.mul_smul] using
      Matrix.det_one_add_mul_comm (r • A) Aᴴ

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.ZeroBlockEntropy ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_8} {μ : Type u_9} {ν : Type u_10} [Fintype ι] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_11} {κ : Type u_12} {μ : Type u_13} {ν : Type u_14} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

end GAD
open scoped BigOperators ComplexOrder
open Matrix
namespace GAD
variable {ι : Type u_19} [Fintype ι] [DecidableEq ι]

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

section
variable {ι : Type u_20} {μ : Type u_21} {ν : Type u_22} [Fintype ι] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]

end

section
variable {ι : Type u_23} {κ : Type u_24} {μ : Type u_25} {ν : Type u_26} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

end

section
variable {ι : Type u_27} {κ : Type u_28} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem entropy_smul (a : ℝ) {P : Matrix ι ι ℂ} (hP : P.IsHermitian) :
    entropy (a • P) = a * entropy P + Real.negMulLog a * P.trace.re := by
  rw [entropy, ← cfc_comp_smul a Real.negMulLog P, trace_cfc_eq hP]
  simp only [smul_eq_mul, Complex.re_sum, Complex.ofReal_re,
    Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← entropy_eq_sum hP]
  rw [hP.trace_eq_sum_eigenvalues]
  simp
  ring

end

variable {ι : Type u_29} {κ : Type u_30} {μ : Type u_31} {ν : Type u_32} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.EntropyContinuity ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace GAD

section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]

variable [DecidableEq ι]

end

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_3} [Fintype ι] [DecidableEq ι]

end

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_4} {κ : Type u_5} [Fintype ι] [Fintype κ]

theorem gram_posSemidef (A : Matrix ι κ ℂ) : (gram A).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose A

theorem gram_trace (A : Matrix ι κ ℂ) : (gram A).trace=(mass A:ℂ) := by
  exact Complex.ext (by rfl) (by simpa using (Complex.nonneg_iff.mp (gram_posSemidef A).trace_nonneg).2.symm)

variable [DecidableEq ι]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_6} {κ : Type u_7} [Fintype ι] [Fintype κ]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.BlockFactors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

section
variable {ι : Type u_1} {μ : Type u_2} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

end

variable {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq μ]

omit [Fintype κ] in
theorem blockProjection_mul (m : μ) (X : Matrix (ι × μ) κ ℂ) (ia : ι × μ) (j : κ) :
    (blockProjection (ι := ι) m*X) ia j=if ia.2=m then X ia j else 0 := by
  simp [blockProjection,Matrix.diagonal_mul]

omit [Fintype κ] [Fintype μ] in
theorem blockInjection_mul (m : μ) (X : Matrix ι κ ℂ) (ia : ι × μ) (j : κ) :
    (blockInjection (ι := ι) m*X) ia j=if ia.2=m then X ia.1 j else 0 := by
  simp [blockInjection,Matrix.mul_apply,ite_mul]

theorem blockInjection_isometry (m : μ) :
    (blockInjection (ι := ι) m)ᴴ*blockInjection (ι := ι) m=1 := by
  ext i j
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.conjTranspose_apply,blockInjection]
  simp [Matrix.one_apply,eq_comm]

omit [Fintype κ] in
theorem blockProjection_range {m : μ} {X : Matrix (ι × μ) κ ℂ}
    (hX : blockProjection (ι := ι) m*X=X) : blockInjection (ι := ι) m*(show Matrix ι κ ℂ from fun i j ↦ X (i,m) j)=X := by
  ext ia j
  have h := congrArg (fun A : Matrix (ι × μ) κ ℂ ↦ A ia j) hX
  rw [blockProjection_mul] at h
  rw [blockInjection_mul]
  split_ifs with hm
  · cases ia with | mk i a => change a=m at hm; subst a; rfl
  · simpa only [ite_eq_right hm] using h

theorem mass_isometry {ρ : Type u_6} [Fintype ρ] (W : Matrix ρ ι ℂ)
    (hW : Wᴴ*W=1) (X : Matrix ι κ ℂ) : mass (W*X)=mass X := by
  dsimp [mass,gram]
  rw [Matrix.conjTranspose_mul,Matrix.trace_mul_comm]
  have h : Xᴴ*Wᴴ*(W*X)=Xᴴ*X := by
    rw [← Matrix.mul_assoc _ W,Matrix.mul_assoc Xᴴ, hW,Matrix.mul_one]
  rw [h,Matrix.trace_mul_comm]

theorem entropy_gram_isometry {ρ : Type u_7} [Fintype ρ] [DecidableEq ρ] [DecidableEq κ]
    (W : Matrix ρ ι ℂ) (hW : Wᴴ*W=1) (X : Matrix ι κ ℂ) :
    entropy (gram (W*X))=entropy (gram X) := by
  change entropy ((W*X)*(W*X)ᴴ)=entropy (X*Xᴴ)
  rw [entropy_mul_conjTranspose,entropy_mul_conjTranspose X,Matrix.conjTranspose_mul]
  congr 1
  rw [← Matrix.mul_assoc _ W,Matrix.mul_assoc Xᴴ,hW,Matrix.mul_one]

theorem block_factor_entropy [DecidableEq κ] (m : μ) (X : Matrix ι κ ℂ) :
    entropy (gram (blockInjection (ι := ι) m*X))=entropy (gram X) :=
  entropy_gram_isometry _ (blockInjection_isometry m) X

omit [Fintype μ] in
theorem gram_blockInjection (m : μ) (X : Matrix ι κ ℂ) (ia jb : ι × μ) :
    gram (blockInjection (ι := ι) m*X) ia jb=
      if ia.2=m ∧ jb.2=m then gram X ia.1 jb.1 else 0 := by
  change (∑ k, (blockInjection (ι := ι) m*X) ia k*star ((blockInjection (ι := ι) m*X) jb k)) = _
  simp only [blockInjection_mul]
  by_cases hi : ia.2=m <;> by_cases hj : jb.2=m <;>
    simp [hi,hj,gram,Matrix.mul_apply,Matrix.conjTranspose_apply]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_8} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.Naimark ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {μ : Type u_2} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} [Fintype ι] [Fintype κ] [Fintype μ]

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

theorem orthogonal_factor_entropy (w : μ → ℝ) (Y : μ → Matrix (ι × μ) κ ℂ)
    (hY : ∀ m, mass (Y m)=1) (hPY : ∀ m, blockProjection (ι := ι) m*Y m=Y m) :
    entropy (∑ m, w m • gram (Y m))=
      ∑ m, (w m*entropy (gram (Y m))+Real.negMulLog (w m)) := by
  let Z : μ → Matrix ι κ ℂ := fun m i k ↦ Y m (i,m) k
  have hZ (m : μ) : blockInjection (ι := ι) m*Z m=Y m := blockProjection_range (hPY m)
  have hmZ (m : μ) : mass (Z m)=1 := by
    rw [← mass_isometry _ (blockInjection_isometry m),hZ,hY]
  have he : (∑ m, w m • gram (Y m))=Matrix.blockDiagonal (fun m ↦ w m • gram (Z m)) := by
    ext ia jb
    simp only [Matrix.sum_apply,Matrix.smul_apply,← hZ,gram_blockInjection,Matrix.blockDiagonal_apply]
    by_cases h : ia.2=jb.2
    · simp only [h,and_self]
      simp
    · have hf (m : μ) : ¬(ia.2=m ∧ jb.2=m) := by intro hm; exact h (hm.1.trans hm.2.symm)
      simp [hf,h]
  rw [he,entropy_blockDiagonal _ (fun m ↦ (gram_posSemidef (Z m)).isHermitian.smul (IsSelfAdjoint.all (w m)))]
  apply Finset.sum_congr rfl
  intro m _
  rw [entropy_smul _ (gram_posSemidef (Z m)).isHermitian,gram_trace,hmZ]
  simp only [Complex.ofReal_one,Complex.one_re,mul_one]
  rw [← hZ,block_factor_entropy]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.orthogonal_factor_entropy := @_root_.OAI.GAD.orthogonal_factor_entropy
