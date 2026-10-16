-- Prove2me | solution 1 for OAI.GAD.sequential_decoder_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:51:30.587981+00:00
-- url     : https://prove2.me/submissions/68592a22-2090-45d1-8e86-8a011cdff195

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/SequentialDecoder.lean:L105-L160
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.sequential_decoder_bound. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseProducts
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CapacityConverse
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalSets
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalProjectors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialDecoder
import Theorems.Thm_OAI_GAD_frobVector_inner
import Theorems.Thm_OAI_GAD_projected_self_failure
import Theorems.Thm_OAI_GAD_sequential_projector_success
import Theorems.Thm_OAI_GAD_spectralFactor_gram

-- ---- from OAI.InformationTheory.AmplitudeDamping.GramMatrices ----
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
open scoped BigOperators ComplexOrder MatrixOrder Topology

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} {μ : Type u_3} {ν : Type u_4} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

omit [DecidableEq ι] [DecidableEq κ] in
theorem mass_nonneg (A : Matrix ι κ ℂ) : 0 ≤ mass A :=
  (Complex.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose A).trace_nonneg).1

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_5} [Fintype ι] [DecidableEq ι]

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

theorem mass_eq_sum_normSq (A : Matrix ι κ ℂ) : mass A=∑ i, ∑ k, Complex.normSq (A i k) := by
  simp [mass,gram,Matrix.trace,Matrix.mul_apply,Complex.mul_conj]

theorem frobVector_norm (A : Matrix ι κ ℂ) : ‖frobVector A‖^2=mass A := by
  rw [EuclideanSpace.norm_sq_eq,mass_eq_sum_normSq]
  simp only [Fintype.sum_prod_type,frobVector,PiLp.toLp_apply,Complex.sq_norm]

omit [Fintype ι] [Fintype κ] in
theorem frobVector_add (A B : Matrix ι κ ℂ) : frobVector (A+B)=frobVector A+frobVector B := rfl
omit [Fintype ι] [Fintype κ] in
theorem frobVector_sub (A B : Matrix ι κ ℂ) : frobVector (A-B)=frobVector A-frobVector B := rfl

variable [DecidableEq ι]

omit [DecidableEq ι] in
theorem IsProjection.posSemidef {P : Matrix ι ι ℂ} (hP : IsProjection P) : P.PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose P
  rwa [hP.1.eq,hP.2] at h

theorem IsProjection.complement {P : Matrix ι ι ℂ} (hP : IsProjection P) : IsProjection (1-P) := by
  refine ⟨(Matrix.isHermitian_one).sub hP.1, ?_⟩
  rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,hP.2]
  simp

omit [DecidableEq ι] in
theorem projection_orthogonal {P : Matrix ι ι ℂ} (hP : IsProjection P) (A B : Matrix ι κ ℂ) :
    ⟪frobVector (P*A),frobVector (B-P*B)⟫_ℝ=0 := by
  rw [frobVector_inner,Matrix.conjTranspose_mul,hP.1.eq,Matrix.mul_sub]
  have he : Aᴴ*P*(P*B)=Aᴴ*P*B := by
    rw [← Matrix.mul_assoc _ P,Matrix.mul_assoc Aᴴ P P,hP.2]
  rw [he,sub_self,Matrix.trace_zero,Complex.zero_re]

omit [DecidableEq ι] in
theorem projection_mass_decomposition {P : Matrix ι ι ℂ} (hP : IsProjection P) (A : Matrix ι κ ℂ) :
    mass (P*A)+mass (A-P*A)=mass A := by
  have h := norm_add_sq_real (frobVector (P*A)) (frobVector (A-P*A))
  rw [← frobVector_add,projection_orthogonal hP A A,mul_zero,add_zero] at h
  have he : P*A+(A-P*A)=A := by abel
  rw [he,frobVector_norm,frobVector_norm,frobVector_norm] at h
  linarith

end

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_3} [Fintype ι] [DecidableEq ι]

end

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_4} {κ : Type u_5} [Fintype ι] [Fintype κ]

variable [DecidableEq ι]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_6} {κ : Type u_7} [Fintype ι] [Fintype κ]

theorem projection_inner {P : Matrix ι ι ℂ} (hP : IsProjection P) (X : Matrix ι κ ℂ) :
    ⟪frobVector X,frobVector (P*X)⟫_ℝ=mass (P*X) := by
  have h := projection_orthogonal hP X X
  rw [frobVector_sub,inner_sub_right,real_inner_self_eq_norm_sq,
    frobVector_norm,real_inner_comm] at h
  linarith

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.BlockFactors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_8} [Fintype ι] [DecidableEq ι]

theorem trace_product_nonneg {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A*B).trace.re := by
  let L := spectralFactor hB
  have hL : L*Lᴴ=B := spectralFactor_gram hB
  have h := (hA.conjTranspose_mul_mul_same L).trace_nonneg
  rw [Matrix.trace_mul_cycle] at h
  rw [hL] at h
  simpa only [Matrix.trace_mul_comm B A] using (Complex.nonneg_iff.mp h).1

theorem trace_product_mono {P A B : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (hAB : (B-A).PosSemidef) : (P*A).trace.re ≤ (P*B).trace.re := by
  have h := trace_product_nonneg hP hAB
  simpa only [Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re,sub_nonneg] using h

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.SequentialMatrices ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι]

theorem rejectProduct_loss (Q : ℕ → Matrix ι ι ℂ) (hQ : ∀ k, IsProjection (Q k)) (k : ℕ) :
    (rejectProduct Q k)ᴴ*rejectProduct Q k-
      (rejectProduct Q (k+1))ᴴ*rejectProduct Q (k+1)=
      (rejectProduct Q k)ᴴ*Q k*rejectProduct Q k := by
  rw [rejectProduct,Matrix.conjTranspose_mul,(hQ k).complement.1.eq]
  have he : (rejectProduct Q k)ᴴ*(1-Q k)*((1-Q k)*rejectProduct Q k)=
      (rejectProduct Q k)ᴴ*(1-Q k)*rejectProduct Q k := by
    rw [← Matrix.mul_assoc _ (1-Q k),Matrix.mul_assoc (rejectProduct Q k)ᴴ,
      (hQ k).complement.2]
  rw [he,Matrix.mul_sub,Matrix.mul_one,Matrix.sub_mul]
  abel

theorem rejectProduct_sum (Q : ℕ → Matrix ι ι ℂ) (hQ : ∀ k, IsProjection (Q k)) (n : ℕ) :
    (∑ k ∈ Finset.range n, (rejectProduct Q k)ᴴ*Q k*rejectProduct Q k)=
      1-(rejectProduct Q n)ᴴ*rejectProduct Q n := by
  simp_rw [← rejectProduct_loss Q hQ]
  rw [Finset.sum_range_sub']
  simp [rejectProduct]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.TypicalProjectors ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem projection_gram_mass {ι : Type u_2} {κ : Type u_3} [Fintype ι] [Fintype κ]
    {P : Matrix ι ι ℂ} (hP : IsProjection P) (F : Matrix ι κ ℂ) :
    mass (P*F)=(P*gram F).trace.re := by
  rw [← projection_inner hP F,frobVector_inner]
  dsimp [gram]
  rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle,Matrix.trace_mul_comm (F*Fᴴ)]

variable {ι : Type u_4} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.SequentialDecoder ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_1

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem finiteProjectors_projection {M : ℕ} (Q : Fin M → Matrix ι ι ℂ)
    (hQ : ∀ m, IsProjection (Q m)) (k : ℕ) : IsProjection (finiteProjectors Q k) := by
  dsimp [finiteProjectors]
  split_ifs with h
  · exact hQ _
  · exact ⟨Matrix.isHermitian_zero, Matrix.zero_mul _⟩

omit [Fintype ι] [DecidableEq ι] in
theorem finiteProjectors_apply {M : ℕ} (Q : Fin M → Matrix ι ι ℂ) (m : Fin M) :
    finiteProjectors Q m=Q m := by simp [finiteProjectors,m.isLt]

theorem sequentialMeasurement_pos {M : ℕ} (P : Matrix ι ι ℂ) (Q : Fin M → Matrix ι ι ℂ)
    (hQ : ∀ m, IsProjection (Q m)) (m : Fin M) : (sequentialMeasurement P Q m).PosSemidef :=
  (hQ m).posSemidef.conjTranspose_mul_mul_same _

theorem sequentialMeasurement_sum {M : ℕ} (P : Matrix ι ι ℂ) (hP : IsProjection P)
    (Q : Fin M → Matrix ι ι ℂ) (hQ : ∀ m, IsProjection (Q m)) :
    (∑ m, sequentialMeasurement P Q m)=
      P-P*(rejectProduct (finiteProjectors Q) M)ᴴ*rejectProduct (finiteProjectors Q) M*P := by
  let R := rejectProduct (finiteProjectors Q)
  have he : (∑ m, sequentialMeasurement P Q m)=
      P*(∑ m : Fin M, (R m)ᴴ*finiteProjectors Q m*R m)*P := by
    simp only [Matrix.mul_sum,Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [finiteProjectors_apply,sequentialMeasurement,Matrix.conjTranspose_mul,hP.1.eq]
    simp only [Matrix.mul_assoc,R]
  rw [he,Fin.sum_univ_eq_sum_range (fun k ↦ (R k)ᴴ*finiteProjectors Q k*R k) M]
  have ht := rejectProduct_sum (finiteProjectors Q) (finiteProjectors_projection Q hQ) M
  dsimp only [R]
  rw [ht,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hP.2]
  simp only [Matrix.mul_assoc]

theorem sequentialMeasurement_remainder {M : ℕ} (P : Matrix ι ι ℂ) (hP : IsProjection P)
    (Q : Fin M → Matrix ι ι ℂ) (hQ : ∀ m, IsProjection (Q m)) :
    (1-∑ m, sequentialMeasurement P Q m).PosSemidef := by
  rw [sequentialMeasurement_sum P hP Q hQ]
  have he : 1-(P-P*(rejectProduct (finiteProjectors Q) M)ᴴ*rejectProduct (finiteProjectors Q) M*P)=
      (1-P)+(rejectProduct (finiteProjectors Q) M*P)ᴴ*(rejectProduct (finiteProjectors Q) M*P) := by
    rw [Matrix.conjTranspose_mul,hP.1.eq]
    simp only [← Matrix.mul_assoc]
    abel
  rw [he]
  exact hP.complement.posSemidef.add (Matrix.posSemidef_conjTranspose_mul_self _)

omit [Fintype ι] in
theorem complete_submeasurement {M : ℕ} (hM : 0 < M) (D : Fin M → Matrix ι ι ℂ)
    (hD : ∀ m, (D m).PosSemidef) (hR : (1-∑ m, D m).PosSemidef) :
    ∃ E : Fin M → Matrix ι ι ℂ, (∀ m, (E m).PosSemidef) ∧ (∑ m, E m=1) ∧
      (∀ m, (E m-D m).PosSemidef) := by
  let m0 : Fin M := ⟨0,hM⟩
  let R := 1-∑ m, D m
  let E := fun m ↦ D m+if m=m0 then R else 0
  refine ⟨E,?_,?_,?_⟩
  · intro m
    dsimp [E]
    split_ifs
    · exact (hD m).add hR
    · simpa only [add_zero] using hD m
  · dsimp [E]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    dsimp [R]
    abel
  · intro m
    dsimp [E]
    split_ifs
    · convert hR using 1; dsimp [R]; abel
    · simp only [add_zero,sub_self]; exact Matrix.PosSemidef.zero

theorem sequentialMeasurement_success {M : ℕ} (P : Matrix ι ι ℂ) (Q : Fin M → Matrix ι ι ℂ)
    (hQ : ∀ m, IsProjection (Q m)) (F : Matrix ι ι ℂ) (m : Fin M) :
    (sequentialMeasurement P Q m*gram F).trace.re=
      mass (Q m*rejectProduct (finiteProjectors Q) m*P*F) := by
  have he : Q m*rejectProduct (finiteProjectors Q) m*P*F=
      Q m*((rejectProduct (finiteProjectors Q) m*P)*F) := by simp only [Matrix.mul_assoc]
  rw [he,← projection_inner (hQ m),frobVector_inner]
  have ht := Matrix.trace_mul_cycle
    ((rejectProduct (finiteProjectors Q) m*P)ᴴ*Q m*(rejectProduct (finiteProjectors Q) m*P)) F Fᴴ
  simpa only [sequentialMeasurement,gram,Matrix.conjTranspose_mul,Matrix.mul_assoc] using congrArg Complex.re ht

/-- Sequential decoding preceded by a global typical-subspace test. -/
theorem sequential_decoder_bound {M : ℕ} (hM : 0 < M) (P : Matrix ι ι ℂ) (hP : IsProjection P)
    (Q A : Fin M → Matrix ι ι ℂ) (hQ : ∀ m, IsProjection (Q m)) (hA : ∀ m, IsState (A m)) :
    ∃ D : Fin M → Matrix ι ι ℂ, (∀ m, (D m).PosSemidef) ∧ (∑ m, D m=1) ∧
      ∀ m, 1-(D m*A m).trace.re ≤
        9*(1-(P*A m).trace.re)+8*(1-(Q m*A m).trace.re)+
          4*∑ j : Fin M, if j=m then 0 else (Q j*(P*A m*P)).trace.re := by
  obtain ⟨D,hD,hDs,hDb⟩ := complete_submeasurement hM (sequentialMeasurement P Q)
    (sequentialMeasurement_pos P Q hQ) (sequentialMeasurement_remainder P hP Q hQ)
  refine ⟨D,hD,hDs,fun m ↦ ?_⟩
  let F := spectralFactor (hA m).1
  have hF : gram F=A m := spectralFactor_gram (hA m).1
  have hmF : mass F=1 := by dsimp [mass]; rw [hF,(hA m).2]; rfl
  have hb := sequential_projector_success (finiteProjectors Q) (finiteProjectors_projection Q hQ) (P*F) m
  rw [finiteProjectors_apply] at hb
  have hself := projected_self_failure (P := P) (hQ m) F
  have hfailP := projection_mass_decomposition hP F
  have hfailQ := projection_mass_decomposition (hQ m) F
  rw [projection_gram_mass hP F,hF] at hfailP
  rw [projection_gram_mass (hQ m) F,hF] at hfailQ
  have hcross : (∑ j ∈ Finset.range (m:ℕ), mass (finiteProjectors Q j*(P*F))) ≤
      ∑ j : Fin M, if j=m then 0 else (Q j*(P*A m*P)).trace.re := by
    have hgp : gram (P*F)=P*A m*P := by
      dsimp only [gram]
      rw [Matrix.conjTranspose_mul,hP.1.eq,← Matrix.mul_assoc,Matrix.mul_assoc P F Fᴴ]
      change P*gram F*P=P*A m*P
      rw [hF]
    calc
      _ = ∑ j ∈ Finset.range (m:ℕ), if j=(m:ℕ) then 0 else mass (finiteProjectors Q j*(P*F)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
      _ ≤ ∑ j ∈ Finset.range M, if j=(m:ℕ) then 0 else mass (finiteProjectors Q j*(P*F)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono m.isLt.le)
        intro j _ _
        split_ifs
        · exact le_rfl
        · exact mass_nonneg _
      _ = _ := by
        rw [← Fin.sum_univ_eq_sum_range (fun j ↦ if j=(m:ℕ) then 0 else mass (finiteProjectors Q j*(P*F))) M]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j=m
        · subst j; simp
        · have hjv : (j:ℕ) ≠ (m:ℕ) := by intro h; exact hj (Fin.ext h)
          rw [ite_eq_right hjv,ite_eq_right hj,finiteProjectors_apply,projection_gram_mass (hQ j),hgp]

  have hsucc := sequentialMeasurement_success P Q hQ F m
  rw [hF] at hsucc
  have hmono := trace_product_mono (hA m).1 (hDb m)
  rw [Matrix.trace_mul_comm (A m) (sequentialMeasurement P Q m),Matrix.trace_mul_comm (A m) (D m)] at hmono
  rw [hsucc] at hmono
  have hpm : mass (P*F)=(P*A m).trace.re := by rw [projection_gram_mass hP,hF]
  rw [hmF] at hfailP hfailQ
  rw [← Matrix.mul_assoc (Q m*rejectProduct (finiteProjectors Q) m) P F] at hb
  linarith

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.sequential_decoder_bound := @_root_.OAI.GAD.sequential_decoder_bound
