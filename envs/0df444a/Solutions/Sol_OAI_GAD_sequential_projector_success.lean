-- Prove2me | solution 1 for OAI.GAD.sequential_projector_success
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:42:24.526794+00:00
-- url     : https://prove2.me/submissions/97f9a476-3400-4cbb-931a-f1b7b0ca9884

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/SequentialMatrices.lean:L62-L92
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.sequential_projector_success. The node keeps its source
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
import Theorems.Thm_OAI_GAD_frobVector_inner
import Theorems.Thm_OAI_GAD_sequential_union_bound

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
theorem frobVector_sub (A B : Matrix ι κ ℂ) : frobVector (A-B)=frobVector A-frobVector B := rfl

variable [DecidableEq ι]

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

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.SequentialMatrices ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_1 u_2

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι]

omit [Fintype κ] [DecidableEq ι] in
theorem projectionAction_frob (P : Matrix ι ι ℂ) (X : Matrix ι κ ℂ) :
    projectionAction P (frobVector X)=frobVector (P*X) := rfl

omit [DecidableEq ι] in
theorem projectionAction_orthogonal {P : Matrix ι ι ℂ} (hP : IsProjection P)
    (v w : EuclideanSpace ℂ (ι × κ)) :
    ⟪projectionAction P v,w-projectionAction P w⟫_ℝ=0 := by
  exact projection_orthogonal hP (fun i k ↦ v (i,k)) (fun i k ↦ w (i,k))

omit [DecidableEq ι] in
theorem matrix_sequential_union_bound (P : ℕ → Matrix ι ι ℂ) (hP : ∀ i, IsProjection (P i))
    (X : ℕ → Matrix ι κ ℂ) (hX : ∀ i, X (i+1)=P i*X i) (n : ℕ) :
    mass (X 0)-mass (X n) ≤ 4*∑ i ∈ Finset.range n, mass (X 0-P i*X 0) := by
  have h := sequential_union_bound (fun i ↦ projectionAction (P i))
    (fun i ↦ projectionAction_orthogonal (hP i)) (fun i ↦ frobVector (X i))
    (fun i ↦ by rw [hX]; rfl) n
  simpa only [projectionAction_frob,← frobVector_sub,frobVector_norm] using h

theorem sequential_projector_success (Q : ℕ → Matrix ι ι ℂ)
    (hQ : ∀ k, IsProjection (Q k)) (Y : Matrix ι κ ℂ) (m : ℕ) :
    mass Y-mass (Q m*rejectProduct Q m*Y) ≤
      4*(mass (Y-Q m*Y)+∑ j ∈ Finset.range m, mass (Q j*Y)) := by
  let P : ℕ → Matrix ι ι ℂ := fun k ↦ if k=m then Q m else 1-Q k
  have hp (k : ℕ) : IsProjection (P k) := by
    dsimp [P]; split_ifs
    · exact hQ m
    · exact (hQ k).complement
  -- Only the first m+1 recurrence steps matter; use a genuine recursively defined sequence.
  let Z : ℕ → Matrix ι κ ℂ := fun k ↦ Nat.rec Y (fun j A ↦ P j*A) k
  have hz (k : ℕ) : Z (k+1)=P k*Z k := rfl
  have hZ (k : ℕ) (hk : k ≤ m) : Z k=rejectProduct Q k*Y := by
    induction k with
    | zero => simp [Z,rejectProduct]
    | succ k ih =>
      rw [hz,ih (by omega)]
      have hkm : k ≠ m := by omega
      simp only [P,ite_eq_right hkm,rejectProduct,Matrix.mul_assoc]
  have hZend : Z (m+1)=Q m*rejectProduct Q m*Y := by
    rw [hz,hZ m le_rfl]; simp only [P,ite_eq_left rfl,Matrix.mul_assoc]
  have h := matrix_sequential_union_bound P hp Z hz (m+1)
  have hZ0 : Z 0=Y := rfl
  rw [hZ0,hZend,Finset.sum_range_succ] at h
  have hs : (∑ j ∈ Finset.range m, mass (Y-P j*Y))=∑ j ∈ Finset.range m, mass (Q j*Y) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j ≠ m := by have := Finset.mem_range.mp hj; omega
    simp only [P,ite_eq_right hjm,Matrix.sub_mul,Matrix.one_mul,sub_sub_cancel]
  rw [hs] at h
  simpa only [P,ite_eq_left rfl,add_comm] using h

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.sequential_projector_success := @_root_.OAI.GAD.sequential_projector_success
