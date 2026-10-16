-- Prove2me | solution 1 for OAI.GAD.factor_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:13:05.865646+00:00
-- url     : https://prove2.me/submissions/d69cd957-e39e-4b7b-a467-632a3f3b93d4

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/EntropyContinuity.lean:L198-L268
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.factor_entropy_bound. The node keeps its source
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
import Theorems.Thm_OAI_GAD_entropy_coupling_bound

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

end

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_3} [Fintype ι] [DecidableEq ι]

end

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_4} {κ : Type u_5} [Fintype ι] [Fintype κ]

theorem mass_real_smul (a : ℝ) (A : Matrix ι κ ℂ) : mass (a • A)=a^2*mass A := by
  rw [← frobVector_norm,← frobVector_norm]
  have he : frobVector (a • A)=a • frobVector A := rfl
  rw [he,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

theorem mass_add (A B : Matrix ι κ ℂ) :
    mass (A+B)=mass A+mass B+2*⟪frobVector A,frobVector B⟫_ℝ := by
  have h := norm_add_sq_real (frobVector A) (frobVector B)
  rw [← frobVector_add,frobVector_norm,frobVector_norm,frobVector_norm] at h
  linarith

theorem mass_sub (A B : Matrix ι κ ℂ) :
    mass (A-B)=mass A+mass B-2*⟪frobVector A,frobVector B⟫_ℝ := by
  have h := norm_sub_sq_real (frobVector A) (frobVector B)
  rw [← frobVector_sub,frobVector_norm,frobVector_norm,frobVector_norm] at h
  linarith

theorem gram_posSemidef (A : Matrix ι κ ℂ) : (gram A).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose A

theorem gram_trace (A : Matrix ι κ ℂ) : (gram A).trace=(mass A:ℂ) := by
  exact Complex.ext (by rfl) (by simpa using (Complex.nonneg_iff.mp (gram_posSemidef A).trace_nonneg).2.symm)

variable [DecidableEq ι]

/-- Quantitative entropy comparison from close normalized Gram factors. -/
theorem factor_entropy_bound [Nonempty ι] (X Y : Matrix ι κ ℂ)
    (hX : mass X=1) (hY : mass Y=1) {ε : ℝ} (hε : 0 < ε) :
    entropy (gram X)-entropy (gram Y) ≤
      (mass (X-Y)/(4*ε)+ε)*Real.log (Fintype.card ι)+
        (1+mass (X-Y)/(4*ε)+ε)*Real.log 2 := by
  let D := X-Y
  let S := X+Y
  have hDS : ⟪frobVector D,frobVector S⟫_ℝ=0 := by
    dsimp [D,S]
    rw [frobVector_sub,frobVector_add,inner_sub_left,inner_add_right,inner_add_right,
      real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_comm (frobVector Y),
      frobVector_norm,frobVector_norm,hX,hY]
    ring
  have hsum : mass D+mass S=4 := by
    dsimp [D,S]; rw [mass_add,mass_sub,hX,hY]; ring
  have hSle : mass S ≤ 4 := by linarith [mass_nonneg D]
  let c : ℝ := (4*ε)⁻¹
  let U : Matrix ι ι ℂ := c • gram (D-ε • S)
  let V : Matrix ι ι ℂ := c • gram (D+ε • S)
  let t : ℝ := c*(mass D+ε^2*mass S)
  have hc : 0 < c := inv_pos.mpr (by positivity)
  have htm : 0 < mass D+ε^2*mass S := by
    have hd := mass_nonneg D
    have hs := mass_nonneg S
    have hes : 0 < ε^2 := sq_pos_of_pos hε
    by_cases hdz : mass D=0
    · have hspos : 0 < mass S := by linarith
      exact add_pos_of_nonneg_of_pos hd (mul_pos hes hspos)
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hd (Ne.symm hdz)) (mul_nonneg hes.le hs)
  have ht : 0 < t := mul_pos hc htm
  have hin : ⟪frobVector D,frobVector (ε • S)⟫_ℝ=0 := by
    change ⟪frobVector D,ε • frobVector S⟫_ℝ=0
    rw [real_inner_smul_right,hDS,mul_zero]
  have hmU : mass (D-ε • S)=mass D+ε^2*mass S := by rw [mass_sub,mass_real_smul,hin]; ring
  have hmV : mass (D+ε • S)=mass D+ε^2*mass S := by rw [mass_add,mass_real_smul,hin]; ring
  have htrU : U.trace=(t:ℂ) := by
    dsimp [U,t]; rw [Matrix.trace_smul,gram_trace,hmU]; simp [Complex.real_smul]; ring
  have htrV : V.trace=(t:ℂ) := by
    dsimp [V,t]; rw [Matrix.trace_smul,gram_trace,hmV]; simp [Complex.real_smul]; ring
  have hUV : gram X+U=gram Y+V := by
    have hcε : c*(4*ε)=1 := inv_mul_cancel₀ (by positivity)
    ext i j
    simp only [U,V,D,S,gram,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,star_sub,star_add,
      Complex.real_smul,star_mul,Complex.star_def,Complex.conj_ofReal]
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hcε' : (c:ℂ)*(4*ε)=1 := by exact_mod_cast hcε
    linear_combination -(X i k*(starRingEnd ℂ) (X j k)-Y i k*(starRingEnd ℂ) (Y j k))*hcε'
  have hA : IsState (gram X) := ⟨gram_posSemidef X, by rw [gram_trace,hX]; norm_num⟩
  have hB : IsState (gram Y) := ⟨gram_posSemidef Y, by rw [gram_trace,hY]; norm_num⟩
  have hb := entropy_coupling_bound hA hB ((gram_posSemidef _).smul hc.le)
    ((gram_posSemidef _).smul hc.le) ht htrU htrV hUV
  have htle : t ≤ mass (X-Y)/(4*ε)+ε := by
    dsimp [t,c,D]
    have haux : ε^2*mass S ≤ ε^2*4 := mul_le_mul_of_nonneg_left hSle (sq_nonneg _)
    have h := mul_le_mul_of_nonneg_left haux (inv_nonneg.mpr (show 0 ≤ 4*ε by positivity))
    have he : (4*ε)⁻¹*(mass (X-Y)+ε^2*4)=mass (X-Y)/(4*ε)+ε := by field_simp
    rw [← he]; nlinarith
  have hlog : 0 ≤ Real.log (Fintype.card ι) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := ι))
  have hint : Real.binEntropy (t/(1+t)) ≤ Real.log 2 := Real.binEntropy_le_log_two
  calc
    _ ≤ t*Real.log (Fintype.card ι)+(1+t)*Real.binEntropy (t/(1+t)) := hb
    _ ≤ t*Real.log (Fintype.card ι)+(1+t)*Real.log 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hint (by positivity))
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_right htle hlog
      have h2 := mul_le_mul_of_nonneg_right htle (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
      nlinarith

end GAD

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_6} {κ : Type u_7} [Fintype ι] [Fintype κ]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.factor_entropy_bound := @_root_.OAI.GAD.factor_entropy_bound
