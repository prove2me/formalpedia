-- Prove2me | solution 1 for OAI.GAD.cq_decoding_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:22:03.4724+00:00
-- url     : https://prove2.me/submissions/74ed9508-ecb8-43dc-9cdb-0bfd77795760

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/HolevoInformation.lean:L91-L132
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.cq_decoding_entropy_bound. The node keeps its source
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
import Theorems.Thm_OAI_GAD_entropy_le_of_logDetShift_le
import Theorems.Thm_OAI_GAD_exists_orthogonal_factors
import Theorems.Thm_OAI_GAD_factor_entropy_bound
import Theorems.Thm_OAI_GAD_orthogonal_factor_entropy
import Theorems.Thm_OAI_GAD_spectralFactor_gram

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

end

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_3} [Fintype ι] [DecidableEq ι]

end

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_4} {κ : Type u_5} [Fintype ι] [Fintype κ]

theorem mass_sub (A B : Matrix ι κ ℂ) :
    mass (A-B)=mass A+mass B-2*⟪frobVector A,frobVector B⟫_ℝ := by
  have h := norm_sub_sq_real (frobVector A) (frobVector B)
  rw [← frobVector_sub,frobVector_norm,frobVector_norm,frobVector_norm] at h
  linarith

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

omit [DecidableEq μ] in
theorem naimark_isometry (D : μ → Matrix ι ι ℂ) (hD : ∀ m, (D m).PosSemidef)
    (hDs : ∑ m, D m=1) : (naimark D hD)ᴴ*naimark D hD=1 := by
  rw [← hDs]
  ext i j
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.conjTranspose_apply,naimark,star_star,
    Matrix.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  exact congrArg (fun A : Matrix ι ι ℂ ↦ A i j) (spectralFactor_gram (hD m))

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} [Fintype ι] [Fintype κ] [Fintype μ]

omit [Fintype ι] in
theorem gram_concatenate (w : μ → ℝ) (X : μ → Matrix ι κ ℂ) (hw : ∀ m, 0 ≤ w m) :
    gram (concatenate w X)=∑ m, w m • gram (X m) := by
  ext i j
  simp only [gram,Matrix.mul_apply,Matrix.conjTranspose_apply,concatenate,
    Fintype.sum_prod_type,Matrix.sum_apply,Matrix.smul_apply,Complex.real_smul,
    star_mul,Complex.star_def,Complex.conj_ofReal,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro k _
  have hs : (Real.sqrt (w m):ℂ)^2=(w m:ℂ) := by exact_mod_cast Real.sq_sqrt (hw m)
  linear_combination X m i k*(starRingEnd ℂ) (X m j k)*hs

theorem mass_concatenate (w : μ → ℝ) (X : μ → Matrix ι κ ℂ) (hw : ∀ m, 0 ≤ w m) :
    mass (concatenate w X)=∑ m, w m*mass (X m) := by
  simp only [mass,gram_concatenate w X hw,Matrix.trace_sum,Matrix.trace_smul,
    Complex.re_sum,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

omit [Fintype ι] [Fintype κ] [Fintype μ] in
theorem concatenate_sub (w : μ → ℝ) (X Y : μ → Matrix ι κ ℂ) :
    concatenate w X-concatenate w Y=concatenate w (fun m ↦ X m-Y m) := by
  ext i mk
  simp [concatenate,mul_sub]

theorem concatenate_mass_one (w : μ → ℝ) (X : μ → Matrix ι κ ℂ)
    (hw : ∀ m, 0 ≤ w m) (hws : ∑ m, w m=1) (hX : ∀ m, mass (X m)=1) :
    mass (concatenate w X)=1 := by
  rw [mass_concatenate w X hw]
  simp only [hX,mul_one,hws]

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.HolevoInformation ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem factorError_mono {ε d e : ℝ} {D : ℕ} (hε : 0 < ε) (hD : 0 < D) (hde : d ≤ e) :
    factorError ε d D ≤ factorError ε e D := by
  have hd := div_le_div_of_nonneg_right hde (show 0 ≤ 4*ε by positivity)
  have hlog : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  dsimp [factorError]
  exact add_le_add (mul_le_mul_of_nonneg_right (by linarith) hlog)
    (mul_le_mul_of_nonneg_right (by linarith) hlog2)

theorem factorError_average {μ : Type u_1} [Fintype μ] (ε : ℝ) (D : ℕ)
    (w d : μ → ℝ) (hws : ∑ m, w m=1) :
    (∑ m, w m*factorError ε (d m) D)=factorError ε (∑ m, w m*d m) D := by
  let c := (Real.log D+Real.log 2)/(4*ε)
  let v := ε*Real.log D+(1+ε)*Real.log 2
  have he (x : ℝ) : factorError ε x D=x*c+v := by dsimp [factorError,c,v]; ring
  simp only [he,mul_add,← mul_assoc,Finset.sum_add_distrib,← Finset.sum_mul,hws,one_mul]

variable {ι : Type u_2} {κ : Type u_3} {μ : Type u_4} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [Nonempty ι] [Nonempty μ]

theorem orthogonal_cq_bound (w : μ → ℝ) (hw : ∀ m, 0 ≤ w m) (hws : ∑ m, w m=1)
    (X Y : μ → Matrix (ι × μ) κ ℂ) (hX : ∀ m, mass (X m)=1) (hY : ∀ m, mass (Y m)=1)
    (hPY : ∀ m, blockProjection (ι := ι) m*Y m=Y m) {ε : ℝ} (hε : 0 < ε) :
    (∑ m, Real.negMulLog (w m)) ≤
      entropy (gram (concatenate w X))-(∑ m, w m*entropy (gram (X m)))+
        2*factorError ε (∑ m, w m*mass (X m-Y m)) (Fintype.card (ι × μ)) := by
  have havg := factor_entropy_bound (concatenate w Y) (concatenate w X)
    (concatenate_mass_one w Y hw hws hY) (concatenate_mass_one w X hw hws hX) hε
  have hmn : mass (concatenate w Y-concatenate w X)=∑ m, w m*mass (X m-Y m) := by
    rw [concatenate_sub,mass_concatenate w _ hw]
    apply Finset.sum_congr rfl
    intro m _
    congr 1
    rw [mass_sub,mass_sub,real_inner_comm]
    ring
  rw [hmn] at havg
  change entropy (gram (concatenate w Y))-entropy (gram (concatenate w X)) ≤
    factorError ε (∑ m, w m*mass (X m-Y m)) (Fintype.card (ι × μ)) at havg
  have hind := Finset.sum_le_sum (s := Finset.univ) (fun m _ ↦
    mul_le_mul_of_nonneg_left (factor_entropy_bound (X m) (Y m) (hX m) (hY m) hε) (hw m))
  change (∑ m, w m*(entropy (gram (X m))-entropy (gram (Y m)))) ≤
    (∑ m, w m*factorError ε (mass (X m-Y m)) (Fintype.card (ι × μ))) at hind
  rw [factorError_average ε _ w _ hws] at hind
  simp only [mul_sub,Finset.sum_sub_distrib] at hind
  rw [gram_concatenate w Y hw,orthogonal_factor_entropy w Y hY hPY,Finset.sum_add_distrib] at havg
  linarith

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_5} {μ : Type u_6} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]
  [Nonempty ι] [Nonempty μ]

omit [DecidableEq μ] in
theorem uniformWeight_nonneg (m : μ) : 0 ≤ uniformWeight μ m := by
  dsimp [uniformWeight]; positivity

omit [DecidableEq μ] in
theorem uniformWeight_sum : (∑ m : μ, uniformWeight μ m)=1 := by
  simp only [uniformWeight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := μ)).ne')

omit [DecidableEq μ] in
theorem uniformWeight_entropy : (∑ m : μ, Real.negMulLog (uniformWeight μ m))=Real.log (Fintype.card μ) := by
  have hc : (Fintype.card μ : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := μ)).ne'
  simp only [uniformWeight,Real.negMulLog,Real.log_inv,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

theorem cq_decoding_entropy_bound (A D : μ → Matrix ι ι ℂ)
    (hA : ∀ m, IsState (A m)) (hD : ∀ m, (D m).PosSemidef) (hDs : ∑ m, D m=1)
    {ε : ℝ} (hε : 0 < ε) :
    Real.log (Fintype.card μ) ≤
      entropy (∑ m, uniformWeight μ m • A m)-(∑ m, uniformWeight μ m*entropy (A m))+
      2*factorError ε (2*(1-∑ m, uniformWeight μ m*(D m*A m).trace.re)) (Fintype.card (ι × μ)) := by
  let W := naimark D hD
  let F := fun m ↦ spectralFactor (hA m).1
  let X := fun m ↦ W*F m
  have hW : Wᴴ*W=1 := naimark_isometry D hD hDs
  have hF (m : μ) : mass (F m)=1 := by dsimp [F,mass]; rw [spectralFactor_gram,(hA m).2]; rfl
  have hX (m : μ) : mass (X m)=1 := by rw [mass_isometry W hW,hF]
  obtain ⟨Y,hY,hPY,hd⟩ := exists_orthogonal_factors A D hA hD hDs
  have hb := orthogonal_cq_bound (uniformWeight μ) uniformWeight_nonneg uniformWeight_sum X Y hX hY hPY hε
  rw [uniformWeight_entropy] at hb
  have hc : concatenate (uniformWeight μ) X=W*concatenate (uniformWeight μ) F := by
    ext i mk
    dsimp [concatenate,X]
    simp only [Matrix.mul_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [concatenate]
    ring
  have hi (m : μ) : entropy (gram (X m))=entropy (A m) := by
    rw [entropy_gram_isometry W hW,spectralFactor_gram]
  have ha : entropy (gram (concatenate (uniformWeight μ) X))=
      entropy (∑ m, uniformWeight μ m • A m) := by
    rw [hc,entropy_gram_isometry W hW,gram_concatenate _ _ uniformWeight_nonneg]
    simp only [F,spectralFactor_gram]
  rw [ha] at hb
  simp only [hi] at hb
  have hd' : (∑ m, uniformWeight μ m*mass (X m-Y m)) ≤
      2*(1-∑ m, uniformWeight μ m*(D m*A m).trace.re) := by
    calc
      _ ≤ ∑ m, uniformWeight μ m*(2*(1-(D m*A m).trace.re)) :=
        Finset.sum_le_sum (fun m _ ↦ mul_le_mul_of_nonneg_left (hd m) (uniformWeight_nonneg m))
      _ = _ := by
        simp only [mul_sub,mul_one,Finset.sum_sub_distrib,← Finset.mul_sum,
          show ∀ a b : ℝ, a*(2*b)=2*(a*b) by intros; ring,← Finset.sum_mul,uniformWeight_sum]
        ring
  exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (factorError_mono hε (Fintype.card_pos (α := ι × μ)) hd') (by norm_num)))

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.cq_decoding_entropy_bound := @_root_.OAI.GAD.cq_decoding_entropy_bound
