-- Prove2me | solution 1 for OAI.GAD.entropy_coupling_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:11:20.875999+00:00
-- url     : https://prove2.me/submissions/7807266d-3626-4561-a677-16175cbb1694

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/EntropyContinuity.lean:L124-L165
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.entropy_coupling_bound. The node keeps its source
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
import Theorems.Thm_OAI_GAD_concaveOn_entropy
import Theorems.Thm_OAI_GAD_entropy_le_diagonal
import Theorems.Thm_OAI_GAD_entropy_le_of_logDetShift_le
import Theorems.Thm_OAI_GAD_spectralFactor_gram

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

theorem entropy_nonneg {A : Matrix ι ι ℂ} (hA : IsState A) : 0 ≤ entropy A := by
  rw [entropy_eq_sum hA.1.isHermitian]
  have hs : ∑ i, hA.1.isHermitian.eigenvalues i = 1 := by
    simpa using congrArg Complex.re
      (hA.1.isHermitian.trace_eq_sum_eigenvalues.symm.trans hA.2)
  apply Finset.sum_nonneg
  intro i _
  apply Real.negMulLog_nonneg (hA.1.eigenvalues_nonneg i)
  rw [← hs]
  exact Finset.single_le_sum (fun j _ ↦ hA.1.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- The square-moduli in each column of a unitary matrix sum to one. -/
theorem unitary_col_sq_sum (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    ∑ i, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ ↦ (A j j).re) (Unitary.coe_star_mul_self U)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_re, Complex.normSq_apply,
    mul_comm] using h

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

-- ---- from OAI.InformationTheory.AmplitudeDamping.StateEntropy ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem spectral_weights_sum {P : Matrix ι ι ℂ} (hP : IsState P) :
    ∑ a, hP.1.isHermitian.eigenvalues a = 1 := by
  simpa using congrArg Complex.re
    (hP.1.isHermitian.trace_eq_sum_eigenvalues.symm.trans hP.2)

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {α : Type u_4} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem spectralFactor_column {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (k : ι) :
    ∑ i, Complex.normSq (spectralFactor hA i k) = hA.isHermitian.eigenvalues k := by
  simp only [spectralFactor,Complex.normSq_mul,Complex.normSq_ofReal,← pow_two,
    Real.sq_sqrt (hA.eigenvalues_nonneg k),← Finset.mul_sum,unitary_col_sq_sum,mul_one]

theorem entropy_sum_le (A : α → Matrix ι ι ℂ) (hA : ∀ a, (A a).PosSemidef) :
    entropy (∑ a, A a) ≤ ∑ a, entropy (A a) := by
  let F : Matrix ι (α × ι) ℂ := fun i ak ↦ spectralFactor (hA ak.1) i ak.2
  have hgram : gram F = ∑ a, A a := by
    ext i j
    change (∑ ak : α × ι, spectralFactor (hA ak.1) i ak.2 *
      star (spectralFactor (hA ak.1) j ak.2)) = (∑ a, A a) i j
    simp only [Fintype.sum_prod_type,Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun M : Matrix ι ι ℂ ↦ M i j) (spectralFactor_gram (hA a))
  have hdiag (ak : α × ι) : ((Fᴴ*F) ak ak).re = (hA ak.1).isHermitian.eigenvalues ak.2 := by
    change (∑ i, star (F i ak)*F i ak).re = _
    simp only [Complex.re_sum,Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,F]
    exact spectralFactor_column (hA ak.1) ak.2
  rw [← hgram]
  change entropy (F*Fᴴ) ≤ _
  rw [entropy_mul_conjTranspose]
  have he := entropy_le_diagonal (Matrix.posSemidef_conjTranspose_mul_self F)
  simpa only [hdiag,Fintype.sum_prod_type,entropy_eq_sum (hA _).isHermitian] using he

theorem entropy_mixture_upper (w : α → ℝ) (A : α → Matrix ι ι ℂ)
    (hw : ∀ a, 0 ≤ w a) (hA : ∀ a, IsState (A a)) :
    entropy (∑ a, w a • A a) ≤ ∑ a, (w a*entropy (A a)+Real.negMulLog (w a)) := by
  have h := entropy_sum_le (fun a ↦ w a • A a) (fun a ↦ (hA a).1.smul (hw a))
  simpa only [entropy_smul _ (hA _).1.isHermitian,(hA _).2,Complex.one_re,mul_one] using h

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

omit [DecidableEq ι] in
theorem shannon_le_log_card [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) : (∑ i, Real.negMulLog (p i)) ≤ Real.log (Fintype.card ι) := by
  let d : ℝ := Fintype.card ι
  have hd : 0 < d := by dsimp [d]; exact_mod_cast (Fintype.card_pos (α := ι))
  have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ : ι ↦ d⁻¹) (p := p)
    (fun _ _ ↦ inv_nonneg.mpr hd.le)
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact mul_inv_cancel₀ hd.ne')
    (fun i _ ↦ (show p i ∈ Set.Ici 0 from hp i))
  simp only [smul_eq_mul,← Finset.mul_sum,hs,mul_one,Real.negMulLog,Real.log_inv] at h
  have hh := mul_le_mul_of_nonneg_left h hd.le
  dsimp only [d] at *
  calc
    _ = (Fintype.card ι:ℝ) * ((Fintype.card ι:ℝ)⁻¹ * ∑ i, Real.negMulLog (p i)) := by
      rw [← mul_assoc,mul_inv_cancel₀ hd.ne',one_mul]
    _ ≤ _ := hh
    _ = _ := by field_simp

theorem entropy_le_log_card [Nonempty ι] {A : Matrix ι ι ℂ} (hA : IsState A) :
    entropy A ≤ Real.log (Fintype.card ι) := by
  rw [entropy_eq_sum hA.1.isHermitian]
  exact shannon_le_log_card _ hA.1.eigenvalues_nonneg (spectral_weights_sum hA)

theorem state_normalize_trace {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 < t) (htr : A.trace=(t:ℂ)) : IsState (t⁻¹ • A) := by
  refine ⟨hA.smul (inv_nonneg.mpr ht.le), ?_⟩
  rw [Matrix.trace_smul,htr]
  simp [Complex.real_smul,ht.ne']

/-- Entropy continuity from a positive common-mixture coupling. -/
theorem entropy_coupling_bound [Nonempty ι] {A B U V : Matrix ι ι ℂ}
    (hA : IsState A) (hB : IsState B) (hU : U.PosSemidef) (hV : V.PosSemidef)
    {t : ℝ} (ht : 0 < t) (htrU : U.trace=(t:ℂ)) (htrV : V.trace=(t:ℂ))
    (heq : A+U=B+V) :
    entropy A-entropy B ≤ t*Real.log (Fintype.card ι)+(1+t)*Real.binEntropy (t/(1+t)) := by
  let a : ℝ := (1+t)⁻¹
  let b : ℝ := t/(1+t)
  have ht1 : 0 < 1+t := by positivity
  have ha : 0 ≤ a := inv_nonneg.mpr ht1.le
  have hb : 0 ≤ b := div_nonneg ht.le ht1.le
  have hab : a+b=1 := by dsimp [a,b]; field_simp
  have hu := state_normalize_trace hU ht htrU
  have hv := state_normalize_trace hV ht htrV
  have he : a • A+b • (t⁻¹ • U)=a • B+b • (t⁻¹ • V) := by
    have hba : b*t⁻¹=a := by dsimp [a,b]; field_simp
    simp only [smul_smul,hba,← smul_add,heq]
  have hlo := concaveOn_entropy.2 hA.1 hu.1 ha hb hab
  have hup := entropy_mixture_upper (fun s : Fin 2 ↦ if s=0 then a else b)
    (fun s : Fin 2 ↦ if s=0 then B else t⁻¹ • V)
    (by intro s; split_ifs <;> assumption)
    (by intro s; split_ifs <;> assumption)
  simp only [Fin.sum_univ_two,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false] at hup
  rw [he] at hlo
  have hU0 := entropy_nonneg hu
  have hVmax := entropy_le_log_card hv
  have hm := mul_le_mul_of_nonneg_left hVmax hb
  have hh : Real.negMulLog a+Real.negMulLog b=Real.binEntropy b := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    have heab : a=1-b := by linarith
    rw [heab]; ring
  have htotal : a*(entropy A-entropy B) ≤ b*Real.log (Fintype.card ι)+Real.binEntropy b := by
    change a*entropy A+b*entropy (t⁻¹ • U) ≤ _ at hlo
    nlinarith [mul_nonneg hb hU0]
  have hh' := mul_le_mul_of_nonneg_left htotal ht1.le
  dsimp only [a,b] at hh'
  have hc : (1+t)*((1+t)⁻¹*(entropy A-entropy B)) = entropy A-entropy B := by
    rw [← mul_assoc,mul_inv_cancel₀ ht1.ne',one_mul]
  rw [hc,mul_add] at hh'
  have hc' : (1+t)*(t/(1+t)*Real.log (Fintype.card ι))=t*Real.log (Fintype.card ι) := by
    field_simp
  rwa [hc'] at hh'

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

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.entropy_coupling_bound := @_root_.OAI.GAD.entropy_coupling_bound
