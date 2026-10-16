-- Prove2me | solution 1 for OAI.GAD.exists_phase_code
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:56:40.381984+00:00
-- url     : https://prove2.me/submissions/21384f0e-363d-4efb-b036-c9343989bbb1

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/PhaseCoding.lean:L92-L166
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.exists_phase_code. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseCoding
import Theorems.Thm_OAI_GAD_exists_packed_measurement
import Theorems.Thm_OAI_GAD_kraus_complete
import Theorems.Thm_OAI_GAD_local_channel
import Theorems.Thm_OAI_GAD_typical_card
import Theorems.Thm_OAI_GAD_typical_tail

-- ---- from OAI.InformationTheory.AmplitudeDamping.Channel ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem tensorKraus_complete (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    ∑ r, (tensorKraus γ ν n r).conjTranspose * tensorKraus γ ν n r = 1 := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, tensorKraus,
    star_prod]
  simp only [← Finset.prod_mul_distrib]
  have hinner (r : Fin n → Fin 4) :
      (∑ b : Basis n, ∏ k, star (kraus γ ν (r k) (b k) (i k)) * kraus γ ν (r k) (b k) (j k)) =
      ∏ k, ∑ b : Fin 2, star (kraus γ ν (r k) b (i k)) * kraus γ ν (r k) b (j k) :=
    (Fintype.prod_sum (fun k b ↦ star (kraus γ ν (r k) b (i k)) * kraus γ ν (r k) b (j k))).symm
  simp only [hinner]
  rw [← Fintype.prod_sum (fun k r ↦ ∑ b : Fin 2,
    star (kraus γ ν r b (i k)) * kraus γ ν r b (j k))]
  have hc (k : Fin n) :
      (∑ r : Fin 4, ∑ b : Fin 2, star (kraus γ ν r b (i k)) * kraus γ ν r b (j k)) =
      if i k = j k then 1 else 0 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ ↦ A (i k) (j k))
      (kraus_complete γ ν hγ hν)
    simpa only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] using h
  simp_rw [hc]
  simp [Fintype.prod_ite_zero, funext_iff, Matrix.one_apply]

theorem applyKraus_posSemidef {ι : Type u_7} {κ : Type u_8} {ρ : Type u_9} [Fintype ι] [Fintype κ] [Fintype ρ]
    [DecidableEq ι] [DecidableEq κ] (L : ρ → Matrix ι κ ℂ)
    {P : Matrix κ κ ℂ} (hP : P.PosSemidef) : (applyKraus L P).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact Finset.sum_nonneg (fun r _ ↦ Matrix.nonneg_iff_posSemidef.mpr
    (hP.mul_mul_conjTranspose_same (L r)))

theorem applyKraus_trace {ι : Type u_10} {κ : Type u_11} {ρ : Type u_12} [Fintype ι] [Fintype κ] [Fintype ρ]
    [DecidableEq κ] (L : ρ → Matrix ι κ ℂ)
    (hL : ∑ r, (L r).conjTranspose * L r = 1) (P : Matrix κ κ ℂ) :
    (applyKraus L P).trace = P.trace := by
  simp only [applyKraus, Matrix.trace_sum]
  calc
    _ = ∑ r, ((L r).conjTranspose * L r * P).trace := by
      apply Finset.sum_congr rfl
      intro r _
      exact Matrix.trace_mul_cycle _ _ _
    _ = _ := by
      rw [← Matrix.trace_sum, ← Matrix.sum_mul, hL, Matrix.one_mul]

theorem channel_trace (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) (P : QMatrix n) :
    (channel γ ν n P).trace = P.trace :=
  applyKraus_trace _ (tensorKraus_complete γ ν hγ hν n) P

theorem channel_posSemidef (γ ν : ℝ) (n : ℕ) {P : QMatrix n} (hP : P.PosSemidef) :
    (channel γ ν n P).PosSemidef := applyKraus_posSemidef _ hP

end GAD

end

end OAI

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

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.PureRecursion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

namespace GAD

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_1} [Fintype ι]

variable [DecidableEq ι]

end

section
open scoped BigOperators ComplexOrder
open Matrix

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_2} {κ : Type u_3} {ρ : Type u_4} [Fintype ι] [Fintype κ] [Fintype ρ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]

theorem channel_state (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) {P : QMatrix n} (hP : IsState P) :
    IsState (channel γ ν n P) :=
  ⟨channel_posSemidef _ _ _ hP.1, (channel_trace γ ν hγ hν n P).trans hP.2⟩

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.PhaseStates ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem phaseOutput_formula (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Fin 2) :
    phaseOutput γ ν p s =
      !![((1-((1-γ)*p+γ*ν) : ℝ):ℂ),
          ((if s=0 then 1 else -1 : ℝ)*Real.sqrt (1-γ)*Real.sqrt (1-p)*Real.sqrt p : ℂ);
         ((if s=0 then 1 else -1 : ℝ)*Real.sqrt (1-γ)*Real.sqrt (1-p)*Real.sqrt p : ℂ),
          (((1-γ)*p+γ*ν : ℝ):ℂ)] := by
  rw [phaseOutput,local_channel γ ν hγ hν]
  have hsp : (Real.sqrt p : ℂ)^2=(p:ℂ) := by exact_mod_cast Real.sq_sqrt hp.1
  have hs1p : (Real.sqrt (1-p) : ℂ)^2=(1-p:ℂ) := by exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hp.2)
  ext i j
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp [pure,phaseSignal,Matrix.of_apply,Complex.ofReal_mul,Complex.ofReal_sub] <;>
    ring_nf <;> simp only [hsp,hs1p] <;> ring

theorem phaseOutput_average (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (1/2:ℝ) • phaseOutput γ ν p 0+(1/2:ℝ) • phaseOutput γ ν p 1 =
      Matrix.diagonal (fun b : Fin 2 ↦ ((if b=0 then 1-((1-γ)*p+γ*ν) else (1-γ)*p+γ*ν : ℝ):ℂ)) := by
  rw [phaseOutput_formula γ ν hγ hν hp 0,phaseOutput_formula γ ν hγ hν hp 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.real_smul] <;> ring

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.PhaseProducts ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace GAD

theorem channel_tensorMatrix (γ ν : ℝ) (n : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    channel γ ν n (tensorMatrix n A) =
      tensorMatrix n (fun k ↦ applyKraus (kraus γ ν) (A k)) := by
  ext i j
  simp only [channel,applyKraus,tensorMatrix,Matrix.mul_apply,Matrix.sum_apply,Matrix.conjTranspose_apply]
  change (∑ r : Fin n → Fin 4, ∑ v : Basis n,
      (∑ u : Basis n, (∏ k, kraus γ ν (r k) (i k) (u k)) * (∏ k, A k (u k) (v k))) *
        star (∏ k, kraus γ ν (r k) (j k) (v k))) =
    ∏ k, ∑ r : Fin 4, ∑ v : Fin 2,
      (∑ u : Fin 2, kraus γ ν r (i k) u * A k u v) * star (kraus γ ν r (j k) v)
  simp only [star_prod,Finset.sum_mul,← Finset.prod_mul_distrib]
  have hinner (r : Fin n → Fin 4) (v : Basis n) :
      (∑ u : Basis n, ∏ k, (kraus γ ν (r k) (i k) (u k) * A k (u k) (v k)) *
        star (kraus γ ν (r k) (j k) (v k))) =
      ∏ k, ∑ u : Fin 2, (kraus γ ν (r k) (i k) u * A k u (v k)) *
        star (kraus γ ν (r k) (j k) (v k)) :=
    (Fintype.prod_sum (fun k u ↦ (kraus γ ν (r k) (i k) u * A k u (v k)) *
      star (kraus γ ν (r k) (j k) (v k)))).symm
  simp only [hinner]
  have hmid (r : Fin n → Fin 4) :
      (∑ v : Basis n, ∏ k, ∑ u : Fin 2,
        (kraus γ ν (r k) (i k) u * A k u (v k)) * star (kraus γ ν (r k) (j k) (v k))) =
      ∏ k, ∑ v : Fin 2, ∑ u : Fin 2,
        (kraus γ ν (r k) (i k) u * A k u v) * star (kraus γ ν (r k) (j k) v) :=
    (Fintype.prod_sum (fun k v ↦ ∑ u : Fin 2,
      (kraus γ ν (r k) (i k) u * A k u v) * star (kraus γ ν (r k) (j k) v))).symm
  simp only [hmid]
  exact (Fintype.prod_sum (fun k r ↦ ∑ v : Fin 2, ∑ u : Fin 2,
    (kraus γ ν r (i k) u * A k u v) * star (kraus γ ν r (j k) v))).symm

theorem tensorMatrix_sum {n : ℕ} (B : Fin n → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ s : Basis n, tensorMatrix n (fun k ↦ B k (s k))) =
      tensorMatrix n (fun k ↦ ∑ s, B k s) := by
  ext i j
  simp only [Matrix.sum_apply,tensorMatrix]
  exact (Fintype.prod_sum (fun k s ↦ B k s (i k) (j k))).symm

theorem tensorMatrix_smul {n : ℕ} (c : Fin n → ℝ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorMatrix n (fun k ↦ c k • A k) = (∏ k, c k) • tensorMatrix n A := by
  ext i j
  simp [tensorMatrix,Complex.real_smul,Finset.prod_mul_distrib]

theorem tensorMatrix_average {n : ℕ} (B : Fin n → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ s : Basis n, ((2:ℝ)^n)⁻¹ • tensorMatrix n (fun k ↦ B k (s k))) =
      tensorMatrix n (fun k ↦ (1/2:ℝ) • B k 0+(1/2:ℝ) • B k 1) := by
  rw [← Finset.smul_sum,tensorMatrix_sum]
  have hm : (fun k ↦ (1/2:ℝ) • B k 0+(1/2:ℝ) • B k 1) =
      (fun k ↦ (1/2:ℝ) • (∑ s, B k s)) := by
    funext k
    rw [Fin.sum_univ_two,smul_add]
  rw [hm,tensorMatrix_smul]
  simp [Finset.prod_const,one_div]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem phaseState_output {n : ℕ} (γ ν p : ℝ) (s : Basis n) :
    channel γ ν n (phaseState p s) = tensorMatrix n (fun k ↦ phaseOutput γ ν p (s k)) := by
  rw [phaseState_tensor,channel_tensorMatrix]
  rfl

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.TypicalSets ----
namespace OAI

noncomputable section

universe u_1 u_2

section
open scoped BigOperators
namespace GAD
variable {α : Type u_1} [Fintype α]

theorem iidWeight_total (q : α → ℝ) (hs : ∑ a, q a=1) (n : ℕ) :
    (∑ x : Fin n → α, iidWeight q n x)=1 := by
  rw [show (∑ x : Fin n → α, iidWeight q n x) = ∏ j : Fin n, ∑ a, q a from
    (Fintype.prod_sum (fun _ : Fin n ↦ q)).symm]
  simp only [hs,Finset.prod_const_one]

end GAD

end

open scoped BigOperators
namespace GAD
variable {α : Type u_2} [Fintype α]
attribute [local instance] OAI.GAD.instDecidablePred_oAI
theorem iid_log (q : α → ℝ) (n : ℕ) (x : Fin n → α) (hx : 0 < iidWeight q n x) :
    iidSum (centeredLog q) n x = -Real.log (iidWeight q n x)-(n:ℝ)*classicalEntropy q := by
  have hn : ∀ j ∈ Finset.univ, q (x j) ≠ 0 := (Finset.prod_ne_zero_iff.mp hx.ne')
  simp only [iidSum,centeredLog,Finset.sum_sub_distrib,Finset.sum_neg_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [iidWeight,Real.log_prod hn]

theorem typical_weight_upper (q : α → ℝ) (δ : ℝ) (n : ℕ) (x : Fin n → α)
    (hx : IsTypical q δ n x) : iidWeight q n x ≤ Real.exp (-(n:ℝ)*(classicalEntropy q-δ)) := by
  rw [← Real.exp_log hx.1]
  apply Real.exp_le_exp.mpr
  have h := (abs_le.mp hx.2).1
  rw [iid_log q n x hx.1] at h
  nlinarith

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

theorem spectralMatrix_hermitian (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) :
    (spectralMatrix U q).IsHermitian := by
  apply Matrix.isHermitian_mul_mul_conjTranspose
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i; exact Complex.conj_ofReal _

theorem spectralMatrix_posSemidef (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) : (spectralMatrix U q).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0:ℂ) ≤ (q i:ℂ)
  exact_mod_cast hq i

theorem spectralMatrix_trace (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) :
    (spectralMatrix U q).trace=(∑ i, q i:ℝ) := by
  rw [spectralMatrix,trace_unitary_conj,Matrix.trace_diagonal]
  simp

theorem spectralMatrix_mul (U : Matrix.unitaryGroup ι ℂ) (q r : ι → ℝ) :
    spectralMatrix U q*spectralMatrix U r=spectralMatrix U (fun i ↦ q i*r i) := by
  rw [spectralMatrix,spectralMatrix,← map_mul,Matrix.diagonal_mul_diagonal]
  congr 2; funext i; exact (Complex.ofReal_mul _ _).symm

theorem spectralMatrix_sub (U : Matrix.unitaryGroup ι ℂ) (q r : ι → ℝ) :
    spectralMatrix U q-spectralMatrix U r=spectralMatrix U (fun i ↦ q i-r i) := by
  rw [spectralMatrix,spectralMatrix,← map_sub]
  congr 1
  ext i j
  by_cases h : i=j <;> simp [h]

theorem spectralMatrix_smul (U : Matrix.unitaryGroup ι ℂ) (c : ℝ) (q : ι → ℝ) :
    c • spectralMatrix U q=spectralMatrix U (fun i ↦ c*q i) := by
  simp only [spectralMatrix,Unitary.conjStarAlgAut_apply]
  rw [← Matrix.smul_mul,← Matrix.mul_smul]
  congr 2
  ext i j
  simp [Matrix.diagonal_apply,Complex.real_smul]

theorem spectralMask_projection (U : Matrix.unitaryGroup ι ℂ) (s : Finset ι) :
    IsProjection (spectralMask U s) := by
  refine ⟨spectralMatrix_hermitian _ _, ?_⟩
  rw [spectralMask,spectralMatrix_mul]
  congr 1; funext i; split_ifs <;> simp

theorem spectralMask_trace (U : Matrix.unitaryGroup ι ℂ) (s : Finset ι) :
    (spectralMask U s).trace=(s.card:ℂ) := by
  rw [spectralMask,spectralMatrix_trace]
  simp

theorem spectralMask_compress (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) (s : Finset ι) :
    spectralMask U s*spectralMatrix U q*spectralMask U s=
      spectralMatrix U (fun i ↦ if i ∈ s then q i else 0) := by
  rw [spectralMask,spectralMatrix_mul,spectralMatrix_mul]
  congr 1; funext i; split_ifs <;> simp

theorem spectralMask_compress_bound (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) (s : Finset ι)
    {c : ℝ} (hc : ∀ i ∈ s, q i ≤ c) :
    (c • spectralMask U s-spectralMask U s*spectralMatrix U q*spectralMask U s).PosSemidef := by
  rw [spectralMask_compress,spectralMask,spectralMatrix_smul,spectralMatrix_sub]
  apply spectralMatrix_posSemidef
  intro i
  split_ifs with hi
  · simpa using sub_nonneg.mpr (hc i hi)
  · simp

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem tensor_spectralMatrix (n : ℕ) (U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ)
    (q : Fin 2 → ℝ) :
    tensorMatrix n (fun k ↦ spectralMatrix (U k) q)=
      spectralMatrix (tensorEigenUnitary U) (iidWeight q n) := by
  dsimp only [spectralMatrix,Unitary.conjStarAlgAut_apply,tensorEigenUnitary]
  simp only [iidWeight,Complex.ofReal_prod,Matrix.star_eq_conjTranspose]
  rw [← tensorMatrix_diagonal (fun _ : Fin n ↦ fun i : Fin 2 ↦ (q i:ℂ)),
    tensorMatrix_conjTranspose, tensorMatrix_mul,tensorMatrix_mul]

variable {ι : Type u_4} [Fintype ι] [DecidableEq ι]

theorem spectralMask_mass (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) (s : Finset ι) :
    (spectralMask U s*spectralMatrix U q).trace.re=∑ i ∈ s, q i := by
  rw [spectralMask,spectralMatrix_mul,spectralMatrix_trace,Complex.ofReal_re]
  simp [ite_mul]

theorem spectralMask_loss (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) (s : Finset ι)
    (hs : ∑ i, q i=1) :
    1-(spectralMask U s*spectralMatrix U q).trace.re=∑ i, if i ∈ s then 0 else q i := by
  rw [spectralMask_mass,← hs]
  have he : (∑ i, q i)=(∑ i ∈ s, q i)+(∑ i, if i ∈ s then 0 else q i) := by
    calc
      _ = ∑ i, ((if i ∈ s then q i else 0)+(if i ∈ s then 0 else q i)) := by
        apply Finset.sum_congr rfl
        intro i _; split_ifs <;> simp
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  linarith

theorem typicalProjection_properties (n : ℕ) (U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ)
    (q : Fin 2 → ℝ) (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i=1)
    {δ : ℝ} (hδ : 0 < δ) (hn : 0 < n) :
    IsProjection (typicalProjection n U q δ) ∧
    (typicalProjection n U q δ).trace.re ≤ Real.exp ((n:ℝ)*(classicalEntropy q+δ)) ∧
    1-(typicalProjection n U q δ*tensorMatrix n (fun k ↦ spectralMatrix (U k) q)).trace.re ≤
      logVariance q/((n:ℝ)*δ^2) ∧
    (Real.exp (-(n:ℝ)*(classicalEntropy q-δ)) • typicalProjection n U q δ-
      typicalProjection n U q δ*tensorMatrix n (fun k ↦ spectralMatrix (U k) q)*typicalProjection n U q δ).PosSemidef := by
  classical
  refine ⟨spectralMask_projection _ _, ?_, ?_, ?_⟩
  · rw [typicalProjection,spectralMask_trace,Complex.natCast_re]
    exact typical_card q hq hs δ n
  · rw [tensor_spectralMatrix,typicalProjection,spectralMask_loss _ _ _ (iidWeight_total q hs n)]
    simpa only [typicalSet,Finset.mem_filter,Finset.mem_univ,true_and] using typical_tail q hq hs hδ hn
  · rw [tensor_spectralMatrix,typicalProjection]
    apply spectralMask_compress_bound
    intro x hx
    exact typical_weight_upper q δ n x (Finset.mem_filter.mp hx).2

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.PhaseCoding ----
namespace OAI

noncomputable section

universe u_1

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem meanPhaseWeights_nonneg (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (b : Fin 2) :
    0 ≤ meanPhaseWeights γ ν p b := by
  have he : 0 ≤ (1-γ)*p+γ*ν := add_nonneg (mul_nonneg (sub_nonneg.mpr hγ.2) hp.1)
    (mul_nonneg hγ.1 hν.1)
  have hu : (1-γ)*p+γ*ν ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hp.2 (sub_nonneg.mpr hγ.2)
    have h2 := mul_le_mul_of_nonneg_left hν.2 hγ.1
    nlinarith
  dsimp [meanPhaseWeights]
  split_ifs
  · linarith
  · exact he

theorem meanPhaseWeights_sum (γ ν p : ℝ) : ∑ b, meanPhaseWeights γ ν p b=1 := by
  simp [meanPhaseWeights,Fin.sum_univ_two]

theorem meanPhaseWeights_entropy (γ ν p : ℝ) :
    classicalEntropy (meanPhaseWeights γ ν p)=Real.binEntropy ((1-γ)*p+γ*ν) := by
  simp [classicalEntropy,meanPhaseWeights,Fin.sum_univ_two,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,add_comm]

theorem phase_mean_spectral (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (1/2:ℝ) • phaseOutput γ ν p 0+(1/2:ℝ) • phaseOutput γ ν p 1=
      spectralMatrix 1 (meanPhaseWeights γ ν p) := by
  rw [phaseOutput_average γ ν hγ hν hp]
  simp [spectralMatrix,meanPhaseWeights]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem exists_phase_code (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1)
    (q : Fin 2 → ℝ) (U : Fin 2 → Matrix.unitaryGroup (Fin 2) ℂ)
    (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i=1)
    (hphase : ∀ s, phaseOutput γ ν p s=spectralMatrix (U s) q)
    (hent : classicalEntropy q=g (v γ ν p))
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) (M : ℕ) (hM : 0 < M) :
    ∃ C : Code n, C.messages=M ∧ averageError γ ν C ≤
      (9*logVariance (meanPhaseWeights γ ν p)+8*logVariance q)/((n:ℝ)*δ^2)+
        4*(M:ℝ)*Real.exp (-(n:ℝ)*(objective γ ν p-2*δ)) := by
  let qb := meanPhaseWeights γ ν p
  let w : Basis n → ℝ := fun _ ↦ ((2:ℝ)^n)⁻¹
  let A : Basis n → QMatrix n := fun s ↦ channel γ ν n (phaseState p s)
  let P := typicalProjection n (fun _ ↦ 1) qb δ
  let Q := fun s : Basis n ↦ typicalProjection n (fun k ↦ U (s k)) q δ
  have hmean : (∑ s, w s • A s)=tensorMatrix n (fun _ ↦ spectralMatrix 1 qb) := by
    simp only [w,A,phaseState_output]
    rw [tensorMatrix_average]
    simp only [phase_mean_spectral γ ν hγ hν hp,qb]
  have hA (s : Basis n) : A s=tensorMatrix n (fun k ↦ spectralMatrix (U (s k)) q) := by
    simp only [A,phaseState_output,hphase]
  have hP := typicalProjection_properties n (fun _ ↦ 1) qb
    (meanPhaseWeights_nonneg γ ν hγ hν hp) (meanPhaseWeights_sum γ ν p) hδ hn
  have hQ (s : Basis n) := typicalProjection_properties n (fun k ↦ U (s k)) q hq hs hδ hn
  have hw : ∀ s, 0 ≤ w s := fun _ ↦ by dsimp [w]; positivity
  have hw1 : ∑ s, w s=1 := phase_weights_sum n
  have hga : (∑ s, w s*(1-(P*A s).trace.re)) ≤ logVariance qb/((n:ℝ)*δ^2) := by
    have he : (∑ s, w s*(1-(P*A s).trace.re))=
        1-(P*(∑ s, w s • A s)).trace.re := by
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hw1,Matrix.mul_sum,Matrix.mul_smul,
        Matrix.trace_sum,Matrix.trace_smul,Complex.re_sum,Complex.real_smul,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [he,hmean]
    exact hP.2.2.1
  have hcb : (∑ s, w s*(1-(Q s*A s).trace.re)) ≤ logVariance q/((n:ℝ)*δ^2) := by
    calc
      _ ≤ ∑ s, w s*(logVariance q/((n:ℝ)*δ^2)) := by
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul_of_nonneg_left _ (hw s)
        rw [hA]
        exact (hQ s).2.2.1
      _ = _ := by rw [← Finset.sum_mul,hw1,one_mul]
  have hcp : (Real.exp (-(n:ℝ)*(classicalEntropy qb-δ)) • P-
      P*(∑ s, w s • A s)*P).PosSemidef := by
    rw [hmean]
    exact hP.2.2.2
  obtain ⟨x,D,hD,hDs,he⟩ := exists_packed_measurement w hw hw1 A Q
    (fun s ↦ channel_state γ ν hγ hν n (phaseState_state hp s))
    (fun s ↦ (hQ s).1) P hP.1 (Real.exp_pos _).le (Real.exp_pos _).le
    hga hcb (fun s ↦ (hQ s).2.1) hcp M hM
  let C : Code n := {
    messages := M
    messages_pos := hM
    encoding := fun m ↦ phaseState p (x m)
    encoding_state := fun m ↦ phaseState_state hp (x m)
    decoding := D
    decoding_pos := hD
    decoding_sum := hDs }
  refine ⟨C,rfl,?_⟩
  have hexp : Real.exp (-(n:ℝ)*(classicalEntropy qb-δ))*
      Real.exp ((n:ℝ)*(classicalEntropy q+δ))=
        Real.exp (-(n:ℝ)*(objective γ ν p-2*δ)) := by
    rw [← Real.exp_add,hent,meanPhaseWeights_entropy]
    congr 1
    dsimp [objective]
    ring
  have hbound : 9*(logVariance qb/((n:ℝ)*δ^2))+8*(logVariance q/((n:ℝ)*δ^2))+
      4*(M:ℝ)*Real.exp (-(n:ℝ)*(classicalEntropy qb-δ))*Real.exp ((n:ℝ)*(classicalEntropy q+δ))=
      (9*logVariance qb+8*logVariance q)/((n:ℝ)*δ^2)+
        4*(M:ℝ)*Real.exp (-(n:ℝ)*(objective γ ν p-2*δ)) := by
    rw [mul_assoc (4*(M:ℝ)),hexp]
    ring
  rw [hbound] at he
  simpa only [averageError,C,A,Complex.re_sum] using he

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.exists_phase_code := @_root_.OAI.GAD.exists_phase_code
