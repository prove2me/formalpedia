-- Prove2me | solution 1 for OAI.GAD.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:08:59.903977+00:00
-- url     : https://prove2.me/submissions/2c4c654f-8420-4dd5-a37b-56d3de1b8dbf

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/Main.lean:L38-L49
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.GAD.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_GAD_main) verbatim and is proved by it.
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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CodingAsymptotics
import Theorems.Thm_OAI_GAD_achievable_upper
import Theorems.Thm_OAI_GAD_entropy_diagonal
import Theorems.Thm_OAI_GAD_entropy_qubit
import Theorems.Thm_OAI_GAD_holevo_formula
import Theorems.Thm_OAI_GAD_kraus_complete
import Theorems.Thm_OAI_GAD_local_channel
import Theorems.Thm_OAI_GAD_phase_rate_achievable
import Theorems.Thm_OAI_GAD_tensorMatrix_entropy

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

-- ---- from OAI.InformationTheory.AmplitudeDamping.OutputConvexity ----
namespace OAI

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

open scoped BigOperators
open Set Filter Topology

namespace GAD

theorem continuous_g : Continuous g := by
  unfold g
  fun_prop

theorem continuous_objective (γ ν : ℝ) : Continuous (objective γ ν) := by
  unfold objective v
  exact (Real.binEntropy_continuous.comp (by fun_prop)).sub
    (continuous_g.comp (by fun_prop))

/-- Existence of the genuine scalar maximum rather than a supremum surrogate. -/
theorem exists_maximizer (γ ν : ℝ) :
    ∃ p ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1, objective γ ν q ≤ objective γ ν p := by
  exact isCompact_Icc.exists_isMaxOn (by norm_num) (continuous_objective γ ν).continuousOn

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

-- ---- from OAI.InformationTheory.AmplitudeDamping.StateEntropy ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem state_mixture (w : α → ℝ) (P : α → Matrix ι ι ℂ)
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (hP : ∀ a, IsState (P a)) :
    IsState (∑ a, w a • P a) := by
  constructor
  · rw [← Matrix.nonneg_iff_posSemidef]
    exact Finset.sum_nonneg (fun a _ ↦ Matrix.nonneg_iff_posSemidef.mpr ((hP a).1.smul (hw a)))
  · simp only [Matrix.trace_sum,Matrix.trace_smul,(hP _).2,Complex.real_smul,mul_one]
    exact_mod_cast hs

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {α : Type u_4} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

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

theorem phaseOutput_state (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Fin 2) :
    IsState (phaseOutput γ ν p s) := by
  refine ⟨applyKraus_posSemidef _ (pure_posSemidef _), ?_⟩
  exact (applyKraus_trace _ (kraus_complete γ ν hγ hν) _).trans (pure_state (phaseSignal_mass hp s)).2

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

theorem phaseOutput_det (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Fin 2) :
    (phaseOutput γ ν p s).det.re=v γ ν p := by
  rw [phaseOutput_formula γ ν hγ hν hp s,Matrix.det_fin_two]
  have hγ' := Real.sq_sqrt (sub_nonneg.mpr hγ.2)
  have hp' := Real.sq_sqrt (sub_nonneg.mpr hp.2)
  have hp'' := Real.sq_sqrt hp.1
  simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    ← Complex.ofReal_mul,← Complex.ofReal_sub,Complex.ofReal_re]
  split_ifs <;> dsimp only [v] <;>
    ring_nf <;> rw [hγ', hp', hp''] <;> ring

theorem phaseOutput_entropy (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Fin 2) :
    entropy (phaseOutput γ ν p s)=g (v γ ν p) := by
  rw [entropy_qubit (phaseOutput_state γ ν hγ hν hp s).1.isHermitian
    (phaseOutput_state γ ν hγ hν hp s).2,phaseOutput_det γ ν hγ hν hp s]

theorem phaseOutput_average (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (1/2:ℝ) • phaseOutput γ ν p 0+(1/2:ℝ) • phaseOutput γ ν p 1 =
      Matrix.diagonal (fun b : Fin 2 ↦ ((if b=0 then 1-((1-γ)*p+γ*ν) else (1-γ)*p+γ*ν : ℝ):ℂ)) := by
  rw [phaseOutput_formula γ ν hγ hν hp 0,phaseOutput_formula γ ν hγ hν hp 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.real_smul] <;> ring

theorem phaseOutput_average_entropy (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    entropy ((1/2:ℝ) • phaseOutput γ ν p 0+(1/2:ℝ) • phaseOutput γ ν p 1) =
      Real.binEntropy ((1-γ)*p+γ*ν) := by
  rw [phaseOutput_average γ ν hγ hν hp,entropy_diagonal]
  simp [Fin.sum_univ_two,Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,add_comm]

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

theorem phaseState_entropy {n : ℕ} (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Basis n) :
    entropy (channel γ ν n (phaseState p s)) = (n:ℝ)*g (v γ ν p) := by
  rw [phaseState_output,tensorMatrix_entropy n _ (fun k ↦ phaseOutput_state γ ν hγ hν hp (s k))]
  simp only [phaseOutput_entropy γ ν hγ hν hp,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]

theorem phaseState_average_entropy (n : ℕ) (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    entropy (∑ s : Basis n, (((2:ℝ)^n)⁻¹ : ℂ) • channel γ ν n (phaseState p s)) =
      (n:ℝ)*Real.binEntropy ((1-γ)*p+γ*ν) := by
  simp only [← Complex.ofReal_pow,← Complex.ofReal_inv,Complex.coe_smul,phaseState_output]
  rw [tensorMatrix_average]
  have hs : IsState ((1/2:ℝ) • phaseOutput γ ν p 0+(1/2:ℝ) • phaseOutput γ ν p 1) := by
    have h := state_mixture (fun _ : Fin 2 ↦ (1/2:ℝ)) (phaseOutput γ ν p)
      (by intro a; norm_num) (by norm_num [Fin.sum_univ_two])
      (fun s ↦ phaseOutput_state γ ν hγ hν hp s)
    simpa only [Fin.sum_univ_two] using h
  rw [tensorMatrix_entropy n _ (fun _ ↦ hs)]
  simp only [phaseOutput_average_entropy γ ν hγ hν hp,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem phaseValue_formula (n : ℕ) (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    phaseValue γ ν p n = (n:ℝ)/Real.log 2*objective γ ν p := by
  unfold phaseValue
  rw [phaseState_average_entropy n γ ν hγ hν hp]
  simp only [phaseState_entropy γ ν hγ hν hp,← Finset.sum_mul,phase_weights_sum,one_mul]
  unfold objective
  ring

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.Holevo ----
namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem holevo_additive (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    holevo γ ν n = (n:ℝ)*holevo γ ν 1 := by
  obtain ⟨p,hp,hmax⟩ := exists_maximizer γ ν
  rw [holevo_formula γ ν hγ hν ⟨hp,hmax⟩ n,holevo_formula γ ν hγ hν ⟨hp,hmax⟩ 1]
  norm_num
  ring

theorem holevo_maximizer (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) :
    ∃ p : ℝ, Maximizes γ ν p ∧
      ∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n:ℝ)/Real.log 2*objective γ ν p := by
  obtain ⟨p,hp,hmax⟩ := exists_maximizer γ ν
  exact ⟨p,⟨hp,hmax⟩,fun n _ ↦ holevo_formula γ ν hγ hν ⟨hp,hmax⟩ n⟩

theorem phase_attainment (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : Maximizes γ ν p) (n : ℕ) :
    (∀ s : Basis n, IsState (phaseState p s)) ∧ holevo γ ν n = phaseValue γ ν p n := by
  exact ⟨fun s ↦ phaseState_state hp.1 s, by
    rw [holevo_formula γ ν hγ hν hp n,phaseValue_formula n γ ν hγ hν hp.1]⟩

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.CodingAsymptotics ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

theorem trivialCode_error (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) : averageError γ ν (trivialCode n)=0 := by
  have h := channel_state γ ν hγ hν n (phaseState_state (n := n) (p := 0) (by norm_num) (fun _ ↦ 0))
  dsimp only [averageError,trivialCode]
  simp only [Matrix.one_mul,Fin.sum_univ_one,Nat.cast_one,div_one]
  rw [h.2,Complex.one_re,sub_self]

theorem zero_achievable (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) : Achievable γ ν 0 := by
  refine ⟨trivialCode,?_,?_⟩
  · simpa only [trivialCode_error γ ν hγ hν] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (nhds 0))
  · intro ε hε
    apply Filter.Eventually.of_forall
    intro n
    simp only [trivialCode,Nat.cast_one,Real.log_one,zero_div,zero_sub]
    linarith

end GAD

end

open Filter
namespace GAD

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.Main ----
namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

theorem capacity_formula (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : Maximizes γ ν p) :
    capacity γ ν=objective γ ν p/Real.log 2 := by
  have hzero := zero_achievable γ ν hγ hν
  have hbdd : BddAbove {R : ℝ | Achievable γ ν R} :=
    ⟨objective γ ν p/Real.log 2,fun _ hR ↦ achievable_upper γ ν hγ hν hp hR⟩
  have hnonempty : {R : ℝ | Achievable γ ν R}.Nonempty := ⟨0,hzero⟩
  have hcap0 : 0 ≤ capacity γ ν := le_csSup hbdd hzero
  apply le_antisymm
  · exact csSup_le hnonempty (fun _ hR ↦ achievable_upper γ ν hγ hν hp hR)
  · by_contra! hbad
    let R := (capacity γ ν+objective γ ν p/Real.log 2)/2
    have hRcap : capacity γ ν < R := by dsimp [R]; linarith
    have hRχ : R < objective γ ν p/Real.log 2 := by dsimp [R]; linarith
    have hR0 : 0 ≤ R := hcap0.trans hRcap.le
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hrχ : R*Real.log 2 < objective γ ν p := (lt_div_iff₀ hl).mp hRχ
    have ha := phase_rate_achievable γ ν hγ hν hp.1 (mul_nonneg hR0 hl.le) hrχ
    rw [mul_div_cancel_right₀ R hl.ne'] at ha
    exact (not_le_of_gt hRcap) (le_csSup hbdd ha)

theorem capacity_holevo (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) : capacity γ ν=holevo γ ν 1 := by
  obtain ⟨p,hp,hmax⟩ := exists_maximizer γ ν
  rw [capacity_formula γ ν hγ hν ⟨hp,hmax⟩,holevo_formula γ ν hγ hν ⟨hp,hmax⟩ 1]
  norm_num
  ring

theorem main (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hν : ν ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n : ℝ) * holevo γ ν 1) ∧
    (∃ p : ℝ, Maximizes γ ν p ∧
      ∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n : ℝ) / Real.log 2 * objective γ ν p) ∧
    capacity γ ν = holevo γ ν 1 ∧
    (∀ p : ℝ, Maximizes γ ν p → ∀ n : ℕ, 1 ≤ n →
      (∀ s : Basis n, IsState (phaseState p s)) ∧
      holevo γ ν n = phaseValue γ ν p n) := by
  exact ⟨fun n _ ↦ holevo_additive γ ν hγ hν n,
    holevo_maximizer γ ν hγ hν,capacity_holevo γ ν hγ hν,
    fun p hp n _ ↦ phase_attainment γ ν hγ hν hp n⟩

end GAD

end

end OAI

-- ---- mission target ----
open OAI OAI.GAD
universe u
open scoped BigOperators ComplexOrder
open Matrix Filter
open scoped BigOperators ComplexOrder MatrixOrder

theorem solution (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hν : ν ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n : ℝ) * holevo γ ν 1) ∧
    (∃ p : ℝ, Maximizes γ ν p ∧
      ∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n : ℝ) / Real.log 2 * objective γ ν p) ∧
    capacity γ ν = holevo γ ν 1 ∧
    (∀ p : ℝ, Maximizes γ ν p → ∀ n : ℕ, 1 ≤ n →
      (∀ s : Basis n, IsState (phaseState p s)) ∧
      holevo γ ν n = phaseValue γ ν p n) := by
  first
    | exact OAI.GAD.main γ ν hγ hν
    | exact OAI.GAD.main
    | (apply OAI.GAD.main <;> assumption)
    | (intros; apply OAI.GAD.main <;> assumption)
