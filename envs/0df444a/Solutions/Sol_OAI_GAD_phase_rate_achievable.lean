-- Prove2me | solution 1 for OAI.GAD.phase_rate_achievable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:05:44.046056+00:00
-- url     : https://prove2.me/submissions/1c10fe64-a9b9-4546-b4c0-b4dd9bec2ef2

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/CapacityAchievability.lean:L10-L42
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.phase_rate_achievable. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CodingAsymptotics
import Theorems.Thm_OAI_GAD_averageError_nonneg
import Theorems.Thm_OAI_GAD_entropy_diagonal
import Theorems.Thm_OAI_GAD_entropy_qubit
import Theorems.Thm_OAI_GAD_entropy_unitary_conj
import Theorems.Thm_OAI_GAD_exists_phase_code
import Theorems.Thm_OAI_GAD_kraus_complete
import Theorems.Thm_OAI_GAD_local_channel

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

theorem spectralMatrix_entropy (U : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) :
    entropy (spectralMatrix U q)=∑ i, Real.negMulLog (q i) := by
  rw [spectralMatrix,entropy_unitary_conj]
  · exact entropy_diagonal q
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro i; exact Complex.conj_ofReal _

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_4} [Fintype ι] [DecidableEq ι]

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

theorem phaseOutput_conjugate (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Fin 2) :
    phaseOutput γ ν p s=Unitary.conjStarAlgAut ℂ _ (signUnitary s) (phaseOutput γ ν p 0) := by
  rw [phaseOutput_formula γ ν hγ hν hp s,phaseOutput_formula γ ν hγ hν hp 0]
  ext i j
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp [Unitary.conjStarAlgAut_apply,signUnitary,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.star_apply]

theorem spectralMatrix_conjugate {ι : Type u_1} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) :
    Unitary.conjStarAlgAut ℂ _ U (spectralMatrix V q)=spectralMatrix (U*V) q := by
  simp only [spectralMatrix,Unitary.conjStarAlgAut_apply,Submonoid.coe_mul,star_mul,
    Matrix.mul_assoc]

/-- The two phase outputs have a single common eigenvalue distribution. -/
theorem phase_spectral (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    ∃ (q : Fin 2 → ℝ) (U : Fin 2 → Matrix.unitaryGroup (Fin 2) ℂ),
      (∀ i, 0 ≤ q i) ∧ (∑ i, q i=1) ∧
      (∀ s, phaseOutput γ ν p s=spectralMatrix (U s) q) ∧
      classicalEntropy q=g (v γ ν p) := by
  let hA := phaseOutput_state γ ν hγ hν hp 0
  let q := hA.1.isHermitian.eigenvalues
  let V := hA.1.isHermitian.eigenvectorUnitary
  have hV : phaseOutput γ ν p 0=spectralMatrix V q := hA.1.isHermitian.spectral_theorem
  refine ⟨q,fun s ↦ signUnitary s*V,?_,spectral_weights_sum hA,?_,?_⟩
  · exact hA.1.eigenvalues_nonneg
  · intro s
    rw [phaseOutput_conjugate γ ν hγ hν hp s,hV,spectralMatrix_conjugate]
  · rw [← phaseOutput_entropy γ ν hγ hν hp 0,hV,spectralMatrix_entropy]
    rfl

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

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

end GAD

end

open Filter
namespace GAD

theorem codingMessages_pos (r : ℝ) (n : ℕ) : 0 < codingMessages r n :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

theorem codingMessages_bound {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    (codingMessages r n:ℝ) ≤ 2*Real.exp ((n:ℝ)*r) := by
  have h1 := Nat.ceil_lt_add_one (Real.exp_pos ((n:ℝ)*r)).le
  have h2 : 1 ≤ Real.exp ((n:ℝ)*r) := Real.one_le_exp_iff.mpr (mul_nonneg (Nat.cast_nonneg _) hr)
  dsimp only [codingMessages]
  linarith

theorem codingMessages_rate (r : ℝ) {n : ℕ} (hn : 0 < n) :
    r/Real.log 2 ≤ Real.log (codingMessages r n:ℝ)/Real.log 2/(n:ℝ) := by
  have h : (n:ℝ)*r ≤ Real.log (codingMessages r n:ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos ((n:ℝ)*r)) (Nat.le_ceil (Real.exp ((n:ℝ)*r)))
    simpa only [Real.log_exp,codingMessages] using hh
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right h hl.le) hn'.le
  have he : (n:ℝ)*r/Real.log 2/(n:ℝ)=r/Real.log 2 := by
    field_simp
  rw [he] at hh
  exact hh

theorem coding_cross_bound {r : ℝ} (hr : 0 ≤ r) (a : ℝ) (n : ℕ) :
    4*(codingMessages r n:ℝ)*Real.exp (-(n:ℝ)*a) ≤
      8*Real.exp (-(n:ℝ)*(a-r)) := by
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (codingMessages_bound hr n) (by norm_num : (0:ℝ) ≤ 4)) (Real.exp_pos (-(n:ℝ)*a)).le
  apply h.trans_eq
  rw [show 4*(2*Real.exp ((n:ℝ)*r))*Real.exp (-(n:ℝ)*a)=
    8*(Real.exp ((n:ℝ)*r)*Real.exp (-(n:ℝ)*a)) by ring,← Real.exp_add]
  congr 2
  ring

theorem coding_error_tendsto (K δ : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦ K/((n:ℝ)*δ^2)+8*Real.exp (-(n:ℝ)*b)) atTop (nhds 0) := by
  have h1 : Tendsto (fun n : ℕ ↦ K/((n:ℝ)*δ^2)) atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat K).div_const (δ^2)
    simpa only [div_div,zero_div] using h
  have h2 : Tendsto (fun n : ℕ ↦ 8*Real.exp (-(n:ℝ)*b)) atTop (nhds 0) := by
    have he := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-b)).le
      (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hb))
    have h := he.const_mul (8:ℝ)
    simpa only [mul_zero,← Real.exp_nat_mul,mul_neg,neg_mul] using h
  simpa only [zero_add] using h1.add h2

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.CapacityAchievability ----
namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

/-- Direct operational coding for the phase pair; conditional and global typical subspaces
and a sequential collective POVM, rather than an assumed coding theorem. -/
theorem phase_rate_achievable (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1)
    {r : ℝ} (hr : 0 ≤ r) (hrχ : r < objective γ ν p) :
    Achievable γ ν (r/Real.log 2) := by
  classical
  obtain ⟨q,U,hq,hs,hphase,hent⟩ := phase_spectral γ ν hγ hν hp
  let δ := (objective γ ν p-r)/4
  let K := 9*logVariance (meanPhaseWeights γ ν p)+8*logVariance q
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hb : 0 < objective γ ν p-2*δ-r := by dsimp [δ]; linarith
  have hex (n : ℕ) : ∃ C : Code n, 0 < n →
      C.messages=codingMessages r n ∧ averageError γ ν C ≤
        K/((n:ℝ)*δ^2)+4*(codingMessages r n:ℝ)*Real.exp (-(n:ℝ)*(objective γ ν p-2*δ)) := by
    by_cases hn : 0 < n
    · obtain ⟨C,hC,he⟩ := exists_phase_code γ ν hγ hν hp q U hq hs hphase hent hδ hn
        (codingMessages r n) (codingMessages_pos r n)
      exact ⟨C,fun _ ↦ ⟨hC,he⟩⟩
    · exact ⟨trivialCode n,fun hn' ↦ (hn hn').elim⟩
  choose C hC using hex
  refine ⟨C,?_,?_⟩
  · apply squeeze_zero' (Filter.Eventually.of_forall (fun n ↦ averageError_nonneg γ ν hγ hν (C n)))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : 0 < n := by omega
      exact ((hC n hn0).2).trans (add_le_add le_rfl
        (coding_cross_bound hr (objective γ ν p-2*δ) n))
    · exact coding_error_tendsto K δ hb
  · intro ε hε
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := by omega
    rw [(hC n hn0).1]
    exact (sub_le_self _ hε.le).trans (codingMessages_rate r hn0)

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter


theorem solution : type_of% @_root_.OAI.GAD.phase_rate_achievable := @_root_.OAI.GAD.phase_rate_achievable
