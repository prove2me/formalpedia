-- Prove2me | solution 1 for OAI.GAD.achievable_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:40:04.227792+00:00
-- url     : https://prove2.me/submissions/38ead669-29aa-4808-abc0-f9c9d76ffff9

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/CapacityConverse.lean:L107-L137
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.achievable_upper. The node keeps its source
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
import Theorems.Thm_OAI_GAD_cq_decoding_entropy_bound
import Theorems.Thm_OAI_GAD_ensemble_nats_upper
import Theorems.Thm_OAI_GAD_kraus_complete
import Theorems.Thm_OAI_GAD_spectralFactor_gram

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

theorem IsState.le_one {A : Matrix ι ι ℂ} (hA : IsState A) : (1-A).PosSemidef := by
  let U := hA.1.isHermitian.eigenvectorUnitary
  let l := hA.1.isHermitian.eigenvalues
  have hl : ∀ i, l i ≤ 1 := by
    intro i
    rw [← spectral_weights_sum hA]
    exact Finset.single_le_sum (fun j _ ↦ hA.1.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hd : (Matrix.diagonal (fun i ↦ ((1-l i:ℝ):ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0:ℂ) ≤ ((1-l i:ℝ):ℂ)
    exact_mod_cast sub_nonneg.mpr (hl i)
  have he : 1-A=U.val*Matrix.diagonal (fun i ↦ ((1-l i:ℝ):ℂ))*U.valᴴ := by
    have hs := hA.1.isHermitian.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    have hd' : Matrix.diagonal (fun i ↦ ((1-l i:ℝ):ℂ))=1-Matrix.diagonal (fun i ↦ (l i:ℂ)) := by
      ext i j
      by_cases h : i=j <;> simp [h]
    rw [hd',Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one]
    have hu : U.val*U.valᴴ=1 := by
      change U.val*star U.val=1
      exact Unitary.mul_star_self_of_mem U.prop
    rw [hu]
    exact congrArg (fun M ↦ 1-M) hs
  rw [he]
  exact hd.mul_mul_conjTranspose_same _

theorem state_measurement_prob_le_trace {A D : Matrix ι ι ℂ} (hA : IsState A)
    (hD : D.PosSemidef) : (D*A).trace.re ≤ D.trace.re := by
  simpa only [Matrix.mul_one] using trace_product_mono hD hA.le_one

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

variable {ι : Type u_2} {κ : Type u_3} {μ : Type u_4} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [Nonempty ι] [Nonempty μ]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_5} {μ : Type u_6} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]
  [Nonempty ι] [Nonempty μ]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.CapacityConverse ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

theorem code_success_dim_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (C : Code n) :
    (∑ m, (C.decoding m*channel γ ν n (C.encoding m)).trace.re) ≤ (2:ℝ)^n := by
  calc
    _ ≤ ∑ m, (C.decoding m).trace.re := Finset.sum_le_sum (fun m _ ↦
      state_measurement_prob_le_trace (channel_state γ ν hγ hν n (C.encoding_state m)) (C.decoding_pos m))
    _ = _ := by
      rw [← Complex.re_sum,← Matrix.trace_sum,C.decoding_sum,Matrix.trace_one]
      rw [basis_card,Nat.cast_pow,Nat.cast_ofNat]
      rw [← Complex.ofReal_ofNat,← Complex.ofReal_pow,Complex.ofReal_re]

theorem code_messages_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (C : Code n)
    (he : averageError γ ν C ≤ 1/2) : (C.messages:ℝ) ≤ 2*(2:ℝ)^n := by
  have hM : 0 < (C.messages:ℝ) := by exact_mod_cast C.messages_pos
  have hs := code_success_dim_bound γ ν hγ hν C
  dsimp [averageError] at he
  have ht : (1/2:ℝ)*(C.messages:ℝ) ≤ ∑ m, (C.decoding m*channel γ ν n (C.encoding m)).trace.re := by
    apply (le_div_iff₀ hM).mp
    linarith
  linarith

theorem code_entropy_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (C : Code n) {p : ℝ} (hp : Maximizes γ ν p)
    {ε : ℝ} (hε : 0 < ε) :
    Real.log (C.messages:ℝ) ≤ (n:ℝ)*objective γ ν p+
      2*factorError ε (2*averageError γ ν C) (2^n*C.messages) := by
  let : Nonempty (Fin C.messages) := Fin.pos_iff_nonempty.mp C.messages_pos
  have h := cq_decoding_entropy_bound (fun m ↦ channel γ ν n (C.encoding m)) C.decoding
    (fun m ↦ channel_state γ ν hγ hν n (C.encoding_state m)) C.decoding_pos C.decoding_sum hε
  have hw (m : Fin C.messages) : uniformWeight (Fin C.messages) m=(C.messages:ℝ)⁻¹ := by
    simp only [uniformWeight,Fintype.card_fin]
  have he : 1-∑ m, uniformWeight (Fin C.messages) m*(C.decoding m*channel γ ν n (C.encoding m)).trace.re =
      averageError γ ν C := by
    simp only [hw,← Finset.mul_sum,averageError,div_eq_mul_inv]
    ring
  rw [he,Fintype.card_prod,basis_card,Fintype.card_fin] at h
  have hu := ensemble_nats_upper γ ν hγ hν (codeEnsemble C) hp
  change entropy (∑ a, (((C.messages:ℝ)⁻¹:ℝ):ℂ) • channel γ ν n (C.encoding a)) -
    (∑ a, (C.messages:ℝ)⁻¹*entropy (channel γ ν n (C.encoding a))) ≤ (n:ℝ)*objective γ ν p at hu
  simp only [Complex.coe_smul] at hu
  simp only [hw] at h
  linarith

theorem code_log_dimension_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (hn : 0 < n) (C : Code n)
    (he : averageError γ ν C ≤ 1/2) :
    Real.log (2^n*C.messages:ℕ) ≤ 3*(n:ℝ)*Real.log 2 := by
  have hM : 0 < (C.messages:ℝ) := by exact_mod_cast C.messages_pos
  have hpow : 0 < (2:ℝ)^n := by positivity
  have hb := code_messages_bound γ ν hγ hν C he
  have hl := Real.log_le_log hM hb
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hpow.ne',Real.log_pow] at hl
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Real.log_mul hpow.ne' hM.ne',Real.log_pow]
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

theorem code_log_rate_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (hn : 0 < n) (C : Code n) {p : ℝ} (hp : Maximizes γ ν p)
    {ε : ℝ} (hε : 0 < ε) (he : averageError γ ν C ≤ 1/2)
    (heε : averageError γ ν C ≤ 2*ε^2) :
    Real.log (C.messages:ℝ) ≤ (n:ℝ)*objective γ ν p+
      12*ε*(n:ℝ)*Real.log 2+(2+4*ε)*Real.log 2 := by
  have h := code_entropy_bound γ ν hγ hν C hp hε
  have hd : 0 < 2^n*C.messages := Nat.mul_pos (pow_pos (by norm_num) n) C.messages_pos
  have hb := factorError_mono hε hd (show 2*averageError γ ν C ≤ 4*ε^2 by nlinarith)
  have hlog := code_log_dimension_bound γ ν hγ hν hn C he
  have ht : factorError ε (4*ε^2) (2^n*C.messages)=
      2*ε*Real.log (2^n*C.messages:ℕ)+(1+2*ε)*Real.log 2 := by
    dsimp [factorError]
    field_simp
    ring
  rw [ht] at hb
  have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*ε by positivity)
  nlinarith

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

theorem achievable_upper (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p R : ℝ} (hp : Maximizes γ ν p)
    (hR : Achievable γ ν R) : R ≤ objective γ ν p/Real.log 2 := by
  obtain ⟨C,herr,hrate⟩ := hR
  by_contra! hbad
  let χ := objective γ ν p/Real.log 2
  let ε := (R-χ)/28
  have hε : 0 < ε := by dsimp [ε,χ]; linarith
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he1 : ∀ᶠ n : ℕ in atTop, averageError γ ν (C n) < 1/2 :=
    herr.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  have he2 : ∀ᶠ n : ℕ in atTop, averageError γ ν (C n) < 2*ε^2 :=
    herr.eventually (gt_mem_nhds (by positivity : (0:ℝ) < 2*ε^2))
  obtain ⟨N,hN⟩ := exists_nat_gt ((2+4*ε)/ε)
  obtain ⟨n,hnR,hn1,hn2,hn⟩ := ((hrate ε hε).and (he1.and
    (he2.and (eventually_ge_atTop (max N 1))))).exists
  have hn0 : 0 < n := by omega
  have hnR0 : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hNn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast (le_trans (le_max_left N 1) hn)
  have hsmall : 2+4*ε ≤ ε*(n:ℝ) := by
    have hh := (div_lt_iff₀ hε).mp hN
    nlinarith
  have hupper := code_log_rate_bound γ ν hγ hν hn0 (C n) hp hε hn1.le hn2.le
  have hlower := (le_div_iff₀ hl).mp ((le_div_iff₀ hnR0).mp hnR)
  have hχ : χ*Real.log 2=objective γ ν p := div_mul_cancel₀ _ hl.ne'
  have hχn : (n:ℝ)*objective γ ν p=χ*(n:ℝ)*Real.log 2 := by rw [← hχ]; ring
  rw [hχn] at hupper
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hl.le
  have hf : (R-χ-14*ε)*((n:ℝ)*Real.log 2) ≤ 0 := by nlinarith
  have hg : 0 < R-χ-14*ε := by dsimp [ε]; change χ < R at hbad; linarith
  exact (not_le_of_gt (mul_pos hg (mul_pos hnR0 hl))) hf

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter


theorem solution : type_of% @_root_.OAI.GAD.achievable_upper := @_root_.OAI.GAD.achievable_upper
