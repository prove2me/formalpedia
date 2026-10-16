-- Prove2me | solution 1 for OAI.GAD.channel_population
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:28:00.307325+00:00
-- url     : https://prove2.me/submissions/82666f49-83b6-40d1-8969-2e82dcaa0b71

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/OutputEntropy.lean:L181-L196
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.channel_population. The node keeps its source
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
import Theorems.Thm_OAI_GAD_channel_first_site_entry
import Theorems.Thm_OAI_GAD_kraus_complete
import Theorems.Thm_OAI_GAD_local_channel
import Theorems.Thm_OAI_GAD_spectral_pure_decomposition

-- ---- from OAI.InformationTheory.AmplitudeDamping.Channel ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem sum_fin_cons {α : Type u_1} {M : Type u_2} [Fintype α] [AddCommMonoid M] {n : ℕ}
    (f : (Fin (n+1) → α) → M) :
    ∑ r, f r = ∑ a, ∑ r : Fin n → α, f (Fin.cons a r) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) ↦ α)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl

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

theorem columns_mul_conjTranspose {ι : Type u_18} {κ : Type u_19} {ρ : Type u_20} [Fintype κ] [Fintype ρ]
    (L : ρ → Matrix ι κ ℂ) (ψ φ : κ → ℂ) :
    columns L ψ * (columns L φ).conjTranspose =
      ∑ r, L r * Matrix.vecMulVec ψ (star φ) * (L r).conjTranspose := by
  simp_rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
  ext i j
  simp [columns, Matrix.mul_apply, Matrix.vecMulVec, Matrix.conjTranspose_apply, Matrix.sum_apply]

theorem columns_pure {ι : Type u_21} {κ : Type u_22} {ρ : Type u_23} [Fintype κ] [Fintype ρ]
    (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) :
    columns L ψ * (columns L ψ).conjTranspose = applyKraus L (pure ψ) :=
  columns_mul_conjTranspose L ψ ψ

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

/-- The square-moduli in each column of a unitary matrix sum to one. -/
theorem unitary_col_sq_sum (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    ∑ i, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ ↦ (A j j).re) (Unitary.coe_star_mul_self U)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_re, Complex.normSq_apply,
    mul_comm] using h

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.TensorEntropy ----
namespace OAI

universe u_1 u_2 u_3 u_4

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

open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem trace_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    (Matrix.reindex e e A).trace = A.trace := by
  exact Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)

end GAD
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace GAD
variable {ι : Type u_3} {κ : Type u_4} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

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

theorem vecMass_branches {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    vecMass ψ = vecMass (branch ψ 0) + vecMass (branch ψ 1) := by
  unfold vecMass
  rw [sum_fin_cons]
  simp [Fin.sum_univ_two,branch]

theorem population_zero {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    population ψ 0 = vecMass (branch ψ 1) := by
  unfold population
  rw [sum_fin_cons]
  simp [vecMass,branch]

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_2} {κ : Type u_3} {ρ : Type u_4} [Fintype ι] [Fintype κ] [Fintype ρ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ] in
theorem gram_columns (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) :
    gram (columns L ψ) = applyKraus L (pure ψ) := columns_pure L ψ

theorem mass_channel_columns (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) (ψ : Basis n → ℂ) :
    mass (columns (tensorKraus γ ν n) ψ) = vecMass ψ := by
  unfold mass
  rw [gram_columns]
  change (channel γ ν n (pure ψ)).trace.re = _
  rw [channel_trace γ ν hγ hν, pure_trace,Complex.ofReal_re]

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

theorem spectral_vectors_mass {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (a : ι) :
    vecMass (fun i ↦ hP.eigenvectorUnitary i a) = 1 :=
  unitary_col_sq_sum hP.eigenvectorUnitary a

theorem channel_mixture (γ ν : ℝ) (n : ℕ) (w : α → ℝ) (P : α → QMatrix n) :
    channel γ ν n (∑ a, w a • P a) = ∑ a, w a • channel γ ν n (P a) := by
  simp only [channel,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]

theorem matrixPopulation_pure {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) :
    matrixPopulation (pure ψ) j = population ψ j := by
  simp [matrixPopulation,population,pure,Complex.mul_conj]

theorem matrixPopulation_mixture {n : ℕ} (w : α → ℝ) (P : α → QMatrix n) (j : Fin n) :
    matrixPopulation (∑ a, w a • P a) j = ∑ a, w a * matrixPopulation (P a) j := by
  simp only [matrixPopulation,Matrix.sum_apply,Complex.re_sum,Matrix.smul_apply,
    Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {α : Type u_4} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.OutputEntropy ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem tensorKraus_reindex (γ ν : ℝ) (n : ℕ) (e : Equiv.Perm (Fin n)) (r : Fin n → Fin 4) :
    Matrix.reindex (coordinatePerm e) (coordinatePerm e) (tensorKraus γ ν n r) =
      tensorKraus γ ν n (coordinatePerm e r) := by
  ext i j
  change (∏ k, kraus γ ν (r k) (i (e k)) (j (e k))) =
    ∏ k, kraus γ ν (r (e.symm k)) (i k) (j k)
  simpa using Equiv.prod_comp e (fun k ↦ kraus γ ν (r (e.symm k)) (i k) (j k))

theorem channel_reindex (γ ν : ℝ) (n : ℕ) (e : Equiv.Perm (Fin n)) (P : QMatrix n) :
    Matrix.reindex (coordinatePerm e) (coordinatePerm e) (channel γ ν n P) =
      channel γ ν n (Matrix.reindex (coordinatePerm e) (coordinatePerm e) P) := by
  let φ := reindexStarAlgEquiv (coordinatePerm e : Basis n ≃ Basis n)
  have hL (r : Fin n → Fin 4) : φ (tensorKraus γ ν n r) =
      tensorKraus γ ν n (coordinatePerm e r) := tensorKraus_reindex γ ν n e r
  change φ (∑ r, tensorKraus γ ν n r * P * star (tensorKraus γ ν n r)) = _
  simp only [map_sum,map_mul,map_star,hL]
  exact (coordinatePerm e : (Fin n → Fin 4) ≃ _).sum_comp
    (fun r ↦ tensorKraus γ ν n r * φ P * star (tensorKraus γ ν n r))

theorem matrixPopulation_reindex {n : ℕ} (e : Equiv.Perm (Fin n)) (P : QMatrix n) (j : Fin n) :
    matrixPopulation (Matrix.reindex (coordinatePerm e) (coordinatePerm e) P) j =
      matrixPopulation P (e.symm j) := by
  apply Fintype.sum_equiv (coordinatePerm e).symm
  intro i
  simp [Matrix.reindex_apply,Matrix.submatrix_apply]

theorem population_channel_pure_zero (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    matrixPopulation (channel γ ν (n+1) (pure ψ)) 0 =
      (1-γ)*population ψ 0+γ*ν*vecMass ψ := by
  have hentry (i : Basis n) :
      (channel γ ν (n+1) (pure ψ) (Fin.cons 1 i) (Fin.cons 1 i)).re =
        (γ*ν)*(gram (columns (tensorKraus γ ν n) (branch ψ 0)) i i).re+
          (1-γ*(1-ν))*(gram (columns (tensorKraus γ ν n) (branch ψ 1)) i i).re := by
    rw [channel_first_site_entry]
    rw [local_channel γ ν hγ hν (fun a d ↦
      (columns (tensorKraus γ ν n) (branch ψ a) *
        (columns (tensorKraus γ ν n) (branch ψ d)).conjTranspose) i i)]
    simp [gram]
  have hmass (b : Fin 2) : (∑ i, (gram (columns (tensorKraus γ ν n) (branch ψ b)) i i).re) =
      vecMass (branch ψ b) := by
    simpa only [mass,Matrix.trace,Matrix.diag,Complex.re_sum] using
      mass_channel_columns γ ν hγ hν n (branch ψ b)
  unfold matrixPopulation
  rw [sum_fin_cons]
  simp only [Fin.sum_univ_two,Fin.cons_zero,show (0:Fin 2) ≠ 1 by decide,ite_false,
    Finset.sum_const_zero,zero_add,ite_true,hentry,Finset.sum_add_distrib,← Finset.mul_sum,hmass,
    population_zero,vecMass_branches]
  ring

theorem population_channel_zero (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} {P : QMatrix (n+1)} (hP : IsState P) :
    matrixPopulation (channel γ ν (n+1) P) 0 = (1-γ)*matrixPopulation P 0+γ*ν := by
  let w := hP.1.isHermitian.eigenvalues
  let ψ := fun a i ↦ hP.1.isHermitian.eigenvectorUnitary i a
  have hs : ∑ a, w a = 1 := spectral_weights_sum hP
  have hv (a) : vecMass (ψ a) = 1 := spectral_vectors_mass hP.1.isHermitian a
  have hdecomp : P = ∑ a, w a • pure (ψ a) := spectral_pure_decomposition hP.1.isHermitian
  conv_lhs => rw [hdecomp]
  rw [channel_mixture,matrixPopulation_mixture]
  simp only [population_channel_pure_zero γ ν hγ hν,hv,mul_one]
  conv_rhs => rw [hdecomp]
  rw [matrixPopulation_mixture]
  simp only [matrixPopulation_pure,mul_add,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,hs,one_mul,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem channel_population (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} {P : QMatrix n} (hP : IsState P) (j : Fin n) :
    matrixPopulation (channel γ ν n P) j = (1-γ)*matrixPopulation P j+γ*ν := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
      let e : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 j
      let Q := Matrix.reindex (coordinatePerm e) (coordinatePerm e) P
      have hQ : IsState Q := ⟨hP.1.submatrix _, (trace_reindex _ P).trans hP.2⟩
      have h := population_channel_zero γ ν hγ hν hQ
      change matrixPopulation (channel γ ν (n+1) (Matrix.reindex _ _ P)) 0 = _ at h
      rw [← channel_reindex, matrixPopulation_reindex] at h
      change matrixPopulation (channel γ ν (n+1) P) (e.symm 0) =
        (1-γ)*matrixPopulation (Matrix.reindex (coordinatePerm e) (coordinatePerm e) P) 0+γ*ν at h
      rw [matrixPopulation_reindex] at h
      simpa [e] using h

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.channel_population := @_root_.OAI.GAD.channel_population
