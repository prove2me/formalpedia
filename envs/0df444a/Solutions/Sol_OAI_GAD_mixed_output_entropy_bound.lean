-- Prove2me | solution 1 for OAI.GAD.mixed_output_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:26:00.135196+00:00
-- url     : https://prove2.me/submissions/ff39ad36-8d31-4c9b-a6a4-1ac8769cc993

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/OutputEntropy.lean:L58-L89
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.mixed_output_entropy_bound. The node keeps its source
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
import Theorems.Thm_OAI_GAD_concaveOn_entropy
import Theorems.Thm_OAI_GAD_hasDerivAt_woottersSlope
import Theorems.Thm_OAI_GAD_pure_output_entropy_bound
import Theorems.Thm_OAI_GAD_spectral_pure_decomposition

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

/-- The square-moduli in each column of a unitary matrix sum to one. -/
theorem unitary_col_sq_sum (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    ∑ i, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ ↦ (A j j).re) (Unitary.coe_star_mul_self U)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_re, Complex.normSq_apply,
    mul_comm] using h

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

theorem continuous_wootters : Continuous wootters := by
  unfold wootters
  exact continuous_g.comp (continuous_id.pow 2)

theorem radius_pos_lt_one {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    0 < radius s ∧ radius s < 1 := by
  have hx : 0 < 1 - 4 * s ^ 2 := by nlinarith [hs.1, hs.2]
  have hx' : 1 - 4 * s ^ 2 < 1 := by nlinarith [hs.1]
  unfold radius
  exact ⟨Real.sqrt_pos.2 hx, (Real.sqrt_lt' (by norm_num)).2 (by simpa using hx')⟩

theorem logRatio_lower {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    2 * t ≤ logRatio t := by
  have h := Real.sum_range_le_log_div ht0 ht1 1
  norm_num at h
  have hplus : 1 + t ≠ 0 := by linarith
  have hminus : 1 - t ≠ 0 := by linarith
  rw [Real.log_div hplus hminus] at h
  unfold logRatio
  linarith

theorem hasDerivAt_radius {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt radius (-4 * s / radius s) s := by
  have hx : 1 - 4 * s ^ 2 ≠ 0 := by nlinarith [hs.1, hs.2]
  have hd := (Real.hasDerivAt_sqrt hx).comp s
    ((hasDerivAt_const s (1 : ℝ)).sub (((hasDerivAt_id s).pow 2).const_mul 4))
  convert! hd using 1
  simp [radius]
  ring

theorem binEntropy_derivative_radius {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    Real.log (1 - (1 + radius s) / 2) - Real.log ((1 + radius s) / 2) =
      -logRatio (radius s) := by
  have ht := radius_pos_lt_one hs
  have hm : 1 - radius s ≠ 0 := by linarith
  have hp : 1 + radius s ≠ 0 := by linarith
  rw [show 1 - (1 + radius s) / 2 = (1 - radius s) / 2 by ring,
    Real.log_div hm (by norm_num), Real.log_div hp (by norm_num)]
  unfold logRatio
  ring

theorem hasDerivAt_wootters {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt wootters (woottersSlope s) s := by
  have ht := radius_pos_lt_one hs
  have hx0 : (1 + radius s) / 2 ≠ 0 := by linarith
  have hx1 : (1 + radius s) / 2 ≠ 1 := by linarith
  have hd := (Real.hasDerivAt_binEntropy hx0 hx1).comp s
    (((hasDerivAt_const s (1 : ℝ)).add (hasDerivAt_radius hs)).div_const 2)
  rw [binEntropy_derivative_radius hs] at hd
  convert! hd using 1
  unfold woottersSlope
  ring

theorem deriv_wootters {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    deriv wootters s = woottersSlope s := (hasDerivAt_wootters hs).deriv

theorem deriv2_wootters {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) (1 / 2)) :
    deriv^[2] wootters s =
      2 * (logRatio (radius s) - 2 * radius s) / radius s ^ 3 := by
  have he : deriv wootters =ᶠ[𝓝 s] woottersSlope := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx
    exact deriv_wootters hx
  exact he.deriv_eq.trans (hasDerivAt_woottersSlope hs).deriv

theorem convexOn_wootters : ConvexOn ℝ (Icc (0 : ℝ) (1 / 2)) wootters := by
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _) continuous_wootters.continuousOn
  · intro s hs
    rw [interior_Icc] at hs
    exact (hasDerivAt_wootters hs).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    have he : deriv wootters =ᶠ[𝓝 s] woottersSlope := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx
      exact deriv_wootters hx
    exact ((hasDerivAt_woottersSlope hs).differentiableAt.congr_of_eventuallyEq he).differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    rw [deriv2_wootters hs]
    have ht := radius_pos_lt_one hs
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.2 (logRatio_lower ht.1.le ht.2)))
      (pow_nonneg ht.1.le _)

theorem monotoneOn_wootters : MonotoneOn wootters (Icc (0 : ℝ) (1 / 2)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    continuous_wootters.continuousOn
  · intro s hs
    rw [interior_Icc] at hs
    exact (hasDerivAt_wootters hs).hasDerivWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    have ht := radius_pos_lt_one hs
    unfold woottersSlope
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hs.1.le) ht.1.le)
      (le_trans (mul_nonneg (by norm_num) ht.1.le) (logRatio_lower ht.1.le ht.2))

theorem v_nonneg {γ ν : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1)
    (hν : ν ∈ Icc (0 : ℝ) 1) (p : ℝ) : 0 ≤ v γ ν p := by
  unfold v
  exact add_nonneg (mul_nonneg (mul_nonneg hγ.1 hν.1) (sub_nonneg.2 hν.2))
    (mul_nonneg (mul_nonneg hγ.1 (sub_nonneg.2 hγ.2)) (sq_nonneg _))

theorem v_population_form (γ ν p : ℝ) :
    v γ ν p = ((1 - γ) * p + γ * ν) * (1 - ((1 - γ) * p + γ * ν)) -
      (1 - γ) * p * (1 - p) := by
  unfold v
  ring

theorem v_le_quarter {γ ν : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1)
    (_hν : ν ∈ Icc (0 : ℝ) 1) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    v γ ν p ≤ 1 / 4 := by
  rw [v_population_form]
  have hsub : 0 ≤ (1 - γ) * p * (1 - p) :=
    mul_nonneg (mul_nonneg (sub_nonneg.2 hγ.2) hp.1) (sub_nonneg.2 hp.2)
  nlinarith [sq_nonneg (((1 - γ) * p + γ * ν) - 1 / 2)]

theorem sqrt_v_mem {γ ν : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1)
    (hν : ν ∈ Icc (0 : ℝ) 1) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    Real.sqrt (v γ ν p) ∈ Icc (0 : ℝ) (1 / 2) := by
  refine ⟨Real.sqrt_nonneg _, (Real.sqrt_le_left (by norm_num)).2 ?_⟩
  convert v_le_quarter hγ hν hp using 1
  norm_num

theorem convexOn_sqrt_v {γ ν : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1)
    (hν : ν ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun p ↦ Real.sqrt (v γ ν p)) := by
  let z : ℝ → ℂ := fun p ↦ ⟨Real.sqrt (γ * ν * (1 - ν)),
    Real.sqrt (γ * (1 - γ)) * (p - ν)⟩
  have hA : 0 ≤ γ * ν * (1 - ν) :=
    mul_nonneg (mul_nonneg hγ.1 hν.1) (sub_nonneg.2 hν.2)
  have hB : 0 ≤ γ * (1 - γ) := mul_nonneg hγ.1 (sub_nonneg.2 hγ.2)
  have hz (p : ℝ) : ‖z p‖ = Real.sqrt (v γ ν p) := by
    rw [Complex.norm_def]
    congr 1
    dsimp [z]
    calc
      _ = Real.sqrt (γ * ν * (1 - ν)) ^ 2 +
          Real.sqrt (γ * (1 - γ)) ^ 2 * (p - ν) ^ 2 := by ring
      _ = v γ ν p := by rw [Real.sq_sqrt hA, Real.sq_sqrt hB]; rfl
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  change Real.sqrt (v γ ν (a * x + b * y)) ≤
    a * Real.sqrt (v γ ν x) + b * Real.sqrt (v γ ν y)
  rw [← hz, ← hz, ← hz]
  have he : z (a * x + b * y) = a • z x + b • z y := by
    have hb' : b = 1 - a := by linarith
    rw [hb']
    apply Complex.ext <;> simp [z] <;> ring
  rw [he]
  calc
    _ ≤ ‖a • z x‖ + ‖b • z y‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ha, abs_of_nonneg hb]

theorem wootters_sqrt {u : ℝ} (hu : 0 ≤ u) : wootters (Real.sqrt u) = g u := by
  unfold wootters
  rw [Real.sq_sqrt hu]

theorem convexOn_output_entropy {γ ν : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1)
    (hν : ν ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun p ↦ g (v γ ν p)) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy := (convex_Icc (0 : ℝ) 1) hx hy ha hb hab
  have hx' := sqrt_v_mem hγ hν hx
  have hy' := sqrt_v_mem hγ hν hy
  have hxy' := sqrt_v_mem hγ hν hxy
  have hc := (convex_Icc (0 : ℝ) (1 / 2)) hx' hy' ha hb hab
  have hm := monotoneOn_wootters hxy' hc ((convexOn_sqrt_v hγ hν).2 hx hy ha hb hab)
  have hh := hm.trans (convexOn_wootters.2 hx' hy' ha hb hab)
  simpa only [wootters_sqrt (v_nonneg hγ hν _)] using hh

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

theorem population_nonneg {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) :
    0 ≤ population ψ j := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact Complex.normSq_nonneg _
  · rfl

theorem population_le_mass {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) :
    population ψ j ≤ vecMass ψ := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · rfl
  · exact Complex.normSq_nonneg _

theorem population_mem {n : ℕ} {ψ : Basis n → ℂ} (hψ : vecMass ψ = 1) (j : Fin n) :
    population ψ j ∈ Set.Icc (0:ℝ) 1 :=
  ⟨population_nonneg ψ j, hψ ▸ population_le_mass ψ j⟩

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_2} {κ : Type u_3} {ρ : Type u_4} [Fintype ι] [Fintype κ] [Fintype ρ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]

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

theorem mixed_output_entropy_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) {P : QMatrix n} (hP : IsState P) :
    ∑ j, g (v γ ν (matrixPopulation P j)) ≤ entropy (channel γ ν n P) := by
  let w := hP.1.isHermitian.eigenvalues
  let ψ := fun a i ↦ hP.1.isHermitian.eigenvectorUnitary i a
  have hw (a) : 0 ≤ w a := hP.1.eigenvalues_nonneg a
  have hs : ∑ a, w a = 1 := spectral_weights_sum hP
  have hv (a) : vecMass (ψ a) = 1 := spectral_vectors_mass hP.1.isHermitian a
  have hdecomp : P = ∑ a, w a • pure (ψ a) := spectral_pure_decomposition hP.1.isHermitian
  have hchan : channel γ ν n P = ∑ a, w a • channel γ ν n (pure (ψ a)) := by
    rw [hdecomp,channel_mixture]
  have hpop (j) : matrixPopulation P j = ∑ a, w a * population (ψ a) j := by
    conv_lhs => rw [hdecomp]
    rw [matrixPopulation_mixture]
    simp only [matrixPopulation_pure]
  have hj (j) : g (v γ ν (matrixPopulation P j)) ≤ ∑ a, w a*g (v γ ν (population (ψ a) j)) := by
    rw [hpop]
    exact (convexOn_output_entropy hγ hν).map_sum_le (fun a _ ↦ hw a) hs
      (fun a _ ↦ population_mem (hv a) j)
  calc
    ∑ j, g (v γ ν (matrixPopulation P j)) ≤
        ∑ j, ∑ a, w a*g (v γ ν (population (ψ a) j)) :=
      Finset.sum_le_sum (fun j _ ↦ hj j)
    _ = ∑ a, w a * ∑ j, g (v γ ν (population (ψ a) j)) := by
      rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ a, w a * entropy (channel γ ν n (pure (ψ a))) :=
      Finset.sum_le_sum (fun a _ ↦ mul_le_mul_of_nonneg_left
        (pure_output_entropy_bound γ ν hγ hν n (ψ a) (hv a)) (hw a))
    _ ≤ entropy (channel γ ν n P) := by
      rw [hchan]
      exact concaveOn_entropy.le_map_sum (fun a _ ↦ hw a) hs
        (fun a _ ↦ channel_posSemidef γ ν n (pure_posSemidef (ψ a)))

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.mixed_output_entropy_bound := @_root_.OAI.GAD.mixed_output_entropy_bound
