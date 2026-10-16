-- Prove2me | solution 1 for OAI.GAD.ensemble_nats_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:31:11.582727+00:00
-- url     : https://prove2.me/submissions/42532388-326b-4f52-9542-096333a9578b

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/EnsembleBounds.lean:L112-L145
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.ensemble_nats_upper. The node keeps its source
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
import Theorems.Thm_OAI_GAD_channel_population
import Theorems.Thm_OAI_GAD_entropy_le_diagonal
import Theorems.Thm_OAI_GAD_hasDerivAt_woottersSlope
import Theorems.Thm_OAI_GAD_kraus_complete
import Theorems.Thm_OAI_GAD_mixed_output_entropy_bound

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

theorem channel_mixture (γ ν : ℝ) (n : ℕ) (w : α → ℝ) (P : α → QMatrix n) :
    channel γ ν n (∑ a, w a • P a) = ∑ a, w a • channel γ ν n (P a) := by
  simp only [channel,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]

theorem matrixPopulation_mixture {n : ℕ} (w : α → ℝ) (P : α → QMatrix n) (j : Fin n) :
    matrixPopulation (∑ a, w a • P a) j = ∑ a, w a * matrixPopulation (P a) j := by
  simp only [matrixPopulation,Matrix.sum_apply,Complex.re_sum,Matrix.smul_apply,
    Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem matrixPopulation_nonneg {n : ℕ} {P : QMatrix n} (hP : P.PosSemidef) (j : Fin n) :
    0 ≤ matrixPopulation P j := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (Complex.nonneg_iff.mp hP.diag_nonneg).1
  · rfl

theorem matrixPopulation_le_trace {n : ℕ} {P : QMatrix n} (hP : P.PosSemidef) (j : Fin n) :
    matrixPopulation P j ≤ P.trace.re := by
  rw [Matrix.trace,Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact (Complex.nonneg_iff.mp hP.diag_nonneg).1

theorem matrixPopulation_mem {n : ℕ} {P : QMatrix n} (hP : IsState P) (j : Fin n) :
    matrixPopulation P j ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨matrixPopulation_nonneg hP.1 j, ?_⟩
  simpa only [hP.2,Complex.one_re] using matrixPopulation_le_trace hP.1 j

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {α : Type u_4} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.EnsembleBounds ----
namespace OAI

noncomputable section

section
open scoped BigOperators
namespace GAD

/-- Binary Shannon entropy is concave, including the endpoints. -/
theorem concaveOn_binEntropy : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) Real.binEntropy := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro p hp q hq a b ha hb hab
  have h₀ := Real.concaveOn_negMulLog.2 hp.1 hq.1 ha hb hab
  have h₁ := Real.concaveOn_negMulLog.2 (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hq.2) ha hb hab
  have heq : 1-(a*p+b*q)=a*(1-p)+b*(1-q) := by nlinarith only [hab]
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,smul_eq_mul,heq] at *
  linarith

theorem weighted_conditional_eq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a+b)*(b/(a+b))=b := by
  by_cases h : a+b=0
  · have : b=0 := by linarith
    simp [this]
  · exact mul_div_cancel₀ _ h

theorem conditional_mem (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    b/(a+b) ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨div_nonneg hb (add_nonneg ha hb), ?_⟩
  by_cases h : a+b=0
  · simp [h]
  · exact (div_le_one (lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h))).mpr (by linarith)

theorem negMulLog_split (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog a+Real.negMulLog b =
      Real.negMulLog (a+b)+(a+b)*Real.binEntropy (b/(a+b)) := by
  have hb' := weighted_conditional_eq a b ha hb
  have ha' : (a+b)*(1-b/(a+b))=a := by nlinarith only [hb']
  have hA := Real.negMulLog_mul (a+b) (1-b/(a+b))
  have hB := Real.negMulLog_mul (a+b) (b/(a+b))
  rw [ha'] at hA
  rw [hb'] at hB
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  nlinarith only [hA,hB]

theorem classical_entropy_le_sum_binary (n : ℕ) (q : Basis n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1) :
    ∑ i, Real.negMulLog (q i) ≤ ∑ j, Real.binEntropy (distPopulation q j) := by
  induction n with
  | zero =>
      have hq1 (i : Basis 0) : q i = 1 := by
        rw [Fintype.sum_unique] at hs
        convert hs using 1
        exact congrArg q (Subsingleton.elim _ _)
      simp only [hq1,Real.negMulLog_one,Finset.sum_const_zero,Fintype.sum_empty,le_refl]
  | succ n ih =>
      let t : Basis n → ℝ := fun i ↦ q (Fin.cons 0 i)+q (Fin.cons 1 i)
      have ht (i) : 0 ≤ t i := add_nonneg (hq _) (hq _)
      have ht1 : ∑ i, t i = 1 := by
        rw [sum_fin_cons] at hs
        simpa only [Fin.sum_univ_two,← Finset.sum_add_distrib,t] using hs
      have hsplit : (∑ i, Real.negMulLog (q i)) =
          (∑ i, Real.negMulLog (t i)) +
            ∑ i, t i*Real.binEntropy (q (Fin.cons 1 i)/t i) := by
        rw [sum_fin_cons,Fin.sum_univ_two,← Finset.sum_add_distrib]
        simp only [negMulLog_split _ _ (hq _) (hq _),Finset.sum_add_distrib,t]
      have hmean : (∑ i, t i*(q (Fin.cons 1 i)/t i)) = distPopulation q 0 := by
        simp only [t,weighted_conditional_eq _ _ (hq _) (hq _)]
        unfold distPopulation
        rw [sum_fin_cons]
        simp
      have hJ : (∑ i, t i*Real.binEntropy (q (Fin.cons 1 i)/t i)) ≤
          Real.binEntropy (distPopulation q 0) := by
        rw [← hmean]
        exact concaveOn_binEntropy.le_map_sum (fun i _ ↦ ht i) ht1
          (fun i _ ↦ conditional_mem _ _ (hq _) (hq _))
      have hpop (j : Fin n) : distPopulation t j = distPopulation q j.succ := by
        unfold distPopulation
        rw [sum_fin_cons]
        simp [Fin.sum_univ_two,t,← Finset.sum_add_distrib,ite_add_ite]
      calc
        (∑ i, Real.negMulLog (q i)) = _ := hsplit
        _ ≤ (∑ j, Real.binEntropy (distPopulation t j))+Real.binEntropy (distPopulation q 0) :=
          add_le_add (ih t ht ht1) hJ
        _ = _ := by simp only [hpop,Fin.sum_univ_succ]; ring

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem entropy_le_sum_populations {n : ℕ} {P : QMatrix n} (hP : IsState P) :
    entropy P ≤ ∑ j, Real.binEntropy (matrixPopulation P j) := by
  have hdiag (i : Basis n) : 0 ≤ (P i i).re := (Complex.nonneg_iff.mp hP.1.diag_nonneg).1
  have hs : ∑ i, (P i i).re=1 := by
    simpa only [Matrix.trace,Matrix.diag,Complex.re_sum,Complex.one_re] using congrArg Complex.re hP.2
  exact (entropy_le_diagonal hP.1).trans (classical_entropy_le_sum_binary n _ hdiag hs)

theorem output_entropy_upper (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} {P : QMatrix n} (hP : IsState P) :
    entropy (channel γ ν n P) ≤ ∑ j, Real.binEntropy ((1-γ)*matrixPopulation P j+γ*ν) := by
  simpa only [channel_population γ ν hγ hν hP] using
    entropy_le_sum_populations (channel_state γ ν hγ hν n hP)

theorem ensemble_nats_upper (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (E : Ensemble n) {p : ℝ} (hp : Maximizes γ ν p) :
    entropy (∑ a, (E.weight a : ℂ) • channel γ ν n (E.signal a)) -
      (∑ a, E.weight a * entropy (channel γ ν n (E.signal a))) ≤
    (n : ℝ)*objective γ ν p := by
  let P := ∑ a, E.weight a • E.signal a
  have hP : IsState P := state_mixture E.weight E.signal E.weight_nonneg E.weight_sum E.signal_state
  have hpop (j) : (∑ a, E.weight a*matrixPopulation (E.signal a) j) = matrixPopulation P j :=
    (matrixPopulation_mixture E.weight E.signal j).symm
  have hJ (j) : g (v γ ν (matrixPopulation P j)) ≤
      ∑ a, E.weight a*g (v γ ν (matrixPopulation (E.signal a) j)) := by
    rw [← hpop]
    exact (convexOn_output_entropy hγ hν).map_sum_le
      (fun a _ ↦ E.weight_nonneg a) E.weight_sum
      (fun a _ ↦ matrixPopulation_mem (E.signal_state a) j)
  have hlow : (∑ j, g (v γ ν (matrixPopulation P j))) ≤
      ∑ a, E.weight a*entropy (channel γ ν n (E.signal a)) := by
    calc
      _ ≤ ∑ j, ∑ a, E.weight a*g (v γ ν (matrixPopulation (E.signal a) j)) :=
        Finset.sum_le_sum (fun j _ ↦ hJ j)
      _ = ∑ a, E.weight a * ∑ j, g (v γ ν (matrixPopulation (E.signal a) j)) := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (fun a _ ↦ mul_le_mul_of_nonneg_left
        (mixed_output_entropy_bound γ ν hγ hν n (E.signal_state a)) (E.weight_nonneg a))
  have hu := output_entropy_upper γ ν hγ hν hP
  have hv : (∑ j, objective γ ν (matrixPopulation P j)) ≤ (n:ℝ)*objective γ ν p := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hp.2 _ (matrixPopulation_mem hP j))
  have heq : (∑ a, (E.weight a : ℂ) • channel γ ν n (E.signal a)) = channel γ ν n P := by
    simp only [Complex.coe_smul, P,channel_mixture]
  rw [heq]
  simp only [objective,Finset.sum_sub_distrib] at hv
  dsimp only [objective]
  linarith

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.ensemble_nats_upper := @_root_.OAI.GAD.ensemble_nats_upper
