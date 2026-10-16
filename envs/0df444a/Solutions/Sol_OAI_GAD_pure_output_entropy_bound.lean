-- Prove2me | solution 1 for OAI.GAD.pure_output_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:23:38.855061+00:00
-- url     : https://prove2.me/submissions/bc3101b6-cb82-43d1-b1d8-169d5883bf2d

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/OutputEntropy.lean:L14-L56
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.pure_output_entropy_bound. The node keeps its source
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
import Theorems.Thm_OAI_GAD_hasDerivAt_woottersSlope
import Theorems.Thm_OAI_GAD_kraus_complete
import Theorems.Thm_OAI_GAD_output_entropy_recursion

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
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

namespace GAD

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_1} [Fintype ι]

theorem vecMass_nonneg (ψ : ι → ℂ) : 0 ≤ vecMass ψ :=
  Finset.sum_nonneg (fun i _ ↦ Complex.normSq_nonneg (ψ i))

theorem vecMass_eq_zero {ψ : ι → ℂ} : vecMass ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    funext i
    apply Complex.normSq_eq_zero.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ Complex.normSq_nonneg (ψ i))).mp h i
      (Finset.mem_univ i)
  · rintro rfl
    simp [vecMass]

variable [DecidableEq ι]

omit [DecidableEq ι] in
theorem vecMass_smul (z : ℂ) (ψ : ι → ℂ) :
    vecMass (z • ψ) = Complex.normSq z * vecMass ψ := by
  simp [vecMass, Complex.normSq_mul, Finset.mul_sum]

theorem sqrt_mass_normalize [Inhabited ι] (ψ : ι → ℂ) :
    (Real.sqrt (vecMass ψ) : ℂ) • normalize ψ = ψ := by
  by_cases h : vecMass ψ = 0
  · have hz := vecMass_eq_zero.mp h
    simp [normalize,hz,vecMass]
  · have hs : (Real.sqrt (vecMass ψ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (vecMass_nonneg ψ) (Ne.symm h)))
    simp [normalize,h,smul_smul,hs]

theorem normalize_mass [Inhabited ι] (ψ : ι → ℂ) : vecMass (normalize ψ) = 1 := by
  by_cases h : vecMass ψ = 0
  · simp [normalize,h]
  · have hs : Real.sqrt (vecMass ψ)*Real.sqrt (vecMass ψ) = vecMass ψ := Real.mul_self_sqrt (vecMass_nonneg ψ)
    simp only [normalize, ite_eq_right h, vecMass_smul, map_inv₀, Complex.normSq_ofReal, hs]
    exact inv_mul_cancel₀ h

theorem normSq_normalize [Inhabited ι] (ψ : ι → ℂ) (i : ι) :
    Complex.normSq (ψ i) = vecMass ψ * Complex.normSq (normalize ψ i) := by
  calc
    Complex.normSq (ψ i) = Complex.normSq (((Real.sqrt (vecMass ψ) : ℂ) • normalize ψ) i) :=
      congrArg (fun f : ι → ℂ ↦ Complex.normSq (f i)) (sqrt_mass_normalize ψ).symm
    _ = _ := by simp [Complex.normSq_mul, Real.mul_self_sqrt (vecMass_nonneg ψ)]

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

theorem vecMass_branches {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    vecMass ψ = vecMass (branch ψ 0) + vecMass (branch ψ 1) := by
  unfold vecMass
  rw [sum_fin_cons]
  simp [Fin.sum_univ_two,branch]

theorem population_succ {n : ℕ} (ψ : Basis (n+1) → ℂ) (j : Fin n) :
    population ψ j.succ = population (branch ψ 0) j + population (branch ψ 1) j := by
  unfold population
  rw [sum_fin_cons]
  simp [Fin.sum_univ_two,branch]

theorem population_normalize {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) :
    population ψ j = vecMass ψ * population (normalize ψ) j := by
  simp only [population,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · exact normSq_normalize ψ i
  · exact (mul_zero _).symm

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

-- ---- from OAI.InformationTheory.AmplitudeDamping.OutputEntropy ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

/-- The population-dependent lower bound for every pure input, including entangled inputs. -/
theorem pure_output_entropy_bound (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) (ψ : Basis n → ℂ)
    (hψ : vecMass ψ = 1) :
    ∑ j, g (v γ ν (population ψ j)) ≤ entropy (channel γ ν n (pure ψ)) := by
  induction n with
  | zero =>
      simpa using entropy_nonneg (channel_state γ ν hγ hν 0 (pure_state hψ))
  | succ n ih =>
      let x := vecMass (branch ψ 0)
      let y := vecMass (branch ψ 1)
      let ψ₀ := normalize (branch ψ 0)
      let ψ₁ := normalize (branch ψ 1)
      have hx : 0 ≤ x := vecMass_nonneg _
      have hy : 0 ≤ y := vecMass_nonneg _
      have hxy : x+y=1 := (vecMass_branches ψ).symm.trans hψ
      have h₀ := ih ψ₀ (normalize_mass _)
      have h₁ := ih ψ₁ (normalize_mass _)
      have hpop (j : Fin n) : population ψ j.succ = x*population ψ₀ j+y*population ψ₁ j := by
        rw [population_succ,population_normalize (branch ψ 0),population_normalize (branch ψ 1)]
      have hj (j : Fin n) : g (v γ ν (population ψ j.succ)) ≤
          x*g (v γ ν (population ψ₀ j))+y*g (v γ ν (population ψ₁ j)) := by
        rw [hpop]
        exact (convexOn_output_entropy hγ hν).2
          (population_mem (normalize_mass _) j) (population_mem (normalize_mass _) j) hx hy hxy
      calc
        ∑ j, g (v γ ν (population ψ j)) =
            g (v γ ν (population ψ 0))+∑ j : Fin n, g (v γ ν (population ψ j.succ)) :=
          Fin.sum_univ_succ _
        _ ≤ g (v γ ν (population ψ 0))+
            ∑ j : Fin n, (x*g (v γ ν (population ψ₀ j))+y*g (v γ ν (population ψ₁ j))) :=
          add_le_add le_rfl (Finset.sum_le_sum (fun j _ ↦ hj j))
        _ = g (v γ ν (population ψ 0))+
            (x*(∑ j, g (v γ ν (population ψ₀ j)))+y*(∑ j, g (v γ ν (population ψ₁ j)))) := by
          rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
        _ ≤ g (v γ ν (population ψ 0))+
            (x*entropy (channel γ ν n (pure ψ₀))+y*entropy (channel γ ν n (pure ψ₁))) :=
          add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_left h₀ hx)
            (mul_le_mul_of_nonneg_left h₁ hy))
        _ ≤ entropy (channel γ ν (n+1) (pure ψ)) := by
          have h := output_entropy_recursion γ ν hγ hν ψ hψ
          dsimp [x,y,ψ₀,ψ₁]
          linarith

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


theorem solution : type_of% @_root_.OAI.GAD.pure_output_entropy_bound := @_root_.OAI.GAD.pure_output_entropy_bound
