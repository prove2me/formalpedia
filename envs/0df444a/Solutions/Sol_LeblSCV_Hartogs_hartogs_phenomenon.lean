-- Prove2me | solution 1 for LeblSCV.Hartogs.hartogs_phenomenon
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T11:16:58.578996+00:00
-- url     : https://prove2.me/submissions/5636945e-b423-4a44-9b1e-8b6a2a83f097

import Mathlib
import Definitions.Def_LeblSCV_Shared_wirtingerBar
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn
import Definitions.Def_LeblSCV_Holomorphic_wirtinger
import Theorems.Thm_LeblSCV_Hartogs_compactly_supported_dbar
import Theorems.Thm_LeblSCV_Holomorphic_holomorphic_contDiff_and_wirtinger_holomorphic

set_option autoImplicit false

open Filter Topology Set
open scoped ContDiff

namespace HartogsGlue

variable {n : ℕ}

/-- The map `ξ ↦ update z k (z k + ξ)` is complex differentiable. -/
theorem differentiable_update_add (z : Fin n → ℂ) (k : Fin n) :
    Differentiable ℂ (fun ξ : ℂ => Function.update z k (z k + ξ)) := by
  intro ξ
  rw [differentiableAt_pi]
  intro j
  by_cases h : j = k
  · subst h
    simp only [Function.update_self]
    fun_prop
  · simp only [Function.update_of_ne h]
    fun_prop

/-- G0: complex differentiable on an open set implies holomorphic in Lebl's sense. -/
theorem isHolomorphicOn_of_differentiableOn {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) :
    LeblSCV.Holomorphic.IsHolomorphicOn f U := by
  constructor
  · intro p hp
    have hc : ContinuousAt f p := (hf.differentiableAt (hU.mem_nhds hp)).continuousAt
    exact ⟨{w | ‖f w‖ < ‖f p‖ + 1}, hc.norm.eventually (gt_mem_nhds (lt_add_one ‖f p‖)),
      ‖f p‖ + 1, fun w hw => hw.1.le⟩
  · intro z hz k
    have hd : DifferentiableAt ℂ f (Function.update z k (z k + 0)) := by
      rw [add_zero, Function.update_eq_self]
      exact hf.differentiableAt (hU.mem_nhds hz)
    exact hd.comp (0 : ℂ) (differentiable_update_add z k 0)

/-- Vanishing propagates along complex lines inside a ball. -/
theorem eqOn_zero_ball {f : (Fin n → ℂ) → ℂ} {z a : Fin n → ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball z r)) (ha : a ∈ Metric.ball z r)
    (h0 : f =ᶠ[𝓝 a] 0) : EqOn f 0 (Metric.ball z r) := by
  intro w hw
  set φ : ℂ → (Fin n → ℂ) := fun t => a + t • (w - a) with hφ
  have hφd : Differentiable ℂ φ := by
    intro t
    simp only [hφ]
    fun_prop
  have hφc : Continuous φ := hφd.continuous
  set T : Set ℂ := φ ⁻¹' Metric.ball z r with hT
  have hTo : IsOpen T := Metric.isOpen_ball.preimage hφc
  have hTc : Convex ℝ T := by
    intro s hs t ht c d hc hd hcd
    simp only [hT, mem_preimage, hφ] at hs ht ⊢
    have hcv := (convex_ball z r) hs ht hc hd hcd
    convert hcv using 1
    have hcd' : (c : ℂ) + d = 1 := by exact_mod_cast hcd
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, Pi.sub_apply]
    linear_combination (-(a i)) * hcd'
  have hg : DifferentiableOn ℂ (f ∘ φ) T := hf.comp hφd.differentiableOn (fun t ht => ht)
  have hga : AnalyticOnNhd ℂ (f ∘ φ) T := hg.analyticOnNhd hTo
  have h0T : (0 : ℂ) ∈ T := by simp [hT, hφ, ha]
  have h1T : (1 : ℂ) ∈ T := by simp [hT, hφ, hw]
  have hev : (f ∘ φ) =ᶠ[𝓝 0] 0 := by
    have htend : Tendsto φ (𝓝 0) (𝓝 a) := by
      have := hφc.tendsto 0
      simpa [hφ] using this
    filter_upwards [htend.eventually h0] with t ht
    simpa using ht
  have := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero hTc.isPreconnected h0T hev h1T
  simpa [hφ] using this

/-- G1: identity theorem for complex differentiable functions of several variables. -/
theorem eqOn_zero_of_preconnected {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) {z₀ : Fin n → ℂ} (hz₀ : z₀ ∈ U)
    (h0 : f =ᶠ[𝓝 z₀] 0) : EqOn f 0 U := by
  have hAo : IsOpen {z | f =ᶠ[𝓝 z] 0} := isOpen_setOfPred_eventually_nhds
  have hsub : U ⊆ {z | f =ᶠ[𝓝 z] 0} := by
    refine hUc.subset_of_closure_inter_subset hAo ⟨z₀, hz₀, h0⟩ ?_
    rintro z ⟨hzc, hzU⟩
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hzU
    obtain ⟨a, haA, hda⟩ := Metric.mem_closure_iff.1 hzc r hr
    have hab : a ∈ Metric.ball z r := Metric.mem_ball.2 (by rwa [dist_comm])
    exact Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds z hr)
      (eqOn_zero_ball (hf.mono hrU) hab haA)
  intro z hz
  exact (hsub hz).eq_of_nhds

/-- G1': two holomorphic functions agreeing near a point of a domain agree on it. -/
theorem eqOn_of_preconnected {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f g : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {z₀ : Fin n → ℂ} (hz₀ : z₀ ∈ U) (h0 : f =ᶠ[𝓝 z₀] g) : EqOn f g U := by
  have h := eqOn_zero_of_preconnected hU hUc (hf.sub hg) hz₀
    (by filter_upwards [h0] with x hx; simp [hx])
  intro z hz
  exact sub_eq_zero.1 (h hz)

/-- The real line `t ↦ update z k (z k + t v)` has velocity `Pi.single k v`. -/
theorem hasDerivAt_update_line (z : Fin n → ℂ) (k : Fin n) (v : ℂ) :
    HasDerivAt (fun t : ℝ => Function.update z k (z k + (t : ℂ) * v)) (Pi.single k v) 0 := by
  rw [hasDerivAt_pi]
  intro j
  by_cases h : j = k
  · subst h
    simp only [Function.update_self, Pi.single_eq_same]
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const v).const_add (z j)
    simpa using this
  · simp only [Function.update_of_ne h, Pi.single_eq_of_ne h]
    exact hasDerivAt_const _ _

theorem deriv_line_eq (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (k : Fin n) (v : ℂ)
    (hf : DifferentiableAt ℝ f z) :
    deriv (fun t : ℝ => f (Function.update z k (z k + (t : ℂ) * v))) 0 =
      fderiv ℝ f z (Pi.single k v) := by
  have hz : Function.update z k (z k + ((0 : ℝ) : ℂ) * v) = z := by simp
  have hf' : HasFDerivAt f (fderiv ℝ f z) (Function.update z k (z k + ((0 : ℝ) : ℂ) * v)) := by
    rw [hz]; exact hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_update_line z k v)).deriv

/-- `∂f/∂z̄_k` in terms of the real Fréchet derivative. -/
theorem wirtingerBar_eq_fderiv {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (k : Fin n)
    (hf : DifferentiableAt ℝ f z) :
    LeblSCV.Shared.wirtingerBar k f z = (1 / 2 : ℂ) *
      (fderiv ℝ f z (Pi.single k 1) + Complex.I * fderiv ℝ f z (Pi.single k Complex.I)) := by
  have h1 := deriv_line_eq f z k 1 hf
  have h2 := deriv_line_eq f z k Complex.I hf
  simp only [mul_one] at h1
  simp only [LeblSCV.Shared.wirtingerBar]
  rw [h1, h2]

theorem single_I_eq (k : Fin n) :
    (Pi.single k Complex.I : Fin n → ℂ) = Complex.I • (Pi.single k 1 : Fin n → ℂ) := by
  ext j
  by_cases hj : j = k
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

/-- Holomorphic functions satisfy `∂f/∂z̄_k = 0`. -/
theorem wirtingerBar_eq_zero_of_differentiableAt {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℂ f z) (k : Fin n) : LeblSCV.Shared.wirtingerBar k f z = 0 := by
  rw [wirtingerBar_eq_fderiv k (hf.restrictScalars ℝ), hf.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [single_I_eq k, map_smul, smul_eq_mul]
  linear_combination ((1 / 2 : ℂ) * fderiv ℂ f z (Pi.single k 1)) * Complex.I_sq

/-- G4 (Cauchy-Riemann): real differentiable with all `∂f/∂z̄_k = 0` implies complex differentiable. -/
theorem differentiableAt_of_wirtingerBar_eq_zero {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℝ f z) (h : ∀ k, LeblSCV.Shared.wirtingerBar k f z = 0) :
    DifferentiableAt ℂ f z := by
  set L := fderiv ℝ f z with hL
  have hI : ∀ k, L (Pi.single k Complex.I) = Complex.I * L (Pi.single k 1) := by
    intro k
    have h0 := h k
    rw [wirtingerBar_eq_fderiv k hf] at h0
    have h2 : L (Pi.single k 1) + Complex.I * L (Pi.single k Complex.I) = 0 := by
      rcases mul_eq_zero.1 h0 with h3 | h3
      · norm_num at h3
      · exact h3
    linear_combination (-Complex.I) * h2 + (L (Pi.single k Complex.I)) * Complex.I_sq
  have hsingle : ∀ k (w : ℂ), L (Pi.single k w) = w * L (Pi.single k 1) := by
    intro k w
    have hw : (Pi.single k w : Fin n → ℂ) =
        w.re • (Pi.single k 1 : Fin n → ℂ) + w.im • (Pi.single k Complex.I : Fin n → ℂ) := by
      ext j
      by_cases hj : j = k
      · subst hj
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Complex.real_smul, mul_one]
        exact (Complex.re_add_im w).symm
      · simp [Pi.single_eq_of_ne hj]
    rw [hw, map_add, map_smul, map_smul, hI k, Complex.real_smul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im w]
    ring
  let L' : (Fin n → ℂ) →L[ℂ] ℂ := ∑ k, (L (Pi.single k 1)) • ContinuousLinearMap.proj k
  have hLL : L'.restrictScalars ℝ = L := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.coe_restrictScalars']
    conv_rhs => rw [← Finset.univ_sum_single v]
    rw [map_sum, Finset.sum_congr rfl fun k _ => hsingle k (v k)]
    simp [L']
    all_goals (refine Finset.sum_congr rfl fun k _ => ?_; ring)
  exact (hasFDerivAt_of_restrictScalars (𝕜 := ℝ) hf.hasFDerivAt hLL).differentiableAt

open Complex in
/-- `∂/∂z̄_k` depends only on the germ. -/
theorem wirtingerBar_congr {h₁ h₂ : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (k : Fin n)
    (h : h₁ =ᶠ[𝓝 z] h₂) : LeblSCV.Shared.wirtingerBar k h₁ z = LeblSCV.Shared.wirtingerBar k h₂ z := by
  have hc : ∀ v : ℂ, (fun t : ℝ => h₁ (Function.update z k (z k + (t : ℂ) * v))) =ᶠ[𝓝 0]
      (fun t : ℝ => h₂ (Function.update z k (z k + (t : ℂ) * v))) := by
    intro v
    have ht : Tendsto (fun t : ℝ => Function.update z k (z k + (t : ℂ) * v)) (𝓝 0) (𝓝 z) := by
      have := (hasDerivAt_update_line z k v).continuousAt.tendsto
      simpa using this
    exact ht.eventually h
  have h1 := (hc 1).deriv_eq
  have h2 := (hc I).deriv_eq
  simp only [mul_one] at h1
  simp only [LeblSCV.Shared.wirtingerBar]
  rw [h1, h2]

open Complex in
theorem contDiffOn_wirtingerBar {h : (Fin n → ℂ) → ℂ} {V : Set (Fin n → ℂ)} (hV : IsOpen V)
    (hh : ContDiffOn ℝ ∞ h V) (k : Fin n) :
    ContDiffOn ℝ ∞ (LeblSCV.Shared.wirtingerBar k h) V := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ h) V := hh.fderiv_of_isOpen hV (by simp)
  have he : ContDiffOn ℝ ∞ (fun z => (1 / 2 : ℂ) *
      (fderiv ℝ h z (Pi.single k 1) + I * fderiv ℝ h z (Pi.single k I))) V := by
    apply ContDiffOn.mul contDiffOn_const
    apply ContDiffOn.add
    · exact hd.clm_apply contDiffOn_const
    · exact contDiffOn_const.mul (hd.clm_apply contDiffOn_const)
  refine he.congr fun z hz => ?_
  exact wirtingerBar_eq_fderiv k ((hh.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hz))

theorem wirtingerBar_sub {h₁ h₂ : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (k : Fin n)
    (h1 : DifferentiableAt ℝ h₁ z) (h2 : DifferentiableAt ℝ h₂ z) :
    LeblSCV.Shared.wirtingerBar k (fun w => h₁ w - h₂ w) z =
      LeblSCV.Shared.wirtingerBar k h₁ z - LeblSCV.Shared.wirtingerBar k h₂ z := by
  have hd : DifferentiableAt ℝ (fun w => h₁ w - h₂ w) z := h1.sub h2
  have hfd : fderiv ℝ (fun w => h₁ w - h₂ w) z = fderiv ℝ h₁ z - fderiv ℝ h₂ z :=
    (h1.hasFDerivAt.sub h2.hasFDerivAt).fderiv
  rw [wirtingerBar_eq_fderiv k hd, wirtingerBar_eq_fderiv k h1,
    wirtingerBar_eq_fderiv k h2, hfd]
  simp only [ContinuousLinearMap.sub_apply]
  ring

open Complex in
/-- Mixed `∂̄` derivatives commute for smooth functions. -/
theorem wirtingerBar_comm {h : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} {V : Set (Fin n → ℂ)}
    (hV : IsOpen V) (hz : z ∈ V) (hh : ContDiffOn ℝ ∞ h V) (k l : Fin n) :
    LeblSCV.Shared.wirtingerBar l (LeblSCV.Shared.wirtingerBar k h) z =
      LeblSCV.Shared.wirtingerBar k (LeblSCV.Shared.wirtingerBar l h) z := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ h) V := hh.fderiv_of_isOpen hV (by simp)
  have hDd : DifferentiableAt ℝ (fderiv ℝ h) z :=
    (hD.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hz)
  have hsymm : IsSymmSndFDerivAt ℝ h z :=
    (hh.contDiffAt (hV.mem_nhds hz)).isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  set E := fderiv ℝ (fderiv ℝ h) z with hE
  have hap : ∀ a : Fin n → ℂ, HasFDerivAt (fun w => fderiv ℝ h w a) (E.flip a) z := by
    intro a
    have := hDd.hasFDerivAt.clm_apply (hasFDerivAt_const a z)
    simpa using this
  have key : ∀ k l : Fin n, LeblSCV.Shared.wirtingerBar l (LeblSCV.Shared.wirtingerBar k h) z =
      (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (E (Pi.single l 1) (Pi.single k 1) +
        I * E (Pi.single l 1) (Pi.single k I)) + I * ((1 / 2 : ℂ) *
        (E (Pi.single l I) (Pi.single k 1) + I * E (Pi.single l I) (Pi.single k I)))) := by
    intro k l
    have hev : LeblSCV.Shared.wirtingerBar k h =ᶠ[𝓝 z] fun w => (1 / 2 : ℂ) •
        (fderiv ℝ h w (Pi.single k 1) + I • fderiv ℝ h w (Pi.single k I)) := by
      filter_upwards [hV.mem_nhds hz] with w hw
      rw [wirtingerBar_eq_fderiv k ((hh.differentiableOn (by simp)).differentiableAt
        (hV.mem_nhds hw))]
      simp only [smul_eq_mul]
    have hWd : HasFDerivAt (fun w => (1 / 2 : ℂ) • (fderiv ℝ h w (Pi.single k 1) +
        I • fderiv ℝ h w (Pi.single k I)))
        ((1 / 2 : ℂ) • (E.flip (Pi.single k 1) + I • E.flip (Pi.single k I))) z := ((hap (Pi.single k 1)).add ((hap (Pi.single k I)).const_smul I)).const_smul
      (1 / 2 : ℂ)
    rw [wirtingerBar_congr l hev, wirtingerBar_eq_fderiv l hWd.differentiableAt, hWd.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
  have h1 := hsymm (Pi.single l 1) (Pi.single k 1)
  have h2 := hsymm (Pi.single l 1) (Pi.single k I)
  have h3 := hsymm (Pi.single l I) (Pi.single k 1)
  have h4 := hsymm (Pi.single l I) (Pi.single k I)
  rw [key k l, key l k]
  linear_combination (1 / 4 : ℂ) * h1 + (I / 4) * h2 + (I / 4) * h3 + (I ^ 2 / 4) * h4

open scoped Manifold in
/-- G2: smooth cutoff, equal to `1` near `K`, with compact topological support in `U`. -/
theorem exists_cutoff {U K : Set (Fin n → ℂ)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ IsCompact (tsupport χ) ∧ tsupport χ ⊆ U ∧
      ∃ W : Set (Fin n → ℂ), IsOpen W ∧ K ⊆ W ∧ EqOn χ 1 W := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨L2, hL2, hLL2, hL2U⟩ := exists_compact_between hL hU hLU
  obtain ⟨χ, hχd, -, hχs, hχ1⟩ := exists_contMDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (I := 𝓘(ℝ, Fin n → ℂ)) isOpen_interior hL.isClosed hLL2
  have hts : tsupport χ ⊆ L2 := by
    rw [tsupport, hχs]
    exact closure_minimal interior_subset hL2.isClosed
  refine ⟨χ, contMDiff_iff_contDiff.1 hχd, hL2.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hL2U, interior L, isOpen_interior, hKL, fun x hx => ?_⟩
  simpa using (hχ1 x).1 (interior_subset hx)

/-- Assembly of the Hartogs phenomenon from the compactly supported `∂̄` theorem (C1) and
regularity of holomorphic functions (C2). -/
theorem hartogs_of_children (hn : 2 ≤ n)
    (C1 : ∀ g : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ ∞ (g j)) → (∀ j, HasCompactSupport (g j)) →
      (∀ k l : Fin n, LeblSCV.Shared.wirtingerBar l (g k) = LeblSCV.Shared.wirtingerBar k (g l)) →
      ∃ ψ : (Fin n → ℂ) → ℂ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        ∀ k : Fin n, LeblSCV.Shared.wirtingerBar k ψ = g k)
    (C2 : ∀ V : Set (Fin n → ℂ), IsOpen V → ∀ f : (Fin n → ℂ) → ℂ,
      LeblSCV.Holomorphic.IsHolomorphicOn f V → ContDiffOn ℝ ∞ f V)
    {U K : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hUc : IsConnected U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hUK : IsConnected (U \ K)) {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (U \ K)) :
    ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ Set.EqOn F f (U \ K) ∧
      ∀ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G U → Set.EqOn G f (U \ K) →
        Set.EqOn G F U := by
  classical
  obtain ⟨χ, hχ, hχc, hχU, W, hWo, hKW, hχW⟩ := exists_cutoff hU hK hKU
  set S := tsupport χ with hS
  have hKS : K ⊆ S := fun z hz => subset_tsupport _ (by
    rw [Function.mem_support, hχW (hKW hz)]; norm_num)
  have hSo : IsOpen Sᶜ := (isClosed_tsupport χ).isOpen_compl
  have hUKo : IsOpen (U \ K) := hU.sdiff hK.isClosed
  have hfs : ContDiffOn ℝ ∞ f (U \ K) := C2 _ hUKo f (isHolomorphicOn_of_differentiableOn hUKo hf)
  have hχC : ContDiff ℝ ∞ (fun w => (χ w : ℂ)) := by
    simpa [Function.comp_def] using Complex.ofRealCLM.contDiff.comp hχ
  set Φ : (Fin n → ℂ) → ℂ := fun z => if z ∈ K then 0 else (1 - (χ z : ℂ)) * f z with hΦ
  have hΦW : ∀ z ∈ W, Φ z = 0 := by
    intro z hz
    simp [hΦ, hχW hz]
  have hΦS : ∀ z, z ∉ S → Φ =ᶠ[𝓝 z] f := by
    intro z hzS
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hzS, hSo.mem_nhds hzS] with w hw hwS
    have hwK : w ∉ K := fun h => hwS (hKS h)
    simp [hΦ, hwK, hw]
  have hΦs : ContDiffOn ℝ ∞ Φ U := by
    intro z hzU
    apply ContDiffAt.contDiffWithinAt
    by_cases hzK : z ∈ K
    · have h0 : Φ =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [hWo.mem_nhds (hKW hzK)] with w hw using hΦW w hw
      exact contDiffAt_const.congr_of_eventuallyEq h0
    · have hzUK : z ∈ U \ K := ⟨hzU, hzK⟩
      have h1 : ContDiffAt ℝ ∞ (fun w => (1 - (χ w : ℂ)) * f w) z :=
        (contDiffAt_const.sub hχC.contDiffAt).mul (hfs.contDiffAt (hUKo.mem_nhds hzUK))
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw
      simp [hΦ, show w ∉ K from hw]
  set g : Fin n → (Fin n → ℂ) → ℂ :=
    fun k z => if z ∈ U then LeblSCV.Shared.wirtingerBar k Φ z else 0 with hg
  have hgS : ∀ k z, z ∉ S → g k =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
    intro k z hzS
    filter_upwards [hSo.mem_nhds hzS] with w hwS
    simp only [hg]
    split_ifs with hwU
    · rw [wirtingerBar_congr k (hΦS w hwS)]
      exact wirtingerBar_eq_zero_of_differentiableAt
        (hf.differentiableAt (hUKo.mem_nhds ⟨hwU, fun h => hwS (hKS h)⟩)) k
    · rfl
  have hgU : ∀ k z, z ∈ U → g k =ᶠ[𝓝 z] LeblSCV.Shared.wirtingerBar k Φ := by
    intro k z hz
    filter_upwards [hU.mem_nhds hz] with w hw
    simp [hg, hw]
  have hgsm : ∀ k, ContDiff ℝ ∞ (g k) := by
    intro k
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact ((contDiffOn_wirtingerBar hU hΦs k).contDiffAt (hU.mem_nhds hz)).congr_of_eventuallyEq
        (hgU k z hz)
    · exact contDiffAt_const.congr_of_eventuallyEq (hgS k z (fun h => hz (hχU h)))
  have hgc : ∀ k, HasCompactSupport (g k) := fun k =>
    HasCompactSupport.intro hχc fun z hz => (hgS k z hz).eq_of_nhds
  have hcompat : ∀ k l : Fin n,
      LeblSCV.Shared.wirtingerBar l (g k) = LeblSCV.Shared.wirtingerBar k (g l) := by
    intro k l
    funext z
    by_cases hz : z ∈ U
    · rw [wirtingerBar_congr l (hgU k z hz), wirtingerBar_congr k (hgU l z hz)]
      exact wirtingerBar_comm hU hz hΦs k l
    · have hzS : z ∉ S := fun h => hz (hχU h)
      rw [wirtingerBar_congr l (hgS k z hzS), wirtingerBar_congr k (hgS l z hzS),
        wirtingerBar_eq_zero_of_differentiableAt (differentiableAt_const _) l,
        wirtingerBar_eq_zero_of_differentiableAt (differentiableAt_const _) k]
  obtain ⟨ψ, hψs, hψc, hψg⟩ := C1 g hgsm hgc hcompat
  set F : (Fin n → ℂ) → ℂ := fun z => Φ z - ψ z with hF
  have hFd : DifferentiableOn ℂ F U := by
    intro z hz
    have hΦd : DifferentiableAt ℝ Φ z :=
      (hΦs.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
    have hψd : DifferentiableAt ℝ ψ z := hψs.differentiable (by simp) z
    refine (differentiableAt_of_wirtingerBar_eq_zero (hΦd.sub hψd) fun k => ?_).differentiableWithinAt
    rw [show (Φ - ψ) = fun w => Φ w - ψ w from rfl, wirtingerBar_sub k hΦd hψd, hψg k]
    simp [hg, hz]
  have hψh : ∀ z, z ∉ S → DifferentiableAt ℂ ψ z := fun z hz =>
    differentiableAt_of_wirtingerBar_eq_zero (hψs.differentiable (by simp) z) fun k => by
      rw [hψg k]
      exact (hgS k z hz).eq_of_nhds
  have hSψ : IsCompact (S ∪ tsupport ψ) := hχc.union hψc
  obtain ⟨q, hq⟩ : ∃ q, q ∉ S ∪ tsupport ψ := by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    by_contra h
    push_neg at h
    exact noncompact_univ (Fin n → ℂ) (hSψ.of_isClosed_subset isClosed_univ fun x _ => h x)
  have hqS : q ∉ S := fun h => hq (Or.inl h)
  have hqψ : ψ =ᶠ[𝓝 q] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hq (Or.inr h)
  set Ω := connectedComponentIn Sᶜ q with hΩ
  have hΩo : IsOpen Ω := hSo.connectedComponentIn
  have hΩS : Ω ⊆ Sᶜ := connectedComponentIn_subset _ _
  have hqΩ : q ∈ Ω := mem_connectedComponentIn hqS
  have hψΩ : EqOn ψ 0 Ω := eqOn_zero_of_preconnected hΩo isPreconnected_connectedComponentIn
    (fun z hz => (hψh z (hΩS hz)).differentiableWithinAt) hqΩ hqψ
  have hΩU : (Ω ∩ U).Nonempty := by
    by_contra hne
    have hΩUc : Ω ⊆ Uᶜ := fun z hz hzU => hne ⟨z, hz, hzU⟩
    have hcl : closure Ω ⊆ Ω := by
      have h1 : closure Ω ⊆ Sᶜ :=
        (closure_minimal hΩUc hU.isClosed_compl).trans (Set.compl_subset_compl.2 hχU)
      exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
        (subset_closure hqΩ) h1
    have hclo : IsClopen Ω := ⟨closure_subset_iff_isClosed.1 hcl, hΩo⟩
    have huniv := hclo.eq_univ ⟨q, hqΩ⟩
    obtain ⟨u, hu⟩ := hUc.nonempty
    have huΩ : u ∈ Ω := by rw [huniv]; trivial
    exact hΩUc huΩ hu
  obtain ⟨z, hzΩ, hzU⟩ := hΩU
  have hzS : z ∉ S := hΩS hzΩ
  have hzK : z ∉ K := fun h => hzS (hKS h)
  have hFf : F =ᶠ[𝓝 z] f := by
    filter_upwards [hΦS z hzS, hΩo.mem_nhds hzΩ] with w hw1 hw2
    have h2 : ψ w = 0 := hψΩ hw2
    simp [hF, hw1, h2]
  have hFeq : EqOn F f (U \ K) := eqOn_of_preconnected hUKo hUK.isPreconnected
    (hFd.mono sdiff_subset) hf ⟨hzU, hzK⟩ hFf
  refine ⟨F, hFd, hFeq, fun G hG hGf => ?_⟩
  obtain ⟨p, hp⟩ := hUK.nonempty
  have hGF : G =ᶠ[𝓝 p] F := by
    filter_upwards [hUKo.mem_nhds hp] with w hw
    rw [hGf hw, hFeq hw]
  exact eqOn_of_preconnected hU hUc.isPreconnected hG hFd hp.1 hGF

end HartogsGlue

/-- Theorem 4.3.1 (Hartogs phenomenon), reduced to Theorem 4.2.1 (compactly supported `∂̄`) and
the smoothness of holomorphic functions. -/
theorem solution {n : ℕ} (hn : 2 ≤ n) {U K : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hUc : IsConnected U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hUK : IsConnected (U \ K)) {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (U \ K)) :
    ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ Set.EqOn F f (U \ K) ∧
      ∀ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G U → Set.EqOn G f (U \ K) →
        Set.EqOn G F U := by
  exact HartogsGlue.hartogs_of_children hn
    (fun g h1 h2 h3 => (LeblSCV.Hartogs.compactly_supported_dbar hn g h1 h2 h3).exists)
    (fun V hV f hf =>
      (LeblSCV.Holomorphic.holomorphic_contDiff_and_wirtinger_holomorphic hV hf).1)
    hU hUc hK hKU hUK hf
