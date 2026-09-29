-- Prove2me | solution 1 for ModularCurve.exists_meromorphic_smul_eq_mul_of_slashInvariant_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f3393803-a654-5465-b47b-f39cb91d9f5a

import Mathlib
import Theorems.Thm_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue

open scoped MatrixGroups Topology ModularForm
open UpperHalfPlane Filter Set Metric

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "exists_meromorphic_logDeriv_eq_of_int_residue"
namespace MultiplicativeIntegration
p2m_open "ModularCurve"

def mC (m : ℍ → ℤ) (z : ℂ) : ℤ := if h : 0 < z.im then m ⟨z, h⟩ else 0

theorem mC_of_im_pos (m : ℍ → ℤ) {z : ℂ} (hz : 0 < z.im) : mC m z = m ⟨z, hz⟩ := dif_pos hz

theorem mC_coe (m : ℍ → ℤ) (τ : ℍ) : mC m τ = m τ := by
  rw [mC_of_im_pos m τ.im_pos]

theorem coe_mk_UpperHalfPlane {z : ℂ} (hz : 0 < z.im) : ((⟨z, hz⟩ : ℍ) : ℂ) = z := rfl

theorem coe_ofComplex_of_im_pos {z : ℂ} (hz : 0 < z.im) : ((ofComplex z : ℍ) : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos hz]

theorem res_lift {m : ℍ → ℤ} {ω : ℍ → ℂ}
    (hres : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = (m τ : ℂ) / (z - τ) + g z) ∧
      (m τ = 0 → ω τ = g τ)) :
    ∀ a : ℂ, 0 < a.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      (∀ᶠ z in 𝓝[≠] a, (ω ∘ ofComplex) z = (mC m a : ℂ) / (z - a) + g z) ∧
      (mC m a = 0 → (ω ∘ ofComplex) a = g a) := by
  intro a ha
  obtain ⟨g, hg, hexp, hval⟩ := hres ⟨a, ha⟩
  refine ⟨g, hg, ?_, ?_⟩
  · rw [mC_of_im_pos m ha]
    exact hexp
  · intro h0
    rw [mC_of_im_pos m ha] at h0
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos ha]
    exact hval h0

def GSpec (m : ℍ → ℤ) (ω : ℍ → ℂ) (G : ℂ → ℂ) : Prop :=
  ∀ τ : ℍ, MeromorphicAt G τ ∧ meromorphicOrderAt G τ = (m τ : WithTop ℤ) ∧
    (m τ ≠ 0 → G τ = 0) ∧
    (m τ = 0 → AnalyticAt ℂ G τ ∧ G τ ≠ 0 ∧ HasDerivAt G (ω τ * G τ) τ)

theorem exists_GSpec {m : ℍ → ℤ} {ω : ℍ → ℂ}
    (hres : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = (m τ : ℂ) / (z - τ) + g z) ∧
      (m τ = 0 → ω τ = g τ)) :
    ∃ G : ℂ → ℂ, GSpec m ω G := by
  obtain ⟨G, hG⟩ :=
    ModularCurve.exists_meromorphic_logDeriv_eq_of_int_residue (mC m) (ω ∘ ofComplex) (res_lift hres)
  refine ⟨G, fun τ => ?_⟩
  have h := hG τ τ.im_pos
  rw [mC_coe] at h
  simp only [Function.comp_apply, ofComplex_apply] at h
  exact h

section Spec

variable {m : ℍ → ℤ} {ω : ℍ → ℂ} {G : ℂ → ℂ} (hG : GSpec m ω G)
include hG

theorem GSpec.eq_zero_iff (τ : ℍ) : G τ = 0 ↔ m τ ≠ 0 := by
  constructor
  · intro h hm
    exact ((hG τ).2.2.2 hm).2.1 h
  · exact (hG τ).2.2.1

theorem GSpec.ne_zero_iff (τ : ℍ) : G τ ≠ 0 ↔ m τ = 0 := by
  rw [Ne, hG.eq_zero_iff]; push Not; rfl

theorem GSpec.eventually_ne_zero (τ : ℍ) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), G z ≠ 0 := by
  rw [← meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hG τ).1, (hG τ).2.1]
  exact WithTop.coe_ne_top

theorem GSpec.analyticAt {τ : ℍ} (hm : m τ = 0) : AnalyticAt ℂ G τ := ((hG τ).2.2.2 hm).1

theorem GSpec.hasDerivAt {τ : ℍ} (hm : m τ = 0) : HasDerivAt G (ω τ * G τ) τ :=
  ((hG τ).2.2.2 hm).2.2

omit hG in

theorem eventuallyEq_ofComplex (G : ℂ → ℂ) (τ : ℍ) :
    (fun z : ℂ => G (ofComplex z)) =ᶠ[𝓝 (τ : ℂ)] G := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  rw [coe_ofComplex_of_im_pos hz]

theorem GSpec.meromorphicAt_ofComplex (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => G (ofComplex z)) (τ : ℂ) :=
  (hG τ).1.congr ((eventuallyEq_ofComplex G τ).filter_mono nhdsWithin_le_nhds).symm

theorem GSpec.meromorphicOrderAt_ofComplex (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => G (ofComplex z)) (τ : ℂ) = (m τ : WithTop ℤ) := by
  rw [meromorphicOrderAt_congr ((eventuallyEq_ofComplex G τ).filter_mono nhdsWithin_le_nhds)]
  exact (hG τ).2.1

end Spec

def μ (g : SL(2, ℤ)) (z : ℂ) : ℂ := ((g • ofComplex z : ℍ) : ℂ)

theorem μ_coe (g : SL(2, ℤ)) (τ : ℍ) : μ g τ = ((g • τ : ℍ) : ℂ) := by
  simp [μ, ofComplex_apply]

theorem μ_im_pos (g : SL(2, ℤ)) (z : ℂ) : 0 < (μ g z).im := (g • ofComplex z).im_pos

theorem μ_of_im_pos (g : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    μ g z = ((g • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := by
  rw [μ, ofComplex_apply_of_im_pos hz]

theorem hasDerivAt_μ (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (μ γ) (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ)) = μ γ := by
    funext z
    rw [μ, MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1
  all_goals try rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

theorem continuousAt_μ (γ : SL(2, ℤ)) (τ : ℍ) : ContinuousAt (μ γ) ↑τ :=
  (hasDerivAt_μ γ τ).continuousAt

theorem slash_two_apply (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[(2 : ℤ)] γ) τ =
      f (γ • τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ) :=
  ModularForm.SL_slash_apply f γ τ

theorem denom_mapGL_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ≠ 0 :=
  denom_ne_zero _ τ

theorem eventually_μ_ne (γ : SL(2, ℤ)) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), μ γ z ≠ μ γ τ := by
  have h1 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
    mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  filter_upwards [h1, self_mem_nhdsWithin] with z hz hzτ
  rw [μ_of_im_pos γ hz, μ_coe]
  intro h
  have h' : γ • (⟨z, hz⟩ : ℍ) = γ • τ := UpperHalfPlane.ext h
  have h'' := MulAction.injective γ h'
  exact hzτ (congrArg UpperHalfPlane.coe h'')

theorem tendsto_μ_nhdsNE (γ : SL(2, ℤ)) (τ : ℍ) :
    Tendsto (μ γ) (𝓝[≠] (τ : ℂ)) (𝓝[≠] ((γ • τ : ℍ) : ℂ)) := by
  rw [← μ_coe]
  refine tendsto_nhdsWithin_iff.mpr ⟨(continuousAt_μ γ τ).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  exact eventually_μ_ne γ τ

theorem μ_inv_μ (γ : SL(2, ℤ)) (τ : ℍ) : μ γ⁻¹ (μ γ τ) = τ := by
  rw [μ_coe, μ_coe, inv_smul_smul]

section Multiplier

variable {m : ℍ → ℤ} {ω : ℍ → ℂ} {G : ℂ → ℂ} (hG : GSpec m ω G)
include hG

theorem GSpec.hasDerivAt_comp_μ (γ : SL(2, ℤ)) (τ : ℍ) (hm : m (γ • τ) = 0) :
    HasDerivAt (fun z => G (μ γ z)) ((ω ∣[(2 : ℤ)] γ) τ * G (μ γ τ)) ↑τ := by
  have hd : HasDerivAt G (ω (γ • τ) * G ↑(γ • τ)) (μ γ ↑τ) := by
    rw [μ_coe]; exact hG.hasDerivAt hm
  have hc := hd.comp (↑τ : ℂ) (hasDerivAt_μ γ τ)
  convert hc using 1
  all_goals try rfl
  rw [slash_two_apply, μ_coe]
  ring

def goodSet (G : ℂ → ℂ) (γ : SL(2, ℤ)) : Set ℂ := {z | 0 < z.im ∧ G z ≠ 0 ∧ G (μ γ z) ≠ 0}

omit hG in
theorem goodSet_subset (γ : SL(2, ℤ)) : goodSet G γ ⊆ {z : ℂ | 0 < z.im} := fun _ hz => hz.1

theorem GSpec.eventually_mem_goodSet (γ : SL(2, ℤ)) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), z ∈ goodSet G γ := by
  have h1 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
    mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  have h2 := hG.eventually_ne_zero τ
  have h3 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), G (μ γ z) ≠ 0 :=
    (tendsto_μ_nhdsNE γ τ).eventually (hG.eventually_ne_zero (γ • τ))
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  exact ⟨hz1, hz2, hz3⟩

theorem GSpec.isOpen_goodSet (γ : SL(2, ℤ)) : IsOpen (goodSet G γ) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hz, hG1, hG2⟩
  set τ : ℍ := ⟨z, hz⟩
  have hm1 : m τ = 0 := (hG.ne_zero_iff τ).mp hG1
  have hG2' : G ↑(γ • τ) ≠ 0 := by rwa [← μ_coe]
  have hm2 : m (γ • τ) = 0 := (hG.ne_zero_iff (γ • τ)).mp hG2'
  have e1 : ∀ᶠ w in 𝓝 z, 0 < w.im := isOpen_upperHalfPlaneSet.mem_nhds hz
  have e2 : ∀ᶠ w in 𝓝 z, G w ≠ 0 := (hG.analyticAt hm1).continuousAt.eventually_ne hG1
  have e3 : ∀ᶠ w in 𝓝 z, G (μ γ w) ≠ 0 := by
    have hc : ContinuousAt (μ γ) z := continuousAt_μ γ τ
    have hGc : ContinuousAt G (μ γ z) := by
      rw [show μ γ z = ↑(γ • τ) from μ_coe γ τ]
      exact (hG.analyticAt hm2).continuousAt
    exact hc.eventually (hGc.eventually_ne hG2)
  filter_upwards [e1, e2, e3] with w h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem GSpec.countable_zeroSet : {z : ℂ | 0 < z.im ∧ G z = 0}.Countable := by
  set Z : Set ℂ := {z : ℂ | 0 < z.im ∧ G z = 0}

  let K : ℕ → Set ℂ := fun n => {z : ℂ | 1 / ((n : ℝ) + 1) ≤ z.im} ∩ closedBall 0 ((n : ℝ) + 1)
  have hKc : ∀ n, IsCompact (K n) := fun n =>
    (isCompact_closedBall _ _).inter_left (isClosed_le continuous_const Complex.continuous_im)
  have hKU : ∀ n, ∀ z ∈ K n, 0 < z.im := by
    rintro n z ⟨hz, -⟩
    exact lt_of_lt_of_le (by positivity) hz
  have hfin : ∀ n, (Z ∩ K n).Finite := by
    intro n
    let U : ℂ → Set ℂ := fun x => {w | w ≠ x → G w ≠ 0}
    have hU : ∀ x ∈ K n, U x ∈ 𝓝 x := by
      intro x hx
      have := hG.eventually_ne_zero ⟨x, hKU n x hx⟩
      exact eventually_nhdsWithin_iff.mp this
    obtain ⟨t, -, hcov⟩ := (hKc n).elim_nhds_subcover U hU
    refine t.finite_toSet.subset ?_
    rintro z ⟨⟨-, hGz⟩, hzK⟩
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (hcov hzK)
    have : z = x := by
      by_contra hne
      exact hzx hne hGz
    rw [this]
    exact hx
  have hcover : Z ⊆ ⋃ n, (Z ∩ K n) := by
    rintro z ⟨hz, hGz⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (max (1 / z.im) ‖z‖)
    refine mem_iUnion.mpr ⟨n, ⟨hz, hGz⟩, ?_, ?_⟩
    · change 1 / ((n : ℝ) + 1) ≤ z.im
      rw [div_le_iff₀ (by positivity)]
      have h1 : 1 / z.im ≤ n := (le_max_left _ _).trans hn
      rw [div_le_iff₀ hz] at h1
      nlinarith
    · rw [mem_closedBall, dist_zero_right]
      exact ((le_max_right _ _).trans hn).trans (by linarith)
  exact (countable_iUnion fun n => (hfin n).countable).mono hcover

omit hG in

theorem isPreconnected_range_diff_of_countable {e : ℂ → ℂ} (he : Continuous e)
    (hinj : Function.Injective e) {S : Set ℂ} (hS : S.Countable) :
    IsPreconnected (range e \ S) := by
  have h1 : (e ⁻¹' S).Countable := hS.preimage_of_injOn (hinj.injOn)
  have h2 : IsPathConnected (e ⁻¹' S)ᶜ :=
    h1.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
  have h3 : IsPathConnected (e '' (e ⁻¹' S)ᶜ) := h2.image' he.continuousOn
  have h4 : e '' (e ⁻¹' S)ᶜ = range e \ S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨mem_range_self w, hw⟩
    · rintro ⟨⟨w, rfl⟩, hz⟩
      exact ⟨w, hz, rfl⟩
  rw [← h4]
  exact h3.isConnected.isPreconnected

omit hG in

theorem upperHalfPlane_eq_range :
    {z : ℂ | 0 < z.im} = range (fun w : ℂ => (w.re : ℂ) + Real.exp w.im * Complex.I) := by
  ext z
  constructor
  · intro hz
    refine ⟨(z.re : ℂ) + Real.log z.im * Complex.I, ?_⟩
    apply Complex.ext <;> simp [Real.exp_log hz]
  · rintro ⟨w, rfl⟩
    show 0 < ((w.re : ℂ) + Real.exp w.im * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    exact Real.exp_pos _

omit hG in
theorem isPreconnected_upperHalfPlane_diff {S : Set ℂ} (hS : S.Countable) :
    IsPreconnected ({z : ℂ | 0 < z.im} \ S) := by
  rw [upperHalfPlane_eq_range]
  refine isPreconnected_range_diff_of_countable (by fun_prop) ?_ hS
  intro w₁ w₂ h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
    zero_add] at hre him
  exact Complex.ext hre (Real.exp_eq_exp.mp him)

theorem GSpec.isPreconnected_goodSet (γ : SL(2, ℤ)) : IsPreconnected (goodSet G γ) := by
  have hsub : {z : ℂ | 0 < z.im} \ goodSet G γ ⊆
      {z : ℂ | 0 < z.im ∧ G z = 0} ∪ (μ γ⁻¹) '' {z : ℂ | 0 < z.im ∧ G z = 0} := by
    rintro z ⟨hz, hzV⟩
    simp only [goodSet, mem_setOf_eq, not_and, not_not] at hzV
    by_cases hGz : G z = 0
    · exact Or.inl ⟨hz, hGz⟩
    · right
      refine ⟨μ γ z, ⟨μ_im_pos γ z, hzV hz hGz⟩, ?_⟩
      rw [μ_of_im_pos γ hz, ← μ_coe, μ_inv_μ]
  have hc : ({z : ℂ | 0 < z.im} \ goodSet G γ).Countable :=
    (hG.countable_zeroSet.union (hG.countable_zeroSet.image _)).mono hsub
  have := isPreconnected_upperHalfPlane_diff hc
  rwa [diff_diff_cancel_left (goodSet_subset γ)] at this

theorem GSpec.exists_multiplier (γ : SL(2, ℤ)) (hγ : ω ∣[(2 : ℤ)] γ = ω) :
    ∃ c : ℂ, c ≠ 0 ∧ (∀ τ : ℍ, m (γ • τ) = m τ) ∧ ∀ τ : ℍ, G ↑(γ • τ) = c * G ↑τ := by
  classical
  set V := goodSet G γ with hV

  let R : ℂ → ℂ := fun z => G (μ γ z) / G z
  have hR : ∀ z ∈ V, HasDerivAt R 0 z := by
    rintro z ⟨hz, hG1, hG2⟩
    set τ : ℍ := ⟨z, hz⟩
    have hm1 : m τ = 0 := (hG.ne_zero_iff τ).mp hG1
    have hG2' : G ↑(γ • τ) ≠ 0 := by rwa [← μ_coe]
    have hm2 : m (γ • τ) = 0 := (hG.ne_zero_iff (γ • τ)).mp hG2'
    have h1 := hG.hasDerivAt_comp_μ γ τ hm2
    rw [hγ] at h1
    have h2 := hG.hasDerivAt hm1
    have h3 := h1.div h2 hG1
    convert h3 using 1
    all_goals try rfl
    simp only [τ]
    ring
  have hRd : DifferentiableOn ℂ R V := fun z hz => (hR z hz).differentiableAt.differentiableWithinAt
  have hR0 : V.EqOn (deriv R) 0 := fun z hz => (hR z hz).deriv
  have hconst : ∀ z ∈ V, ∀ w ∈ V, R z = R w := fun z hz w hw =>
    (hG.isOpen_goodSet γ).is_const_of_deriv_eq_zero (hG.isPreconnected_goodSet γ) hRd hR0 hz hw

  obtain ⟨z₀, hz₀⟩ := (hG.eventually_mem_goodSet γ UpperHalfPlane.I).exists
  refine ⟨R z₀, div_ne_zero hz₀.2.2 hz₀.2.1, ?_⟩
  have hV_eq : ∀ z ∈ V, G (μ γ z) = R z₀ * G z := by
    intro z hz
    rw [← hconst z hz z₀ hz₀]
    simp only [R]
    field_simp [hz.2.1]

  have hm : ∀ τ : ℍ, m (γ • τ) = m τ := by
    intro τ
    have hpos : (0 : ℝ) < ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL,
        Units.val_one]
      norm_num
    have h1 := UpperHalfPlane.meromorphicOrderAt_comp_smul (f := fun σ : ℍ => G ↑σ) (τ := τ) hpos
    have e1 : (fun z : ℂ => (fun σ : ℍ => G ↑σ)
        ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) • ofComplex z)) =
        fun z => G (μ γ z) := by
      funext z
      simp only [μ, MulAction.compHom_smul_def]
    have e2 : ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) • τ) = γ • τ := by
      rw [MulAction.compHom_smul_def]
    rw [e1, e2] at h1
    change meromorphicOrderAt (fun z => G (μ γ z)) ↑τ =
      meromorphicOrderAt (fun z : ℂ => G ↑(ofComplex z)) ↑(γ • τ) at h1
    rw [hG.meromorphicOrderAt_ofComplex (γ • τ)] at h1

    have e3 : (fun z => G (μ γ z)) =ᶠ[𝓝[≠] (τ : ℂ)] (fun _ => R z₀) * G := by
      filter_upwards [hG.eventually_mem_goodSet γ τ] with z hz
      rw [Pi.mul_apply, hV_eq z hz]
    rw [meromorphicOrderAt_congr e3, meromorphicOrderAt_mul_of_ne_zero analyticAt_const
      (div_ne_zero hz₀.2.2 hz₀.2.1), (hG τ).2.1] at h1
    exact_mod_cast h1.symm
  refine ⟨hm, fun τ => ?_⟩
  by_cases hmτ : m τ = 0
  · have hG1 : G ↑τ ≠ 0 := (hG.ne_zero_iff τ).mpr hmτ
    have hG2 : G ↑(γ • τ) ≠ 0 := (hG.ne_zero_iff (γ • τ)).mpr ((hm τ).trans hmτ)
    have hτV : (τ : ℂ) ∈ V := ⟨τ.im_pos, hG1, by rwa [μ_coe]⟩
    have := hV_eq τ hτV
    rwa [μ_coe] at this
  · rw [(hG.eq_zero_iff τ).mpr hmτ, (hG.eq_zero_iff (γ • τ)).mpr (by rwa [hm τ]), mul_zero]

end Multiplier

section Analytic

variable {m : ℍ → ℤ} {ω : ℍ → ℂ}
  (hres : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = (m τ : ℂ) / (z - τ) + g z) ∧
    (m τ = 0 → ω τ = g τ))
include hres

theorem analyticAt_omega (τ : ℍ) (hm : m τ = 0) :
    AnalyticAt ℂ (fun z => ω (ofComplex z)) τ := by
  obtain ⟨g, hg, hexp, hval⟩ := hres τ
  refine hg.congr ?_
  have h1 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), g z = ω (ofComplex z) := by
    filter_upwards [hexp] with z hz
    rw [hz, hm]
    simp
  rw [eventually_nhdsWithin_iff] at h1
  filter_upwards [h1] with z hz
  by_cases hzτ : z = τ
  · subst hzτ
    rw [ofComplex_apply]
    exact (hval hm).symm
  · exact hz hzτ

theorem tendsto_norm_omega_atTop (τ : ℍ) (hm : m τ ≠ 0) :
    Tendsto (fun z => ‖ω (ofComplex z)‖) (𝓝[≠] (τ : ℂ)) atTop := by
  obtain ⟨g, hg, hexp, -⟩ := hres τ
  have h1 : Tendsto (fun z => (z - τ) * ω (ofComplex z)) (𝓝[≠] (τ : ℂ)) (𝓝 (m τ : ℂ)) := by
    have hc : ContinuousAt (fun z : ℂ => (m τ : ℂ) + (z - τ) * g z) τ :=
      continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul hg.continuousAt)
    have h2 := hc.tendsto
    simp only [sub_self, zero_mul, add_zero] at h2
    refine (h2.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hexp, self_mem_nhdsWithin] with z hz hzτ
    rw [hz, mul_add, mul_div_cancel₀ _ (sub_ne_zero.mpr hzτ)]
  have h3 := h1.norm
  have h4 : Tendsto (fun z : ℂ => ‖z - τ‖⁻¹) (𝓝[≠] (τ : ℂ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_norm_sub_self_nhdsNE (τ : ℂ))
  have hpos : 0 < ‖(m τ : ℂ)‖ := norm_pos_iff.mpr (Int.cast_ne_zero.mpr hm)
  refine (h3.pos_mul_atTop hpos h4).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hzτ
  have hne : ‖z - ↑τ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzτ)
  rw [norm_mul]
  field_simp

end Analytic

structure CuspBound (ω : ℍ → ℂ) (σ : SL(2, ℤ)) (C δ A₀ : ℝ) : Prop where
  δ_pos : 0 < δ
  C_nonneg : 0 ≤ C
  A₀_pos : 0 < A₀
  bound : ∀ τ : ℍ, A₀ ≤ τ.im → ‖(ω ∣[(2 : ℤ)] σ) τ‖ ≤ C * Real.exp (-δ * τ.im)

theorem exists_cuspBound {ω : ℍ → ℂ} {σ : SL(2, ℤ)}
    (hcusp : ∃ δ : ℝ, 0 < δ ∧
      (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im)) :
    ∃ C δ A₀, CuspBound ω σ C δ A₀ := by
  obtain ⟨δ, hδ, hO⟩ := hcusp
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  refine ⟨max C 0, δ, max A 1, hδ, le_max_right _ _, by positivity, fun τ hτ => ?_⟩
  have h : ‖(ω ∣[(2 : ℤ)] σ) τ‖ ≤ C * ‖Real.exp (-δ * τ.im)‖ := hA τ ((le_max_left _ _).trans hτ)
  rw [Real.norm_eq_abs, Real.abs_exp] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

theorem continuous_denom (g : GL (Fin 2) ℝ) : Continuous (fun z : ℂ => denom g z) := by
  simp only [denom]
  fun_prop

theorem differentiableAt_denom (g : GL (Fin 2) ℝ) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => denom g w) z := by
  simp only [denom]
  fun_prop

theorem exists_primitive_halfPlane {f : ℂ → ℂ} {A : ℝ}
    (hf : DifferentiableOn ℂ f {z : ℂ | A < z.im}) :
    ∃ Ψ : ℂ → ℂ, ∀ z : ℂ, A < z.im → HasDerivAt Ψ (f z) z := by
  classical
  let c : ℕ → ℂ := fun n => ((A + n + 1 : ℝ) : ℂ) * Complex.I
  let r : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hc_re : ∀ n, (c n).re = 0 := fun n => by simp [c]
  have hc_im : ∀ n, (c n).im = A + n + 1 := fun n => by simp [c]
  have hsub : ∀ n, ball (c n) (r n) ⊆ {z : ℂ | A < z.im} := by
    intro n z hz
    rw [mem_ball, Complex.dist_eq] at hz
    have h1 := Complex.abs_im_le_norm (z - c n)
    rw [Complex.sub_im, hc_im] at h1
    have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hz)).1
    show A < z.im
    simp only [r] at h2
    linarith
  have hmono : ∀ {n k : ℕ}, n ≤ k → ball (c n) (r n) ⊆ ball (c k) (r k) := by
    intro n k hnk z hz
    rw [mem_ball] at hz ⊢
    have hd : dist (c n) (c k) ≤ (k : ℝ) - n := by
      rw [Complex.dist_eq]
      have : c n - c k = (((n : ℝ) - k : ℝ) : ℂ) * Complex.I := by
        simp only [c]; push_cast; ring
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hnk) : (0:ℝ) ≤ (k:ℝ) - n)]
    calc dist z (c k) ≤ dist z (c n) + dist (c n) (c k) := dist_triangle _ _ _
      _ < r n + ((k : ℝ) - n) := by linarith
      _ = r k := by simp only [r]; ring
  have hcover : ∀ z : ℂ, A < z.im → ∃ n : ℕ, z ∈ ball (c n) (r n) := by
    intro z hz
    set y := z.im - A with hy
    have hy0 : 0 < y := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((z.re ^ 2 + y ^ 2) / (2 * y))
    refine ⟨n, ?_⟩
    rw [mem_ball, Complex.dist_eq]
    have h1 : z.re ^ 2 + y ^ 2 < 2 * y * (n + 1) := by
      rw [div_lt_iff₀ (by positivity)] at hn
      nlinarith
    have hr : (0 : ℝ) ≤ r n := by simp only [r]; positivity
    rw [← sq_lt_sq₀ (norm_nonneg _) hr, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, hc_re, hc_im]
    simp only [r, sub_zero]
    nlinarith

  have hprim : ∀ n, ∃ g : ℂ → ℂ, g (c 0) = 0 ∧ ∀ z ∈ ball (c n) (r n), HasDerivAt g (f z) z :=
    fun n => (hf.mono (hsub n)).isExactOn_ball.with_val_at (c 0) 0
  choose g hg0 hg using hprim
  have hc0 : ∀ n, c 0 ∈ ball (c n) (r n) := fun n =>
    hmono (Nat.zero_le n) (mem_ball_self (by simp only [r]; positivity))
  have hcons : ∀ {n k : ℕ}, n ≤ k → ∀ z ∈ ball (c n) (r n), g n z = g k z := by
    intro n k hnk z hz
    have hderiv : ∀ w ∈ ball (c n) (r n), HasDerivAt (fun w => g n w - g k w) 0 w := by
      intro w hw
      have := (hg n w hw).sub (hg k w (hmono hnk hw))
      rwa [sub_self] at this
    have hdiff : DifferentiableOn ℂ (fun w => g n w - g k w) (ball (c n) (r n)) :=
      fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt
    have := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (c n) (r n)).isPreconnected hdiff
      (fun w hw => (hderiv w hw).deriv) hz (hc0 n)
    simp only [hg0, sub_self] at this
    exact sub_eq_zero.mp this
  refine ⟨fun z => if h : A < z.im then g (Classical.choose (hcover z h)) z else 0,
    fun z hz => ?_⟩
  set n := Classical.choose (hcover z hz)
  have hn : z ∈ ball (c n) (r n) := Classical.choose_spec (hcover z hz)
  apply (hg n z hn).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hn] with w hw
  have hw' : A < w.im := hsub n hw
  rw [dif_pos hw']
  have hk : w ∈ ball (c (Classical.choose (hcover w hw'))) (r (Classical.choose (hcover w hw'))) :=
    Classical.choose_spec (hcover w hw')
  rcases le_total n (Classical.choose (hcover w hw')) with h | h
  · exact (hcons h w hw).symm
  · exact hcons h w hk

theorem norm_sub_le_of_exp_decay {Ψ f : ℂ → ℂ} {A C δ : ℝ} (hδ : 0 < δ)
    (hΨ : ∀ z : ℂ, A < z.im → HasDerivAt Ψ (f z) z)
    (hf : ∀ z : ℂ, A < z.im → ‖f z‖ ≤ C * Real.exp (-δ * z.im))
    {y : ℝ} (hy : A < y) {z w : ℂ} (hz : y ≤ z.im) (hw : y ≤ w.im) :
    ‖Ψ w - Ψ z‖ ≤ C * Real.exp (-δ * y) * ‖w - z‖ := by
  have hseg : ∀ x ∈ segment ℝ z w, y ≤ x.im := by
    intro x hx
    rw [segment_eq_image] at hx
    obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hx
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    nlinarith
  have hA : ∀ x ∈ segment ℝ z w, A < x.im := fun x hx => lt_of_lt_of_le hy (hseg x hx)
  refine (convex_segment z w).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hΨ x (hA x hx)).hasDerivWithinAt) (fun x hx => ?_)
    (left_mem_segment ℝ z w) (right_mem_segment ℝ z w)
  refine (hf x (hA x hx)).trans ?_
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hf x (hA x hx))
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  nlinarith [hseg x hx, hδ]

theorem exists_uniform_limit_of_exp_decay {Ψ f : ℂ → ℂ} {A C δ : ℝ} (hδ : 0 < δ)
    (hΨ : ∀ z : ℂ, A < z.im → HasDerivAt Ψ (f z) z)
    (hf : ∀ z : ℂ, A < z.im → ‖f z‖ ≤ C * Real.exp (-δ * z.im)) :
    ∃ (L : ℂ) (M : ℝ), ∀ z : ℂ, A < z.im → ‖Ψ z - L‖ ≤ M * Real.exp (-δ * z.im) := by
  set q : ℝ := Real.exp (-δ) with hq
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq0 : 0 < q := Real.exp_pos _

  let u : ℂ → ℕ → ℂ := fun z n => Ψ (z + n * Complex.I)
  have him : ∀ (z : ℂ) (n : ℕ), (z + n * Complex.I).im = z.im + n := fun z n => by simp
  have hstep : ∀ z : ℂ, A < z.im → ∀ n : ℕ,
      dist (u z n) (u z (n + 1)) ≤ C * Real.exp (-δ * z.im) * q ^ n := by
    intro z hz n
    have hy : A < z.im + n := lt_of_lt_of_le hz (le_add_of_nonneg_right n.cast_nonneg)
    have h := norm_sub_le_of_exp_decay hδ hΨ hf hy (z := z + n * Complex.I)
      (w := z + (n + 1 : ℕ) * Complex.I) (by rw [him]) (by rw [him]; push_cast; linarith)
    rw [dist_comm, dist_eq_norm]
    refine h.trans (le_of_eq ?_)
    have hn : ‖(z + ((n + 1 : ℕ) : ℂ) * Complex.I) - (z + (n : ℂ) * Complex.I)‖ = 1 := by
      push_cast
      ring_nf
      exact Complex.norm_I
    rw [hn, mul_one, hq, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 1
    ring_nf
  have hlim : ∀ z : ℂ, A < z.im → ∃ a : ℂ, Tendsto (u z) atTop (𝓝 a) ∧
      dist (u z 0) a ≤ C * Real.exp (-δ * z.im) / (1 - q) := by
    intro z hz
    have hcs : CauchySeq (u z) := cauchySeq_of_le_geometric q _ hq1 (hstep z hz)
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcs
    exact ⟨a, ha, dist_le_of_le_geometric_of_tendsto₀ q _ hq1 (hstep z hz) ha⟩

  set zb : ℂ := ((A + 1 : ℝ) : ℂ) * Complex.I with hzb_def
  have hzb : A < zb.im := by simp [zb]
  obtain ⟨L, hL, -⟩ := hlim zb hzb
  refine ⟨L, C / (1 - q), fun z hz => ?_⟩
  obtain ⟨a, ha, hdist⟩ := hlim z hz

  have haL : a = L := by
    set y : ℝ := min z.im zb.im
    have hy : A < y := lt_min hz hzb
    have hbound : ∀ n : ℕ, ‖u z n - u zb n‖ ≤ C * Real.exp (-δ * y) * ‖z - zb‖ * q ^ n := by
      intro n
      have hyn : A < y + n := lt_of_lt_of_le hy (le_add_of_nonneg_right n.cast_nonneg)
      have h := norm_sub_le_of_exp_decay hδ hΨ hf hyn (z := zb + n * Complex.I)
        (w := z + n * Complex.I) (by rw [him]; gcongr; exact min_le_right _ _)
        (by rw [him]; gcongr; exact min_le_left _ _)
      refine h.trans (le_of_eq ?_)
      have : (z + (n : ℂ) * Complex.I) - (zb + (n : ℂ) * Complex.I) = z - zb := by ring
      have hexp : Real.exp (-δ * (y + n)) = Real.exp (-δ * y) * q ^ n := by
        rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      rw [this, hexp]
      ring
    have h0 : Tendsto (fun n => u z n - u zb n) atTop (𝓝 0) := by
      refine squeeze_zero_norm hbound ?_
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul
        (C * Real.exp (-δ * y) * ‖z - zb‖)
      rwa [mul_zero] at this
    have h1 : Tendsto (fun n => u z n - u zb n) atTop (𝓝 (a - L)) := ha.sub hL
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h0)
  subst haL
  have h0 : u z 0 = Ψ z := by simp [u]
  rw [← dist_eq_norm, ← h0]
  refine hdist.trans (le_of_eq ?_)
  ring

section Cusp

variable {m : ℍ → ℤ} {ω : ℍ → ℂ} {G : ℂ → ℂ} (hG : GSpec m ω G)
  (hres : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = (m τ : ℂ) / (z - τ) + g z) ∧
    (m τ = 0 → ω τ = g τ))
include hG hres

omit hG in

theorem m_smul_eq_zero_of_lt_im {σ : SL(2, ℤ)} {C δ A₀ : ℝ} (hb : CuspBound ω σ C δ A₀)
    (τ : ℍ) (hτ : A₀ < τ.im) : m (σ • τ) = 0 := by
  by_contra hm
  have h1 : Tendsto (fun z => ‖ω (ofComplex (μ σ z))‖) (𝓝[≠] (τ : ℂ)) atTop :=
    (tendsto_norm_omega_atTop hres (σ • τ) hm).comp (tendsto_μ_nhdsNE σ τ)
  set D : ℂ → ℂ := fun z => denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) z with hD_def
  have hDc : Continuous D := continuous_denom _
  set B : ℝ := C * ‖D τ‖ ^ 2 + 1
  have h2 : ∀ᶠ z in 𝓝 (τ : ℂ), C * ‖D z‖ ^ 2 < B := by
    have : ContinuousAt (fun z => C * ‖D z‖ ^ 2) τ := by fun_prop
    exact this.eventually_lt continuousAt_const (lt_add_one _)
  have h3 : ∀ᶠ z in 𝓝 (τ : ℂ), A₀ < z.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hτ
  have h4 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), ‖ω (ofComplex (μ σ z))‖ < B := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds h2, mem_nhdsWithin_of_mem_nhds h3]
      with z hz2 hz3
    have hz : 0 < z.im := hb.A₀_pos.trans hz3
    set τz : ℍ := ⟨z, hz⟩
    have hψ : ‖ω (σ • τz) * D z ^ (-2 : ℤ)‖ ≤ C * Real.exp (-δ * z.im) := by
      have := hb.bound τz hz3.le
      rwa [slash_two_apply] at this
    have hD : D z ≠ 0 := denom_mapGL_ne_zero σ τz
    have hexp : Real.exp (-δ * z.im) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := hb.δ_pos
      nlinarith
    have key : ω (σ • τz) = (ω (σ • τz) * D z ^ (-2 : ℤ)) * D z ^ (2 : ℤ) := by
      rw [mul_assoc, ← zpow_add₀ hD]
      norm_num
    rw [μ_of_im_pos σ hz, ofComplex_apply, key, norm_mul, norm_zpow]
    calc ‖ω (σ • τz) * D z ^ (-2 : ℤ)‖ * ‖D z‖ ^ (2 : ℤ)
        ≤ (C * Real.exp (-δ * z.im)) * ‖D z‖ ^ (2 : ℤ) := by gcongr
      _ ≤ (C * 1) * ‖D z‖ ^ (2 : ℤ) := by gcongr; exact hb.C_nonneg
      _ = C * ‖D z‖ ^ 2 := by rw [mul_one, zpow_two, sq]
      _ < B := hz2
  obtain ⟨z, hz1, hz2⟩ := ((h1.eventually_gt_atTop B).and h4).exists
  exact lt_asymm hz1 hz2

theorem GSpec.exists_limit_cusp (σ : SL(2, ℤ))
    (hcuspσ : ∃ δ : ℝ, 0 < δ ∧
      (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im)) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (fun τ : ℍ => G ↑(σ • τ)) atImInfty (𝓝 L) := by
  obtain ⟨C, δ, A₀, hb⟩ := exists_cuspBound hcuspσ
  set ψ := ω ∣[(2 : ℤ)] σ with hψ_def
  set P : Set ℂ := {z | A₀ < z.im} with hP_def
  have hPo : IsOpen P := isOpen_lt continuous_const Complex.continuous_im
  have hP0 : ∀ z ∈ P, 0 < z.im := fun z hz => hb.A₀_pos.trans hz
  have hm0 : ∀ z (hz : z ∈ P), m (σ • ⟨z, hP0 z hz⟩) = 0 := fun z hz =>
    m_smul_eq_zero_of_lt_im hres hb _ hz

  set K : ℂ → ℂ := fun z => G (μ σ z) with hK_def
  set ψt : ℂ → ℂ := fun z => ψ (ofComplex z) with hψt_def
  have hK : ∀ z (hz : z ∈ P), HasDerivAt K (ψt z * K z) z ∧ K z ≠ 0 := by
    intro z hz
    have hz0 := hP0 z hz
    set τz : ℍ := ⟨z, hz0⟩
    have h1 := hG.hasDerivAt_comp_μ σ τz (hm0 z hz)
    refine ⟨?_, ?_⟩
    · have e : ψt z = ψ τz := by
        simp only [hψt_def]
        rw [ofComplex_apply_of_im_pos hz0]
      rw [e]
      exact h1
    · show G (μ σ z) ≠ 0
      rw [μ_of_im_pos σ hz0]
      exact (hG.ne_zero_iff _).mpr (hm0 z hz)
  have hψt : DifferentiableOn ℂ ψt P := by
    intro z hz
    have hz0 := hP0 z hz
    set τz : ℍ := ⟨z, hz0⟩
    have e : ψt = fun w => ω (ofComplex (μ σ w)) *
        denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) ↑(ofComplex w) ^ (-2 : ℤ) := by
      funext w
      simp only [hψt_def, hψ_def, slash_two_apply, μ, ofComplex_apply]
    rw [e]
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.mul
    · have ha : AnalyticAt ℂ (fun z => ω (ofComplex z)) (μ σ z) := by
        rw [μ_of_im_pos σ hz0]
        exact analyticAt_omega hres _ (hm0 z hz)
      exact ha.differentiableAt.comp z (hasDerivAt_μ σ τz).differentiableAt
    · have e2 : (fun w => denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) ↑(ofComplex w) ^ (-2 : ℤ))
          =ᶠ[𝓝 z] fun w => denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) w ^ (-2 : ℤ) := by
        filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz0] with w hw
        rw [coe_ofComplex_of_im_pos hw]
      refine (DifferentiableAt.zpow ?_ (Or.inl (denom_mapGL_ne_zero σ τz))).congr_of_eventuallyEq
        e2
      exact differentiableAt_denom _ z

  obtain ⟨Ψ, hΨ⟩ := exists_primitive_halfPlane hψt
  have hq : ∀ z ∈ P, HasDerivAt (fun w => K w * Complex.exp (-Ψ w)) 0 z := by
    intro z hz
    have h1 := (hK z hz).1
    have h2 : HasDerivAt (fun w => Complex.exp (-Ψ w)) (Complex.exp (-Ψ z) * -ψt z) z :=
      (hΨ z hz).neg.cexp
    convert h1.mul h2 using 1
    all_goals try rfl
    ring
  set zb : ℂ := ((A₀ + 1 : ℝ) : ℂ) * Complex.I with hzb_def
  have hzb : zb ∈ P := by
    show A₀ < (((A₀ + 1 : ℝ) : ℂ) * Complex.I).im
    simp
  set κ : ℂ := K zb * Complex.exp (-Ψ zb) with hκ_def
  have hκ : κ ≠ 0 := mul_ne_zero (hK zb hzb).2 (Complex.exp_ne_zero _)
  have hKexp : ∀ z ∈ P, K z = κ * Complex.exp (Ψ z) := by
    intro z hz
    have hc := hPo.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt A₀).isPreconnected
      (fun w hw => (hq w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hq w hw).deriv) hz hzb
    calc K z = (K z * Complex.exp (-Ψ z)) * Complex.exp (Ψ z) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = κ * Complex.exp (Ψ z) := by rw [hc]

  have hdecay : ∀ z : ℂ, A₀ < z.im → ‖ψt z‖ ≤ C * Real.exp (-δ * z.im) := by
    intro z hz
    have hz0 : 0 < z.im := hb.A₀_pos.trans hz
    have := hb.bound ⟨z, hz0⟩ hz.le
    simp only [hψt_def]
    rwa [ofComplex_apply_of_im_pos hz0]
  obtain ⟨L, M, hLM⟩ := exists_uniform_limit_of_exp_decay hb.δ_pos hΨ hdecay

  have him : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := Filter.tendsto_comap
  have hg0 : Tendsto (fun τ : ℍ => M * Real.exp (-δ * τ.im)) atImInfty (𝓝 0) := by
    have h1 : Tendsto (fun τ : ℍ => -δ * τ.im) atImInfty atBot := by
      have := (him.const_mul_atTop hb.δ_pos)
      have h2 := tendsto_neg_atTop_atBot.comp this
      refine h2.congr fun τ => ?_
      simp [neg_mul]
    have h3 := (Real.tendsto_exp_atBot.comp h1).const_mul M
    rw [mul_zero] at h3
    exact h3
  have hΨlim : Tendsto (fun τ : ℍ => Ψ ↑τ) atImInfty (𝓝 L) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg0
    rw [Filter.Eventually, atImInfty_mem]
    refine ⟨A₀ + 1, fun τ hτ => hLM τ ?_⟩
    show A₀ < τ.im
    linarith
  refine ⟨κ * Complex.exp L, mul_ne_zero hκ (Complex.exp_ne_zero _), ?_⟩
  have hlim : Tendsto (fun τ : ℍ => κ * Complex.exp (Ψ ↑τ)) atImInfty
      (𝓝 (κ * Complex.exp L)) :=
    ((Complex.continuous_exp.tendsto L).comp hΨlim).const_mul κ
  refine hlim.congr' ?_
  rw [Filter.EventuallyEq, Filter.Eventually, atImInfty_mem]
  refine ⟨A₀ + 1, fun τ hτ => ?_⟩
  have hτP : (τ : ℂ) ∈ P := by
    show A₀ < τ.im
    linarith
  show κ * Complex.exp (Ψ ↑τ) = G ↑(σ • τ)
  rw [← μ_coe, ← hKexp τ hτP]

end Cusp

end ModularCurve.MultiplicativeIntegration

end

open ModularCurve.MultiplicativeIntegration in

theorem solution
    (Γ : Subgroup SL(2, ℤ)) (m : ℍ → ℤ) (ω : ℍ → ℂ)
    (hΓ : ∀ γ ∈ Γ, ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
      (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hres : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = (m τ : ℂ) / (z - τ) + g z) ∧
      (m τ = 0 → ω τ = g τ)) :
    ∃ (F : ℍ → ℂ) (χ : Γ → ℂ),
      (∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) ∧
      (∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ) ∧
      (∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) ∧
      ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (m τ : WithTop ℤ) := by
  classical
  obtain ⟨G, hG⟩ := exists_GSpec hres
  refine ⟨fun τ => G τ,
    fun γ => Classical.choose (hG.exists_multiplier (γ : SL(2, ℤ)) (hΓ γ γ.2)),
    fun τ => hG.meromorphicAt_ofComplex τ, fun γ τ => ?_,
    fun σ => hG.exists_limit_cusp hres σ (hcusp σ), fun τ => hG.meromorphicOrderAt_ofComplex τ⟩
  exact (Classical.choose_spec (hG.exists_multiplier (γ : SL(2, ℤ)) (hΓ γ γ.2))).2.2 τ

end S_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue
end P2MW
export P2MW.S_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue (solution)
