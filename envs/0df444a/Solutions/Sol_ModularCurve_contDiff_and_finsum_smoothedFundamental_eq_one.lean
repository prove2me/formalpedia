-- Prove2me | solution 1 for ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/0860bd0a-9916-575e-8c7f-fb1f68a655e3

import Mathlib
import Definitions.Def_ModularCurve_SmoothedFundamental
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one

noncomputable section

p2m_open "UpperHalfPlane~I~coe_smul"
open Filter Complex MulAction Set ModularCurve.SmoothedFundamental
open scoped MatrixGroups Topology ContDiff Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "smoothedFundamental SmoothedFundamental.smoothedFundamental_nonneg"
namespace SmoothedFundamentalProof
p2m_open "ModularCurve"

local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

theorem det_entries (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℤ) : ℂ) * γ 1 1 - ((γ 0 1 : ℤ) : ℂ) * γ 1 0 = 1 := by
  have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact_mod_cast this

theorem denom_eq (γ : SL(2, ℤ)) (z : ℂ) :
    denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

theorem num_eq (γ : SL(2, ℤ)) (z : ℂ) :
    num γ z = ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) := by
  simp [num]

theorem denom_ne_zero' (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : denom γ z ≠ 0 :=
  UpperHalfPlane.denom_ne_zero_of_im γ hz.ne'

theorem analyticAt_denom (γ : SL(2, ℤ)) (z : ℂ) : AnalyticAt ℂ (denom (γ : GL (Fin 2) ℝ)) z := by
  have : denom (γ : GL (Fin 2) ℝ) = fun z => ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) :=
    funext (denom_eq γ)
  rw [this]
  exact (analyticAt_const.mul analyticAt_id).add analyticAt_const

theorem analyticAt_num (γ : SL(2, ℤ)) (z : ℂ) : AnalyticAt ℂ (num (γ : GL (Fin 2) ℝ)) z := by
  have : num (γ : GL (Fin 2) ℝ) = fun z => ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) :=
    funext (num_eq γ)
  rw [this]
  exact (analyticAt_const.mul analyticAt_id).add analyticAt_const

theorem analyticAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : AnalyticAt ℂ (mob γ) z :=
  (analyticAt_num γ z).div (analyticAt_denom γ z) (denom_ne_zero' γ hz)

theorem mob_contDiffAt (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) (n : ℕ∞) :
    ContDiffAt ℝ n (mob γ) z :=
  ((analyticAt_mob γ hz).contDiffAt (n := n)).restrict_scalars ℝ

theorem im_mob (γ : SL(2, ℤ)) (z : ℂ) : (mob γ z).im = z.im / Complex.normSq (denom γ z) := by
  have hdet := det_entries γ
  have hdetR : ((γ 0 0 : ℤ) : ℝ) * γ 1 1 - ((γ 0 1 : ℤ) : ℝ) * γ 1 0 = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact_mod_cast this
  rw [mob, Complex.div_im, num_eq, denom_eq]
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
    sub_zero, Complex.add_im, Complex.mul_im, add_zero, zero_add]
  rw [← sub_div]
  congr 1
  · linear_combination z.im * (((γ 1 0 : ℤ) : ℝ) * z.re + ((γ 1 1 : ℤ) : ℝ)) * 0 + z.im * hdetR -
      z.im * hdetR + z.im * hdetR
  all_goals rfl

theorem im_pos_of_im_mob_pos (γ : SL(2, ℤ)) {z : ℂ} (h : 0 < (mob γ z).im) : 0 < z.im := by
  rw [im_mob] at h
  by_contra hz
  push Not at hz
  have : z.im / Complex.normSq (denom γ z) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hz (Complex.normSq_nonneg _)
  linarith

theorem mob_inv_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : mob γ⁻¹ (mob γ z) = z := by
  have := mob_mob γ⁻¹ γ ⟨z, hz⟩
  rw [inv_mul_cancel, mob_one_apply] at this
  exact this

theorem finite_moving (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L) :
    {γ : SL(2, ℤ) | ((fun τ : ℍ => γ • τ) '' K ∩ L).Nonempty}.Finite := by
  have h := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := 𝒮ℒ) (T := ℍ) hK hL
  set φ : SL(2, ℤ) →* GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ with hφ
  have hinj : Function.Injective φ := by
    intro a b hab
    ext i j
    have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) hab
    simpa [hφ] using this
  refine Finite.of_finite_image ?_ hinj.injOn
  refine (h.image Subtype.val).subset ?_
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨⟨φ g, ⟨g, rfl⟩⟩, hg, rfl⟩

theorem im_smul_le_inv (γ : SL(2, ℤ)) (τ : ℍ) (hc : (γ 1 0 : ℤ) ≠ 0) :
    (γ • τ).im ≤ τ.im⁻¹ := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  have h1 := UpperHalfPlane.c_mul_im_sq_le_normSq_denom (g := (γ : GL (Fin 2) ℝ)) (z := τ)
  have hc' : (1 : ℝ) ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (γ 1 0) ^ 2 := by
      have := Int.one_le_abs hc
      nlinarith [sq_abs (γ 1 0)]
    exact_mod_cast this
  have hτ := τ.im_pos
  have hent : ((γ : GL (Fin 2) ℝ) 1 0 : ℝ) = ((γ 1 0 : ℤ) : ℝ) := by simp
  rw [hent] at h1
  have hns : τ.im ^ 2 ≤ Complex.normSq (denom γ τ) := by
    calc τ.im ^ 2 = 1 * τ.im ^ 2 := by ring
      _ ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 * τ.im ^ 2 := by gcongr
      _ = (((γ 1 0 : ℤ) : ℝ) * τ.im) ^ 2 := by ring
      _ ≤ _ := h1
  have hpos : 0 < Complex.normSq (denom γ τ) := lt_of_lt_of_le (by positivity) hns
  rw [div_le_iff₀ hpos]
  calc τ.im = τ.im⁻¹ * τ.im ^ 2 := by field_simp
    _ ≤ τ.im⁻¹ * Complex.normSq (denom γ τ) := by gcongr

theorem denom_of_c_eq_zero (γ : SL(2, ℤ)) (z : ℂ) (hc : (γ 1 0 : ℤ) = 0) :
    denom γ z = ((γ 1 1 : ℤ) : ℂ) := by
  rw [denom_eq, hc]; simp

theorem d_sq_of_c_eq_zero (γ : SL(2, ℤ)) (hc : (γ 1 0 : ℤ) = 0) :
    (γ 0 0 : ℤ) * γ 1 1 = 1 ∧ (γ 1 1 : ℤ) * γ 1 1 = 1 := by
  have h := γ.det_coe
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at h
  refine ⟨h, ?_⟩
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> norm_num

theorem im_smul_of_c_eq_zero (γ : SL(2, ℤ)) (τ : ℍ) (hc : (γ 1 0 : ℤ) = 0) :
    (γ • τ).im = τ.im := by
  rw [ModularGroup.im_smul_eq_div_normSq, denom_of_c_eq_zero γ _ hc]
  have h2 := (d_sq_of_c_eq_zero γ hc).2
  have : Complex.normSq (((γ 1 1 : ℤ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_intCast, Complex.normSq_ofReal]; exact_mod_cast h2
  rw [this, div_one]

theorem im_smul_le_max (γ : SL(2, ℤ)) (τ : ℍ) : (γ • τ).im ≤ max τ.im τ.im⁻¹ := by
  by_cases hc : (γ 1 0 : ℤ) = 0
  · rw [im_smul_of_c_eq_zero γ τ hc]; exact le_max_left _ _
  · exact (im_smul_le_inv γ τ hc).trans (le_max_right _ _)

theorem exists_smul_nice (τ : ℍ) : ∃ γ : SL(2, ℤ),
    |(γ • τ).re| ≤ 1 / 2 ∧ 3 / 4 ≤ (γ • τ).im ∧ (γ • τ).im ≤ max τ.im τ.im⁻¹ := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  refine ⟨γ, hγ.2, ?_, im_smul_le_max γ τ⟩
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
  nlinarith [(γ • τ).im_pos]

theorem pOne_contDiff (n : ℕ∞) : ContDiff ℝ n pOne :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem pTwo_contDiff (T : ℝ) (n : ℕ∞) : ContDiff ℝ n (pTwo T) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem bump_contDiff (T : ℝ) (n : ℕ∞) : ContDiff ℝ n (bump T) :=
  ((pOne_contDiff n).comp Complex.reCLM.contDiff).mul
    ((pTwo_contDiff T n).comp Complex.imCLM.contDiff)

theorem recip_contDiff (n : ℕ∞) : ContDiff ℝ n recip := by
  refine contDiff_iff_contDiffAt.2 fun t => ?_
  rcases lt_or_ge (1 / 8 : ℝ) t with h | h
  · exact ((Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).contDiffAt).div contDiffAt_id
      (by positivity)
  · have : recip =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show t < 1 / 4 by linarith)] with s hs
      simp [recip, Real.smoothTransition.zero_of_nonpos (by linarith [hs.out] : 4 * s - 1 ≤ 0)]
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem gcut_contDiff (T : ℝ) (n : ℕ∞) : ContDiff ℝ n (gcut T) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (Complex.imCLM.contDiff.sub
    contDiff_const))

def boxH (T : ℝ) : Set ℍ := ((↑) : ℍ → ℂ) ⁻¹' box T

theorem isCompact_coe_preimage {K : Set ℂ} (hK : IsCompact K) (hK' : K ⊆ 𝕌) :
    IsCompact (((↑) : ℍ → ℂ) ⁻¹' K) := by
  refine isEmbedding_coe.isCompact_iff.2 ?_
  rw [image_preimage_eq_of_subset]
  · exact hK
  · intro z hz; exact ⟨⟨z, hK' hz⟩, rfl⟩

theorem box_subset (T : ℝ) : box T ⊆ 𝕌 := fun _ hz => im_pos_of_mem_box hz

theorem isCompact_boxH (T : ℝ) : IsCompact (boxH T) :=
  isCompact_coe_preimage (isCompact_box T) (box_subset T)

theorem hasFiniteSupport_bump_mob (T : ℝ) (τ : ℍ) :
    Function.HasFiniteSupport fun γ : SL(2, ℤ) => bump T (mob γ τ) := by
  refine (finite_moving {τ} (boxH T) isCompact_singleton (isCompact_boxH T)).subset ?_
  intro γ hγ
  refine ⟨γ • τ, ⟨τ, rfl, rfl⟩, ?_⟩
  show ((γ • τ : ℍ) : ℂ) ∈ box T
  rw [coe_smul]
  exact support_bump_subset T hγ

theorem hasFiniteSupport_puCut_mob (T : ℝ) (τ : ℍ) :
    Function.HasFiniteSupport fun γ : SL(2, ℤ) => puCut T (mob γ τ) :=
  (hasFiniteSupport_bump_mob T τ).subset fun _ hγ =>
    support_pu_subset T (left_ne_zero_of_mul hγ)

theorem hasFiniteSupport_pu_mob (T : ℝ) (τ : ℍ) :
    Function.HasFiniteSupport fun γ : SL(2, ℤ) => pu T (mob γ τ) :=
  (hasFiniteSupport_bump_mob T τ).subset fun _ hγ => support_pu_subset T hγ

theorem bump_le_cover (T : ℝ) (τ : ℍ) (γ : SL(2, ℤ)) : bump T (mob γ τ) ≤ cover T τ :=
  single_le_finsum γ (hasFiniteSupport_bump_mob T τ) fun _ => bump_nonneg _ _

theorem cover_mob (T : ℝ) (γ' : SL(2, ℤ)) (τ : ℍ) : cover T (mob γ' τ) = cover T τ := by
  unfold cover
  simp_rw [mob_mob]
  exact finsum_comp_equiv (Equiv.mulRight γ') (f := fun γ => bump T (mob γ τ))

theorem half_le_cover {T : ℝ} (τ : ℍ) (h1 : τ.im ≤ T + 3) (h2 : τ.im⁻¹ ≤ T + 3) :
    1 / 2 ≤ cover T τ := by
  obtain ⟨γ, hre, him, him'⟩ := exists_smul_nice τ
  refine le_trans ?_ (bump_le_cover T τ γ)
  rw [← coe_smul]
  unfold bump
  rw [pTwo_eq_one (by rw [coe_im]; exact him)
    (by rw [coe_im]; exact him'.trans (max_le h1 h2)), mul_one]

  have hx : |(↑(γ • τ) : ℂ).re| ≤ 1 / 2 := by rw [coe_re]; exact hre
  rcases abs_le.1 hx with ⟨hx1, hx2⟩
  have st_half : Real.smoothTransition (1 / 2 : ℝ) = 1 / 2 := by
    unfold Real.smoothTransition
    have h : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [h]
    have hp := expNegInvGlue.pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [div_eq_iff (by positivity)]
    ring
  unfold pOne
  rcases le_total (↑(γ • τ) : ℂ).re 0 with h | h
  · rw [Real.smoothTransition.zero_of_nonpos h, sub_zero, ← st_half]
    exact Real.smoothTransition.monotone (by linarith)
  · rw [Real.smoothTransition.one_of_one_le (by linarith)]
    have := Real.smoothTransition.monotone (show (↑(γ • τ) : ℂ).re ≤ 1 / 2 by linarith)
    rw [st_half] at this
    linarith

theorem finsum_pu_mob {T : ℝ} (τ : ℍ) (h : 1 / 2 ≤ cover T τ) :
    ∑ᶠ γ : SL(2, ℤ), pu T (mob γ τ) = 1 := by
  unfold pu
  simp_rw [cover_mob]
  rw [← finsum_mul]
  exact mul_recip_of_half_le h

theorem finsum_pu_mob_le_one (T : ℝ) (τ : ℍ) : ∑ᶠ γ : SL(2, ℤ), pu T (mob γ τ) ≤ 1 := by
  unfold pu
  simp_rw [cover_mob]
  rw [← finsum_mul]
  exact mul_recip_le_one _

theorem cover_eventuallyEq_sum (T : ℝ) {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    ∃ s : Finset SL(2, ℤ), cover T =ᶠ[𝓝 z₀] fun z => ∑ γ ∈ s, bump T (mob γ z) := by
  have hN : Metric.closedBall z₀ (z₀.im / 2) ⊆ 𝕌 := by
    intro z hz
    have h1 := abs_im_le_norm (z - z₀)
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [sub_im] at h1
    have := (abs_le.1 (h1.trans hz)).1
    show 0 < z.im
    linarith
  have hNH : IsCompact (((↑) : ℍ → ℂ) ⁻¹' Metric.closedBall z₀ (z₀.im / 2)) :=
    isCompact_coe_preimage (isCompact_closedBall _ _) hN
  have hfin := finite_moving _ (boxH T) hNH (isCompact_boxH T)
  refine ⟨hfin.toFinset, ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds z₀ (by positivity : 0 < z₀.im / 2)] with z hz
  apply finsum_eq_sum_of_support_subset
  intro γ hγ
  simp only [Set.Finite.coe_toFinset, mem_setOf_eq]
  refine ⟨γ • ⟨z, hN hz⟩, ⟨⟨z, hN hz⟩, hz, rfl⟩, ?_⟩
  show ((γ • (⟨z, hN hz⟩ : ℍ) : ℍ) : ℂ) ∈ box T
  rw [coe_smul]
  exact support_bump_subset T hγ

theorem cover_contDiffAt (T : ℝ) {z : ℂ} (hz : 0 < z.im) (n : ℕ∞) :
    ContDiffAt ℝ n (cover T) z := by
  obtain ⟨s, hs⟩ := cover_eventuallyEq_sum T hz
  refine ContDiffAt.congr_of_eventuallyEq ?_ hs
  exact ContDiffAt.sum fun γ _ => (bump_contDiff T n).contDiffAt.comp z (mob_contDiffAt γ hz n)

theorem pu_contDiff (T : ℝ) (n : ℕ∞) : ContDiff ℝ n (pu T) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  rcases lt_or_ge 0 z.im with hz | hz
  · exact (bump_contDiff T n).contDiffAt.mul ((recip_contDiff n).contDiffAt.comp z
      (cover_contDiffAt T hz n))
  · have : pu T =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(Complex.continuous_im.isOpen_preimage _ isOpen_Iio).mem_nhds
        (show z ∈ Complex.im ⁻¹' Iio (5 / 8 : ℝ) by
          simp only [mem_preimage, mem_Iio]; linarith)] with w hw
      have hb : bump T w = 0 := by
        by_contra hb
        have := (mem_of_bump_ne_zero hb).2.1
        simp only [mem_preimage, mem_Iio] at hw; linarith
      simp [pu, hb]
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem puCut_contDiff (T : ℝ) (n : ℕ∞) : ContDiff ℝ n (puCut T) :=
  (pu_contDiff T n).mul (gcut_contDiff T n)

section Coset

variable {G : Type*} [Group G] (Γ : Subgroup G)

def cosetEquiv : (G ⧸ Γ) × Γ ≃ G where
  toFun p := p.1.out * p.2
  invFun g := ((g : G ⧸ Γ), ⟨(Quotient.out (g : G ⧸ Γ))⁻¹ * g,
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : G ⧸ Γ))⟩)
  left_inv p := by
    obtain ⟨q, γ⟩ := p
    have hq : ((q.out * (γ : G) : G) : G ⧸ Γ) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ γ.2, QuotientGroup.out_eq']
    ext
    · exact hq
    · simp only
      rw [hq, inv_mul_cancel_left]
  right_inv g := by
    simp only
    rw [mul_inv_cancel_left]

theorem cosetEquiv_apply (p : (G ⧸ Γ) × Γ) : cosetEquiv Γ p = p.1.out * p.2 := rfl

theorem finsum_sum_coset [Fintype (G ⧸ Γ)] {M : Type*} [AddCommMonoid M] (f : G → M)
    (hf : Function.HasFiniteSupport f) :
    ∑ᶠ γ : Γ, ∑ q : G ⧸ Γ, f (q.out * γ) = ∑ᶠ g : G, f g := by
  have hinj : ∀ q : G ⧸ Γ, Function.HasFiniteSupport fun γ : Γ => f (q.out * γ) := by
    intro q
    refine (hf.preimage (f := fun γ : Γ => q.out * (γ : G)) ?_)
    exact (fun a _ b _ h => Subtype.ext (mul_left_cancel h))
  rw [finsum_sum_comm _ (fun (γ : Γ) (q : G ⧸ Γ) => f (q.out * γ)) fun q _ => hinj q]
  have hF : Function.HasFiniteSupport fun p : (G ⧸ Γ) × Γ => f (cosetEquiv Γ p) :=
    hf.preimage (cosetEquiv Γ).injective.injOn
  rw [← finsum_comp_equiv (cosetEquiv Γ) (f := f), finsum_curry _ hF, finsum_eq_sum_of_fintype]
  rfl

end Coset

section Support

variable (Γ : Subgroup SL(2, ℤ)) (T : ℝ)

theorem im_pos_of_puCut_mob_ne_zero {T : ℝ} {σ : SL(2, ℤ)} {z : ℂ} (h : puCut T (mob σ z) ≠ 0) :
    0 < z.im :=
  im_pos_of_im_mob_pos σ (im_pos_of_bump_ne_zero (support_pu_subset T (left_ne_zero_of_mul h)))

def piece (T : ℝ) (σ : SL(2, ℤ)) : Set ℂ := ((↑) : ℍ → ℂ) '' (σ⁻¹ • boxH T)

theorem isCompact_piece (σ : SL(2, ℤ)) : IsCompact (piece T σ) :=
  ((isCompact_boxH T).smul σ⁻¹).image continuous_coe

theorem piece_subset (σ : SL(2, ℤ)) : piece T σ ⊆ 𝕌 := by
  rintro _ ⟨τ, -, rfl⟩; exact τ.im_pos

theorem mem_piece_of_ne_zero {T : ℝ} {σ : SL(2, ℤ)} {z : ℂ} (h : puCut T (mob σ z) ≠ 0) :
    z ∈ piece T σ := by
  have hz := im_pos_of_puCut_mob_ne_zero h
  refine ⟨⟨z, hz⟩, ?_, rfl⟩
  rw [Set.mem_inv_smul_set_iff]
  show ((σ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) ∈ box T
  rw [coe_smul]
  exact support_puCut_subset T h

theorem puCut_mob_contDiff (σ : SL(2, ℤ)) (n : ℕ∞) : ContDiff ℝ n fun z => puCut T (mob σ z) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  rcases lt_or_ge 0 z.im with hz | hz
  · exact (puCut_contDiff T n).contDiffAt.comp z (mob_contDiffAt σ hz n)
  · have hzK : z ∉ piece T σ := fun h => absurd (piece_subset T σ h) (not_lt.2 hz)
    have hev : (fun w => puCut T (mob σ w)) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(isCompact_piece T σ).isClosed.isOpen_compl.mem_nhds hzK] with w hw
      by_contra h
      exact hw (mem_piece_of_ne_zero h)
    exact contDiffAt_const.congr_of_eventuallyEq hev

variable [Γ.FiniteIndex]

scoped instance : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _

def carrier : Set ℂ := ⋃ q : SL(2, ℤ) ⧸ Γ, piece T (Quotient.out q)

theorem isCompact_carrier : IsCompact (carrier Γ T) :=
  isCompact_iUnion fun q => isCompact_piece T _

theorem carrier_subset : carrier Γ T ⊆ 𝕌 :=
  Set.iUnion_subset fun q => piece_subset T _

theorem mem_carrier_of_ne_zero {z : ℂ} (h : ModularCurve.smoothedFundamental Γ T z ≠ 0) :
    z ∈ carrier Γ T := by
  rw [smoothedFundamental_eq_sum] at h
  obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact Set.mem_iUnion.2 ⟨q, mem_piece_of_ne_zero hq⟩

theorem eq_zero_of_notMem_carrier {z : ℂ} (h : z ∉ carrier Γ T) :
    ModularCurve.smoothedFundamental Γ T z = 0 := by
  by_contra h'; exact h (mem_carrier_of_ne_zero Γ T h')

theorem hasCompactSupport : HasCompactSupport (ModularCurve.smoothedFundamental Γ T) :=
  HasCompactSupport.intro (isCompact_carrier Γ T) fun _ hz => eq_zero_of_notMem_carrier Γ T hz

theorem tsupport_subset : tsupport (ModularCurve.smoothedFundamental Γ T) ⊆ 𝕌 :=
  (closure_minimal (fun _ hz => mem_carrier_of_ne_zero Γ T hz)
    (isCompact_carrier Γ T).isClosed).trans (carrier_subset Γ T)

private theorem _root_.ModularCurve.SmoothedFundamentalProof.contDiff (n : ℕ∞) : ContDiff ℝ n (ModularCurve.smoothedFundamental Γ T) := by
  have : ModularCurve.smoothedFundamental Γ T =
      fun z => ∑ q : SL(2, ℤ) ⧸ Γ, puCut T (mob (Quotient.out q) z) :=
    funext (smoothedFundamental_eq_sum Γ T)
  rw [this]
  exact ContDiff.sum fun q _ => puCut_mob_contDiff T _ n

p2m_export "ModularCurve.SmoothedFundamentalProof" "contDiff"
end Support

section Sums

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (T : ℝ)

theorem finsum_smul_eq (τ : ℍ) :
    ∑ᶠ γ : Γ, ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) =
      ∑ᶠ δ : SL(2, ℤ), puCut T (mob δ τ) := by
  have h1 : ∀ γ : Γ, ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) =
      ∑ q : SL(2, ℤ) ⧸ Γ, puCut T (mob (Quotient.out q * (γ : SL(2, ℤ))) τ) := by
    intro γ
    rw [smoothedFundamental_eq_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [coe_smul, mob_mob]
  simp_rw [h1]
  exact finsum_sum_coset Γ (fun δ => puCut T (mob δ τ)) (hasFiniteSupport_puCut_mob T τ)

def carrierH : Set ℍ := ((↑) : ℍ → ℂ) ⁻¹' carrier Γ T

theorem isCompact_carrierH : IsCompact (carrierH Γ T) :=
  isCompact_coe_preimage (isCompact_carrier Γ T) (carrier_subset Γ T)

theorem finite_support_smul (τ : ℍ) :
    (Function.support fun γ : Γ =>
      ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ)).Finite := by
  have hfin := finite_moving {τ} (carrierH Γ T) isCompact_singleton (isCompact_carrierH Γ T)
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  intro γ hγ
  refine ⟨(γ : SL(2, ℤ)) • τ, ⟨τ, rfl, rfl⟩, ?_⟩
  exact mem_carrier_of_ne_zero Γ T hγ

theorem finsum_smul_le_one (τ : ℍ) :
    ∑ᶠ γ : Γ, ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) ≤ 1 := by
  rw [finsum_smul_eq]
  refine le_trans ?_ (finsum_pu_mob_le_one T τ)
  have hf := hasFiniteSupport_puCut_mob T τ
  have hg := hasFiniteSupport_pu_mob T τ
  rw [finsum_eq_sum_of_support_subset _
      (show Function.support (fun γ : SL(2, ℤ) => puCut T (mob γ τ)) ⊆
        ↑(hf.toFinset ∪ hg.toFinset) by
        intro γ hγ; simp only [Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inl hγ),
    finsum_eq_sum_of_support_subset _
      (show Function.support (fun γ : SL(2, ℤ) => pu T (mob γ τ)) ⊆
        ↑(hf.toFinset ∪ hg.toFinset) by
        intro γ hγ; simp only [Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inr hγ)]
  exact Finset.sum_le_sum fun γ _ => puCut_le_pu T _

theorem finsum_smul_eq_one {τ : ℍ} (hτ : max τ.im τ.im⁻¹ ≤ T) :
    ∑ᶠ γ : Γ, ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = 1 := by
  rw [finsum_smul_eq]
  have h1 : τ.im ≤ T + 3 := by linarith [le_max_left τ.im τ.im⁻¹]
  have h2 : τ.im⁻¹ ≤ T + 3 := by linarith [le_max_right τ.im τ.im⁻¹]
  rw [← finsum_pu_mob τ (half_le_cover τ h1 h2)]
  refine finsum_congr fun δ => puCut_eq_pu_of_im_le ?_
  rw [← coe_smul, UpperHalfPlane.coe_im]
  exact (im_smul_le_max δ τ).trans hτ

theorem exists_finset_disjoint :
    ∃ G : Finset SL(2, ℤ), ∀ δ : SL(2, ℤ), δ ∉ G → ∀ τ : ℍ,
      ModularCurve.smoothedFundamental Γ T τ ≠ 0 →
        ModularCurve.smoothedFundamental Γ T ((δ • τ : ℍ) : ℂ) = 0 := by
  have hfin := finite_moving (carrierH Γ T) (carrierH Γ T) (isCompact_carrierH Γ T)
    (isCompact_carrierH Γ T)
  refine ⟨hfin.toFinset, fun δ hδ τ hτ => ?_⟩
  by_contra h
  refine hδ (hfin.mem_toFinset.2 ⟨δ • τ, ⟨τ, ?_, rfl⟩, ?_⟩)
  · exact mem_carrier_of_ne_zero Γ T hτ
  · exact mem_carrier_of_ne_zero Γ T h

end Sums

end ModularCurve.SmoothedFundamentalProof
p2m_reactivate "P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.ModularCurve P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.ModularCurve.SmoothedFundamentalProof"
p2m_reactivate "P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.ModularCurve"

open ModularCurve.SmoothedFundamentalProof in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (T : ℝ) :
    (∀ n : ℕ∞, ContDiff ℝ n (ModularCurve.smoothedFundamental Γ T)) ∧
    HasCompactSupport (ModularCurve.smoothedFundamental Γ T) ∧
    tsupport (ModularCurve.smoothedFundamental Γ T) ⊆ {z : ℂ | 0 < z.im} ∧
    (∀ z : ℂ, 0 ≤ ModularCurve.smoothedFundamental Γ T z) ∧
    (∀ τ : ℍ, (Function.support fun γ : Γ =>
        ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ)).Finite) ∧
    (∀ τ : ℍ,
      ∑ᶠ γ : Γ, ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) ≤ 1) ∧
    (∀ τ : ℍ, max τ.im τ.im⁻¹ ≤ T →
      ∑ᶠ γ : Γ, ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = 1) ∧
    (∃ G : Finset SL(2, ℤ), ∀ δ : SL(2, ℤ), δ ∉ G → ∀ τ : ℍ,
      ModularCurve.smoothedFundamental Γ T τ ≠ 0 →
        ModularCurve.smoothedFundamental Γ T ((δ • τ : ℍ) : ℂ) = 0) :=
  ⟨contDiff Γ T, hasCompactSupport Γ T, tsupport_subset Γ T,
    ModularCurve.SmoothedFundamental.smoothedFundamental_nonneg Γ T, finite_support_smul Γ T,
    finsum_smul_le_one Γ T, fun _ hτ => finsum_smul_eq_one Γ T hτ, exists_finset_disjoint Γ T⟩

end
p2m_reactivate "P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.ModularCurve P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.ModularCurve.SmoothedFundamentalProof"

end S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one
end P2MW
export P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one (solution)
