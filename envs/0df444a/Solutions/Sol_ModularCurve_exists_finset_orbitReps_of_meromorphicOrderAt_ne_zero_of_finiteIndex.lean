-- Prove2me | solution 1 for ModularCurve.exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1cd9fc08-4230-5d4d-9487-0fbdd722e2a7

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Definitions.Def_AutomorphicForm_SiegelSetCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Filter
open scoped MatrixGroups Topology

namespace ModularCurve
p2m_export "ModularCurve" "periodOf"
namespace FiniteDivisorProofOf
p2m_open "ModularCurve"

def J (γ : SL(2, ℤ)) (z : ℂ) : ℂ := denom (γ : GL (Fin 2) ℝ) z

def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ := num (γ : GL (Fin 2) ℝ) z / denom (γ : GL (Fin 2) ℝ) z

theorem J_apply (γ : SL(2, ℤ)) (z : ℂ) :
    J γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [J, denom]

theorem num_apply (γ : SL(2, ℤ)) (z : ℂ) :
    num (γ : GL (Fin 2) ℝ) z = ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) := by
  simp [num]

theorem mob_apply (γ : SL(2, ℤ)) (z : ℂ) :
    mob γ z = (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) / J γ z := by
  rw [mob, num_apply]; rfl

theorem det_one (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
  have := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at this
  exact_mod_cast this

theorem J_coe_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : J γ τ ≠ 0 := denom_ne_zero_of_im _ τ.im_ne_zero

theorem coe_smul_eq_mob (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) = mob γ τ := by
  rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]
  rfl

theorem analyticAt_J (γ : SL(2, ℤ)) (z : ℂ) : AnalyticAt ℂ (J γ) z := by
  simp only [funext (J_apply γ)]
  fun_prop

theorem analyticAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : J γ z ≠ 0) : AnalyticAt ℂ (mob γ) z := by
  simp only [funext (mob_apply γ)]
  exact AnalyticAt.div (by fun_prop) (analyticAt_J γ z) hz

theorem hasDerivAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : J γ z ≠ 0) :
    HasDerivAt (mob γ) (J γ z ^ 2)⁻¹ z := by
  have h1 : HasDerivAt (fun w : ℂ => ((γ 0 0 : ℤ) : ℂ) * w + ((γ 0 1 : ℤ) : ℂ))
      ((γ 0 0 : ℤ) : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((γ 0 0 : ℤ) : ℂ)).add_const ((γ 0 1 : ℤ) : ℂ)
  have h2 : HasDerivAt (J γ) ((γ 1 0 : ℤ) : ℂ) z := by
    rw [funext (J_apply γ)]
    simpa using ((hasDerivAt_id z).const_mul ((γ 1 0 : ℤ) : ℂ)).add_const ((γ 1 1 : ℤ) : ℂ)
  have h3 := h1.div h2 hz
  rw [funext (mob_apply γ)]
  refine h3.congr_deriv (Eq.symm ?_)
  have hd := det_one γ
  rw [J_apply] at hz ⊢
  field_simp
  linear_combination (-1) * hd

theorem deriv_mob_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : J γ z ≠ 0) : deriv (mob γ) z ≠ 0 := by
  rw [(hasDerivAt_mob γ hz).deriv]
  exact inv_ne_zero (pow_ne_zero _ hz)

theorem meromorphicOrderAt_comp_mob (f : ℂ → ℂ) (γ : SL(2, ℤ)) {z : ℂ} (hz : J γ z ≠ 0) :
    meromorphicOrderAt (f ∘ mob γ) z = meromorphicOrderAt f (mob γ z) :=
  meromorphicOrderAt_comp_of_deriv_ne_zero (analyticAt_mob γ hz) (deriv_mob_ne_zero γ hz)

theorem eventually_comp_mob (F : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    ∀ᶠ z in 𝓝 (τ : ℂ), F (ofComplex (mob γ z)) = F (γ • ofComplex z) := by
  have hpos : ∀ᶠ z in 𝓝 (τ : ℂ), 0 < z.im :=
    Complex.continuous_im.continuousAt.eventually (lt_mem_nhds τ.im_pos)
  filter_upwards [hpos] with z hz
  have h1 : ofComplex z = ⟨z, hz⟩ := ofComplex_apply_of_im_pos hz
  rw [h1]
  have h2 : mob γ z = ((γ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := (coe_smul_eq_mob γ ⟨z, hz⟩).symm
  rw [h2, ofComplex_apply]

theorem meromorphicOrderAt_smul (F : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) ((γ • τ : ℍ) : ℂ) =
      meromorphicOrderAt (fun z : ℂ => F (γ • ofComplex z)) (τ : ℂ) := by
  rw [coe_smul_eq_mob, ← meromorphicOrderAt_comp_mob _ γ (J_coe_ne_zero γ τ)]
  apply meromorphicOrderAt_congr
  exact eventually_nhdsWithin_of_eventually_nhds (eventually_comp_mob F γ τ)

theorem meromorphicAt_smul (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (γ : SL(2, ℤ)) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => F (γ • ofComplex z)) (τ : ℂ) := by
  have h1 : MeromorphicAt ((fun z : ℂ => F (ofComplex z)) ∘ mob γ) (τ : ℂ) := by
    apply MeromorphicAt.comp_analyticAt _ (analyticAt_mob γ (J_coe_ne_zero γ τ))
    rw [← coe_smul_eq_mob]
    exact hF _
  exact h1.congr (eventually_nhdsWithin_of_eventually_nhds (eventually_comp_mob F γ τ))

theorem meromorphicOrderAt_smul_of_mul (F : ℍ → ℂ) (γ : SL(2, ℤ)) {c : ℂ} (hc : c ≠ 0)
    (h : ∀ w : ℍ, F (γ • w) = c * F w) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) ((γ • τ : ℍ) : ℂ) =
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) := by
  rw [meromorphicOrderAt_smul]
  simp only [h]
  exact meromorphicOrderAt_mul_of_ne_zero (f := fun z : ℂ => F (ofComplex z))
    (g := fun _ => c) analyticAt_const hc

def H : Set ℂ := {z : ℂ | 0 < z.im}

theorem isPreconnected_H : IsPreconnected H := (convex_halfSpace_im_gt 0).isPreconnected

theorem meromorphicOn_H (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) :
    MeromorphicOn (fun z : ℂ => F (ofComplex z)) H := fun z hz => by
  simpa using hF ⟨z, hz⟩

theorem exists_meromorphicOrderAt_ne_top (F : ℍ → ℂ)
    {L : ℂ} (hL : L ≠ 0) (h : Tendsto F atImInfty (𝓝 L)) :
    ∃ τ₀ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ₀ : ℂ) ≠ ⊤ := by
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 (h.eventually_ne hL)
  set y : ℝ := max A 0 + 1 with hy
  have hypos : 0 < y := by rw [hy]; positivity
  have hyA : A < y := by rw [hy]; exact lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  let τ₀ : ℍ := ⟨Complex.I * y, by simpa using hypos⟩
  have him : (τ₀ : ℂ).im = y := by
    change (Complex.I * y).im = y
    simp
  refine ⟨τ₀, fun htop => ?_⟩
  rw [meromorphicOrderAt_eq_top_iff] at htop
  have hnhds : ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), A < z.im ∧ 0 < z.im := by
    apply eventually_nhdsWithin_of_eventually_nhds
    have hc : ContinuousAt Complex.im (τ₀ : ℂ) := Complex.continuous_im.continuousAt
    exact (hc.eventually (lt_mem_nhds (by rw [him]; exact hyA))).and
      (hc.eventually (lt_mem_nhds (by rw [him]; exact hypos)))
  obtain ⟨z, hz0, hzA, hzim⟩ := (htop.and hnhds).exists
  refine hA ⟨z, hzim⟩ ?_ ?_
  · change A ≤ z.im
    exact hzA.le
  · simpa [ofComplex_apply_of_im_pos hzim] using hz0

theorem meromorphicOrderAt_ne_top (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    {L : ℂ} (hL : L ≠ 0) (h : Tendsto F atImInfty (𝓝 L)) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ ⊤ := by
  obtain ⟨τ₀, hτ₀⟩ := exists_meromorphicOrderAt_ne_top F hL h
  exact (meromorphicOn_H F hF).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_H (τ₀.im_pos : (τ₀ : ℂ) ∈ H) (τ.im_pos : (τ : ℂ) ∈ H) hτ₀

theorem meromorphicOrderAt_eq_zero_of_tendsto (G : ℍ → ℂ) {L : ℂ} (hL : L ≠ 0)
    (h : Tendsto G atImInfty (𝓝 L)) :
    ∃ A : ℝ, ∀ w : ℍ, A < w.im → MeromorphicAt (fun z : ℂ => G (ofComplex z)) (w : ℂ) →
      meromorphicOrderAt (fun z : ℂ => G (ofComplex z)) (w : ℂ) = 0 := by
  have hL2 : 0 < ‖L‖ / 2 := by positivity
  have hev : ∀ᶠ τ in atImInfty, dist (G τ) L < ‖L‖ / 2 := h (Metric.ball_mem_nhds L hL2)
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 hev
  refine ⟨A, fun w hw hGw => ?_⟩
  set g : ℂ → ℂ := fun z => G (ofComplex z) with hg

  have hnear : ∀ᶠ z in 𝓝[≠] (w : ℂ), dist (g z) L < ‖L‖ / 2 := by
    apply eventually_nhdsWithin_of_eventually_nhds
    have hc : ContinuousAt Complex.im (w : ℂ) := Complex.continuous_im.continuousAt
    have h1 : ∀ᶠ z in 𝓝 (w : ℂ), A < z.im := hc.eventually (lt_mem_nhds hw)
    have h2 : ∀ᶠ z in 𝓝 (w : ℂ), 0 < z.im := hc.eventually (lt_mem_nhds w.im_pos)
    filter_upwards [h1, h2] with z hzA hz0
    have := hA ⟨z, hz0⟩ hzA.le
    simpa [hg, ofComplex_apply_of_im_pos hz0] using this

  have hntop : meromorphicOrderAt g (w : ℂ) ≠ ⊤ := by
    intro htop
    rw [meromorphicOrderAt_eq_top_iff] at htop
    obtain ⟨z, hz0, hzL⟩ := (htop.and hnear).exists
    rw [hz0, dist_zero_left] at hzL
    linarith [norm_nonneg L]

  have hnneg : 0 ≤ meromorphicOrderAt g (w : ℂ) := by
    by_contra hneg
    rw [not_le] at hneg
    have hcb := tendsto_cobounded_of_meromorphicOrderAt_neg hneg
    have hbig : ∀ᶠ z in 𝓝[≠] (w : ℂ), 2 * ‖L‖ < ‖g z‖ := by
      have := hcb.eventually (eventually_cobounded_le_norm (2 * ‖L‖ + 1))
      exact this.mono fun z hz => by linarith
    obtain ⟨z, hz1, hz2⟩ := (hbig.and hnear).exists
    have : ‖g z‖ ≤ ‖g z - L‖ + ‖L‖ := norm_le_norm_sub_add _ _
    rw [dist_eq_norm] at hz2
    linarith [norm_nonneg L]

  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hGw hnneg
  have hcL : dist c L ≤ ‖L‖ / 2 := by
    have h1 : Tendsto (fun z => dist (g z) L) (𝓝[≠] (w : ℂ)) (𝓝 (dist c L)) :=
      hc.dist tendsto_const_nhds
    exact le_of_tendsto h1 (hnear.mono fun z hz => hz.le)
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, dist_zero_left] at hcL
    linarith [norm_pos_iff.2 hL]
  exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hGw).1 ⟨c, hc0, hc⟩

theorem finite_setOf_order_ne_zero (f : ℂ → ℂ) (hf : MeromorphicOn f H) {K : Set ℍ}
    (hK : IsCompact K) :
    {τ : ℍ | τ ∈ K ∧ meromorphicOrderAt f τ ≠ 0 ∧ meromorphicOrderAt f τ ≠ ⊤}.Finite := by
  classical
  set V : Set ℂ := ((↑) : ℍ → ℂ) '' K with hV
  have hVH : V ⊆ H := by
    rintro _ ⟨τ, -, rfl⟩
    exact τ.im_pos
  have hVc : IsCompact V := hK.image UpperHalfPlane.continuous_coe
  have hfin := ((MeromorphicOn.divisor f H).restrict hVH).finiteSupport hVc
  have hsub : {τ : ℍ | τ ∈ K ∧ meromorphicOrderAt f τ ≠ 0 ∧ meromorphicOrderAt f τ ≠ ⊤} ⊆
      ((↑) : ℍ → ℂ) ⁻¹' Function.support ((MeromorphicOn.divisor f H).restrict hVH) := by
    rintro τ ⟨hτK, h0, htop⟩
    have hτV : (τ : ℂ) ∈ V := ⟨τ, hτK, rfl⟩
    change ((MeromorphicOn.divisor f H).restrict hVH) τ ≠ 0
    rw [Function.locallyFinsuppWithin.restrict_apply, if_pos hτV,
      MeromorphicOn.divisor_apply hf (hVH hτV)]
    simp [WithTop.untop₀_eq_zero, h0, htop]
  exact (hfin.preimage (UpperHalfPlane.coe_injective.injOn)).subset hsub

theorem exists_finset_inequiv {G X : Type*} [Group G] [MulAction G X] (S : Finset X) :
    ∃ S' : Finset X, (∀ σ ∈ S', ∀ σ' ∈ S', ∀ g : G, g • σ = σ' → σ = σ') ∧
      ∀ σ ∈ S, ∃ σ' ∈ S', ∃ g : G, g • σ' = σ := by
  classical
  let π : X → Quotient (MulAction.orbitRel G X) := fun x => Quotient.mk _ x
  refine ⟨(S.image π).image Quotient.out, ?_, ?_⟩
  · intro σ hσ σ' hσ' g hg
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hσ
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hσ'
    have hab : a = b := by
      rw [← Quotient.out_eq a, ← Quotient.out_eq b]
      apply Quotient.sound
      change a.out ∈ MulAction.orbit G b.out
      exact ⟨g⁻¹, by simp [← hg]⟩
    rw [hab]
  · intro σ hσ
    refine ⟨(π σ).out, Finset.mem_image.2 ⟨π σ, Finset.mem_image.2 ⟨σ, hσ, rfl⟩, rfl⟩, ?_⟩
    have h : (π σ).out ∈ MulAction.orbit G σ := by
      have := Quotient.mk_out (s := MulAction.orbitRel G X) σ
      exact this
    obtain ⟨g, hg⟩ := h
    exact ⟨g⁻¹, by simp [← hg]⟩

open scoped Modular in

theorem exists_finset_orbitReps (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (χ : Γ → ℂ) (hχ0 : ∀ γ, χ γ ≠ 0)
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ S : Finset ℍ, ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ 0 →
      ∃ σ ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • σ = τ := by
  classical
  set f : ℂ → ℂ := fun z => F (ofComplex z) with hfdef

  have hA : ∀ q : SL(2, ℤ) ⧸ Γ, ∃ A : ℝ, ∀ w : ℍ, A < w.im →
      meromorphicOrderAt f (((Quotient.out q)⁻¹ • w : ℍ) : ℂ) = 0 := by
    intro q
    obtain ⟨L, hL, hT⟩ := hcusp (Quotient.out q)⁻¹
    obtain ⟨A, hA⟩ :=
      meromorphicOrderAt_eq_zero_of_tendsto (fun τ => F ((Quotient.out q)⁻¹ • τ)) hL hT
    refine ⟨A, fun w hw => ?_⟩
    rw [hfdef, meromorphicOrderAt_smul]
    exact hA w hw (meromorphicAt_smul F hF _ w)
  choose A hA using hA
  obtain ⟨M, hM⟩ := Finite.bddAbove_range A
  set K : Set ℍ := FLT.Gamma0FundamentalSet.truncatedGammaFundamentalSet
    (Γ) M with hKdef
  have hK : IsCompact K := FLT.Gamma0FundamentalSet.isCompact_truncatedGammaFundamentalSet Γ M
  have hfH : MeromorphicOn f H := fun z hz => by simpa [hfdef] using hF ⟨z, hz⟩
  obtain ⟨L₁, hL₁, hT₁⟩ := hcusp 1
  simp only [one_smul] at hT₁
  have hntop : ∀ τ : ℍ, meromorphicOrderAt f τ ≠ ⊤ := meromorphicOrderAt_ne_top F hF hL₁ hT₁
  refine ⟨(finite_setOf_order_ne_zero f hfH hK).toFinset, fun τ hτ => ?_⟩
  obtain ⟨γ, hγ, hmem⟩ :=
    FLT.Gamma0FundamentalSet.exists_smul_mem_gammaFundamentalSet (Γ) τ
  obtain ⟨q, hq⟩ := FLT.Gamma0FundamentalSet.mem_gammaFundamentalSet_iff.1 hmem

  have hord : meromorphicOrderAt f ((γ • τ : ℍ) : ℂ) = meromorphicOrderAt f τ :=
    meromorphicOrderAt_smul_of_mul F γ (hχ0 ⟨γ, hγ⟩) (fun w => hχ ⟨γ, hγ⟩ w) τ

  set w : ℍ := Quotient.out q • γ • τ with hwdef
  have hγτ : γ • τ = (Quotient.out q)⁻¹ • w := (inv_smul_smul _ _).symm
  have him : w.im ≤ M := by
    by_contra hlt
    rw [not_le] at hlt
    have h0 := hA q w (lt_of_le_of_lt (hM ⟨q, rfl⟩) hlt)
    rw [← hγτ, hord] at h0
    exact hτ h0
  have hKmem : γ • τ ∈ K := by
    rw [hγτ, hKdef]
    exact Set.mem_iUnion.2 ⟨q, Set.smul_mem_smul_set ⟨hq, him⟩⟩
  refine ⟨γ • τ, (Set.Finite.mem_toFinset _).2 ⟨hKmem, by rwa [hord], hntop _⟩, ⟨γ, hγ⟩⁻¹, ?_⟩
  simp

end ModularCurve.FiniteDivisorProofOf

end

open UpperHalfPlane
open scoped MatrixGroups Topology

open ModularCurve.FiniteDivisorProofOf in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ S : Finset ℍ,
      (∀ s ∈ S, ∀ t ∈ S,
        (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t) ∧
      ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ 0 →
        ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ := by
  obtain ⟨S₀, hS₀⟩ := exists_finset_orbitReps Γ F hF
    (fun γ => Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)))
    (fun _ => Complex.exp_ne_zero _) hχ hcusp
  obtain ⟨S, hS1, hS2⟩ := exists_finset_inequiv (G := Γ) S₀
  refine ⟨S, fun s hs t ht ⟨γ, hγ⟩ => hS1 s hs t ht γ hγ, fun τ hτ => ?_⟩
  obtain ⟨σ, hσ, γ, hγ⟩ := hS₀ τ hτ
  obtain ⟨s, hs, δ, hδ⟩ := hS2 σ hσ
  refine ⟨s, hs, γ * δ, ?_⟩
  rw [← hγ, ← hδ, Subgroup.coe_mul, mul_smul]
  rfl

end S_ModularCurve_exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex
end P2MW
export P2MW.S_ModularCurve_exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex (solution)
