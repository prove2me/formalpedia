-- Prove2me | solution 5 for MilnorDynamics.thrice_punctured_plane_disk_cover
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-02T15:52:07.144125+00:00
-- url     : https://prove2.me/submissions/c64648b6-5a3b-4a52-b1b5-f6e1bebfadcf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_MilnorDynamics_gammaTwo_smul_nhds_disjoint
import Theorems.Thm_MilnorDynamics_modular_lambda_exists

open scoped OnePoint
open Filter Set Topology UpperHalfPlane
open scoped MatrixGroups

open MilnorDynamics

/-- The subgroup of permutations of `ℍ` induced by `Γ(2)`. -/
private noncomputable abbrev gammaTwoPerm : Subgroup (Equiv.Perm ℍ) :=
  (CongruenceSubgroup.Gamma 2).map (MulAction.toPermHom SL(2, ℤ) ℍ)

private lemma gammaTwoPerm_eq_one {σ : gammaTwoPerm} {γ : SL(2, ℤ)}
    (hγ : γ = 1 ∨ γ = -1) (hσ : MulAction.toPermHom SL(2, ℤ) ℍ γ = σ) : σ = 1 := by
  apply Subtype.ext
  rw [← hσ]
  rcases hγ with rfl | rfl
  · ext τ
    simp
  · ext τ
    simp

private lemma gammaTwoPerm_smul (σ : gammaTwoPerm) (τ : ℍ) : σ • τ = (σ : Equiv.Perm ℍ) τ := rfl

/-- Covering criterion on `ℍ`. -/
private lemma upper_half_plane_cover_aux (p : ℂ → ℂ)
    (hdiff : DifferentiableOn ℂ p {z : ℂ | 0 < z.im})
    (hne : ∀ τ : ℍ, p τ ≠ 0 ∧ p τ ≠ 1)
    (hsurj : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∃ τ : ℍ, p τ = w)
    (hfib : ∀ τ τ' : ℍ, p τ = p τ' ↔ ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ = τ') :
    let q : ℍ → ({0, 1}ᶜ : Set ℂ) := fun τ => ⟨p τ, by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]; exact hne τ⟩
    Function.Surjective q ∧ IsCoveringMap q := by
  intro q
  have hqsurj : Function.Surjective q := by
    rintro ⟨w, hw⟩
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hw
    obtain ⟨τ, hτ⟩ := hsurj w hw.1 hw.2
    exact ⟨τ, Subtype.ext hτ⟩
  refine ⟨hqsurj, ?_⟩
  have hopenH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hcont : Continuous q := by
    apply Continuous.subtype_mk
    exact hdiff.continuousOn.comp_continuous UpperHalfPlane.continuous_coe
      (fun τ => τ.2)
  have hopen : IsOpenMap q := by
    have han : AnalyticOnNhd ℂ p {z : ℂ | 0 < z.im} := hdiff.analyticOnNhd hopenH
    have hconn : IsPreconnected {z : ℂ | 0 < z.im} :=
      (convex_halfSpace_im_gt 0).isPreconnected
    rcases han.is_constant_or_isOpen hconn with ⟨w, hw⟩ | hop
    · exfalso
      obtain ⟨τ, hτ⟩ := hsurj (if w = 2 then 3 else 2) (by split_ifs <;> norm_num)
        (by split_ifs <;> norm_num)
      rw [hw τ τ.2] at hτ
      split_ifs at hτ with h <;> simp_all
    · intro V hV
      obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
      have himg : q '' (UpperHalfPlane.coe ⁻¹' W) =
          Subtype.val ⁻¹' (p '' (W ∩ {z : ℂ | 0 < z.im})) := by
        ext ⟨w, hw⟩
        simp only [mem_image, mem_preimage, mem_inter_iff, mem_ofPred_eq, q]
        constructor
        · rintro ⟨τ, hτ, he⟩
          exact ⟨τ, ⟨hτ, τ.2⟩, congrArg Subtype.val he⟩
        · rintro ⟨z, ⟨hzW, hz⟩, he⟩
          exact ⟨⟨z, hz⟩, hzW, Subtype.ext he⟩
      rw [himg]
      exact (hop _ inter_subset_right (hW.inter hopenH)).preimage continuous_subtype_val
  have hquot : IsQuotientMap q := hopen.isQuotientMap hcont hqsurj
  have hfG : ∀ {e₁ e₂ : ℍ}, q e₁ = q e₂ ↔ e₁ ∈ MulAction.orbit gammaTwoPerm e₂ := by
    intro e₁ e₂
    rw [MulAction.mem_orbit_iff]
    constructor
    · intro h
      have h' : p e₂ = p e₁ := (congrArg Subtype.val h).symm
      obtain ⟨γ, hγ, hγe⟩ := (hfib e₂ e₁).mp h'
      exact ⟨⟨MulAction.toPermHom SL(2, ℤ) ℍ γ, γ, hγ, rfl⟩, hγe⟩
    · rintro ⟨⟨σ, γ, hγ, rfl⟩, hσ⟩
      apply Subtype.ext
      exact ((hfib e₂ e₁).mpr ⟨γ, hγ, hσ⟩).symm
  have : ContinuousConstSMul gammaTwoPerm ℍ := by
    constructor
    rintro ⟨σ, γ, hγ, rfl⟩
    change Continuous fun τ : ℍ => γ • τ
    exact continuous_const_smul (γ : GL (Fin 2) ℝ)
  have hdisj : ∀ e : ℍ, ∃ U ∈ 𝓝 e, ∀ g : gammaTwoPerm,
      ((g • ·) '' U ∩ U).Nonempty → g • e = e := by
    intro e
    obtain ⟨U, hU, hUγ⟩ := gammaTwo_smul_nhds_disjoint e
    refine ⟨U, hU, ?_⟩
    rintro ⟨σ, γ, hγ, rfl⟩ ⟨_, ⟨x, hxU, rfl⟩, hx⟩
    have : (⟨_, γ, hγ, rfl⟩ : gammaTwoPerm) = 1 :=
      gammaTwoPerm_eq_one (hUγ γ hγ ⟨x, hxU, hx⟩) rfl
    rw [this, one_smul]
  have hstab : ∀ e : ℍ, MulAction.stabilizer gammaTwoPerm e = ⊥ := by
    intro e
    rw [eq_bot_iff]
    rintro ⟨σ, γ, hγ, rfl⟩ hfix
    rw [Subgroup.mem_bot]
    obtain ⟨U, hU, hUγ⟩ := gammaTwo_smul_nhds_disjoint e
    rw [MulAction.mem_stabilizer_iff] at hfix
    change γ • e = e at hfix
    exact gammaTwoPerm_eq_one (hUγ γ hγ ⟨e, mem_of_mem_nhds hU, by
      rw [hfix]; exact mem_of_mem_nhds hU⟩) rfl
  have hcov := hquot.isCoveringMapOn_of_smul_disjoint hfG hdisj
  have himg : q '' {e | MulAction.stabilizer gammaTwoPerm e = ⊥} = univ := by
    rw [show {e | MulAction.stabilizer gammaTwoPerm e = ⊥} = univ from
      eq_univ_of_forall hstab, image_univ, range_eq_univ.mpr hqsurj]
  rw [himg] at hcov
  exact isCoveringMap_iff_isCoveringMapOn_univ.mpr hcov

/-- `{z | 0 < z.im}` and `ℍ` are the same subtype. -/
private def halfPlaneHomeomorph : ({z : ℂ | 0 < z.im} : Set ℂ) ≃ₜ ℍ where
  toFun z := ⟨z.1, z.2⟩
  invFun τ := ⟨τ, τ.im_pos⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.upperHalfPlaneMk _
  continuous_invFun := UpperHalfPlane.continuous_coe.subtype_mk _

private theorem upper_half_plane_thrice_punctured_cover :
    ∃ p : ℂ → ℂ, DifferentiableOn ℂ p {z : ℂ | 0 < z.im} ∧
      ∃ hp : MapsTo p {z : ℂ | 0 < z.im} ({0, 1}ᶜ : Set ℂ),
        Function.Surjective hp.restrict ∧ IsCoveringMap hp.restrict := by
  obtain ⟨p, hdiff, hne, hsurj, hfib⟩ := modular_lambda_exists
  obtain ⟨hqs, hqc⟩ := upper_half_plane_cover_aux p hdiff hne hsurj hfib
  have hp : MapsTo p {z : ℂ | 0 < z.im} ({0, 1}ᶜ : Set ℂ) := by
    intro z hz
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact hne ⟨z, hz⟩
  refine ⟨p, hdiff, hp, ?_⟩
  have heq : hp.restrict = (fun τ : ℍ => (⟨p τ, by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      exact hne τ⟩ : ({0, 1}ᶜ : Set ℂ))) ∘ halfPlaneHomeomorph := by
    funext z
    rfl
  rw [heq]
  exact ⟨hqs.comp halfPlaneHomeomorph.surjective, hqc.comp_homeomorph halfPlaneHomeomorph⟩


/-- Cayley transform from the unit disc to the upper half-plane. -/
private noncomputable def cayleyMap (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

private lemma one_sub_ne_zero_of_mem_ball {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    1 - w ≠ 0 := by
  intro h
  have : w = 1 := by linear_combination -h
  subst this
  simp at hw

private lemma cayleyMap_im_pos {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    0 < (cayleyMap w).im := by
  have hne := one_sub_ne_zero_of_mem_ball hw
  have hns : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr hne
  have hw2 : w.re ^ 2 + w.im ^ 2 < 1 := by
    have h1 : ‖w‖ < 1 := by simpa using hw
    have h2 : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
    rw [Complex.sq_norm, Complex.normSq_apply] at h2
    nlinarith
  unfold cayleyMap
  rw [Complex.div_im]
  have key : (Complex.I * (1 + w)).im * (1 - w).re / Complex.normSq (1 - w) -
      (Complex.I * (1 + w)).re * (1 - w).im / Complex.normSq (1 - w) =
      (1 - w.re ^ 2 - w.im ^ 2) / Complex.normSq (1 - w) := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    field_simp
    ring
  rw [key]
  apply div_pos _ hns
  linarith

private lemma add_I_ne_zero {z : ℂ} (hz : 0 < z.im) : z + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

private lemma invCayley_mem_ball {z : ℂ} (hz : 0 < z.im) :
    (z - Complex.I) / (z + Complex.I) ∈ Metric.ball (0 : ℂ) 1 := by
  have hne := add_I_ne_zero hz
  rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.mpr hne)]
  have h : ‖z - Complex.I‖ ^ 2 < ‖z + Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.I_re,
      Complex.I_im]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h

/-- The Cayley transform as a homeomorphism from the unit disc onto the upper half-plane. -/
private noncomputable def cayleyHomeomorph :
    Metric.ball (0 : ℂ) 1 ≃ₜ {z : ℂ | 0 < z.im} where
  toFun w := ⟨cayleyMap w, cayleyMap_im_pos w.2⟩
  invFun z := ⟨(z - Complex.I) / (z + Complex.I), invCayley_mem_ball z.2⟩
  left_inv w := by
    have hne := one_sub_ne_zero_of_mem_ball w.2
    apply Subtype.ext
    simp only [cayleyMap]
    have h1 : Complex.I * (1 + (w : ℂ)) / (1 - w) - Complex.I = 2 * Complex.I * w / (1 - w) := by
      field_simp; ring
    have h2 : Complex.I * (1 + (w : ℂ)) / (1 - w) + Complex.I = 2 * Complex.I / (1 - w) := by
      field_simp; ring
    rw [h1, h2, div_div_div_cancel_right₀ hne]
    field_simp
  right_inv z := by
    have hne := add_I_ne_zero z.2
    apply Subtype.ext
    simp only [cayleyMap]
    have h1 : (1 : ℂ) - (z - Complex.I) / (z + Complex.I) = 2 * Complex.I / (z + Complex.I) := by
      field_simp; ring
    rw [h1]
    field_simp
    ring_nf
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousOn.domRestrict (s := Metric.ball (0 : ℂ) 1) (f := cayleyMap)
    intro w hw
    apply ContinuousAt.continuousWithinAt
    unfold cayleyMap
    exact (continuousAt_const.mul (continuousAt_const.add continuousAt_id)).div
      (continuousAt_const.sub continuousAt_id) (one_sub_ne_zero_of_mem_ball hw)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply ContinuousOn.domRestrict (s := {z : ℂ | 0 < z.im})
      (f := fun z : ℂ => (z - Complex.I) / (z + Complex.I))
    intro z hz
    apply ContinuousAt.continuousWithinAt
    exact (continuousAt_id.sub continuousAt_const).div (continuousAt_id.add continuousAt_const)
      (add_I_ne_zero hz)

theorem solution :
    ∃ p : ℂ → ℂ, DifferentiableOn ℂ p (Metric.ball 0 1) ∧
      ∃ hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ),
        Function.Surjective hp.restrict ∧ IsCoveringMap hp.restrict := by
  obtain ⟨p, hdiff, hp, hsurj, hcov⟩ := upper_half_plane_thrice_punctured_cover
  have hmaps : MapsTo cayleyMap (Metric.ball (0 : ℂ) 1) {z : ℂ | 0 < z.im} :=
    fun w hw => cayleyMap_im_pos hw
  have hcay : DifferentiableOn ℂ cayleyMap (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    unfold cayleyMap
    exact ((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
      ((differentiableAt_const _).sub differentiableAt_id) (one_sub_ne_zero_of_mem_ball hw)
  have hpD : MapsTo (p ∘ cayleyMap) (Metric.ball (0 : ℂ) 1) ({0, 1}ᶜ : Set ℂ) :=
    hp.comp hmaps
  refine ⟨p ∘ cayleyMap, hdiff.comp hcay hmaps, hpD, ?_⟩
  have heq : hpD.restrict = hp.restrict ∘ cayleyHomeomorph := by
    funext w
    rfl
  rw [heq]
  exact ⟨hsurj.comp cayleyHomeomorph.surjective, hcov.comp_homeomorph cayleyHomeomorph⟩
