-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.exists_smooth_density_expCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:33:02.96637+00:00
-- url     : https://prove2.me/submissions/89ee54c9-0f7c-4205-9139-68d8a199b320

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarDensity
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_prodExp_eq_expG_prodExpCoord
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_smooth_density_prodExp_tsupport
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_prodExp_coord
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_contDiffOn_prodExpCoord
import Theorems.Thm_GroundTheory_Automorphic_contDiff_det_pi
import Theorems.Thm_GroundTheory_Automorphic_prodExpCoord_zero
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open MeasureTheory Metric Set Filter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ ε > 0, ∀ β : EuclideanSpace ℝ (Fin d) → ℂ, ContDiff ℝ ∞ β →
      tsupport β ⊆ closedBall 0 ε →
      ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧
        HasCompactSupport κ ∧ tsupport κ ⊆ (fun x => h.expG (coordEquiv b x)) '' tsupport β ∧
        ∀ φ : G → ℂ, Continuous φ →
          ∫ y, κ y * φ y ∂μ = ∫ x, β x * φ (h.expG (coordEquiv b x)) := by
  classical
  obtain ⟨ε₁, hε₁, hdens⟩ := h.exists_smooth_density_prodExp_tsupport μ b
  obtain ⟨S, T, ψ, hSo, hTo, h0S, hΦST, hψTS, hψΦ, hΦψ, hψs, hSN⟩ := h.exists_prodExp_coord b
  set Φ := prodExpCoord b with hΦdef
  set P := h.prodExp (⇑b) with hPdef
  have hΦ0 : Φ 0 = 0 := prodExpCoord_zero b
  have h0T : (0 : Fin d → ℝ) ∈ T := hΦ0 ▸ hΦST h0S
  have hψ0 : ψ 0 = 0 := by have := hψΦ 0 h0S; rwa [hΦ0] at this

  have hSU : S ⊆ {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph ℝ 𝔸).target} :=
    fun t ht => h.nhdOne_subset_target (hSN t ht)
  have hΦs : ContDiffOn ℝ ∞ Φ S := (contDiffOn_prodExpCoord b).mono hSU
  have hΦat : ∀ t ∈ S, ContDiffAt ℝ ∞ Φ t := fun t ht => hΦs.contDiffAt (hSo.mem_nhds ht)
  have hψat : ∀ w ∈ T, ContDiffAt ℝ ∞ ψ w := fun w hw => hψs.contDiffAt (hTo.mem_nhds hw)

  have hPΦ : ∀ t ∈ S, P t = h.expG (b.equivFun.symm (Φ t)) := fun t ht =>
    h.prodExp_eq_expG_prodExpCoord b (hSN t ht)

  have hdet : ∀ t ∈ S, (fderiv ℝ Φ t).det ≠ 0 := by
    intro t ht
    have hΦt : HasFDerivAt Φ (fderiv ℝ Φ t) t := ((hΦat t ht).differentiableAt (by simp)).hasFDerivAt
    have hψt : HasFDerivAt ψ (fderiv ℝ ψ (Φ t)) (Φ t) :=
      ((hψat _ (hΦST ht)).differentiableAt (by simp)).hasFDerivAt
    have hcomp := hψt.comp t hΦt
    have hid : (ψ ∘ Φ) =ᶠ[𝓝 t] id := by
      filter_upwards [hSo.mem_nhds ht] with s hs
      exact hψΦ s hs
    have e : (fderiv ℝ ψ (Φ t)).comp (fderiv ℝ Φ t) = ContinuousLinearMap.id ℝ (Fin d → ℝ) := by
      rw [← hcomp.fderiv, hid.fderiv_eq, fderiv_id]
    intro h0
    have := congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L.det) e
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id] at this
    have h2 : LinearMap.det ((fderiv ℝ ψ (Φ t) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) ∘ₗ
        (fderiv ℝ Φ t : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))) = 1 := this
    rw [LinearMap.det_comp] at h2
    replace this := h2
    rw [show LinearMap.det (fderiv ℝ Φ t : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = 0 from h0,
      mul_zero] at this
    exact zero_ne_one this

  have hψc : ContinuousAt ψ 0 := (hψat 0 h0T).continuousAt
  obtain ⟨δ, hδ, hδT⟩ := Metric.isOpen_iff.1 hTo 0 h0T
  obtain ⟨η, hη, hηψ⟩ := Metric.continuousAt_iff.1 hψc ε₁ hε₁
  refine ⟨min (δ / 2) (η / 2), lt_min (by positivity) (by positivity), fun β hβ hβs => ?_⟩
  set ε := min (δ / 2) (η / 2) with hεdef
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεη : ε < η := lt_of_le_of_lt (min_le_right _ _) (by linarith)

  set e : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d) := fun w => WithLp.toLp 2 w with he
  set β' : (Fin d → ℝ) → ℂ := fun w => β (e w) with hβ'
  have he_cont : Continuous e := PiLp.continuous_toLp 2 _
  have hβ'c : ContDiff ℝ ∞ β' := hβ.comp PiLp.contDiff_toLp
  have hnorm : ∀ w : Fin d → ℝ, ‖w‖ ≤ ‖e w‖ := fun w =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
      simpa [e] using PiLp.norm_apply_le (e w) i
  have hβ's : tsupport β' ⊆ closedBall 0 ε := by
    refine closure_minimal (fun w hw => ?_) isClosed_closedBall
    have : e w ∈ closedBall 0 ε := hβs (subset_tsupport _ hw)
    rw [mem_closedBall_zero_iff] at this ⊢
    exact (hnorm w).trans this
  have hβ'T : tsupport β' ⊆ T := fun w hw => hδT (by
    have := hβ's hw
    rw [mem_closedBall_zero_iff] at this
    rw [mem_ball_zero_iff]; linarith)
  have hβ'comp : IsCompact (tsupport β') :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hβ's
  have hβ'e : ∀ w ∈ tsupport β', e w ∈ tsupport β := by
    intro w hw
    have : tsupport β' ⊆ e ⁻¹' tsupport β :=
      closure_minimal (fun v hv => subset_tsupport _ hv) ((isClosed_tsupport β).preimage he_cont)
    exact this hw

  set C' := ψ '' tsupport β' with hC'def
  have hC'c : IsCompact C' := hβ'comp.image_of_continuousOn (hψs.continuousOn.mono hβ'T)
  have hC'S : C' ⊆ S := by rintro _ ⟨w, hw, rfl⟩; exact hψTS (hβ'T hw)
  have hC'ε : C' ⊆ closedBall 0 ε₁ := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' := hβ's hw
    rw [mem_closedBall_zero_iff] at hw'
    have := hηψ (x := w) (by rw [dist_zero_right]; linarith)
    rw [hψ0, dist_zero_right] at this
    rw [mem_closedBall_zero_iff]; exact this.le
  let K : (Fin d → ℝ) → ℂ := fun t =>
    if t ∈ S then ((|(fderiv ℝ Φ t).det| : ℝ) : ℂ) * β' (Φ t) else 0
  have hKsupp : Function.support K ⊆ C' := by
    intro t ht
    by_cases htS : t ∈ S
    · have hβt : β' (Φ t) ≠ 0 := by
        intro h0; apply ht; simp [K, htS, h0]
      exact ⟨Φ t, subset_tsupport _ hβt, hψΦ t htS⟩
    · exact absurd (by simp [K, htS]) ht
  have hKts : tsupport K ⊆ C' := closure_minimal hKsupp hC'c.isClosed
  have hK : ContDiff ℝ ∞ K := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases htS : t ∈ S
    · have hev : K =ᶠ[𝓝 t] fun s => ((|(fderiv ℝ Φ s).det| : ℝ) : ℂ) * β' (Φ s) := by
        filter_upwards [hSo.mem_nhds htS] with s hs
        simp [K, hs]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have hfd : ContDiffAt ℝ ∞ (fderiv ℝ Φ) t := (hΦat t htS).fderiv_right (by simp)
      have hd : ContDiffAt ℝ ∞ (fun s => (fderiv ℝ Φ s).det) t :=
        contDiff_det_pi.contDiffAt.comp t hfd
      have ha : ContDiffAt ℝ ∞ (fun s => |(fderiv ℝ Φ s).det|) t := by
        have := (contDiffAt_abs (n := ⊤) (hdet t htS)).comp t hd
        exact this
      exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp t ha).mul
        (hβ'c.contDiffAt.comp t (hΦat t htS))
    · have hev : K =ᶠ[𝓝 t] fun _ => 0 := by
        have htC : t ∉ C' := fun hC => htS (hC'S hC)
        filter_upwards [hC'c.isClosed.isOpen_compl.mem_nhds htC] with s hs
        by_contra hne
        exact hs (hKsupp hne)
      exact contDiffAt_const.congr_of_eventuallyEq hev
  obtain ⟨κ, hκs, hκc, hκt, hκint⟩ := hdens K hK (hKts.trans hC'ε)
  refine ⟨κ, hκs, hκc, ?_, fun φ hφ => ?_⟩
  ·
    refine hκt.trans ?_
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hKts ht
    have hψw : ψ w ∈ S := hψTS (hβ'T hw)
    refine ⟨e w, hβ'e w hw, ?_⟩
    rw [hPΦ _ hψw, hΦψ w (hβ'T hw)]
    congr 1
  · rw [hκint φ hφ]
    set F : (Fin d → ℝ) → ℂ := fun w => β' w * φ (h.expG (b.equivFun.symm w)) with hF

    have h1 : ∫ x, β x * φ (h.expG (coordEquiv b x)) = ∫ w, F w := by
      have := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
        (g := F)
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [F, β', e, coordEquiv]
    rw [h1]

    set s := S ∩ Φ ⁻¹' T with hsdef
    have hs : IsOpen s := hΦs.continuousOn.isOpen_inter_preimage hSo hTo
    have hΦs_img : Φ '' s = T := by
      ext w; constructor
      · rintro ⟨t, ht, rfl⟩; exact ht.2
      · intro hw; exact ⟨ψ w, ⟨hψTS hw, by rw [mem_preimage, hΦψ w hw]; exact hw⟩, hΦψ w hw⟩
    have h2 : ∫ w, F w = ∫ w in T, F w := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_).symm
      have : β' w = 0 := image_eq_zero_of_notMem_tsupport fun h' => hw (hβ'T h')
      simp [F, this]
    have hderiv : ∀ t ∈ s, HasFDerivWithinAt Φ (fderiv ℝ Φ t) s t := fun t ht =>
      ((hΦat t ht.1).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
    have hinj : InjOn Φ s := fun t₁ ht₁ t₂ ht₂ he => by
      rw [← hψΦ t₁ ht₁.1, ← hψΦ t₂ ht₂.1, he]
    have h3 := integral_image_eq_integral_abs_det_fderiv_smul volume hs.measurableSet hderiv hinj F
    rw [hΦs_img] at h3
    rw [h2, h3]

    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := s)
      (f := fun t => K t * φ (P t)) fun t ht => by
        by_cases htS : t ∈ S
        · have hΦt : Φ t ∉ T := fun hT => ht ⟨htS, hT⟩
          have : β' (Φ t) = 0 := image_eq_zero_of_notMem_tsupport fun h' => hΦt (hβ'T h')
          simp [K, htS, this]
        · simp [K, htS]]
    refine setIntegral_congr_fun hs.measurableSet fun t ht => ?_
    simp only [K, if_pos ht.1, F, Complex.real_smul, hPΦ t ht.1]
    ring
end GroundTheory.Automorphic.IsExpLieAlgebra
