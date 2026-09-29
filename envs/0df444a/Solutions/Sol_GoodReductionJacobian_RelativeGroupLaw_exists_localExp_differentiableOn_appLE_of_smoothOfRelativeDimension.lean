-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/26ceb16f-ac5e-5cc0-a254-c3e235db9066

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_chart_differentiableOn_mul_of_smoothOfRelativeDimension
import Theorems.Thm_LocalGroupLaw_exists_localExp_of_differentiableOn_of_comm_of_assoc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

namespace LocalExpGlue

theorem val_congr {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)}
    {P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f} (h : P = Q) (U : G.Opens)
    (hP : ⊤ ≤ P.1 ⁻¹ᵁ U) (hQ : ⊤ ≤ Q.1 ⁻¹ᵁ U) (s : Γ(G, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) s) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U ⊤ hQ) s) := by
  subst h; rfl

end LocalExpGlue

open LocalExpGlue in
theorem solution
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f) (hc : L.IsCommutative)
    {g : ℕ} (hsm : SmoothOfRelativeDimension g f) :
    ∃ (r : ℝ) (_ : 0 < r) (exp₀ : (Fin g → ℂ) → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)
      (U : G.Opens) (_ : IsAffineOpen U) (t : Fin g → Γ(G, U))
      (hU : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ U),

      exp₀ 0 = L.one (𝟙 (Spec (CommRingCat.of ℂ))) ∧

      (∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r → w ∈ Metric.ball (0 : Fin g → ℂ) r →
        v + w ∈ Metric.ball (0 : Fin g → ℂ) r →
        exp₀ (v + w) = L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (exp₀ v) (exp₀ w)) ∧

      Set.InjOn exp₀ (Metric.ball (0 : Fin g → ℂ) r) ∧

      (∀ (V : G.Opens) (φ : Γ(G, V)),
        IsOpen {v : Fin g → ℂ | v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ V} ∧
        ∃ F : (Fin g → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin g → ℂ | v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ V} ∧
          ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ V), v ∈ Metric.ball (0 : Fin g → ℂ) r →
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((exp₀ v).1.appLE V ⊤ h) φ)) ∧

      (∃ (D : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (F : (Fin g → ℂ) → (Fin g → ℂ)),
          (∀ (v : Fin g → ℂ) (hv : v ∈ Metric.ball (0 : Fin g → ℂ) r),
            F v = fun i : Fin g =>
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((exp₀ v).1.appLE U ⊤ (hU v hv)) (t i))) ∧
          HasFDerivAt F (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) 0) ∧

      (∃ (fs : Finset (Γ(G, U))) (ε : ℝ) (h1 : ⊤ ≤ (L.one (𝟙 (Spec (CommRingCat.of ℂ)))).1 ⁻¹ᵁ U), 0 < ε ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
            (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) φ) -
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                  (((L.one (𝟙 (Spec (CommRingCat.of ℂ)))).1.appLE U ⊤ h1) φ)‖ < ε) →
            ∃ v ∈ Metric.ball (0 : Fin g → ℂ) r, exp₀ v = P) := by
  classical
  obtain ⟨r, hr, ψ, U, hUaff, t, hU, hE, hINJ, hCOORD, hAN, hSURJ, hMUL⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_chart_differentiableOn_mul_of_smoothOfRelativeDimension L hsm
  obtain ⟨r₁, M, hr₁, hr₁r, hMdiff, hM⟩ := hMUL
  have sub1 : Metric.ball (0 : Fin g → ℂ) r₁ ⊆ Metric.ball (0 : Fin g → ℂ) r := Metric.ball_subset_ball hr₁r
  have h0r₁ : (0 : Fin g → ℂ) ∈ Metric.ball (0 : Fin g → ℂ) r₁ := Metric.mem_ball_self hr₁

  have hzero_left : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r₁, M 0 v = v := by
    intro v hv
    have h := hM 0 v h0r₁ hv
    exact hINJ h.1 (sub1 hv) (by rw [h.2, hE, L.one_mul])
  have hzero_right : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r₁, M v 0 = v := by
    intro v hv
    have h := hM v 0 hv h0r₁
    exact hINJ h.1 (sub1 hv) (by rw [h.2, hE, L.mul_one])
  have hcommM : ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r₁ →
      w ∈ Metric.ball (0 : Fin g → ℂ) r₁ → M v w = M w v := by
    intro v w hv hw
    exact hINJ (hM v w hv hw).1 (hM w v hw hv).1 (by rw [(hM v w hv hw).2, (hM w v hw hv).2]; exact hc _ _ _)
  have hassocM : ∀ u v w : Fin g → ℂ, u ∈ Metric.ball (0 : Fin g → ℂ) r₁ →
      v ∈ Metric.ball (0 : Fin g → ℂ) r₁ → w ∈ Metric.ball (0 : Fin g → ℂ) r₁ →
      M u v ∈ Metric.ball (0 : Fin g → ℂ) r₁ → M v w ∈ Metric.ball (0 : Fin g → ℂ) r₁ →
      M (M u v) w = M u (M v w) := by
    intro u v w hu hv hw huv hvw
    exact hINJ (hM _ _ huv hw).1 (hM _ _ hu hvw).1 (by
      rw [(hM _ _ huv hw).2, (hM _ _ hu hvw).2, (hM u v hu hv).2, (hM v w hv hw).2, L.mul_assoc])
  obtain ⟨rb, hrb, e, he0, hediff, heD, heinj, hemaps, hehom, δ, hδ, hesurj⟩ :=
    LocalGroupLaw.exists_localExp_of_differentiableOn_of_comm_of_assoc hr₁ M hMdiff hzero_left hzero_right
      hcommM hassocM
  have heball : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) rb, e v ∈ Metric.ball (0 : Fin g → ℂ) r :=
    fun v hv => sub1 (hemaps hv)
  have hU' : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) rb, ⊤ ≤ (ψ (e v)).1 ⁻¹ᵁ U :=
    fun v hv => hU (e v) (heball v hv)
  refine ⟨rb, hrb, fun v => ψ (e v), U, hUaff, t, hU', ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    show ψ (e 0) = _
    rw [he0, hE]
  ·
    intro v w hv hw hvw
    show ψ (e (v + w)) = L.mul _ (ψ (e v)) (ψ (e w))
    rw [hehom v w hv hw hvw, (hM _ _ (hemaps hv) (hemaps hw)).2]
  ·
    exact hINJ.comp heinj (fun v hv => heball v hv)
  ·
    intro V φ
    obtain ⟨hopen, F₀, hF₀, hval⟩ := hAN V φ
    have hset : {v : Fin g → ℂ | v ∈ Metric.ball (0 : Fin g → ℂ) rb ∧ ⊤ ≤ (ψ (e v)).1 ⁻¹ᵁ V} =
        Metric.ball (0 : Fin g → ℂ) rb ∩
          e ⁻¹' {u : Fin g → ℂ | u ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ⊤ ≤ (ψ u).1 ⁻¹ᵁ V} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hv, h⟩; exact ⟨hv, heball v hv, h⟩
      · rintro ⟨hv, -, h⟩; exact ⟨hv, h⟩
    refine ⟨?_, fun v => F₀ (e v), ?_, ?_⟩
    · rw [hset]
      exact hediff.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hopen
    · rw [hset]
      refine hF₀.comp (hediff.mono Set.inter_subset_left) ?_
      intro v hv; exact hv.2
    · intro v h hv
      exact (hval (e v) h (heball v hv)).symm ▸ rfl
  ·
    refine ⟨ContinuousLinearEquiv.refl ℂ (Fin g → ℂ), e, ?_, ?_⟩
    · intro v hv
      funext i
      exact (hCOORD (e v) (heball v hv) i).symm
    · simpa using heD
  ·
    obtain ⟨fs₀, ε₀, h1, hε₀, hS⟩ := hSURJ
    refine ⟨fs₀ ∪ Finset.univ.image t, min ε₀ δ, h1, lt_min hε₀ hδ, ?_⟩
    intro P hP hclose
    obtain ⟨u, hu, hψu⟩ := hS P hP (fun φ hφ => (lt_min_iff.mp (hclose φ (Finset.mem_union_left _ hφ))).1)

    have hut : ∀ i : Fin g, ‖u i‖ < δ := by
      intro i
      have hti : t i ∈ fs₀ ∪ Finset.univ.image t :=
        Finset.mem_union_right _ (Finset.mem_image_of_mem t (Finset.mem_univ i))
      have hlt := (lt_min_iff.mp (hclose (t i) hti)).2
      have h0 : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          (((L.one (𝟙 (Spec (CommRingCat.of ℂ)))).1.appLE U ⊤ h1) (t i)) = 0 := by
        rw [← val_congr hE U (hU 0 (Metric.mem_ball_self hr)) h1 (t i), hCOORD 0 (Metric.mem_ball_self hr) i]
        rfl
      have hPu : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) (t i)) = u i := by
        rw [← val_congr hψu U (hU u hu) hP (t i), hCOORD u hu i]
      rw [h0, hPu, sub_zero] at hlt
      exact hlt
    have huδ : u ∈ Metric.ball (0 : Fin g → ℂ) δ := by
      rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hδ]
      exact hut
    obtain ⟨v, hv, hev⟩ := hesurj u huδ
    exact ⟨v, hv, by show ψ (e v) = P; rw [hev, hψu]⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension (solution)
