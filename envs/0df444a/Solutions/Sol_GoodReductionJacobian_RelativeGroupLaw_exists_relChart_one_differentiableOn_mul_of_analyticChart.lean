-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_relChart_one_differentiableOn_mul_of_analyticChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/75a9a8dd-ff82-52cc-b469-9a028a443367

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_exists_relChart_differentiableOn_appLE_of_analyticChart
import Theorems.Thm_AlgebraicGeometry_differentiableOn_appLE_pullback_pair_of_relChart
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_differentiableOn_appLE_one_of_analyticChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relChart_one_differentiableOn_mul_of_analyticChart
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology
open Filter Set

namespace AGrp16

theorem appLE_congr_pt {X Y : Scheme.{0}} {p q : X ⟶ Y} (hpq : p = q) (U : Y.Opens)
    (hp : ⊤ ≤ p ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) (φ : Γ(Y, U)) :
    p.appLE U ⊤ hp φ = q.appLE U ⊤ hq φ := by
  subst hpq; rfl

theorem appLE_app {X Y Z : Scheme.{0}} (p : X ⟶ Y) (μ : Y ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ p ⁻¹ᵁ (μ ⁻¹ᵁ U)) (h' : ⊤ ≤ (p ≫ μ) ⁻¹ᵁ U) (φ : Γ(Z, U)) :
    p.appLE (μ ⁻¹ᵁ U) ⊤ h (μ.app U φ) = (p ≫ μ).appLE U ⊤ h' φ := by
  rw [Scheme.Hom.app_eq_appLE]
  rw [← Scheme.Hom.appLE_comp_appLE p μ U (μ ⁻¹ᵁ U) ⊤ le_rfl h]
  rfl

theorem exists_ball_prod {E : Type*} [PseudoMetricSpace E] {z : ℂ} {v w : E} {S : Set (ℂ × (E × E))}
    (hS : S ∈ 𝓝 (z, (v, w))) : ∃ δ > 0, Metric.ball z δ ×ˢ (Metric.ball v δ ×ˢ Metric.ball w δ) ⊆ S := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.1 hS
  refine ⟨δ, hδ, fun p hp => hsub ?_⟩
  rcases p with ⟨a, b, c⟩
  simp only [mem_prod, Metric.mem_ball] at hp
  rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq]
  exact max_lt hp.1 (max_lt hp.2.1 hp.2.2)

theorem preimage_comp' {X Y Z : Scheme.{0}} (p : X ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens) :
    (p ≫ q) ⁻¹ᵁ U = p ⁻¹ᵁ (q ⁻¹ᵁ U) := rfl

end AGrp16

open AGrp16 in
theorem solution

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of Sc)} (L : RelativeGroupLaw Sc f) {g : ℕ} (hsm : SmoothOfRelativeDimension g f)
    (σ₁ : Sc →ₐ[ℂ] ℂ) (hσ₁ : σ₁ ∈ 𝒰)
    (hdt₁ : ((RingHom.ker σ₁.toRingHom) • (⊤ : Submodule Sc (KaehlerDifferential ℂ Sc)) ⊔
        Submodule.span Sc {KaehlerDifferential.D ℂ Sc t} = ⊤)) :
    ∃ (ε ρ' : ℝ) (_ : 0 < ε) (_ : 0 < ρ') (_ : Metric.ball (σ₁ t) ε ⊆ Metric.ball (σ₀ t) r)
      (U₁ : G.Opens) (_ : IsAffineOpen U₁) (s₁ : Fin g → Γ(G, U₁)) (v₁ : Fin g → ℂ)
      (ψ₁ : (σ : Sc →ₐ[ℂ] ℂ) → (Fin g → ℂ) → SchemeHomOver (Spec.map (CommRingCat.ofHom σ.toRingHom)) f)
      (hU₁ : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₁ ρ', ⊤ ≤ (ψ₁ σ v).1 ⁻¹ᵁ U₁)
      (h1U₁ : ⊤ ≤ (L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1 ⁻¹ᵁ U₁),

      ψ₁ σ₁ v₁ = L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom)) ∧

      (∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (hz : σ t ∈ Metric.ball (σ₁ t) ε) (v : Fin g → ℂ) (hv : v ∈ Metric.ball v₁ ρ')
        (i : Fin g), (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ₁ σ v).1.appLE U₁ ⊤ (hU₁ σ hσ hz v hv)) (s₁ i)) = v i) ∧

      (∀ (V : G.Opens) (φ : Γ(G, V)),
        IsOpen {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2 ∈ Metric.ball v₁ ρ' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ₁ σ p.2).1 ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin g → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2 ∈ Metric.ball v₁ ρ' ∧
            ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ₁ σ p.2).1 ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₁ ρ', ∀ (hV : ⊤ ≤ (ψ₁ σ v).1 ⁻¹ᵁ V),
            F (σ t, v) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ₁ σ v).1.appLE V ⊤ hV) φ)) ∧

      (∃ (fs₁ : Finset (Γ(G, U₁))) (η₁ : ℝ), 0 < η₁ ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε →
          ∀ (P : SchemeHomOver (Spec.map (CommRingCat.ofHom σ.toRingHom)) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U₁),
            (∀ φ ∈ fs₁, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P).1.appLE U₁ ⊤ hP) φ) - (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1.appLE U₁ ⊤ h1U₁) φ)‖ < η₁) →
            ∃ v ∈ Metric.ball v₁ ρ', ψ₁ σ v = P) ∧

      (∃ o : ℂ → (Fin g → ℂ), DifferentiableOn ℂ o (Metric.ball (σ₁ t) ε) ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε →
          o (σ t) ∈ Metric.ball v₁ ρ' ∧ ψ₁ σ (o (σ t)) = L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))) ∧

      (∃ (ρ₂ : ℝ) (M : ℂ → (Fin g → ℂ) → (Fin g → ℂ) → (Fin g → ℂ)), 0 < ρ₂ ∧ ρ₂ ≤ ρ' ∧
        DifferentiableOn ℂ (fun p : ℂ × ((Fin g → ℂ) × (Fin g → ℂ)) => M p.1 p.2.1 p.2.2)
          (Metric.ball (σ₁ t) ε ×ˢ (Metric.ball v₁ ρ₂ ×ˢ Metric.ball v₁ ρ₂)) ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₁ ρ₂, ∀ w ∈ Metric.ball v₁ ρ₂,
          M (σ t) v w ∈ Metric.ball v₁ ρ' ∧
          ψ₁ σ (M (σ t) v w) = L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom)) (ψ₁ σ v) (ψ₁ σ w)) := by
  classical

  obtain ⟨ε₀, ρ₀, hε₀, hρ₀, hball₀, U, hUaff, s, v₀, ψ, hU, hP₀U, hOVER, hCENTRE, hCOORD, hAN, hSURJ⟩ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.exists_relChart_differentiableOn_appLE_of_analyticChart
      Sc hSc hΩ t σ₀ r 𝒰 hr hσ₀ hbij hhol f hsm σ₁ hσ₁ hdt₁ (L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom)))
  obtain ⟨fs, η, hη, hsurj⟩ := hSURJ
  have hz₁ : σ₁ t ∈ Metric.ball (σ₁ t) ε₀ := Metric.mem_ball_self hε₀
  have hv₀ : v₀ ∈ Metric.ball v₀ ρ₀ := Metric.mem_ball_self hρ₀

  have hinj : ∀ σ ∈ 𝒰, ∀ σ' ∈ 𝒰, σ' t = σ t → σ' = σ := fun σ hσ σ' hσ' h => hbij.injOn hσ' hσ h

  let ψ₁ : (σ : Sc →ₐ[ℂ] ℂ) → (Fin g → ℂ) → SchemeHomOver (Spec.map (CommRingCat.ofHom σ.toRingHom)) f :=
    fun σ v => if h : σ ∈ 𝒰 ∧ σ t ∈ Metric.ball (σ₁ t) ε₀ ∧ v ∈ Metric.ball v₀ ρ₀ then
      (⟨ψ σ v, hOVER σ h.1 h.2.1 v h.2.2⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom σ.toRingHom)) f)
      else L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))
  have hψ₁ : ∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (hz : σ t ∈ Metric.ball (σ₁ t) ε₀) (v : Fin g → ℂ)
      (hv : v ∈ Metric.ball v₀ ρ₀), (ψ₁ σ v).1 = ψ σ v := by
    intro σ hσ hz v hv
    have h : σ ∈ 𝒰 ∧ σ t ∈ Metric.ball (σ₁ t) ε₀ ∧ v ∈ Metric.ball v₀ ρ₀ := ⟨hσ, hz, hv⟩
    simp only [ψ₁, dif_pos h]

  let t₂ : pullback f f ⟶ Spec (CommRingCat.of Sc) := pullback.fst f f ≫ f
  let Pu : SchemeHomOver t₂ f := ⟨pullback.fst f f, rfl⟩
  let Qu : SchemeHomOver t₂ f := ⟨pullback.snd f f, pullback.condition.symm⟩
  let μ : pullback f f ⟶ G := (L.mul t₂ Pu Qu).1

  let pair : (Sc →ₐ[ℂ] ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ pullback f f) :=
    fun σ v w => if h : σ ∈ 𝒰 ∧ σ t ∈ Metric.ball (σ₁ t) ε₀ ∧ v ∈ Metric.ball v₀ ρ₀ ∧ w ∈ Metric.ball v₀ ρ₀ then
      pullback.lift (ψ σ v) (ψ σ w) (by rw [hOVER σ h.1 h.2.1 v h.2.2.1, hOVER σ h.1 h.2.1 w h.2.2.2])
      else pullback.lift ((L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1)
        ((L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1) rfl
  have hpair : ∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (hz : σ t ∈ Metric.ball (σ₁ t) ε₀) (v : Fin g → ℂ)
      (hv : v ∈ Metric.ball v₀ ρ₀) (w : Fin g → ℂ) (hw : w ∈ Metric.ball v₀ ρ₀),
      pair σ v w ≫ pullback.fst f f = ψ σ v ∧ pair σ v w ≫ pullback.snd f f = ψ σ w := by
    intro σ hσ hz v hv w hw
    have h : σ ∈ 𝒰 ∧ σ t ∈ Metric.ball (σ₁ t) ε₀ ∧ v ∈ Metric.ball v₀ ρ₀ ∧ w ∈ Metric.ball v₀ ρ₀ := ⟨hσ, hz, hv, hw⟩
    simp only [pair, dif_pos h, pullback.lift_fst, pullback.lift_snd, and_self]
  have hpair₁ : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε₀ → ∀ v ∈ Metric.ball v₀ ρ₀, ∀ w ∈ Metric.ball v₀ ρ₀,
      pair σ v w ≫ pullback.fst f f = ψ σ v := fun σ hσ hz v hv w hw => (hpair σ hσ hz v hv w hw).1
  have hpair₂ : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε₀ → ∀ v ∈ Metric.ball v₀ ρ₀, ∀ w ∈ Metric.ball v₀ ρ₀,
      pair σ v w ≫ pullback.snd f f = ψ σ w := fun σ hσ hz v hv w hw => (hpair σ hσ hz v hv w hw).2

  have hmul : ∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (hz : σ t ∈ Metric.ball (σ₁ t) ε₀) (v : Fin g → ℂ)
      (hv : v ∈ Metric.ball v₀ ρ₀) (w : Fin g → ℂ) (hw : w ∈ Metric.ball v₀ ρ₀),
      (L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom)) (ψ₁ σ v) (ψ₁ σ w)).1 = pair σ v w ≫ μ := by
    intro σ hσ hz v hv w hw
    have hφ : pair σ v w ≫ t₂ = Spec.map (CommRingCat.ofHom σ.toRingHom) := by
      show pair σ v w ≫ (pullback.fst f f ≫ f) = _
      rw [← Category.assoc, (hpair σ hσ hz v hv w hw).1, hOVER σ hσ hz v hv]
    have hP : GoodReductionJacobian.schemeHomOverComp (pair σ v w) hφ Pu = ψ₁ σ v :=
      Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, hψ₁ σ hσ hz v hv]; exact (hpair σ hσ hz v hv w hw).1)
    have hQ : GoodReductionJacobian.schemeHomOverComp (pair σ v w) hφ Qu = ψ₁ σ w :=
      Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, hψ₁ σ hσ hz w hw]; exact (hpair σ hσ hz v hv w hw).2)
    have hn := congrArg Subtype.val (L.mul_natural t₂ _ (pair σ v w) hφ Pu Qu)
    rw [GoodReductionJacobian.schemeHomOverComp_coe, hP, hQ] at hn
    exact hn.symm

  have hC : ψ σ₁ v₀ = (L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1 := hCENTRE
  have hC₁ : ψ₁ σ₁ v₀ = L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom)) :=
    Subtype.ext (by rw [hψ₁ σ₁ hσ₁ hz₁ v₀ hv₀, hC])
  have hCμ : pair σ₁ v₀ v₀ ≫ μ = (L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1 := by
    rw [← hmul σ₁ hσ₁ hz₁ v₀ hv₀ v₀ hv₀, hC₁, L.one_mul]

  have A3 := fun φ : Γ(G, U) =>
    GoodReductionJacobian.RelativeGroupLaw.exists_differentiableOn_appLE_one_of_analyticChart
      Sc hSc hΩ t σ₀ r 𝒰 hr hσ₀ hbij hhol L σ₁ hσ₁ U hP₀U φ
  choose εt Ft hεt hballt hFt hFt_spec using A3

  have A1 := fun (V' : (pullback f f).Opens) (φ' : Γ(pullback f f, V')) =>
    AlgebraicGeometry.differentiableOn_appLE_pullback_pair_of_relChart
      Sc hSc hΩ t σ₀ r 𝒰 hr hσ₀ hbij hhol f σ₁ hσ₁ ε₀ ρ₀ hε₀ hρ₀ hball₀ v₀ ψ hOVER hAN pair hpair₁ hpair₂ V' φ'

  set 𝓛 : Set (ℂ × ((Fin g → ℂ) × (Fin g → ℂ))) :=
    {p : ℂ × ((Fin g → ℂ) × (Fin g → ℂ)) | p.1 ∈ Metric.ball (σ₁ t) ε₀ ∧ p.2.1 ∈ Metric.ball v₀ ρ₀ ∧
        p.2.2 ∈ Metric.ball v₀ ρ₀ ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (pair σ p.2.1 p.2.2) ⁻¹ᵁ (μ ⁻¹ᵁ U)} with h𝓛
  have h𝓛o : IsOpen 𝓛 := (A1 (μ ⁻¹ᵁ U) 0).1
  have A1' := fun φ : Γ(G, U) => (A1 (μ ⁻¹ᵁ U) (μ.app U φ)).2
  choose Fm hFm hFm_spec using A1'

  have hc₀ : ((σ₁ t, (v₀, v₀)) : ℂ × ((Fin g → ℂ) × (Fin g → ℂ))) ∈ 𝓛 := by
    refine ⟨hz₁, hv₀, hv₀, σ₁, hσ₁, rfl, ?_⟩
    show ⊤ ≤ (pair σ₁ v₀ v₀) ⁻¹ᵁ (μ ⁻¹ᵁ U)
    rw [← preimage_comp', hCμ]; exact hP₀U

  have h𝓛mem : ∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (v w : Fin g → ℂ),
      ((σ t, (v, w)) : ℂ × ((Fin g → ℂ) × (Fin g → ℂ))) ∈ 𝓛 →
      σ t ∈ Metric.ball (σ₁ t) ε₀ ∧ v ∈ Metric.ball v₀ ρ₀ ∧ w ∈ Metric.ball v₀ ρ₀ ∧
        ⊤ ≤ (pair σ v w) ⁻¹ᵁ (μ ⁻¹ᵁ U) := by
    rintro σ hσ v w ⟨hz, hv, hw, σ', hσ', hσ't, hV⟩
    have : σ' = σ := hinj σ hσ σ' hσ' hσ't
    subst this
    exact ⟨hz, hv, hw, hV⟩

  have hval : ∀ (φ : Γ(G, U)) (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (hz : σ t ∈ Metric.ball (σ₁ t) ε₀) (v : Fin g → ℂ)
      (hv : v ∈ Metric.ball v₀ ρ₀) (w : Fin g → ℂ) (hw : w ∈ Metric.ball v₀ ρ₀)
      (hV : ⊤ ≤ (pair σ v w) ⁻¹ᵁ (μ ⁻¹ᵁ U))
      (hR : ⊤ ≤ (L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom)) (ψ₁ σ v) (ψ₁ σ w)).1 ⁻¹ᵁ U),
      Fm φ (σ t, (v, w)) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (((L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom)) (ψ₁ σ v) (ψ₁ σ w)).1.appLE U ⊤ hR) φ) := by
    intro φ σ hσ hz v hv w hw hV hR
    rw [hFm_spec φ σ hσ hz v hv w hw hV]
    have h' : ⊤ ≤ (pair σ v w ≫ μ) ⁻¹ᵁ U := by rw [preimage_comp']; exact hV
    rw [appLE_app (pair σ v w) μ U hV h' φ]
    congr 1
    exact appLE_congr_pt (hmul σ hσ hz v hv w hw).symm U h' hR φ

  have hRU : ∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (hz : σ t ∈ Metric.ball (σ₁ t) ε₀) (v : Fin g → ℂ)
      (hv : v ∈ Metric.ball v₀ ρ₀) (w : Fin g → ℂ) (hw : w ∈ Metric.ball v₀ ρ₀)
      (hV : ⊤ ≤ (pair σ v w) ⁻¹ᵁ (μ ⁻¹ᵁ U)),
      ⊤ ≤ (L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom)) (ψ₁ σ v) (ψ₁ σ w)).1 ⁻¹ᵁ U := by
    intro σ hσ hz v hv w hw hV
    rw [hmul σ hσ hz v hv w hw, preimage_comp']; exact hV

  have hcontM : ∀ φ : Γ(G, U), ∀ᶠ p in 𝓝 ((σ₁ t, (v₀, v₀)) : ℂ × ((Fin g → ℂ) × (Fin g → ℂ))),
      p ∈ 𝓛 ∧ ‖Fm φ p - Fm φ (σ₁ t, (v₀, v₀))‖ < η := by
    intro φ
    have h1 : ∀ᶠ p in 𝓝 ((σ₁ t, (v₀, v₀)) : ℂ × ((Fin g → ℂ) × (Fin g → ℂ))), p ∈ 𝓛 := h𝓛o.mem_nhds hc₀
    have hc : ContinuousAt (Fm φ) (σ₁ t, (v₀, v₀)) :=
      ((hFm φ).continuousOn.continuousWithinAt hc₀).continuousAt (h𝓛o.mem_nhds hc₀)
    have h2 : ∀ᶠ p in 𝓝 ((σ₁ t, (v₀, v₀)) : ℂ × ((Fin g → ℂ) × (Fin g → ℂ))),
        ‖Fm φ p - Fm φ (σ₁ t, (v₀, v₀))‖ < η := by
      have := (hc.sub (continuousAt_const (y := Fm φ (σ₁ t, (v₀, v₀))))).norm
      have h0 : ‖Fm φ (σ₁ t, (v₀, v₀)) - Fm φ (σ₁ t, (v₀, v₀))‖ < η := by simp [hη]
      exact this.eventually (Iio_mem_nhds h0) |>.mono fun p hp => hp
    exact h1.and h2
  have hMall : ∀ᶠ p in 𝓝 ((σ₁ t, (v₀, v₀)) : ℂ × ((Fin g → ℂ) × (Fin g → ℂ))),
      p ∈ 𝓛 ∧ ∀ φ ∈ fs, ‖Fm φ p - Fm φ (σ₁ t, (v₀, v₀))‖ < η := by
    refine Filter.Eventually.and (h𝓛o.mem_nhds hc₀) ?_
    exact (fs.eventually_all).2 fun φ _ => (hcontM φ).mono fun p hp => hp.2
  obtain ⟨δ, hδ, hδsub⟩ := exists_ball_prod hMall

  have hcontO : ∀ φ : Γ(G, U), ∀ᶠ z in 𝓝 (σ₁ t),
      z ∈ Metric.ball (σ₁ t) (εt φ) ∧ ‖Ft φ z - Ft φ (σ₁ t)‖ < η := by
    intro φ
    have h1 : ∀ᶠ z in 𝓝 (σ₁ t), z ∈ Metric.ball (σ₁ t) (εt φ) := Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hεt φ))
    have hc : ContinuousAt (Ft φ) (σ₁ t) :=
      ((hFt φ).continuousOn.continuousWithinAt (Metric.mem_ball_self (hεt φ))).continuousAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hεt φ)))
    have h2 : ∀ᶠ z in 𝓝 (σ₁ t), ‖Ft φ z - Ft φ (σ₁ t)‖ < η := by
      have := (hc.sub (continuousAt_const (y := Ft φ (σ₁ t)))).norm
      have h0 : ‖Ft φ (σ₁ t) - Ft φ (σ₁ t)‖ < η := by simp [hη]
      exact this.eventually (Iio_mem_nhds h0) |>.mono fun p hp => hp
    exact h1.and h2
  have hOall : ∀ᶠ z in 𝓝 (σ₁ t), z ∈ Metric.ball (σ₁ t) ε₀ ∧ z ∈ Metric.ball (σ₁ t) δ ∧
      (∀ i : Fin g, z ∈ Metric.ball (σ₁ t) (εt (s i))) ∧ z ∈ Metric.ball (σ₁ t) (εt 0) ∧
      ∀ φ ∈ fs, z ∈ Metric.ball (σ₁ t) (εt φ) ∧ ‖Ft φ z - Ft φ (σ₁ t)‖ < η := by
    refine Filter.Eventually.and (Metric.isOpen_ball.mem_nhds hz₁)
      (Filter.Eventually.and (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
        (Filter.Eventually.and (eventually_all.2 fun i => (hcontO (s i)).mono fun z hz => hz.1)
          (Filter.Eventually.and ((hcontO 0).mono fun z hz => hz.1) ((fs.eventually_all).2 fun φ _ => hcontO φ))))
  obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff_ball.1 hOall

  set ρ₂ : ℝ := min δ ρ₀ with hρ₂
  have hρ₂pos : 0 < ρ₂ := lt_min hδ hρ₀
  have hρ₂δ : ρ₂ ≤ δ := min_le_left _ _
  have hρ₂ρ : ρ₂ ≤ ρ₀ := min_le_right _ _
  have hεε₀ : Metric.ball (σ₁ t) ε ⊆ Metric.ball (σ₁ t) ε₀ := fun z hz => (hεsub z hz).1
  have hεδ : Metric.ball (σ₁ t) ε ⊆ Metric.ball (σ₁ t) δ := fun z hz => (hεsub z hz).2.1

  refine ⟨ε, ρ₀, hε, hρ₀, hεε₀.trans hball₀, U, hUaff, s, v₀, ψ₁,
    fun σ hσ hz v hv => by rw [hψ₁ σ hσ (hεε₀ hz) v hv]; exact hU σ hσ (hεε₀ hz) v hv,
    hP₀U, hC₁, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro σ hσ hz v hv i
    have := hCOORD σ hσ (hεε₀ hz) v hv i
    rw [← this]
    congr 1
    exact appLE_congr_pt (hψ₁ σ hσ (hεε₀ hz) v hv) U _ _ (s i)
  ·
    intro V φ
    obtain ⟨hVo, F, hF, hFval⟩ := hAN V φ
    have hset : {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2 ∈ Metric.ball v₀ ρ₀ ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ₁ σ p.2).1 ⁻¹ᵁ V} =
        {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε₀ ∧ p.2 ∈ Metric.ball v₀ ρ₀ ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ σ p.2) ⁻¹ᵁ V} ∩ {p | p.1 ∈ Metric.ball (σ₁ t) ε} := by
      ext p
      simp only [mem_setOf_eq, mem_inter_iff]
      constructor
      · rintro ⟨h1, h2, σ, hσ, hσt, hV⟩
        refine ⟨⟨hεε₀ h1, h2, σ, hσ, hσt, ?_⟩, h1⟩
        rwa [hψ₁ σ hσ (hσt ▸ hεε₀ h1) p.2 h2] at hV
      · rintro ⟨⟨-, h2, σ, hσ, hσt, hV⟩, h1⟩
        refine ⟨h1, h2, σ, hσ, hσt, ?_⟩
        rwa [hψ₁ σ hσ (hσt ▸ hεε₀ h1) p.2 h2]
    rw [hset]
    refine ⟨hVo.inter (Metric.isOpen_ball.preimage continuous_fst), F, hF.mono inter_subset_left, ?_⟩
    intro σ hσ hz v hv hV
    have hV' : ⊤ ≤ (ψ σ v) ⁻¹ᵁ V := by rwa [hψ₁ σ hσ (hεε₀ hz) v hv] at hV
    rw [hFval σ hσ (hεε₀ hz) v hv hV']
    congr 1
    exact appLE_congr_pt (hψ₁ σ hσ (hεε₀ hz) v hv).symm V hV' hV φ
  ·
    refine ⟨fs, η, hη, fun σ hσ hz P hP hclose => ?_⟩
    obtain ⟨v, hv, hvP⟩ := hsurj σ hσ (hεε₀ hz) P hP hclose
    exact ⟨v, hv, Subtype.ext (by rw [hψ₁ σ hσ (hεε₀ hz) v hv]; exact hvP)⟩
  ·
    refine ⟨fun z => fun i => Ft (s i) z, ?_, ?_⟩
    · refine differentiableOn_pi.2 fun i => (hFt (s i)).mono fun z hz => (hεsub z hz).2.2.1 i
    · intro σ hσ hz

      obtain ⟨h1U, -⟩ := hFt_spec 0 σ hσ (hεsub _ hz).2.2.2.1
      have hclose : ∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
            (((L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))).1.appLE U ⊤ h1U) φ) -
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
            (((L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1.appLE U ⊤ hP₀U) φ)‖ < η := by
        intro φ hφ
        obtain ⟨hmemφ, hlt⟩ := (hεsub _ hz).2.2.2.2 φ hφ
        obtain ⟨hσU, hFσ⟩ := hFt_spec φ σ hσ hmemφ
        obtain ⟨hσ₁U, hFσ₁⟩ := hFt_spec φ σ₁ hσ₁ (Metric.mem_ball_self (hεt φ))
        rw [appLE_congr_pt rfl U h1U hσU φ, ← hFσ, appLE_congr_pt rfl U hP₀U hσ₁U φ, ← hFσ₁]
        exact hlt
      obtain ⟨v, hv, hvP⟩ := hsurj σ hσ (hεε₀ hz) (L.one _) h1U hclose

      have hvo : v = fun i => Ft (s i) (σ t) := by
        funext i
        obtain ⟨hiU, hFi⟩ := hFt_spec (s i) σ hσ ((hεsub _ hz).2.2.1 i)
        rw [hFi, ← hCOORD σ hσ (hεε₀ hz) v hv i]
        congr 1
        exact appLE_congr_pt hvP U _ hiU (s i)
      have hmemo : (fun i => Ft (s i) (σ t)) ∈ Metric.ball v₀ ρ₀ := hvo ▸ hv
      refine ⟨by beta_reduce; exact hmemo, Subtype.ext ?_⟩
      beta_reduce
      rw [hψ₁ σ hσ (hεε₀ hz) _ hmemo, ← hvo]; exact hvP
  ·
    refine ⟨ρ₂, fun z v w => fun i => Fm (s i) (z, (v, w)), hρ₂pos, hρ₂ρ, ?_, ?_⟩
    · have hsub : Metric.ball (σ₁ t) ε ×ˢ (Metric.ball v₀ ρ₂ ×ˢ Metric.ball v₀ ρ₂) ⊆ 𝓛 := by
        refine fun p hp => (hδsub ?_).1
        exact ⟨hεδ hp.1, Metric.ball_subset_ball hρ₂δ hp.2.1, Metric.ball_subset_ball hρ₂δ hp.2.2⟩
      have : (fun p : ℂ × ((Fin g → ℂ) × (Fin g → ℂ)) => fun i => Fm (s i) (p.1, (p.2.1, p.2.2))) =
          fun p => fun i => Fm (s i) p := by
        funext p; rfl
      rw [this]
      exact differentiableOn_pi.2 fun i => (hFm (s i)).mono hsub
    · intro σ hσ hz v hv w hw
      have hp : ((σ t, (v, w)) : ℂ × ((Fin g → ℂ) × (Fin g → ℂ))) ∈
          Metric.ball (σ₁ t) δ ×ˢ (Metric.ball v₀ δ ×ˢ Metric.ball v₀ δ) :=
        ⟨hεδ hz, Metric.ball_subset_ball hρ₂δ hv, Metric.ball_subset_ball hρ₂δ hw⟩
      obtain ⟨hp𝓛, hpclose⟩ := hδsub hp
      obtain ⟨hz₀, hv', hw', hV⟩ := h𝓛mem σ hσ v w hp𝓛
      have hR := hRU σ hσ hz₀ v hv' w hw' hV

      have hclose : ∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
            (((L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom)) (ψ₁ σ v) (ψ₁ σ w)).1.appLE U ⊤ hR) φ) -
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
            (((L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1.appLE U ⊤ hP₀U) φ)‖ < η := by
        intro φ hφ
        have h1 := hval φ σ hσ hz₀ v hv' w hw' hV hR
        obtain ⟨-, -, -, hV₁⟩ := h𝓛mem σ₁ hσ₁ v₀ v₀ hc₀
        have hR₁ := hRU σ₁ hσ₁ hz₁ v₀ hv₀ v₀ hv₀ hV₁
        have h2 := hval φ σ₁ hσ₁ hz₁ v₀ hv₀ v₀ hv₀ hV₁ hR₁
        have h3 : (L.mul (Spec.map (CommRingCat.ofHom σ₁.toRingHom)) (ψ₁ σ₁ v₀) (ψ₁ σ₁ v₀)).1 =
            (L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1 := by rw [hC₁, L.one_mul]
        rw [← h1, appLE_congr_pt h3.symm U hP₀U hR₁ φ, ← h2]
        exact hpclose φ hφ
      obtain ⟨v', hv'mem, hv'P⟩ := hsurj σ hσ hz₀ _ hR hclose
      have hvM : v' = fun i => Fm (s i) (σ t, (v, w)) := by
        funext i
        rw [hval (s i) σ hσ hz₀ v hv' w hw' hV hR, ← hCOORD σ hσ hz₀ v' hv'mem i]
        congr 1
        exact appLE_congr_pt hv'P U _ hR (s i)
      have hmemM : (fun i => Fm (s i) (σ t, (v, w))) ∈ Metric.ball v₀ ρ₀ := hvM ▸ hv'mem
      refine ⟨by beta_reduce; exact hmemM, Subtype.ext ?_⟩
      beta_reduce
      rw [hψ₁ σ hσ hz₀ _ hmemM, ← hvM]; exact hv'P

end S_GoodReductionJacobian_RelativeGroupLaw_exists_relChart_one_differentiableOn_mul_of_analyticChart
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relChart_one_differentiableOn_mul_of_analyticChart (solution)
