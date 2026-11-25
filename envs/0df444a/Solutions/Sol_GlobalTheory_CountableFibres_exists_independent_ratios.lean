-- Prove2me | solution 1 for GlobalTheory.CountableFibres.exists_independent_ratios
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:37:09.498424+00:00
-- url     : https://prove2.me/submissions/d65a3904-a37f-40bb-9842-0b70354ef23a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialEqZeroOfEventually
import Theorems.Thm_GlobalTheory_CountableFibres_exists_injective_fderiv
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CountableFibres
open Filter Topology
namespace GlobalTheory.CountableFibres
namespace _root_.GlobalTheory.CountableFibres
theorem _root_.solution :
    ∀ (d : ℕ) (I : Type) [Finite I] (B : Set (Fin d → ℂ)) (θ : (Fin d → ℂ) → I → ℂ), IsOpen B →
      IsPreconnected B → B.Nonempty → (∀ a, DifferentiableOn ℂ (fun z => θ z a) B) →
      (∀ z ∈ B, θ z ≠ 0 ∧ {z' ∈ B | ∃ c : ℂ, θ z' = c • θ z}.Countable) →
      ∃ (a₀ : I) (a : Fin d → I), (∃ z ∈ B, θ z a₀ ≠ 0) ∧ ∀ F : MvPolynomial (Fin d) ℂ,
        (∀ z ∈ B, θ z a₀ ≠ 0 → MvPolynomial.eval (fun i => θ z (a i) / θ z a₀) F = 0) → F = 0 := by
  intro d I _ B θ hB _ hBne hdiff hfib
  haveI := Fintype.ofFinite I
  have hO : _root_.ReciprocityTheory.AnForm.Osgood.OsgoodStatement := _root_.ReciprocityTheory.AnForm.Osgood.osgood
  unfold _root_.ReciprocityTheory.AnForm.Osgood.OsgoodStatement at hO
  have hAn : ∀ a, AnalyticOnNhd ℂ (fun z => θ z a) B := fun a => hO d B _ hB (hdiff a)
  obtain ⟨z₁, hz₁⟩ := hBne
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, θ z₁ a₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact (hfib z₁ hz₁).1 (funext h)
  set U := B ∩ (fun z => θ z a₀) ⁻¹' {0}ᶜ
  have hUo : IsOpen U := (hAn a₀).continuousOn.isOpen_inter_preimage hB isOpen_compl_singleton
  have hUB : ∀ z ∈ U, z ∈ B ∧ θ z a₀ ≠ 0 := fun z hz => hz
  set ρ : (Fin d → ℂ) → I → ℂ := fun z b => θ z b / θ z a₀
  have hρ : ∀ z ∈ U, ContDiffAt ℂ 1 ρ z := fun z hz =>
    contDiffAt_pi.2 fun b => ((hAn b z hz.1).contDiffAt).div ((hAn a₀ z hz.1).contDiffAt) hz.2
  have hρc : ∀ z ∈ U, {z' ∈ U | ρ z' = ρ z}.Countable := by
    intro z hz
    refine (hfib z hz.1).2.mono ?_
    rintro z' ⟨hz'U, hz'⟩
    refine ⟨hz'U.1, θ z' a₀ / θ z a₀, funext fun b => ?_⟩
    have h := congrFun hz' b
    simp only [ρ] at h
    have h1 := hz.2
    have h2 := hz'U.2
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at h1 h2
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp at h ⊢
    linear_combination h
  obtain ⟨z₂, hz₂, hinj⟩ := _root_.GlobalTheory.CountableFibres.exists_injective_fderiv hUo ⟨z₁, hz₁, ha₀⟩ hρ hρc
  set D := fderiv ℂ ρ z₂

  set v : I → Module.Dual ℂ (Fin d → ℂ) := fun b => (LinearMap.proj b).comp (D : (Fin d → ℂ) →ₗ[ℂ] I → ℂ)
  obtain ⟨κ, c, hc, hspan, hli⟩ := exists_linearIndependent' ℂ v
  haveI : Finite κ := Finite.of_injective c hc
  haveI := Fintype.ofFinite κ
  have hkill : ∀ y, (∀ k, v (c k) y = 0) → y = 0 := by
    intro y hy
    have hle : Submodule.span ℂ (Set.range (v ∘ c)) ≤ LinearMap.ker (Module.Dual.eval ℂ _ y) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hy k
    rw [hspan] at hle
    apply hinj
    rw [map_zero]
    funext b
    exact hle (Submodule.subset_span ⟨b, rfl⟩)
  have hcard : Fintype.card κ = d := by
    apply le_antisymm
    · have := hli.fintype_card_le_finrank
      rwa [Subspace.dual_finrank_eq, Module.finrank_fin_fun] at this
    · let T : (Fin d → ℂ) →ₗ[ℂ] κ → ℂ := LinearMap.pi fun k => v (c k)
      have hT : Function.Injective T := by
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro y hy
        exact hkill y fun k => congrFun hy k
      have := LinearMap.finrank_le_finrank_of_injective hT
      rwa [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at this
  set e := Fintype.equivFinOfCardEq hcard
  set a : Fin d → I := fun i => c (e.symm i)
  refine ⟨a₀, a, ⟨z₁, hz₁, ha₀⟩, fun F hF => ?_⟩
  set π : (I → ℂ) →L[ℂ] Fin d → ℂ := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (a i)
  have hG : HasStrictFDerivAt (fun z => π (ρ z)) (π.comp D) z₂ :=
    π.hasStrictFDerivAt.comp z₂ ((hρ z₂ hz₂).hasStrictFDerivAt one_ne_zero)
  have hsurj : LinearMap.range ((π.comp D : (Fin d → ℂ) →L[ℂ] Fin d → ℂ) :
      (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = ⊤ := by
    rw [LinearMap.range_eq_top, ← LinearMap.injective_iff_surjective, ← LinearMap.ker_eq_bot,
      Submodule.eq_bot_iff]
    intro y hy
    apply hkill y
    intro k
    have := congrFun hy (e k)
    simpa [π, a, v] using this
  have hN : (fun z => π (ρ z)) '' U ∈ 𝓝 (π (ρ z₂)) := by
    rw [← hG.map_nhds_eq_of_surj hsurj]
    exact Filter.image_mem_map (hUo.mem_nhds hz₂)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  have hinf : ∀ i, (Metric.ball (π (ρ z₂) i) ε).Infinite := fun i hfin => by
    obtain ⟨x, hx, hxc⟩ := (hfin.countable.dense_compl ℝ).inter_open_nonempty _ Metric.isOpen_ball
      ⟨_, Metric.mem_ball_self hε⟩
    exact hxc hx
  choose S hS hScard using fun i => (hinf i).exists_subset_card_eq (MvPolynomial.degreeOf i F + 1)
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset F S (fun i => by rw [hScard i]; omega) fun x hx => ?_
  have hxb : x ∈ Metric.ball (π (ρ z₂)) ε := by
    rw [ball_pi _ hε]
    exact fun i _ => hS i (hx i)
  obtain ⟨z, hzU, rfl⟩ := hball hxb
  exact hF z hzU.1 hzU.2
end _root_.GlobalTheory.CountableFibres
end GlobalTheory.CountableFibres
