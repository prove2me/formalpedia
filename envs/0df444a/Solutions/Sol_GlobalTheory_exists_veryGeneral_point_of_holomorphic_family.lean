-- Prove2me | solution 1 for GlobalTheory.exists_veryGeneral_point_of_holomorphic_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:36.23047+00:00
-- url     : https://prove2.me/submissions/3471143f-088a-4bd2-b85b-1121f267b4fa

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsVeryGeneralPointOfHolomorphicFamily
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (o : Type) [CommRing o] [Countable o] (em : o →+* ℂ) (I : Type) [Countable I] (m : ℕ) (B : Set (Fin m → ℂ)) (θ : (Fin m → ℂ) → I → ℂ), IsOpen B → IsPreconnected B → B.Nonempty → (∀ a, DifferentiableOn ℂ (fun z => θ z a) B) → ∃ z ∈ B, ∃ c : ℂ, c ≠ 0 ∧ ∀ F : MvPolynomial I o, MvPolynomial.eval₂ em (c • θ z) F = 0 → ∀ z' ∈ B, ∀ c' : ℂ, c' ≠ 0 → MvPolynomial.eval₂ em (c' • θ z') F = 0 := by
  intro o _ _ em I _ m B θ hB hBc hBne hθ
  classical
  have : Countable (MvPolynomial I o) :=
    Function.Surjective.countable
      (f := (AddMonoidAlgebra.ofCoeff : ((I →₀ ℕ) →₀ o) → MvPolynomial I o))
      fun F => ⟨AddMonoidAlgebra.coeff F, rfl⟩

  set Ω : Set (Fin (m + 1) → ℂ) := {p | Fin.tail p ∈ B ∧ p 0 ∈ ({0}ᶜ : Set ℂ)} with hΩ
  have htail : Differentiable ℂ (fun p : Fin (m + 1) → ℂ => Fin.tail p) :=
    differentiable_pi.2 fun i => differentiable_apply _
  have hhead : Differentiable ℂ (fun p : Fin (m + 1) → ℂ => p 0) := differentiable_apply _
  have hΩo : IsOpen Ω :=
    (hB.preimage htail.continuous).inter (isOpen_compl_singleton.preimage hhead.continuous)
  have hΩimg : Ω = (fun q : (Fin m → ℂ) × ℂ => (Fin.cons q.2 q.1 : Fin (m + 1) → ℂ)) ''
      (B ×ˢ ({0}ᶜ : Set ℂ)) := by
    ext p
    constructor
    · intro hp
      exact ⟨(Fin.tail p, p 0), ⟨hp.1, hp.2⟩, Fin.cons_self_tail p⟩
    · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, rfl⟩
      exact ⟨by simpa using hz, by simpa using hc⟩
  have hΩc : IsPreconnected Ω := by
    rw [hΩimg]
    refine (hBc.prod (isConnected_compl_singleton_of_one_lt_rank ?_ 0).isPreconnected).image _ ?_
    · rw [Complex.rank_real_complex]; norm_num
    · exact (Continuous.finCons (A := fun _ => ℂ) continuous_snd continuous_fst).continuousOn
  have hΩne : Ω.Nonempty := by
    obtain ⟨z₀, hz₀⟩ := hBne
    exact ⟨Fin.cons 1 z₀, by simpa using hz₀, by simp⟩

  let f : MvPolynomial I o → (Fin (m + 1) → ℂ) → ℂ :=
    fun F p => MvPolynomial.eval₂ em (p 0 • θ (Fin.tail p)) F
  have hfd : ∀ F, DifferentiableOn ℂ (f F) Ω := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a =>
      simp only [f, MvPolynomial.eval₂_C]
      exact differentiableOn_const _
    | add F G hF hG =>
      simp only [f, MvPolynomial.eval₂_add]
      exact hF.add hG
    | mul_X F a hF =>
      have ha : DifferentiableOn ℂ (fun p : Fin (m + 1) → ℂ => θ (Fin.tail p) a) Ω :=
        (hθ a).comp htail.differentiableOn fun p hp => hp.1
      simp only [f, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.smul_apply, smul_eq_mul]
      exact hF.mul (hhead.differentiableOn.mul ha)
  have hfa : ∀ F, AnalyticOnNhd ℂ (f F) Ω := fun F =>
    ReciprocityTheory.AnForm.Osgood.osgood (m + 1) Ω (f F) hΩo (hfd F)

  let W : MvPolynomial I o → Set (Fin (m + 1) → ℂ) := fun F =>
    if Set.EqOn (f F) 0 Ω then Set.univ else (Ω ∩ f F ⁻¹' {0}ᶜ) ∪ (closure Ω)ᶜ
  have hWo : ∀ F, IsOpen (W F) := by
    intro F
    by_cases h : Set.EqOn (f F) 0 Ω
    · simp only [W, if_pos h]
      exact isOpen_univ
    · simp only [W, if_neg h]
      exact ((hfd F).continuousOn.isOpen_inter_preimage hΩo isOpen_compl_singleton).union
        isClosed_closure.isOpen_compl
  have hWd : ∀ F, Dense (W F) := by
    intro F
    by_cases h : Set.EqOn (f F) 0 Ω
    · simp only [W, if_pos h]
      exact dense_univ
    · simp only [W, if_neg h]
      have hsub : Ω ⊆ closure (Ω ∩ f F ⁻¹' {0}ᶜ) := by
        intro q hq
        by_contra hq'
        apply h
        refine (hfa F).eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩc hq ?_
        have hn : (closure (Ω ∩ f F ⁻¹' {0}ᶜ))ᶜ ∩ Ω ∈ nhds q :=
          Filter.inter_mem (isClosed_closure.isOpen_compl.mem_nhds hq') (hΩo.mem_nhds hq)
        filter_upwards [hn] with p hp
        by_contra hne
        exact hp.1 (subset_closure ⟨hp.2, hne⟩)
      intro x
      by_cases hx : x ∈ closure Ω
      · exact closure_mono Set.subset_union_left (closure_minimal hsub isClosed_closure hx)
      · exact subset_closure (Or.inr hx)

  obtain ⟨p, hpΩ, hpW⟩ := (dense_iInter_of_isOpen hWo hWd).inter_open_nonempty Ω hΩo hΩne
  refine ⟨Fin.tail p, hpΩ.1, p 0, hpΩ.2, fun F hF z' hz' c' hc' => ?_⟩
  by_cases h : Set.EqOn (f F) 0 Ω
  · have hmem : (Fin.cons c' z' : Fin (m + 1) → ℂ) ∈ Ω := ⟨by simpa using hz', by simpa using hc'⟩
    simpa [f] using h hmem
  · have hpW' := Set.mem_iInter.1 hpW F
    simp only [W, if_neg h] at hpW'
    rcases hpW' with hp' | hp'
    · exact absurd hF hp'.2
    · exact absurd (subset_closure hpΩ) hp'
end GlobalTheory
