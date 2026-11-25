-- Prove2me | solution 1 for GlobalTheory.JR.RankOneTransfer.rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:20:54.02815+00:00
-- url     : https://prove2.me/submissions/5eecb3c9-6629-41c8-a6fa-1e4d0c28041f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KirillovVanishingOfLimitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypMemInducedFourierWeylStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerJHypEqOrbitalIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepEvalZeroMemInducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerWeilRepEventuallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierTransformKProdLocallyConstantCompactSuppoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleOrbitalFourierRankOneTransfer
import Theorems.Thm_GlobalTheory_JR_RankOneTransfer_inI_comb
import Theorems.Thm_GlobalTheory_JR_RankOneTransfer_lam_comb
import Theorems.Thm_GlobalTheory_JR_RankOneTransfer_inI_sum
import Theorems.Thm_GlobalTheory_JR_RankOneTransfer_lam_sum
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts
import Theorems.Thm_GlobalTheory_T_fourierTransformKProd_locallyConstantCompactSupport
import Theorems.Thm_GlobalTheory_T_jHyp_mem_induced_fourier_weyl
import Theorems.Thm_GlobalTheory_T_kirillov_vanishing_of_limit
import Theorems.Thm_GlobalTheory_T_truncatedWhittaker_jHyp_eq_orbitalIntegral
import Theorems.Thm_GlobalTheory_T_truncatedWhittaker_weilRep_eventually
import Theorems.Thm_GlobalTheory_T_weilRep_evalZero_mem_induced


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.RankOneTransfer
namespace GlobalTheory.JR.RankOneTransfer
theorem _root_.solution : RankOne := by
  intro F E _ _ _ _ _ A ψ hψ m S hS γ W hW φ' φ κ hφ' hφ hmatch x hx y hy
  classical
  obtain ⟨-, -, -, -, -, -, -, hfin, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hSf := hfin S hS
  set Sf := hSf.toFinset with hSfdef
  have hmem : ∀ x', x' ∈ Sf ↔ x' ∈ S := fun x' => hSf.mem_toFinset
  have hμ : m.μK.IsAddHaarMeasure := m.sdK.1

  have huniq : ∀ (x₀ x₁ : A.Kˣ) (y₀ y₁ : A.L), x₀ ∈ S → x₁ ∈ S → IsUnit y₀ → IsUnit y₁ →
      (x₀ : A.K) * A.NL y₀ = x₁ * A.NL y₁ → x₀ = x₁ := by
    intro x₀ x₁ y₀ y₁ h₀ h₁ u₀ u₁ he
    have hu : IsUnit ((x₀ : A.K) * A.NL y₀) := x₀.isUnit.mul (u₀.map (Algebra.norm A.K))
    obtain ⟨z, -, hz⟩ := hS hu.unit
    have e0 := hz x₀ ⟨h₀, y₀, u₀, by simp⟩
    have e1 := hz x₁ ⟨h₁, y₁, u₁, by simp [he]⟩
    rw [e0, e1]
  let jx : A.Kˣ → SpecialLinearGroup (Fin 2) A.K → ℂ := fun x' g => W x' g (φ x') 0
  let φw : A.Kˣ → A.L → ℂ := fun x' => W x' (wS A.K) (φ x')
  let jw : A.Kˣ → SpecialLinearGroup (Fin 2) A.K → ℂ := fun x' g => W x' g (φw x') 0
  let r : A.Kˣ → ℂ := fun x' => -(γ x')⁻¹
  let Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ := fun g =>
    (∑ x' ∈ Sf, r x' * jx x' g) + κ * A.jHyp m.μK ψ φ' g
  have hφw : ∀ x' ∈ S, IsTest (φw x') := fun x' hx' => (hW x' hx').1.1 _ _ (hφ x' hx')
  have hjx : ∀ x' ∈ Sf, A.InI (jx x') := fun x' hx' =>
    (GlobalTheory.T.weilRep_evalZero_mem_induced F E A ψ hψ x' _ _ _ (hW x' ((hmem x').1 hx')) _ (hφ x' ((hmem x').1 hx'))).1
  have hjw : ∀ x' ∈ Sf, A.InI (jw x') := fun x' hx' =>
    (GlobalTheory.T.weilRep_evalZero_mem_induced F E A ψ hψ x' _ _ _ (hW x' ((hmem x').1 hx')) _ (hφw x' ((hmem x').1 hx'))).1
  have h14 := GlobalTheory.T.jHyp_mem_induced_fourier_weyl F E A ψ hψ m.μK m.sdK φ' hφ'
  have hF' : IsTest (A.fourK m.μK ψ φ') := GlobalTheory.T.fourierTransformKProd_locallyConstantCompactSupport F E A ψ hψ m.μK m.sdK φ' hφ'
  have h14F := GlobalTheory.T.jHyp_mem_induced_fourier_weyl F E A ψ hψ m.μK m.sdK _ hF'
  have hΨ : A.InI Ψ := inI_comb F E A _ _ κ (inI_sum A Sf r jx hjx) h14.1

  have hlim : ∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ m.μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0) := by
    intro a ha
    obtain ⟨x₀, ⟨hx₀, y₀, hy₀, ha₀⟩, -⟩ := hS ha.unit
    have ha₀' : a = x₀ * A.NL y₀ := by simpa using ha₀
    have hne : ∀ᶠ c in 𝓝[≠] (0 : F), c ≠ 0 := self_mem_nhdsWithin
    have h14b := GlobalTheory.T.truncatedWhittaker_jHyp_eq_orbitalIntegral F E A ψ hψ m.μK m.sdK φ' hφ' a ha
    have h15 : ∀ᶠ c in 𝓝[≠] (0 : F), ∀ x' ∈ Sf,
        A.abelian₂ m.μK ψ a (jx x') c = if x' = x₀ then γ x₀ * A.orbL m.ν (φ x₀) y₀ else 0 := by
      rw [Finset.eventually_all]
      intro x' hx'
      have hx'S := (hmem x').1 hx'
      have := GlobalTheory.T.truncatedWhittaker_weilRep_eventually F E A ψ hψ m x' _ _ (hW x' hx'S) _ (hφ x' hx'S) a ha
      by_cases hxx : x' = x₀
      · subst hxx
        simpa using this.1 y₀ hy₀ ha₀'
      · have hno : ¬ ∃ y' : A.L, IsUnit y' ∧ a = x' * A.NL y' := by
          rintro ⟨y', hy', he⟩
          exact hxx (huniq x' x₀ y' y₀ hx'S hx₀ hy' hy₀ (he.symm.trans ha₀'))
        simpa [hxx] using this.2 hno
    have hev : ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a Ψ c = 0 := by
      filter_upwards [hne, h14b, h15] with c hc e14 e15
      have hl := lam_comb F E A ψ hψ m.μK hμ a _ _ κ (inI_sum A Sf r jx hjx) h14.1 c hc
      rw [hl, lam_sum A ψ hψ m.μK hμ a Sf r jx hjx c hc, e14]
      rw [Finset.sum_congr rfl (fun x' hx' => by rw [e15 x' hx'])]
      have hx₀f : x₀ ∈ Sf := (hmem x₀).2 hx₀
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', hx₀f, if_true]
      have hm := hmatch x₀ hx₀ y₀ hy₀
      rw [← ha₀'] at hm
      rw [hm]
      by_cases hg : γ x₀ = 0
      · have h0 : φ x₀ = 0 := by
          by_contra hne0
          exact (GlobalTheory.T.weilRep_evalZero_mem_induced F E A ψ hψ x₀ _ _ _ (hW x₀ hx₀) _ (hφ x₀ hx₀)).2 hne0 hg
        simp [h0, Et.orbL]
      · simp only [r]
        field_simp
        ring
    exact tendsto_const_nhds.congr' (hev.mono fun c hc => hc.symm)
  have h13 := (GlobalTheory.T.kirillov_vanishing_of_limit F E A ψ hψ m.μK m.sdK Ψ hΨ hlim).2

  have hΨw : (fun h => Ψ (h * wS A.K)) = fun g => (∑ x' ∈ Sf, r x' * jw x' g) +
      κ * A.jHyp m.μK ψ (A.fourK m.μK ψ φ') g := by
    funext g
    simp only [Ψ]
    rw [h14.2 g]
    congr 1
    refine Finset.sum_congr rfl fun x' hx' => ?_
    have hx'S := (hmem x').1 hx'
    simp only [jx, jw, φw]
    rw [(hW x' hx'S).1.2.2.1 g (wS A.K) (φ x') (hφ x' hx'S)]
  set a := (x : A.K) * A.NL y with hadef
  have ha : IsUnit a := x.isUnit.mul (hy.map (Algebra.norm A.K))
  have hne : ∀ᶠ c in 𝓝[≠] (0 : F), c ≠ 0 := self_mem_nhdsWithin
  have h14b := GlobalTheory.T.truncatedWhittaker_jHyp_eq_orbitalIntegral F E A ψ hψ m.μK m.sdK _ hF' a ha
  have h15 : ∀ᶠ c in 𝓝[≠] (0 : F), ∀ x' ∈ Sf,
      A.abelian₂ m.μK ψ a (jw x') c = if x' = x then γ x * A.orbL m.ν (φw x) y else 0 := by
    rw [Finset.eventually_all]
    intro x' hx'
    have hx'S := (hmem x').1 hx'
    have := GlobalTheory.T.truncatedWhittaker_weilRep_eventually F E A ψ hψ m x' _ _ (hW x' hx'S) _ (hφw x' hx'S) a ha
    by_cases hxx : x' = x
    · subst hxx
      simpa using this.1 y hy rfl
    · have hno : ¬ ∃ y' : A.L, IsUnit y' ∧ a = x' * A.NL y' := by
        rintro ⟨y', hy', he⟩
        exact hxx (huniq x' x y' y hx'S hx hy' hy he.symm)
      simpa [hxx] using this.2 hno
  obtain ⟨c, hc, e14, e15⟩ := (hne.and (h14b.and h15)).exists
  have hz := h13 a c
  rw [hΨw, lam_comb F E A ψ hψ m.μK hμ a _ _ κ (inI_sum A Sf r jw hjw) h14F.1 c hc,
    lam_sum A ψ hψ m.μK hμ a Sf r jw hjw c hc, e14,
    Finset.sum_congr rfl (fun x' hx' => by rw [e15 x' hx'])] at hz
  have hxf : x ∈ Sf := (hmem x).2 hx
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', hxf, if_true] at hz
  have horb : A.orbL m.ν (φw x) y = γ x * A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) (φ x)) y := by
    simp only [Et.orbL, φw]
    rw [← integral_const_mul]
    congr 1
    funext t
    exact ((hW x hx).2 (φ x) (hφ x hx)).2.2 _
  rw [horb] at hz
  simp only [r] at hz
  by_cases hg : γ x = 0
  · simp [hg] at hz
    simp [hg, hz]
  · field_simp at hz
    linear_combination hz
end GlobalTheory.JR.RankOneTransfer
