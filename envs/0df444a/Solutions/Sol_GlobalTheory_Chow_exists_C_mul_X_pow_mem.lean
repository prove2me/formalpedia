-- Prove2me | solution 1 for GlobalTheory.Chow.exists_C_mul_X_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:39.505305+00:00
-- url     : https://prove2.me/submissions/96e8d2bd-a279-4b6d-8b2e-61f9b735c454

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Theorems.Thm_GlobalTheory_Chow_exists_smul_mem_of_span_eq_top
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.Chow
theorem _root_.solution {R Ω σ : Type*} [CommRing R] [Field Ω] [IsAlgClosed Ω] [Finite σ]
    (φ : R →+* Ω) {I : Ideal (MvPolynomial σ R)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R))
    (h : ∀ x : σ → Ω, (∀ g ∈ I, eval x (map φ g) = 0) → x = 0) :
    ∃ r, φ r ≠ 0 ∧ ∃ m : ℕ, ∀ j, C r * X j ^ m ∈ I := by
  classical
  cases nonempty_fintype σ
  have hrad : ∀ j, ∃ m : ℕ, (X j : MvPolynomial σ Ω) ^ m ∈ I.map (map φ) := by
    intro j
    have : (X j : MvPolynomial σ Ω) ∈ (I.map (map φ)).radical := by
      rw [← vanishingIdeal_zeroLocus_eq_radical (K := Ω)]
      intro x hx
      rw [h x fun g hg => hx _ (Ideal.mem_map_of_mem _ hg)]
      simp
    exact this
  choose m hm using hrad
  let d := ∑ j, m j + 1
  let n := {a : σ →₀ ℕ // a.degree = d}
  haveI : Finite n := (Finsupp.finite_of_degree_eq d).to_subtype
  letI : Fintype n := Fintype.ofFinite n

  have hmon : ∀ a : n, monomial a.1 (1 : Ω) ∈ I.map (map φ) := by
    intro a
    obtain ⟨j, hj⟩ : ∃ j, m j ≤ a.1 j := by
      by_contra hc
      push Not at hc
      have h1 : ∑ j, a.1 j ≤ ∑ j, m j := Finset.sum_le_sum fun j _ => (hc j).le
      have h2 := a.2
      rw [Finsupp.degree_eq_sum] at h2
      omega
    have hle : Finsupp.single j (m j) ≤ a.1 := Finsupp.single_le_iff.2 hj
    obtain ⟨c, hc⟩ := exists_add_of_le hle
    rw [hc, ← mul_one (1 : Ω), ← monomial_mul, ← X_pow_eq_monomial]
    exact Ideal.mul_mem_right _ _ (hm j)
  let L : (n → R) →ₗ[R] MvPolynomial σ R := ∑ a : n, (monomial a.1).comp (LinearMap.proj a)
  have hL (v) : L v = ∑ a : n, monomial a.1 (v a) := by simp [L]
  let S : Submodule R (n → R) := (I.restrictScalars R).comap L
  let π : MvPolynomial σ Ω →ₗ[Ω] (n → Ω) := LinearMap.pi fun a => lcoeff Ω a.1
  let T := Submodule.span Ω ((fun v : n → R => φ ∘ v) '' S)
  have h1 : ∀ g ∈ I, π (map φ g) ∈ T := by
    intro g hg
    refine Submodule.subset_span ⟨fun a => coeff a.1 g, ?_, ?_⟩
    · have : L (fun a => coeff a.1 g) = homogeneousComponent d g := by
        ext c
        rw [hL, coeff_sum, coeff_homogeneousComponent]
        split_ifs with hc
        · rw [Finset.sum_eq_single (⟨c, hc⟩ : n)]
          · simp
          · intro a _ ha
            rw [coeff_monomial, if_neg fun h => ha (Subtype.ext h)]
          · simp
        · refine Finset.sum_eq_zero fun a _ => ?_
          rw [coeff_monomial, if_neg fun h : a.1 = c => hc (h ▸ a.2)]
      change L _ ∈ I
      rw [this]
      exact homogeneousComponent_mem_of_mem hI hg d
    · ext a
      simp [π, coeff_map]
  have h2 : ∀ g ∈ I.map (map φ), ∀ c, π (monomial c 1 * g) ∈ T := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      intro c
      have := h1 _ (I.mul_mem_left (monomial c 1) hg)
      rwa [map_mul, map_monomial, map_one] at this
    | zero => simp
    | add x y _ _ hx hy => intro c; rw [mul_add, map_add]; exact T.add_mem (hx c) (hy c)
    | smul a x _ hx =>
      intro c
      induction a using MvPolynomial.induction_on' with
      | monomial u r =>
        have : monomial c 1 * monomial u r • x = r • (monomial (c + u) 1 * x) := by
          rw [smul_eq_mul, ← mul_assoc, monomial_mul, ← smul_mul_assoc, smul_monomial]
          simp
        rw [this, map_smul]
        exact T.smul_mem _ (hx _)
      | add p q hp hq => rw [add_smul, mul_add, map_add]; exact T.add_mem hp hq
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun Ω n).span_eq, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have := h2 _ (hmon a) 0
    rw [monomial_zero', C_1, one_mul] at this
    have h3 : Pi.basisFun Ω n a = π (monomial a.1 1) := by
      ext b
      by_cases hab : a = b
      · simp [π, hab]
      · have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
        simp [π, coeff_monomial, hab', Ne.symm hab]
    rwa [h3]
  obtain ⟨r, hr, hrS⟩ := exists_smul_mem_of_span_eq_top φ S hT
  refine ⟨r, hr, d, fun j => ?_⟩
  let a : n := ⟨Finsupp.single j d, by simp⟩
  have : L (r • Pi.single a 1) ∈ I := hrS (Pi.single a 1)
  rw [map_smul, hL, Finset.sum_eq_single a] at this
  · rwa [Pi.single_eq_same, ← X_pow_eq_monomial, smul_eq_C_mul] at this
  · intro b _ hb
    simp [hb]
  · simp
end GlobalTheory.Chow
