-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_prod_params
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:59.422436+00:00
-- url     : https://prove2.me/submissions/768cca65-79da-41fe-99a4-bd3ff87672f7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_RegularSystemOfParametersLocalRing
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_BdRad_algebraMap_locRing_eq_zero_of_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_BdRad_map_ptIdeal_eq_maximalIdeal
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_BdRad_exists_den_of_mem_map
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_BdRad_radical_span_prod_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_exists_mul_mem_of_algebraMap_locRing_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isUnit_algebraMap_locRing_iff
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_mk_locRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_isDomain_of_isRegularLocalRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_prime_of_regular_params
import Theorems.Thm_ReciprocityTheory_AnForm_R_regular_params_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
namespace GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
theorem _root_.solution : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ h : MvPolynomial (Fin m) ℂ, eval t h ≠ 0 ∧ h * ∏ l ∈ Jf, r l ∈ Dc.radical ∧ ∀ g ∈ Dc.radical, h * g ∈ Ideal.span {∏ l ∈ Jf, r l} ⊔ I := by
  classical
  intro m e I Dc t r Jf hID hp hreg hdim hspan hprime
  haveI := hreg
  haveI : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing
  set alg : MvPolynomial (Fin m) ℂ →+* locRing I t := algebraMap _ (locRing I t) with halg
  set R : Fin e → locRing I t := fun l => alg (r l) with hR
  have hspan' : Ideal.span (Set.range R) = IsLocalRing.maximalIdeal (locRing I t) := by
    rw [← map_ptIdeal_eq_maximalIdeal I t hp]
    exact hspan
  have hpr : ∀ i, Prime (R i) := prime_of_regular_params R hspan' hdim.symm
  have hna := (regular_params_spec R hspan' hdim.symm).2
  set Q : MvPolynomial (Fin m) ℂ := ∏ l ∈ Jf, r l with hQ
  have hPQ : alg Q = ∏ l ∈ Jf, R l := map_prod alg _ _

  have hpr2 : ∀ 𝔓 : Ideal (locRing I t), 𝔓.IsPrime →
      (Ideal.map alg Dc ≤ 𝔓 ↔ alg Q ∈ 𝔓) := by
    intro 𝔓 h𝔓
    have hq1 : (Ideal.comap alg 𝔓).IsPrime := Ideal.comap_isPrime alg 𝔓
    have hq2 : I ≤ Ideal.comap alg 𝔓 := fun a ha => by
      rw [Ideal.mem_comap, halg, algebraMap_locRing_eq_zero_of_mem I t ha]
      exact 𝔓.zero_mem
    have hq3 : Ideal.comap alg 𝔓 ≤ ptIdeal t := fun a ha => by
      by_contra hne
      have hu := (isUnit_algebraMap_locRing_iff I t hp a).mpr fun h => hne (RingHom.mem_ker.mpr h)
      exact h𝔓.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
    rw [Ideal.map_le_iff_le_comap, hprime _ hq1 hq2 hq3, hPQ, Ideal.IsPrime.prod_mem_iff]
    rfl
  have hrad : (Ideal.map alg Dc).radical = Ideal.span {alg Q} := by
    rw [hPQ, ← radical_span_prod_eq R Jf hpr hna, ← hPQ, Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
    congr 1
    ext 𝔓
    simp only [Set.mem_setOf_eq, Ideal.span_singleton_le_iff_mem]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(hpr2 𝔓 h2).mp h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(hpr2 𝔓 h2).mpr h1, h2⟩⟩

  obtain ⟨h', hh', hQrad⟩ : ∃ h', eval t h' ≠ 0 ∧ h' * Q ∈ Dc.radical := by
    have h1 : alg Q ∈ (Ideal.map alg Dc).radical := by
      rw [hrad]; exact Ideal.mem_span_singleton_self _
    obtain ⟨N, hN⟩ := h1
    rw [← map_pow] at hN
    obtain ⟨s, hs, hsm⟩ := exists_den_of_mem_map I Dc t hID hp hN
    refine ⟨s, hs, N + 1, ?_⟩
    have : (s * Q) ^ (N + 1) = s ^ N * Q * (s * Q ^ N) := by ring
    rw [this]
    exact Dc.mul_mem_left _ hsm

  have hone : ∀ g ∈ Dc.radical, ∃ hg, eval t hg ≠ 0 ∧ hg * g ∈ Ideal.span {Q} ⊔ I := by
    rintro g ⟨n, hn⟩
    have h1 : alg g ∈ (Ideal.map alg Dc).radical :=
      ⟨n, by rw [← map_pow]; exact Ideal.mem_map_of_mem _ hn⟩
    rw [hrad, Ideal.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t c
    have h0 : algebraMap _ (locRing I t) (g * b - Q * a) = 0 := by
      change alg (g * b - Q * a) = 0
      have hab' : c * alg b = alg a := hab
      rw [map_sub, map_mul, map_mul, hc, ← hab']
      ring
    obtain ⟨s, hs, hsm⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t h0
    refine ⟨s * b, by simpa using ⟨hs, hb⟩, ?_⟩
    have : s * b * g = s * (g * b - Q * a) + Q * (s * a) := by ring
    rw [this, add_comm]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_right hsm)

  obtain ⟨S, hS⟩ : Dc.radical.FG := IsNoetherian.noetherian _
  have hSm : ∀ g, g ∈ S → ∃ hg, eval t hg ≠ 0 ∧ hg * g ∈ Ideal.span {Q} ⊔ I := fun g hg =>
    hone g (hS ▸ Submodule.subset_span hg)
  choose! f hf0 hf1 using hSm
  set H : MvPolynomial (Fin m) ℂ := ∏ g ∈ S, f g with hH
  have hH0 : eval t H ≠ 0 := by
    rw [hH, map_prod]
    exact Finset.prod_ne_zero_iff.mpr hf0
  have hHS : Dc.radical ≤
      Submodule.comap (LinearMap.mulLeft (MvPolynomial (Fin m) ℂ) H) (Ideal.span {Q} ⊔ I) := by
    rw [← hS]
    refine Submodule.span_le.mpr fun g hg => ?_
    obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem f hg
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    rw [hH, hw, mul_comm (f g) w, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hf1 g hg)
  refine ⟨h' * H, by simpa using ⟨hh', hH0⟩, ?_, fun g hg => ?_⟩
  · have : h' * H * Q = H * (h' * Q) := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hQrad
  · have h1 := hHS hg
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at h1
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ h1
end GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
