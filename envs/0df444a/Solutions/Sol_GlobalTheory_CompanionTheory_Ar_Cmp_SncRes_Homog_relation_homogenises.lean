-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.relation_homogenises
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:10.441212+00:00
-- url     : https://prove2.me/submissions/e1a11249-3c25-4a80-b22a-a3d0fecb8f08

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerInAffineChart
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Homog_aeval_smul_of_isMultiHomog
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Homog_chartSub_bind
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Homog_aeval_algebraMap_X
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Homog_map_ideal_le
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
theorem _root_.solution (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ)
    (a : K → ℕ) (n : ℕ) (s' : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
    (hP : IsMultiHomogIdeal P) (hQ : IsMultiHomogIdeal Q) (hQp : Q.IsPrime)
    (hX : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) (hf : IsMultiHomog f a)
    (hs' : s' ∉ SncRes.ideal Q p)
    (hrel : s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p) :
    ∃ s ∉ Q, s * f ∈ Q ^ n ⊔ P := by
  set x : MvPolynomial (Σ k, ι k) ℂ := ∏ k, X ⟨k, p k⟩ with hx
  let L := Localization.Away x
  let i : MvPolynomial (Σ k, ι k) ℂ →+* L := algebraMap _ L
  have hxu : IsUnit (i x) := IsLocalization.Away.algebraMap_isUnit x
  have hu : ∀ k, IsUnit (i (X ⟨k, p k⟩)) := fun k =>
    isUnit_of_dvd_unit (map_dvd i (Finset.dvd_prod_of_mem (fun k => (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ)) (Finset.mem_univ k))) hxu
  have hv : ∀ k, ∃ v, v * i (X ⟨k, p k⟩) = 1 := fun k => (hu k).exists_left_inv
  choose c hc using hv
  let w : (Σ k, ι k) → L := fun q => c q.1 * i (X q)
  have hw1 : ∀ k, w ⟨k, p k⟩ = 1 := hc
  let ψ := chartSub w
  have hψf : ψ (bind₁ (lift p) f) = (∏ k, c k ^ a k) * i f := by
    rw [chartSub_bind w p hw1, aeval_smul_of_isMultiHomog hf c, aeval_algebraMap_X]

  have h1 : ψ s' * ψ (bind₁ (lift p) f) ∈ (Q ^ n ⊔ P).map i := by
    have h2 : (ideal Q p ^ n ⊔ ideal P p).map ψ ≤ (Q ^ n ⊔ P).map i := by
      rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_sup, Ideal.map_pow]
      exact sup_le_sup (Ideal.pow_right_mono (map_ideal_le Q hQ p c hc) n)
        (map_ideal_le P hP p c hc)
    have := h2 (Ideal.mem_map_of_mem ψ hrel)
    rwa [map_mul] at this
  have hinv : (∏ k, i (X ⟨k, p k⟩) ^ a k) * ∏ k, c k ^ a k = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [← mul_pow, mul_comm, hc k, one_pow]
  have h3 : ψ s' * i f ∈ (Q ^ n ⊔ P).map i := by
    have := Ideal.mul_mem_left _ (∏ k, i (X ⟨k, p k⟩) ^ a k) h1
    rw [hψf] at this
    have e : (∏ k, i (X ⟨k, p k⟩) ^ a k) * (ψ s' * ((∏ k, c k ^ a k) * i f)) =
        ((∏ k, i (X ⟨k, p k⟩) ^ a k) * ∏ k, c k ^ a k) * (ψ s' * i f) := by ring
    rwa [e, hinv, one_mul] at this
  obtain ⟨e, s₀, hs₀⟩ := IsLocalization.Away.surj x (ψ s')
  have h4 : i (s₀ * f) ∈ (Q ^ n ⊔ P).map i := by
    rw [map_mul]
    change i s₀ * i f ∈ _
    rw [show i s₀ = ψ s' * i x ^ e from hs₀.symm]
    have := Ideal.mul_mem_left _ (i x ^ e) h3
    convert this using 1
    ring
  obtain ⟨m, hm, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers x) L _ _).1 h4
  refine ⟨m * s₀, ?_, by rwa [mul_assoc]⟩
  intro hmem
  have hxQ : x ∉ Q := by
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff).1 h
    exact hX k hk
  obtain ⟨N, rfl⟩ := hm
  have hs₀Q : s₀ ∈ Q := by
    rcases hQp.mem_or_mem hmem with h | h
    · exact absurd (hQp.mem_of_pow_mem _ h) hxQ
    · exact h

  let J := ideal Q p
  let g : MvPolynomial (Σ k, ι k) ℂ →+* (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) :=
    (Ideal.Quotient.mk J).comp (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)
  have hg1 : ∀ k, g (X ⟨k, p k⟩) = 1 := by
    intro k
    have hmem : (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) (X ⟨k, p k⟩ - 1) ∈ J :=
      Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
    have := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at this
    exact this
  have hgx : g x = 1 := by
    rw [hx, map_prod]
    exact Finset.prod_eq_one fun k _ => hg1 k
  let Φ : L →+* (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) :=
    IsLocalization.Away.lift x (g := g) (by rw [hgx]; exact isUnit_one)
  have hΦ : ∀ h, Φ (i h) = g h := fun h => IsLocalization.Away.lift_eq x _ h
  have hΦc : ∀ k, Φ (c k) = 1 := by
    intro k
    have := congrArg Φ (hc k)
    rwa [map_mul, hΦ, hg1, mul_one, map_one] at this
  have hΦψ : Φ.comp (ψ : _ →+* L) = Ideal.Quotient.mk J := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · have e1 : ψ (C r) = i (C r) := by
        rw [show (C r : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) = algebraMap ℂ _ r from rfl,
          AlgHom.commutes]
        exact IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Σ k, ι k) ℂ) L r
      show Φ (ψ (C r)) = _
      rw [e1, hΦ]
      simp [g]
    · show Φ (ψ (X j)) = _
      have e1 : ψ (X j) = w ((Fintype.equivFin (Σ k, ι k)).symm j) := by simp [ψ, chartSub]
      rw [e1]
      show Φ (c _ * i (X _)) = _
      rw [map_mul, hΦc, one_mul, hΦ]
      simp [g, renC, renameEquiv_apply]
  apply hs'
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h5 : Φ (ψ s') = Ideal.Quotient.mk J s' := DFunLike.congr_fun hΦψ s'
  have h6 := congrArg Φ hs₀
  rw [map_mul, map_pow, hΦ, hΦ, hgx, one_pow, mul_one, h5] at h6
  rw [h6]
  exact Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hs₀Q))
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
