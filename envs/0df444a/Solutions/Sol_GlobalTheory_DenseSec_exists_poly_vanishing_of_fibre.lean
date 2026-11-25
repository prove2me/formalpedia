-- Prove2me | solution 1 for GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:41:27.368856+00:00
-- url     : https://prove2.me/submissions/b43b5d69-653b-4947-be1c-606a9e38170a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedAStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleChartLocalizationFiniteTypeFormallyUnramifiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolyVanishingOfFibre
import Theorems.Thm_GlobalTheory_T_etaleChart_localization_finiteType_formallyUnramified
import Theorems.Thm_P2M_GlobalTheory_T_exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified__2991a8b24817


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.DenseSec
open TensorProduct
namespace GlobalTheory.DenseSec
theorem _root_.solution : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω], IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ Q : MvPolynomial (Fin g) Ω, Q ≠ 0 ∧ ∀ a : A →ₐ[R] Ω, a h ≠ 0 → GlobalTheory.DenseSec.pt a f = 0 → MvPolynomial.eval (fun i => a (t i)) Q = 0 := by
  intro R _ A _ _ g t h hE Ω _ _ hirr f hf
  have hN : (nilradical (TensorProduct R Ω A)).IsPrime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.1 hirr
  have kill : ∀ (a : A →ₐ[R] Ω) (x : TensorProduct R Ω A), x ∈ nilradical (TensorProduct R Ω A) → GlobalTheory.DenseSec.pt a x = 0 := by
    intro a x hx
    exact ((mem_nilradical.1 hx).map (GlobalTheory.DenseSec.pt a)).eq_zero
  have pth : ∀ (a : A →ₐ[R] Ω) (x : A), GlobalTheory.DenseSec.pt a (1 ⊗ₜ[R] x) = a x := by
    intro a x
    simp [GlobalTheory.DenseSec.pt]
  have ptw : ∀ (a : A →ₐ[R] Ω) (w : Ω), GlobalTheory.DenseSec.pt a (w ⊗ₜ[R] 1) = w := by
    intro a w
    simp [GlobalTheory.DenseSec.pt]
  by_cases h1 : (1 ⊗ₜ[R] h : TensorProduct R Ω A) ∈ nilradical (TensorProduct R Ω A)
  · refine ⟨1, one_ne_zero, fun a ha _ => ?_⟩
    exact absurd (by rw [← pth a h]; exact kill a _ h1) ha
  set N := nilradical (TensorProduct R Ω A)
  set u : TensorProduct R Ω A ⧸ N := Ideal.Quotient.mk N (1 ⊗ₜ[R] h)
  have hu : u ≠ 0 := by
    simpa [u, Ideal.Quotient.eq_zero_iff_mem] using h1
  letI : IsDomain (TensorProduct R Ω A ⧸ N) := Ideal.Quotient.isDomain N
  have hle : Submonoid.powers u ≤ nonZeroDivisors (TensorProduct R Ω A ⧸ N) := powers_le_nonZeroDivisors_of_noZeroDivisors hu
  letI : IsDomain (Localization.Away u) := IsLocalization.isDomain_localization hle
  obtain ⟨hFT, hFU⟩ := GlobalTheory.T.etaleChart_localization_finiteType_formallyUnramified R A g t h hE Ω N
  letI : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away u) :=
    (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
  have hf' : algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N f) ≠ 0 := by
    intro h0
    rw [map_eq_zero_iff _ (IsLocalization.injective (Localization.Away u) hle), Ideal.Quotient.eq_zero_iff_mem] at h0
    exact hf (mem_nilradical.1 h0)
  obtain ⟨Q, hQ, d, hd⟩ := GlobalTheory.T.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified' (MvPolynomial (Fin g) Ω) (Localization.Away u) _ hf'
  refine ⟨Q, hQ, fun a ha hfa => ?_⟩
  let φ : TensorProduct R Ω A ⧸ N →+* Ω := Ideal.Quotient.lift N (GlobalTheory.DenseSec.pt a).toRingHom (fun x hx => kill a x hx)
  have hφu : IsUnit (φ u) := by
    simp only [φ, u, Ideal.Quotient.lift_mk]
    exact isUnit_iff_ne_zero.2 (by simpa [pth] using ha)
  let χ : Localization.Away u →+* Ω := IsLocalization.Away.lift u hφu
  have hχ : ∀ x : TensorProduct R Ω A, χ (algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N x)) = GlobalTheory.DenseSec.pt a x := by
    intro x
    simp [χ, φ, IsLocalization.Away.lift]
  have hP : χ.comp (algebraMap (MvPolynomial (Fin g) Ω) (Localization.Away u)) = MvPolynomial.eval₂Hom (RingHom.id Ω) (fun i => a (t i)) := by
    apply MvPolynomial.ringHom_ext
    · intro w
      show χ (MvPolynomial.aeval _ (MvPolynomial.C w)) = _
      have e : algebraMap Ω (TensorProduct R Ω A ⧸ N) w = Ideal.Quotient.mk N (w ⊗ₜ[R] 1) := rfl
      rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply Ω (TensorProduct R Ω A ⧸ N) (Localization.Away u), e, hχ, ptw]
      simp
    · intro i
      show χ (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, hχ, pth]
      simp
  have := congrArg χ hd
  rw [← RingHom.comp_apply, hP, map_mul, hχ, hfa, zero_mul] at this
  exact this
end GlobalTheory.DenseSec
