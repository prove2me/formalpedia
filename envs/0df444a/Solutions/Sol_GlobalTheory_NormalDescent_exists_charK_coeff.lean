-- Prove2me | solution 1 for GlobalTheory.NormalDescent.exists_charK_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:12.041288+00:00
-- url     : https://prove2.me/submissions/0e290cd3-aba5-4742-a507-ce0abc717438

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ReversedCharpolyCoeffInDomainMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Polynomial TensorProduct
open GlobalTheory GlobalTheory.NormalDescent
namespace GlobalTheory.NormalDescent
theorem _root_.solution {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Finite) (b : B) (n : ℕ) :
    ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).coeff n := by
  classical
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  let K := FractionRing A
  let Ω := AlgebraicClosure K
  let ι := algebraMap K Ω
  let V := K ⊗[A] B
  haveI : Module.Free K V := Module.Free.of_divisionRing _ _
  let e := Module.finBasis K V
  let Mx := Algebra.leftMulMatrix e ((1 : K) ⊗ₜ[A] b)
  have hg : charK φ hφ K b = Mx.charpoly := by
    show (Algebra.lmul K V ((1 : K) ⊗ₜ[A] b)).charpoly = _
    show _ = (Algebra.leftMulMatrix e _).charpoly
    rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  have hb : IsIntegral A b := Algebra.IsIntegral.isIntegral b
  have h1 : IsIntegral A ((1 : K) ⊗ₜ[A] b) :=
    hb.map (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B)
  have h2 : IsIntegral A Mx := h1.map ((Algebra.leftMulMatrix e).restrictScalars A)
  have h3 : IsIntegral A (Mx.map ι) := h2.map (AlgHom.mapMatrix (IsScalarTower.toAlgHom A K Ω))
  obtain ⟨p, hpm, hp⟩ := h3
  have hroot : ∀ μ ∈ (Mx.charpoly.map ι).roots, IsIntegral A μ := by
    intro μ hμ
    have hs : μ ∈ spectrum Ω (Mx.map ι) := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map]
      exact isRoot_of_mem_roots hμ
    have h4 := spectrum.subset_polynomial_aeval (Mx.map ι) (p.map (algebraMap A Ω)) ⟨μ, hs, rfl⟩
    have h5 : aeval (Mx.map ι) (p.map (algebraMap A Ω)) = 0 := by
      rw [aeval_map_algebraMap, aeval_def]; exact hp
    rw [h5] at h4
    refine ⟨p, hpm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap Ω]
    by_contra hne
    exact (spectrum.mem_iff.1 h4) (by
      simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) Ω)))
  have hl : Mx.charpoly.map ι ∈ Polynomial.lifts (integralClosure A Ω).val.toRingHom :=
    (IsAlgClosed.splits _).mem_lift_of_roots_mem_range ((Matrix.charpoly_monic _).map _) _
      fun μ hμ => ⟨⟨μ, hroot μ hμ⟩, rfl⟩
  rw [lifts_iff_coeff_lifts] at hl
  obtain ⟨s, hs⟩ := hl n
  have hc : IsIntegral A (Mx.charpoly.coeff n) := by
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K Ω) ι.injective).1 ?_
    show IsIntegral A (ι _)
    rw [← coeff_map, ← hs]
    exact s.2
  rw [hg]
  exact IsIntegrallyClosed.isIntegral_iff.1 hc
end GlobalTheory.NormalDescent
