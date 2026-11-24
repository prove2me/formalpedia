-- Prove2me | solution 1 for GlobalTheory.DenseSec.exists_etChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:29:00.239797+00:00
-- url     : https://prove2.me/submissions/21f7e2fc-51a4-400a-9e3c-32b43721b11c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEtaleChartSmoothAlgebraLocalPoint
import Theorems.Thm_GlobalTheory_DenseSec_formallyEtale_of_bijective_kaehler_mapBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
noncomputable section
open GlobalTheory GlobalTheory.DenseSec
open KaehlerDifferential
open scoped TensorProduct
namespace GlobalTheory.DenseSec
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A),
      (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := by
  intro R _ _ A _ _ _ ε
  classical
  let p : Ideal A := (maximalIdeal R).comap ε
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _
    (span_range_map_derivation_of_isLocalization R _ (Localization.AtPrime p) p.primeCompl)
  let t : κ → A := fun i => a i - algebraMap R A (ε (a i))
  have hDt : ∀ i, D R A (t i) = D R A (a i) := by intro i; simp [t]
  have hεt : ∀ i, ε (t i) = 0 := by intro i; simp [t]
  let e : (κ →₀ A) →ₗ[A] Ω[A⁄R] :=
    Finsupp.linearCombination A fun i : κ ↦ D R A (t i)
  let l₁ : (κ →₀ A) →ₗ[A] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.AtPrime p))
  let l₂ : Ω[A⁄R] →ₗ[A] Ω[Localization.AtPrime p⁄R] := map R R A (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e <| l₁ <| Finsupp.single i 1
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb, hDt]
  have heₚ : Function.Bijective eₚ := this ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ A) →ₗ[A] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A _)
  let l₂ₜ : Ω[A⁄R] →ₗ[A] Ω[Localization.Away g⁄R] :=
    map R R A (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  let bB : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R] :=
    .ofRepr (LinearEquiv.ofBijective eₜ' h).symm
  have hbB : ∀ i, bB i = D R _ (algebraMap A (Localization.Away g) (t i)) := by
    intro i
    have h1 : bB i = eₜ' (Finsupp.single i 1) := by
      rfl
    rw [h1]
    trans IsLocalizedModule.map (Submonoid.powers g) l₁ₜ l₂ₜ e <| l₁ₜ <| Finsupp.single i 1
    · simp [eₜ', -IsLocalizedModule.map_apply, l₁ₜ]
    · simp [l₂ₜ, e]
  let eκ : κ ≃ Fin (Nat.card κ) := Finite.equivFin κ
  refine ⟨Nat.card κ, t ∘ eκ.symm, g, fun i => hεt _, ?_, ?_⟩
  · have hg' : ε g ∉ maximalIdeal R := hg
    exact (IsLocalRing.notMem_maximalIdeal.mp hg')
  · unfold EtChart
    letI inst : Algebra (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) :=
      ((algebraMap A (Localization.Away g)).comp (MvPolynomial.aeval (t ∘ eκ.symm)).toRingHom).toAlgebra
    show Algebra.Etale (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g)
    have hsc : IsScalarTower R (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change algebraMap R (Localization.Away g) r =
          algebraMap A (Localization.Away g) (MvPolynomial.aeval (t ∘ eκ.symm) (MvPolynomial.C r))
        rw [MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply]
    have hX : ∀ i, algebraMap (MvPolynomial (Fin (Nat.card κ)) R) (Localization.Away g) (MvPolynomial.X i) =
        algebraMap A (Localization.Away g) (t (eκ.symm i)) := by
      intro i
      change algebraMap A (Localization.Away g) (MvPolynomial.aeval (t ∘ eκ.symm) (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X]; rfl
    haveI : Algebra.FormallySmooth A (Localization.Away g) := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers g)
    haveI : Algebra.FormallySmooth R (Localization.Away g) := Algebra.FormallySmooth.comp R A (Localization.Away g)
    let P := MvPolynomial (Fin (Nat.card κ)) R
    let bP : Module.Basis (Fin (Nat.card κ)) (Localization.Away g) ((Localization.Away g) ⊗[P] Ω[P⁄R]) :=
      (mvPolynomialBasis R (Fin (Nat.card κ))).baseChange (Localization.Away g)
    let bB' := bB.reindex eκ
    have hbij : Function.Bijective (mapBaseChange R P (Localization.Away g)) := by
      have : mapBaseChange R P (Localization.Away g) = (bP.equiv bB' (Equiv.refl _)).toLinearMap := by
        refine bP.ext fun i => ?_
        rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
        simp [bP, bB', hbB, ← hX, P]
      rw [this]
      exact (bP.equiv bB' (Equiv.refl _)).bijective
    haveI : Algebra.FormallyEtale P (Localization.Away g) :=
      formallyEtale_of_bijective_kaehler_mapBaseChange R P (Localization.Away g) hbij
    haveI : Algebra.FinitePresentation R (Localization.Away g) :=
      Algebra.FinitePresentation.trans R A (Localization.Away g)
    haveI : Algebra.FinitePresentation P (Localization.Away g) :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R P (Localization.Away g)
    exact ⟨inferInstance, inferInstance⟩
end GlobalTheory.DenseSec
