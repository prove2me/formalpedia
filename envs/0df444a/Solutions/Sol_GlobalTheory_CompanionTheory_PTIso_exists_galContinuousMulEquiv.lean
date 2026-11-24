-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.exists_galContinuousMulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:12:17.298476+00:00
-- url     : https://prove2.me/submissions/19ee0975-f02b-4c0d-ab8b-f2780d1e3ef9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisGroupTransportIsomorphism
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_galConjHom_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_continuous_galConjHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso
namespace GlobalTheory.CompanionTheory.PTIso
theorem _root_.solution : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω']
    [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'),
    (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) →
    ∃ Φ : G F Ω ≃ₜ* G F' Ω', ∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F' Ω' := IsAlgClosure.isAlgebraic
  have hE' : ∀ x : F', E.symm (algebraMap F' Ω' x) = algebraMap F Ω (e.symm x) := by
    intro x
    rw [RingEquiv.symm_apply_eq, hE, RingEquiv.apply_symm_apply]
  refine ⟨{ toFun := galConjHom e E hE
            invFun := galConjHom e.symm E.symm hE'
            left_inv := ?_
            right_inv := ?_
            map_mul' := map_mul _
            continuous_toFun := continuous_galConjHom e E hE
            continuous_invFun := continuous_galConjHom e.symm E.symm hE' },
    fun σ x => galConjHom_apply e E hE σ x⟩
  · intro σ
    ext x
    have h := galConjHom_apply e.symm E.symm hE' (galConjHom e E hE σ) (E x)
    rw [galConjHom_apply e E hE σ x, RingEquiv.symm_apply_apply,
      RingEquiv.symm_apply_apply] at h
    exact h
  · intro τ
    ext y
    have h := galConjHom_apply e E hE (galConjHom e.symm E.symm hE' τ) (E.symm y)
    rw [galConjHom_apply e.symm E.symm hE' τ y, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply] at h
    exact h
end GlobalTheory.CompanionTheory.PTIso
