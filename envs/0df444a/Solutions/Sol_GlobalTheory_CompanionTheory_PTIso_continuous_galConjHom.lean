-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.continuous_galConjHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:55:20.646861+00:00
-- url     : https://prove2.me/submissions/aa396881-5720-43d2-9bb8-0256b4191692

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisGroupTransportIsomorphism
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_galConjHom_apply

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
variable {F Ω F' Ω' : Type} [Field F] [Field Ω] [Algebra F Ω]
  [Field F'] [Field Ω'] [Algebra F' Ω']
namespace GlobalTheory.CompanionTheory.PTIso
theorem _root_.solution [Algebra.IsAlgebraic F Ω]
    (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) :
    Continuous (galConjHom e E hE) := by
  refine continuous_of_continuousAt_one _ ?_
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨K', hK', hKs⟩ := hs
  let b := Module.finBasis F' K'
  let T : Set Ω := Set.range fun i => E.symm (b i : Ω')
  let L : IntermediateField F Ω := IntermediateField.adjoin F T
  have hL : FiniteDimensional F L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨L, hL, fun σ hσ => hKs ?_⟩
  have hfix : ∀ i, galConjHom e E hE σ (b i : Ω') = (b i : Ω') := by
    intro i
    have hmem : E.symm (b i : Ω') ∈ L :=
      IntermediateField.subset_adjoin F T ⟨i, rfl⟩
    have h1 : σ (E.symm (b i : Ω')) = E.symm (b i : Ω') :=
      (IntermediateField.mem_fixingSubgroup_iff L σ).1 hσ _ hmem
    have h2 := galConjHom_apply e E hE σ (E.symm (b i : Ω'))
    rwa [h1, RingEquiv.apply_symm_apply] at h2
  have hlin : ((galConjHom e E hE σ).toAlgHom.comp K'.val).toLinearMap = K'.val.toLinearMap :=
    b.ext fun i => hfix i
  refine (IntermediateField.mem_fixingSubgroup_iff K' _).2 fun x hx => ?_
  exact congrArg (fun f : K' →ₗ[F'] Ω' => f ⟨x, hx⟩) hlin
end GlobalTheory.CompanionTheory.PTIso
