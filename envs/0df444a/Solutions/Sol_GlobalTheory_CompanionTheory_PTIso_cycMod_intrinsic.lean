-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:14:00.828809+00:00
-- url     : https://prove2.me/submissions/6181b04b-d910-4df2-81c9-241a9f08d95f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingEquivCyclotomicCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_apply_eq_pow_cycMod_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso
namespace GlobalTheory.CompanionTheory.PTIso
theorem _root_.solution : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω), cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ l _ r σ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have h1 := apply_eq_pow_cycMod_val (F := F) (Ω := Ω) l r σ hζ.pow_eq_one
  have h2 := apply_eq_pow_cycMod_val (F := F') (Ω := Ω') l r (Φ σ) (ζ := E ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hζ' : IsPrimitiveRoot (E ζ) (l ^ r) := hζ.map_of_injective E.injective
  rw [hΦ, h1, map_pow] at h2
  have hv := hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2
  apply Units.ext
  exact ZMod.val_injective _ hv.symm
end GlobalTheory.CompanionTheory.PTIso
