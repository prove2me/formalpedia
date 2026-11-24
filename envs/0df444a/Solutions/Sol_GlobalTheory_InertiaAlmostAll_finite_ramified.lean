-- Prove2me | solution 1 for GlobalTheory.InertiaAlmostAll.finite_ramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:22:14.226622+00:00
-- url     : https://prove2.me/submissions/2aa33f4a-fb1e-468a-95b1-4b0eedc953a4

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinitePlacesInertiaNotFixingFiniteExtension
import Theorems.Thm_GlobalTheory_InertiaAlmostAll_finite_moves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.InertiaAlmostAll
namespace GlobalTheory.InertiaAlmostAll
theorem _root_.solution (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L] :
    {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      ¬ Ine (F := F) B ≤ L.fixingSubgroup}.Finite := by
  let b := Module.finBasis F L
  refine (Set.finite_iUnion fun i => finite_moves F Ω (b i : Ω)).subset ?_
  rintro v ⟨B, hB, hn⟩
  by_contra hv
  apply hn
  intro τ hτ
  have hb : ∀ i, τ (b i : Ω) = b i := by
    intro i
    by_contra h
    exact hv (Set.mem_iUnion.mpr ⟨i, B, hB, τ, hτ, h⟩)
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have : τ.toLinearMap.comp L.val.toLinearMap = L.val.toLinearMap :=
    b.ext fun i => by simpa using hb i
  simpa using LinearMap.congr_fun this ⟨y, hy⟩
end GlobalTheory.InertiaAlmostAll
