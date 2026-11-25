-- Prove2me | solution 1 for GlobalTheory.T.finite_isometryClasses_definiteHermitian_boundedScale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:05.979268+00:00
-- url     : https://prove2.me/submissions/859ed276-2074-437d-af07-2deda4a3164b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FiniteIsometryClassesDefiniteHermitianBoundedSca
import Mathlib
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FiniteIsometryClassesDefiniteHermitianBoundedScaStatement
import Theorems.Thm_GlobalTheory_hermLat_boundedScaleDual_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) → ∀ (d c : ℕ), 0 < d → 0 < c → ∃ s : Finset (Submodule (𝓞 K) V), (∀ M₀ ∈ s, Submodule.IsLattice K M₀) ∧ ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M) → ∃ M₀ ∈ s, ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g M₀ = M := by
  first | exact @GlobalTheory.hermLat_boundedScaleDual_finite | exact GlobalTheory.hermLat_boundedScaleDual_finite | (intros; apply GlobalTheory.hermLat_boundedScaleDual_finite <;> assumption)
end _root_.GlobalTheory.T
