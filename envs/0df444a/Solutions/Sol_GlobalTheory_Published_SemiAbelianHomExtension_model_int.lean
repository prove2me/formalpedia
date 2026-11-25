-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.model_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:07:15.96483+00:00
-- url     : https://prove2.me/submissions/e87a3d2d-6f27-431f-8170-6c6cb496e205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_isSemiAbelian_Gm
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_nontrivial_Gm_int
import Theorems.Thm_GlobalTheory_ExtUnique_dense_open
import Theorems.Thm_GlobalTheory_ExtUnique_flat_and_isSeparated_of_isSemiAbelian
import Theorems.Thm_GlobalTheory_ExtUnique_pullback_map_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
open scoped TensorProduct
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution : AlgebraicGeometry.IsNoetherian (Sp ℤ) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp ℤ) ∧
    ∃ U : (Sp ℤ).Opens, Dense (U : Set (Sp ℤ)) ∧ U ≠ ⊤ ∧ IsSemiAbelian (Gm (Sp ℤ)) ∧
      Nontrivial (𝟙_ (Over (Sp ℤ)) ⟶ Gm (Sp ℤ)) ∧
      ∀ F₀ : Gm (Sp ℤ) ⟶ Gm (Sp ℤ), IsMonHom F₀ → IsMonHom ((Over.pullback U.ι).map F₀) ∧
        ∃! F : Gm (Sp ℤ) ⟶ Gm (Sp ℤ), IsMonHom F ∧ (Over.pullback U.ι).map F = (Over.pullback U.ι).map F₀ := by
  let U : (Sp ℤ).Opens := PrimeSpectrum.basicOpen (2 : ℤ)
  have hU : Dense (U : Set (Sp ℤ)) :=
    U.isOpen.dense ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℤ), by
      change (2 : ℤ) ∉ (⊥ : Ideal ℤ)
      simp⟩
  refine ⟨inferInstance, GlobalTheory.IsNormalScheme.pred _, U, hU, fun h => ?_, isSemiAbelian_Gm _, nontrivial_Gm_int,
    fun F₀ hF₀ => ⟨inferInstance, F₀, ⟨hF₀, rfl⟩, fun F hF => ?_⟩⟩
  · have h₂ : (⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2 Int.prime_two⟩ : PrimeSpectrum ℤ) ∈
        PrimeSpectrum.basicOpen (2 : ℤ) := by
      change _ ∈ U
      rw [h]
      trivial
    exact h₂ (Ideal.mem_span_singleton_self _)
  · obtain ⟨_, _⟩ := dense_open U hU
    obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian _ (isSemiAbelian_Gm (Sp ℤ))
    exact pullback_map_injective U.ι _ _ hF.2
end GlobalTheory.Published.SemiAbelianHomExtension
