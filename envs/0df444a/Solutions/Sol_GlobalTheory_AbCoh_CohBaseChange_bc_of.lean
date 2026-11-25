-- Prove2me | solution 1 for GlobalTheory.AbCoh.CohBaseChange.bc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:07:28.940142+00:00
-- url     : https://prove2.me/submissions/0c1d5100-3daa-4bb3-8a1e-407761992578

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpMapAlgHomAlgebraMap
import Theorems.Thm_GlobalTheory_AbCoh_CohBaseChange_exists_equiv_of_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.CohBaseChange
variable {R : Type} [CommRing R]
namespace GlobalTheory.AbCoh.CohBaseChange
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra R R'] {Z Z' P H H' : Type} [AddCommGroup Z] [Module R Z]
    [AddCommGroup Z'] [Module R' Z'] [AddCommGroup P] [Module R P] [AddCommGroup H] [Module R H]
    [AddCommGroup H'] [Module R' H'] (u : Z →ₗ[R] P) (v : Z' →ₗ[R'] R' ⊗[R] P) (θ : Z →ₗ[R] H)
    (θ' : Z' →ₗ[R'] H') (p : H → H') (hu : Function.Surjective u) (hv : Function.Surjective v)
    (hθ : Function.Surjective θ) (hθ' : Function.Surjective θ') (h : ∀ z, θ z = 0 ↔ u z = 0)
    (h' : ∀ z, v z = 0 ↔ θ' z = 0) (nat : ∀ z, ∃ z', v z' = 1 ⊗ₜ u z ∧ θ' z' = p (θ z)) :
    ∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ c, e (1 ⊗ₜ c) = p c := by
  obtain ⟨e, he⟩ := exists_equiv_of_ker θ u hθ hu h
  obtain ⟨e', he'⟩ := exists_equiv_of_ker v θ' hv hθ' h'
  refine ⟨e.baseChange R R' _ _ ≪≫ₗ e', fun c ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hθ c
  obtain ⟨z', h1, h2⟩ := nat z
  rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, he, ← h1, he', h2]
end GlobalTheory.AbCoh.CohBaseChange
