-- Prove2me | solution 1 for GlobalTheory.AbCoh.SplitCx.bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:10:31.266982+00:00
-- url     : https://prove2.me/submissions/146f0568-db60-4677-9c89-b1e194aa884b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomSplitBaseChange

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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.SplitCx
variable {R : Type} [CommRing R]
namespace GlobalTheory.AbCoh.SplitCx
theorem _root_.solution {M0 M1 M2 P : Type} [AddCommGroup M0] [Module R M0] [AddCommGroup M1] [Module R M1]
    [AddCommGroup M2] [Module R M2] [AddCommGroup P] [Module R P]
    (d0 : M0 →ₗ[R] M1) (d1 : M1 →ₗ[R] M2) (π : M1 →ₗ[R] P) (σ : P →ₗ[R] M1)
    (a : M1 →ₗ[R] M0) (b : M2 →ₗ[R] M1)
    (hπσ : π ∘ₗ σ = LinearMap.id) (hπd : π ∘ₗ d0 = 0) (hdσ : d1 ∘ₗ σ = 0)
    (hid : LinearMap.id = σ ∘ₗ π + d0 ∘ₗ a + b ∘ₗ d1) (S : Type) [CommRing S] [Algebra R S] :
    Function.Surjective (fun z : LinearMap.ker (d1.baseChange S) => π.baseChange S z.1) ∧
      ∀ z : LinearMap.ker (d1.baseChange S),
        π.baseChange S z.1 = 0 ↔ z.1 ∈ LinearMap.range (d0.baseChange S) := by
  have e1 : ∀ y, π.baseChange S (σ.baseChange S y) = y := fun y => by
    have := congrArg (LinearMap.baseChange S) hπσ
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at this
    exact LinearMap.congr_fun this y
  have e2 : ∀ y, π.baseChange S (d0.baseChange S y) = 0 := fun y => by
    have := congrArg (LinearMap.baseChange S) hπd
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_zero] at this
    exact LinearMap.congr_fun this y
  have e3 : ∀ y, d1.baseChange S (σ.baseChange S y) = 0 := fun y => by
    have := congrArg (LinearMap.baseChange S) hdσ
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_zero] at this
    exact LinearMap.congr_fun this y
  have e4 : ∀ y, y = σ.baseChange S (π.baseChange S y) + d0.baseChange S (a.baseChange S y)
      + b.baseChange S (d1.baseChange S y) := fun y => by
    have := congrArg (LinearMap.baseChange S) hid
    rw [LinearMap.baseChange_id, LinearMap.baseChange_add, LinearMap.baseChange_add,
      LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.baseChange_comp] at this
    exact LinearMap.congr_fun this y
  refine ⟨fun y => ⟨⟨σ.baseChange S y, e3 y⟩, e1 y⟩, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · refine ⟨a.baseChange S z.1, ?_⟩
    have h0 : d1.baseChange S z.1 = 0 := z.2
    have := e4 z.1
    rw [hz, h0, map_zero, map_zero, zero_add, add_zero] at this
    exact this.symm
  · rintro ⟨w, hw⟩
    rw [← hw]; exact e2 w
end GlobalTheory.AbCoh.SplitCx
