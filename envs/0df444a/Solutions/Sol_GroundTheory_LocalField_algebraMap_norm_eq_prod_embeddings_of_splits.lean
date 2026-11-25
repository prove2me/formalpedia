-- Prove2me | solution 1 for GroundTheory.LocalField.algebraMap_norm_eq_prod_embeddings_of_splits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:19:58.833603+00:00
-- url     : https://prove2.me/submissions/7c9ec4a1-1ad7-4c3a-af54-242cf60709f7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomTransport
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Abstract IntermediateField
variable (K L Ω : Type*) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
namespace GroundTheory.LocalField
theorem _root_.solution
    (hL : ∀ x : L, ((minpoly K x).map (algebraMap K Ω)).Splits) (x : L) :
    haveI : Fintype (L →ₐ[K] Ω) := Fintype.ofFinite _
    algebraMap K Ω (Algebra.norm K x) = ∏ τ : L →ₐ[K] Ω, τ x := by
  classical
  let _ : Fintype (L →ₐ[K] Ω) := Fintype.ofFinite _
  let ι : Ω →ₐ[K] AlgebraicClosure Ω := IsScalarTower.toAlgHom K Ω (AlgebraicClosure Ω)
  let c : (L →ₐ[K] Ω) → (L →ₐ[K] AlgebraicClosure Ω) := fun τ => ι.comp τ
  have hc : Function.Injective c := fun τ τ' h =>
    AlgHom.ext fun y => ι.toRingHom.injective (AlgHom.congr_fun h y)
  have hcard : Nat.card (L →ₐ[K] Ω) = Nat.card (L →ₐ[K] AlgebraicClosure Ω) := by
    rw [AlgHom.natCard_of_splits K L Ω hL, AlgHom.natCard_of_splits K L _
      (fun _ => IsAlgClosed.splits _)]
  have hbij : Function.Bijective c := by
    refine (Function.Injective.bijective_of_nat_card_le hc hcard.ge)
  apply ι.toRingHom.injective
  change ι (algebraMap K Ω _) = ι (∏ τ : L →ₐ[K] Ω, τ x)
  rw [AlgHom.commutes, map_prod, Algebra.norm_eq_prod_embeddings K (AlgebraicClosure Ω) x]
  exact (Fintype.prod_bijective c hbij _ _ fun τ => rfl).symm
end GroundTheory.LocalField
