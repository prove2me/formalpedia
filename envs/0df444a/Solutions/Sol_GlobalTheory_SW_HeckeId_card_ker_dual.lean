-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.card_ker_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:26:14.055244+00:00
-- url     : https://prove2.me/submissions/48259927-118b-4ad2-aca9-aa4c7d7f054d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution (F V W : Type) [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] [FiniteDimensional F V] [FiniteDimensional F W] (g : V →ₗ[F] W) :
    Nat.card (LinearMap.ker g) * Nat.card F ^ Module.finrank F W =
      Nat.card (LinearMap.ker g.dualMap) * Nat.card F ^ Module.finrank F V := by
  have h1 := g.finrank_range_add_finrank_ker
  have h2 := g.dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at h2
  rw [Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker g),
    Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker g.dualMap), ← pow_add, ← pow_add]
  congr 1
  omega
end GlobalTheory.SW.HeckeId
