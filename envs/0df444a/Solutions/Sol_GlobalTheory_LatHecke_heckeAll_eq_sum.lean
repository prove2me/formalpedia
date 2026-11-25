-- Prove2me | solution 1 for GlobalTheory.LatHecke.heckeAll_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:03:08.436358+00:00
-- url     : https://prove2.me/submissions/7a8c9f03-f49e-4f11-b9a6-e71746cbc524

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatHecke
open scoped TensorProduct
variable (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
variable [IsFractionRing O K] (r : ℕ)
variable {O K r}
variable [Finite (IsLocalRing.ResidueField O)]
variable {E : Type} [AddCommMonoid E]
namespace GlobalTheory.LatHecke
theorem _root_.solution (n : ℕ) (φ : Lat O K r → E) (L : Lat O K r) :
    heckeAll n φ L = ∑ M ∈ (subIdx_finite n L).toFinset, φ M :=
  finsum_mem_eq_finite_toFinset_sum φ (subIdx_finite n L)
end GlobalTheory.LatHecke
