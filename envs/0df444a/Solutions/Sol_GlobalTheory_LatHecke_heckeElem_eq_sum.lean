-- Prove2me | solution 1 for GlobalTheory.LatHecke.heckeElem_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:59:27.853116+00:00
-- url     : https://prove2.me/submissions/84dc1cde-7368-4141-92b1-060322560e21

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
theorem _root_.solution (k : ℕ) (φ : Lat O K r → E) (L : Lat O K r) :
    heckeElem k φ L = ∑ M ∈ (subElem_finite k L).toFinset, φ M :=
  finsum_mem_eq_finite_toFinset_sum φ (subElem_finite k L)
end GlobalTheory.LatHecke
