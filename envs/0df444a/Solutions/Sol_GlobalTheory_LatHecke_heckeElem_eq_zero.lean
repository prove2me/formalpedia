-- Prove2me | solution 1 for GlobalTheory.LatHecke.heckeElem_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:59:29.125103+00:00
-- url     : https://prove2.me/submissions/fceb27f1-4ee1-4841-b7c0-4aef6c49ff9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt
import Theorems.Thm_GlobalTheory_LatHecke_subElem_eq_empty

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
theorem _root_.solution {k : ℕ} (hk : r < k) (φ : Lat O K r → E) (L : Lat O K r) :
    heckeElem k φ L = 0 := by
  simp [heckeElem, subElem_eq_empty hk]
end GlobalTheory.LatHecke
