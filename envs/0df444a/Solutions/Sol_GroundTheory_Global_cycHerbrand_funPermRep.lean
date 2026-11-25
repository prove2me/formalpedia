-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_funPermRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:04.332798+00:00
-- url     : https://prove2.me/submissions/3e88a55f-9b63-46eb-bda7-47bf90cca4be

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Theorems.Thm_GroundTheory_Global_funEquivMonoidAlgebra_funPermRep
import Theorems.Thm_GroundTheory_Global_cycHerbrand_congr
import Theorems.Thm_GroundTheory_Global_cyclicHerbrand_eq_cycHerbrand
import Theorems.Thm_GroundTheory_Global_cyclicHerbrand_ofMulAction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MulAction NumberField IsDedekindDomain
open scoped Pointwise
noncomputable section
variable (k G X : Type*) [CommRing k] [Group G] [MulAction G X]
variable {k G X}
namespace GroundTheory.Global
theorem _root_.solution [Fintype G] [Finite X] [Fintype (orbitRel.Quotient G X)] {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (funPermRep ℤ G X) σ =
      ∏ ω : orbitRel.Quotient G X, (Nat.card (stabilizer G (Quotient.out ω)) : ℚ) := by
  rw [cycHerbrand_congr funEquivMonoidAlgebra funEquivMonoidAlgebra_funPermRep σ,
    ← cyclicHerbrand_eq_cycHerbrand, cyclicHerbrand_ofMulAction hσ]
end GroundTheory.Global
