-- Prove2me | solution 1 for GroundTheory.Global.SUnit.index_range_powMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:45:31.387286+00:00
-- url     : https://prove2.me/submissions/4b670147-f81f-450b-9741-52dd5d1e2415

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_ExistenceTheorem_PowerIndex
import Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_eq_pow_mul
import Theorems.Thm_GroundTheory_Global_SUnit_finrank_quotient_torsion
import Theorems.Thm_GroundTheory_Global_SUnit_dvd_natCard_torsion

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
open NumberField IsDedekindDomain Module
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
open GroundTheory.Global.SUnit
namespace GroundTheory.Global.SUnit
theorem _root_.solution (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] [Finite S] :
    (powMonoidHom n : S.unit K →* S.unit K).range.index =
      n ^ (Fintype.card (InfinitePlace K) + Nat.card S) := by
  have hpos : 0 < InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  rw [index_range_powMonoidHom_eq_pow_mul (NeZero.ne n), finrank_quotient_torsion,
    IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right (dvd_natCard_torsion S n), ← pow_succ,
    Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  congr 1
  omega
end GroundTheory.Global.SUnit
