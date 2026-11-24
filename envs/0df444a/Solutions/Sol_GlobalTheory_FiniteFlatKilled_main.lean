-- Prove2me | solution 1 for GlobalTheory.FiniteFlatKilled.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:16.414802+00:00
-- url     : https://prove2.me/submissions/121067a1-9657-4561-8d36-880a99b2a08d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIdPowEqOneOfIsFiniteOfFlat
import Theorems.Thm_GlobalTheory_FiniteFlatKilled_exists_id_pow_eq_one_of_isFinite_of_flat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FiniteFlatKilled
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TensorProduct WithConv
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FiniteFlatKilled
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (H : Over (Spec (CommRingCat.of R)))
    [GrpObj H] [IsCommMonObj H], IsFinite H.hom → Flat H.hom → ∃ N : ℕ, 1 ≤ N ∧ 𝟙 H ^ N = 1 :=
  fun R _ _ H _ _ hf hfl => exists_id_pow_eq_one_of_isFinite_of_flat R H hf hfl
end GlobalTheory.FiniteFlatKilled
