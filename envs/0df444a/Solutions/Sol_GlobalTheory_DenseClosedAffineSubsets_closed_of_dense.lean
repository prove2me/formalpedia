-- Prove2me | solution 1 for GlobalTheory.DenseClosedAffineSubsets.closed_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:11:04.065862+00:00
-- url     : https://prove2.me/submissions/79d7ab4b-b2c8-448c-b7a5-a7c343d09f0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
namespace GlobalTheory.DenseClosedAffineSubsets
theorem _root_.solution {V X T D Y : Scheme.{0}} (p : T ⟶ D) [IsSeparated p] (ι : X ⟶ T)
    [IsClosedImmersion ι] (j : V ⟶ X) [IsSchemeTheoreticallyDominant j] (e : Y ⟶ T)
    [IsClosedImmersion (e ≫ p)] (v : V ⟶ Y) (hv : v ≫ e = j ≫ ι) :
    IsClosedImmersion (ι ≫ p) := by
  have : IsClosedImmersion e := IsClosedImmersion.of_comp e p
  have hk : e.ker ≤ ι.ker := by
    have h1 : (j ≫ ι).ker = ι.ker := by
      rw [Scheme.Hom.ker_comp, j.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [← h1, ← hv]
    exact Scheme.Hom.le_ker_comp v e
  have hl := IsClosedImmersion.lift_fac e ι hk
  have : IsClosedImmersion (IsClosedImmersion.lift e ι hk ≫ e) := by rw [hl]; infer_instance
  have : IsClosedImmersion (IsClosedImmersion.lift e ι hk) :=
    IsClosedImmersion.of_comp_isClosedImmersion _ e
  rw [← hl, Category.assoc]
  infer_instance
end GlobalTheory.DenseClosedAffineSubsets
