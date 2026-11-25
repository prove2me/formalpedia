-- Prove2me | solution 1 for GlobalTheory.TorsionTheta.tmul_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:27:21.301852+00:00
-- url     : https://prove2.me/submissions/dfe1ee28-1f53-49f8-b920-27952681bfc6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTorsionPointFrobeniusLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TorsionTheta
namespace GlobalTheory.TorsionTheta
theorem _root_.solution {O : Type} [CommRing O] [IsLocalRing O] {H : Type} [CommRing H]
    [Algebra O H] [Module.Finite O H] [Module.Free O H] (l : H)
    (hl : l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H))
    (K : Type) [Field K] [Algebra O K] : l ⊗ₜ[O] (1 : K) ≠ 0 := by
  classical
  intro h0
  let b := Module.Free.chooseBasis O H
  have hex : ∃ i, IsUnit (b.repr l i) := by
    by_contra hne
    push Not at hne
    apply hl
    rw [← b.sum_repr l]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i)))
  obtain ⟨i, hi⟩ := hex
  have h1 := congrArg (fun x => TensorProduct.lid O K (TensorProduct.map (b.coord i) LinearMap.id x)) h0
  simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, map_zero,
    Module.Basis.coord_apply] at h1
  rw [Algebra.smul_def, _root_.mul_one] at h1
  exact (hi.map (algebraMap O K)).ne_zero h1
end GlobalTheory.TorsionTheta
