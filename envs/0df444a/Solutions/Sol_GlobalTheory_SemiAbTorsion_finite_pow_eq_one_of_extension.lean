-- Prove2me | solution 1 for GlobalTheory.SemiAbTorsion.finite_pow_eq_one_of_extension
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:49.916817+00:00
-- url     : https://prove2.me/submissions/48fe0cf2-4cc3-409f-b221-8587209a8200

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.SemiAbTorsion
namespace GlobalTheory.SemiAbTorsion
theorem _root_.solution {T G B : Type*} [Group T] [CommGroup G] [Group B]
    (i : T →* G) (q : G →* B) (hi : Function.Injective i) (hk : ∀ x, q x = 1 → ∃ t, i t = x)
    (n : ℕ) (hT : Finite {t : T // t ^ n = 1}) (hB : Finite {b : B // b ^ n = 1}) :
    Finite {x : G // x ^ n = 1} := by
  let f : {x : G // x ^ n = 1} → {b : B // b ^ n = 1} :=
    fun x => ⟨q x.1, by rw [← map_pow, x.2, map_one]⟩
  refine Set.finite_univ_iff.mp (Set.Finite.of_finite_fibers f (Set.toFinite _) fun b hb => ?_)
  obtain ⟨x₀, -, rfl⟩ := hb
  rw [Set.univ_inter, ← Set.finite_coe_iff]
  have key : ∀ x : f ⁻¹' {f x₀}, ∃ t : {t : T // t ^ n = 1}, i t.1 = x.1.1 / x₀.1 := by
    intro x
    have hx : q x.1.1 = q x₀.1 := congrArg Subtype.val x.2
    obtain ⟨t, ht⟩ := hk (x.1.1 / x₀.1) (by rw [map_div, hx, div_self'])
    refine ⟨⟨t, hi ?_⟩, ht⟩
    rw [map_pow, ht, div_pow, x.1.2, x₀.2, map_one, div_one]
  choose g hg using key
  refine Finite.of_injective g fun x y h => Subtype.ext (Subtype.ext ?_)
  have := hg x
  rw [h, hg y] at this
  exact (div_left_inj.mp this).symm
end GlobalTheory.SemiAbTorsion
