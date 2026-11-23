-- Prove2me | solution 1 for GlobalTheory.ThickGlue.surjective_toSpec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:26.610887+00:00
-- url     : https://prove2.me/submissions/df0f8b6a-3afd-4615-9f86-9dccc7e066b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThickGlue
namespace GlobalTheory.ThickGlue
theorem _root_.solution {B₀ : Scheme.{0}} {𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}}
    (p : 𝒜 ⟶ B₀.presheaf) {U : B₀.Opens} (hU : IsAffineOpen U)
    (h : Function.Surjective (p.app (Opposite.op U)).hom)
    (h' : IsNilpotent (RingHom.ker (p.app (Opposite.op U)).hom)) : Surjective (toSpec p U) := by
  have : Surjective (Spec.map (p.app (Opposite.op U))) := by
    constructor
    change Function.Surjective (PrimeSpectrum.comap (p.app (Opposite.op U)).hom)
    rw [← Set.range_eq_univ, range_comap_of_surjective _ _ h,
      PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    obtain ⟨n, hn⟩ := h'
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rwa [hn] at this
  rw [toSpec, ← hU.isoSpec_hom]
  infer_instance
end GlobalTheory.ThickGlue
