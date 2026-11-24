-- Prove2me | solution 1 for GlobalTheory.DenseFibreIso.surjective_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:11:01.085795+00:00
-- url     : https://prove2.me/submissions/1cd41fa8-3a8f-4cfb-a3cb-79b6d7e8c6df

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Theorems.Thm_GlobalTheory_DenseFibreIso_includeLeft_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DenseFibreIso
variable {A : Type} [CommRing A]
variable {B : Type} [CommRing B] [Algebra A B]
namespace GlobalTheory.DenseFibreIso
theorem _root_.solution (S : Type) [CommRing S] [Algebra A S] :
    Function.Surjective (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B) ↔
      Subsingleton (S ⊗[A] (B ⧸ LinearMap.range (Algebra.linearMap A B))) := by
  rw [includeLeft_eq, EquivLike.surjective_comp]
  have hs := LinearMap.lTensor_surjective S (LinearMap.range (Algebra.linearMap A B)).mkQ_surjective
  have hex := lTensor_exact S (LinearMap.exact_map_mkQ_range (Algebra.linearMap A B))
    (LinearMap.range (Algebra.linearMap A B)).mkQ_surjective
  constructor
  · intro h
    refine subsingleton_of_forall_eq 0 fun z => ?_
    obtain ⟨y, rfl⟩ := hs z
    exact (hex y).2 (h y)
  · intro h y
    exact (hex y).1 (Subsingleton.elim _ _)
end GlobalTheory.DenseFibreIso
