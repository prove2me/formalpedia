-- Prove2me | solution 1 for GlobalTheory.UU.ExpLin.sum_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:28.923925+00:00
-- url     : https://prove2.me/submissions/7b40a9dc-3f47-4916-8b1a-873559fa7509

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalSecComb

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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ExpLin
namespace GlobalTheory.UU.ExpLin
theorem _root_.solution {S X : Type} [CommRing S] [DecidableEq X] {n : ℕ} (w : S) (c a : Fin n → S) (s : Fin n → Finset X)
    (b : Fin n → X → S) (t : X → S) (h₀ : ∀ i, ∀ α ∉ s i, b i α = 0) (h : ∀ i, w * a i = ∑ α ∈ s i, b i α * t α) :
    w * ∑ i, c i * a i = ∑ α ∈ Finset.univ.biUnion s, (∑ i, c i * b i α) * t α := by
  simp only [Finset.sum_mul]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, h i, Finset.mul_sum]
  simp only [_root_.mul_assoc]
  refine Finset.sum_subset (Finset.subset_biUnion_of_mem s (Finset.mem_univ i)) fun α _ hα => ?_
  rw [h₀ i α hα, zero_mul, mul_zero]
end GlobalTheory.UU.ExpLin
