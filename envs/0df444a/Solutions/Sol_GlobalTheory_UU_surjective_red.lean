-- Prove2me | solution 1 for GlobalTheory.UU.surjective_red
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:27.1018+00:00
-- url     : https://prove2.me/submissions/5072b120-7aca-4f0a-ac07-a1b6a20def7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat

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
noncomputable section
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution {A : Type} [CommRing A] {J : Ideal A} (hJ : IsNilpotent J) :
    Surjective (red J) := by
  rw [surjective_iff]
  intro x
  have hx : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    obtain ⟨n, hn⟩ := hJ
    intro a ha
    have hpow : a ^ n ∈ J ^ n := Ideal.pow_mem_pow ha n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hpow
    exact x.isPrime.mem_of_pow_mem n (by rw [hpow]; exact zero_mem _)
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩
end GlobalTheory.UU
