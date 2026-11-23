-- Prove2me | solution 1 for GlobalTheory.ZM.exists_arBase_away
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:42.127113+00:00
-- url     : https://prove2.me/submissions/523dc95a-8d3e-4c29-989b-81c6ad4df165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_GoodClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_W8AddTransposeEqE8
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_ExistsArBaseAway

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
noncomputable section
open GlobalTheory GlobalTheory.ZM
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
namespace GlobalTheory.ZM
theorem _root_.solution {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ) {n : ℕ} (hn : n ≠ 0) :
    ∃ em : Localization.Away (n : 𝓞 F) →+* ℂ, ArBase em ∧
      em.comp (algebraMap (𝓞 F) (Localization.Away (n : 𝓞 F))) = φ.comp (algebraMap (𝓞 F) F) := by

  have hn' : (n : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  have hM : Submonoid.powers (n : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hn'
  have : IsDomain (Localization.Away (n : 𝓞 F)) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM

  set ψ : 𝓞 F →+* ℂ := φ.comp (algebraMap (𝓞 F) F) with hψ
  have hu : IsUnit (ψ (n : 𝓞 F)) := by
    rw [map_natCast]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hn)
  have hψinj : Function.Injective ψ :=
    φ.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 F) F)
  refine ⟨IsLocalization.Away.lift (n : 𝓞 F) hu, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact IsLocalization.isDedekindDomain (𝓞 F) hM _
  ·
    convert (inferInstance : Algebra.FiniteType ℤ (Localization.Away (n : 𝓞 F))) <;>
      first | rfl | exact Subsingleton.elim _ _
  · unfold IsLocalization.Away.lift
    rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [(IsLocalization.injective (Localization.Away (n : 𝓞 F)) hM).eq_iff, hψinj.eq_iff]
  · exact IsLocalization.lift_comp _
end GlobalTheory.ZM
