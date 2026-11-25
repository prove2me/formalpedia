-- Prove2me | solution 1 for GlobalTheory.exists_clopen_integral_of_smooth_over_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:33.78628+00:00
-- url     : https://prove2.me/submissions/cccf993d-623f-45be-9b26-19c878bf3615

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsClopenIntegralOfSmoothOverField
import Theorems.Thm_GlobalTheory_isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F : Type) [Field F] (Z : Scheme.{0}) (q : Z ⟶ Sp F), Smooth q → ∀ z : Z,
      ∃ (W' : Scheme.{0}) (j : W' ⟶ Z), IsClosedImmersion j ∧ IsOpenImmersion j ∧ IsIntegral W' ∧
        z ∈ Set.range j := by
  intro F _ Z q hq z
  obtain ⟨hR, hN, hL⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F Z q hq
  have : GlobalTheory.IsNormalScheme Z := by first | exact hN | exact IsNormalScheme.of_pred hN
  have hC : irreducibleComponent z ∈ irreducibleComponents Z := irreducibleComponent_mem_irreducibleComponents z
  let C : Z.Opens := ⟨irreducibleComponent z, IsNormalScheme.isOpen_of_mem_irreducibleComponents hC⟩
  have hzC : z ∈ C := mem_irreducibleComponent
  have hrange : Set.range C.ι = (C : Set Z) := Scheme.Opens.range_ι C
  refine ⟨C.toScheme, C.ι, ?_, inferInstance, ?_, by rw [hrange]; exact hzC⟩
  · apply IsClosedImmersion.of_isPreimmersion
    rw [hrange]
    exact isClosed_of_mem_irreducibleComponents _ hC
  · have : IrreducibleSpace C := Subtype.irreducibleSpace isIrreducible_irreducibleComponent
    have : Nonempty C := ⟨⟨z, hzC⟩⟩
    exact isIntegral_of_irreducibleSpace_of_isReduced C.toScheme
end GlobalTheory
