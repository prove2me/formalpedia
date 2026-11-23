-- Prove2me | solution 1 for GlobalTheory.GenTorsor.pb_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:04.941806+00:00
-- url     : https://prove2.me/submissions/60042098-10aa-48a7-9d5a-ea4cfa9309b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenTorsor
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.GenTorsor
theorem _root_.solution (a : Y ⟶ X) [IsOpenImmersion a] {U : X.Opens} (hU : U ≤ a.opensRange)
    {W : Y.Opens} (h : W = a ⁻¹ᵁ U) : Function.Bijective (pb a U W h.le) := by
  subst h
  have := a.isIso_app U hU
  have e : a.appLE U (a ⁻¹ᵁ U) le_rfl = a.app U := (a.app_eq_appLE).symm
  have h2 : pb a U (a ⁻¹ᵁ U) le_rfl =
      (Units.mapEquiv (asIso (a.app U)).commRingCatIsoToRingEquiv.toMulEquiv).toMonoidHom := by
    ext x
    change (a.appLE U (a ⁻¹ᵁ U) le_rfl).hom _ = _
    rw [e]; rfl
  rw [h2]
  exact (Units.mapEquiv _).bijective
end GlobalTheory.GenTorsor
