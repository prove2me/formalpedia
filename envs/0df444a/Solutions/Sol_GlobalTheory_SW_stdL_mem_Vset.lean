-- Prove2me | solution 1 for GlobalTheory.SW.stdL_mem_Vset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:11:59.897495+00:00
-- url     : https://prove2.me/submissions/4d514282-a477-48a1-8b81-56799ee38ea9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleIndicatorFunctions
import Theorems.Thm_GlobalTheory_SW_mem_stdL
import Theorems.Thm_GlobalTheory_SW_Base_mem_stdL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
namespace GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
private theorem cc_zero_siegel_theta_transformation : cc (0 : E) = 0 := map_zero (IsCMField.complexConj E)
private theorem cc_one' : cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
private theorem isIntegral_cc' {t : E} (ht : IsIntegral ℤ t) : IsIntegral ℤ (cc t) :=
  ht.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
private theorem herm_one_apply (x y : Fin n → E) : herm 1 x y = ∑ a, x a * cc (y a) := by
  simp [herm, Matrix.one_apply]
end
end GlobalTheory.SW
end

set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
namespace GlobalTheory.SW
theorem _root_.solution (M : ℕ) : stdL E n ∈ Vset E n M := by
  refine ⟨Submodule.fg_span (Set.finite_range _), fun x => ?_,
    ⟨1, one_pos, Nat.coprime_one_left M, fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩⟩
  constructor
  · intro hx y hy
    rw [herm_one_apply]
    rw [mem_stdL] at hx hy
    exact IsIntegral.sum _ fun a _ => (hx a).mul (isIntegral_cc' (hy a))
  · intro h
    rw [mem_stdL]
    intro a
    have ha := h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)
    rw [herm_one_apply, Finset.sum_eq_single a (fun b _ hb => by simp [hb, cc_zero_siegel_theta_transformation])
      (by simp)] at ha
    simpa [cc_one'] using ha
end GlobalTheory.SW
