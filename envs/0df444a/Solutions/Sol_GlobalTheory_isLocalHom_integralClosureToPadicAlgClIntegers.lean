-- Prove2me | solution 1 for GlobalTheory.isLocalHom_integralClosureToPadicAlgClIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:52:30.553491+00:00
-- url     : https://prove2.me/submissions/ac00e79c-a9a3-41e3-be03-9b175b71fa37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Theorems.Thm_GlobalTheory_mem_integralClosure_padicInt_iff


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
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory
theorem _root_.solution
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    IsLocalHom (integralClosureToPadicAlgClIntegers K) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have hy' : ((x : K) : PadicAlgCl p) * (y : PadicAlgCl p) = 1 :=
    congrArg (fun z : OO p => (z : PadicAlgCl p)) hy
  have h0 : (x : K) ≠ 0 := by
    intro h0
    rw [h0] at hy'
    simp at hy'
  have hinv : (x : K)⁻¹ ∈ integralClosure ℤ_[p] K := by
    rw [mem_integralClosure_padicInt_iff, IntermediateField.coe_inv,
      ← eq_inv_of_mul_eq_one_right hy']
    exact (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).mp y.2
  exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ h0))
end GlobalTheory
