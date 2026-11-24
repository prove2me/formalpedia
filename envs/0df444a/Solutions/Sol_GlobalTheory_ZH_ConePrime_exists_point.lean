-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.exists_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:50.724147+00:00
-- url     : https://prove2.me/submissions/d6c1e102-e3c6-4b48-a582-cb979e8f089c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
import Theorems.Thm_GlobalTheory_ZH_ConePrime_valHom_constHom
import Theorems.Thm_GlobalTheory_TangentOrigin_eq_spMap_of_evalPt
import Theorems.Thm_GlobalTheory_TangentOrigin_exists_evalPt_eq


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin
variable {k : Type} [Field k] {X : Scheme.{0}}
namespace GlobalTheory.ZH.ConePrime
theorem _root_.solution (p : X ⟶ Sp k) {U : X.Opens} (hU : IsAffineOpen U) (e : Γ(X, U) →+* k)
    (he : ∀ a, e (constHom p U a) = a) :
    ∃ (x : Sp k ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ ∧ valHom x U h = e := by
  obtain ⟨x, h, hx⟩ := exists_evalPt_eq hU e
  refine ⟨x, h, ?_, hx⟩
  have e' : 𝟙 (Sp k) = spMap (RingHom.id k) := (Spec.map_id _).symm
  rw [e']
  refine eq_spMap_of_evalPt _ _ fun a => ?_
  rw [← valHom_constHom p x U h]
  exact (RingHom.congr_fun hx _).trans (he a)
end GlobalTheory.ZH.ConePrime
