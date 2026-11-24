-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.coneHom_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:29:09.366845+00:00
-- url     : https://prove2.me/submissions/359e58d5-3bb0-47e0-8444-48ee8cad511f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
import Theorems.Thm_GlobalTheory_ZH_ConePrime_map_coneHom
import Theorems.Thm_GlobalTheory_ZH_ConePrime_coneHom_mul
import Theorems.Thm_GlobalTheory_ZH_ConePrime_valHom_constHom
import Theorems.Thm_GlobalTheory_ZH_ConePrime_valHom_injective
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_isUnit_iff
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_ratio
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_valR_eq


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
variable {H : LB X} {J : Type} {s : J → H.Sec}
namespace GlobalTheory.ZH.ConePrime
theorem _root_.solution [IsIntegral X] (p : X ⟶ Sp k) {K : Type} [Field K] (y : Sp K ⟶ X)
    (hy : ∀ U : X.Opens, (U : Set X).Nonempty → ⊤ ≤ y ⁻¹ᵁ U) {v : J → K} (hv : Crd H s y v) (i : J)
    (hi : ⊤ ≤ y ⁻¹ᵁ Out.nonzeroLocus (s i)) (r : J → Γ(X, Out.nonzeroLocus (s i)))
    (hr : ∀ j, IsRatio (s j) (s i) _ (r j)) (f : MvPolynomial J k) :
    coneHom (constHom p _) r f = 0 ↔
      coneHom ((evalPt (y ≫ p) ⊤ le_rfl).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) v f = 0 := by
  have hu : v i ≠ 0 := ((crd_isUnit_iff i hv).2 hi).ne_zero
  have e1 : (valHom y _ hi).comp (constHom p _) =
      (evalPt (y ≫ p) ⊤ le_rfl).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    RingHom.ext fun a => valHom_constHom p y _ hi a
  have e2 : v = fun j => valHom y _ hi (r j) * v i :=
    funext fun j => by rw [← valR_eq]; exact crd_ratio hv (hr j) hi
  rw [← e1, e2, coneHom_mul, ← map_coneHom, Polynomial.comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hu),
    Polynomial.map_eq_zero_iff (valHom_injective y hy _ hi)]
end GlobalTheory.ZH.ConePrime
