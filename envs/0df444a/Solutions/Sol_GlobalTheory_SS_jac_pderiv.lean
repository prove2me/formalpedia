-- Prove2me | solution 1 for GlobalTheory.SS.jac_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:41:04.874118+00:00
-- url     : https://prove2.me/submissions/9bab70ef-9b9a-4468-b169-98d082522d44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Theorems.Thm_GlobalTheory_SS_VF_ofDerivation_fnOn

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
noncomputable section
open GlobalTheory GlobalTheory.SS
variable (R : Type) [CommRing R] {K : Type} [Field K] [Algebra R K]
variable {R} {A A' : Over (Sp K)}
variable {B : Type} [CommRing B] [Algebra K B]
namespace GlobalTheory.SS
theorem _root_.solution (n : ℕ) (U : (Sp (MvPolynomial (Fin n) K)).Opens) :
    jac (A := Over.mk (spMap (algebraMap K (MvPolynomial (Fin n) K))))
      (fun i : Fin n => VF.ofDerivation (MvPolynomial.pderiv i)) U
      (fun j => fnOn _ U (MvPolynomial.X j)) = 1 := by
  unfold jac
  convert Matrix.det_one (n := Fin n)
  ext i j
  rw [Matrix.of_apply, VF.ofDerivation_fnOn, MvPolynomial.pderiv_X, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]
end GlobalTheory.SS
