-- Prove2me | solution 1 for GlobalTheory.InvExt.special_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:01:49.640992+00:00
-- url     : https://prove2.me/submissions/bb7a15fc-77cf-4271-a1d2-2b5641e8a2e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsInverseExtensionProperClosure
import Theorems.Thm_GlobalTheory_InvExt_range_residue
import Theorems.Thm_GlobalTheory_InvExt_rPt_apply
import Theorems.Thm_GlobalTheory_InvExt_exists_common_residue

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
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.InvExt
variable (C : Core)
variable {C}
namespace GlobalTheory.InvExt
theorem _root_.solution (hF : C.FibLaw) {p : ℕ} [Fact p.Prime] {y y' : Sp (OO p) ⟶ C.Z}
    (τ : C.Test y) (τ' : C.Test y')
    (c : Sp (OO p) ⟶ τ.H.left) (hc : c ≫ τ.H.hom = spMap τ.j)
    (c' : Sp (OO p) ⟶ τ'.H.left) (hc' : c' ≫ τ'.H.hom = spMap τ'.j)
    (h : (c ≫ τ.f) (cPt p) = (c' ≫ τ'.f) (cPt p)) :
    (c ≫ (ι[τ.H]).left ≫ τ.f) (cPt p) = (c' ≫ (ι[τ'.H]).left ≫ τ'.f) (cPt p) := by
  obtain ⟨K, _, _, v, v', hv⟩ := exists_common_residue _ _ h
  let d : Over.mk (v ≫ rPt p ≫ spMap τ.j) ⟶ τ.H := Over.homMk (v ≫ rPt p ≫ c) (by simp [hc])
  let d' : Over.mk (v' ≫ rPt p ≫ spMap τ'.j) ⟶ τ'.H := Over.homMk (v' ≫ rPt p ≫ c') (by simp [hc'])
  have hd : d.left ≫ τ.f = d'.left ≫ τ'.f := by simpa [d, d'] using hv
  have hr : (v ≫ rPt p ≫ spMap τ.j) ≫ τ.y₀ = (v' ≫ rPt p ≫ spMap τ'.j) ≫ τ'.y₀ := by
    have := congrArg (· ≫ C.GG.hom) hv
    simp only [Category.assoc, τ.f_over, τ'.f_over, reassoc_of% hc, reassoc_of% hc'] at this
    simpa using this
  have e := (hF p y y' τ τ' K _ _ (range_residue τ v) (range_residue τ' v') hr d d d' d' hd hd).2
  have e' : v ≫ rPt p ≫ c ≫ (ι[τ.H]).left ≫ τ.f = v' ≫ rPt p ≫ c' ≫ (ι[τ'.H]).left ≫ τ'.f := by
    simpa [Hom.inv_def, d, d'] using e
  obtain ⟨x⟩ : Nonempty (Sp K) := inferInstance
  have := congrArg (fun g => g x) e'
  simp only [Scheme.Hom.comp_apply, rPt_apply] at this
  simpa only [Scheme.Hom.comp_apply] using this
end GlobalTheory.InvExt
