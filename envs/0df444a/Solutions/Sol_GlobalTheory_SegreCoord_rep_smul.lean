-- Prove2me | solution 1 for GlobalTheory.SegreCoord.rep_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:09:33.783871+00:00
-- url     : https://prove2.me/submissions/a5af5f1f-1f1c-4e52-a47a-79947c0a3939

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Theorems.Thm_GlobalTheory_SegreCoord_loc_of_secCoord
import Theorems.Thm_GlobalTheory_SegreCoord_secCoord_of_loc
import Theorems.Thm_GlobalTheory_SegreCoord_Loc_smul
import Theorems.Thm_GlobalTheory_SegreCoord_unimod_map
import Theorems.Thm_GlobalTheory_SegreCoord_unimod_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
variable {R : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {s : X ⟶ Sp R} (H : ProjRep I s M th)
include H
namespace GlobalTheory.SegreCoord
theorem _root_.solution {β : R →+* T} {v : σ → T} (hv : Ideal.span (Set.range v) = ⊤)
    (h : ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) (t : T) :
    ∀ F ∈ I, MvPolynomial.eval₂ β (fun i => t * v i) F = 0 := by
  intro F hF
  let L := Localization.Away (Polynomial.X : Polynomial T)
  let φ : T →+* L := (algebraMap (Polynomial T) L).comp Polynomial.C
  have hu : IsUnit (algebraMap (Polynomial T) L Polynomial.X) := IsLocalization.Away.algebraMap_isUnit _
  obtain ⟨x, ⟨hx, hc⟩, -⟩ := H.2.2 L (φ.comp β) (fun i => φ (v i)) (unimod_map hv φ) fun G hG => by
    have := MvPolynomial.eval₂_comp_left φ β v G
    rw [h G hG, map_zero] at this
    exact this.symm
  have h1 := (H.2.1 L _ x _ hx (secCoord_of_loc (unimod_smul (unimod_map hv φ) hu)
    ((loc_of_secCoord hc).smul hu))).2 F hF
  have h2 : MvPolynomial.eval₂ (Polynomial.C.comp β) (fun i => Polynomial.X * Polynomial.C (v i)) F = 0 := by
    apply IsLocalization.injective L (M := Submonoid.powers (Polynomial.X : Polynomial T))
      (Submonoid.powers_le.2 Polynomial.X_mem_nonzeroDivisors)
    rw [MvPolynomial.eval₂_comp_left, map_zero, ← h1]
    congr 1
    funext i
    exact map_mul _ _ _
  have h3 := congrArg (Polynomial.evalRingHom t) h2
  rw [MvPolynomial.eval₂_comp_left, map_zero] at h3
  rw [← h3]
  congr 1
  · ext; simp
  · funext i; simp only [Function.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
end GlobalTheory.SegreCoord
