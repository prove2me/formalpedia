-- Prove2me | solution 1 for GlobalTheory.PrimSec.isPrime_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:49:50.291037+00:00
-- url     : https://prove2.me/submissions/241dc92f-18f1-414c-a4fd-6090cafc559e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
import Theorems.Thm_GlobalTheory_PrimSec_isPushout_app
import Theorems.Thm_GlobalTheory_PrimSec_app_cst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.PrimSec
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
namespace GlobalTheory.PrimSec
theorem _root_.solution [IsLocalRing R] (f : X ⟶ Spec (CommRingCat.of R)) [GeometricallyIntegral f] {V : X.Opens}
    (hV : IsAffineOpen V) {x : X} (hx : x ∈ V) (hfx : f x = IsLocalRing.closedPoint R) :
    ((IsLocalRing.maximalIdeal R).map (AbLaw.cst f V)).IsPrime := by
  let g := IsLocalRing.residue R
  let t := Spec.map (CommRingCat.ofHom g)
  have H := IsPullback.of_hasPullback f t
  haveI : IsIntegral (pullback f t) :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ H
  have po := isPushout_app H hV
  have hne : Nonempty (pullback.fst f t ⁻¹ᵁ V) := by
    have : x ∈ Set.range (pullback.fst f t) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨IsLocalRing.closedPoint _, ?_⟩
      rw [hfx]
      exact IsLocalRing.comap_closedPoint g
    obtain ⟨y, rfl⟩ := this
    exact ⟨⟨y, hx⟩⟩
  have hk : RingHom.ker ((pullback.fst f t).app V).hom = (IsLocalRing.maximalIdeal R).map (AbLaw.cst f V) := by
    apply le_antisymm
    · intro b hb
      let I := (IsLocalRing.maximalIdeal R).map (AbLaw.cst f V)
      let q : IsLocalRing.ResidueField R →+* Γ(X, V) ⧸ I :=
        Ideal.quotientMap I (AbLaw.cst f V) Ideal.le_comap_map
      have e := congrArg (fun φ => φ.hom b) (po.inl_desc (CommRingCat.ofHom (Ideal.Quotient.mk I))
        (CommRingCat.ofHom q) (by ext a; rfl))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
      rw [RingHom.mem_ker.1 hb, map_zero] at e
      exact Ideal.Quotient.eq_zero_iff_mem.1 e.symm
    · refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
      change ((pullback.fst f t).app V).hom (AbLaw.cst f V a) = 0
      rw [app_cst H.w, show g a = 0 from (IsLocalRing.residue_eq_zero_iff a).2 ha, map_zero]
  rw [← hk]
  exact RingHom.ker_isPrime _
end GlobalTheory.PrimSec
