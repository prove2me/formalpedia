-- Prove2me | solution 1 for GlobalTheory.Cris.hodgeFiltration_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:03.501728+00:00
-- url     : https://prove2.me/submissions/a52657ec-8c36-4304-a1ff-ace0a1c03d3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {I : Ideal R} {I' : Ideal R'}
  {I'' : Ideal R''} {X X' X'' : Scheme.{0}}
attribute [instance] Thick.ring Thick.alg Thick.ring₀
variable {s : X ⟶ Sp R}
namespace GlobalTheory.Cris
theorem _root_.solution (s : X ⟶ Sp R) : F1 s = LinearMap.range (Form.cl s) := by
  apply le_antisymm
  · intro c hc
    rw [F1, LinearMap.mem_ker] at hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [toH1O, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    classical
    obtain ⟨g', hg'⟩ : ∃ g' : C0 (O (dp0 R) s), ∀ (T : Thick (dp0 R) s) (hT : T.J = ⊥), g' T = g ⟨T, hT⟩ :=
      ⟨fun T ↦ if hT : T.J = ⊥ then g ⟨T, hT⟩ else 0, fun T hT ↦ dif_pos hT⟩
    have key : ∀ ⦃T T' : Thick (dp0 R) s⦄ (φ : T ⟶ T') (hT : T.J = ⊥) (hT' : T'.J = ⊥),
        f.1 T T' φ = g' T' - mp (O (dp0 R) s) φ (g' T) := by
      intro T T' φ hT hT'
      have e := congrFun (congrFun (congrFun hg ⟨T, hT⟩) ⟨T', hT'⟩) (ObjectProperty.homMk φ)
      rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
      rw [hg' T hT, hg' T' hT']
      exact e.symm
    refine LinearMap.mem_range.2 ⟨⟨f - ⟨d0 _ g', commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g'⟩, fun T T' φ hT hT' ↦ ?_⟩, ?_⟩
    · show f.1 T T' φ - d0 _ g' T T' φ = 0
      rw [amitsur_d0_apply, key φ hT hT', sub_self]
    · show H1.mk _ (f - ⟨d0 _ g', commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g'⟩) = H1.mk _ f
      exact H1.mk_eq_mk.2 ⟨-g', by rw [map_neg, Submodule.coe_sub, sub_sub_cancel_left]⟩
  · rintro _ ⟨f, rfl⟩
    rw [F1, LinearMap.mem_ker, toH1O]
    show (CoefMap.restrict (O (dp0 R) s) (IsTriv s).ι).pull1 (H1.mk _ f.1) = 0
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
    refine ⟨0, ?_⟩
    rw [map_zero]
    funext T T' φ
    exact (f.2 φ.hom T.2 T'.2).symm
end GlobalTheory.Cris
