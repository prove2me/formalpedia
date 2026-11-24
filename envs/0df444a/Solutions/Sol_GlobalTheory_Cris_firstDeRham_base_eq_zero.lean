-- Prove2me | solution 1 for GlobalTheory.Cris.firstDeRham_base_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:24:25.776868+00:00
-- url     : https://prove2.me/submissions/cd58ecd2-a9c5-4076-84ff-3df0c38e79f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Theorems.Thm_GlobalTheory_CatCoh_H1_eq_zero_of_isInitial


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
variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
namespace GlobalTheory.Cris
theorem _root_.solution (s : X ⟶ Sp R) [IsIso s] (c : FirstDeRham s) : c = 0 := by
  have hx : inv s ≫ s = spMap (algebraMap R R) := by rw [IsIso.inv_hom_id]; exact (spMap_id R).symm
  refine H1.eq_zero_of_isInitial _ (T₀ := Thick.triv R (inv s) hx)
    (Limits.IsInitial.ofUniqueHom (fun T ↦ Thick.trivHom (Algebra.ofId R T.B) ?_) fun T m ↦ ?_) c
  · rw [IsIso.comp_inv_eq]; exact T.w.symm
  · exact Thick.hom_ext fun b ↦ (m.φ.commutes b).trans ((Algebra.ofId R T.B).commutes b).symm
end GlobalTheory.Cris
