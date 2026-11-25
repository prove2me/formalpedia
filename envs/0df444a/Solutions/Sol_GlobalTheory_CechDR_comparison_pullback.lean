-- Prove2me | solution 1 for GlobalTheory.CechDR.comparison_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:32:18.956619+00:00
-- url     : https://prove2.me/submissions/c5d645c9-934e-454e-abb1-28ff5eb223d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Theorems.Thm_GlobalTheory_CechDR_pullHyp1_ptCmp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_id
import Theorems.Thm_GlobalTheory_Cris_IsMor_pullCohomologyOne_id


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
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open CatCoh Cris
universe v u v' u'
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
variable (h : φ ≫ s = s' ≫ spMap σ)
variable {h}
namespace GlobalTheory.CechDR
theorem _root_.solution (h : IsMor (dp0 R) s (dp0 R') s' σ φ) (c : FirstDeRham s) :
    IsPull1 h.w (cmp1 s c) (cmp1 s' (h.pull1 c)) := by
  let x' : ∀ p : (Pair φ)ᵒᵖ, Sp ((OPair φ s').obj p) ⟶ X' := fun p ↦ affPt s' p.unop.1.1
  have hx' : ∀ p, x' p ≫ s' = spMap (algebraMap R' ((OPair φ s').obj p)) := fun p ↦ affPt_w s' _
  have hc' : ∀ ⦃p q : (Pair φ)ᵒᵖ⦄ (a : p ⟶ q), spMap (mp (OPair φ s') a : _ →+* _) ≫ x' p = x' q :=
    fun _ _ a ↦ affPt_res s' (Pair.le_fst (leOfHom a.unop))
  refine (pullHyp1_ptCmp _ _ _ x' hx' hc' h (pairPull h.w) (fun p ↦ secPull_affPt s s' p.unop) c).trans ?_
  refine ((pullHyp1_ptCmp _ _ _ x' hx' hc' (IsMor.id _ s') (pairRes φ s') (fun p ↦ ?_) _).trans ?_).symm
  · change spMap (RingHom.id _) ≫ _ = _
    rw [spMap_id, Category.id_comp, Category.comp_id]; rfl
  · rw [IsMor.pullCohomologyOne_id]
end GlobalTheory.CechDR
