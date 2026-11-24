-- Prove2me | solution 1 for GlobalTheory.CechDR.isPullForm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:58:12.122942+00:00
-- url     : https://prove2.me/submissions/cb0936e8-b51a-46f0-ac94-fc907b205efa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamCoefMapOneForms_restrictAlongFunctor


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
theorem _root_.solution {ω : GlobForm s} {ω' : GlobForm s'} : IsPullForm h ω ω' ↔
    ∀ p : Pair φ, (semiHom_secPull h p).m1 (ω.1 (op p.1.2)) = ω'.1 (op p.1.1) := by
  have k : ∀ p : (Pair φ)ᵒᵖ, (pullGlob1 (pairRes φ s') ω').1 p = ω'.1 (op p.unop.1.1) := fun p ↦
    cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) p (ω'.1 (op p.unop.1.1))
  have k' : ∀ p : (Pair φ)ᵒᵖ, (pullGlob1 (pairPull h) ω).1 p =
      (semiHom_secPull h p.unop).m1 (ω.1 (op p.unop.1.2)) := fun p ↦ rfl
  refine ⟨fun e p ↦ ?_, fun e ↦ Subtype.ext (funext fun p ↦ ?_)⟩
  · exact (k' (op p)).symm.trans
      ((congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 (op p)) e).trans (k (op p)))
  · exact (k' p).trans ((e p.unop).trans (k p).symm)
end GlobalTheory.CechDR
