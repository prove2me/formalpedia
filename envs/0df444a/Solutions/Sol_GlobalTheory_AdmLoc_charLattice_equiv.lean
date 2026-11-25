-- Prove2me | solution 1 for GlobalTheory.AdmLoc.charLattice_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:42:42.538282+00:00
-- url     : https://prove2.me/submissions/73382385-b1df-4d18-907d-a7cd745f9781

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdmLoc
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)
open scoped Pointwise
variable {G : Type} [Group G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
variable {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}
namespace GlobalTheory.AdmLoc
theorem _root_.solution (hinj : Function.Injective (algebraMap O LL)) (χ : G →* Oˣ) :
    ∃ e : O ≃ₗ[O] ↥(charLattice hinj χ).T, (∀ a, (e a : LL) = algebraMap O LL a) ∧
      ∀ g a, e (scalRep O χ g a) = latRep (charLattice hinj χ) g (e a) := by
  refine ⟨LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj, fun _ => rfl, fun g a => Subtype.ext ?_⟩
  change algebraMap O LL ((χ g : O) • a) = algebraMap O LL (χ g) • algebraMap O LL a
  simp
end GlobalTheory.AdmLoc
