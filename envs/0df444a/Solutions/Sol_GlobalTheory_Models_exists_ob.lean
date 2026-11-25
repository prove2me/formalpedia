-- Prove2me | solution 1 for GlobalTheory.Models.exists_ob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:02:20.417239+00:00
-- url     : https://prove2.me/submissions/6c271db8-4746-4d3c-a10e-00171eb11513

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwistedModelAdmissibleCocycles
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
open GlobalTheory GlobalTheory.Models
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1)
variable {k G : Type} [Field k] [Group G]
open scoped LaurentSeries PowerSeries
variable {k G : Type} [Field k] [Group G]
namespace GlobalTheory.Models
namespace _root_.GlobalTheory.Models
theorem _root_.solution {M : Type} [AddCommGroup M] [Module k M]
    [Module.Finite k M] (π : Representation k G M) :
    ∃ (A : _root_.GlobalTheory.Models.Ob k G) (e : M ≃ₗ[k] (Fin A.m → k)),
      ∀ g x, e (π g x) = A.ρ g (e x) := by
  let e : M ≃ₗ[k] (Fin (Module.finrank k M) → k) := (Module.finBasis k M).equivFun
  refine ⟨⟨Module.finrank k M,
    { toFun := fun g => (e : M →ₗ[k] _) ∘ₗ π g ∘ₗ (e.symm : _ →ₗ[k] M)
      map_one' := by ext; simp
      map_mul' := fun g h => by ext; simp }⟩, e, fun g x => ?_⟩
  simp
end _root_.GlobalTheory.Models
end GlobalTheory.Models
