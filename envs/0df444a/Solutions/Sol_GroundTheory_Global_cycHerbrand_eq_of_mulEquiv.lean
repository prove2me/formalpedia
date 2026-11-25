-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_eq_of_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:12:58.647808+00:00
-- url     : https://prove2.me/submissions/c50d24ff-6f0b-429e-a219-88fc69407114

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.GroupCoh
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {k H G V W : Type*} [CommRing k] [Group H] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ' : Representation k H V} {ρ : Representation k G W}
variable [Fintype H] [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution (e : H ≃* G) (f : V ≃+ W)
    (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x)) (τ : H) :
    (HasHerbrandQuotient (cycSubOne ρ' τ) (cycNorm ρ') ↔
      HasHerbrandQuotient (cycSubOne ρ (e τ)) (cycNorm ρ)) ∧
    cycHerbrand ρ' τ = cycHerbrand ρ (e τ) := by
  have e0 := (cycTateZeroEquivOfMulEquiv e f hf τ).toEquiv
  have e1 := (cycTateNegOneEquivOfMulEquiv e f hf τ).toEquiv
  refine ⟨?_, ?_⟩
  · exact ⟨fun h ↦ ⟨Finite.of_equiv _ e0 (h := h.1), Finite.of_equiv _ e1 (h := h.2)⟩,
      fun h ↦ ⟨Finite.of_equiv _ e0.symm (h := h.1), Finite.of_equiv _ e1.symm (h := h.2)⟩⟩
  · rw [cycHerbrand_eq, cycHerbrand_eq, Nat.card_congr e0, Nat.card_congr e1]
end GroundTheory.Global
