-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.isChar_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:38.880297+00:00
-- url     : https://prove2.me/submissions/42ddf206-51d8-4a30-ae7c-443ff4fb107f

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CuspElliptic
open GlobalTheory GlobalTheory.CuspCharCheck
variable {G : Type} [Group G]
namespace GlobalTheory.CuspCharCheck
theorem _root_.solution (χ : G → ℂ) : IsChar χ ↔ ∃ V : FDRep ℂ G, V.character = χ := by
  constructor
  · rintro ⟨n, ρ, h⟩
    let r : Representation ℂ G (Fin n → ℂ) :=
      (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toMonoidHom.comp ((Units.coeHom _).comp ρ)
    refine ⟨FDRep.of r, funext fun x => ?_⟩
    rw [h]
    exact Matrix.trace_toLin'_eq _
  · rintro ⟨V, rfl⟩
    let b := Module.finBasis ℂ V
    let m : G →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
      (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp V.ρ
    exact ⟨_, m.toHomUnits, fun x => LinearMap.trace_eq_matrix_trace ℂ b _⟩
end GlobalTheory.CuspCharCheck
