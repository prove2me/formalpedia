-- Prove2me | solution 1 for GlobalTheory.ThetaClaimsCompare.minor_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:51.951053+00:00
-- url     : https://prove2.me/submissions/547a6b8d-96a6-40f4-b30f-1f76f719eea0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos

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
open GlobalTheory GlobalTheory.ThetaClaimsCompare
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (col : ∀ σ, Fin (r σ) → Fin n)
namespace GlobalTheory.ThetaClaimsCompare
theorem _root_.solution (w : (Σ σ, Fin (r σ)) → ℕ) (σ : T) (s : Fin (r σ)) :
    (minor r n col k σ s).IsWeightedHomogeneous (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
      (∑ j : Fin (s + 1), w ⟨σ, Fin.castLE s.isLt j⟩) := by
  rw [minor, Matrix.det_apply']
  refine IsWeightedHomogeneous.sum _ _ _ fun g _ => ?_
  have h := IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
    (Finset.univ : Finset (Fin (s + 1)))
    (fun j => (X ⟨σ, Fin.castLE s.isLt (g j), col σ (Fin.castLE s.isLt j)⟩ : MvPolynomial (Letter T r n) k))
    (fun j => w ⟨σ, Fin.castLE s.isLt (g j)⟩) (fun j _ => isWeightedHomogeneous_X _ _ _)
  rw [Equiv.sum_comp g (fun j => w ⟨σ, Fin.castLE s.isLt j⟩)] at h
  have h2 := (isWeightedHomogeneous_C (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
    (((Equiv.Perm.sign g : ℤˣ) : ℤ) : k)).mul h
  simpa using h2
end GlobalTheory.ThetaClaimsCompare
