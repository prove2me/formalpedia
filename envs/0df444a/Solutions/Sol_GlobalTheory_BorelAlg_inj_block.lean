-- Prove2me | solution 1 for GlobalTheory.BorelAlg.inj_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:34.383042+00:00
-- url     : https://prove2.me/submissions/5b9415b6-0ff0-4365-8681-3825500550aa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
variable {ι : Type} (m : ι → ℕ) (L : Type) [Field L]
namespace GlobalTheory.BorelAlg
theorem _root_.solution (τ : ι) :
    Function.Injective (fun p : Fin (m τ) × Fin (m τ) => (⟨τ, p⟩ : Lt m)) :=
  sigma_mk_injective (β := fun τ => Fin (m τ) × Fin (m τ))
end GlobalTheory.BorelAlg
