-- Prove2me | solution 1 for GlobalTheory.BorelAlg.eval_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:21.429914+00:00
-- url     : https://prove2.me/submissions/d79e7e60-12d9-44da-9537-d4558db56bf1

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
theorem _root_.solution {T : Type*} [CommRing T] (c : L →+* T)
    (y : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T) (τ : ι) :
    eval₂Hom c (fun p : Lt m => y p.1 p.2.1 p.2.2) (gen m L τ).det = (y τ).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [gen]
end GlobalTheory.BorelAlg
