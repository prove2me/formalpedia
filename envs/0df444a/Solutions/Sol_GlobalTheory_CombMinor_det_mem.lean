-- Prove2me | solution 1 for GlobalTheory.CombMinor.det_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:31.544229+00:00
-- url     : https://prove2.me/submissions/d4ae31c6-bacf-423b-8603-62acfc859b27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdDetMemHaO

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
open scoped BigOperators
open Classical MvPolynomial Formalism.L2.Pj Formalism.L2.Pj.Crude
open GlobalTheory GlobalTheory.CombMinor
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k]
namespace GlobalTheory.CombMinor
theorem _root_.solution {R : Type} [CommRing R] (S : Subring R) {s : ℕ} (M : Matrix (Fin s) (Fin s) R)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine S.sum_mem fun π _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (S.prod_mem fun i _ => h _ _) _
end GlobalTheory.CombMinor
