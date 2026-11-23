-- Prove2me | solution 1 for GlobalTheory.PMonE.LangIsogenyConstruction.langX_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:24.290482+00:00
-- url     : https://prove2.me/submissions/cc1b77ac-cfd4-44bc-9221-e4fdbc63d3fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangXRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LangIsogenyConstruction
open Polynomial
variable {k V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
namespace GlobalTheory.PMonE.LangIsogenyConstruction
theorem _root_.solution (q : ℕ) (hq : 1 < q) (a : ℕ → k) (i : ℕ) : (X : k[X]) ^ q ∣ langX q a i := by
  induction i with
  | zero => exact Dvd.intro_left _ rfl
  | succ i ih =>
    exact dvd_add (ih.trans (dvd_pow_self _ (by omega))) (Dvd.intro_left _ rfl)
end GlobalTheory.PMonE.LangIsogenyConstruction
