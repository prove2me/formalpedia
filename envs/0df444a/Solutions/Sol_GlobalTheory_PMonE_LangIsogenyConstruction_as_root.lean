-- Prove2me | solution 1 for GlobalTheory.PMonE.LangIsogenyConstruction.as_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:17:33.029804+00:00
-- url     : https://prove2.me/submissions/c3391535-fa28-4e34-b073-19ddb65d8d7c

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
theorem _root_.solution (q : ℕ) (hq : 1 < q) (c : k) : ∃ z : k, z ^ q - z = c := by
  have hdeg : (X ^ q - (X + C c) : k[X]).degree = q := by
    rw [degree_sub_eq_left_of_degree_lt, degree_X_pow]
    rw [degree_X_pow, degree_X_add_C]
    exact_mod_cast hq
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (X ^ q - (X + C c) : k[X]) (by
    rw [hdeg]; exact_mod_cast (by omega : q ≠ 0))
  have h2 : (X ^ q - (X + C c) : k[X]).eval z = 0 := hz
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h2
  exact ⟨z, by linear_combination h2⟩
end GlobalTheory.PMonE.LangIsogenyConstruction
