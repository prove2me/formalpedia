-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_eq_mul_mul_of_cellMinor_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:43:28.059049+00:00
-- url     : https://prove2.me/submissions/da63824a-df0f-4658-90a8-239331c546f5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_normalForm
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_cellMinor_normalForm
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_eq_of_prod_bottomRows_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {g g' : GL (Fin n) F} {w : Equiv.Perm (Fin n)}
    (hg : bruhatCell g = w) (hg' : bruhatCell g' = w) (h : cellMinor w g = cellMinor w g') :
    ∃ a ∈ Iwasawa.unipotent F n, ∃ b ∈ Iwasawa.unipotent F n, g' = a * g * b := by
  obtain ⟨u, hu, t, v, hv, e⟩ := exists_normalForm g
  obtain ⟨u', hu', t', v', hv', e'⟩ := exists_normalForm g'
  rw [hg] at e
  rw [hg'] at e'
  rw [e, e', cellMinor_normalForm w hu hv, cellMinor_normalForm w hu' hv'] at h
  have ht : t = t' := eq_of_prod_bottomRows_eq fun k => congrFun h k
  subst ht
  refine ⟨u' * u⁻¹, (Iwasawa.unipotent F n).mul_mem hu' ((Iwasawa.unipotent F n).inv_mem hu),
    v⁻¹ * v', (Iwasawa.unipotent F n).mul_mem ((Iwasawa.unipotent F n).inv_mem hv) hv', ?_⟩
  rw [e, e']
  group
end GroundTheory.Automorphic.Whittaker
