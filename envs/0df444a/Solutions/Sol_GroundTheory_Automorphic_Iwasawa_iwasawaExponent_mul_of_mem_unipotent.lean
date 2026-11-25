-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.iwasawaExponent_mul_of_mem_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:46.814144+00:00
-- url     : https://prove2.me/submissions/dbbba93f-850c-4e32-941b-f1d1a90ad837

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_exists_eq_mul_torusPow_iwasawaExponent
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_iwasawaExponent_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Iwasawa
theorem _root_.solution {u : GL (Fin n) F} (hu : u ∈ unipotent F n)
    (g : GL (Fin n) F) : iwasawaExponent F n (u * g) = iwasawaExponent F n g := by
  obtain ⟨u', hu', k', hk', h⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
  conv_lhs => rw [h, ← mul_assoc, ← mul_assoc]
  exact iwasawaExponent_eq F n ((unipotent F n).mul_mem hu hu') hk'
end GroundTheory.Automorphic.Iwasawa
