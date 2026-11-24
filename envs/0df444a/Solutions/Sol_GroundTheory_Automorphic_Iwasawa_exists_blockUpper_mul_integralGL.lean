-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:43:17.846507+00:00
-- url     : https://prove2.me/submissions/21f45042-0ff1-4eea-8a55-12ddcb6fbcdb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_borel_le_blockUpper

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
theorem _root_.solution {α : Type*} [LinearOrder α] {β : Fin n → α}
    (hβ : Monotone β) (g : GL (Fin n) F) :
    ∃ p ∈ blockUpper F n β, ∃ k ∈ integralGL F n, g = p * k := by
  obtain ⟨b, hb, k, hk, rfl⟩ := exists_borel_mul_integralGL F n g
  exact ⟨b, borel_le_blockUpper F n hβ hb, k, hk, rfl⟩
end GroundTheory.Automorphic.Iwasawa
