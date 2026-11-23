-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.exists_eq_mul_torusPow_iwasawaExponent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:28.114085+00:00
-- url     : https://prove2.me/submissions/ecee6372-8472-47ad-9410-8971e3f876aa

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa

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
theorem _root_.solution (g : GL (Fin n) F) :
    ∃ u ∈ unipotent F n, ∃ k ∈ integralGL F n,
      g = u * torusPow F n (iwasawaExponent F n g) * k := by
  obtain ⟨k, hk, h⟩ := (exists_iwasawa F n g).choose_spec.2.choose_spec
  exact ⟨_, (exists_iwasawa F n g).choose_spec.1, k, hk, h⟩
end GroundTheory.Automorphic.Iwasawa
