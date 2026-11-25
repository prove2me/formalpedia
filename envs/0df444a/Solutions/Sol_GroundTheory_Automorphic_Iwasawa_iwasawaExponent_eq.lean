-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.iwasawaExponent_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:55.837449+00:00
-- url     : https://prove2.me/submissions/1c8003dc-82a8-49fb-b200-e39d2270e3c1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_iwasawa_unique
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_exists_eq_mul_torusPow_iwasawaExponent

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
theorem _root_.solution {u k : GL (Fin n) F} {l : Fin n → ℤ} (hu : u ∈ unipotent F n)
    (hk : k ∈ integralGL F n) : iwasawaExponent F n (u * torusPow F n l * k) = l := by
  obtain ⟨u', hu', k', hk', h⟩ :=
    exists_eq_mul_torusPow_iwasawaExponent F n (u * torusPow F n l * k)
  exact (iwasawa_unique F n hu' hu hk' hk h.symm).1
end GroundTheory.Automorphic.Iwasawa
