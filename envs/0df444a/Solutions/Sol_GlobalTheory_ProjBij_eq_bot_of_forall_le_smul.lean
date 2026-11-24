-- Prove2me | solution 1 for GlobalTheory.ProjBij.eq_bot_of_forall_le_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:41:27.066348+00:00
-- url     : https://prove2.me/submissions/39b70ac2-aee1-4d0b-8a9d-b54c1c09c133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfInjectiveModMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.ProjBij
namespace GlobalTheory.ProjBij
theorem _root_.solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K : Submodule R M) (hK : K.FG) (h : ∀ m : Ideal R, m.IsMaximal → K ≤ m • K) : K = ⊥ := by
  rw [← Submodule.annihilator_eq_top_iff]
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨r, hr, hr0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m K hK (h m hm)
  have h1 : r ∈ m := hle (Submodule.mem_annihilator.2 hr0)
  apply hm.ne_top
  rw [Ideal.eq_top_iff_one]
  have := m.sub_mem h1 hr
  simpa using this
end GlobalTheory.ProjBij
