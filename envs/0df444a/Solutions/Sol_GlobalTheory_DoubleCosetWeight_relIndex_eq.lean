-- Prove2me | solution 1 for GlobalTheory.DoubleCosetWeight.relIndex_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:04:42.238209+00:00
-- url     : https://prove2.me/submissions/e52c78f3-ada0-4958-a9a4-8eb18c8a3a7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetRelIndexInfConjConst
import Theorems.Thm_GlobalTheory_DoubleCosetWeight_inf_map_conj_mul_eq
import Theorems.Thm_GlobalTheory_DoubleCosetWeight_gen_map_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DoubleCosetWeight
open Subgroup
namespace GlobalTheory.DoubleCosetWeight
theorem _root_.solution {G : Type} [Group G] (T C K : Subgroup G)
    (hC : ∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) :
    ∀ t ∈ T, ∀ k ∈ K, ∀ q : G,
      (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C =
        (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by
  intro t ht k hk q
  have hN : gen T K ≤ C := iSup_le hC
  have hA : ∀ p : G, T ⊓ K.map (MulAut.conj p).toMonoidHom ≤ gen T K := fun p =>
    le_iSup (fun q : G => T ⊓ K.map (MulAut.conj q).toMonoidHom) p
  have e1 := relIndex_mul_relIndex _ _ _ (hA (t * q * k)) hN
  have e2 := relIndex_mul_relIndex _ _ _ (hA q) hN
  rw [← e1, ← e2, inf_map_conj_mul_eq T K ht hk q]
  congr 1
  conv_lhs => rw [← gen_map_eq T K ht]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj t).injective
end GlobalTheory.DoubleCosetWeight
