-- Prove2me | solution 1 for GlobalTheory.DoubleCosetWeight.inf_map_conj_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:43.574432+00:00
-- url     : https://prove2.me/submissions/61262f8c-2e21-43c2-bba4-2a57bf70a261

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetRelIndexInfConjConst

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
theorem _root_.solution {G : Type} [Group G] (T K : Subgroup G) {t k : G}
    (ht : t ∈ T) (hk : k ∈ K) (q : G) :
    T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom =
      (T ⊓ K.map (MulAut.conj q).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
  ext x
  simp only [mem_inf, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hxT, y, hy, rfl⟩
    refine ⟨q * (k * y * k⁻¹) * q⁻¹, ⟨?_, k * y * k⁻¹, K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk), rfl⟩, ?_⟩
    · have : q * (k * y * k⁻¹) * q⁻¹ = t⁻¹ * (t * q * k * y * (t * q * k)⁻¹) * t := by group
      rw [this]; exact T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
    · group
  · rintro ⟨z, ⟨hzT, y, hy, rfl⟩, rfl⟩
    refine ⟨T.mul_mem (T.mul_mem ht hzT) (T.inv_mem ht), k⁻¹ * y * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk, ?_⟩
    group
end GlobalTheory.DoubleCosetWeight
