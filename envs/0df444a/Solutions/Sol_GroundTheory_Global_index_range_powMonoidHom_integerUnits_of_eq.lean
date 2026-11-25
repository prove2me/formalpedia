-- Prove2me | solution 1 for GroundTheory.Global.index_range_powMonoidHom_integerUnits_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:28:14.50554+00:00
-- url     : https://prove2.me/submissions/ef93d970-2bf9-45eb-ae85-f54a1aa70ef8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_eq_one_of_pow_eq_one
import Theorems.Thm_GroundTheory_Global_map_powMonoidHom_unitFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n d : ℕ} {ε : 𝒪[K]ˣ}
  (hnd : (n : 𝒪[K]) = ε * ϖ ^ d)
include hϖ hnd
namespace GroundTheory.Global
theorem _root_.solution :
    (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range.index =
      Nat.card (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker * Nat.card 𝓀[K] ^ d := by
  set f : 𝒪[K]ˣ →* 𝒪[K]ˣ := powMonoidHom n
  set V := unitFiltration K (d + 1)
  have hdisj : Disjoint V f.ker := by
    rw [Subgroup.disjoint_def]
    intro u hu hk
    exact eq_one_of_pow_eq_one hϖ hnd hu hk
  have h1 : V.relIndex f.ker = Nat.card f.ker := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.2 hdisj, Subgroup.index_bot]
  have h2 : V.relIndex (V ⊔ f.ker) * (V ⊔ f.ker).index = V.index :=
    Subgroup.relIndex_mul_index le_sup_left
  have h3 : V.relIndex (V ⊔ f.ker) = V.relIndex f.ker := Subgroup.relIndex_sup_left f.ker V
  have h4 : (V.map f).index = (V ⊔ f.ker).index * f.range.index := V.index_map f
  rw [map_powMonoidHom_unitFiltration hϖ hnd, index_unitFiltration K (by omega)] at h4
  rw [h3, h1, index_unitFiltration K (by omega)] at h2
  have hq : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hc : 0 < (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ d :=
    Nat.mul_pos (by omega) (pow_pos (by omega) d)
  refine Nat.eq_of_mul_eq_mul_left hc ?_
  have e1 : d + 1 - 1 = d := by omega
  have e2 : d + 1 + d - 1 = d + d := by omega
  rw [e1] at h2
  rw [e2, pow_add] at h4
  calc (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ d * f.range.index
      = Nat.card f.ker * ((V ⊔ f.ker).index * f.range.index) := by rw [← h2]; ring
    _ = _ := by rw [← h4]; ring
end GroundTheory.Global
