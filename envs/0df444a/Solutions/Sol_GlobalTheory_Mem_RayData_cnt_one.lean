-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.cnt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:10.565454+00:00
-- url     : https://prove2.me/submissions/e1d2acea-e11b-489d-a665-70edcd43913b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Theorems.Thm_GlobalTheory_Mem_RayData_cls_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem
open NumberField IsDedekindDomain
attribute [instance] RayData.grp RayData.fin
open GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
open Classical
namespace GlobalTheory.Mem.RayData
theorem _root_.solution (c : D.G) : D.cnt c 1 = if c = 1 then 1 else 0 := by
  have key : ∀ I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧
      Ideal.absNorm I = 1 ∧ D.cls I = c}, I.1 = ⊤ :=
    fun I => Ideal.absNorm_eq_one_iff.mp I.2.2.1
  rw [cnt]
  split_ifs with hc
  · subst hc
    have h1 : Nat.card {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧
        Ideal.absNorm I = 1 ∧ D.cls I = 1} = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext ((key a).trans (key b).symm)⟩,
        ⟨⟨⊤, by rw [← Ideal.one_eq_top]; exact isCoprime_one_left, Ideal.absNorm_top, D.cls_top⟩⟩⟩
    rw [h1, Nat.cast_one]
  · have : IsEmpty {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧
        Ideal.absNorm I = 1 ∧ D.cls I = c} :=
      ⟨fun I => hc (by rw [← I.2.2.2, key I, D.cls_top])⟩
    rw [Nat.card_of_isEmpty, Nat.cast_zero]
end GlobalTheory.Mem.RayData
