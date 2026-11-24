-- Prove2me | solution 1 for GlobalTheory.FullLevel.Uniq.ev_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:20.436901+00:00
-- url     : https://prove2.me/submissions/44e18432-a586-441a-99eb-0029cadf0eb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullSymplecticLevelStructureUniqueOfLevels
import Theorems.Thm_GlobalTheory_FullLevel_Uniq_nsmul_cancel
import Theorems.Thm_GlobalTheory_FullLevel_Uniq_ev_nsmul
import Theorems.Thm_GlobalTheory_FullLevel_Uniq_ev_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel
open GlobalTheory GlobalTheory.FullLevel GlobalTheory.FullLevel.Uniq
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
  {N : ℕ} {z : kˣ} {ev : D.La → Q}
namespace GlobalTheory.FullLevel.Uniq
theorem _root_.solution (h : IsSympLevel D act e N z ev) (hN : 0 < N) {A : ℕ} (hA : A ∣ N) {x y : D.La}
    (hxy : ev x ^ (N / A) = ev y ^ (N / A)) : ∃ b, x - y = A • b := by
  obtain ⟨m, hm⟩ := hA
  have hA0 : 0 < A := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm; omega
  have hd : N / A = m := by rw [hm, Nat.mul_div_cancel_left _ hA0]
  rw [hd, ← ev_nsmul h, ← ev_nsmul h, ev_eq_iff h] at hxy
  obtain ⟨b, hb⟩ := hxy
  refine ⟨b, nsmul_cancel hm0 ?_⟩
  rw [smul_sub, hb, hm, smul_smul, mul_comm]
end GlobalTheory.FullLevel.Uniq
