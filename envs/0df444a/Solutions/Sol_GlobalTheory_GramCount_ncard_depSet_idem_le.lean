-- Prove2me | solution 1 for GlobalTheory.GramCount.ncard_depSet_idem_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:01:47.507357+00:00
-- url     : https://prove2.me/submissions/0747a0ad-ff60-4cc6-bdbd-6fa493dfd7e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardDependentVectorsAffineGramLe
import Theorems.Thm_GlobalTheory_GramCount_dep_kernel
import Theorems.Thm_GlobalTheory_GramCount_card_fixed_sq
import Theorems.Thm_GlobalTheory_GramCount_ip_sub_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
variable {B : Type} [CommRing B]
namespace GlobalTheory.GramCount
theorem _root_.solution [Fintype B] (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B}
    (hω : IsUnit (ω - c ω)) {q : ℕ} (hq : Fintype.card B = q ^ 2) {k n : ℕ}
    (x : Fin k → Fin n → B) (hx : Prim c x) (g : Fin k → B) {ε : B} (h1 : ε + c ε = 1)
    (h2 : ε * c ε = 0) : (depSet c x g ε).ncard ≤ q ^ n := by
  obtain ⟨d, hd⟩ := hx
  have hK : Nat.card {t : B // c t = t} = q := by
    have := (card_fixed_sq c hc hω (M := B) c.toAddMonoidHom hc (fun a y => by simp)).1
    rw [Nat.card_eq_fintype_card (α := B), hq] at this
    exact Nat.pow_left_injective two_ne_zero this
  let F : depSet c x g ε × (Fin k → B) → (Fin k → B) × (Fin n → {t : B // c t = t}) :=
    fun p => (fun i => c (ε * ip c p.1.1 (d i)) + ε * p.2 i,
      fun l => ⟨(c ε • p.1.1 + ∑ j, (c ε * p.2 j) • d j) l +
        c ((c ε • p.1.1 + ∑ j, (c ε * p.2 j) • d j) l), by rw [map_add, hc, add_comm]⟩)
  have hF : Function.Injective F := by
    rintro ⟨⟨y, hy, s, hs⟩, r⟩ ⟨⟨y', hy', s', hs'⟩, r'⟩ h
    obtain ⟨hA, hB⟩ := Prod.ext_iff.1 h
    have key := dep_kernel c hc x d hd h1 h2 (y - y') (r - r') (s - s')
      (fun i => by rw [ip_sub_left, hy, hy', sub_self])
      (by simp only [smul_sub, hs, hs', Pi.sub_apply, sub_smul, Finset.sum_sub_distrib])
      (fun i => by
        have := congrFun hA i
        simp only [F, map_mul] at this
        simp only [ip_sub_left, map_mul, map_sub, Pi.sub_apply]
        linear_combination this)
      (fun l => by
        have := congrArg Subtype.val (congrFun hB l)
        simp only [F, Pi.add_apply, map_add] at this
        simp only [smul_sub, mul_sub, sub_smul, Finset.sum_sub_distrib, Pi.add_apply,
          Pi.sub_apply, map_add, map_sub]
        linear_combination this)
    exact Prod.ext (Subtype.ext (sub_eq_zero.1 key.1)) (sub_eq_zero.1 key.2)
  have h3 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fun (α := Fin n), hK,
    mul_comm] at h3
  have h4 : 0 < Nat.card (Fin k → B) := Nat.card_pos
  simpa using Nat.le_of_mul_le_mul_left h3 h4
end GlobalTheory.GramCount
