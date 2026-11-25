-- Prove2me | solution 1 for GlobalTheory.RowStab.gen_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:53:08.429253+00:00
-- url     : https://prove2.me/submissions/5594a2d7-4a4a-47f6-b6c1-a9d76c7d8a98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianUnipotentGeneratorMapIsometry
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RowStab_gen_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open GlobalTheory GlobalTheory.RowStab
namespace GlobalTheory.RowStab
theorem _root_.solution {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) (hee : ∀ a b, H.B (e a) (e b) = 0) (hρe : ∀ a b, H.B (ρ a) (e b) = 0) (hc : ∀ a b, star (c a b) + c b a + H.B (ρ a) (ρ b) = 0) (u v : V) : H.B (GlobalTheory.RowStab.gen H J e ρ c u) (GlobalTheory.RowStab.gen H J e ρ c v) = H.B u v := by
  have heρ : ∀ a b, H.B (e a) (ρ b) = 0 := fun a b => by rw [← H.herm, hρe, star_zero]
  have hX : ∀ w y, H.B (∑ b ∈ J, (H.B w (e b) • ρ b - H.B w (ρ b) • e b + ∑ a ∈ J, (c a b * H.B w (e b)) • e a)) y = ∑ b ∈ J, (H.B w (e b) * H.B (ρ b) y - H.B w (ρ b) * H.B (e b) y + ∑ a ∈ J, c a b * H.B w (e b) * H.B (e a) y) := by
    intro w y
    simp [map_sum, LinearMap.sum_apply, mul_assoc]
  have hXr : ∀ w y, H.B y (∑ b ∈ J, (H.B w (e b) • ρ b - H.B w (ρ b) • e b + ∑ a ∈ J, (c a b * H.B w (e b)) • e a)) = star (∑ b ∈ J, (H.B w (e b) * H.B (ρ b) y - H.B w (ρ b) * H.B (e b) y + ∑ a ∈ J, c a b * H.B w (e b) * H.B (e a) y)) := by
    intro w y; rw [← H.herm, hX]
  have hρv : ∀ b, H.B (ρ b) v = star (H.B v (ρ b)) := fun b => (H.herm _ _).symm
  have hev : ∀ b, H.B (e b) v = star (H.B v (e b)) := fun b => (H.herm _ _).symm
  have hρu : ∀ b, H.B (ρ b) u = star (H.B u (ρ b)) := fun b => (H.herm _ _).symm
  have heu : ∀ b, H.B (e b) u = star (H.B u (e b)) := fun b => (H.herm _ _).symm
  rw [GlobalTheory.RowStab.gen_apply, GlobalTheory.RowStab.gen_apply]
  simp only [map_add, LinearMap.add_apply, hX, hXr, hee, heρ, hρe, mul_zero, sub_zero, add_zero, Finset.sum_const_zero, star_zero, hρv, hev, hρu, heu, star_sum, star_add, star_sub, star_mul', star_star]
  have hρρ : ∀ a b, star (H.B (ρ a) (ρ b)) = H.B (ρ b) (ρ a) := fun a b => H.herm _ _
  simp only [hρρ]
  have h2 : ∑ x ∈ J, ∑ x1 ∈ J, star (c x1 x) * star (H.B v (e x)) * H.B u (e x1) = ∑ x ∈ J, ∑ x1 ∈ J, star (c x x1) * star (H.B v (e x1)) * H.B u (e x) := Finset.sum_comm
  have hS : ∑ x ∈ J, ∑ x1 ∈ J, c x1 x * H.B u (e x) * star (H.B v (e x1)) + ∑ x ∈ J, ∑ x1 ∈ J, star (c x1 x) * star (H.B v (e x)) * H.B u (e x1) + ∑ x ∈ J, H.B u (e x) * ∑ x1 ∈ J, star (H.B v (e x1)) * H.B (ρ x) (ρ x1) = 0 := by
    rw [h2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x1 _
    linear_combination (H.B u (e x) * star (H.B v (e x1))) * hc x x1
  have hA : ∑ x ∈ J, star (H.B v (ρ x)) * H.B u (e x) = ∑ x ∈ J, H.B u (e x) * star (H.B v (ρ x)) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hB : ∑ x ∈ J, star (H.B v (e x)) * H.B u (ρ x) = ∑ x ∈ J, H.B u (ρ x) * star (H.B v (e x)) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linear_combination hS - hA + hB
end GlobalTheory.RowStab
