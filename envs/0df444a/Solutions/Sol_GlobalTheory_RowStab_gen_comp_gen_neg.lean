-- Prove2me | solution 1 for GlobalTheory.RowStab.gen_comp_gen_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:25:54.398588+00:00
-- url     : https://prove2.me/submissions/cb3f0c65-b1fa-433a-8a65-6942b1348d32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianUnipotentGeneratorMapCompNeg
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
theorem _root_.solution {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c c' : ι → ι → K)
    (he : ∀ a b, H.B (e a) (e b) = 0) (hρe : ∀ a b, H.B (ρ a) (e b) = 0)
    (hc : ∀ a b, c a b + c' a b + H.B (ρ b) (ρ a) = 0) (v : V) :
    gen H J e ρ c (gen H J e (-ρ) c' v) = v := by
  have heρ : ∀ a b, H.B (e a) (ρ b) = 0 := fun a b => by rw [← H.herm, hρe, star_zero]
  set u := gen H J e (-ρ) c' v with hu
  have hue : ∀ b, H.B u (e b) = H.B v (e b) := by
    intro b
    rw [hu, gen_apply]
    simp [LinearMap.sum_apply, he, hρe]
  have huρ : ∀ b, H.B u (ρ b) = H.B v (ρ b) - ∑ d ∈ J, H.B v (e d) * H.B (ρ d) (ρ b) := by
    intro b
    rw [hu, gen_apply]
    simp [LinearMap.sum_apply, heρ, sub_eq_add_neg]
  have h4 : ∑ b ∈ J, (∑ d ∈ J, H.B v (e d) * H.B (ρ d) (ρ b)) • e b =
      ∑ b ∈ J, ∑ a ∈ J, (H.B (ρ b) (ρ a) * H.B v (e b)) • e a := by
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have key : (∑ b ∈ J, ∑ a ∈ J, (c' a b * H.B v (e b)) • e a) +
      (∑ b ∈ J, (∑ d ∈ J, H.B v (e d) * H.B (ρ d) (ρ b)) • e b) +
      ∑ b ∈ J, ∑ a ∈ J, (c a b * H.B v (e b)) • e a = 0 := by
    rw [h4, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← add_smul, ← add_smul, ← add_mul, ← add_mul,
      show c' a b + H.B (ρ b) (ρ a) + c a b = 0 by linear_combination hc a b, zero_mul, zero_smul]
  rw [gen_apply H J e ρ c u]
  simp only [hue, huρ]
  rw [hu, gen_apply H J e (-ρ) c' v]
  simp only [map_neg, Pi.neg_apply, neg_smul, smul_neg, sub_smul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  linear_combination (norm := module) key
end GlobalTheory.RowStab
