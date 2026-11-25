-- Prove2me | solution 1 for GlobalTheory.HeightOneHopf.truncated_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:52:49.724802+00:00
-- url     : https://prove2.me/submissions/df1ee6e7-7fd1-404b-aebb-2d710f710b9a

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfIsNilpotentKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfSpanCotangent
import Theorems.Thm_GlobalTheory_HeightOneHopf_aeval_surjective_of_span_cotangent
import Theorems.Thm_GlobalTheory_HeightOneHopf_exists_isPtDer_dual
import Theorems.Thm_ReciprocityTheory_PGsh_aeval_eq_zero_of_mem_span
import Theorems.Thm_ReciprocityTheory_PGsh_coeff_eq_zero_of_stable
import Theorems.Thm_ReciprocityTheory_PGsh_convD_mul
import Theorems.Thm_ReciprocityTheory_PGsh_counit_convD
import Theorems.Thm_ReciprocityTheory_PGsh_mem_span_pow_of_coeff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.HeightOneHopf
namespace GlobalTheory.HeightOneHopf
theorem _root_.solution : TruncatedPolynomialStatement := by
  intro p hp k H _ _ _ _ _ d x hpow hx hspan hind
  have : IsNoetherianRing H := isNoetherian_of_tower k inferInstance
  have hnil : IsNilpotent (RingHom.ker (Bialgebra.counitAlgHom k H)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨p, hpow f hf⟩
  have hsurj := aeval_surjective_of_span_cotangent _ hnil x hx hspan
  refine ⟨hsurj, le_antisymm ?_ ?_⟩
  · obtain ⟨δ, hδ, hδx⟩ := exists_isPtDer_dual x hx hind
    intro P hP
    apply mem_span_pow_of_coeff
    refine coeff_eq_zero_of_stable (Bialgebra.counitAlgHom k H) x hx (fun i => convD (δ i))
      (fun i => convD_mul _ (hδ i)) (fun i j => ?_) hsurj (CharP.cast_eq_zero k p)
      (fun n h0 hn => ?_) {0} ?_ ?_ P hP
    · rw [Bialgebra.counitAlgHom_apply, counit_convD, hδx]
    · rw [isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff k p]
      exact Nat.not_dvd_of_pos_of_lt h0 hn
    · rintro a rfl; simp
    · rintro i a rfl; simp
  · intro P hP
    exact aeval_eq_zero_of_mem_span x (fun j => hpow _ (hx j)) hP
end GlobalTheory.HeightOneHopf
