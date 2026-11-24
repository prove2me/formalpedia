-- Prove2me | solution 1 for GlobalTheory.BorelUMod.Cayley.relIndex_unipLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:09:36.725985+00:00
-- url     : https://prove2.me/submissions/0e24f4f0-4262-471a-bd93-b3749ddf9f39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowApplyEqZeroOfStrictUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
import Theorems.Thm_GlobalTheory_BorelUMod_Cayley_relIndex_eq_of_surj
import Theorems.Thm_GlobalTheory_BorelUMod_Cayley_unit_mul_mem_iff
import Theorems.Thm_GlobalTheory_BorelUMod_Cayley_cay_mem
import Theorems.Thm_GlobalTheory_BorelUMod_Cayley_cay_skew
import Theorems.Thm_GlobalTheory_BorelUMod_Cayley_cay_sub_mem_iff
import Theorems.Thm_GlobalTheory_BorelUMod_Cayley_cay_surj
import Theorems.Thm_GlobalTheory_BorelUMod_exists_trace_one
import Theorems.Thm_GlobalTheory_LGrp_mem_borelU_U


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod GlobalTheory.BorelUMod.Cayley
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.BorelUMod.Cayley
theorem _root_.solution (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (h : IsUnramInv ϖ σ q) (c C : Fin n → Fin n → ℤ) (hc : IsWeight c) (hC : IsWeight C) (hI : IsIdealWeight c C) :
    (unipLat h.2.1 hC).relIndex (unipLat h.2.1 hc) =
      (upLat L C ⊓ skewJ σ n).relIndex (upLat L c ⊓ skewJ σ n) := by
  obtain ⟨⟨t, ht, hσ⟩, -⟩ := exists_trace_one h
  have hadj : ∀ u : (borelU σ n).U, (u.1.1⁻¹).val = adjJ σ u.1.1.val := fun u => (mem_GU_iff_adjJ σ _).1 u.1.2
  have hsk : ∀ u : unipLat h.2.1 hc, cay t u.1.1.1.val ∈ skewJ σ n := fun u =>
    cay_skew hc ht hσ u.2 (by rw [← hadj, Units.mul_inv])
  refine relIndex_eq_of_surj _ _ _ _ (fun u => ⟨cay t u.1.1.1.val, cay_mem hc ht u.2, hsk u⟩) ?_ ?_
  · rintro ⟨X, hX, hs⟩
    obtain ⟨u, hu, e1, e⟩ := cay_surj hc h.1 ht hσ hX hs
    let g : GL (Fin n) L := ⟨u, adjJ σ u, mul_eq_one_comm.1 e1, e1⟩
    have hg : g ∈ GU σ n := (mem_GU_iff_adjJ σ g).2 rfl
    have hU : (⟨g, hg⟩ : GU σ n) ∈ (borelU σ n).U := by
      rw [mem_borelU_U]
      refine ⟨fun i j e => ?_, fun i => ?_⟩
      · have := hu.1 i j (le_of_lt e)
        rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt e), sub_zero] at this
        exact this
      · have := hu.1 i i le_rfl
        rw [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this
        exact this
    exact ⟨⟨⟨⟨g, hg⟩, hU⟩, hu⟩, Subtype.ext e⟩
  · intro u u'
    have h1 : (u.1.1.1⁻¹).val - 1 ∈ upLat L c := (unipLat h.2.1 hc).inv_mem u.2
    have h2 := unit_mul_mem_iff hc hI (x := u'.1.1.1.val - u.1.1.1.val) h1 (zero_mem _)
    rw [add_zero, mul_one, add_sub_cancel, mul_sub, Units.inv_mul] at h2
    show (u.1.1.1⁻¹).val * u'.1.1.1.val - 1 ∈ upLat L C ↔
      -cay t u.1.1.1.val + cay t u'.1.1.1.val ∈ upLat L C ⊓ skewJ σ n
    rw [h2, AddSubgroup.mem_inf, cay_sub_mem_iff hc hI ht u.2 u'.2]
    exact ⟨fun e => ⟨e, add_mem (neg_mem (hsk u)) (hsk u')⟩, fun e => e.1⟩
end GlobalTheory.BorelUMod.Cayley
