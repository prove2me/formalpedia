-- Prove2me | solution 1 for GlobalTheory.WeylDuality.weyl_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:53.220743+00:00
-- url     : https://prove2.me/submissions/b06cd6d8-0293-422b-8f14-300885c78819

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
import Theorems.Thm_GlobalTheory_WeylDuality_intQ_apply
import Theorems.Thm_GlobalTheory_WeylDuality_intQ_word
import Theorems.Thm_GlobalTheory_WeylDuality_mem_inV
import Theorems.Thm_GlobalTheory_WeylDuality_dualWeyl_int_fg
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylEqNablaQ
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylLeDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace GlobalTheory.WeylDuality
private theorem mem_dualWeyl_rat_of_mem_map_weyl {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∀ P ∈ (weyl ℤ r n hn ν).map (intQ r n), P ∈ dualWeyl ℚ r n ν := by
  rintro P ⟨G, hG, rfl⟩
  rw [intQ_apply]
  exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν G (weylLeDual ℤ r n hn ν hν hG)
end GlobalTheory.WeylDuality
end
end

set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    (inV ν ((weyl ℤ r n hn ν).map (intQ r n))).IsLattice ℚ where
  fg := by
    have hW : (weyl ℤ r n hn ν).FG := by
      have := isNoetherian_of_fg_of_noetherian _ (dualWeyl_int_fg r n ν)
      exact Submodule.FG.of_le_of_isNoetherian (weylLeDual ℤ r n hn ν hν)
    have hsub := mem_dualWeyl_rat_of_mem_map_weyl hn ν hν
    refine Submodule.fg_of_fg_map_injective ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ)
      Subtype.val_injective ?_
    have heq : (inV ν ((weyl ℤ r n hn ν).map (intQ r n))).map
        ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ) = (weyl ℤ r n hn ν).map (intQ r n) := by
      apply le_antisymm
      · exact Submodule.map_comap_le _ _
      · intro P hP
        exact ⟨⟨P, hsub P hP⟩, hP, rfl⟩
    rw [heq]
    exact hW.map _
  span_eq_top := by
    have hsub := mem_dualWeyl_rat_of_mem_map_weyl hn ν hν
    apply Submodule.map_injective_of_injective (f := (dualWeyl ℚ r n ν).subtype) Subtype.val_injective
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    · refine le_trans (le_of_eq (weylEqNablaQ r n hn ν hν).symm) (Submodule.span_le.mpr ?_)
      rintro _ ⟨w, rfl⟩
      apply Submodule.subset_span
      have hmem : applyWord ℚ w (hw ℚ hn ν) ∈ (weyl ℤ r n hn ν).map (intQ r n) := by
        refine ⟨applyWord ℤ w (hw ℤ hn ν), ?_, intQ_word hn ν _⟩
        unfold weyl
        exact Submodule.subset_span ⟨_, rfl⟩
      exact ⟨⟨_, hsub _ hmem⟩, (mem_inV _ _ _).mpr hmem, rfl⟩
end GlobalTheory.WeylDuality
