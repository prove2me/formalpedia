-- Prove2me | solution 1 for GlobalTheory.WigSh.omg_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:07:43.754379+00:00
-- url     : https://prove2.me/submissions/6690d2cc-db5b-4693-b388-dfa019bce865

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgEquivariant
import Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_fix_fvec
import Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_inv_mem
import Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_inv_eq
import Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_mul_mem
import Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_prW_comm
import Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_Zhat_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open GlobalTheory GlobalTheory.WigSh
open OmgEquiv
namespace GlobalTheory.WigSh
theorem _root_.solution : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g h h' : Mx k r), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → g ∈ UH (Hpk k r) → h ∈ UWset k r z → h' ∈ UWset k r z' → GlobalTheory.WigSh.omg k r z z' (h⁻¹ * g * h') = h'⁻¹ *ᵥ GlobalTheory.WigSh.omg k r z z' g := by
  intro k r z z' g h h' _ _ _ _ hg hh hh'
  have hUW : ∀ {w : Fin (2 * r + k + 1) → ℂ} {m : Mx k r}, m ∈ UWset k r w → m ∈ UH (Hpk k r) := by
    intro w m hm
    simp only [Formalism.QuantumDeterminants.UWset, Set.mem_ofPred_eq] at hm
    exact hm.1
  have hG : h⁻¹ * g * h' ∈ UH (Hpk k r) :=
    GlobalTheory.WigSh.OmgEquiv.mul_mem
      (GlobalTheory.WigSh.OmgEquiv.mul_mem (hUW (GlobalTheory.WigSh.OmgEquiv.inv_mem hh)) hg) (hUW hh')
  unfold GlobalTheory.WigSh.omg
  rw [GlobalTheory.WigSh.OmgEquiv.Zhat_eq hh hh', ← GlobalTheory.WigSh.OmgEquiv.inv_eq hG, ← GlobalTheory.WigSh.OmgEquiv.inv_eq hg,
    Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  set S := ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a with hSdef
  have hfixS : ∀ m : Mx k r, m ∈ UWset k r z → m *ᵥ S = S := by
    intro m hm
    rw [hSdef, Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [Matrix.mulVec_smul, GlobalTheory.WigSh.OmgEquiv.fix_fvec hm a]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hfixS _ (GlobalTheory.WigSh.OmgEquiv.inv_mem (GlobalTheory.WigSh.OmgEquiv.inv_mem hh))]
  exact GlobalTheory.WigSh.OmgEquiv.prW_comm (GlobalTheory.WigSh.OmgEquiv.inv_mem hh') _
end GlobalTheory.WigSh
