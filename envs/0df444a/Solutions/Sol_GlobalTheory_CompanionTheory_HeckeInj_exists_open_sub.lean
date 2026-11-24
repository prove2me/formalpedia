-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeInj.exists_open_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:37:04.509146+00:00
-- url     : https://prove2.me/submissions/810722eb-d013-49db-ab69-a96dd8b10631

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeInj
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.HeckeInj
theorem _root_.solution {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F))) (s : Finset (GL ι F)) :
    ∃ L : Subgroup (GL ι F), IsOpen (L : Set (GL ι F)) ∧ L ≤ K ∧ ∀ g ∈ s, ∀ l ∈ L, g⁻¹ * l * g ∈ K := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨K, hKo, le_rfl, by simp⟩
  | insert a s _ ih =>
    obtain ⟨L, hLo, hLK, hL⟩ := ih
    let C : Subgroup (GL ι F) := K.comap (MulAut.conj a⁻¹).toMonoidHom
    have hC : IsOpen (C : Set (GL ι F)) := by
      have hcont : Continuous fun l : GL ι F => a⁻¹ * l * a⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hKo.preimage hcont
    refine ⟨L ⊓ C, hLo.inter hC, inf_le_left.trans hLK, fun g hg l hl => ?_⟩
    rcases Finset.mem_insert.1 hg with rfl | hg
    · have := hl.2
      simpa [C, Subgroup.mem_comap] using this
    · exact hL g hg l hl.1
end GlobalTheory.CompanionTheory.HeckeInj
