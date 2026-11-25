-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.level_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:25:34.75654+00:00
-- url     : https://prove2.me/submissions/d05b9ea7-343a-49e8-a977-d3e7378f4c11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_step
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_bot
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (N : NF H r) (M Q : Submodule (𝓞 K) V) (w : Fin r → V)
    (hw : ∀ b : Fin r, N.j ≤ b.val → w b - N.F.e b.castSucc ∈ Ia N b.val)
    (h : ∀ b : Fin r, N.j ≤ b.val → ∀ y ∈ M, y ∈ Ia N (b.val + 1) →
      H.B y (N.ist b) • w b ∈ M ∧ H.B y (N.ist b) • w b ∈ Q) :
    ∀ n ≤ r, ∀ y ∈ M, y ∈ Ia N n → y ∈ Q := by
  intro n
  induction n with
  | zero => intro _ y _ hy; rw [Ia_bot N (Nat.zero_le _) hy]; exact zero_mem _
  | succ n ih =>
    intro hn y hyM hy
    by_cases hj : N.j ≤ n
    · let b : Fin r := ⟨n, hn⟩
      obtain ⟨h1, h2⟩ := h b hj y hyM hy
      have h3 : y - H.B y (N.ist b) • w b ∈ Ia N n := by
        convert sub_mem (Ia_step N b hj hy) (Submodule.smul_mem _ (H.B y (N.ist b)) (hw b hj)) using 1
        module
      simpa using add_mem (ih (by omega) _ (sub_mem hyM h1) h3) h2
    · rw [Ia_bot N (by omega) hy]; exact zero_mem _
end GlobalTheory.DegCnt.PosIso
