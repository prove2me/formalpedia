-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.exists_adapted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:02.664877+00:00
-- url     : https://prove2.me/submissions/f0ea4fc5-0586-4ecd-9335-7623fc9e31a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_exists_section
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_step
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
theorem _root_.solution (N : NF H r) (Λ : Submodule (𝓞 K) V) (hΛ : Λ.FG) (b : Fin r) (hb : N.j ≤ b.val) :
    ∃ v, v - N.F.e b.castSucc ∈ Ia N b.val ∧
      ∀ y ∈ Λ, y ∈ Ia N (b.val + 1) → H.B y (N.ist b) • v ∈ Λ := by
  by_cases h0 : ∃ y ∈ Λ ⊓ rs (𝓞 K) (Ia N (b.val + 1)), H.B.flip (N.ist b) y ≠ 0
  · obtain ⟨v, hv, h1, h⟩ := exists_section _ (hΛ.of_le inf_le_left) _ h0
    have hv' : v ∈ Ia N (b.val + 1) := (Submodule.span_le.2 fun y hy => hy.2) hv
    refine ⟨v, ?_, fun y hy hy' => (h y ⟨hy, hy'⟩).1⟩
    have := Ia_step N b hb hv'
    rwa [show H.B v (N.ist b) = 1 from h1, one_smul] at this
  · push_neg at h0
    refine ⟨N.F.e b.castSucc, by simp, fun y hy hy' => ?_⟩
    rw [show H.B y (N.ist b) = 0 from h0 y ⟨hy, hy'⟩]; simp
end GlobalTheory.DegCnt.PosIso
