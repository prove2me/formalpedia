-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.Ia_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:58:06.575084+00:00
-- url     : https://prove2.me/submissions/b0786268-f9d7-409f-a759-21d128b42615

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_e_mem_Ia
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
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (N : NF H r) (b : Fin r) (hb : N.j ≤ b.val) {y : V} (hy : y ∈ Ia N (b.val + 1)) :
    y - H.B y (N.ist b) • N.F.e b.castSucc ∈ Ia N b.val := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    simp only [N.ist_e a b hb]
    split_ifs with h
    · subst h; simp
    · have : a.val ≠ b.val := fun h' => h (Fin.ext h')
      have h2 := ha.2
      simpa using e_mem_Ia N a ha.1 (show a.val < b.val by omega)
  | zero => simp
  | add y y' _ _ h h' =>
    convert add_mem h h' using 1
    simp only [map_add, LinearMap.add_apply]; module
  | smul a y _ h =>
    convert Submodule.smul_mem _ a h using 1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; module
end GlobalTheory.DegCnt.PosIso
