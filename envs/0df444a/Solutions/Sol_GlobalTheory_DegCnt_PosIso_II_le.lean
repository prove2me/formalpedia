-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.II_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:04:34.045881+00:00
-- url     : https://prove2.me/submissions/8069e6fa-82d1-40d1-adb5-8802544c05b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Xa_coords
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Dl_ne
import Theorems.Thm_P2M_GlobalTheory_DegCnt_PosIso_Ia_X__933463d23d40
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Xa_le_sup
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
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
theorem _root_.solution (N : NF H r) : II N.F N.F' ≤ Ia N r := by
  intro x hx
  obtain ⟨ξ, hξ, i, hi, rfl⟩ := Submodule.mem_sup.1 (Xa_le_sup N r hx.1)
  have hξ' : ξ ∈ N.F'.X := by simpa using sub_mem hx.2 (Ia_X' N hi)
  obtain ⟨p, -, rfl⟩ := Xa_coords N.F (N.j_le.trans (Nat.le_succ r)) le_rfl hξ
  have : p = 0 := by
    refine Matrix.eq_zero_of_vecMul_eq_zero (Dl_ne N) ?_
    funext b
    have := X_iso N.F' hξ' (e_mem_X N.F' (Fin.castLE N.j_le b))
    simpa [Matrix.vecMul, dotProduct, Zhat, map_sum] using this
  simpa [this] using hi
end GlobalTheory.DegCnt.PosIso
