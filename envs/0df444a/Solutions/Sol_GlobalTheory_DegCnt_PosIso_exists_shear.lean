-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.exists_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:36:14.527068+00:00
-- url     : https://prove2.me/submissions/9e5e0421-a546-415c-93f2-f5b3f462941b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_mono
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_le
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Ia_X
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Xa_ist
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_exists_eich
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_z_X
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
theorem _root_.solution (N : NF H r) (b : Fin r) (hb : N.j ≤ b.val) {x : V} (hx : x ∈ Ia N b.val) :
    ∃ s ∈ Gs N, s N.F.z = N.F.z ∧ ∀ y ∈ N.F.X, s y = y + H.B y (N.ist b) • x := by
  obtain ⟨s, hs, h⟩ := exists_eich N x (N.ist b) 0 (Ia_mono N b.isLt.le hx) (Xa_ist N b hb x (Ia_le N _ hx))
    (by simp [N.ist_iso b b hb hb])
    (fun a _ => by
      rw [N.ist_e a b hb]
      split_ifs with h
      · subst h; simpa using hx
      · simp)
    (fun a ha => by rw [N.ist_e a b hb, if_neg (by rintro rfl; omega)])
    (fun a ha => N.ist_e' a b ha hb)
    (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))
  refine ⟨s, hs, ?_, fun y hy => h y (X_iso N.F hy (Ia_X N hx))⟩
  rw [h _ (z_X N.F (Ia_X N hx)), N.normalForm_dual_orthogonal_last b hb]; simp
end GlobalTheory.DegCnt.PosIso
