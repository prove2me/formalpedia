-- Prove2me | solution 1 for GlobalTheory.InnerRead.good_of_mem_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:38:29.490531+00:00
-- url     : https://prove2.me/submissions/00dce02a-6fb5-46a6-8a70-133259e530d1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NonGenericDatumLatticeEqPerpQuotientImageTerm
import Theorems.Thm_GlobalTheory_InnerRead_good_inv
import Theorems.Thm_GlobalTheory_InnerRead_good_mul
import Theorems.Thm_GlobalTheory_InnerRead_X_le_perp
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
noncomputable section
open GlobalTheory GlobalTheory.InnerRead
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {H} {r : ℕ} (Fr : FrameD H r)
namespace GlobalTheory.InnerRead
theorem _root_.solution {g : V ≃ₗ[E] V} (hg : g ∈ Fr.N) : Good H (H.X Fr.f) g := by
  have hX := X_le_perp Fr
  unfold FrameD.N at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨hx.1, hx.2.2⟩
  | one => exact ⟨fun x y => rfl, fun v _ => by simp⟩
  | mul x y _ _ hx hy => exact good_mul H hX hx hy
  | inv x _ hx => exact good_inv H hX hx
end GlobalTheory.InnerRead
