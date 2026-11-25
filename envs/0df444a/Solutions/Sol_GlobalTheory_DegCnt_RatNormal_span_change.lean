-- Prove2me | solution 1 for GlobalTheory.DegCnt.RatNormal.span_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:24.446664+00:00
-- url     : https://prove2.me/submissions/900053c9-47e0-4d4b-b169-8c5455af6188

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsInvLower
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_Xa
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.HermitianLatticeCounting.P
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.RatNormal
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.RatNormal
theorem _root_.solution (F : FlagD H r) (f : Fin (r + 1) → V) (hf : ∀ a, f a - F.e a ∈ F.Xa a.val) (n : ℕ) :
    Submodule.span K ((fun b : Fin r => f b.castSucc) '' {b | b.val < n}) = F.Xa n := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have h1 : f b.castSucc - F.e b.castSucc ∈ F.Xa n := Xa_mono F (le_of_lt hb) (hf b.castSucc)
    simpa using Submodule.add_mem _ h1 (e_mem_Xa F b hb)
  · induction n with
    | zero => rw [Xa_zero]; exact bot_le
    | succ n ih =>
      have hm : Submodule.span K ((fun b : Fin r => f b.castSucc) '' {b | b.val < n}) ≤
          Submodule.span K ((fun b : Fin r => f b.castSucc) '' {b | b.val < n + 1}) :=
        Submodule.span_mono (Set.image_mono fun b (hb : b.val < n) => Nat.lt_succ_of_lt hb)
      rw [FlagD.Xa, Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b.val ≤ n := Nat.lt_succ_iff.mp hb
      have h1 := hm (ih (Xa_mono F hb' (hf b.castSucc)))
      have h2 : f b.castSucc ∈ Submodule.span K ((fun b : Fin r => f b.castSucc) '' {b | b.val < n + 1}) :=
        Submodule.subset_span ⟨b, hb, rfl⟩
      simpa using Submodule.sub_mem _ h2 h1
end GlobalTheory.DegCnt.RatNormal
