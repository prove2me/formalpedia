-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.star_mem_ipow_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:31:30.566823+00:00
-- url     : https://prove2.me/submissions/2e141d25-bcd5-44af-a83c-58538ac1cd67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_ipow_add
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_ipow_zero
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_star_mem_one
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
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (𝔡 : Ideal (𝓞 K)) (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℕ) :
    ∀ x ∈ ipow 𝔡 n, star x ∈ ipow 𝔡 n := by
  induction n with
  | zero => intro x hx; simp only [Nat.cast_zero, ipow_zero] at hx ⊢; exact star_mem_one hx
  | succ n ih =>
    intro x hx
    rw [Nat.cast_succ, ipow_add _ h] at hx ⊢
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [star_mul']
      refine Submodule.mul_mem_mul (ih a ha) ?_
      simp only [ipow, zpow_one] at hb ⊢
      obtain ⟨o, ho, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hb
      obtain ⟨y, hy, hy'⟩ := hs o ho
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, hy'⟩
    · intro a b ha hb; rw [star_add]; exact add_mem ha hb
end GlobalTheory.DegCnt.PosIso
