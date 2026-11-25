-- Prove2me | solution 1 for GlobalTheory.DegCnt.NearCount.exists_gens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:42.190731+00:00
-- url     : https://prove2.me/submissions/1acaaa45-d12b-47e8-8847-570b63b8b3be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardLatticesNearReferenceLatticeLe
import Theorems.Thm_GlobalTheory_DegCnt_NearCount_line_cyclic
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NearCount
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.NearCount
theorem _root_.solution [StarRing K] {H : HermSpace K V} {r : ℕ} (N : NF H r) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ v : Fin (2 * r + 1) → V, (∀ i, v i ∈ N.P0) ∧ N.P0 ≤ n • N.P0 ⊔ Submodule.span (𝓞 K) (Set.range v) := by
  choose u hu hu' using fun (I : FractionalIdeal (𝓞 K)⁰ K) (v : V) => line_cyclic I v n hn
  let d : FractionalIdeal (𝓞 K)⁰ K := N.𝔡
  let I : Option (Fin r ⊕ Fin r) → FractionalIdeal (𝓞 K)⁰ K := fun o => o.elim 1
    (Sum.elim (fun a => d ^ (-((r : ℤ) - a.val)))
      fun a => if a.val < N.j then d ^ (-((r : ℤ) - a.val)) else d ^ ((r : ℤ) - a.val))
  let x : Option (Fin r ⊕ Fin r) → V := fun o => o.elim N.F.z
    (Sum.elim (fun a => N.F.e a.castSucc) fun a => if a.val < N.j then N.F'.e a.castSucc else N.ist a)
  have hP : N.P0 = ⨆ o, line (I o : Submodule (𝓞 K) K) (x o) := by
    apply le_antisymm
    · refine sup_le (sup_le (sup_le (iSup_le fun a => ?_) (iSup₂_le fun a h => ?_)) ?_) (iSup₂_le fun a h => ?_)
      · exact le_iSup_of_le (some (Sum.inl a)) le_rfl
      · refine le_iSup_of_le (some (Sum.inr a)) (le_of_eq ?_)
        simp only [I, x, Option.elim, Sum.elim_inr, if_pos h]
        rfl
      · refine le_iSup_of_le none (le_of_eq ?_)
        simp only [I, x, Option.elim, FractionalIdeal.coe_one]
      · refine le_iSup_of_le (some (Sum.inr a)) (le_of_eq ?_)
        simp only [I, x, Option.elim, Sum.elim_inr, if_neg (not_lt.2 h)]
        rfl
    · refine iSup_le ?_
      rintro (_ | a | a)
      · simp only [I, x, Option.elim, FractionalIdeal.coe_one]
        exact le_sup_of_le_left le_sup_right
      · refine le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left ?_))
        exact le_iSup_of_le a le_rfl
      · by_cases h : a.val < N.j
        · simp only [I, x, Option.elim, Sum.elim_inr, if_pos h]
          refine le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right ?_))
          exact le_iSup₂_of_le a h le_rfl
        · simp only [I, x, Option.elim, Sum.elim_inr, if_neg h]
          refine le_sup_of_le_right ?_
          exact le_iSup₂_of_le a (not_lt.1 h) le_rfl
  have hle : ∀ o, line (I o : Submodule (𝓞 K) K) (x o) ≤ N.P0 := fun o => by
    rw [hP]; exact le_iSup (fun o => line (I o : Submodule (𝓞 K) K) (x o)) o
  let σ : Fin (2 * r + 1) ≃ Option (Fin r ⊕ Fin r) := Fintype.equivOfCardEq (by simp; ring)
  refine ⟨fun i => u (I (σ i)) (x (σ i)), fun i => hle _ (hu _ _), ?_⟩
  conv_lhs => rw [hP]
  refine iSup_le fun o => (hu' _ _).trans (sup_le_sup (Submodule.smul_mono le_rfl (hle o)) ?_)
  exact Submodule.span_mono (Set.singleton_subset_iff.2 ⟨σ.symm o, by simp⟩)
end GlobalTheory.DegCnt.NearCount
