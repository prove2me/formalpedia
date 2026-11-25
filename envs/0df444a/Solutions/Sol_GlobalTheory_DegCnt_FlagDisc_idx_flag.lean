-- Prove2me | solution 1 for GlobalTheory.DegCnt.FlagDisc.idx_flag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:48:55.501691+00:00
-- url     : https://prove2.me/submissions/dd5156b7-f224-4e8b-99aa-85eb165a552e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinor
import Theorems.Thm_GlobalTheory_DegCnt_FlagDisc_idx_sum
import Theorems.Thm_GlobalTheory_DegCnt_FlagDisc_Xa_succ
import Theorems.Thm_GlobalTheory_DegCnt_FlagDisc_eq_zero_of_smul_mem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_inf_left
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_mul
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_sup
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
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FlagDisc
open GlobalTheory.DegCnt.DelScale GlobalTheory.DegCnt.Absorb
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [NumberField K]
namespace GlobalTheory.DegCnt.FlagDisc
theorem _root_.solution (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (y : Fin r → V) (hy : ∀ a, y a ∈ Λ)
    (he : ∀ a, F.e a.castSucc - y a ∈ F.Xa a.val) (n : ℕ → ℝ)
    (hn : ∀ a : Fin r, (idx (lead F Λ a.castSucc) 1 : ℝ) = n a.val) : ∀ l ≤ r,
    Submodule.span K (y '' {a | a.val < l}) = F.Xa l ∧
      Submodule.span (𝓞 K) (y '' {a | a.val < l}) ≤ latF F Λ l ∧
      (idx (latF F Λ l) (Submodule.span (𝓞 K) (y '' {a | a.val < l})) : ℝ) = ∏ a ∈ Finset.range l, n a := by
  intro l
  induction l with
  | zero => intro _; simp [FlagD.Xa, latF, idx]
  | succ l ih =>
    intro hl
    obtain ⟨h1, h2, h3⟩ := ih (Nat.le_of_succ_le hl)
    set a : Fin r := ⟨l, hl⟩ with ha
    have es : y '' {b | b.val < l + 1} = y '' {b | b.val < l} ∪ {y a} := by
      rw [← Set.image_singleton, ← Set.image_union]
      congr 1
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff, ha]
      omega
    have hX : F.Xa (l + 1) = F.Xa l ⊔ Submodule.span K {F.e a.castSucc} := Xa_succ F a
    have hea : F.e a.castSucc - y a ∈ F.Xa l := he a
    have hz : ∀ t : K, t • F.e a.castSucc ∈ F.Xa l → t = 0 := fun t => eq_zero_of_smul_mem F a
    have hle : F.Xa l ≤ F.Xa (l + 1) := hX ▸ le_sup_left
    have hya : y a ∈ F.Xa (l + 1) := by
      have : F.e a.castSucc ∈ F.Xa (l + 1) := hX ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      simpa using sub_mem this (hle hea)
    have hA : latF F Λ l ≤ latF F Λ (l + 1) := inf_le_inf_left _ hle
    have hY : Submodule.span (𝓞 K) {y a} ≤ latF F Λ (l + 1) :=
      (Submodule.span_singleton_le_iff_mem _ _).2 ⟨hy a, hya⟩
    rw [es, Submodule.span_union, Submodule.span_union, h1]
    refine ⟨le_antisymm (sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).2 hya)) ?_,
      sup_le (h2.trans hA) hY, ?_⟩
    · rw [hX]
      refine sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
      simpa using Submodule.add_mem_sup hea (Submodule.mem_span_singleton_self (R := K) (y a))
    have hd : latF F Λ l ⊓ Submodule.span (𝓞 K) {y a} = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨⟨-, hv⟩, hv'⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv'
      have hv : c • y a ∈ F.Xa l := hv
      rw [← algebraMap_smul K c] at hv ⊢
      have := add_mem ((F.Xa l).smul_mem (algebraMap (𝓞 K) K c) hea) hv
      rw [smul_sub, sub_add_cancel] at this
      rw [hz _ this, zero_smul]
      exact zero_mem _
    rw [← idx_mul (sup_le_sup_right h2 _) (sup_le hA hY), idx_sum h2 le_rfl hd, Finset.prod_range_succ, ← h3,
      ← show _ = n l from hn a]
    have e0 : idx (Submodule.span (𝓞 K) {y a}) (Submodule.span (𝓞 K) {y a}) = 1 := by simp [idx]
    rw [e0, mul_one, Nat.cast_mul]
    congr 2
    set T : Submodule (𝓞 K) V := Submodule.span (𝓞 K) {y a} ⊔ rs (𝓞 K) (F.Xa l) with hT
    set f : K →ₗ[𝓞 K] V := (LinearMap.toSpanSingleton K V (F.e a.castSucc)).restrictScalars (𝓞 K) with hf
    have e1 : T ⊓ latF F Λ (l + 1) = Submodule.span (𝓞 K) {y a} ⊔ latF F Λ l := by
      rw [hT, sup_inf_assoc_of_le _ hY]
      congr 1
      exact le_antisymm (fun v hv => ⟨hv.2.1, hv.1⟩) fun v hv => ⟨hv.2, hA hv⟩
    have e2 : T.comap f = 1 := by
      ext t
      change t • F.e a.castSucc ∈ T ↔ _
      constructor
      · intro h
        obtain ⟨v, hv, w, hw, e⟩ := Submodule.mem_sup.1 h
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
        refine Submodule.mem_one.2 ⟨c, (sub_eq_zero.1 (hz _ ?_)).symm⟩
        have := sub_mem (show w ∈ F.Xa l from hw) ((F.Xa l).smul_mem (algebraMap (𝓞 K) K c) hea)
        convert this using 1
        rw [sub_smul, ← e, smul_sub, algebraMap_smul, algebraMap_smul]
        abel
      · intro h
        obtain ⟨c, rfl⟩ := Submodule.mem_one.1 h
        rw [algebraMap_smul]
        refine T.smul_mem c ?_
        simpa using Submodule.add_mem_sup (Submodule.mem_span_singleton_self (R := 𝓞 K) (y a))
          (show _ ∈ rs (𝓞 K) (F.Xa l) from hea)
    have e3 : (lead F Λ a.castSucc).map f ⊔ rs (𝓞 K) (F.Xa l) = latF F Λ (l + 1) ⊔ rs (𝓞 K) (F.Xa l) := by
      refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
      · rintro _ ⟨t, ht, rfl⟩
        have ht' : t • F.e a.castSucc ∈ Λ ⊔ rs (𝓞 K) (F.Xa l) := ht
        obtain ⟨v, hv, w, hw, e⟩ := Submodule.mem_sup.1 ht'
        refine Submodule.mem_sup.2 ⟨v, ⟨hv, ?_⟩, w, hw, e⟩
        rw [eq_sub_of_add_eq e]
        refine sub_mem (show _ ∈ F.Xa (l + 1) from ?_) (hle hw)
        rw [hX]
        exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      · rintro v ⟨hv, hv'⟩
        have hv' : v ∈ F.Xa (l + 1) := hv'
        rw [hX] at hv'
        obtain ⟨w, hw, u, hu, e⟩ := Submodule.mem_sup.1 hv'
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hu
        refine Submodule.mem_sup.2 ⟨_, ⟨t, ?_, rfl⟩, w, hw, (add_comm _ _).trans e⟩
        change t • F.e a.castSucc ∈ Λ ⊔ rs (𝓞 K) (F.Xa l)
        rw [eq_sub_of_add_eq' e]
        exact sub_mem (Submodule.mem_sup_left hv) (Submodule.mem_sup_right hw)
    rw [sup_comm, ← e1, inf_comm, idx_inf_left, ← idx_sup (I := rs (𝓞 K) (F.Xa l)) le_sup_right, ← e3,
      idx_sup le_sup_right, ← e2]
    exact (AddSubgroup.relIndex_comap T.toAddSubgroup f.toAddMonoidHom (lead F Λ a.castSucc).toAddSubgroup).symm
end GlobalTheory.DegCnt.FlagDisc
