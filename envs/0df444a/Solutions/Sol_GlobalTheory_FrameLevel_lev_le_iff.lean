-- Prove2me | solution 1 for GlobalTheory.FrameLevel.lev_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:02:36.042959+00:00
-- url     : https://prove2.me/submissions/d1d8fdec-8f04-48f9-bdf0-dde9e98c2494

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSte
import Theorems.Thm_GlobalTheory_FrameLevel_exists_coords
import Theorems.Thm_GlobalTheory_FrameLevel_exists_coords_Mof
import Theorems.Thm_GlobalTheory_FrameLevel_th_ne_zero
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameLevel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameLevel
theorem _root_.solution {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g g' : Fin (r + 1) → S.V)
    (y : S.V) (hy : y ∈ S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1)) (j : ℕ) :
    S.lev g g' (algebraMap F E S.th • y) ≤ j ↔
      ∃ y₁ ∈ S.spanTo g j ⊔ S.spanTo g' j, y - y₁ ∈ S.Mof g g' := by
  constructor
  · intro hle
    unfold Frames.lev at hle
    obtain ⟨u, hu, u', hu', huy⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, hc, -⟩ := exists_coords S g (r + 1) hu
    obtain ⟨c', hc', -⟩ := exists_coords S g' (r + 1) hu'
    obtain ⟨al, al', hrep, hRR⟩ := Nat.sInf_mem (s := {j | ∃ al al' : Fin (r + 1) → E,
        algebraMap F E S.th • y = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
        ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i)})
      ⟨r + 1, fun i => algebraMap F E S.th * c i, fun i => algebraMap F E S.th * c' i, by
        rw [← huy, hc, hc', smul_add, Finset.smul_sum, Finset.smul_sum]
        simp only [smul_smul], fun i hi => absurd hi (not_le.mpr i.isLt)⟩
    have hRR' : ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i) := fun i hi => hRR i (le_trans hle hi)
    have htt : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (th_ne_zero S), map_one]
    have hyy : y = algebraMap F E S.th⁻¹ • (∑ i, al i • g i + ∑ i, al' i • g' i) := by
      rw [← hrep, smul_smul, htt, one_smul]
    refine ⟨algebraMap F E S.th⁻¹ • (∑ i : Fin (r + 1), (if (i : ℕ) < j then al i else 0) • g i +
      ∑ i : Fin (r + 1), (if (i : ℕ) < j then al' i else 0) • g' i), ?_, ?_⟩
    · refine Submodule.smul_mem _ _ (Submodule.add_mem_sup (Submodule.sum_mem _ fun i _ => ?_)
        (Submodule.sum_mem _ fun i _ => ?_))
      · split_ifs with hi
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
        · rw [zero_smul]
          exact Submodule.zero_mem _
      · split_ifs with hi
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
        · rw [zero_smul]
          exact Submodule.zero_mem _
    · have hdiff : y - algebraMap F E S.th⁻¹ • (∑ i : Fin (r + 1), (if (i : ℕ) < j then al i else 0) • g i +
          ∑ i : Fin (r + 1), (if (i : ℕ) < j then al' i else 0) • g' i) =
          ∑ i : Fin (r + 1), algebraMap F E S.th⁻¹ • (if (i : ℕ) < j then 0 else al i • g i + al' i • g' i) := by
        rw [hyy, ← smul_sub, ← Finset.smul_sum]
        congr 1
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      rw [hdiff]
      refine Submodule.sum_mem _ fun i _ => ?_
      split_ifs with hi
      · rw [smul_zero]
        exact Submodule.zero_mem _
      · obtain ⟨hO, cc, hcc, hsum⟩ := hRR' i (not_lt.mp hi)
        have hal : al i = algebraMap F E S.th * cc - al' i := eq_sub_of_add_eq hsum
        have heq : algebraMap F E S.th⁻¹ • (al i • g i + al' i • g' i) =
            cc • g i + al' i • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by
          rw [hal]
          calc algebraMap F E S.th⁻¹ • ((algebraMap F E S.th * cc - al' i) • g i + al' i • g' i)
              = (algebraMap F E S.th⁻¹ * algebraMap F E S.th * cc) • g i +
                  al' i • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by module
            _ = cc • g i + al' i • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by rw [htt, one_mul]
        rw [heq]
        refine Submodule.add_mem _ ?_ ?_
        · exact Submodule.smul_mem (S.Mof g g') (⟨cc, hcc⟩ : L.O)
            (Submodule.subset_span (Set.mem_union_left _ ⟨i, rfl⟩))
        · exact Submodule.smul_mem (S.Mof g g') (⟨al' i, hO⟩ : L.O)
            (Submodule.subset_span (Set.mem_union_right _ ⟨i, rfl⟩))
  · rintro ⟨y₁, hy₁, hm⟩
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hy₁
    obtain ⟨a, rfl, ha⟩ := exists_coords S g j hu
    obtain ⟨a', rfl, ha'⟩ := exists_coords S g' j hu'
    obtain ⟨β, γ, hβγ⟩ := exists_coords_Mof S g g' hm
    have htt : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (th_ne_zero S), map_one]
    have hy' : y = ∑ i, ((a i + (β i : E)) • g i + a' i • g' i +
        (γ i : E) • (algebraMap F E S.th⁻¹ • (g' i - g i))) := by
      simp only [add_smul, Finset.sum_add_distrib]
      rw [eq_add_of_sub_eq hβγ]
      abel
    unfold Frames.lev
    apply Nat.sInf_le
    refine ⟨fun i => algebraMap F E S.th * a i + algebraMap F E S.th * (β i : E) - (γ i : E),
      fun i => algebraMap F E S.th * a' i + (γ i : E), ?_, fun i hi => ?_⟩
    · rw [hy', Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_add, smul_comm (algebraMap F E S.th) (γ i : E),
        smul_smul (algebraMap F E S.th) (algebraMap F E S.th⁻¹), htt, one_smul]
      module
    · unfold Frames.RR
      refine ⟨?_, (β i : E), (β i).2, ?_⟩
      · dsimp only
        rw [ha' i hi, mul_zero, zero_add]
        exact (γ i).2
      · dsimp only
        rw [ha i hi, ha' i hi]
        ring
end GlobalTheory.FrameLevel
