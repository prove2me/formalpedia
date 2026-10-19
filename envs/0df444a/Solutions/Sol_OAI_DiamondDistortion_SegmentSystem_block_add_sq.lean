-- Prove2me | solution 1 for OAI.DiamondDistortion.SegmentSystem.block_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:13:45.762327+00:00
-- url     : https://prove2.me/submissions/f4ac9f6c-4a80-4037-b620-33d0dfc31e9e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Orthogonality.lean:L38-L65
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.SegmentSystem.block_add_sq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_primal_sq_le
import Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_test_energy_le_allow_empty

-- ---- from OAI.Analysis.DiamondDistortion.Orthogonality ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι κ : Type*} (T : SegmentSystem ι)

/-- Segment families in disjoint components spend orthogonal testing energies. -/
lemma block_add_sq (c : ι → κ)
    (hsame : ∀ S, T.IsSegment S → ∀ u ∈ S, ∀ v ∈ S, c u=c v)
    (p q : ι →₀ ℝ) (hd : Disjoint (T.colorSupport c p) (T.colorSupport c q)) :
    (T.primalSeminorm (p+q))^2 ≤ (T.primalSeminorm p)^2+(T.primalSeminorm q)^2 := by
  classical
  apply T.primal_sq_le (p+q) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  intro F
  have hz (i : Fin F.n) : (∑ v ∈ F.seg i,p v)*(∑ v ∈ F.seg i,q v)=0 := by
    by_cases hp : (∑ v ∈ F.seg i,p v)=0
    · rw [hp,zero_mul]
    by_cases hq : (∑ v ∈ F.seg i,q v)=0
    · rw [hq,mul_zero]
    obtain ⟨u,hu,hpu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
    obtain ⟨v,hv,hqv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    have he := hsame _ (F.allowed i) u hu v hv
    exact False.elim (Finset.disjoint_left.mp hd
      (Finset.mem_image.mpr ⟨u,Finsupp.mem_support_iff.mpr hpu,rfl⟩)
      (Finset.mem_image.mpr ⟨v,Finsupp.mem_support_iff.mpr hqv,he.symm⟩))
  have he (i : Fin F.n) : (∑ v ∈ F.seg i,(p+q) v)^2 =
      (∑ v ∈ F.seg i,p v)^2+(∑ v ∈ F.seg i,q v)^2 := by
    simp only [Finsupp.add_apply,Finset.sum_add_distrib]
    nlinarith [hz i]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  exact add_le_add
    (T.test_energy_le_allow_empty F.seg (fun i _ => F.allowed i) F.disjoint p)
    (T.test_energy_le_allow_empty F.seg (fun i _ => F.allowed i) F.disjoint q)

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.SegmentSystem.block_add_sq := @_root_.OAI.DiamondDistortion.SegmentSystem.block_add_sq
