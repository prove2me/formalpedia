-- Prove2me | solution 1 for GlobalTheory.Published.SvN.average
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:40:07.780562+00:00
-- url     : https://prove2.me/submissions/dbf81152-d347-49f5-a569-3f8954254ad9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_Splits_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
variable {c : W → W → ℂ}
variable {ρ : W → Module.End ℂ M}
variable {A : AddSubgroup W} {α : W → ℂ}
namespace GlobalTheory.Published.SvN
theorem _root_.solution (hρ : Ops c ρ) (hα : Splits c A α) (U : AddSubgroup W) (hU : ∀ u ∈ U, α u = 1)
    [Fintype (A ⧸ U.addSubgroupOf A)] (m : M) (hm : ∀ u ∈ U, ρ u m = m) (a : W) (ha : a ∈ A) :
    ρ a (∑ q : A ⧸ U.addSubgroupOf A, (α q.out.1)⁻¹ • ρ q.out.1 m)
      = α a • ∑ q : A ⧸ U.addSubgroupOf A, (α q.out.1)⁻¹ • ρ q.out.1 m := by
  rw [← inv_smul_eq_iff₀ (hα.ne a ha), map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft ((⟨a, ha⟩ : A) : A ⧸ U.addSubgroupOf A)) _ _ fun q => ?_
  rw [hα.comp hρ ha q.out.2]
  set p := (Equiv.addLeft ((⟨a, ha⟩ : A) : A ⧸ U.addSubgroupOf A)) q with hp
  have h1 : (p.out : A ⧸ U.addSubgroupOf A) = ((⟨a, ha⟩ + q.out : A) : A ⧸ U.addSubgroupOf A) := by
    simp [hp]
  have h2 : -p.out.1 + (a + q.out.1) ∈ U := by
    have := QuotientAddGroup.eq.1 h1
    exact this
  have h3 := hα.comp hρ p.out.2 (A.add_mem (A.neg_mem p.out.2) (A.add_mem ha q.out.2)) m
  rw [hm _ h2, hU _ h2, add_neg_cancel_left] at h3
  rw [← h3]; simp
end GlobalTheory.Published.SvN
