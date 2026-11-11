-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:23:27.265064+00:00
-- url     : https://prove2.me/submissions/a65071e0-a4a3-49d4-8b01-89928658e56a

import Mathlib
import Definitions.Def_Q238K015
import Theorems.Thm_OAI_MetricKMedianRecovery_Anchoring_anchoring_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_AllBad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralCandidates
open LocalSearch Anchoring Completion Sampling
variable {V : Type*} [MetricSpace V] [LinearOrder V] [Fintype V]

omit [Fintype V] in

theorem separated_comparison_s238_oai (F D O S : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
    (hO2 : 2 ≤ O.card) (hOF : O ⊆ F) (hSF : S ⊆ F) (hcard : S.card = O.card)
    (hlocal : WidthLocalMin F D S 5) (beta : ℝ) (hbeta : 0 < beta) (hP : 0 < cost D O)
    (hsep : ∀ i ∈ O, beta*cost D O ≤
      ((Anchoring.cluster D (LocalSearch.nearest O hO) i).card:ℝ)*separation O i) :
    ∃ C : Comparison D S O,
      C.assign = LocalSearch.nearest O hO ∧ (C.bad.card:ℝ) ≤ countConstant (1/100)/beta := by
  let b := beta*cost D O
  have hb : 0 < b := mul_pos hbeta hP
  have hshort : shortCenters O (clusterScale D O (LocalSearch.nearest O hO)) b = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hh := Finset.mem_filter.mp hi
    exact (not_lt.mpr (hsep i hh.1)) hh.2
  have hscale : b*((S.card:ℝ)-O.card+
      (shortCenters O (clusterScale D O (LocalSearch.nearest O hO)) b).card) ≤ 10*cost D O := by
    simp only [hshort,Finset.card_empty,hcard,sub_self,Nat.cast_zero,add_zero,mul_zero]
    positivity
  obtain ⟨G,B,hpart,hdis,hinj,hmem,hproxy,hcount⟩ :=
    anchoring_s238 F D O S hO hS hO2 hSF hOF (by omega) hlocal b (1/100) hb hP
      (by norm_num) (by norm_num) hscale
  have hGO : G ⊆ O := by rw [← hpart]; exact Finset.subset_union_left
  let C : Comparison D S O := {
    assign := LocalSearch.nearest O hO
    assigned := fun p _ => nearest_mem O hO p
    nearest := fun p _ i hi => (nearest_distance O hO p).trans_le (connection_le hi)
    good := G
    good_subset := hGO
    proxy := LocalSearch.nearest S hS
    proxy_mem := hmem
    proxy_inj := hinj
    same_card := hcard
    proxy_cost := by
      rw [comparisonCost_nearest]
      exact hproxy }
  have hbad : C.bad = B := by
    change O \ G = B
    ext i
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hi,hng⟩
      rw [← hpart] at hi
      rcases Finset.mem_union.mp hi with hg | hb
      · exact False.elim (hng hg)
      · exact hb
    · intro hi
      refine ⟨?_,?_⟩
      · rw [← hpart]
        exact Finset.mem_union_right _ hi
      · exact fun hg => Finset.disjoint_left.mp hdis hg hi
  refine ⟨C,rfl,?_⟩
  rw [hbad]
  have he : countConstant (1/100)*cost D O/b = countConstant (1/100)/beta := by
    dsimp [b]
    field_simp
  exact hcount.trans_eq he

end MetricKMedianRecovery.IntegralCandidates

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison_s238_oai.{u_1}
