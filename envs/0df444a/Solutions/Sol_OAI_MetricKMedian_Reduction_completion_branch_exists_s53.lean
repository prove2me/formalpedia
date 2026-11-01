-- Prove2me | solution 1 for OAI.MetricKMedian.Reduction.completion_branch_exists_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:21:47.338001+00:00
-- url     : https://prove2.me/submissions/33a1d59c-891b-4ebb-8e37-e4e79ad2df0a

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K037
import Theorems.Thm_OAI_MetricKMedian_Reduction_CloseCenters_completionSet_spec_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_DeletionGeometry
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

attribute [local instance] OAI.MetricKMedian.Reduction.deletionGeometryPseudoMetricSpace
theorem serving_exists (U : Finset (Fin I.n)) (hk : I.k < U.card) :
    Nonempty (Serving (I:=I) U) := by
  classical
  have hU : U.Nonempty := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hk)
  have has : ∀ j : ↥I.clients, ∃ u : ↥U, dist j.val u.val=nearest I j U := by
    intro j
    obtain ⟨u,hu,he⟩ := I.nearest_attained j U hU
    exact ⟨⟨u,hu⟩,he.symm⟩
  choose a ha using has
  have hot : ∀ t : ↥U, ∃ u : ↥U, u ≠ t ∧ ∀ v : ↥U, v ≠ t → dist t.val u.val ≤ dist t.val v.val := by
    intro t
    have hE : (U.erase t.val).Nonempty := by
      apply card_pos.mp
      rw [card_erase_of_mem t.property]
      have hkp := I.k_pos
      omega
    obtain ⟨u,hu,he⟩ := I.nearest_attained t (U.erase t.val) hE
    refine ⟨⟨u,(mem_erase.mp hu).2⟩,?_,?_⟩
    · intro hh
      exact (mem_erase.mp hu).1 (congrArg Subtype.val hh)
    · intro v hv
      have hv' : v.val ≠ t.val := fun hh => hv (Subtype.ext hh)
      have hb := I.nearest_le t (mem_erase.mpr ⟨hv',v.property⟩)
      rw [he] at hb
      exact hb
  choose other hne hnear using hot
  exact ⟨⟨a,ha,other,hne,hnear⟩⟩

namespace Serving
variable {U : Finset (Fin I.n)}

attribute [local instance] OAI.MetricKMedian.Reduction.deletionGeometryPseudoMetricSpace
theorem radius_nonneg (D : Serving (I:=I) U) (t : ↥U) : 0 ≤ D.radius t := dist_nonneg

theorem groupCost_nonneg (D : Serving (I:=I) U) (t : ↥U) : 0 ≤ D.groupCost t :=
  sum_nonneg (fun j _ => I.nearest_nonneg j U)

theorem groupCost_total (D : Serving (I:=I) U) : ∑ t, D.groupCost t=cost I U := by
  change (∑ t : ↥U, ∑ j with D.assignment j=t, nearest I j U)=cost I U
  calc
    _ = ∑ j : ↥I.clients, nearest I j U := sum_fiberwise univ D.assignment (fun j => nearest I j U)
    _ = cost I U := sum_coe_sort I.clients (fun j => nearest I j U)

theorem deletion_bound (D : Serving (I:=I) U) (t : ↥U) :
    cost I (U.erase t.val)-cost I U ≤ (D.group t).card*D.radius t := by
  have hpoint : ∀ j : ↥I.clients, nearest I j (U.erase t.val)-nearest I j U ≤
      if D.assignment j=t then D.radius t else 0 := by
    intro j
    by_cases hj : D.assignment j=t
    · rw [ite_eq_left hj]
      have ho : (D.other t).val ∈ U.erase t.val := by
        apply mem_erase.mpr
        exact ⟨fun he => D.other_ne t (Subtype.ext he),(D.other t).property⟩
      have hnear := I.nearest_le j ho
      have htri := dist_triangle j.val t.val (D.other t).val
      have hex : dist j.val t.val=nearest I j U := by simpa only [hj] using D.assignment_cost j
      change nearest I j (U.erase t.val) ≤ dist j.val (D.other t).val at hnear
      dsimp only [radius]
      linarith only [hnear,htri,hex]
    · rw [ite_eq_right hj]
      have ha : (D.assignment j).val ∈ U.erase t.val := by
        exact mem_erase.mpr ⟨fun he => hj (Subtype.ext he),(D.assignment j).property⟩
      have hnear := I.nearest_le j ha
      change nearest I j (U.erase t.val) ≤ dist j.val (D.assignment j).val at hnear
      rw [D.assignment_cost j] at hnear
      linarith only [hnear]
  calc
    cost I (U.erase t.val)-cost I U = ∑ j : ↥I.clients,
        (nearest I j (U.erase t.val)-nearest I j U) := by
          rw [sum_sub_distrib]
          rw [sum_coe_sort I.clients (fun j => nearest I j (U.erase t.val)),
            sum_coe_sort I.clients (fun j => nearest I j U)]
          rfl
    _ ≤ ∑ j : ↥I.clients, if D.assignment j=t then D.radius t else 0 :=
      sum_le_sum (fun j _ => hpoint j)
    _ = (D.group t).card*D.radius t := by
      rw [← sum_filter]
      simp only [group,sum_const,nsmul_eq_mul]

end Serving
end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_CompletionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable (I : Instance)

namespace CloseCenters
variable {I} {G O : Finset (Fin I.n)} {δ : ℝ}

attribute [local instance] OAI.MetricKMedian.Reduction.completionGeometryPseudoMetricSpace
theorem match_injective (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ < 1/2) :
    Function.Injective C.matchTo := by
  intro t u he
  by_contra htu
  have ht := C.close t
  have hu := C.close u
  have hrt := C.separated t u htu
  have hru : C.radius u ≤ dist t.val u.val := by
    simpa only [dist_comm] using C.separated u t (Ne.symm htu)
  have hh := dist_triangle t.val (C.matchTo t) u.val
  rw [he] at ht
  rw [he,dist_comm (C.matchTo u) u.val] at hh
  have hm1 := mul_le_mul_of_nonneg_left hrt hδ
  have hm2 := mul_le_mul_of_nonneg_left hru hδ
  have hd := dist_nonneg (x:=t.val) (y:=u.val)
  have hp := mul_nonneg (show 0 ≤ 1-2*δ by linarith) hd
  linarith only [ht,hu,hh,hm1,hm2,hp]

end CloseCenters
end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_LocalCompletion
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

namespace CloseCenters
variable {G O : Finset (Fin I.n)} {δ : ℝ}

attribute [local instance] OAI.MetricKMedian.Reduction.localCompletionPseudoMetricSpace
theorem matched_sub (C : CloseCenters I G O δ) : C.matched ⊆ O := by
  intro i hi
  obtain ⟨t,_,rfl⟩ := mem_image.mp hi
  exact C.match_mem t

end CloseCenters
end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_CloseFromServing
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

namespace Serving
variable {U O : Finset (Fin I.n)} {δ : ℝ}

attribute [local instance] OAI.MetricKMedian.Reduction.closeFromServingPseudoMetric
theorem good_close (D : Serving (I:=I) U) (t : ↥(D.good O δ)) :
    nearest I t O < δ*D.radius ⟨t.val,D.good_sub t.property⟩ := by
  obtain ⟨u,hu,he⟩ := mem_image.mp t.property
  have hn : ¬δ*D.radius u ≤ nearest I u O := by
    intro hb
    exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨mem_univ _,hb⟩)
  have heq : u=⟨t.val,D.good_sub t.property⟩ := Subtype.ext he
  rw [heq] at hn
  exact lt_of_not_ge hn

theorem good_bad_card (D : Serving (I:=I) U) :
    (D.good O δ).card+(D.bad O δ).card=U.card := by
  rw [good,card_image_of_injective _ Subtype.val_injective,
    card_sdiff_add_card_eq_card (subset_univ _),card_univ,Fintype.card_coe]

theorem closeCenters_exists (D : Serving (I:=I) U) (hO : O.Nonempty) :
    ∃ C : CloseCenters I (D.good O δ) O δ,
      ∀ t, C.radius t=D.radius ⟨t.val,D.good_sub t.property⟩ := by
  have hm : ∀ t : ↥(D.good O δ), ∃ o ∈ O, nearest I t O=dist t.val o := by
    intro t
    exact I.nearest_attained t O hO
  choose m hm hdist using hm
  refine ⟨⟨(fun t => D.radius ⟨t.val,D.good_sub t.property⟩),
    (fun t => D.radius_nonneg _),?_,m,hm,?_⟩,fun _ => rfl⟩
  · intro t u htu
    apply D.other_nearest ⟨t.val,D.good_sub t.property⟩ ⟨u.val,D.good_sub u.property⟩
    intro he
    exact htu (Subtype.ext (congrArg Subtype.val he).symm)
  · intro t
    rw [← hdist t]
    exact D.good_close t

theorem backup_card_bound (D : Serving (I:=I) U)
    (C : CloseCenters I (D.good O δ) O δ) (hδ : 0 ≤ δ) (hsmall : δ < 1/2)
    (hk : O.card ≤ U.card) : C.backup.card ≤ (D.bad O δ).card := by
  have hc := card_sdiff_add_card_eq_card C.matched_sub
  have hm : C.matched.card=(D.good O δ).card := by
    rw [CloseCenters.matched,card_image_of_injective _ (C.match_injective hδ hsmall),
      card_univ,Fintype.card_coe]
  change C.backup.card+C.matched.card=O.card at hc
  rw [hm] at hc
  have htotal := D.good_bad_card (O:=O) (δ:=δ)
  omega

end Serving
end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseDeletion
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.Input.distance_client_facility _root_.OAI.MetricKMedian.Instance.restrict_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

namespace Serving
variable {U O F : Finset (Fin I.n)} {ρ δ : ℝ}

attribute [local instance] OAI.MetricKMedian.Reduction.sparseDeletionPseudoMetricSpace
theorem sparse_deletion (D : Serving (I:=I) U) (hUF : U ⊆ F) (hsp : Sparse (I:=I) F O ρ)
    (hδ : 0 ≤ δ) (t : ↥U) (hbad : δ*D.radius t ≤ nearest I t O) :
    δ*(cost I (U.erase t.val)-cost I U) ≤ ρ*cost I O+3*D.groupCost t := by
  classical
  let N : Finset ↥I.clients := (D.group t).filter (fun (j : ↥I.clients) => nearest I j U < δ*D.radius t/3)
  have hNsub : N.image (fun j => j.val) ⊆ denseBall (I:=I) O t := by
    intro j hj
    obtain ⟨j',hj',rfl⟩ := mem_image.mp hj
    obtain ⟨hg,hn⟩ := mem_filter.mp hj'
    have hassign : D.assignment j'=t := (mem_filter.mp hg).2
    have hdist : dist j'.val t.val=nearest I j' U := by
      simpa only [hassign] using D.assignment_cost j'
    apply mem_filter.mpr
    refine ⟨j'.property,?_⟩
    rw [hdist]
    exact hn.trans_le (div_le_div_of_nonneg_right hbad (by norm_num))
  have hcard : N.card ≤ (denseBall (I:=I) O t).card := by
    rw [← card_image_of_injective N (f:=fun j : ↥I.clients => j.val) Subtype.val_injective]
    exact card_le_card hNsub
  have hnear : (N.card:ℝ)*(δ*D.radius t) ≤ ρ*cost I O := by
    calc
      _ ≤ N.card*nearest I t O := mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg _)
      _ ≤ (denseBall (I:=I) O t).card*nearest I t O :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (I.nearest_nonneg t O)
      _ ≤ _ := by simpa only [mul_comm] using hsp t (hUF t.property)
  have hp : ∀ j ∈ D.group t, δ*D.radius t ≤
      (if nearest I j U < δ*D.radius t/3 then δ*D.radius t else 0)+3*nearest I j U := by
    intro j _
    split_ifs with hj
    · have hn := I.nearest_nonneg j U
      linarith only [hn]
    · have hn := le_of_not_gt hj
      linarith only [hn]
  have hsum := sum_le_sum hp
  have heleft : (∑ _j ∈ D.group t, δ*D.radius t)=(D.group t).card*(δ*D.radius t) := by
    simp only [sum_const,nsmul_eq_mul]
  have heright : (∑ j ∈ D.group t,
      ((if nearest I j U < δ*D.radius t/3 then δ*D.radius t else 0)+3*nearest I j U)) =
      N.card*(δ*D.radius t)+3*D.groupCost t := by
    rw [sum_add_distrib,← mul_sum,← sum_filter]
    simp only [N,groupCost,sum_const,nsmul_eq_mul]
  rw [heleft,heright] at hsum
  have hdel := mul_le_mul_of_nonneg_left (D.deletion_bound t) hδ
  calc
    _ ≤ δ*((D.group t).card*D.radius t) := hdel
    _ = (D.group t).card*(δ*D.radius t) := by ring
    _ ≤ N.card*(δ*D.radius t)+3*D.groupCost t := hsum
    _ ≤ _ := add_le_add hnear le_rfl

theorem bad_count_charge (D : Serving (I:=I) U) (hUF : U ⊆ F)
    (hsp : Sparse (I:=I) F O ρ) (hδ : 0 ≤ δ) (B : ℝ)
    (hstuck : ∀ t : ↥U, B ≤ cost I (U.erase t.val)-cost I U) :
    let H := univ.filter (fun t : ↥U => δ*D.radius t ≤ nearest I t O)
    (H.card:ℝ)*(δ*B-ρ*cost I O) ≤ 3*cost I U := by
  classical
  dsimp only
  let H := univ.filter (fun t : ↥U => δ*D.radius t ≤ nearest I t O)
  have hpoint : ∀ t ∈ H, δ*B-ρ*cost I O ≤ 3*D.groupCost t := by
    intro t ht
    have hc := D.sparse_deletion hUF hsp hδ t (mem_filter.mp ht).2
    have hd := mul_le_mul_of_nonneg_left (hstuck t) hδ
    linarith only [hc,hd]
  have hsum := sum_le_sum hpoint
  simp only [sum_const,nsmul_eq_mul,← mul_sum] at hsum
  have hcost : (∑ t ∈ H, D.groupCost t) ≤ cost I U := by
    rw [← D.groupCost_total]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun t _ _ => D.groupCost_nonneg t)
  exact hsum.trans (mul_le_mul_of_nonneg_left hcost (by norm_num))

end Serving
end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_BadCenterBound
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.Input.distance_client_facility _root_.OAI.MetricKMedian.Instance.restrict_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

namespace Serving
variable {U F O : Finset (Fin I.n)}

local instance badCenterBoundPseudoMetric_r232ccb_1 : PseudoMetricSpace (Fin I.n) := I.pseudoMetric
theorem bad_count (D : Serving (I:=I) U) (hUF : U ⊆ F)
    (α δ η : ℝ) (c : ℕ) (hc : 0 < c) (hδ : 0 < δ) (hη : 0 < η)
    (hC : 0 < cost I O) (hcost : cost I U ≤ α*cost I O)
    (hsp : Sparse (I:=I) F O (δ*η/(2*c)))
    (hstuck : ∀ t : ↥U, η*cost I O/c ≤ cost I (U.erase t.val)-cost I U) :
    ((D.bad O δ).card:ℝ) ≤ 6*α*c/(δ*η) := by
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hcharge := D.bad_count_charge hUF hsp hδ.le (η*cost I O/c) hstuck
  change ((D.bad O δ).card:ℝ)*(δ*(η*cost I O/c)-(δ*η/(2*c))*cost I O) ≤ 3*cost I U at hcharge
  have heq : δ*(η*cost I O/c)-(δ*η/(2*c))*cost I O=
      (δ*η/(2*c))*cost I O := by field_simp; ring
  rw [heq] at hcharge
  have hh := hcharge.trans (mul_le_mul_of_nonneg_left hcost (by norm_num : (0:ℝ) ≤ 3))
  have hh' : ((D.bad O δ).card:ℝ)*(δ*η/(2*c)) ≤ 3*α := by
    apply (mul_le_mul_iff_left₀ hC).mp
    nlinarith only [hh]
  have hdiv : ((D.bad O δ).card:ℝ)*(δ*η) ≤ 6*α*c := by
    have hh'' := (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) hcR)).mp
      (show (((D.bad O δ).card:ℝ)*(δ*η))/(2*c) ≤ 3*α by simpa only [mul_div_assoc] using hh')
    nlinarith only [hh'']
  exact (le_div_iff₀ (mul_pos hδ hη)).mpr hdiv

end Serving
end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_RationalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

theorem mem_deletionChoices {I : Type} [DecidableEq I] (T D : Finset I) (c : ℕ) :
    D ∈ deletionChoices T c ↔ D ⊆ T ∧ D.card ≤ c := by
  simp only [deletionChoices,mem_biUnion,mem_range,mem_powersetCard]
  constructor
  · rintro ⟨m,hm,hsub,hcard⟩
    exact ⟨hsub,by omega⟩
  · rintro ⟨hsub,hcard⟩
    exact ⟨D.card,by omega,hsub,rfl⟩

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_CompletionEnumeration
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

namespace Serving
variable {U O : Finset (Fin I.n)} {δ : ℝ}

local instance completionEnumerationPseudoMetric_r232ccb_1 : PseudoMetricSpace (Fin I.n) := I.pseudoMetric
theorem radius_rational (D : Serving (I:=I) U) (t : ↥U) :
    D.radius t=(rationalRadii I U t.val:ℝ) := by
  rw [rationalRadii,I.cast_rationalNearest]
  have ho : (D.other t).val ∈ U.erase t.val := mem_erase.mpr
    ⟨fun he => D.other_ne t (Subtype.ext he),(D.other t).property⟩
  apply le_antisymm
  · obtain ⟨u,hu,he⟩ := I.nearest_attained t (U.erase t.val) ⟨_,ho⟩
    rw [he]
    exact D.other_nearest t ⟨u,(mem_erase.mp hu).2⟩
      (fun he => (mem_erase.mp hu).1 (congrArg Subtype.val he))
  · exact I.nearest_le t ho

theorem badSet_sub (D : Serving (I:=I) U) : D.badSet O δ ⊆ U := by
  intro i hi
  obtain ⟨t,_,rfl⟩ := mem_image.mp hi
  exact t.property

theorem badSet_card (D : Serving (I:=I) U) : (D.badSet O δ).card=(D.bad O δ).card :=
  card_image_of_injective _ Subtype.val_injective

theorem sdiff_badSet (D : Serving (I:=I) U) : U \ D.badSet O δ=D.good O δ := by
  ext i
  constructor
  · intro hi
    obtain ⟨hiU,hiH⟩ := mem_sdiff.mp hi
    refine mem_image.mpr ⟨⟨i,hiU⟩,mem_sdiff.mpr ⟨mem_univ _,?_⟩,rfl⟩
    intro hb
    exact hiH (mem_image_of_mem _ hb)
  · intro hi
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hi
    refine mem_sdiff.mpr ⟨t.property,?_⟩
    intro hb
    obtain ⟨u,hu,he⟩ := mem_image.mp hb
    have heq : u=t := Subtype.ext he
    rw [heq] at hu
    exact (mem_sdiff.mp ht).2 hu

end Serving

local instance completionEnumerationPseudoMetric_r232ccb_2 : PseudoMetricSpace (Fin I.n) := I.pseudoMetric
theorem completion_branch_exists_s53_oai (F O U : Finset (Fin I.n)) (hOF : O ⊆ F)
    (hO : O.Nonempty) (hk : O.card=I.k) (hUF : U ⊆ F) (hU : I.k < U.card)
    (α η : ℝ) (δ : ℚ) (c b : ℕ) (hc : 0 < c) (hδ : 0 < (δ:ℝ))
    (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η) (hC : 0 < cost I O)
    (hcost : cost I U ≤ α*cost I O)
    (hsp : Sparse (I:=I) F O ((δ:ℝ)*η/(2*c)))
    (hstuck : ∀ i ∈ U, η*cost I O/c ≤ cost I (U.erase i)-cost I U)
    (hb : 6*α*c/((δ:ℝ)*η) ≤ (b:ℝ)) :
    ∃ S ∈ completionBranches I F U δ b,
      S ⊆ F ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (1+12*(δ:ℝ))*cost I O := by
  classical
  obtain ⟨D⟩ := serving_exists U hU
  have hbad : (D.bad O (δ:ℝ)).card ≤ b := by
    have hh := (D.bad_count hUF α (δ:ℝ) η c hc hδ hη hC hcost hsp
      (fun t => hstuck t.val t.property)).trans hb
    exact_mod_cast hh
  obtain ⟨C,hr⟩ := D.closeCenters_exists (δ:=(δ:ℝ)) hO
  have hbackup : C.backup.card ≤ b :=
    (D.backup_card_bound C hδ.le (by linarith) (by omega)).trans hbad
  have hBsub : C.backup ⊆ F := sdiff_subset.trans hOF
  have hH : D.badSet O (δ:ℝ) ∈ deletionChoices U b := by
    apply (mem_deletionChoices _ _ _).mpr
    exact ⟨D.badSet_sub,by rw [D.badSet_card]; exact hbad⟩
  have hB : C.backup ∈ deletionChoices F b := (mem_deletionChoices _ _ _).mpr ⟨hBsub,hbackup⟩
  have hrat : ∀ t, C.radius t=(rationalRadii I U t.val:ℝ) := fun t =>
    (hr t).trans (D.radius_rational _)
  let S := completionSet I F C.backup (D.good O (δ:ℝ)) (rationalRadii I U) δ
  have hspec := C.completionSet_spec_s53 hδ.le hsmall hO F hOF (rationalRadii I U) hrat
  refine ⟨S,?_,hspec.1,hspec.2.1,?_,hspec.2.2.2⟩
  · apply mem_image.mpr
    refine ⟨(D.badSet O (δ:ℝ),C.backup),mem_product.mpr ⟨hH,hB⟩,?_⟩
    simp only [D.sdiff_badSet,S]
  · exact hspec.2.2.1.trans_eq hk

end MetricKMedian.Reduction
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Reduction.completion_branch_exists_s53_oai := @OAI.MetricKMedian.Reduction.completion_branch_exists_s53_oai
