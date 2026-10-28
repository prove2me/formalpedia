-- Prove2me | solution 1 for OAI.MetricKMedian.Reduction.Serving.bad_count_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:08:19.471455+00:00
-- url     : https://prove2.me/submissions/3848e906-ba3d-40d7-a18e-be23cb935425

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K023
import Definitions.Def_OAIQ035K024
import Definitions.Def_OAIQ035K026

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_DeletionGeometry
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
variable {U : Finset (Fin I.n)}

theorem groupCost_nonneg (D : Serving (I:=I) U) (t : ↥U) : 0 ≤ D.groupCost t :=
  sum_nonneg (fun j _ => I.nearest_nonneg j U)

theorem groupCost_total (D : Serving (I:=I) U) : ∑ t, D.groupCost t=cost I U := by
  change (∑ t : ↥U, ∑ j with D.assignment j=t, nearest I j U)=cost I U
  calc
    _ = ∑ j : ↥I.clients, nearest I j U := sum_fiberwise univ D.assignment (fun j => nearest I j U)
    _ = cost I U := sum_coe_sort I.clients (fun j => nearest I j U)

attribute [local instance] OAI.MetricKMedian.Reduction.deletionGeometryPseudoMetricSpace
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseDeletion
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_BadCenterBound
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

theorem bad_count_s35_oai (D : Serving (I:=I) U) (hUF : U ⊆ F)
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

theorem solution : type_of% @OAI.MetricKMedian.Reduction.Serving.bad_count_s35_oai := @OAI.MetricKMedian.Reduction.Serving.bad_count_s35_oai
