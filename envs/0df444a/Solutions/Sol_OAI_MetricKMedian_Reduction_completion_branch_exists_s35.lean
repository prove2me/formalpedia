-- Prove2me | solution 1 for OAI.MetricKMedian.Reduction.completion_branch_exists_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:13:10.473746+00:00
-- url     : https://prove2.me/submissions/314f13ce-6307-469b-9bc9-cf74f8ca4807

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K023
import Definitions.Def_OAIQ035K032
import Definitions.Def_OAIQ035K036
import Theorems.Thm_OAI_MetricKMedian_Reduction_CloseCenters_completionSet_spec_s35
import Theorems.Thm_OAI_MetricKMedian_Reduction_Serving_bad_count_s35

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

end Serving
end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CompletionGeometry
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_LocalCompletion
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CloseFromServing
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

attribute [local instance] OAI.MetricKMedian.Reduction.closeFromServingPseudoMetric
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalThreshold
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CompletionEnumeration
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

theorem completion_branch_exists_s35_oai (F O U : Finset (Fin I.n)) (hOF : O ⊆ F)
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
    have hh := (D.bad_count_s35 hUF α (δ:ℝ) η c hc hδ hη hC hcost hsp
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
  have hspec := C.completionSet_spec_s35 hδ.le hsmall hO F hOF (rationalRadii I U) hrat
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

theorem solution : type_of% @OAI.MetricKMedian.Reduction.completion_branch_exists_s35_oai := @OAI.MetricKMedian.Reduction.completion_branch_exists_s35_oai
