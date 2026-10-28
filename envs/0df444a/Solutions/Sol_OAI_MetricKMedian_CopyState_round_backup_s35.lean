-- Prove2me | solution 1 for OAI.MetricKMedian.CopyState.round_backup_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:58:14.012737+00:00
-- url     : https://prove2.me/submissions/39b58173-8299-4c47-94a3-92e60851fa1a

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K015
import Definitions.Def_OAIQ035K016

section
-- module Solutions.OAIQ035_KM.KMedian_Process_SourceGenerator
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I : Type*} [DecidableEq I] [Fintype I]

 theorem mem_graph_erase (G : I → Finset I) (h i : I) :
    i ∈ (graphActions G).erase h ↔ h ∈ G i := by simp [graphActions]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_HeavyActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I : Type*} [DecidableEq I] [Fintype I]

 theorem ordinary_heavyActions (Full : Actions I I) (H : Finset I) (e : HeavyAction Full H) :
    e ∈ (heavyActions Full H).ordinary ↔ e.isLeft := by simp [heavyActions]

omit [Fintype I] in
 theorem heavyParent_membership (Full : Actions I I) (H : Finset I) (e : HeavyAction Full H) :
    heavyParent Full H e ∈ H ↔ ¬ e.isLeft := by
  cases e with
  | inl h => simp [heavyParent, h.property]
  | inr p => simp [heavyParent, p.property.1]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_ActualActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential FiniteGraph
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

 theorem nonordinary_parent_heavy (G : I → Finset I) (H : Finset I)
    (e : HeavyAction (graphActions G) H) (he : e ∉ (heavyActions (graphActions G) H).ordinary) :
    (heavyActions (graphActions G) H).source e ∈ H := by
  apply (heavyParent_membership _ _ e).mpr
  simpa only [ordinary_heavyActions] using he

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

theorem mass_from_near_unit {g P D : ℝ} (d : I → ℝ) (S : Finset I)
    (hg : 0 ≤ g) (hP : 0 < P) (hP1 : P < 1) (hD : 0 < D)
    (hunit : (S.card : ℝ)*g=1) (hnear : ∀ i ∈ S, d i ≤ D) :
    1 ≤ mass g P d ((1-P)/D) := by
  have hq : ∀ i ∈ S, marginal P (d i) ((1-P)/D)=1 := by
    intro i hi
    apply marginal_one hP
    have hh := mul_le_mul_of_nonneg_left (hnear i hi)
      (div_nonneg (sub_nonneg.mpr hP1.le) hD.le)
    rw [div_mul_cancel₀ _ (ne_of_gt hD)] at hh
    exact hh
  have hs : (∑ i ∈ S, g*marginal P (d i) ((1-P)/D))=1 := by
    calc
      _ = ∑ _i ∈ S, g := Finset.sum_congr rfl (fun i hi => by rw [hq i hi, mul_one])
      _ = 1 := by rw [Finset.sum_const, nsmul_eq_mul, hunit]
  calc
    1 = ∑ i ∈ S, g*marginal P (d i) ((1-P)/D) := hs.symm
    _ ≤ mass g P d ((1-P)/D) :=
      Finset.sum_le_univ_sum_of_nonneg (fun i => mul_nonneg hg (marginal_nonneg hP))

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BackupGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I]

theorem minimal_near_unit {g P D N : ℝ} (d : I → ℝ) (S : Finset I)
    (hg : 0 ≤ g) (hP : 0 < P) (hP1 : P < 1) (hD : 0 ≤ D)
    (hunit : (S.card:ℝ)*g=1) (hnear : ∀ i ∈ S, d i ≤ D)
    (hminimal : ∀ R : ℝ, 0 < R → 1 ≤ mass g P d (1/R) → N ≤ R) :
    N ≤ D/(1-P) := by
  have hden : 0 < 1-P := sub_pos.mpr hP1
  by_cases hd : 0 < D
  · apply hminimal _ (div_pos hd hden)
    rw [one_div_div]
    exact mass_from_near_unit d S hg hP hP1 hd hunit hnear
  · have he : D=0 := le_antisymm (le_of_not_gt hd) hD
    rw [he, zero_div]
    by_contra hn
    have hN : 0 < N := lt_of_not_ge hn
    let D' := (N/2)*(1-P)
    have hd' : 0 < D' := mul_pos (by linarith only [hN]) hden
    have hn' : ∀ i ∈ S, d i ≤ D' := by
      intro i hi
      exact (he ▸ hnear i hi).trans hd'.le
    have hh := hminimal (D'/(1-P)) (div_pos hd' hden)
      (by rw [one_div_div]; exact mass_from_near_unit d S hg hP hP1 hd' hunit hn')
    dsimp only [D'] at hh
    rw [mul_div_cancel_right₀ _ (ne_of_gt hden)] at hh
    linarith only [hh,hN]

variable {X : Type*} [PseudoMetricSpace X]

theorem backup_source_close {g P R : ℝ} (location : I → X) (client : X)
    (S : Finset I) (N : I → ℝ) (q : I → I → ℝ)
    (hg : 0 ≤ g) (hP : 0 < P) (hP1 : P ≤ 1/2) (hR : 0 ≤ R)
    (hunit : (S.card:ℝ)*g=1) (hnear : ∀ i ∈ S, dist client (location i) ≤ R)
    (hN : ∀ i, 0 ≤ N i) (hq : ∀ h i, 0 ≤ q h i)
    (hminimal : ∀ i ∈ S, ∀ r : ℝ, 0 < r →
      1 ≤ mass g P (fun t => dist (location i) (location t)) (1/r) → N i ≤ r)
    (htaper : ∀ h i, 0 < q h i → dist (location i) (location h) ≤ N i*(1-P*q h i))
    {i h : I} (hi : i ∈ S) (hedge : 0 < q h i) :
    dist client (location h) ≤ 5*R := by
  have hpair : ∀ t ∈ S, dist (location i) (location t) ≤ 2*R := by
    intro t ht
    have hh := dist_triangle (location i) client (location t)
    rw [dist_comm (location i) client] at hh
    linarith only [hh,hnear i hi,hnear t ht]
  have hp : P < 1 := by linarith only [hP1]
  have hn := minimal_near_unit (fun t => dist (location i) (location t)) S hg hP hp
    (show 0 ≤ 2*R by positivity) hunit hpair (hminimal i hi)
  have hb : (2*R)/(1-P) ≤ 4*R := by
    apply (div_le_iff₀ (sub_pos.mpr hp)).mpr
    have hh := mul_le_mul_of_nonneg_left hP1 hR
    nlinarith only [hh]
  have he : dist (location i) (location h) ≤ N i := by
    apply (htaper h i hedge).trans
    have hh : 0 ≤ P*q h i := mul_nonneg hP.le (hq h i)
    nlinarith only [hN i,hh]
  have hh := dist_triangle client (location i) (location h)
  linarith only [hh,hnear i hi,he,hn,hb]

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type*} [DecidableEq F]
variable (Δ : ℕ)

variable [Fintype F]

 theorem reset_integral (A erased : Finset (Copy (F := F) Δ)) (O : Finset F) :
    O ⊆ integral Δ (next Δ A erased O) := by
  intro f hf
  apply (mem_integral _ _ _).mpr
  intro i hi
  exact mem_union_right _ ((mem_resets _ _ _).mpr ((mem_slots _ _ _).mp hi ▸ hf))

theorem integral_persists (A erased : Finset (Copy (F := F) Δ)) (O : Finset F)
    (hattribute : ∀ i ∈ A, i ∈ erased → i.1 ∈ integral Δ A → i.1 ∈ O) :
    integral Δ A ⊆ integral Δ (next Δ A erased O) := by
  intro f hf
  apply (mem_integral _ _ _).mpr
  intro i hi
  have hiA := (mem_integral _ _ _).mp hf hi
  have hif := (mem_slots _ _ _).mp hi
  by_cases hie : i ∈ erased
  · apply mem_union_right
    apply (mem_resets _ _ _).mpr
    exact hattribute i hiA hie (hif ▸ hf)
  · exact mem_union_left _ (mem_sdiff.mpr ⟨hiA,hie⟩)

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] (Δ : ℕ)

 theorem own_card_integral (A : Finset (Copy (F := F) Δ)) (i : A)
    (hi : i.val.1 ∈ integral Δ A) : (own Δ A i).card=Δ := by
  have he : (own Δ A i).image Subtype.val=slots Δ i.val.1 := by
    ext h
    constructor
    · intro hh
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hh
      exact (mem_slots _ _ _).mpr ((mem_own _ _ _ _).mp ht)
    · intro hh
      have hA := (mem_integral _ _ _).mp hi hh
      exact mem_image.mpr ⟨⟨h,hA⟩,(mem_own _ _ _ _).mpr ((mem_slots _ _ _).mp hh),rfl⟩
  have hc := congrArg Finset.card he
  simpa only [card_image_of_injective _ Subtype.val_injective,card_slots] using hc

 theorem integral_incoming_same_group (A : Finset (Copy (F := F) Δ))
    (G : A → Finset A) (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i)
    {i h : A} (hi : i.val.1 ∈ integral Δ A) (hh : h ∈ G i) : h.val.1=i.val.1 := by
  have he : own Δ A i=G i := eq_of_subset_of_card_le (hown i)
    (by rw [hG i,own_card_integral Δ A i hi])
  exact (mem_own _ _ _ _).mp (he.symm ▸ hh)

variable {Δ}

 theorem heavy_erase_parent {I : Type*} [Fintype I] [DecidableEq I]
    (Full : Actions I I) (H : Finset I) (e : HeavyAction Full H) :
    (heavyActions Full H).erase e ⊆ Full.erase (heavyParent Full H e) := by
  intro i hi
  cases e with
  | inl h => exact hi
  | inr p => exact (mem_singleton.mp hi).symm ▸ p.property.2

 theorem parent_selected {I : Type*} [Fintype I] [DecidableEq I]
    (G : I → Finset I) (H : Finset I) (Z : Finset (HeavyAction (graphActions G) H))
    {e : HeavyAction (graphActions G) H} (he : e ∈ Z) :
    heavyParent (graphActions G) H e ∈ selectedSources G H Z := by
  by_cases ho : e ∈ (heavyActions (graphActions G) H).ordinary
  · exact mem_union_right _ (mem_image.mpr ⟨e,mem_inter.mpr ⟨he,ho⟩,rfl⟩)
  · exact mem_union_left _ (nonordinary_parent_heavy G H e ho)

 theorem round_integral_persists (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H))
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i) :
    integral Δ A ⊆ integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z)) := by
  apply integral_persists
  intro i _ hie hii
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hie
  obtain ⟨e,he,hje⟩ := mem_biUnion.mp hj
  have hp := heavy_erase_parent (graphActions G) H e hje
  have hg := (mem_graph_erase G _ _).mp hp
  have hsame := integral_incoming_same_group Δ A G hG hown hii hg
  exact mem_image.mpr ⟨_,parent_selected G H Z he,hsame⟩

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

 theorem localSet_image (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) :
    (localSet A S).image Subtype.val=S := by
  ext i
  constructor
  · rintro hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact (mem_localSet _ _ _).mp hj
  · intro hi
    exact mem_image.mpr ⟨⟨i,hS hi⟩,(mem_localSet _ _ _).mpr hi,rfl⟩

 theorem image_mass (A : Finset (Copy (F := F) Δ)) (S : Finset A) (g : ℝ) :
    mass g (S.image Subtype.val)=mass g S := by
  simp only [mass,card_image_of_injective _ Subtype.val_injective]

 theorem localSet_mass (A S : Finset (Copy (F := F) Δ)) (hS : S ⊆ A) (g : ℝ) :
    mass g (localSet A S)=mass g S := by
  rw [← image_mass,localSet_image A S hS]

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BackupInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F X : Type*} [Fintype F] [DecidableEq F] [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype F] in

theorem round_erasure_backup (A S₀ : Finset (Copy (F := F) Δ))
    (location : F → X) (client : X) {g P R : ℝ}
    (D : Taper.GraphData Δ g P (fun i : A => location i.val.1) (own Δ A))
    (G : A → Finset A) (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H))
    (hg : 0 ≤ g) (hP : 0 < P) (hP1 : P ≤ 1/2) (hR : 0 ≤ R)
    (hS : S₀ ⊆ A) (hm : mass g S₀=1)
    (hd : ∀ i ∈ S₀, dist client (location i.1) ≤ R) (hgood : D.Good G)
    (herased : (S₀ ∩ roundErased A G H Z).Nonempty) :
    ∃ f ∈ roundOpened A G H Z, dist client (location f) ≤ 5*R := by
  obtain ⟨i,hi⟩ := herased
  obtain ⟨t,ht,hti⟩ := mem_image.mp (mem_inter.mp hi).2
  obtain ⟨e,he,hte⟩ := mem_biUnion.mp ht
  let a := heavyParent (graphActions G) H e
  have ha : a ∈ G t := (mem_graph_erase G _ _).mp (heavy_erase_parent (graphActions G) H e hte)
  have hiS : t ∈ localSet A S₀ := (mem_localSet A S₀ t).mpr (hti ▸ (mem_inter.mp hi).1)
  have hm' : ((localSet A S₀).card:ℝ)*g=1 := by
    rw [mul_comm,← mass,localSet_mass A S₀ hS,hm]
  have hn := Taper.backup_source_close (fun i : A => location i.val.1) client
    (localSet A S₀) D.radius D.marginal hg hP hP1 hR hm'
    (fun i hi => hd i.val ((mem_localSet A S₀ i).mp hi)) D.radius_nonneg D.marginal_nonneg
    (fun i _ => D.minimal i) D.upper hiS (hgood.2.2 a t ha)
  exact ⟨a.val.1,mem_image.mpr ⟨a,parent_selected G H Z he,rfl⟩,hn⟩

theorem round_backup_s35_oai (A S₀ : Finset (Copy (F := F) Δ))
    (location : F → X) (client : X) {g P R : ℝ}
    (D : Taper.GraphData Δ g P (fun i : A => location i.val.1) (own Δ A))
    (G : A → Finset A) (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H))
    (hg : 0 ≤ g) (hP : 0 < P) (hP1 : P ≤ 1/2) (hR : 0 ≤ R)
    (hm : mass g S₀=1) (hd : ∀ i ∈ S₀, dist client (location i.1) ≤ R)
    (hgood : D.Good G)
    (hbackup : (¬∃ f ∈ integral Δ A, dist client (location f) ≤ 5*R) → S₀ ⊆ A) :
    (¬∃ f ∈ integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z)),
      dist client (location f) ≤ 5*R) →
      S₀ ⊆ next Δ A (roundErased A G H Z) (roundOpened A G H Z) := by
  intro hn
  have hnone : ¬∃ f ∈ integral Δ A, dist client (location f) ≤ 5*R := by
    rintro ⟨f,hf,hd⟩
    exact hn ⟨f,round_integral_persists A G H Z hgood.1 hgood.2.1 hf,hd⟩
  have hS := hbackup hnone
  intro i hi
  by_cases he : i ∈ roundErased A G H Z
  · obtain ⟨f,hf,hfd⟩ := round_erasure_backup A S₀ location client D G H Z hg hP hP1 hR
      hS hm hd hgood ⟨i,mem_inter.mpr ⟨hi,he⟩⟩
    exact False.elim (hn ⟨f,reset_integral Δ A _ _ hf,hfd⟩)
  · exact mem_union_left _ (mem_sdiff.mpr ⟨hS hi,he⟩)

end MetricKMedian.CopyState
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedian.CopyState.round_backup_s35_oai.{u_1, u_2} := @OAI.MetricKMedian.CopyState.round_backup_s35_oai.{u_1, u_2}
