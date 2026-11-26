-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.Staircase.nesting
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T09:03:10.659715+00:00
-- url     : https://prove2.me/submissions/6152535a-f230-421f-a8ef-01c6e53950ca

import Definitions.Def_IntMul_Kappa_DeferredReadoutStaircase
import Theorems.Thm_IntMul_Kappa_DeferredReadout_deferredReadoutNesting
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_certificateBatch1
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_certificateBatch2
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_certificateBatch3
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_certificateBatch4
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_certificateBatch5
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Staircase_certificateBatch6

open IntMul.Kappa.DeferredReadout

private theorem sixRanges {p : Nat → Prop} (a b c d e n : Nat)
    (h₁ : ∀ i, 0 ≤ i → i < a → p i) (h₂ : ∀ i, a ≤ i → i < b → p i)
    (h₃ : ∀ i, b ≤ i → i < c → p i) (h₄ : ∀ i, c ≤ i → i < d → p i)
    (h₅ : ∀ i, d ≤ i → i < e → p i) (h₆ : ∀ i, e ≤ i → i < n → p i) :
    ∀ i, i < n → p i := by
  intro i hin
  by_cases ha : i<a
  · exact h₁ i (Nat.zero_le _) ha
  by_cases hb : i<b
  · exact h₂ i (Nat.le_of_not_gt ha) hb
  by_cases hc : i<c
  · exact h₃ i (Nat.le_of_not_gt hb) hc
  by_cases hd : i<d
  · exact h₄ i (Nat.le_of_not_gt hc) hd
  by_cases he : i<e
  · exact h₅ i (Nat.le_of_not_gt hd) he
  exact h₆ i (Nat.le_of_not_gt he) hin

private theorem collect {α : Type} [Inhabited α] (xs : Array α) (f : α → Bool)
    (h : ∀ i, i < xs.size → f (xs[i]?.getD default) = true) : xs.toList.all f = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨i, hi, eq⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hx)
  simpa [hi,eq] using h i hi

private theorem assemble (d : Block) (nr ne nt : Nat)
    (sr : d.ids.size = nr) (se : d.edges.size = ne) (st : d.targets.size = nt)
    (hr : ∀ i, i < nr → validIdentity 23 d.entry (d.identity i) = true)
    (he : ∀ i, i < ne → d.edgeOK (d.edge i) = true)
    (ht : ∀ i, i < nt → d.timelineOK (d.targets[i]?.getD []) = true) (t : Fin nt) :
    ((d.targets[t.val]?.getD []).map d.atEvent).Pairwise (· ≤ ·) := by
  have ir : d.identitiesOK = true :=
    collect d.ids (validIdentity 23 d.entry) (fun i hi => hr i (sr ▸ hi))
  have ie : d.edgesOK = true :=
    collect d.edges d.edgeOK (fun i hi => he i (se ▸ hi))
  have it : d.timelinesOK = true :=
    collect d.targets d.timelineOK (fun i hi => ht i (st ▸ hi))
  have hi : t.val < d.targets.size := st.symm ▸ t.isLt
  simpa only [Array.getElem?_eq_getElem hi, Option.getD_some] using
    deferredReadoutNesting d ir ie it ⟨t.val,hi⟩

private theorem size_identities : Staircase.schedule.ids.size=3606 := by
  change Staircase.identities.size=3606
  unfold Staircase.identities
  simp only [Array.size_append]
  rfl

private theorem size_edges : Staircase.schedule.edges.size=5552 := by
  change Staircase.edges.size=5552
  unfold Staircase.edges
  simp only [Array.size_append]
  rfl

private theorem size_timelines : Staircase.schedule.targets.size=1771 := by
  change Staircase.timelines.size=1771
  unfold Staircase.timelines
  simp only [Array.size_append]
  rfl

theorem solution (t : Fin 1771) : (Staircase.framesAt t).Pairwise (· ≤ ·) := by
  apply assemble Staircase.schedule 3606 5552 1771 size_identities size_edges size_timelines (t := t)
  · exact sixRanges (p := fun i => validIdentity 23 Staircase.schedule.entry (Staircase.schedule.identity i) = true) 601 1202 1803 2404 3005 3606
      IntMul.Kappa.DeferredReadout.Staircase.certificateBatch1.1 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch2.1 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch3.1 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch4.1 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch5.1 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch6.1
  · exact sixRanges (p := fun i => Staircase.schedule.edgeOK (Staircase.schedule.edge i) = true) 925 1850 2776 3701 4626 5552
      IntMul.Kappa.DeferredReadout.Staircase.certificateBatch1.2.1 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch2.2.1 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch3.2.1 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch4.2.1 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch5.2.1 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch6.2.1
  · exact sixRanges (p := fun i => Staircase.schedule.timelineOK (Staircase.schedule.targets[i]?.getD []) = true) 295 590 885 1180 1475 1771
      IntMul.Kappa.DeferredReadout.Staircase.certificateBatch1.2.2 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch2.2.2 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch3.2.2 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch4.2.2 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch5.2.2 IntMul.Kappa.DeferredReadout.Staircase.certificateBatch6.2.2
