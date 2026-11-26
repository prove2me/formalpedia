-- Prove2me | solution 1 for IntMul.Kappa.DeferredReadout.Plain.nesting
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T09:03:09.334241+00:00
-- url     : https://prove2.me/submissions/7b526a4a-43b5-43a1-8c3d-9ee0041a1b09

import Definitions.Def_IntMul_Kappa_DeferredReadoutPlain
import Theorems.Thm_IntMul_Kappa_DeferredReadout_deferredReadoutNesting
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Plain_certificateBatch1
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Plain_certificateBatch2
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Plain_certificateBatch3
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Plain_certificateBatch4
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Plain_certificateBatch5
import Theorems.Thm_IntMul_Kappa_DeferredReadout_Plain_certificateBatch6

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

private theorem size_identities : Plain.schedule.ids.size=2937 := by
  change Plain.identities.size=2937
  unfold Plain.identities
  simp only [Array.size_append]
  rfl

private theorem size_edges : Plain.schedule.edges.size=5781 := by
  change Plain.edges.size=5781
  unfold Plain.edges
  simp only [Array.size_append]
  rfl

private theorem size_timelines : Plain.schedule.targets.size=1771 := by
  change Plain.timelines.size=1771
  unfold Plain.timelines
  simp only [Array.size_append]
  rfl

theorem solution (t : Fin 1771) : (Plain.framesAt t).Pairwise (· ≤ ·) := by
  apply assemble Plain.schedule 2937 5781 1771 size_identities size_edges size_timelines (t := t)
  · exact sixRanges (p := fun i => validIdentity 23 Plain.schedule.entry (Plain.schedule.identity i) = true) 489 979 1468 1958 2447 2937
      IntMul.Kappa.DeferredReadout.Plain.certificateBatch1.1 IntMul.Kappa.DeferredReadout.Plain.certificateBatch2.1 IntMul.Kappa.DeferredReadout.Plain.certificateBatch3.1 IntMul.Kappa.DeferredReadout.Plain.certificateBatch4.1 IntMul.Kappa.DeferredReadout.Plain.certificateBatch5.1 IntMul.Kappa.DeferredReadout.Plain.certificateBatch6.1
  · exact sixRanges (p := fun i => Plain.schedule.edgeOK (Plain.schedule.edge i) = true) 963 1927 2890 3854 4817 5781
      IntMul.Kappa.DeferredReadout.Plain.certificateBatch1.2.1 IntMul.Kappa.DeferredReadout.Plain.certificateBatch2.2.1 IntMul.Kappa.DeferredReadout.Plain.certificateBatch3.2.1 IntMul.Kappa.DeferredReadout.Plain.certificateBatch4.2.1 IntMul.Kappa.DeferredReadout.Plain.certificateBatch5.2.1 IntMul.Kappa.DeferredReadout.Plain.certificateBatch6.2.1
  · exact sixRanges (p := fun i => Plain.schedule.timelineOK (Plain.schedule.targets[i]?.getD []) = true) 295 590 885 1180 1475 1771
      IntMul.Kappa.DeferredReadout.Plain.certificateBatch1.2.2 IntMul.Kappa.DeferredReadout.Plain.certificateBatch2.2.2 IntMul.Kappa.DeferredReadout.Plain.certificateBatch3.2.2 IntMul.Kappa.DeferredReadout.Plain.certificateBatch4.2.2 IntMul.Kappa.DeferredReadout.Plain.certificateBatch5.2.2 IntMul.Kappa.DeferredReadout.Plain.certificateBatch6.2.2
