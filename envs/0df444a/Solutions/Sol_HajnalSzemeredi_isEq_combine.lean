-- Prove2me | solution 1 for HajnalSzemeredi.isEq_combine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:52.348239+00:00
-- url     : https://prove2.me/submissions/71144f5f-386c-41be-9283-c24cd07a660b

module
public import Definitions.Def_HajnalSzemeredi_Shift
public import Definitions.Def_HajnalSzemeredi_Structure
public import Definitions.Def_HajnalSzemeredi_Cases
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
attribute [local simp] HajnalSzemeredi.mem_cls
attribute [local simp] HajnalSzemeredi.mem_nbr


section
@[expose] public section
noncomputable section
open Classical Finset Relation
namespace HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
private lemma proper_comb {S SA SB : Finset V} {PA PB : Finset ℕ} {cA cB : V → ℕ}
    (hA : Proper G SA cA) (hB : Proper G SB cB) (hiA : Into SA cA PA) (hiB : Into SB cB PB)
    (hS : SA ∪ SB = S) (hPdisj : Disjoint PA PB) :
    Proper G S (fun v => if v ∈ SA then cA v else cB v) := by
  intro v hv w hw hvw
  have hv' : v ∈ SA ∪ SB := hS ▸ hv
  have hw' : w ∈ SA ∪ SB := hS ▸ hw
  by_cases hvA : v ∈ SA <;> by_cases hwA : w ∈ SA <;> simp only [hvA, hwA, ite_true, ite_false]
  · exact hA v hvA w hwA hvw
  · have hwB : w ∈ SB := (mem_union.mp hw').resolve_left hwA
    intro heq
    exact disjoint_left.mp hPdisj (hiA v hvA) (heq ▸ hiB w hwB)
  · have hvB : v ∈ SB := (mem_union.mp hv').resolve_left hvA
    intro heq
    exact disjoint_left.mp hPdisj (hiA w hwA) (heq ▸ hiB v hvB)
  · exact hB v ((mem_union.mp hv').resolve_left hvA) w ((mem_union.mp hw').resolve_left hwA) hvw
private lemma into_comb {S SA SB : Finset V} {P PA PB : Finset ℕ} {cA cB : V → ℕ}
    (hiA : Into SA cA PA) (hiB : Into SB cB PB) (hS : SA ∪ SB = S) (hP : PA ∪ PB = P) :
    Into S (fun v => if v ∈ SA then cA v else cB v) P := by
  intro v hv
  have hv' : v ∈ SA ∪ SB := hS ▸ hv
  rw [← hP]
  by_cases hvA : v ∈ SA
  · simp only [hvA, ite_true]; exact mem_union_left _ (hiA v hvA)
  · simp only [hvA, ite_false]
    exact mem_union_right _ (hiB v ((mem_union.mp hv').resolve_left hvA))
private lemma cls_comb_A {S SA SB : Finset V} {PA PB : Finset ℕ} {cA cB : V → ℕ} {i : ℕ}
    (hiB : Into SB cB PB) (hS : SA ∪ SB = S) (hPdisj : Disjoint PA PB) (hi : i ∈ PA) :
    cls S (fun v => if v ∈ SA then cA v else cB v) i = cls SA cA i := by
  ext v
  simp only [mem_cls]
  constructor
  · rintro ⟨hv, hc⟩
    by_cases hvA : v ∈ SA
    · simp only [hvA, ite_true] at hc; exact ⟨hvA, hc⟩
    · simp only [hvA, ite_false] at hc
      have hvB : v ∈ SB := (mem_union.mp (hS ▸ hv : v ∈ SA ∪ SB)).resolve_left hvA
      exact absurd (hc ▸ hiB v hvB) (disjoint_left.mp hPdisj hi)
  · rintro ⟨hv, hc⟩
    exact ⟨hS ▸ mem_union_left _ hv, by simp only [hv, ite_true]; exact hc⟩
private lemma cls_comb_B {S SA SB : Finset V} {PA PB : Finset ℕ} {cA cB : V → ℕ} {i : ℕ}
    (hiA : Into SA cA PA) (hS : SA ∪ SB = S) (hdisj : Disjoint SA SB)
    (hPdisj : Disjoint PA PB) (hi : i ∈ PB) :
    cls S (fun v => if v ∈ SA then cA v else cB v) i = cls SB cB i := by
  ext v
  simp only [mem_cls]
  constructor
  · rintro ⟨hv, hc⟩
    by_cases hvA : v ∈ SA
    · simp only [hvA, ite_true] at hc
      exact absurd hi (disjoint_left.mp hPdisj (hc ▸ hiA v hvA))
    · simp only [hvA, ite_false] at hc
      exact ⟨(mem_union.mp (hS ▸ hv : v ∈ SA ∪ SB)).resolve_left hvA, hc⟩
  · rintro ⟨hv, hc⟩
    have hvA : v ∉ SA := fun h => disjoint_left.mp hdisj h hv
    exact ⟨hS ▸ mem_union_right _ hv, by simp only [hvA, ite_false]; exact hc⟩
end HajnalSzemeredi
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
namespace HajnalSzemeredi
theorem _root_.solution {S SA SB : Finset V} {P PA PB : Finset ℕ} {cA cB : V → ℕ} {s : ℕ}
    (hA : IsEq G SA PA cA s) (hB : IsEq G SB PB cB s) (hS : SA ∪ SB = S)
    (hdisj : Disjoint SA SB) (hP : PA ∪ PB = P) (hPdisj : Disjoint PA PB) :
    IsEq G S P (fun v => if v ∈ SA then cA v else cB v) s := by
  refine ⟨proper_comb hA.proper hB.proper hA.into hB.into hS hPdisj,
    into_comb hA.into hB.into hS hP, fun i hi => ?_⟩
  rcases mem_union.mp (hP ▸ hi : i ∈ PA ∪ PB) with hi' | hi'
  · rw [cls_comb_A hB.into hS hPdisj hi']; exact hA.card i hi'
  · rw [cls_comb_B hA.into hS hdisj hPdisj hi']; exact hB.card i hi'
end HajnalSzemeredi
