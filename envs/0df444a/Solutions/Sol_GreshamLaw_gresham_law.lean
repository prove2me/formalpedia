-- Prove2me | solution 1 for GreshamLaw.gresham_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T19:20:40.043134+00:00
-- url     : https://prove2.me/submissions/21541a15-6c8c-4899-9a75-1fc2c1024ad5

import Mathlib
import Definitions.Def_GreshamLaw_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open GreshamLaw

theorem solution {ι : Type*} [DecidableEq ι] (coin : ι → Coin)
    (s good bad : Finset ι) (hpart : good ∪ bad = s)
    (hlegal : EqualLegalTender coin s)
    (hworse : ∀ g ∈ good, ∀ b ∈ bad, (coin b).melt < (coin g).melt)
    (d : ℝ) (P : Finset ι) (hP : IsOptimalPayment coin s P d) :
    (P ∩ good).Nonempty → bad ⊆ P := by
  classical
  rintro ⟨g, hg⟩
  by_contra hnot
  obtain ⟨b, hbBad, hbNotP⟩ := Finset.not_subset.mp hnot
  have hgP : g ∈ P := (Finset.mem_inter.mp hg).1
  have hgGood : g ∈ good := (Finset.mem_inter.mp hg).2
  have hbS : b ∈ s := by rw [← hpart]; exact Finset.mem_union_right good hbBad
  have hgS : g ∈ s := by rw [← hpart]; exact Finset.mem_union_left bad hgGood
  obtain ⟨⟨hPs, hPd⟩, hoptimal⟩ := hP
  let Q : Finset ι := insert b (P.erase g)
  have hbNotErased : b ∉ P.erase g := by simp [hbNotP]
  have hQs : Q ⊆ s := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hEr
    · exact hbS
    · exact hPs (Finset.mem_of_mem_erase hEr)
  have hswap (f : ι → ℝ) :
      (∑ i ∈ Q, f i) = (∑ i ∈ P, f i) + f b - f g := by
    have hsum : (∑ i ∈ P.erase g, f i) + f g = ∑ i ∈ P, f i := by
      exact Finset.sum_erase_add (s := P) (f := f) hgP
    calc
      (∑ i ∈ Q, f i) = f b + ∑ i ∈ P.erase g, f i := by
        simp [Q, hbNotErased]
      _ = (∑ i ∈ P, f i) + f b - f g := by linarith
  have hface : (coin b).face = (coin g).face :=
    hlegal b hbS g hgS
  have hQface : totalFace coin Q = totalFace coin P := by
    unfold totalFace
    rw [hswap]
    linarith
  have hQlegal : IsLegalPayment coin s Q d := ⟨hQs, hQface.trans hPd⟩
  have hpaid : totalMelt coin Q < totalMelt coin P := by
    have hstrict := hworse g hgGood b hbBad
    unfold totalMelt
    rw [hswap]
    linarith
  have hretain (R : Finset ι) (hR : R ⊆ s) :
      totalMelt coin (s \ R) + totalMelt coin R = totalMelt coin s := by
    unfold totalMelt
    have hsum := Finset.sum_sdiff hR (f := fun i => (coin i).melt)
    linarith
  have hretQ := hretain Q hQs
  have hretP := hretain P hPs
  have hlt : totalMelt coin (s \ P) < totalMelt coin (s \ Q) := by
    linarith
  exact (not_lt_of_ge (hoptimal Q hQlegal)) hlt
