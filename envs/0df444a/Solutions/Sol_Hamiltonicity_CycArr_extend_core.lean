-- Prove2me | solution 1 for Hamiltonicity.CycArr.extend_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:29:27.583308+00:00
-- url     : https://prove2.me/submissions/bb93bcc5-1520-4602-a9d2-20ffc6fae095

module
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Definitions.Def_MengerHamilton_LongerCycle
public import Theorems.Thm_Hamiltonicity_CycArr_of_fun
public import Theorems.Thm_Menger_Aux_Sep_symm


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
open Hamiltonicity.CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}
namespace Hamiltonicity.CycArr
theorem _root_.solution (hC : CycArr G m f) {d : ℕ} (hd1 : 1 ≤ d) (hdm : d < m)
    (Q : G.Walk (f 0) (f d)) (hQ : Q.IsPath) (hQl : 2 ≤ Q.length)
    (hint : ∀ y ∈ Q.support, ∀ i, f i = y → y = f 0 ∨ y = f d)
    (hadj : G.Adj (f 1) (f (d + 1))) :
    ∃ g, CycArr G (m + Q.length - 1) g := by
  set l := Q.length with hl
  have hm := hC.three_le
  set q := Q.getVert with hq
  have hq0 : q 0 = f 0 := Q.getVert_zero
  have hql : q l = f d := Q.getVert_length
  have hqinj : ∀ i j, i ≤ l → j ≤ l → q i = q j → i = j := fun i j hi hj h =>
    hQ.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) h
  have hqoff : ∀ i, 0 < i → i < l → ∀ j, f j ≠ q i := by
    intro i hi0 hil j hj
    rcases hint (q i) (Q.getVert_mem_support i) j hj with h | h
    · have := hqinj i 0 (by omega) (by omega) (h.trans hq0.symm)
      omega
    · have := hqinj i l (by omega) le_rfl (h.trans hql.symm)
      omega
  have hfinj : ∀ i j, i < m → j < m → f i = f j → i = j := hC.inj
  set h : ℕ → V := fun j =>
    if j ≤ l then q j else if j < l + d then f (d + l - j) else f (j - l + 1) with hh
  have hA : ∀ j, j ≤ l → h j = q j := fun j hj => by
    simp only [hh]
    rw [if_pos hj]
  have hB : ∀ j, l < j → j < l + d → h j = f (d + l - j) := fun j hj1 hj2 => by
    simp only [hh]
    rw [if_neg (by omega), if_pos hj2]
  have hC' : ∀ j, l + d ≤ j → h j = f (j - l + 1) := fun j hj => by
    simp only [hh]
    rw [if_neg (by omega), if_neg (by omega)]
  refine ⟨_, of_fun (h := h) (by omega) ?_ ?_ ?_⟩
  · -- injectivity
    have hcls : ∀ j, l < j → j < m + l - 1 → ∃ s, 0 < s ∧ s < m ∧ s ≠ d ∧ h j = f s ∧
        (j < l + d → s = d + l - j) ∧ (l + d ≤ j → s = j - l + 1) := by
      intro j hj1 hj2
      by_cases hjd : j < l + d
      · exact ⟨d + l - j, by omega, by omega, by omega, hB j hj1 hjd, fun _ => rfl,
          fun h' => by omega⟩
      · exact ⟨j - l + 1, by omega, by omega, by omega, hC' j (by omega), fun h' => by omega,
          fun _ => rfl⟩
    have hmix : ∀ a b, a ≤ l → l < b → b < m + l - 1 → h a ≠ h b := by
      intro a b ha hb1 hb2 hab
      obtain ⟨s, hs0, hsm, hsd, hs, -, -⟩ := hcls b hb1 hb2
      rw [hA a ha, hs] at hab
      by_cases ha0 : a = 0
      · subst ha0
        rw [hq0] at hab
        have := hfinj _ _ (by omega) hsm hab
        omega
      by_cases hal : a = l
      · subst hal
        rw [hql] at hab
        exact hsd (hfinj _ _ hsm (by omega) hab.symm)
      exact hqoff a (by omega) (by omega) s hab.symm
    intro a b ha hb hab
    by_cases ha' : a ≤ l <;> by_cases hb' : b ≤ l
    · rw [hA a ha', hA b hb'] at hab
      exact hqinj a b ha' hb' hab
    · exact absurd hab (hmix a b ha' (by omega) hb)
    · exact absurd hab.symm (hmix b a hb' (by omega) ha)
    · obtain ⟨s, hs0, hsm, hsd, hs, hs1, hs2⟩ := hcls a (by omega) ha
      obtain ⟨t, ht0, htm, htd, ht, ht1, ht2⟩ := hcls b (by omega) hb
      rw [hs, ht] at hab
      have hst := hfinj _ _ hsm htm hab
      by_cases h1 : a < l + d <;> by_cases h2 : b < l + d
      · have := hs1 h1
        have := ht1 h2
        omega
      · have := hs1 h1
        have := ht2 (by omega)
        omega
      · have := hs2 (by omega)
        have := ht1 h2
        omega
      · have := hs2 (by omega)
        have := ht2 (by omega)
        omega
  · -- adjacency
    intro j hj
    rcases lt_trichotomy j l with hjl | rfl | hjl
    · rw [hA j hjl.le, hA (j + 1) hjl]
      exact Q.adj_getVert_succ hjl
    · rw [hA _ le_rfl, hql]
      by_cases hd : d = 1
      · subst hd
        rw [hC' _ (by omega), show Q.length + 1 - Q.length + 1 = 1 + 1 by omega]
        exact hC.adj 1
      · rw [hB _ (by omega) (by omega), show d + Q.length - (Q.length + 1) = d - 1 by omega]
        have := hC.adj (d - 1)
        rw [show d - 1 + 1 = d by omega] at this
        exact this.symm
    · by_cases h1 : j + 1 < l + d
      · rw [hB j hjl (by omega), hB (j + 1) (by omega) h1]
        have := hC.adj (d + l - (j + 1))
        rw [show d + l - (j + 1) + 1 = d + l - j by omega] at this
        exact this.symm
      by_cases h2 : j + 1 = l + d
      · rw [hB j hjl (by omega), hC' (j + 1) (by omega), show d + l - j = 1 by omega,
          show j + 1 - l + 1 = d + 1 by omega]
        exact hadj
      · rw [hC' j (by omega), hC' (j + 1) (by omega), show j + 1 - l + 1 = j - l + 1 + 1 by omega]
        exact hC.adj _
  · -- closing up
    rw [hC' _ (by omega), hA 0 (Nat.zero_le _), hq0, show m + l - 1 - l + 1 = 0 + m by omega,
      hC.periodic]
end Hamiltonicity.CycArr
