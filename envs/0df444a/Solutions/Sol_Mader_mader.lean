-- Prove2me | solution 1 for Mader.mader
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:57:05.809996+00:00
-- url     : https://prove2.me/submissions/09b53260-c72d-4db9-a463-5983c594d95e

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderSteps
public import Definitions.Def_MaderLib_Mader
public import Theorems.Thm_Mader_dbl_induce
public import Theorems.Thm_Mader_dbl_le
public import Theorems.Thm_Mader_dbl_univ
public import Theorems.Thm_Mader_induce_connected
public import Theorems.Thm_Mader_ndeg_le
public import Theorems.Thm_Mader_stepA


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Mader
variable {V : Type*}
namespace Mader
theorem _root_.solution [Fintype V] [Nonempty V] (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hd : 4 * k * Fintype.card V ≤ 2 * G.edgeSet.ncard) :
    ∃ S : Finset V, IsKConnected (G.induce (S : Set V)) (k + 1) ∧
      (G.edgeSet.ncard : ℝ) / Fintype.card V - k <
        ((G.induce (S : Set V)).edgeSet.ncard : ℝ) / S.card := by
  classical
  set n := Fintype.card V with hn
  set m := dbl G Finset.univ with hmdef
  have hm2 : m = 2 * G.edgeSet.ncard := dbl_univ G
  have hm : 4 * k * n ≤ m := by rw [hm2]; exact hd
  have hnpos : 0 < n := Fintype.card_pos
  have hmpos : 0 < m := by
    have : 0 < 4 * k * n := by positivity
    omega
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun S : Finset V =>
      2 * k ≤ S.card ∧ (m : ℤ) * ((S.card : ℤ) - k) < (dbl G S : ℤ) * n))
    Finset.card ⟨Finset.univ, by
      have hD := dbl_le G (Finset.univ : Finset V)
      rw [Finset.card_univ, ← hmdef, ← hn] at hD
      have h1 : 4 * k * n ≤ (n - 1) * n := by rw [mul_comm (n - 1)]; exact hm.trans hD
      have h2 : 4 * k ≤ n - 1 := Nat.le_of_mul_le_mul_right h1 hnpos
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [Finset.card_univ, ← hn]; omega
      · rw [Finset.card_univ, ← hn, ← hmdef]
        have : (0 : ℤ) < m := by exact_mod_cast hmpos
        have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
        nlinarith⟩
  obtain ⟨-, h2k, hP⟩ := Finset.mem_filter.1 hS
  have hmin' : ∀ S' : Finset V, S'.card < S.card → 2 * k ≤ S'.card →
      (dbl G S' : ℤ) * n ≤ (m : ℤ) * ((S'.card : ℤ) - k) := by
    intro S' hlt h2k'
    by_contra hcon
    push Not at hcon
    have := hmin S' (Finset.mem_filter.2 ⟨Finset.mem_univ _, h2k', hcon⟩)
    omega
  have hdeg := stepA G hm hmin' h2k hP
  obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  have hbound : m < 2 * (S.card - 1) * n :=
    (hdeg v hv).trans_le (by have := ndeg_le G hv; gcongr)
  have hbig : 2 * k + 1 < S.card := by
    have h3 : 2 * k * (2 * n) < (S.card - 1) * (2 * n) := by
      calc 2 * k * (2 * n) = 4 * k * n := by ring
        _ ≤ m := hm
        _ < 2 * (S.card - 1) * n := hbound
        _ = (S.card - 1) * (2 * n) := by ring
    have := Nat.lt_of_mul_lt_mul_right h3
    omega
  refine ⟨S, ⟨?_, fun T hT => induce_connected G hm hmin' hP hdeg (by omega) T hT⟩, ?_⟩
  · simp only [Finset.coe_sort_coe, Fintype.card_coe]
    omega
  · have e1 : (2 : ℝ) * (G.induce (S : Set V)).edgeSet.ncard = dbl G S := by
      exact_mod_cast (dbl_induce G S).symm
    have e2 : (2 : ℝ) * G.edgeSet.ncard = m := by exact_mod_cast hm2.symm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hSR : (0 : ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
    have hPR : (m : ℝ) * ((S.card : ℝ) - k) < (dbl G S : ℝ) * n := by exact_mod_cast hP
    have hbR : (m : ℝ) ≤ 2 * S.card * n := by
      have : m ≤ 2 * S.card * n := hbound.le.trans (by gcongr; omega)
      exact_mod_cast this
    have hsub : (G.edgeSet.ncard : ℝ) / n - k = (G.edgeSet.ncard - k * n) / n := by
      field_simp
    rw [hsub, div_lt_div_iff₀ hnR hSR]
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hbR hk0]
end Mader
