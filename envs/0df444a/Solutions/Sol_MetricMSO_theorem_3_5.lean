-- Prove2me | solution 1 for MetricMSO.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:47:27.197433+00:00
-- url     : https://prove2.me/submissions/603cca7b-3706-44b9-84b0-7044274543e4

import Mathlib
import Definitions.Def_MetricMSO_cbl
import Definitions.Def_MetricMSO_Admissible
import Theorems.Thm_MetricMSO_lemma_3_1
import Theorems.Thm_MetricMSO_lemma_3_4

open MetricMSO

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (M : ℕ) (hM : 3 ≤ M)
    (hcbl : cbl G < M) {s t : V} (p : G.Walk s t) (hp : p.IsPath) :
    p.length = G.dist s t ↔
      ∃ c : V → ZMod M, Admissible G c ∧
        ∀ i, i < p.length → c (p.getVert (i + 1)) = c (p.getVert i) + 1 := by
  constructor
  · intro hlen
    obtain ⟨lam, hlip, hinc⟩ := (MetricMSO.lemma_3_1 G p hp).mp hlen
    refine ⟨fun v => (lam v : ZMod M), ?_, ?_⟩
    · intro u v hadj
      have h1 : |lam v - lam u| ≤ 1 := by
        rw [abs_sub_comm]
        exact hlip u v hadj
      rw [abs_le] at h1
      have hcases : lam v - lam u = -1 ∨ lam v - lam u = 0 ∨ lam v - lam u = 1 := by omega
      have hcast : (lam v : ZMod M) - (lam u : ZMod M) = ((lam v - lam u : ℤ) : ZMod M) := by
        push_cast; ring
      rcases hcases with h | h | h
      · left; rw [hcast, h]; simp
      · right; left; rw [hcast, h]; simp
      · right; right; rw [hcast, h]; simp
    · intro i hi
      have h := hinc i hi
      calc (lam (p.getVert (i + 1)) : ZMod M)
          = ((lam (p.getVert i) + 1 : ℤ) : ZMod M) := by rw [h]
        _ = (lam (p.getVert i) : ZMod M) + 1 := by push_cast; ring
  · rintro ⟨c, hc, hinc⟩
    obtain ⟨lam, _, hdiff⟩ := MetricMSO.lemma_3_4 G M hM hcbl c hc
    refine (MetricMSO.lemma_3_1 G p hp).mpr ⟨lam, ?_, ?_⟩
    · intro u v hadj
      obtain ⟨hmem, _⟩ := hdiff u v hadj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h
      · rw [abs_sub_comm, h]; norm_num
      · rw [abs_sub_comm, h]; norm_num
      · rw [abs_sub_comm, h]; norm_num
    · intro i hi
      have hadj : G.Adj (p.getVert i) (p.getVert (i + 1)) := p.adj_getVert_succ hi
      obtain ⟨hmem, hcong⟩ := hdiff (p.getVert i) (p.getVert (i + 1)) hadj
      have hc1 : c (p.getVert (i + 1)) - c (p.getVert i) = 1 := by
        rw [hinc i hi]; ring
      rw [hc1] at hcong
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h
      · exfalso
        rw [h] at hcong
        have h2 : ((2 : ℕ) : ZMod M) = 0 := by
          calc ((2 : ℕ) : ZMod M) = (1 : ZMod M) - ((-1 : ℤ) : ZMod M) := by norm_num
            _ = 0 := by rw [hcong, sub_self]
        rw [ZMod.natCast_eq_zero_iff] at h2
        have hle : M ≤ 2 := Nat.le_of_dvd (by decide) h2
        omega
      · exfalso
        rw [h] at hcong
        have h1 : ((1 : ℕ) : ZMod M) = 0 := by simpa using hcong.symm
        rw [ZMod.natCast_eq_zero_iff] at h1
        have hle : M ≤ 1 := Nat.le_of_dvd (by decide) h1
        omega
      · omega
