-- Prove2me | solution 1 for NadlerCLS.theorem_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:01:38.825983+00:00
-- url     : https://prove2.me/submissions/7ee98271-3c07-491b-8a68-8a2a8c84a27a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NadlerCLS_pnSearch
import Definitions.Def_NadlerCLS_pnPromiseSearch
import Theorems.Thm_NadlerCLS_theorem_C_4
import Theorems.Thm_NadlerCLS_lemma_C_6
import Theorems.Thm_NadlerCLS_lemma_C_8
import Theorems.Thm_NadlerCLS_co_equiv_clsSearch
import Theorems.Thm_NadlerCLS_pnSearch_check_P
import Theorems.Thm_ConstrSOSP_searchReduces_trans
import Theorems.Thm_CookPvsNP_tm_output_length_le
import Theorems.Thm_CookPvsNP_polynomial_absorb

set_option autoImplicit false

open NetworkEquilibriumCLS.LinearNash

namespace NadlerCLS.T32

/-- Output length of a polynomial-time computable map is polynomially bounded. -/
theorem polyTime_length {A B : Type} (g : List A → List B) (hg : CookPvsNP.PolyTimeComputable g) :
    ∃ c : ℕ, ∀ x, (g x).length ≤ (c + 2) * (x.length + 1) ^ (c + 1) := by
  obtain ⟨Γ, _, ι₁, ι₂, M, k, h⟩ := hg
  refine ⟨k, fun x => ?_⟩
  have h1 := (h x).2
  have h2 := CookPvsNP.tm_output_length_le M (x.length ^ k + k) (x.map ι₁)
  rw [h1] at h2
  simp only [List.length_map] at h2
  have e1 : x.length ^ k ≤ (x.length + 1) ^ (k + 1) :=
    le_trans (Nat.pow_le_pow_left (Nat.le_succ _) k)
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ k))
  have e2 : 1 ≤ (x.length + 1) ^ (k + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have e3 : x.length + 1 ≤ (x.length + 1) ^ (k + 1) :=
    le_self_pow₀ (Nat.le_add_left 1 _) (Nat.succ_ne_zero k)
  nlinarith

/-- `(y + 1)^d` under a polynomial bound on `y`. -/
theorem pow_succ_bound (y C e m d : ℕ) (hy : y ≤ C * (m + 1) ^ e) :
    (y + 1) ^ d ≤ (C + 1) ^ d * (m + 1) ^ (e * d) := by
  have h1 : 1 ≤ (m + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have : y + 1 ≤ (C + 1) * (m + 1) ^ e := by nlinarith
  calc (y + 1) ^ d ≤ ((C + 1) * (m + 1) ^ e) ^ d := Nat.pow_le_pow_left this d
    _ = (C + 1) ^ d * (m + 1) ^ (e * d) := by rw [mul_pow, ← pow_mul]

/-- Replacing the target by a problem with the same valid instances (on the image) and fewer
answers preserves a reduction. -/
theorem reduces_mono (Q R R' : SearchProblem)
    (hv : ∀ s, R.valid s → R'.valid s) (ha : ∀ s t, R'.answer s t → R.answer s t)
    (h : SearchReduces Q R) : SearchReduces Q R' := by
  obtain ⟨f, g, hf, hg, H⟩ := h
  exact ⟨f, g, hf, hg, fun s hs => ⟨hv _ (H s hs).1, fun t ht => (H s hs).2 t (ha _ _ ht)⟩⟩

end NadlerCLS.T32

open NadlerCLS NadlerCLS.T32 in
theorem solution (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (∃ k : ℕ, CLSComplete (bounded (pnSearch 3 β) k)) ∧ CLSHard (pnPromiseSearch 3 β) := by
  obtain ⟨⟨k', hHcomp⟩, -⟩ := theorem_C_4 β hβ0 hβ1
  obtain ⟨⟨hHtot, -, -⟩, hHcls⟩ := hHcomp.1
  have h6 := lemma_C_6 3 (by norm_num) β hβ0 hβ1
  have h8 := lemma_C_8 3 (by norm_num) β hβ0 hβ1
  have hco := co_equiv_clsSearch.2
  -- CLS-hardness of the promise problem
  have hard : CLSHard (pnPromiseSearch 3 β) := fun R hR =>
    ConstrSOSP.searchReduces_trans _ _ _ hR.2
      (ConstrSOSP.searchReduces_trans _ _ _ hco h8)
  refine ⟨?_, hard⟩
  -- the reduction of Lemma C.6 and polynomial bounds on its maps
  obtain ⟨F, G, hF, hG, H⟩ := h6
  obtain ⟨a, ha⟩ := polyTime_length F hF
  obtain ⟨c, hc⟩ := polyTime_length G hG
  -- a uniform polynomial bound on decoded answers
  set C2 := (a + 2 + 1) ^ k' + k' with hC2
  set e2 := (a + 1) * k' with he2
  set C3 := C2 + 1 with hC3
  set e3 := e2 + 1 with he3
  obtain ⟨K, hK⟩ := CookPvsNP.polynomial_absorb ((c + 2) * (C3 + 1) ^ (c + 1)) (e3 * (c + 1)) 0
  have bound : ∀ s t : List Bool, t.length ≤ ((F s).length + 1) ^ k' + k' →
      (G (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr))).length ≤
        (s.length + 1) ^ K + K := by
    intro s t ht
    set m := s.length
    have hFs : (F s).length ≤ (a + 2) * (m + 1) ^ (a + 1) := ha s
    have h1 : 1 ≤ (m + 1) ^ e2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have ht2 : t.length ≤ C2 * (m + 1) ^ e2 := by
      have := pow_succ_bound _ _ _ m k' hFs
      rw [hC2, he2]
      nlinarith
    have hw : (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr)).length ≤
        C3 * (m + 1) ^ e3 := by
      simp only [List.length_append, List.length_map, List.length_cons]
      have : (m + 1) ^ e2 ≤ (m + 1) ^ e3 := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
      have : m + 1 ≤ (m + 1) ^ e3 := le_self_pow₀ (Nat.le_add_left 1 _) (by omega)
      rw [hC3]
      nlinarith
    have hg := hc (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr))
    have hp := pow_succ_bound _ _ _ m (c + 1) hw
    have hK' := hK m
    have : m ^ K ≤ (m + 1) ^ K := Nat.pow_le_pow_left (Nat.le_succ _) K
    calc _ ≤ (c + 2) * ((C3 + 1) ^ (c + 1) * (m + 1) ^ (e3 * (c + 1))) :=
          le_trans hg (Nat.mul_le_mul_left _ hp)
      _ = (c + 2) * (C3 + 1) ^ (c + 1) * (m + 1) ^ (e3 * (c + 1)) + 0 := by ring
      _ ≤ m ^ K + K := hK'
      _ ≤ (m + 1) ^ K + K := by omega
  -- reduction of the bounded Projected-Nadler problem to bounded Hölder-LocalOpt
  have red : SearchReduces (bounded (pnSearch 3 β) K) (bounded (holderSearch 3 β) k') := by
    refine ⟨F, G, hF, hG, fun s hs => ⟨(H s hs).1, fun t ht => ⟨(H s hs).2 t ht.1, ?_⟩⟩⟩
    exact bound s t ht.2
  refine ⟨K, ⟨⟨?_, ?_, pnSearch_check_P 3 β hβ0 hβ1 K⟩, ?_⟩, ?_⟩
  · -- totality, with short answers
    intro s hs
    obtain ⟨t, ht⟩ := hHtot (F s) (H s hs).1
    exact ⟨_, (H s hs).2 t ht.1, bound s t ht.2⟩
  · exact ⟨K, fun x y _ hy => hy.2⟩
  · exact ConstrSOSP.searchReduces_trans _ _ _ red hHcls
  · -- CLS-hardness of the bounded problem
    intro R hR
    refine reduces_mono R (pnPromiseSearch 3 β) _ ?_ ?_ (hard R hR)
    · rintro s ⟨I, hI, -, rfl⟩
      exact ⟨I, hI, rfl⟩
    · intro s t ht
      exact ht.1
