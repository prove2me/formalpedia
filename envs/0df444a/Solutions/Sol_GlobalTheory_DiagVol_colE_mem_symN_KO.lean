-- Prove2me | solution 1 for GlobalTheory.DiagVol.colE_mem_symN_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:22:05.915069+00:00
-- url     : https://prove2.me/submissions/70beb6cb-7c24-4739-974b-7622d724ccd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagColumnUnipotentMemPeriodUnipotentIntegralGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
open GlobalTheory GlobalTheory.DiagVol
namespace GlobalTheory.DiagVol
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (t : n ⊕ Fin c) (y : n ⊕ Fin c → k) (hy : ∀ r, y r ∈ 𝒪[k])
    (hz : ∀ r, ¬ ordL c r < ordL c t → y r = 0) :
    ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c),
      x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0) := by
  set E : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of (fun r s => if s = t then y r else 0) with hE
  have hyt : y t = 0 := hz t (lt_irrefl _)
  have hEE : E * E = 0 := by
    ext r s
    simp only [hE, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    rw [Finset.sum_eq_single t]
    · simp [hyt]
    · intro u _ hu; simp [hu]
    · intro h; exact absurd (Finset.mem_univ t) h
  have h1 : (1 + E) * (1 - E) = 1 := by
    have : (1 + E) * (1 - E) = 1 - E * E := by noncomm_ring
    rw [this, hEE, sub_zero]
  have h2 : (1 - E) * (1 + E) = 1 := by
    have : (1 - E) * (1 + E) = 1 - E * E := by noncomm_ring
    rw [this, hEE, sub_zero]
  let x : GL (n ⊕ Fin c) k := ⟨1 + E, 1 - E, h1, h2⟩
  have hone : ∀ i j : n ⊕ Fin c, (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hEi : ∀ i j, E i j ∈ 𝒪[k] := by
    intro i j
    simp only [hE, Matrix.of_apply]
    split_ifs
    · exact hy i
    · exact zero_mem _
  have hInN : ∀ p : ℕ, (∀ r, y r ≠ 0 → lev p r < lev (n := n) (c := c) p t) → InN p x := by
    intro p hp r s hrs
    show (1 + E) r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s
    rw [Matrix.add_apply, add_eq_left]
    simp only [hE, Matrix.of_apply]
    split_ifs with h
    · subst h
      by_contra hne
      exact absurd hrs (not_le.2 (hp r hne))
    · rfl
  refine ⟨x, Subgroup.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
  · show x ∈ N k n c ((c + 1) / 2) ⊔ N k n c (c / 2 + 1)
    cases t with
    | inr j =>
      refine Subgroup.mem_sup_left (Model.mem_N_iff.2 (hInN _ fun r hr => ?_))
      have hlt : ordL c r < ordL c (Sum.inr j : n ⊕ Fin c) := by
        by_contra h; exact hr (hz r h)
      cases r with
      | inl a => simp [ordL, lev] at hlt ⊢; omega
      | inr i => simp [ordL, lev] at hlt ⊢; omega
    | inl a0 =>
      refine Subgroup.mem_sup_right (Model.mem_N_iff.2 (hInN _ fun r hr => ?_))
      have hlt : ordL c r < ordL c (Sum.inl a0 : n ⊕ Fin c) := by
        by_contra h; exact hr (hz r h)
      cases r with
      | inl a => simp [ordL, lev] at hlt ⊢
      | inr i => simp [ordL, lev] at hlt ⊢; omega
  · refine (mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      rw [Matrix.add_apply]; exact add_mem (hone i j) (hEi i j)
    · show (1 - E) i j ∈ 𝒪[k]
      rw [Matrix.sub_apply]; exact sub_mem (hone i j) (hEi i j)
end GlobalTheory.DiagVol
