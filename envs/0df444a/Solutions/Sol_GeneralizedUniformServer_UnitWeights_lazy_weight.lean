-- Prove2me | solution 1 for GeneralizedUniformServer.UnitWeights.lazy_weight
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T13:27:37.199182+00:00
-- url     : https://prove2.me/submissions/7c184fcd-f640-434b-810f-ce4f95a69ccb

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Weights

section
open scoped NNReal

noncomputable section

namespace GeneralizedUniformServer.Dev.LazyWeight

open GeneralizedUniformServer.UnitWeights

variable {k : ℕ} {M : Fin k → Type*}

theorem weights_take_succ (a : Config M) (ρ : List (Config M)) (t : ℕ) (h : t < ρ.length) :
    weights a (ρ.take (t+1)) = update ρ[t] (weights a (ρ.take t)) := by
  unfold weights
  rw [List.take_succ_eq_append_getElem h, List.foldl_append]
  rfl

theorem update_ge_serves (r : Config M) (ϕ : Config M →₀ ℝ≥0) (y : Config M) (hy : Serves y r) :
    ϕ y ≤ update r ϕ y := by
  classical
  unfold update
  rw [Finsupp.add_apply, Finsupp.filter_apply, if_pos hy]
  exact le_self_add

theorem update_ge_repair (r x : Config M) (ϕ : Config M →₀ ℝ≥0) (hx : ¬ Serves x r)
    (i : Fin k) :
    ϕ x / (2 * (k : ℝ≥0)) ≤ update r ϕ (repair x r i) := by
  classical
  by_cases hs : x ∈ ϕ.support
  · unfold update
    rw [Finsupp.add_apply]
    refine le_trans ?_ le_add_self
    rw [Finsupp.finsetSum_apply]
    have hx' : x ∈ ϕ.support.filter (fun x => ¬ Serves x r) := Finset.mem_filter.2 ⟨hs, hx⟩
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun x' => (∑ i' : Fin k,
        Finsupp.single (repair x' r i') (ϕ x' / (2 * (k : ℝ≥0)))) (repair x r i))
      (fun _ _ => zero_le) hx')
    simp only [Finsupp.finsetSum_apply]
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i' => (Finsupp.single (repair x r i') (ϕ x / (2 * (k : ℝ≥0))))
        (repair x r i)) (fun _ _ => zero_le) (Finset.mem_univ i))
    simp
  · rw [Finsupp.notMem_support_iff.1 hs]; simp

def ext (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M) (t : ℕ) : Config M :=
  if h : t < ρ.length + 1 then o ⟨t, h⟩ else o 0

open scoped Classical in
def mv (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M) (t : ℕ) : ℕ :=
  ∑ s ∈ Finset.range t, if ext ρ o (s+1) ≠ ext ρ o s then 1 else 0

theorem ext_castSucc (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M)
    (s : Fin ρ.length) : ext ρ o s.val = o s.castSucc := by
  unfold ext; rw [dif_pos (by omega)]; rfl

theorem ext_succ (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M)
    (s : Fin ρ.length) : ext ρ o (s.val + 1) = o s.succ := by
  unfold ext; rw [dif_pos (by omega)]; rfl

theorem numMoves_eq (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M) :
    numMoves ρ o = mv ρ o ρ.length := by
  classical
  unfold numMoves mv
  rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range
    (fun s => if ext ρ o (s+1) ≠ ext ρ o s then 1 else 0) ρ.length]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ext_castSucc, ext_succ]

theorem main (a : Config M) [NeZero k] (ρ : List (Config M))
    (o : Fin (ρ.length + 1) → Config M) (hlazy : IsLazy ρ o) (h₀ : o 0 = a) :
    ∀ t, t ≤ ρ.length →
      ((2 * (k : ℝ≥0)) ^ mv ρ o t)⁻¹ ≤ weights a (ρ.take t) (ext ρ o t) := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    have : ext ρ o 0 = a := by unfold ext; rw [dif_pos (by omega)]; exact h₀
    simp [mv, this, weights]
  | succ t ih =>
    intro hle
    have ht : t < ρ.length := hle
    have ih := ih ht.le
    rw [weights_take_succ a ρ t ht]
    have hmv : mv ρ o (t+1) = mv ρ o t + (if ext ρ o (t+1) ≠ ext ρ o t then 1 else 0) := by
      unfold mv; rw [Finset.sum_range_succ]
    have hl := hlazy ⟨t, ht⟩
    have e1 : ext ρ o t = o (⟨t, ht⟩ : Fin ρ.length).castSucc := ext_castSucc ρ o ⟨t, ht⟩
    have e2 : ext ρ o (t+1) = o (⟨t, ht⟩ : Fin ρ.length).succ := ext_succ ρ o ⟨t, ht⟩
    rw [← e1, ← e2] at hl
    by_cases hs : Serves (ext ρ o t) ρ[t]
    · have hz := hl.1 hs
      rw [hmv, hz]
      simp only [ne_eq, not_true_eq_false, if_false, add_zero]
      exact le_trans ih (update_ge_serves _ _ _ hs)
    · obtain ⟨i, hi⟩ := hl.2 hs
      have hne : ext ρ o (t+1) ≠ ext ρ o t := by
        intro h
        apply hs
        rw [← h, hi]
        exact ⟨i, by simp [repair]⟩
      rw [hmv, if_pos hne, hi, pow_succ, mul_inv, ← div_eq_mul_inv]
      refine le_trans ?_ (update_ge_repair _ _ _ hs i)
      gcongr

end GeneralizedUniformServer.Dev.LazyWeight

namespace GeneralizedUniformServer

open scoped NNReal
open GeneralizedUniformServer.UnitWeights

theorem chk_lazy_weight {k : ℕ} [NeZero k] {M : Fin k → Type*}
    (a : Config M) (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M)
    (hsol : IsOfflineSolution ρ o) (hlazy : IsLazy ρ o) (h₀ : o 0 = a) :
    weights a ρ (o (Fin.last ρ.length)) ≤ totalWeight a ρ ∧
      ((2 * (k : ℝ≥0)) ^ numMoves ρ o)⁻¹ ≤ weights a ρ (o (Fin.last ρ.length)) := by
  classical
  have hlast : Dev.LazyWeight.ext ρ o ρ.length = o (Fin.last ρ.length) := by
    unfold Dev.LazyWeight.ext; rw [dif_pos (by omega)]; rfl
  refine ⟨?_, ?_⟩
  · by_cases hm : o (Fin.last ρ.length) ∈ (weights a ρ).support
    · unfold totalWeight Finsupp.sum
      exact Finset.single_le_sum (f := fun x => weights a ρ x) (fun _ _ => zero_le) hm
    · rw [Finsupp.notMem_support_iff.1 hm]; exact zero_le
  · have := Dev.LazyWeight.main a ρ o hlazy h₀ ρ.length le_rfl
    rw [List.take_length, hlast] at this
    rw [Dev.LazyWeight.numMoves_eq]
    exact this

end GeneralizedUniformServer
end
end

theorem solution : type_of% @GeneralizedUniformServer.chk_lazy_weight := @GeneralizedUniformServer.chk_lazy_weight
