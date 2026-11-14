-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_2_7_changed_balls
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:22:16.037198+00:00
-- url     : https://prove2.me/submissions/09302952-863f-4d8d-9c0c-9891af0ea817

import Theorems.Thm_KSATSingleFlip_Connect_lemma_2_7_ball_bounds
import Theorems.Thm_KSATSingleFlip_Connect_lemma_2_7_changed_ball_endpoint

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- If each changed root lies in an old or new family around one endpoint,
and each such family has at most M roots, there are at most 2kM changed roots. -/
theorem audit_changed_union_bound {V : Type} [DecidableEq V]
    (S changed : Finset V) (old new : V → Finset V) (k M : ℕ)
    (hS : S.card ≤ k)
    (hold : ∀ u ∈ S, (old u).card ≤ M)
    (hnew : ∀ u ∈ S, (new u).card ≤ M)
    (hcover : ∀ v ∈ changed, ∃ u ∈ S, v ∈ old u ∨ v ∈ new u) :
    changed.card ≤ 2 * k * M := by
  let U := S.biUnion fun u => old u ∪ new u
  have hsub : changed ⊆ U := by
    intro v hv
    obtain ⟨u, hu, hmem⟩ := hcover v hv
    exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_union.mpr hmem⟩
  calc
    changed.card ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ u ∈ S, (old u ∪ new u).card := Finset.card_biUnion_le
    _ ≤ S.card * (2 * M) := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul S (fun u => (old u ∪ new u).card) (2*M)
        (by intro u hu; have hc := Finset.card_union_le (old u) (new u); have ho := hold u hu; have hn := hnew u hu; omega)
    _ ≤ 2 * k * M := by nlinarith

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

theorem solution {n : ℕ} (Φ : GFormula (Fin n)) (C : GClause (Fin n)) (k r D : ℕ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hD : 1 ≤ D)
    (hwidth : ∀ c : Fin Φ.length, (vbl (Φ.get c)).card ≤ k) (hC : (vbl C).card ≤ k) :
    (Finset.univ.filter fun v : Fin n =>
      trimmedBall Φ v r D ≠ trimmedBall (Φ ++ [C]) v r D).card ≤
        2 * k * ∑ h ∈ Finset.range (r + 2), (k * D)^h := by
  classical
  have hnewwidth : ∀ c : Fin (Φ ++ [C]).length, (vbl ((Φ ++ [C]).get c)).card ≤ k := by
    intro c
    have hm := List.get_mem (Φ ++ [C]) c
    rcases List.mem_append.mp hm with hold | hlast
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hold
      rw [← hj]
      exact hwidth j
    · have he : (Φ ++ [C]).get c = C := by simpa using hlast
      rw [he]
      exact hC
  let old : Fin n → Finset (Fin n) := fun u => Finset.univ.filter fun v =>
    LocallyTree Φ v r D ∧ u ∈ ballVars Φ v r
  let new : Fin n → Finset (Fin n) := fun u => Finset.univ.filter fun v =>
    LocallyTree (Φ ++ [C]) v r D ∧ u ∈ ballVars (Φ ++ [C]) v r
  let changed : Finset (Fin n) := Finset.univ.filter fun v =>
    trimmedBall Φ v r D ≠ trimmedBall (Φ ++ [C]) v r D
  let M := ∑ h ∈ Finset.range (r + 2), (k * D)^h
  have hold : ∀ u ∈ vbl C, (old u).card ≤ M := by
    intro u hu
    exact (lemma_2_7_ball_bounds Φ k r D hk hr hD hwidth).2 u
  have hnew : ∀ u ∈ vbl C, (new u).card ≤ M := by
    intro u hu
    exact (lemma_2_7_ball_bounds (Φ ++ [C]) k r D hk hr hD hnewwidth).2 u
  have hcover : ∀ v ∈ changed, ∃ u ∈ vbl C, v ∈ old u ∨ v ∈ new u := by
    intro v hv
    have hv' : trimmedBall Φ v r D ≠ trimmedBall (Φ ++ [C]) v r D := by
      simpa [changed] using hv
    obtain ⟨u, hu, hmem⟩ := lemma_2_7_changed_ball_endpoint Φ C r D v hv'
    refine ⟨u, hu, ?_⟩
    simpa [old, new] using hmem
  exact audit_changed_union_bound (vbl C) changed old new k M hC hold hnew hcover

#print axioms solution
