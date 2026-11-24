-- Prove2me | solution 1 for GlobalTheory.ClassicalTheta.forall_of_box_of_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:18.824799+00:00
-- url     : https://prove2.me/submissions/3069b011-663a-475e-afed-f80f66686621

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ClassicalTheta
namespace GlobalTheory.ClassicalTheta
theorem _root_.solution {g n : ℕ} (hn : 1 ≤ n) (P : (Fin g → ℤ) → Prop)
    (hP : ∀ m j, P (m + Pi.single j (n : ℤ)) ↔ P m)
    (hbox : ∀ r : Fin g → Fin n, P (fun i => ((r i : ℕ) : ℤ))) (m : Fin g → ℤ) : P m := by
  have h1 : ∀ (j : Fin g) (k : ℤ) (m : Fin g → ℤ), P (m + Pi.single j (k * n)) ↔ P m := by
    intro j k
    induction k using Int.induction_on with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      have : m + Pi.single j (((k : ℤ) + 1) * n) =
          (m + Pi.single j ((k : ℤ) * n)) + Pi.single j (n : ℤ) := by
        rw [add_assoc, ← Pi.single_add]; congr 2; ring
      rw [this, hP, ih]
    | pred k ih =>
      intro m
      have : m + Pi.single j ((-(k : ℤ)) * n) =
          (m + Pi.single j ((-(k : ℤ) - 1) * n)) + Pi.single j (n : ℤ) := by
        rw [add_assoc, ← Pi.single_add]; congr 2; ring
      rw [← ih m, this, hP]
  have h2 : ∀ (k : Fin g → ℤ) (s : Finset (Fin g)) (m : Fin g → ℤ),
      P (m + ∑ j ∈ s, Pi.single j (k j * n)) ↔ P m := by
    intro k s
    induction s using Finset.induction_on with
    | empty => intro m; simp
    | insert a s ha ih =>
      intro m
      rw [Finset.sum_insert ha, add_comm (Pi.single a _), ← add_assoc, h1, ih]
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  let r : Fin g → Fin n := fun i => ⟨(m i % n).toNat, by
    have h0 := Int.emod_nonneg (m i) hn'.ne'
    have h1 := Int.emod_lt_of_pos (m i) hn'
    omega⟩
  have hm : m = (fun i => ((r i : ℕ) : ℤ)) + ∑ j, Pi.single j (m j / n * n) := by
    rw [Finset.univ_sum_single (fun j => m j / n * n)]
    funext i
    have h0 := Int.emod_nonneg (m i) hn'.ne'
    simp only [r, Pi.add_apply, Int.toNat_of_nonneg h0]
    have := Int.emod_add_mul_ediv (m i) n
    linarith
  rw [hm, h2]
  exact hbox r
end GlobalTheory.ClassicalTheta
