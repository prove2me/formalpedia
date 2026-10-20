-- Prove2me | solution 1 for OAI.CirculantHadamard.Barker.periodic_eq_aperiodic_add
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T15:16:46.102742+00:00
-- url     : https://prove2.me/submissions/4920b52d-a7d5-4714-b1ac-c806f454ad2c

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/Barker/Wraparound.lean:L9-L69
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.Barker.periodic_eq_aperiodic_add. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_Model

-- ---- from OAI.LinearAlgebra.Barker.Wraparound ----
namespace OAI

namespace CirculantHadamard.Barker
open scoped BigOperators

theorem periodic_eq_aperiodic_add {n : ℕ} [NeZero n]
    (h : Fin n → ℤ) (a : Fin n) (_ : a ≠ 0) :
    periodic h a = aperiodic h a.val + aperiodic h (n - a.val) := by
  have ha_le : a.val ≤ n := Nat.le_of_lt a.isLt
  have hn : a.val + (n - a.val) = n := Nat.add_sub_of_le ha_le
  let f : Fin n → ℤ := fun j => h j * h (j - a)
  have split := Fin.sum_univ_add
    (fun j : Fin (a.val + (n - a.val)) => f (j.cast hn))
  rw [Fin.sum_congr' f hn] at split
  have low :
      (∑ j : Fin a.val, f ((Fin.castAdd (n - a.val) j).cast hn)) =
        aperiodic h (n - a.val) := by
    have hc : n - (n - a.val) = a.val := by omega
    have reindex : aperiodic h (n - a.val) =
        ∑ j : Fin a.val,
          h ⟨j.val, by omega⟩ * h ⟨j.val + (n - a.val), by omega⟩ := by
      unfold aperiodic
      apply Fintype.sum_equiv (finCongr hc)
      intro j
      rfl
    rw [reindex]
    apply Finset.sum_congr rfl
    intro j _
    have hsub : ((Fin.castAdd (n - a.val) j).cast hn - a) =
        (⟨j.val + (n - a.val), by omega⟩ : Fin n) := by
      apply Fin.ext
      have hlt : (Fin.castAdd (n - a.val) j).cast hn < a := by
        change j.val < a.val
        exact j.isLt
      rw [Fin.coe_sub_iff_lt.mpr hlt]
      dsimp only [Fin.val_cast, Fin.val_castAdd]
      omega
    change h ((Fin.castAdd (n - a.val) j).cast hn) *
        h ((Fin.castAdd (n - a.val) j).cast hn - a) = _
    rw [hsub]
    rfl
  have high :
      (∑ j : Fin (n - a.val), f ((Fin.natAdd a.val j).cast hn)) =
        aperiodic h a.val := by
    unfold aperiodic
    apply Finset.sum_congr rfl
    intro j _
    have hsub : ((Fin.natAdd a.val j).cast hn - a) =
        (⟨j.val, by omega⟩ : Fin n) := by
      apply Fin.ext
      have hle : a ≤ (Fin.natAdd a.val j).cast hn := by
        change a.val ≤ a.val + j.val
        omega
      rw [Fin.sub_val_of_le hle]
      dsimp only [Fin.val_cast, Fin.val_natAdd]
      omega
    change h ((Fin.natAdd a.val j).cast hn) *
        h ((Fin.natAdd a.val j).cast hn - a) = _
    rw [hsub, mul_comm]
    congr 1
    apply congrArg h
    apply Fin.ext
    change a.val + j.val = j.val + a.val
    omega
  change (∑ j : Fin n, f j) = _
  rw [split, low, high, add_comm]

end CirculantHadamard.Barker

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.Barker
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.CirculantHadamard.Barker.periodic_eq_aperiodic_add := @_root_.OAI.CirculantHadamard.Barker.periodic_eq_aperiodic_add
