-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.val_eq_of_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:13.282902+00:00
-- url     : https://prove2.me/submissions/bac085d6-eb53-4133-aa9c-ef665ca2b512

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Finset
variable {n : ℕ} {w : Equiv.Perm (Fin n)}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) :
    ∀ (g : ℕ) (z y : Fin n), (w y).val = (w z).val + g → z ≤ y →
      ∀ x : Fin n, z ≤ x → x ≤ y → (w x).val = (w z).val + (x.val - z.val) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro z y hgap hzy x hzx hxy
  rw [Fin.le_iff_val_le_val] at hzy hzx hxy
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    have hyz : y = z := w.injective (Fin.ext (by omega))
    subst hyz
    have hxy' : x = y := Fin.ext (by omega)
    subst hxy'
    simp
  · have hlt : (w z).val + 1 < n := by have := (w y).isLt; omega
    set p := w.symm ⟨(w z).val + 1, hlt⟩ with hp
    have hwp : (w p).val = (w z).val + 1 := by simp [hp]
    have hzy' : z.val < y.val := by
      rcases Nat.lt_or_eq_of_le hzy with h | h
      · exact h
      · have : z = y := Fin.ext h
        subst this
        omega
    rcases lt_trichotomy p.val z.val with hpz | hpz | hpz
    ·
      exfalso
      have key := ih (g - 1) (by omega) p y (by omega) (Fin.le_iff_val_le_val.2 (by omega)) z
        (Fin.le_iff_val_le_val.2 (by omega)) (Fin.le_iff_val_le_val.2 hzy)
      omega
    · exfalso
      have : p = z := Fin.ext hpz
      rw [this] at hwp
      omega
    ·
      have hp1 : p.val = z.val + 1 := hB z p (Fin.lt_def.2 hpz) hwp
      rcases Nat.eq_or_lt_of_le hzx with hx | hx
      · have : x = z := Fin.ext hx.symm
        subst this
        simp
      · have key := ih (g - 1) (by omega) p y (by omega) (Fin.le_iff_val_le_val.2 (by omega)) x
          (Fin.le_iff_val_le_val.2 (by omega)) (Fin.le_iff_val_le_val.2 hxy)
        omega
end GroundTheory.Automorphic.Whittaker
