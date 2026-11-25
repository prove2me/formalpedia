-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ProfiniteInteger.exists_eq_nsmul_of_proj_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:44.494552+00:00
-- url     : https://prove2.me/submissions/d5d03e0a-f611-4cd6-b724-f8664d809acc

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open GroundTheory.LocalField.Abstract.ProfiniteInteger
namespace GroundTheory.LocalField.Abstract.ProfiniteInteger
theorem _root_.solution {n : ℕ+} {x : ℤ̂} (hx : proj n x = 0) :
    ∃ y : ℤ̂, x = (n : ℕ) • y := by

  let v : ℕ+ → ℕ := fun m => (proj (n * m) x).val
  have hdvd : ∀ m : ℕ+, (n : ℕ) ∣ v m := by
    intro m
    have h := proj_eq_val_cast (n := n) (k := n * m) (by simp) x
    rw [hx, eq_comm, ZMod.natCast_eq_zero_iff] at h
    exact h
  have hmod : ∀ m k : ℕ+, (m : ℕ) ∣ (k : ℕ) → v k ≡ v m [MOD (n : ℕ) * m] := by
    intro m k hmk
    have h := proj_eq_val_cast (n := n * m) (k := n * k) (by simpa using Nat.mul_dvd_mul_left _ hmk) x
    have h2 : ((v m : ℕ) : ZMod ((n * m : ℕ+) : ℕ)) = proj (n * m) x := ZMod.natCast_zmod_val _
    rw [← h2, ZMod.natCast_eq_natCast_iff, PNat.mul_coe] at h
    exact h.symm
  let yf : ∀ m : ℕ+, ZMod m := fun m => ((v m / n : ℕ) : ZMod m)
  have hy : yf ∈ profiniteIntegers := by
    rw [mem_profiniteIntegers]
    intro m k hmk
    simp only [yf, map_natCast]
    rw [ZMod.natCast_eq_natCast_iff]
    have h := hmod m k hmk
    obtain ⟨a, ha⟩ := hdvd k
    obtain ⟨b, hb⟩ := hdvd m
    rw [ha, hb] at h ⊢
    rw [Nat.mul_div_cancel_left _ n.pos, Nat.mul_div_cancel_left _ n.pos]
    exact Nat.ModEq.mul_left_cancel' n.ne_zero h
  refine ⟨⟨yf, hy⟩, ?_⟩
  ext m
  rw [map_nsmul, nsmul_eq_mul]
  change proj m x = (n : ZMod m) * ((v m / n : ℕ) : ZMod m)
  rw [← Nat.cast_mul, Nat.mul_div_cancel' (hdvd m)]
  exact proj_eq_val_cast (n := m) (k := n * m) (by simp) x
end GroundTheory.LocalField.Abstract.ProfiniteInteger
