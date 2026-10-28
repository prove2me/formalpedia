-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_local_complete_intersection_bezout_height_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T21:43:50.569087+00:00
-- url     : https://prove2.me/submissions/bd23aace-1ac7-42d8-ad3a-1fa00e7bd979

import Mathlib
import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m k : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
    (f : Fin k → MvPolynomial (Fin (m + 1)) Complex)
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal : (Ideal.span (Set.range f)).IsMinimalPrime P)
    (hdegree : ∀ j, logarithmicDegreeBound w H (f j))
    (A : Finset (Fin (m + 1)))
    (hA : coordinateNormalBasisAtPrime P A)
    (hcard : A.card = P.height)
    (L : Nat)
    (hlength : componentLocalLength (Ideal.span (Set.range f)) P = (L : ENat))
    (hz : P.height = 0) :
    (L : Real) * (∏ i ∈ A, (w i : Real)) ≤ 2 * H ^ A.card := by
  have hA0 : A.card = 0 := by
    have : (A.card : ℕ∞) = 0 := by rw [hcard, hz]
    exact_mod_cast this
  have hAe : A = ∅ := Finset.card_eq_zero.mp hA0
  subst hAe
  simp only [Finset.prod_empty, mul_one, Finset.card_empty, pow_zero]
  have hP : P = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp hz
  have hI : Ideal.span (Set.range f) = ⊥ := le_bot_iff.mp (hP ▸ hminimal.1.2)
  rw [hI] at hlength
  unfold componentLocalLength at hlength
  set Rp := Localization.AtPrime P
  rw [Ideal.map_bot] at hlength
  have hmax : IsLocalRing.maximalIdeal Rp = ⊥ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact (Ideal.map_eq_bot_iff_le_ker _).mpr (fun x hx => by rw [hP, Ideal.mem_bot] at hx; rw [hx]; exact (RingHom.ker _).zero_mem)
  have hfield : IsField Rp := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax
  letI : Field Rp := hfield.toField
  have h1 : Module.length Rp Rp = 1 := Module.length_eq_one Rp Rp
  rw [(Submodule.quotEquivOfEqBot (⊥ : Ideal Rp) rfl).length_eq, h1] at hlength
  have : L = 1 := by exact_mod_cast hlength.symm
  rw [this]; norm_num
