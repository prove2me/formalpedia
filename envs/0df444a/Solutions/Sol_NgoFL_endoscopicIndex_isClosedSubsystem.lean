-- Prove2me | solution 1 for NgoFL.endoscopicIndex_isClosedSubsystem
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T18:17:49.997765+00:00
-- url     : https://prove2.me/submissions/1e21819a-780e-48f4-ab5b-24c2c26257d8

import Mathlib
import Definitions.Def_NgoEndoscopicDiscriminant

open NgoFL

/-- **Ngô, §1.8**: the root system `Φ_H = {α ∈ Φ : κ(α^∨) = 1}` of the endoscopic group
attached to `κ` is a closed subsystem of `Φ`. -/
theorem solution {ι M N A : Type*} [AddCommGroup M]
    [AddCommGroup N] [CommGroup A] (P : RootPairing ι ℤ M N)
    (κ : Multiplicative N →* A) :
    IsClosedSubsystem P (endoscopicIndex P κ) := by
  have key : ∀ i, i ∈ endoscopicIndex P κ ↔ κ (Multiplicative.ofAdd (P.coroot i)) = 1 :=
    fun _ => Iff.rfl
  constructor
  · -- stability under `α ↦ -α`
    intro i hi
    rw [key] at hi ⊢
    have hcoroot : P.coroot (negIdx P i) = - P.coroot i := by
      simp [negIdx]
    rw [hcoroot, show Multiplicative.ofAdd (- P.coroot i)
      = (Multiplicative.ofAdd (P.coroot i))⁻¹ from rfl, map_inv, hi, inv_one]
  · -- stability under the reflections of the subsystem
    intro i hi j hj
    rw [key] at hi hj ⊢
    have hcoroot : P.coroot (P.reflectionPerm i j)
        = P.coroot j - P.pairing i j • P.coroot i := by
      rw [P.coroot_reflectionPerm, P.coreflection_apply_coroot]
    rw [hcoroot, show Multiplicative.ofAdd (P.coroot j - P.pairing i j • P.coroot i)
      = Multiplicative.ofAdd (P.coroot j) /
        (Multiplicative.ofAdd (P.coroot i)) ^ (P.pairing i j) from by
          rw [← ofAdd_zsmul, ← ofAdd_sub],
      map_div, map_zpow, hi, hj, one_zpow, div_one]
