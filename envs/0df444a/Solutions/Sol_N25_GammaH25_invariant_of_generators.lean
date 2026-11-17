-- Prove2me | solution 1 for N25.GammaH25_invariant_of_generators
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:15.168195+00:00
-- url     : https://prove2.me/submissions/0c86f999-14f1-4fd0-bb71-2971372228c9

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_GammaH25_factorization

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup

namespace N25

/-- Invariance under Gamma1 and a lift of the residue generator suffices. -/
theorem _root_.solution (T : Gamma0 25)
    (hT : CohCarrier.gamma0Units 25 T = (ZMod.unitOfCoprime 7 (by decide))⁻¹)
    (f : UpperHalfPlane → ℂ)
    (h1 : ∀ A ∈ Gamma1 25, ∀ τ : UpperHalfPlane, f (A • τ) = f τ)
    (hgen : ∀ τ : UpperHalfPlane, f ((T : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) = f τ)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : A ∈ CohCarrier.GammaH 25 N25.H25) (τ : UpperHalfPlane) :
    f (A • τ) = f τ := by
  let K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    { carrier := {B | ∀ z : UpperHalfPlane, f (B • z) = f z}
      one_mem' := by intro z; simp
      mul_mem' := by
        intro B C hB hC z
        rw [mul_smul, hB, hC]
      inv_mem' := by
        intro B hB z
        have h := hB (B⁻¹ • z)
        simpa using h.symm }
  have hsub : Gamma1 25 ≤ K := fun B hB => h1 B hB
  have hTK : (T : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ K := hgen
  obtain ⟨n, hn⟩ := GammaH25_factorization T hT A hA
  have hAK : A ∈ K := by
    have h := K.mul_mem (hsub hn) (K.inv_mem (K.zpow_mem hTK n))
    simpa only [mul_inv_cancel_right] using h
  exact hAK τ

end N25
