-- Prove2me | solution 1 for IsDedekindDomain.isRegularLocalRing_localization_symmetricPower
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T06:44:21.299375+00:00
-- url     : https://prove2.me/submissions/ab506593-b5a8-450b-880b-4eb7bcd33da7

import Mathlib
import Definitions.Def_RPLib_F2_017

set_option autoImplicit false

open RamanujanPetersson.JacSym in
theorem solution
    {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra k B]
    [Algebra.FiniteType k B] (hB : ¬ IsField B) (g : ℕ)
    (S : Subalgebra k (PiTensorProduct k (fun _ : Fin g => B)))
    (hS : ∀ x, x ∈ S ↔ ∀ σ : Equiv.Perm (Fin g), PiTensorProduct.reindex k (fun _ : Fin g => B) σ x = x)
    (M : Ideal S) [M.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime M) ∧ ringKrullDim (Localization.AtPrime M) = g := by
  have hEq : S = SymRing k B g := by
    ext x
    rw [hS, mem_symRing]
    refine forall_congr' fun σ => ?_
    have hlin : (permHom σ : XPow k B g →ₐ[k] XPow k B g).toLinearMap =
        (PiTensorProduct.reindex k (fun _ : Fin g => B) σ).toLinearMap :=
      PiTensorProduct.ext (MultilinearMap.ext fun b => by
        simp [permHom_tprod]; rfl)
    rw [perm_smul_def, show permHom σ x = PiTensorProduct.reindex k (fun _ : Fin g => B) σ x from
      LinearMap.congr_fun hlin x]
  subst hEq
  exact isRegularLocalRing_symRing hB M

