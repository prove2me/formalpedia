-- Prove2me | solution 1 for NumberField.algebraMap_restrictNormal_smul
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:33.386948+00:00
-- url     : https://prove2.me/submissions/5a8e69c0-819e-4960-829f-a3638fef444a

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Mathlib.NumberTheory.NumberField.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Automorphisms acting on the ring of integers

A ring automorphism of a field restricts to its ring of integers, because it preserves
integrality. This file records how that restricted action relates to the ambient one: the
structure map `𝓞 K → K` is equivariant, carrying `σ • z` to `σ` applied to the image of `z`.
It also records that restriction to a normal subfield commutes with the map between the two
rings of integers.

For a tower `F / K` of fields it also records that the `Gal(F/K)`-action on `𝓞 F` commutes with
the `𝓞 K`-scalar action: a `K`-algebra automorphism fixes `K` pointwise, hence fixes the image of
`𝓞 K`. Mathlib supplies the corresponding `SMulCommClass` only over the base `ℤ`
(`integralClosure`'s own instance, with `ℤ` the ring `𝓞 F` is integral over), which is what a
Frobenius over `ℚ` needs; a *relative* Frobenius over a general base `K` needs this one.

`𝓞 K` is the integral closure of `ℤ`, and any ring automorphism of `K` preserves `ℤ`-integrality,
so the base ring `R` over which `σ` is linear is irrelevant to both statement and proof; it is a
free parameter, specialized to `ℚ` by the callers. Nothing here needs `K` to be finite-dimensional
either, so `[NumberField K]` is not assumed.

This is the `AlgEquiv` specialization of Mathlib's `integralClosure.coe_smul`, which is stated
for an arbitrary `[Group G] [MulSemiringAction G K]` and therefore cannot phrase the right-hand
side as function application. Callers want exactly that applied form, so the specialization is
recorded once here rather than reconstructed at each use site.

## Main results

* `NumberField.algebraMap_smul_eq_apply`: `algebraMap (𝓞 K) K (σ • z) = σ (algebraMap (𝓞 K) K z)`.
* `NumberField.algebraMap_restrictNormal_smul`: mapping the action of a restricted automorphism
  into the top ring of integers gives the action of the original automorphism.
* `NumberField.RingOfIntegers.smulCommClass`: `Gal(F/K)` acting on `𝓞 F` commutes with the
  `𝓞 K`-action.
* `AlgEquiv.mapAlgEquiv_symm_autCongr_smul`: restriction to rings of integers intertwines
  conjugation of automorphisms along an algebra equivalence.
-/

 section

open scoped NumberField

namespace NumberField
end NumberField
section NumberField
open NumberField

variable {R K : Type*} [CommSemiring R] [Field K] [Algebra R K]



variable {M L : Type*} [Field M] [Field L] [Algebra K M] [Algebra M L] [Algebra K L]
  [IsScalarTower K M L] [Normal K M]

/-- **Restriction of automorphisms commutes with the map between rings of integers.** If `M/K`
is normal inside `L`, then acting on `𝓞 M` by the restriction of `σ ∈ Gal(L/K)` and mapping to
`𝓞 L` agrees with first mapping and then acting by `σ`. -/
@[simp]
theorem solution (σ : L ≃ₐ[K] L) (x : 𝓞 M) :
    _root_.Algebra.algebraMap (𝓞 M) (𝓞 L) (σ.restrictNormal M • x) =
      σ • _root_.Algebra.algebraMap (𝓞 M) (𝓞 L) x := by
  apply _root_.NumberField.RingOfIntegers.ext
  -- `RingOfIntegers.ext` exposes coercions into `L`; state them as the canonical algebra maps so
  -- the two scalar towers can be rewritten explicitly.
  change _root_.Algebra.algebraMap (𝓞 L) L (_root_.Algebra.algebraMap (𝓞 M) (𝓞 L) (σ.restrictNormal M • x)) =
    _root_.Algebra.algebraMap (𝓞 L) L (σ • _root_.Algebra.algebraMap (𝓞 M) (𝓞 L) x)
  rw [← _root_.IsScalarTower.algebraMap_apply (𝓞 M) (𝓞 L) L,
    _root_.IsScalarTower.algebraMap_apply (𝓞 M) M L,
    _root_.NumberField.algebraMap_smul_eq_apply, _root_.NumberField.algebraMap_smul_eq_apply,
    ← _root_.IsScalarTower.algebraMap_apply (𝓞 M) (𝓞 L) L,
    _root_.IsScalarTower.algebraMap_apply (𝓞 M) M L]
  exact _root_.AlgEquiv.restrictNormal_commutes σ M (_root_.Algebra.algebraMap (𝓞 M) M x)

variable {F : Type*} [Field F] [Algebra K F]



end NumberField

namespace AlgEquiv
end AlgEquiv
section AlgEquiv
open AlgEquiv

variable {R K L : Type*} [Field R] [Field K] [Field L] [Algebra R K] [Algebra R L]



end AlgEquiv

end
end
