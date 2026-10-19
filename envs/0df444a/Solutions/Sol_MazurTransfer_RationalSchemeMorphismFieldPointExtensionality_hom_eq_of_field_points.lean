-- Prove2me | solution 1 for MazurTransfer.RationalSchemeMorphismFieldPointExtensionality.hom_eq_of_field_points
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T19:49:15.84297+00:00
-- url     : https://prove2.me/submissions/ad483f0f-b377-4585-958f-79522e81e85a

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: morphisms from a reduced Q-scheme to a separated Q-scheme
are determined by all characteristic-zero perfect field points. The proof
uses the literal residue-field maps at all source points, without a density
claim about rational points. Named downstream consumer: the cyclotomic and
norm identities on the existing rational order-13 Picard scheme.
-/
import Mathlib

noncomputable section
open CategoryTheory AlgebraicGeometry
variable {X Y : Scheme} (cX : X ⟶ Spec (CommRingCat.of ℚ))
    (cY : Y ⟶ Spec (CommRingCat.of ℚ)) [IsReduced X] [IsSeparated cY]

theorem solution (f g : X ⟶ Y)
    (hf : f ≫ cY = cX) (hg : g ≫ cY = cX)
    (H : ∀ (K : Type) [Field K] [CharZero K] [PerfectField K]
      (a : Spec (CommRingCat.of K) ⟶ X)
      (ha : a ≫ cX = Spec.map (CommRingCat.ofHom (algebraMap ℚ K))),
        a ≫ f = a ≫ g) : f = g := by
  apply AlgebraicGeometry.ext_of_fromSpecResidueField_eq f g cY Set.univ dense_univ
    (fun x _ => ?_) (hf.trans hg.symm)
  let K : Type := X.residueField x
  letI : Field K := inferInstanceAs (Field (X.residueField x))
  let a : Spec (CommRingCat.of K) ⟶ X := X.fromSpecResidueField x
  let r : ℚ →+* K := (Spec.preimage (a ≫ cX)).hom
  haveI : CharZero K := by
    refine ⟨fun n m hnm => ?_⟩
    apply (Nat.cast_injective (R := ℚ))
    apply r.injective
    simpa only [map_natCast] using hnm
  have hs : a ≫ cX = Spec.map (CommRingCat.ofHom (algebraMap ℚ K)) := by
    have hr : CommRingCat.ofHom (algebraMap ℚ K) = Spec.preimage (a ≫ cX) :=
      CommRingCat.hom_ext (Subsingleton.elim _ _)
    rw [hr, Spec.map_preimage]
  exact H K a hs

#print axioms solution
