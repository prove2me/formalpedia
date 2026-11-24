-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.coaction_counit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:56:31.953026+00:00
-- url     : https://prove2.me/submissions/434612ea-3ba5-4546-b9d5-f06e03fe2569

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Theorems.Thm_GlobalTheory_AffineQuotient_specHom_injective
import Theorems.Thm_GlobalTheory_AffineQuotient_specHom_counit
import Theorems.Thm_GlobalTheory_AffineQuotient_specHom_comp_coaction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TensorProduct Algebra.TensorProduct
open GlobalTheory GlobalTheory.AffineQuotient
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]
variable {Λ B : Type} [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A]
  (i : specOver R Λ ⟶ A) (v : specOver R B ⟶ A) (ρ : B →ₐ[R] B ⊗[R] Λ)
  (hρ : specHom ρ ≫ v = (specHom includeRight ≫ i) * (specHom includeLeft ≫ v))
include hρ
namespace GlobalTheory.AffineQuotient
theorem _root_.solution [IsMonHom i] [Mono v] (b : B) :
    TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b := by
  let φ : B ⊗[R] Λ →ₐ[R] B := Algebra.TensorProduct.lift (AlgHom.id R B)
    ((Algebra.ofId R B).comp (Bialgebra.counitAlgHom R Λ)) fun _ _ ↦ .all _ _
  have h := specHom_comp_coaction i v ρ hρ φ
  rw [lift_comp_includeRight', lift_comp_includeLeft, specHom_counit, Category.assoc,
    IsMonHom.one_hom, ← Hom.one_def, _root_.one_mul, cancel_mono] at h
  have h1 : φ (ρ b) = b := congr($(specHom_injective h) b)
  refine Eq.trans ?_ h1
  generalize ρ b = z
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [φ, Algebra.smul_def, _root_.mul_comm]
end GlobalTheory.AffineQuotient
