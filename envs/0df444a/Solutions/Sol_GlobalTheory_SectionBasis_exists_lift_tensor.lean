-- Prove2me | solution 1 for GlobalTheory.SectionBasis.exists_lift_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:59.828839+00:00
-- url     : https://prove2.me/submissions/c4d7fb8b-7c73-44f7-b241-91e3a18c92ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
import Theorems.Thm_GlobalTheory_SectionBasis_incl_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
  [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']
namespace GlobalTheory.SectionBasis
theorem _root_.solution {R : Type} [CommRing R] (a : K' →+* R) (ψ : Ω →+* R)
    (hc : ∀ c : K, ψ (algebraMap K Ω c) = a (algebraMap K K' c)) :
    ∃ f : K' ⊗[Kl] (Kl ⊗[K] Ω) →+* R, (∀ y, f (algebraMap K' _ y) = a y) ∧ ∀ ω, f (incl K Kl K' ω) = ψ ω := by
  letI : Algebra K' R := a.toAlgebra
  letI : Algebra Kl R := (a.comp (algebraMap Kl K')).toAlgebra
  letI : Algebra K R := (a.comp (algebraMap K K')).toAlgebra
  haveI : IsScalarTower Kl K' R := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K Kl R := IsScalarTower.of_algebraMap_eq fun c => by
    show a (algebraMap K K' c) = a (algebraMap Kl K' (algebraMap K Kl c))
    rw [← IsScalarTower.algebraMap_apply]
  let ε : Ω →ₐ[K] R := { ψ with commutes' := hc }
  let α₁ : Kl ⊗[K] Ω →ₐ[Kl] R :=
    Algebra.TensorProduct.lift (Algebra.ofId Kl _) ε fun _ _ => Commute.all _ _
  let α₀ : K' ⊗[Kl] (Kl ⊗[K] Ω) →ₐ[K'] R :=
    Algebra.TensorProduct.lift (Algebra.ofId K' _) α₁ fun _ _ => Commute.all _ _
  refine ⟨α₀.toRingHom, fun y => α₀.commutes y, fun ω => ?_⟩
  show α₀ _ = _
  rw [incl_apply, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one, map_one, one_mul,
    one_mul]
  rfl
end GlobalTheory.SectionBasis
