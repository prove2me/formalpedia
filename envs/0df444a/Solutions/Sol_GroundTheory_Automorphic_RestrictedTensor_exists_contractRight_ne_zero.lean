-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.exists_contractRight_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:24:08.648519+00:00
-- url     : https://prove2.me/submissions/bd0172a4-fbed-4329-8c54-57f751678cbb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contractRight_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set TensorProduct
open scoped TensorProduct
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂]
  {V₁ V₂ V₁' V₂' : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup V₁'] [Module ℂ V₁'] [AddCommGroup V₂'] [Module ℂ V₂']
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {z : V₁ ⊗[ℂ] V₂} (hz : z ≠ 0) :
    ∃ l : Dual ℂ V₂, contractRight l z ≠ 0 := by
  classical
  let b := Basis.ofVectorSpace ℂ V₂
  set F := TensorProduct.equivFinsuppOfBasisRight (M := V₁) b
  have hfz : F z ≠ 0 := fun h => hz (F.injective (h.trans (map_zero F).symm))
  obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.1 hfz
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hj₀
  refine ⟨b.coord j₀, ?_⟩
  have hz' : z = (F z).sum fun j a => a ⊗ₜ[ℂ] b j := by
    conv_lhs => rw [← F.symm_apply_apply z]
    exact TensorProduct.equivFinsuppOfBasisRight_symm_apply b (F z)
  rw [hz', map_finsuppSum]
  simp only [contractRight_tmul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  rw [Finsupp.sum, Finset.sum_eq_single j₀]
  · simpa using hj₀
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finsupp.mem_support_iff.2 hj₀) h
end GroundTheory.Automorphic.RestrictedTensor
