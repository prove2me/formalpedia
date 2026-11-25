-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:52:55.211163+00:00
-- url     : https://prove2.me/submissions/61b0c79a-345b-4422-9878-b5d865c33993

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
import Theorems.Thm_GlobalTheory_BCT_DimFac_map_smulRight
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_asAlgebraHom_eq
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_contractLeft_ne_zero
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GroundTheory.Automorphic.RestrictedTensor Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.DimFac
variable {Γ V W M : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.BCT.DimFac
theorem _root_.solution {ρ : Representation ℂ Γ V} (hρ : ρ.IsIrreducible) {σ : Representation ℂ Γ W}
    (hσ : σ.IsIrreducible) (hs : ∀ T : End ℂ W, (∀ g, T * σ g = σ g * T) → ∃ c : ℂ, T = c • 1) {e : Γ →* Γ}
    (he : ∀ g, e (e g) = e g) (hc : ∀ g y, Commute ((e g)⁻¹ * g) (e y))
    {f : W →ₗ[ℂ] V} (hf0 : f ≠ 0) (hf : ∀ g x, f (σ g x) = ρ (e g) (f x)) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (τ : Representation ℂ Γ M) (Φ : W ⊗[ℂ] M ≃ₗ[ℂ] V),
      (∀ g, τ (e g) = 1) ∧ ∀ g t, Φ (TensorProduct.map (σ g) (τ g) t) = ρ g (Φ t) := by
  classical
  let ev : W ⊗[ℂ] homSp σ ρ e →ₗ[ℂ] V := TensorProduct.lift (homSp σ ρ e).subtype.flip
  have hev : ∀ x (u : homSp σ ρ e), ev (x ⊗ₜ u) = u.1 x := fun x u => rfl
  have heq : ∀ g t, ev (TensorProduct.map (σ g) (homRep σ ρ e hc g) t) = ρ g (ev t) := by
    intro g t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x u =>
      rw [TensorProduct.map_tmul, hev, hev]
      change ρ ((e g)⁻¹ * g) (u.1 (σ g x)) = _
      rw [u.2 g x, rep_mul, (hc g g).eq, mul_inv_cancel_left]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsurj : Function.Surjective ev := by
    rcases ((GlobalTheory.CuspRep.isIrreducible_iff ρ).1 hρ).2 (LinearMap.range ev) (by
      rintro g _ ⟨t, rfl⟩
      exact ⟨_, heq g t⟩) with h | h
    · refine absurd (LinearMap.ext fun x => ?_) hf0
      have : ev (x ⊗ₜ ⟨f, hf⟩) ∈ LinearMap.range ev := ⟨_, rfl⟩
      rw [h] at this
      exact this
    · exact LinearMap.range_eq_top.1 h
  have hinj : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun t ht => ?_
    by_contra h0
    obtain ⟨l, hl⟩ := exists_contractLeft_ne_zero h0
    refine hl (Subtype.ext (LinearMap.ext fun y => ?_))
    obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
    obtain ⟨r, hr⟩ := exists_asAlgebraHom_eq hσ hs (l.smulRight y) (s.image Prod.fst)
    have key : ∀ (r : MonoidAlgebra ℂ Γ) (u : homSp σ ρ e) x,
        u.1 (σ.asAlgebraHom r x) = Representation.asAlgebraHom (ρ.comp e) r (u.1 x) := by
      intro r u x
      induction r using MonoidAlgebra.induction_on with
      | of g => simpa using u.2 g x
      | add a b ha hb => simp [ha, hb]
      | smul c a ha => simp [ha]
    have h1 : ev (TensorProduct.map (l.smulRight y) LinearMap.id (∑ i ∈ s, i.1 ⊗ₜ[ℂ] i.2)) =
        Representation.asAlgebraHom (ρ.comp e) r (ev (∑ i ∈ s, i.1 ⊗ₜ[ℂ] i.2)) := by
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [TensorProduct.map_tmul, hev, hev, ← key, hr _ (Finset.mem_image_of_mem _ hi)]
      rfl
    rw [ht, map_zero, map_smulRight, hev] at h1
    exact h1
  refine ⟨homSp σ ρ e, inferInstance, inferInstance, homRep σ ρ e hc, LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩,
    fun g => LinearMap.ext fun u => Subtype.ext (LinearMap.ext fun x => ?_), heq⟩
  change ρ ((e (e g))⁻¹ * e g) (u.1 x) = u.1 x
  rw [he, inv_mul_cancel, map_one, Module.End.one_apply]
end GlobalTheory.BCT.DimFac
