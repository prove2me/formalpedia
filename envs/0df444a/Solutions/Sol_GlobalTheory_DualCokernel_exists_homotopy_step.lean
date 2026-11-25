-- Prove2me | solution 1 for GlobalTheory.DualCokernel.exists_homotopy_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:17:16.635106+00:00
-- url     : https://prove2.me/submissions/f0e429d8-d9bd-4542-95ae-5f982e9936c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Theorems.Thm_GlobalTheory_DualCokernel_exists_smul_eq_zero_of_fibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R]
namespace GlobalTheory.DualCokernel
theorem _root_.solution (p : Ideal R) [hp : p.IsPrime] {M₀ M₁ M₂ M₃ : Type}
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] [Module.Finite R M₁] [Module.Projective R M₁]
    (a : M₀ →ₗ[R] M₁) (b : M₁ →ₗ[R] M₂) (c : M₂ →ₗ[R] M₃) (hab : ∀ x, b (a x) = 0)
    (hbc : ∀ x, c (b x) = 0)
    (hex : Exact (a.lTensor p.ResidueField) (b.lTensor p.ResidueField))
    (s : R) (hs : s ∉ p) (h₁ : M₂ →ₗ[R] M₁) (h₂ : M₃ →ₗ[R] M₂)
    (hh : ∀ x, b (h₁ x) + h₂ (c x) = s • x) :
    ∃ (t : R) (_ : t ∉ p) (k₀ : M₁ →ₗ[R] M₀) (k₁ : M₂ →ₗ[R] M₁),
      ∀ x, a (k₀ x) + k₁ (b x) = t • x := by
  have hb : ∀ x, b (h₁ (b x)) = s • b x := fun x => by simpa [hbc] using hh (b x)
  set π : M₁ →ₗ[R] M₁ := s • LinearMap.id - h₁ ∘ₗ b with hπ
  have hbπ : b ∘ₗ π = 0 := by
    ext x
    simp [hπ, hb]
  set N := LinearMap.range a ⊔ LinearMap.range (h₁ ∘ₗ b) with hN
  have hsub : Subsingleton (p.ResidueField ⊗[R] (M₁ ⧸ N)) := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective p.ResidueField N.mkQ_surjective y
    have h1 : b.lTensor p.ResidueField (π.lTensor p.ResidueField x) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hbπ]
      simp
    obtain ⟨z, hz⟩ := (hex _).1 h1
    have h2 : N.mkQ ∘ₗ a = 0 := by
      ext w
      exact (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_sup_left ⟨w, rfl⟩)
    have h3 : N.mkQ ∘ₗ π = s • N.mkQ := by
      ext w
      have : N.mkQ (h₁ (b w)) = 0 :=
        (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_sup_right ⟨w, rfl⟩)
      simp only [hπ, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, map_sub, this, sub_zero, map_smul]
    have h4 := congrArg (N.mkQ.lTensor p.ResidueField) hz
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h2, ← LinearMap.comp_apply,
      ← LinearMap.lTensor_comp, h3, LinearMap.lTensor_zero, LinearMap.zero_apply,
      LinearMap.lTensor_smul, LinearMap.smul_apply, ← algebraMap_smul p.ResidueField] at h4
    exact (smul_eq_zero.mp h4.symm).resolve_left
      (fun h0 => hs (Ideal.algebraMap_residueField_eq_zero.mp h0))
  obtain ⟨t, ht, htN⟩ := exists_smul_eq_zero_of_fibre p (M₁ ⧸ N) hsub
  have hmem : ∀ x, (t • π) x ∈ LinearMap.range a := by
    intro x
    have h1 : t • x ∈ N := (Submodule.Quotient.mk_eq_zero N).1 (htN (N.mkQ x))
    obtain ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, huv⟩ := Submodule.mem_sup.mp h1
    rw [LinearMap.smul_apply, ← map_smul, ← huv]
    refine ⟨s • u, ?_⟩
    simp [hπ, hab, hb]
  obtain ⟨k, hk⟩ := Module.projective_lifting_property a.rangeRestrict
    (LinearMap.codRestrict _ _ hmem) a.surjective_rangeRestrict
  refine ⟨t * s, fun h => (hp.mem_or_mem h).elim ht hs, k, t • h₁, fun x => ?_⟩
  have : a (k x) = (t • π) x := congrArg Subtype.val (LinearMap.congr_fun hk x)
  simp [this, hπ, smul_sub, mul_smul]
end GlobalTheory.DualCokernel
