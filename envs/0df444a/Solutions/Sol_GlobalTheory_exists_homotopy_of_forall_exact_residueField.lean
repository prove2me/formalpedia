-- Prove2me | solution 1 for GlobalTheory.exists_homotopy_of_forall_exact_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:18.188842+00:00
-- url     : https://prove2.me/submissions/95e09db6-0d1d-47a0-94fd-6ad717dc8908

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Theorems.Thm_GlobalTheory_split_injective_of_forall_lTensor_residueField_injective
import Theorems.Thm_GlobalTheory_lTensor_liftQ_injective_of_exact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
open GlobalTheory
variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
namespace GlobalTheory
theorem _root_.solution [Module.Finite R B] [Module.Projective R B]
    [Module.Finite R C] [Module.Projective R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Exact (f.lTensor m.ResidueField) (g.lTensor m.ResidueField)) :
    ∃ (s : B →ₗ[R] A) (t : C →ₗ[R] B), f ∘ₗ s + t ∘ₗ g = LinearMap.id := by
  have hle : LinearMap.range f ≤ LinearMap.ker g := LinearMap.range_le_ker_iff.2 hfg
  obtain ⟨r, hr⟩ := split_injective_of_forall_lTensor_residueField_injective
    ((LinearMap.range f).liftQ g hle) fun m _ => lTensor_liftQ_injective_of_exact _ hle (h m)
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ r
    (Submodule.mkQ_surjective _)
  have hmem : ∀ b, (LinearMap.id - t ∘ₗ g : B →ₗ[R] B) b ∈ LinearMap.range f := by
    intro b
    have h1 := LinearMap.congr_fun ht (g b)
    have h2 := LinearMap.congr_fun hr (Submodule.Quotient.mk b)
    simp only [LinearMap.comp_apply, Submodule.liftQ_apply, Submodule.mkQ_apply,
      LinearMap.id_apply] at h1 h2
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, ← Submodule.Quotient.eq,
      h1, h2]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict
    (LinearMap.codRestrict _ _ hmem) f.surjective_rangeRestrict
  refine ⟨s, t, LinearMap.ext fun b => ?_⟩
  have := congrArg Subtype.val (LinearMap.congr_fun hs b)
  simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.rangeRestrict] at this
  simp [this]
end GlobalTheory
