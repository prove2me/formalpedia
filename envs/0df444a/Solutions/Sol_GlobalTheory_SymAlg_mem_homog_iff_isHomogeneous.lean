-- Prove2me | solution 1 for GlobalTheory.SymAlg.mem_homog_iff_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:13:01.41521+00:00
-- url     : https://prove2.me/submissions/a7758225-f7a7-48be-8006-b003547756b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Theorems.Thm_GlobalTheory_SymAlg_algHom_mem_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open scoped DirectSum
open GlobalTheory
open GlobalTheory.SymAlg
variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
namespace GlobalTheory.SymAlg
theorem _root_.solution {ι : Type*} (b : Basis ι R M) (d : ℕ)
    (x : SymmetricAlgebra R M) :
    x ∈ homog R M d ↔ (SymmetricAlgebra.equivMvPolynomial b x).IsHomogeneous d := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, ← MvPolynomial.homogeneousSubmodule_one_pow]
  constructor
  · intro hx
    refine algHom_mem_pow (SymmetricAlgebra.equivMvPolynomial b).toAlgHom _ (fun m => ?_) hx
    have hm : m ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simpa using MvPolynomial.isHomogeneous_X R i
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul r x _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx
  · intro hx
    have h1 : (MvPolynomial.homogeneousSubmodule ι R 1).map
        (SymmetricAlgebra.equivMvPolynomial b).symm.toAlgHom.toLinearMap ≤
        LinearMap.range (SymmetricAlgebra.ι R M) := by
      rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨b i, by simp⟩
    have h2 := Submodule.map_pow (MvPolynomial.homogeneousSubmodule ι R 1)
      (SymmetricAlgebra.equivMvPolynomial b).symm.toAlgHom d
    have h3 : x ∈ ((MvPolynomial.homogeneousSubmodule ι R 1) ^ d).map
        (SymmetricAlgebra.equivMvPolynomial b).symm.toAlgHom.toLinearMap :=
      ⟨_, hx, by simp⟩
    rw [h2] at h3
    exact pow_le_pow_left' h1 d h3
end GlobalTheory.SymAlg
