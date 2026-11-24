-- Prove2me | solution 1 for GlobalTheory.ProjModFinIso.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:38:48.831241+00:00
-- url     : https://prove2.me/submissions/dfb128de-2686-4b6e-bc02-f61c2583a4e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
import Theorems.Thm_GlobalTheory_ProjModFinIso_projective_of_isTorsionFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.ProjModFinIso
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace GlobalTheory.ProjModFinIso
theorem _root_.solution (X : Type) [AddCommGroup X] [Module R X] [Module.Projective R X]
    [Nontrivial X] :
    ∃ (I : (Ideal R)⁰) (K : Submodule R X), Nonempty (X ≃ₗ[R] K × (I : Ideal R)) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective R X)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have hsx : s x ≠ 0 := by
    intro h
    apply hx
    have := LinearMap.congr_fun hs x
    simp only [LinearMap.comp_apply, h, map_zero, LinearMap.id_apply] at this
    exact this.symm
  obtain ⟨a, ha⟩ : ∃ a, s x a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hsx (Finsupp.ext h)
  let f : X →ₗ[R] R := Finsupp.lapply a ∘ₗ s
  have hI : LinearMap.range f ≠ ⊥ := by
    intro h
    have hm : f x ∈ LinearMap.range f := LinearMap.mem_range_self f x
    rw [h, Submodule.mem_bot] at hm
    exact ha hm
  let I : (Ideal R)⁰ := ⟨LinearMap.range f, mem_nonZeroDivisors_of_ne_zero hI⟩
  let g := f.rangeRestrict
  haveI := projective_of_isTorsionFree (R := R) (LinearMap.range f)
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id f.surjective_rangeRestrict
  have hex : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
  obtain ⟨e, -⟩ := hex.splitSurjectiveEquiv (LinearMap.ker g).injective_subtype ⟨l, hl⟩
  exact ⟨I, LinearMap.ker g, ⟨e⟩⟩
end GlobalTheory.ProjModFinIso
