-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.mem_borel_inf_integralGL_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:29.196729+00:00
-- url     : https://prove2.me/submissions/6292cf21-9f9c-4e14-a65f-ce8215538443

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa

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
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
variable [ValuativeRel F]
namespace GroundTheory.Automorphic.Iwasawa
theorem _root_.solution {g : GL (Fin n) F} :
    g ∈ borel F n ⊓ integralGL F n ↔
      g ∈ borel F n ∧ (∀ i j, g i j ∈ 𝒪[F]) ∧ ∀ i, valuation F (g i i) = 1 := by
  have hint := Valuation.integer.integers (valuation F)
  constructor
  · rintro ⟨hB, hK⟩
    obtain ⟨h1, h2⟩ := (mem_integralGL_iff F n).1 hK
    refine ⟨hB, h1, fun i => ?_⟩
    have h2' := h2 i i
    rw [inv_apply_self_of_mem_borel F n hB] at h2'
    have hne := apply_self_ne_zero_of_mem_borel F n hB i
    have hu : IsUnit (⟨g i i, h1 i i⟩ : 𝒪[F]) :=
      isUnit_iff_exists_inv.2 ⟨⟨(g i i)⁻¹, h2'⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩
    exact hint.isUnit_iff_valuation_eq_one.1 hu
  · rintro ⟨hB, h1, h2⟩
    refine ⟨hB, ?_⟩
    let A : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨g i j, h1 i j⟩
    have hAu : A.IsUpperTriangular := fun i j hij => Subtype.ext (hB hij)
    have hdet : IsUnit A.det := by
      rw [det_of_isUpperTriangular hAu]
      exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
        fun i _ => hint.isUnit_iff_valuation_eq_one.2 (h2 i)
    refine ⟨((Matrix.isUnit_iff_isUnit_det A).2 hdet).unit, Units.ext (Matrix.ext fun i j => ?_)⟩
    rw [integralGLHom_apply, IsUnit.unit_spec]
    rfl
end GroundTheory.Automorphic.Iwasawa
