-- Prove2me | solution 1 for GlobalTheory.shortComplex_quasiIso_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:51.946861+00:00
-- url     : https://prove2.me/submissions/307c4cef-47cf-4ca0-b08b-0d935a7e897b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
variable {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T) :
    ShortComplex.QuasiIso φ ↔
      (∀ y : T.X₂, T.g y = 0 → ∃ (x : S.X₂) (z : T.X₁), S.g x = 0 ∧ T.f z + φ.τ₂ x = y) ∧
      (∀ (x : S.X₂) (z : T.X₁), S.g x = 0 → T.f z = φ.τ₂ x → ∃ w : S.X₁, S.f w = x) := by
  let γ := ShortComplex.leftHomologyMapData φ S.moduleCatLeftHomologyData
    T.moduleCatLeftHomologyData
  let φK : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom := γ.φK.hom
  let φH : (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) →ₗ[R]
    (LinearMap.ker T.g.hom ⧸ LinearMap.range T.moduleCatToCycles) := γ.φH.hom
  have hi : ∀ x, (φK x : T.X₂) = φ.τ₂ x := fun x => congr($(γ.commi).hom x)
  have hπ : ∀ x, φH (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φK x) :=
    fun x => congr($(γ.commπ).hom x)
  rw [γ.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective φH ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun y hy => ?_, fun x z hx hz => ?_⟩
    · obtain ⟨x, hx⟩ := h2 (Submodule.Quotient.mk ⟨y, hy⟩)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hπ] at hx
      obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).1 hx.symm
      refine ⟨x, z, x.2, ?_⟩
      have : T.f z = y - φK x := congrArg Subtype.val hz
      rw [this, hi, sub_add_cancel]
    · have : φH (Submodule.Quotient.mk ⟨x, hx⟩) = 0 := by
        rw [hπ, Submodule.Quotient.mk_eq_zero]
        exact ⟨z, Subtype.ext (hz.trans (hi ⟨x, hx⟩).symm)⟩
      obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).1
        ((injective_iff_map_eq_zero _).1 h1 _ this)
      exact ⟨w, congrArg Subtype.val hw⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
    · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hπ, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨z, hz⟩ := hx
      obtain ⟨w, hw⟩ := h2 x z x.2 ((congrArg Subtype.val hz).trans (hi x))
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨w, Subtype.ext hw⟩
    · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨x, z, hx, hz⟩ := h1 y y.2
      refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
      rw [hπ]
      symm
      refine (Submodule.Quotient.eq _).2 ⟨z, Subtype.ext ?_⟩
      change T.f z = y - φK ⟨x, hx⟩
      rw [hi, ← hz, add_sub_cancel_right]
end GlobalTheory
