-- Prove2me | solution 1 for GlobalTheory.OnePoint.exists_section_of_locallyQuasiFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:45:07.221874+00:00
-- url     : https://prove2.me/submissions/a70985de-81c5-463b-81f7-3946a2442754

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_exists_algHom_of_isIntegrallyClosedIn
import Theorems.Thm_GlobalTheory_OnePoint_point_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution {F : Scheme.{u}} (f : F ⟶ Spec (.of K))
    [LocallyQuasiFinite f] (L : Type u) [Field L] [Algebra K L] [IsIntegrallyClosedIn K L]
    (x : Spec (.of L) ⟶ F) (hx : x ≫ f = specAlg(K, L)) :
    ∃ x₀ : Spec (.of K) ⟶ F, specAlg(K, L) ≫ x₀ = x ∧ x₀ ≫ f = 𝟙 _ ∧
      ∀ x₁ : Spec (.of K) ⟶ F, specAlg(K, L) ≫ x₁ = x → x₁ = x₀ := by
  suffices H : ∃ x₀ : Spec (.of K) ⟶ F, specAlg(K, L) ≫ x₀ = x by
    obtain ⟨x₀, h₀⟩ := H
    refine ⟨x₀, h₀, point_ext specAlg(K, L) ?_, fun x₁ h₁ ↦ point_ext _ (h₁.trans h₀.symm)⟩
    rw [reassoc_of% h₀, hx, Category.comp_id]
  obtain ⟨A, i, _, q, hq⟩ := Scheme.exists_Spec_apply_eq (x (Classical.arbitrary _))
  have hle : Set.range x ⊆ Set.range i := by
    rintro _ ⟨t, rfl⟩
    exact ⟨q, hq.trans (congrArg x (Subsingleton.elim _ _))⟩
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ i = x := ⟨_, IsOpenImmersion.lift_fac i x hle⟩
  obtain ⟨a, rfl⟩ := Spec.map_surjective l
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  have hqf : φ.hom.QuasiFinite := by
    have : LocallyQuasiFinite (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp this
  let : Algebra K A := φ.hom.toAlgebra
  have : Algebra.QuasiFinite K A := hqf
  have : Module.Finite K A := .of_quasiFinite
  rw [Category.assoc, ← hφ, ← Spec.map_comp] at hx
  have hc := congrArg CommRingCat.Hom.hom (Spec.map_injective hx)
  let a' : A →ₐ[K] L := ⟨a.hom, fun c ↦ DFunLike.congr_fun hc c⟩
  obtain ⟨ψ, hψ⟩ := exists_algHom_of_isIntegrallyClosedIn a'
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext t
  exact DFunLike.congr_fun hψ t
end GlobalTheory.OnePoint
