-- Prove2me | solution 1 for GlobalTheory.IsoExt.exists_unitary_of_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:42:42.44329+00:00
-- url     : https://prove2.me/submissions/1cff4b20-d3cc-4673-972b-6e8889678d67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUnitaryMatrixOfLatticeIsometry
import Theorems.Thm_GlobalTheory_IsoExt_exists_gl_of_equiv
import Theorems.Thm_GlobalTheory_FrameFibre_herm_of_trace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.IsoExt
namespace GlobalTheory.IsoExt
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (gam : D.La ≃ₗ[𝓞 E] D'.La), cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) → (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) → (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) → ∃ γ : GL (Fin r) E, (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ ∀ a, φ' (gam a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  intro E _ _ _ H D D' r ξ Gm φ φ' gam _ hl hl' hiso
  obtain ⟨γ, hγ⟩ := exists_gl_of_equiv φ φ' hl.1 hl.2.1 hl'.1 hl'.2.1 gam
  refine ⟨γ, ?_, fun a => (hγ a).symm⟩
  by_cases hξ : ξ = 0
  · have h0 : ∀ x : D.La, x = 0 := fun x => by
      apply D.unimod.1
      rw [map_zero]
      refine LinearMap.ext fun y => ?_
      have h := hl.2.2.2.2 x y
      rw [hξ, zero_mul, map_zero] at h
      exact_mod_cast h
    have h1 : ∀ u : Fin r → E, u = 0 := fun u => by
      have hu : u ∈ Submodule.span E (Set.range φ) := by rw [hl.2.1]; trivial
      have hle : Submodule.span E (Set.range φ) ≤ ⊥ := Submodule.span_le.2 (by
        rintro _ ⟨x, rfl⟩
        rw [h0 x, map_zero]
        exact Submodule.zero_mem _)
      exact hle hu
    intro u v
    rw [h1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u), h1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v), h1 u,
      h1 v]
  · exact GlobalTheory.FrameFibre.herm_of_trace φ hl.2.1 Gm γ ξ hξ fun v w => by
      rw [hγ, hγ, ← hl.2.2.2.2, ← hl'.2.2.2.2, hiso]
end GlobalTheory.IsoExt
