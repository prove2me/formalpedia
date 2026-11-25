-- Prove2me | solution 1 for GlobalTheory.PrincFree.princ_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:02:07.67914+00:00
-- url     : https://prove2.me/submissions/cd15dfe2-d052-4543-809a-070a5b4715b8

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_PrincipalGroupActsFreelyOnFlags
import Theorems.Thm_GlobalTheory_PrincFree_cmType_of_rt
import Theorems.Thm_GlobalTheory_PrincFree_exists_equiv_of_stab
import Theorems.Thm_GlobalTheory_GamFree_gam_free
import Theorems.Thm_GlobalTheory_LevelHalf_trivial_mod_of_trivial_on_half
import Theorems.Thm_GlobalTheory_latMinkowski


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
open GlobalTheory GlobalTheory.PrincFree
namespace GlobalTheory.PrincFree
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∀ (Ψ : Finset (E →+* ℂ)) (q : ℕ), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → ∀ γ ∈ princ l Gm Di φ0, ∀ x ∈ GG Ψ Gm q, ∀ b ∈ Bor Ψ r, lact γ x = rmul x b → γ = 1 := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 _ ⟨hinj, hsp, hG, _, hEF⟩ Ψ q hΨ γ hγ x hx b hb hxb
  obtain ⟨hU, hhalf, -⟩ := hγ
  obtain ⟨g, hg⟩ := exists_equiv_of_stab φ0 hinj γ hU.2
  have hiso : ∀ a a', Di.EF (g a) (g a') = Di.EF a a' := by
    intro a a'
    have : ((Di.EF (g a) (g a') : ℤ) : ℚ) = ((Di.EF a a' : ℤ) : ℚ) := by
      rw [hEF, hEF, hg, hg, hU.1]
    exact_mod_cast this
  have hfull := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H Di l g hiso (fun a ha => by
    obtain ⟨e, he⟩ := hhalf a ha
    exact ⟨e, hinj (by rw [hg, he, map_add, map_nsmul])⟩)
  have hfin := Di.fin
  refine GlobalTheory.GamFree.gam_free GlobalTheory.latMinkowski E r q l.M Ψ Gm (LinearMap.range φ0) γ
    (fun τ => ?_) hG ?_ ?_ l.three_le hU ?_ x hx b hb hxb
  · rw [hΨ, hΨ]; exact cmType_of_rt H τ
  · rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map φ0
  · rw [LinearMap.coe_range]; exact hsp
  · rintro _ ⟨a, rfl⟩
    obtain ⟨e, he⟩ := hfull a
    exact ⟨φ0 e, LinearMap.mem_range_self φ0 e, by rw [← hg, he, map_add, map_nsmul]⟩
end GlobalTheory.PrincFree
