-- Prove2me | solution 1 for GlobalTheory.FrameUnif.princ_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:22:59.820292+00:00
-- url     : https://prove2.me/submissions/6f811636-ee11-4935-97ba-72d47f58bd55

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CongruenceFiniteIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_PrincipalLevelGroupFiniteIndexUnitaryStabiliser
import Theorems.Thm_GlobalTheory_CongruenceIndex_exists_finset_cosets


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
open GlobalTheory GlobalTheory.FrameUnif
namespace GlobalTheory.FrameUnif
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab Gm (LinearMap.range φ0) γ → ∃ s ∈ S, s⁻¹ * γ ∈ princ l Gm Di φ0 := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 _ _
  haveI := Di.fin
  have hΛ : (LinearMap.range φ0).FG := by
    rw [← Submodule.map_top]
    exact Submodule.FG.map φ0 Module.Finite.fg_top
  have hM : 0 < l.M * l.A := Nat.mul_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos
  obtain ⟨S, hS⟩ := GlobalTheory.CongruenceIndex.exists_finset_cosets (Gm := Gm) hΛ hM
  refine ⟨S, fun γ hγ => ?_⟩
  obtain ⟨s, hs, hst, hc⟩ := hS γ hγ
  refine ⟨s, hs, hst, fun a _ => ?_, fun a => ?_⟩
  · obtain ⟨w, ⟨b, rfl⟩, e⟩ := hc _ (LinearMap.mem_range_self φ0 a)
    exact ⟨l.A • b, by rw [e, map_nsmul, mul_smul]⟩
  · obtain ⟨w, ⟨b, rfl⟩, e⟩ := hc _ (LinearMap.mem_range_self φ0 a)
    exact ⟨l.M • b, by rw [e, map_nsmul, mul_comm, mul_smul]⟩
end GlobalTheory.FrameUnif
