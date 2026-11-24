-- Prove2me | solution 1 for GlobalTheory.CuspCentre.exists_nsmul_mem_zGam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:59:57.338069+00:00
-- url     : https://prove2.me/submissions/d2291eb8-09f5-4e19-be4e-2e08fe4774b7

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZMatEInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SkewMatrixMultipleInLattice
import Theorems.Thm_GlobalTheory_CuspCentre_isSkew_nsmul
import Theorems.Thm_GlobalTheory_CuspCentre_zUnit_add
import Theorems.Thm_GlobalTheory_CuspCentre_exists_isUStab_zUnit

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
open GlobalTheory GlobalTheory.CuspCentre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace GlobalTheory.CuspCentre
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), FJ.IsSkew β → ∃ n : ℕ, 0 < n ∧ n • β ∈ FJ.zGam X cu := by
  intro E _ _ _ r ρ X cu β hβ
  obtain ⟨d, hd, h⟩ := exists_isUStab_zUnit X cu β hβ
  obtain ⟨S, hS⟩ := X.Γ_index
  choose s hsS hs using fun j => hS _ (h j)
  have key : ∀ i j, i < j → s i = s j → ∃ n : ℕ, 0 < n ∧ n • β ∈ FJ.zGam X cu := by
    intro i j hij e
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
    refine ⟨(k + 1) * d, mul_pos k.succ_pos hd, isSkew_nsmul hβ _,
      zUnit X cu (((k + 1) * d) • β), ?_, rfl⟩
    have h1 := X.Γ.mul_mem (X.Γ.inv_mem (hs i)) (hs (i + k + 1))
    rw [← e, add_assoc, add_mul, add_smul, zUnit_add, ← mul_assoc (s i)⁻¹, inv_mul_cancel_left] at h1
    exact h1
  obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite (fun j => (⟨s j, hsS j⟩ : S))
  have e' : s i = s j := congrArg Subtype.val e
  rcases lt_or_gt_of_ne hij with h1 | h1
  · exact key i j h1 e'
  · exact key j i h1 e'.symm
end GlobalTheory.CuspCentre
