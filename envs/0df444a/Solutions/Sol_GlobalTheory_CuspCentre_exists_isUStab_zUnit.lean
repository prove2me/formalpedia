-- Prove2me | solution 1 for GlobalTheory.CuspCentre.exists_isUStab_zUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:42:52.524585+00:00
-- url     : https://prove2.me/submissions/26962399-2604-433f-b9db-2a02e0993022

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
import Theorems.Thm_GlobalTheory_CuspCentre_exists_pos_nsmul_mulVec_mem
import Theorems.Thm_GlobalTheory_CuspCentre_zMatE_nsmul_mulVec
import Theorems.Thm_GlobalTheory_CuspCentre_isSkew_nsmul
import Theorems.Thm_GlobalTheory_CuspCentre_zMatE_unitary


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
theorem _root_.solution (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E)
    (hβ : FJ.IsSkew β) : ∃ d : ℕ, 0 < d ∧ ∀ j : ℕ, IsUStab X.Gm X.Λ (zUnit X cu ((j * d) • β)) := by
  obtain ⟨d, hd, h⟩ := exists_pos_nsmul_mulVec_mem X (FJ.zMatE X cu.e β - 1)
  obtain ⟨d', hd', h'⟩ := exists_pos_nsmul_mulVec_mem X (FJ.zMatE X cu.e (-β) - 1)
  refine ⟨d * d', mul_pos hd hd', fun j => ⟨zMatE_unitary X cu _ (isSkew_nsmul hβ _), fun x => ?_⟩⟩
  show x ∈ X.Λ ↔ FJ.zMatE X cu.e ((j * (d * d')) • β) *ᵥ x ∈ X.Λ
  constructor
  · intro hx
    rw [zMatE_nsmul_mulVec, mul_comm d, ← mul_assoc, mul_smul]
    exact X.Λ.add_mem hx (nsmul_mem (h x hx) _)
  · intro hx
    have h1 : FJ.zMatE X cu.e ((j * (d * d')) • -β) *ᵥ (FJ.zMatE X cu.e ((j * (d * d')) • β) *ᵥ x)
        ∈ X.Λ := by
      rw [zMatE_nsmul_mulVec X cu.e (-β), ← mul_assoc, mul_smul (j * d) d' (_ *ᵥ _)]
      rw [← mul_assoc] at hx
      exact X.Λ.add_mem hx (nsmul_mem (h' _ hx) _)
    rwa [Matrix.mulVec_mulVec, ← zMatE_add, smul_neg, neg_add_cancel, zMatE_zero,
      Matrix.one_mulVec] at h1
end GlobalTheory.CuspCentre
