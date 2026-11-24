-- Prove2me | solution 1 for GlobalTheory.DerLin.le_of_fst_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:34:14.674339+00:00
-- url     : https://prove2.me/submissions/e12c2ede-fc41-479b-b20e-1d24437c5989

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExponentialDerivativeAtZeroIsTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DerivativeAlongTangentCombinationModuliStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsCombAtIffIsDerivAt0
import Theorems.Thm_GlobalTheory_DerLin_surj_fst

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
open GlobalTheory GlobalTheory.DerLin
namespace GlobalTheory.DerLin
theorem _root_.solution {S : Type} [CommRing S] {X : Scheme.{0}} {v v' : Sp (DualNumber S) ⟶ X}
    (hh : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v')
    {U : X.Opens} (h : ⊤ ≤ v' ⁻¹ᵁ U) : ⊤ ≤ v ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := surj_fst S p
  have h1 := h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom S S S).toRingHom : Sp S ⟶ Sp (DualNumber S)) q))
  change v' _ ∈ U at h1
  change v _ ∈ U
  rw [← Scheme.Hom.comp_apply] at h1 ⊢
  rw [hh]; exact h1
end GlobalTheory.DerLin
