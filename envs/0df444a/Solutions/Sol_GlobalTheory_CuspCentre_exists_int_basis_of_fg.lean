-- Prove2me | solution 1 for GlobalTheory.CuspCentre.exists_int_basis_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:35:54.467277+00:00
-- url     : https://prove2.me/submissions/61d45abb-0d72-4f76-865e-374e1d8a959d

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SpanCuspCentreArithmeticGroupFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SkewMatrixMultipleInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankRatSkewHermitianMatricesCmFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ArithmeticGroupCuspCentreLattice

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
namespace GlobalTheory.CuspCentre
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℚ V] (Z : Submodule ℤ V)
    (hZ : Z.FG) {n : ℕ} (hn : Module.finrank ℚ (Submodule.span ℚ (Z : Set V)) = n) :
    ∃ bs : Fin n → V, LinearIndependent ℤ bs ∧ Submodule.span ℤ (Set.range bs) = Z := by
  haveI : Module.Finite ℤ Z := Module.Finite.iff_fg.2 hZ
  haveI : IsAddTorsionFree V := IsAddTorsionFree.of_module_rat V
  haveI : Module.Free ℤ Z := inferInstance
  let b := Module.finBasis ℤ Z
  have hli : LinearIndependent ℤ (Z.subtype ∘ b) :=
    b.linearIndependent.map' Z.subtype Z.ker_subtype
  have hsp : Submodule.span ℤ (Set.range (Z.subtype ∘ b)) = Z := by
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hq : LinearIndependent ℚ (Z.subtype ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have h1 := finrank_span_eq_card hq
  have h2 : Submodule.span ℚ (Set.range (Z.subtype ∘ b)) = Submodule.span ℚ (Z : Set V) := by
    conv_rhs => rw [← hsp]
    rw [Submodule.span_span_of_tower]
  rw [h2, hn, Fintype.card_fin] at h1
  subst h1
  exact ⟨_, hli, hsp⟩
end GlobalTheory.CuspCentre
