-- Prove2me | solution 1 for GlobalTheory.Reg.span_evR_eq_top_of_noCommonZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:55:12.101798+00:00
-- url     : https://prove2.me/submissions/c60ae06a-0264-4da8-9505-f65f3884c582

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_NaturalRuleValueBaseChangeOfIsReducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_SpanEvalEqTopOfNoCommonZeroReduced
import Theorems.Thm_Formalism_L2_Pj_OverLa_bc
import Theorems.Thm_GlobalTheory_T_naturalRule_value_baseChange_of_isReduced


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.Reg
namespace GlobalTheory.Reg
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S), Ideal.span (Set.range fun i => evR Xo c (ws i) y) = ⊤ := by
  intro E _ _ _ H Dw l Xo c hL a n m ws hws hnz S _ _ _ y
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  letI : Field (S ⧸ M) := Ideal.Quotient.field M
  let T : Type := AlgebraicClosure (S ⧸ M)
  let φ : S →ₐ[c.F] T := (IsScalarTower.toAlgHom c.F (S ⧸ M) T).comp (Ideal.Quotient.mkₐ c.F M)
  obtain ⟨z, hz⟩ := hL.bc S T φ y
  obtain ⟨i, hi⟩ := hnz T z
  apply hi
  rw [GlobalTheory.T.naturalRule_value_baseChange_of_isReduced E H Dw l Xo c hL a n (ws i) (hws i) S T φ y z hz]
  have hm : evR Xo c (ws i) y ∈ M := hle (Ideal.subset_span ⟨i, rfl⟩)
  have h0 : Ideal.Quotient.mkₐ c.F M (evR Xo c (ws i) y) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
  show (IsScalarTower.toAlgHom c.F (S ⧸ M) T) (Ideal.Quotient.mkₐ c.F M (evR Xo c (ws i) y)) = 0
  rw [h0, map_zero]
end GlobalTheory.Reg
