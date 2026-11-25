-- Prove2me | solution 1 for GlobalTheory.Reg.exists_covers_fam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:03:32.58289+00:00
-- url     : https://prove2.me/submissions/a449fe1c-2878-4029-bd1b-9eb720f4b8b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AdjoinRatiosOfSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_NaturalRuleValueBaseChangeOfIsReducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_SpanEvalEqTopOfNoCommonZeroReducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsRefinedCoveringChartFamily
import Theorems.Thm_GlobalTheory_Reg_PChart_exists_refine
import Theorems.Thm_GlobalTheory_T_naturalRule_value_baseChange_of_isReduced
import Theorems.Thm_GlobalTheory_T_span_eval_eq_top_of_noCommonZero_reduced


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
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory GlobalTheory.Reg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
namespace GlobalTheory.Reg
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (J : Type) [Finite J] (P : J → PChart Xo c β), Covers P → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ (J' : Type) (_ : Finite J') (P' : J' → PChart Xo c β), Covers P' ∧ ∀ j, (P' j).Fam ws := by
  intro E _ _ _ H Dw l Xo c hL O _ β J _ P hP a n m ws hws hnc
  have hw : ∀ j e (he : e ∈ (P j).es) i,
      ((evR Xo c (ws i) ((P j).y e he) : (P j).R e) : (P j).Ω) = evR Xo c (ws i) (P j).yg := fun j e he i =>
    (GlobalTheory.T.naturalRule_value_baseChange_of_isReduced E H Dw l Xo c hL a n (ws i) (hws i) _ _ _ _ _ ((P j).gen e he)).symm
  have hspan : ∀ j e (he : e ∈ (P j).es),
      Ideal.span (Set.range fun i => (evR Xo c (ws i) ((P j).y e he) : (P j).R e)) = ⊤ := fun j e he =>
    GlobalTheory.T.span_eval_eq_top_of_noCommonZero_reduced E H Dw l Xo c hL a n m ws hws hnc _ _
  have h := fun p : {p : J × Fin m // evR Xo c (ws p.2) (P p.1).yg ≠ 0} =>
    PChart.exists_refine hL (P p.1.1) ws (hw p.1.1) (hspan p.1.1) p.1.2 p.2
  choose P' hF hC using h
  refine ⟨_, inferInstance, P', ?_, hF⟩
  intro L _ _ W hW y
  obtain ⟨j, e, he, ψ, z, t, h1, hz, hb⟩ := hP L W hW y
  have hex : ∃ i, ψ (evR Xo c (ws i) ((P j).y e he)) ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hle : Ideal.span (Set.range fun i => (evR Xo c (ws i) ((P j).y e he) : (P j).R e)) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hn i
    rw [hspan j e he] at hle
    have h1 : ψ 1 = 0 := hle (Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  obtain ⟨i₀, hi₀⟩ := hex
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ
    (fun i => W.valuation (ψ (evR Xo c (ws i) ((P j).y e he)))) ⟨i₀, Finset.mem_univ _⟩
  have hk0 : ψ (evR Xo c (ws k) ((P j).y e he)) ≠ 0 := by
    intro h0
    have := hk i₀ (Finset.mem_univ _)
    simp only [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi₀ this
  have hk1 : evR Xo c (ws k) (P j).yg ≠ 0 := by
    intro h0
    rw [← hw j e he k] at h0
    apply hk0
    have h2 : (evR Xo c (ws k) ((P j).y e he) : (P j).R e) = 0 := Subtype.ext h0
    rw [h2, map_zero]
  refine ⟨⟨(j, k), hk1⟩, hC ⟨(j, k), hk1⟩ L W y e he ψ z t h1 hz hb hk0 fun i => ?_⟩
  rw [← W.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hk i (Finset.mem_univ _)) zero_le'
end GlobalTheory.Reg
