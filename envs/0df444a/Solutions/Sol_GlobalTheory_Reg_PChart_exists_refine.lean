-- Prove2me | solution 1 for GlobalTheory.Reg.PChart.exists_refine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:32:44.545866+00:00
-- url     : https://prove2.me/submissions/6b70fb4e-76cc-48c1-8d38-b5162b89edf6

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
import Theorems.Thm_GlobalTheory_Reg_adjoin_insert_union_image
import Theorems.Thm_Formalism_L2_Pj_OverLa_bc
import Theorems.Thm_Formalism_L2_Pj_frMap_cancel
import Theorems.Thm_Formalism_L2_Pj_frMap_trans
import Theorems.Thm_GlobalTheory_adjoin_ratios_of_span_eq_top
import Theorems.Thm_P2M_Formalism_L2_PjFree_regular__int_f20b464cd2c4


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
set_option maxHeartbeats 800000
namespace GlobalTheory.Reg
namespace PChart
theorem _root_.solution (hL : EvLaws Xo c) {O : Type} [CommRing O] {β : O →+* c.F} (P : PChart Xo c β)
    {m : ℕ} (ws : Fin m → Rul Xo c)
    (hw : ∀ e (he : e ∈ P.es) i, ((evR Xo c (ws i) (P.y e he) : P.R e) : P.Ω) = evR Xo c (ws i) P.yg)
    (hspan : ∀ e (he : e ∈ P.es), Ideal.span (Set.range fun i => (evR Xo c (ws i) (P.y e he) : P.R e)) = ⊤)
    (k : Fin m) (hk : evR Xo c (ws k) P.yg ≠ 0) :
    ∃ P' : PChart Xo c β, P'.Fam ws ∧
      ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L) (y : FrPt Xo c L)
        (e : P.Ω) (he : e ∈ P.es) (ψ : P.R e →ₐ[c.F] L) (z : FrPt Xo c L) (t : Ix Dw → Lˣ),
        (∀ g : P.R e, (g : P.Ω) ∈ P.gens → ψ g ∈ W) → FrMap ψ (P.y e he) z → FrBor t y z →
        ψ (evR Xo c (ws k) (P.y e he)) ≠ 0 →
        (∀ i, ψ (evR Xo c (ws i) (P.y e he)) / ψ (evR Xo c (ws k) (P.y e he)) ∈ W) → P'.Catches W y := by
  classical
  let G : Finset P.Ω := P.gens ∪ Finset.univ.image fun i => evR Xo c (ws i) P.yg / evR Xo c (ws k) P.yg
  have hG : (P.gens : Set P.Ω) ⊆ G := fun g hg => Finset.mem_coe.2 (Finset.mem_union_left _ hg)
  have hGr : ∀ i, evR Xo c (ws i) P.yg / evR Xo c (ws k) P.yg ∈ G := fun i =>
    Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  have hblow := fun e (he : e ∈ P.es) =>
    GlobalTheory.adjoin_ratios_of_span_eq_top c.F P.Ω (P.R e) m (fun i => evR Xo c (ws i) (P.y e he)) k (hspan e he)
      (by rw [hw e he k]; exact hk) (Algebra.adjoin c.F (insert e⁻¹ (G : Set P.Ω)))
      (by simp only [hw e he]; exact adjoin_insert_union_image _ _ _)
  choose hle hinv hsm hext using hblow
  have hy := fun e (he : e ∈ P.es) => hL.bc _ _ (Subalgebra.inclusion (hle e he)) (P.y e he)
  choose y' hy' using hy
  refine ⟨{ Ω := P.Ω
            gens := G
            frac := ?_
            es := P.es
            es_ne := P.es_ne
            es_mem := fun e he => ⟨(P.es_mem e he).1, ?_⟩
            sm := fun e he => hsm e he (P.sm e he)
            yg := P.yg
            y := y'
            gen := fun e he => frMap_cancel _ _ _ (Subalgebra.inclusion (hle e he)) _ (P.y e he) _ _ (hy' e he)
              (P.gen e he)
            int := ?_ }, ⟨k, hk, fun i => ?_, fun e he => ?_⟩, ?_⟩
  · rw [eq_top_iff, ← P.frac]
    exact Subfield.closure_mono (Set.union_subset_union_right _ hG)
  · exact Subring.closure_mono (Set.union_subset_union_right _ hG) (P.es_mem e he).2
  · intro e he T io
    letI := io.toAlgebra
    intro ψ h1 h2 z hz
    refine P.int e he T io (ψ.comp (Subalgebra.inclusion (hle e he))) h1 (fun g hg => ?_) z
      (frMap_trans _ _ _ _ _ _ _ _ (hy' e he) hz)
    exact h2 (Subalgebra.inclusion (hle e he) g) (hG hg)
  · exact Subring.subset_closure (Or.inr (hGr i))
  · have := hinv e he
    rw [hw e he k] at this
    exact this
  · intro L _ _ W y e he ψ z t h1 hz hb hψ hW
    obtain ⟨ψ', hc, hr⟩ := hext e he L ψ hψ
    refine ⟨e, he, ψ', z, t, fun g hg => ?_, ?_, hb⟩
    · rcases Finset.mem_union.1 hg with h | h
      · have e1 : g = Subalgebra.inclusion (hle e he) ⟨g, Algebra.subset_adjoin (Or.inr h)⟩ := Subtype.ext rfl
        have e2 := h1 ⟨g, Algebra.subset_adjoin (Or.inr h)⟩ h
        have e3 := DFunLike.congr_fun hc ⟨g, Algebra.subset_adjoin (Or.inr h)⟩
        rw [AlgHom.comp_apply] at e3
        have e4 := (congrArg ψ' e1).trans e3
        exact e4.symm ▸ e2
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
        rw [← hw e he i, ← hw e he k] at hi
        have e1 := hr i (hi.symm ▸ g.2)
        have e2 : g = ⟨_, hi.symm ▸ g.2⟩ := Subtype.ext hi.symm
        have e4 := (congrArg ψ' e2).trans e1
        exact e4.symm ▸ hW i
    · refine frMap_cancel _ _ _ (Subalgebra.inclusion (hle e he)) ψ' (P.y e he) _ _ (hy' e he) ?_
      exact hc.symm ▸ hz
end PChart
end GlobalTheory.Reg
