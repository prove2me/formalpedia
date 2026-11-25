-- Prove2me | solution 1 for GlobalTheory.ShortLawsCompare.isBeta_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:04.556464+00:00
-- url     : https://prove2.me/submissions/ca6a815d-dbf4-45f7-85bd-eedc36667de0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Theorems.Thm_GlobalTheory_ShortLawsCompare_isUnit_idealAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ShortLawsCompare
open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l)
set_option autoImplicit false
open NumberField MvPolynomial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
variable (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l)
namespace GlobalTheory.ShortLawsCompare
namespace _root_.GlobalTheory.ShortLawsCompare
theorem _root_.solution {n : ℕ} {Λ : _root_.Formalism.L2.Pj.GenLat E n} (hU : Λ.Unimod)
    (hT : Λ.TrivAt l.M) {β β' : c.F}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta Dw c Λ β) (h' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta Dw c Λ β') :
    ∃ ζ : c.F, IsOfFinOrder ζ ∧ β' = ζ * β := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta _root_.Formalism.L2.Pj.BetaIs _root_.Formalism.L2.Pj.BetaAbs at h h'
  obtain ⟨hβ, hs, hn⟩ := h
  obtain ⟨-, hs', hn'⟩ := h'
  have hP : IsUnit (∏ τ, _root_.Formalism.L2.Pj.idealAt c Λ.La τ ^ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult Dw τ) := by
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun τ _ => ?_)
    have h3 := l.three_le
    exact (_root_.GlobalTheory.ShortLawsCompare.isUnit_idealAt c hT hU (by omega) τ).pow _
  have heq : (𝓞 c.F ∙ β) = 𝓞 c.F ∙ β' := hP.mul_right_cancel (hs.trans hs'.symm)
  obtain ⟨u, hu⟩ := Submodule.span_singleton_eq_span_singleton.mp heq
  have hβ'eq : β' = ((u : 𝓞 c.F) : c.F) * β := by
    rw [← hu]
    rfl
  refine ⟨((u : 𝓞 c.F) : c.F), ?_, hβ'eq⟩
  have htors : u ∈ NumberField.Units.torsion c.F := by
    rw [NumberField.Units.mem_torsion]
    intro w
    rw [← w.mk_embedding, NumberField.InfinitePlace.apply]
    have h1 := hn w.embedding
    have h2 := hn' w.embedding
    have hne : ‖w.embedding β‖ ≠ 0 := by simpa using hβ
    have hsq : ‖w.embedding ((u : 𝓞 c.F) : c.F)‖ ^ 2 * ‖w.embedding β‖ ^ 2 =
        1 * ‖w.embedding β‖ ^ 2 := by
      rw [_root_.one_mul, ← _root_.mul_pow, ← norm_mul, ← map_mul, ← hβ'eq, h2, h1]
    have hsq' := mul_right_cancel₀ (pow_ne_zero 2 hne) hsq
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq'
  obtain ⟨m, hm, hum⟩ := isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion _).mp htors)
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, ?_⟩
  have := congrArg (fun x : (𝓞 c.F)ˣ => ((x : 𝓞 c.F) : c.F)) hum
  simpa using this
end _root_.GlobalTheory.ShortLawsCompare
end GlobalTheory.ShortLawsCompare
