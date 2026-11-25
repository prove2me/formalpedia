-- Prove2me | solution 1 for GlobalTheory.ShortLawsCompare.isUnit_idealAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:42.396338+00:00
-- url     : https://prove2.me/submissions/ce1b935d-dd9a-4beb-a93b-35cf9d954e2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Theorems.Thm_GlobalTheory_BetaEx_bdd_of_unimod
import Theorems.Thm_GlobalTheory_BetaEx_frac_of_bdd
import Theorems.Thm_GlobalTheory_BetaEx_mem_detSet
import Theorems.Thm_GlobalTheory_BetaEx_mem_std
import Theorems.Thm_GlobalTheory_BetaEx_span_image_span


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
theorem _root_.solution {n b : ℕ} {Λ : _root_.Formalism.L2.Pj.GenLat E n}
    (hT : Λ.TrivAt b) (hU : Λ.Unimod) (hb : b ≠ 1) (τ : E →+* ℂ) :
    IsUnit (_root_.Formalism.L2.Pj.idealAt c Λ.La τ) := by
  unfold _root_.Formalism.L2.Pj.idealAt
  obtain ⟨k, hk, -, hkstd⟩ := hT
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hb (Nat.coprime_zero_left _ |>.mp hk)
  have hfrac := _root_.GlobalTheory.BetaEx.frac_of_bdd
    (_root_.GlobalTheory.BetaEx.bdd_of_unimod Λ hU)
  obtain ⟨s, hs⟩ := FractionalIdeal.fg_of_isNoetherianRing le_rfl
    (⟨_, hfrac⟩ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
  have hspan : Submodule.span (𝓞 c.F) (_root_.Formalism.L2.Pj.embF c τ '' _root_.Formalism.L2.Pj.detSet Λ.La) =
      Submodule.span (𝓞 c.F) (_root_.Formalism.L2.Pj.embF c τ '' (s : Set E)) := by
    rw [← _root_.GlobalTheory.BetaEx.span_image_span (_root_.Formalism.L2.Pj.embF c τ) (_root_.Formalism.L2.Pj.detSet Λ.La),
      ← _root_.GlobalTheory.BetaEx.span_image_span (_root_.Formalism.L2.Pj.embF c τ) (s : Set E)]
    congr 2
    rw [hs]
    rfl
  have hfg : (Submodule.span (𝓞 c.F) (_root_.Formalism.L2.Pj.embF c τ '' _root_.Formalism.L2.Pj.detSet Λ.La)).FG := by
    rw [hspan]
    exact Submodule.fg_span (s.finite_toSet.image _)
  let J : FractionalIdeal (nonZeroDivisors (𝓞 c.F)) c.F :=
    ⟨_, FractionalIdeal.isFractional_of_fg hfg⟩
  have hdet : ((k : E) ^ n) ∈ _root_.Formalism.L2.Pj.detSet Λ.La := by
    rw [_root_.GlobalTheory.BetaEx.mem_detSet]
    refine ⟨(k : E) • (1 : Matrix (Fin n) (Fin n) E), fun i => ?_, by simp [Matrix.det_smul]⟩
    have hrow : ((k : E) • (1 : Matrix (Fin n) (Fin n) E)) i =
        ((k : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) E) i := by
      ext j
      simp [Algebra.smul_def]
    rw [hrow]
    apply hkstd
    refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ?_
    rw [_root_.GlobalTheory.BetaEx.mem_std]
    intro j
    refine ⟨if i = j then 1 else 0, ?_⟩
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hJ : J ≠ 0 := by
    intro h0
    have hbot : (J : Submodule (𝓞 c.F) c.F) = ⊥ := by
      rw [h0]
      exact FractionalIdeal.coe_zero
    have hmem : _root_.Formalism.L2.Pj.embF c τ ((k : E) ^ n) ∈ (J : Submodule (𝓞 c.F) c.F) :=
      Submodule.subset_span ⟨_, hdet, rfl⟩
    rw [hbot, Submodule.mem_bot, map_eq_zero] at hmem
    exact pow_ne_zero n (Nat.cast_ne_zero.mpr hk0) hmem
  refine isUnit_iff_exists_inv.mpr
    ⟨((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 c.F)) c.F) : Submodule (𝓞 c.F) c.F), ?_⟩
  change (J : Submodule (𝓞 c.F) c.F) * _ = 1
  rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one]
end _root_.GlobalTheory.ShortLawsCompare
end GlobalTheory.ShortLawsCompare
