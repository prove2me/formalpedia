-- Prove2me | solution 1 for GlobalTheory.ShortLawsCompare.isBeta_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:30.948209+00:00
-- url     : https://prove2.me/submissions/5c16f8b3-ea77-46a3-a0c9-56f3d7b364ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm

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
theorem _root_.solution {n : ℕ} {Λ : _root_.Formalism.L2.Pj.GenLat E n} {β ζ : c.F}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta Dw c Λ β) (hζ : IsOfFinOrder ζ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta Dw c Λ (ζ * β) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.IsBeta _root_.Formalism.L2.Pj.BetaIs _root_.Formalism.L2.Pj.BetaAbs at h ⊢
  obtain ⟨hβ, hspan, hnorm⟩ := h
  obtain ⟨k, hk, hζk⟩ := isOfFinOrder_iff_pow_eq_one.mp hζ
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hζk
    exact zero_ne_one hζk
  have hint : IsIntegral ℤ ζ := IsIntegral.of_pow hk (by rw [hζk]; exact isIntegral_one)
  have hint' : IsIntegral ℤ ζ⁻¹ :=
    IsIntegral.of_pow hk (by rw [inv_pow, hζk, inv_one]; exact isIntegral_one)
  have hsp : (𝓞 c.F ∙ (ζ * β)) = 𝓞 c.F ∙ β := by
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨⟨ζ, hint⟩, rfl⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      refine ⟨⟨ζ⁻¹, hint'⟩, ?_⟩
      change ζ⁻¹ * (ζ * β) = β
      rw [← _root_.mul_assoc, inv_mul_cancel₀ hζ0, _root_.one_mul]
  refine ⟨mul_ne_zero hζ0 hβ, by rw [hsp]; exact hspan, fun σ => ?_⟩
  have hσ : ‖σ ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζk, map_one]) hk.ne'
  rw [map_mul, norm_mul, hσ, _root_.one_mul]
  exact hnorm σ
end _root_.GlobalTheory.ShortLawsCompare
end GlobalTheory.ShortLawsCompare
