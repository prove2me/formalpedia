-- Prove2me | solution 1 for GlobalTheory.ShortLawsCompare.unimod_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:31.697615+00:00
-- url     : https://prove2.me/submissions/24ef6dcf-a981-4ae8-924f-77679961efdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Theorems.Thm_GlobalTheory_BetaEx_mem_std

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ShortLawsCompare
open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke
section Lattice
variable {E : Type} [Field E] [NumberField E]
variable {n₁ n₂ : ℕ}
set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] in
variable {n₁ n₂ : ℕ} in
private theorem complexConj_coe_mem_range_algebraMap [IsCMField E] (a : 𝓞 E) :
    IsCMField.complexConj E (a : E) ∈ (algebraMap (𝓞 E) E).range :=
  ⟨RingOfIntegers.mapRingHom (IsCMField.complexConj E : E →+* E) a, rfl⟩
end Lattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
section Beta
variable (c : Coeff l)
end Beta
section Level
variable {Xo : Moduli Dw l} {c : Coeff l}
end Level
section Objects
variable (c : Coeff l) {n₁ n₂ : ℕ}
end Objects
variable (Xo : Moduli Dw l) (c : Coeff l)
variable [StarRing (𝓞 E)] {Xo c} {nab : NabV Xo c}
end GlobalTheory.ShortLawsCompare
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ShortLawsCompare
open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke
variable {E : Type} [Field E] [NumberField E]
variable {n₁ n₂ : ℕ}
set_option autoImplicit false
open NumberField MvPolynomial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {E : Type} [Field E] [NumberField E]
variable {n₁ n₂ : ℕ}
namespace GlobalTheory.ShortLawsCompare
namespace _root_.GlobalTheory.ShortLawsCompare
theorem _root_.solution [IsCMField E] (n : ℕ) :
    _root_.Formalism.L2.Pj.GenLat.Unimod (⟨_root_.Formalism.L2.Pj.stdLat E n⟩ : _root_.Formalism.L2.Pj.GenLat E n) := by
  unfold _root_.Formalism.L2.Pj.GenLat.Unimod
  intro v
  show v ∈ _root_.Formalism.L2.Pj.stdLat E n ↔ ∀ w ∈ _root_.Formalism.L2.Pj.stdLat E n, _
  constructor
  · intro hv w hw
    rw [_root_.GlobalTheory.BetaEx.mem_std] at hv hw
    refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ?_
    · obtain ⟨a, ha⟩ := hv j
      rw [← ha]
      exact complexConj_coe_mem_range_algebraMap a
    · obtain ⟨b, hb⟩ := hw j
      exact ⟨b, hb⟩
  · intro h
    rw [_root_.GlobalTheory.BetaEx.mem_std]
    intro j
    have hsingle : (Pi.single j 1 : Fin n → E) ∈ _root_.Formalism.L2.Pj.stdLat E n := by
      rw [_root_.GlobalTheory.BetaEx.mem_std]
      intro i
      refine ⟨if i = j then 1 else 0, ?_⟩
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hc := h _ hsingle
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at hc
    obtain ⟨b, hb⟩ := hc
    obtain ⟨a, ha⟩ := complexConj_coe_mem_range_algebraMap b
    refine ⟨a, ?_⟩
    change (algebraMap (𝓞 E) E) a = v j
    rw [ha]
    change IsCMField.complexConj E ((algebraMap (𝓞 E) E) b) = v j
    rw [hb, _root_.mul_one, IsCMField.complexConj_apply_apply]
end _root_.GlobalTheory.ShortLawsCompare
end GlobalTheory.ShortLawsCompare
