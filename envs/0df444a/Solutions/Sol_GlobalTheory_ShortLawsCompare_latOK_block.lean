-- Prove2me | solution 1 for GlobalTheory.ShortLawsCompare.latOK_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:40:55.165351+00:00
-- url     : https://prove2.me/submissions/6a2fb886-e8bb-4dcf-b456-8ebb69eba03a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Theorems.Thm_GlobalTheory_ShortLawsCompare_mem_std_block
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_BlockProductLattices_mem_blockLat

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
private theorem smul_inf_comap_funLeft_le (I : Ideal (𝓞 E)) (L₁ P₁ : Submodule (𝓞 E) (Fin n₁ → E))
    (L₂ P₂ : Submodule (𝓞 E) (Fin n₂ → E)) (h₁ : I • L₁ ≤ P₁) (h₂ : I • L₂ ≤ P₂) :
    I • (L₁.comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
        L₂.comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁))) ≤
      P₁.comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
        P₂.comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁)) := by
  rw [Submodule.smul_le]
  intro r hr v hv
  rw [Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_comap] at hv ⊢
  refine ⟨?_, ?_⟩
  · rw [map_smul]
    exact h₁ (Submodule.smul_mem_smul hr hv.1)
  · rw [map_smul]
    exact h₂ (Submodule.smul_mem_smul hr hv.2)
set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] in
variable {n₁ n₂ : ℕ} in
private theorem stdLat_add_eq_inf_comap_funLeft :
    _root_.Formalism.L2.Pj.stdLat E (n₁ + n₂) =
      (_root_.Formalism.L2.Pj.stdLat E n₁).comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
        (_root_.Formalism.L2.Pj.stdLat E n₂).comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁)) := by
  ext v
  exact _root_.GlobalTheory.ShortLawsCompare.mem_std_block v
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
set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] in
variable {n₁ n₂ : ℕ} in
private theorem blockLat_unimod [IsCMField E] {Λ₁ : _root_.Formalism.L2.Pj.GenLat E n₁}
    {Λ₂ : _root_.Formalism.L2.Pj.GenLat E n₂} (h₁ : Λ₁.Unimod) (h₂ : Λ₂.Unimod) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.blockLat Λ₁ Λ₂).Unimod := by
  unfold _root_.Formalism.L2.Pj.GenLat.Unimod at *
  intro v
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.mem_blockLat, Fin.sum_univ_add]
  constructor
  · rintro ⟨hv₁, hv₂⟩ w ⟨hw₁, hw₂⟩
    exact add_mem ((h₁ _).1 hv₁ _ hw₁) ((h₂ _).1 hv₂ _ hw₂)
  · intro h
    refine ⟨(h₁ _).2 fun w₁ hw₁ => ?_, (h₂ _).2 fun w₂ hw₂ => ?_⟩
    · have hz : (fun j => (0 : Fin n₂ → E) j) ∈ Λ₂.La := Λ₂.La.zero_mem
      have := h (Fin.append w₁ 0) ⟨by simpa using hw₁, by simpa using hz⟩
      simpa using this
    · have hz : (fun j => (0 : Fin n₁ → E) j) ∈ Λ₁.La := Λ₁.La.zero_mem
      have := h (Fin.append 0 w₂) ⟨by simpa using hz, by simpa using hw₂⟩
      simpa using this
set_option autoImplicit false in
open NumberField MvPolynomial in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {E : Type} [Field E] [NumberField E] in
variable {n₁ n₂ : ℕ} in
private theorem blockLat_trivAt {Λ₁ : _root_.Formalism.L2.Pj.GenLat E n₁} {Λ₂ : _root_.Formalism.L2.Pj.GenLat E n₂} {b : ℕ}
    (h₁ : Λ₁.TrivAt b) (h₂ : Λ₂.TrivAt b) : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.blockLat Λ₁ Λ₂).TrivAt b := by
  unfold _root_.Formalism.L2.Pj.GenLat.TrivAt at *
  obtain ⟨k₁, hk₁, a₁, b₁⟩ := h₁
  obtain ⟨k₂, hk₂, a₂, b₂⟩ := h₂
  have hle₁ : Ideal.span {((k₁ * k₂ : ℕ) : 𝓞 E)} ≤ Ideal.span {((k₁ : ℕ) : 𝓞 E)} :=
    Ideal.span_singleton_le_span_singleton.mpr ⟨(k₂ : 𝓞 E), by push_cast; ring⟩
  have hle₂ : Ideal.span {((k₁ * k₂ : ℕ) : 𝓞 E)} ≤ Ideal.span {((k₂ : ℕ) : 𝓞 E)} :=
    Ideal.span_singleton_le_span_singleton.mpr ⟨(k₁ : 𝓞 E), by push_cast; ring⟩
  refine ⟨k₁ * k₂, Nat.Coprime.mul hk₁ hk₂, ?_, ?_⟩
  · rw [stdLat_add_eq_inf_comap_funLeft]
    exact smul_inf_comap_funLeft_le _ _ _ _ _ ((Submodule.smul_mono_left hle₁).trans a₁)
      ((Submodule.smul_mono_left hle₂).trans a₂)
  · rw [stdLat_add_eq_inf_comap_funLeft]
    exact smul_inf_comap_funLeft_le _ _ _ _ _ ((Submodule.smul_mono_left hle₁).trans b₁)
      ((Submodule.smul_mono_left hle₂).trans b₂)
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n₁ n₂ : ℕ}
set_option autoImplicit false
open NumberField MvPolynomial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
variable (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) {n₁ n₂ : ℕ}
namespace GlobalTheory.ShortLawsCompare
namespace _root_.GlobalTheory.ShortLawsCompare
theorem _root_.solution {bad : ℕ} {Λ₁ : _root_.Formalism.L2.Pj.GenLat E n₁} {Λ₂ : _root_.Formalism.L2.Pj.GenLat E n₂}
    (h₁ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.LatOK bad l.M Λ₁)
    (h₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.LatOK bad l.M Λ₂) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.LatOK bad l.M (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.blockLat Λ₁ Λ₂) :=
  ⟨blockLat_unimod h₁.1 h₂.1, blockLat_trivAt h₁.2.1 h₂.2.1,
    blockLat_trivAt h₁.2.2 h₂.2.2⟩
end _root_.GlobalTheory.ShortLawsCompare
end GlobalTheory.ShortLawsCompare
