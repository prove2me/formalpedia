-- Prove2me | solution 1 for GlobalTheory.ShortLawsCompare.levOK_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:10:39.434583+00:00
-- url     : https://prove2.me/submissions/cc1f8c87-095d-49c6-8b16-77ad34c557a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Theorems.Thm_GlobalTheory_ShortLawsCompare_mem_std_block
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
theorem _root_.solution {Λ₁ : _root_.Formalism.L2.Pj.GenLat E n₁} {Λ₂ : _root_.Formalism.L2.Pj.GenLat E n₂} {N M : ℕ}
    (h₁ : Λ₁.LevOK N M) (h₂ : Λ₂.LevOK N M) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.blockLat Λ₁ Λ₂).LevOK N M := by
  unfold _root_.Formalism.L2.Pj.GenLat.LevOK _root_.Formalism.L2.Pj.GenLat.Ln at *
  refine ⟨h₁.1, h₁.2.1, ?_⟩
  have key := smul_inf_comap_funLeft_le (Ideal.span {((N : ℕ) : 𝓞 E)}) _ _ _ _ h₁.2.2 h₂.2.2
  rw [stdLat_add_eq_inf_comap_funLeft]
  refine key.trans ?_
  intro v hv
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices.blockLat, Submodule.mem_inf, Submodule.mem_comap] at hv ⊢
  tauto
end _root_.GlobalTheory.ShortLawsCompare
end GlobalTheory.ShortLawsCompare
