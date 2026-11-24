-- Prove2me | solution 1 for GlobalTheory.SymShape.sym_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:33:58.706879+00:00
-- url     : https://prove2.me/submissions/a0d04886-d4df-4694-a66a-cb820a181026

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GenericLevelOfFrameBlockAndCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SymmetricPositionLevelShapeOnParabolic
import Theorems.Thm_GlobalTheory_SymShape_block_mul_embX
import Theorems.Thm_GlobalTheory_SymShape_simpleSum_embX
import Theorems.Thm_GlobalTheory_GenericShape_superSum_one
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val
import Theorems.Thm_P2M_GlobalTheory_RootEx_Radical_toBlocks___of_mem_fe0d9551bf6c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.SymShape
namespace GlobalTheory.SymShape
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin l)), IsSymLevel ψ ϖ ρ P → ((∀ u ∈ N k (Fin κ) l 1, ∀ γ : GL (Fin κ) k, u * embX l γ ∈ P.J → ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧ (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb → IsUpperUnip Fin.val gb.val → ∃ hm : embX l γ ∈ P.J, (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧ ∀ u ∈ N k (Fin κ) l 1, ∀ hm : u ∈ P.J, (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u)) := by
  intro k _ _ _ _ ψ ϖ ρ κ l P hP
  refine ⟨?_, ?_, ?_⟩
  · intro u hu γ hm
    obtain ⟨u', hu', γ', hγ', g₀, hg₀, hr₀⟩ := (hP.1 _).1 hm
    have key : ∀ {F : Type} [Field F] (f : 𝒪[k] →+* F) (x : GL (Fin κ ⊕ Fin l) F) (y : GL (Fin κ) F),
        Matrix.GeneralLinearGroup.map f g₀ = x → x.val.toBlocks₁₁ = y.val →
          (g₀.val.toBlocks₁₁).map f = y.val := by
      intro F _ f x y h1 h2
      rw [← h2, ← h1]
      rfl
    have hBk := key (algebraMap 𝒪[k] k) _ γ hg₀ (block_mul_embX hu γ)
    have hBr := key (IsLocalRing.residue 𝒪[k]) _ γ' hr₀ (block_mul_embX hu' γ')
    have hdet : IsUnit (g₀.val.toBlocks₁₁).det := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
      change ((g₀.val.toBlocks₁₁).map (IsLocalRing.residue 𝒪[k])).det ≠ 0
      rw [hBr]
      exact (Matrix.isUnits_det_units γ').ne_zero
    refine ⟨γ', ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_, ?_⟩, hγ'⟩
    · exact Units.ext (by rw [← hBk]; rfl)
    · exact Units.ext (by rw [← hBr]; rfl)
  · intro γ gb hred hgb
    obtain ⟨γ₀, h1, h2⟩ := hred
    let g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k] :=
      ⟨Matrix.fromBlocks γ₀.val 0 0 1, Matrix.fromBlocks (γ₀⁻¹).val 0 0 1,
        by rw [Matrix.fromBlocks_multiply]; simp, by rw [Matrix.fromBlocks_multiply]; simp⟩
    have hemb : ∀ {F : Type} [Field F] (f : 𝒪[k] →+* F),
        Matrix.GeneralLinearGroup.map f g₀ = embX l (Matrix.GeneralLinearGroup.map f γ₀) := by
      intro F _ f
      refine Units.ext ?_
      rw [GlobalTheory.RootEx.Radical.embX_val]
      change (Matrix.fromBlocks γ₀.val 0 0 1).map f = _
      rw [Matrix.fromBlocks_map]
      simp
    have hm : embX l γ ∈ P.J := (hP.1 _).2 ⟨1, one_mem _, gb, hgb, g₀, by rw [hemb, h1], by rw [hemb, h2, one_mul]⟩
    refine ⟨hm, ?_⟩
    have hblk : (embX l γ).val.toBlocks₁₁ = γ.val := by
      rw [GlobalTheory.RootEx.Radical.embX_val, Matrix.toBlocks_fromBlocks₁₁]
    rw [hP.2 ⟨_, hm⟩]
    simp only [simpleSum_embX, hblk, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
  · intro u hu hm
    rw [hP.2 ⟨u, hm⟩]
    simp only [GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu, GlobalTheory.GenericShape.superSum_one, mul_zero,
      AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
end GlobalTheory.SymShape
