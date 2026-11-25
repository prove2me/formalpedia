-- Prove2me | solution 1 for GlobalTheory.CechDR.exists_triple_below_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:27:37.811997+00:00
-- url     : https://prove2.me/submissions/2411f47b-bd7b-4693-8d13-69aac45b2ffd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite GlobalTheory.CatCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open FormExt FormExtJ
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
variable {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
variable (ψ φ)
variable {ψ φ}
variable (ψ φ)
namespace GlobalTheory.CechDR
theorem _root_.solution (s'' : X'' ⟶ Sp R'') : ∀ (t₁ t₂ : (Triple ψ φ)ᵒᵖ) (S : AffOp X''),
    ((cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t₁ ⟶ S) → ((cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s'').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X'') (u : S ⟶ S'), IsUnit (mp (OAff s'') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧
            Nonempty ((cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t₃ ⟶ S') := by
  intro t₁ t₂ S h₁ h₂
  have hS₁ : S.unop.1 ≤ t₁.unop.1.1.1 := leOfHom h₁.unop
  have hS₂ : S.unop.1 ≤ t₂.unop.1.1.1 := leOfHom h₂.unop
  let B : Set Γ(X'', S.unop.1) := {g | ∃ (W' : X'.affineOpens) (W : X.affineOpens),
    W.1 ≤ t₁.unop.1.2.2.1 ∧ W.1 ≤ t₂.unop.1.2.2.1 ∧ W'.1 ≤ t₁.unop.1.2.1.1 ∧
      W'.1 ≤ t₂.unop.1.2.1.1 ∧ W'.1 ≤ φ ⁻¹ᵁ W.1 ∧ X''.basicOpen g ≤ ψ ⁻¹ᵁ W'.1}
  have hB : Ideal.span B = ⊤ := by
    refine (S.unop.2.self_le_iSup_basicOpen_iff).1 fun x hx ↦ ?_
    have hy₁ : ψ.base x ∈ t₁.unop.1.2.1.1 := t₁.unop.2.1 (hS₁ hx)
    have hy₂ : ψ.base x ∈ t₂.unop.1.2.1.1 := t₂.unop.2.1 (hS₂ hx)
    have hz₁ : φ.base (ψ.base x) ∈ t₁.unop.1.2.2.1 := t₁.unop.2.2 hy₁
    have hz₂ : φ.base (ψ.base x) ∈ t₂.unop.1.2.2.1 := t₂.unop.2.2 hy₂
    obtain ⟨W, hW, hzW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base (ψ.base x))
      (U := t₁.unop.1.2.2.1 ⊓ t₂.unop.1.2.2.1) ⟨hz₁, hz₂⟩
    obtain ⟨W', hW', hyW', hW'V⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base x)
      (U := t₁.unop.1.2.1.1 ⊓ t₂.unop.1.2.1.1 ⊓ φ ⁻¹ᵁ W) ⟨⟨hy₁, hy₂⟩, hzW⟩
    obtain ⟨f, hf, hxf⟩ := S.unop.2.exists_basicOpen_le (V := S.unop.1 ⊓ ψ ⁻¹ᵁ W')
      ⟨x, hx, hyW'⟩ hx
    have hfB : f ∈ B := ⟨⟨W', hW'⟩, ⟨W, hW⟩, fun y hy ↦ (hWV hy).1, fun y hy ↦ (hWV hy).2,
      fun y hy ↦ (hW'V hy).1.1, fun y hy ↦ (hW'V hy).1.2, fun y hy ↦ (hW'V hy).2,
      hf.trans inf_le_right⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfB⟩, hxf⟩
  obtain ⟨s0, hs0, hspan⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
  refine ⟨s0.card, fun i ↦ (s0.equivFin.symm i).1, ?_, fun i S' u hu ↦ ?_⟩
  · have hsp : Ideal.span (Set.range fun i ↦ ((s0.equivFin.symm i).1 : Γ(X'', S.unop.1))) = ⊤ := by
      rw [eq_top_iff, ← hspan]
      exact Ideal.span_mono fun x hx ↦ ⟨s0.equivFin ⟨x, hx⟩, by simp⟩
    exact hsp
  · have hbB : (s0.equivFin.symm i).1 ∈ B := hs0 (s0.equivFin.symm i).2
    obtain ⟨W', W, hW₁, hW₂, hW'₁, hW'₂, hW'W, hg⟩ := hbB
    set g : Γ(X'', S.unop.1) := (s0.equivFin.symm i).1
    change IsUnit (X''.presheaf.map (homOfLE (show S'.unop.1 ≤ S.unop.1 from leOfHom u.unop)).op g) at hu
    have hS' : S'.unop.1 ≤ X''.basicOpen g := by
      have := Scheme.basicOpen_of_isUnit X'' hu
      rw [Scheme.basicOpen_res] at this
      rw [← this]; exact inf_le_right
    let t₃ : Triple ψ φ := ⟨(⟨X''.basicOpen g, S.unop.2.basicOpen g⟩, W', W), hg, hW'W⟩
    refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩⟩
    · exact ⟨(X''.basicOpen_le g).trans hS₁, hW'₁, hW₁⟩
    · exact ⟨(X''.basicOpen_le g).trans hS₂, hW'₂, hW₂⟩
    · exact hS'
end GlobalTheory.CechDR
