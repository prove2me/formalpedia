-- Prove2me | solution 1 for GlobalTheory.CechDR.exists_pair_below_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:15:40.017501+00:00
-- url     : https://prove2.me/submissions/422d6aac-592e-4bf4-98c9-508a077df704

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPairBelowTwo
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR
namespace GlobalTheory.CechDR
theorem _root_.solution : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R'), (∀ (t₁ t₂ : (Pair φ)ᵒᵖ) (S : AffOp X'), ((pairFst φ).obj t₁ ⟶ S) → ((pairFst φ).obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty ((pairFst φ).obj t₃ ⟶ S')) := by
  intro R' _ X X' φ s' t₁ t₂ S h₁ h₂
  have hS₁ : S.unop.1 ≤ t₁.unop.1.1.1 := leOfHom h₁.unop
  have hS₂ : S.unop.1 ≤ t₂.unop.1.1.1 := leOfHom h₂.unop
  let B : Set Γ(X', S.unop.1) := {g | ∃ W : X.affineOpens, W.1 ≤ t₁.unop.1.2.1 ∧
    W.1 ≤ t₂.unop.1.2.1 ∧ X'.basicOpen g ≤ φ ⁻¹ᵁ W.1}
  have hB : Ideal.span B = ⊤ := by
    refine (S.unop.2.self_le_iSup_basicOpen_iff).1 fun x hx ↦ ?_
    have hx₁ : φ.base x ∈ t₁.unop.1.2.1 := t₁.unop.2 (hS₁ hx)
    have hx₂ : φ.base x ∈ t₂.unop.1.2.1 := t₂.unop.2 (hS₂ hx)
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x)
      (U := t₁.unop.1.2.1 ⊓ t₂.unop.1.2.1) ⟨hx₁, hx₂⟩
    obtain ⟨f, hf, hxf⟩ := S.unop.2.exists_basicOpen_le (V := S.unop.1 ⊓ φ ⁻¹ᵁ W)
      ⟨x, hx, hxW⟩ hx
    have hfB : f ∈ B := ⟨⟨W, hW⟩, fun y hy ↦ (hWV hy).1, fun y hy ↦ (hWV hy).2,
      hf.trans inf_le_right⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfB⟩, hxf⟩
  obtain ⟨s0, hs0, hspan⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
  refine ⟨s0.card, fun i ↦ (s0.equivFin.symm i).1, ?_, fun i S' u hu ↦ ?_⟩
  · have hsp : Ideal.span (Set.range fun i ↦ ((s0.equivFin.symm i).1 : Γ(X', S.unop.1))) = ⊤ := by
      rw [eq_top_iff, ← hspan]
      exact Ideal.span_mono fun x hx ↦ ⟨s0.equivFin ⟨x, hx⟩, by simp⟩
    exact hsp
  · have hbB : (s0.equivFin.symm i).1 ∈ B := hs0 (s0.equivFin.symm i).2
    obtain ⟨W, hW₁, hW₂, hW⟩ := hbB
    set g : Γ(X', S.unop.1) := (s0.equivFin.symm i).1 with hg
    change IsUnit (X'.presheaf.map (homOfLE (show S'.unop.1 ≤ S.unop.1 from leOfHom u.unop)).op g) at hu
    have hS' : S'.unop.1 ≤ X'.basicOpen g := by
      have := Scheme.basicOpen_of_isUnit X' hu
      rw [Scheme.basicOpen_res] at this
      rw [← this]; exact inf_le_right
    let t₃ : Pair φ := ⟨(⟨X'.basicOpen g, S.unop.2.basicOpen g⟩, W), hW⟩
    refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩⟩
    · exact ⟨(X'.basicOpen_le g).trans hS₁, hW₁⟩
    · exact ⟨(X'.basicOpen_le g).trans hS₂, hW₂⟩
    · exact hS'
end GlobalTheory.CechDR
