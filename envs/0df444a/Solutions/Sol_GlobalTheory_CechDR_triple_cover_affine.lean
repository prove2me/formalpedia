-- Prove2me | solution 1 for GlobalTheory.CechDR.triple_cover_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:32:29.697888+00:00
-- url     : https://prove2.me/submissions/87d4761f-a3ab-4dd4-9936-cbec86b7c75e

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
theorem _root_.solution (s'' : X'' ⟶ Sp R'') : ∀ T : AffOp X'', ∃ (n : ℕ) (b : Fin n → (OAff s'').obj T),
    Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X'') (u : T ⟶ S),
      IsUnit (mp (OAff s'') u (b i)) →
        ∃ (t : (Triple ψ φ)ᵒᵖ) (v : T ⟶ (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t)
          (w : (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t ⟶ S), v ≫ w = u := by
  intro T
  have hT : IsAffineOpen T.unop.1 := T.unop.2
  let G : Set Γ(X'', T.unop.1) :=
    {f | ∃ (V' : X'.affineOpens) (V : X.affineOpens), V'.1 ≤ φ ⁻¹ᵁ V.1 ∧
      X''.basicOpen f ≤ ψ ⁻¹ᵁ V'.1}
  have hG : Ideal.span G = ⊤ := by
    rw [← hT.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base (ψ.base x))
      (U := (⊤ : X.Opens)) trivial
    obtain ⟨V', hV', hxV', hV'V⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base x)
      (U := φ ⁻¹ᵁ V) hxV
    obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := ψ ⁻¹ᵁ V') ⟨x, hxV'⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨⟨f, ⟨⟨V', hV'⟩, ⟨V, hV⟩, fun y hy ↦ hV'V hy, hf⟩⟩, hxf⟩
  obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
  · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X'', T.unop.1)) := by
      ext f
      constructor
      · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
      · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
    exact hR ▸ hF
  · intro i S u hu
    obtain ⟨V', V, hV'V, hV⟩ := hFG (F.equivFin.symm i).2
    set f : Γ(X'', T.unop.1) := (F.equivFin.symm i).1
    have hW : IsAffineOpen (X''.basicOpen f) := hT.basicOpen f
    have hWT : X''.basicOpen f ≤ T.unop.1 := X''.basicOpen_le f
    let t : Triple ψ φ := ⟨(⟨_, hW⟩, V', V), hV, hV'V⟩
    have hSW : S.unop.1 ≤ X''.basicOpen f := by
      have h1 : X''.basicOpen (X''.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
        X''.basicOpen_of_isUnit hu
      rw [Scheme.basicOpen_res] at h1
      rw [← h1]; exact inf_le_right
    refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X''.affineOpens) ≤ T.unop from hWT)).op,
      (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X''.affineOpens) from hSW)).op, ?_⟩
    exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
end GlobalTheory.CechDR
