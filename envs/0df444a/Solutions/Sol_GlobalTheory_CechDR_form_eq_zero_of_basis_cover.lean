-- Prove2me | solution 1 for GlobalTheory.CechDR.form_eq_zero_of_basis_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:25:02.556837+00:00
-- url     : https://prove2.me/submissions/e82c6e4b-0ce5-4f4d-8710-efd5856ca37e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FormPowSmulEqZeroOfResBasicOpen
import Theorems.Thm_GlobalTheory_CechDR_form_pow_smul_eq_zero_of_res_basicOpen
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
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR
namespace GlobalTheory.CechDR
theorem _root_.solution : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : AffOp X') (ω : Ω[(OAff s').obj T⁄R']), (∀ t (u : T ⟶ G.obj t), p1 (OAff s') u ω = 0) → ω = 0) := by
  intro R' _ X' s' C' _ G hcov T ω hω
  obtain ⟨n, b, hspan, hb⟩ := hcov T
  let A := (OAff s').obj T
  let J : Ideal A := (Submodule.span A {ω}).annihilator
  have hpow : ∀ i, ∃ m : ℕ, b i ^ m ∈ J := by
    intro i
    have hU : IsAffineOpen (X'.basicOpen (show Γ(X', T.unop.1) from b i)) :=
      T.unop.2.basicOpen _
    have hle : (⟨X'.basicOpen (show Γ(X', T.unop.1) from b i), hU⟩ : X'.affineOpens) ≤ T.unop :=
      X'.basicOpen_le _
    have hunit : IsUnit (mp (OAff s') (homOfLE hle).op (b i)) :=
      X'.toRingedSpace.isUnit_res_basicOpen (show Γ(X', T.unop.1) from b i)
    obtain ⟨t, v, w, hvw⟩ := hb i _ (homOfLE hle).op hunit
    have h0 : p1 (OAff s') (homOfLE hle).op ω = 0 := by
      rw [← hvw, oneFormsMapOfFunctorMorphism_comp, hω t v, map_zero]
    obtain ⟨m, hm⟩ := form_pow_smul_eq_zero_of_res_basicOpen s' T.unop _ hU hle ω h0
    exact ⟨m, (Submodule.mem_annihilator_span_singleton ω _).2 hm⟩
  choose m hm using hpow
  have hJ : J = ⊤ := by
    rw [eq_top_iff, ← Ideal.span_pow_eq_top _ hspan (∑ i, m i), Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hmi : m i ≤ ∑ j, m j :=
      Finset.single_le_sum (f := m) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    change b i ^ (∑ j, m j) ∈ J
    rw [← Nat.add_sub_cancel' hmi, pow_add]
    exact J.mul_mem_right _ (hm i)
  have h1 : (1 : A) ∈ J := hJ ▸ Submodule.mem_top
  simpa using (Submodule.mem_annihilator_span_singleton _ _).1 h1
end GlobalTheory.CechDR
