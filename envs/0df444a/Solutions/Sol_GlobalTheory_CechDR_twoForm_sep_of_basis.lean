-- Prove2me | solution 1 for GlobalTheory.CechDR.twoForm_sep_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:13.371863+00:00
-- url     : https://prove2.me/submissions/969a090b-1091-49f3-9f38-48c51d3319e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoFormExistsPowSmulEqZeroOfIsLocalization
import Theorems.Thm_GlobalTheory_CechDR_twoForm_exists_pow_smul_eq_zero_of_algHom
import Theorems.Thm_GlobalTheory_CechDR_pOm_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR
namespace GlobalTheory.CechDR
theorem _root_.solution : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : AffOp X') (η : Om R' ((OAff s').obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm (OAff s') 2 u η = 0) → η = 0) := by
  intro R' _ X' s' C' _ G hcov T η hη
  obtain ⟨n, b, hb, hf⟩ := hcov T
  have key : ∀ i, ∃ m : ℕ, b i ^ m • η = 0 := by
    intro i
    let U : X'.affineOpens := T.unop
    let c : Γ(X', U.1) := b i
    let V : X'.affineOpens := ⟨X'.basicOpen c, U.2.basicOpen c⟩
    have hle : V ≤ U := X'.basicOpen_le c
    let u : T ⟶ Opposite.op V := (homOfLE hle).op
    have hu : IsUnit (mp (OAff s') u (b i)) := X'.toRingedSpace.isUnit_res_basicOpen c
    obtain ⟨t, v, w, hvw⟩ := hf i (Opposite.op V) u hu
    have h0 : pOm (OAff s') 2 u η = 0 := by rw [← hvw, pOm_comp, hη t v, map_zero]
    exact twoForm_exists_pow_smul_eq_zero_of_algHom (mp (OAff s') u) (b i)
      (U.2.isLocalization_basicOpen c) η h0
  choose m hm using key
  have hN : ∀ i, b i ^ (∑ j, m j) • η = 0 := fun i ↦ by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (m j))
      (Finset.mem_univ i))
    rw [hk, pow_add, mul_comm, mul_smul, hm i, smul_zero]
  have := Ideal.span_pow_eq_top _ hb (∑ j, m j)
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at this
  obtain ⟨r, hr⟩ := this
  rw [← one_smul ((OAff s').obj T) η, ← hr, Finset.sum_smul]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [Function.comp_apply, mul_smul, hN i, smul_zero]
end GlobalTheory.CechDR
