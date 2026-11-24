-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.covBy_unit_above
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:17:35.859507+00:00
-- url     : https://prove2.me/submissions/732f1dbf-0bdd-4e05-8ceb-fc6a68db5728

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovBy
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisObjectsUnitLociCoverAbove
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_span_map_eq_top
import Theorems.Thm_GlobalTheory_CatCoh_Desc_isUnit_comp
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm


section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry KaehlerDifferential in
private lemma covBy_of_covBy_localizations {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (P : C → Prop) (hLoc : _root_.GlobalTheory.CatCoh.Desc.HasLoc F) (T : C)
    {n : ℕ} (c : Fin n → F.obj T) (hc : Ideal.span (Set.range c) = ⊤)
    (h : ∀ (j : Fin n) (L : C) (l : T ⟶ L), IsUnit (_root_.GlobalTheory.CatCoh.mp F l (c j)) →
      (∀ (S : C) (w : T ⟶ S), IsUnit (_root_.GlobalTheory.CatCoh.mp F w (c j)) → ∃! v, l ≫ v = w) →
      _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy F P L) :
    _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy F P T := by
  have hL := fun j => hLoc T (c j)
  choose L l hlu hsurj hker huniv using hL
  have hcov := fun j => h j (L j) (l j) (hlu j) (huniv j)
  unfold _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy at hcov
  choose m e he hP using hcov
  choose N x hx using fun j k => hsurj j (e j k)
  let b' : (Σ j : Fin n, Fin (m j)) → F.obj T := fun p => x p.1 p.2 * c p.1
  have hspan' : Ideal.span (Set.range b') = ⊤ := by
    rw [← Ideal.radical_eq_top, eq_top_iff, ← hc, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : (1 : F.obj (L j)) ∈ Ideal.span (Set.range (e j)) := by
      rw [he j]; exact Submodule.mem_top
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    choose N' s hs using fun k => hsurj j (r k)
    have hq : ∀ k, ∃ q, (∑ k', (N' k' + N j k')) = N' k + N j k + q := fun k =>
      Nat.exists_eq_add_of_le (Finset.single_le_sum (f := fun k' => N' k' + N j k')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    choose q hq using hq
    have hterm : ∀ k, _root_.GlobalTheory.CatCoh.mp F (l j) (s k * x j k * c j ^ q k) =
        (r k • e j k) * _root_.GlobalTheory.CatCoh.mp F (l j) (c j) ^ (∑ k', (N' k' + N j k')) := by
      intro k
      rw [map_mul, map_mul, map_pow, ← hs k, ← hx j k, hq k, pow_add, pow_add, smul_eq_mul]
      ring
    have hz : _root_.GlobalTheory.CatCoh.mp F (l j)
        (c j ^ (∑ k', (N' k' + N j k')) - ∑ k, s k * x j k * c j ^ q k) = 0 := by
      rw [map_sub, map_sum, Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_mul, hr,
        one_mul, map_pow, sub_self]
    obtain ⟨M, hM⟩ := hker j _ hz
    refine ⟨M + (∑ k', (N' k' + N j k')) + 1, ?_⟩
    have h2 : c j ^ M * c j ^ (∑ k', (N' k' + N j k')) =
        c j ^ M * ∑ k, s k * x j k * c j ^ q k := by
      rw [← sub_eq_zero, ← mul_sub]; exact hM
    have h3 : c j ^ (M + (∑ k', (N' k' + N j k')) + 1) =
        ∑ k, (c j ^ M * s k * c j ^ q k) * b' ⟨j, k⟩ := by
      rw [pow_succ, pow_add, h2, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [b']
      ring
    rw [h3]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨j, k⟩, rfl⟩)
  unfold _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy
  let eqv := Fintype.equivFin (Σ j : Fin n, Fin (m j))
  refine ⟨Fintype.card (Σ j : Fin n, Fin (m j)), b' ∘ eqv.symm, ?_, ?_⟩
  · rw [Set.range_comp, eqv.symm.range_eq_univ, Set.image_univ]
    exact hspan'
  · intro i S w hw
    change IsUnit (_root_.GlobalTheory.CatCoh.mp F w
      (x (eqv.symm i).1 (eqv.symm i).2 * c (eqv.symm i).1)) at hw
    generalize eqv.symm i = p at hw
    obtain ⟨j, k⟩ := p
    rw [map_mul, IsUnit.mul_iff] at hw
    obtain ⟨hxw, hcw⟩ := hw
    obtain ⟨v, hv, -⟩ := huniv j S w hcw
    apply hP j k S v
    have hfac : _root_.GlobalTheory.CatCoh.mp F w (x j k) = _root_.GlobalTheory.CatCoh.mp F v (e j k) *
        (_root_.GlobalTheory.CatCoh.mp F v (_root_.GlobalTheory.CatCoh.mp F (l j) (c j))) ^ (N j k) := by
      rw [← hv, _root_.GlobalTheory.CatCoh.mp_comp, ← hx j k, map_mul, map_pow]
    rw [hfac, IsUnit.mul_iff] at hxw
    exact hxw.1
end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end

set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential
namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
namespace _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → _root_.GlobalTheory.CatCoh.Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (_root_.GlobalTheory.CatCoh.mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (_root_.GlobalTheory.CatCoh.mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (t : C') (u : T ⟶ G.obj t), _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), (∃ i, IsUnit (_root_.GlobalTheory.CatCoh.mp F (u ≫ G.map a) (d i))) ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) := by
  intro R _ C _ C' _ F G _ _ hLoc hbasis hB T n d hd t u
  apply covBy_of_covBy_localizations F _ hLoc (G.obj t)
    (fun j => _root_.GlobalTheory.CatCoh.mp F u (d j)) (_root_.GlobalTheory.CatCoh.Desc.Basis.span_map_eq_top F u hd)
  intro j L l hl _
  obtain ⟨m, e, he, hfac⟩ := hbasis L
  apply covBy_of_covBy_localizations F _ hLoc L e he
  intro k L' l' hl' _
  obtain ⟨t'', v₁, v₂, -⟩ := hfac k L' l' hl'
  obtain ⟨p, f, hf, hP⟩ := hB t t'' L' (l ≫ l') v₂
  unfold _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy
  refine ⟨p, f, hf, ?_⟩
  intro i S'' z hz
  obtain ⟨t₃, ⟨c₁⟩, ⟨c₂⟩, ⟨w⟩⟩ := hP i S'' z hz
  refine ⟨t₃, c₁, ⟨j, ?_⟩, ⟨w⟩⟩
  have hunit : IsUnit (_root_.GlobalTheory.CatCoh.mp F (u ≫ l ≫ v₁ ≫ G.map c₂) (d j)) := by
    rw [_root_.GlobalTheory.CatCoh.mp_comp]
    exact _root_.GlobalTheory.CatCoh.Desc.isUnit_comp (v₁ ≫ G.map c₂) hl
  rwa [show u ≫ G.map c₁ = u ≫ l ≫ v₁ ≫ G.map c₂ from Subsingleton.elim _ _]
end _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
