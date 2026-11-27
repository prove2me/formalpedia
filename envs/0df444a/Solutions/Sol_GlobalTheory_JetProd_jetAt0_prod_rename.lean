-- Prove2me | solution 1 for GlobalTheory.JetProd.jetAt0_prod_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:55:44.312718+00:00
-- url     : https://prove2.me/submissions/530995bc-e87f-446e-a73e-b311fff3fb73

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_JetAt0ProdRename
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_prod
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.JetProd
open Finsupp
section General
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ)
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma prod_monomial_eq_monomial_sum_prod' {α κ : Type} (s : Finset κ) (D : κ → α →₀ ℕ) (a : κ → C) :
    ∏ k ∈ s, MvPolynomial.monomial (D k) (a k) =
      MvPolynomial.monomial (∑ k ∈ s, D k) (∏ k ∈ s, a k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk, Finset.prod_insert hk, ih,
      MvPolynomial.monomial_mul]
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma jetAt0_zero_left_unramified_depth {α : Type} (G : MvPowerSeries α C) :
    _root_.Formalism.IncomingBounds.jetAt0 (0 : MvPolynomial α C) G = 0 := by
  unfold _root_.Formalism.IncomingBounds.jetAt0
  simp
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma jetAt0_eq_sum_coeff_mul_mfact_of_support_subset {α : Type} (P : MvPolynomial α C) (G : MvPowerSeries α C)
    {s : Finset (α →₀ ℕ)} (hs : P.support ⊆ s) :
    _root_.Formalism.IncomingBounds.jetAt0 P G = ∑ m ∈ s, MvPolynomial.coeff m P * (_root_.Formalism.IncomingBounds.mfact m : C) * MvPowerSeries.coeff m G := by
  unfold _root_.Formalism.IncomingBounds.jetAt0
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm, zero_mul, zero_mul]
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma jetAt0_add_left' {α : Type} (P Q : MvPolynomial α C) (G : MvPowerSeries α C) :
    _root_.Formalism.IncomingBounds.jetAt0 (P + Q) G = _root_.Formalism.IncomingBounds.jetAt0 P G + _root_.Formalism.IncomingBounds.jetAt0 Q G := by
  classical
  rw [jetAt0_eq_sum_coeff_mul_mfact_of_support_subset (P + Q) G (MvPolynomial.support_add (p := P) (q := Q)),
    jetAt0_eq_sum_coeff_mul_mfact_of_support_subset P G Finset.subset_union_left,
    jetAt0_eq_sum_coeff_mul_mfact_of_support_subset Q G Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma jetAt0_monomial_eq_mul_mfact_mul_coeff {α : Type} (D : α →₀ ℕ) (a : C) (G : MvPowerSeries α C) :
    _root_.Formalism.IncomingBounds.jetAt0 (MvPolynomial.monomial D a) G = a * (_root_.Formalism.IncomingBounds.mfact D : C) * MvPowerSeries.coeff D G := by
  classical
  rw [jetAt0_eq_sum_coeff_mul_mfact_of_support_subset _ G (MvPolynomial.support_monomial_subset (s := D) (a := a)),
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma jetAt0_sum_monomial_eq_sum_mul_mfact_mul_coeff {α κ : Type} (F : Finset κ) (D : κ → α →₀ ℕ) (a : κ → C)
    (G : MvPowerSeries α C) :
    _root_.Formalism.IncomingBounds.jetAt0 (∑ f ∈ F, MvPolynomial.monomial (D f) (a f)) G =
      ∑ f ∈ F, a f * (_root_.Formalism.IncomingBounds.mfact (D f) : C) * MvPowerSeries.coeff (D f) G := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [jetAt0_zero_left_unramified_depth]
  | insert f F hf ih => rw [Finset.sum_insert hf, Finset.sum_insert hf, jetAt0_add_left', ih, jetAt0_monomial_eq_mul_mfact_mul_coeff]
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma coeff_rename_eq_zero_of_not_mem_range_embDomain {α β : Type} (f : α ↪ β) (p : MvPowerSeries α C)
    {x : β →₀ ℕ} (hx : x ∉ Set.range (Finsupp.embDomain f)) :
    MvPowerSeries.coeff x (MvPowerSeries.rename f p) = 0 := by
  rw [MvPowerSeries.coeff_rename]
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [Set.Finite.mem_toFinset] at hy
  exact absurd ⟨y, by rw [Finsupp.embDomain_eq_mapDomain]; simpa using hy⟩ hx
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma sum_embDomain_apply_eq_of_disjoint (hd : ∀ i j x y, e i x = e j y → i = j)
    (z : ∀ i, σ i →₀ ℕ) (j : ι) (x : σ j) :
    (∑ k, Finsupp.embDomain (e k) (z k)) (e j x) = z j x := by
  classical
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single j]
  · exact Finsupp.embDomain_apply_self (e j) (z j) x
  · intro k _ hk
    apply Finsupp.embDomain_notin_range
    rintro ⟨w, hw⟩
    exact hk (hd k j w x hw)
  · intro h
    exact absurd (Finset.mem_univ j) h
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma coeff_sum_embDomain_prod_rename_eq_prod_coeff (hd : ∀ i j x y, e i x = e j y → i = j)
    (G : ∀ i, MvPowerSeries (σ i) C) (m : ∀ i, σ i →₀ ℕ) :
    MvPowerSeries.coeff (∑ k, Finsupp.embDomain (e k) (m k))
        (∏ j, MvPowerSeries.rename (e j) (G j)) = ∏ j, MvPowerSeries.coeff (m j) (G j) := by
  classical
  rw [MvPowerSeries.coeff_prod]
  set l0 : ι →₀ (τ →₀ ℕ) := Finsupp.equivFunOnFinite.symm fun k => Finsupp.embDomain (e k) (m k)
    with hl0
  have hl0j : ∀ j, l0 j = Finsupp.embDomain (e j) (m j) := fun j => by simp [hl0]
  rw [Finset.sum_eq_single l0]
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [hl0j]
    exact MvPowerSeries.coeff_embDomain_rename (e j) (G j) (m j)
  · intro b hb hne
    by_contra hprod
    apply hne
    rw [Finset.mem_finsuppAntidiag] at hb
    have hz : ∀ j, ∃ z, Finsupp.embDomain (e j) z = b j := fun j => by
      by_contra h
      exact Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ j)
        (coeff_rename_eq_zero_of_not_mem_range_embDomain (e j) (G j) (by rintro ⟨z, hz⟩; exact h ⟨z, hz⟩))
    choose z hz using hz
    have hsum : ∑ k, Finsupp.embDomain (e k) (z k) = ∑ k, Finsupp.embDomain (e k) (m k) := by
      rw [← hb.1]
      exact Finset.sum_congr rfl fun k _ => hz k
    have hzm : z = m := by
      funext j
      ext x
      rw [← sum_embDomain_apply_eq_of_disjoint e hd z j x, hsum,
        sum_embDomain_apply_eq_of_disjoint e hd m j x]
    ext j : 1
    rw [← hz j, hzm, hl0j]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    exact Finset.sum_congr rfl fun j _ => hl0j j
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ) in
private lemma prod_factorial_sum_embDomain_eq_prod_prod_factorial (hd : ∀ i j x y, e i x = e j y → i = j)
    (m : ∀ i, σ i →₀ ℕ) :
    ((∑ k, Finsupp.embDomain (e k) (m k)).prod fun _ n => n.factorial) =
      ∏ j, (m j).prod fun _ n => n.factorial := by
  classical
  have hsub : (∑ k, Finsupp.embDomain (e k) (m k)).support ⊆
      Finset.univ.biUnion fun j => (m j).support.map (e j) := by
    refine (Finsupp.support_finset_sum).trans ?_
    simp [Finsupp.support_embDomain]
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      fun j => (m j).support.map (e j) := by
    intro j _ k _ hjk
    refine Finset.disjoint_left.mpr fun y hy hy' => ?_
    simp only [Finset.mem_map] at hy hy'
    obtain ⟨x, _, rfl⟩ := hy
    obtain ⟨x', _, hx'⟩ := hy'
    exact hjk (hd k j x' x hx').symm
  rw [Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => rfl), Finset.prod_biUnion hdisj]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_map, Finsupp.prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [sum_embDomain_apply_eq_of_disjoint e hd m j x]
end General
section Rows
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]
end Rows
end GlobalTheory.JetProd
end

set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.JetProd
open Finsupp
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ)
open scoped BigOperators
open NumberField
open Finsupp
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ)
namespace GlobalTheory.JetProd
namespace _root_.GlobalTheory.JetProd
theorem _root_.solution (hd : ∀ i j x y, e i x = e j y → i = j)
    (P : ∀ i, MvPolynomial (σ i) C) (G : ∀ i, MvPowerSeries (σ i) C) :
    _root_.Formalism.IncomingBounds.jetAt0 (∏ j, MvPolynomial.rename (e j) (P j)) (∏ j, MvPowerSeries.rename (e j) (G j)) =
      ∏ j, _root_.Formalism.IncomingBounds.jetAt0 (P j) (G j) := by
  classical
  have hP : ∏ j, MvPolynomial.rename (e j) (P j) =
      ∑ f ∈ Fintype.piFinset fun j => (P j).support,
        MvPolynomial.monomial (∑ k, Finsupp.embDomain (e k) (f k))
          (∏ k, MvPolynomial.coeff (f k) (P k)) := by
    conv_lhs => rw [show P = fun j => ∑ v ∈ (P j).support,
      MvPolynomial.monomial v (MvPolynomial.coeff v (P j)) from
        funext fun j => MvPolynomial.as_sum (P j)]
    simp only [map_sum, MvPolynomial.rename_monomial]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [prod_monomial_eq_monomial_sum_prod']
    simp only [Finsupp.embDomain_eq_mapDomain]
  rw [hP, jetAt0_sum_monomial_eq_sum_mul_mfact_mul_coeff]
  simp only [jetAt0_eq_sum_coeff_mul_mfact_of_support_subset _ _ (subset_refl _)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [coeff_sum_embDomain_prod_rename_eq_prod_coeff e hd, _root_.Formalism.IncomingBounds.mfact, prod_factorial_sum_embDomain_eq_prod_prod_factorial e hd,
    Nat.cast_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rfl
end _root_.GlobalTheory.JetProd
end GlobalTheory.JetProd
