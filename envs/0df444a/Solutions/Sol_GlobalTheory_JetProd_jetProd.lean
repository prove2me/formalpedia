-- Prove2me | solution 1 for GlobalTheory.JetProd.jetProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:13:50.282019+00:00
-- url     : https://prove2.me/submissions/6bf1451d-a5d2-4a54-9b0a-68f1745696a0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_JetAt0ProdRename
import Theorems.Thm_GlobalTheory_JetProd_jetAt0_prod_rename
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_kindAll_pl
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
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
private lemma coeff_rename_eq_zero_of_not_mem_range_embDomain {α β : Type} (f : α ↪ β) (p : MvPowerSeries α C)
    {x : β →₀ ℕ} (hx : x ∉ Set.range (Finsupp.embDomain f)) :
    MvPowerSeries.coeff x (MvPowerSeries.rename f p) = 0 := by
  rw [MvPowerSeries.coeff_rename]
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [Set.Finite.mem_toFinset] at hy
  exact absurd ⟨y, by rw [Finsupp.embDomain_eq_mapDomain]; simpa using hy⟩ hx
end General
section Rows
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] in
private lemma mvExp_zero_eq_one' {α : Type} : _root_.Formalism.IncomingBounds.mvExp (0 : MvPowerSeries α C) = 1 := by
  ext m
  show (∑ k ∈ Finset.range (m.degree + 1),
    MvPowerSeries.coeff m ((0 : MvPowerSeries α C) ^ k) / (k.factorial : C)) =
      MvPowerSeries.coeff m 1
  rw [Finset.sum_range_succ']
  simp
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] in
private lemma rowCopy_eq_rename_rowEmb {N : ℕ} (ρ : Fin N) (g : MvPowerSeries (_root_.Formalism.L2.FormalSeriesBounds.WV I) C) :
    _root_.Formalism.L2.FormalSeriesBounds.rowCopy ρ g = MvPowerSeries.rename (_root_.GlobalTheory.JetProd.rowEmb ρ) g := by
  unfold _root_.Formalism.L2.FormalSeriesBounds.rowCopy
  rw [MvPowerSeries.rename_eq_subst]
  rfl
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] in
private lemma degree_embDomain_eq_degree {α β : Type} (f : α ↪ β) (y : α →₀ ℕ) :
    (Finsupp.embDomain f y).degree = y.degree := by
  classical
  show ∑ i ∈ (Finsupp.embDomain f y).support, (Finsupp.embDomain f y) i = ∑ i ∈ y.support, y i
  rw [Finsupp.support_embDomain, Finset.sum_map]
  simp
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] in
private lemma rename_mvExp_eq_mvExp_rename {α β : Type} (f : α ↪ β) (g : MvPowerSeries α C) :
    MvPowerSeries.rename f (_root_.Formalism.IncomingBounds.mvExp g) = _root_.Formalism.IncomingBounds.mvExp (MvPowerSeries.rename f g) := by
  ext x
  by_cases hx : x ∈ Set.range (Finsupp.embDomain f)
  · obtain ⟨y, rfl⟩ := hx
    rw [MvPowerSeries.coeff_embDomain_rename]
    show (∑ k ∈ Finset.range (y.degree + 1), MvPowerSeries.coeff y (g ^ k) / (k.factorial : C)) =
      ∑ k ∈ Finset.range ((Finsupp.embDomain f y).degree + 1),
        MvPowerSeries.coeff (Finsupp.embDomain f y) (MvPowerSeries.rename f g ^ k) /
          (k.factorial : C)
    rw [degree_embDomain_eq_degree]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_pow, MvPowerSeries.coeff_embDomain_rename]
  · rw [coeff_rename_eq_zero_of_not_mem_range_embDomain f _ hx]
    show (0 : C) = ∑ k ∈ Finset.range (x.degree + 1),
        MvPowerSeries.coeff x (MvPowerSeries.rename f g ^ k) / (k.factorial : C)
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [← map_pow, coeff_rename_eq_zero_of_not_mem_range_embDomain f _ hx, zero_div]
open scoped BigOperators in
open NumberField in
open Finsupp in
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] in
private lemma valOf_eq_jetAt0_prod_rename_rowSer
    (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (_root_.Formalism.L2.FormalSeriesBounds.WV I) C)
    {N : ℕ} (P : MvPolynomial (Fin N × _root_.Formalism.L2.FormalSeriesBounds.WV I) C) (kd : Fin N → _root_.Formalism.L2.FormalSeriesBounds.Knd d)
    (gs : Fin N → MvPowerSeries (_root_.Formalism.L2.FormalSeriesBounds.WV I) C) :
    _root_.Formalism.L2.FormalSeriesBounds.ValOf hL P kd gs = _root_.Formalism.IncomingBounds.jetAt0 P (∏ ρ, MvPowerSeries.rename (_root_.GlobalTheory.JetProd.rowEmb ρ)
      (_root_.GlobalTheory.JetProd.rowSer hL (kd ρ) (gs ρ))) := by
  unfold _root_.Formalism.L2.FormalSeriesBounds.ValOf
  congr 1
  refine Finset.prod_congr rfl fun ρ _ => ?_
  simp only [rowCopy_eq_rename_rowEmb]
  rw [← rename_mvExp_eq_mvExp_rename, ← map_mul]
  rfl
end Rows
end GlobalTheory.JetProd
end

set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.JetProd
open Finsupp
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]
open scoped BigOperators
open NumberField
open Finsupp
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]
namespace GlobalTheory.JetProd
namespace _root_.GlobalTheory.JetProd
theorem _root_.solution : _root_.Formalism.L2.FormalSeriesBounds.JetProdSt := by
  intro C _ d I _ hL N K what₂ pl hpl P kind gr
  classical
  let emb : ∀ i, Fin (what₂ i) × _root_.Formalism.L2.FormalSeriesBounds.WV I ↪ Fin N × _root_.Formalism.L2.FormalSeriesBounds.WV I := fun i =>
    ⟨fun x => (pl ⟨i, x.1⟩, x.2), fun x y h => by
      simp only [Prod.mk.injEq] at h
      have h1 := hpl h.1
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h1
      exact Prod.ext h1 h.2⟩
  have hdisj : ∀ i j (x : Fin (what₂ i) × _root_.Formalism.L2.FormalSeriesBounds.WV I) (y : Fin (what₂ j) × _root_.Formalism.L2.FormalSeriesBounds.WV I),
      emb i x = emb j y → i = j := fun i j x y h =>
    congrArg Sigma.fst (hpl (congrArg Prod.fst h))
  have hZ : ∀ s, _root_.Formalism.L2.FormalSeriesBounds.grAll pl gr (pl s) = gr s.1 s.2 := fun s => by
    unfold _root_.Formalism.L2.FormalSeriesBounds.grAll
    split_ifs with h
    · rw [hpl h.choose_spec]
    · exact absurd ⟨s, rfl⟩ h
  have hT : ∏ ρ, MvPowerSeries.rename (_root_.GlobalTheory.JetProd.rowEmb ρ)
        (_root_.GlobalTheory.JetProd.rowSer hL (_root_.Formalism.L2.FormalSeriesBounds.kindAll pl kind ρ) (_root_.Formalism.L2.FormalSeriesBounds.grAll pl gr ρ)) =
      ∏ i, MvPowerSeries.rename (emb i) (∏ r, MvPowerSeries.rename (_root_.GlobalTheory.JetProd.rowEmb r)
        (_root_.GlobalTheory.JetProd.rowSer hL (kind i r) (gr i r))) := by
    rw [← Fintype.prod_of_injective pl hpl
      (fun s => MvPowerSeries.rename (_root_.GlobalTheory.JetProd.rowEmb (pl s))
        (_root_.GlobalTheory.JetProd.rowSer hL (kind s.1 s.2) (gr s.1 s.2)))]
    · rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [MvPowerSeries.rename_rename]
      rfl
    · intro ρ hρ
      have hn : ¬ ∃ s, pl s = ρ := fun ⟨s, hs⟩ => hρ ⟨s, hs⟩
      have hZ1 : _root_.Formalism.L2.FormalSeriesBounds.grAll pl gr ρ = 1 := by unfold _root_.Formalism.L2.FormalSeriesBounds.grAll; rw [dif_neg hn]
      have hK : _root_.Formalism.L2.FormalSeriesBounds.kindAll pl kind ρ = none := by unfold _root_.Formalism.L2.FormalSeriesBounds.kindAll; rw [dif_neg hn]
      rw [hZ1, hK]
      show MvPowerSeries.rename _ (1 * _root_.Formalism.IncomingBounds.mvExp 0) = 1
      rw [mvExp_zero_eq_one', mul_one, map_one]
    · intro s
      rw [hZ, _root_.Formalism.L2.FormalSeriesBounds.kindAll_pl hpl]
  simp only [valOf_eq_jetAt0_prod_rename_rowSer]
  rw [hT]
  exact _root_.GlobalTheory.JetProd.jetAt0_prod_rename emb hdisj P _
end _root_.GlobalTheory.JetProd
end GlobalTheory.JetProd
