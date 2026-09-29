-- Prove2me | solution 1 for MvFormalGroup.BigWittLaw.subst_elim_negSeries_hom_and_coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c15256ce-b1b6-58e3-bc03-18484ce36576

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse
import Definitions.Def_MvFormalGroup_WittPointFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_BigWittLaw_subst_elim_negSeries_hom_and_coeff_eq_zero

set_option autoImplicit false

universe u v

noncomputable section

open MvPowerSeries

namespace P2mK1c

section PowerSeries

def ordIdeal (τ : Type*) (R : Type*) [CommRing R] (n : ℕ) : Ideal (MvPowerSeries τ R) where
  carrier := {a | (n : ℕ∞) ≤ a.order}
  zero_mem' := by simp
  add_mem' {a b} ha hb := le_trans (le_min ha hb) min_order_le_add
  smul_mem' c a ha := by
    refine le_trans ha (le_trans ?_ le_order_mul)
    exact le_add_self

variable {R : Type*} [CommRing R] {σ τ : Type*}

theorem mem_ordIdeal_iff {n : ℕ} {a : MvPowerSeries τ R} :
    a ∈ ordIdeal τ R n ↔ (n : ℕ∞) ≤ a.order := Iff.rfl

theorem coeff_eq_zero_of_mem_ordIdeal {n : ℕ} {a : MvPowerSeries τ R} (ha : a ∈ ordIdeal τ R n)
    {e : τ →₀ ℕ} (he : e.degree < n) : coeff e a = 0 :=
  coeff_of_lt_order (lt_of_lt_of_le (ENat.coe_lt_coe.mpr he) ha)

theorem mem_ordIdeal_of_coeff {n : ℕ} {a : MvPowerSeries τ R}
    (h : ∀ e : τ →₀ ℕ, e.degree < n → coeff e a = 0) : a ∈ ordIdeal τ R n :=
  nat_le_order fun e he => h e he

theorem mem_ordIdeal_iff_coeff {n : ℕ} {a : MvPowerSeries τ R} :
    a ∈ ordIdeal τ R n ↔ ∀ e : τ →₀ ℕ, e.degree < n → coeff e a = 0 :=
  ⟨fun ha _ he => coeff_eq_zero_of_mem_ordIdeal ha he, mem_ordIdeal_of_coeff⟩

theorem ordIdeal_antitone {m n : ℕ} (h : m ≤ n) : ordIdeal τ R n ≤ ordIdeal τ R m :=
  fun _ ha => le_trans (ENat.coe_le_coe.mpr h) ha

theorem mem_ordIdeal_zero (a : MvPowerSeries τ R) : a ∈ ordIdeal τ R 0 := by
  rw [mem_ordIdeal_iff, Nat.cast_zero]
  exact bot_le

theorem mem_ordIdeal_one_iff {a : MvPowerSeries τ R} :
    a ∈ ordIdeal τ R 1 ↔ a.constantCoeff = 0 := by
  rw [mem_ordIdeal_iff, Nat.cast_one]
  exact one_le_order_iff_constCoeff_eq_zero

theorem constantCoeff_eq_zero_of_mem_ordIdeal {n : ℕ} (hn : 1 ≤ n) {a : MvPowerSeries τ R}
    (ha : a ∈ ordIdeal τ R n) : a.constantCoeff = 0 :=
  mem_ordIdeal_one_iff.mp (ordIdeal_antitone hn ha)

theorem mul_mem_ordIdeal_add {m n : ℕ} {a b : MvPowerSeries τ R} (ha : a ∈ ordIdeal τ R m)
    (hb : b ∈ ordIdeal τ R n) : a * b ∈ ordIdeal τ R (m + n) := by
  rw [mem_ordIdeal_iff, Nat.cast_add]
  exact le_trans (add_le_add ha hb) le_order_mul

theorem pow_mem_ordIdeal_mul {n : ℕ} {a : MvPowerSeries τ R} (ha : a ∈ ordIdeal τ R n) (k : ℕ) :
    a ^ k ∈ ordIdeal τ R (k * n) := by
  induction k with
  | zero => rw [pow_zero, zero_mul]; exact mem_ordIdeal_zero _
  | succ k ih => rw [pow_succ, Nat.succ_mul]; exact mul_mem_ordIdeal_add ih ha

theorem finsuppProd_pow_mem_ordIdeal {n : ℕ} {c : σ → MvPowerSeries τ R}
    (hc : ∀ s, c s ∈ ordIdeal τ R n) (m : σ →₀ ℕ) :
    (m.prod fun s k => c s ^ k) ∈ ordIdeal τ R (m.degree * n) := by
  classical
  induction m using Finsupp.induction with
  | zero =>
    rw [Finsupp.prod_zero_index, map_zero, zero_mul]
    exact mem_ordIdeal_zero _
  | single_add s k m hs hk ih =>
    rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun s' k' => c s' ^ k') (pow_zero _), map_add,
      Finsupp.degree_single, Nat.add_mul]
    exact mul_mem_ordIdeal_add (pow_mem_ordIdeal_mul (hc s) k) ih

theorem subst_mem_ordIdeal {n : ℕ} {c : σ → MvPowerSeries τ R} (hc : HasSubst c)
    (hcn : ∀ s, c s ∈ ordIdeal τ R n) {g : MvPowerSeries σ R} (hg : g.constantCoeff = 0) :
    subst c g ∈ ordIdeal τ R n := by
  refine mem_ordIdeal_of_coeff fun e he => ?_
  rw [coeff_subst hc]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  by_cases hm : m = 0
  · subst hm
    rw [coeff_zero_eq_constantCoeff_apply, hg, zero_smul]
  · have hdeg : 0 < m.degree :=
      Nat.pos_of_ne_zero fun h0 => hm ((Finsupp.degree_eq_zero_iff m).mp h0)
    have hmem : (m.prod fun s k => c s ^ k) ∈ ordIdeal τ R n :=
      ordIdeal_antitone (Nat.le_mul_of_pos_left n hdeg) (finsuppProd_pow_mem_ordIdeal hcn m)
    rw [coeff_eq_zero_of_mem_ordIdeal hmem he, smul_zero]

theorem coeff_subst_eq_finsum_linear {n : ℕ} (hn : 1 ≤ n) {c : σ → MvPowerSeries τ R}
    (hc : HasSubst c) (hcn : ∀ s, c s ∈ ordIdeal τ R n) {g : MvPowerSeries σ R}
    (hg : g.constantCoeff = 0) {e : τ →₀ ℕ} (he : e.degree ≤ n) :
    coeff e (subst c g) = ∑ᶠ s, coeff (Finsupp.single s 1) g * coeff e (c s) := by
  classical
  rw [coeff_subst hc]
  set T : (σ →₀ ℕ) → R := fun m => coeff m g • coeff e (m.prod fun s k => c s ^ k) with hT

  have hvan : ∀ m : σ →₀ ℕ, m ∉ Set.range (fun s : σ => Finsupp.single s 1) → T m = 0 := by
    intro m hm
    by_cases h0 : m = 0
    · subst h0
      simp only [hT, coeff_zero_eq_constantCoeff_apply, hg, zero_smul]
    · have h2 : 2 ≤ m.degree := by
        by_contra hlt
        have h1 : m.degree = 1 := by
          have := Nat.pos_of_ne_zero fun h => h0 ((Finsupp.degree_eq_zero_iff m).mp h)
          omega
        have hmem : m ∈ {d : σ →₀ ℕ | d.degree = 1} := h1
        rw [← Finsupp.range_single_one] at hmem
        exact hm hmem
      have hle : n + 1 ≤ m.degree * n := by nlinarith
      have hmem := ordIdeal_antitone hle (finsuppProd_pow_mem_ordIdeal hcn m)
      simp only [hT]
      rw [coeff_eq_zero_of_mem_ordIdeal hmem (Nat.lt_succ_of_le he), smul_zero]
  have hsupp : Function.support T ⊆ Set.range (fun s : σ => Finsupp.single s 1) :=
    fun m hm => by_contra fun hnot => hm (hvan m hnot)
  calc ∑ᶠ m, T m = ∑ᶠ m ∈ Set.univ, T m := (finsum_mem_univ T).symm
    _ = ∑ᶠ m ∈ Set.range (fun s : σ => Finsupp.single s 1), T m :=
        finsum_mem_inter_support_eq T _ _ (by
          rw [Set.univ_inter, Set.inter_eq_right.mpr hsupp])
    _ = ∑ᶠ s, T (Finsupp.single s 1) :=
        finsum_mem_range (Finsupp.single_left_injective one_ne_zero)
    _ = ∑ᶠ s, coeff (Finsupp.single s 1) g * coeff e (c s) :=
        finsum_congr fun s => by
          simp only [hT]
          rw [Finsupp.prod_single_index (h := fun s' k' => c s' ^ k') (pow_zero _), pow_one,
            smul_eq_mul]

theorem hasFiniteSupport_linear {c : σ → MvPowerSeries τ R} (hc : HasSubst c)
    (g : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    Function.HasFiniteSupport fun s => coeff (Finsupp.single s 1) g * coeff e (c s) :=
  (hc.coeff_zero e).subset (Function.support_mul_subset_right _ _)

theorem coeff_subst_eq_sum_linear [Fintype σ] {n : ℕ} (hn : 1 ≤ n)
    {c : σ → MvPowerSeries τ R} (hc : HasSubst c) (hcn : ∀ s, c s ∈ ordIdeal τ R n)
    {g : MvPowerSeries σ R} (hg : g.constantCoeff = 0) {e : τ →₀ ℕ} (he : e.degree ≤ n) :
    coeff e (subst c g) = ∑ s, coeff (Finsupp.single s 1) g * coeff e (c s) := by
  rw [coeff_subst_eq_finsum_linear hn hc hcn hg he, finsum_eq_sum_of_fintype]

theorem subst_sub_add_mem_ordIdeal_succ {n : ℕ} (hn : 1 ≤ n) {c c₁ c₂ : σ → MvPowerSeries τ R}
    (hc : HasSubst c) (hc₁ : HasSubst c₁) (hc₂ : HasSubst c₂)
    (hcn : ∀ s, c s ∈ ordIdeal τ R n) (hc₁n : ∀ s, c₁ s ∈ ordIdeal τ R n)
    (hc₂n : ∀ s, c₂ s ∈ ordIdeal τ R n) (hsum : ∀ s, c s = c₁ s + c₂ s)
    {g : MvPowerSeries σ R} (hg : g.constantCoeff = 0) :
    subst c g - (subst c₁ g + subst c₂ g) ∈ ordIdeal τ R (n + 1) := by
  refine mem_ordIdeal_of_coeff fun e he => ?_
  have he' : e.degree ≤ n := Nat.lt_succ_iff.mp he
  rw [map_sub, map_add, coeff_subst_eq_finsum_linear hn hc hcn hg he',
    coeff_subst_eq_finsum_linear hn hc₁ hc₁n hg he', coeff_subst_eq_finsum_linear hn hc₂ hc₂n hg he',
    ← finsum_add_distrib (hasFiniteSupport_linear hc₁ g e) (hasFiniteSupport_linear hc₂ g e),
    sub_eq_zero]
  exact finsum_congr fun s => by rw [hsum s, map_add, mul_add]

theorem finite_setOf_degree_le [Finite τ] (n : ℕ) : {e : τ →₀ ℕ | e.degree ≤ n}.Finite :=
  Finsupp.finite_of_degree_le n

end PowerSeries

section SeriesPoint

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}
  {τ : Type*}

def PInI (n : ℕ) (a : SeriesPoint Φ τ) : Prop := ∀ j, a.val j ∈ ordIdeal τ R n

omit hp in
theorem PInI.mono {m n : ℕ} (h : m ≤ n) {a : SeriesPoint Φ τ} (ha : PInI n a) : PInI m a :=
  fun j => ordIdeal_antitone h (ha j)

omit hp in
theorem PInI.zero (n : ℕ) : PInI n (0 : SeriesPoint Φ τ) := fun j => by
  rw [SeriesPoint.val_zero]
  exact zero_mem _

omit hp in
theorem elim_mem {n : ℕ} {a b : Fin d → MvPowerSeries τ R} (ha : ∀ j, a j ∈ ordIdeal τ R n)
    (hb : ∀ j, b j ∈ ordIdeal τ R n) : ∀ s, Sum.elim a b s ∈ ordIdeal τ R n := by
  rintro (j | j)
  exacts [ha j, hb j]

omit hp in
theorem PInI.add {n : ℕ} {a b : SeriesPoint Φ τ} (ha : PInI n a) (hb : PInI n b) : PInI n (a + b) :=
  fun j => subst_mem_ordIdeal (hasSubst_elim a.constantCoeff_eq_zero b.constantCoeff_eq_zero)
    (elim_mem ha hb) (Φ.constantCoeff_eq_zero j)

omit hp in

theorem val_neg_eq_subst_invSeries (a : SeriesPoint Φ τ) (i : Fin d) :
    (-a).val i = subst a.val (invSeries Φ i) := by
  have h := subst_negSeries Φ (a := fun j : Fin d => (X j : MvPowerSeries (Fin d) R))
    (fun j => constantCoeff_X j) a.constantCoeff_eq_zero
  have hX : (fun i => subst a.val (X i : MvPowerSeries (Fin d) R)) = a.val :=
    funext fun i => subst_X a.hasSubst_val i
  rw [hX] at h
  rw [SeriesPoint.val_neg, ← h]
  rfl

omit hp in
theorem PInI.neg {n : ℕ} {a : SeriesPoint Φ τ} (ha : PInI n a) : PInI n (-a) := fun j => by
  rw [val_neg_eq_subst_invSeries]
  exact subst_mem_ordIdeal a.hasSubst_val ha (constantCoeff_invSeries Φ j)

omit hp in
theorem PInI.sub [Φ.IsComm] {n : ℕ} {a b : SeriesPoint Φ τ} (ha : PInI n a) (hb : PInI n b) :
    PInI n (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

omit hp in
theorem PInI.sum [Φ.IsComm] {n : ℕ} {ι : Type*} (s : Finset ι) {a : ι → SeriesPoint Φ τ}
    (ha : ∀ i ∈ s, PInI n (a i)) : PInI n (∑ i ∈ s, a i) :=
  Finset.sum_induction _ (PInI n) (fun _ _ hx hy => hx.add hy) (PInI.zero n) ha

omit hp in

theorem coeff_val_add_sub_mem {n : ℕ} (hn : 1 ≤ n) {a b : SeriesPoint Φ τ} (ha : PInI n a)
    (hb : PInI n b) (j : Fin d) : (a + b).val j - (a.val j + b.val j) ∈ ordIdeal τ R (n + 1) := by
  have hz0 : ∀ j : Fin d, ((fun _ : Fin d => (0 : MvPowerSeries τ R)) j).constantCoeff = 0 :=
    fun _ => map_zero _
  have hz : ∀ j : Fin d, (fun _ : Fin d => (0 : MvPowerSeries τ R)) j ∈ ordIdeal τ R n :=
    fun _ => zero_mem _
  have h := subst_sub_add_mem_ordIdeal_succ hn
    (hasSubst_elim a.constantCoeff_eq_zero b.constantCoeff_eq_zero)
    (hasSubst_elim a.constantCoeff_eq_zero hz0) (hasSubst_elim hz0 b.constantCoeff_eq_zero)
    (elim_mem ha hb) (elim_mem ha hz) (elim_mem hz hb)
    (by rintro (i | i); exacts [(add_zero _).symm, (zero_add _).symm]) (Φ.constantCoeff_eq_zero j)
  rwa [subst_elim_zero_right Φ a.constantCoeff_eq_zero j,
    subst_elim_zero_left Φ b.constantCoeff_eq_zero j] at h

end SeriesPoint

section LHom

open MvFormalGroup MvFormalGroup.CartierModule

variable {R : Type u} [CommRing R] {d : ℕ} (Φ : MvFormalGroup d R)

def IsLHom (G : Fin d → MvPowerSeries ℕ R) : Prop :=
  ∀ j, subst (BigWittLaw.addFam R) (G j) = subst (Sum.elim (inBlk 0 G) (inBlk 1 G)) (Φ.toPowerSeries j)

variable {Φ}

theorem isLHom_neg [Φ.IsComm] {G : Fin d → MvPowerSeries ℕ R} (hG0 : ∀ j, (G j).constantCoeff = 0)
    (hG : IsLHom Φ G) : IsLHom Φ (negSeries Φ G) := by
  intro j
  have hneg : ∀ j, (negSeries Φ G j).constantCoeff = 0 := constantCoeff_negSeries Φ _
  have hS : (fun l => subst (BigWittLaw.addFam R) (negSeries Φ G l)) =
      negSeries Φ fun l => subst (BigWittLaw.addFam R) (G l) := by
    have hA := BigWittLaw.hasSubst_addFam R
    have hA0 := BigWittLaw.constantCoeff_addFam R
    refine negSeries_unique Φ (fun l => constantCoeff_subst_eq_zero hA hA0 (hG0 l))
      (fun l => constantCoeff_subst_eq_zero hA hA0 (hneg l)) fun i => ?_
    rw [← subst_subst_elim Φ hG0 hneg hA i, subst_elim_negSeries Φ hG0 i, ← coe_substAlgHom hA,
      map_zero]
  have h1 := congrFun hS j
  rw [h1]
  have hfeq : (fun l => subst (BigWittLaw.addFam R) (G l)) =
      fun l => subst (Sum.elim (inBlk 0 G) (inBlk 1 G)) (Φ.toPowerSeries l) := funext hG
  rw [hfeq, negSeries_elim_add Φ (constantCoeff_inBlk 0 hG0) (constantCoeff_inBlk 1 hG0),
    ← inBlk_negSeries Φ 0 hG0, ← inBlk_negSeries Φ 1 hG0]

theorem isLHom_add [Φ.IsComm] {G H : Fin d → MvPowerSeries ℕ R} (hG0 : ∀ j, (G j).constantCoeff = 0)
    (hH0 : ∀ j, (H j).constantCoeff = 0) (hG : IsLHom Φ G) (hH : IsLHom Φ H) :
    IsLHom Φ (fun j => subst (Sum.elim G H) (Φ.toPowerSeries j)) := by
  intro j
  show subst (BigWittLaw.addFam R) (subst (Sum.elim G H) (Φ.toPowerSeries j)) =
    subst (Sum.elim (inBlk 0 fun l => subst (Sum.elim G H) (Φ.toPowerSeries l))
      (inBlk 1 fun l => subst (Sum.elim G H) (Φ.toPowerSeries l))) (Φ.toPowerSeries j)
  rw [subst_subst_elim Φ hG0 hH0 (BigWittLaw.hasSubst_addFam R) j, inBlk_subst_elim Φ 0 hG0 hH0,
    inBlk_subst_elim Φ 1 hG0 hH0]
  have hfeq : (fun l => subst (BigWittLaw.addFam R) (G l)) =
      fun l => subst (Sum.elim (inBlk 0 G) (inBlk 1 G)) (Φ.toPowerSeries l) := funext hG
  have hgeq : (fun l => subst (BigWittLaw.addFam R) (H l)) =
      fun l => subst (Sum.elim (inBlk 0 H) (inBlk 1 H)) (Φ.toPowerSeries l) := funext hH
  rw [hfeq, hgeq]
  exact subst_elim_exchange Φ (constantCoeff_inBlk 0 hG0) (constantCoeff_inBlk 1 hG0)
    (constantCoeff_inBlk 0 hH0) (constantCoeff_inBlk 1 hH0) j

def omega : ℕ → PowerSeries R := fun m => (PowerSeries.X : PowerSeries R) ^ (m + 1)

theorem constantCoeff_omega (m : ℕ) : MvPowerSeries.constantCoeff (omega (R := R) m) = 0 := by
  simp only [omega]
  rw [map_pow]
  simp [PowerSeries.X]

theorem hasSubst_omega : HasSubst (omega (R := R)) := by
  refine ⟨fun m => by rw [constantCoeff_omega]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_le_nat (e ())).subset fun m hm => ?_
  by_contra hlt
  apply hm
  simp only [Set.mem_setOf_eq, not_le] at hlt
  show MvPowerSeries.coeff e ((PowerSeries.X : PowerSeries R) ^ (m + 1)) = 0
  rw [Finsupp.unique_single e]
  change PowerSeries.coeff (e ()) ((PowerSeries.X : PowerSeries R) ^ (m + 1)) = 0
  rw [PowerSeries.coeff_X_pow, if_neg]
  change ¬ e () = m + 1
  omega

theorem omega_negSeries {H : Fin d → MvPowerSeries ℕ R} (hH0 : ∀ j, (H j).constantCoeff = 0) :
    (fun i => subst omega (negSeries Φ H i)) = negSeries Φ fun i => subst (omega (R := R)) (H i) := by
  have hb := hasSubst_omega (R := R)
  have hneg : ∀ j, (negSeries Φ H j).constantCoeff = 0 := constantCoeff_negSeries Φ H
  refine negSeries_unique Φ (fun j => constantCoeff_subst_eq_zero hb constantCoeff_omega (hH0 j))
    (fun j => constantCoeff_subst_eq_zero hb constantCoeff_omega (hneg j)) fun i => ?_
  rw [← subst_subst_elim Φ hH0 hneg hb i, subst_elim_negSeries Φ hH0 i, ← coe_substAlgHom hb, map_zero]

theorem mem_ordIdeal_of_powerSeries_coeff {n : ℕ} {f : PowerSeries R}
    (h : ∀ k, k < n → PowerSeries.coeff k f = 0) : f ∈ ordIdeal Unit R n := by
  refine mem_ordIdeal_of_coeff fun e he => ?_
  have hdeg : e.degree = e () := by
    rw [show e.degree = (Finsupp.single () (e ())).degree from congrArg _ (Finsupp.unique_single e),
      Finsupp.degree_single]
  rw [Finsupp.unique_single e]
  change PowerSeries.coeff (e ()) f = 0
  exact h _ (by change e () < n; omega)

theorem powerSeries_coeff_eq_zero_of_mem_ordIdeal {n : ℕ} {f : PowerSeries R} (hf : f ∈ ordIdeal Unit R n)
    (k : ℕ) (hk : k < n) : PowerSeries.coeff k f = 0 := by
  change MvPowerSeries.coeff (Finsupp.single () k) f = 0
  exact coeff_eq_zero_of_mem_ordIdeal hf (by rw [Finsupp.degree_single]; exact hk)

end LHom

end P2mK1c

end

open MvPowerSeries MvFormalGroup MvFormalGroup.CartierModule P2mK1c in
theorem solution
    {R : Type u} [CommRing R] {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (G H : Fin d → MvPowerSeries ℕ R)
    (hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0)
    (hG : ∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (G j) =
      MvPowerSeries.subst
        (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
          fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        (Φ.toPowerSeries j))
    (hH0 : ∀ j, MvPowerSeries.constantCoeff (H j) = 0)
    (hH : ∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (H j) =
      MvPowerSeries.subst
        (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (H l))
          fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (H l))
        (Φ.toPowerSeries j))
    (n : ℕ) (hn : 1 ≤ n)
    (hGn : ∀ (j : Fin d) (k : ℕ), k < n →
      PowerSeries.coeff k (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j)) = 0)
    (hHn : ∀ (j : Fin d) (k : ℕ), k < n →
      PowerSeries.coeff k (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (H j)) = 0)
    (hGH : ∀ j : Fin d,
      PowerSeries.coeff n (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j))
        = PowerSeries.coeff n (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (H j))) :
    (∀ j, MvPowerSeries.constantCoeff
        (MvPowerSeries.subst (Sum.elim G (MvFormalGroup.negSeries Φ H)) (Φ.toPowerSeries j)) = 0) ∧
    (∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R)
        (MvPowerSeries.subst (Sum.elim G (MvFormalGroup.negSeries Φ H)) (Φ.toPowerSeries j)) =
      MvPowerSeries.subst
        (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R))
            (MvPowerSeries.subst (Sum.elim G (MvFormalGroup.negSeries Φ H)) (Φ.toPowerSeries l)))
          fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R))
            (MvPowerSeries.subst (Sum.elim G (MvFormalGroup.negSeries Φ H)) (Φ.toPowerSeries l)))
        (Φ.toPowerSeries j)) ∧
    (∀ (j : Fin d) (k : ℕ), k < n + 1 →
      PowerSeries.coeff k (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1))
        (MvPowerSeries.subst (Sum.elim G (MvFormalGroup.negSeries Φ H)) (Φ.toPowerSeries j))) = 0) := by
  classical
  have hN0 : ∀ j, (MvFormalGroup.negSeries Φ H j).constantCoeff = 0 := constantCoeff_negSeries Φ H

  refine ⟨fun j => constantCoeff_subst_elim Φ hG0 hN0 j, ?_, ?_⟩

  · have hGL : IsLHom Φ G := hG
    have hHL : IsLHom Φ H := hH
    exact isLHom_add hG0 hN0 hGL (isLHom_neg hH0 hHL)

  · intro j k hk

    set γG : SeriesPoint Φ Unit := ⟨fun l => subst omega (G l), fun l =>
      constantCoeff_subst_eq_zero hasSubst_omega constantCoeff_omega (hG0 l)⟩ with hγG
    set γH : SeriesPoint Φ Unit := ⟨fun l => subst omega (H l), fun l =>
      constantCoeff_subst_eq_zero hasSubst_omega constantCoeff_omega (hH0 l)⟩ with hγH
    have hcurve : subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1))
        (subst (Sum.elim G (MvFormalGroup.negSeries Φ H)) (Φ.toPowerSeries j)) = (γG - γH).val j := by
      change subst omega (subst (Sum.elim G (MvFormalGroup.negSeries Φ H)) (Φ.toPowerSeries j)) = _
      rw [subst_subst_elim Φ hG0 hN0 hasSubst_omega j, SeriesPoint.val_sub]
      congr 2
      exact omega_negSeries hH0
    rw [hcurve]
    have hGI : PInI n γG := fun l => mem_ordIdeal_of_powerSeries_coeff (hGn l)
    have hHI : PInI n γH := fun l => mem_ordIdeal_of_powerSeries_coeff (hHn l)

    have h1 := coeff_val_add_sub_mem hn hGI hHI.neg j
    have h2 : (-γH).val j + γH.val j ∈ ordIdeal Unit R (n + 1) := by
      have h := coeff_val_add_sub_mem hn hHI.neg hHI j
      rw [neg_add_cancel, SeriesPoint.val_zero] at h
      simpa using neg_mem h
    have h3 : γG.val j - γH.val j ∈ ordIdeal Unit R (n + 1) := by
      change subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j) -
        subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (H j) ∈ ordIdeal Unit R (n + 1)
      refine mem_ordIdeal_of_powerSeries_coeff fun k hk => ?_
      rw [map_sub]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [hGn j k hk, hHn j k hk, sub_zero]
      · rw [sub_eq_zero]; exact hGH j
    have : (γG - γH).val j = ((γG + -γH).val j - (γG.val j + (-γH).val j)) +
        ((-γH).val j + γH.val j) + (γG.val j - γH.val j) := by
      rw [sub_eq_add_neg γG γH]; ring
    rw [this]
    exact powerSeries_coeff_eq_zero_of_mem_ordIdeal (add_mem (add_mem h1 h2) h3) k hk

end S_MvFormalGroup_BigWittLaw_subst_elim_negSeries_hom_and_coeff_eq_zero
end P2MW
export P2MW.S_MvFormalGroup_BigWittLaw_subst_elim_negSeries_hom_and_coeff_eq_zero (solution)
