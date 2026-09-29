-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_forall_le_order_coeff_sub_of_forall_le_order_presPi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/56e2d3ae-429b-5ca2-b142-d20ce518d904

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_WittPointFamily
import Theorems.Thm_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_teichPt_frobPt_eq_presPi_frobPt_iterate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_of_forall_le_order_presPi

set_option autoImplicit false

universe u v

noncomputable section

namespace P2mKcKappaTwo

open MvPowerSeries

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

section Witt

open MvFormalGroup

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] {τ : Type*}

def wmap (p : ℕ) [Fact p.Prime] (τ : Type*) (R : Type*) [CommRing R] (n : ℕ) :
    WittVector p (MvPowerSeries τ R) →+* WittVector p (MvPowerSeries τ R ⧸ ordIdeal τ R n) :=
  WittVector.map (Ideal.Quotient.mk (ordIdeal τ R n))

theorem wmap_eq_iff {n : ℕ} {x y : WittVector p (MvPowerSeries τ R)} :
    wmap p τ R n x = wmap p τ R n y ↔ ∀ k, x.coeff k - y.coeff k ∈ ordIdeal τ R n := by
  simp only [wmap, WittVector.ext_iff, WittVector.map_coeff, Ideal.Quotient.eq]

theorem wmap_eq_zero_iff {n : ℕ} {x : WittVector p (MvPowerSeries τ R)} :
    wmap p τ R n x = 0 ↔ ∀ k, x.coeff k ∈ ordIdeal τ R n := by
  simp only [wmap, WittVector.ext_iff, WittVector.map_coeff, WittVector.zero_coeff,
    Ideal.Quotient.eq_zero_iff_mem]

def InI (n : ℕ) (x : WittLaw.seriesPoint p R τ) : Prop :=
  ∀ k, (x : WittVector p (MvPowerSeries τ R)).coeff k ∈ ordIdeal τ R n

theorem inI_iff_wmap_eq_zero {n : ℕ} {x : WittLaw.seriesPoint p R τ} :
    InI n x ↔ wmap p τ R n (x : WittVector p (MvPowerSeries τ R)) = 0 :=
  wmap_eq_zero_iff.symm

theorem InI.mono {m n : ℕ} (h : m ≤ n) {x : WittLaw.seriesPoint p R τ} (hx : InI n x) : InI m x :=
  fun k => ordIdeal_antitone h (hx k)

theorem inI_one (x : WittLaw.seriesPoint p R τ) : InI 1 x :=
  fun k => mem_ordIdeal_one_iff.mpr (WittLaw.constantCoeff_coeff x k)

theorem InI.zero (n : ℕ) : InI n (0 : WittLaw.seriesPoint p R τ) := fun k => by
  rw [ZeroMemClass.coe_zero, WittVector.zero_coeff]
  exact zero_mem _

theorem pairSeries_mem {n : ℕ} {a b : ℕ → MvPowerSeries τ R} (ha : ∀ m, a m ∈ ordIdeal τ R n)
    (hb : ∀ m, b m ∈ ordIdeal τ R n) : ∀ s, WittLaw.pairSeries a b s ∈ ordIdeal τ R n :=
  fun ⟨i, m⟩ => Fin.cases (ha m) (fun _ => hb m) i

theorem InI.add {n : ℕ} {x y : WittLaw.seriesPoint p R τ} (hx : InI n x) (hy : InI n y) :
    InI n (x + y) := fun k => by
  rw [WittLaw.coe_add_coeff]
  exact subst_mem_ordIdeal (WittLaw.hasSubst_pairSeries (WittLaw.hasSubst_coeff x)
    (WittLaw.hasSubst_coeff y)) (pairSeries_mem hx hy) (WittLaw.constantCoeff_addFam p R k)

theorem InI.wittSMulPt {n : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : InI n x) (w : WittVector p R) :
    InI n (WittLaw.wittSMulPt w x) := fun k => by
  rw [WittLaw.coeff_wittSMulPt]
  exact subst_mem_ordIdeal (WittLaw.hasSubst_coeff x) hx (WittLaw.constantCoeff_mulFam w k)

theorem InI.teichPt {n : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : InI n x) (c : R) :
    InI n (WittLaw.teichPt c x) :=
  hx.wittSMulPt _

theorem neg_eq_wittSMulPt (x : WittLaw.seriesPoint p R τ) :
    -x = WittLaw.wittSMulPt (-1 : WittVector p R) x :=
  Subtype.ext (by rw [AddSubgroup.coe_neg, WittLaw.coe_wittSMulPt, map_neg, map_one, neg_one_mul])

theorem InI.neg {n : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : InI n x) : InI n (-x) := by
  rw [neg_eq_wittSMulPt]
  exact hx.wittSMulPt _

theorem InI.sub {n : ℕ} {x y : WittLaw.seriesPoint p R τ} (hx : InI n x) (hy : InI n y) :
    InI n (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem InI.sum {n : ℕ} {ι : Type*} (s : Finset ι) {x : ι → WittLaw.seriesPoint p R τ}
    (hx : ∀ i ∈ s, InI n (x i)) : InI n (∑ i ∈ s, x i) :=
  Finset.sum_induction _ (InI n) (fun _ _ ha hb => ha.add hb) (InI.zero n) hx

theorem InI.verPt {n : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : InI n x) : InI n (WittLaw.verPt x) := by
  intro k
  cases k with
  | zero => rw [WittLaw.coeff_verPt_zero]; exact zero_mem _
  | succ k => rw [WittLaw.coeff_verPt_succ]; exact hx k

theorem InI.frobPt_iterate [CharP R p] {n : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : InI n x)
    (m : ℕ) : InI (p ^ m * n) ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] x) := fun k => by
  rw [WittLaw.coeff_frobPt_iterate]
  exact pow_mem_ordIdeal_mul (hx k) _

theorem InI.frobPt_iterate' [CharP R p] {n : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : InI n x)
    (m : ℕ) : InI n ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] x) :=
  (hx.frobPt_iterate m).mono (Nat.le_mul_of_pos_left n (pow_pos hp.out.pos m))

theorem InI.frobPt_iterate_succ [CharP R p] {n : ℕ} (hn : 1 ≤ n) {x : WittLaw.seriesPoint p R τ}
    (hx : InI n x) {m : ℕ} (hm : m ≠ 0) :
    InI (n + 1) ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] x) := by
  refine (hx.frobPt_iterate m).mono ?_
  have h2 : 2 ≤ p ^ m := le_trans hp.out.two_le (Nat.le_self_pow hm p)
  nlinarith

theorem coeff_add_sub_mem {n : ℕ} (hn : 1 ≤ n) {x y : WittLaw.seriesPoint p R τ} (hx : InI n x)
    (hy : InI n y) (k : ℕ) :
    ((x + y : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k -
      ((x : WittVector p (MvPowerSeries τ R)).coeff k + (y : WittVector p (MvPowerSeries τ R)).coeff k)
        ∈ ordIdeal τ R (n + 1) := by
  have h0 : (fun m => ((0 : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff m) =
      fun _ => (0 : MvPowerSeries τ R) := by
    funext m
    rw [ZeroMemClass.coe_zero, WittVector.zero_coeff]
  have hx0 : (x : WittVector p (MvPowerSeries τ R)).coeff k =
      subst (WittLaw.pairSeries (fun m => (x : WittVector p (MvPowerSeries τ R)).coeff m)
        fun _ => 0) (WittLaw.addFam p R k) := by
    have h := WittLaw.coe_add_coeff x 0 k
    rw [add_zero, h0] at h
    exact h
  have hy0 : (y : WittVector p (MvPowerSeries τ R)).coeff k =
      subst (WittLaw.pairSeries (fun _ => 0)
        fun m => (y : WittVector p (MvPowerSeries τ R)).coeff m) (WittLaw.addFam p R k) := by
    have h := WittLaw.coe_add_coeff 0 y k
    rw [zero_add, h0] at h
    exact h
  have hz : ∀ m : ℕ, (0 : MvPowerSeries τ R) ∈ ordIdeal τ R n := fun _ => zero_mem _
  have hZ : HasSubst (fun _ : ℕ => (0 : MvPowerSeries τ R)) := HasSubst.zero
  rw [WittLaw.coe_add_coeff, hx0, hy0]
  refine subst_sub_add_mem_ordIdeal_succ hn
    (WittLaw.hasSubst_pairSeries (WittLaw.hasSubst_coeff x) (WittLaw.hasSubst_coeff y))
    (WittLaw.hasSubst_pairSeries (WittLaw.hasSubst_coeff x) hZ)
    (WittLaw.hasSubst_pairSeries hZ (WittLaw.hasSubst_coeff y))
    (pairSeries_mem hx hy) (pairSeries_mem hx hz) (pairSeries_mem hz hy) ?_
    (WittLaw.constantCoeff_addFam p R k)
  rintro ⟨i, m⟩
  refine Fin.cases ?_ (fun _ => ?_) i
  · exact (add_zero _).symm
  · exact (zero_add _).symm

theorem coeff_neg_add_mem {n : ℕ} (hn : 1 ≤ n) {x : WittLaw.seriesPoint p R τ} (hx : InI n x)
    (k : ℕ) :
    ((-x : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k +
      (x : WittVector p (MvPowerSeries τ R)).coeff k ∈ ordIdeal τ R (n + 1) := by
  have h := coeff_add_sub_mem hn hx hx.neg k
  rw [add_neg_cancel, ZeroMemClass.coe_zero, WittVector.zero_coeff, zero_sub, neg_mem_iff,
    add_comm ((x : WittVector p (MvPowerSeries τ R)).coeff k)] at h
  exact h

theorem coeff_sub_sub_mem {n : ℕ} (hn : 1 ≤ n) {x y : WittLaw.seriesPoint p R τ} (hx : InI n x)
    (hy : InI n y) (k : ℕ) :
    ((x - y : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k -
      ((x : WittVector p (MvPowerSeries τ R)).coeff k - (y : WittVector p (MvPowerSeries τ R)).coeff k)
        ∈ ordIdeal τ R (n + 1) := by
  have h1 := coeff_add_sub_mem hn hx hy.neg k
  have h2 := coeff_neg_add_mem hn hy k
  have h := add_mem h1 h2
  rw [sub_eq_add_neg x y]
  convert h using 1
  ring

theorem coeff_sum_sub_mem {n : ℕ} (hn : 1 ≤ n) {ι : Type*} (s : Finset ι)
    (x : ι → WittLaw.seriesPoint p R τ) (hx : ∀ i ∈ s, InI n (x i)) (k : ℕ) :
    ((∑ i ∈ s, x i : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k -
      ∑ i ∈ s, (x i : WittVector p (MvPowerSeries τ R)).coeff k ∈ ordIdeal τ R (n + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, ZeroMemClass.coe_zero, WittVector.zero_coeff, sub_zero]
    exact zero_mem _
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, InI n (x i) := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have h1 := coeff_add_sub_mem hn (hx a (Finset.mem_insert_self a s)) (InI.sum s hs) k
    have h := add_mem h1 (ih hs)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    convert h using 1
    ring

end Witt

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

omit hp in

theorem coeff_val_sum_sub_mem [Φ.IsComm] {n : ℕ} (hn : 1 ≤ n) {ι : Type*} (s : Finset ι)
    (a : ι → SeriesPoint Φ τ) (ha : ∀ i ∈ s, PInI n (a i)) (j : Fin d) :
    (∑ i ∈ s, a i).val j - ∑ i ∈ s, (a i).val j ∈ ordIdeal τ R (n + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, SeriesPoint.val_zero, sub_zero]
    exact zero_mem _
  | insert i s hi ih =>
    have hs : ∀ i ∈ s, PInI n (a i) := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have h1 := coeff_val_add_sub_mem hn (ha i (Finset.mem_insert_self i s)) (PInI.sum s hs) j
    have h := add_mem h1 (ih hs)
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    convert h using 1
    ring

theorem PInI.evalPt [Φ.IsComm] {n : ℕ} (g : CartierModule p Φ) {w : WittLaw.seriesPoint p R τ}
    (hw : InI n w) : PInI n (evalPt g w) :=
  fun j => subst_mem_ordIdeal (WittLaw.hasSubst_coeff w) hw (g.constantCoeff_eq_zero j)

theorem PInI.presPi [Φ.IsComm] {n : ℕ} {ι : Type*} [Fintype ι] (f : ι → CartierModule p Φ)
    {w : ι → WittLaw.seriesPoint p R τ} (hw : ∀ l, InI n (w l)) : PInI n (presPi f w) :=
  PInI.sum _ fun l _ => PInI.evalPt (f l) (hw l)

theorem coeff_val_presPi [Φ.IsComm] {n : ℕ} (hn : 1 ≤ n) {ι : Type*} [Fintype ι]
    (f : ι → CartierModule p Φ) {w : ι → WittLaw.seriesPoint p R τ} (hw : ∀ l, InI n (w l))
    (j : Fin d) {e : τ →₀ ℕ} (he : e.degree ≤ n) :
    coeff e ((presPi f w).val j) = ∑ l, ∑ᶠ k, coeff (Finsupp.single k 1) ((f l).toPowerSeries j) *
      coeff e ((w l : WittVector p (MvPowerSeries τ R)).coeff k) := by
  have hsum := coeff_val_sum_sub_mem hn Finset.univ (fun l => evalPt (f l) (w l))
    (fun l _ => PInI.evalPt (f l) (hw l)) j
  have h0 := coeff_eq_zero_of_mem_ordIdeal hsum (Nat.lt_succ_of_le he)
  rw [map_sub, sub_eq_zero, map_sum] at h0
  rw [presPi_def, h0]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact coeff_subst_eq_finsum_linear hn (WittLaw.hasSubst_coeff (w l)) (hw l)
    ((f l).constantCoeff_eq_zero j) he

end SeriesPoint

section Tangent

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}

theorem coeff_single_toPowerSeries [Φ.IsComm] (g : CartierModule p Φ) (k : ℕ) (j : Fin d) :
    coeff (Finsupp.single k 1) (g.toPowerSeries j) =
      tangent ((⇑(frobenius (p := p) (Φ := Φ)))^[k] g) j := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ← ih (frobenius g), toPowerSeries_frobenius]
    change _ = coeff (Finsupp.single k 1) (subst (WittLaw.verFam R) (g.toPowerSeries j))
    rw [coeff_subst_eq_finsum_linear (n := 1) le_rfl WittLaw.hasSubst_verFam
      (fun s => mem_ordIdeal_one_iff.mpr (WittLaw.constantCoeff_verFam s)) (g.constantCoeff_eq_zero j)
      (by rw [Finsupp.degree_single]),
      finsum_eq_single _ (k + 1) (fun s hs => ?_)]
    · rw [WittLaw.verFam_succ, coeff_X, if_pos rfl, mul_one]
    · cases s with
      | zero => rw [WittLaw.verFam_zero, map_zero, mul_zero]
      | succ s =>
        rw [WittLaw.verFam_succ, coeff_X, if_neg, mul_zero]
        intro h
        exact hs (by rw [Finsupp.single_left_injective one_ne_zero h])

theorem frobenius_iterate_homothety [Φ.IsComm] (a : R) (g : CartierModule p Φ) (k : ℕ) :
    (⇑(frobenius (p := p) (Φ := Φ)))^[k] (homothety a g) =
      homothety (a ^ p ^ k) ((⇑(frobenius (p := p) (Φ := Φ)))^[k] g) := by
  induction k generalizing a g with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply, pow_zero, pow_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply, frobenius_homothety, ih, Function.iterate_succ_apply, ← pow_mul,
      pow_succ']

theorem frobenius_iterate_map_add [Φ.IsComm] (x y : CartierModule p Φ) (k : ℕ) :
    (⇑(frobenius (p := p) (Φ := Φ)))^[k] (x + y) =
      (⇑(frobenius (p := p) (Φ := Φ)))^[k] x + (⇑(frobenius (p := p) (Φ := Φ)))^[k] y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_add, ih]; rfl

theorem frobenius_iterate_map_sum [Φ.IsComm] {ι : Type*} (s : Finset ι) (x : ι → CartierModule p Φ)
    (k : ℕ) :
    (⇑(frobenius (p := p) (Φ := Φ)))^[k] (∑ i ∈ s, x i) =
      ∑ i ∈ s, (⇑(frobenius (p := p) (Φ := Φ)))^[k] (x i) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply, map_sum, ih]

theorem tangent_verschiebung_iterate [Φ.IsComm] [CharP R p] {m : ℕ} (hm : m ≠ 0)
    (g : CartierModule p Φ) :
    tangent ((⇑(verschiebung (p := p) (Φ := Φ)))^[m] g) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [Function.iterate_succ_apply']
  exact tangent_verschiebung _

theorem tangent_frobenius_iterate_succ [Φ.IsComm] [CharP R p] (f : Fin d → CartierModule p Φ)
    {N : ℕ} (hN : 0 < N) (c : Fin N → Fin d → Fin d → R) (h : Fin d → CartierModule p Φ)
    (hexp : ∀ i, frobenius (f i) =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Φ)))^[m] (∑ l : Fin d, homothety (c m i l) (f l))) +
        (⇑(verschiebung (p := p) (Φ := Φ)))^[N] (h i))
    (k : ℕ) (i j : Fin d) :
    tangent ((⇑(frobenius (p := p) (Φ := Φ)))^[k + 1] (f i)) j =
      ∑ l, c ⟨0, hN⟩ i l ^ p ^ k * tangent ((⇑(frobenius (p := p) (Φ := Φ)))^[k] (f l)) j := by
  have hcomm : Function.Commute (⇑(frobenius (p := p) (Φ := Φ))) (⇑(verschiebung (p := p) (Φ := Φ))) :=
    fun g => frobenius_verschiebung g
  rw [Function.iterate_succ_apply, hexp i, frobenius_iterate_map_add, frobenius_iterate_map_sum,
    map_add, map_sum, (hcomm.iterate_iterate k N) (h i),
    tangent_verschiebung_iterate (Nat.pos_iff_ne_zero.mp hN), add_zero,
    Finset.sum_eq_single (⟨0, hN⟩ : Fin N), Function.iterate_zero_apply, frobenius_iterate_map_sum,
    map_sum, Finset.sum_apply]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [frobenius_iterate_homothety, tangent_homothety, Pi.smul_apply, smul_eq_mul]
  · intro m _ hm
    have hm0 : (m : ℕ) ≠ 0 := fun h0 => hm (Fin.ext h0)
    rw [(hcomm.iterate_iterate k m) _, tangent_verschiebung_iterate hm0]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

end Tangent

section Algebra

theorem telescope {R : Type*} [CommRing R] {d : ℕ} (p K : ℕ) (T : ℕ → Fin d → Fin d → R)
    (c₀ : Fin d → Fin d → R) (X U : ℕ → Fin d → R)
    (hT0 : ∀ l j, T 0 l j = if l = j then 1 else 0)
    (hT : ∀ k i j, T (k + 1) i j = ∑ l, c₀ i l ^ p ^ k * T k l j)
    (hUK : ∀ l, U K l = 0)
    (hrec : ∀ k l, X (k + 1) l = U k l - ∑ i, c₀ i l ^ p ^ (k + 1) * U (k + 1) i)
    (j : Fin d) (hPi : ∑ l, ∑ k ∈ Finset.range (K + 1), T k l j * X k l = 0) :
    X 0 j = -∑ l, c₀ l j * U 0 l := by
  set A : ℕ → R := fun k => ∑ l, T (k + 1) l j * U k l with hA
  have hstep : ∀ k, ∑ l, T (k + 1) l j * X (k + 1) l = A k - A (k + 1) := by
    intro k
    simp only [hA, hrec, mul_sub, Finset.sum_sub_distrib]
    congr 1
    simp only [Finset.mul_sum, hT (k + 1), Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have h0 : ∑ l, T 0 l j * X 0 l = X 0 j := by
    simp only [hT0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hA0 : A 0 = ∑ l, c₀ l j * U 0 l := by
    simp only [hA, hT 0, pow_zero, pow_one, hT0, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hAK : A K = 0 := by
    simp only [hA, hUK, mul_zero, Finset.sum_const_zero]
  have key : ∑ l, ∑ k ∈ Finset.range (K + 1), T k l j * X k l = X 0 j + (A 0 - A K) := by
    simp only [Finset.sum_range_succ' _ K]
    rw [Finset.sum_add_distrib, h0, Finset.sum_comm, Finset.sum_congr rfl fun k _ => hstep k,
      Finset.sum_range_sub', add_comm]
  rw [key, hAK, sub_zero, hA0] at hPi
  exact eq_neg_of_add_eq_zero_left hPi

variable {R : Type*} [CommRing R] {τ : Type*}

def IsHomog (n : ℕ) (a : MvPowerSeries τ R) : Prop := ∀ e : τ →₀ ℕ, e.degree ≠ n → coeff e a = 0

theorem isHomog_homogeneousComponent (n : ℕ) (a : MvPowerSeries τ R) :
    IsHomog n (homogeneousComponent n a) := fun e he => by
  rw [coeff_homogeneousComponent, if_neg he]

theorem IsHomog.zero (n : ℕ) : IsHomog n (0 : MvPowerSeries τ R) := fun _ _ => map_zero _

theorem IsHomog.add {n : ℕ} {a b : MvPowerSeries τ R} (ha : IsHomog n a) (hb : IsHomog n b) :
    IsHomog n (a + b) := fun e he => by rw [map_add, ha e he, hb e he, add_zero]

theorem IsHomog.smul {n : ℕ} {a : MvPowerSeries τ R} (ha : IsHomog n a) (r : R) : IsHomog n (r • a) :=
  fun e he => by rw [map_smul, ha e he, smul_zero]

theorem IsHomog.neg {n : ℕ} {a : MvPowerSeries τ R} (ha : IsHomog n a) : IsHomog n (-a) :=
  fun e he => by rw [map_neg, ha e he, neg_zero]

theorem IsHomog.sum {n : ℕ} {ι : Type*} (s : Finset ι) {a : ι → MvPowerSeries τ R}
    (ha : ∀ i ∈ s, IsHomog n (a i)) : IsHomog n (∑ i ∈ s, a i) :=
  Finset.sum_induction _ (IsHomog n) (fun _ _ hx hy => hx.add hy) (IsHomog.zero n) ha

theorem IsHomog.mem_ordIdeal {n : ℕ} {a : MvPowerSeries τ R} (ha : IsHomog n a) : a ∈ ordIdeal τ R n :=
  mem_ordIdeal_of_coeff fun e he => ha e he.ne

theorem IsHomog.constantCoeff {n : ℕ} (hn : 1 ≤ n) {a : MvPowerSeries τ R} (ha : IsHomog n a) :
    a.constantCoeff = 0 :=
  constantCoeff_eq_zero_of_mem_ordIdeal hn ha.mem_ordIdeal

theorem IsHomog.ext {n : ℕ} {a b : MvPowerSeries τ R} (ha : IsHomog n a) (hb : IsHomog n b)
    (h : ∀ e : τ →₀ ℕ, e.degree = n → coeff e a = coeff e b) : a = b := by
  ext e
  by_cases he : e.degree = n
  · exact h e he
  · rw [ha e he, hb e he]

variable {d : ℕ}

def Gseq (p : ℕ) (x : Fin d → ℕ → MvPowerSeries τ R) (c₀ : Fin d → Fin d → R) (K : ℕ) :
    ℕ → Fin d → MvPowerSeries τ R
  | 0 => fun _ => 0
  | j + 1 => fun l => x l (K - j) + ∑ i, c₀ i l ^ p ^ (K - j) • Gseq p x c₀ K j i

theorem gseq_zero (p : ℕ) (x : Fin d → ℕ → MvPowerSeries τ R) (c₀ : Fin d → Fin d → R) (K : ℕ) :
    Gseq p x c₀ K 0 = fun _ => 0 := rfl

theorem gseq_succ (p : ℕ) (x : Fin d → ℕ → MvPowerSeries τ R) (c₀ : Fin d → Fin d → R) (K j : ℕ) :
    Gseq p x c₀ K (j + 1) = fun l => x l (K - j) + ∑ i, c₀ i l ^ p ^ (K - j) • Gseq p x c₀ K j i := rfl

theorem isHomog_gseq {n : ℕ} (p : ℕ) {x : Fin d → ℕ → MvPowerSeries τ R} (hx : ∀ l k, IsHomog n (x l k))
    (c₀ : Fin d → Fin d → R) (K : ℕ) : ∀ j l, IsHomog n (Gseq p x c₀ K j l) := by
  intro j
  induction j with
  | zero => intro l; exact IsHomog.zero n
  | succ j ih =>
    intro l
    rw [gseq_succ]
    exact (hx l _).add (IsHomog.sum _ fun i _ => (ih i).smul _)

theorem gseq_rec (p : ℕ) {x : Fin d → ℕ → MvPowerSeries τ R} (c₀ : Fin d → Fin d → R) {K : ℕ}
    (hxK : ∀ l k, K ≤ k → x l k = 0) (k : ℕ) (l : Fin d) :
    Gseq p x c₀ K (K - k) l =
      x l (k + 1) + ∑ i, c₀ i l ^ p ^ (k + 1) • Gseq p x c₀ K (K - (k + 1)) i := by
  rcases Nat.lt_or_ge k K with hk | hk
  · have h1 : K - k = (K - (k + 1)) + 1 := by omega
    have h2 : K - (K - (k + 1)) = k + 1 := by omega
    rw [h1, gseq_succ, h2]
  · have h1 : K - k = 0 := by omega
    have h2 : K - (k + 1) = 0 := by omega
    rw [h1, h2, hxK l (k + 1) (by omega), gseq_zero]
    simp only [smul_zero, Finset.sum_const_zero, add_zero]

end Algebra

section LinearStep

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}
  {τ : Type*}

private def _root_.P2mKcKappaTwo.relPt [CharP R p] {N : ℕ} (c : Fin N → Fin d → Fin d → R)
    (u : Fin d → WittLaw.seriesPoint p R τ) (l : Fin d) : WittLaw.seriesPoint p R τ :=
  WittLaw.verPt (u l) - ∑ i : Fin d, ∑ m : Fin N, WittLaw.teichPt (c m i l)
    ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i))

p2m_export "P2mKcKappaTwo" "relPt"
theorem frobPt_iterate_map_add [CharP R p] (x y : WittLaw.seriesPoint p R τ) (m : ℕ) :
    (⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (x + y) =
      (⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] x +
        (⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] y := by
  induction m generalizing x y with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, map_add, ih]; rfl

theorem relPt_add [CharP R p] {N : ℕ} (c : Fin N → Fin d → Fin d → R)
    (u v : Fin d → WittLaw.seriesPoint p R τ) (l : Fin d) :
    relPt c (u + v) l = relPt c u l + relPt c v l := by
  unfold relPt
  rw [Pi.add_apply, map_add, ← add_sub_add_comm, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Pi.add_apply, frobPt_iterate_map_add, map_add]

theorem InI.relPt [CharP R p] {n N : ℕ} (c : Fin N → Fin d → Fin d → R)
    {u : Fin d → WittLaw.seriesPoint p R τ} (hu : ∀ i, InI n (u i)) (l : Fin d) :
    InI n (relPt c u l) :=
  (hu l).verPt.sub (InI.sum _ fun i _ => InI.sum _ fun m _ => ((hu i).frobPt_iterate' m).teichPt _)

theorem coeff_relPt_sub_mem [CharP R p] {n : ℕ} (hn : 1 ≤ n) {N : ℕ} (hN : 0 < N)
    (c : Fin N → Fin d → Fin d → R) {u : Fin d → WittLaw.seriesPoint p R τ}
    (hu : ∀ i, InI n (u i)) (l : Fin d) (k : ℕ) :
    ((relPt c u l : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k -
      (((WittLaw.verPt (u l) : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k -
        ∑ i, c ⟨0, hN⟩ i l ^ p ^ k •
          (u i : WittVector p (MvPowerSeries τ R)).coeff k) ∈ ordIdeal τ R (n + 1) := by
  unfold relPt
  have hbI : ∀ i, InI n (∑ m : Fin N, WittLaw.teichPt (c m i l)
      ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i))) := fun i =>
    InI.sum _ fun m _ => ((hu i).frobPt_iterate' m).teichPt _
  have h1 := coeff_sub_sub_mem hn (hu l).verPt (InI.sum Finset.univ fun i _ => hbI i) k
  have h2 := coeff_sum_sub_mem hn Finset.univ (fun i => ∑ m : Fin N, WittLaw.teichPt (c m i l)
      ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i))) (fun i _ => hbI i) k
  have h3 : ∀ i, ((∑ m : Fin N, WittLaw.teichPt (c m i l)
      ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i)) : WittLaw.seriesPoint p R τ) :
        WittVector p (MvPowerSeries τ R)).coeff k -
        c ⟨0, hN⟩ i l ^ p ^ k • (u i : WittVector p (MvPowerSeries τ R)).coeff k
          ∈ ordIdeal τ R (n + 1) := by
    intro i
    have h := coeff_sum_sub_mem hn Finset.univ (fun m : Fin N => WittLaw.teichPt (c m i l)
        ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i)))
        (fun m _ => ((hu i).frobPt_iterate' m).teichPt _) k
    have hrest : ∑ m ∈ Finset.univ.erase (⟨0, hN⟩ : Fin N),
        ((WittLaw.teichPt (c m i l) ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i)) :
          WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k
            ∈ ordIdeal τ R (n + 1) := by
      refine Ideal.sum_mem _ fun m hm => ?_
      have hm0 : (m : ℕ) ≠ 0 := fun h0 => (Finset.ne_of_mem_erase hm) (Fin.ext h0)
      rw [WittLaw.coeff_teichPt]
      exact Submodule.smul_of_tower_mem _ _ (((hu i).frobPt_iterate_succ hn hm0) k)
    have e0 : (⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[((⟨0, hN⟩ : Fin N) : ℕ)] (u i) = u i := rfl
    have hsplit : ∑ m : Fin N, ((WittLaw.teichPt (c m i l)
        ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i)) : WittLaw.seriesPoint p R τ) :
          WittVector p (MvPowerSeries τ R)).coeff k -
        c ⟨0, hN⟩ i l ^ p ^ k • (u i : WittVector p (MvPowerSeries τ R)).coeff k
          ∈ ordIdeal τ R (n + 1) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hN⟩ : Fin N)), WittLaw.coeff_teichPt, e0,
        add_sub_cancel_left]
      exact hrest
    have := add_mem h hsplit
    rwa [sub_add_sub_cancel] at this
  have := sub_mem (sub_mem h1 h2) (sum_mem fun i (_ : i ∈ Finset.univ) => h3 i)
  convert this using 1
  simp only [Finset.sum_sub_distrib]
  ring

variable [Finite τ]

theorem exists_bound {ι : Type*} [Finite ι] (w : ι → WittLaw.seriesPoint p R τ) (n : ℕ) :
    ∃ K : ℕ, ∀ l k, K ≤ k → ∀ e : τ →₀ ℕ, e.degree ≤ n →
      coeff e ((w l : WittVector p (MvPowerSeries τ R)).coeff k) = 0 := by
  have hfin : (⋃ l, ⋃ e ∈ {e : τ →₀ ℕ | e.degree ≤ n},
      {k | coeff e ((w l : WittVector p (MvPowerSeries τ R)).coeff k) ≠ 0}).Finite :=
    Set.finite_iUnion fun l => Set.Finite.biUnion (finite_setOf_degree_le n)
      fun e _ => (WittLaw.hasSubst_coeff (w l)).coeff_zero e
  obtain ⟨K, hK⟩ := hfin.bddAbove
  refine ⟨K + 1, fun l k hk e he => ?_⟩
  by_contra hne
  have hmem : k ∈ ⋃ l, ⋃ e ∈ {e : τ →₀ ℕ | e.degree ≤ n},
      {k | coeff e ((w l : WittVector p (MvPowerSeries τ R)).coeff k) ≠ 0} :=
    Set.mem_iUnion.mpr ⟨l, Set.mem_biUnion he hne⟩
  have := hK hmem
  omega

theorem linear_step [Φ.IsComm] [CharP R p] (f : Fin d → CartierModule p Φ)
    (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0)
    {N : ℕ} (hN : 0 < N) (c : Fin N → Fin d → Fin d → R) (h : Fin d → CartierModule p Φ)
    (hexp : ∀ i, frobenius (f i) =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Φ)))^[m] (∑ l : Fin d, homothety (c m i l) (f l))) +
        (⇑(verschiebung (p := p) (Φ := Φ)))^[N] (h i))
    {n : ℕ} (hn : 1 ≤ n) (w : Fin d → WittLaw.seriesPoint p R τ) (hwI : ∀ l, InI n (w l))
    (hPi : PInI (n + 1) (presPi f w)) :
    ∃ u : Fin d → WittLaw.seriesPoint p R τ, (∀ l, InI n (u l)) ∧
      ∀ l k, ((w l : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k -
        ((relPt c u l : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k
          ∈ ordIdeal τ R (n + 1) := by
  classical

  obtain ⟨K, hK⟩ := exists_bound w n

  obtain ⟨x, hx⟩ : ∃ x : Fin d → ℕ → MvPowerSeries τ R, x = fun l k =>
      homogeneousComponent n ((w l : WittVector p (MvPowerSeries τ R)).coeff k) := ⟨_, rfl⟩
  have hxH : ∀ l k, IsHomog n (x l k) := fun l k => by
    rw [hx]
    exact isHomog_homogeneousComponent n _
  have hxe : ∀ l k (e : τ →₀ ℕ), e.degree = n →
      coeff e (x l k) = coeff e ((w l : WittVector p (MvPowerSeries τ R)).coeff k) := fun l k e he => by
    simp only [hx, coeff_homogeneousComponent, if_pos he]
  have hxK : ∀ l k, K ≤ k → x l k = 0 := fun l k hk => by
    ext e
    rw [map_zero]
    by_cases he : e.degree = n
    · rw [hxe l k e he, hK l k hk e he.le]
    · exact hxH l k e he
  have hxw : ∀ l k, (w l : WittVector p (MvPowerSeries τ R)).coeff k - x l k ∈ ordIdeal τ R (n + 1) := by
    intro l k
    refine mem_ordIdeal_of_coeff fun e he => ?_
    rw [map_sub]
    rcases Nat.lt_or_ge e.degree n with hlt | hge
    · rw [coeff_eq_zero_of_mem_ordIdeal (hwI l k) hlt, (hxH l k) e hlt.ne, sub_zero]
    · have heq : e.degree = n := by omega
      rw [hxe l k e heq, sub_self]

  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Fin d → Fin d → R, c₀ = c ⟨0, hN⟩ := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℕ → Fin d → MvPowerSeries τ R, U = fun k => Gseq p x c₀ K (K - k) :=
    ⟨_, rfl⟩
  have hUH : ∀ k l, IsHomog n (U k l) := fun k l => by
    rw [hU]
    exact isHomog_gseq p hxH c₀ K _ l
  have hUK : ∀ k l, K ≤ k → U k l = 0 := fun k l hk => by
    simp only [hU, Nat.sub_eq_zero_of_le hk, gseq_zero]
  have hUrec : ∀ k l, U k l = x l (k + 1) + ∑ i, c₀ i l ^ p ^ (k + 1) • U (k + 1) i :=
    fun k l => by
    simp only [hU]
    exact gseq_rec p c₀ hxK k l

  let u : Fin d → WittLaw.seriesPoint p R τ := fun l =>
    ⟨WittVector.mk p fun k => U k l, fun k => by
      rw [WittVector.coeff_mk]; exact (hUH k l).constantCoeff hn, by
      refine ⟨fun k => ?_, fun e => ?_⟩
      · rw [WittVector.coeff_mk, (hUH k l).constantCoeff hn]
        exact IsNilpotent.zero
      · refine (Set.finite_Iio K).subset fun k hk => ?_
        by_contra hge
        apply hk
        rw [WittVector.coeff_mk, hUK k l (not_lt.mp hge), map_zero]⟩
  have hu_coeff : ∀ l k, (u l : WittVector p (MvPowerSeries τ R)).coeff k = U k l :=
    fun l k => rfl
  have huI : ∀ l, InI n (u l) := fun l k => by
    rw [hu_coeff]
    exact (hUH k l).mem_ordIdeal
  refine ⟨u, huI, fun l k => ?_⟩

  have h5 := coeff_relPt_sub_mem hn hN c huI l k
  rw [← hc₀] at h5

  have h7 : ∀ j, x j 0 = -∑ l, c₀ l j • U 0 l := by
    intro j
    refine (hxH j 0).ext (IsHomog.sum _ fun l _ => (hUH 0 l).smul _).neg fun e he => ?_
    rw [map_neg, map_sum]
    simp only [map_smul, smul_eq_mul]
    refine telescope p K (fun k l j => coeff (Finsupp.single k 1) ((f l).toPowerSeries j)) c₀
      (fun k l => coeff e (x l k)) (fun k l => coeff e (U k l)) (fun l j => ?_) (fun k i j => ?_)
      (fun l => ?_) (fun k l => ?_) j ?_
    · beta_reduce
      rw [coeff_single_toPowerSeries, Function.iterate_zero_apply, hf]
    · beta_reduce
      simp only [coeff_single_toPowerSeries, hc₀]
      exact tangent_frobenius_iterate_succ f hN c h hexp k i j
    · beta_reduce
      rw [hUK K l le_rfl, map_zero]
    · beta_reduce
      rw [eq_sub_of_add_eq (hUrec k l).symm, map_sub, map_sum]
      simp only [map_smul, smul_eq_mul]
    · beta_reduce
      have h0 := coeff_eq_zero_of_mem_ordIdeal (hPi j) (Nat.lt_succ_of_le he.le)
      rw [coeff_val_presPi hn f hwI j he.le] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (K + 1)) ?_]
      · exact Finset.sum_congr rfl fun k _ => by rw [hxe l k e he]
      · intro k hk
        rw [Finset.coe_range, Set.mem_Iio]
        by_contra hge
        apply hk
        beta_reduce
        rw [hK l k (by omega) e he.le, mul_zero]

  cases k with
  | zero =>
    rw [WittLaw.coeff_verPt_zero, zero_sub, pow_zero] at h5
    simp only [pow_one, hu_coeff] at h5
    have hA := hxw l 0
    rw [h7 l] at hA
    have := sub_mem hA h5
    rwa [sub_sub_sub_cancel_right] at this
  | succ k =>
    rw [WittLaw.coeff_verPt_succ, hu_coeff] at h5
    simp only [hu_coeff] at h5
    have hA := hxw l (k + 1)
    rw [eq_sub_of_add_eq (hUrec k l).symm] at hA
    have := sub_mem hA h5
    rwa [sub_sub_sub_cancel_right] at this

end LinearStep

section Main

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}
  {τ : Type v}

theorem exists_wmap_eq_relPt [Finite τ] [Φ.IsComm] [CharP R p] (f : Fin d → CartierModule p Φ)
    (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0)
    (N : ℕ) (c : Fin N → Fin d → Fin d → R) (h : Fin d → CartierModule p Φ)
    (hexp : ∀ i, frobenius (f i) =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Φ)))^[m] (∑ l : Fin d, homothety (c m i l) (f l))) +
        (⇑(verschiebung (p := p) (Φ := Φ)))^[N] (h i)) :
    ∀ n : ℕ, 1 ≤ n → n ≤ p ^ N → ∀ w : Fin d → WittLaw.seriesPoint p R τ, PInI n (presPi f w) →
      ∃ u : Fin d → WittLaw.seriesPoint p R τ, ∀ l,
        wmap p τ R n (w l : WittVector p (MvPowerSeries τ R)) =
          wmap p τ R n (relPt c u l : WittVector p (MvPowerSeries τ R)) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro _ w _
    exact ⟨0, fun l => wmap_eq_iff.mpr fun k => sub_mem (inI_one (w l) k) (inI_one _ k)⟩
  | succ n hn ih =>
    intro hnN w hw
    have hN : 0 < N := Nat.pos_of_ne_zero (by
      rintro rfl
      rw [pow_zero] at hnN
      omega)
    obtain ⟨u, hu⟩ := ih (Nat.le_of_succ_le hnN) w (hw.mono (Nat.le_succ n))

    obtain ⟨w', hw'⟩ : ∃ w' : Fin d → WittLaw.seriesPoint p R τ, w' = fun l => w l - relPt c u l :=
      ⟨_, rfl⟩
    have hw'I : ∀ l, InI n (w' l) := fun l => inI_iff_wmap_eq_zero.mpr (by
      rw [hw', AddSubgroupClass.coe_sub, map_sub, hu l, sub_self])

    have hk1 : presPi f (fun l => relPt c u l) =
        presPi h (fun i => (⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[N] (u i)) :=
      MvFormalGroup.CartierModule.presPi_verPt_sub_sum_teichPt_frobPt_eq_presPi_frobPt_iterate
        p Φ f N c h hexp u
    have hrel : PInI (n + 1) (presPi f fun l => relPt c u l) := by
      rw [hk1]
      refine (PInI.presPi h fun i => ?_).mono hnN
      have h1 := (inI_one (u i)).frobPt_iterate N
      rwa [mul_one] at h1
    have hPi' : PInI (n + 1) (presPi f w') := by
      have hsub : presPi f w' = presPi f w - presPi f (fun l => relPt c u l) := by
        rw [hw']
        exact presPi_sub f w _
      rw [hsub]
      exact hw.sub hrel
    obtain ⟨u', -, hu'⟩ := linear_step f hf hN c h hexp hn w' hw'I hPi'
    refine ⟨u' + u, fun l => ?_⟩
    have hwl : (w l : WittVector p (MvPowerSeries τ R)) =
        (w' l : WittVector p (MvPowerSeries τ R)) + (relPt c u l : WittVector p (MvPowerSeries τ R)) := by
      rw [hw', ← AddSubgroup.coe_add, sub_add_cancel]
    rw [relPt_add, AddSubgroup.coe_add, map_add, hwl, map_add, wmap_eq_iff.mpr (hu' l)]

end Main

end P2mKcKappaTwo

end

open MvFormalGroup MvFormalGroup.CartierModule P2mKcKappaTwo in

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : ∀ i j, MvFormalGroup.CartierModule.tangent (f i) j = if i = j then 1 else 0)
    (N : ℕ) (c : Fin N → Fin d → Fin d → R) (h : Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ i, MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[N] (h i))
    {τ : Type v} [Finite τ] (n : ℕ) (hn : n ≤ p ^ N)
    (w : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ)
    (hw : ∀ j, (n : ℕ∞) ≤ ((MvFormalGroup.CartierModule.presPi f w).val j).order) :
    ∃ u : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ, ∀ (l : Fin d) (k : ℕ),
      (n : ℕ∞) ≤
        ((w l : WittVector p (MvPowerSeries τ R)).coeff k -
          ((MvFormalGroup.WittLaw.verPt (u l) -
              ∑ i : Fin d, ∑ m : Fin N, MvFormalGroup.WittLaw.teichPt (c m i l)
                ((⇑(MvFormalGroup.WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i)) :
              MvFormalGroup.WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k).order := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · exact ⟨0, fun l k => by rw [Nat.cast_zero]; exact bot_le⟩
  · obtain ⟨u, hu⟩ := exists_wmap_eq_relPt f hf N c h hexp n hnpos hn w (fun j => hw j)
    exact ⟨u, fun l k => (wmap_eq_iff.mp (hu l)) k⟩

end S_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_of_forall_le_order_presPi
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_of_forall_le_order_presPi (solution)
