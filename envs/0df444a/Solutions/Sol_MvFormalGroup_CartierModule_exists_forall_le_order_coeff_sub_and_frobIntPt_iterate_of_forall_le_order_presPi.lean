-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_forall_le_order_coeff_sub_and_frobIntPt_iterate_of_forall_le_order_presPi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7a2ea2f6-dc84-585f-8c75-7624a5b6e3f5

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_WittPointFamily
import Definitions.Def_MvFormalGroup_WittPointFamilyInt
import Theorems.Thm_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_wittSMulPt_frobIntPt_eq_presPi_frobIntPt_iterate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_and_frobIntPt_iterate_of_forall_le_order_presPi

set_option autoImplicit false

universe u v

noncomputable section

open MvPowerSeries

namespace P2mLP3Int

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

theorem mem_seriesPoint_of_finite {x : WittVector p (MvPowerSeries τ R)}
    (h0 : ∀ n, (x.coeff n).constantCoeff = 0) (hfin : {n | x.coeff n ≠ 0}.Finite) :
    x ∈ WittLaw.seriesPoint p R τ := by
  refine ⟨h0, ⟨fun n => ?_, fun d => ?_⟩⟩
  · rw [h0]; exact IsNilpotent.zero
  · exact hfin.subset fun n hn => fun h => hn (by simp [h])

theorem teichmuller_mem_seriesPoint {a : MvPowerSeries τ R} (ha : a.constantCoeff = 0) :
    WittVector.teichmuller p a ∈ WittLaw.seriesPoint p R τ := by
  refine mem_seriesPoint_of_finite (fun n => ?_) ?_
  · cases n with
    | zero => rw [WittVector.teichmuller_coeff_zero]; exact ha
    | succ n => rw [WittVector.teichmuller_coeff_pos p a (n + 1) (Nat.succ_pos n), map_zero]
  · refine (Set.finite_singleton 0).subset fun n hn => ?_
    by_contra h
    exact hn (WittVector.teichmuller_coeff_pos p a n (Nat.pos_of_ne_zero h))

theorem shift_mem_seriesPoint (x : WittLaw.seriesPoint p R τ) (m : ℕ) :
    (x : WittVector p (MvPowerSeries τ R)).shift m ∈ WittLaw.seriesPoint p R τ := by
  refine ⟨fun n => ?_, ⟨fun n => ?_, fun d => ?_⟩⟩
  · rw [WittVector.shift_coeff]; exact WittLaw.constantCoeff_coeff x _
  · rw [WittVector.shift_coeff, WittLaw.constantCoeff_coeff x]; exact IsNilpotent.zero
  · have hf := (WittLaw.hasSubst_coeff x).coeff_zero d
    have hinj : Set.InjOn (fun a : ℕ => m + a) ((fun a : ℕ => m + a) ⁻¹' {s | (coeff d) ((x : WittVector p (MvPowerSeries τ R)).coeff s) ≠ 0}) :=
      fun a _ b _ h => add_left_cancel h
    refine (hf.preimage hinj).subset fun n hn => ?_
    simpa [WittVector.shift_coeff] using hn

theorem eq_teichmuller_add_verschiebung_shift {A : Type*} [CommRing A] (w : WittVector p A) :
    w = WittVector.teichmuller p (w.coeff 0) + WittVector.verschiebung (w.shift 1) := by
  have h := WittVector.init_add_tail w 1
  have hi : WittVector.init 1 w = WittVector.teichmuller p (w.coeff 0) := by
    ext n
    simp only [WittVector.init, WittVector.select, WittVector.coeff_mk]
    cases n with
    | zero => simp [WittVector.teichmuller_coeff_zero]
    | succ n => simp [WittVector.teichmuller_coeff_pos p (w.coeff 0) (n + 1) (Nat.succ_pos n)]
  have ht : WittVector.tail 1 w = WittVector.verschiebung (w.shift 1) := by
    ext n
    simp only [WittVector.tail, WittVector.select, WittVector.coeff_mk]
    cases n with
    | zero => simp [WittVector.verschiebung_coeff_zero]
    | succ n => simp [WittVector.verschiebung_coeff_succ, WittVector.shift_coeff, Nat.add_comm]
  rw [hi, ht] at h
  exact h.symm

theorem frobenius_eq_teichmuller_add {A : Type*} [CommRing A] (x : WittVector p A) :
    WittVector.frobenius x =
      WittVector.teichmuller p (x.coeff 0 ^ p) + x.shift 1 * (p : WittVector p A) := by
  conv_lhs => rw [eq_teichmuller_add_verschiebung_shift x]
  rw [map_add, WittVector.frobenius_teichmuller_eq, WittVector.frobenius_verschiebung]

theorem InI.nsmul {n : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : InI n x) (m : ℕ) : InI n (m • x) := by
  induction m with
  | zero => rw [zero_smul]; exact InI.zero n
  | succ m ih => rw [add_smul, one_smul]; exact ih.add hx

theorem InI.verPt {n : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : InI n x) : InI n (WittLaw.verPt x) := by
  intro k
  cases k with
  | zero => rw [WittLaw.coeff_verPt_zero]; exact zero_mem _
  | succ k => rw [WittLaw.coeff_verPt_succ]; exact hx k

theorem InI.frobIntPt {n : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : InI n x) :
    InI n (WittLaw.frobIntPt x) := fun k => by
  rw [WittLaw.coeff_frobIntPt]
  exact subst_mem_ordIdeal (WittLaw.hasSubst_coeff x) hx (WittLaw.constantCoeff_frobPolyFam (p := p) (R := R) k)

theorem InI.frobPt_iterate' {n : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : InI n x)
    (m : ℕ) : InI n ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] x) := by
  induction m with
  | zero => exact hx
  | succ m ih => rw [Function.iterate_succ_apply']; exact ih.frobIntPt

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

theorem coeff_nsmul_sub_mem {n : ℕ} (hn : 1 ≤ n) {x : WittLaw.seriesPoint p R τ} (hx : InI n x)
    (m k : ℕ) :
    ((m • x : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k -
      (m : MvPowerSeries τ R) * (x : WittVector p (MvPowerSeries τ R)).coeff k ∈ ordIdeal τ R (n + 1) := by
  induction m with
  | zero =>
    rw [zero_smul, ZeroMemClass.coe_zero, WittVector.zero_coeff, Nat.cast_zero, zero_mul, sub_zero]
    exact zero_mem _
  | succ m ih =>
    have h1 := coeff_add_sub_mem hn (hx.nsmul m) hx k
    have h2 := add_mem h1 ih
    rw [add_smul, one_smul]
    convert h2 using 1
    push_cast
    ring

theorem coeff_frobIntPt_sub_mem {n : ℕ} (hn : 1 ≤ n) {x : WittLaw.seriesPoint p R τ} (hx : InI n x)
    (k : ℕ) :
    ((WittLaw.frobIntPt x : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k -
      (p : MvPowerSeries τ R) * (x : WittVector p (MvPowerSeries τ R)).coeff (k + 1) ∈ ordIdeal τ R (n + 1) := by
  have h00 : ((x : WittVector p (MvPowerSeries τ R)).coeff 0 ^ p).constantCoeff = 0 := by
    rw [map_pow, WittLaw.constantCoeff_coeff x 0, zero_pow hp.out.ne_zero]
  set tPt : WittLaw.seriesPoint p R τ :=
    ⟨WittVector.teichmuller p ((x : WittVector p (MvPowerSeries τ R)).coeff 0 ^ p),
      teichmuller_mem_seriesPoint h00⟩ with htPt
  set shPt : WittLaw.seriesPoint p R τ :=
    ⟨(x : WittVector p (MvPowerSeries τ R)).shift 1, shift_mem_seriesPoint x 1⟩ with hshPt
  have hdec : WittLaw.frobIntPt x = tPt + p • shPt := by
    apply Subtype.ext
    rw [WittLaw.coe_frobIntPt, frobenius_eq_teichmuller_add, AddSubgroup.coe_add, AddSubgroup.coe_nsmul,
      nsmul_eq_mul, mul_comm]
  have htI : InI n tPt := by
    intro j
    cases j with
    | zero =>
      change (WittVector.teichmuller p ((x : WittVector p (MvPowerSeries τ R)).coeff 0 ^ p)).coeff 0 ∈ _
      rw [WittVector.teichmuller_coeff_zero]
      exact ordIdeal_antitone (Nat.le_mul_of_pos_left n hp.out.pos) (pow_mem_ordIdeal_mul (hx 0) p)
    | succ j =>
      change (WittVector.teichmuller p ((x : WittVector p (MvPowerSeries τ R)).coeff 0 ^ p)).coeff (j + 1) ∈ _
      rw [WittVector.teichmuller_coeff_pos p _ (j + 1) (Nat.succ_pos j)]
      exact zero_mem _
  have hshI : InI n shPt := fun j => by
    change ((x : WittVector p (MvPowerSeries τ R)).shift 1).coeff j ∈ _
    rw [WittVector.shift_coeff]
    exact hx (1 + j)
  have h1 := coeff_add_sub_mem hn htI (hshI.nsmul p) k
  have h2 := coeff_nsmul_sub_mem hn hshI p k
  have ht0 : (tPt : WittVector p (MvPowerSeries τ R)).coeff k ∈ ordIdeal τ R (n + 1) := by
    cases k with
    | zero =>
      change (WittVector.teichmuller p ((x : WittVector p (MvPowerSeries τ R)).coeff 0 ^ p)).coeff 0 ∈ _
      rw [WittVector.teichmuller_coeff_zero]
      refine ordIdeal_antitone ?_ (pow_mem_ordIdeal_mul (hx 0) p)
      calc n + 1 ≤ 2 * n := by omega
        _ ≤ p * n := Nat.mul_le_mul_right n hp.out.two_le
    | succ k =>
      change (WittVector.teichmuller p ((x : WittVector p (MvPowerSeries τ R)).coeff 0 ^ p)).coeff (k + 1) ∈ _
      rw [WittVector.teichmuller_coeff_pos p _ (k + 1) (Nat.succ_pos k)]
      exact zero_mem _
  have hsh1 : (shPt : WittVector p (MvPowerSeries τ R)).coeff k =
      (x : WittVector p (MvPowerSeries τ R)).coeff (k + 1) := by
    change ((x : WittVector p (MvPowerSeries τ R)).shift 1).coeff k = _
    rw [WittVector.shift_coeff, Nat.add_comm]
  rw [hdec]
  have := add_mem (add_mem h1 h2) ht0
  rw [hsh1] at this
  convert this using 1
  ring

theorem ghostComponent_succ_eq {A : Type*} [CommRing A] (w : WittVector p A) (k : ℕ) :
    WittVector.ghostComponent (k + 1) w =
      w.coeff 0 ^ p ^ (k + 1) + (p : A) * WittVector.ghostComponent k (w.shift 1) := by
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply, aeval_wittPolynomial,
    aeval_wittPolynomial, Finset.sum_range_succ', Finset.mul_sum, pow_zero, one_mul, Nat.sub_zero, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [WittVector.shift_coeff, Nat.succ_sub_succ, pow_succ', mul_assoc, Nat.add_comm 1 i]

theorem ghostComponent_zero_eq {A : Type*} [CommRing A] (w : WittVector p A) :
    WittVector.ghostComponent 0 w = w.coeff 0 := by
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial]
  simp

theorem wittSMulPt_eq_teichPt_add_verPt (w : WittVector p R) (y : WittLaw.seriesPoint p R τ) :
    WittLaw.wittSMulPt w y = WittLaw.teichPt (w.coeff 0) y +
      WittLaw.verPt (WittLaw.wittSMulPt (w.shift 1) (WittLaw.frobIntPt y)) := by
  apply Subtype.ext
  rw [AddSubgroup.coe_add, WittLaw.coe_wittSMulPt, WittLaw.coe_teichPt, WittLaw.coe_verPt,
    WittLaw.coe_wittSMulPt, WittLaw.coe_frobIntPt, WittVector.verschiebung_mul_frobenius,
    ← WittVector.map_verschiebung, ← WittVector.map_teichmuller, ← add_mul, ← map_add,
    ← eq_teichmuller_add_verschiebung_shift w]

theorem coeff_wittSMulPt_sub_mem {n : ℕ} (hn : 1 ≤ n) (w : WittVector p R) {y : WittLaw.seriesPoint p R τ}
    (hy : InI n y) (k : ℕ) :
    ((WittLaw.wittSMulPt w y : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k -
      WittVector.ghostComponent k w • (y : WittVector p (MvPowerSeries τ R)).coeff k ∈ ordIdeal τ R (n + 1) := by
  induction k generalizing w y with
  | zero =>
    have h1 := coeff_add_sub_mem hn (hy.teichPt (w.coeff 0)) ((hy.frobIntPt.wittSMulPt (w.shift 1)).verPt) 0
    rw [← wittSMulPt_eq_teichPt_add_verPt, WittLaw.coeff_teichPt, WittLaw.coeff_verPt_zero, add_zero,
      pow_zero, pow_one] at h1
    rwa [ghostComponent_zero_eq]
  | succ k ih =>
    have hFy := hy.frobIntPt
    have h1 := coeff_add_sub_mem hn (hy.teichPt (w.coeff 0)) ((hFy.wittSMulPt (w.shift 1)).verPt) (k + 1)
    rw [← wittSMulPt_eq_teichPt_add_verPt, WittLaw.coeff_teichPt, WittLaw.coeff_verPt_succ] at h1
    have h2 := ih (w.shift 1) hFy
    have h3 := coeff_frobIntPt_sub_mem hn hy k

    have h4 : WittVector.ghostComponent k (w.shift 1) •
        (((WittLaw.frobIntPt y : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k -
          (p : MvPowerSeries τ R) * (y : WittVector p (MvPowerSeries τ R)).coeff (k + 1)) ∈ ordIdeal τ R (n + 1) :=
      Submodule.smul_of_tower_mem _ _ h3
    have := add_mem (add_mem h1 h2) h4
    rw [ghostComponent_succ_eq]
    convert this using 1
    simp only [MvPowerSeries.smul_eq_C_mul, map_add, map_mul, map_pow, map_natCast]
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

section TangentInt

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}

theorem ghostComponent_frobenius_iterate (w : WittVector p R) (n j : ℕ) :
    WittVector.ghostComponent n ((⇑(WittVector.frobenius (p := p) (R := R)))^[j] w) =
      WittVector.ghostComponent (n + j) w := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', WittVector.ghostComponent_frobenius, ih,
      Nat.add_right_comm, Nat.add_assoc]

theorem ghostComponent_zero_eq_coeff (w : WittVector p R) : WittVector.ghostComponent 0 w = w.coeff 0 := by
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial, Finset.range_one, Finset.sum_singleton]
  simp

theorem coeff_zero_frobenius_iterate (w : WittVector p R) (j : ℕ) :
    ((⇑(WittVector.frobenius (p := p) (R := R)))^[j] w).coeff 0 = WittVector.ghostComponent j w := by
  rw [← ghostComponent_zero_eq_coeff, ghostComponent_frobenius_iterate, Nat.zero_add]

variable [Φ.IsComm]

theorem frobenius_iterate_map_add' (x y : CartierModule p Φ) (k : ℕ) :
    (⇑(frobenius (p := p) (Φ := Φ)))^[k] (x + y) =
      (⇑(frobenius (p := p) (Φ := Φ)))^[k] x + (⇑(frobenius (p := p) (Φ := Φ)))^[k] y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_add, ih]; rfl

theorem frobenius_iterate_map_sum' {ι : Type*} (s : Finset ι) (x : ι → CartierModule p Φ) (k : ℕ) :
    (⇑(frobenius (p := p) (Φ := Φ)))^[k] (∑ i ∈ s, x i) =
      ∑ i ∈ s, (⇑(frobenius (p := p) (Φ := Φ)))^[k] (x i) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply, map_sum, ih]

theorem frobenius_iterate_nsmul (n : ℕ) (x : CartierModule p Φ) (k : ℕ) :
    (⇑(frobenius (p := p) (Φ := Φ)))^[k] (n • x) = n • (⇑(frobenius (p := p) (Φ := Φ)))^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_nsmul, ih, Function.iterate_succ_apply]

theorem frobenius_iterate_smul (w : WittVector p R) (x : CartierModule p Φ) (k : ℕ) :
    (⇑(frobenius (p := p) (Φ := Φ)))^[k] (w • x) =
      (⇑(WittVector.frobenius (p := p) (R := R)))^[k] w • (⇑(frobenius (p := p) (Φ := Φ)))^[k] x := by
  induction k generalizing w x with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, frobenius_smul, ih, Function.iterate_succ_apply,
      Function.iterate_succ_apply]

theorem frobenius_iterate_verschiebungInt_iterate {m k : ℕ} (hmk : m ≤ k) (y : CartierModule p Φ) :
    (⇑(frobenius (p := p) (Φ := Φ)))^[k] ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] y) =
      (p ^ m) • (⇑(frobenius (p := p) (Φ := Φ)))^[k - m] y := by
  induction m generalizing k with
  | zero => rw [pow_zero, one_nsmul, Nat.sub_zero]; rfl
  | succ m ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', frobenius_verschiebungInt,
      frobenius_iterate_nsmul, ih (by omega), smul_smul, ← pow_succ', Nat.add_sub_add_right]

theorem frobenius_iterate_verschiebungInt_iterate_succ (k : ℕ) (y : CartierModule p Φ) :
    (⇑(frobenius (p := p) (Φ := Φ)))^[k] ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[k + 1] y) =
      (p ^ k) • verschiebungInt y := by
  have := frobenius_iterate_verschiebungInt_iterate (p := p) (Φ := Φ) (le_refl k)
    (verschiebungInt y)
  rw [Nat.sub_self, Function.iterate_zero_apply] at this
  rw [← this, Function.iterate_succ_apply]

theorem tangent_frobenius_iterate_succ_int (f : Fin d → CartierModule p Φ)
    (w : ℕ → Fin d → Fin d → WittVector p R) (h : ℕ → Fin d → CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin d), frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (∑ l : Fin d, w m i l • f l)) +
        (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    (k : ℕ) (i j : Fin d) :
    tangent ((⇑(frobenius (p := p) (Φ := Φ)))^[k + 1] (f i)) j =
      ∑ m ∈ Finset.range (k + 1), (p : R) ^ m *
        ∑ l : Fin d, WittVector.ghostComponent (k - m) (w m i l) *
          tangent ((⇑(frobenius (p := p) (Φ := Φ)))^[k - m] (f l)) j := by
  rw [Function.iterate_succ_apply, hexp (k + 1) i, frobenius_iterate_map_add',
    frobenius_iterate_map_sum', frobenius_iterate_verschiebungInt_iterate_succ, map_add, map_nsmul,
    tangent_verschiebungInt, smul_zero, add_zero, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [frobenius_iterate_verschiebungInt_iterate hmk, map_nsmul, Pi.smul_apply, nsmul_eq_mul,
    Nat.cast_pow, frobenius_iterate_map_sum', map_sum, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [frobenius_iterate_smul, tangent_smul_witt, Pi.smul_apply, smul_eq_mul,
    coeff_zero_frobenius_iterate]

end TangentInt

section RelInt

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ} {τ : Type v}

private def _root_.P2mLP3Int.relPt (w : ℕ → Fin d → Fin d → WittVector p R) (N : ℕ)
    (u : Fin d → WittLaw.seriesPoint p R τ) (l : Fin d) : WittLaw.seriesPoint p R τ :=
  WittLaw.verPt (u l) - ∑ i : Fin d, ∑ m ∈ Finset.range N, WittLaw.wittSMulPt (w m i l)
    ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] (u i))

p2m_export "P2mLP3Int" "relPt"
theorem InI.relPtN {n : ℕ} (w : ℕ → Fin d → Fin d → WittVector p R) (N : ℕ)
    {u : Fin d → WittLaw.seriesPoint p R τ} (hu : ∀ i, InI n (u i)) (l : Fin d) :
    InI n (relPt w N u l) :=
  (hu l).verPt.sub (InI.sum _ fun i _ => InI.sum _ fun m _ => ((hu i).frobPt_iterate' m).wittSMulPt _)

theorem coeff_frobIntPt_iterate_sub_mem {n : ℕ} (hn : 1 ≤ n) (m : ℕ) {x : WittLaw.seriesPoint p R τ}
    (hx : InI n x) (k : ℕ) :
    ((((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] x : WittLaw.seriesPoint p R τ) :
        WittVector p (MvPowerSeries τ R)).coeff k -
      (p : MvPowerSeries τ R) ^ m * (x : WittVector p (MvPowerSeries τ R)).coeff (k + m))
        ∈ ordIdeal τ R (n + 1) := by
  induction m generalizing x k with
  | zero => rw [pow_zero, one_mul, add_zero, Function.iterate_zero_apply, sub_self]; exact zero_mem _
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have h1 := ih hx.frobIntPt k
    have h2 := Ideal.mul_mem_left _ ((p : MvPowerSeries τ R) ^ m) (coeff_frobIntPt_sub_mem hn hx (k + m))
    have := add_mem h1 h2
    rw [mul_sub, ← mul_assoc, ← pow_succ, sub_add_sub_cancel, add_assoc] at this
    exact this

omit hp in
theorem smul_eq_C_pow_mul (g : R) (m : ℕ) (y : MvPowerSeries τ R) :
    (g * (p : R) ^ m) • y = g • ((p : MvPowerSeries τ R) ^ m * y) := by
  rw [mul_smul, Algebra.smul_def ((p : R) ^ m), map_pow, map_natCast]

theorem coeff_relPt_sub_mem_int {n : ℕ} (hn : 1 ≤ n) (w : ℕ → Fin d → Fin d → WittVector p R) (N : ℕ)
    {u : Fin d → WittLaw.seriesPoint p R τ} (hu : ∀ i, InI n (u i)) (l : Fin d) (k : ℕ) :
    ((relPt w N u l : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k -
      (((WittLaw.verPt (u l) : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k -
        ∑ i : Fin d, ∑ m ∈ Finset.range N, (WittVector.ghostComponent k (w m i l) * (p : R) ^ m) •
          (u i : WittVector p (MvPowerSeries τ R)).coeff (k + m)) ∈ ordIdeal τ R (n + 1) := by
  unfold relPt
  have hbI : ∀ i, InI n (∑ m ∈ Finset.range N, WittLaw.wittSMulPt (w m i l)
      ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] (u i))) := fun i =>
    InI.sum _ fun m _ => ((hu i).frobPt_iterate' m).wittSMulPt _
  have h1 := coeff_sub_sub_mem hn (hu l).verPt (InI.sum Finset.univ fun i _ => hbI i) k
  have h2 := coeff_sum_sub_mem hn Finset.univ (fun i => ∑ m ∈ Finset.range N,
      WittLaw.wittSMulPt (w m i l) ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] (u i)))
      (fun i _ => hbI i) k
  have h3 : ∀ i, ((∑ m ∈ Finset.range N, WittLaw.wittSMulPt (w m i l)
      ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] (u i)) : WittLaw.seriesPoint p R τ) :
        WittVector p (MvPowerSeries τ R)).coeff k -
        ∑ m ∈ Finset.range N, (WittVector.ghostComponent k (w m i l) * (p : R) ^ m) •
          (u i : WittVector p (MvPowerSeries τ R)).coeff (k + m) ∈ ordIdeal τ R (n + 1) := by
    intro i
    have h := coeff_sum_sub_mem hn (Finset.range N) (fun m => WittLaw.wittSMulPt (w m i l)
        ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] (u i)))
        (fun m _ => ((hu i).frobPt_iterate' m).wittSMulPt _) k
    have h' : ∀ m ∈ Finset.range N, ((WittLaw.wittSMulPt (w m i l)
        ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] (u i)) : WittLaw.seriesPoint p R τ) :
          WittVector p (MvPowerSeries τ R)).coeff k -
        (WittVector.ghostComponent k (w m i l) * (p : R) ^ m) •
          (u i : WittVector p (MvPowerSeries τ R)).coeff (k + m) ∈ ordIdeal τ R (n + 1) := by
      intro m _
      have a := coeff_wittSMulPt_sub_mem hn (w m i l) ((hu i).frobPt_iterate' m) k
      have b := Submodule.smul_of_tower_mem (ordIdeal τ R (n + 1)) (WittVector.ghostComponent k (w m i l))
        (coeff_frobIntPt_iterate_sub_mem hn m (hu i) k)
      have := add_mem a b
      rw [smul_sub, add_sub, sub_add_cancel, ← smul_eq_C_pow_mul] at this
      exact this
    have := add_mem h (Ideal.sum_mem _ h')
    rwa [Finset.sum_sub_distrib, add_sub, sub_add_cancel] at this
  have := sub_mem (sub_mem h1 h2) (Ideal.sum_mem _ fun i (_ : i ∈ Finset.univ) => h3 i)
  convert this using 1
  simp only [Finset.sum_sub_distrib]
  ring

end RelInt

section Algebra2

theorem telescope2 {R : Type*} [CommRing R] {d : ℕ} (K N : ℕ) (hKN : K < N)
    (T : ℕ → Fin d → Fin d → R) (a : ℕ → ℕ → Fin d → Fin d → R) (X U : ℕ → Fin d → R)
    (hT0 : ∀ l j, T 0 l j = if l = j then 1 else 0)
    (hT : ∀ k i j, T (k + 1) i j =
      ∑ m ∈ Finset.range (k + 1), ∑ l, a (k - m) m i l * T (k - m) l j)
    (hUK : ∀ k l, K ≤ k → U k l = 0)
    (hrec : ∀ k l, X (k + 1) l = U k l - ∑ i, ∑ m ∈ Finset.range N, a (k + 1) m i l * U (k + 1 + m) i)
    (j : Fin d) (hPi : ∑ l, ∑ k ∈ Finset.range (K + 1), T k l j * X k l = 0) :
    X 0 j = -∑ i, ∑ m ∈ Finset.range N, a 0 m i j * U m i := by
  classical

  set G : ℕ → ℕ → R := fun k m => ∑ i, (∑ l, T k l j * a k m i l) * U (k + m) i with hG
  have hG0 : ∀ k m, K ≤ k + m → G k m = 0 := fun k m hkm => by
    simp only [hG, hUK (k + m) _ hkm, mul_zero, Finset.sum_const_zero]

  have hBC : (∑ k ∈ Finset.range (K + 1), ∑ m ∈ Finset.range N, G k m) =
      ∑ s ∈ Finset.range K, ∑ i, T (s + 1) i j * U s i := by
    rw [← Finset.sum_product (Finset.range (K + 1)) (Finset.range N) (fun x => G x.1 x.2)]

    rw [← Finset.sum_filter_of_ne (p := fun x : ℕ × ℕ => x.1 + x.2 < K)
      (fun x _ hx => by by_contra hc; exact hx (hG0 x.1 x.2 (not_lt.mp hc)))]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : ℕ × ℕ => x.1 + x.2) (t := Finset.range K)
      (fun x hx => by simpa using (Finset.mem_filter.mp hx).2)]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hsK : s < K := Finset.mem_range.mp hs
    have hfib : ((Finset.range (K + 1) ×ˢ Finset.range N).filter (fun x : ℕ × ℕ => x.1 + x.2 < K)).filter
        (fun x : ℕ × ℕ => x.1 + x.2 = s) = Finset.HasAntidiagonal.antidiagonal s := by
      ext ⟨k, m⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
      omega
    rw [hfib, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k m => G k m) s]
    have hU : ∀ k ∈ Finset.range (s + 1), G k (s - k) = ∑ i, (∑ l, T k l j * a k (s - k) i l) * U s i := by
      intro k hk
      have hks : k ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [hG, Nat.add_sub_cancel' hks]
    rw [Finset.sum_congr rfl hU, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hT s]
    refine congrArg (· * U s i) ?_
    refine ((Finset.sum_range_reflect (fun k => ∑ l, T k l j * a k (s - k) i l) (s + 1)).symm).trans ?_
    refine Finset.sum_congr rfl fun m hm => ?_
    have hms : m ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    simp only [show s + 1 - 1 - m = s - m from by omega, Nat.sub_sub_self hms]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _

  have h0 : ∑ l, T 0 l j * X 0 l = X 0 j := by
    simp only [hT0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsplit : (∑ l, ∑ k ∈ Finset.range (K + 1), T k l j * X k l) =
      X 0 j + ∑ s ∈ Finset.range K, ∑ l, T (s + 1) l j * X (s + 1) l := by
    rw [Finset.sum_comm, Finset.sum_range_succ', h0, add_comm, Finset.sum_comm]

  have hB0 : (∑ m ∈ Finset.range N, G 0 m) = ∑ i, ∑ m ∈ Finset.range N, a 0 m i j * U m i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [hT0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Nat.zero_add]
  have hBsucc : ∀ s, (∑ m ∈ Finset.range N, G (s + 1) m) =
      ∑ l, T (s + 1) l j * ∑ i, ∑ m ∈ Finset.range N, a (s + 1) m i l * U (s + 1 + m) i := by
    intro s
    simp only [hG, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have hB : (∑ k ∈ Finset.range (K + 1), ∑ m ∈ Finset.range N, G k m) =
      (∑ i, ∑ m ∈ Finset.range N, a 0 m i j * U m i) +
        ∑ s ∈ Finset.range K, ∑ l, T (s + 1) l j *
          ∑ i, ∑ m ∈ Finset.range N, a (s + 1) m i l * U (s + 1 + m) i := by
    rw [Finset.sum_range_succ', hB0, add_comm]
    exact congrArg _ (Finset.sum_congr rfl fun s _ => hBsucc s)

  rw [hsplit] at hPi
  simp only [hrec, mul_sub, Finset.sum_sub_distrib] at hPi
  rw [← hBC, hB] at hPi
  linear_combination hPi

end Algebra2

section LinearStepInt

open MvFormalGroup MvFormalGroup.CartierModule

variable {R : Type u} [CommRing R] {τ : Type v} {d : ℕ}

def IsHomog' (n : ℕ) (a : MvPowerSeries τ R) : Prop := ∀ e : τ →₀ ℕ, e.degree ≠ n → coeff e a = 0

theorem isHomog'_homogeneousComponent (n : ℕ) (a : MvPowerSeries τ R) :
    IsHomog' n (homogeneousComponent n a) := fun e he => by
  rw [coeff_homogeneousComponent, if_neg he]

theorem IsHomog'.zero (n : ℕ) : IsHomog' n (0 : MvPowerSeries τ R) := fun _ _ => map_zero _

theorem IsHomog'.add {n : ℕ} {a b : MvPowerSeries τ R} (ha : IsHomog' n a) (hb : IsHomog' n b) :
    IsHomog' n (a + b) := fun e he => by rw [map_add, ha e he, hb e he, add_zero]

theorem IsHomog'.smul {n : ℕ} {a : MvPowerSeries τ R} (ha : IsHomog' n a) (r : R) : IsHomog' n (r • a) :=
  fun e he => by rw [map_smul, ha e he, smul_zero]

theorem IsHomog'.neg {n : ℕ} {a : MvPowerSeries τ R} (ha : IsHomog' n a) : IsHomog' n (-a) :=
  fun e he => by rw [map_neg, ha e he, neg_zero]

theorem IsHomog'.sum {n : ℕ} {ι : Type*} (s : Finset ι) {a : ι → MvPowerSeries τ R}
    (ha : ∀ i ∈ s, IsHomog' n (a i)) : IsHomog' n (∑ i ∈ s, a i) :=
  Finset.sum_induction _ (IsHomog' n) (fun _ _ hx hy => hx.add hy) (IsHomog'.zero n) ha

theorem IsHomog'.mem_ordIdeal {n : ℕ} {a : MvPowerSeries τ R} (ha : IsHomog' n a) : a ∈ ordIdeal τ R n :=
  mem_ordIdeal_of_coeff fun e he => ha e he.ne

theorem IsHomog'.constantCoeff {n : ℕ} (hn : 1 ≤ n) {a : MvPowerSeries τ R} (ha : IsHomog' n a) :
    a.constantCoeff = 0 :=
  constantCoeff_eq_zero_of_mem_ordIdeal hn ha.mem_ordIdeal

theorem IsHomog'.ext {n : ℕ} {a b : MvPowerSeries τ R} (ha : IsHomog' n a) (hb : IsHomog' n b)
    (h : ∀ e : τ →₀ ℕ, e.degree = n → coeff e a = coeff e b) : a = b := by
  ext e
  by_cases he : e.degree = n
  · exact h e he
  · rw [ha e he, hb e he]

def Useq (a : ℕ → ℕ → Fin d → Fin d → R) (N K : ℕ) (x : Fin d → ℕ → MvPowerSeries τ R) :
    ℕ → Fin d → MvPowerSeries τ R
  | k => fun l =>
    if h : k < K then
      x l (k + 1) + ∑ i : Fin d, ∑ m ∈ Finset.range N, a (k + 1) m i l • Useq a N K x (k + 1 + m) i
    else 0
  termination_by k => K - k
  decreasing_by omega

theorem useq_of_le (a : ℕ → ℕ → Fin d → Fin d → R) (N K : ℕ) (x : Fin d → ℕ → MvPowerSeries τ R)
    {k : ℕ} (hk : K ≤ k) (l : Fin d) : Useq a N K x k l = 0 := by
  rw [Useq]; simp only [dif_neg (not_lt.mpr hk)]

theorem useq_of_lt (a : ℕ → ℕ → Fin d → Fin d → R) (N K : ℕ) (x : Fin d → ℕ → MvPowerSeries τ R)
    {k : ℕ} (hk : k < K) (l : Fin d) : Useq a N K x k l =
      x l (k + 1) + ∑ i : Fin d, ∑ m ∈ Finset.range N, a (k + 1) m i l • Useq a N K x (k + 1 + m) i := by
  rw [Useq]; simp only [dif_pos hk]

theorem useq_rec (a : ℕ → ℕ → Fin d → Fin d → R) (N K : ℕ) {x : Fin d → ℕ → MvPowerSeries τ R}
    (hxK : ∀ l k, K ≤ k → x l k = 0) (k : ℕ) (l : Fin d) : Useq a N K x k l =
      x l (k + 1) + ∑ i : Fin d, ∑ m ∈ Finset.range N, a (k + 1) m i l • Useq a N K x (k + 1 + m) i := by
  rcases Nat.lt_or_ge k K with hk | hk
  · exact useq_of_lt a N K x hk l
  · rw [useq_of_le a N K x hk, hxK l (k + 1) (by omega)]
    rw [zero_add, eq_comm]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun m _ => ?_
    rw [useq_of_le a N K x (by omega), smul_zero]

theorem isHomog'_useq {n : ℕ} (a : ℕ → ℕ → Fin d → Fin d → R) (N K : ℕ)
    {x : Fin d → ℕ → MvPowerSeries τ R} (hx : ∀ l k, IsHomog' n (x l k)) :
    ∀ k l, IsHomog' n (Useq a N K x k l) := by
  suffices H : ∀ j k, K - k ≤ j → ∀ l, IsHomog' n (Useq a N K x k l) from fun k l => H _ k le_rfl l
  intro j
  induction j with
  | zero =>
    intro k hk l
    rw [useq_of_le a N K x (by omega)]; exact IsHomog'.zero n
  | succ j ih =>
    intro k hk l
    rcases Nat.lt_or_ge k K with hkK | hkK
    · rw [useq_of_lt a N K x hkK]
      exact (hx l _).add (IsHomog'.sum _ fun i _ => IsHomog'.sum _ fun m _ => (ih _ (by omega) i).smul _)
    · rw [useq_of_le a N K x hkK]; exact IsHomog'.zero n

variable {p : ℕ} [hp : Fact p.Prime] {Φ : MvFormalGroup d R}

theorem coeff_single_toPowerSeries' [Φ.IsComm] (g : CartierModule p Φ) (k : ℕ) (j : Fin d) :
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

theorem linear_step_int [Finite τ] [Φ.IsComm] (f : Fin d → CartierModule p Φ)
    (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0)
    (w : ℕ → Fin d → Fin d → WittVector p R) (h : ℕ → Fin d → CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin d), frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (∑ l : Fin d, w m i l • f l)) +
        (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    {n : ℕ} (hn : 1 ≤ n) {K N : ℕ} (hKN : K < N)
    (w' : Fin d → WittLaw.seriesPoint p R τ) (hw'n : ∀ l, InI n (w' l))
    (hw'K : ∀ l k, K ≤ k → (w' l : WittVector p (MvPowerSeries τ R)).coeff k ∈ ordIdeal τ R (n + 1))
    (hPi0 : PInI (n + 1) (presPi f w')) :
    ∃ u' : Fin d → WittLaw.seriesPoint p R τ,
      (∀ l, InI n (u' l)) ∧
      (∀ l k, K ≤ k → (u' l : WittVector p (MvPowerSeries τ R)).coeff k = 0) ∧
      ∀ l k, ((w' l : WittVector p (MvPowerSeries τ R)).coeff k -
        (relPt w N u' l : WittVector p (MvPowerSeries τ R)).coeff k) ∈ ordIdeal τ R (n + 1) := by
  classical

  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℕ → Fin d → Fin d → R, a = fun k' m i l =>
      WittVector.ghostComponent k' (w m i l) * (p : R) ^ m := ⟨_, rfl⟩

  obtain ⟨x, hx⟩ : ∃ x : Fin d → ℕ → MvPowerSeries τ R, x = fun l k =>
      homogeneousComponent n ((w' l : WittVector p (MvPowerSeries τ R)).coeff k) := ⟨_, rfl⟩
  have hxH : ∀ l k, IsHomog' n (x l k) := fun l k => by
    rw [hx]; exact isHomog'_homogeneousComponent n _
  have hxe : ∀ l k (e : τ →₀ ℕ), e.degree = n →
      coeff e (x l k) = coeff e ((w' l : WittVector p (MvPowerSeries τ R)).coeff k) := fun l k e he => by
    simp only [hx, coeff_homogeneousComponent, if_pos he]
  have hxK : ∀ l k, K ≤ k → x l k = 0 := fun l k hk => by
    ext e
    rw [map_zero]
    by_cases he : e.degree = n
    · rw [hxe l k e he]
      exact coeff_eq_zero_of_mem_ordIdeal (hw'K l k hk) (by omega)
    · exact hxH l k e he
  have hxw : ∀ l k, (w' l : WittVector p (MvPowerSeries τ R)).coeff k - x l k ∈ ordIdeal τ R (n + 1) := by
    intro l k
    refine mem_ordIdeal_of_coeff fun e he => ?_
    rw [map_sub]
    rcases Nat.lt_or_ge e.degree n with hlt | hge
    · rw [coeff_eq_zero_of_mem_ordIdeal (hw'n l k) hlt, (hxH l k) e hlt.ne, sub_zero]
    · have heq : e.degree = n := by omega
      rw [hxe l k e heq, sub_self]

  obtain ⟨U, hU⟩ : ∃ U : ℕ → Fin d → MvPowerSeries τ R, U = Useq a N K x := ⟨_, rfl⟩
  have hUH : ∀ k l, IsHomog' n (U k l) := fun k l => by rw [hU]; exact isHomog'_useq a N K hxH k l
  have hUK : ∀ k l, K ≤ k → U k l = 0 := fun k l hk => by rw [hU]; exact useq_of_le a N K x hk l
  have hUrec : ∀ k l, U k l = x l (k + 1) + ∑ i, ∑ m ∈ Finset.range N, a (k + 1) m i l • U (k + 1 + m) i :=
    fun k l => by simp only [hU]; exact useq_rec a N K hxK k l

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
  have hu_coeff : ∀ l k, (u l : WittVector p (MvPowerSeries τ R)).coeff k = U k l := fun l k => rfl
  have huI : ∀ l, InI n (u l) := fun l k => by
    rw [hu_coeff]; exact (hUH k l).mem_ordIdeal
  refine ⟨u, huI, fun l k hk => by rw [hu_coeff, hUK k l hk], fun l k => ?_⟩
  have h5 := coeff_relPt_sub_mem_int hn w N huI l k
  have ha' : ∀ (k' m : ℕ) (i l : Fin d), WittVector.ghostComponent k' (w m i l) * (p : R) ^ m = a k' m i l :=
    fun k' m i l => by rw [ha]
  simp only [hu_coeff, ha'] at h5

  have h7 : ∀ j, x j 0 = -∑ i, ∑ m ∈ Finset.range N, a 0 m i j • U m i := by
    intro j
    refine (hxH j 0).ext (IsHomog'.sum _ fun i _ => IsHomog'.sum _ fun m _ => (hUH m i).smul _).neg
      fun e he => ?_
    rw [map_neg, map_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine telescope2 K N hKN (fun k l j => coeff (Finsupp.single k 1) ((f l).toPowerSeries j)) a
      (fun k l => coeff e (x l k)) (fun k l => coeff e (U k l)) (fun l j => ?_) (fun k i j => ?_)
      (fun k l hk => ?_) (fun k l => ?_) j ?_
    · beta_reduce
      rw [coeff_single_toPowerSeries', Function.iterate_zero_apply, hf]
    · beta_reduce
      simp only [coeff_single_toPowerSeries', ha]
      rw [tangent_frobenius_iterate_succ_int f w h hexp k i j]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    · beta_reduce
      rw [hUK k l hk, map_zero]
    · beta_reduce
      rw [eq_sub_of_add_eq (hUrec k l).symm, map_sub, map_sum]
      simp only [map_sum, map_smul, smul_eq_mul]
    · beta_reduce
      have h0 := coeff_eq_zero_of_mem_ordIdeal (hPi0 j) (Nat.lt_succ_of_le he.le)
      rw [coeff_val_presPi hn f hw'n j he.le] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (K + 1)) ?_]
      · exact Finset.sum_congr rfl fun k _ => by rw [hxe l k e he]
      · intro k hk
        rw [Finset.coe_range, Set.mem_Iio]
        by_contra hge
        apply hk
        beta_reduce
        rw [← hxe l k e he, hxK l k (by omega), map_zero, mul_zero]

  cases k with
  | zero =>
    rw [WittLaw.coeff_verPt_zero, zero_sub] at h5
    simp only [Nat.zero_add] at h5
    have hA := hxw l 0
    rw [h7 l] at hA
    have := sub_mem hA h5
    rwa [sub_sub_sub_cancel_right] at this
  | succ k =>
    rw [WittLaw.coeff_verPt_succ] at h5
    simp only [hu_coeff] at h5
    have hA := hxw l (k + 1)
    rw [eq_sub_of_add_eq (hUrec k l).symm] at hA
    have := sub_mem hA h5
    rwa [sub_sub_sub_cancel_right] at this

end LinearStepInt

section Graded

open MvFormalGroup

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] {τ : Type*}

omit hp in

theorem pow_tsub_le_sum [hp : Fact p.Prime] {σ : Type*} (j : σ → ℕ) (B k : ℕ) (e : σ →₀ ℕ)
    (he : e ≠ 0) (hw : e.sum (fun s a => a * p ^ j s) = p ^ k) :
    p ^ (k - B) ≤ e.sum (fun s a => a * p ^ (j s - B)) := by
  classical
  by_cases hk : k ≤ B
  · rw [Nat.sub_eq_zero_of_le hk, pow_zero]
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext fun s => by simpa using h s)
    have h1 : 1 ≤ e s * p ^ (j s - B) :=
      le_trans (Nat.one_le_pow _ _ hp.out.pos) (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hs))
    exact le_trans h1 (Finset.single_le_sum (f := fun s => e s * p ^ (j s - B))
      (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hs))
  · push_neg at hk
    have key : p ^ k ≤ p ^ B * e.sum (fun s a => a * p ^ (j s - B)) := by
      rw [← hw, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      rw [mul_left_comm]
      refine Nat.mul_le_mul_left _ ?_
      rw [← pow_add]
      exact Nat.pow_le_pow_right hp.out.pos (by omega)
    have hsplit : p ^ k = p ^ B * p ^ (k - B) := by rw [← pow_add]; congr 1; omega
    rw [hsplit] at key
    exact Nat.le_of_mul_le_mul_left key (pow_pos hp.out.pos B)

theorem subst_mem_ordIdeal_weighted {σ : Type*} {c : σ → MvPowerSeries τ R} (hc : HasSubst c)
    (j : σ → ℕ) (B k : ℕ) (hcn : ∀ s, c s ∈ ordIdeal τ R (p ^ (j s - B)))
    {g : MvPowerSeries σ R}
    (hg : ∀ e : σ →₀ ℕ, coeff e g ≠ 0 → e.sum (fun s a => a * p ^ j s) = p ^ k) :
    subst c g ∈ ordIdeal τ R (p ^ (k - B)) := by
  classical
  refine mem_ordIdeal_of_coeff fun d hd => ?_
  rw [coeff_subst hc]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  by_cases hm : coeff m g = 0
  · rw [hm, zero_smul]
  · have hm0 : m ≠ 0 := by
      intro h0
      subst h0
      have h := hg 0 hm
      rw [Finsupp.sum_zero_index] at h
      exact absurd h (ne_of_lt (pow_pos hp.out.pos k))
    have hmem : ∀ m : σ →₀ ℕ,
        (m.prod fun s a => c s ^ a) ∈ ordIdeal τ R (m.sum fun s a => a * p ^ (j s - B)) := by
      intro m
      induction m using Finsupp.induction with
      | zero => rw [Finsupp.prod_zero_index, Finsupp.sum_zero_index]; exact mem_ordIdeal_zero _
      | single_add s a m hs ha ih =>
        rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
          Finsupp.prod_single_index (h := fun s' k' => c s' ^ k') (pow_zero _),
          Finsupp.sum_add_index (fun _ _ => zero_mul _) (fun _ _ _ _ => add_mul _ _ _),
          Finsupp.sum_single_index (zero_mul _)]
        exact mul_mem_ordIdeal_add (pow_mem_ordIdeal_mul (hcn s) a) ih
    have hle := pow_tsub_le_sum (p := p) j B k m hm0 (hg m hm)
    rw [coeff_eq_zero_of_mem_ordIdeal (ordIdeal_antitone hle (hmem m)) hd, smul_zero]

def Gd (a B : ℕ) (u : WittLaw.seriesPoint p R τ) : Prop :=
  ∀ k, (u : WittVector p (MvPowerSeries τ R)).coeff k ∈ ordIdeal τ R (p ^ (k + a - B))

theorem Gd.zero (a B : ℕ) : Gd a B (0 : WittLaw.seriesPoint p R τ) := fun k => by
  rw [ZeroMemClass.coe_zero, WittVector.zero_coeff]; exact zero_mem _

theorem Gd.mono {a B : ℕ} {u : WittLaw.seriesPoint p R τ} (hu : Gd (a + 1) B u) : Gd a B u := fun k =>
  ordIdeal_antitone (Nat.pow_le_pow_right hp.out.pos (by omega)) (hu k)

theorem gd_of_support {B : ℕ} {u : WittLaw.seriesPoint p R τ}
    (hu : ∀ k, B ≤ k → (u : WittVector p (MvPowerSeries τ R)).coeff k = 0) : Gd 0 B u := by
  intro k
  by_cases hk : B ≤ k
  · rw [hu k hk]; exact zero_mem _
  · rw [add_zero, Nat.sub_eq_zero_of_le (le_of_not_ge hk), pow_zero]
    exact mem_ordIdeal_one_iff.mpr (WittLaw.constantCoeff_coeff u k)

theorem Gd.add {a B : ℕ} {x y : WittLaw.seriesPoint p R τ} (hx : Gd a B x) (hy : Gd a B y) :
    Gd a B (x + y) := by
  intro k
  rw [WittLaw.coe_add_coeff]
  refine subst_mem_ordIdeal_weighted (WittLaw.hasSubst_pairSeries (WittLaw.hasSubst_coeff x)
    (WittLaw.hasSubst_coeff y)) (fun im : Fin 2 × ℕ => im.2 + a) B (k + a) (fun im => ?_) (fun e he => ?_)
  · obtain ⟨i, m⟩ := im
    exact Fin.cases (hx m) (fun _ => hy m) i
  · have hw := WittLaw.weight_eq_of_coeff_addFam_ne_zero p R he
    rw [Finsupp.weight_apply, Finsupp.sum] at hw
    rw [Finsupp.sum, pow_add, ← hw, Finset.sum_mul]
    refine Finset.sum_congr rfl fun im _ => ?_
    obtain ⟨i, m⟩ := im
    simp only [WittLaw.weight_apply, smul_eq_mul, one_mul, pow_add]
    ring

theorem Gd.wittSMulPt {a B : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : Gd a B x) (w : WittVector p R) :
    Gd a B (WittLaw.wittSMulPt w x) := by
  intro k
  rw [WittLaw.coeff_wittSMulPt]
  refine subst_mem_ordIdeal_weighted (WittLaw.hasSubst_coeff x) (fun m : ℕ => m + a) B (k + a) hx
    (fun e he => ?_)
  have hw := WittLaw.weight_eq_of_coeff_mulFam_ne_zero (p := p) (w := w) he
  rw [Finsupp.weight_apply, Finsupp.sum] at hw
  rw [Finsupp.sum, pow_add, ← hw, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [smul_eq_mul, pow_add]
  ring

theorem Gd.neg {a B : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : Gd a B x) : Gd a B (-x) := by
  rw [neg_eq_wittSMulPt]; exact hx.wittSMulPt _

theorem Gd.sub {a B : ℕ} {x y : WittLaw.seriesPoint p R τ} (hx : Gd a B x) (hy : Gd a B y) :
    Gd a B (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem Gd.sum {a B : ℕ} {ι : Type*} (s : Finset ι) {x : ι → WittLaw.seriesPoint p R τ}
    (hx : ∀ i ∈ s, Gd a B (x i)) : Gd a B (∑ i ∈ s, x i) :=
  Finset.sum_induction _ (Gd a B) (fun _ _ ha hb => ha.add hb) (Gd.zero a B) hx

theorem Gd.frobIntPt {a B : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : Gd a B x) :
    Gd (a + 1) B (WittLaw.frobIntPt x) := by
  intro k
  rw [WittLaw.coeff_frobIntPt]
  have h := subst_mem_ordIdeal_weighted (WittLaw.hasSubst_coeff x) (fun m : ℕ => m + a) B (k + 1 + a) hx
    (g := WittLaw.frobPolyFam p R k) (fun e he => ?_)
  · have e : k + (a + 1) - B = k + 1 + a - B := by omega
    rw [e]; exact h
  have hw := WittLaw.weight_eq_of_coeff_frobPolyFam_ne_zero (p := p) (R := R) he
  rw [Finsupp.weight_apply, Finsupp.sum] at hw
  rw [Finsupp.sum, pow_add, ← hw, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [smul_eq_mul, pow_add]
  ring

theorem Gd.frobIntPt_iterate {a B : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : Gd a B x) (N : ℕ) :
    Gd (a + N) B ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] x) := by
  induction N with
  | zero => simpa using hx
  | succ N ih =>
    rw [Function.iterate_succ_apply', ← add_assoc]
    exact ih.frobIntPt

theorem InI_frobIntPt_iterate_of_gd {B N n : ℕ} (hN : n ≤ p ^ (N - B)) {x : WittLaw.seriesPoint p R τ}
    (hx : Gd 0 B x) : InI n ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] x) := fun k =>
  ordIdeal_antitone (le_trans hN (Nat.pow_le_pow_right hp.out.pos (by omega)))
    ((hx.frobIntPt_iterate N) k)

omit hp in
theorem min_le_sum_min [hp : Fact p.Prime] {σ : Type*} (j : σ → ℕ) (B k C : ℕ) (e : σ →₀ ℕ)
    (he : e ≠ 0) (hw : e.sum (fun s a => a * p ^ j s) = p ^ k) :
    min C (p ^ (k - B)) ≤ e.sum (fun s a => a * min C (p ^ (j s - B))) := by
  classical
  by_cases hbig : ∃ s ∈ e.support, C ≤ p ^ (j s - B)
  · obtain ⟨s, hs, hC⟩ := hbig
    have hes : 1 ≤ e s := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hs)
    calc min C (p ^ (k - B)) ≤ C := min_le_left _ _
      _ = 1 * min C (p ^ (j s - B)) := by rw [one_mul, min_eq_left hC]
      _ ≤ e s * min C (p ^ (j s - B)) := Nat.mul_le_mul_right _ hes
      _ ≤ e.sum (fun s a => a * min C (p ^ (j s - B))) :=
          Finset.single_le_sum (f := fun s => e s * min C (p ^ (j s - B))) (fun _ _ => Nat.zero_le _) hs
  · push_neg at hbig
    have heq : e.sum (fun s a => a * min C (p ^ (j s - B))) = e.sum (fun s a => a * p ^ (j s - B)) := by
      rw [Finsupp.sum, Finsupp.sum]
      exact Finset.sum_congr rfl fun s hs => by rw [min_eq_right (le_of_lt (hbig s hs))]
    rw [heq]
    exact le_trans (min_le_right _ _) (pow_tsub_le_sum (p := p) j B k e he hw)

theorem subst_mem_ordIdeal_weighted_cap {σ : Type*} {c : σ → MvPowerSeries τ R} (hc : HasSubst c)
    (j : σ → ℕ) (B k C : ℕ) (hcn : ∀ s, c s ∈ ordIdeal τ R (min C (p ^ (j s - B))))
    {g : MvPowerSeries σ R}
    (hg : ∀ e : σ →₀ ℕ, coeff e g ≠ 0 → e.sum (fun s a => a * p ^ j s) = p ^ k) :
    subst c g ∈ ordIdeal τ R (min C (p ^ (k - B))) := by
  classical
  refine mem_ordIdeal_of_coeff fun d hd => ?_
  rw [coeff_subst hc]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  by_cases hm : coeff m g = 0
  · rw [hm, zero_smul]
  · have hm0 : m ≠ 0 := by
      intro h0
      subst h0
      have h := hg 0 hm
      rw [Finsupp.sum_zero_index] at h
      exact absurd h (ne_of_lt (pow_pos hp.out.pos k))
    have hmem : ∀ m : σ →₀ ℕ,
        (m.prod fun s a => c s ^ a) ∈ ordIdeal τ R (m.sum fun s a => a * min C (p ^ (j s - B))) := by
      intro m
      induction m using Finsupp.induction with
      | zero => rw [Finsupp.prod_zero_index, Finsupp.sum_zero_index]; exact mem_ordIdeal_zero _
      | single_add s a m hs ha ih =>
        rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
          Finsupp.prod_single_index (h := fun s' k' => c s' ^ k') (pow_zero _),
          Finsupp.sum_add_index (fun _ _ => zero_mul _) (fun _ _ _ _ => add_mul _ _ _),
          Finsupp.sum_single_index (zero_mul _)]
        exact mul_mem_ordIdeal_add (pow_mem_ordIdeal_mul (hcn s) a) ih
    have hle := min_le_sum_min (p := p) j B k C m hm0 (hg m hm)
    rw [coeff_eq_zero_of_mem_ordIdeal (ordIdeal_antitone hle (hmem m)) hd, smul_zero]

def GdC (C a B : ℕ) (u : WittLaw.seriesPoint p R τ) : Prop :=
  ∀ k, (u : WittVector p (MvPowerSeries τ R)).coeff k ∈ ordIdeal τ R (min C (p ^ (k + a - B)))

theorem GdC.zero (C a B : ℕ) : GdC C a B (0 : WittLaw.seriesPoint p R τ) := fun k => by
  rw [ZeroMemClass.coe_zero, WittVector.zero_coeff]; exact zero_mem _

theorem GdC.mono_a {C a B : ℕ} {u : WittLaw.seriesPoint p R τ} (hu : GdC C (a + 1) B u) : GdC C a B u :=
  fun k => ordIdeal_antitone (min_le_min_left _ (Nat.pow_le_pow_right hp.out.pos (by omega))) (hu k)

theorem GdC.mono_B {C a B B' : ℕ} (hB : B ≤ B') {u : WittLaw.seriesPoint p R τ} (hu : GdC C a B u) :
    GdC C a B' u :=
  fun k => ordIdeal_antitone (min_le_min_left _ (Nat.pow_le_pow_right hp.out.pos (by omega))) (hu k)

theorem gdC_of_support {C B : ℕ} {u : WittLaw.seriesPoint p R τ}
    (hu : ∀ k, B ≤ k → (u : WittVector p (MvPowerSeries τ R)).coeff k ∈ ordIdeal τ R C) : GdC C 0 B u := by
  intro k
  by_cases hk : B ≤ k
  · exact ordIdeal_antitone (min_le_left _ _) (hu k hk)
  · rw [add_zero, Nat.sub_eq_zero_of_le (le_of_not_ge hk), pow_zero]
    exact ordIdeal_antitone (min_le_right _ _) (mem_ordIdeal_one_iff.mpr (WittLaw.constantCoeff_coeff u k))

theorem GdC.support {C a B L : ℕ} (hL : C ≤ p ^ L) {u : WittLaw.seriesPoint p R τ} (hu : GdC C a B u)
    (k : ℕ) (hk : B + L ≤ k) : (u : WittVector p (MvPowerSeries τ R)).coeff k ∈ ordIdeal τ R C := by
  refine ordIdeal_antitone ?_ (hu k)
  refine le_min le_rfl (le_trans hL (Nat.pow_le_pow_right hp.out.pos (by omega)))

theorem GdC.add {C a B : ℕ} {x y : WittLaw.seriesPoint p R τ} (hx : GdC C a B x) (hy : GdC C a B y) :
    GdC C a B (x + y) := by
  intro k
  rw [WittLaw.coe_add_coeff]
  refine subst_mem_ordIdeal_weighted_cap (WittLaw.hasSubst_pairSeries (WittLaw.hasSubst_coeff x)
    (WittLaw.hasSubst_coeff y)) (fun im : Fin 2 × ℕ => im.2 + a) B (k + a) C (fun im => ?_) (fun e he => ?_)
  · obtain ⟨i, m⟩ := im
    exact Fin.cases (hx m) (fun _ => hy m) i
  · have hw := WittLaw.weight_eq_of_coeff_addFam_ne_zero p R he
    rw [Finsupp.weight_apply, Finsupp.sum] at hw
    rw [Finsupp.sum, pow_add, ← hw, Finset.sum_mul]
    refine Finset.sum_congr rfl fun im _ => ?_
    obtain ⟨i, m⟩ := im
    simp only [WittLaw.weight_apply, smul_eq_mul, one_mul, pow_add]
    ring

theorem GdC.wittSMulPt {C a B : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : GdC C a B x) (w : WittVector p R) :
    GdC C a B (WittLaw.wittSMulPt w x) := by
  intro k
  rw [WittLaw.coeff_wittSMulPt]
  refine subst_mem_ordIdeal_weighted_cap (WittLaw.hasSubst_coeff x) (fun m : ℕ => m + a) B (k + a) C hx
    (fun e he => ?_)
  have hw := WittLaw.weight_eq_of_coeff_mulFam_ne_zero (p := p) (w := w) he
  rw [Finsupp.weight_apply, Finsupp.sum] at hw
  rw [Finsupp.sum, pow_add, ← hw, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [smul_eq_mul, pow_add]
  ring

theorem GdC.neg {C a B : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : GdC C a B x) : GdC C a B (-x) := by
  rw [neg_eq_wittSMulPt]; exact hx.wittSMulPt _

theorem GdC.sub {C a B : ℕ} {x y : WittLaw.seriesPoint p R τ} (hx : GdC C a B x) (hy : GdC C a B y) :
    GdC C a B (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem GdC.sum {C a B : ℕ} {ι : Type*} (s : Finset ι) {x : ι → WittLaw.seriesPoint p R τ}
    (hx : ∀ i ∈ s, GdC C a B (x i)) : GdC C a B (∑ i ∈ s, x i) :=
  Finset.sum_induction _ (GdC C a B) (fun _ _ ha hb => ha.add hb) (GdC.zero C a B) hx

theorem GdC.frobIntPt {C a B : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : GdC C a B x) :
    GdC C (a + 1) B (WittLaw.frobIntPt x) := by
  intro k
  rw [WittLaw.coeff_frobIntPt]
  have h := subst_mem_ordIdeal_weighted_cap (WittLaw.hasSubst_coeff x) (fun m : ℕ => m + a) B (k + 1 + a) C
    hx (g := WittLaw.frobPolyFam p R k) (fun e he => ?_)
  · have e : k + (a + 1) - B = k + 1 + a - B := by omega
    rw [e]; exact h
  have hw := WittLaw.weight_eq_of_coeff_frobPolyFam_ne_zero (p := p) (R := R) he
  rw [Finsupp.weight_apply, Finsupp.sum] at hw
  rw [Finsupp.sum, pow_add, ← hw, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [smul_eq_mul, pow_add]
  ring

theorem GdC.frobIntPt' {C a B : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : GdC C a B x) :
    GdC C a B (WittLaw.frobIntPt x) := hx.frobIntPt.mono_a

theorem GdC.frobIntPt_iterate {C a B : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : GdC C a B x) (N : ℕ) :
    GdC C (a + N) B ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] x) := by
  induction N with
  | zero => simpa using hx
  | succ N ih =>
    rw [Function.iterate_succ_apply', ← add_assoc]
    exact ih.frobIntPt

theorem GdC.frobIntPt_iterate' {C a B : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : GdC C a B x) (N : ℕ) :
    GdC C a B ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] x) := by
  induction N with
  | zero => simpa using hx
  | succ N ih => rw [Function.iterate_succ_apply']; exact ih.frobIntPt'

theorem GdC.verPt {C a B : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : GdC C a B x) :
    GdC C a (B + 1) (WittLaw.verPt x) := by
  intro k
  cases k with
  | zero => rw [WittLaw.coeff_verPt_zero]; exact zero_mem _
  | succ k =>
    rw [WittLaw.coeff_verPt_succ]
    have e : k + 1 + a - (B + 1) = k + a - B := by omega
    rw [e]; exact hx k

theorem InI_frobIntPt_iterate_of_gdC {C B N : ℕ} (hN : C ≤ p ^ (N - B)) {x : WittLaw.seriesPoint p R τ}
    (hx : GdC C 0 B x) : InI C ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] x) := fun k =>
  ordIdeal_antitone (le_min le_rfl (le_trans hN (Nat.pow_le_pow_right hp.out.pos (by omega))))
    ((hx.frobIntPt_iterate N) k)

end Graded

section MainInt

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}
  {τ : Type v}

theorem frobIntPt_iterate_map_add (x y : WittLaw.seriesPoint p R τ) (m : ℕ) :
    (⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] (x + y) =
      (⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] x +
        (⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] y := by
  induction m generalizing x y with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, map_add, ih]; rfl

theorem relPt_add (w : ℕ → Fin d → Fin d → WittVector p R) (N : ℕ)
    (u v : Fin d → WittLaw.seriesPoint p R τ) (l : Fin d) :
    relPt w N (u + v) l = relPt w N u l + relPt w N v l := by
  unfold relPt
  rw [Pi.add_apply, map_add, ← add_sub_add_comm, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Pi.add_apply, frobIntPt_iterate_map_add, map_add]

theorem GdC.relPt {C B : ℕ} (w : ℕ → Fin d → Fin d → WittVector p R) (N : ℕ)
    {u : Fin d → WittLaw.seriesPoint p R τ} (hu : ∀ i, GdC C 0 B (u i)) (l : Fin d) :
    GdC C 0 (B + 1) (relPt w N u l) := by
  unfold P2mLP3Int.relPt
  exact (hu l).verPt.sub (GdC.sum _ fun i _ => GdC.sum _ fun m _ =>
    (((hu i).frobIntPt_iterate' m).wittSMulPt _).mono_B (Nat.le_succ B))

variable [Finite τ] in

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

theorem sum_range_eq_sum_fin' {M : Type*} [AddCommMonoid M] (N : ℕ) (T : ℕ → M) :
    (∑ m ∈ Finset.range N, T m) = ∑ m : Fin N, T m :=
  (Fin.sum_univ_eq_sum_range T N).symm

theorem exists_wmap_eq_relPt_int [Finite τ] [Φ.IsComm] (f : Fin d → CartierModule p Φ)
    (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0)
    (w : ℕ → Fin d → Fin d → WittVector p R) (h : ℕ → Fin d → CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin d), frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (∑ l : Fin d, w m i l • f l)) +
        (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    (n Kv S N : ℕ) (hSn : n ≤ p ^ (S - 1)) (hS : 1 ≤ S) (hN : Kv + n * S + S ≤ N)
    (v : Fin d → WittLaw.seriesPoint p R τ)
    (hvK : ∀ l k, Kv ≤ k → (v l : WittVector p (MvPowerSeries τ R)).coeff k ∈ ordIdeal τ R n)
    (hv : PInI n (presPi f v)) :
    ∀ m : ℕ, 1 ≤ m → m ≤ n →
      ∃ u : Fin d → WittLaw.seriesPoint p R τ, (∀ l, GdC n 0 (Kv + m * S) (u l)) ∧ ∀ l,
        wmap p τ R m (v l : WittVector p (MvPowerSeries τ R)) =
          wmap p τ R m (relPt w N u l : WittVector p (MvPowerSeries τ R)) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro _
    exact ⟨0, fun l => GdC.zero n 0 _, fun l =>
      wmap_eq_iff.mpr fun k => sub_mem (inI_one (v l) k) (inI_one _ k)⟩
  | succ m hm ih =>
    intro hmn
    obtain ⟨u, huG, hu⟩ := ih (Nat.le_of_succ_le hmn)

    obtain ⟨w', hw'⟩ : ∃ w' : Fin d → WittLaw.seriesPoint p R τ, w' = fun l => v l - relPt w N u l :=
      ⟨_, rfl⟩
    have hw'I : ∀ l, InI m (w' l) := fun l => inI_iff_wmap_eq_zero.mpr (by
      rw [hw', AddSubgroupClass.coe_sub, map_sub, hu l, sub_self])

    have hvG : ∀ l, GdC n 0 Kv (v l) := fun l => gdC_of_support (hvK l)
    have hrelG : ∀ l, GdC n 0 (Kv + m * S + 1) (relPt w N u l) := fun l => GdC.relPt w N huG l
    have hw'G : ∀ l, GdC n 0 (Kv + m * S + 1) (w' l) := fun l => by
      rw [hw']; exact ((hvG l).mono_B (by omega)).sub (hrelG l)
    have hw'K : ∀ l k, Kv + (m + 1) * S ≤ k →
        (w' l : WittVector p (MvPowerSeries τ R)).coeff k ∈ ordIdeal τ R (m + 1) := fun l k hk =>
      ordIdeal_antitone hmn ((hw'G l).support (L := S - 1) hSn k (by
        have : (m + 1) * S = m * S + S := by ring
        omega))

    have hexpN : ∀ i, frobenius (f i) =
        (∑ m' : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[(m' : ℕ)]
            (∑ l : Fin d, w m' i l • f l)) +
          (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i) := fun i => by
      rw [hexp N i, sum_range_eq_sum_fin']
    have hk1 : presPi f (fun l => relPt w N u l) =
        presPi (h N) (fun i => (⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] (u i)) := by
      have e : (fun l => relPt w N u l) = fun l => WittLaw.verPt (u l) -
          ∑ i : Fin d, ∑ m' : Fin N, WittLaw.wittSMulPt (w m' i l)
            ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[(m' : ℕ)] (u i)) := by
        funext l; unfold relPt; congr 1
        exact Finset.sum_congr rfl fun i _ => sum_range_eq_sum_fin' N _
      rw [e]
      exact MvFormalGroup.CartierModule.presPi_verPt_sub_sum_wittSMulPt_frobIntPt_eq_presPi_frobIntPt_iterate
        p Φ f N (fun m' => w m') (h N) hexpN u
    have hFN : ∀ i, InI (m + 1) ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] (u i)) := fun i =>
      (InI_frobIntPt_iterate_of_gdC (C := n) (B := Kv + m * S) (N := N)
        (le_trans hSn (Nat.pow_le_pow_right hp.out.pos (by
          have : m * S + S ≤ n * S := by nlinarith
          omega))) (huG i)).mono hmn
    have hrel : PInI (m + 1) (presPi f fun l => relPt w N u l) := by
      rw [hk1]; exact PInI.presPi _ hFN
    have hPi' : PInI (m + 1) (presPi f w') := by
      have hsub : presPi f w' = presPi f v - presPi f (fun l => relPt w N u l) := by
        rw [hw']; exact presPi_sub f v _
      rw [hsub]
      exact (hv.mono hmn).sub hrel
    have hKN : Kv + (m + 1) * S < N := by
      have : (m + 1) * S ≤ n * S := Nat.mul_le_mul_right S hmn
      omega
    obtain ⟨u', -, hu'0, hu'⟩ := linear_step_int f hf w h hexp hm hKN w' hw'I hw'K hPi'
    refine ⟨u' + u, fun l => ?_, fun l => ?_⟩
    · rw [Pi.add_apply]
      exact (gdC_of_support fun k hk => by rw [hu'0 l k hk]; exact zero_mem _).add
        ((huG l).mono_B (by nlinarith))
    · have hwl : (v l : WittVector p (MvPowerSeries τ R)) =
          (w' l : WittVector p (MvPowerSeries τ R)) + (relPt w N u l : WittVector p (MvPowerSeries τ R)) := by
        rw [hw', ← AddSubgroup.coe_add, sub_add_cancel]
      rw [relPt_add, AddSubgroup.coe_add, map_add, hwl, map_add, wmap_eq_iff.mpr (hu' l)]

end MainInt

end P2mLP3Int

end

open MvFormalGroup MvFormalGroup.CartierModule P2mLP3Int in
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : ∀ i j, MvFormalGroup.CartierModule.tangent (f i) j = if i = j then 1 else 0)
    (w : ℕ → Fin d → Fin d → WittVector p R)
    (h : ℕ → Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, w m i l • f l)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    {τ : Type v} [Finite τ] (n : ℕ)
    (v : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ)
    (hv : ∀ j, (n : ℕ∞) ≤ ((MvFormalGroup.CartierModule.presPi f v).val j).order) :
    ∃ (N : ℕ) (u : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ),
      (∀ (l : Fin d) (k : ℕ), (n : ℕ∞) ≤
        ((v l : WittVector p (MvPowerSeries τ R)).coeff k -
          ((MvFormalGroup.WittLaw.verPt (u l) -
              ∑ i : Fin d, ∑ m ∈ Finset.range N, MvFormalGroup.WittLaw.wittSMulPt (w m i l)
                ((⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] (u i)) :
              MvFormalGroup.WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k).order) ∧
      (∀ (i : Fin d) (k : ℕ), (n : ℕ∞) ≤
        ((((⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] (u i) :
            MvFormalGroup.WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k).order) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · exact ⟨0, fun _ => 0, fun l k => by rw [Nat.cast_zero]; exact bot_le, fun i k => by
      rw [Nat.cast_zero]; exact bot_le⟩
  ·
    obtain ⟨Kv, hKv⟩ := P2mLP3Int.exists_bound v (n - 1)
    have hvK : ∀ l k, Kv ≤ k → (v l : WittVector p (MvPowerSeries τ R)).coeff k ∈ P2mLP3Int.ordIdeal τ R n :=
      fun l k hk => P2mLP3Int.mem_ordIdeal_of_coeff fun e he => hKv l k hk e (by omega)

    set S : ℕ := n + 1 with hS
    have hSn : n ≤ p ^ (S - 1) := by
      rw [hS, Nat.add_sub_cancel]; exact (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    set N : ℕ := Kv + n * S + S with hN
    obtain ⟨u, huG, hu⟩ := P2mLP3Int.exists_wmap_eq_relPt_int f hf w h hexp n Kv S N hSn (by omega) le_rfl
      v hvK (fun j => hv j) n hnpos le_rfl
    refine ⟨N, u, fun l k => (P2mLP3Int.wmap_eq_iff.mp (hu l)) k, fun i k => ?_⟩
    exact (P2mLP3Int.InI_frobIntPt_iterate_of_gdC (C := n) (B := Kv + n * S) (N := N)
      (le_trans hSn (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega))) (huG i)) k

end S_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_and_frobIntPt_iterate_of_forall_le_order_presPi
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_and_frobIntPt_iterate_of_forall_le_order_presPi (solution)
