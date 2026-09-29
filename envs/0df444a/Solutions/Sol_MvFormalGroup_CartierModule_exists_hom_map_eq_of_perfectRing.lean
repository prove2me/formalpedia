-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_hom_map_eq_of_perfectRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/5ea131fb-8fe9-5f2c-8377-9ce464086daf

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_WittPointFamily
import Theorems.Thm_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_of_forall_le_order_presPi
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebung_homothety_add
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective
import Theorems.Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_exists_hom_map_eq_of_perfectRing
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u v

noncomputable section

namespace P2mKcCartierFull

open MvPowerSeries

section OrdIdeal

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

theorem ordIdeal_antitone {m n : ℕ} (h : m ≤ n) : ordIdeal τ R n ≤ ordIdeal τ R m :=
  fun _ ha => le_trans (ENat.coe_le_coe.mpr h) ha

theorem mem_ordIdeal_zero (a : MvPowerSeries τ R) : a ∈ ordIdeal τ R 0 := by
  rw [mem_ordIdeal_iff, Nat.cast_zero]
  exact bot_le

theorem mem_ordIdeal_one_iff {a : MvPowerSeries τ R} :
    a ∈ ordIdeal τ R 1 ↔ a.constantCoeff = 0 := by
  rw [mem_ordIdeal_iff, Nat.cast_one]
  exact one_le_order_iff_constCoeff_eq_zero

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

theorem eq_zero_of_forall_mem_ordIdeal {a : MvPowerSeries τ R} (h : ∀ n, a ∈ ordIdeal τ R n) :
    a = 0 :=
  order_eq_top_iff.mp (ENat.eq_top_iff_forall_ge.mpr fun n => h n)

end OrdIdeal

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

theorem InI.sum {n : ℕ} {ι : Type*} (s : Finset ι) {x : ι → WittLaw.seriesPoint p R τ}
    (hx : ∀ i ∈ s, InI n (x i)) : InI n (∑ i ∈ s, x i) :=
  Finset.sum_induction _ (InI n) (fun _ _ ha hb => ha.add hb) (InI.zero n) hx

theorem InI.frobPt_iterate [CharP R p] {n : ℕ} {x : WittLaw.seriesPoint p R τ} (hx : InI n x)
    (m : ℕ) : InI (p ^ m * n) ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] x) := fun k => by
  rw [WittLaw.coeff_frobPt_iterate]
  exact pow_mem_ordIdeal_mul (hx k) _

theorem inI_pow_frobPt_iterate [CharP R p] (x : WittLaw.seriesPoint p R τ) (m : ℕ) :
    InI (p ^ m) ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] x) := by
  have h := (inI_one x).frobPt_iterate m
  rwa [mul_one] at h

end Witt

section SeriesPoint

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] {d d' : ℕ} {Φ : MvFormalGroup d R}
  {Φ' : MvFormalGroup d' R} {τ : Type*}

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

theorem PInI.mapPt [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') {n : ℕ} {a : SeriesPoint Φ τ}
    (ha : PInI n a) : PInI n (SeriesPoint.mapPt φ a) :=
  fun i => subst_mem_ordIdeal a.hasSubst_val ha (φ.constantCoeff_eq_zero i)

theorem PInI.evalPt [Φ.IsComm] {n : ℕ} (g : CartierModule p Φ) {w : WittLaw.seriesPoint p R τ}
    (hw : InI n w) : PInI n (evalPt g w) :=
  fun j => subst_mem_ordIdeal (WittLaw.hasSubst_coeff w) hw (g.constantCoeff_eq_zero j)

theorem PInI.presPi [Φ.IsComm] {n : ℕ} {ι : Type*} [Fintype ι] (f : ι → CartierModule p Φ)
    {w : ι → WittLaw.seriesPoint p R τ} (hw : ∀ l, InI n (w l)) : PInI n (presPi f w) :=
  PInI.sum _ fun l _ => PInI.evalPt (f l) (hw l)

omit hp in

theorem eq_zero_of_forall_pInI {a : SeriesPoint Φ τ} (h : ∀ n, PInI n a) : a = 0 :=
  SeriesPoint.ext (funext fun j => eq_zero_of_forall_mem_ordIdeal fun n => h n j)

end SeriesPoint

section Transport

open MvFormalGroup MvFormalGroup.CartierModule

theorem iterate_map_sum {M : Type*} [AddCommMonoid M] (g : M →+ M) (m : ℕ) {ι : Type*}
    (s : Finset ι) (x : ι → M) : (⇑g)^[m] (∑ i ∈ s, x i) = ∑ i ∈ s, (⇑g)^[m] (x i) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, map_sum, ih]
    rfl

theorem iterate_map_add {M : Type*} [AddCommMonoid M] (g : M →+ M) (m : ℕ) (x y : M) :
    (⇑g)^[m] (x + y) = (⇑g)^[m] x + (⇑g)^[m] y := by
  induction m generalizing x y with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, map_add, ih]; rfl

theorem semiconj_iterate {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] (θ : M →+ M')
    (g : M →+ M) (g' : M' →+ M') (h : ∀ x, θ (g x) = g' (θ x)) (m : ℕ) (x : M) :
    θ ((⇑g)^[m] x) = (⇑g')^[m] (θ x) :=
  Function.Semiconj.iterate_right (f := θ) (ga := g) (gb := g') h m x

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d d' : ℕ}
  {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} [Φ.IsComm] [Φ'.IsComm]

theorem map_expansion (θ : CartierModule p Φ →+ CartierModule p Φ')
    (hV : ∀ x, θ (verschiebung x) = verschiebung (θ x))
    (hH : ∀ (a : R) x, θ (homothety a x) = homothety a (θ x))
    {ι : Type*} [Fintype ι] {N : ℕ} (a : Fin N → ι → R) (f : ι → CartierModule p Φ)
    (y : CartierModule p Φ) :
    θ ((∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Φ)))^[m] (∑ i, homothety (a m i) (f i))) +
        (⇑(verschiebung (p := p) (Φ := Φ)))^[N] y) =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Φ')))^[m] (∑ i, homothety (a m i) (θ (f i)))) +
        (⇑(verschiebung (p := p) (Φ := Φ')))^[N] (θ y) := by
  rw [map_add, map_sum, semiconj_iterate θ _ _ hV]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [semiconj_iterate θ _ _ hV, map_sum]
  simp only [hH]

theorem evalPt_expansion {e : ℕ} {Ψ : MvFormalGroup e R} [Ψ.IsComm] {τ : Type*}
    {ι : Type*} [Fintype ι] {N : ℕ} (a : Fin N → ι → R) (F : ι → CartierModule p Ψ)
    (y : CartierModule p Ψ) (w : WittLaw.seriesPoint p R τ) :
    evalPt ((∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Ψ)))^[m] (∑ i, homothety (a m i) (F i))) +
        (⇑(verschiebung (p := p) (Φ := Ψ)))^[N] y) w =
      presPi F (fun i => ∑ m : Fin N, WittLaw.teichPt (a m i)
          ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] w)) +
        evalPt y ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[N] w) := by
  rw [map_add, AddMonoidHom.add_apply, ← evalPt_frobPt_iterate, map_sum,
    AddMonoidHom.finsetSum_apply, presPi_def]
  congr 1
  simp only [map_sum, ← evalPt_frobPt_iterate, AddMonoidHom.finsetSum_apply, evalPt_teichPt]
  exact Finset.sum_comm

theorem presPi_rel_eq {e : ℕ} {Ψ : MvFormalGroup e R} [Ψ.IsComm] {ι : Type*} [Fintype ι]
    (F : ι → CartierModule p Ψ) (N : ℕ) (c : Fin N → ι → ι → R) (H : ι → CartierModule p Ψ)
    (hexp : ∀ i, frobenius (F i) =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Ψ)))^[m] (∑ l, homothety (c m i l) (F l))) +
        (⇑(verschiebung (p := p) (Φ := Ψ)))^[N] (H i))
    {τ : Type*} (u : ι → WittLaw.seriesPoint p R τ) :
    presPi F (fun l => WittLaw.verPt (u l) - ∑ i, ∑ m : Fin N, WittLaw.teichPt (c m i l)
        ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i))) =
      presPi H (fun i => (⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[N] (u i)) := by
  simp only [presPi_def, map_sub, map_sum, evalPt_verPt, evalPt_teichPt, evalPt_frobPt_iterate]
  have hF : (∑ l, evalPt (frobenius (F l)) (u l)) =
      ∑ i, ((∑ m : Fin N, ∑ l,
          evalPt ((⇑(verschiebung (p := p) (Φ := Ψ)))^[m] (homothety (c m i l) (F l))) (u i)) +
        evalPt ((⇑(verschiebung (p := p) (Φ := Ψ)))^[N] (H i)) (u i)) :=
    Finset.sum_congr rfl fun i _ => by
      rw [hexp i, map_add, AddMonoidHom.add_apply, map_sum, AddMonoidHom.finsetSum_apply]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [iterate_map_sum, map_sum, AddMonoidHom.finsetSum_apply]
  rw [Finset.sum_sub_distrib, hF, Finset.sum_add_distrib]
  have hswap :
      (∑ i, ∑ m : Fin N, ∑ l,
          evalPt ((⇑(verschiebung (p := p) (Φ := Ψ)))^[m] (homothety (c m i l) (F l))) (u i)) =
        ∑ l, ∑ i, ∑ m : Fin N,
          evalPt ((⇑(verschiebung (p := p) (Φ := Ψ)))^[m] (homothety (c m i l) (F l))) (u i) :=
    calc (∑ i, ∑ m : Fin N, ∑ l,
            evalPt ((⇑(verschiebung (p := p) (Φ := Ψ)))^[m] (homothety (c m i l) (F l))) (u i))
        = ∑ i, ∑ l, ∑ m : Fin N,
            evalPt ((⇑(verschiebung (p := p) (Φ := Ψ)))^[m] (homothety (c m i l) (F l))) (u i) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ m : Fin N,
            evalPt ((⇑(verschiebung (p := p) (Φ := Ψ)))^[m] (homothety (c m i l) (F l))) (u i) :=
          Finset.sum_comm
  rw [hswap, add_sub_cancel_left]

end Transport

section Kernel

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d d' : ℕ}
  {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} [Φ.IsComm] [Φ'.IsComm]

theorem pInI_presPi_map (θ : CartierModule p Φ →+ CartierModule p Φ')
    (hF : ∀ x, θ (frobenius x) = frobenius (θ x))
    (hV : ∀ x, θ (verschiebung x) = verschiebung (θ x))
    (hH : ∀ (a : R) x, θ (homothety a x) = homothety a (θ x))
    (f : Fin d → CartierModule p Φ) (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0)
    {N : ℕ} (c : Fin N → Fin d → Fin d → R) (h : Fin d → CartierModule p Φ)
    (hexp : ∀ i, frobenius (f i) =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Φ)))^[m] (∑ l : Fin d, homothety (c m i l) (f l))) +
        (⇑(verschiebung (p := p) (Φ := Φ)))^[N] (h i))
    {τ : Type v} [Finite τ] {n : ℕ} (hn : n ≤ p ^ N) (w : Fin d → WittLaw.seriesPoint p R τ)
    (hw : PInI n (presPi f w)) : PInI n (presPi (fun l => θ (f l)) w) := by

  obtain ⟨u, hu⟩ :=
    MvFormalGroup.CartierModule.exists_forall_le_order_coeff_sub_of_forall_le_order_presPi p Φ f hf N
      c h hexp n hn w hw
  set k : Fin d → WittLaw.seriesPoint p R τ := fun l => WittLaw.verPt (u l) -
    ∑ i : Fin d, ∑ m : Fin N, WittLaw.teichPt (c m i l)
      ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i)) with hk
  have hkl : ∀ l, k l = WittLaw.verPt (u l) - ∑ i : Fin d, ∑ m : Fin N, WittLaw.teichPt (c m i l)
      ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i)) := fun l => rfl

  have hwk : ∀ l, wmap p τ R n (w l : WittVector p (MvPowerSeries τ R)) =
      wmap p τ R n (k l : WittVector p (MvPowerSeries τ R)) := fun l =>
    wmap_eq_iff.mpr fun m => by rw [hkl]; exact hu l m
  have hw'I : ∀ l, InI n (w l - k l) := fun l => inI_iff_wmap_eq_zero.mpr (by
    rw [AddSubgroupClass.coe_sub, map_sub, hwk l, sub_self])
  have hsplit : w = (fun l => w l - k l) + k := by
    funext l
    simp only [Pi.add_apply, sub_add_cancel]

  have hexp' : ∀ i, frobenius (θ (f i)) =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Φ')))^[m]
          (∑ l : Fin d, homothety (c m i l) (θ (f l)))) +
        (⇑(verschiebung (p := p) (Φ := Φ')))^[N] (θ (h i)) := fun i => by
    rw [← hF, hexp i]
    exact map_expansion θ hV hH (fun m l => c m i l) f (h i)
  have hk1 : presPi (fun l => θ (f l)) k =
      presPi (fun i => θ (h i)) (fun i => (⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[N] (u i)) :=
    presPi_rel_eq (fun l => θ (f l)) N c (fun i => θ (h i)) hexp' u
  rw [hsplit, presPi_add, hk1]
  refine (PInI.presPi _ hw'I).add ((PInI.presPi _ fun i => inI_pow_frobPt_iterate (u i) N).mono hn)

theorem exists_expansion (f : Fin d → CartierModule p Φ)
    (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0) (N : ℕ) :
    ∃ (c : Fin N → Fin d → Fin d → R) (h : Fin d → CartierModule p Φ), ∀ i, frobenius (f i) =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Φ)))^[m] (∑ l : Fin d, homothety (c m i l) (f l))) +
        (⇑(verschiebung (p := p) (Φ := Φ)))^[N] (h i) := by
  have hdet : IsUnit (Matrix.of fun i j => tangent (f i) j).det := by
    have h1 : (Matrix.of fun i j => tangent (f i) j) = (1 : Matrix (Fin d) (Fin d) R) := by
      ext i j
      rw [Matrix.of_apply, hf, Matrix.one_apply]
    rw [h1, Matrix.det_one]
    exact isUnit_one
  choose ch hch using fun i =>
    (MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebung_homothety_add p Φ f hdet
      (frobenius (f i)) N).exists
  exact ⟨fun m i l => (ch i).1 m l, fun i => (ch i).2, hch⟩

theorem exists_expansion_elem (f : Fin d → CartierModule p Φ)
    (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0) (g : CartierModule p Φ) (N : ℕ) :
    ∃ (a : Fin N → Fin d → R) (y : CartierModule p Φ), g =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Φ)))^[m] (∑ i : Fin d, homothety (a m i) (f i))) +
        (⇑(verschiebung (p := p) (Φ := Φ)))^[N] y := by
  have hdet : IsUnit (Matrix.of fun i j => tangent (f i) j).det := by
    have h1 : (Matrix.of fun i j => tangent (f i) j) = (1 : Matrix (Fin d) (Fin d) R) := by
      ext i j
      rw [Matrix.of_apply, hf, Matrix.one_apply]
    rw [h1, Matrix.det_one]
    exact isUnit_one
  obtain ⟨ch, hch, -⟩ :=
    MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebung_homothety_add p Φ f hdet g N
  exact ⟨ch.1, ch.2, hch⟩

theorem presPi_map_eq_zero (θ : CartierModule p Φ →+ CartierModule p Φ')
    (hF : ∀ x, θ (frobenius x) = frobenius (θ x))
    (hV : ∀ x, θ (verschiebung x) = verschiebung (θ x))
    (hH : ∀ (a : R) x, θ (homothety a x) = homothety a (θ x))
    (f : Fin d → CartierModule p Φ) (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0)
    {τ : Type v} [Finite τ] (w : Fin d → WittLaw.seriesPoint p R τ) (hw : presPi f w = 0) :
    presPi (fun l => θ (f l)) w = 0 := by
  refine eq_zero_of_forall_pInI fun n => ?_
  obtain ⟨c, h, hexp⟩ := exists_expansion f hf n
  refine pInI_presPi_map θ hF hV hH f hf c h hexp (Nat.lt_pow_self hp.out.one_lt).le w ?_
  rw [hw]
  exact PInI.zero n

theorem presPi_map_eq_of_presPi_eq (θ : CartierModule p Φ →+ CartierModule p Φ')
    (hF : ∀ x, θ (frobenius x) = frobenius (θ x))
    (hV : ∀ x, θ (verschiebung x) = verschiebung (θ x))
    (hH : ∀ (a : R) x, θ (homothety a x) = homothety a (θ x))
    (f : Fin d → CartierModule p Φ) (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0)
    {τ : Type v} [Finite τ] {w w' : Fin d → WittLaw.seriesPoint p R τ}
    (hw : presPi f w = presPi f w') : presPi (fun l => θ (f l)) w = presPi (fun l => θ (f l)) w' := by
  rw [← sub_eq_zero, ← presPi_sub]
  refine presPi_map_eq_zero θ hF hV hH f hf _ ?_
  rw [presPi_sub, hw, sub_self]

end Kernel

section Generic

open MvFormalGroup

variable {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}

theorem hasSubst_constX (i : Fin d) :
    HasSubst (fun _ : Unit => (X i : MvPowerSeries (Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X i

def linMap (Φ : MvFormalGroup d R) [Φ.IsComm] (m : ℕ) :
    SeriesPoint Φ (Fin m) →+ Matrix (Fin d) (Fin m) R where
  toFun a := linearPart a.val
  map_zero' := by rw [SeriesPoint.val_zero]; exact linearPart_zero
  map_add' a b := by
    rw [SeriesPoint.val_add]
    exact linearPart_subst_elim Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero

@[scoped simp] theorem linMap_apply [Φ.IsComm] (m : ℕ) (a : SeriesPoint Φ (Fin m)) :
    linMap Φ m a = linearPart a.val :=
  rfl

def XPt (Φ : MvFormalGroup d R) : SeriesPoint Φ (Fin d) := ⟨fun i => X i, fun i => constantCoeff_X i⟩

def inlPt (Φ : MvFormalGroup d R) : SeriesPoint Φ (Fin d ⊕ Fin d) :=
  ⟨fun l => X (Sum.inl l), fun _ => constantCoeff_X _⟩

def inrPt (Φ : MvFormalGroup d R) : SeriesPoint Φ (Fin d ⊕ Fin d) :=
  ⟨fun l => X (Sum.inr l), fun _ => constantCoeff_X _⟩

theorem val_inlPt_add_inrPt : (inlPt Φ + inrPt Φ).val = Φ.toPowerSeries := by
  rw [SeriesPoint.val_add]
  funext j
  have hX : Sum.elim (inlPt Φ).val (inrPt Φ).val =
      fun s => (X s : MvPowerSeries (Fin d ⊕ Fin d) R) := by
    funext s
    rcases s with l | l <;> rfl
  rw [hX]
  exact congrFun subst_self _

theorem prod_X_pow_eq_monomial {σ : Type*} (e : σ →₀ ℕ) :
    (e.prod fun s k => (X s : MvPowerSeries σ R) ^ k) = monomial e 1 := by
  have h := monomial_eq e (fun _ : σ => (1 : R))
  have h1 : (e.prod fun _ n => (1 : R) ^ n) = 1 := by simp [Finsupp.prod]
  rw [h1] at h
  rw [h]
  exact Finsupp.prod_congr fun s _ => by rw [one_smul]

end Generic

section Section

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d d' : ℕ}
  {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} [Φ.IsComm] [Φ'.IsComm]

def cwPt (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (d : ℕ) (i : Fin d) :
    WittLaw.seriesPoint p R (Fin d) :=
  WittLaw.substPt (b := fun _ : Unit => (X i : MvPowerSeries (Fin d) R)) (hasSubst_constX i)
    (fun _ => constantCoeff_X i) WittLaw.curveTautPt

theorem val_evalPt_cwPt (g : CartierModule p Φ) (i : Fin d) :
    (evalPt g (cwPt p R d i)).val = fun j => subst (fun _ : Unit => (X i : MvPowerSeries (Fin d) R))
      (curve g j) := by
  rw [cwPt, ← substPt_evalPt]
  rfl

theorem coeff_single_val_evalPt_cwPt (g : CartierModule p Φ) (i j j' : Fin d) :
    coeff (Finsupp.single j' 1) ((evalPt g (cwPt p R d i)).val j) =
      if j' = i then tangent g j else 0 := by
  classical
  rw [val_evalPt_cwPt]
  dsimp only
  rw [coeff_single_subst (fun _ => constantCoeff_X i), Fintype.sum_unique, coeff_X,
    ← PowerSeries.coeff_def (s := Finsupp.single (default : Unit) 1) (n := 1) (by simp), coeff_one_curve]
  by_cases hji : j' = i
  · subst hji
    rw [if_pos rfl, if_pos rfl, mul_one]
  · rw [if_neg (fun h => hji (Finsupp.single_left_injective one_ne_zero h)), if_neg hji, mul_zero]

def GPt (f : Fin d → CartierModule p Φ) : SeriesPoint Φ (Fin d) :=
  presPi f (cwPt p R d)

theorem linearPart_GPt (f : Fin d → CartierModule p Φ)
    (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0) : linearPart (GPt (p := p) f).val = 1 := by
  rw [← linMap_apply, GPt, presPi_def, map_sum]
  ext j j'
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp only [linMap_apply, linearPart, Matrix.of_apply, coeff_single_val_evalPt_cwPt]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), hf]
  by_cases h : j = j'
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem presPi_substPt {ι : Type*} [Fintype ι] (F : ι → CartierModule p Φ) {τ : Type v}
    {τ' : Type*} {b : τ → MvPowerSeries τ' R} (hb : HasSubst b) (hb0 : ∀ t, (b t).constantCoeff = 0)
    (v : ι → WittLaw.seriesPoint p R τ) :
    presPi F (fun l => WittLaw.substPt hb hb0 (v l)) = SeriesPoint.substPt hb hb0 (presPi F v) := by
  simp only [presPi_def, map_sum, substPt_evalPt]

variable (f : Fin d → CartierModule p Φ) {uinv : Fin d → MvPowerSeries (Fin d) R}
  (hu0 : ∀ i, (uinv i).constantCoeff = 0) (hu : ∀ i, subst uinv ((GPt (p := p) f).val i) = X i)

def wX : Fin d → WittLaw.seriesPoint p R (Fin d) := fun l =>
  WittLaw.substPt (hasSubst_of_constantCoeff_zero hu0) hu0 (cwPt p R d l)

include hu in

theorem presPi_wX : presPi f (wX (p := p) hu0) = XPt Φ := by
  unfold wX
  rw [presPi_substPt]
  refine SeriesPoint.ext (funext fun i => ?_)
  exact hu i

def wOf {τ : Type v} (a : SeriesPoint Φ τ) : Fin d → WittLaw.seriesPoint p R τ := fun l =>
  WittLaw.substPt a.hasSubst_val a.constantCoeff_eq_zero (wX (p := p) hu0 l)

include hu in

theorem presPi_wOf {τ : Type v} (a : SeriesPoint Φ τ) : presPi f (wOf (p := p) hu0 a) = a := by
  unfold wOf
  rw [presPi_substPt, presPi_wX f hu0 hu]
  refine SeriesPoint.ext (funext fun i => ?_)
  exact subst_X a.hasSubst_val i

end Section

section Phi

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d d' : ℕ}
  {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} [Φ.IsComm] [Φ'.IsComm]
  (θ : CartierModule p Φ →+ CartierModule p Φ')
  (hF : ∀ x, θ (frobenius x) = frobenius (θ x))
  (hV : ∀ x, θ (verschiebung x) = verschiebung (θ x))
  (hH : ∀ (a : R) x, θ (homothety a x) = homothety a (θ x))
  (f : Fin d → CartierModule p Φ) (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0)
  {uinv : Fin d → MvPowerSeries (Fin d) R}
  (hu0 : ∀ i, (uinv i).constantCoeff = 0) (hu : ∀ i, subst uinv ((GPt (p := p) f).val i) = X i)

def phiSeries : Fin d' → MvPowerSeries (Fin d) R :=
  (presPi (fun l => θ (f l)) (wX (p := p) hu0)).val

def phiPt {τ : Type v} (a : SeriesPoint Φ τ) : SeriesPoint Φ' τ :=
  ⟨fun i => subst a.val (phiSeries θ f hu0 i), fun i =>
    constantCoeff_subst_eq_zero a.hasSubst_val a.constantCoeff_eq_zero
      ((presPi (fun l => θ (f l)) (wX (p := p) hu0)).constantCoeff_eq_zero i)⟩

omit [CharP R p] in

theorem phiPt_eq {τ : Type v} (a : SeriesPoint Φ τ) :
    phiPt θ f hu0 a = presPi (fun l => θ (f l)) (wOf (p := p) hu0 a) := by
  unfold wOf
  rw [presPi_substPt]
  rfl

include hF hV hH hf hu in

theorem phiPt_add {τ : Type v} [Finite τ] (a b : SeriesPoint Φ τ) :
    phiPt θ f hu0 (a + b) = phiPt θ f hu0 a + phiPt θ f hu0 b := by
  rw [phiPt_eq, phiPt_eq, phiPt_eq, ← presPi_add]
  refine presPi_map_eq_of_presPi_eq θ hF hV hH f hf ?_
  rw [presPi_add, presPi_wOf f hu0 hu, presPi_wOf f hu0 hu, presPi_wOf f hu0 hu]

include hF hV hH hf hu in

def phiHom : Φ.Hom Φ' where
  toPowerSeries := phiSeries θ f hu0
  constantCoeff_eq_zero := (presPi (fun l => θ (f l)) (wX (p := p) hu0)).constantCoeff_eq_zero
  subst_eq i := by
    have key := congrArg (fun P : SeriesPoint Φ' (Fin d ⊕ Fin d) => P.val i)
      (phiPt_add θ hF hV hH f hf hu0 hu (inlPt Φ) (inrPt Φ))
    simp only [SeriesPoint.val_add] at key
    have h1 : (phiPt θ f hu0 (inlPt Φ + inrPt Φ)).val i =
        subst Φ.toPowerSeries (phiSeries θ f hu0 i) := by
      show subst (inlPt Φ + inrPt Φ).val (phiSeries θ f hu0 i) = _
      rw [val_inlPt_add_inrPt]
    rw [← h1, key]
    rfl

@[scoped simp] theorem toPowerSeries_phiHom : (phiHom θ hF hV hH f hf hu0 hu).toPowerSeries = phiSeries θ f hu0 :=
  rfl

theorem mapPt_phiHom {τ : Type v} (a : SeriesPoint Φ τ) :
    SeriesPoint.mapPt (phiHom θ hF hV hH f hf hu0 hu) a = phiPt θ f hu0 a :=
  rfl

theorem mapPt_phiHom_presPi {τ : Type v} [Finite τ] (v : Fin d → WittLaw.seriesPoint p R τ) :
    SeriesPoint.mapPt (phiHom θ hF hV hH f hf hu0 hu) (presPi f v) = presPi (fun l => θ (f l)) v := by
  rw [mapPt_phiHom, phiPt_eq]
  refine presPi_map_eq_of_presPi_eq θ hF hV hH f hf ?_
  rw [presPi_wOf f hu0 hu]

theorem mapPt_phiHom_evalPt {τ : Type v} [Finite τ] (g : CartierModule p Φ)
    (w : WittLaw.seriesPoint p R τ) :
    SeriesPoint.mapPt (phiHom θ hF hV hH f hf hu0 hu) (evalPt g w) = evalPt (θ g) w := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_pInI fun n => ?_
  obtain ⟨a, y, hg⟩ := exists_expansion_elem f hf g n
  have hθg : θ g = (∑ m : Fin n, (⇑(verschiebung (p := p) (Φ := Φ')))^[m]
      (∑ i : Fin d, homothety (a m i) (θ (f i)))) +
        (⇑(verschiebung (p := p) (Φ := Φ')))^[n] (θ y) := by
    rw [hg]
    exact map_expansion θ hV hH a f y
  rw [hθg, hg, evalPt_expansion, evalPt_expansion, map_add, mapPt_phiHom_presPi,
    add_sub_add_left_eq_sub]
  refine PInI.sub ?_ ?_
  · exact (PInI.mapPt _ (PInI.evalPt y (inI_pow_frobPt_iterate w n))).mono
      (Nat.lt_pow_self hp.out.one_lt).le
  · exact (PInI.evalPt (θ y) (inI_pow_frobPt_iterate w n)).mono (Nat.lt_pow_self hp.out.one_lt).le

end Phi

section Trunc

open MvFormalGroup MvFormalGroup.CartierModule

variable {R : Type u} [CommRing R]

def truncFam (R : Type u) [CommRing R] (n : ℕ) : ℕ → MvPowerSeries (Fin n) R := fun m =>
  killCompl (Fin.valEmbedding (n := n)) (X m)

theorem truncFam_of_lt {n m : ℕ} (h : m < n) : truncFam R n m = X ⟨m, h⟩ :=
  killCompl_X (e := Fin.valEmbedding (n := n)) ⟨m, h⟩

theorem truncFam_of_le {n m : ℕ} (h : n ≤ m) : truncFam R n m = 0 := by
  refine killCompl_X_eq_zero ?_
  rintro ⟨i, hi⟩
  have : (i : ℕ) = m := hi
  omega

theorem constantCoeff_truncFam (n m : ℕ) : (truncFam R n m).constantCoeff = 0 := by
  rcases lt_or_ge m n with h | h
  · rw [truncFam_of_lt h]; exact constantCoeff_X _
  · rw [truncFam_of_le h]; exact map_zero _

theorem hasSubst_truncFam (n : ℕ) : HasSubst (truncFam R n) := by
  refine ⟨fun m => by rw [constantCoeff_truncFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_Iio n).subset fun m hm => ?_
  by_contra hge
  exact hm (by rw [truncFam_of_le (not_lt.mp hge), map_zero])

theorem subst_truncFam (n : ℕ) (F : MvPowerSeries ℕ R) :
    subst (truncFam R n) F = killCompl (Fin.valEmbedding (n := n)) F := by
  classical
  ext x
  rw [coeff_subst (hasSubst_truncFam n), coeff_killCompl]
  have hprod : ∀ e : ℕ →₀ ℕ, (e.prod fun m k => truncFam R n m ^ k) =
      killCompl (Fin.valEmbedding (n := n)) (monomial e (1 : R)) := fun e => by
    rw [← prod_X_pow_eq_monomial, map_finsuppProd]
    simp only [map_pow]
    rfl
  simp only [hprod, coeff_killCompl, coeff_monomial]
  rw [finsum_eq_single _ (Finsupp.embDomain Fin.valEmbedding x)]
  · rw [if_pos rfl, smul_eq_mul, mul_one]
  · intro e he
    rw [if_neg (Ne.symm he), smul_zero]

theorem eq_of_forall_killCompl_eq (F G : MvPowerSeries ℕ R)
    (h : ∀ n : ℕ, killCompl (Fin.valEmbedding (n := n)) F = killCompl (Fin.valEmbedding (n := n)) G) :
    F = G := by
  ext e
  obtain ⟨n, hn⟩ : ∃ n, ∀ m ∈ e.support, m < n :=
    ⟨e.support.sup id + 1, fun m hm => Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)⟩
  obtain ⟨x, hx⟩ : e ∈ Set.range (Finsupp.embDomain (Fin.valEmbedding (n := n))) := by
    rw [Finsupp.mem_range_embDomain_iff]
    intro m hm
    exact ⟨⟨m, hn m hm⟩, rfl⟩
  rw [← hx, ← coeff_killCompl, ← coeff_killCompl, h n]

variable {p : ℕ} [hp : Fact p.Prime]

def truncPt (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (n : ℕ) : WittLaw.seriesPoint p R (Fin n) :=
  WittLaw.substPt (hasSubst_truncFam n) (constantCoeff_truncFam n) WittLaw.tautPt

theorem coeff_truncPt (n m : ℕ) :
    ((truncPt p R n : WittLaw.seriesPoint p R (Fin n)) : WittVector p (MvPowerSeries (Fin n) R)).coeff m =
      truncFam R n m := by
  rw [truncPt, WittLaw.coeff_substPt, WittLaw.coeff_tautPt]
  exact subst_X (hasSubst_truncFam n) m

theorem val_evalPt_truncPt {e : ℕ} {Ψ : MvFormalGroup e R} [Ψ.IsComm] (g : CartierModule p Ψ) (n : ℕ)
    (j : Fin e) :
    (evalPt g (truncPt p R n)).val j = killCompl (Fin.valEmbedding (n := n)) (g.toPowerSeries j) := by
  rw [← subst_truncFam]
  show subst _ (g.toPowerSeries j) = _
  congr 1
  funext m
  exact coeff_truncPt n m

variable [CharP R p] {d d' : ℕ} {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} [Φ.IsComm] [Φ'.IsComm]
  (θ : CartierModule p Φ →+ CartierModule p Φ')
  (hF : ∀ x, θ (frobenius x) = frobenius (θ x))
  (hV : ∀ x, θ (verschiebung x) = verschiebung (θ x))
  (hH : ∀ (a : R) x, θ (homothety a x) = homothety a (θ x))
  (f : Fin d → CartierModule p Φ) (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0)
  {uinv : Fin d → MvPowerSeries (Fin d) R}
  (hu0 : ∀ i, (uinv i).constantCoeff = 0) (hu : ∀ i, subst uinv ((GPt (p := p) f).val i) = X i)

theorem map_phiHom_eq (g : CartierModule p Φ) : CartierModule.map (phiHom θ hF hV hH f hf hu0 hu) g = θ g := by
  refine CartierModule.ext (funext fun j => eq_of_forall_killCompl_eq _ _ fun n => ?_)
  have key := congrArg (fun P : SeriesPoint Φ' (Fin n) => P.val j)
    (mapPt_phiHom_evalPt θ hF hV hH f hf hu0 hu g (truncPt p R n))
  try simp only at key
  rw [val_evalPt_truncPt] at key
  rw [← key, ← subst_truncFam]
  show subst (truncFam R n) (subst g.toPowerSeries (phiSeries θ f hu0 j)) =
    subst (evalPt g (truncPt p R n)).val (phiSeries θ f hu0 j)
  rw [subst_comp_subst_apply g.hasSubst_toPowerSeries (hasSubst_truncFam n)]
  congr 1
  funext i
  rw [subst_truncFam, val_evalPt_truncPt]

theorem exists_hom_map_eq (θ : CartierModule p Φ →+ CartierModule p Φ')
    (hF : ∀ x, θ (frobenius x) = frobenius (θ x))
    (hV : ∀ x, θ (verschiebung x) = verschiebung (θ x))
    (hH : ∀ (a : R) x, θ (homothety a x) = homothety a (θ x)) :
    ∃ φ : Φ.Hom Φ', ∀ g, CartierModule.map φ g = θ g := by
  classical
  have hsurj := MvFormalGroup.CartierModule.tangent_surjective p Φ
  choose f hf using fun i : Fin d => hsurj fun j => if i = j then (1 : R) else 0
  have hf' : ∀ i j, tangent (f i) j = if i = j then 1 else 0 := fun i j => congrFun (hf i) j
  obtain ⟨uinv, hu0, -, hu⟩ := MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one
    (GPt (p := p) f).val (GPt (p := p) f).constantCoeff_eq_zero (linearPart_GPt f hf')
  exact ⟨phiHom θ hF hV hH f hf' hu0 hu, map_phiHom_eq θ hF hV hH f hf' hu0 hu⟩

end Trunc

end P2mKcCartierFull
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_exists_hom_map_eq_of_perfectRing.P2mKcCartierFull"

end
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_exists_hom_map_eq_of_perfectRing.P2mKcCartierFull"

open MvFormalGroup MvFormalGroup.CartierModule in

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d d' : ℕ}
    (Φ : MvFormalGroup d k) (Φ' : MvFormalGroup d' k) [Φ.IsComm] [Φ'.IsComm]
    (θ : MvFormalGroup.CartierModule p Φ →+ MvFormalGroup.CartierModule p Φ')
    (hF : ∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
      MvFormalGroup.CartierModule.frobenius (θ f))
    (hV : ∀ f, θ (MvFormalGroup.CartierModule.verschiebung f) =
      MvFormalGroup.CartierModule.verschiebung (θ f))
    (hH : ∀ (a : k) f, θ (MvFormalGroup.CartierModule.homothety a f) =
      MvFormalGroup.CartierModule.homothety a (θ f)) :
    ∃ φ : Φ.Hom Φ', ∀ f, MvFormalGroup.CartierModule.map φ f = θ f :=
  P2mKcCartierFull.exists_hom_map_eq θ hF hV hH

end S_MvFormalGroup_CartierModule_exists_hom_map_eq_of_perfectRing
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_hom_map_eq_of_perfectRing (solution)
