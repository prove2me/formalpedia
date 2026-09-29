-- Prove2me | solution 1 for MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebung_iterate_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/07543ec5-63c0-5b6f-b368-7cd98cb64e85

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebung_iterate_add

set_option autoImplicit false

noncomputable section

open MvPowerSeries MvFormalGroup MvFormalGroup.CartierModule

universe u

namespace P2mKcVComplete

section Congruence

variable {R : Type u} [CommRing R] {τ : Type*}

def bigO (τ : Type*) (R : Type u) [CommRing R] (n : ℕ) : Ideal (MvPowerSeries τ R) where
  carrier := {h | (n : ℕ∞) ≤ h.order}
  zero_mem' := by simp
  add_mem' {a b} ha hb := le_trans (le_min ha hb) min_order_le_add
  smul_mem' c {h} hh := le_trans (le_trans hh le_add_self) le_order_mul

theorem mem_bigO_iff {n : ℕ} {h : MvPowerSeries τ R} :
    h ∈ bigO τ R n ↔ ∀ e : τ →₀ ℕ, e.degree < n → coeff e h = 0 := by
  constructor
  · intro hh e he
    exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast he : ((e.degree : ℕ) : ℕ∞) < n) hh)
  · intro hh
    exact nat_le_order fun e he => hh e (by exact_mod_cast he)

theorem coeff_eq_of_sub_mem_bigO {n : ℕ} {f g : MvPowerSeries τ R} (hfg : f - g ∈ bigO τ R n)
    {e : τ →₀ ℕ} (he : e.degree < n) : coeff e f = coeff e g := by
  have h := (mem_bigO_iff.mp hfg) e he
  rwa [map_sub, sub_eq_zero] at h

theorem sub_mem_bigO_of_forall_coeff_eq {n : ℕ} {f g : MvPowerSeries τ R}
    (h : ∀ e : τ →₀ ℕ, e.degree < n → coeff e f = coeff e g) : f - g ∈ bigO τ R n :=
  mem_bigO_iff.mpr fun e he => by rw [map_sub, h e he, sub_self]

theorem bigO_antitone {m n : ℕ} (h : m ≤ n) {f : MvPowerSeries τ R} (hf : f ∈ bigO τ R n) :
    f ∈ bigO τ R m := by
  show (m : ℕ∞) ≤ f.order
  exact le_trans (by exact_mod_cast h) hf

theorem degree_le_order_prod {σ : Type*} {a : σ → MvPowerSeries τ R}
    (ha0 : ∀ s, (a s).constantCoeff = 0) (d : σ →₀ ℕ) :
    ((d.degree : ℕ) : ℕ∞) ≤ (d.prod fun s e => a s ^ e).order := by
  rw [Finsupp.prod, Finsupp.degree_apply, Nat.cast_sum]
  refine le_trans (Finset.sum_le_sum fun s _ => ?_) (le_order_prod _ _)
  exact le_order_pow_of_constantCoeff_eq_zero (d s) (ha0 s)

theorem coeff_subst_congr {σ : Type*} {a a' : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (ha' : HasSubst a') (ha0 : ∀ s, (a s).constantCoeff = 0) (ha0' : ∀ s, (a' s).constantCoeff = 0)
    {n : ℕ} (haa : ∀ s, a s - a' s ∈ bigO τ R n) {F F' : MvPowerSeries σ R}
    (hFF : ∀ d : σ →₀ ℕ, d.degree < n → coeff d F = coeff d F') {E : τ →₀ ℕ} (hE : E.degree < n) :
    coeff E (subst a F) = coeff E (subst a' F') := by
  rw [coeff_subst ha, coeff_subst ha']
  refine finsum_congr fun d => ?_
  by_cases hd : d.degree < n
  · rw [hFF d hd]
    congr 1
    refine coeff_eq_of_sub_mem_bigO ?_ hE
    rw [← Ideal.Quotient.eq, map_finsuppProd, map_finsuppProd]
    refine Finsupp.prod_congr fun s _ => ?_
    rw [map_pow, map_pow, (Ideal.Quotient.eq (I := bigO τ R n)).mpr (haa s)]
  · push Not at hd
    have hlt : ∀ {b : σ → MvPowerSeries τ R}, (∀ s, (b s).constantCoeff = 0) →
        coeff E (d.prod fun s e => b s ^ e) = 0 := by
      intro b hb0
      refine coeff_of_lt_order (lt_of_lt_of_le ?_ (degree_le_order_prod hb0 d))
      exact_mod_cast lt_of_lt_of_le hE hd
    rw [hlt ha0, hlt ha0', smul_zero, smul_zero]

theorem coeff_subst_congr_left {σ : Type*} {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (ha0 : ∀ s, (a s).constantCoeff = 0) {n : ℕ} {F F' : MvPowerSeries σ R}
    (hFF : ∀ d : σ →₀ ℕ, d.degree < n → coeff d F = coeff d F') {E : τ →₀ ℕ} (hE : E.degree < n) :
    coeff E (subst a F) = coeff E (subst a F') :=
  coeff_subst_congr ha ha ha0 ha0 (fun s => by rw [sub_self]; exact Ideal.zero_mem _) hFF hE

theorem subst_sub_subst_mem_bigO {σ : Type*} {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (ha0 : ∀ s, (a s).constantCoeff = 0) {n : ℕ} {F F' : MvPowerSeries σ R}
    (hFF : F - F' ∈ bigO σ R n) : subst a F - subst a F' ∈ bigO τ R n :=
  sub_mem_bigO_of_forall_coeff_eq fun _ hE =>
    coeff_subst_congr_left ha ha0 (fun _ hd => coeff_eq_of_sub_mem_bigO hFF hd) hE

end Congruence

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
variable {Φ : MvFormalGroup d R} [Φ.IsComm]

theorem le_order_iterate_verschiebung (N : ℕ) (t : CartierModule p Φ) (j : Fin d) :
    ((p ^ N : ℕ) : ℕ∞) ≤ (((⇑(verschiebung (p := p) (Φ := Φ)))^[N] t).toPowerSeries j).order := by
  induction N generalizing t with
  | zero =>
    rw [pow_zero, Function.iterate_zero_apply, Nat.cast_one]
    exact one_le_order_iff_constCoeff_eq_zero.mpr (t.constantCoeff_eq_zero j)
  | succ N ih =>
    rw [Function.iterate_succ_apply', toPowerSeries_verschiebung_eq_expand, order_expand]
    calc ((p ^ (N + 1) : ℕ) : ℕ∞) = p • (((p ^ N : ℕ) : ℕ∞)) := by
          rw [nsmul_eq_mul, ← Nat.cast_mul, pow_succ']
      _ ≤ p • _ := nsmul_le_nsmul_right (ih t) p

theorem iterate_verschiebung_mem_bigO (N : ℕ) (t : CartierModule p Φ) (j : Fin d) :
    ((⇑(verschiebung (p := p) (Φ := Φ)))^[N] t).toPowerSeries j ∈ bigO ℕ R (p ^ N) :=
  le_order_iterate_verschiebung N t j

theorem eq_zero_of_forall_exists_iterate_verschiebung (y : CartierModule p Φ)
    (hy : ∀ N : ℕ, ∃ t : CartierModule p Φ, y = (⇑(verschiebung (p := p) (Φ := Φ)))^[N] t) :
    y = 0 := by
  apply CartierModule.ext
  funext j
  show y.toPowerSeries j = 0
  rw [← order_eq_top_iff]
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  obtain ⟨t, ht⟩ := hy n
  calc (n : ℕ∞) ≤ ((p ^ n : ℕ) : ℕ∞) := by exact_mod_cast (Nat.lt_pow_self hp.out.one_lt).le
    _ ≤ _ := by rw [ht]; exact le_order_iterate_verschiebung n t j

theorem iterate_verschiebung_congr {n : ℕ} (N : ℕ) {y y' : CartierModule p Φ}
    (h : ∀ j, y.toPowerSeries j - y'.toPowerSeries j ∈ bigO ℕ R n) (j : Fin d) :
    ((⇑(verschiebung (p := p) (Φ := Φ)))^[N] y).toPowerSeries j -
      ((⇑(verschiebung (p := p) (Φ := Φ)))^[N] y').toPowerSeries j ∈ bigO ℕ R n := by
  induction N generalizing j with
  | zero => exact h j
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', toPowerSeries_verschiebung,
      toPowerSeries_verschiebung]
    exact subst_sub_subst_mem_bigO WittLaw.hasSubst_frobFam WittLaw.constantCoeff_frobFam
      (ih j)

omit [CharP R p] in

theorem add_congr_right {n : ℕ} (a : CartierModule p Φ) {b b' : CartierModule p Φ}
    (h : ∀ j, b.toPowerSeries j - b'.toPowerSeries j ∈ bigO ℕ R n) (j : Fin d) :
    (a + b).toPowerSeries j - (a + b').toPowerSeries j ∈ bigO ℕ R n := by
  rw [toPowerSeries_add, toPowerSeries_add]
  refine sub_mem_bigO_of_forall_coeff_eq fun E hE => ?_
  refine coeff_subst_congr (hasSubst_elim a.constantCoeff_eq_zero b.constantCoeff_eq_zero)
    (hasSubst_elim a.constantCoeff_eq_zero b'.constantCoeff_eq_zero)
    (by rintro (l | l); exacts [a.constantCoeff_eq_zero l, b.constantCoeff_eq_zero l])
    (by rintro (l | l); exacts [a.constantCoeff_eq_zero l, b'.constantCoeff_eq_zero l])
    (by rintro (l | l)
        · show a.toPowerSeries l - a.toPowerSeries l ∈ _
          rw [sub_self]; exact Ideal.zero_mem _
        · exact h l)
    (fun _ _ => rfl) hE

def verIter (N : ℕ) : CartierModule p Φ →+ CartierModule p Φ where
  toFun := (⇑(verschiebung (p := p) (Φ := Φ)))^[N]
  map_zero' := iterate_map_zero _ N
  map_add' := iterate_map_add _ N

@[scoped simp] theorem verIter_apply (N : ℕ) (t : CartierModule p Φ) :
    verIter N t = (⇑(verschiebung (p := p) (Φ := Φ)))^[N] t := rfl

def psum (N : ℕ) (x : ℕ → CartierModule p Φ) : CartierModule p Φ :=
  ∑ m ∈ Finset.range N, (⇑(verschiebung (p := p) (Φ := Φ)))^[m] (x m)

theorem psum_zero (x : ℕ → CartierModule p Φ) : psum 0 x = 0 := by
  simp [psum]

theorem psum_one (x : ℕ → CartierModule p Φ) : psum 1 x = x 0 := by
  simp [psum]

theorem psum_add (N K : ℕ) (x : ℕ → CartierModule p Φ) :
    psum (N + K) x = psum N x + (⇑(verschiebung (p := p) (Φ := Φ)))^[N] (psum K fun m => x (N + m)) := by
  rw [psum, Finset.sum_range_add, psum, psum, ← verIter_apply, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [verIter_apply, ← Function.iterate_add_apply, add_comm]

theorem psum_congr {N K : ℕ} (hNK : N ≤ K) (x : ℕ → CartierModule p Φ) (j : Fin d) :
    (psum K x).toPowerSeries j - (psum N x).toPowerSeries j ∈ bigO ℕ R (p ^ N) := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hNK
  rw [psum_add]
  have h := add_congr_right (n := p ^ N) (psum N x)
    (b := (⇑(verschiebung (p := p) (Φ := Φ)))^[N] (psum L fun m => x (N + m))) (b' := 0)
    (fun l => by
      rw [toPowerSeries_zero, sub_zero]
      exact iterate_verschiebung_mem_bigO N _ l) j
  rwa [add_zero] at h

def limSeries (x : ℕ → CartierModule p Φ) (j : Fin d) : MvPowerSeries ℕ R :=
  fun e => coeff e ((psum (e.degree + 1) x).toPowerSeries j)

theorem coeff_limSeries (x : ℕ → CartierModule p Φ) (j : Fin d) (e : ℕ →₀ ℕ) :
    coeff e (limSeries x j) = coeff e ((psum (e.degree + 1) x).toPowerSeries j) := by
  rw [coeff_apply]; rfl

theorem coeff_limSeries_eq (x : ℕ → CartierModule p Φ) (j : Fin d) {N : ℕ} {e : ℕ →₀ ℕ}
    (he : e.degree < p ^ N) : coeff e (limSeries x j) = coeff e ((psum N x).toPowerSeries j) := by
  rw [coeff_limSeries]
  set B := e.degree + 1 with hB
  have heB : e.degree < p ^ B := lt_trans (Nat.lt_succ_self _) (Nat.lt_pow_self hp.out.one_lt)
  have h1 := coeff_eq_of_sub_mem_bigO (psum_congr (le_max_right N B) x j) heB
  have h2 := coeff_eq_of_sub_mem_bigO (psum_congr (le_max_left N B) x j) he
  rw [← h1, h2]

theorem limSeries_sub_psum_mem_bigO (x : ℕ → CartierModule p Φ) (N : ℕ) (j : Fin d) :
    limSeries x j - (psum N x).toPowerSeries j ∈ bigO ℕ R (p ^ N) :=
  sub_mem_bigO_of_forall_coeff_eq fun _ he => coeff_limSeries_eq x j he

theorem constantCoeff_limSeries (x : ℕ → CartierModule p Φ) (j : Fin d) :
    (limSeries x j).constantCoeff = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_limSeries_eq x j (N := 0)
    (by rw [map_zero, pow_zero]; exact Nat.one_pos), psum_zero, toPowerSeries_zero]
  simp

def limElt (x : ℕ → CartierModule p Φ) : CartierModule p Φ where
  toPowerSeries := limSeries x
  constantCoeff_eq_zero := constantCoeff_limSeries x
  subst_eq := by
    intro j
    ext E

    set n := E.degree + 1 with hn
    have hEn : E.degree < n := Nat.lt_succ_self _
    have hnp : n ≤ p ^ n := (Nat.lt_pow_self hp.out.one_lt).le
    set s := psum n x with hs
    have hagree : ∀ l (e : ℕ →₀ ℕ), e.degree < n →
        coeff e (limSeries x l) = coeff e (s.toPowerSeries l) :=
      fun l e he => coeff_limSeries_eq x l (lt_of_lt_of_le he hnp)

    have hL : coeff E (subst (WittLaw.addFam p R) (limSeries x j)) =
        coeff E (subst (WittLaw.addFam p R) (s.toPowerSeries j)) :=
      coeff_subst_congr_left (WittLaw.hasSubst_addFam p R) (WittLaw.constantCoeff_addFam p R)
        (hagree j) hEn

    have h0 : ∀ (i : Fin 2) (g : Fin d → MvPowerSeries ℕ R), (∀ l, (g l).constantCoeff = 0) →
        ∀ l, (subst (fun m => (X (i, m) : MvPowerSeries (Fin 2 × ℕ) R)) (g l)).constantCoeff = 0 :=
      fun i g hg l => constantCoeff_subst_eq_zero (WittLaw.hasSubst_blk i)
        (WittLaw.constantCoeff_blk i) (hg l)
    have hblk : ∀ (i : Fin 2) (l : Fin d),
        subst (fun m => (X (i, m) : MvPowerSeries (Fin 2 × ℕ) R)) (limSeries x l) -
          subst (fun m => (X (i, m) : MvPowerSeries (Fin 2 × ℕ) R)) (s.toPowerSeries l) ∈
            bigO (Fin 2 × ℕ) R n :=
      fun i l => subst_sub_subst_mem_bigO (WittLaw.hasSubst_blk i)
        (WittLaw.constantCoeff_blk i) (sub_mem_bigO_of_forall_coeff_eq (hagree l))
    have hR : coeff E (subst (Sum.elim
          (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (limSeries x l))
          fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (limSeries x l))
          (Φ.toPowerSeries j)) =
        coeff E (subst (Sum.elim
          (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (s.toPowerSeries l))
          fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (s.toPowerSeries l))
          (Φ.toPowerSeries j)) := by
      refine coeff_subst_congr
        (hasSubst_elim (h0 0 _ (constantCoeff_limSeries x)) (h0 1 _ (constantCoeff_limSeries x)))
        (hasSubst_elim (h0 0 _ s.constantCoeff_eq_zero) (h0 1 _ s.constantCoeff_eq_zero))
        (by rintro (l | l)
            exacts [h0 0 _ (constantCoeff_limSeries x) l, h0 1 _ (constantCoeff_limSeries x) l])
        (by rintro (l | l)
            exacts [h0 0 _ s.constantCoeff_eq_zero l, h0 1 _ s.constantCoeff_eq_zero l])
        (by rintro (l | l); exacts [hblk 0 l, hblk 1 l]) (fun _ _ => rfl) hEn
    rw [hL, hR]
    exact congrArg (coeff E) (s.subst_eq j)

@[scoped simp] theorem toPowerSeries_limElt (x : ℕ → CartierModule p Φ) :
    (limElt x).toPowerSeries = limSeries x := rfl

theorem limElt_eq (x : ℕ → CartierModule p Φ) (N : ℕ) :
    limElt x = psum N x + (⇑(verschiebung (p := p) (Φ := Φ)))^[N] (limElt fun m => x (N + m)) := by
  apply CartierModule.ext
  funext j
  ext E
  set n := E.degree + 1 with hn
  have hEn : E.degree < n := Nat.lt_succ_self _
  have hnp : ∀ K, n ≤ p ^ (K + n) := fun K =>
    le_trans (Nat.lt_pow_self hp.out.one_lt).le (Nat.pow_le_pow_right hp.out.pos le_add_self)

  have hL : coeff E ((limElt x).toPowerSeries j) = coeff E ((psum (N + n) x).toPowerSeries j) :=
    coeff_limSeries_eq x j (lt_of_lt_of_le hEn (hnp N))

  have hshift : ∀ l, (limElt fun m => x (N + m)).toPowerSeries l -
      (psum n fun m => x (N + m)).toPowerSeries l ∈ bigO ℕ R n := fun l =>
    bigO_antitone (Nat.lt_pow_self hp.out.one_lt).le (limSeries_sub_psum_mem_bigO _ n l)
  have hR := coeff_eq_of_sub_mem_bigO
    (add_congr_right (psum N x) (iterate_verschiebung_congr N hshift) j) hEn
  rw [hL, hR, ← psum_add]

theorem existsUnique_sum (x : ℕ → CartierModule p Φ) :
    ∃! s : CartierModule p Φ, ∀ N : ℕ, ∃ t : CartierModule p Φ,
      s = psum N x + (⇑(verschiebung (p := p) (Φ := Φ)))^[N] t := by
  refine ⟨limElt x, fun N => ⟨limElt fun m => x (N + m), limElt_eq x N⟩, ?_⟩
  intro s' hs'
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_exists_iterate_verschiebung _ fun N => ?_
  obtain ⟨t', ht'⟩ := hs' N
  refine ⟨t' - limElt fun m => x (N + m), ?_⟩
  rw [iterate_map_sub, ht']
  conv_lhs => rw [limElt_eq x N]
  exact add_sub_add_left_eq_sub _ _ _

end P2mKcVComplete
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebung_iterate_add.P2mKcVComplete"

open P2mKcVComplete in
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] (x : ℕ → MvFormalGroup.CartierModule p Φ) :
    ∃! s : MvFormalGroup.CartierModule p Φ, ∀ N : ℕ, ∃ t : MvFormalGroup.CartierModule p Φ,
      s = (∑ m ∈ Finset.range N,
              (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[m] (x m)) +
            (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[N] t :=
  existsUnique_sum x

end
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebung_iterate_add.P2mKcVComplete"

end S_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebung_iterate_add
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebung_iterate_add (solution)
