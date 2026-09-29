-- Prove2me | solution 1 for MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ef66351d-28cd-5220-81e5-173c2866922d

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add

set_option autoImplicit false

noncomputable section

open MvPowerSeries MvFormalGroup MvFormalGroup.CartierModule

universe u

namespace P2mKcVIntComplete

section Congruence

variable {R : Type u} [CommRing R] {τ : Type*}

def bigO (w : τ → ℕ) (R : Type u) [CommRing R] (n : ℕ) : Ideal (MvPowerSeries τ R) where
  carrier := {h | (n : ℕ∞) ≤ h.weightedOrder w}
  zero_mem' := by simp
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (min_weightedOrder_le_add w)
  smul_mem' c {h} hh := le_trans (le_trans hh le_add_self) (le_weightedOrder_mul w)

theorem mem_bigO_iff {w : τ → ℕ} {n : ℕ} {h : MvPowerSeries τ R} :
    h ∈ bigO w R n ↔ ∀ e : τ →₀ ℕ, Finsupp.weight w e < n → coeff e h = 0 := by
  constructor
  · intro hh e he
    exact coeff_eq_zero_of_lt_weightedOrder w
      (lt_of_lt_of_le (by exact_mod_cast he : ((Finsupp.weight w e : ℕ) : ℕ∞) < n) hh)
  · intro hh
    exact nat_le_weightedOrder w fun e he => hh e he

theorem coeff_eq_of_sub_mem_bigO {w : τ → ℕ} {n : ℕ} {f g : MvPowerSeries τ R}
    (hfg : f - g ∈ bigO w R n) {e : τ →₀ ℕ} (he : Finsupp.weight w e < n) : coeff e f = coeff e g := by
  have h := (mem_bigO_iff.mp hfg) e he
  rwa [map_sub, sub_eq_zero] at h

theorem sub_mem_bigO_of_forall_coeff_eq {w : τ → ℕ} {n : ℕ} {f g : MvPowerSeries τ R}
    (h : ∀ e : τ →₀ ℕ, Finsupp.weight w e < n → coeff e f = coeff e g) : f - g ∈ bigO w R n :=
  mem_bigO_iff.mpr fun e he => by rw [map_sub, h e he, sub_self]

theorem bigO_antitone {w : τ → ℕ} {m n : ℕ} (h : m ≤ n) {f : MvPowerSeries τ R}
    (hf : f ∈ bigO w R n) : f ∈ bigO w R m := by
  show (m : ℕ∞) ≤ f.weightedOrder w
  exact le_trans (by exact_mod_cast h) hf

theorem weight_le_weightedOrder_prod {σ : Type*} {wσ : σ → ℕ} {wτ : τ → ℕ}
    {a : σ → MvPowerSeries τ R} (ha : ∀ s, ((wσ s : ℕ) : ℕ∞) ≤ (a s).weightedOrder wτ)
    (d : σ →₀ ℕ) :
    ((Finsupp.weight wσ d : ℕ) : ℕ∞) ≤ (d.prod fun s e => a s ^ e).weightedOrder wτ := by
  rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
  refine le_trans (Finset.sum_le_sum fun s _ => ?_) (le_weightedOrder_prod wτ _ _)
  have h1 : (d s : ℕ∞) * (wσ s : ℕ∞) ≤ (d s : ℕ∞) * (a s).weightedOrder wτ :=
    mul_le_mul_right (ha s) _
  have h2 := le_weightedOrder_pow wτ (f := a s) (d s)
  rw [nsmul_eq_mul] at h2
  rw [smul_eq_mul, Nat.cast_mul]
  exact h1.trans h2

theorem coeff_subst_congr {σ : Type*} {wσ : σ → ℕ} {wτ : τ → ℕ} {a a' : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (ha' : HasSubst a')
    (hw : ∀ s, ((wσ s : ℕ) : ℕ∞) ≤ (a s).weightedOrder wτ)
    (hw' : ∀ s, ((wσ s : ℕ) : ℕ∞) ≤ (a' s).weightedOrder wτ)
    {n : ℕ} (haa : ∀ s, a s - a' s ∈ bigO wτ R n) {F F' : MvPowerSeries σ R}
    (hFF : ∀ d : σ →₀ ℕ, Finsupp.weight wσ d < n → coeff d F = coeff d F') {E : τ →₀ ℕ}
    (hE : Finsupp.weight wτ E < n) :
    coeff E (subst a F) = coeff E (subst a' F') := by
  rw [coeff_subst ha, coeff_subst ha']
  refine finsum_congr fun d => ?_
  by_cases hd : Finsupp.weight wσ d < n
  · rw [hFF d hd]
    congr 1
    refine coeff_eq_of_sub_mem_bigO ?_ hE
    rw [← Ideal.Quotient.eq, map_finsuppProd, map_finsuppProd]
    refine Finsupp.prod_congr fun s _ => ?_
    rw [map_pow, map_pow, (Ideal.Quotient.eq (I := bigO wτ R n)).mpr (haa s)]
  · push Not at hd
    have hlt : ∀ {b : σ → MvPowerSeries τ R}, (∀ s, ((wσ s : ℕ) : ℕ∞) ≤ (b s).weightedOrder wτ) →
        coeff E (d.prod fun s e => b s ^ e) = 0 := by
      intro b hb
      refine coeff_eq_zero_of_lt_weightedOrder wτ
        (lt_of_lt_of_le ?_ (weight_le_weightedOrder_prod hb d))
      exact_mod_cast lt_of_lt_of_le hE hd
    rw [hlt hw, hlt hw', smul_zero, smul_zero]

theorem coeff_subst_congr_left {σ : Type*} {wσ : σ → ℕ} {wτ : τ → ℕ} {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (hw : ∀ s, ((wσ s : ℕ) : ℕ∞) ≤ (a s).weightedOrder wτ) {n : ℕ}
    {F F' : MvPowerSeries σ R} (hFF : ∀ d : σ →₀ ℕ, Finsupp.weight wσ d < n → coeff d F = coeff d F')
    {E : τ →₀ ℕ} (hE : Finsupp.weight wτ E < n) :
    coeff E (subst a F) = coeff E (subst a F') :=
  coeff_subst_congr ha ha hw hw (fun s => by rw [sub_self]; exact Ideal.zero_mem _) hFF hE

theorem subst_sub_subst_mem_bigO {σ : Type*} {wσ : σ → ℕ} {wτ : τ → ℕ} {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (hw : ∀ s, ((wσ s : ℕ) : ℕ∞) ≤ (a s).weightedOrder wτ) {n : ℕ}
    {F F' : MvPowerSeries σ R} (hFF : F - F' ∈ bigO wσ R n) :
    subst a F - subst a F' ∈ bigO wτ R n :=
  sub_mem_bigO_of_forall_coeff_eq fun _ hE =>
    coeff_subst_congr_left ha hw (fun _ hd => coeff_eq_of_sub_mem_bigO hFF hd) hE

theorem le_weightedOrder_subst_of_le {σ : Type*} {wσ : σ → ℕ} {wτ : τ → ℕ}
    {a : σ → MvPowerSeries τ R} (ha : HasSubst a) (c : ℕ)
    (hle : ∀ s, (((c * wσ s : ℕ)) : ℕ∞) ≤ (a s).weightedOrder wτ) (g : MvPowerSeries σ R) :
    (c : ℕ∞) * g.weightedOrder wσ ≤ (subst a g).weightedOrder wτ := by
  refine le_weightedOrder wτ fun E hE => ?_
  rw [coeff_subst ha]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : coeff d g = 0
  · rw [hd, zero_smul]
  · have hWd : g.weightedOrder wσ ≤ (Finsupp.weight wσ d : ℕ) := weightedOrder_le wσ hd
    have hprod : (((c * Finsupp.weight wσ d : ℕ)) : ℕ∞) ≤
        (d.prod fun s e => a s ^ e).weightedOrder wτ := by
      have h := weight_le_weightedOrder_prod (wσ := fun s => c * wσ s) hle d
      have hw : Finsupp.weight (fun s => c * wσ s) d = c * Finsupp.weight wσ d := by
        rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [smul_eq_mul, smul_eq_mul]
        ring
      rwa [hw] at h
    have hlt : ((Finsupp.weight wτ E : ℕ) : ℕ∞) < (d.prod fun s e => a s ^ e).weightedOrder wτ := by
      refine lt_of_lt_of_le (lt_of_lt_of_le hE ?_) hprod
      calc (c : ℕ∞) * g.weightedOrder wσ ≤ (c : ℕ∞) * (Finsupp.weight wσ d : ℕ) :=
            mul_le_mul_right hWd _
        _ = (((c * Finsupp.weight wσ d : ℕ)) : ℕ∞) := by rw [Nat.cast_mul]
    rw [coeff_eq_zero_of_lt_weightedOrder wτ hlt, smul_zero]

theorem one_le_weightedOrder_of_constantCoeff {w : τ → ℕ} (hw : ∀ s, 0 < w s) {f : MvPowerSeries τ R}
    (hf : f.constantCoeff = 0) : (((1 : ℕ)) : ℕ∞) ≤ f.weightedOrder w := by
  refine nat_le_weightedOrder w fun e he => ?_
  have he0 : e = 0 := by
    by_contra hne
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hne
    have h1 : e s ≤ Finsupp.weight w e := Finsupp.le_weight w (hw s).ne' e
    have h2 : 0 < e s := Nat.pos_of_ne_zero hs
    omega
  rw [he0, coeff_zero_eq_constantCoeff_apply, hf]

theorem le_weightedOrder_X {w : τ → ℕ} (s : τ) :
    ((w s : ℕ) : ℕ∞) ≤ (X s : MvPowerSeries τ R).weightedOrder w := by
  classical
  refine nat_le_weightedOrder w fun e he => ?_
  rw [coeff_X]
  split_ifs with h
  · subst h
    exfalso
    rw [Finsupp.weight_single, one_smul] at he
    exact lt_irrefl _ he
  · rfl

end Congruence

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}
variable {Φ : MvFormalGroup d R} [Φ.IsComm]

variable (p) in

def pw : ℕ → ℕ := fun m => p ^ m

variable (p) in

def pw2 : Fin 2 × ℕ → ℕ := WittLaw.weight p fun _ : Fin 2 => 1

omit hp in
theorem pw_apply (m : ℕ) : pw p m = p ^ m := rfl

omit hp in
theorem pw2_apply (i : Fin 2) (m : ℕ) : pw2 p (i, m) = p ^ m := by
  show 1 * p ^ m = p ^ m
  rw [one_mul]

theorem pw_pos (m : ℕ) : 0 < pw p m := pow_pos hp.out.pos m

theorem le_weightedOrder_frobPolyFam (n : ℕ) :
    (((p * pw p n : ℕ)) : ℕ∞) ≤ (WittLaw.frobPolyFam p R n).weightedOrder (pw p) := by
  refine nat_le_weightedOrder _ fun e he => ?_
  by_contra hne
  have hw := WittLaw.weight_eq_of_coeff_frobPolyFam_ne_zero (p := p) (R := R) hne
  have hw' : Finsupp.weight (pw p) e = p ^ (n + 1) := hw
  rw [hw', pw_apply, ← pow_succ'] at he
  exact lt_irrefl _ he

theorem le_weightedOrder_frobPolyFam' (n : ℕ) :
    ((pw p n : ℕ) : ℕ∞) ≤ (WittLaw.frobPolyFam p R n).weightedOrder (pw p) :=
  le_trans (by exact_mod_cast Nat.le_mul_of_pos_left _ hp.out.pos) (le_weightedOrder_frobPolyFam n)

theorem le_weightedOrder_addFam (n : ℕ) :
    ((pw p n : ℕ) : ℕ∞) ≤ (WittLaw.addFam p R n).weightedOrder (pw2 p) := by
  refine nat_le_weightedOrder _ fun e he => ?_
  by_contra hne
  have hw := WittLaw.weight_eq_of_coeff_addFam_ne_zero p R hne
  have hw' : Finsupp.weight (pw2 p) e = p ^ n := hw
  rw [hw', pw_apply] at he
  exact lt_irrefl _ he

omit hp in

theorem le_weightedOrder_blk (i : Fin 2) (m : ℕ) :
    ((pw p m : ℕ) : ℕ∞) ≤ (X (i, m) : MvPowerSeries (Fin 2 × ℕ) R).weightedOrder (pw2 p) := by
  have h := le_weightedOrder_X (R := R) (w := pw2 p) (i, m)
  rwa [pw2_apply] at h

omit [Φ.IsComm] in

theorem one_le_weightedOrder_toPowerSeries (t : CartierModule p Φ) (j : Fin d) :
    (((1 : ℕ)) : ℕ∞) ≤ (t.toPowerSeries j).weightedOrder (pw p) :=
  one_le_weightedOrder_of_constantCoeff pw_pos (t.constantCoeff_eq_zero j)

theorem le_weightedOrder_iterate_verschiebungInt (N : ℕ) (t : CartierModule p Φ) (j : Fin d) :
    ((p ^ N : ℕ) : ℕ∞) ≤
      (((⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] t).toPowerSeries j).weightedOrder (pw p) := by
  induction N generalizing t with
  | zero =>
    rw [pow_zero, Function.iterate_zero_apply]
    exact one_le_weightedOrder_toPowerSeries t j
  | succ N ih =>
    rw [Function.iterate_succ_apply', toPowerSeries_verschiebungInt]
    have h := le_weightedOrder_subst_of_le (wσ := pw p) (wτ := pw p)
      (WittLaw.hasSubst_frobPolyFam (p := p) (R := R)) p le_weightedOrder_frobPolyFam
      (((⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] t).toPowerSeries j)
    refine le_trans ?_ h
    calc ((p ^ (N + 1) : ℕ) : ℕ∞) = (p : ℕ∞) * ((p ^ N : ℕ) : ℕ∞) := by
          rw [← Nat.cast_mul, pow_succ']
      _ ≤ (p : ℕ∞) * _ := mul_le_mul_right (ih t) _

theorem iterate_verschiebungInt_mem_bigO (N : ℕ) (t : CartierModule p Φ) (j : Fin d) :
    ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] t).toPowerSeries j ∈ bigO (pw p) R (p ^ N) :=
  le_weightedOrder_iterate_verschiebungInt N t j

theorem eq_zero_of_forall_exists_iterate_verschiebungInt (y : CartierModule p Φ)
    (hy : ∀ N : ℕ, ∃ t : CartierModule p Φ, y = (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] t) :
    y = 0 := by
  apply CartierModule.ext
  funext j
  show y.toPowerSeries j = 0
  rw [← weightedOrder_eq_top_iff (pw p)]
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  obtain ⟨t, ht⟩ := hy n
  calc (n : ℕ∞) ≤ ((p ^ n : ℕ) : ℕ∞) := by exact_mod_cast (Nat.lt_pow_self hp.out.one_lt).le
    _ ≤ _ := by rw [ht]; exact le_weightedOrder_iterate_verschiebungInt n t j

theorem iterate_verschiebungInt_congr {n : ℕ} (N : ℕ) {y y' : CartierModule p Φ}
    (h : ∀ j, y.toPowerSeries j - y'.toPowerSeries j ∈ bigO (pw p) R n) (j : Fin d) :
    ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] y).toPowerSeries j -
      ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] y').toPowerSeries j ∈ bigO (pw p) R n := by
  induction N generalizing j with
  | zero => exact h j
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', toPowerSeries_verschiebungInt,
      toPowerSeries_verschiebungInt]
    exact subst_sub_subst_mem_bigO WittLaw.hasSubst_frobPolyFam le_weightedOrder_frobPolyFam' (ih j)

theorem add_congr_right {n : ℕ} (a : CartierModule p Φ) {b b' : CartierModule p Φ}
    (h : ∀ j, b.toPowerSeries j - b'.toPowerSeries j ∈ bigO (pw p) R n) (j : Fin d) :
    (a + b).toPowerSeries j - (a + b').toPowerSeries j ∈ bigO (pw p) R n := by
  rw [toPowerSeries_add, toPowerSeries_add]
  refine sub_mem_bigO_of_forall_coeff_eq fun E hE => ?_
  refine coeff_subst_congr (wσ := fun _ : Fin d ⊕ Fin d => 1)
    (hasSubst_elim a.constantCoeff_eq_zero b.constantCoeff_eq_zero)
    (hasSubst_elim a.constantCoeff_eq_zero b'.constantCoeff_eq_zero)
    (by rintro (l | l)
        exacts [one_le_weightedOrder_toPowerSeries a l, one_le_weightedOrder_toPowerSeries b l])
    (by rintro (l | l)
        exacts [one_le_weightedOrder_toPowerSeries a l, one_le_weightedOrder_toPowerSeries b' l])
    (by rintro (l | l)
        · show a.toPowerSeries l - a.toPowerSeries l ∈ _
          rw [sub_self]; exact Ideal.zero_mem _
        · exact h l)
    (fun _ _ => rfl) hE

def verIter (N : ℕ) : CartierModule p Φ →+ CartierModule p Φ where
  toFun := (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N]
  map_zero' := iterate_map_zero _ N
  map_add' := iterate_map_add _ N

@[scoped simp] theorem verIter_apply (N : ℕ) (t : CartierModule p Φ) :
    verIter N t = (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] t := rfl

def psum (N : ℕ) (x : ℕ → CartierModule p Φ) : CartierModule p Φ :=
  ∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (x m)

theorem psum_zero (x : ℕ → CartierModule p Φ) : psum 0 x = 0 := by
  simp [psum]

theorem psum_add (N K : ℕ) (x : ℕ → CartierModule p Φ) :
    psum (N + K) x =
      psum N x + (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (psum K fun m => x (N + m)) := by
  rw [psum, Finset.sum_range_add, psum, psum, ← verIter_apply, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [verIter_apply, ← Function.iterate_add_apply, add_comm]

theorem psum_congr {N K : ℕ} (hNK : N ≤ K) (x : ℕ → CartierModule p Φ) (j : Fin d) :
    (psum K x).toPowerSeries j - (psum N x).toPowerSeries j ∈ bigO (pw p) R (p ^ N) := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hNK
  rw [psum_add]
  have h := add_congr_right (n := p ^ N) (psum N x)
    (b := (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (psum L fun m => x (N + m))) (b' := 0)
    (fun l => by
      rw [toPowerSeries_zero, sub_zero]
      exact iterate_verschiebungInt_mem_bigO N _ l) j
  rwa [add_zero] at h

def limSeries (x : ℕ → CartierModule p Φ) (j : Fin d) : MvPowerSeries ℕ R :=
  fun e => coeff e ((psum (Finsupp.weight (pw p) e + 1) x).toPowerSeries j)

theorem coeff_limSeries (x : ℕ → CartierModule p Φ) (j : Fin d) (e : ℕ →₀ ℕ) :
    coeff e (limSeries x j) =
      coeff e ((psum (Finsupp.weight (pw p) e + 1) x).toPowerSeries j) := by
  rw [coeff_apply]; rfl

theorem coeff_limSeries_eq (x : ℕ → CartierModule p Φ) (j : Fin d) {N : ℕ} {e : ℕ →₀ ℕ}
    (he : Finsupp.weight (pw p) e < p ^ N) :
    coeff e (limSeries x j) = coeff e ((psum N x).toPowerSeries j) := by
  rw [coeff_limSeries]
  set B := Finsupp.weight (pw p) e + 1 with hB
  have heB : Finsupp.weight (pw p) e < p ^ B :=
    lt_trans (Nat.lt_succ_self _) (Nat.lt_pow_self hp.out.one_lt)
  have h1 := coeff_eq_of_sub_mem_bigO (psum_congr (le_max_right N B) x j) heB
  have h2 := coeff_eq_of_sub_mem_bigO (psum_congr (le_max_left N B) x j) he
  rw [← h1, h2]

theorem limSeries_sub_psum_mem_bigO (x : ℕ → CartierModule p Φ) (N : ℕ) (j : Fin d) :
    limSeries x j - (psum N x).toPowerSeries j ∈ bigO (pw p) R (p ^ N) :=
  sub_mem_bigO_of_forall_coeff_eq fun _ he => coeff_limSeries_eq x j he

theorem constantCoeff_limSeries (x : ℕ → CartierModule p Φ) (j : Fin d) :
    (limSeries x j).constantCoeff = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_limSeries_eq x j (N := 0)
    (by rw [map_zero, pow_zero]; exact Nat.one_pos), psum_zero, toPowerSeries_zero]
  simp

theorem one_le_weightedOrder_limSeries (x : ℕ → CartierModule p Φ) (j : Fin d) :
    (((1 : ℕ)) : ℕ∞) ≤ (limSeries x j).weightedOrder (pw p) :=
  one_le_weightedOrder_of_constantCoeff pw_pos (constantCoeff_limSeries x j)

theorem one_le_weightedOrder_subst_blk (i : Fin 2) {g : MvPowerSeries ℕ R} (hg : g.constantCoeff = 0) :
    (((1 : ℕ)) : ℕ∞) ≤
      (subst (fun m => (X (i, m) : MvPowerSeries (Fin 2 × ℕ) R)) g).weightedOrder (pw2 p) := by
  refine one_le_weightedOrder_of_constantCoeff (fun im => ?_) ?_
  · show 0 < 1 * p ^ im.2
    rw [one_mul]; exact pow_pos hp.out.pos _
  · exact constantCoeff_subst_eq_zero (WittLaw.hasSubst_blk i) (WittLaw.constantCoeff_blk i) hg

def limElt (x : ℕ → CartierModule p Φ) : CartierModule p Φ where
  toPowerSeries := limSeries x
  constantCoeff_eq_zero := constantCoeff_limSeries x
  subst_eq := by
    intro j
    ext E

    set n := Finsupp.weight (pw2 p) E + 1 with hn
    have hEn : Finsupp.weight (pw2 p) E < n := Nat.lt_succ_self _
    have hnp : n ≤ p ^ n := (Nat.lt_pow_self hp.out.one_lt).le
    set s := psum n x with hs
    have hagree : ∀ l (e : ℕ →₀ ℕ), Finsupp.weight (pw p) e < n →
        coeff e (limSeries x l) = coeff e (s.toPowerSeries l) :=
      fun l e he => coeff_limSeries_eq x l (lt_of_lt_of_le he hnp)

    have hL : coeff E (subst (WittLaw.addFam p R) (limSeries x j)) =
        coeff E (subst (WittLaw.addFam p R) (s.toPowerSeries j)) :=
      coeff_subst_congr_left (wσ := pw p) (wτ := pw2 p) (WittLaw.hasSubst_addFam p R)
        le_weightedOrder_addFam (hagree j) hEn

    have h0 : ∀ (i : Fin 2) (g : Fin d → MvPowerSeries ℕ R), (∀ l, (g l).constantCoeff = 0) →
        ∀ l, (subst (fun m => (X (i, m) : MvPowerSeries (Fin 2 × ℕ) R)) (g l)).constantCoeff = 0 :=
      fun i g hg l => constantCoeff_subst_eq_zero (WittLaw.hasSubst_blk i)
        (WittLaw.constantCoeff_blk i) (hg l)
    have hblk : ∀ (i : Fin 2) (l : Fin d),
        subst (fun m => (X (i, m) : MvPowerSeries (Fin 2 × ℕ) R)) (limSeries x l) -
          subst (fun m => (X (i, m) : MvPowerSeries (Fin 2 × ℕ) R)) (s.toPowerSeries l) ∈
            bigO (pw2 p) R n :=
      fun i l => subst_sub_subst_mem_bigO (wσ := pw p) (WittLaw.hasSubst_blk i)
        (le_weightedOrder_blk i) (sub_mem_bigO_of_forall_coeff_eq (hagree l))
    have hR : coeff E (subst (Sum.elim
          (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (limSeries x l))
          fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (limSeries x l))
          (Φ.toPowerSeries j)) =
        coeff E (subst (Sum.elim
          (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (s.toPowerSeries l))
          fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (s.toPowerSeries l))
          (Φ.toPowerSeries j)) := by
      refine coeff_subst_congr (wσ := fun _ : Fin d ⊕ Fin d => 1)
        (hasSubst_elim (h0 0 _ (constantCoeff_limSeries x)) (h0 1 _ (constantCoeff_limSeries x)))
        (hasSubst_elim (h0 0 _ s.constantCoeff_eq_zero) (h0 1 _ s.constantCoeff_eq_zero))
        (by rintro (l | l)
            exacts [one_le_weightedOrder_subst_blk 0 (constantCoeff_limSeries x l),
              one_le_weightedOrder_subst_blk 1 (constantCoeff_limSeries x l)])
        (by rintro (l | l)
            exacts [one_le_weightedOrder_subst_blk 0 (s.constantCoeff_eq_zero l),
              one_le_weightedOrder_subst_blk 1 (s.constantCoeff_eq_zero l)])
        (by rintro (l | l); exacts [hblk 0 l, hblk 1 l]) (fun _ _ => rfl) hEn
    rw [hL, hR]
    exact congrArg (coeff E) (s.subst_eq j)

@[scoped simp] theorem toPowerSeries_limElt (x : ℕ → CartierModule p Φ) :
    (limElt x).toPowerSeries = limSeries x := rfl

theorem limElt_eq (x : ℕ → CartierModule p Φ) (N : ℕ) :
    limElt x =
      psum N x + (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (limElt fun m => x (N + m)) := by
  apply CartierModule.ext
  funext j
  ext E
  set n := Finsupp.weight (pw p) E + 1 with hn
  have hEn : Finsupp.weight (pw p) E < n := Nat.lt_succ_self _
  have hnp : ∀ K, n ≤ p ^ (K + n) := fun K =>
    le_trans (Nat.lt_pow_self hp.out.one_lt).le (Nat.pow_le_pow_right hp.out.pos le_add_self)

  have hL : coeff E ((limElt x).toPowerSeries j) = coeff E ((psum (N + n) x).toPowerSeries j) :=
    coeff_limSeries_eq x j (lt_of_lt_of_le hEn (hnp N))

  have hshift : ∀ l, (limElt fun m => x (N + m)).toPowerSeries l -
      (psum n fun m => x (N + m)).toPowerSeries l ∈ bigO (pw p) R n := fun l =>
    bigO_antitone (Nat.lt_pow_self hp.out.one_lt).le (limSeries_sub_psum_mem_bigO _ n l)
  have hR := coeff_eq_of_sub_mem_bigO
    (add_congr_right (psum N x) (iterate_verschiebungInt_congr N hshift) j) hEn
  rw [hL, hR, ← psum_add]

theorem existsUnique_sum (x : ℕ → CartierModule p Φ) :
    ∃! s : CartierModule p Φ, ∀ N : ℕ, ∃ t : CartierModule p Φ,
      s = psum N x + (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] t := by
  refine ⟨limElt x, fun N => ⟨limElt fun m => x (N + m), limElt_eq x N⟩, ?_⟩
  intro s' hs'
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_exists_iterate_verschiebungInt _ fun N => ?_
  obtain ⟨t', ht'⟩ := hs' N
  refine ⟨t' - limElt fun m => x (N + m), ?_⟩
  rw [iterate_map_sub, ht']
  conv_lhs => rw [limElt_eq x N]
  exact add_sub_add_left_eq_sub _ _ _

end P2mKcVIntComplete
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add.P2mKcVIntComplete"

open P2mKcVIntComplete in
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] (x : ℕ → MvFormalGroup.CartierModule p Φ) :
    ∃! s : MvFormalGroup.CartierModule p Φ, ∀ N : ℕ, ∃ t : MvFormalGroup.CartierModule p Φ,
      s = (∑ m ∈ Finset.range N,
              (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m] (x m)) +
            (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] t :=
  existsUnique_sum x

end
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add.P2mKcVIntComplete"

end S_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add (solution)
