-- Prove2me | solution 1 for MvFormalGroup.BigWittLaw.exists_hom_subst_curveFam_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/36ffd2ef-737d-58bd-a119-eee0f3866ae2

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_SymmetricPowerPowerSeriesFTSym
import Definitions.Def_SymmetricPowerBlockwiseFTSym
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq

set_option autoImplicit false

noncomputable section

universe u

open MvPowerSeries MvFormalGroup

namespace CartierFirstSol

variable {R : Type u} [CommRing R]

section Generic

variable {σ τ : Type*}

theorem constantCoeff_subst_of_constantCoeff_zero {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have h1 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  have h2 := constantCoeff_subst_eq_zero ha ha0 h1
  rw [subst_sub ha, subst_C, map_sub, constantCoeff_C] at h2
  exact sub_eq_zero.mp h2

def killFam (p : σ → Prop) [DecidablePred p] : σ → MvPowerSeries σ R :=
  fun s => if p s then X s else 0

theorem constantCoeff_killFam (p : σ → Prop) [DecidablePred p] (s : σ) :
    constantCoeff (killFam (R := R) p s) = 0 := by
  unfold killFam
  split_ifs
  · exact constantCoeff_X _
  · exact map_zero _

theorem hasSubst_killFam (p : σ → Prop) [DecidablePred p] : HasSubst (killFam (R := R) p) := by
  classical
  refine ⟨fun s => by rw [constantCoeff_killFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (e.support.finite_toSet).subset fun s hs => ?_
  simp only [Set.mem_setOf_eq, killFam] at hs
  by_contra hns
  apply hs
  split_ifs with h
  · rw [coeff_X, if_neg]
    intro he
    apply hns
    rw [he]
    simp
  · exact map_zero _

theorem coeff_subst_killFam (p : σ → Prop) [DecidablePred p] (f : MvPowerSeries σ R)
    (m : σ →₀ ℕ) :
    coeff m (subst (killFam p) f) = if ∀ s ∈ m.support, p s then coeff m f else 0 := by
  classical
  have hprod : ∀ e : σ →₀ ℕ, (e.prod fun s n => killFam (R := R) p s ^ n) =
      if ∀ s ∈ e.support, p s then monomial e (1 : R) else 0 := by
    intro e
    split_ifs with h
    · rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.prod]
      refine Finset.prod_congr rfl fun s hs => ?_
      rw [killFam, if_pos (h s hs)]
    · push Not at h
      obtain ⟨s, hs, hps⟩ := h
      rw [Finsupp.prod]
      refine Finset.prod_eq_zero hs ?_
      rw [killFam, if_neg hps]
      exact zero_pow (Finsupp.mem_support_iff.mp hs)
  rw [coeff_subst (hasSubst_killFam p), finsum_eq_single _ m]
  · rw [hprod]
    split_ifs with h
    · rw [coeff_monomial_same, smul_eq_mul, mul_one]
    · rw [map_zero, smul_zero]
  · intro e he
    rw [hprod]
    split_ifs with h
    · rw [coeff_monomial_ne he.symm, smul_zero]
    · rw [map_zero, smul_zero]

theorem eq_of_forall_subst_killFam_eq {ι : Type*} (p : ι → σ → Prop) [∀ i, DecidablePred (p i)]
    (hp : ∀ S : Finset σ, ∃ i, ∀ s ∈ S, p i s) {f g : MvPowerSeries σ R}
    (h : ∀ i, subst (killFam (R := R) (p i)) f = subst (killFam (R := R) (p i)) g) : f = g := by
  ext m
  obtain ⟨i, hi⟩ := hp m.support
  have := congrArg (coeff m) (h i)
  rwa [coeff_subst_killFam, coeff_subst_killFam, if_pos hi, if_pos hi] at this

end Generic

variable {d : ℕ}

@[scoped ext]
structure Pt (Φ : MvFormalGroup d R) (τ : Type) : Type u where

  val : Fin d → MvPowerSeries τ R
  cc : ∀ j, constantCoeff (val j) = 0

namespace Pt

variable {Φ : MvFormalGroup d R} {τ τ' : Type}

scoped instance : Zero (Pt Φ τ) := ⟨⟨fun _ => 0, fun _ => map_zero _⟩⟩

@[scoped simp] theorem val_zero : (0 : Pt Φ τ).val = fun _ => 0 := rfl

scoped instance : Add (Pt Φ τ) :=
  ⟨fun x y => ⟨fun j => subst (Sum.elim x.val y.val) (Φ.toPowerSeries j),
    constantCoeff_subst_elim Φ x.cc y.cc⟩⟩

theorem val_add (x y : Pt Φ τ) :
    (x + y).val = fun j => subst (Sum.elim x.val y.val) (Φ.toPowerSeries j) := rfl

scoped instance [Φ.IsComm] : AddCommMonoid (Pt Φ τ) where
  add_assoc x y z := Pt.ext (funext fun j => subst_elim_assoc Φ x.cc y.cc z.cc j)
  zero_add x := Pt.ext (funext fun j => subst_elim_zero_left Φ x.cc j)
  add_zero x := Pt.ext (funext fun j => subst_elim_zero_right Φ x.cc j)
  add_comm x y := Pt.ext (funext fun j => subst_elim_comm Φ x.cc y.cc j)
  nsmul := nsmulRec

def map [Φ.IsComm] {b : τ → MvPowerSeries τ' R} (hb : HasSubst b)
    (hb0 : ∀ s, constantCoeff (b s) = 0) : Pt Φ τ →+ Pt Φ τ' where
  toFun x := ⟨fun j => subst b (x.val j), fun j => constantCoeff_subst_eq_zero hb hb0 (x.cc j)⟩
  map_zero' := Pt.ext (funext fun j => by
    show subst b (0 : MvPowerSeries τ R) = 0
    rw [← coe_substAlgHom hb, map_zero])
  map_add' x y := Pt.ext (funext fun j => subst_subst_elim Φ x.cc y.cc hb j)

@[scoped simp] theorem map_val [Φ.IsComm] {b : τ → MvPowerSeries τ' R} (hb : HasSubst b)
    (hb0 : ∀ s, constantCoeff (b s) = 0) (x : Pt Φ τ) (j : Fin d) :
    (map hb hb0 x).val j = subst b (x.val j) := rfl

end Pt
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq.CartierFirstSol.Pt"

variable (Φ : MvFormalGroup d R) (γ : Fin d → PowerSeries R)
  (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0)

def curAt {τ : Type} (x : MvPowerSeries τ R) (hx : constantCoeff x = 0) : Pt Φ τ :=
  ⟨fun j => subst (fun _ : Unit => x) (γ j), fun j =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => hx) (fun _ => hx) (hγ j)⟩

@[scoped simp] theorem curAt_val {τ : Type} (x : MvPowerSeries τ R) (hx : constantCoeff x = 0) (j : Fin d) :
    (curAt Φ γ hγ x hx).val j = subst (fun _ : Unit => x) (γ j) := rfl

theorem map_curAt [Φ.IsComm] {τ τ' : Type} {b : τ → MvPowerSeries τ' R} (hb : HasSubst b)
    (hb0 : ∀ s, constantCoeff (b s) = 0) (x : MvPowerSeries τ R) (hx : constantCoeff x = 0) :
    Pt.map hb hb0 (curAt Φ γ hγ x hx) =
      curAt Φ γ hγ (subst b x) (constantCoeff_subst_eq_zero hb hb0 hx) := by
  refine Pt.ext (funext fun j => ?_)
  simp only [Pt.map_val, curAt_val]
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => hx) hb]

theorem curAt_zero {τ : Type} :
    curAt (τ := τ) Φ γ hγ 0 (map_zero _) = 0 :=
  Pt.ext (funext fun j => subst_zero_of_constantCoeff_eq_zero (hγ j))

def S [Φ.IsComm] (r : ℕ) : Pt Φ (Fin r) := ∑ i : Fin r, curAt Φ γ hγ (X i) (constantCoeff_X i)

theorem rename_S_val [Φ.IsComm] (r : ℕ) (σ : Equiv.Perm (Fin r)) (j : Fin d) :
    MvPowerSeries.rename σ ((S Φ γ hγ r).val j) = (S Φ γ hγ r).val j := by
  rw [MvPowerSeries.rename_eq_subst]
  have hb : HasSubst (X ∘ σ : Fin r → MvPowerSeries (Fin r) R) := HasSubst.X_comp _
  have hb0 : ∀ s, constantCoeff ((X ∘ σ : Fin r → MvPowerSeries (Fin r) R) s) = 0 :=
    fun s => constantCoeff_X _
  have key : Pt.map hb hb0 (S Φ γ hγ r) = S Φ γ hγ r := by
    unfold S
    rw [map_sum]
    calc ∑ i : Fin r, Pt.map hb hb0 (curAt Φ γ hγ (X i) (constantCoeff_X i))
        = ∑ i : Fin r, curAt Φ γ hγ (X (σ i)) (constantCoeff_X (σ i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_curAt]
          congr 1
          exact subst_X hb i
      _ = ∑ i : Fin r, curAt Φ γ hγ (X i) (constantCoeff_X i) :=
          Equiv.sum_comp σ (fun i => curAt Φ γ hγ (X i) (constantCoeff_X i))
  have := congrArg (fun x : Pt Φ (Fin r) => x.val j) key
  simpa only [Pt.map_val] using this

section Esymm

variable {A : Type*} [CommRing A]

theorem coeff_prod_one_add_C_mul_X {ι : Type*} (s : Finset ι) (x : ι → A) (k : ℕ) :
    PowerSeries.coeff k (∏ i ∈ s, (1 + PowerSeries.C (x i) * PowerSeries.X)) =
      ∑ t ∈ s.powersetCard k, ∏ i ∈ t, x i := by
  classical
  rw [Finset.prod_one_add, map_sum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const, PowerSeries.coeff_C_mul_X_pow]
  by_cases h : t.card = k
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem constantCoeff_prod_one_add_C_mul_X {ι : Type*} (s : Finset ι) (x : ι → A) :
    PowerSeries.constantCoeff (∏ i ∈ s, (1 + PowerSeries.C (x i) * PowerSeries.X)) = 1 := by
  rw [map_prod]
  exact Finset.prod_eq_one fun i _ => by simp

theorem aeval_esymm_eq_coeff_prod [Algebra R A] {ι : Type*} [Fintype ι] (f : ι → A) (n : ℕ) :
    MvPolynomial.aeval f (MvPolynomial.esymm ι R n) =
      PowerSeries.coeff n (∏ i : ι, (1 + PowerSeries.C (f i) * PowerSeries.X)) := by
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, Finset.esymm_map_val, coeff_prod_one_add_C_mul_X]

end Esymm
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq.CartierFirstSol.Pt"

variable (R) in

def dropLast (r : ℕ) : Fin (r + 1) → MvPowerSeries (Fin r) R :=
  fun i => if h : (i : ℕ) < r then X ⟨i, h⟩ else 0

theorem dropLast_castSucc (r : ℕ) (k : Fin r) : dropLast R r k.castSucc = X k := by
  simp [dropLast]

theorem dropLast_last (r : ℕ) : dropLast R r (Fin.last r) = 0 := by
  simp [dropLast]

theorem constantCoeff_dropLast (r : ℕ) (i : Fin (r + 1)) : constantCoeff (dropLast R r i) = 0 := by
  unfold dropLast
  split_ifs
  · exact constantCoeff_X _
  · exact map_zero _

theorem hasSubst_dropLast (r : ℕ) : HasSubst (dropLast R r) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_dropLast r)

theorem subst_dropLast_esymm (r n : ℕ) :
    subst (dropLast R r) ((MvPolynomial.esymm (Fin (r + 1)) R n : MvPolynomial (Fin (r + 1)) R) :
        MvPowerSeries (Fin (r + 1)) R) =
      ((MvPolynomial.esymm (Fin r) R n : MvPolynomial (Fin r) R) : MvPowerSeries (Fin r) R) := by
  rw [subst_coe, aeval_esymm_eq_coeff_prod, Fin.prod_univ_castSucc]
  simp only [dropLast_castSucc, dropLast_last, map_zero, zero_mul, add_zero, mul_one]
  have hR : ((MvPolynomial.esymm (Fin r) R n : MvPolynomial (Fin r) R) : MvPowerSeries (Fin r) R) =
      subst (X : Fin r → MvPowerSeries (Fin r) R) ((MvPolynomial.esymm (Fin r) R n :
        MvPolynomial (Fin r) R) : MvPowerSeries (Fin r) R) := by
    rw [subst_self]; rfl
  rw [hR, subst_coe, aeval_esymm_eq_coeff_prod]

open AlgebraicCurve.SymmetricPower.PowerSeriesFTSym in
/-!
                          -/

variable (R) in

def tFam (r : ℕ) : ℕ → MvPowerSeries (Fin r) R :=
  fun n => ((MvPolynomial.esymm (Fin r) R (n + 1) : MvPolynomial (Fin r) R) : MvPowerSeries (Fin r) R)

theorem tFam_eq_zero {r n : ℕ} (h : r ≤ n) : tFam R r n = 0 := by
  unfold tFam
  rw [MvPolynomial.esymm, Finset.powersetCard_eq_empty.mpr (by simp; omega), Finset.sum_empty,
    MvPolynomial.coe_zero]

open AlgebraicCurve.SymmetricPower.PowerSeriesFTSym in
theorem tFam_fin (r : ℕ) (i : Fin r) : tFam R r i = ea R r i := rfl

open AlgebraicCurve.SymmetricPower.PowerSeriesFTSym in
theorem degree_eq_of_coeff_tFam_ne_zero {r n : ℕ} {e : Fin r →₀ ℕ} (h : coeff e (tFam R r n) ≠ 0) :
    e.degree = n + 1 := by
  unfold tFam at h
  rw [MvPolynomial.coeff_coe] at h
  by_contra hne
  exact h ((esymm_isHomogeneous (n + 1)).coeff_eq_zero hne)

theorem constantCoeff_tFam (r n : ℕ) : constantCoeff (tFam R r n) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  by_contra h
  have := degree_eq_of_coeff_tFam_ne_zero h
  simp at this

theorem hasSubst_tFam (r : ℕ) : HasSubst (tFam R r) := by
  refine ⟨fun n => by rw [constantCoeff_tFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_singleton (e.degree - 1)).subset fun n hn => ?_
  have := degree_eq_of_coeff_tFam_ne_zero hn
  show n = e.degree - 1
  omega

variable (R) in

def inclFam (r : ℕ) : Fin r → MvPowerSeries ℕ R := fun i => X (i : ℕ)

theorem hasSubst_inclFam (r : ℕ) : HasSubst (inclFam R r) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem constantCoeff_inclFam (r : ℕ) (i : Fin r) : constantCoeff (inclFam R r i) = 0 :=
  constantCoeff_X _

variable (R) in

def truncFam (r : ℕ) : ℕ → MvPowerSeries (Fin r) R := fun n => if h : n < r then X ⟨n, h⟩ else 0

theorem constantCoeff_truncFam (r n : ℕ) : constantCoeff (truncFam R r n) = 0 := by
  unfold truncFam
  split_ifs
  · exact constantCoeff_X _
  · exact map_zero _

theorem hasSubst_truncFam (r : ℕ) : HasSubst (truncFam R r) := by
  refine ⟨fun n => by rw [constantCoeff_truncFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_Iio r).subset fun n hn => ?_
  by_contra h
  simp only [Set.mem_setOf_eq, truncFam, dif_neg (show ¬ n < r from h), map_zero, ne_eq,
    not_true_eq_false] at hn

variable (R) in

abbrev lowFam (r : ℕ) : ℕ → MvPowerSeries ℕ R := killFam (R := R) (· < r)

open AlgebraicCurve.SymmetricPower.PowerSeriesFTSym in
theorem subst_tFam_subst_inclFam (r : ℕ) (f : MvPowerSeries (Fin r) R) :
    subst (tFam R r) (subst (inclFam R r) f) = subst (ea R r) f := by
  rw [subst_comp_subst_apply (hasSubst_inclFam r) (hasSubst_tFam r)]
  congr 1
  funext i
  rw [inclFam, subst_X (hasSubst_tFam r), tFam_fin]

open AlgebraicCurve.SymmetricPower.PowerSeriesFTSym in
theorem subst_tFam_eq_subst_ea_subst_truncFam (r : ℕ) (f : MvPowerSeries ℕ R) :
    subst (tFam R r) f = subst (ea R r) (subst (truncFam R r) f) := by
  rw [subst_comp_subst_apply (hasSubst_truncFam r) (hasSubst_ea R r)]
  congr 1
  funext n
  unfold truncFam
  split_ifs with h
  · rw [subst_X (hasSubst_ea R r), ← tFam_fin]
  · rw [← coe_substAlgHom (hasSubst_ea R r), map_zero, tFam_eq_zero (not_lt.mp h)]

theorem subst_inclFam_subst_truncFam (r : ℕ) (f : MvPowerSeries ℕ R) :
    subst (inclFam R r) (subst (truncFam R r) f) = subst (lowFam R r) f := by
  rw [subst_comp_subst_apply (hasSubst_truncFam r) (hasSubst_inclFam r)]
  congr 1
  funext n
  unfold truncFam lowFam killFam
  split_ifs with h
  · rw [subst_X (hasSubst_inclFam r)]; rfl
  · rw [← coe_substAlgHom (hasSubst_inclFam r), map_zero]

theorem subst_lowFam_subst_inclFam (r : ℕ) (f : MvPowerSeries (Fin r) R) :
    subst (lowFam R r) (subst (inclFam R r) f) = subst (inclFam R r) f := by
  rw [subst_comp_subst_apply (hasSubst_inclFam r) (hasSubst_killFam _)]
  congr 1
  funext i
  rw [inclFam, subst_X (hasSubst_killFam _), killFam, if_pos i.2]

theorem subst_lowFam_subst_lowFam {r r' : ℕ} (h : r ≤ r') (f : MvPowerSeries ℕ R) :
    subst (lowFam R r) (subst (lowFam R r') f) = subst (lowFam R r) f := by
  rw [subst_comp_subst_apply (hasSubst_killFam _) (hasSubst_killFam _)]
  congr 1
  funext n
  simp only [lowFam, killFam]
  split_ifs with h1 h2 h2
  · rw [subst_X (hasSubst_killFam _), killFam, if_pos h2]
  · rw [subst_X (hasSubst_killFam _), killFam, if_neg h2]
  · omega
  · rw [← coe_substAlgHom (hasSubst_killFam _), map_zero]

theorem subst_tFam_subst_lowFam {r r' : ℕ} (h : r ≤ r') (f : MvPowerSeries ℕ R) :
    subst (tFam R r) (subst (lowFam R r') f) = subst (tFam R r) f := by
  rw [subst_comp_subst_apply (hasSubst_killFam _) (hasSubst_tFam r)]
  congr 1
  funext n
  simp only [killFam]
  split_ifs with h1
  · rw [subst_X (hasSubst_tFam r)]
  · rw [← coe_substAlgHom (hasSubst_tFam r), map_zero, tFam_eq_zero (by omega)]

open AlgebraicCurve.SymmetricPower.PowerSeriesFTSym in

theorem subst_tFam_subst_inclFam_succ (r : ℕ) (f : MvPowerSeries (Fin (r + 1)) R) :
    subst (tFam R r) (subst (inclFam R (r + 1)) f) = subst (dropLast R r) (subst (ea R (r + 1)) f) := by
  rw [subst_comp_subst_apply (hasSubst_inclFam (r + 1)) (hasSubst_tFam r),
    subst_comp_subst_apply (hasSubst_ea R (r + 1)) (hasSubst_dropLast r)]
  congr 1
  funext i
  rw [inclFam, subst_X (hasSubst_tFam r), ← tFam_fin, tFam, tFam, subst_dropLast_esymm]

section Limit

variable [Φ.IsComm]

open AlgebraicCurve.SymmetricPower.PowerSeriesFTSym in
theorem exists_Gfin (r : ℕ) (j : Fin d) :
    ∃ g : MvPowerSeries (Fin r) R, subst (ea R r) g = (S Φ γ hγ r).val j :=
  exists_subst_ea_eq fun σ => rename_S_val Φ γ hγ r σ j

def Gfin (r : ℕ) (j : Fin d) : MvPowerSeries (Fin r) R := (exists_Gfin Φ γ hγ r j).choose

open AlgebraicCurve.SymmetricPower.PowerSeriesFTSym in
theorem subst_ea_Gfin (r : ℕ) (j : Fin d) :
    subst (ea R r) (Gfin Φ γ hγ r j) = (S Φ γ hγ r).val j :=
  (exists_Gfin Φ γ hγ r j).choose_spec

open AlgebraicCurve.SymmetricPower.PowerSeriesFTSym in
theorem constantCoeff_Gfin (r : ℕ) (j : Fin d) : constantCoeff (Gfin Φ γ hγ r j) = 0 := by
  rw [← constantCoeff_subst_of_constantCoeff_zero (hasSubst_ea R r) constantCoeff_ea, subst_ea_Gfin]
  exact (S Φ γ hγ r).cc j

def Ginc (r : ℕ) (j : Fin d) : MvPowerSeries ℕ R := subst (inclFam R r) (Gfin Φ γ hγ r j)

theorem constantCoeff_Ginc (r : ℕ) (j : Fin d) : constantCoeff (Ginc Φ γ hγ r j) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_inclFam r) (constantCoeff_inclFam r) (constantCoeff_Gfin Φ γ hγ r j)

theorem subst_tFam_Ginc (r : ℕ) (j : Fin d) :
    subst (tFam R r) (Ginc Φ γ hγ r j) = (S Φ γ hγ r).val j := by
  rw [Ginc, subst_tFam_subst_inclFam, subst_ea_Gfin]

omit [Φ.IsComm] in
theorem curAt_congr {τ : Type} {x y : MvPowerSeries τ R} (h : x = y) (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) : curAt Φ γ hγ x hx = curAt Φ γ hγ y hy := by
  subst h; rfl

theorem map_dropLast_S (r : ℕ) :
    Pt.map (hasSubst_dropLast r) (constantCoeff_dropLast r) (S Φ γ hγ (r + 1)) = S Φ γ hγ r := by
  unfold S
  rw [map_sum, Fin.sum_univ_castSucc]
  have hlast : Pt.map (hasSubst_dropLast r) (constantCoeff_dropLast r)
      (curAt Φ γ hγ (X (Fin.last r)) (constantCoeff_X _)) = 0 := by
    rw [map_curAt, ← curAt_zero Φ γ hγ]
    exact curAt_congr Φ γ hγ (by rw [subst_X (hasSubst_dropLast r), dropLast_last]) _ _
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_curAt]
  exact curAt_congr Φ γ hγ (by rw [subst_X (hasSubst_dropLast r), dropLast_castSucc]) _ _

theorem subst_tFam_Ginc_succ (r : ℕ) (j : Fin d) :
    subst (tFam R r) (Ginc Φ γ hγ (r + 1) j) = (S Φ γ hγ r).val j := by
  rw [Ginc, subst_tFam_subst_inclFam_succ, subst_ea_Gfin, ← map_dropLast_S Φ γ hγ r, Pt.map_val]

open AlgebraicCurve.SymmetricPower.PowerSeriesFTSym in

theorem subst_lowFam_Ginc_succ (r : ℕ) (j : Fin d) :
    subst (lowFam R r) (Ginc Φ γ hγ (r + 1) j) = Ginc Φ γ hγ r j := by
  have h := subst_tFam_Ginc_succ Φ γ hγ r j
  rw [← subst_tFam_Ginc Φ γ hγ r j, subst_tFam_eq_subst_ea_subst_truncFam,
    subst_tFam_eq_subst_ea_subst_truncFam] at h
  have h2 := congrArg (subst (inclFam R r)) (subst_ea_injective h)
  rw [subst_inclFam_subst_truncFam, subst_inclFam_subst_truncFam] at h2
  rw [h2, Ginc, subst_lowFam_subst_inclFam]

theorem subst_lowFam_Ginc_of_le {r r' : ℕ} (h : r ≤ r') (j : Fin d) :
    subst (lowFam R r) (Ginc Φ γ hγ r' j) = Ginc Φ γ hγ r j := by
  induction r', h using Nat.le_induction with
  | base => rw [Ginc, subst_lowFam_subst_inclFam]
  | succ r' hr ih => rw [← subst_lowFam_subst_lowFam hr, subst_lowFam_Ginc_succ, ih]

def bound (m : ℕ →₀ ℕ) : ℕ := m.support.sup (· + 1)

theorem lt_bound {m : ℕ →₀ ℕ} {n : ℕ} (h : n ∈ m.support) : n < bound m :=
  Finset.le_sup (f := fun n => n + 1) h

def G (j : Fin d) : MvPowerSeries ℕ R := fun m => coeff m (Ginc Φ γ hγ (bound m) j)

theorem coeff_G (j : Fin d) (m : ℕ →₀ ℕ) :
    coeff m (G Φ γ hγ j) = coeff m (Ginc Φ γ hγ (bound m) j) := rfl

theorem coeff_Ginc_of_le {m : ℕ →₀ ℕ} {r a : ℕ} (hm : ∀ n ∈ m.support, n < r) (ha : r ≤ a)
    (j : Fin d) : coeff m (Ginc Φ γ hγ a j) = coeff m (Ginc Φ γ hγ r j) := by
  rw [← subst_lowFam_Ginc_of_le Φ γ hγ ha, coeff_subst_killFam, if_pos hm]

theorem subst_lowFam_G (r : ℕ) (j : Fin d) :
    subst (lowFam R r) (G Φ γ hγ j) = Ginc Φ γ hγ r j := by
  ext m
  rw [coeff_subst_killFam, ← subst_lowFam_Ginc_of_le Φ γ hγ (le_refl r), coeff_subst_killFam]
  split_ifs with h
  · rw [coeff_G, ← coeff_Ginc_of_le Φ γ hγ h (le_max_left r (bound m)),
      coeff_Ginc_of_le Φ γ hγ (fun n hn => lt_bound hn) (le_max_right r (bound m))]
  · rfl

theorem subst_tFam_G (r : ℕ) (j : Fin d) :
    subst (tFam R r) (G Φ γ hγ j) = (S Φ γ hγ r).val j := by
  rw [← subst_tFam_subst_lowFam (le_refl r), subst_lowFam_G, subst_tFam_Ginc]

theorem constantCoeff_G (j : Fin d) : constantCoeff (G Φ γ hγ j) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_G, coeff_zero_eq_constantCoeff_apply]
  exact constantCoeff_Ginc Φ γ hγ _ j

end Limit
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq.CartierFirstSol.Pt"

section TwoBlocks

open MvPowerSeries.BlockwiseFTSym

theorem coe_aeval {σ τ : Type*} (g : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    ((MvPolynomial.aeval g p : MvPolynomial τ R) : MvPowerSeries τ R) =
      MvPolynomial.aeval (fun s => ((g s : MvPolynomial τ R) : MvPowerSeries τ R)) p := by
  have h1 : ∀ q : MvPolynomial τ R,
      (q : MvPowerSeries τ R) = MvPolynomial.coeToMvPowerSeries.algHom R q := fun q => by
    rw [MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self, MvPowerSeries.map_id]
    rfl
  rw [h1, MvPolynomial.comp_aeval_apply]
  congr 1

abbrev two (r : ℕ) : Fin 2 → ℕ := fun _ => r

abbrev Idx (r : ℕ) : Type := Fin (∑ j, two r j)

abbrev emb (r : ℕ) (b : Fin 2) : Fin r → Idx r := MvPowerSeries.blockIn (rs := two r) b

def ePol (r : ℕ) (b : Fin 2) (k : ℕ) : MvPolynomial (Idx r) R :=
  MvPolynomial.rename (emb r b) (MvPolynomial.esymm (Fin r) R k)

theorem esymm_two_blocks (r n : ℕ) :
    MvPolynomial.esymm (Idx r) R (n + 1) =
      ePol (R := R) r 0 (n + 1) + ePol r 1 (n + 1) +
        ∑ i ∈ Finset.range n, ePol r 0 (i + 1) * ePol r 1 (n - 1 - i + 1) := by
  set F : Fin 2 → PowerSeries (MvPolynomial (Idx r) R) := fun b =>
    ∏ i : Fin r, (1 + PowerSeries.C (MvPolynomial.X (emb r b i) : MvPolynomial (Idx r) R) *
      PowerSeries.X) with hFdef
  have hF : ∀ b, PowerSeries.constantCoeff (F b) = 1 := fun b =>
    constantCoeff_prod_one_add_C_mul_X _ _
  have hcoef : ∀ b k, PowerSeries.coeff k (F b) = ePol (R := R) r b k := by
    intro b k
    rw [ePol, MvPolynomial.rename_eq_aeval, aeval_esymm_eq_coeff_prod]
    rfl
  have htot : MvPolynomial.esymm (Idx r) R (n + 1) = PowerSeries.coeff (n + 1) (F 0 * F 1) := by
    conv_lhs => rw [← MvPolynomial.aeval_X_left_apply (MvPolynomial.esymm (Idx r) R (n + 1))]
    rw [aeval_esymm_eq_coeff_prod]
    congr 1
    rw [← Equiv.prod_comp (finSigmaFinEquiv (n := two r)), Fintype.prod_sigma, Fin.prod_univ_two]
    simp only [hFdef, ← MvPowerSeries.blockIn_eq_finSigmaFinEquiv]
  rw [htot, BigWittLaw.coeff_succ_mul (hF 0) (hF 1) n]
  simp only [hcoef]

variable (R) in

def blkFam (r : ℕ) (b : Fin 2) : Fin r → MvPowerSeries (Idx r) R := fun i => X (emb r b i)

theorem hasSubst_blkFam (r : ℕ) (b : Fin 2) : HasSubst (blkFam R r b) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem constantCoeff_blkFam (r : ℕ) (b : Fin 2) (i : Fin r) : constantCoeff (blkFam R r b i) = 0 :=
  constantCoeff_X _

variable (R) in

def θFam (r : ℕ) : Fin 2 × ℕ → MvPowerSeries (Idx r) R :=
  fun bn => subst (blkFam R r bn.1) (tFam R r bn.2)

theorem θFam_eq_coe (r : ℕ) (b : Fin 2) (n : ℕ) :
    θFam R r (b, n) = ((ePol r b (n + 1) : MvPolynomial (Idx r) R) : MvPowerSeries (Idx r) R) := by
  show subst (blkFam R r b) (tFam R r n) = _
  rw [tFam, subst_coe, ePol, MvPolynomial.rename_eq_aeval, coe_aeval]
  have hf : blkFam R r b = fun s => (((MvPolynomial.X ∘ emb r b) s : MvPolynomial (Idx r) R) :
      MvPowerSeries (Idx r) R) := by
    funext i
    simp [blkFam]
  rw [hf]

theorem constantCoeff_θFam (r : ℕ) (bn : Fin 2 × ℕ) : constantCoeff (θFam R r bn) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_blkFam r bn.1) (constantCoeff_blkFam r bn.1)
    (constantCoeff_tFam r bn.2)

open AlgebraicCurve.SymmetricPower.PowerSeriesFTSym in
theorem hasSubst_θFam (r : ℕ) : HasSubst (θFam R r) := by
  refine ⟨fun bn => by rw [constantCoeff_θFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine ((Finset.univ : Finset (Fin 2)) ×ˢ ({e.degree - 1} : Finset ℕ)).finite_toSet.subset ?_
  rintro ⟨b, n⟩ hbn
  simp only [Set.mem_setOf_eq, θFam_eq_coe, MvPolynomial.coeff_coe] at hbn
  have hh : (ePol (R := R) r b (n + 1)).IsHomogeneous (n + 1) :=
    (esymm_isHomogeneous (n + 1)).rename_isHomogeneous
  have hdeg : e.degree = n + 1 := by
    by_contra hne
    exact hbn (hh.coeff_eq_zero hne)
  simp only [Finset.coe_product, Finset.coe_univ, Finset.coe_singleton, Set.mem_prod, Set.mem_univ,
    Set.mem_singleton_iff, true_and]
  omega

theorem subst_θFam_addFam (r n : ℕ) :
    subst (θFam R r) (BigWittLaw.addFam R n) = tFam R (∑ j, two r j) n := by
  rw [BigWittLaw.subst_addFam (hasSubst_θFam r) n, tFam, esymm_two_blocks]
  simp only [θFam_eq_coe, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add, map_mul, map_sum]

variable (R) in

def trunc2Fam (r : ℕ) : Fin 2 × ℕ → MvPowerSeries (Idx r) R :=
  fun bn => if h : bn.2 < r then X (emb r bn.1 ⟨bn.2, h⟩) else 0

theorem constantCoeff_trunc2Fam (r : ℕ) (bn : Fin 2 × ℕ) : constantCoeff (trunc2Fam R r bn) = 0 := by
  unfold trunc2Fam
  split_ifs
  · exact constantCoeff_X _
  · exact map_zero _

theorem hasSubst_trunc2Fam (r : ℕ) : HasSubst (trunc2Fam R r) := by
  refine ⟨fun bn => by rw [constantCoeff_trunc2Fam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine ((Set.finite_univ (α := Fin 2)).prod (Set.finite_Iio r)).subset ?_
  rintro ⟨b, n⟩ hbn
  refine ⟨Set.mem_univ _, ?_⟩
  by_contra h
  simp only [Set.mem_setOf_eq, trunc2Fam, dif_neg (show ¬ n < r from h), map_zero, ne_eq,
    not_true_eq_false] at hbn

variable (R) in

def backFam (r : ℕ) : Idx r → MvPowerSeries (Fin 2 × ℕ) R :=
  fun l => X ((toBlock (rs := two r) l).1, ((toBlock (rs := two r) l).2 : ℕ))

theorem hasSubst_backFam (r : ℕ) : HasSubst (backFam R r) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem subst_θFam_eq (r : ℕ) (f : MvPowerSeries (Fin 2 × ℕ) R) :
    subst (θFam R r) f = subst (bea R 2 (two r)) (subst (trunc2Fam R r) f) := by
  rw [subst_comp_subst_apply (hasSubst_trunc2Fam r) (hasSubst_bea R 2 (two r))]
  congr 1
  funext ⟨b, n⟩
  simp only [trunc2Fam]
  split_ifs with h
  · rw [subst_X (hasSubst_bea R 2 (two r)), bea, bes_blockIn_gen, θFam_eq_coe, ePol]
  · rw [← coe_substAlgHom (hasSubst_bea R 2 (two r)), map_zero]
    show subst (blkFam R r b) (tFam R r n) = 0
    rw [tFam_eq_zero (not_lt.mp h), ← coe_substAlgHom (hasSubst_blkFam r b), map_zero]

theorem subst_backFam_subst_trunc2Fam (r : ℕ) (f : MvPowerSeries (Fin 2 × ℕ) R) :
    subst (backFam R r) (subst (trunc2Fam R r) f) = subst (killFam fun bn : Fin 2 × ℕ => bn.2 < r) f := by
  rw [subst_comp_subst_apply (hasSubst_trunc2Fam r) (hasSubst_backFam r)]
  congr 1
  funext ⟨b, n⟩
  simp only [trunc2Fam, killFam]
  split_ifs with h
  · rw [subst_X (hasSubst_backFam r), backFam, toBlock_blockIn]
  · rw [← coe_substAlgHom (hasSubst_backFam r), map_zero]

theorem eq_of_forall_subst_θFam_eq {f g : MvPowerSeries (Fin 2 × ℕ) R}
    (h : ∀ r, subst (θFam R r) f = subst (θFam R r) g) : f = g := by
  refine eq_of_forall_subst_killFam_eq (fun (r : ℕ) (bn : Fin 2 × ℕ) => bn.2 < r)
    (fun T => ⟨T.sup fun bn => bn.2 + 1, fun bn hbn => Finset.le_sup (f := fun bn => bn.2 + 1) hbn⟩)
    fun r => ?_
  have h1 := h r
  rw [subst_θFam_eq, subst_θFam_eq] at h1
  have h2 := congrArg (subst (backFam R r)) (subst_bea_injective h1)
  rwa [subst_backFam_subst_trunc2Fam, subst_backFam_subst_trunc2Fam] at h2

variable [Φ.IsComm]

theorem S_two_blocks (r : ℕ) :
    S Φ γ hγ (∑ j, two r j) =
      Pt.map (hasSubst_blkFam r 0) (constantCoeff_blkFam r 0) (S Φ γ hγ r) +
        Pt.map (hasSubst_blkFam r 1) (constantCoeff_blkFam r 1) (S Φ γ hγ r) := by
  unfold S
  rw [map_sum, map_sum,
    ← Equiv.sum_comp (finSigmaFinEquiv (n := two r)) (fun l => curAt Φ γ hγ (X l) (constantCoeff_X l)),
    Fintype.sum_sigma,
    Fin.sum_univ_two (f := fun b : Fin 2 => ∑ y : Fin r,
      curAt Φ γ hγ (X (finSigmaFinEquiv (n := two r) ⟨b, y⟩)) (constantCoeff_X _))]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> rw [map_curAt] <;>
    exact curAt_congr Φ γ hγ
      (by rw [subst_X (hasSubst_blkFam r _), blkFam, emb, MvPowerSeries.blockIn_eq_finSigmaFinEquiv]) _ _

theorem subst_addFam_G (j : Fin d) :
    subst (BigWittLaw.addFam R) (G Φ γ hγ j) =
      subst
        (Sum.elim
          (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G Φ γ hγ l))
          fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G Φ γ hγ l))
        (Φ.toPowerSeries j) := by
  refine eq_of_forall_subst_θFam_eq fun r => ?_

  rw [subst_comp_subst_apply (BigWittLaw.hasSubst_addFam R) (hasSubst_θFam r)]
  have hL : (fun n => subst (θFam R r) (BigWittLaw.addFam R n)) = tFam R (∑ j, two r j) :=
    funext fun n => subst_θFam_addFam r n
  rw [hL, subst_tFam_G, S_two_blocks]

  have hA : ∀ b : Fin 2, ∀ l, constantCoeff
      (subst (fun m => (X (b, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G Φ γ hγ l)) = 0 :=
    fun b l => constantCoeff_subst_eq_zero (WittLaw.hasSubst_blk b) (WittLaw.constantCoeff_blk b)
      (constantCoeff_G Φ γ hγ l)
  rw [subst_subst_elim Φ (hA 0) (hA 1) (hasSubst_θFam r) j]
  have hblk : ∀ b : Fin 2, HasSubst (fun m : ℕ => (X (b, m) : MvPowerSeries (Fin 2 × ℕ) R)) :=
    fun b => WittLaw.hasSubst_blk b
  have hB : ∀ b : Fin 2, ∀ l, subst (θFam R r)
      (subst (fun m => (X (b, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G Φ γ hγ l)) =
      subst (blkFam R r b) ((S Φ γ hγ r).val l) := by
    intro b l
    rw [subst_comp_subst_apply (hblk b) (hasSubst_θFam r), ← subst_tFam_G Φ γ hγ r l,
      subst_comp_subst_apply (hasSubst_tFam r) (hasSubst_blkFam r b)]
    congr 1
    funext m
    exact subst_X (hasSubst_θFam r) (b, m)
  simp only [hB]
  rfl

end TwoBlocks
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq.CartierFirstSol.Pt"

section Final

variable [Φ.IsComm]

theorem curveFam_eq (n : ℕ) :
    CartierModule.curveFam R n =
      subst (fun _ : Fin 1 => (PowerSeries.X : PowerSeries R)) (tFam R 1 n) := by
  have hu : HasSubst (fun _ : Fin 1 => (PowerSeries.X : PowerSeries R)) :=
    hasSubst_of_constantCoeff_zero fun _ => PowerSeries.constantCoeff_X
  cases n with
  | zero =>
    rw [tFam, zero_add, MvPolynomial.esymm_one, Fin.sum_univ_one, MvPolynomial.coe_X, subst_X hu]
    rfl
  | succ k =>
    rw [tFam_eq_zero (by omega), ← coe_substAlgHom hu, map_zero]
    rfl

theorem subst_curveFam_G (j : Fin d) :
    subst (CartierModule.curveFam R) (G Φ γ hγ j) = γ j := by
  have hu : HasSubst (fun _ : Fin 1 => (PowerSeries.X : PowerSeries R)) :=
    hasSubst_of_constantCoeff_zero fun _ => PowerSeries.constantCoeff_X
  have h1 : CartierModule.curveFam R =
      fun n => subst (fun _ : Fin 1 => (PowerSeries.X : PowerSeries R)) (tFam R 1 n) :=
    funext curveFam_eq
  rw [h1, ← subst_comp_subst_apply (hasSubst_tFam 1) hu, subst_tFam_G]
  simp only [S, Fin.sum_univ_one, curAt_val]
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hu,
    subst_X hu]
  have hX : (fun _ : Unit => (PowerSeries.X : PowerSeries R)) = (X : Unit → MvPowerSeries Unit R) := by
    funext u; cases u; rfl
  rw [hX, subst_self]
  rfl

include hγ in

theorem main :
    ∃ G : Fin d → MvPowerSeries ℕ R,
      (∀ j, MvPowerSeries.constantCoeff (G j) = 0) ∧
      (∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (G j) =
          MvPowerSeries.subst
            (Sum.elim
              (fun l => MvPowerSeries.subst
                (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
              fun l => MvPowerSeries.subst
                (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
            (Φ.toPowerSeries j)) ∧
      (∀ j, MvPowerSeries.subst (MvFormalGroup.CartierModule.curveFam R) (G j) = γ j) :=
  ⟨G Φ γ hγ, constantCoeff_G Φ γ hγ, subst_addFam_G Φ γ hγ, subst_curveFam_G Φ γ hγ⟩

end Final
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq.CartierFirstSol.Pt"

end CartierFirstSol
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq.CartierFirstSol.Pt P2MW.S_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq.CartierFirstSol"

theorem solution
    {R : Type u} [CommRing R] {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (γ : Fin d → PowerSeries R) (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0) :
    ∃ G : Fin d → MvPowerSeries ℕ R,
      (∀ j, MvPowerSeries.constantCoeff (G j) = 0) ∧
      (∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (G j) =
          MvPowerSeries.subst
            (Sum.elim
              (fun l => MvPowerSeries.subst
                (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
              fun l => MvPowerSeries.subst
                (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
            (Φ.toPowerSeries j)) ∧
      (∀ j, MvPowerSeries.subst (MvFormalGroup.CartierModule.curveFam R) (G j) = γ j) :=
  CartierFirstSol.main Φ γ hγ

end
end S_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq
end P2MW
export P2MW.S_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq (solution)
