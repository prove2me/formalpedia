-- Prove2me | solution 1 for MvFormalGroup.Hom.exists_subst_eq_X_and_coeff_subst_eq_zero_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/39e914d1-f1ab-55b5-959c-e2aa14ccd532

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Theorems.Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
import Theorems.Thm_MvPowerSeries_coeff_sumElim_single_subst_add_sum_X_mul_eq
import Theorems.Thm_MvPowerSeries_coeff_sumElim_zero_subst_add_sum_X_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_Hom_exists_subst_eq_X_and_coeff_subst_eq_zero_of_not_dvd

set_option autoImplicit false

noncomputable section

universe u

namespace P2mKcNormalForm

open MvPowerSeries MvFormalGroup

section Calculus

variable {k : Type u} [CommRing k]

def pd {σ : Type*} (s : σ) (f : MvPowerSeries σ k) : MvPowerSeries σ k :=
  fun m => ((m s + 1 : ℕ) : k) * coeff (m + Finsupp.single s 1) f

theorem coeff_pd {σ : Type*} (s : σ) (f : MvPowerSeries σ k) (m : σ →₀ ℕ) :
    coeff m (pd s f) = ((m s + 1 : ℕ) : k) * coeff (m + Finsupp.single s 1) f := rfl

theorem pd_add {σ : Type*} (s : σ) (f g : MvPowerSeries σ k) : pd s (f + g) = pd s f + pd s g := by
  ext m; simp only [coeff_pd, map_add, mul_add]

theorem pd_smul {σ : Type*} (s : σ) (c : k) (f : MvPowerSeries σ k) : pd s (c • f) = c • pd s f := by
  ext m; simp only [coeff_pd, map_smul, smul_eq_mul]; ring

theorem pd_sum {σ : Type*} {ι : Type*} (s : σ) (t : Finset ι) (f : ι → MvPowerSeries σ k) :
    pd s (∑ i ∈ t, f i) = ∑ i ∈ t, pd s (f i) := by
  ext m; simp only [coeff_pd, map_sum, Finset.mul_sum]

theorem pd_zero {σ : Type*} (s : σ) : pd s (0 : MvPowerSeries σ k) = 0 := by
  ext m; simp [coeff_pd]

theorem pd_X {σ : Type*} [DecidableEq σ] (s t : σ) :
    pd s (X t : MvPowerSeries σ k) = if s = t then 1 else 0 := by
  ext m
  rw [coeff_pd, coeff_X]
  by_cases hst : s = t
  · subst hst
    rw [if_pos rfl]
    by_cases hm : m = 0
    · subst hm; simp
    · rw [coeff_one, if_neg hm, if_neg, mul_zero]
      intro h
      apply hm
      have := congrArg (fun n => n - Finsupp.single s 1) h
      simpa using this
  · rw [if_neg hst, if_neg, mul_zero, map_zero]
    intro h
    have := congrArg (fun n => n s) h
    simp [Ne.symm hst] at this

theorem pd_C {σ : Type*} (s : σ) (c : k) : pd s (C c : MvPowerSeries σ k) = 0 := by
  classical
  ext m
  rw [coeff_pd, coeff_C, if_neg, mul_zero, map_zero]
  intro h
  have := congrArg (fun n => n s) h
  simp at this

theorem pd_one {σ : Type*} (s : σ) : pd s (1 : MvPowerSeries σ k) = 0 := by
  rw [← map_one (C (σ := σ) (R := k)), pd_C]

theorem constantCoeff_pd {σ : Type*} (s : σ) (f : MvPowerSeries σ k) :
    constantCoeff (pd s f) = coeff (Finsupp.single s 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pd]
  simp

theorem hDf_pd {σ : Type*} (f : MvPowerSeries σ k) :
    ∀ (i : σ) (m : σ →₀ ℕ), coeff m (pd i f) = ((m i + 1 : ℕ) : k) * coeff (m + Finsupp.single i 1) f :=
  fun i m => coeff_pd i f m

theorem coeff_mul_congr_le {τ : Type*} {a a' b b' : MvPowerSeries τ k} (N : τ →₀ ℕ)
    (ha : ∀ n ≤ N, coeff n a = coeff n a') (hb : ∀ n ≤ N, coeff n b = coeff n b') :
    ∀ n ≤ N, coeff n (a * b) = coeff n (a' * b') := by
  classical
  intro n hn
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h1 : x.1 ≤ N := le_trans (by rw [← hx]; exact le_self_add) hn
  have h2 : x.2 ≤ N := le_trans (by rw [← hx]; exact le_add_self) hn
  rw [ha _ h1, hb _ h2]

theorem coeff_pow_congr_le {τ : Type*} {a a' : MvPowerSeries τ k} (N : τ →₀ ℕ)
    (ha : ∀ n ≤ N, coeff n a = coeff n a') (e : ℕ) :
    ∀ n ≤ N, coeff n (a ^ e) = coeff n (a' ^ e) := by
  induction e with
  | zero => intro n _; simp
  | succ e ih =>
    intro n hn
    rw [pow_succ, pow_succ]
    exact coeff_mul_congr_le N ih ha n hn

theorem coeff_prod_congr_le {τ ι : Type*} (t : Finset ι) {u v : ι → MvPowerSeries τ k} (N : τ →₀ ℕ)
    (h : ∀ i ∈ t, ∀ n ≤ N, coeff n (u i) = coeff n (v i)) :
    ∀ n ≤ N, coeff n (∏ i ∈ t, u i) = coeff n (∏ i ∈ t, v i) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro n _; simp
  | insert i t hi ih =>
    intro n hn
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact coeff_mul_congr_le N (h i (Finset.mem_insert_self i t))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)) n hn

theorem coeff_subst_congr_le {σ τ : Type*} {a b : σ → MvPowerSeries τ k}
    (ha : HasSubst a) (hb : HasSubst b) (N : τ →₀ ℕ)
    (h : ∀ s, ∀ n ≤ N, coeff n (a s) = coeff n (b s)) (f : MvPowerSeries σ k) :
    coeff N (subst a f) = coeff N (subst b f) := by
  classical
  rw [coeff_subst ha, coeff_subst hb]
  refine finsum_congr fun e => ?_
  congr 1
  rw [Finsupp.prod, Finsupp.prod]
  exact coeff_prod_congr_le e.support N (fun i _ => coeff_pow_congr_le N (h i) (e i)) N le_rfl

theorem sumElim_cases {τ : Type*} (n : τ ⊕ Unit →₀ ℕ) (m : τ →₀ ℕ)
    (hn : n ≤ m.sumElim (Finsupp.single () 1)) :
    ∃ n' : τ →₀ ℕ, n = n'.sumElim 0 ∨ n = n'.sumElim (Finsupp.single () 1) := by
  refine ⟨n.comapDomain Sum.inl Sum.inl_injective.injOn, ?_⟩
  have hu : n (Sum.inr ()) ≤ 1 := by
    have := hn (Sum.inr ())
    simpa [Finsupp.sumElim_inr] using this
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hu with h0 | h1
  · left
    ext s
    rcases s with t | ⟨⟩
    · simp [Finsupp.sumElim_inl, Finsupp.comapDomain_apply]
    · simp [Finsupp.sumElim_inr, h0]
  · right
    ext s
    rcases s with t | ⟨⟩
    · simp [Finsupp.sumElim_inl, Finsupp.comapDomain_apply]
    · simp [Finsupp.sumElim_inr, h1]

theorem pd_subst {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
    (G : σ → MvPowerSeries τ k) (hG : ∀ s, constantCoeff (G s) = 0)
    (f : MvPowerSeries σ k) (t : τ) :
    pd t (subst G f) = ∑ s, pd t (G s) * subst G (pd s f) := by
  classical
  have hGs := hasSubst_of_constantCoeff_zero hG

  let famX : τ → MvPowerSeries (τ ⊕ Unit) k := fun t' =>
    subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ Unit) k)) (X t' : MvPowerSeries τ k) +
      ∑ k' : Unit, X (Sum.inr k') *
        subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ Unit) k))
          ((fun (t' : τ) (_ : Unit) => (if t' = t then 1 else 0 : MvPowerSeries τ k)) t' k')
  let famG : σ → MvPowerSeries (τ ⊕ Unit) k := fun s =>
    subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ Unit) k)) (G s) +
      ∑ k' : Unit, X (Sum.inr k') *
        subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ Unit) k))
          ((fun (s : σ) (_ : Unit) => pd t (G s)) s k')
  have hXinl : HasSubst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ Unit) k)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hfamX0 : ∀ t', constantCoeff (famX t') = 0 := by
    intro t'
    simp only [famX, map_add, map_sum, map_mul, constantCoeff_X, zero_mul, Finset.sum_const_zero, add_zero]
    rw [subst_X hXinl, constantCoeff_X]
  have hfamG0 : ∀ s, constantCoeff (famG s) = 0 := by
    intro s
    simp only [famG, map_add, map_sum, map_mul, constantCoeff_X, zero_mul, Finset.sum_const_zero, add_zero]
    exact constantCoeff_subst_eq_zero hXinl (fun _ => constantCoeff_X _) (hG s)
  have hfamXs := hasSubst_of_constantCoeff_zero hfamX0
  have hfamGs := hasSubst_of_constantCoeff_zero hfamG0
  have hX0 : ∀ i : τ, constantCoeff (X i : MvPowerSeries τ k) = 0 := fun _ => constantCoeff_X _
  ext m

  have h1 := MvPowerSeries.coeff_sumElim_single_subst_add_sum_X_mul_eq (subst G f)
    (fun t' => pd t' (subst G f)) (hDf_pd _) (fun i => (X i : MvPowerSeries τ k)) hX0
    (fun (t' : τ) (_ : Unit) => (if t' = t then 1 else 0 : MvPowerSeries τ k)) m ()
  change coeff (m.sumElim (Finsupp.single () 1)) (subst famX (subst G f)) = _ at h1
  have hsum1 : (∑ i : τ, (if i = t then (1 : MvPowerSeries τ k) else 0) *
      subst (fun i => (X i : MvPowerSeries τ k)) (pd i (subst G f))) = pd t (subst G f) := by
    rw [Finset.sum_eq_single t]
    · rw [if_pos rfl, one_mul]; exact congrFun subst_self _
    · intro i _ hit; rw [if_neg hit, zero_mul]
    · intro h; exact absurd (Finset.mem_univ t) h
  rw [hsum1] at h1
  rw [← h1]

  rw [subst_comp_subst_apply hGs hfamXs]

  have hcong : coeff (m.sumElim (Finsupp.single () 1)) (subst (fun s => subst famX (G s)) f) =
      coeff (m.sumElim (Finsupp.single () 1)) (subst famG f) := by
    refine coeff_subst_congr_le
      (hasSubst_of_constantCoeff_zero fun s => constantCoeff_subst_eq_zero hfamXs hfamX0 (hG s))
      hfamGs _ (fun s n hn => ?_) f
    obtain ⟨n', hn' | hn'⟩ := sumElim_cases n m hn
    ·
      rw [hn']
      have hL := MvPowerSeries.coeff_sumElim_zero_subst_add_sum_X_mul_eq (G s)
        (fun i => (X i : MvPowerSeries τ k)) hX0
        (fun (t' : τ) (_ : Unit) => (if t' = t then 1 else 0 : MvPowerSeries τ k)) n'
      change coeff (n'.sumElim 0) (subst famX (G s)) = _ at hL
      have hR := MvPowerSeries.coeff_sumElim_zero_subst_add_sum_X_mul_eq (X s : MvPowerSeries σ k) G hG
        (fun (s' : σ) (_ : Unit) => pd t (G s')) n'
      change coeff (n'.sumElim 0) (subst famG (X s)) = _ at hR
      rw [subst_X hfamGs] at hR
      rw [hL, hR, subst_X hGs]
      exact congrArg _ (congrFun subst_self _)
    ·
      rw [hn']
      have hL := MvPowerSeries.coeff_sumElim_single_subst_add_sum_X_mul_eq (G s)
        (fun t' => pd t' (G s)) (hDf_pd _) (fun i => (X i : MvPowerSeries τ k)) hX0
        (fun (t' : τ) (_ : Unit) => (if t' = t then 1 else 0 : MvPowerSeries τ k)) n' ()
      change coeff (n'.sumElim (Finsupp.single () 1)) (subst famX (G s)) = _ at hL
      have hR := MvPowerSeries.coeff_sumElim_single_subst_add_sum_X_mul_eq (X s : MvPowerSeries σ k)
        (fun s' => pd s' (X s : MvPowerSeries σ k)) (hDf_pd _) G hG
        (fun (s' : σ) (_ : Unit) => pd t (G s')) n' ()
      change coeff (n'.sumElim (Finsupp.single () 1)) (subst famG (X s)) = _ at hR
      rw [subst_X hfamGs] at hR
      rw [hL, hR]
      congr 1
      rw [Finset.sum_eq_single t, Finset.sum_eq_single s]
      · rw [if_pos rfl, one_mul, pd_X, if_pos rfl, ← coe_substAlgHom hGs, map_one, mul_one]
        exact congrFun subst_self _
      · intro s' _ hs'
        rw [pd_X, if_neg hs', ← coe_substAlgHom hGs, map_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ s) h
      · intro t' _ ht'; rw [if_neg ht', zero_mul]
      · intro h; exact absurd (Finset.mem_univ t) h
  rw [hcong]

  have h4 := MvPowerSeries.coeff_sumElim_single_subst_add_sum_X_mul_eq f (fun s => pd s f) (hDf_pd f)
    G hG (fun (s : σ) (_ : Unit) => pd t (G s)) m ()
  exact h4

end Calculus

section SubstHelpers

variable {k : Type u} [CommRing k]

theorem constantCoeff_subst_of_zero {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ k}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ k) :
    constantCoeff (subst a f) = constantCoeff f := by
  classical
  have ha := hasSubst_of_constantCoeff_zero ha0
  rw [MvPowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra hc
      push Not at hc
      exact he (Finsupp.ext hc)
    have hz : constantCoeff (e.prod fun s n => a s ^ n) = 0 := by
      rw [Finsupp.prod, map_prod]
      refine Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) ?_
      rw [map_pow, ha0, zero_pow hs]
    rw [hz, smul_zero]

theorem subst_zero_family {σ τ : Type*} [Finite σ] (g : MvPowerSeries σ k) :
    subst (fun _ : σ => (0 : MvPowerSeries τ k)) g = C (constantCoeff g) := by
  classical
  ext n
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun _ => map_zero _), finsum_eq_single _ 0, coeff_C]
  · by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn]; simp [coeff_one, hn]
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra hc
      push Not at hc
      exact he (Finsupp.ext hc)
    have hz : (e.prod fun _ n => (0 : MvPowerSeries τ k) ^ n) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [zero_pow hs])
    rw [hz, map_zero, smul_zero]

end SubstHelpers

section LinTuple

variable {k : Type u} [Field k] {d : ℕ}

def linTuple (A : Matrix (Fin d) (Fin d) k) : Fin d → MvPowerSeries (Fin d) k :=
  fun i => ∑ j, A i j • (X j : MvPowerSeries (Fin d) k)

theorem constantCoeff_linTuple (A : Matrix (Fin d) (Fin d) k) (i : Fin d) :
    (linTuple A i).constantCoeff = 0 := by
  simp [linTuple, map_sum, constantCoeff_X]

theorem hasSubst_linTuple (A : Matrix (Fin d) (Fin d) k) : HasSubst (linTuple A) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_linTuple A)

theorem linearPart_linTuple (A : Matrix (Fin d) (Fin d) k) : linearPart (linTuple A) = A := by
  classical
  ext i j
  simp only [linearPart, Matrix.of_apply, linTuple, map_sum, map_smul, coeff_index_single_X,
    smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hlj
    simp [Ne.symm hlj]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem subst_linTuple {τ : Type*} {b : Fin d → MvPowerSeries τ k} (hb : HasSubst b)
    (A : Matrix (Fin d) (Fin d) k) (i : Fin d) :
    subst b (linTuple A i) = ∑ j, A i j • b j := by
  simp only [linTuple, ← coe_substAlgHom hb, map_sum, map_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coe_substAlgHom hb, subst_X hb]

theorem subst_linTuple_linTuple (A B : Matrix (Fin d) (Fin d) k) (i : Fin d) :
    subst (linTuple B) (linTuple A i) = linTuple (A * B) i := by
  rw [subst_linTuple (hasSubst_linTuple B)]
  simp only [linTuple, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem linTuple_one (i : Fin d) : linTuple (1 : Matrix (Fin d) (Fin d) k) i = X i := by
  classical
  simp only [linTuple, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem linearPart_sum_smul (A : Matrix (Fin d) (Fin d) k) (c : Fin d → MvPowerSeries (Fin d) k) :
    linearPart (fun i => ∑ j, A i j • c j) = A * linearPart c := by
  ext i l
  simp [linearPart, Matrix.mul_apply, map_sum]

end LinTuple

section Key

variable {k : Type u} [Field k] {d : ℕ}

def ev0fam : Fin d ⊕ Fin d → MvPowerSeries (Fin d) k :=
  Sum.elim (fun i => (X i : MvPowerSeries (Fin d) k)) fun _ => 0

theorem ev0fam_zero (s : Fin d ⊕ Fin d) : constantCoeff (ev0fam (k := k) (d := d) s) = 0 := by
  rcases s with i | i
  · exact constantCoeff_X _
  · exact map_zero _

theorem hasSubst_ev0fam : HasSubst (ev0fam (k := k) (d := d)) :=
  hasSubst_of_constantCoeff_zero ev0fam_zero

variable (Ψ : MvFormalGroup d k)

def Cf (j l : Fin d) : MvPowerSeries (Fin d) k :=
  subst (ev0fam (k := k) (d := d)) (pd (Sum.inr j) (Ψ.toPowerSeries l))

theorem constantCoeff_Cf (j l : Fin d) : constantCoeff (Cf Ψ j l) = if l = j then 1 else 0 := by
  rw [Cf, constantCoeff_subst_of_zero ev0fam_zero, constantCoeff_pd, Ψ.coeff_single_inr]

theorem ev0_law (l : Fin d) :
    subst (ev0fam (k := k) (d := d)) (Ψ.toPowerSeries l) = (X l : MvPowerSeries (Fin d) k) :=
  Ψ.subst_elim_zero_right (fun j => constantCoeff_X j) l

variable {Ψ} {Φ : MvFormalGroup d k} (ψ : Ψ.Hom Φ)

theorem sum_Cf_pd_eq_zero (v : Fin d → k) (hv : (linearPart ψ.toPowerSeries).mulVec v = 0)
    (i : Fin d) :
    (∑ j, v j • ∑ l, Cf Ψ j l * pd l (ψ.toPowerSeries i)) = 0 := by
  classical
  have hψ0 := ψ.constantCoeff_eq_zero
  have hΨ0 := Ψ.constantCoeff_eq_zero
  have hEψ0 : ∀ s : Fin d ⊕ Fin d, constantCoeff ((Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (ψ.toPowerSeries j))
      fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (ψ.toPowerSeries j)) s) = 0 := by
    have hl : HasSubst (fun l : Fin d => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have hr : HasSubst (fun l : Fin d => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero hl (fun _ => constantCoeff_X _) (hψ0 j)
    · exact constantCoeff_subst_eq_zero hr (fun _ => constantCoeff_X _) (hψ0 j)
  have hl : HasSubst (fun l : Fin d => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hr : HasSubst (fun l : Fin d => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

  have key : ∀ j, (∑ l, Cf Ψ j l * pd l (ψ.toPowerSeries i)) =
      ∑ m, C ((linearPart ψ.toPowerSeries) m j) *
        subst (ev0fam (k := k) (d := d)) (subst (Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (ψ.toPowerSeries j))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (ψ.toPowerSeries j))
          (pd (Sum.inr m) (Φ.toPowerSeries i))) := by
    intro j
    have h := congrArg (fun F => subst (ev0fam (k := k) (d := d)) (pd (Sum.inr j) F)) (ψ.subst_eq i)
    rw [pd_subst Ψ.toPowerSeries hΨ0, pd_subst _ hEψ0, ← coe_substAlgHom hasSubst_ev0fam, map_sum, map_sum,
      Fintype.sum_sum_type] at h
    simp only [map_mul, coe_substAlgHom] at h

    have hL : ∀ l, subst (ev0fam (k := k) (d := d)) (subst Ψ.toPowerSeries (pd l (ψ.toPowerSeries i))) =
        pd l (ψ.toPowerSeries i) := by
      intro l
      rw [subst_comp_subst_apply Ψ.hasSubst_toPowerSeries hasSubst_ev0fam, funext (ev0_law Ψ)]
      exact congrFun subst_self _
    simp only [hL] at h
    change (∑ l, Cf Ψ j l * pd l (ψ.toPowerSeries i)) = _ at h
    rw [h]

    have hinl : ∀ m, subst (ev0fam (k := k) (d := d)) (pd (Sum.inr j)
        (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (ψ.toPowerSeries m))) = 0 := by
      intro m
      rw [pd_subst _ (fun _ => constantCoeff_X _)]
      have hz : (∑ s, pd (Sum.inr j) (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) k) *
          subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (pd s (ψ.toPowerSeries m))) = 0 :=
        Finset.sum_eq_zero fun s _ => by rw [pd_X, if_neg Sum.inr_ne_inl, zero_mul]
      rw [hz, ← coe_substAlgHom hasSubst_ev0fam, map_zero]

    have hinr : ∀ m, subst (ev0fam (k := k) (d := d)) (pd (Sum.inr j)
        (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (ψ.toPowerSeries m))) =
        C ((linearPart ψ.toPowerSeries) m j) := by
      intro m
      rw [pd_subst _ (fun _ => constantCoeff_X _)]
      have hsum : (∑ s, pd (Sum.inr j) (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) k) *
          subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (pd s (ψ.toPowerSeries m))) =
          subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (pd j (ψ.toPowerSeries m)) := by
        rw [Finset.sum_eq_single j]
        · rw [pd_X, if_pos rfl, one_mul]
        · intro s _ hs
          rw [pd_X, if_neg (fun h => hs (Sum.inr_injective h).symm), zero_mul]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [hsum, subst_comp_subst_apply hr hasSubst_ev0fam]
      have hfam : (fun l => subst (ev0fam (k := k) (d := d)) (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) =
          fun _ : Fin d => (0 : MvPowerSeries (Fin d) k) := by
        funext l
        exact subst_X hasSubst_ev0fam (Sum.inr l)
      rw [hfam, subst_zero_family, constantCoeff_pd]
      rfl
    simp only [Sum.elim_inl, Sum.elim_inr, hinl, zero_mul, Finset.sum_const_zero, zero_add, hinr]
  have hv' : ∀ m, (∑ j, v j * (linearPart ψ.toPowerSeries) m j) = 0 := by
    intro m
    have h := congrFun hv m
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp_rw [key, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun m _ => ?_
  have hterm : ∀ x (W : MvPowerSeries (Fin d) k), v x • (C (linearPart ψ.toPowerSeries m x) * W) =
      C (v x * linearPart ψ.toPowerSeries m x) * W := by
    intro x W
    rw [← smul_mul_assoc, smul_eq_C_mul, ← map_mul]
  simp only [hterm]
  rw [← Finset.sum_mul, ← map_sum, hv', map_zero, zero_mul]

theorem sum_mul_sum_eq {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R) (M1 : Fin n → Fin n → R)
    (M2r : Fin n → R) (b : R) (s' : Fin n) (h : ∀ i, (∑ m, M2r m * M1 m i) = if s' = i then 1 else 0) :
    (∑ m, ∑ i, a i * M1 m i * (M2r m * b)) = a s' * b := by
  rw [Finset.sum_comm]
  calc (∑ i, ∑ m, a i * M1 m i * (M2r m * b)) = ∑ i, a i * b * ∑ m, M2r m * M1 m i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ = a s' * b := by
        simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem transport {α β : Fin d → MvPowerSeries (Fin d) k} (hα0 : ∀ i, constantCoeff (α i) = 0)
    (hαβ : ∀ i, subst α (β i) = X i) (c : Fin d → MvPowerSeries (Fin d) k) (g : MvPowerSeries (Fin d) k) :
    (∑ m, subst α (∑ s, c s * pd s (β m)) * pd m (subst α g)) = subst α (∑ s, c s * pd s g) := by
  classical
  have hαs := hasSubst_of_constantCoeff_zero hα0

  let M1 : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) k) := Matrix.of fun j s => subst α (pd s (β j))
  let M2 : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) k) := Matrix.of fun s m => pd m (α s)
  have h12 : M1 * M2 = 1 := by
    ext j m
    have h := congrArg (pd m) (hαβ j)
    rw [pd_subst α hα0 (β j) m, pd_X] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hcomm : (∑ s, M1 j s * M2 s m) = ∑ s, pd m (α s) * subst α (pd s (β j)) :=
      Finset.sum_congr rfl fun s _ => mul_comm _ _
    rw [hcomm, h]
    by_cases hjm : j = m
    · rw [if_pos hjm, if_pos hjm.symm]
    · rw [if_neg hjm, if_neg (Ne.symm hjm)]
  have h21 : M2 * M1 = 1 := mul_eq_one_comm.mp h12
  have h21' : ∀ s' s, (∑ j, pd j (α s) * subst α (pd s' (β j))) = if s = s' then 1 else 0 := by
    intro s' s
    have h := congrFun (congrFun h21 s) s'
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h

  have hL : ∀ m, subst α (∑ s, c s * pd s (β m)) = ∑ s', subst α (c s') * subst α (pd s' (β m)) := by
    intro m
    rw [← coe_substAlgHom hαs, map_sum]
    simp only [map_mul]
  have hR : subst α (∑ s, c s * pd s g) = ∑ s, subst α (c s) * subst α (pd s g) := by
    rw [← coe_substAlgHom hαs, map_sum]
    simp only [map_mul]
  simp only [hL, hR, pd_subst α hα0 g, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  exact sum_mul_sum_eq (fun i => subst α (c i)) (fun m i => subst α (pd i (β m))) (fun m => pd m (α s'))
    (subst α (pd s' g)) s' (fun i => h21' i s')

end Key

section Main

variable {k : Type u} [Field k] {d : ℕ}

theorem main (p : ℕ) [Fact p.Prime] [CharP k p] (Ψ Φ : MvFormalGroup d k) (ψ : Ψ.Hom Φ) :
    ∃ (T : Finset (Fin d)) (Q : Matrix (Fin d) (Fin d) k) (α β : Fin d → MvPowerSeries (Fin d) k),
      T.card = (linearPart ψ.toPowerSeries).rank ∧ IsUnit Q ∧
      (∀ i, (α i).constantCoeff = 0) ∧ (∀ i, (β i).constantCoeff = 0) ∧
      (∀ i, subst α (β i) = X i) ∧ (∀ i, subst β (α i) = X i) ∧
      (∀ i ∈ T, β i = ∑ j, Q i j • ψ.toPowerSeries j) ∧
      (∀ (i : Fin d) (m : Fin d →₀ ℕ), (∃ j ∉ T, ¬ p ∣ m j) →
        coeff m (subst α (ψ.toPowerSeries i)) = 0) := by
  classical

  set L := linearPart ψ.toPowerSeries with hLdef
  obtain ⟨Ls, Ls', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal L
  set Q₀ := (Ls.map Matrix.TransvectionStruct.toMatrix).prod with hQ₀def
  set P := (Ls'.map Matrix.TransvectionStruct.toMatrix).prod with hPdef
  have hPdet : P.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod Ls'
  have hQ₀det : Q₀.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod Ls
  let T : Finset (Fin d) := Finset.univ.filter fun i => D i ≠ 0
  have hT : ∀ i, i ∈ T ↔ D i ≠ 0 := fun i => by simp [T]
  let Dinv : Fin d → k := fun i => if D i ≠ 0 then (D i)⁻¹ else 1
  have hDinv : ∀ i, Dinv i ≠ 0 := by
    intro i; simp only [Dinv]; split_ifs with h
    · exact inv_ne_zero h
    · exact one_ne_zero
  set Q : Matrix (Fin d) (Fin d) k := Matrix.diagonal Dinv * Q₀ with hQdef
  let J : Matrix (Fin d) (Fin d) k := Matrix.diagonal fun i => if i ∈ T then 1 else 0
  have hQLP : Q * L * P = J := by
    rw [hQdef, Matrix.mul_assoc (Matrix.diagonal Dinv), Matrix.mul_assoc (Matrix.diagonal Dinv), hD,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Dinv, hT]
    by_cases hi : D i ≠ 0
    · rw [if_pos hi, if_pos hi, inv_mul_cancel₀ hi]
    · rw [if_neg hi, if_neg hi, one_mul]; push Not at hi; exact hi
  have hQdet : IsUnit Q.det := by
    rw [hQdef, Matrix.det_mul, hQ₀det, mul_one, Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hDinv i)
  have hQu : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).mpr hQdet
  have hPu : IsUnit P.det := by rw [hPdet]; exact isUnit_one
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQdet

  have hcard : T.card = L.rank := by
    have h1 : (Q * L * P).rank = L.rank := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det P (Q * L) hPu, Matrix.rank_mul_eq_right_of_isUnit_det Q L hQdet]
    rw [← h1, hQLP, Matrix.rank_diagonal, Fintype.card_subtype]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ T <;> simp [hi]

  have hψ0 := ψ.constantCoeff_eq_zero
  let u : Fin d → MvPowerSeries (Fin d) k := fun i => ∑ j, Q i j • ψ.toPowerSeries j
  let β : Fin d → MvPowerSeries (Fin d) k := fun i => if i ∈ T then u i else linTuple P⁻¹ i
  have hu0 : ∀ i, constantCoeff (u i) = 0 := fun i => by simp [u, map_sum, hψ0]
  have hβ0 : ∀ i, constantCoeff (β i) = 0 := by
    intro i; simp only [β]; split_ifs
    · exact hu0 i
    · exact constantCoeff_linTuple _ i
  have hβs := hasSubst_of_constantCoeff_zero hβ0
  have hlinβ : linearPart β = P⁻¹ := by
    have hQL : Q * L = J * P⁻¹ := by rw [← hQLP, Matrix.mul_assoc (Q * L) P P⁻¹, hPP, Matrix.mul_one]
    ext i l
    by_cases hi : i ∈ T
    · have h := congrFun (congrFun hQL i) l
      rw [Matrix.mul_apply, Matrix.mul_apply] at h
      have hJ : (∑ j, J i j * P⁻¹ j l) = P⁻¹ i l := by
        rw [Finset.sum_eq_single i]
        · simp [J, Matrix.diagonal_apply_eq, hi]
        · intro j _ hji; simp [J, Matrix.diagonal_apply_ne _ (Ne.symm hji)]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [hJ] at h
      rw [← h]
      simp only [linearPart, Matrix.of_apply, β, if_pos hi, u, map_sum, map_smul, smul_eq_mul]
      rfl
    · have h := congrFun (congrFun (linearPart_linTuple (P⁻¹)) i) l
      simp only [linearPart, Matrix.of_apply] at h ⊢
      simp only [β, if_neg hi]
      exact h
  let β' : Fin d → MvPowerSeries (Fin d) k := fun i => ∑ j, P i j • β j
  have hβ'0 : ∀ i, constantCoeff (β' i) = 0 := fun i => by simp [β', map_sum, hβ0]
  have hβ's := hasSubst_of_constantCoeff_zero hβ'0
  have hlinβ' : linearPart β' = 1 := by
    show linearPart (fun i => ∑ j, P i j • β j) = 1
    rw [linearPart_sum_smul, hlinβ, hPP]
  obtain ⟨α', hα'0, h1, h2⟩ := MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one β' hβ'0 hlinβ'
  have hα's := hasSubst_of_constantCoeff_zero hα'0
  let α : Fin d → MvPowerSeries (Fin d) k := fun i => subst (linTuple P) (α' i)
  have hα0 : ∀ i, constantCoeff (α i) = 0 :=
    fun i => constantCoeff_subst_eq_zero (hasSubst_linTuple P) (constantCoeff_linTuple P) (hα'0 i)
  have hαs := hasSubst_of_constantCoeff_zero hα0
  have hβ'eq : ∀ j, β' j = subst β (linTuple P j) := fun j => (subst_linTuple hβs P j).symm
  have hβeq : ∀ i, β i = subst β' (linTuple P⁻¹ i) := by
    intro i
    rw [funext hβ'eq, ← subst_comp_subst_apply (hasSubst_linTuple P) hβs, subst_linTuple_linTuple, hPP',
      linTuple_one, subst_X hβs]
  have hαβ : ∀ i, subst α (β i) = X i := by
    intro i
    rw [hβeq i, subst_comp_subst_apply hβ's hαs]
    have hfam : (fun j => subst α (β' j)) = linTuple P := by
      funext j
      show subst (fun i => subst (linTuple P) (α' i)) (β' j) = _
      rw [← subst_comp_subst_apply hα's (hasSubst_linTuple P), h2 j, subst_X (hasSubst_linTuple P)]
    rw [hfam, subst_linTuple_linTuple, hPP', linTuple_one]
  have hβα : ∀ i, subst β (α i) = X i := by
    intro i
    show subst β (subst (linTuple P) (α' i)) = X i
    rw [subst_comp_subst_apply (hasSubst_linTuple P) hβs, ← funext hβ'eq]
    exact h1 i

  have hpd : ∀ i, ∀ j ∉ T, pd j (subst α (ψ.toPowerSeries i)) = 0 := by
    intro i

    let c : Fin d → Fin d → MvPowerSeries (Fin d) k := fun j s => ∑ j', P j' j • Cf Ψ j' s
    have hDψ : ∀ j ∉ T, ∀ i', (∑ s, c j s * pd s (ψ.toPowerSeries i')) = 0 := by
      intro j hj i'
      have hv : L.mulVec (fun l => P l j) = 0 := by
        have hLP : L * P = Q⁻¹ * J := by
          rw [← hQLP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]
        funext m
        have h := congrFun (congrFun hLP m) j
        rw [Matrix.mul_apply, Matrix.mul_apply] at h
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
        rw [h]
        refine Finset.sum_eq_zero fun t _ => ?_
        by_cases htj : t = j
        · subst htj; simp [J, hj]
        · simp [J, Matrix.diagonal_apply_ne _ htj]
      have h := sum_Cf_pd_eq_zero ψ (fun l => P l j) hv i'
      rw [← h]
      simp only [c, Finset.sum_mul, Finset.smul_sum, smul_mul_assoc]
      rw [Finset.sum_comm]
    have hDu : ∀ j ∉ T, ∀ m ∈ T, (∑ s, c j s * pd s (β m)) = 0 := by
      intro j hj m hm
      simp only [β, if_pos hm, u, pd_sum, pd_smul, Finset.mul_sum, mul_smul_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j'' _ => ?_
      rw [← Finset.smul_sum, hDψ j hj, smul_zero]

    let e : Fin d → Fin d → MvPowerSeries (Fin d) k := fun j m => subst α (∑ s, c j s * pd s (β m))
    have heT : ∀ j ∉ T, ∀ m ∈ T, e j m = 0 := by
      intro j hj m hm
      simp only [e, hDu j hj m hm, ← coe_substAlgHom hαs, map_zero]
    have hsum : ∀ j ∉ T, (∑ m, e j m * pd m (subst α (ψ.toPowerSeries i))) = 0 := by
      intro j hj
      simp only [e]
      rw [transport hα0 hαβ (c j) (ψ.toPowerSeries i), hDψ j hj i, ← coe_substAlgHom hαs, map_zero]
    have hcc : ∀ j m, constantCoeff (e j m) = if m = j then 1 else 0 := by
      intro j m
      simp only [e]
      rw [constantCoeff_subst_of_zero hα0, map_sum]
      simp only [map_mul, constantCoeff_pd, c, map_sum]
      have hin : ∀ s, (∑ j', constantCoeff (P j' j • Cf Ψ j' s)) = P s j := by
        intro s
        simp only [smul_eq_C_mul, map_mul, constantCoeff_C, constantCoeff_Cf, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
      simp only [hin]
      have h := congrFun (congrFun hPP' m) j
      rw [Matrix.mul_apply, Matrix.one_apply] at h
      rw [← h]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hls : coeff (Finsupp.single s 1) (β m) = P⁻¹ m s := by
        have := congrFun (congrFun hlinβ m) s
        simpa only [linearPart, Matrix.of_apply] using this
      rw [hls, mul_comm]

    let N : Matrix {m : Fin d // m ∉ T} {m : Fin d // m ∉ T} (MvPowerSeries (Fin d) k) :=
      Matrix.of fun a b => e a.1 b.1
    let wv : {m : Fin d // m ∉ T} → MvPowerSeries (Fin d) k := fun b => pd b.1 (subst α (ψ.toPowerSeries i))
    have hNw : N.mulVec wv = 0 := by
      funext a
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, N, Matrix.of_apply, wv]
      have h := hsum a.1 a.2
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => m ∉ T)] at h
      have hz : (∑ m ∈ Finset.univ.filter (fun m => ¬ (m ∉ T)), e a.1 m * pd m (subst α (ψ.toPowerSeries i))) = 0 :=
        Finset.sum_eq_zero fun m hm => by
          rw [Finset.mem_filter, not_not] at hm
          rw [heT a.1 a.2 m hm.2, zero_mul]
      rw [hz, add_zero, Finset.sum_subtype (Finset.univ.filter fun m => m ∉ T) (p := fun m => m ∉ T)
        (fun m => by simp)] at h
      exact h
    have hNdet : IsUnit N.det := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff]
      have hN1 : N.map constantCoeff = 1 := by
        ext a b
        rw [Matrix.map_apply, Matrix.one_apply]
        simp only [N, Matrix.of_apply, hcc, Subtype.ext_iff]
        simp only [eq_comm]
      have h : constantCoeff N.det = 1 := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, hN1, Matrix.det_one]
      rw [h]; exact isUnit_one
    have hw : wv = 0 := by
      have h := congrArg N.adjugate.mulVec hNw
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero, Matrix.smul_mulVec,
        Matrix.one_mulVec] at h
      rw [← hNdet.smul_left_cancel (y := (0 : {m : Fin d // m ∉ T} → MvPowerSeries (Fin d) k)), smul_zero]
      exact h
    intro j hj
    exact congrFun hw ⟨j, hj⟩
  have hKL : ∀ (i : Fin d) (m : Fin d →₀ ℕ), (∃ j ∉ T, ¬ p ∣ m j) →
      coeff m (subst α (ψ.toPowerSeries i)) = 0 := by
    rintro i m ⟨j, hj, hpm⟩
    have hmj : m j ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
    obtain ⟨n, rfl⟩ : ∃ n, m = n + Finsupp.single j 1 :=
      ⟨m - Finsupp.single j 1, (tsub_add_cancel_of_le
        (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hmj))).symm⟩
    have h := congrArg (coeff n) (hpd i j hj)
    rw [coeff_pd, map_zero] at h
    rcases mul_eq_zero.mp h with h0 | h0
    · exfalso
      apply hpm
      rw [CharP.cast_eq_zero_iff k p] at h0
      simpa using h0
    · exact h0
  refine ⟨T, Q, α, β, hcard, hQu, hα0, hβ0, hαβ, hβα, fun i hi => ?_, hKL⟩
  simp only [β, if_pos hi, u]

end Main

end P2mKcNormalForm

open MvPowerSeries in

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] {d : ℕ}
    (Ψ Φ : MvFormalGroup d k) (ψ : Ψ.Hom Φ) :
    ∃ (T : Finset (Fin d)) (Q : Matrix (Fin d) (Fin d) k) (α β : Fin d → MvPowerSeries (Fin d) k),
      T.card = (MvFormalGroup.linearPart ψ.toPowerSeries).rank ∧ IsUnit Q ∧
      (∀ i, (α i).constantCoeff = 0) ∧ (∀ i, (β i).constantCoeff = 0) ∧
      (∀ i, subst α (β i) = X i) ∧ (∀ i, subst β (α i) = X i) ∧
      (∀ i ∈ T, β i = ∑ j, Q i j • ψ.toPowerSeries j) ∧
      (∀ (i : Fin d) (m : Fin d →₀ ℕ), (∃ j ∉ T, ¬ p ∣ m j) →
        coeff m (subst α (ψ.toPowerSeries i)) = 0) :=
  P2mKcNormalForm.main p Ψ Φ ψ

end

end S_MvFormalGroup_Hom_exists_subst_eq_X_and_coeff_subst_eq_zero_of_not_dvd
end P2MW
export P2MW.S_MvFormalGroup_Hom_exists_subst_eq_X_and_coeff_subst_eq_zero_of_not_dvd (solution)
