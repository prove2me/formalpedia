-- Prove2me | solution 1 for KedlayaUmans.Multimodular.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T01:54:29.02371+00:00
-- url     : https://prove2.me/submissions/feb781f7-4957-4bdb-a157-f52662498d73

import Mathlib
import Definitions.Def_KedlayaUmans_Multimodular_Algorithm
import Definitions.Def_KedlayaUmans_Multimodular_ExtensionRing

set_option autoImplicit false

namespace KUMM44

open Real

lemma theta_big (n : ℕ) (hn : 1000 ≤ n) : ((n:ℝ) + 1) / 16 ≤ Real.log (primorial n) := by
  have hθ := Chebyshev.theta_ge n
  have hθe : Chebyshev.theta (n:ℝ) = Real.log (primorial n) := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  rw [← hθe]
  have hnR : (1000:ℝ) ≤ n := by exact_mod_cast hn
  set s := √(n:ℝ) with hs_def
  have hs2 : s ^ 2 = n := Real.sq_sqrt (by linarith)
  have hs31 : (31:ℝ) ≤ s := by
    rw [hs_def]; apply Real.le_sqrt_of_sq_le; linarith
  have hspos : 0 < s := by linarith
  have hlogn : Real.log n = 2 * Real.log s := by
    rw [← hs2, Real.log_pow]; norm_num
  have hl16 : Real.log (s / 16) ≤ s / 16 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at hl16
  have h16 : Real.log (16:ℝ) = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hn1 : Real.log ((n:ℝ) + 1) ≤ Real.log 2 + Real.log n := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  rw [hlogn] at hθ hn1
  rw [h16] at hl16
  nlinarith

lemma primorial_eleven : primorial 11 = 2310 := by
  decide

lemma prim109_ge : 3 ^ 90 ≤ primorial 109 := by
  have : primorial 109 = 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 37 * 41 * 43 * 47 * 53 * 59 * 61 * 67 *
      71 * 73 * 79 * 83 * 89 * 97 * 101 * 103 * 107 * 109 := by
    decide
  rw [this]; norm_num

lemma exp_le_three_pow (k : ℕ) : Real.exp k ≤ 3 ^ k := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) k

lemma log_ge_of_pow (k N : ℕ) (h : 3 ^ k ≤ N) : (k:ℝ) ≤ Real.log N := by
  have hN : (0:ℝ) < N := by
    have : 0 < N := lt_of_lt_of_le (by positivity) h
    exact_mod_cast this
  rw [Real.le_log_iff_exp_le hN]
  calc Real.exp k ≤ 3 ^ k := exp_le_three_pow k
    _ ≤ N := by exact_mod_cast h

lemma prim_bound (n : ℕ) (hn : 11 ≤ n) : ((n:ℝ) + 1) / 16 ≤ Real.log (primorial n) := by
  rcases lt_or_ge n 109 with h1 | h1
  · have hm : 3 ^ 7 ≤ primorial n := by
      calc 3 ^ 7 ≤ primorial 11 := by rw [primorial_eleven]; norm_num
        _ ≤ primorial n := primorial_mono hn
    have := log_ge_of_pow 7 _ hm
    have : (n:ℝ) ≤ 108 := by exact_mod_cast (by omega : n ≤ 108)
    push_cast at *; linarith
  rcases lt_or_ge n 1000 with h2 | h2
  · have hm : 3 ^ 90 ≤ primorial n := le_trans prim109_ge (primorial_mono h1)
    have := log_ge_of_pow 90 _ hm
    have : (n:ℝ) ≤ 999 := by exact_mod_cast (by omega : n ≤ 999)
    push_cast at *; linarith
  · exact theta_big n h2

/-- the product of the primes up to `16 log B` exceeds `B`. -/
lemma lt_prod_primes (B : ℕ) (hB : 2 ≤ B) :
    B < ∏ p ∈ Nat.primesLE ⌊16 * Real.log (B:ℝ)⌋₊, p := by
  set n := ⌊16 * Real.log (B:ℝ)⌋₊ with hn
  have hprod : ∏ p ∈ Nat.primesLE n, p = primorial n := by
    simp [primorial, Nat.primesLE, Nat.primesBelow]
  rw [hprod]
  have hBR : (2:ℝ) ≤ B := by exact_mod_cast hB
  have hlogB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hBR
  have hl2' := Real.log_two_gt_d9
  have h11 : 11 ≤ n := by
    rw [hn]; apply Nat.le_floor; push_cast; linarith
  have hlt : 16 * Real.log (B:ℝ) < n + 1 := Nat.lt_floor_add_one _
  have hp := prim_bound n h11
  have hpos : (0:ℝ) < primorial n := by exact_mod_cast primorial_pos n
  have : Real.log B < Real.log (primorial n) := by linarith
  have := (Real.log_lt_log_iff (by positivity) hpos).1 this
  exact_mod_cast this


open KedlayaUmans.Multimodular

lemma eval_map_hom {σ R S : Type*} [CommRing R] [CommRing S] [Fintype σ] (φ : R →+* S)
    (g : MvPolynomial σ R) (a : σ → R) :
    MvPolynomial.eval (fun i => φ (a i)) (MvPolynomial.map φ g) = φ (MvPolynomial.eval a g) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq', MvPolynomial.eval_eq']
  simp [map_sum, map_mul, map_prod, map_pow]

lemma eval_bound {m : ℕ} (d : ℕ) (hd : 1 ≤ d) (A : ℤ) (hA1 : 1 ≤ A) (g : MvPolynomial (Fin m) ℤ)
    (hdeg : ∀ s ∈ g.support, ∀ i, s i ≤ d - 1) (hc : ∀ s, 0 ≤ g.coeff s ∧ g.coeff s ≤ A)
    (a : Fin m → ℤ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ A) :
    0 ≤ MvPolynomial.eval a g ∧ MvPolynomial.eval a g ≤ (d:ℤ) ^ m * A ^ ((d - 1) * m + 1) := by
  rw [MvPolynomial.eval_eq']
  constructor
  · exact Finset.sum_nonneg fun s _ =>
      mul_nonneg (hc s).1 (Finset.prod_nonneg fun i _ => pow_nonneg (ha i).1 _)
  · have hterm : ∀ s ∈ g.support, g.coeff s * ∏ i, a i ^ s i ≤ A ^ ((d - 1) * m + 1) := by
      intro s hs
      have hp : ∏ i, a i ^ s i ≤ A ^ ((d - 1) * m) := by
        calc ∏ i, a i ^ s i ≤ ∏ _i : Fin m, A ^ (d - 1) := by
              apply Finset.prod_le_prod (fun i _ => pow_nonneg (ha i).1 _)
              intro i _
              calc a i ^ s i ≤ A ^ s i := pow_le_pow_left₀ (ha i).1 (ha i).2 _
                _ ≤ A ^ (d - 1) := pow_le_pow_right₀ hA1 (hdeg s hs i)
          _ = A ^ ((d - 1) * m) := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      calc g.coeff s * ∏ i, a i ^ s i ≤ A * A ^ ((d - 1) * m) :=
            mul_le_mul (hc s).2 hp (Finset.prod_nonneg fun i _ => pow_nonneg (ha i).1 _) (by linarith)
        _ = A ^ ((d - 1) * m + 1) := by ring
    have hcard : g.support.card ≤ d ^ m := by
      classical
      let F : (Fin m → Fin d) → (Fin m →₀ ℕ) :=
        fun u => Finsupp.equivFunOnFinite.symm (fun i => (u i : ℕ))
      have hsub : g.support ⊆ Finset.univ.image F := by
        intro s hs
        rw [Finset.mem_image]
        refine ⟨fun i => ⟨s i, by have := hdeg s hs i; omega⟩, Finset.mem_univ _, ?_⟩
        ext i; simp [F]
      calc g.support.card ≤ (Finset.univ.image F).card := Finset.card_le_card hsub
        _ ≤ (Finset.univ : Finset (Fin m → Fin d)).card := Finset.card_image_le
        _ = d ^ m := by simp
    calc ∑ s ∈ g.support, g.coeff s * ∏ i, a i ^ s i
          ≤ ∑ _s ∈ g.support, A ^ ((d - 1) * m + 1) := Finset.sum_le_sum hterm
      _ = (g.support.card : ℤ) * A ^ ((d - 1) * m + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (d:ℤ) ^ m * A ^ ((d - 1) * m + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard

lemma coeff_liftPoly {m r : ℕ} (f : MvPolynomial (Fin m) (ZMod r)) (s : Fin m →₀ ℕ) :
    (liftPoly f).coeff s = (((f.coeff s).val : ℕ) : ℤ) := by
  classical
  by_cases h : s ∈ f.support
  · simp [liftPoly, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, h]
  · have h0 : f.coeff s = 0 := MvPolynomial.notMem_support_iff.1 h
    simp [liftPoly, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, h, h0]

lemma map_liftPoly {m r : ℕ} [NeZero r] (f : MvPolynomial (Fin m) (ZMod r)) :
    MvPolynomial.map (Int.castRingHom (ZMod r)) (liftPoly f) = f := by
  ext s
  rw [MvPolynomial.coeff_map, coeff_liftPoly]
  simp

lemma support_liftPoly {m r : ℕ} (f : MvPolynomial (Fin m) (ZMod r)) {s : Fin m →₀ ℕ}
    (hs : s ∈ (liftPoly f).support) : s ∈ f.support := by
  rw [MvPolynomial.mem_support_iff, coeff_liftPoly] at hs
  rw [MvPolynomial.mem_support_iff]
  intro h; apply hs; simp [h]

lemma mm_step (d : ℕ) (hd : 2 ≤ d) {m : ℕ} (hm : 1 ≤ m) (t r : ℕ) (hr : 2 ≤ r)
    (f : MvPolynomial (Fin m) (ZMod r)) (α : Fin m → ZMod r)
    (hf : ∀ s ∈ f.support, ∀ i, s i ≤ d - 1)
    (hrec : ∀ p : ℕ, p.Prime → ∀ (g : MvPolynomial (Fin m) (ZMod p)) (β : Fin m → ZMod p),
      (∀ s ∈ g.support, ∀ i, s i ≤ d - 1) →
      (if t = 0 then MvPolynomial.eval β g else multimodular d t p g β) = MvPolynomial.eval β g) :
    multimodular d (t + 1) r f α = MvPolynomial.eval α f := by
  have : NeZero r := ⟨by omega⟩
  have hr2 : (2:ℤ) ≤ r := by exact_mod_cast hr
  set v : ℤ := MvPolynomial.eval (liftPoint α) (liftPoly f) with hv
  have hcast : ∀ n : ℕ, MvPolynomial.eval (fun i => ((liftPoint α i : ℤ) : ZMod n))
      (MvPolynomial.map (Int.castRingHom (ZMod n)) (liftPoly f)) = (v : ZMod n) := by
    intro n
    exact eval_map_hom (Int.castRingHom (ZMod n)) (liftPoly f) (liftPoint α)
  have hvr : (v : ZMod r) = MvPolynomial.eval α f := by
    have hpt : (fun i => ((liftPoint α i : ℤ) : ZMod r)) = α := by
      funext i; simp [liftPoint]
    rw [← hcast r, map_liftPoly, hpt]
  have hbd := eval_bound d (by omega) ((r:ℤ) - 1) (by linarith) (liftPoly f)
    (fun s hs i => hf s (support_liftPoly f hs) i)
    (fun s => by
      rw [coeff_liftPoly]
      refine ⟨by positivity, ?_⟩
      have := ZMod.val_lt (f.coeff s)
      have : ((f.coeff s).val : ℤ) < r := by exact_mod_cast this
      linarith)
    (liftPoint α)
    (fun i => by
      refine ⟨by simp only [liftPoint]; positivity, ?_⟩
      have := ZMod.val_lt (α i)
      have : ((α i).val : ℤ) < r := by exact_mod_cast this
      simp only [liftPoint]; linarith)
  rw [← hv] at hbd
  set S : Finset ℕ := primesUpTo (ell d m r) with hS
  set N : ℕ := ∏ p : S, (p : ℕ) with hN
  have hBN : magnitudeBound d m r < N := by
    have h1 := lt_prod_primes (magnitudeBound d m r) ?_
    · have hpc : (∏ p : S, (p : ℕ)) = ∏ p ∈ S, p := Finset.prod_coe_sort S id
      rw [hN, hpc]
      simpa [hS, primesUpTo, ell] using h1
    · unfold magnitudeBound
      have h1 : 2 ≤ d ^ m := le_trans hd (Nat.le_self_pow (by omega) d)
      have h2 : 1 ≤ (r - 1) ^ (m * d) := Nat.one_le_pow _ _ (by omega)
      nlinarith
  have hvB : v ≤ (magnitudeBound d m r : ℤ) := by
    refine le_trans hbd.2 ?_
    unfold magnitudeBound
    push_cast [Nat.cast_sub (by omega : 1 ≤ r)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_right₀ (by linarith)
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  have hvN : v < N := by
    have : ((magnitudeBound d m r : ℕ) : ℤ) < N := by exact_mod_cast hBN
    linarith
  haveI hNz : NeZero N := ⟨by
    rw [hN]
    exact Finset.prod_ne_zero_iff.2 (fun p _ => (Nat.prime_of_mem_primesLE p.2).ne_zero)⟩
  have hfun : ∀ (res : (p : S) → ZMod (p : ℕ)), (∀ p, res p = (v : ZMod (p : ℕ))) →
      ((((ZMod.prodEquivPi (fun p : S => (p : ℕ)) (primesUpTo_pairwise_coprime _)).symm res).val : ℕ)
        : ZMod r) = MvPolynomial.eval α f := by
    intro res hres
    have hres' : res = ZMod.prodEquivPi (fun p : S => (p : ℕ)) (primesUpTo_pairwise_coprime _)
        (v : ZMod N) := by
      funext p; rw [hres p, map_intCast]; rfl
    rw [hres', RingEquiv.symm_apply_apply, ← hvr]
    have hval : (((v : ZMod N).val : ℕ) : ℤ) = v := by
      rw [ZMod.val_intCast]; exact Int.emod_eq_of_lt hbd.1 hvN
    rw [show (((v : ZMod N).val : ℕ) : ZMod r) = ((((v : ZMod N).val : ℕ) : ℤ) : ZMod r) by
      push_cast; rfl, hval]
  simp only [multimodular]
  apply hfun
  intro p
  rw [hrec p (Nat.prime_of_mem_primesLE p.2) _ _ ?_]
  · exact hcast p
  · intro s hs i
    exact hf s (support_liftPoly f (MvPolynomial.support_map_subset _ _ hs)) i

theorem mm_correct (d : ℕ) (hd : 2 ≤ d) {m : ℕ} (hm : 1 ≤ m) (t : ℕ) :
    ∀ (r : ℕ), 2 ≤ r → ∀ (f : MvPolynomial (Fin m) (ZMod r)) (α : Fin m → ZMod r),
    (∀ s ∈ f.support, ∀ i, s i ≤ d - 1) → multimodular d (t + 1) r f α = MvPolynomial.eval α f := by
  induction t with
  | zero =>
    intro r hr f α hf
    exact mm_step d hd hm 0 r hr f α hf (fun p _ g β _ => by simp)
  | succ t ih =>
    intro r hr f α hf
    exact mm_step d hd hm (t + 1) r hr f α hf (fun p hp g β hg => by
      rw [if_neg (Nat.succ_ne_zero t)]; exact ih p hp.two_le g β hg)


section ExtPart
open Polynomial

lemma coeff_liftZPoly {r : ℕ} (q : (ZMod r)[X]) (j : ℕ) :
    (liftZPoly q).coeff j = (((q.coeff j).val : ℕ) : ℤ) := by
  classical
  by_cases h : j ∈ q.support
  · simp [liftZPoly, Polynomial.coeff_monomial, h]
  · have h0 : q.coeff j = 0 := Polynomial.notMem_support_iff.1 h
    simp [liftZPoly, Polynomial.coeff_monomial, h, h0]

lemma map_liftZPoly {r : ℕ} [NeZero r] (q : (ZMod r)[X]) :
    (liftZPoly q).map (Int.castRingHom (ZMod r)) = q := by
  ext j; rw [Polynomial.coeff_map, coeff_liftZPoly]; simp

lemma natDegree_liftZPoly {r : ℕ} (q : (ZMod r)[X]) : (liftZPoly q).natDegree ≤ q.natDegree := by
  unfold liftZPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_monomial_le _).trans (Polynomial.le_natDegree_of_mem_supp i hi)

lemma eval_one_liftZPoly {r : ℕ} (q : (ZMod r)[X]) :
    (liftZPoly q).eval 1 = ∑ i ∈ q.support, (((q.coeff i).val : ℕ) : ℤ) := by
  simp [liftZPoly, Polynomial.eval_finsetSum]

lemma liftElt_zero {r : ℕ} {E : (ZMod r)[X]} (hE : E.Monic) : liftElt hE (0 : AdjoinRoot E) = 0 := by
  simp [liftElt, liftZPoly]

lemma natDegree_modByMonicHom_lt {r : ℕ} [Fact (1 < r)] {E : (ZMod r)[X]} (hE : E.Monic)
    (he : 1 ≤ E.natDegree) (x : AdjoinRoot E) :
    (AdjoinRoot.modByMonicHom hE x).natDegree < E.natDegree := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [AdjoinRoot.modByMonicHom_mk]
  exact Polynomial.natDegree_modByMonic_lt g hE (by rintro rfl; simp at he)

lemma eval_one_liftElt {r : ℕ} [NeZero r] [Fact (1 < r)] {E : (ZMod r)[X]} (hE : E.Monic)
    (he : 1 ≤ E.natDegree) (x : AdjoinRoot E) :
    0 ≤ (liftElt hE x).eval 1 ∧ (liftElt hE x).eval 1 ≤ (E.natDegree : ℤ) * ((r:ℤ) - 1) := by
  have hr2 : (2:ℤ) ≤ r := by exact_mod_cast (Fact.out : 1 < r)
  unfold liftElt
  rw [eval_one_liftZPoly]
  set q := AdjoinRoot.modByMonicHom hE x with hq
  refine ⟨Finset.sum_nonneg fun i _ => by positivity, ?_⟩
  have hsub := Polynomial.supp_subset_range (natDegree_modByMonicHom_lt hE he x)
  rw [← hq] at hsub
  calc ∑ i ∈ q.support, (((q.coeff i).val : ℕ) : ℤ) ≤ ∑ _i ∈ q.support, ((r:ℤ) - 1) := by
        apply Finset.sum_le_sum; intro i _
        have := ZMod.val_lt (q.coeff i)
        have : ((q.coeff i).val : ℤ) < r := by exact_mod_cast this
        linarith
    _ = (q.support.card : ℤ) * ((r:ℤ) - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (E.natDegree : ℤ) * ((r:ℤ) - 1) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        have := Finset.card_le_card hsub
        rw [Finset.card_range] at this
        exact_mod_cast this

/-- nonnegative coefficients -/
def NN (p : ℤ[X]) : Prop := ∀ j, 0 ≤ p.coeff j

lemma NN_mul {p q : ℤ[X]} (hp : NN p) (hq : NN q) : NN (p * q) := fun j => by
  rw [Polynomial.coeff_mul]; exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

lemma NN_one : NN 1 := fun j => by rw [Polynomial.coeff_one]; split_ifs <;> norm_num

lemma NN_pow {p : ℤ[X]} (hp : NN p) (n : ℕ) : NN (p ^ n) := by
  induction n with
  | zero => simpa using NN_one
  | succ n ih => rw [pow_succ]; exact NN_mul ih hp

lemma NN_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) (h : ∀ i ∈ s, NN (f i)) :
    NN (∏ i ∈ s, f i) :=
  Finset.prod_induction _ NN (fun _ _ => NN_mul) NN_one h

lemma NN_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) (h : ∀ i ∈ s, NN (f i)) :
    NN (∑ i ∈ s, f i) :=
  Finset.sum_induction _ NN (fun a b ha hb j => by rw [Polynomial.coeff_add]; exact add_nonneg (ha j) (hb j))
    (fun j => by simp) h

lemma coeff_le_eval_one {p : ℤ[X]} (hp : NN p) (j : ℕ) : p.coeff j ≤ p.eval 1 := by
  rw [Polynomial.eval_eq_sum_range]
  simp only [one_pow, mul_one]
  by_cases hj : j ≤ p.natDegree
  · exact Finset.single_le_sum (f := fun i => p.coeff i) (fun i _ => hp i)
      (Finset.mem_range.2 (by omega))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact Finset.sum_nonneg fun i _ => hp i

lemma digit_sum_lt (M : ℕ) (hM : 1 ≤ M) (N : ℕ) : ∀ (c : ℕ → ℕ), (∀ j, c j < M) →
    ∑ i ∈ Finset.range N, c i * M ^ i < M ^ N := by
  induction N with
  | zero => intro c _; simp
  | succ N ih =>
    intro c hc
    rw [Finset.sum_range_succ', pow_succ']
    have h1 := ih (fun i => c (i + 1)) (fun j => hc (j + 1))
    have h2 := hc 0
    have hS : ∑ i ∈ Finset.range N, c (i + 1) * M ^ (i + 1)
        = M * ∑ i ∈ Finset.range N, c (i + 1) * M ^ i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [hS]
    simp only [pow_zero, mul_one]
    have h3 := Nat.mul_le_mul_left M (Nat.succ_le_of_lt h1)
    rw [Nat.mul_succ] at h3
    omega

lemma digit_eq (M : ℕ) (hM : 1 ≤ M) (N : ℕ) : ∀ (c : ℕ → ℕ), (∀ j, c j < M) → ∀ j, j < N →
    (∑ i ∈ Finset.range N, c i * M ^ i) / M ^ j % M = c j := by
  induction N with
  | zero => intro c _ j hj; omega
  | succ N ih =>
    intro c hc j hj
    rw [Finset.sum_range_succ']
    have hS : ∑ i ∈ Finset.range N, c (i + 1) * M ^ (i + 1)
        = M * ∑ i ∈ Finset.range N, c (i + 1) * M ^ i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [hS]
    simp only [pow_zero, mul_one]
    rcases j with _ | j
    · simp only [pow_zero, Nat.div_one]
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (hc 0)
    · rw [pow_succ', ← Nat.div_div_eq_div_mul]
      rw [show (M * ∑ i ∈ Finset.range N, c (i + 1) * M ^ i + c 0) / M
          = ∑ i ∈ Finset.range N, c (i + 1) * M ^ i by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (hc 0)]; simp]
      exact ih (fun i => c (i + 1)) (fun j => hc (j + 1)) j (by omega)

theorem ext_main {r m : ℕ} (hr : 2 ≤ r) (d t : ℕ) (ht : 1 ≤ t) (hd : 2 ≤ d) (hm : 1 ≤ m)
    (E : (ZMod r)[X]) (hE : E.Monic) (he : 1 ≤ E.natDegree)
    (f : MvPolynomial (Fin m) (AdjoinRoot E)) (hf : ∀ i, f.degreeOf i ≤ d - 1)
    (α : Fin m → AdjoinRoot E) :
    multimodularExt d t hE f α = MvPolynomial.eval α f := by
  haveI : Fact (1 < r) := ⟨by omega⟩
  haveI : NeZero r := ⟨by omega⟩
  have hr2 : (2:ℤ) ≤ r := by exact_mod_cast hr
  have hf' : ∀ s ∈ f.support, ∀ i, s i ≤ d - 1 :=
    fun s hs i => (MvPolynomial.degreeOf_le_iff.1 (hf i)) s hs
  simp only [multimodularExt]
  set e := E.natDegree with he_def
  set M := bigM d m e r with hM
  set D := digitDegree d m e with hD
  set r' := rPrime d m e r with hr'
  set g := liftPolyExt hE f with hg
  set a := liftPointExt hE α with ha
  set P : ℤ[X] := MvPolynomial.eval a g with hP
  have coeff_g : ∀ s, g.coeff s = liftElt hE (f.coeff s) := by
    intro s
    classical
    by_cases h : s ∈ f.support
    · simp [hg, liftPolyExt, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, h]
    · have h0 : f.coeff s = 0 := MvPolynomial.notMem_support_iff.1 h
      simp [hg, liftPolyExt, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, h, h0, liftElt_zero]
  have supp_g : ∀ s ∈ g.support, s ∈ f.support := by
    intro s hs
    rw [MvPolynomial.mem_support_iff, coeff_g] at hs
    rw [MvPolynomial.mem_support_iff]
    intro h; apply hs; rw [h, liftElt_zero]
  have NN_lift : ∀ x : AdjoinRoot E, NN (liftElt hE x) := fun x j => by
    unfold liftElt; rw [coeff_liftZPoly]; positivity
  have deg_lift : ∀ x : AdjoinRoot E, (liftElt hE x).natDegree ≤ e - 1 := fun x => by
    have := natDegree_modByMonicHom_lt hE he x
    have h2 := natDegree_liftZPoly (AdjoinRoot.modByMonicHom hE x)
    unfold liftElt; omega
  have hPsum : P = ∑ s ∈ g.support, g.coeff s * ∏ i, a i ^ s i := by
    rw [hP, MvPolynomial.eval_eq']
  -- (P1) nonnegative coefficients
  have hNN : NN P := by
    rw [hPsum]
    apply NN_sum; intro s _
    apply NN_mul
    · rw [coeff_g]; exact NN_lift _
    · apply NN_prod; intro i _; exact NN_pow (NN_lift _) _
  -- (P2) value at 1
  have hM1 : P.eval 1 ≤ (M : ℤ) - 1 := by
    have h1 : P.eval 1 = MvPolynomial.eval (fun i => Polynomial.evalRingHom 1 (a i))
        (MvPolynomial.map (Polynomial.evalRingHom 1) g) := by
      rw [eval_map_hom]; rfl
    have hA : (1:ℤ) ≤ (e:ℤ) * ((r:ℤ) - 1) := by
      have : (1:ℤ) ≤ e := by exact_mod_cast he
      nlinarith
    have hb := eval_bound d (by omega) ((e:ℤ) * ((r:ℤ) - 1)) hA
      (MvPolynomial.map (Polynomial.evalRingHom 1) g)
      (fun s hs i => hf' s (supp_g s (MvPolynomial.support_map_subset _ _ hs)) i)
      (fun s => by
        rw [MvPolynomial.coeff_map, coeff_g, Polynomial.coe_evalRingHom]
        exact eval_one_liftElt hE he _)
      (fun i => Polynomial.evalRingHom 1 (a i))
      (fun i => by
        rw [Polynomial.coe_evalRingHom]
        exact eval_one_liftElt hE he _)
    rw [h1]
    refine le_trans hb.2 (le_of_eq ?_)
    rw [hM]; unfold bigM
    push_cast [Nat.cast_sub (by omega : 1 ≤ r)]
    ring
  -- (P3) degree
  have hdeg : P.natDegree ≤ D := by
    rw [hPsum]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro s hs
    refine (Polynomial.natDegree_mul_le).trans ?_
    have h1 : (g.coeff s).natDegree ≤ e - 1 := by rw [coeff_g]; exact deg_lift _
    have h2 : (∏ i, a i ^ s i).natDegree ≤ m * ((d - 1) * (e - 1)) := by
      refine (Polynomial.natDegree_prod_le _ _).trans ?_
      calc ∑ i, (a i ^ s i).natDegree ≤ ∑ _i : Fin m, (d - 1) * (e - 1) := by
            apply Finset.sum_le_sum; intro i _
            refine (Polynomial.natDegree_pow_le).trans ?_
            exact Nat.mul_le_mul (hf' s (supp_g s hs) i) (deg_lift _)
        _ = m * ((d - 1) * (e - 1)) := by simp
    rw [hD]; unfold digitDegree
    obtain ⟨d', hd'⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [hd'] at h2 ⊢
    simp only [Nat.add_sub_cancel] at h2
    have h3 : e - 1 ≤ (e - 1) * m := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  -- (P4) coefficients as naturals
  have hMge : 2 ≤ M := by
    rw [hM]; unfold bigM
    have : 1 ≤ d ^ m * (e * (r - 1)) ^ ((d - 1) * m + 1) := by
      apply Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ ?_)
      have : 1 ≤ e := he
      have : 1 ≤ r - 1 := by omega
      nlinarith
    omega
  set c : ℕ → ℕ := fun j => (P.coeff j).toNat with hc
  have hcP : ∀ j, (c j : ℤ) = P.coeff j := fun j => Int.toNat_of_nonneg (hNN j)
  have hcM : ∀ j, c j < M := by
    intro j
    have h1 := coeff_le_eval_one hNN j
    have : (c j : ℤ) < M := by rw [hcP]; linarith
    exact_mod_cast this
  set n : ℕ := ∑ j ∈ Finset.range (D + 1), c j * M ^ j with hn
  have hPM : P.eval (M : ℤ) = (n : ℤ) := by
    rw [Polynomial.eval_eq_sum_range' (n := D + 1) (by omega), hn]
    push_cast
    apply Finset.sum_congr rfl; intro j _; rw [hcP]
  have hnr' : n < r' := by
    rw [hr', rPrime, ← hD]
    exact digit_sum_lt M (by omega) (D + 1) c hcM
  have hr'2 : 2 ≤ r' := by
    rw [hr', rPrime, ← hD, ← hM]
    exact le_trans hMge (Nat.le_self_pow (by omega) M)
  -- (P6) the inner call
  have hβ : multimodular d t r' (MvPolynomial.map (evalAtM M r') g) (fun i => evalAtM M r' (a i))
      = ((n : ℕ) : ZMod r') := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [mm_correct d hd hm t' r' hr'2 _ _ (fun s hs i =>
      hf' s (supp_g s (MvPolynomial.support_map_subset _ _ hs)) i), eval_map_hom (evalAtM M r') g a]
    rw [← hP]
    unfold evalAtM
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_at_natCast, hPM]
    simp
  haveI : NeZero r' := ⟨by omega⟩
  have hβval : (((n : ℕ) : ZMod r').val) = n := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt hnr'
  -- (P7) digits recover P
  have hdig : digitPoly M D n = P := by
    unfold digitPoly
    conv_rhs => rw [Polynomial.as_sum_range' P (D + 1) (by omega)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Polynomial.C_mul_X_pow_eq_monomial, hn,
      digit_eq M (by omega) (D + 1) c hcM j (Finset.mem_range.1 hj), hcP]
  rw [hβ, hβval, hdig]
  -- (P8) map back to R
  let ψ : ℤ[X] →+* AdjoinRoot E := (AdjoinRoot.mk E).comp (Polynomial.mapRingHom (Int.castRingHom (ZMod r)))
  have hψ : ∀ x, ψ (liftElt hE x) = x := fun x => by
    simp only [ψ, RingHom.comp_apply, Polynomial.coe_mapRingHom, liftElt, map_liftZPoly]
    exact AdjoinRoot.mk_leftInverse hE x
  show ψ P = _
  rw [hP, ← eval_map_hom ψ g a]
  have h1 : MvPolynomial.map ψ g = f := by
    ext s; rw [MvPolynomial.coeff_map, coeff_g, hψ]
  have h2 : (fun i => ψ (a i)) = α := by
    funext i; rw [ha]; exact hψ (α i)
  rw [h1, h2]

theorem main_thm {r m : ℕ} [NeZero r] (d t : ℕ) (ht : 1 ≤ t) (hd : 2 ≤ d) (hm : 1 ≤ m)
    (E : (ZMod r)[X]) (hE : E.Monic) (he : 1 ≤ E.natDegree)
    (f : MvPolynomial (Fin m) (AdjoinRoot E)) (hf : ∀ i, f.degreeOf i ≤ d - 1)
    (α : Fin m → AdjoinRoot E) :
    multimodularExt d t hE f α = MvPolynomial.eval α f := by
  rcases Nat.lt_or_ge r 2 with hr | hr
  · have hr1 : r = 1 := by have := NeZero.ne r; omega
    subst hr1
    haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.2 rfl
    haveI : Subsingleton (AdjoinRoot E) := ⟨fun x y => by
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
      obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
      rw [show p = q from Polynomial.ext fun n => Subsingleton.elim _ _]⟩
    exact Subsingleton.elim _ _
  · exact ext_main hr d t ht hd hm E hE he f hf α

end ExtPart

end KUMM44

open Polynomial KedlayaUmans.Multimodular in
theorem solution {r m : ℕ} [NeZero r] (d t : ℕ) (ht : 1 ≤ t) (hd : 2 ≤ d) (hm : 1 ≤ m)
    (E : (ZMod r)[X]) (hE : E.Monic) (he : 1 ≤ E.natDegree)
    (f : MvPolynomial (Fin m) (AdjoinRoot E)) (hf : ∀ i, f.degreeOf i ≤ d - 1)
    (α : Fin m → AdjoinRoot E) :
    multimodularExt d t hE f α = MvPolynomial.eval α f := by
  exact KUMM44.main_thm d t ht hd hm E hE he f hf α
