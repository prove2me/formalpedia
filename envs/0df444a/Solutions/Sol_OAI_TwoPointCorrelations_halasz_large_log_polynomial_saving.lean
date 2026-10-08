-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_large_log_polynomial_saving
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:02:30.697446+00:00
-- url     : https://prove2.me/submissions/88d65886-7c20-4e6c-99a8-9c8cd58d0ff1

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_classical_step
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_normalized_double_moment

section
-- module Solutions.OAIChowla.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open _root_.Polynomial


lemma Multiset.esymm_of_card_lt {R : Type*} [CommSemiring R] {s : Multiset R} {n : ℕ}
    (h : s.card < n) : s.esymm n = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ h]


namespace Finset



end Finset

section LogSubst
open _root_.Real _root_.Set _root_.MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end LogSubst

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovDiagonal
namespace OAI

/-! The diagonal algebra for the complete Vinogradov system: its first
s power sums determine all elementary symmetric functions of s entries.
This is the finite algebraic starting point for the mean-value argument
underlying Ford's logarithmic exponential-sum estimate. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MvPolynomial

theorem halasz_vinogradov_esymm {s : ℕ} (x y : Fin s → ℚ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ s → ∑ i, x i^j = ∑ i, y i^j) :
    ∀ k : ℕ, k ≤ s →
      eval x (esymm (Fin s) ℚ k) = eval y (esymm (Fin s) ℚ k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hks
    by_cases hk : k=0
    · subst k
      simp
    have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    have he (a : ℕ × ℕ) (ha : a ∈ (antidiagonal k).filter (fun a => a.1< k)) :
        eval x ((-1: MvPolynomial (Fin s) ℚ)^a.1 * esymm (Fin s) ℚ a.1 * psum (Fin s) ℚ a.2) =
          eval y ((-1: MvPolynomial (Fin s) ℚ)^a.1 * esymm (Fin s) ℚ a.1 * psum (Fin s) ℚ a.2) := by
      obtain ⟨ha,hak⟩ := mem_filter.mp ha
      have hab : a.1+a.2=k := mem_antidiagonal.mp ha
      have hp := hpower a.2 (by omega) (by omega)
      have hi := ih a.1 hak (by omega)
      simp only [map_mul,map_pow,map_neg,map_one]
      rw [hi]
      have heval : eval x (psum (Fin s) ℚ a.2) = eval y (psum (Fin s) ℚ a.2) := by
        simpa [psum] using hp
      rw [heval]
    have hsum := sum_congr rfl he
    have hx := congrArg (eval x) (mul_esymm_eq_sum (Fin s) ℚ k)
    have hy := congrArg (eval y) (mul_esymm_eq_sum (Fin s) ℚ k)
    simp only [map_mul,map_natCast,map_pow,map_neg,map_one,map_sum] at hx hy
    have heq : (k:ℚ)*eval x (esymm (Fin s) ℚ k) =
        (k:ℚ)*eval y (esymm (Fin s) ℚ k) := by
      rw [hx,hy]
      simpa only [map_mul,map_pow,map_neg,map_one] using
        congrArg (fun z : ℚ => (-1:ℚ)^(k+1)*z) hsum
    exact mul_left_cancel₀ (by exact_mod_cast hk : (k:ℚ)≠0) heq

/-- The complete diagonal system determines the multiset of its variables. -/
theorem halasz_vinogradov_multiset {s : ℕ} (x y : Fin s → ℚ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ s → ∑ i, x i^j = ∑ i, y i^j) :
    (univ.val.map x) = (univ.val.map y) := by
  let a : Multiset ℚ := univ.val.map x
  let b : Multiset ℚ := univ.val.map y
  have ha : a.card=s := by simp [a]
  have hb : b.card=s := by simp [b]
  have he : ∀ k : ℕ, a.esymm k=b.esymm k := by
    intro k
    by_cases hk : k ≤ s
    · have hx := aeval_esymm_eq_multiset_esymm (Fin s) ℚ k x
      have hy := aeval_esymm_eq_multiset_esymm (Fin s) ℚ k y
      rw [aeval_eq_eval] at hx hy
      exact hx.symm.trans ((halasz_vinogradov_esymm x y hpower k hk).trans hy)
    · rw [Multiset.esymm_of_card_lt (by omega : a.card< k),
        Multiset.esymm_of_card_lt (by omega : b.card< k)]
  have hprod : (a.map (fun t => Polynomial.X-Polynomial.C t)).prod =
      (b.map (fun t => Polynomial.X-Polynomial.C t)).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm,Multiset.prod_X_sub_X_eq_sum_esymm,ha,hb]
    apply sum_congr rfl
    intro k _
    rw [he k]
  have hr := congrArg Polynomial.roots hprod
  simpa only [Polynomial.roots_multiset_prod_X_sub_C] using hr


@[simp] lemma mem_halaszVinogradovFiber {s N k : ℕ} {x y : Fin s → Fin N} :
    y ∈ halaszVinogradovFiber x k ↔ ∀ j ∈ Icc 1 k,
      (∑ i, ((x i).val+1)^j) = ∑ i, ((y i).val+1)^j := by
  classical
  simp [halaszVinogradovFiber]

lemma halasz_vinogradov_fiber_perm {s N k : ℕ} (hsk : s ≤ k)
    (x y : Fin s → Fin N) (hy : y ∈ halaszVinogradovFiber x k) :
    (List.ofFn y).Perm (List.ofFn x) := by
  classical
  have hp := mem_halaszVinogradovFiber.mp hy
  let v : Fin N → ℚ := fun a => (a.val:ℚ)+1
  have hv : Function.Injective v := by
    intro a b hab
    have he : (a.val:ℚ)=(b.val:ℚ) := add_right_cancel hab
    exact Fin.ext (by exact_mod_cast he)
  have hq : ∀ j : ℕ, 1 ≤ j → j ≤ s →
      (∑ i, v (y i)^j) = ∑ i, v (x i)^j := by
    intro j hj hjs
    have hh := (hp j (mem_Icc.mpr ⟨hj,hjs.trans hsk⟩)).symm
    dsimp only [v]
    exact_mod_cast hh
  have hm := halasz_vinogradov_multiset (fun i => v (y i)) (fun i => v (x i)) hq
  have hu : (univ:Finset (Fin s)).val=(List.finRange s:Multiset (Fin s)) := by
    apply Multiset.ext.mpr
    intro i
    simp
  apply Multiset.coe_eq_coe.mp
  rw [List.ofFn_eq_map,List.ofFn_eq_map,← Multiset.map_coe,← Multiset.map_coe,← hu]
  apply Multiset.map_injective hv
  simpa only [Multiset.map_map,Function.comp_def] using hm

theorem halasz_vinogradov_fiber_card {s N k : ℕ} (hsk : s ≤ k)
    (x : Fin s → Fin N) : (halaszVinogradovFiber x k).card ≤ s.factorial := by
  classical
  let A := halaszVinogradovFiber x k
  have hinj : Function.Injective (List.ofFn : (Fin s → Fin N) → List (Fin N)) :=
    List.ofFn_injective
  have hsub : A.image List.ofFn ⊆ (List.ofFn x).permutations.toFinset := by
    intro l hl
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hl
    exact List.mem_toFinset.mpr (List.mem_permutations.mpr
      (halasz_vinogradov_fiber_perm hsk x y hy))
  calc
    A.card = (A.image List.ofFn).card := (card_image_of_injective A hinj).symm
    _ ≤ ((List.ofFn x).permutations.toFinset).card := card_le_card hsub
    _ ≤ (List.ofFn x).permutations.length := List.toFinset_card_le _
    _ = s.factorial := by rw [List.length_permutations,List.length_ofFn]


/-- The diagonal-range upper bound for the complete Vinogradov system. -/
theorem halasz_vinogradov_diagonal_bound {s k N : ℕ} (hsk : s ≤ k) :
    halaszVinogradovCount s k N ≤ N^s*s.factorial := by
  unfold halaszVinogradovCount
  calc
    _ ≤ ∑ _x : Fin s → Fin N, s.factorial :=
      sum_le_sum (fun x _ => halasz_vinogradov_fiber_card hsk x)
    _ = _ := by simp



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszScaleFactor
namespace OAI

/-! Normalizing the long/short scale in the classical recurrence.
The loss is a fixed exponential in the moment order. -/
namespace TwoPointCorrelations

lemma halasz_scale_factor {k : ℕ} {x R Q a e : ℝ}
    (hx : 0< x) (hR : 0< R) (hQ : 0≤ Q) (he : 0≤ e) (hae : e≤ a)
    (hRQ : Q≤2*x/R) (hRx : R≤2*x^(1/(k:ℝ))) :
    R^a*x^k*Q^e ≤ 2^a*x^((k:ℝ)+e+(a-e)/(k:ℝ)) := by
  have hbase : 0≤ R^a*x^k := mul_nonneg (Real.rpow_nonneg hR.le _) (pow_nonneg hx.le _)
  have hfirst : R^a*x^k*(2*x/R)^e =
      2^e*x^((k:ℝ)+e)*R^(a-e) := by
    rw [Real.div_rpow (by positivity : 0≤2*x) hR.le,
      Real.mul_rpow (by norm_num : (0:ℝ)≤2) hx.le,
      Real.rpow_add hx,Real.rpow_natCast,Real.rpow_sub hR]
    field_simp
  have hlast : 2^e*x^((k:ℝ)+e)*(2*x^(1/(k:ℝ)))^(a-e) =
      2^a*x^((k:ℝ)+e+(a-e)/(k:ℝ)) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hx.le _),
      ← Real.rpow_mul hx.le]
    have htwo : (2:ℝ)^e*2^(a-e)=2^a := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1
      ring
    have hxexp : (1/(k:ℝ))*(a-e)=(a-e)/(k:ℝ) := by ring
    rw [hxexp]
    calc
      _ = (2^e*2^(a-e))*(x^((k:ℝ)+e)*x^((a-e)/(k:ℝ))) := by ring
      _ = _ := by rw [htwo,← Real.rpow_add hx]
  calc
    _ ≤ R^a*x^k*(2*x/R)^e :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hQ hRQ he) hbase
    _ = 2^e*x^((k:ℝ)+e)*R^(a-e) := hfirst
    _ ≤ 2^e*x^((k:ℝ)+e)*(2*x^(1/(k:ℝ)))^(a-e) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR.le hRx (sub_nonneg.mpr hae))
      positivity
    _ = _ := hlast


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszRootScale
namespace OAI

/-! A natural modulus scale just above the k-th root, with the exact
division endpoint controlled for the classical recurrence. -/
namespace TwoPointCorrelations


lemma halasz_root_scale_pos (N k : ℕ) : 0< halaszRootScale N k := by
  unfold halaszRootScale
  omega

lemma halasz_root_scale_lt {N k : ℕ} (hk : 0< k) : N<(halaszRootScale N k)^k := by
  have hroot : 0≤(N:ℝ)^(1/(k:ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlt : (N:ℝ)^(1/(k:ℝ))<(halaszRootScale N k:ℝ) := by
    simpa only [halaszRootScale,Nat.cast_add,Nat.cast_one] using
      Nat.lt_floor_add_one ((N:ℝ)^(1/(k:ℝ)))
  have hp := pow_lt_pow_left₀ hlt hroot hk.ne'
  have he : ((N:ℝ)^(1/(k:ℝ)))^k=(N:ℝ) := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) hk.ne'
  rw [he] at hp
  exact_mod_cast hp

lemma halasz_root_scale_upper {N k : ℕ} (hN : 1≤ N) :
    (halaszRootScale N k:ℝ)≤2*(N:ℝ)^(1/(k:ℝ)) := by
  have hroot : 1≤(N:ℝ)^(1/(k:ℝ)) := Real.one_le_rpow
    (by exact_mod_cast hN) (by positivity)
  have hf := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) (1/(k:ℝ)))
  simp only [halaszRootScale,Nat.cast_add,Nat.cast_one]
  linarith

lemma halasz_root_scale_large {N k T : ℕ} (hk : 0< k) (hT : T^k≤ N) :
    T< halaszRootScale N k := by
  by_contra! h
  have hpow := Nat.pow_le_pow_left h k
  have hstrict := halasz_root_scale_lt (N := N) hk
  omega

lemma halasz_root_scale_le_endpoint {N k : ℕ} (hk : 2≤ k) (hN : 2^k≤ N) :
    halaszRootScale N k≤ N := by
  let x := (N:ℝ)^(1/(k:ℝ))
  have hk0 : k≠0 := by omega
  have hx0 : 0≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hxk : x^k=(N:ℝ) := by
    simpa only [x,one_div] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) hk0
  have hx2 : (2:ℝ)≤ x := by
    by_contra! h
    have hh := pow_lt_pow_left₀ h hx0 hk0
    have hN' : (2:ℝ)^k≤(N:ℝ) := by exact_mod_cast hN
    rw [hxk] at hh
    linarith
  have hsquare : x^2≤ x^k := pow_le_pow_right₀ (by linarith : 1≤ x) hk
  have hfloor := Nat.floor_le hx0
  have hreal : (halaszRootScale N k:ℝ)≤(N:ℝ) := by
    simp only [halaszRootScale,Nat.cast_add,Nat.cast_one]
    change (⌊x⌋₊:ℝ)+1≤(N:ℝ)
    rw [hxk] at hsquare
    nlinarith
  exact_mod_cast hreal

lemma halasz_division_endpoint {N R : ℕ} (hR : 0< R) (hRN : R≤ N) :
    ((N/R+1:ℕ):ℝ)≤2*(N:ℝ)/(R:ℝ) := by
  have hr : (0:ℝ)< R := by exact_mod_cast hR
  have hone : (1:ℝ)≤(N:ℝ)/(R:ℝ) :=
    (le_div_iff₀ hr).mpr (by simpa only [one_mul] using
      (show (R:ℝ)≤ N by exact_mod_cast hRN))
  have hd : ((N/R:ℕ):ℝ)≤(N:ℝ)/(R:ℝ) := Nat.cast_div_le
  push_cast
  rw [show 2*(N:ℝ)/(R:ℝ)=2*((N:ℝ)/(R:ℝ)) by ring]
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszIterationScale
namespace OAI

/-! One explicit polynomial threshold for the root scale, and its
induced threshold for the summation endpoint. -/
namespace TwoPointCorrelations




lemma halasz_iteration_scale {R₀ k N : ℕ} (hk : 2≤ k)
    (hN : halaszIterationThreshold R₀ k< N) :
    2^k≤ N ∧ (4*(k:ℝ)^2)^2<(N:ℝ) ∧ R₀≤ halaszRootScale N k ∧
      (2*(k^2*k)+1)^2≤ halaszRootScale N k ∧ k< halaszRootScale N k := by
  have hparts : (halaszIterationRootThreshold R₀ k)^k< N ∧
      (4*k^2)^2< N ∧ 2^k< N := by
    unfold halaszIterationThreshold at hN
    generalize (halaszIterationRootThreshold R₀ k)^k=a at *
    generalize (4*k^2)^2=b at *
    generalize 2^k=c at *
    omega
  have hsmall := hparts.2.1
  have htwo := hparts.2.2.le
  have hT := hparts.1.le
  have hroot := halasz_root_scale_large (by omega : 0< k) hT
  have hR0 : R₀≤ halaszIterationRootThreshold R₀ k := by
    unfold halaszIterationRootThreshold
    omega
  have hm : (2*(k^2*k)+1)^2≤ halaszIterationRootThreshold R₀ k := by
    unfold halaszIterationRootThreshold
    omega
  have hkt : k< halaszIterationRootThreshold R₀ k := by
    unfold halaszIterationRootThreshold
    omega
  exact ⟨htwo,by exact_mod_cast hsmall,hR0.trans hroot.le,hm.trans hroot.le,hkt.trans hroot⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszIterationConstants
namespace OAI

/-! Explicit constants for the classical iteration. -/
namespace TwoPointCorrelations



lemma halasz_iteration_base_bounds (R₀ k : ℕ) :
    1≤ halaszIterationBase R₀ k ∧ k.factorial≤ halaszIterationBase R₀ k ∧
    (halaszIterationThreshold R₀ k)^(k+k*(k-1)/2)≤ halaszIterationBase R₀ k ∧
    2*(2*(k^2*k)+1)*k^k*32^(k*(k-1)/2)≤ halaszIterationBase R₀ k := by
  unfold halaszIterationBase
  omega

lemma halasz_iteration_constant_ge_base (R₀ k n : ℕ) :
    halaszIterationBase R₀ k≤ halaszIterationConstant R₀ k n := by
  have hb := (halasz_iteration_base_bounds R₀ k).1
  have hp : halaszIterationBase R₀ k≤(halaszIterationBase R₀ k)^(n+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hb (by omega : 1≤ n+1)
  have h32 : 1≤(32:ℕ)^(k*n*(n+1)) := Nat.one_le_pow _ _ (by decide)
  exact hp.trans (Nat.le_mul_of_pos_right _ (by omega))

lemma halasz_iteration_constant_zero (R₀ k : ℕ) :
    halaszIterationConstant R₀ k 0=halaszIterationBase R₀ k := by
  simp [halaszIterationConstant]

theorem halasz_iteration_constant_step (R₀ k n : ℕ) :
    halaszIterationConstant R₀ k n *
      (2*(2*(k^2*k)+1)*k^k*32^(2*((n+1)*k)+k*(k-1)/2)) ≤
        halaszIterationConstant R₀ k (n+1) := by
  have hc := (halasz_iteration_base_bounds R₀ k).2.2.2
  have hfactor : 2*(2*(k^2*k)+1)*k^k*32^(2*((n+1)*k)+k*(k-1)/2) =
      (2*(2*(k^2*k)+1)*k^k*32^(k*(k-1)/2))*32^(2*((n+1)*k)) := by
    rw [pow_add]
    ring
  rw [hfactor]
  calc
    _ ≤ halaszIterationConstant R₀ k n *
        (halaszIterationBase R₀ k*32^(2*((n+1)*k))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc)
    _ = halaszIterationConstant R₀ k (n+1) := by
      unfold halaszIterationConstant
      rw [pow_succ]
      have he : k*n*(n+1)+2*((n+1)*k)=k*(n+1)*(n+1+1) := by ring
      rw [← he,pow_add]
      ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszConstantGrowth
namespace OAI

/-! Polynomial-in-the-degree control of the logarithm of the explicit
iteration constant. The absolute prime-supply threshold is retained. -/
namespace TwoPointCorrelations

private lemma four_terms {b e a c d f : ℕ} (hb : 4≤ b)
    (ha : a≤ b^e) (hc : c≤ b^e) (hd : d≤ b^e) (hf : f≤ b^e) :
    a+c+d+f≤ b^(e+1) := by
  rw [pow_succ]
  have hh := Nat.mul_le_mul_left (b^e) hb
  omega

lemma halasz_iteration_threshold_growth {R₀ k : ℕ} (hk : 2≤ k) :
    halaszIterationThreshold R₀ k≤(R₀+k+32)^(10*k) := by
  let b := R₀+k+32
  have hb : 32≤ b := by omega
  have hb1 : 1≤ b := by omega
  have hkb : k≤ b := by omega
  have hRb : R₀≤ b := by omega
  have h3 : 1≤ b^3 := Nat.one_le_pow _ _ hb1
  have hm : 2*(k^2*k)+1≤ b^4 := by
    have hk3 : k^2*k≤ b^3 := by simpa [pow_succ] using Nat.pow_le_pow_left hkb 3
    have hfour : b^3*3≤ b^3*b := Nat.mul_le_mul_left _ (by omega)
    rw [← pow_succ] at hfour
    change b^3*3≤ b^4 at hfour
    omega
  have hm2 : (2*(k^2*k)+1)^2≤ b^8 := by
    simpa [← pow_mul] using Nat.pow_le_pow_left hm 2
  have hbe : b≤ b^8 := by simpa using pow_le_pow_right₀ hb1 (by decide : 1≤8)
  have hT : halaszIterationRootThreshold R₀ k≤ b^9 := by
    exact four_terms (by omega) (hRb.trans hbe) hm2 (hkb.trans hbe)
      ((show 2≤ b by omega).trans hbe)
  have hp : (halaszIterationRootThreshold R₀ k)^k≤ b^(9*k) := by
    simpa [← pow_mul] using Nat.pow_le_pow_left hT k
  have hs : (4*k^2)^2≤ b^8 := by
    have hkk := Nat.pow_le_pow_left hkb 2
    have hb2 : 4≤ b^2 := by nlinarith
    have hmul := Nat.mul_le_mul hb2 hkk
    have ht : 4*k^2≤ b^4 := by simpa [← pow_add] using hmul
    simpa [← pow_mul] using Nat.pow_le_pow_left ht 2
  have hs' : (4*k^2)^2≤ b^(9*k) := hs.trans (pow_le_pow_right₀ hb1 (by omega))
  have htwo : 2^k≤ b^(9*k) := (Nat.pow_le_pow_left (by omega : 2≤ b) k).trans
    (pow_le_pow_right₀ hb1 (by omega))
  have hone : 1≤ b^(9*k) := Nat.one_le_pow _ _ hb1
  exact (four_terms (by omega) hp hs' htwo hone).trans
    (pow_le_pow_right₀ hb1 (by omega))

lemma halasz_iteration_base_growth {R₀ k : ℕ} (hk : 2≤ k) :
    halaszIterationBase R₀ k≤(R₀+k+32)^(11*k^3) := by
  let b := R₀+k+32
  have hb : 32≤ b := by omega
  have hb1 : 1≤ b := by omega
  have hkb : k≤ b := by omega
  have hk1 : 1≤ k := by omega
  have hk3 : k≤ k^3 := by simpa using pow_le_pow_right₀ hk1 (by decide : 1≤3)
  have htri : k*(k-1)/2≤ k^2 := (Nat.div_le_self _ _).trans (by
    simpa [pow_two] using Nat.mul_le_mul_left k (Nat.sub_le k 1))
  have hK : k+k*(k-1)/2≤ k^2 := by
    have he := Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one k)
    have hsub : k*(k-1)=k^2-k := by
      rw [Nat.mul_sub_left_distrib,pow_two,mul_one]
    rw [hsub] at he ⊢
    have hkk : k≤ k^2 := by simpa using pow_le_pow_right₀ hk1 (by decide : 1≤2)
    omega
  have hH : (halaszIterationThreshold R₀ k)^(k+k*(k-1)/2)≤ b^(10*k^3) := by
    have hh := Nat.pow_le_pow_left (halasz_iteration_threshold_growth (R₀ := R₀) hk) (k+k*(k-1)/2)
    rw [← pow_mul] at hh
    apply hh.trans (pow_le_pow_right₀ hb1 _)
    nlinarith
  have hfact : k.factorial≤ b^(10*k^3) := (Nat.factorial_le_pow k).trans
    ((Nat.pow_le_pow_left hkb k).trans (pow_le_pow_right₀ hb1 (by omega)))
  have h3 : 1≤ b^3 := Nat.one_le_pow _ _ hb1
  have hm : 2*(k^2*k)+1≤ b^4 := by
    have hk3b : k^2*k≤ b^3 := by simpa [pow_succ] using Nat.pow_le_pow_left hkb 3
    have hfour : b^3*3≤ b^3*b := Nat.mul_le_mul_left _ (by omega)
    rw [← pow_succ] at hfour
    change b^3*3≤ b^4 at hfour
    omega
  have hstep : 2*(2*(k^2*k)+1)*k^k*32^(k*(k-1)/2)≤ b^(10*k^3) := by
    have hh := Nat.mul_le_mul (Nat.mul_le_mul
      (Nat.mul_le_mul (show 2≤ b by omega) hm) (Nat.pow_le_pow_left hkb k))
      (Nat.pow_le_pow_left hb (k*(k-1)/2))
    have hh' : 2*(2*(k^2*k)+1)*k^k*32^(k*(k-1)/2)≤ b^(5+k+k*(k-1)/2) := by
      convert (preTransparency := .instances) hh using 1
      simp only [pow_add,pow_succ]
      ring
    apply hh'.trans (pow_le_pow_right₀ hb1 _)
    have hk2 : k^2≤ k^3 := pow_le_pow_right₀ hk1 (by decide : 2≤3)
    have hk32 : 2≤ k^3 := (show 2≤ k from hk).trans hk3
    omega
  have hone : 1≤ b^(10*k^3) := Nat.one_le_pow _ _ hb1
  exact (four_terms (by omega) hfact hH hstep hone).trans
    (pow_le_pow_right₀ hb1 (by nlinarith))

/-- The constant at the selected moment has logarithm `O(k^4 log k)`.
No endpoint-dependent constant is hidden. -/
theorem halasz_selected_constant_growth {R₀ k : ℕ} (hk : 2≤ k) :
    halaszIterationConstant R₀ k (10*k)≤(R₀+k+32)^(256*k^4) := by
  let b := R₀+k+32
  have hb : 32≤ b := by omega
  have hb1 : 1≤ b := by omega
  have hk1 : 1≤ k := by omega
  have h1 := Nat.pow_le_pow_left (halasz_iteration_base_growth (R₀ := R₀) hk) (10*k+1)
  have h2 := Nat.pow_le_pow_left hb (k*(10*k)*(10*k+1))
  have hmul := Nat.mul_le_mul h1 h2
  unfold halaszIterationConstant
  apply hmul.trans
  rw [← pow_mul,← pow_add]
  apply pow_le_pow_right₀ hb1
  have h34 : k^3≤ k^4 := pow_le_pow_right₀ hk1 (by decide : 3≤4)
  have h24 : k^2≤ k^4 := pow_le_pow_right₀ hk1 (by decide : 2≤4)
  have he : 11*k^3*(10*k+1)+k*(10*k)*(10*k+1)=110*k^4+111*k^3+10*k^2 := by ring
  rw [he]
  omega

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszNormalizedStep
namespace OAI

/-! The classical step in the power-bound form used by iteration. -/
namespace TwoPointCorrelations


theorem halasz_normalize_classical_bound {s k N R : ℕ} {A e : ℝ}
    (hN : 0< N) (hR : 0< R) (hRN : R≤ N)
    (hroot : (R:ℝ)≤2*(N:ℝ)^(1/(k:ℝ))) (hA : 0≤ A)
    (he : 0≤ e) (hea : e≤(halaszStepExponent s k:ℝ))
    (hshort : (halaszVinogradovCount s k (N/R+1):ℝ)≤ A*((N/R+1:ℕ):ℝ)^e)
    (hstep : halaszVinogradovCount (k+s) k N ≤
      2*(2*(k^2*k)+1)*((16*R)^(2*s)*((k^k*(16*R)^(k*(k-1)/2))*
        (N^k*halaszVinogradovCount s k (N/R+1))))) :
    (halaszVinogradovCount (k+s) k N:ℝ) ≤
      (A*(2*(2*(k^2*k)+1)*(k:ℝ)^k*32^(halaszStepExponent s k)))*
        (N:ℝ)^((k:ℝ)+e+((halaszStepExponent s k:ℝ)-e)/(k:ℝ)) := by
  let a := halaszStepExponent s k
  let C : ℝ := 2*(2*(k^2*k)+1)*(k:ℝ)^k*16^a
  have hC : 0≤ C := by dsimp [C]; positivity
  have hN0 : (0:ℝ)< N := by exact_mod_cast hN
  have hR0 : (0:ℝ)< R := by exact_mod_cast hR
  have hnat : halaszVinogradovCount (k+s) k N ≤
      (2*(2*(k^2*k)+1)*k^k*16^a)*R^a*N^k*halaszVinogradovCount s k (N/R+1) := by
    convert (preTransparency := .instances) hstep using 1
    simp only [a,halaszStepExponent,pow_add,mul_pow]
    ring
  have hreal : (halaszVinogradovCount (k+s) k N:ℝ) ≤
      C*(R:ℝ)^a*(N:ℝ)^k*(halaszVinogradovCount s k (N/R+1):ℝ) := by
    dsimp only [C]
    exact_mod_cast hnat
  have hscale := halasz_scale_factor hN0 hR0 (by positivity : (0:ℝ)≤(N/R+1:ℕ))
    he hea (halasz_division_endpoint hR hRN) hroot
  rw [Real.rpow_natCast] at hscale
  have hmul := mul_le_mul_of_nonneg_left hscale (mul_nonneg hA hC)
  have h32 : (16:ℝ)^a*2^a=(32:ℝ)^a := by rw [← mul_pow]; norm_num
  calc
    (halaszVinogradovCount (k+s) k N:ℝ)
        ≤ C*(R:ℝ)^a*(N:ℝ)^k*(A*((N/R+1:ℕ):ℝ)^e) :=
      hreal.trans (mul_le_mul_of_nonneg_left hshort (by positivity))
    _ = (A*C)*((R:ℝ)^a*(N:ℝ)^k*((N/R+1:ℕ):ℝ)^e) := by ring
    _ ≤ (A*C)*(2^a*(N:ℝ)^((k:ℝ)+e+((a:ℝ)-e)/(k:ℝ))) := by
      simpa only [Real.rpow_natCast] using hmul
    _ = _ := by
      dsimp only [C]
      rw [show A*(2*(2*(k^2*k)+1)*(k:ℝ)^k*16^a)*
          (2^a*(N:ℝ)^((k:ℝ)+e+((a:ℝ)-e)/(k:ℝ))) =
          (A*(2*(2*(k^2*k)+1)*(k:ℝ)^k)*(16^a*2^a))*
            (N:ℝ)^((k:ℝ)+e+((a:ℝ)-e)/(k:ℝ)) by ring,h32]
      dsimp only [a]
      ring

theorem halasz_normalized_classical_step : ∃ R₀ : ℕ, ∀ s k N : ℕ, ∀ A e : ℝ,
    0< s → 2≤ k → 2^k≤ N → (4*(k:ℝ)^2)^2<(N:ℝ) →
    R₀≤ halaszRootScale N k → (2*(k^2*k)+1)^2≤ halaszRootScale N k →
    k< halaszRootScale N k → 0≤ A → 0≤ e → e≤(halaszStepExponent s k:ℝ) →
    ((halaszVinogradovCount s k (N/halaszRootScale N k+1):ℝ)≤
      A*((N/halaszRootScale N k+1:ℕ):ℝ)^e) →
    (halaszVinogradovCount (k+s) k N:ℝ) ≤
      (A*(2*(2*(k^2*k)+1)*(k:ℝ)^k*32^(halaszStepExponent s k)))*
        (N:ℝ)^((k:ℝ)+e+((halaszStepExponent s k:ℝ)-e)/(k:ℝ)) := by
  obtain ⟨R₀,hstep⟩ := halasz_classical_step
  refine ⟨R₀,?_⟩
  intro s k N A e hs hk hN hsize hR0 hmany hkR hA he hea hshort
  have hN0 : 0< N := (pow_pos (by omega : 0<(2:ℕ)) k).trans_le hN
  have h := hstep s k N (halaszRootScale N k) hs hk hsize hkR
    (halasz_root_scale_lt (by omega)) hR0 hmany
  exact halasz_normalize_classical_bound hN0 (halasz_root_scale_pos N k)
    (halasz_root_scale_le_endpoint hk hN) (halasz_root_scale_upper (by omega)) hA he hea hshort h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszClassicalDefect
namespace OAI

/-! The geometric defect in the classical Vinogradov iteration. -/
namespace TwoPointCorrelations





lemma halasz_triangular_degree_cast {k : ℕ} (hk : 0< k) :
    (halaszTriangularDegree k:ℝ)=(k:ℝ)*(k-1)/2 := by
  have h := Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one k)
  have hR : (2:ℝ)*(halaszTriangularDegree k:ℝ)=(k:ℝ)*((k-1:ℕ):ℝ) := by
    exact_mod_cast h
  rw [Nat.cast_sub hk,Nat.cast_one] at hR
  linarith

lemma halasz_total_degree_cast {k : ℕ} (hk : 0< k) :
    (halaszTotalDegree k:ℝ)=(k:ℝ)*(k+1)/2 := by
  simp only [halaszTotalDegree,Nat.cast_add,halasz_triangular_degree_cast hk]
  ring

lemma halasz_classical_ratio_bounds {k : ℕ} (hk : 0< k) :
    0≤1-1/(k:ℝ) ∧ 1-1/(k:ℝ)≤1 := by
  have hk1 : (1:ℝ)≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ)< k := by exact_mod_cast hk
  have hi : 1/(k:ℝ)≤1 := (div_le_one hk0).mpr hk1
  constructor <;> linarith [one_div_pos.mpr hk0]

lemma halasz_classical_defect_bounds {k : ℕ} (hk : 0< k) (n : ℕ) :
    0≤ halaszClassicalDefect k n ∧
      halaszClassicalDefect k n≤(halaszTriangularDegree k:ℝ) := by
  have hr := halasz_classical_ratio_bounds hk
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr.1 _)
  · exact mul_le_of_le_one_right (Nat.cast_nonneg _)
      (pow_le_one₀ hr.1 hr.2)

lemma halasz_classical_defect_successor (k n : ℕ) :
    halaszClassicalDefect k (n+1)=(1-1/(k:ℝ))*halaszClassicalDefect k n := by
  simp only [halaszClassicalDefect,pow_succ]
  ring

lemma halasz_classical_exponent_zero (k : ℕ) : halaszClassicalExponent k 0=k := by
  simp only [halaszClassicalExponent,halaszClassicalDefect,pow_zero,mul_one,
    zero_add,one_mul,halaszTotalDegree,Nat.cast_add]
  ring

lemma halasz_classical_exponent_successor (k n : ℕ) :
    halaszClassicalExponent k (n+1)=halaszClassicalExponent k n+2*k-
      halaszClassicalDefect k n/(k:ℝ) := by
  simp only [halaszClassicalExponent,halasz_classical_defect_successor,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  ring

lemma halasz_classical_exponent_bounds {k : ℕ} (hk : 0< k) (n : ℕ) :
    (k:ℝ)≤ halaszClassicalExponent k n ∧
      halaszClassicalExponent k n≤(halaszStepExponent ((n+1)*k) k:ℝ) := by
  have hk0 : (0:ℝ)< k := by exact_mod_cast hk
  have hd (n : ℕ) : halaszClassicalDefect k n/(k:ℝ)≤ k := by
    apply (div_le_iff₀ hk0).mpr
    have hh := (halasz_classical_defect_bounds hk n).2
    rw [halasz_triangular_degree_cast hk] at hh
    nlinarith
  constructor
  · induction n with
    | zero => exact (halasz_classical_exponent_zero k).ge
    | succ n ih =>
      rw [halasz_classical_exponent_successor]
      linarith [hd n]
  · have hh := (halasz_classical_defect_bounds hk n).2
    simp only [halaszClassicalExponent,halaszTotalDegree,Nat.cast_add,
      halaszStepExponent,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    change 2*(((n:ℝ)+1)*k)-((k:ℝ)+(halaszTriangularDegree k:ℝ))+
      halaszClassicalDefect k n ≤ 2*(((n:ℝ)+1)*k)+(halaszTriangularDegree k:ℝ)
    linarith [show (0:ℝ)≤(halaszTriangularDegree k:ℝ) from Nat.cast_nonneg _]

lemma halasz_classical_exponent_normalization {k : ℕ} (hk : 0< k) (n : ℕ) :
    (k:ℝ)+halaszClassicalExponent k n +
      ((halaszStepExponent ((n+1)*k) k:ℝ)-halaszClassicalExponent k n)/(k:ℝ) =
      halaszClassicalExponent k (n+1) := by
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have ha : (halaszStepExponent ((n+1)*k) k:ℝ) =
      2*(((n+1)*k:ℕ):ℝ)+(halaszTriangularDegree k:ℝ) := by
    simp only [halaszStepExponent,halaszTriangularDegree,Nat.cast_add,Nat.cast_mul,
      Nat.cast_ofNat]
  rw [ha]
  simp only [halaszClassicalExponent,halasz_classical_defect_successor,
    Nat.cast_add,Nat.cast_mul,Nat.cast_one]
  rw [halasz_total_degree_cast hk,halasz_triangular_degree_cast hk]
  field_simp
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSmallMoment
namespace OAI

/-! The trivial count absorbs endpoints below the fixed iteration
threshold without changing the exponent of the large-endpoint bound. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_vinogradov_trivial (s k N : ℕ) : halaszVinogradovCount s k N≤ N^(2*s) := by
  have hf (x : Fin s → Fin N) : (halaszVinogradovFiber x k).card≤ N^s := by
    calc
      _ ≤ (univ : Finset (Fin s → Fin N)).card := card_le_card (subset_univ _)
      _ = _ := by simp
  unfold halaszVinogradovCount
  calc
    _ ≤ ∑ _x : Fin s → Fin N, N^s := sum_le_sum (fun x _ => hf x)
    _ = _ := by simp [← pow_add,two_mul]

theorem halasz_small_moment {s k N H K : ℕ} {e : ℝ}
    (hN : 1≤ N) (hNH : N≤ H) (he : (2*s:ℕ)≤ e+(K:ℝ)) :
    (halaszVinogradovCount s k N:ℝ)≤(H:ℝ)^K*(N:ℝ)^e := by
  have hN1 : (1:ℝ)≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ)< N := lt_of_lt_of_le zero_lt_one hN1
  have hcount : (halaszVinogradovCount s k N:ℝ)≤(N:ℝ)^(2*s) := by
    exact_mod_cast halasz_vinogradov_trivial s k N
  calc
    _ ≤ (N:ℝ)^(2*s) := hcount
    _ = (N:ℝ)^((2*s:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (N:ℝ)^(e+(K:ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 he
    _ = (N:ℝ)^e*(N:ℝ)^K := by rw [Real.rpow_add hN0,Real.rpow_natCast]
    _ ≤ (N:ℝ)^e*(H:ℝ)^K := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hNH) K)
      (Real.rpow_nonneg hN0.le _)
    _ = _ := mul_comm _ _

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszClassicalMeanValue
namespace OAI

/-! The iterated classical Vinogradov mean-value estimate, with an
explicit geometric defect and explicit constants at every finite scale. -/
namespace TwoPointCorrelations

theorem halasz_classical_mean_value : ∃ R₀ : ℕ, ∀ k : ℕ, 2≤ k → ∀ n N : ℕ, 1≤ N →
    (halaszVinogradovCount ((n+1)*k) k N:ℝ) ≤
      (halaszIterationConstant R₀ k n:ℝ)*(N:ℝ)^(halaszClassicalExponent k n) := by
  obtain ⟨R₀,hstep⟩ := halasz_normalized_classical_step
  refine ⟨R₀,?_⟩
  intro k hk n
  have hk0 : 0< k := by omega
  induction n with
  | zero =>
    intro N hN
    simp only [Nat.zero_add,one_mul,halasz_classical_exponent_zero,
      Real.rpow_natCast,halasz_iteration_constant_zero]
    have hf := (halasz_iteration_base_bounds R₀ k).2.1
    have hnat : halaszVinogradovCount k k N≤ halaszIterationBase R₀ k*N^k := by
      calc
        _ ≤ N^k*k.factorial := halasz_vinogradov_diagonal_bound (N := N) (le_refl k)
        _ ≤ N^k*halaszIterationBase R₀ k := Nat.mul_le_mul_left _ hf
        _ = _ := Nat.mul_comm _ _
    exact_mod_cast hnat
  | succ n ih =>
    intro N hN
    by_cases hsmall : N≤ halaszIterationThreshold R₀ k
    · have hd := (halasz_classical_defect_bounds hk0 (n+1)).1
      have he : ((2*((n+1+1)*k):ℕ):ℝ)≤
          halaszClassicalExponent k (n+1)+(halaszTotalDegree k:ℝ) := by
        unfold halaszClassicalExponent
        push_cast
        linarith
      have hh := halasz_small_moment (s := (n+1+1)*k) (k := k)
        (K := halaszTotalDegree k) hN hsmall he
      have hB : (halaszIterationThreshold R₀ k)^(halaszTotalDegree k)≤
          halaszIterationConstant R₀ k (n+1) :=
        (halasz_iteration_base_bounds R₀ k).2.2.1.trans
          (halasz_iteration_constant_ge_base R₀ k (n+1))
      exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hB)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    · have hlarge : halaszIterationThreshold R₀ k< N := by omega
      obtain ⟨hpow,hsize,hR0,hmany,hkR⟩ := halasz_iteration_scale hk hlarge
      have hs : 0<(n+1)*k := Nat.mul_pos (by omega) hk0
      have he0 : 0≤ halaszClassicalExponent k n :=
        (show (0:ℝ)≤ k from Nat.cast_nonneg _).trans
          (halasz_classical_exponent_bounds hk0 n).1
      have hh := hstep ((n+1)*k) k N (halaszIterationConstant R₀ k n:ℝ)
        (halaszClassicalExponent k n) hs hk hpow hsize hR0 hmany hkR
        (Nat.cast_nonneg _) he0 (halasz_classical_exponent_bounds hk0 n).2
        (ih (N/halaszRootScale N k+1) (Nat.le_add_left 1 _))
      rw [halasz_classical_exponent_normalization hk0 n] at hh
      rw [show k+(n+1)*k=(n+1+1)*k by ring] at hh
      have hcoef : (halaszIterationConstant R₀ k n:ℝ)*
          (2*(2*(k^2*k)+1)*(k:ℝ)^k*32^(halaszStepExponent ((n+1)*k) k)) ≤
          (halaszIterationConstant R₀ k (n+1):ℝ) := by
        exact_mod_cast halasz_iteration_constant_step R₀ k n
      exact hh.trans (mul_le_mul_of_nonneg_right hcoef
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSmallDefect
namespace OAI

/-! A fixed multiple of the degree gives the small quadratic defect
needed in the double mean-value argument. -/
namespace TwoPointCorrelations

lemma halasz_classical_ratio_block {k : ℕ} (hk : 2≤ k) :
    (1-1/(k:ℝ))^k≤(1/2:ℝ) := by
  have hk0 : (0:ℝ)< k := by exact_mod_cast (show 0< k by omega)
  have hq := (halasz_classical_ratio_bounds (by omega : 0< k)).1
  have hki : 0≤1/(k:ℝ) := by positivity
  have hb := one_add_mul_le_pow (show (-2:ℝ)≤1/(k:ℝ) by linarith) k
  have hb2 : (2:ℝ)≤(1+1/(k:ℝ))^k := by
    simpa only [mul_one_div_cancel hk0.ne',one_add_one_eq_two] using hb
  have hprod : (1-1/(k:ℝ))^k*(1+1/(k:ℝ))^k≤1 := by
    rw [← mul_pow]
    apply pow_le_one₀ (mul_nonneg hq (by positivity))
    nlinarith [sq_nonneg (1/(k:ℝ))]
  have hp := pow_nonneg hq k
  nlinarith

lemma halasz_classical_defect_ten_blocks {k : ℕ} (hk : 2≤ k) :
    halaszClassicalDefect k (10*k)≤(k:ℝ)^2/2048 := by
  have hkpos : 0< k := by omega
  have hq := (halasz_classical_ratio_bounds hkpos).1
  have hp := pow_le_pow_left₀ (pow_nonneg hq k) (halasz_classical_ratio_block hk) 10
  norm_num at hp
  have he : (1-1/(k:ℝ))^(10*k)=((1-1/(k:ℝ))^k)^10 := by
    rw [← pow_mul]
    congr 1
    omega
  unfold halaszClassicalDefect
  rw [he]
  have htri0 : (0:ℝ)≤(halaszTriangularDegree k:ℝ) := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_left hp htri0
  rw [halasz_triangular_degree_cast hkpos] at hm
  rw [halasz_triangular_degree_cast hkpos]
  have hk0 : (0:ℝ)≤ k := Nat.cast_nonneg _
  simp only [one_div] at *
  nlinarith

/-- The selected moment has a defect at most `k^2/2048`, uniformly in
its endpoint. Its explicit constant is bounded separately. -/
theorem halasz_classical_selected_moment : ∃ R₀ : ℕ, ∀ k : ℕ, 2≤ k →
    ∀ N : ℕ, 1≤ N →
    (halaszVinogradovCount ((10*k+1)*k) k N:ℝ) ≤
      (halaszIterationConstant R₀ k (10*k):ℝ)*
        (N:ℝ)^(2*(((10*k+1)*k:ℕ):ℝ)-(halaszTotalDegree k:ℝ)+(k:ℝ)^2/2048) := by
  obtain ⟨R₀,hmean⟩ := halasz_classical_mean_value
  refine ⟨R₀,?_⟩
  intro k hk N hN
  apply (hmean k hk (10*k) N hN).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
  unfold halaszClassicalExponent
  linarith [halasz_classical_defect_ten_blocks hk]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszQuantitativeMeanValue
namespace OAI

/-! The one quantitative complete-system estimate used by the subsequent
logarithmic phase argument. Both the defect and the constant are explicit. -/
namespace TwoPointCorrelations

theorem halasz_quantitative_mean_value : ∃ R₀ : ℕ, ∀ k : ℕ, 2≤ k →
    ∀ N : ℕ, 1≤ N →
    (halaszVinogradovCount ((10*k+1)*k) k N:ℝ) ≤
      (R₀+k+32:ℝ)^(256*k^4)*
        (N:ℝ)^(2*(((10*k+1)*k:ℕ):ℝ)-(halaszTotalDegree k:ℝ)+(k:ℝ)^2/2048) := by
  obtain ⟨R₀,hmean⟩ := halasz_classical_selected_moment
  refine ⟨R₀,?_⟩
  intro k hk N hN
  apply (hmean k hk N hN).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact_mod_cast halasz_selected_constant_growth (R₀ := R₀) hk

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDegreeSaving
namespace OAI

/-! Numerical margins for the degree and shift-length choices in the
logarithmic exponential-sum application. -/
namespace TwoPointCorrelations





lemma halasz_large_degree_margin {m : ℝ} (hm : 8≤ m) :
    m^2/4≤(2*m+1)*(m-6)-(12*m)^2/1024 := by
  have hh : 0≤ m*(m-8) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma halasz_large_degree_saving {m lam j : ℝ} (hm : 8≤ m)
    (hlamlo : 6*m-6≤ lam) (hlamhi : lam≤6*m)
    (hjlo : 8*m≤ j) (hjhi : j≤10*m) :
    m-6≤ min (j/4) (min (j-lam) (lam-j/2)) := by
  apply le_min
  · linarith
  · apply le_min <;> linarith



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCircleWindow
namespace OAI

/-! A compact circle window with a lower bound for its small Fourier
coefficients. This supplies the localizer for the double moment estimate. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Metric _root_.Set
open scoped _root_.ComplexConjugate

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogCoefficients
namespace OAI

/-! Identification of the logarithmic Taylor polynomial with the exact
coefficient-torus character in the double mean-value estimate. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Complex


lemma halasz_log_coefficient_ne_zero {k : ℕ} {t z : ℝ}
    (ht : t≠0) (hz : z≠0) (j : Fin k) : halaszLogCoefficient t z j≠0 := by
  unfold halaszLogCoefficient
  exact div_ne_zero (mul_ne_zero ht (pow_ne_zero _ (by norm_num)))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (by positivity)) (pow_ne_zero _ hz))

lemma halasz_log_coefficient_abs {k : ℕ} (t z : ℝ) (j : Fin k) :
    |halaszLogCoefficient t z j|=|t|/(2*Real.pi*(j.val+1)*|z|^(j.val+1)) := by
  simp only [halaszLogCoefficient,abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,
    mul_one,abs_of_nonneg (by norm_num : 0≤(2:ℝ)),abs_of_pos Real.pi_pos]
  rw [abs_of_nonneg (show 0≤(j.val:ℝ)+1 by positivity)]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszNormalizedDoubleMoment
namespace OAI

/-! Cancellation of the two complete-system degree costs against the
coordinate volumes in the double moment. -/
namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_coordinate_degree (k : ℕ) :
    (∑ j : Fin k, ((j.val+1:ℕ):ℝ))=(k:ℝ)*(k+1)/2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih]
    push_cast
    ring

lemma halasz_coordinate_total_degree {k : ℕ} (hk : 0< k) :
    ((∑ j : Fin k, (j.val+1):ℕ):ℝ)=(halaszTotalDegree k:ℝ) := by
  rw [halasz_total_degree_cast hk]
  simpa only [Nat.cast_sum] using halasz_coordinate_degree k

lemma halasz_normalized_weight_nonneg {k r M : ℕ} (γ : Fin k → ℝ) (j : Fin k) :
    0≤ halaszNormalizedWeight r M γ j := by
  unfold halaszNormalizedWeight
  positivity



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogWeights
namespace OAI

/-! The three competing degree weights for the logarithmic phase. -/
namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_log_weight_identity {k r M : ℕ} (hr : 1≤ r) (hM : 1≤ M)
    {t z : ℝ} (ht : t≠0) (hz : 0< z) (j : Fin k) :
    halaszNormalizedWeight r M (halaszLogCoefficient t z) j =
      min (2*(r:ℝ)+1)
        ((5/2:ℝ)/(M:ℝ)^(j.val+1)+
          (r:ℝ)*|t|/(Real.pi*(j.val+1)*z^(j.val+1))+
          Real.pi*(j.val+1)*z^(j.val+1)/
            ((r:ℝ)*((M:ℝ)^(j.val+1))^2*|t|)) := by
  have hr0 : (r:ℝ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have hM0 : (M:ℝ)≠0 := by exact_mod_cast (show M≠0 by omega)
  have hj0 : (j.val:ℝ)+1≠0 := by positivity
  have ht0 : |t|≠0 := abs_ne_zero.mpr ht
  unfold halaszNormalizedWeight
  rw [halasz_log_coefficient_abs,abs_of_pos hz]
  congr 1
  field_simp [hr0,hM0,hj0,ht0,hz.ne',Real.pi_ne_zero]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogWeightBounds
namespace OAI

/-! The coordinate saving follows from the three elementary scale ratios. -/
namespace TwoPointCorrelations

lemma halasz_log_weight_bound {k r M : ℕ} (hr : 1≤ r) (hM : 1≤ M)
    {t z N A B E η : ℝ} (ht : t≠0) (hz : 0< z) (j : Fin k)
    (h₁ : 1/(M:ℝ)^(j.val+1)≤ A*N^(-η))
    (h₂ : |t|/z^(j.val+1)≤ B*N^(-η))
    (h₃ : z^(j.val+1)/(((M:ℝ)^(j.val+1))^2*|t|)≤ E*N^(-η)) :
    halaszNormalizedWeight r M (halaszLogCoefficient t z) j ≤
      ((5/2:ℝ)*A+(r:ℝ)/(Real.pi*(j.val+1))*B+
        Real.pi*(j.val+1)/(r:ℝ)*E)*N^(-η) := by
  have hr0 : 0<(r:ℝ) := by exact_mod_cast (show 0< r by omega)
  have hj0 : 0<(j.val:ℝ)+1 := by positivity
  rw [halasz_log_weight_identity hr hM ht hz]
  apply (min_le_right _ _).trans
  have hh := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left h₁ (by norm_num : (0:ℝ)≤5/2))
    (mul_le_mul_of_nonneg_left h₂ (by positivity : 0≤(r:ℝ)/(Real.pi*(j.val+1)))))
    (mul_le_mul_of_nonneg_left h₃ (by positivity : 0≤ Real.pi*(j.val+1)/(r:ℝ)))
  convert (preTransparency := .instances) hh using 1
  · field_simp
  · ring

lemma halasz_three_degree_rates {N α lam d η : ℝ} (hN : 1≤ N)
    (h₁ : η≤α*d) (h₂ : η≤ d-lam) (h₃ : η≤ lam-d+2*α*d) :
    N^(-α*d)≤ N^(-η) ∧ N^(lam-d)≤ N^(-η) ∧
      N^(d-2*α*d-lam)≤ N^(-η) := by
  refine ⟨Real.rpow_le_rpow_of_exponent_le hN (by linarith),
    Real.rpow_le_rpow_of_exponent_le hN (by linarith),
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszScaleRatios
namespace OAI

/-! Elementary scale ratios in the logarithmic coefficient weights. -/
namespace TwoPointCorrelations

lemma halasz_inverse_short_power {M : ℕ} (hM : 1≤ M)
    {N α : ℝ} (hN : 0< N) (hscale : N^α≤2*(M:ℝ)) (d : ℕ) :
    1/(M:ℝ)^d≤(2:ℝ)^d*N^(-α*(d:ℝ)) := by
  have hM0 : 0<(M:ℝ) := by exact_mod_cast (show 0< M by omega)
  have hp : N^(α*(d:ℝ))≤(2:ℝ)^d*(M:ℝ)^d := by
    calc
      _ = (N^α)^d := by rw [← Real.rpow_natCast,← Real.rpow_mul hN.le]
      _ ≤ (2*(M:ℝ))^d := pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hscale d
      _ = _ := mul_pow _ _ _
  calc
    _ ≤ (2:ℝ)^d/N^(α*(d:ℝ)) := by
      apply (div_le_div_iff₀ (pow_pos hM0 d) (Real.rpow_pos_of_pos hN _)).mpr
      simpa only [one_mul] using hp
    _ = _ := by rw [show -α*(d:ℝ)= -(α*(d:ℝ)) by ring,Real.rpow_neg hN.le]; ring

lemma halasz_height_over_long_power {t z N lam : ℝ} (hN : 0< N)
    (hz : N≤ z) (ht : |t|=N^lam) (d : ℕ) :
    |t|/z^d≤ N^(lam-(d:ℝ)) := by
  have hz0 : 0< z := hN.trans_le hz
  calc
    _ ≤ |t|/N^d := div_le_div_of_nonneg_left (abs_nonneg t)
      (pow_pos hN d) (pow_le_pow_left₀ hN.le hz d)
    _ = _ := by rw [ht,Real.rpow_sub hN,Real.rpow_natCast]

lemma halasz_long_over_short_height {M : ℕ} (hM : 1≤ M)
    {t z N α lam : ℝ} (hN : 0< N) (hz : 0≤ z) (hzhi : z≤2*N)
    (ht : |t|=N^lam) (hscale : N^α≤2*(M:ℝ)) (d : ℕ) :
    z^d/(((M:ℝ)^d)^2*|t|)≤(8:ℝ)^d*N^((d:ℝ)-2*α*(d:ℝ)-lam) := by
  have hinv := halasz_inverse_short_power hM hN hscale d
  have hsq := pow_le_pow_left₀ (by positivity : 0≤1/(M:ℝ)^d) hinv 2
  have hzpow := pow_le_pow_left₀ hz hzhi d
  have hmult := mul_le_mul hzpow hsq (by positivity) (by positivity)
  have hmult' := mul_le_mul_of_nonneg_right hmult
    (Real.rpow_nonneg hN.le (-lam))
  calc
    _ = (z^d*(1/(M:ℝ)^d)^2)*N^(-lam) := by
      rw [ht,Real.rpow_neg hN.le]
      ring
    _ ≤ ((2*N)^d*((2:ℝ)^d*N^(-α*(d:ℝ)))^2)*N^(-lam) := hmult'
    _ = (8:ℝ)^d*N^((d:ℝ)-2*α*(d:ℝ)-lam) := by
      rw [mul_pow,mul_pow,← pow_mul,← Real.rpow_natCast N d,
        ← Real.rpow_natCast (N^(-α*(d:ℝ))) 2,← Real.rpow_mul hN.le]
      norm_num only [Nat.cast_ofNat]
      have he : (2:ℝ)^d*(2:ℝ)^(d*2)=(8:ℝ)^d := by
        rw [show d*2=2*d by omega,pow_mul,← mul_pow]
        norm_num
      calc
        _ = ((2:ℝ)^d*(2:ℝ)^(d*2))*(N^(d:ℝ)*N^((-α*(d:ℝ))*(2:ℝ))*N^(-lam)) := by ring
        _ = _ := by rw [he,← Real.rpow_add hN,← Real.rpow_add hN]; congr 2; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogWeightCost
namespace OAI

/-! A single explicit coefficient cost for every active Taylor degree. -/
namespace TwoPointCorrelations


lemma halasz_log_weight_cost_pos (k r : ℕ) : 0< halaszLogWeightCost k r := by
  unfold halaszLogWeightCost
  positivity

lemma halasz_log_degree_cost {k r : ℕ} (hr : 1≤ r) (j : Fin k) :
    (5/2:ℝ)*(2:ℝ)^(j.val+1)+(r:ℝ)/(Real.pi*(j.val+1))+
      Real.pi*(j.val+1)/(r:ℝ)*(8:ℝ)^(j.val+1) ≤ halaszLogWeightCost k r := by
  have hrR : 1≤(r:ℝ) := by exact_mod_cast hr
  have hd : 1≤(j.val:ℝ)+1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j.val)
  have hdk : (j.val:ℝ)+1≤ k := by exact_mod_cast (show j.val+1≤ k by omega)
  have hpi : 1≤ Real.pi*((j.val:ℝ)+1) := by nlinarith [Real.pi_gt_three]
  have hdiv : (r:ℝ)/(Real.pi*(j.val+1))≤ r := div_le_self (by positivity) hpi
  have hdiv' : Real.pi*(j.val+1)/(r:ℝ)≤4*k := by
    apply (div_le_iff₀ (by positivity : 0<(r:ℝ))).mpr
    nlinarith [Real.pi_lt_four,show (0:ℝ)≤ k by positivity]
  have hdN : j.val+1≤ k := by omega
  have hpow8 : (8:ℝ)^(j.val+1)≤(8:ℝ)^k := pow_le_pow_right₀ (by norm_num) hdN
  have hpow2 : (2:ℝ)^(j.val+1)≤(8:ℝ)^k :=
    (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (by norm_num : (2:ℝ)≤8) _).trans hpow8
  have hterm := mul_le_mul hdiv' hpow8 (by positivity) (by positivity : (0:ℝ)≤4*k)
  have hP : 1≤(8:ℝ)^k := one_le_pow₀ (by norm_num)
  have hrP : (r:ℝ)≤ r*(8:ℝ)^k := le_mul_of_one_le_right (by positivity) hP
  unfold halaszLogWeightCost
  rw [show (8:ℝ)^(k+2)=64*(8:ℝ)^k by rw [pow_add]; norm_num only [pow_two]; ring]
  have hkP : 0≤(k:ℝ)*(8:ℝ)^k := by positivity
  have hrP0 : 0≤(r:ℝ)*(8:ℝ)^k := by positivity
  nlinarith only [hpow2,hdiv,hterm,hP,hrP,hkP,hrP0]

lemma halasz_log_coordinate_saving {k r M : ℕ} (hr : 1≤ r) (hM : 1≤ M)
    {t z N α lam η : ℝ} (hN : 1≤ N) (hz : N≤ z) (hzhi : z≤2*N)
    (ht : |t|=N^lam) (hscale : N^α≤2*(M:ℝ)) (j : Fin k)
    (h₁ : η≤α*(j.val+1)) (h₂ : η≤(j.val+1)-lam)
    (h₃ : η≤ lam-(j.val+1)+2*α*(j.val+1)) :
    halaszNormalizedWeight r M (halaszLogCoefficient t z) j ≤
      halaszLogWeightCost k r*N^(-η) := by
  have hN0 : 0< N := by linarith
  have hz0 : 0< z := hN0.trans_le hz
  have ht0 : t≠0 := by
    intro ht0
    have hp := Real.rpow_pos_of_pos hN0 lam
    rw [ht0,abs_zero] at ht
    linarith
  have hrate := halasz_three_degree_rates (d := ((j.val+1:ℕ):ℝ)) hN
    (by simpa only [Nat.cast_add,Nat.cast_one] using h₁)
    (by simpa only [Nat.cast_add,Nat.cast_one] using h₂)
    (by simpa only [Nat.cast_add,Nat.cast_one] using h₃)
  have ha := (halasz_inverse_short_power hM hN0 hscale (j.val+1)).trans
    (mul_le_mul_of_nonneg_left hrate.1 (by positivity : (0:ℝ)≤2^(j.val+1)))
  have hb := (halasz_height_over_long_power hN0 hz ht (j.val+1)).trans hrate.2.1
  have he := (halasz_long_over_short_height hM hN0 hz0.le hzhi ht hscale (j.val+1)).trans
    (mul_le_mul_of_nonneg_left hrate.2.2 (by positivity : (0:ℝ)≤8^(j.val+1)))
  have hh := halasz_log_weight_bound (B := 1) hr hM ht0 hz0 j ha
    (by simpa only [one_mul] using hb) he
  apply hh.trans
  exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using halasz_log_degree_cost hr j)
    (Real.rpow_nonneg hN0.le _)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSelectedDoubleMoment
namespace OAI

/-! The sole selected moment needed for logarithmic exponential sums. -/
namespace TwoPointCorrelations

open _root_.Finset


lemma halasz_selected_moment_pos {k : ℕ} (hk : 2≤ k) : 1≤ halaszSelectedMoment k := by
  unfold halaszSelectedMoment
  nlinarith

theorem halasz_selected_double_moment : ∃ R₀ : ℕ, ∀ k : ℕ, 2≤ k →
    ∀ M : ℕ, 1≤ M → ∀ γ : Fin k → ℝ, (∀ j,γ j≠0) →
    ‖∑ b : Fin M,halaszVinogradovPolynomial k M
      (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^
        (2*halaszSelectedMoment k*halaszSelectedMoment k) ≤
      (32*(halaszSelectedMoment k:ℝ))^k*(R₀+k+32:ℝ)^(512*k^4)*
        (M:ℝ)^(4*(halaszSelectedMoment k:ℝ)^2+(k:ℝ)^2/1024)*
          ∏ j,halaszNormalizedWeight (halaszSelectedMoment k) M γ j := by
  obtain ⟨R₀,hR⟩ := halasz_quantitative_mean_value
  refine ⟨R₀,?_⟩
  intro k hk M hM γ hγ
  have hJ := hR k hk M hM
  rw [← halasz_coordinate_total_degree (by omega : 0< k)] at hJ
  have h := halasz_normalized_double_moment (halasz_selected_moment_pos hk) hM γ hγ
    (C := (R₀+k+32:ℝ)^(256*k^4)) (ε := (k:ℝ)^2/2048) hJ
  convert (preTransparency := .instances) h using 1
  have he : 2*((k:ℝ)^2/2048)=(k:ℝ)^2/1024 := by ring
  rw [he,← pow_mul,show (256*k^4)*2=512*k^4 by omega]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszMomentConstant
namespace OAI

/-! The apparently large complete-system constants become a fixed sixth
power after taking the selected double-moment root. -/
namespace TwoPointCorrelations

lemma halasz_moment_constant_nat {k : ℕ} (hk : 2≤ k) (R₀ : ℕ) :
    (32*halaszSelectedMoment k)^k*(R₀+k+32)^(512*k^4)*
      (8^(k+2)*(halaszSelectedMoment k+k+1))^k ≤
    (R₀+k+32)^(6*(2*halaszSelectedMoment k*halaszSelectedMoment k)) := by
  let R := R₀+k+32
  let r := halaszSelectedMoment k
  have hRk : k≤ R := by dsimp [R]; omega
  have hR32 : 32≤ R := by dsimp [R]; omega
  have hR1 : 1≤ R := by omega
  have hkk : k≤ k^2 := by nlinarith
  have hr : r≤11*k^2 := by dsimp [r,halaszSelectedMoment]; nlinarith only [hkk]
  have hrlo : 10*k^2≤ r := by dsimp [r,halaszSelectedMoment]; nlinarith
  have hR2 : k^2≤ R^2 := Nat.pow_le_pow_left hRk 2
  have h32 : 1024≤ R^2 := by simpa using Nat.pow_le_pow_left hR32 2
  have hbase : 32*r≤ R^4 := by
    calc
      _ ≤ 352*k^2 := by nlinarith only [hr]
      _ ≤ 1024*k^2 := by omega
      _ ≤ R^2*k^2 := Nat.mul_le_mul_right _ h32
      _ ≤ R^2*R^2 := Nat.mul_le_mul_left _ hR2
      _ = _ := by ring
  have hshort : r+k+1≤ R^3 := by
    have hkpos : 1≤ k^2 := by nlinarith
    calc
      _ ≤ 13*k^2 := by nlinarith only [hr,hkk,hkpos]
      _ ≤ 32*k^2 := by omega
      _ ≤ R*k^2 := Nat.mul_le_mul_right _ hR32
      _ ≤ R*R^2 := Nat.mul_le_mul_left _ hR2
      _ = _ := by ring
  have hcost : 8^(k+2)*(r+k+1)≤ R^(k+5) := by
    calc
      _ ≤ R^(k+2)*R^3 := Nat.mul_le_mul
        (Nat.pow_le_pow_left (by omega : 8≤ R) _) hshort
      _ = _ := by rw [← pow_add]
  have hk4 : k^2≤ k^4 := by
    have hh := Nat.pow_le_pow_right (by omega : 1≤ k) (by norm_num : 2≤4)
    exact hh
  have hr2 : 100*k^4≤ r^2 := by
    have hh := Nat.pow_le_pow_left hrlo 2
    nlinarith only [hh]
  have he : 4*k+512*k^4+(k+5)*k≤6*(2*r*r) := by
    nlinarith only [hkk,hk4,hr2]
  calc
    _ ≤ (R^4)^k*R^(512*k^4)*(R^(k+5))^k :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbase k))
        (Nat.pow_le_pow_left hcost k)
    _ = R^(4*k+512*k^4+(k+5)*k) := by rw [← pow_mul,← pow_mul,← pow_add,← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right hR1 he

lemma halasz_moment_constant_root {k : ℕ} (hk : 2≤ k) (R₀ : ℕ) :
    ((32*(halaszSelectedMoment k:ℝ))^k*(R₀+k+32:ℝ)^(512*k^4)*
      (halaszLogWeightCost k (halaszSelectedMoment k))^k)^
        (((2*halaszSelectedMoment k*halaszSelectedMoment k:ℕ):ℝ)⁻¹) ≤
      (R₀+k+32:ℝ)^6 := by
  have hp : 0<2*halaszSelectedMoment k*halaszSelectedMoment k := by
    have hr := halasz_selected_moment_pos hk
    positivity
  have hB : (32*(halaszSelectedMoment k:ℝ))^k*(R₀+k+32:ℝ)^(512*k^4)*
      (halaszLogWeightCost k (halaszSelectedMoment k))^k ≤
      (R₀+k+32:ℝ)^(6*(2*halaszSelectedMoment k*halaszSelectedMoment k)) := by
    dsimp only [halaszLogWeightCost]
    exact_mod_cast halasz_moment_constant_nat hk R₀
  apply (Real.rpow_inv_le_iff_of_pos (by dsimp only [halaszLogWeightCost]; positivity) (by positivity)
    (by exact_mod_cast hp)).mpr
  simpa only [Real.rpow_natCast,← pow_mul] using hB

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszMomentRoot
namespace OAI

/-! Extracting the normalized exponential-sum saving from its even moment. -/
namespace TwoPointCorrelations

lemma halasz_moment_root {x B M N d : ℝ} {p : ℕ}
    (hp : 0< p) (hx : 0≤ x) (hB : 0≤ B) (hM : 0< M) (hN : 0< N)
    (h : x^p≤ B*M^(2*p)*N^d) :
    x/M^2≤ B^((p:ℝ)⁻¹)*N^(d/(p:ℝ)) := by
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp
  have hden : 0<(M^2)^p := pow_pos (pow_pos hM 2) p
  have hn : (x/M^2)^p≤ B*N^d := by
    rw [div_pow]
    apply (div_le_iff₀ hden).mpr
    convert (preTransparency := .instances) h using 1
    rw [← pow_mul]
    ring
  have hroot : x/M^2≤(B*N^d)^((p:ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos (by positivity : 0≤ x/M^2)
      (mul_nonneg hB (Real.rpow_nonneg hN.le _)) hpR).mpr
    simpa only [Real.rpow_natCast] using hn
  apply hroot.trans_eq
  rw [Real.mul_rpow hB (Real.rpow_nonneg hN.le _),← Real.rpow_mul hN.le]
  rw [div_eq_mul_inv]

lemma halasz_moment_transfer {x A D M N ε σ d : ℝ} {p : ℕ}
    (hp : 0< p) (hx : 0≤ x) (hA : 0≤ A) (hD : 0≤ D)
    (hM : 1≤ M) (hMN : M≤ N) (hε : 0≤ε) (hδ : ε-σ≤ d)
    (h : x^p≤ A*M^(((2*p:ℕ):ℝ)+ε)*D*N^(-σ)) :
    x/M^2≤(A*D)^((p:ℝ)⁻¹)*N^(d/(p:ℝ)) := by
  have hM0 : 0< M := by linarith
  have hN : 1≤ N := hM.trans hMN
  have hN0 : 0< N := hM0.trans_le hMN
  apply halasz_moment_root hp hx (mul_nonneg hA hD) hM0 hN0
  apply h.trans
  have hscale : M^ε*N^(-σ)≤ N^d := by
    calc
      _ ≤ N^ε*N^(-σ) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hM0.le hMN hε) (Real.rpow_nonneg hN0.le _)
      _ = N^(ε-σ) := by rw [← Real.rpow_add hN0]; rfl
      _ ≤ N^d := Real.rpow_le_rpow_of_exponent_le hN hδ
  rw [Real.rpow_add hM0,Real.rpow_natCast]
  calc
    _ = (A*D*M^(2*p))*(M^ε*N^(-σ)) := by ring
    _ ≤ (A*D*M^(2*p))*N^d :=
      mul_le_mul_of_nonneg_left hscale (by positivity)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSelectedWeights
namespace OAI

/-! Only the selected middle degrees need nontrivial cancellation. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_log_weight_cost_trivial (k r : ℕ) : 2*(r:ℝ)+1≤ halaszLogWeightCost k r := by
  have hp : (8:ℝ)^2≤(8:ℝ)^(k+2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hmul := mul_le_mul_of_nonneg_right hp (show (0:ℝ)≤ r+k+1 by positivity)
  unfold halaszLogWeightCost
  norm_num at hmul
  nlinarith [show (0:ℝ)≤ k by positivity]

lemma halasz_selected_weight_product {k r M : ℕ} (γ : Fin k → ℝ)
    (S : Finset (Fin k)) {C N η : ℝ} (hN : 0< N)
    (htriv : ∀ j,halaszNormalizedWeight r M γ j≤ C)
    (hsel : ∀ j∈S,halaszNormalizedWeight r M γ j≤ C*N^(-η)) :
    (∏ j : Fin k,halaszNormalizedWeight r M γ j)≤ C^k*N^(-(S.card:ℝ)*η) := by
  let w : Fin k → ℝ := fun j => if j∈S then η else 0
  have hw : ∀ j,halaszNormalizedWeight r M γ j≤ C*N^(-w j) := by
    intro j
    by_cases hj : j∈S
    · simpa only [w,if_pos hj] using hsel j hj
    · simpa only [w,if_neg hj,neg_zero,Real.rpow_zero,mul_one] using htriv j
  have hs : (∑ j,w j)=(S.card:ℝ)*η := by
    simp [w]
  calc
    _ ≤ ∏ j,C*N^(-w j) :=
      Finset.prod_le_prod (fun j _ => halasz_normalized_weight_nonneg γ j) (fun j _ => hw j)
    _ = _ := by
      rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,
        ← Real.rpow_sum_of_pos hN,sum_neg_distrib,hs]
      congr 2
      ring

theorem halasz_log_selected_weight_product {k r M : ℕ} (hr : 1≤ r) (hM : 1≤ M)
    {t z N α lam η : ℝ} (hN : 1≤ N) (hz : N≤ z) (hzhi : z≤2*N)
    (ht : |t|=N^lam) (hscale : N^α≤2*(M:ℝ)) (S : Finset (Fin k))
    (h₁ : ∀ j∈S,η≤α*(j.val+1)) (h₂ : ∀ j∈S,η≤(j.val+1)-lam)
    (h₃ : ∀ j∈S,η≤ lam-(j.val+1)+2*α*(j.val+1)) :
    (∏ j : Fin k,halaszNormalizedWeight r M (halaszLogCoefficient t z) j)≤
      (halaszLogWeightCost k r)^k*N^(-(S.card:ℝ)*η) := by
  apply halasz_selected_weight_product _ S (by linarith : 0< N)
  · intro j
    exact (min_le_left _ _).trans (halasz_log_weight_cost_trivial k r)
  · intro j hj
    exact halasz_log_coordinate_saving hr hM hN hz hzhi ht hscale j
      (h₁ j hj) (h₂ j hj) (h₃ j hj)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLargeDegrees
namespace OAI

/-! The block of middle Taylor degrees supplying a quadratic total saving. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_large_degree_map_injective {m : ℕ} (hm : 1≤ m) :
    Function.Injective (halaszLargeDegreeMap m hm) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  dsimp only [halaszLargeDegreeMap] at hv
  omega


lemma halasz_large_degrees_card {m : ℕ} (hm : 1≤ m) :
    (halaszLargeDegrees m hm).card=2*m+1 := by
  rw [halaszLargeDegrees,card_image_of_injective _ (halasz_large_degree_map_injective hm)]
  simp

lemma halasz_large_degrees_range {m : ℕ} (hm : 1≤ m) {j : Fin (12*m)}
    (hj : j∈halaszLargeDegrees m hm) : 8*m≤ j.val+1 ∧ j.val+1≤10*m := by
  obtain ⟨i,_,rfl⟩ := mem_image.mp hj
  dsimp only [halaszLargeDegreeMap]
  have hi := i.isLt
  omega

theorem halasz_large_degree_weight_product {m r M : ℕ} (hm : 8≤ m)
    (hr : 1≤ r) (hM : 1≤ M) {t z N lam : ℝ} (hN : 1≤ N)
    (hz : N≤ z) (hzhi : z≤2*N) (ht : |t|=N^lam)
    (hscale : N^(1/4:ℝ)≤2*(M:ℝ))
    (hlo : 6*(m:ℝ)-6≤ lam) (hhi : lam≤6*m) :
    (∏ j : Fin (12*m),halaszNormalizedWeight r M (halaszLogCoefficient t z) j)≤
      (halaszLogWeightCost (12*m) r)^(12*m)*N^(-((2*m+1:ℕ):ℝ)*((m:ℝ)-6)) := by
  have hm1 : 1≤ m := by omega
  have hdeg (j : Fin (12*m)) (hj : j∈halaszLargeDegrees m hm1) :
      (m:ℝ)-6≤ min (((j.val:ℝ)+1)/4)
        (min (((j.val:ℝ)+1)-lam) (lam-((j.val:ℝ)+1)/2)) := by
    have hj' := halasz_large_degrees_range hm1 hj
    apply halasz_large_degree_saving (by exact_mod_cast hm) hlo hhi
    · exact_mod_cast hj'.1
    · exact_mod_cast hj'.2
  have hh := halasz_log_selected_weight_product hr hM hN hz hzhi ht hscale
    (halaszLargeDegrees m hm1)
    (η := (m:ℝ)-6)
    (fun j hj => by have hd := (le_min_iff.mp (hdeg j hj)).1; linarith)
    (fun j hj => (le_min_iff.mp (le_min_iff.mp (hdeg j hj)).2).1)
    (fun j hj => by have hd := (le_min_iff.mp (le_min_iff.mp (hdeg j hj)).2).2; linarith)
  simpa only [halasz_large_degrees_card] using hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDegreeSelection
namespace OAI

/-! Quantitative degree choices as a function of log|t|/log N. -/
namespace TwoPointCorrelations


lemma halasz_large_root_saving {m : ℕ} (hm : 8≤ m) {lam : ℝ}
    (hlo : 6*(m:ℝ)-6≤ lam) :
    1/((10^8:ℝ)*lam^2)≤
      (m:ℝ)^2/(4*((2*halaszSelectedMoment (12*m)*halaszSelectedMoment (12*m):ℕ):ℝ)) := by
  have hmR : (8:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : 0<(m:ℝ) := by linarith
  have hlam : 5*(m:ℝ)≤ lam := by linarith
  have hlam0 : 0< lam := by linarith
  have hr : (halaszSelectedMoment (12*m):ℝ)≤1584*(m:ℝ)^2 := by
    simp only [halaszSelectedMoment,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    nlinarith
  have hr0 : 0<(halaszSelectedMoment (12*m):ℝ) := by
    exact_mod_cast (show 0< halaszSelectedMoment (12*m) from
      lt_of_lt_of_le Nat.zero_lt_one (halasz_selected_moment_pos (by omega)))
  have hp : 0<((2*halaszSelectedMoment (12*m)*halaszSelectedMoment (12*m):ℕ):ℝ) := by
    push_cast
    positivity
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<10^8*lam^2) (by positivity :
    (0:ℝ)<4*((2*halaszSelectedMoment (12*m)*halaszSelectedMoment (12*m):ℕ):ℝ))).mpr
  have hr2 : (halaszSelectedMoment (12*m):ℝ)^2≤1584^2*(m:ℝ)^4 := by
    calc
      _ ≤ (1584*(m:ℝ)^2)^2 := pow_le_pow_left₀ hr0.le hr 2
      _ = _ := by ring
  have hlam2 : 25*(m:ℝ)^2≤ lam^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlam2 (sq_nonneg (m:ℝ))
  push_cast
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLargeLogPolynomial
namespace OAI

/-! The large-height logarithmic Taylor polynomial gains a quadratic
saving in the degree before taking its selected moment root. -/
namespace TwoPointCorrelations

open _root_.Finset

theorem halasz_large_log_polynomial : ∃ R₀ : ℕ, ∀ m : ℕ, 8≤ m →
    ∀ M : ℕ, 1≤ M → ∀ t z N lam : ℝ, (M:ℝ)≤ N → N≤ z → z≤2*N →
    |t|=N^lam → N^(1/4:ℝ)≤2*(M:ℝ) →
    6*(m:ℝ)-6≤ lam → lam≤6*m →
    let k := 12*m
    let r := halaszSelectedMoment k
    let p := 2*r*r
    ‖∑ b : Fin M,halaszVinogradovPolynomial k M
      (halaszScaledFrequency (halaszLogCoefficient t z)
        (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(M:ℝ)^2 ≤
      ((32*(r:ℝ))^k*(R₀+k+32:ℝ)^(512*k^4)*(halaszLogWeightCost k r)^k)^((p:ℝ)⁻¹)*
        N^(-(m:ℝ)^2/(4*(p:ℝ))) := by
  obtain ⟨R₀,hR⟩ := halasz_selected_double_moment
  refine ⟨R₀,?_⟩
  intro m hm M hM t z N lam hMN hz hzhi ht hscale hlo hhi
  dsimp only
  let k := 12*m
  let r := halaszSelectedMoment k
  let p := 2*r*r
  have hk : 2≤ k := by dsimp only [k]; omega
  have hr : 1≤ r := halasz_selected_moment_pos hk
  have hp : 0< p := by dsimp only [p]; positivity
  have hMR : 1≤(M:ℝ) := by exact_mod_cast hM
  have hN : 1≤ N := hMR.trans hMN
  have hN0 : 0< N := by linarith
  have ht0 : t≠0 := by
    intro ht0
    have hh := Real.rpow_pos_of_pos hN0 lam
    rw [ht0,abs_zero] at ht
    linarith
  have hz0 : z≠0 := by linarith
  have hbase := hR k hk M hM (halaszLogCoefficient t z)
    (halasz_log_coefficient_ne_zero ht0 hz0)
  have hweights := halasz_large_degree_weight_product hm hr hM hN hz hzhi ht hscale hlo hhi
  have hbound := hbase.trans (mul_le_mul_of_nonneg_left hweights (by positivity))
  let A := (32*(r:ℝ))^k*(R₀+k+32:ℝ)^(512*k^4)
  let D := (halaszLogWeightCost k r)^k
  have hexp : 4*(r:ℝ)^2=((2*p:ℕ):ℝ) := by
    dsimp only [p]
    push_cast
    ring
  have hbound' :
      ‖∑ b : Fin M,halaszVinogradovPolynomial k M
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^p ≤
      A*(M:ℝ)^(((2*p:ℕ):ℝ)+(k:ℝ)^2/1024)*D*
        N^(-(((2*m+1:ℕ):ℝ)*((m:ℝ)-6))) := by
    convert (preTransparency := .instances) hbound using 1
    dsimp only [A,D,k,r]
    rw [hexp]
    ring_nf
  have hmargin : (k:ℝ)^2/1024-((2*m+1:ℕ):ℝ)*((m:ℝ)-6)≤ -(m:ℝ)^2/4 := by
    have hh := halasz_large_degree_margin (by exact_mod_cast hm : (8:ℝ)≤ m)
    dsimp only [k]
    push_cast
    nlinarith only [hh]
  have hh := halasz_moment_transfer hp (by positivity)
    (show 0≤ A by dsimp only [A]; positivity)
    (show 0≤ D by dsimp only [D]; exact pow_nonneg (halasz_log_weight_cost_pos _ _).le _)
    hMR hMN (by positivity : (0:ℝ)≤(k:ℝ)^2/1024) hmargin hbound'
  convert (preTransparency := .instances) hh using 1
  congr 1
  congr 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogPolynomialSaving
namespace OAI

/-! Polynomial phase cancellation after removing the selected-moment
constant. The remaining loss is a fixed sixth power. -/
namespace TwoPointCorrelations

open _root_.Finset

theorem halasz_large_log_polynomial_saving : ∃ R₀ : ℕ, ∀ m : ℕ, 8≤ m →
    ∀ M : ℕ, 1≤ M → ∀ t z N lam : ℝ, (M:ℝ)≤ N → N≤ z → z≤2*N →
    |t|=N^lam → N^(1/4:ℝ)≤2*(M:ℝ) → 6*(m:ℝ)-6≤ lam → lam≤6*m →
    ‖∑ b : Fin M,halaszVinogradovPolynomial (12*m) M
      (halaszScaledFrequency (halaszLogCoefficient t z)
        (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(M:ℝ)^2 ≤
      (R₀+12*m+32:ℝ)^6*N^(-1/((10^8:ℝ)*lam^2)) := by
  obtain ⟨R₀,hR⟩ := halasz_large_log_polynomial
  refine ⟨R₀,?_⟩
  intro m hm M hM t z N lam hMN hz hzhi ht hscale hlo hhi
  have h := hR m hm M hM t z N lam hMN hz hzhi ht hscale hlo hhi
  have hC := halasz_moment_constant_root (k := 12*m) (by omega) R₀
  push_cast at hC
  have hN : 1≤ N := (show (1:ℝ)≤ M by exact_mod_cast hM).trans hMN
  have hb := neg_le_neg (halasz_large_root_saving hm hlo)
  have he : -(m:ℝ)^2/(4*((2*halaszSelectedMoment (12*m)*halaszSelectedMoment (12*m):ℕ):ℝ)) ≤
      -1/((10^8:ℝ)*lam^2) := by simpa only [neg_div] using hb
  push_cast at h he
  exact h.trans (mul_le_mul hC (Real.rpow_le_rpow_of_exponent_le hN he)
    (Real.rpow_nonneg (by linarith) _) (by positivity))


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_large_log_polynomial_saving := @OAI.TwoPointCorrelations.halasz_large_log_polynomial_saving
