-- Prove2me | solution 1 for OAI.Erdos3.permanent_gcd_mean_sublevel_all_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:50:43.377953+00:00
-- url     : https://prove2.me/submissions/41026c7d-3065-4797-a2cc-486f7e12c6d8

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B089
import Definitions.Def_OAIE3v2B112

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularMultilinearSublevelFiber
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem zmod_affine_zero_card_le_gcd (N : ℕ) [NeZero N] (c d : ZMod N) :
    (Finset.univ.filter fun x : ZMod N => c * x + d = 0).card ≤ Nat.gcd c.val N := by
  by_cases h : ∃ y : ZMod N, c * y + d = 0
  · obtain ⟨y, hy⟩ := h
    let f : {x : ZMod N // c * x + d = 0} →
        (nsmulAddMonoidHom c.val : ZMod N →+ ZMod N).ker := fun x =>
      ⟨x.val - y, by
        change c.val • (x.val - y) = 0
        rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_sub]
        have hx := x.property
        linear_combination hx - hy⟩
    have hf : Function.Injective f := by
      intro x z hxz
      apply Subtype.ext
      have he := congrArg Subtype.val hxz
      change x.val - y = z.val - y at he
      exact sub_left_injective he
    have hc := Nat.card_le_card_of_injective f hf
    rw [IsAddCyclic.card_nsmulAddMonoidHom_ker] at hc
    simp only [Nat.card_eq_fintype_card, ZMod.card, Nat.gcd_comm N c.val] at hc
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hc
  · have he : (Finset.univ.filter fun x : ZMod N => c * x + d = 0) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ⟨x, (Finset.mem_filter.mp hx).2⟩
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

theorem zmod_mul_zero_card_eq_gcd (N : ℕ) [NeZero N] (c : ZMod N) :
    (Finset.univ.filter fun x : ZMod N => c * x = 0).card = Nat.gcd c.val N := by
  have hk := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod N) c.val
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, nsmul_eq_mul,
    ZMod.card, Nat.gcd_comm] using hk

theorem zmod_mul_zero_expect_eq_gcd (N : ℕ) [NeZero N] (c : ZMod N) :
    (𝔼 x : ZMod N, if c * x = 0 then (1 : ℝ) else 0) =
      (Nat.gcd c.val N : ℝ) / N := by
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  have hsum : (∑ x : ZMod N, if c * x = 0 then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun x : ZMod N => c * x = 0).card : ℝ) := by simp
  rw [hsum, zmod_mul_zero_card_eq_gcd]

theorem zmod_gcd_expect_eq_mul_zero_expect {Ω : Type*} [Fintype Ω]
    (N : ℕ) [NeZero N] (c : Ω → ZMod N) :
    (𝔼 y : Ω, (Nat.gcd (c y).val N : ℝ) / N) =
      𝔼 y : Ω, 𝔼 x : ZMod N, if c y * x = 0 then (1 : ℝ) else 0 := by
  apply Finset.expect_congr rfl
  intro y _
  exact (zmod_mul_zero_expect_eq_gcd N (c y)).symm

theorem zmod_prime_power_affine_zero_card_le {p a b : ℕ} [NeZero p] (hp : p.Prime)
    (c d : ZMod (p ^ a)) (hc : ¬p ^ b ∣ c.val) :
    (Finset.univ.filter fun x : ZMod (p ^ a) => c * x + d = 0).card ≤ p ^ (b - 1) := by
  refine (zmod_affine_zero_card_le_gcd (p ^ a) c d).trans ?_
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right c.val (p ^ a))
  have hjb : j < b := by
    by_contra hn
    have hbj : b ≤ j := by omega
    exact hc ((pow_dvd_pow p hbj).trans (hj ▸ Nat.gcd_dvd_left c.val (p ^ a)))
  rw [hj]
  exact Nat.pow_le_pow_right hp.pos (by omega)

theorem zmod_prime_power_affine_zero_expect_le {p a b : ℕ} [NeZero p]
    (hp : p.Prime) (hba : b ≤ a) (c d : ZMod (p ^ a))
    (hc : ZMod.castHom (pow_dvd_pow p hba) (ZMod (p ^ b)) c ≠ 0) :
    (𝔼 x : ZMod (p ^ a), if c * x + d = 0 then (1 : ℝ) else 0) ≤
      (p : ℝ) ^ (b - 1) / (p : ℝ) ^ a := by
  have hc' : ¬p ^ b ∣ c.val := by
    intro hd
    apply hc
    rw [← ZMod.natCast_zmod_val c, map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hcard := zmod_prime_power_affine_zero_card_le hp c d hc'
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  have hsum : (∑ x : ZMod (p ^ a), if c * x + d = 0 then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun x : ZMod (p ^ a) => c * x + d = 0).card : ℝ) := by
    simp
  rw [hsum, Nat.cast_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hcard

theorem zmod_prime_power_affine_zero_expect_le_rpow {p a b : ℕ} [NeZero p]
    (hp : p.Prime) (hb : 1 ≤ b) (hba : b ≤ a) (c d : ZMod (p ^ a))
    (hc : ZMod.castHom (pow_dvd_pow p hba) (ZMod (p ^ b)) c ≠ 0) :
    (𝔼 x : ZMod (p ^ a), if c * x + d = 0 then (1 : ℝ) else 0) ≤
      (p : ℝ) ^ ((b : ℝ) - 1 - a) := by
  have hr : (p : ℝ) ^ ((b : ℝ) - 1 - a) =
      (p : ℝ) ^ (b - 1) / (p : ℝ) ^ a := by
    have he : (b : ℝ) - 1 = ((b - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hb, Nat.cast_one]
    rw [Real.rpow_sub (by exact_mod_cast hp.pos), he,
      Real.rpow_natCast, Real.rpow_natCast]
  rw [hr]
  exact zmod_prime_power_affine_zero_expect_le hp hba c d hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularMultilinearSublevelNumerics
namespace OAI

section

namespace Erdos3

theorem modularSublevel_half_depth {a : ℕ} (ha : 0 < a) :
    0 < (a + 1) / 2 ∧ (a + 1) / 2 ≤ a ∧
      (a : ℝ) / 2 ≤ ((a + 1) / 2 : ℕ) ∧
      (((a + 1) / 2 : ℕ) : ℝ) - 1 - a ≤ -(a : ℝ) / 2 := by
  have h₁ : a ≤ 2 * ((a + 1) / 2) := by omega
  have h₂ : 2 * ((a + 1) / 2) ≤ a + 1 := by omega
  refine ⟨by omega, by omega, ?_, ?_⟩
  · have : (a : ℝ) ≤ 2 * (((a + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h₁
    linarith
  · have : 2 * (((a + 1) / 2 : ℕ) : ℝ) ≤ (a : ℝ) + 1 := by exact_mod_cast h₂
    linarith

theorem modularSublevel_fiber_exponent {p : ℝ} (hp : 1 ≤ p) {a : ℕ} (ha : 0 < a) :
    p ^ ((((a + 1) / 2 : ℕ) : ℝ) - 1 - a) ≤ p ^ (-(a : ℝ) / 2) :=
  Real.rpow_le_rpow_of_exponent_le hp (modularSublevel_half_depth ha).2.2.2

theorem modularSublevel_induction_bound {p : ℝ} (hp : 1 ≤ p)
    {a r : ℕ} (ha : 0 < a) (hr : 0 < r) :
    (r : ℝ) * p ^ (-(((a + 1) / 2 : ℕ) : ℝ) / (2 : ℝ) ^ (r - 1)) +
        p ^ (-(a : ℝ) / 2) ≤
      ((r + 1 : ℕ) : ℝ) * p ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  have hpow : (2 : ℝ) ^ r = 2 * (2 : ℝ) ^ (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [pow_succ, mul_comm]
  have hpos : 0 < (2 : ℝ) ^ (r - 1) := by positivity
  have hdepth := (modularSublevel_half_depth ha).2.2.1
  have hexp : -(((a + 1) / 2 : ℕ) : ℝ) / (2 : ℝ) ^ (r - 1) ≤
      -(a : ℝ) / (2 : ℝ) ^ r := by
    rw [hpow]
    apply (div_le_div_iff₀ hpos (by positivity)).2
    nlinarith
  have hpow2 : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    calc
      (2 : ℝ) = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
  have hexp2 : -(a : ℝ) / 2 ≤ -(a : ℝ) / (2 : ℝ) ^ r := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).2
    nlinarith [show (0 : ℝ) ≤ a from Nat.cast_nonneg a]
  have h₁ := Real.rpow_le_rpow_of_exponent_le hp hexp
  have h₂ := Real.rpow_le_rpow_of_exponent_le hp hexp2
  have h₃ := mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  push_cast
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformResidueSmallPeriod
namespace OAI


namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformPMF_map_fiber {G H : Type*} [Fintype G] [Nonempty G]
    [DecidableEq H] (f : G → H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
  classical
  rw [pmf_map_toReal_indicator, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

theorem uniformPMF_map_hom_image {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      if y ∈ f.range then (Nat.card f.range : ℝ)⁻¹ else 0 := by
  classical
  rw [uniformPMF_map_fiber]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have he := AddMonoidHom.card_fiber_eq_of_mem_range f hy
      (show (0 : H) ∈ Set.range f from ⟨0, f.map_zero⟩)
    have hk : (Finset.univ.filter (fun x => f x = 0)).card = Fintype.card f.ker := by
      simp [Fintype.card_subtype, AddMonoidHom.mem_ker]
    have hc : Fintype.card f.ker * Fintype.card f.range = Fintype.card G := by
      simpa only [AddSubgroup.index_ker, Nat.card_eq_fintype_card] using f.ker.card_mul_index
    rw [he, hk, ← hc, Nat.cast_mul, Nat.card_eq_fintype_card]
    have hkn : (Fintype.card f.ker : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · simp only [hy, ite_false]
    have hz : Finset.univ.filter (fun x => f x = y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ⟨x, (Finset.mem_filter.mp hx).2⟩
    simp [hz]

theorem uniformPMF_map_hom_index {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      (if y ∈ f.range then (f.range.index : ℝ) else 0) / Fintype.card H := by
  classical
  rw [uniformPMF_map_hom_image]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have hcard : (Nat.card f.range : ℝ) * f.range.index = Fintype.card H := by
      have h := f.range.card_mul_index
      rw [Nat.card_eq_fintype_card (α := H)] at h
      exact_mod_cast h
    have hn : (Nat.card f.range : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hh : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    apply (eq_div_iff hh).mpr
    rw [← hcard, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · simp [hy]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformHomFiberWeights
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_mean_surjective_hom_fiber {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    (FiniteProbabilityWeights.uniform G).mean (fun x => if f x = y then (1 : ℝ) else 0) =
      (Fintype.card H : ℝ)⁻¹ := by
  have h := uniformPMF_map_hom_index f y
  have hr : f.range = ⊤ := by
    ext z
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_top, iff_true]
    exact hf z
  have hy : y ∈ f.range := hf y
  rw [if_pos hy, hr] at h
  simp only [AddSubgroup.index_top, Nat.cast_one, one_div] at h
  rw [uniformPMF_map_fiber] at h
  calc
    _ = ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
      rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
      simp
    _ = _ := h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformHomExpectation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_mean_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (g : H → ℝ) :
    (FiniteProbabilityWeights.uniform G).mean (fun x => g (f x)) =
      (FiniteProbabilityWeights.uniform H).mean g := by
  calc
    _ = ∑ y : H, (FiniteProbabilityWeights.uniform G).mean
        (fun x => if f x = y then (1 : ℝ) else 0) * g y := by
      unfold FiniteProbabilityWeights.mean
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp [mul_ite, ite_mul]
    _ = ∑ y : H, (Fintype.card H : ℝ)⁻¹ * g y := by
      simp_rw [uniform_mean_surjective_hom_fiber f hf]
    _ = _ := rfl

theorem expect_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (g : H → ℝ) :
    (𝔼 x : G, g (f x)) = 𝔼 y : H, g y := by
  simpa only [FiniteProbabilityWeights.uniform_mean] using
    uniform_mean_surjective_hom f hf g

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteUniformCoordinateRefresh
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I J X : Type*}

theorem expect_coordinate_resampling [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Fintype X] [Nonempty X]
    (f : J → I) (hf : Function.Injective f) (F : (I → X) → ℝ) :
    (𝔼 v : I → X, 𝔼 y : J → X, F (Function.extend f y v)) = 𝔼 v : I → X, F v := by
  have he := Fintype.expect_equiv (coordinateResamplingEquiv (X := X) f hf)
    (fun p => F (Function.extend f p.2 p.1)) (fun p => F p.1) (fun _ => rfl)
  simpa only [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_const] using he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ModularMultilinearSublevelPolynomial
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical

variable {R : Type*} [CommRing R]

theorem multiaffine_eval_fin_cons {n : ℕ} (P : MvPolynomial (Fin (n + 1)) R)
    (hP : degreeOf 0 P ≤ 1) (x : R) (y : Fin n → R) :
    eval (Fin.cons x y) P =
      x * eval y ((finSuccEquiv R n P).coeff 1) +
        eval y ((finSuccEquiv R n P).coeff 0) := by
  rw [eval_eq_eval_mv_eval']
  have hd : (finSuccEquiv R n P).natDegree ≤ 1 := by
    rwa [natDegree_finSuccEquiv]
  calc
    _ = Polynomial.eval x (Polynomial.map (eval y)
        (Polynomial.C ((finSuccEquiv R n P).coeff 1) * Polynomial.X +
          Polynomial.C ((finSuccEquiv R n P).coeff 0))) :=
      congrArg (fun Q => Polynomial.eval x (Polynomial.map (eval y) Q))
        (Polynomial.eq_X_add_C_of_natDegree_le_one hd)
    _ = _ := by simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]; rw [mul_comm]

theorem multiaffine_finSuccEquiv_coeff {n : ℕ} (P : MvPolynomial (Fin (n + 1)) R)
    (hP : ∀ j, degreeOf j P ≤ 1) (i : ℕ) :
    ∀ j, degreeOf j ((finSuccEquiv R n P).coeff i) ≤ 1 := by
  intro j
  exact (degreeOf_coeff_finSuccEquiv P j i).trans (hP j.succ)

theorem fullSquarefree_finSuccEquiv_coeff {n : ℕ} (P : MvPolynomial (Fin (n + 1)) R) :
    ((finSuccEquiv R n P).coeff 1).coeff
        (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val =
      P.coeff (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (n + 1)))).val := by
  rw [finSuccEquiv_coeff_coeff]
  congr 1
  ext j
  refine Fin.cases ?_ (fun i => ?_) j <;>
    simp [SquarefreeIndex.ofFinset_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularMultilinearAmbientSublevel
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical BigOperators

variable {I J R : Type*} [CommRing R]

theorem degreeOf_polynomialTranslate_le (P : MvPolynomial I R) (v : I → R) (i : I) :
    degreeOf i (polynomialTranslate v P) ≤ degreeOf i P := by
  let w : I → ℕ := Pi.single i 1
  have hP : P ∈ weightedSupportLE w (degreeOf i P) := by
    intro a ha
    change Finsupp.weight w a ≤ degreeOf i P
    rw [Finsupp.weight_single_one_apply]
    exact monomial_le_degreeOf i ha
  have ht := weightedSupportLE_aeval w w (fun j => X j + C (v j))
    (fun j => (weightedSupportLE w (w j)).add_mem
      (weightedSupportLE_X w j) (weightedSupportLE_C w (w j) (v j))) hP
  apply degreeOf_le_iff.mpr
  intro a ha
  have hh : Finsupp.weight w a ≤ degreeOf i P := ht ha
  simpa only [w, Finsupp.weight_single_one_apply] using hh

theorem degreeOf_killCompl_le (f : J → I) (hf : Function.Injective f)
    (P : MvPolynomial I R) (j : J) :
    degreeOf j (killCompl hf P) ≤ degreeOf (f j) P := by
  apply degreeOf_le_iff.mpr
  intro a ha
  have ham : a.mapDomain f ∈ P.support := by
    simpa only [mem_support_iff, coeff_killCompl] using ha
  have hh := monomial_le_degreeOf (f j) ham
  simpa only [Finsupp.mapDomain_apply hf] using hh

theorem degreeOf_conditionPolynomial_le (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) (j : J) :
    degreeOf j (conditionPolynomial f hf v P) ≤ degreeOf (f j) P :=
  (degreeOf_killCompl_le f hf _ j).trans (degreeOf_polynomialTranslate_le P _ (f j))

theorem coeff_conditionPolynomial_top (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) (a : J →₀ ℕ)
    (hP : P.totalDegree ≤ a.degree) :
    (conditionPolynomial f hf v P).coeff a = P.coeff (a.mapDomain f) := by
  rw [conditionPolynomial, coeff_killCompl]
  apply top_coeff_polynomialTranslate
  simpa only [Finsupp.degree_mapDomain] using hP

theorem eval_conditionPolynomial (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) (y : J → R) :
    eval y (conditionPolynomial f hf v P) = eval (Function.extend f y v) P := by
  unfold conditionPolynomial
  induction P using MvPolynomial.induction_on with
  | C c => simp only [polynomialTranslate_C, killCompl_C, eval_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP, polynomialTranslate_X, map_add, killCompl_C, eval_C, eval_X]
    congr 1
    by_cases hi : i ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hi
      simp only [show f j ∈ Set.range f from ⟨j, rfl⟩, ite_true, add_zero,
        hf.extend_apply]
      rw [← rename_X f j, killCompl_rename_app, eval_X]
    · simp only [hi, ite_false, Function.extend_apply' y v i hi]
      have hz : killCompl hf (X i : MvPolynomial I R) = 0 := by
        simp only [killCompl, aeval_X, hi, dite_false]
      rw [hz, map_zero, zero_add]

theorem conditionPolynomial_fullSquarefree {r : ℕ} (f : Fin r → I)
    (hf : Function.Injective f) (v : I → R) (P : MvPolynomial I R)
    (hP : P.totalDegree ≤ r) (hmulti : ∀ i, degreeOf i P ≤ 1) :
    (∀ j, degreeOf j (conditionPolynomial f hf v P) ≤ 1) ∧
      (conditionPolynomial f hf v P).coeff (fullShiftExponent r) =
        P.coeff ((fullShiftExponent r).mapDomain f) := by
  constructor
  · intro j
    exact (degreeOf_conditionPolynomial_le f hf v P j).trans (hmulti (f j))
  · apply coeff_conditionPolynomial_top
    change P.totalDegree ≤ (fullShiftExponent r).sum (fun _ e => e)
    rwa [fullShiftExponent_sum]

theorem expect_eval_conditionPolynomial [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Fintype R]
    (f : J → I) (hf : Function.Injective f) (P : MvPolynomial I R) (F : R → ℝ) :
    (𝔼 v : I → R, 𝔼 y : J → R, F (eval y (conditionPolynomial f hf v P))) =
      𝔼 x : I → R, F (eval x P) := by
  simp only [eval_conditionPolynomial]
  exact expect_coordinate_resampling f hf (fun x => F (eval x P))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem modularPolynomial_zero_reduction {I : Type*} [Fintype I] [DecidableEq I]
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (P : MvPolynomial I (ZMod N)) :
    (𝔼 x : I → ZMod N,
      if ZMod.castHom hMN (ZMod M) (MvPolynomial.eval x P) = 0 then (1 : ℝ) else 0) =
      𝔼 y : I → ZMod M,
        if MvPolynomial.eval y (P.map (ZMod.castHom hMN (ZMod M))) = 0 then (1 : ℝ) else 0 := by
  let f : (I → ZMod N) →+ (I → ZMod M) :=
    { toFun := fun x i => ZMod.castHom hMN (ZMod M) (x i)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; exact map_add (ZMod.castHom hMN (ZMod M)) (x i) (y i) }
  have hf : Function.Surjective f := by
    intro y
    choose x hx using fun i => ZMod.castHom_surjective hMN (y i)
    exact ⟨x, funext hx⟩
  have h := expect_surjective_hom f hf (fun y =>
    if MvPolynomial.eval y (P.map (ZMod.castHom hMN (ZMod M))) = 0 then (1 : ℝ) else 0)
  convert h using 1
  apply Finset.expect_congr rfl
  intro x _
  rw [MvPolynomial.map_eval]
  rfl

theorem modularAffine_zero_split {X R S : Type*} [Fintype X] [Nonempty X] [Fintype R]
    [Nonempty R] [DecidableEq R] [DecidableEq S] [Zero R] [Add R] [Mul R] [Zero S]
    (g h : X → R) (reduce : R → S) {ε : ℝ} (hε : 0 ≤ ε)
    (hfiber : ∀ c d : R, reduce c ≠ 0 →
      (𝔼 t : R, if t * c + d = 0 then (1 : ℝ) else 0) ≤ ε) :
    (𝔼 x : X, 𝔼 t : R, if t * g x + h x = 0 then (1 : ℝ) else 0) ≤
      (𝔼 x : X, if reduce (g x) = 0 then (1 : ℝ) else 0) + ε := by
  calc
    _ ≤ 𝔼 x : X, ((if reduce (g x) = 0 then (1 : ℝ) else 0) + ε) := by
      apply Finset.expect_le_expect
      intro x _
      by_cases hx : reduce (g x) = 0
      · simp only [hx, ite_true]
        have hle : (𝔼 t : R, if t * g x + h x = 0 then (1 : ℝ) else 0) ≤ 1 := by
          calc
            _ ≤ 𝔼 _t : R, (1 : ℝ) := Finset.expect_le_expect (by intro t _; split_ifs <;> norm_num)
            _ = 1 := Fintype.expect_const _
        linarith
      · simpa only [hx, ite_false, zero_add] using hfiber (g x) (h x) hx
    _ ≤ _ := by
      rw [Finset.expect_add_distrib]
      rw [Fintype.expect_const]

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

private theorem multiaffine_map {I R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : MvPolynomial I R) (hP : ∀ i, degreeOf i P ≤ 1) :
    ∀ i, degreeOf i (P.map f) ≤ 1 := by
  intro i
  rw [degreeOf_le_iff]
  intro m hm
  exact degreeOf_le_iff.mp (hP i) m (support_map_subset f P hm)

theorem modularMultilinear_full_sublevel (r : ℕ) {p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial (Fin (r + 1)) (ZMod (p ^ a)))
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (r + 1)))).val)) :
    (𝔼 x : Fin (r + 1) → ZMod (p ^ a),
      if eval x P = 0 then (1 : ℝ) else 0) ≤
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  induction r generalizing a with
  | zero =>
    let G := (finSuccEquiv (ZMod (p ^ a)) 0 P).coeff 1
    let H := (finSuccEquiv (ZMod (p ^ a)) 0 P).coeff 0
    let y : Fin 0 → ZMod (p ^ a) := fun i => Fin.elim0 i
    have hG : IsUnit (eval y G) := by
      have hcoef := fullSquarefree_finSuccEquiv_coeff P
      have hz : (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin 0))).val = 0 := by
        ext i; exact Fin.elim0 i
      rw [hz] at hcoef
      have he : eval y G = G.coeff 0 := by
        have hconst : G = C (G.coeff 0) := by
          have hh := (isEmptyRingEquiv (ZMod (p ^ a)) (Fin 0)).symm_apply_apply G
          simpa only [isEmptyRingEquiv_eq_coeff_zero,
            isEmptyRingEquiv_symm_apply] using hh.symm
        conv_lhs => rw [hconst, eval_C]
      rw [he, hcoef]
      exact hunit
    let : Fact (1 < p ^ 1) := ⟨by simpa using hp.one_lt⟩
    have hc : ZMod.castHom (pow_dvd_pow p (show 1 ≤ a by omega)) (ZMod (p ^ 1))
        (eval y G) ≠ 0 := by
      have hi := hG.map (ZMod.castHom (pow_dvd_pow p (show 1 ≤ a by omega)) (ZMod (p ^ 1)))
      exact hi.ne_zero
    have hf := zmod_prime_power_affine_zero_expect_le_rpow hp (show 1 ≤ 1 by omega)
      (show 1 ≤ a by omega) (eval y G) (eval y H) hc
    rw [expect_fin_cons]
    simp_rw [multiaffine_eval_fin_cons P (hP 0)]
    simp_rw [expect_empty_tuple]
    simp only [Nat.cast_one, zero_add, pow_zero, div_one, one_mul]
    convert hf using 1
    · congr 1; funext t; rw [mul_comm]
    · congr 1; ring
  | succ r ih =>
    let b := (a + 1) / 2
    have hb := modularSublevel_half_depth ha
    let f : ZMod (p ^ a) →+* ZMod (p ^ b) :=
      ZMod.castHom (pow_dvd_pow p hb.2.1) (ZMod (p ^ b))
    let G := (finSuccEquiv (ZMod (p ^ a)) (r + 1) P).coeff 1
    let H := (finSuccEquiv (ZMod (p ^ a)) (r + 1) P).coeff 0
    have hG : ∀ i, degreeOf i G ≤ 1 := multiaffine_finSuccEquiv_coeff P hP 1
    have hGu : IsUnit (G.coeff
        (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (r + 1)))).val) := by
      rw [fullSquarefree_finSuccEquiv_coeff]
      exact hunit
    have hGfu : IsUnit ((G.map f).coeff
        (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (r + 1)))).val) := by
      rw [coeff_map]
      exact hGu.map f
    have hsmall := ih hb.1 (G.map f) (multiaffine_map f G hG) hGfu
    have hbad : (𝔼 y : Fin (r + 1) → ZMod (p ^ a),
        if f (eval y G) = 0 then (1 : ℝ) else 0) ≤
          ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(b : ℝ) / (2 : ℝ) ^ r) := by
      change (𝔼 y : Fin (r + 1) → ZMod (p ^ a),
        if ZMod.castHom (pow_dvd_pow p hb.2.1) (ZMod (p ^ b)) (eval y G) = 0
          then (1 : ℝ) else 0) ≤ _
      rw [modularPolynomial_zero_reduction (pow_dvd_pow p hb.2.1)]
      exact hsmall
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hfiber (c d : ZMod (p ^ a)) (hc : f c ≠ 0) :
        (𝔼 t : ZMod (p ^ a), if t * c + d = 0 then (1 : ℝ) else 0) ≤
          (p : ℝ) ^ (-(a : ℝ) / 2) := by
      have h := zmod_prime_power_affine_zero_expect_le_rpow hp hb.1 hb.2.1 c d hc
      simpa only [mul_comm c] using h.trans (modularSublevel_fiber_exponent hp1 ha)
    have hsplit := modularAffine_zero_split (fun y => eval y G) (fun y => eval y H) f
      (Real.rpow_nonneg (show (0 : ℝ) ≤ p by positivity) (-(a : ℝ) / 2)) hfiber
    rw [expect_fin_cons]
    simp_rw [multiaffine_eval_fin_cons P (hP 0)]
    rw [Finset.expect_comm]
    apply hsplit.trans
    apply (add_le_add hbad (le_refl ((p : ℝ) ^ (-(a : ℝ) / 2)))).trans
    simpa only [Nat.succ_sub_one] using
      modularSublevel_induction_bound hp1 ha (Nat.succ_pos r)

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem modularMultilinear_sublevel {I : Type*} [Fintype I] [DecidableEq I]
    (r : ℕ) {p a : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial I (ZMod (p ^ a))) (f : Fin (r + 1) → I)
    (hf : Function.Injective f) (hdeg : P.totalDegree ≤ r + 1)
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff ((fullShiftExponent (r + 1)).mapDomain f))) :
    (𝔼 x : I → ZMod (p ^ a), if eval x P = 0 then (1 : ℝ) else 0) ≤
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  rw [← expect_eval_conditionPolynomial f hf P (fun z => if z = 0 then (1 : ℝ) else 0)]
  calc
    _ ≤ 𝔼 _v : I → ZMod (p ^ a),
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
      apply Finset.expect_le_expect
      intro v _
      have h := conditionPolynomial_fullSquarefree f hf v P hdeg hP
      apply modularMultilinear_full_sublevel r hp ha _ h.1
      have he : (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (r + 1)))).val =
          fullShiftExponent (r + 1) := by
        ext i
        simp [SquarefreeIndex.ofFinset_apply, fullShiftExponent_apply]
      rw [he, h.2]
      exact hunit
    _ = _ := Fintype.expect_const _

theorem modularMultilinear_sublevel_of_pos {I : Type*} [Fintype I] [DecidableEq I]
    {r p a : ℕ} [NeZero p] (hr : 0 < r) (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial I (ZMod (p ^ a))) (f : Fin r → I)
    (hf : Function.Injective f) (hdeg : P.totalDegree ≤ r)
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff ((fullShiftExponent r).mapDomain f))) :
    (𝔼 x : I → ZMod (p ^ a), if eval x P = 0 then (1 : ℝ) else 0) ≤
        (r : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ (r - 1)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simpa only [Nat.succ_sub_one] using modularMultilinear_sublevel r hp ha P f hf hdeg hP hunit

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ModularMultilinearAffineCost
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem modularMultilinear_affine_mean_sublevel {I : Type*} [Fintype I] [DecidableEq I]
    {r p a : ℕ} [NeZero p] (hr : 0 < r) (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial I (ZMod (p ^ a))) (f : Fin r → I)
    (hf : Function.Injective f) (hdeg : P.totalDegree ≤ r)
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff ((fullShiftExponent r).mapDomain f)))
    (offset : (I → ZMod (p ^ a)) → ZMod (p ^ a)) :
    (𝔼 x : I → ZMod (p ^ a), 𝔼 t : ZMod (p ^ a),
      if t * eval x P + offset x = 0 then (1 : ℝ) else 0) ≤
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  let b := (a + 1) / 2
  have hb := modularSublevel_half_depth ha
  let reduce : ZMod (p ^ a) →+* ZMod (p ^ b) :=
    ZMod.castHom (pow_dvd_pow p hb.2.1) (ZMod (p ^ b))
  have hmap : ∀ i, degreeOf i (P.map reduce) ≤ 1 := by
    intro i
    rw [degreeOf_le_iff]
    intro m hm
    exact degreeOf_le_iff.mp (hP i) m (support_map_subset reduce P hm)
  have hunit' : IsUnit ((P.map reduce).coeff ((fullShiftExponent r).mapDomain f)) := by
    rw [coeff_map]
    exact hunit.map reduce
  have hdeg' : (P.map reduce).totalDegree ≤ r := by
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact (le_totalDegree (support_map_subset reduce P hm)).trans hdeg
  have hsmall := modularMultilinear_sublevel_of_pos hr hp hb.1
    (P.map reduce) f hf hdeg' hmap hunit'
  have hbad : (𝔼 x : I → ZMod (p ^ a),
      if reduce (eval x P) = 0 then (1 : ℝ) else 0) ≤
        (r : ℝ) * (p : ℝ) ^ (-(b : ℝ) / (2 : ℝ) ^ (r - 1)) := by
    change (𝔼 x : I → ZMod (p ^ a),
      if ZMod.castHom (pow_dvd_pow p hb.2.1) (ZMod (p ^ b)) (eval x P) = 0
        then (1 : ℝ) else 0) ≤ _
    rw [modularPolynomial_zero_reduction (pow_dvd_pow p hb.2.1)]
    exact hsmall
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hfiber (c d : ZMod (p ^ a)) (hc : reduce c ≠ 0) :
      (𝔼 t : ZMod (p ^ a), if t * c + d = 0 then (1 : ℝ) else 0) ≤
        (p : ℝ) ^ (-(a : ℝ) / 2) := by
    have h := zmod_prime_power_affine_zero_expect_le_rpow hp hb.1 hb.2.1 c d hc
    simpa only [mul_comm c] using h.trans (modularSublevel_fiber_exponent hp1 ha)
  have hsplit := modularAffine_zero_split (fun x => eval x P) offset reduce
    (Real.rpow_nonneg (show (0 : ℝ) ≤ p by positivity) (-(a : ℝ) / 2)) hfiber
  exact hsplit.trans ((add_le_add hbad le_rfl).trans
    (modularSublevel_induction_bound hp1 ha hr))

theorem modularMultilinear_gcd_mean_sublevel {I : Type*} [Fintype I] [DecidableEq I]
    {r p a : ℕ} [NeZero p] (hr : 0 < r) (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial I (ZMod (p ^ a))) (f : Fin r → I)
    (hf : Function.Injective f) (hdeg : P.totalDegree ≤ r)
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff ((fullShiftExponent r).mapDomain f))) :
    (𝔼 x : I → ZMod (p ^ a), ((eval x P).val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)) ≤
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  have h := modularMultilinear_affine_mean_sublevel hr hp ha P f hf hdeg hP hunit
    (fun _ => 0)
  rw [zmod_gcd_expect_eq_mul_zero_expect (p ^ a) (fun x => eval x P)]
  simpa only [add_zero, mul_comm] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDifferencePermanentBlocks
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {R : Type*} [CommSemiring R]

theorem permanentExponent_apply (n : ℕ) (σ : Equiv.Perm (Fin n)) (j : Fin n × Fin n) :
    permanentExponent n σ j = if σ j.2 = j.1 then 1 else 0 := by
  rcases j with ⟨a, b⟩
  simp only [permanentExponent, Finsupp.finsetSum_apply, Finsupp.single_apply, Prod.mk.injEq,
    and_comm, ite_and]
  simp

theorem permanentExponent_injective (n : ℕ) : Function.Injective (permanentExponent n) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have hh := congrArg (fun d => d (σ i, i)) h
  simp only [permanentExponent_apply, ite_true] at hh
  by_contra hi
  have hne : τ i ≠ σ i := Ne.symm hi
  simp [hne] at hh

theorem permanentPolynomial_eq_monomial_sum (n : ℕ) :
    permanentPolynomial n (R := R) = ∑ σ : Equiv.Perm (Fin n), monomial (permanentExponent n σ) 1 := by
  unfold permanentPolynomial Matrix.permanent permanentExponent
  apply Finset.sum_congr rfl
  intro σ _
  rw [monomial_sum_one]
  rfl

theorem permanentPolynomial_degreeOf (n : ℕ) (j : Fin n × Fin n) :
    degreeOf j (permanentPolynomial n (R := R)) ≤ 1 := by
  by_cases h : Subsingleton R
  · let := h
    have hp : permanentPolynomial n (R := R) = 0 := Subsingleton.elim _ _
    simp [hp]
  let : Nontrivial R := not_subsingleton_iff_nontrivial.mp h
  rw [permanentPolynomial_eq_monomial_sum]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro σ _
  rw [degreeOf_monomial_eq _ _ one_ne_zero, permanentExponent_apply]
  split_ifs <;> omega

theorem permanentPolynomial_totalDegree (n : ℕ) :
    (permanentPolynomial n (R := R)).totalDegree ≤ n := by
  by_cases h : Subsingleton R
  · let := h
    have hp : permanentPolynomial n (R := R) = 0 := Subsingleton.elim _ _
    simp [hp]
  let : Nontrivial R := not_subsingleton_iff_nontrivial.mp h
  unfold permanentPolynomial Matrix.permanent
  apply totalDegree_finsetSum_le
  intro σ _
  apply (totalDegree_finsetProd _ _).trans
  simp [totalDegree_X]

theorem permanentPolynomial_coeff (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permanentPolynomial n (R := R)).coeff (permanentExponent n σ) = 1 := by
  rw [permanentPolynomial_eq_monomial_sum, coeff_sum]
  simp only [coeff_monomial, (permanentExponent_injective n).eq_iff]
  simp

theorem permanentExponent_one_eq_diagonal (n : ℕ) :
    permanentExponent n 1 = (fullShiftExponent n).mapDomain (fun i => (i, i)) := by
  rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (fun _ => Finsupp.single_zero _)]
  simp only [fullShiftExponent_apply, permanentExponent, Equiv.Perm.one_apply]

theorem permanentPolynomial_diagonal_coefficient (n : ℕ) :
    (permanentPolynomial n (R := R)).coeff
      ((fullShiftExponent n).mapDomain (fun i => (i, i))) = 1 := by
  rw [← permanentExponent_one_eq_diagonal]
  exact permanentPolynomial_coeff n 1

theorem eval_permanentPolynomial (n : ℕ) (x : Fin n × Fin n → R) :
    eval x (permanentPolynomial n) = Matrix.permanent (fun i j => x (i, j)) := by
  simp only [permanentPolynomial, Matrix.permanent, map_sum, map_prod, eval_X]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem permanent_gcd_mean_sublevel {n p a : ℕ} [NeZero p]
    (hn : 0 < n) (hp : p.Prime) (ha : 0 < a) :
    (𝔼 x : (Fin n × Fin n) → ZMod (p ^ a),
      ((Matrix.permanent (fun i j => x (i, j))).val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)) ≤
        ((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n) := by
  have h := modularMultilinear_gcd_mean_sublevel hn hp ha
    (permanentPolynomial n) (fun i => (i, i))
    (fun _ _ h => congrArg Prod.fst h)
    (permanentPolynomial_totalDegree n) (permanentPolynomial_degreeOf n)
    (by rw [permanentPolynomial_diagonal_coefficient]; exact isUnit_one)
  simpa only [eval_permanentPolynomial] using h

theorem permanent_zero_gcd_mean {p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) :
    (𝔼 x : (Fin 0 × Fin 0) → ZMod (p ^ a),
      ((Matrix.permanent (fun i j => x (i, j))).val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)) =
        1 / (p ^ a : ℕ) := by
  have hm : 1 < p ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
  have hval : (1 : ZMod (p ^ a)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt hm
  have hperm (x : (Fin 0 × Fin 0) → ZMod (p ^ a)) :
      Matrix.permanent (fun i j => x (i, j)) = 1 := Matrix.permanent_isEmpty
  simp only [hperm, hval, Nat.gcd_one_left, Nat.cast_one,
    Fintype.expect_const]

theorem permanent_gcd_mean_sublevel_all_s2_oai {n p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) :
    (𝔼 x : (Fin n × Fin n) → ZMod (p ^ a),
      ((Matrix.permanent (fun i j => x (i, j))).val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)) ≤
        ((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n) := by
  cases n with
  | zero =>
    rw [permanent_zero_gcd_mean hp ha]
    simp only [Nat.zero_add, Nat.cast_one, pow_zero, div_one, one_mul]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Nat.cast_pow, one_div]
  | succ n => exact permanent_gcd_mean_sublevel (Nat.succ_pos _) hp ha

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.permanent_gcd_mean_sublevel_all_s2_oai := @OAI.Erdos3.permanent_gcd_mean_sublevel_all_s2_oai
