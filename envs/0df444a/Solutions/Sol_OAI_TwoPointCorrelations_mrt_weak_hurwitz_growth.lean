-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_weak_hurwitz_growth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:39:17.673314+00:00
-- url     : https://prove2.me/submissions/48a71bfc-083e-4b1e-8755-6a5fd95dfd4c

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_hurwitz_cutoff
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_log_dirichlet_block

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDyadicPrefix
namespace OAI

/-! Combining uniform prefix bounds on dyadic blocks. -/
namespace TwoPointCorrelations

open _root_.Finset

theorem halasz_dyadic_prefix (f : ℕ → ℂ) {B : ℝ} (hB : 0≤ B)
    (hzero : ‖f 0‖≤ B)
    (K : ℕ) (hblock : ∀ k< K, ∀ H : ℕ, H≤2^k → ‖∑ i∈range H,f (2^k+i)‖≤ B) :
    ∀ M : ℕ, M≤2^K → ‖∑ n∈range M,f n‖≤((K:ℝ)+1)*B := by
  induction K with
  | zero =>
    intro M hM
    have hM1 : M≤1 := by simpa only [pow_zero] using hM
    interval_cases M
    · simpa using hB
    · simpa using hzero
  | succ K ih =>
    have hprev : ∀ k< K, ∀ H : ℕ, H≤2^k → ‖∑ i∈range H,f (2^k+i)‖≤ B :=
      fun k hk H hH => hblock k (by omega) H hH
    intro M hM
    by_cases hsmall : M≤2^K
    · have hh := ih hprev M hsmall
      push_cast
      linarith
    · have hsplit : M=2^K+(M-2^K) := by omega
      have htail : M-2^K≤2^K := by rw [pow_succ] at hM; omega
      conv_lhs => rw [hsplit, sum_range_add]
      apply (norm_add_le _ _).trans
      have hleft := ih hprev (2^K) le_rfl
      have hright := hblock K (by omega) (M-2^K) htail
      push_cast
      linarith

end TwoPointCorrelations

end OAI

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




@[simp] lemma mem_halaszVinogradovFiber {s N k : ℕ} {x y : Fin s → Fin N} :
    y ∈ halaszVinogradovFiber x k ↔ ∀ j ∈ Icc 1 k,
      (∑ i, ((x i).val+1)^j) = ∑ i, ((y i).val+1)^j := by
  classical
  simp [halaszVinogradovFiber]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszWeakStripScale
namespace OAI

/-! The displacement of the weak strip has bounded cubic cost. -/
namespace TwoPointCorrelations

lemma halasz_weak_strip_cost {δ L : ℝ} (hδ : 0≤δ) (hL : 0< L)
    (hδhi : δ≤4*L^(-(2/3:ℝ))) :
    δ^(3/2:ℝ)*L≤(4:ℝ)^(3/2:ℝ) := by
  calc
    _ ≤ (4*L^(-(2/3:ℝ)))^(3/2:ℝ)*L := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hδ hδhi (by norm_num)) hL.le
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hL.le _),
        ← Real.rpow_mul hL.le]
      norm_num only [show (-(2/3:ℝ))*(3/2)=-1 by norm_num,Real.rpow_neg_one]
      field_simp

lemma halasz_dyadic_log (k : ℕ) : Real.log ((2^k:ℕ):ℝ)=(k:ℝ)*Real.log 2 := by
  push_cast
  rw [Real.log_pow]

lemma halasz_dyadic_size {k : ℕ} (hk : 3≤ k) :
    1≤ Real.log ((2^k:ℕ):ℝ) ∧
      ((2^k:ℕ):ℝ)^(2/3:ℝ)≤((2^k:ℕ):ℝ)/2 := by
  have hkR : (3:ℝ)≤ k := by exact_mod_cast hk
  have hlog2 : (1/2:ℝ)≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  refine ⟨?_,?_⟩
  · rw [halasz_dyadic_log]
    nlinarith
  · have hp : ((2^k:ℕ):ℝ)=(2:ℝ)^(k:ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
    rw [hp,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    have he : (k:ℝ)*(2/3)≤(k:ℝ)-1 := by linarith
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) he
    simpa only [Real.rpow_sub (by norm_num : (0:ℝ)<2),Real.rpow_one] using hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDyadicCutoff
namespace OAI

/-! A dyadic cutoff comparable with the square of the height, with the
precise height-to-length margin needed by the phase estimate. -/
namespace TwoPointCorrelations


lemma halasz_dyadic_cutoff_bounds {L : ℝ} (hL : 100≤ L) :
    let K := halaszDyadicCutoffDegree L
    1≤2^K-1 ∧ (K:ℝ)*Real.log 2≤(100/49:ℝ)*L ∧
      (K:ℝ)≤4*L+2 ∧
      (Real.exp L)^2≤((2^K-1:ℕ):ℝ) ∧
      ((2^K-1:ℕ):ℝ)≤4*(Real.exp L)^2 := by
  have hL0 : 0< L := by linarith
  have hlog : 0< Real.log 2 := Real.log_pos (by norm_num)
  have hloglo : (1/2:ℝ)≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have hloghi : Real.log 2≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  let K := halaszDyadicCutoffDegree L
  have hceil : 2*L/Real.log 2≤(⌈2*L/Real.log 2⌉₊:ℝ) := Nat.le_ceil _
  have hceilhi := Nat.ceil_lt_add_one (show 0≤2*L/Real.log 2 by positivity)
  have hK : (K:ℝ)<2*L/Real.log 2+2 := by dsimp only [K,halaszDyadicCutoffDegree]; push_cast; linarith
  have hKlo : 2*L+Real.log 2≤(K:ℝ)*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_right hceil hlog.le
    have he : 2*L/Real.log 2*Real.log 2=2*L := by field_simp
    rw [he] at hh
    dsimp only [K,halaszDyadicCutoffDegree]
    push_cast
    linarith
  have hKhi : (K:ℝ)*Real.log 2≤2*L+2*Real.log 2 := by
    have hh := mul_lt_mul_of_pos_right hK hlog
    have he : (2*L/Real.log 2+2)*Real.log 2=2*L+2*Real.log 2 := by field_simp
    rw [he] at hh
    exact hh.le
  have hKlinear : (K:ℝ)≤4*L+2 := by
    have hq : 2*L/Real.log 2≤4*L := (div_le_iff₀ hlog).mpr (by nlinarith)
    linarith
  have hpow : ((2^K:ℕ):ℝ)=Real.exp ((K:ℝ)*Real.log 2) := by
    push_cast
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  have hexp (y : ℝ) : Real.exp (2*y)=(Real.exp y)^2 := by
    rw [two_mul,Real.exp_add,pow_two]
  have hpowlo : 2*(Real.exp L)^2≤((2^K:ℕ):ℝ) := by
    rw [hpow]
    have hh := Real.exp_le_exp.mpr hKlo
    have he : Real.exp (2*L+Real.log 2)=2*(Real.exp L)^2 := by
      rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),hexp]
      ring
    rwa [he] at hh
  have hpowhi : ((2^K:ℕ):ℝ)≤4*(Real.exp L)^2 := by
    rw [hpow]
    have hh := Real.exp_le_exp.mpr hKhi
    have he : Real.exp (2*L+2*Real.log 2)=4*(Real.exp L)^2 := by
      rw [Real.exp_add,hexp,hexp,Real.exp_log (by norm_num : (0:ℝ)<2)]
      ring
    rwa [he] at hh
  have hE : 1≤ Real.exp L := Real.one_le_exp_iff.mpr (by linarith)
  have hNcast : ((2^K-1:ℕ):ℝ)=((2^K:ℕ):ℝ)-1 := by
    rw [Nat.cast_sub (Nat.one_le_pow K 2 (by norm_num)),Nat.cast_one]
  have hN : 1≤2^K-1 := by
    have hh : (1:ℝ)≤((2^K-1:ℕ):ℝ) := by rw [hNcast]; nlinarith
    exact_mod_cast hh
  refine ⟨hN,by nlinarith,hKlinear,?_,?_⟩
  · rw [hNcast]
    nlinarith
  · rw [hNcast]
    linarith

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDyadicDirichlet
namespace OAI

/-! The actual shifted Dirichlet polynomial at an exponential cutoff.
All prefixes, including the small dyadic blocks, are retained. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Complex

theorem halasz_dyadic_dirichlet : ∃ C : ℝ, 1≤ C ∧ ∀ K : ℕ, ∀ L : ℝ,
    1≤ L → (K:ℝ)*Real.log 2≤(100/49:ℝ)*L → ∀ a : ℝ,
    a∈Set.Icc (0:ℝ) 1 → ∀ s : ℂ, 2/3≤ s.re → |s.im|=Real.exp L →
    max (1-s.re) 0≤4*L^(-(2/3:ℝ)) →
    ‖∑ n∈range (2^K-1),(((n+1:ℕ):ℝ)+a:ℂ)^(-s)‖≤
      ((K:ℝ)+1)*C*(L+1)^6 := by
  obtain ⟨C₀,hC₀,hblock⟩ := halasz_log_dirichlet_block
  let D := (10^9:ℝ)*(4:ℝ)^(3/2:ℝ)
  let C := C₀*Real.exp D+8
  have hCE : 0≤ C₀*Real.exp D := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hC : 1≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro K L hL hKL a ha s hσ ht hδ
  have hL0 : 0< L := by linarith
  have hpow : 1≤(L+1)^6 := one_le_pow₀ (by linarith)
  have hB0 : 0≤ C*(L+1)^6 := by positivity
  let f : ℕ → ℂ := fun n => if n=0 then 0 else (((n:ℝ)+a:ℝ):ℂ)^(-s)
  have hf0 : ‖f 0‖≤ C*(L+1)^6 := by simpa [f] using hB0
  have hblocks : ∀ k< K, ∀ H : ℕ, H≤2^k →
      ‖∑ i∈range H,f (2^k+i)‖≤ C*(L+1)^6 := by
    intro k hk H hH
    have hNk : 1≤2^k := Nat.one_le_pow _ _ (by norm_num)
    have heq : (∑ i∈range H,f (2^k+i))=
        ∑ i∈range H,((((2^k:ℕ):ℝ)+a+i:ℝ):ℂ)^(-s) := by
      apply sum_congr rfl
      intro i _
      have hn : 2^k+i≠0 := by omega
      simp only [f,if_neg hn,Nat.cast_add]
      congr 2
      ring
    rw [heq]
    by_cases hsmall : k<3
    · have hNH : H≤4 := by interval_cases k <;> norm_num at hH ⊢ <;> omega
      have hs : ‖∑ i∈range H,((((2^k:ℕ):ℝ)+a+i:ℝ):ℂ)^(-s)‖≤ H := by
        apply (norm_sum_le _ _).trans
        calc
          _ ≤ ∑ _i∈range H,(1:ℝ) := by
            apply sum_le_sum
            intro i _
            have hx : (1:ℝ)≤((2^k:ℕ):ℝ)+a+i := by
              have hNR : (1:ℝ)≤(2^k:ℕ) := by exact_mod_cast hNk
              have hi : (0:ℝ)≤ i := Nat.cast_nonneg _
              linarith [ha.1]
            rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith :
              (0:ℝ)<((2^k:ℕ):ℝ)+a+i)]
            simp only [Complex.neg_re]
            exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
          _ = _ := by simp
      have hHR : (H:ℝ)≤4 := by exact_mod_cast hNH
      have hCB : 8≤ C*(L+1)^6 := by
        have hC8 : 8≤ C := by dsimp only [C]; linarith
        nlinarith
      linarith
    · have hk3 : 3≤ k := by omega
      obtain ⟨hlog,hhalf⟩ := halasz_dyadic_size hk3
      have hy : 0< Real.log ((2^k:ℕ):ℝ) := by linarith
      let lam := L/Real.log ((2^k:ℕ):ℝ)
      have hLy : L=lam*Real.log ((2^k:ℕ):ℝ) := by dsimp only [lam]; field_simp
      have hlam : 49/100≤ lam := by
        apply (le_div_iff₀ hy).mpr
        have hkR : (k:ℝ)≤ K := by exact_mod_cast hk.le
        have hlog2 : 0≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have hh := mul_le_mul_of_nonneg_right hkR hlog2
        rw [halasz_dyadic_log]
        nlinarith
      have ht' : |s.im|=((2^k:ℕ):ℝ)^lam := by
        rw [Real.rpow_def_of_pos (by positivity : (0:ℝ)<(2^k:ℕ)),ht]
        congr 1
        dsimp only [lam]
        field_simp
      have hb := hblock (2^k) H hNk hH a ha s hσ L lam hL0 hlog hLy hlam hhalf ht'
      have hcost := halasz_weak_strip_cost (show 0≤ max (1-s.re) 0 from le_max_right _ _) hL0 hδ
      have hexp : Real.exp ((10^9:ℝ)*(max (1-s.re) 0)^(3/2:ℝ)*L)≤ Real.exp D := by
        apply Real.exp_le_exp.mpr
        dsimp only [D]
        nlinarith
      have hc : C₀*(L+1)^6*Real.exp ((10^9:ℝ)*(max (1-s.re) 0)^(3/2:ℝ)*L)≤
          C₀*(L+1)^6*Real.exp D := mul_le_mul_of_nonneg_left hexp (by positivity)
      apply hb.trans
      dsimp only [C]
      nlinarith
  have hp := halasz_dyadic_prefix f hB0 hf0 K hblocks (2^K) le_rfl
  have heq : (∑ n∈range (2^K),f n)=
      ∑ n∈range (2^K-1),(((n+1:ℕ):ℝ)+a:ℂ)^(-s) := by
    have hK : 2^K=(2^K-1)+1 := by have := Nat.one_le_pow K 2 (by norm_num); omega
    rw [hK,sum_range_succ']
    simp only [f,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,ite_true,Nat.add_sub_cancel,Complex.ofReal_add,
      Nat.cast_zero,add_zero]
  rw [heq] at hp
  simpa only [mul_assoc] using hp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log













































attribute [fun_prop] measurable_from_top












section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end












































end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCutoffRemainder
namespace OAI

/-! The first-order cutoff has a bounded remainder when its length is
comparable with the square of the height. -/
namespace TwoPointCorrelations

open _root_.Complex

lemma halasz_cutoff_remainder {N E : ℝ} (hE : 1≤ E)
    (hNlo : E^2≤ N) (hNhi : N≤4*E^2) {s : ℂ}
    (hσ : 2/3≤ s.re) (hσhi : s.re≤2) (ht : |s.im|=E) :
    N^(1-s.re)/‖1-s‖+N^(-s.re)/2+2*‖s‖*N^(-s.re)/s.re≤15 := by
  have hE0 : 0< E := by linarith
  have hN : 1≤ N := by nlinarith
  have hN0 : 0< N := by linarith
  have hσ0 : 0< s.re := by linarith
  have hden : E≤‖1-s‖ := by
    have hh := Complex.abs_im_le_norm (1-s)
    simpa only [Complex.sub_im,Complex.one_im,zero_sub,abs_neg,ht] using hh
  have hden0 : 0<‖1-s‖ := hE0.trans_le hden
  have hnorm : ‖s‖≤3*E := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg hσ0.le,ht] at hh
    linarith
  have hrootlo : E≤ Real.sqrt N := (Real.le_sqrt hE0.le hN0.le).mpr hNlo
  have hroothi : Real.sqrt N≤2*E := (Real.sqrt_le_left (by positivity)).mpr (by nlinarith)
  have hneg : N^(-s.re)≤1/E := by
    calc
      _ ≤ N^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = 1/Real.sqrt N := by rw [Real.rpow_neg hN0.le,← Real.sqrt_eq_rpow]; simp only [one_div]
      _ ≤ _ := one_div_le_one_div_of_le hE0 hrootlo
  have hpos : N^(1-s.re)≤2*E := by
    calc
      _ ≤ N^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = Real.sqrt N := (Real.sqrt_eq_rpow N).symm
      _ ≤ _ := hroothi
  have hfirst : N^(1-s.re)/‖1-s‖≤2 := by
    apply (div_le_iff₀ hden0).mpr
    linarith
  have hsecond : N^(-s.re)/2≤1/2 := by
    have hh : 1/E≤1 := (div_le_one hE0).mpr hE
    linarith
  have hthird : 2*‖s‖*N^(-s.re)/s.re≤12 := by
    apply (div_le_iff₀ hσ0).mpr
    have hmul := mul_le_mul hnorm hneg (Real.rpow_nonneg hN0.le _) (by positivity : 0≤3*E)
    have heq : (3*E)*(1/E)=3 := by field_simp
    rw [heq] at hmul
    linarith
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszHurwitzGrowth
namespace OAI

/-! Polynomial logarithmic growth of the actual Hurwitz function in a
weak Vinogradov--Korobov strip, uniform in the translation parameter. -/
namespace TwoPointCorrelations

open _root_.Complex _root_.HurwitzZeta _root_.Finset

theorem halasz_hurwitz_growth : ∃ A : ℝ, 1≤ A ∧ ∀ L : ℝ, 100≤ L →
    ∀ a∈Set.Icc (0:ℝ) 1, ∀ s : ℂ, 2/3≤ s.re → s.re≤2 →
    |s.im|=Real.exp L → max (1-s.re) 0≤4*L^(-(2/3:ℝ)) →
      ‖hurwitzZeta (a:UnitAddCircle) s-mrtHurwitzFirstTerm a s‖≤ A*(L+1)^7 := by
  obtain ⟨C,hC,hpoly⟩ := halasz_dyadic_dirichlet
  refine ⟨7*C+15,by linarith,?_⟩
  intro L hL a ha s hσ hσhi ht hδ
  let K := halaszDyadicCutoffDegree L
  let N := 2^K-1
  obtain ⟨hN,hKL,hKhi,hNlo,hNhi⟩ := halasz_dyadic_cutoff_bounds hL
  have hσ0 : 0< s.re := by linarith
  have hs1 : s≠1 := by
    intro hs1
    rw [hs1] at ht
    norm_num at ht
    exact (Real.exp_pos L).ne' ht.symm
  have hcut := halasz_hurwitz_cutoff ha hσ0 hs1 hN
  have hrem := halasz_cutoff_remainder
    (Real.one_le_exp_iff.mpr (by linarith : 0≤ L)) hNlo hNhi hσ hσhi ht
  have hp := hpoly K L (by linarith) hKL a ha s hσ ht hδ
  have hn : ‖hurwitzZeta (a:UnitAddCircle) s-mrtHurwitzFirstTerm a s‖≤
      15+((K:ℝ)+1)*C*(L+1)^6 := by
    calc
      _ = ‖(hurwitzZeta (a:UnitAddCircle) s-mrtHurwitzFirstTerm a s-
          ∑ n∈range N,(((n+1:ℕ):ℝ)+a:ℂ)^(-s))+
          ∑ n∈range N,(((n+1:ℕ):ℝ)+a:ℂ)^(-s)‖ := by congr 1; ring
      _ ≤ ‖hurwitzZeta (a:UnitAddCircle) s-mrtHurwitzFirstTerm a s-
          ∑ n∈range N,(((n+1:ℕ):ℝ)+a:ℂ)^(-s)‖+
          ‖∑ n∈range N,(((n+1:ℕ):ℝ)+a:ℂ)^(-s)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (hcut.trans hrem) hp
  have hK : (K:ℝ)+1≤7*(L+1) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hK (by positivity : 0≤ C*(L+1)^6)
  have hone : 1≤(L+1)^7 := one_le_pow₀ (by linarith)
  apply hn.trans
  have heq : (L+1)^7=(L+1)^6*(L+1) := by ring
  rw [heq] at hone ⊢
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszWeakHurwitzTheorem
namespace OAI

/-! Weak Hurwitz growth from the
Vinogradov-system moment proof and first-order Hurwitz cutoff. -/
namespace TwoPointCorrelations

open _root_.Filter _root_.Complex _root_.HurwitzZeta

theorem mrt_weak_hurwitz_growth_oai : MRTWeakHurwitzGrowthInput := by
  obtain ⟨A,hA,hgrowth⟩ := halasz_hurwitz_growth
  have hrsmall : ∀ᶠ x : ℝ in atTop, x^(-(2/3:ℝ))≤ 1/5 := by
    have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<2/3)).eventually
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1/5))
    exact hh.mono (fun _ hx => hx.le)
  obtain ⟨M₀,hM₀⟩ := eventually_atTop.1 hrsmall
  let B := max M₀ (max 100 (128*A))
  have hB100 : 100≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBA : 128*A≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hBM : M₀≤ B := le_max_left _ _
  refine ⟨8,Real.exp B+3,by norm_num,by positivity,?_⟩
  intro t ht a ha s hσ hσhi hsim
  let M := mrtVKLog t
  have hM : B≤ M := by
    have hh : Real.exp B≤|t|+3 := by linarith
    have hl := Real.log_le_log (Real.exp_pos B) hh
    simpa only [Real.log_exp,M,mrtVKLog] using hl
  have hM100 : 100≤ M := hB100.trans hM
  have hM0 : 0 < M := by linarith
  have hR : mrtVKRadius t≤ 1/5 := by
    change M^(-(2/3:ℝ))≤ 1/5
    exact hM₀ M (hBM.trans hM)
  have hR0 : 0 < mrtVKRadius t := by
    change 0 < M^(-(2/3:ℝ))
    exact Real.rpow_pos_of_pos hM0 _
  have hupper : |s.im|≤|t|+3 := by
    have hh : |s.im|≤|t|+|s.im-t| := by
      calc
        _ = |t+(s.im-t)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    linarith
  have hlower : Real.exp B≤|s.im| := by
    have hh : |t|≤|s.im|+|s.im-t| := by
      calc
        _ = |s.im+(t-s.im)| := by congr 1; ring
        _ ≤ |s.im|+|t-s.im| := abs_add_le _ _
        _ = _ := by rw [abs_sub_comm]
    linarith
  have him0 : 0 < |s.im| := (Real.exp_pos B).trans_le hlower
  let L := Real.log |s.im|
  have hL : B≤ L := by
    have hh := Real.log_le_log (Real.exp_pos B) hlower
    simpa only [Real.log_exp,L] using hh
  have hL100 : 100≤ L := hB100.trans hL
  have hL0 : 0 < L := by linarith
  have hLM : L≤ M := Real.log_le_log him0 hupper
  have hδ : max (1-s.re) 0≤4*L^(-(2/3:ℝ)) := by
    have hδR : max (1-s.re) 0≤ mrtVKRadius t := max_le_iff.mpr ⟨by linarith,hR0.le⟩
    have hRL : mrtVKRadius t≤ L^(-(2/3:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hL0 hLM (by norm_num)
    have hn : 0≤ L^(-(2/3:ℝ)) := Real.rpow_nonneg hL0.le _
    linarith
  have hg := hgrowth L hL100 a ha s (by linarith) (by linarith)
    (Real.exp_log him0).symm hδ
  apply hg.trans
  have hsize : L+1≤2*M := by linarith
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith : 0≤ L+1) hsize 7) (by linarith : 0≤ A)
  have hcoef : 128*A≤ M := hBA.trans hM
  have hm7 : 0≤ M^7 := pow_nonneg hM0.le _
  have hh := mul_le_mul_of_nonneg_right hcoef hm7
  change A*(L+1)^7≤ M^(8:ℝ)
  rw [Real.rpow_ofNat,show M^8=M^7*M from pow_succ M 7]
  norm_num only [mul_pow] at hp
  nlinarith

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_weak_hurwitz_growth_oai := @OAI.TwoPointCorrelations.mrt_weak_hurwitz_growth_oai
