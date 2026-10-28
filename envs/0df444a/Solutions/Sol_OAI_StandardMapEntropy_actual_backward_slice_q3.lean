-- Prove2me | solution 1 for OAI.StandardMapEntropy.actual_backward_slice_q3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T04:56:08.597481+00:00
-- url     : https://prove2.me/submissions/25840123-d467-43d2-a61f-e720c0f749ac

import Mathlib
import Definitions.Def_StandardMapLyapunov
import Definitions.Def_OAIQ3St000

section
-- module Solutions.OAIQ3_Std.StandardMap_LocalScarcity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

lemma hasDerivAt_phi (k x : ℝ) : HasDerivAt (phi k) (potential k x) x := by
  have hs : HasDerivAt (fun y : ℝ => Real.sin (2 * Real.pi * y))
      (Real.cos (2 * Real.pi * x) * (2 * Real.pi)) x := by
    simpa using ((hasDerivAt_id x).const_mul (2 * Real.pi)).sin
  have hl : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  convert! hl.add (hs.const_mul k) using 1
  unfold potential
  ring

lemma linearSolution_step (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    linearSolution v a b (n + 2) =
      v (n + 1) * linearSolution v a b (n + 1) - linearSolution v a b n := rfl

lemma linearSolution_decomposition (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    linearSolution v a b n = a * sSolution v n + b * tSolution v n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [sSolution, tSolution]
  | one => simp [sSolution, tSolution]
  | more n h₀ h₁ =>
    rw [linearSolution_step, h₀, h₁]
    dsimp only [sSolution, tSolution] at *
    rw [linearSolution_step, linearSolution_step]
    ring

theorem solution_wronskian (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    linearSolution v a b n * tSolution v (n + 1) -
      linearSolution v a b (n + 1) * tSolution v n = a := by
  induction n with
  | zero => simp [tSolution]
  | succ n ih =>
    change linearSolution v a b (n + 1) * tSolution v (n + 2) -
      linearSolution v a b (n + 2) * tSolution v (n + 1) = a
    simp only [tSolution, linearSolution_step] at *
    nlinarith only [ih]

lemma boundaryValue_vanishes (v : ℕ → ℝ) (j : ℕ) (hj : tSolution v j ≠ 0) :
    linearSolution v 1 (boundaryValue v j) j = 0 := by
  rw [linearSolution_decomposition]
  simp [boundaryValue, hj]

lemma boundaryValue_unique (v : ℕ → ℝ) (j : ℕ) (hj : tSolution v j ≠ 0)
    (b : ℝ) (hb : linearSolution v 1 b j = 0) : b = boundaryValue v j := by
  rw [linearSolution_decomposition] at hb
  apply (eq_div_iff hj).mpr
  linarith

lemma liftedOrbit_step (k q₀ q₁ : ℝ) (n : ℕ) :
    liftedOrbit k q₀ q₁ (n + 2) =
      phi k (liftedOrbit k q₀ q₁ (n + 1)) - liftedOrbit k q₀ q₁ n := rfl

lemma dirichletSolution_zero (v : ℕ → ℝ) (j : ℕ) :
    dirichletSolution v j 0 = 1 := rfl

lemma dirichletSolution_boundary (v : ℕ → ℝ) (j : ℕ) (hj : tSolution v j ≠ 0) :
    dirichletSolution v j j = 0 := boundaryValue_vanishes v j hj

lemma dirichletSolution_step (v : ℕ → ℝ) (j n : ℕ) :
    dirichletSolution v j (n + 2) =
      v (n + 1) * dirichletSolution v j (n + 1) - dirichletSolution v j n := rfl

lemma greenKernel_zero (v : ℕ → ℝ) (j b : ℕ) : greenKernel v j 0 b = 0 := by
  simp [greenKernel, tSolution]

lemma greenKernel_boundary (v : ℕ → ℝ) (j b : ℕ)
    (hj : tSolution v j ≠ 0) (hb : b ≤ j) : greenKernel v j j b = 0 := by
  simp only [greenKernel, max_eq_left hb, dirichletSolution_boundary v j hj, mul_zero]

theorem greenKernel_jump (v : ℕ → ℝ) (j a b : ℕ) :
    v (a + 1) * greenKernel v j (a + 1) b -
      greenKernel v j a b - greenKernel v j (a + 2) b =
      if a + 1 = b then 1 else 0 := by
  rcases lt_trichotomy (a + 1) b with hab | hab | hab
  · have ha : a ≤ b := by omega
    have ha₁ : a + 1 ≤ b := by omega
    have ha₂ : a + 2 ≤ b := by omega
    simp only [greenKernel, min_eq_left ha, max_eq_right ha,
      min_eq_left ha₁, max_eq_right ha₁, min_eq_left ha₂, max_eq_right ha₂,
      ite_eq_right (ne_of_lt hab)]
    change v (a + 1) * (tSolution v (a + 1) * dirichletSolution v j b) -
      tSolution v a * dirichletSolution v j b -
      (v (a + 1) * tSolution v (a + 1) - tSolution v a) * dirichletSolution v j b = 0
    ring
  · subst b
    rw [ite_eq_left rfl]
    have ha : a ≤ a + 1 := by omega
    have ha₂ : a + 1 ≤ a + 2 := by omega
    simp only [greenKernel, min_self, max_self, min_eq_left ha, max_eq_right ha,
      min_eq_right ha₂, max_eq_left ha₂]
    have hw := solution_wronskian v 1 (boundaryValue v j) (a + 1)
    change dirichletSolution v j (a + 1) *
      (v (a + 1) * tSolution v (a + 1) - tSolution v a) -
      dirichletSolution v j (a + 2) * tSolution v (a + 1) = 1 at hw
    nlinarith only [hw]
  · have ha : b ≤ a := by omega
    have ha₁ : b ≤ a + 1 := by omega
    have ha₂ : b ≤ a + 2 := by omega
    simp only [greenKernel, min_eq_right ha, max_eq_left ha,
      min_eq_right ha₁, max_eq_left ha₁, min_eq_right ha₂, max_eq_left ha₂,
      ite_eq_right (ne_of_gt hab), dirichletSolution_step]
    ring

lemma potential_lipschitz (k x y : ℝ) (hk : 0 ≤ k) :
    |potential k y - potential k x| ≤ (2 * Real.pi * growthBase k) * |y - x| := by
  have hK : 0 ≤ 2 * Real.pi * k := by positivity
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hid : potential k y - potential k x =
      (2 * Real.pi * k) * (Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * x)) := by
    unfold potential
    ring
  rw [hid, abs_mul, abs_of_nonneg hK]
  have hdiff : |2 * Real.pi * y - 2 * Real.pi * x| = (2 * Real.pi) * |y - x| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hπ]
  calc
    (2 * Real.pi * k) * |Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * x)| ≤
        (2 * Real.pi * k) * ((2 * Real.pi) * |y - x|) := by
      apply mul_le_mul_of_nonneg_left _ hK
      rw [← hdiff]
      exact Real.abs_cos_sub_cos_le _ _
    _ ≤ (2 * Real.pi * growthBase k) * |y - x| := by
      have h : 2 * Real.pi * k ≤ growthBase k := by unfold growthBase; linarith
      have h' := mul_le_mul_of_nonneg_right h (mul_nonneg hπ (abs_nonneg (y - x)))
      nlinarith only [h']

lemma hasDerivAt_potential (k x : ℝ) : HasDerivAt (potential k) (phiSecond k x) x := by
  have h := (hasDerivAt_const x (2 : ℝ)).add
    ((((hasDerivAt_id x).const_mul (2 * Real.pi)).cos).const_mul (2 * Real.pi * k))
  convert! h using 1
  simp only [id_eq]
  unfold phiSecond
  ring

lemma phiSecond_bound (k x : ℝ) (hk : 0 ≤ k) : |phiSecond k x| ≤ 2 * Real.pi * growthBase k := by
  have hM : 2 * Real.pi * k ≤ growthBase k := by unfold growthBase; linarith
  have hsin := Real.abs_sin_le_one (2 * Real.pi * x)
  have h₁ := mul_le_mul_of_nonneg_left hsin (show 0 ≤ (2 * Real.pi) ^ 2 * k by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hM (show 0 ≤ 2 * Real.pi by positivity)
  unfold phiSecond
  rw [abs_mul, abs_mul, abs_neg, abs_pow, abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_of_nonneg hk]
  nlinarith only [h₁, h₂]

open scoped Matrix.Norms.Operator

open Filter
open scoped Topology

open Metric

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_TransferCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma transferProduct_pair (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    transferProduct v n ⟨b,a⟩ = ⟨linearSolution v a b (n+1),linearSolution v a b n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [transferProduct,ContinuousLinearMap.comp_apply,ih]
    apply Complex.ext <;> simp only [transferStep_re,transferStep_im,linearSolution_step]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_LiftDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma liftIter_add (k : ℝ) (i j : ℤ) (z : ℝ × ℝ) :
    liftIter k (i+j) z=liftIter k i (liftIter k j z) := by
  simp only [liftIter,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
lemma liftIter_nat (k : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    liftIter k n z=(liftedOrbit k z.2 z.1 (n+1),liftedOrbit k z.2 z.1 n) := by
  induction n with
  | zero => simp [liftIter,liftedOrbit]
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,add_comm,liftIter_add,ih]
    simp only [liftIter,zpow_one]
    change (phi k (liftedOrbit k z.2 z.1 (n+1))-liftedOrbit k z.2 z.1 n,
      liftedOrbit k z.2 z.1 (n+1))=_
    rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_NonlinearDirichlet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma phi_remainder_lipschitz (k x u v R : ℝ) (hk : 0 ≤ k) (hu : |u| ≤ R) (hv : |v| ≤ R) :
    |(phi k (x+u)-phi k x-potential k x*u)-
      (phi k (x+v)-phi k x-potential k x*v)| ≤
      (2*Real.pi*growthBase k)*R*|u-v| := by
  let f := fun z => phi k (x+z)-phi k x-potential k x*z
  have hd' (z : ℝ) : HasDerivAt f (potential k (x+z)-potential k x) z := by
    have hh:=((hasDerivAt_phi k (x+z)).comp z ((hasDerivAt_const z x).add (hasDerivAt_id z))).sub_const (phi k x)
    have hh':=hh.sub ((hasDerivAt_id z).const_mul (potential k x))
    convert! hh' using 1; simp
  have hC : 0 ≤ 2*Real.pi*growthBase k := by have := growthBase_ge_four k hk; positivity
  have hf:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := fun z => potential k (x+z)-potential k x)
    (s := uIcc v u) (C := (2*Real.pi*growthBase k)*R)
    (fun z _ => (hd' z).hasDerivWithinAt)
    (by
      intro z hz
      rw [Real.norm_eq_abs]
      have hzR : |z| ≤ R := by
        have hmin : -R ≤ min v u := le_min (abs_le.mp hv).1 (abs_le.mp hu).1
        have hmax : max v u ≤ R := max_le (abs_le.mp hv).2 (abs_le.mp hu).2
        exact abs_le.mpr ⟨hmin.trans hz.1,hz.2.trans hmax⟩
      calc
        _ ≤ (2*Real.pi*growthBase k)*|x+z-x| := potential_lipschitz k x (x+z) hk
        _ ≤ _ := by simpa only [add_sub_cancel_left] using mul_le_mul_of_nonneg_left hzR hC)
    (convex_uIcc v u) left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs,f] using hf

lemma finite_weighted_dirichlet {ι : Type*} [Fintype ι]
    (w U : ι → ℝ) (G : ι → ι → ℝ) (F : ι → ℝ → ℝ) (L : ι → ℝ) (r R : ℝ)
    (hw : ∀ i, 0 < w i) (hR : 0 ≤ R) (hL : ∀ i, 0 ≤ L i)
    (hzero : ∀ i, F i 0=0)
    (hLip : ∀ i x y, |x| ≤ R/w i → |y| ≤ R/w i → |F i x-F i y| ≤ L i*|x-y|)
    (hlin : ∀ i, |w i*U i*r| ≤ R/2)
    (hrow : ∀ i, ∑ j, |w i*G i j| *L j/w j ≤ 1/2) :
    ∃ ξ : ι → ℝ, (∀ i, |ξ i| ≤ R/w i) ∧
      ∀ i, ξ i=U i*r+∑ j, G i j*F j (ξ j) := by
  classical
  let T : (ι → ℝ) → (ι → ℝ) := fun X i => w i*U i*r+∑ j, w i*G i j*F j (X j/w j)
  have hcoord (X : ι → ℝ) (hX : ‖X‖ ≤ R) (i : ι) : |X i/w i| ≤ R/w i := by
    rw [abs_div,abs_of_pos (hw i)]
    exact div_le_div_of_nonneg_right (((norm_le_pi_norm X i)).trans hX) (hw i).le
  have hdiff (X Y : ι → ℝ) (hX : ‖X‖ ≤ R) (hY : ‖Y‖ ≤ R) : ‖T X-T Y‖ ≤ (1/2)*‖X-Y‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have hc (j : ι) : |X j/w j-Y j/w j| ≤ ‖X-Y‖/w j := by
      rw [← sub_div,abs_div,abs_of_pos (hw j)]
      exact div_le_div_of_nonneg_right (norm_le_pi_norm (X-Y) j) (hw j).le
    calc
      ‖(T X-T Y) i‖ = |∑ j, w i*G i j*(F j (X j/w j)-F j (Y j/w j))| := by
        simp only [Pi.sub_apply,T,Real.norm_eq_abs,add_sub_add_left_eq_sub,← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ j, |w i*G i j| *|F j (X j/w j)-F j (Y j/w j)| := by
        simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => w i*G i j*(F j (X j/w j)-F j (Y j/w j))) Finset.univ
      _ ≤ ∑ j, |w i*G i j| *(L j*(‖X-Y‖/w j)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left ((hLip j _ _ (hcoord X hX j) (hcoord Y hY j)).trans
          (mul_le_mul_of_nonneg_left (hc j) (hL j))) (abs_nonneg _)
      _ = (∑ j, |w i*G i j| *L j/w j)*‖X-Y‖ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)
  have hT0 : ‖T 0‖ ≤ R/2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    simpa only [T,Pi.zero_apply,zero_div,hzero,mul_zero,Finset.sum_const_zero,add_zero,Real.norm_eq_abs] using hlin i
  have hmaps : MapsTo T (closedBall (0:(ι→ℝ)) R) (closedBall 0 R) := by
    intro X hX
    rw [mem_closedBall_zero_iff] at hX ⊢
    have hd:=hdiff X 0 hX (by simpa using hR)
    have htri:=norm_le_norm_sub_add (T X) (T 0)
    simp only [sub_zero] at hd
    nlinarith
  have hcont : ContractingWith (1/2:NNReal) (hmaps.restrict T (closedBall 0 R) (closedBall 0 R)) := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro X Y
      have hh:=hdiff X Y (mem_closedBall_zero_iff.mp X.property) (mem_closedBall_zero_iff.mp Y.property)
      change ‖T (X : ι → ℝ)-T (Y : ι → ℝ)‖ ≤ (↑(1/2:NNReal):ℝ)*‖(X : ι → ℝ)-(Y : ι → ℝ)‖
      simpa only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using hh
  obtain ⟨X,hX,hfix,_,_⟩:=hcont.exists_fixedPoint' isClosed_closedBall.isComplete hmaps
    (x := (0:ι→ℝ)) (by simpa using hR) (edist_ne_top _ _)
  have hXnorm : ‖X‖ ≤ R := by simpa using hX
  refine ⟨fun i => X i/w i,fun i => hcoord X hXnorm i,?_⟩
  intro i
  have hh:=congrFun hfix i
  dsimp [T] at hh
  apply (div_eq_iff (hw i).ne').mpr
  rw [← hh]
  rw [add_mul,Finset.sum_mul]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma weighted_green_exponent (l p : ℕ) :
    (4/5:ℝ)*((l:ℝ)+1)+(min l p:ℕ)-(9/10)*((max l p:ℕ)+1)+1-
      (8/5)*((p:ℝ)+1) ≤ -(1/10)-(3/5)*((p:ℝ)+1) := by
  have hl : (0:ℝ) ≤ l := Nat.cast_nonneg _
  have hp : (0:ℝ) ≤ p := Nat.cast_nonneg _
  rcases le_total l p with h|h
  · rw [min_eq_left h,max_eq_right h]
    have hh : (l:ℝ) ≤ p := by exact_mod_cast h
    linarith
  · rw [min_eq_right h,max_eq_left h]
    linarith
lemma finite_green_weight_sum (M : ℝ) (hM : 1 < M) (hq : M^(-(3/5:ℝ)) ≤ 1/2) (n : ℕ) :
    ∑ i : Fin n, M^(-(1/10:ℝ)-(3/5)*((i:ℝ)+1)) ≤ 2*M^(-(7/10:ℝ)) := by
  have hp : 0 < M := by linarith
  have he (i : Fin n) : M^(-(1/10:ℝ)-(3/5)*((i:ℝ)+1)) =
      M^(-(7/10:ℝ))*(M^(-(3/5:ℝ)))^(i:ℕ) := by
    rw [← Real.rpow_mul_natCast hp.le,← Real.rpow_add hp]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range]
  have hs : ∑ i ∈ Finset.range n, (M^(-(3/5:ℝ)))^i ≤ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (1/2:ℝ)^i := by gcongr
      _ ≤ 2 := sum_geometric_two_le n
  nlinarith [Real.rpow_pos_of_pos hp (-(7/10:ℝ))]

lemma green_weighted_rows (M C R : ℝ) (n : ℕ) (t U : ℕ → ℝ)
    (hM : 1 < M) (hC : 0 ≤ C) (hR : 0 ≤ R) (hq : M^(-(3/5:ℝ)) ≤ 1/2)
    (ht : ∀ p, 1 ≤ p → p ≤ n → |t p| ≤ M^((p:ℝ)-1))
    (hU : ∀ p, 1 ≤ p → p ≤ n → |U p| ≤ C*M^(-(9/10:ℝ)*(p:ℝ))) :
    ∀ i : Fin n,
      ∑ j : Fin n,
        |M^((4/5:ℝ)*((i:ℝ)+1))*(t (min (i:ℕ) (j:ℕ)+1)*U (max (i:ℕ) (j:ℕ)+1))| *
          ((2*Real.pi*M)*R/M^((4/5:ℝ)*((j:ℝ)+1)))/M^((4/5:ℝ)*((j:ℝ)+1)) ≤
        (4*Real.pi*C*R)*M^(-(7/10:ℝ)) := by
  have hp : 0 < M := by linarith
  intro i
  calc
    _ ≤ ∑ j : Fin n, (2*Real.pi*C*R)*M^(-(1/10:ℝ)-(3/5)*((j:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hmin : min (i:ℕ) (j:ℕ)+1 ≤ n := by have:=min_le_left (i:ℕ) (j:ℕ); omega
      have hmax : max (i:ℕ) (j:ℕ)+1 ≤ n := by omega
      have ht' := ht _ (by omega) hmin
      have hU' := hU _ (by omega) hmax
      rw [abs_mul,abs_of_pos (Real.rpow_pos_of_pos hp _),abs_mul]
      calc
        _ ≤ M^((4/5:ℝ)*((i:ℝ)+1))*(M^((min (i:ℕ) (j:ℕ):ℝ))*(C*M^(-(9/10:ℝ)*((max (i:ℕ) (j:ℕ):ℝ)+1)))) *
          ((2*Real.pi*M)*R/M^((4/5:ℝ)*((j:ℝ)+1)))/M^((4/5:ℝ)*((j:ℝ)+1)) := by
            gcongr
            · simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Nat.cast_min] using ht'
            · simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_max] using hU'
        _ = (2*Real.pi*C*R)*M^((4/5:ℝ)*((i:ℝ)+1)+(min (i:ℕ) (j:ℕ):ℝ)-
            (9/10)*((max (i:ℕ) (j:ℕ):ℝ)+1)+1-(8/5)*((j:ℝ)+1)) := by
          rw [show (4/5:ℝ)*((i:ℝ)+1)+(min (i:ℕ) (j:ℕ):ℝ)-
            (9/10)*((max (i:ℕ) (j:ℕ):ℝ)+1)+1-(8/5)*((j:ℝ)+1) =
            ((4/5:ℝ)*((i:ℝ)+1)+(min (i:ℕ) (j:ℕ):ℝ)+
            (-(9/10)*((max (i:ℕ) (j:ℕ):ℝ)+1))+1)-
            ((4/5)*((j:ℝ)+1)+(4/5)*((j:ℝ)+1)) by ring]
          rw [Real.rpow_sub hp]
          simp only [Real.rpow_add hp,Real.rpow_one]
          ring

        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hM.le (by simpa only [Nat.cast_min,Nat.cast_max] using weighted_green_exponent i j)) (by positivity)
    _ = (2*Real.pi*C*R)*∑ j : Fin n, M^(-(1/10:ℝ)-(3/5)*((j:ℝ)+1)) := by rw [Finset.mul_sum]
    _ ≤ (2*Real.pi*C*R)*(2*M^(-(7/10:ℝ))) :=
      mul_le_mul_of_nonneg_left (finite_green_weight_sum M hM hq n) (by positivity)
    _ = _ := by ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeNonlinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma tSolution_abs_le_pow (v : ℕ → ℝ) (M : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (hM : 1 ≤ M) (hv : ∀ i, 1 ≤ i → i < p → |v i|+1 ≤ M) :
    |tSolution v p| ≤ M^((p:ℝ)-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have hh := (transferProduct_norm_bounds v M n (by linarith)
    (fun i hi hin => hv i hi (by omega))).2
  have hp := (transferProduct v n).le_opNorm (1:ℂ)
  have he : (transferProduct v n 1).re=tSolution v (n+1) := by
    change (transferProduct v n ⟨1,0⟩).re=tSolution v (n+1)
    rw [transferProduct_pair]; rfl
  calc
    _ = |(transferProduct v n 1).re| := congrArg abs he.symm
    _ ≤ ‖transferProduct v n 1‖ := Complex.abs_re_le_norm _
    _ ≤ M^n := by simpa only [norm_one,mul_one] using hp.trans (by simpa using hh)
    _ = _ := by simp only [Nat.cast_succ,add_sub_cancel_right,Real.rpow_natCast]

lemma nonlinear_dirichlet_fixedPoint (k q a r : ℝ) (n : ℕ)
    (hk : 0 ≤ k) (hr : |r| ≤ 1/4)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (hU : ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k q a) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
    ∃ ξ : Fin n → ℝ,
      (∀ i, |ξ i| ≤ 8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) ∧
      ∀ i, ξ i=dirichletSolution (orbitCoefficient k q a) (n+1) (i+1)*r+
        ∑ j, greenMatrix (orbitCoefficient k q a) n i j *
          (-(phi k (liftedOrbit k q a (j+1)+ξ j)-phi k (liftedOrbit k q a (j+1))-
            potential k (liftedOrbit k q a (j+1))*ξ j)) := by
  let M := growthBase k
  have hMm : 4 ≤ M := growthBase_ge_four k hk
  have hm : 1 < M := by linarith
  have hp : 0 < M := by linarith
  let w : Fin n → ℝ := fun i => M^((4/5:ℝ)*((i:ℝ)+1))
  let U : Fin n → ℝ := fun i => dirichletSolution (orbitCoefficient k q a) (n+1) (i+1)
  let F : Fin n → ℝ → ℝ := fun j z => -(phi k (liftedOrbit k q a (j+1)+z)-
    phi k (liftedOrbit k q a (j+1))-potential k (liftedOrbit k q a (j+1))*z)
  let L : Fin n → ℝ := fun i => (2*Real.pi*M)*8/w i
  have hw (i : Fin n) : 0 < w i := Real.rpow_pos_of_pos hp _
  have hlin (i : Fin n) : |w i*U i*r| ≤ (8:ℝ)/2 := by
    have hU':=hU (i+1) (by omega) (by omega)
    have hexp : M^((4/5:ℝ)*((i:ℝ)+1))*M^(-(9/10:ℝ)*((i:ℝ)+1)) ≤ 1 := by
      rw [← Real.rpow_add hp]
      exact Real.rpow_le_one_of_one_le_of_nonpos hm.le (by have : (0:ℝ) ≤ (i:ℕ) := Nat.cast_nonneg _; linarith)
    rw [abs_mul,abs_mul,abs_of_pos (hw i)]
    calc
      _ ≤ w i*(12*M^(-(9/10:ℝ)*((i:ℝ)+1)))*(1/4) := by
        gcongr
        simpa only [U,Nat.cast_add,Nat.cast_one] using hU'
      _ ≤ 3 := by dsimp only [w]; nlinarith
      _ ≤ _ := by norm_num
  have hrow (i : Fin n) : ∑ j, |w i*greenMatrix (orbitCoefficient k q a) n i j| *L j/w j ≤ 1/2 := by
    have hh:=green_weighted_rows M 12 8 n (tSolution (orbitCoefficient k q a))
      (dirichletSolution (orbitCoefficient k q a) (n+1)) hm (by norm_num) (by norm_num) hq
      (fun p hp' hn => tSolution_abs_le_pow _ M p hp' hm.le
        (fun i hi hip => potential_bound k (liftedOrbit k q a i) hk)) hU i
    have he : ∀ i j : Fin n, greenMatrix (orbitCoefficient k q a) n i j=
        tSolution (orbitCoefficient k q a) (min (i:ℕ) (j:ℕ)+1)*
        dirichletSolution (orbitCoefficient k q a) (n+1) (max (i:ℕ) (j:ℕ)+1) := by
      intro i j
      simp only [greenMatrix,greenKernel,min_add_add_right,max_add_add_right]
    simp_rw [he]
    exact hh.trans (by nlinarith only [hsmall])
  exact finite_weighted_dirichlet w U (greenMatrix (orbitCoefficient k q a) n) F L r 8 hw
    (by norm_num) (fun i => by dsimp [L]; positivity)
    (by intro i; simp [F])
    (by
      intro i x y hx hy
      dsimp only [F]
      rw [← neg_sub,abs_neg]
      have hh:=phi_remainder_lipschitz k (liftedOrbit k q a (i+1)) x y (8/w i) hk hx hy
      dsimp only [L,M]
      convert hh using 1 <;> ring_nf)
    hlin hrow
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_DirichletOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma green_convolution_jump (v : ℕ → ℝ) (n l : ℕ) (hl : l < n) (F : Fin n → ℝ) :
    v (l+1)*(∑ j : Fin n, greenKernel v (n+1) (l+1) (j+1)*F j)-
      (∑ j : Fin n, greenKernel v (n+1) l (j+1)*F j)-
      (∑ j : Fin n, greenKernel v (n+1) (l+2) (j+1)*F j)=F ⟨l,hl⟩ := by
  classical
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : Fin n, (if l+1=(j:ℕ)+1 then 1 else 0)*F j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← greenKernel_jump v (n+1) l (j+1)]
      ring
    _ = _ := by
      rw [Finset.sum_eq_single (⟨l,hl⟩:Fin n)]
      · simp
      · intro j hj hjl
        have hne : l ≠ (j:ℕ) := by
          intro hh
          apply hjl
          apply Fin.ext
          exact hh.symm
        simp [hne]
      · simp

lemma nonlinear_fixedPoint_orbit (k q a r : ℝ) (n : ℕ)
    (ht : tSolution (orbitCoefficient k q a) (n+1) ≠ 0)
    (ζ : Fin n → ℝ)
    (hζ : ∀ i, ζ i=dirichletSolution (orbitCoefficient k q a) (n+1) (i+1)*r+
        ∑ j, greenMatrix (orbitCoefficient k q a) n i j *
          (-(phi k (liftedOrbit k q a (j+1)+ζ j)-phi k (liftedOrbit k q a (j+1))-
            potential k (liftedOrbit k q a (j+1))*ζ j))) :
    ∃ b : ℝ, liftedOrbit k (q+r) b (n+1)=liftedOrbit k q a (n+1) ∧
      ∀ i : Fin n, liftedOrbit k (q+r) b (i+1)-liftedOrbit k q a (i+1)=ζ i := by
  let v:=orbitCoefficient k q a
  let U:=dirichletSolution v (n+1)
  let F : Fin n → ℝ := fun j => -(phi k (liftedOrbit k q a (j+1)+ζ j)-phi k (liftedOrbit k q a (j+1))-
            potential k (liftedOrbit k q a (j+1))*ζ j)
  let ξ : ℕ → ℝ := fun p => U p*r+∑ j : Fin n, greenKernel v (n+1) p (j+1)*F j
  have hξ (i : Fin n) : ξ (i+1)=ζ i := (hζ i).symm
  have hξ0 : ξ 0=r := by simp only [ξ,U,dirichletSolution_zero,greenKernel_zero,zero_mul,Finset.sum_const_zero,one_mul,add_zero]
  have hξn : ξ (n+1)=0 := by
    simp only [ξ,U,dirichletSolution_boundary v (n+1) ht,zero_mul,zero_add]
    apply Finset.sum_eq_zero
    intro j hj
    rw [greenKernel_boundary v (n+1) (j+1) ht (by omega),zero_mul]
  have hstep (l : ℕ) (hl : l<n) :
      liftedOrbit k q a (l+2)+ξ (l+2)=
        phi k (liftedOrbit k q a (l+1)+ξ (l+1))-(liftedOrbit k q a l+ξ l) := by
    have hG:=green_convolution_jump v n l hl F
    have hU:=dirichletSolution_step v (n+1) l
    have hζ':=hξ (⟨l,hl⟩:Fin n)
    change U (l+2)=v (l+1)*U (l+1)-U l at hU
    have hlin : v (l+1)*ξ (l+1)-ξ l-ξ (l+2)=F ⟨l,hl⟩ := by
      dsimp only [ξ]
      linear_combination hG - r*hU
    dsimp only [F] at hlin
    rw [← hζ'] at hlin
    change potential k (liftedOrbit k q a (l+1))*ξ (l+1)-ξ l-ξ (l+2)=
      -(phi k (liftedOrbit k q a (l+1)+ξ (l+1))-phi k (liftedOrbit k q a (l+1))-
        potential k (liftedOrbit k q a (l+1))*ξ (l+1)) at hlin
    rw [liftedOrbit_step]
    linarith
  have horb : ∀ p, p ≤ n+1 → liftedOrbit k (q+r) (a+ξ 1) p=liftedOrbit k q a p+ξ p := by
    intro p
    induction p using Nat.twoStepInduction with
    | zero => intro hp; simp [liftedOrbit,hξ0]
    | one => intro hp; rfl
    | more p ih0 ih1 =>
      intro hp
      rw [liftedOrbit_step,ih0 (by omega),ih1 (by omega)]
      exact (hstep p (by omega)).symm
  refine ⟨a+ξ 1,?_,?_⟩
  · simpa only [hξn,add_zero] using horb (n+1) le_rfl
  · intro i
    rw [horb (i+1) (by omega),add_sub_cancel_left,hξ i]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_WeightedStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma weighted_convolution_difference {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (G : ι → ι → ℝ) (F : ι → ℝ → ℝ) (L ξ ζ : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hL : ∀ i, 0 ≤ L i)
    (hLip : ∀ i, |F i (ξ i)-F i (ζ i)| ≤ L i*|ξ i-ζ i|)
    (hrow : ∀ i, ∑ j, |w i*G i j| *L j/w j ≤ 1/2) :
    ‖fun i => ∑ j, w i*G i j*(F j (ξ j)-F j (ζ j))‖ ≤
      (1/2)*‖fun i => w i*(ξ i-ζ i)‖ := by
  classical
  let N := ‖fun i => w i*(ξ i-ζ i)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hc (j : ι) : |ξ j-ζ j| ≤ N/w j := by
    apply (le_div_iff₀ (hw j)).mpr
    have hh:=norm_le_pi_norm (fun i => w i*(ξ i-ζ i)) j
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (hw j),mul_comm] using hh
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    _ ≤ ∑ j, |w i*G i j| *|F j (ξ j)-F j (ζ j)| := by
      simpa only [Real.norm_eq_abs,abs_mul] using Finset.abs_sum_le_sum_abs
        (fun j => w i*G i j*(F j (ξ j)-F j (ζ j))) Finset.univ
    _ ≤ ∑ j, |w i*G i j| *(L j*(N/w j)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left ((hLip j).trans
        (mul_le_mul_of_nonneg_left (hc j) (hL j))) (abs_nonneg _)
    _ = (∑ j, |w i*G i j| *L j/w j)*N := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) hN
lemma weighted_fixedPoint_stability {ι : Type*} [Fintype ι]
    (w U : ι → ℝ) (G : ι → ι → ℝ) (F : ι → ℝ → ℝ) (L ξ ζ : ι → ℝ) (r s C : ℝ)
    (hw : ∀ i, 0 < w i) (hL : ∀ i, 0 ≤ L i)
    (hLip : ∀ i, |F i (ξ i)-F i (ζ i)| ≤ L i*|ξ i-ζ i|)
    (hrow : ∀ i, ∑ j, |w i*G i j| *L j/w j ≤ 1/2)
    (hU : ‖fun i => w i*U i‖ ≤ C)
    (hξ : ∀ i, ξ i=U i*r+∑ j, G i j*F j (ξ j))
    (hζ : ∀ i, ζ i=U i*s+∑ j, G i j*F j (ζ j)) :
    ‖fun i => w i*(ξ i-ζ i)‖ ≤ 2*C*|r-s| := by
  classical
  have hnl:=weighted_convolution_difference w G F L ξ ζ hw hL hLip hrow
  have he : (fun i => w i*(ξ i-ζ i)) =
      (fun i => (r-s)*(w i*U i))+(fun i => ∑ j, w i*G i j*(F j (ξ j)-F j (ζ j))) := by
    funext i
    rw [hξ i,hζ i]
    simp only [Pi.add_apply,mul_add,mul_sub,Finset.mul_sum,Finset.sum_sub_distrib,mul_assoc]
    ring
  have hlin : ‖fun i => (r-s)*(w i*U i)‖ ≤ C*|r-s| := by
    calc
      _ = |r-s| *‖fun i => w i*U i‖ := by
        change ‖(r-s) • (fun i => w i*U i)‖= _
        rw [norm_smul,Real.norm_eq_abs]
      _ ≤ _ := by nlinarith [abs_nonneg (r-s)]
  have ht:=norm_add_le (fun i => (r-s)*(w i*U i))
    (fun i => ∑ j, w i*G i j*(F j (ξ j)-F j (ζ j)))
  rw [← he] at ht
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_VariedDirichlet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma linear_fixedPoint_dirichlet (v v' : ℕ → ℝ) (n : ℕ)
    (ht : tSolution v (n+1) ≠ 0) (ζ : Fin n → ℝ)
    (hζ : ∀ i, ζ i=dirichletSolution v (n+1) (i+1)+
      ∑ j, greenMatrix v n i j*((v (j+1)-v' (j+1))*ζ j)) :
    tSolution v' (n+1) ≠ 0 ∧ ∀ i : Fin n, dirichletSolution v' (n+1) (i+1)=ζ i := by
  let U:=dirichletSolution v (n+1)
  let F : Fin n → ℝ := fun j => (v (j+1)-v' (j+1))*ζ j
  let ξ : ℕ → ℝ := fun p => U p+∑ j : Fin n, greenKernel v (n+1) p (j+1)*F j
  have hξ (i : Fin n) : ξ (i+1)=ζ i := (hζ i).symm
  have hξ0 : ξ 0=1 := by simp only [ξ,U,dirichletSolution_zero,greenKernel_zero,zero_mul,Finset.sum_const_zero,add_zero]
  have hξn : ξ (n+1)=0 := by
    simp only [ξ,U,dirichletSolution_boundary v (n+1) ht,zero_add]
    apply Finset.sum_eq_zero
    intro j hj
    rw [greenKernel_boundary v (n+1) (j+1) ht (by omega),zero_mul]
  have hstep (l : ℕ) (hl : l<n) : ξ (l+2)=v' (l+1)*ξ (l+1)-ξ l := by
    have hG:=green_convolution_jump v n l hl F
    have hU:=dirichletSolution_step v (n+1) l
    have hζ':=hξ (⟨l,hl⟩:Fin n)
    change U (l+2)=v (l+1)*U (l+1)-U l at hU
    have hlin : v (l+1)*ξ (l+1)-ξ l-ξ (l+2)=F ⟨l,hl⟩ := by
      dsimp only [ξ]
      linear_combination hG - hU
    dsimp only [F] at hlin
    rw [← hζ'] at hlin
    nlinarith only [hlin]
  have hsol : ∀ p, p ≤ n+1 → linearSolution v' 1 (ξ 1) p=ξ p := by
    intro p
    induction p using Nat.twoStepInduction with
    | zero => intro hp; exact hξ0.symm
    | one => intro hp; rfl
    | more p ih0 ih1 =>
      intro hp
      rw [linearSolution_step,ih0 (by omega),ih1 (by omega)]
      exact (hstep p (by omega)).symm
  have hterm : linearSolution v' 1 (ξ 1) (n+1)=0 := (hsol _ le_rfl).trans hξn
  have ht' : tSolution v' (n+1) ≠ 0 := by
    have hh:=solution_wronskian v' 1 (ξ 1) n
    rw [hterm,zero_mul,sub_zero] at hh
    intro hz
    rw [hz,mul_zero] at hh
    norm_num at hh
  have hb : ξ 1=boundaryValue v' (n+1) := boundaryValue_unique v' (n+1) ht' (ξ 1) hterm
  refine ⟨ht',?_⟩
  intro i
  have he:=hsol (i+1) (by omega)
  rw [hb] at he
  exact he.trans (hξ i)

lemma varied_dirichlet_bound (v v' : ℕ → ℝ) (M : ℝ) (n : ℕ)
    (hM : 1 < M) (hq : M^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*M^(-(7/10:ℝ)) ≤ 1/2)
    (ht : tSolution v (n+1) ≠ 0)
    (hv : ∀ p, 1 ≤ p → p ≤ n → |tSolution v p| ≤ M^((p:ℝ)-1))
    (hU : ∀ p, 1 ≤ p → p ≤ n → |dirichletSolution v (n+1) p| ≤ 12*M^(-(9/10:ℝ)*(p:ℝ)))
    (hdiff : ∀ i : Fin n, |v (i+1)-v' (i+1)| ≤ (2*Real.pi*M)*8/M^((4/5:ℝ)*((i:ℝ)+1))) :
    tSolution v' (n+1) ≠ 0 ∧ ∀ i : Fin n,
      |dirichletSolution v' (n+1) (i+1)| ≤ 24/M^((4/5:ℝ)*((i:ℝ)+1)) := by
  have hp : 0 < M := by linarith
  let w : Fin n → ℝ := fun i => M^((4/5:ℝ)*((i:ℝ)+1))
  let U : Fin n → ℝ := fun i => dirichletSolution v (n+1) (i+1)
  let L : Fin n → ℝ := fun i => (2*Real.pi*M)*8/w i
  let F : Fin n → ℝ → ℝ := fun i x => (v (i+1)-v' (i+1))*x
  have hw (i : Fin n) : 0 < w i := Real.rpow_pos_of_pos hp _
  have hlin (i : Fin n) : |w i*U i*1| ≤ (24:ℝ)/2 := by
    have hU':=hU (i+1) (by omega) (by omega)
    have hexp : M^((4/5:ℝ)*((i:ℝ)+1))*M^(-(9/10:ℝ)*((i:ℝ)+1)) ≤ 1 := by
      rw [← Real.rpow_add hp]
      exact Real.rpow_le_one_of_one_le_of_nonpos hM.le (by have : (0:ℝ) ≤ (i:ℕ) := Nat.cast_nonneg _; linarith)
    rw [mul_one,abs_mul,abs_of_pos (hw i)]
    calc
      _ ≤ w i*(12*M^(-(9/10:ℝ)*((i:ℝ)+1))) := by
        gcongr
        simpa only [U,Nat.cast_add,Nat.cast_one] using hU'
      _ ≤ 24/2 := by dsimp only [w]; nlinarith
  have hrow (i : Fin n) : ∑ j, |w i*greenMatrix v n i j| *L j/w j ≤ 1/2 := by
    have hh:=green_weighted_rows M 12 8 n (tSolution v) (dirichletSolution v (n+1))
      hM (by norm_num) (by norm_num) hq hv hU i
    have he : ∀ i j : Fin n, greenMatrix v n i j=
        tSolution v (min (i:ℕ) (j:ℕ)+1)*dirichletSolution v (n+1) (max (i:ℕ) (j:ℕ)+1) := by
      intro i j
      simp only [greenMatrix,greenKernel,min_add_add_right,max_add_add_right]
    simp_rw [he]
    exact hh.trans (by nlinarith only [hsmall])
  obtain ⟨ζ,hζb,hζ⟩:=finite_weighted_dirichlet w U (greenMatrix v n) F L 1 24 hw
    (by norm_num) (fun i => by dsimp only [L]; positivity)
    (by intro i; simp [F])
    (by
      intro i x y hx hy
      dsimp only [F]
      rw [← mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_right (hdiff i) (abs_nonneg _)) hlin hrow
  have hζ' : ∀ i, ζ i=dirichletSolution v (n+1) (i+1)+
      ∑ j, greenMatrix v n i j*((v (j+1)-v' (j+1))*ζ j) := by
    intro i
    simpa only [U,F,mul_one] using hζ i
  obtain ⟨ht',hsol⟩:=linear_fixedPoint_dirichlet v v' n ht ζ hζ'
  exact ⟨ht',fun i => (hsol i ▸ hζb i)⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_GraphCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma hasStrictDerivAt_phi (k x : ℝ) : HasStrictDerivAt (phi k) (potential k x) x := by
  have h := ((hasStrictDerivAt_id x).const_mul 2).add
    (((Real.hasStrictDerivAt_sin (2*Real.pi*x)).comp x
      ((hasStrictDerivAt_id x).const_mul (2*Real.pi))).const_mul k)
  convert! h using 1
  dsimp only [potential]
  ring

lemma hasStrictFDerivAt_liftedOrbit (k q a : ℝ) (n : ℕ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => liftedOrbit k z.1 z.2 n)
      (sSolution (orbitCoefficient k q a) n • ContinuousLinearMap.fst ℝ ℝ ℝ+
       tSolution (orbitCoefficient k q a) n • ContinuousLinearMap.snd ℝ ℝ ℝ) (q,a) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [sSolution,tSolution,linearSolution] using
      (hasStrictFDerivAt_fst : HasStrictFDerivAt (Prod.fst : ℝ × ℝ → ℝ) _ (q,a))
  | one => simpa [sSolution,tSolution,linearSolution] using
      (hasStrictFDerivAt_snd : HasStrictFDerivAt (Prod.snd : ℝ × ℝ → ℝ) _ (q,a))
  | more n h0 h1 =>
    have h := ((hasStrictDerivAt_phi k (liftedOrbit k q a (n+1))).comp_hasStrictFDerivAt (q,a) h1).sub h0
    apply h.congr_fderiv
    apply ContinuousLinearMap.ext
    intro z
    change potential k (liftedOrbit k q a (n+1)) *
      (sSolution (orbitCoefficient k q a) (n+1)*z.1+tSolution (orbitCoefficient k q a) (n+1)*z.2)-
      (sSolution (orbitCoefficient k q a) n*z.1+tSolution (orbitCoefficient k q a) n*z.2) =
      (orbitCoefficient k q a (n+1)*sSolution (orbitCoefficient k q a) (n+1)-sSolution (orbitCoefficient k q a) n)*z.1+
      (orbitCoefficient k q a (n+1)*tSolution (orbitCoefficient k q a) (n+1)-tSolution (orbitCoefficient k q a) n)*z.2
    dsimp only [orbitCoefficient]
    ring

lemma hasDerivAt_of_regular_level (F : ℝ × ℝ → ℝ) (b : ℝ → ℝ) (x s t : ℝ)
    (hD : HasStrictFDerivAt F
      (s • ContinuousLinearMap.fst ℝ ℝ ℝ+t • ContinuousLinearMap.snd ℝ ℝ ℝ) (x,b x))
    (ht : t ≠ 0) (hb : ContinuousAt b x)
    (hlevel : ∀ᶠ y in 𝓝 x, F (y,b y)=F (x,b x)) :
    HasDerivAt b (-s/t) x := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := s • ContinuousLinearMap.fst ℝ ℝ ℝ+t • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hInv : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := t⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
  let ψ := hD.implicitFunctionOfProdDomain hInv
  have he : ∀ᶠ y in 𝓝 x, ψ y=b y := by
    have hpair : Tendsto (fun y => (y,b y)) (𝓝 x) (𝓝 (x,b x)) :=
      tendsto_id.prodMk_nhds hb
    filter_upwards [hpair.eventually (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv),hlevel] with y hy hy'
    exact hy.mp hy'
  have hd := (hD.hasStrictFDerivAt_implicitFunctionOfProdDomain hInv).hasFDerivAt.hasDerivAt
  have heq : (-(L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).inverse.comp
      (L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ))) 1 = -s/t := by
    have hh : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).inverse
        ((L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1)=s/t := by
      apply hInv.inverse_apply_eq.mpr
      simp only [L,ContinuousLinearMap.comp_apply,add_apply,smul_apply]
      change s*1+t*0=s*0+t*(s/t)
      field_simp
      ring
    change -(L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).inverse
      ((L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1) = -s/t
    rw [hh,neg_div]
  change HasDerivAt ψ _ x at hd
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq (EventuallyEq.symm he)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_FixedPointFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma bridge_green_row (k q a : ℝ) (n : ℕ) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (hU : ∀ p, 1 ≤ p → p ≤ n → |dirichletSolution (orbitCoefficient k q a) (n+1) p| ≤
      12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) (i : Fin n) :
    ∑ j : Fin n, |growthBase k^((4/5:ℝ)*((i:ℝ)+1))*greenMatrix (orbitCoefficient k q a) n i j| *
      ((2*Real.pi*growthBase k)*8/growthBase k^((4/5:ℝ)*((j:ℝ)+1)))/
        growthBase k^((4/5:ℝ)*((j:ℝ)+1)) ≤ 1/2 := by
  have hm : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hh:=green_weighted_rows (growthBase k) 12 8 n (tSolution (orbitCoefficient k q a))
    (dirichletSolution (orbitCoefficient k q a) (n+1)) hm (by norm_num) (by norm_num) hq
    (fun p hp' hn => tSolution_abs_le_pow _ _ p hp' hm.le
      (fun i hi hip => potential_bound k (liftedOrbit k q a i) hk)) hU i
  have he : ∀ i j : Fin n, greenMatrix (orbitCoefficient k q a) n i j=
      tSolution (orbitCoefficient k q a) (min (i:ℕ) (j:ℕ)+1)*
      dirichletSolution (orbitCoefficient k q a) (n+1) (max (i:ℕ) (j:ℕ)+1) := by
    intro i j
    simp only [greenMatrix,greenKernel,min_add_add_right,max_add_add_right]
  simp_rw [he]
  exact hh.trans (by nlinarith only [hsmall])

lemma nonlinear_fixedPoint_stability (k q a : ℝ) (n : ℕ) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (hU : ∀ p, 1 ≤ p → p ≤ n → |dirichletSolution (orbitCoefficient k q a) (n+1) p| ≤
      12*growthBase k^(-(9/10:ℝ)*(p:ℝ)))
    (r s : ℝ) (ξ ζ : Fin n → ℝ)
    (hξb : ∀ i, |ξ i| ≤ 8/growthBase k^((4/5:ℝ)*((i:ℝ)+1)))
    (hζb : ∀ i, |ζ i| ≤ 8/growthBase k^((4/5:ℝ)*((i:ℝ)+1)))
    (hξ : ∀ i, ξ i=dirichletSolution (orbitCoefficient k q a) (n+1) (i+1)*r+
        ∑ j, greenMatrix (orbitCoefficient k q a) n i j *
          (-(phi k (liftedOrbit k q a (j+1)+ξ j)-phi k (liftedOrbit k q a (j+1))-
            potential k (liftedOrbit k q a (j+1))*ξ j)))
    (hζ : ∀ i, ζ i=dirichletSolution (orbitCoefficient k q a) (n+1) (i+1)*s+
        ∑ j, greenMatrix (orbitCoefficient k q a) n i j *
          (-(phi k (liftedOrbit k q a (j+1)+ζ j)-phi k (liftedOrbit k q a (j+1))-
            potential k (liftedOrbit k q a (j+1))*ζ j))) :
    ∀ i, |ξ i-ζ i| ≤ 24*|r-s|/growthBase k^((4/5:ℝ)*((i:ℝ)+1)) := by
  let M := growthBase k
  have hm : 1 < M := by have := growthBase_ge_four k hk; linarith
  have hp : 0 < M := by linarith
  let w : Fin n → ℝ := fun i => M^((4/5:ℝ)*((i:ℝ)+1))
  let U : Fin n → ℝ := fun i => dirichletSolution (orbitCoefficient k q a) (n+1) (i+1)
  let F : Fin n → ℝ → ℝ := fun j z => -(phi k (liftedOrbit k q a (j+1)+z)-
    phi k (liftedOrbit k q a (j+1))-potential k (liftedOrbit k q a (j+1))*z)
  let L : Fin n → ℝ := fun i => (2*Real.pi*M)*8/w i
  have hw (i : Fin n) : 0 < w i := Real.rpow_pos_of_pos hp _
  have hlin : ‖fun i => w i*U i‖ ≤ (12:ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    have hU':=hU (i+1) (by omega) (by omega)
    have hexp : M^((4/5:ℝ)*((i:ℝ)+1))*M^(-(9/10:ℝ)*((i:ℝ)+1)) ≤ 1 := by
      rw [← Real.rpow_add hp]
      exact Real.rpow_le_one_of_one_le_of_nonpos hm.le (by have : (0:ℝ) ≤ (i:ℕ) := Nat.cast_nonneg _; linarith)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (hw i)]
    calc
      _ ≤ w i*(12*M^(-(9/10:ℝ)*((i:ℝ)+1))) := by
        gcongr
        simpa only [U,Nat.cast_add,Nat.cast_one] using hU'
      _ ≤ _ := by dsimp only [w]; nlinarith
  have hn:=weighted_fixedPoint_stability w U (greenMatrix (orbitCoefficient k q a) n) F L ξ ζ r s 12 hw
    (fun i => by dsimp only [L]; positivity) (by
      intro i
      dsimp only [F]
      rw [← neg_sub,abs_neg]
      have hh:=phi_remainder_lipschitz k (liftedOrbit k q a (i+1)) (ξ i) (ζ i) (8/w i) hk (hξb i) (hζb i)
      dsimp only [L,M]
      convert hh using 1 <;> ring_nf)
    (bridge_green_row k q a n hk hq hsmall hU) hlin hξ hζ
  intro i
  apply (le_div_iff₀ (hw i)).mpr
  have hh:=(norm_le_pi_norm (fun i => w i*(ξ i-ζ i)) i).trans hn
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (hw i),mul_comm,show (2:ℝ)*12=24 by norm_num] using hh

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_GraphFamilySmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma hasStrictFDerivAt_liftedOrbit_shift (k q r a : ℝ) (n : ℕ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => liftedOrbit k (q+z.1) z.2 n)
      (sSolution (orbitCoefficient k (q+r) a) n • ContinuousLinearMap.fst ℝ ℝ ℝ+
       tSolution (orbitCoefficient k (q+r) a) n • ContinuousLinearMap.snd ℝ ℝ ℝ) (r,a) := by
  have hpair : HasStrictFDerivAt (fun z : ℝ × ℝ => (q+z.1,z.2)) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) (r,a) := by
    have h1 : HasStrictFDerivAt (fun z : ℝ × ℝ => q+z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (r,a) := by
      have hh := (hasStrictFDerivAt_const q (r,a)).add (hasStrictFDerivAt_fst (𝕜 := ℝ))
      convert! hh using 1
      simp
    have h2 : HasStrictFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) (r,a) := hasStrictFDerivAt_snd
    simpa using h1.prodMk h2
  have hh := (hasStrictFDerivAt_liftedOrbit k (q+r) a n).comp (r,a) hpair
  simpa only [ContinuousLinearMap.comp_id] using hh

lemma hasDerivAt_liftedOrbit_curve (k q r : ℝ) (b : ℝ → ℝ) (b' : ℝ)
    (hb : HasDerivAt b b' r) (n : ℕ) :
    HasDerivAt (fun x => liftedOrbit k (q+x) (b x) n)
      (linearSolution (orbitCoefficient k (q+r) (b r)) 1 b' n) r := by
  have hpair := ((hasDerivAt_id r).const_add q).prodMk hb
  have hh := (hasStrictFDerivAt_liftedOrbit k (q+r) (b r) n).hasFDerivAt.comp_hasDerivAt r hpair
  rw [linearSolution_decomposition]
  convert! hh using 1
  change 1*sSolution _ n+b'*tSolution _ n=sSolution _ n*1+tSolution _ n*b'
  ring

lemma continuousAt_of_local_lipschitz (f : ℝ → ℝ) (x R C : ℝ) (hC : 0 ≤ C)
    (hx : |x| < R)
    (hLip : ∀ y z, |y| ≤ R → |z| ≤ R → |f y-f z| ≤ C*|y-z|) : ContinuousAt f x := by
  have hcont : ContinuousOn f (Icc (-R) R) := by
    apply LipschitzOnWith.continuousOn (K := (⟨C,hC⟩ : NNReal))
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    change |f y-f z| ≤ C*|y-z|
    exact hLip y z (abs_le.mpr hy) (abs_le.mpr hz)
  exact (hcont x (abs_le.mp hx.le)).continuousAt
    (Icc_mem_nhds (by linarith [(abs_lt.mp hx).1]) (abs_lt.mp hx).2)

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_FixedPointContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

lemma continuousOn_contractive_fixedPoints {α E : Type*} [TopologicalSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set α) (B : Set E) (T : α → E → E) (p : α → E)
    (hp : ∀ a ∈ s, p a ∈ B) (hfix : ∀ a ∈ s, T a (p a)=p a)
    (hcontract : ∀ a ∈ s, ∀ x ∈ B, ∀ y ∈ B,
      ‖T a x-T a y‖ ≤ (1/2)*‖x-y‖)
    (hcont : ∀ x ∈ B, ContinuousOn (fun a => T a x) s) : ContinuousOn p s := by
  intro a ha
  have hbound (b : α) (hb : b ∈ s) : ‖p b-p a‖ ≤ 2*‖T b (p a)-T a (p a)‖ := by
    have hh:=hcontract b hb (p b) (hp b hb) (p a) (hp a ha)
    rw [hfix b hb] at hh
    have ht:=dist_triangle (p b) (T b (p a)) (p a)
    simp only [dist_eq_norm] at ht
    rw [hfix a ha]
    nlinarith
  change Tendsto p (𝓝[s] a) (𝓝 (p a))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε/2 := by positivity
  have ht : ∀ᶠ b in 𝓝[s] a, dist (T b (p a)) (T a (p a)) < ε/2 :=
    (hcont (p a) (hp a ha) a ha).eventually (ball_mem_nhds _ hε')
  filter_upwards [self_mem_nhdsWithin,ht] with b hb hnear
  rw [dist_eq_norm]
  have hh:=hbound b hb
  rw [dist_eq_norm] at hnear
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ScaledContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma weighted_dirichlet_contraction {ι : Type*} [Fintype ι]
    (w U : ι → ℝ) (G : ι → ι → ℝ) (F : ι → ℝ → ℝ) (L : ι → ℝ) (r R : ℝ)
    (hw : ∀ i, 0 < w i) (hL : ∀ i, 0 ≤ L i)
    (hLip : ∀ i x y, |x| ≤ R/w i → |y| ≤ R/w i → |F i x-F i y| ≤ L i*|x-y|)
    (hrow : ∀ i, ∑ j, |w i*G i j| *L j/w j ≤ 1/2)
    (X Y : ι → ℝ) (hX : ‖X‖ ≤ R) (hY : ‖Y‖ ≤ R) :
    ‖(fun i => w i*U i*r+∑ j, w i*G i j*F j (X j/w j))-
      (fun i => w i*U i*r+∑ j, w i*G i j*F j (Y j/w j))‖ ≤ (1/2)*‖X-Y‖ := by
  classical
  have hcoord (Z : ι → ℝ) (hZ : ‖Z‖ ≤ R) (i : ι) : |Z i/w i| ≤ R/w i := by
    rw [abs_div,abs_of_pos (hw i)]
    exact div_le_div_of_nonneg_right ((norm_le_pi_norm Z i).trans hZ) (hw i).le
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hc (j : ι) : |X j/w j-Y j/w j| ≤ ‖X-Y‖/w j := by
    rw [← sub_div,abs_div,abs_of_pos (hw j)]
    exact div_le_div_of_nonneg_right (norm_le_pi_norm (X-Y) j) (hw j).le
  calc
    _ = |∑ j, w i*G i j*(F j (X j/w j)-F j (Y j/w j))| := by
      simp only [Pi.sub_apply,Real.norm_eq_abs,add_sub_add_left_eq_sub,← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ ∑ j, |w i*G i j| *|F j (X j/w j)-F j (Y j/w j)| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun j => w i*G i j*(F j (X j/w j)-F j (Y j/w j))) Finset.univ
    _ ≤ ∑ j, |w i*G i j| *(L j*(‖X-Y‖/w j)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left ((hLip j _ _ (hcoord X hX j) (hcoord Y hY j)).trans
        (mul_le_mul_of_nonneg_left (hc j) (hL j))) (abs_nonneg _)
    _ = (∑ j, |w i*G i j| *L j/w j)*‖X-Y‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)

lemma continuousOn_weighted_fixedPoints {α ι : Type*} [TopologicalSpace α] [Fintype ι]
    (s : Set α) (w : ι → ℝ) (U : α → ι → ℝ) (G : α → ι → ι → ℝ)
    (F : α → ι → ℝ → ℝ) (L : ι → ℝ) (r : α → ℝ) (R : ℝ)
    (ξ : α → ι → ℝ) (hw : ∀ i, 0 < w i) (hR : 0 ≤ R) (hL : ∀ i, 0 ≤ L i)
    (hξb : ∀ a ∈ s, ∀ i, |ξ a i| ≤ R/w i)
    (hξ : ∀ a ∈ s, ∀ i, ξ a i=U a i*r a+∑ j, G a i j*F a j (ξ a j))
    (hLip : ∀ a ∈ s, ∀ i x y, |x| ≤ R/w i → |y| ≤ R/w i → |F a i x-F a i y| ≤ L i*|x-y|)
    (hrow : ∀ a ∈ s, ∀ i, ∑ j, |w i*G a i j| *L j/w j ≤ 1/2)
    (hUc : ∀ i, ContinuousOn (fun a => U a i) s)
    (hGc : ∀ i j, ContinuousOn (fun a => G a i j) s)
    (hFc : ∀ i x, ContinuousOn (fun a => F a i x) s)
    (hrc : ContinuousOn r s) : ContinuousOn ξ s := by
  classical
  let T : α → (ι → ℝ) → (ι → ℝ) := fun a X i =>
    w i*U a i*r a+∑ j, w i*G a i j*F a j (X j/w j)
  let p : α → (ι → ℝ) := fun a i => w i*ξ a i
  have hp : ContinuousOn p s := by
    apply continuousOn_contractive_fixedPoints s {X | ‖X‖ ≤ R} T p
    · intro a ha
      apply (pi_norm_le_iff_of_nonneg hR).mpr
      intro i
      change |w i*ξ a i| ≤ R
      rw [abs_mul,abs_of_pos (hw i)]
      simpa only [mul_comm] using (le_div_iff₀ (hw i)).mp (hξb a ha i)
    · intro a ha
      funext i
      dsimp only [T,p]
      simp only [mul_div_cancel_left₀ _ (hw _).ne']
      rw [hξ a ha i,mul_add,Finset.mul_sum]
      rw [mul_assoc]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · intro a ha X hX Y hY
      exact weighted_dirichlet_contraction w (U a) (G a) (F a) L (r a) R hw hL
        (hLip a ha) (hrow a ha) X Y hX hY
    · intro X hX
      apply continuousOn_pi.mpr
      intro i
      exact ((continuousOn_const.mul (hUc i)).mul hrc).add
        (continuousOn_finsetSum _ (fun j _ =>
          (continuousOn_const.mul (hGc i j)).mul (hFc j (X j/w j))))
  apply continuousOn_pi.mpr
  intro i
  have hi := (continuousOn_pi.mp hp i).div_const (w i)
  simpa only [p,mul_div_cancel_left₀ _ (hw i).ne'] using hi
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_GraphParameterContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma continuous_liftedOrbit_pair (k : ℝ) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => liftedOrbit k z.1 z.2 n) :=
  continuous_iff_continuousAt.mpr (fun z =>
    (hasStrictFDerivAt_liftedOrbit k z.1 z.2 n).continuousAt)
lemma continuousOn_linearSolution_params {α : Type*} [TopologicalSpace α]
    (s : Set α) (v : α → ℕ → ℝ) (a b : α → ℝ)
    (hv : ∀ n, ContinuousOn (fun x => v x n) s)
    (ha : ContinuousOn a s) (hb : ContinuousOn b s) (n : ℕ) :
    ContinuousOn (fun x => linearSolution (v x) (a x) (b x) n) s := by
  induction n using Nat.twoStepInduction with
  | zero => exact ha
  | one => exact hb
  | more n h0 h1 => exact ((hv (n+1)).mul h1).sub h0
lemma continuousOn_dirichlet_params {α : Type*} [TopologicalSpace α]
    (s : Set α) (v : α → ℕ → ℝ) (j p : ℕ)
    (hv : ∀ n, ContinuousOn (fun x => v x n) s)
    (ht : ∀ x ∈ s, tSolution (v x) j ≠ 0) :
    ContinuousOn (fun x => dirichletSolution (v x) j p) s := by
  have hb : ContinuousOn (fun x => boundaryValue (v x) j) s :=
    (continuousOn_linearSolution_params s v (fun _ => 1) (fun _ => 0) hv
      continuousOn_const continuousOn_const j).neg.div
      (continuousOn_linearSolution_params s v (fun _ => 0) (fun _ => 1) hv
        continuousOn_const continuousOn_const j) ht
  exact continuousOn_linearSolution_params s v (fun _ => 1) _ hv continuousOn_const hb p

lemma continuousOn_nonlinear_dirichlet_corrections (k : ℝ) (n : ℕ) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (s : Set ((ℝ × ℝ) × ℝ)) (ξ : ((ℝ × ℝ) × ℝ) → Fin n → ℝ)
    (ht : ∀ z ∈ s, tSolution (orbitCoefficient k z.1.1 z.1.2) (n+1) ≠ 0)
    (hU : ∀ z ∈ s, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1.1 z.1.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ)))
    (hξb : ∀ z ∈ s, ∀ i, |ξ z i| ≤ 8/growthBase k^((4/5:ℝ)*((i:ℝ)+1)))
    (hξ : ∀ z ∈ s, ∀ i, ξ z i=
      dirichletSolution (orbitCoefficient k z.1.1 z.1.2) (n+1) (i+1)*z.2+
        ∑ j, greenMatrix (orbitCoefficient k z.1.1 z.1.2) n i j *
          (-(phi k (liftedOrbit k z.1.1 z.1.2 (j+1)+ξ z j)-
            phi k (liftedOrbit k z.1.1 z.1.2 (j+1))-
            potential k (liftedOrbit k z.1.1 z.1.2 (j+1))*ξ z j))) :
    ContinuousOn ξ s := by
  let M := growthBase k
  have hp : 0 < M := by have := growthBase_ge_four k hk; dsimp [M]; linarith
  let w : Fin n → ℝ := fun i => M^((4/5:ℝ)*((i:ℝ)+1))
  let U : ((ℝ × ℝ) × ℝ) → Fin n → ℝ := fun z i =>
    dirichletSolution (orbitCoefficient k z.1.1 z.1.2) (n+1) (i+1)
  let G : ((ℝ × ℝ) × ℝ) → Fin n → Fin n → ℝ := fun z =>
    greenMatrix (orbitCoefficient k z.1.1 z.1.2) n
  let F : ((ℝ × ℝ) × ℝ) → Fin n → ℝ → ℝ := fun z j u =>
    -(phi k (liftedOrbit k z.1.1 z.1.2 (j+1)+u)-
      phi k (liftedOrbit k z.1.1 z.1.2 (j+1))-
      potential k (liftedOrbit k z.1.1 z.1.2 (j+1))*u)
  let L : Fin n → ℝ := fun i => (2*Real.pi*M)*8/w i
  have ho (p : ℕ) : Continuous (fun z : ((ℝ × ℝ) × ℝ) => liftedOrbit k z.1.1 z.1.2 p) :=
    (continuous_liftedOrbit_pair k p).comp continuous_fst
  have hpot : Continuous (potential k) := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_potential k x).continuousAt)
  have hphi : Continuous (phi k) := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_phi k x).continuousAt)
  have hv (p : ℕ) : ContinuousOn
      (fun z : ((ℝ × ℝ) × ℝ) => orbitCoefficient k z.1.1 z.1.2 p) s :=
    (hpot.comp (ho p)).continuousOn
  apply continuousOn_weighted_fixedPoints s w U G F L Prod.snd 8 ξ
    (fun i => Real.rpow_pos_of_pos hp _) (by norm_num)
    (fun i => by dsimp only [L,w]; positivity) hξb hξ
  · intro z hz i x y hx hy
    dsimp only [F]
    rw [← neg_sub,abs_neg]
    have hh:=phi_remainder_lipschitz k (liftedOrbit k z.1.1 z.1.2 (i+1)) x y (8/w i) hk hx hy
    dsimp only [L,M]
    convert hh using 1 <;> ring_nf
  · intro z hz i
    exact bridge_green_row k z.1.1 z.1.2 n hk hq hsmall (hU z hz) i
  · intro i
    exact continuousOn_dirichlet_params s _ (n+1) (i+1) hv ht
  · intro i j
    exact (continuousOn_linearSolution_params s _ (fun _ => 0) (fun _ => 1) hv
      continuousOn_const continuousOn_const (min ((i:ℕ)+1) ((j:ℕ)+1))).mul
      (continuousOn_dirichlet_params s _ (n+1) (max ((i:ℕ)+1) ((j:ℕ)+1)) hv ht)
  · intro i x
    exact (((hphi.comp ((ho (i+1)).add_const x)).sub
      (hphi.comp (ho (i+1)))).sub ((hpot.comp (ho (i+1))).mul_const x)).neg.continuousOn
  · exact continuous_snd.continuousOn
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_JointGraphFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

lemma jointly_continuous_dirichlet_family (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (s : Set (ℝ × ℝ))
    (ht : ∀ z ∈ s, tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0)
    (hU : ∀ z ∈ s, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
    ∃ b : (ℝ × ℝ) → ℝ → ℝ,
      ContinuousOn (fun z : (ℝ × ℝ) × ℝ => b z.1 z.2) (s ×ˢ Icc (-(1/4)) (1/4)) ∧
      ∀ z ∈ s, b z 0=z.2 ∧
      (∀ r, |r| ≤ 1/4 → liftedOrbit k (z.1+r) (b z r) (n+1)=liftedOrbit k z.1 z.2 (n+1)) ∧
      (∀ r, |r| ≤ 1/4 → ∀ i : Fin n,
        |liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k z.1 z.2 (i+1)| ≤
          8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) ∧
      (∀ r t, |r| ≤ 1/4 → |t| ≤ 1/4 → ∀ i : Fin n,
        |liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k (z.1+t) (b z t) (i+1)| ≤
          24*|r-t|/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
  classical
  let S := s ×ˢ Icc (-(1/4:ℝ)) (1/4)
  let ξ : ((ℝ × ℝ) × ℝ) → Fin n → ℝ := fun z => if hz : z ∈ S then
    (nonlinear_dirichlet_fixedPoint k z.1.1 z.1.2 z.2 n hk (abs_le.mpr hz.2) hq hsmall (hU z.1 hz.1)).choose else 0
  have hξb (z : (ℝ × ℝ) × ℝ) (hz : z ∈ S) (i : Fin n) :
      |ξ z i| ≤ 8/growthBase k^((4/5:ℝ)*((i:ℝ)+1)) := by
    simpa only [ξ,dite_eq_left hz] using
      (nonlinear_dirichlet_fixedPoint k z.1.1 z.1.2 z.2 n hk (abs_le.mpr hz.2) hq hsmall (hU z.1 hz.1)).choose_spec.1 i
  have hξ (z : (ℝ × ℝ) × ℝ) (hz : z ∈ S) (i : Fin n) :
      ξ z i=dirichletSolution (orbitCoefficient k z.1.1 z.1.2) (n+1) (i+1)*z.2+
        ∑ j, greenMatrix (orbitCoefficient k z.1.1 z.1.2) n i j *
          (-(phi k (liftedOrbit k z.1.1 z.1.2 (j+1)+ξ z j)-
            phi k (liftedOrbit k z.1.1 z.1.2 (j+1))-
            potential k (liftedOrbit k z.1.1 z.1.2 (j+1))*ξ z j)) := by
    simpa only [ξ,dite_eq_left hz] using
      (nonlinear_dirichlet_fixedPoint k z.1.1 z.1.2 z.2 n hk (abs_le.mpr hz.2) hq hsmall (hU z.1 hz.1)).choose_spec.2 i
  let b : (ℝ × ℝ) → ℝ → ℝ := fun z r => z.2+ξ (z,r) ⟨0,hn⟩
  have hcont : ContinuousOn ξ S := continuousOn_nonlinear_dirichlet_corrections k n hk hq hsmall S ξ
    (fun z hz => ht z.1 hz.1) (fun z hz => hU z.1 hz.1) hξb hξ
  have horb (z : ℝ × ℝ) (hz : z ∈ s) (r : ℝ) (hr : |r| ≤ 1/4) :
      liftedOrbit k (z.1+r) (b z r) (n+1)=liftedOrbit k z.1 z.2 (n+1) ∧
      ∀ i : Fin n, liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k z.1 z.2 (i+1)=ξ (z,r) i := by
    have hz' : (z,r) ∈ S := ⟨hz,abs_le.mp hr⟩
    obtain ⟨b',he,hξ'⟩:=nonlinear_fixedPoint_orbit k z.1 z.2 r n (ht z hz) (ξ (z,r)) (hξ (z,r) hz')
    have h0:=hξ' ⟨0,hn⟩
    change b'-z.2=ξ (z,r) ⟨0,hn⟩ at h0
    have hb' : b'=b z r := by dsimp only [b]; linarith
    subst b'
    exact ⟨he,hξ'⟩
  refine ⟨b,((continuous_snd.comp continuous_fst).continuousOn).add
    (continuousOn_pi.mp hcont ⟨0,hn⟩),?_⟩
  intro z hz
  have hξ0 : ξ (z,0)=0 := by
    have hp : 0 < growthBase k := by have := growthBase_ge_four k hk; linarith
    have hz0 : (z,(0:ℝ)) ∈ S := ⟨hz,by norm_num⟩
    have hh:=nonlinear_fixedPoint_stability k z.1 z.2 n hk hq hsmall (hU z hz) 0 0 (ξ (z,0)) 0
      (hξb (z,0) hz0) (fun i => by simpa using (div_nonneg (by norm_num : (0:ℝ) ≤ 8) (Real.rpow_pos_of_pos hp _).le))
      (hξ (z,0) hz0) (fun i => by simp)
    funext i
    have hi:=hh i
    simpa using (abs_nonpos_iff.mp (by simpa using hi) : ξ (z,0) i=0)
  refine ⟨by simp [b,hξ0],fun r hr => (horb z hz r hr).1,?_,?_⟩
  · intro r hr i
    rw [(horb z hz r hr).2 i]
    exact hξb (z,r) ⟨hz,abs_le.mp hr⟩ i
  · intro r t hr ht' i
    have hh:=nonlinear_fixedPoint_stability k z.1 z.2 n hk hq hsmall (hU z hz) r t (ξ (z,r)) (ξ (z,t))
      (hξb (z,r) ⟨hz,abs_le.mp hr⟩) (hξb (z,t) ⟨hz,abs_le.mp ht'⟩)
      (hξ (z,r) ⟨hz,abs_le.mp hr⟩) (hξ (z,t) ⟨hz,abs_le.mp ht'⟩) i
    have he : liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k (z.1+t) (b z t) (i+1)=ξ (z,r) i-ξ (z,t) i := by
      rw [← (horb z hz r hr).2 i,← (horb z hz t ht').2 i]; ring
    rwa [he]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_GraphDerivativeUpgrade
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma contracting_family_derivatives_of_bounds (k q a : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (ht : tSolution (orbitCoefficient k q a) (n+1) ≠ 0)
    (hU : ∀ p, 1 ≤ p → p ≤ n → |dirichletSolution (orbitCoefficient k q a) (n+1) p| ≤
      12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) (b : ℝ → ℝ)
    (hterm : ∀ r, |r| ≤ 1/4 → liftedOrbit k (q+r) (b r) (n+1)=liftedOrbit k q a (n+1))
    (hbound : ∀ r, |r| ≤ 1/4 → ∀ i : Fin n,
      |liftedOrbit k (q+r) (b r) (i+1)-liftedOrbit k q a (i+1)| ≤
        8/growthBase k^((4/5:ℝ)*((i:ℝ)+1)))
    (hLip : ∀ r s, |r| ≤ 1/4 → |s| ≤ 1/4 → ∀ i : Fin n,
      |liftedOrbit k (q+r) (b r) (i+1)-liftedOrbit k (q+s) (b s) (i+1)| ≤
        24*|r-s|/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) :
    (∀ r, |r| ≤ 1/4 → tSolution (orbitCoefficient k (q+r) (b r)) (n+1) ≠ 0) ∧
      (∀ r, |r| < 1/4 → ∀ p,
        HasDerivAt (fun x => liftedOrbit k (q+x) (b x) p)
          (dirichletSolution (orbitCoefficient k (q+r) (b r)) (n+1) p) r) ∧
      (∀ r, |r| ≤ 1/4 → ∀ i : Fin n,
        |dirichletSolution (orbitCoefficient k (q+r) (b r)) (n+1) (i+1)| ≤
          24/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
  have hm : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hp : 0 < growthBase k := by linarith
  have hvar (r : ℝ) (hr : |r| ≤ 1/4) := varied_dirichlet_bound (orbitCoefficient k q a)
    (orbitCoefficient k (q+r) (b r)) (growthBase k) n hm hq hsmall ht
    (fun p hp' hn => tSolution_abs_le_pow _ _ p hp' hm.le
      (fun i hi hip => potential_bound k (liftedOrbit k q a i) hk)) hU (by
      intro i
      have hh:=potential_lipschitz k (liftedOrbit k q a (i+1)) (liftedOrbit k (q+r) (b r) (i+1)) hk
      dsimp only [orbitCoefficient]
      calc
        _ ≤ (2*Real.pi*growthBase k)*|liftedOrbit k q a (i+1)-liftedOrbit k (q+r) (b r) (i+1)| := by simpa only [abs_sub_comm] using hh
        _ ≤ (2*Real.pi*growthBase k)*(8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
          gcongr
          simpa only [abs_sub_comm] using hbound r hr i
        _ = _ := by ring)
  refine ⟨fun r hr => (hvar r hr).1,?_,fun r hr => (hvar r hr).2⟩
  intro r hr p
  have hcont : ContinuousAt b r := continuousAt_of_local_lipschitz b r (1/4)
    (24/growthBase k^((4/5:ℝ))) (by positivity) hr (by
      intro y z hy hz
      have hh:=hLip y z hy hz (⟨0,hn⟩:Fin n)
      simpa only [Fin.val_zero,Nat.cast_zero,zero_add,mul_one,liftedOrbit_one,div_mul_eq_mul_div] using hh)
  have hd := hasDerivAt_of_regular_level (fun z : ℝ × ℝ => liftedOrbit k (q+z.1) z.2 (n+1)) b r
    (sSolution (orbitCoefficient k (q+r) (b r)) (n+1)) (tSolution (orbitCoefficient k (q+r) (b r)) (n+1))
    (hasStrictFDerivAt_liftedOrbit_shift k q r (b r) (n+1)) (hvar r hr.le).1 hcont (by
      have he : ∀ᶠ y in 𝓝 r, |y| < 1/4 := (continuous_abs.continuousAt.eventually (Iio_mem_nhds hr))
      filter_upwards [he] with y hy
      exact (hterm y hy.le).trans (hterm r hr.le).symm)
  exact hasDerivAt_liftedOrbit_curve k q r b _ hd p
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_LogDerivativeCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma hasDerivAt_tSolution_family (v : ℝ → ℕ → ℝ) (dv : ℕ → ℝ) (x : ℝ)
    (hv : ∀ i, HasDerivAt (fun r => v r i) (dv i) x) (n : ℕ) :
    HasDerivAt (fun r => tSolution (v r) n) (tVariation (v x) dv n) x := by
  induction n using Nat.twoStepInduction with
  | zero => exact hasDerivAt_const x 0
  | one => exact hasDerivAt_const x 1
  | more n h0 h1 =>
    have hh:=((hv (n+1)).mul h1).sub h0
    convert! hh using 1
    change v x (n+1)*tVariation (v x) dv (n+1)-tVariation (v x) dv n+dv (n+1)*tSolution (v x) (n+1)=_
    ring

lemma tVariation_wronskian (v dv : ℕ → ℝ) (J n : ℕ) :
    dirichletSolution v J (n+1)*tVariation v dv (n+2)-
      dirichletSolution v J (n+2)*tVariation v dv (n+1)=
        ∑ i ∈ Finset.range (n+1), dirichletSolution v J (i+1)*dv (i+1)*tSolution v (i+1) := by
  induction n with
  | zero => simp [tVariation,dirichletSolution,linearSolution,tSolution]
  | succ n ih =>
    rw [Finset.sum_range_succ,← ih]
    rw [show n+1+1=n+2 by omega,show n+1+2=(n+1)+2 by omega]
    rw [show tVariation v dv (n+1+2)=v (n+2)*tVariation v dv (n+2)-tVariation v dv (n+1)+dv (n+2)*tSolution v (n+2) by rfl,
      dirichletSolution_step v J (n+1)]
    ring

lemma tVariation_div_terminal (v dv : ℕ → ℝ) (n : ℕ) (ht : tSolution v (n+1) ≠ 0) :
    tVariation v dv (n+1)/tSolution v (n+1)=
      ∑ i ∈ Finset.range n, tSolution v (i+1)*dirichletSolution v (n+1) (i+1)*dv (i+1) := by
  cases n with
  | zero => simp [tVariation]
  | succ n =>
    have hh:=tVariation_wronskian v dv (n+1+1) n
    rw [dirichletSolution_boundary v (n+1+1) ht,zero_mul,sub_zero] at hh
    have hw:=solution_wronskian v 1 (boundaryValue v (n+1+1)) (n+1)
    change dirichletSolution v (n+1+1) (n+1)*tSolution v (n+1+1)-
      dirichletSolution v (n+1+1) (n+1+1)*tSolution v (n+1)=1 at hw
    rw [dirichletSolution_boundary v (n+1+1) ht,zero_mul,sub_zero] at hw
    have hu : dirichletSolution v (n+1+1) (n+1)=1/tSolution v (n+1+1) := (eq_div_iff ht).mpr hw
    rw [hu] at hh
    calc
      _ = (1/tSolution v (n+1+1))*tVariation v dv (n+1+1) := by ring
      _ = _ := hh
      _ = _ := by apply Finset.sum_congr rfl; intro i hi; ring

lemma hasDerivAt_log_tSolution_family (v : ℝ → ℕ → ℝ) (dv : ℕ → ℝ) (x : ℝ)
    (hv : ∀ i, HasDerivAt (fun r => v r i) (dv i) x) (n : ℕ)
    (ht : tSolution (v x) (n+1) ≠ 0) :
    HasDerivAt (fun r => Real.log |tSolution (v r) (n+1)|)
      (∑ i ∈ Finset.range n, tSolution (v x) (i+1)*dirichletSolution (v x) (n+1) (i+1)*dv (i+1)) x := by
  have hh := (hasDerivAt_tSolution_family v dv x hv (n+1)).log ht
  rw [tVariation_div_terminal (v x) dv n ht] at hh
  simpa only [Real.log_abs] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_GraphDistortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma finite_six_tenths_sum (M : ℝ) (hM : 1 < M) (hq : M^(-(3/5:ℝ)) ≤ 1/2) (n : ℕ) :
    ∑ i ∈ Finset.range n, M^(-(3/5:ℝ)*((i:ℝ)+1)) ≤ 2 := by
  have hp : 0 < M := by linarith
  have he (i : ℕ) : M^(-(3/5:ℝ)*((i:ℝ)+1)) = (M^(-(3/5:ℝ)))^i*M^(-(3/5:ℝ)) := by
    rw [← Real.rpow_mul_natCast hp.le,← Real.rpow_add hp]
    congr 1; ring
  simp_rw [he]
  rw [← Finset.sum_mul]
  have hs : ∑ i ∈ Finset.range n, (M^(-(3/5:ℝ)))^i ≤ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (1/2:ℝ)^i := by gcongr
      _ ≤ 2 := sum_geometric_two_le n
  nlinarith [Real.rpow_pos_of_pos hp (-(3/5:ℝ))]

lemma log_dirichlet_row_bound (M : ℝ) (n : ℕ) (t U V : ℕ → ℝ)
    (hM : 1 < M) (hq : M^(-(3/5:ℝ)) ≤ 1/2)
    (ht : ∀ p, 1 ≤ p → p ≤ n → |t p| ≤ M^((p:ℝ)-1))
    (hU : ∀ p, 1 ≤ p → p ≤ n → |U p| ≤ 24/M^((4/5:ℝ)*(p:ℝ)))
    (hV : ∀ p, 1 ≤ p → p ≤ n → |V p| ≤ 2*Real.pi*M) :
    |∑ i ∈ Finset.range n, t (i+1)*U (i+1)*(V (i+1)*U (i+1))| ≤ 2304*Real.pi := by
  have hp : 0 < M := by linarith
  calc
    _ ≤ ∑ i ∈ Finset.range n, |t (i+1)*U (i+1)*(V (i+1)*U (i+1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, (1152*Real.pi)*M^(-(3/5:ℝ)*((i:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      simp only [abs_mul]
      calc
        _ ≤ M^((i:ℝ))* (24/M^((4/5:ℝ)*((i:ℝ)+1)))*
            ((2*Real.pi*M)*(24/M^((4/5:ℝ)*((i:ℝ)+1)))) := by
          gcongr
          · simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using ht (i+1) (by omega) (by omega)
          · simpa only [Nat.cast_add,Nat.cast_one] using hU (i+1) (by omega) (by omega)
          · exact hV (i+1) (by omega) (by omega)
          · simpa only [Nat.cast_add,Nat.cast_one] using hU (i+1) (by omega) (by omega)
        _ = _ := by
          rw [show -(3/5:ℝ)*((i:ℝ)+1)=(i:ℝ)+1-((4/5)*((i:ℝ)+1)+(4/5)*((i:ℝ)+1)) by ring,
            Real.rpow_sub hp,Real.rpow_add hp,Real.rpow_add hp,Real.rpow_one]
          ring
    _ = (1152*Real.pi)*(∑ i ∈ Finset.range n, M^(-(3/5:ℝ)*((i:ℝ)+1))) := by rw [Finset.mul_sum]
    _ ≤ (1152*Real.pi)*2 := mul_le_mul_of_nonneg_left (finite_six_tenths_sum M hM hq n) (by positivity)
    _ = _ := by ring

lemma log_terminal_derivative_bound (k q r : ℝ) (b : ℝ → ℝ) (n : ℕ) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (ht : tSolution (orbitCoefficient k (q+r) (b r)) (n+1) ≠ 0)
    (hd : ∀ p, HasDerivAt (fun x => liftedOrbit k (q+x) (b x) p)
      (dirichletSolution (orbitCoefficient k (q+r) (b r)) (n+1) p) r)
    (hU : ∀ i : Fin n, |dirichletSolution (orbitCoefficient k (q+r) (b r)) (n+1) (i+1)| ≤
      24/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) :
    ∃ D : ℝ, HasDerivAt (fun x => Real.log |tSolution (orbitCoefficient k (q+x) (b x)) (n+1)|) D r ∧
      |D| ≤ 2304*Real.pi := by
  let v : ℝ → ℕ → ℝ := fun x => orbitCoefficient k (q+x) (b x)
  let U:=dirichletSolution (v r) (n+1)
  let V : ℕ → ℝ := fun p => phiSecond k (liftedOrbit k (q+r) (b r) p)
  have hv (p : ℕ) : HasDerivAt (fun x => v x p) (V p*U p) r :=
    (hasDerivAt_potential k _).comp r (hd p)
  have hder:=hasDerivAt_log_tSolution_family v (fun p => V p*U p) r hv n ht
  refine ⟨_,hder,?_⟩
  have hm : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  exact log_dirichlet_row_bound (growthBase k) n (tSolution (v r)) U V hm hq
    (fun p hp' hn => tSolution_abs_le_pow _ _ p hp' hm.le
      (fun i hi hip => potential_bound k (liftedOrbit k (q+r) (b r) i) hk))
    (by
      intro p hp' hpn
      obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
      simpa only [Nat.cast_succ] using hU ⟨i,by omega⟩)
    (fun p hp' hpn => phiSecond_bound k _ hk)

lemma log_ratio_of_derivative_bound (f : ℝ → ℝ) (C R x y : ℝ)
    (_hC : 0 ≤ C) (hx : |x| < R) (hy : |y| < R)
    (hD : ∀ r, |r| < R → ∃ D, HasDerivAt (fun r => Real.log |f r|) D r ∧ |D| ≤ C)
    (hn : ∀ r, |r| < R → f r ≠ 0) :
    Real.exp (-C*|y-x|) ≤ |f y|/|f x| ∧ |f y|/|f x| ≤ Real.exp (C*|y-x|) := by
  have hlog : |Real.log (abs (f y))-Real.log (abs (f x))| ≤ C*|y-x| := by
    have hh:=Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun r => Real.log |f r|) (s := Ioo (-R) R)
      (fun r hr => (hD r (abs_lt.mpr hr)).choose_spec.1.differentiableAt)
      (by
        intro r hr
        obtain ⟨D,hD,hb⟩:=hD r (abs_lt.mpr hr)
        rw [hD.deriv,Real.norm_eq_abs]
        exact hb)
      (convex_Ioo (-R) R) (abs_lt.mp hx) (abs_lt.mp hy)
    exact hh
  have hposx : 0 < |f x| := abs_pos.mpr (hn x hx)
  have hposy : 0 < |f y| := abs_pos.mpr (hn y hy)
  have he : Real.exp (Real.log |f y|-Real.log |f x|)=|f y|/|f x| := by
    rw [Real.exp_sub,Real.exp_log hposy,Real.exp_log hposx]
  constructor
  · rw [← he,Real.exp_le_exp]
    linarith [(abs_le.mp hlog).1]
  · rw [← he,Real.exp_le_exp]
    exact (abs_le.mp hlog).2

lemma contracting_graph_terminal_ratio (k q : ℝ) (b : ℝ → ℝ) (n : ℕ)
    (hk : 0 ≤ k) (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (ht : ∀ r, |r| < 1/4 → tSolution (orbitCoefficient k (q+r) (b r)) (n+1) ≠ 0)
    (hd : ∀ r, |r| < 1/4 → ∀ p, HasDerivAt (fun x => liftedOrbit k (q+x) (b x) p)
      (dirichletSolution (orbitCoefficient k (q+r) (b r)) (n+1) p) r)
    (hU : ∀ r, |r| < 1/4 → ∀ i : Fin n,
      |dirichletSolution (orbitCoefficient k (q+r) (b r)) (n+1) (i+1)| ≤
      24/growthBase k^((4/5:ℝ)*((i:ℝ)+1)))
    {x y : ℝ} (hx : |x| < 1/4) (hy : |y| < 1/4) :
    Real.exp (-1152*Real.pi) ≤
      |tSolution (orbitCoefficient k (q+y) (b y)) (n+1)|/
      |tSolution (orbitCoefficient k (q+x) (b x)) (n+1)| ∧
      |tSolution (orbitCoefficient k (q+y) (b y)) (n+1)|/
      |tSolution (orbitCoefficient k (q+x) (b x)) (n+1)| ≤ Real.exp (1152*Real.pi) := by
  have hh:=log_ratio_of_derivative_bound
    (fun r => tSolution (orbitCoefficient k (q+r) (b r)) (n+1)) (2304*Real.pi) (1/4) x y
    (by positivity) hx hy
    (fun r hr => log_terminal_derivative_bound k q r b n hk hq (ht r hr) (hd r hr) (hU r hr)) ht
  have hxy : |y-x| ≤ 1/2 := by
    have hh:=norm_sub_le y x
    simp only [Real.norm_eq_abs] at hh
    linarith
  constructor
  · apply le_trans _ hh.1
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  · apply le_trans hh.2
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_GraphSubsetCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

lemma hasFDerivWithinAt_of_regular_level {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (F : E × ℝ → ℝ) (b : E → ℝ) (s : Set E) (x : E)
    (A : E →L[ℝ] ℝ) (t : ℝ)
    (hD : HasStrictFDerivAt F
      (A.comp (ContinuousLinearMap.fst ℝ E ℝ)+t • ContinuousLinearMap.snd ℝ E ℝ) (x,b x))
    (ht : t ≠ 0) (hb : ContinuousWithinAt b s x)
    (hlevel : ∀ᶠ y in 𝓝[s] x, F (y,b y)=F (x,b x)) :
    HasFDerivWithinAt b ((-t⁻¹) • A) s x := by
  let L : (E × ℝ) →L[ℝ] ℝ :=
    A.comp (ContinuousLinearMap.fst ℝ E ℝ)+t • ContinuousLinearMap.snd ℝ E ℝ
  have hInv : (L.comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := t⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
  let ψ := hD.implicitFunctionOfProdDomain hInv
  have he : ∀ᶠ y in 𝓝[s] x, ψ y=b y := by
    have hpair : Tendsto (fun y => (y,b y)) (𝓝[s] x) (𝓝 (x,b x)) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.prodMk_nhds hb
    filter_upwards [hpair.eventually (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv),hlevel] with y hy hy'
    exact hy.mp hy'
  have he0 : ψ x=b x := ((hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv).self_of_nhds).mp rfl
  have hd := (hD.hasStrictFDerivAt_implicitFunctionOfProdDomain hInv).hasFDerivAt.hasFDerivWithinAt (s := s)
  have heq : -(L.comp (ContinuousLinearMap.inr ℝ E ℝ)).inverse.comp
      (L.comp (ContinuousLinearMap.inl ℝ E ℝ)) = (-t⁻¹) • A := by
    apply ContinuousLinearMap.ext
    intro z
    have hh : (L.comp (ContinuousLinearMap.inr ℝ E ℝ)).inverse
        ((L.comp (ContinuousLinearMap.inl ℝ E ℝ)) z)=t⁻¹*A z := by
      apply hInv.inverse_apply_eq.mpr
      simp [L,ht]
    change -((L.comp (ContinuousLinearMap.inr ℝ E ℝ)).inverse
      ((L.comp (ContinuousLinearMap.inl ℝ E ℝ)) z))=(-t⁻¹)*A z
    rw [hh,neg_mul]
  change HasFDerivWithinAt ψ _ s x at hd
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq (EventuallyEq.symm he) he0.symm
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_GraphUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma graph_local_coincidence (F : ℝ × ℝ → ℝ) (b c : ℝ → ℝ)
    (s : Set ℝ) (x u v : ℝ)
    (hD : HasStrictFDerivAt F
      (u • ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ) (x,b x))
    (hv : v ≠ 0) (he : b x=c x) (hb : ContinuousWithinAt b s x)
    (hc : ContinuousWithinAt c s x)
    (hFb : ∀ᶠ y in 𝓝[s] x, F (y,b y)=F (x,b x))
    (hFc : ∀ᶠ y in 𝓝[s] x, F (y,c y)=F (x,b x)) :
    b =ᶠ[𝓝[s] x] c := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ :=
    u • ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hInv : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := v⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext; intro z; simp [L,hv]
    · apply ContinuousLinearMap.ext; intro z; simp [L,hv]
  have hbpair : Tendsto (fun y => (y,b y)) (𝓝[s] x) (𝓝 (x,b x)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.prodMk_nhds hb
  have hcpair : Tendsto (fun y => (y,c y)) (𝓝[s] x) (𝓝 (x,b x)) := by
    rw [he]
    exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.prodMk_nhds hc
  filter_upwards [hbpair.eventually (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv),
    hcpair.eventually (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv),hFb,hFc] with y hyb hyc h1 h2
  exact (hyb.mp h1).symm.trans (hyc.mp h2)

lemma eqOn_of_locally_coincident {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [T2Space β] (s : Set α) (f g : α → β)
    (hs : IsPreconnected s) (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hloc : ∀ x ∈ s, f x=g x → f =ᶠ[𝓝[s] x] g)
    (x : α) (hx : x ∈ s) (he : f x=g x) : EqOn f g s := by
  let : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  have hc : IsClosed {y : s | f y=g y} := isClosed_eq hf.domRestrict hg.domRestrict
  have ho : IsOpen {y : s | f y=g y} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hh := hloc y y.property hy
    have ht : Tendsto (Subtype.val : s → α) (𝓝 y) (𝓝[s] (y:α)) :=
      tendsto_nhdsWithin_iff.mpr ⟨continuous_subtype_val.tendsto y,Filter.Eventually.of_forall (fun z => z.property)⟩
    exact ht.eventually hh
  have hu : {y : s | f y=g y}=univ := IsClopen.eq_univ (s := {y : s | f y=g y}) ⟨hc,ho⟩ ⟨⟨x,hx⟩,he⟩
  intro y hy
  have hh : (⟨y,hy⟩ : s) ∈ ({z : s | f z=g z}) := by rw [hu]; trivial
  exact hh

lemma regular_graphs_coincide (F : ℝ × ℝ → ℝ) (b c : ℝ → ℝ)
    (s : Set ℝ) (hs : IsPreconnected s) (hb : ContinuousOn b s) (hc : ContinuousOn c s)
    (L : ℝ) (hFb : ∀ y ∈ s, F (y,b y)=L) (hFc : ∀ y ∈ s, F (y,c y)=L)
    (hreg : ∀ y ∈ s, ∃ u v : ℝ, v ≠ 0 ∧ HasStrictFDerivAt F
      (u • ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ) (y,b y))
    (x : ℝ) (hx : x ∈ s) (he : b x=c x) : EqOn b c s := by
  apply eqOn_of_locally_coincident s b c hs hb hc _ x hx he
  intro y hy hey
  obtain ⟨u,v,hv,hD⟩:=hreg y hy
  apply graph_local_coincidence F b c s y u v hD hv hey (hb y hy) (hc y hy)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hFb z hz,hFb y hy]
  · filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hFc z hz,hFb y hy]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_StrictGraphCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

lemma hasStrictDerivAt_of_regular_level (F : ℝ × ℝ → ℝ) (b : ℝ → ℝ) (x s t : ℝ)
    (hD : HasStrictFDerivAt F
      (s • ContinuousLinearMap.fst ℝ ℝ ℝ+t • ContinuousLinearMap.snd ℝ ℝ ℝ) (x,b x))
    (ht : t ≠ 0) (hb : ContinuousAt b x)
    (hlevel : ∀ᶠ y in 𝓝 x, F (y,b y)=F (x,b x)) :
    HasStrictDerivAt b (-s/t) x := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := s • ContinuousLinearMap.fst ℝ ℝ ℝ+t • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hInv : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := t⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
  let ψ := hD.implicitFunctionOfProdDomain hInv
  have he : ∀ᶠ y in 𝓝 x, ψ y=b y := by
    have hpair : Tendsto (fun y => (y,b y)) (𝓝 x) (𝓝 (x,b x)) :=
      tendsto_id.prodMk_nhds hb
    filter_upwards [hpair.eventually (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv),hlevel] with y hy hy'
    exact hy.mp hy'
  have hd := (hD.hasStrictFDerivAt_implicitFunctionOfProdDomain hInv).hasStrictDerivAt
  have heq : (-(L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).inverse.comp
      (L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ))) 1 = -s/t := by
    have hh : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).inverse
        ((L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1)=s/t := by
      apply hInv.inverse_apply_eq.mpr
      simp only [L,ContinuousLinearMap.comp_apply,add_apply,smul_apply]
      change s*1+t*0=s*0+t*(s/t)
      field_simp
      ring
    change -(L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).inverse
      ((L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1) = -s/t
    rw [hh,neg_div]
  change HasStrictDerivAt ψ _ x at hd
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq he
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ContractingGraphPack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

lemma continuous_contracting_graph_pack_full (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (S : Set (ℝ × ℝ))
    (ht : ∀ z ∈ S, tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0)
    (hU : ∀ z ∈ S, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
    ∃ b : (ℝ × ℝ) → ℝ → ℝ,
      ContinuousOn (fun z : (ℝ × ℝ) × ℝ => b z.1 z.2) (S ×ˢ Icc (-(1/4)) (1/4)) ∧
      ∀ z ∈ S, b z 0=z.2 ∧
      (∀ r, |r| ≤ 1/4 → liftedOrbit k (z.1+r) (b z r) (n+1)=liftedOrbit k z.1 z.2 (n+1)) ∧
      (∀ r, |r| ≤ 1/4 → tSolution (orbitCoefficient k (z.1+r) (b z r)) (n+1) ≠ 0) ∧
      (∀ r, |r| < 1/4 → HasStrictDerivAt (b z)
        (boundaryValue (orbitCoefficient k (z.1+r) (b z r)) (n+1)) r) ∧
      (∀ r, |r| ≤ 1/4 →
        |boundaryValue (orbitCoefficient k (z.1+r) (b z r)) (n+1)| ≤
          24/growthBase k^((4/5:ℝ))) ∧
      (∀ r t, |r| ≤ 1/4 → |t| ≤ 1/4 →
        |b z r-b z t| ≤ (24/growthBase k^((4/5:ℝ)))*|r-t|) ∧
      (∀ r t, |r| < 1/4 → |t| < 1/4 →
        Real.exp (-1152*Real.pi) ≤
          |tSolution (orbitCoefficient k (z.1+r) (b z r)) (n+1)|/
          |tSolution (orbitCoefficient k (z.1+t) (b z t)) (n+1)| ∧
        |tSolution (orbitCoefficient k (z.1+r) (b z r)) (n+1)|/
          |tSolution (orbitCoefficient k (z.1+t) (b z t)) (n+1)| ≤ Real.exp (1152*Real.pi)) ∧
      (∀ r, |r| ≤ 1/4 → ∀ i : Fin n,
        |liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k z.1 z.2 (i+1)| ≤
          8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) ∧
      (∀ r t, |r| ≤ 1/4 → |t| ≤ 1/4 → ∀ i : Fin n,
        |liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k (z.1+t) (b z t) (i+1)| ≤
          24*|r-t|/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
  have hp : 0 < growthBase k := by have := growthBase_ge_four k hk; linarith
  obtain ⟨b,hcont,hb⟩ := jointly_continuous_dirichlet_family k n hn hk hq hsmall S ht hU
  refine ⟨b,hcont,?_⟩
  intro z hz
  obtain ⟨hb0,hterm,hbound,hLip⟩ := hb z hz
  obtain ⟨ht',hd,hU'⟩ := contracting_family_derivatives_of_bounds k z.1 z.2 n hn hk hq hsmall
    (ht z hz) (hU z hz) (b z) hterm hbound hLip
  have hLip' (r t : ℝ) (hr : |r| ≤ 1/4) (ht : |t| ≤ 1/4) :
      |b z r-b z t| ≤ (24/growthBase k^((4/5:ℝ)))*|r-t| := by
    simpa only [Fin.val_zero,Nat.cast_zero,zero_add,mul_one,liftedOrbit_one,div_mul_eq_mul_div]
      using hLip r t hr ht (⟨0,hn⟩:Fin n)
  refine ⟨hb0,hterm,ht',?_,?_,hLip',?_,hbound,hLip⟩
  · intro r hr
    apply hasStrictDerivAt_of_regular_level
      (fun w : ℝ × ℝ => liftedOrbit k (z.1+w.1) w.2 (n+1)) (b z) r
      (sSolution (orbitCoefficient k (z.1+r) (b z r)) (n+1))
      (tSolution (orbitCoefficient k (z.1+r) (b z r)) (n+1))
      (hasStrictFDerivAt_liftedOrbit_shift k z.1 r (b z r) (n+1)) (ht' r hr.le)
    · exact continuousAt_of_local_lipschitz (b z) r (1/4) (24/growthBase k^((4/5:ℝ)))
        (by positivity) hr hLip'
    · filter_upwards [(continuous_abs.continuousAt.eventually (Iio_mem_nhds hr))] with y hy
      exact (hterm y hy.le).trans (hterm r hr.le).symm
  · intro r hr
    simpa only [Fin.val_zero,Nat.cast_zero,zero_add,mul_one,dirichletSolution,linearSolution] using hU' r hr (⟨0,hn⟩:Fin n)
  · intro r t hr ht
    exact contracting_graph_terminal_ratio k z.1 (b z) n hk hq
      (fun r hr => ht' r hr.le) hd (fun r hr => hU' r hr.le) ht hr
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ChangeVariablesBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy

lemma weighted_sweep_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (s : Set E) (f : E → E)
    (D : E → E →L[ℝ] E) (c : ℝ) (g w : E → ℝ≥0∞) (δ : ℝ≥0∞)
    (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hinj : InjOn f s)
    (hlo : ∀ x ∈ s, c ≤ |(D x).det|)
    (hobs : ∀ x ∈ s, w x ≤ g (f x)+δ) :
    ENNReal.ofReal c*(∫⁻ x in s, w x ∂μ) ≤
      (∫⁻ x in f '' s, g x ∂μ)+ENNReal.ofReal c*δ*μ s := by
  calc
    _ ≤ ENNReal.ofReal c*(∫⁻ x in s, g (f x)+δ ∂μ) :=
      mul_le_mul_of_nonneg_left (setLIntegral_mono' hs hobs) (by positivity)
    _ = ENNReal.ofReal c*(∫⁻ x in s, g (f x) ∂μ)+ENNReal.ofReal c*δ*μ s := by
      rw [lintegral_add_right _ measurable_const]
      simp [mul_add,mul_assoc]
    _ ≤ _ := add_le_add (by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hD hinj g,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' hs (fun x hx => mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hlo x hx)) (by positivity))) le_rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_GraphJacobians
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma planeMatrix_det (a b c d : ℝ) : (planeMatrix a b c d).det=a*d-b*c := by
  change (planeMatrix a b c d).toLinearMap.det=_
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,Module.Basis.coe_finTwoProd_repr]

lemma transverse_jacobian_bounds (A B C x α β c C₀ : ℝ)
    (hB : B ≠ 0) (hC : C ≠ 0) (_hc : 0 ≤ c) (hC₀ : 0 ≤ C₀)
    (hα : 0 ≤ α) (_hβ : 0 ≤ β) (hsmall : α*β ≤ 1)
    (hlo : c ≤ |B/C|) (hhi : |B/C| ≤ C₀)
    (hA : |A/B| ≤ α) (hx : |x| ≤ β) :
    c*(1-α*β) ≤ |(B+A*x)/C| ∧ |(B+A*x)/C| ≤ C₀*(1+α*β) := by
  have he : (B+A*x)/C=(B/C)*(1+(A/B)*x) := by field_simp
  have hprod : |A/B*x| ≤ α*β := by rw [abs_mul]; exact mul_le_mul hA hx (abs_nonneg _) hα
  have hupper : |1+(A/B)*x| ≤ 1+α*β := by
    calc
      _ ≤ |(1:ℝ)|+|A/B*x| := abs_add_le _ _
      _ ≤ _ := by simpa using add_le_add (le_refl (1:ℝ)) hprod
  have hlower : 1-α*β ≤ |1+(A/B)*x| := by
    have ht := abs_sub_abs_le_abs_sub (1:ℝ) (-A/B*x)
    simp only [abs_one,neg_div,neg_mul,abs_neg,sub_neg_eq_add] at ht
    linarith
  rw [he,abs_mul]
  exact ⟨mul_le_mul hlo hlower (by linarith) (abs_nonneg _),
    mul_le_mul hhi hupper (abs_nonneg _) hC₀⟩

lemma sweep_graph_derivative (F : ℝ × ℝ → ℝ) (X : ℝ → ℝ) (Θ : ℝ × ℝ → ℝ)
    (S : Set (ℝ × ℝ)) (z : ℝ × ℝ) (A B C D x' : ℝ)
    (hF : HasStrictFDerivAt F (planeDual C D) (z.1,Θ z))
    (hR : HasStrictFDerivAt F (planeDual A B) (X z.2,z.2))
    (hX : HasStrictDerivAt X x' z.2)
    (hD : D ≠ 0) (hΘ : ContinuousWithinAt Θ S z)
    (hlevel : ∀ᶠ w in 𝓝[S] z, F (w.1,Θ w)=F (X w.2,w.2))
    (hlevel0 : F (z.1,Θ z)=F (X z.2,z.2)) :
    HasFDerivWithinAt (fun w => (w.1,Θ w))
      (planeMatrix 1 0 (-C/D) ((B+A*x')/D)) S z := by
  let G : (ℝ × ℝ) × ℝ → ℝ := fun w => F (w.1.1,w.2)-F (X w.1.2,w.1.2)
  let L := planeDual C (-(B+A*x'))
  have hGD : HasStrictFDerivAt G
      (L.comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+D • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (z,Θ z) := by
    have hp := hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (z,Θ z))
    have h1 := (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := z)).comp (z,Θ z) hp
    have h2 := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := z)).comp (z,Θ z) hp
    have h3 := hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (z,Θ z))
    have hh := (hF.comp (z,Θ z) (h1.prodMk h3)).sub
      (hR.comp (z,Θ z) ((hX.hasStrictFDerivAt.comp (z,Θ z) h2).prodMk h2))
    apply hh.congr_fderiv
    apply ContinuousLinearMap.ext
    intro w
    change C*w.1.1+D*w.2-(A*(w.1.2*x')+B*w.1.2)=
      (C*w.1.1+(-(B+A*x'))*w.1.2)+D*w.2
    ring
  have hθ := hasFDerivWithinAt_of_regular_level G Θ S z L D hGD hD hΘ (by
    filter_upwards [hlevel] with w hw
    dsimp only [G]
    rw [hw,hlevel0]; ring)
  have ht := (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).hasFDerivWithinAt.prodMk hθ
  apply ht.congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  apply Prod.ext
  · change w.1=1*w.1+0*w.2
    ring
  · change (-D⁻¹)*(C*w.1+(-(B+A*x'))*w.2)=(-C/D)*w.1+((B+A*x')/D)*w.2
    ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_TransverseSweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma transverse_intersections_unique (x y X Y α β : ℝ)
    (_hα : 0 ≤ α) (hβ : 0 ≤ β) (hsmall : α*β < 1)
    (hx : |x-X| ≤ α*|y-Y|) (hy : |y-Y| ≤ β*|x-X|) : x=X ∧ y=Y := by
  have hyy : |y-Y| ≤ (α*β)*|y-Y| := by
    calc
      _ ≤ β*|x-X| := hy
      _ ≤ β*(α*|y-Y|) := mul_le_mul_of_nonneg_left hx hβ
      _ = _ := by ring
  have he : |y-Y|=0 := by nlinarith [abs_nonneg (y-Y)]
  have hx0 : |x-X|=0 := by rw [he,mul_zero] at hx; exact le_antisymm hx (abs_nonneg _)
  exact ⟨sub_eq_zero.mp (abs_eq_zero.mp hx0),sub_eq_zero.mp (abs_eq_zero.mp he)⟩

lemma transverse_sweep_injective (F : ℝ × ℝ → ℝ) (X : ℝ → ℝ) (Θ : ℝ × ℝ → ℝ)
    (I D : Set ℝ) (α β : ℝ) (hI : IsPreconnected I)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsmall : α*β < 1)
    (hX : ∀ y ∈ D, X y ∈ I)
    (hbase : ∀ y ∈ D, Θ (X y,y)=y)
    (hcont : ∀ y ∈ D, ContinuousOn (fun u => Θ (u,y)) I)
    (hlevel : ∀ y ∈ D, ∀ u ∈ I, F (u,Θ (u,y))=F (X y,y))
    (hreg : ∀ y ∈ D, ∀ u ∈ I, ∃ a b : ℝ, b ≠ 0 ∧
      HasStrictFDerivAt F (planeDual a b) (u,Θ (u,y)))
    (hforward : ∀ y ∈ D, ∀ z ∈ D, |X y-X z| ≤ α*|y-z|)
    (hbackward : ∀ y ∈ D, ∀ u ∈ I, ∀ v ∈ I, |Θ (u,y)-Θ (v,y)| ≤ β*|u-v|) :
    InjOn (fun z : ℝ × ℝ => (z.1,Θ z)) (I ×ˢ D) := by
  intro z hz w hw he
  have hu : z.1=w.1 := by
    have hh := congrArg (fun v : ℝ × ℝ => v.1) he
    exact hh
  have hθ : Θ (z.1,z.2)=Θ (z.1,w.2) := by
    have hh := congrArg (fun v : ℝ × ℝ => v.2) he
    change Θ (z.1,z.2)=Θ (w.1,w.2) at hh
    rwa [← hu] at hh
  have hLv : F (X z.2,z.2)=F (X w.2,w.2) := by
    rw [← hlevel z.2 hz.2 z.1 hz.1,← hlevel w.2 hw.2 z.1 hz.1,hθ]
  have hc := regular_graphs_coincide F (fun u => Θ (u,z.2)) (fun u => Θ (u,w.2)) I hI
    (hcont z.2 hz.2) (hcont w.2 hw.2) (F (X z.2,z.2)) (hlevel z.2 hz.2)
    (fun u hu => (hlevel w.2 hw.2 u hu).trans hLv.symm) (hreg z.2 hz.2) z.1 hz.1 hθ
  have hby : |z.2-w.2| ≤ β*|X z.2-X w.2| := by
    have hh := hbackward z.2 hz.2 (X z.2) (hX z.2 hz.2) (X w.2) (hX w.2 hw.2)
    have hc' : Θ (X w.2,z.2)=Θ (X w.2,w.2) := hc (hX w.2 hw.2)
    rw [hbase z.2 hz.2,hc',hbase w.2 hw.2] at hh
    exact hh
  have hy := (transverse_intersections_unique (X z.2) z.2 (X w.2) w.2 α β hα hβ hsmall
    (hforward z.2 hz.2 w.2 hw.2) hby).2
  exact Prod.ext hu hy
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_TorusIntegral
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy

lemma unit_cell_integral (g : Torus → ℝ≥0∞) (hg : Measurable g) (a b : ℝ) :
    (∫⁻ z in Ioc a (a+1) ×ˢ Ioc b (b+1), g (liftProjection z)) = ∫⁻ z, g z ∂area := by
  have h := (AddCircle.measurePreserving_mk (1:ℝ) a).prod (AddCircle.measurePreserving_mk (1:ℝ) b)
  rw [Measure.prod_restrict] at h
  exact h.lintegral_comp hg

lemma interval_four_cell_cover (x : ℝ) (hx : x ∈ Ioc (-2:ℝ) 2) :
    ∃ j : Fin 4, x ∈ Ioc ((j:ℝ)-2) ((j:ℝ)-2+1) := by
  by_cases h1 : x ≤ -1
  · exact ⟨0,by norm_num at *; exact ⟨hx.1,h1⟩⟩
  by_cases h2 : x ≤ 0
  · exact ⟨1,by norm_num at *; exact ⟨by linarith,h2⟩⟩
  by_cases h3 : x ≤ 1
  · exact ⟨2,by norm_num at *; exact ⟨by linarith,h3⟩⟩
  · exact ⟨3,by norm_num at *; exact ⟨by linarith,hx.2⟩⟩

lemma bounded_lift_integral (g : Torus → ℝ≥0∞) (hg : Measurable g)
    (S : Set (ℝ × ℝ)) (hS : S ⊆ Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2) :
    (∫⁻ z in S, g (liftProjection z)) ≤ 16*(∫⁻ z, g z ∂area) := by
  let cell : (Fin 4 × Fin 4) → Set (ℝ × ℝ) := fun j =>
    Ioc ((j.1:ℝ)-2) ((j.1:ℝ)-2+1) ×ˢ Ioc ((j.2:ℝ)-2) ((j.2:ℝ)-2+1)
  have hcover : S ⊆ ⋃ j, cell j := by
    intro z hz
    obtain ⟨i,hi⟩ := interval_four_cell_cover z.1 (hS hz).1
    obtain ⟨j,hj⟩ := interval_four_cell_cover z.2 (hS hz).2
    exact mem_iUnion.mpr ⟨(i,j),hi,hj⟩
  calc
    _ ≤ ∫⁻ z in ⋃ j, cell j, g (liftProjection z) := lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ z in cell j, g (liftProjection z) := lintegral_iUnion_le _ _
    _ = _ := by simp only [cell,unit_cell_integral g hg,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]; norm_num
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_TransportCarry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma actual_backward_carry_full (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (D : Set ℝ) (X X' : ℝ → ℝ) (l u : ℝ)
    (hlen : u-l < 1/4)
    (hXI : ∀ y ∈ D, X y ∈ Icc l u)
    (hX : ∀ y ∈ D, HasStrictDerivAt X (X' y) y)
    (hXs : ∀ y ∈ D, |X' y| ≤ 24/growthBase k^((4/5:ℝ)))
    (hXL : ∀ y ∈ D, ∀ z ∈ D, |X y-X z| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z|)
    (htrans : (24/growthBase k^((4/5:ℝ)))^2 < 1)
    (ht : ∀ y ∈ D, tSolution (orbitCoefficient k (X y) y) (n+1) ≠ 0)
    (hU : ∀ y ∈ D, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k (X y) y) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
    ∃ Θ : ℝ × ℝ → ℝ, ∃ J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      ContinuousOn Θ (Icc l u ×ˢ D) ∧
      (∀ y ∈ D, Θ (X y,y)=y) ∧
      (∀ y ∈ D, ∀ v ∈ Icc l u,
        liftedOrbit k v (Θ (v,y)) (n+1)=liftedOrbit k (X y) y (n+1)) ∧
      InjOn (fun z : ℝ × ℝ => (z.1,Θ z)) (Icc l u ×ˢ D) ∧
      (∀ z ∈ Icc l u ×ˢ D, HasFDerivWithinAt (fun w => (w.1,Θ w)) (J z) (Icc l u ×ˢ D) z) ∧
      (∀ z ∈ Icc l u ×ˢ D,
        Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2) ≤ |(J z).det| ∧
        |(J z).det| ≤ Real.exp (1152*Real.pi)*(1+(24/growthBase k^((4/5:ℝ)))^2)) ∧
      (∀ y ∈ D, ∀ v ∈ Icc l u,
        |Θ (v,y)-y| ≤ (24/growthBase k^((4/5:ℝ)))*|v-X y| ∧
        ∀ i : Fin n, |liftedOrbit k v (Θ (v,y)) (i+1)-liftedOrbit k (X y) y (i+1)| ≤
          8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
  classical
  let a : ℝ := 24/growthBase k^((4/5:ℝ))
  have hp : 0 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have ha : 0 ≤ a := div_nonneg (by norm_num) (Real.rpow_pos_of_pos hp _).le
  let S : Set (ℝ × ℝ) := (fun y => (X y,y)) '' D
  have htS : ∀ z ∈ S, tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0 := by
    rintro z ⟨y,hy,rfl⟩; exact ht y hy
  have hUS : ∀ z ∈ S, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ)) := by
    rintro z ⟨y,hy,rfl⟩; exact hU y hy
  obtain ⟨b,hbc,hb⟩ := continuous_contracting_graph_pack_full k n hn hk hq hsmall S htS hUS
  let Θ : ℝ × ℝ → ℝ := fun z => b (X z.2,z.2) (z.1-X z.2)
  have hmem (y : ℝ) (hy : y ∈ D) : (X y,y) ∈ S := mem_image_of_mem _ hy
  have hdist (y : ℝ) (hy : y ∈ D) (v : ℝ) (hv : v ∈ Icc l u) : |v-X y| < 1/4 := by
    have hxy := hXI y hy
    apply abs_lt.mpr
    constructor <;> linarith [hxy.1,hxy.2,hv.1,hv.2]
  have hXc : ContinuousOn X D := fun y hy => (hX y hy).hasDerivAt.continuousAt.continuousWithinAt
  have hXcs : ContinuousOn (fun z : ℝ × ℝ => X z.2) (Icc l u ×ˢ D) :=
    hXc.comp continuous_snd.continuousOn (fun z hz => hz.2)
  have hΘ : ContinuousOn Θ (Icc l u ×ˢ D) := by
    apply hbc.comp ((hXcs.prodMk continuous_snd.continuousOn).prodMk
      (continuous_fst.continuousOn.sub hXcs))
    intro z hz
    exact ⟨hmem z.2 hz.2,abs_le.mp (hdist z.2 hz.2 z.1 hz.1).le⟩
  have hbase (y : ℝ) (hy : y ∈ D) : Θ (X y,y)=y := by
    simpa [Θ] using (hb (X y,y) (hmem y hy)).1
  have hlevel (y : ℝ) (hy : y ∈ D) (v : ℝ) (hv : v ∈ Icc l u) :
      liftedOrbit k v (Θ (v,y)) (n+1)=liftedOrbit k (X y) y (n+1) := by
    simpa only [add_sub_cancel] using (hb (X y,y) (hmem y hy)).2.1 (v-X y) (hdist y hy v hv).le
  have htn (y : ℝ) (hy : y ∈ D) (v : ℝ) (hv : v ∈ Icc l u) :
      tSolution (orbitCoefficient k v (Θ (v,y))) (n+1) ≠ 0 := by
    simpa only [add_sub_cancel] using (hb (X y,y) (hmem y hy)).2.2.1 (v-X y) (hdist y hy v hv).le
  have hback (y : ℝ) (hy : y ∈ D) (v : ℝ) (hv : v ∈ Icc l u) (w : ℝ) (hw : w ∈ Icc l u) :
      |Θ (v,y)-Θ (w,y)| ≤ a*|v-w| := by
    simpa only [sub_sub_sub_cancel_right] using (hb (X y,y) (hmem y hy)).2.2.2.2.2.1
      (v-X y) (w-X y) (hdist y hy v hv).le (hdist y hy w hw).le
  let J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := fun z =>
    planeMatrix 1 0
      (-sSolution (orbitCoefficient k z.1 (Θ z)) (n+1)/tSolution (orbitCoefficient k z.1 (Θ z)) (n+1))
      ((tSolution (orbitCoefficient k (X z.2) z.2) (n+1)+sSolution (orbitCoefficient k (X z.2) z.2) (n+1)*X' z.2)/
        tSolution (orbitCoefficient k z.1 (Θ z)) (n+1))
  refine ⟨Θ,J,hΘ,hbase,hlevel,?_,?_,?_,?_⟩
  · apply transverse_sweep_injective (fun z : ℝ × ℝ => liftedOrbit k z.1 z.2 (n+1)) X Θ
      (Icc l u) D a a (convex_Icc l u).isPreconnected ha ha (by simpa only [← sq] using htrans)
      hXI hbase
    · intro y hy
      exact hΘ.comp (continuousOn_id.prodMk continuousOn_const) (fun v hv => ⟨hv,hy⟩)
    · exact hlevel
    · intro y hy v hv
      exact ⟨_,_,htn y hy v hv,hasStrictFDerivAt_liftedOrbit k v (Θ (v,y)) (n+1)⟩
    · exact hXL
    · exact hback
  · intro z hz
    apply sweep_graph_derivative (fun z : ℝ × ℝ => liftedOrbit k z.1 z.2 (n+1)) X Θ
      (Icc l u ×ˢ D) z _ _ _ _ _
      (hasStrictFDerivAt_liftedOrbit k z.1 (Θ z) (n+1))
      (hasStrictFDerivAt_liftedOrbit k (X z.2) z.2 (n+1)) (hX z.2 hz.2)
      (htn z.2 hz.2 z.1 hz.1) (hΘ z hz) _ (hlevel z.2 hz.2 z.1 hz.1)
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hlevel w.2 hw.2 w.1 hw.1
  · intro z hz
    have hr := (hb (X z.2,z.2) (hmem z.2 hz.2)).2.2.2.2.2.2.1 0 (z.1-X z.2)
      (by norm_num) (hdist z.2 hz.2 z.1 hz.1)
    simp only [add_zero,add_sub_cancel,(hb (X z.2,z.2) (hmem z.2 hz.2)).1] at hr
    have hs0 := (hb (X z.2,z.2) (hmem z.2 hz.2)).2.2.2.2.1 0 (by norm_num)
    simp only [add_zero,(hb (X z.2,z.2) (hmem z.2 hz.2)).1,boundaryValue,neg_div,abs_neg] at hs0
    have hbj := transverse_jacobian_bounds
      (sSolution (orbitCoefficient k (X z.2) z.2) (n+1))
      (tSolution (orbitCoefficient k (X z.2) z.2) (n+1))
      (tSolution (orbitCoefficient k z.1 (Θ z)) (n+1)) (X' z.2)
      a a (Real.exp (-1152*Real.pi)) (Real.exp (1152*Real.pi))
      (ht z.2 hz.2) (htn z.2 hz.2 z.1 hz.1) (Real.exp_pos _).le (Real.exp_pos _).le
      ha ha (by simpa only [← sq] using htrans.le)
      (by simpa only [abs_div] using hr.1) (by simpa only [abs_div] using hr.2)
      hs0 (hXs z.2 hz.2)
    simpa only [J,planeMatrix_det,one_mul,zero_mul,sub_zero,← sq] using hbj
  · intro y hy v hv
    refine ⟨?_,?_⟩
    · have hh := hback y hy v hv (X y) (hXI y hy)
      rw [hbase y hy] at hh
      exact hh
    · intro i
      have hh := (hb (X y,y) (hmem y hy)).2.2.2.2.2.2.2.1 (v-X y) (hdist y hy v hv).le i
      simpa only [add_sub_cancel] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_EndpointTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma liftIter_neg_swap (k : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    liftIter k (-(n:ℤ)) z=(liftIter k (n:ℤ) z.swap).swap := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show ((n+1:ℕ):ℤ)=1+(n:ℤ) by omega,show -(1+(n:ℤ))=(-1)+(-(n:ℤ)) by ring,
      liftIter_add,liftIter_add,ih]
    simp only [liftIter,zpow_neg_one,zpow_one,Equiv.Perm.inv_def,liftStep_symm_apply,liftStep_apply,
      Prod.fst_swap,Prod.snd_swap,Prod.swap_prod_mk]
lemma graph_endpoint_close (k : ℝ) (hk : 0 ≤ k) (z w : ℝ × ℝ) (n B : ℕ) (hn : 1 ≤ n)
    (hB : B=n ∨ B=n+1)
    (hterm : liftedOrbit k z.2 z.1 (n+1)=liftedOrbit k w.2 w.1 (n+1))
    (hbound : ∀ i : Fin n,
      |liftedOrbit k z.2 z.1 (i+1)-liftedOrbit k w.2 w.1 (i+1)| ≤
        8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) :
    dist (liftIter k (B:ℤ) z) (liftIter k (B:ℤ) w) ≤
      8/growthBase k^((4/5:ℝ)*(B-1:ℕ)) := by
  have hM : 1 ≤ growthBase k := by have := growthBase_ge_four k hk; linarith
  have hMn : 0 ≤ 8/growthBase k^((4/5:ℝ)*(n:ℝ)) := by positivity
  have hn' : n-1+1=n := by omega
  have hlast := hbound (⟨n-1,by omega⟩ : Fin n)
  have hreal : ((n-1:ℕ):ℝ)+1=n := by exact_mod_cast hn'
  simp only [hn',hreal] at hlast
  have he : dist (liftIter k (B:ℤ) z) (liftIter k (B:ℤ) w) ≤
      8/growthBase k^((4/5:ℝ)*(n:ℝ)) := by
    rcases hB with rfl|rfl
    · rw [liftIter_nat,liftIter_nat,Prod.dist_eq,Real.dist_eq,Real.dist_eq,hterm,sub_self,abs_zero]
      exact max_le hMn hlast
    · rw [liftIter_nat,liftIter_nat,Prod.dist_eq,Real.dist_eq,Real.dist_eq,liftedOrbit_step,
        liftedOrbit_step,hterm,sub_self,abs_zero]
      have he : |phi k (liftedOrbit k w.2 w.1 (n+1))-liftedOrbit k z.2 z.1 n-
          (phi k (liftedOrbit k w.2 w.1 (n+1))-liftedOrbit k w.2 w.1 n)| =
          |liftedOrbit k z.2 z.1 n-liftedOrbit k w.2 w.1 n| := by
        rw [sub_sub_sub_cancel_left,abs_sub_comm]
      rw [he]
      exact max_le hlast hMn
  apply he.trans
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hM
  have hle : (B-1:ℕ) ≤ n := by rcases hB with rfl|rfl <;> omega
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (by norm_num)
lemma graph_backward_endpoint_close (k : ℝ) (hk : 0 ≤ k) (z w : ℝ × ℝ) (n B : ℕ) (hn : 1 ≤ n)
    (hB : B=n ∨ B=n+1)
    (hterm : liftedOrbit k z.1 z.2 (n+1)=liftedOrbit k w.1 w.2 (n+1))
    (hbound : ∀ i : Fin n,
      |liftedOrbit k z.1 z.2 (i+1)-liftedOrbit k w.1 w.2 (i+1)| ≤
        8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) :
    dist (liftIter k (-(B:ℤ)) z) (liftIter k (-(B:ℤ)) w) ≤
      8/growthBase k^((4/5:ℝ)*(B-1:ℕ)) := by
  rw [liftIter_neg_swap,liftIter_neg_swap]
  simpa only [Prod.dist_eq,Prod.fst_swap,Prod.snd_swap,max_comm] using graph_endpoint_close k hk z.swap w.swap n B hn hB hterm hbound
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_SweepSlice
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma sweep_slice_bound (I D : Set ℝ) (f : (ℝ × ℝ) → (ℝ × ℝ))
    (J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (w : ℝ → ℝ≥0∞) (g : Torus → ℝ≥0∞) (c : ℝ) (δ : ℝ≥0∞)
    (hI : MeasurableSet I) (hD : MeasurableSet D) (hw : Measurable w) (hg : Measurable g)
    (hJ : ∀ z ∈ I ×ˢ D, HasFDerivWithinAt f (J z) (I ×ˢ D) z)
    (hinj : InjOn f (I ×ˢ D))
    (hlo : ∀ z ∈ I ×ˢ D, c ≤ |(J z).det|)
    (himage : f '' (I ×ˢ D) ⊆ Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2)
    (hobs : ∀ z ∈ I ×ˢ D, w z.2 ≤ g (liftProjection (f z))+δ) :
    (ENNReal.ofReal c*volume I)*(∫⁻ y in D, w y) ≤
      16*(∫⁻ z, g z ∂area)+(ENNReal.ofReal c*volume I)*δ*volume D := by
  have hbase := weighted_sweep_bound volume (I ×ˢ D) f J c (g ∘ liftProjection)
    (fun z => w z.2) δ (hI.prod hD) hJ hinj hlo hobs
  have he : (∫⁻ z in I ×ˢ D, w z.2) = volume I*(∫⁻ y in D, w y) := by
    change (∫⁻ z, w z.2 ∂(volume.prod volume).restrict (I ×ˢ D)) = _
    have hw' : Measurable (fun z : ℝ × ℝ => w z.2) := hw.comp measurable_snd
    rw [← Measure.prod_restrict,lintegral_prod _ hw'.aemeasurable]
    simp [mul_comm]
  rw [he] at hbase
  have hm : volume (I ×ˢ D) = volume I*volume D := Measure.prod_prod _ _
  rw [hm] at hbase
  calc
    _ = ENNReal.ofReal c*(volume I*(∫⁻ y in D, w y)) := by ring
    _ ≤ (∫⁻ z in f '' (I ×ˢ D), g (liftProjection z))+ENNReal.ofReal c*δ*(volume I*volume D) := hbase
    _ ≤ 16*(∫⁻ z, g z ∂area)+(ENNReal.ofReal c*volume I)*δ*volume D := by
      have h := bounded_lift_integral g hg (f '' (I ×ˢ D)) himage
      calc
        _ ≤ 16*(∫⁻ z, g z ∂area)+ENNReal.ofReal c*δ*(volume I*volume D) := add_le_add h le_rfl
        _ = _ := by ring

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BackwardSlice
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_liftProjection : Continuous liftProjection :=
  (((AddCircle.continuous_mk' (1:ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_snd))
lemma interval_small_move (y y' : ℝ) (hy : y ∈ Icc (0:ℝ) 1) (hmove : |y'-y| ≤ 1) :
    y' ∈ Ioc (-2:ℝ) 2 := by
  have hh := abs_le.mp hmove
  constructor <;> linarith [hy.1,hy.2,hh.1,hh.2]
lemma actual_backward_slice_q3_oai (k : ℝ) (n B : ℕ) (hn : 1 ≤ n) (hB : B=n ∨ B=n+1) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (ha : 24/growthBase k^((4/5:ℝ)) ≤ 1/2)
    (D : Set ℝ) (hD : MeasurableSet D) (X X' : ℝ → ℝ) (l u : ℝ)
    (hlen : u-l < 1/4) (hlu : Icc l u ⊆ Icc (0:ℝ) 1)
    (hDunit : D ⊆ Icc (0:ℝ) 1)
    (hXI : ∀ y ∈ D, X y ∈ Icc l u)
    (hX : ∀ y ∈ D, HasStrictDerivAt X (X' y) y)
    (hXs : ∀ y ∈ D, |X' y| ≤ 24/growthBase k^((4/5:ℝ)))
    (hXL : ∀ y ∈ D, ∀ z ∈ D, |X y-X z| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z|)
    (ht : ∀ y ∈ D, tSolution (orbitCoefficient k (X y) y) (n+1) ≠ 0)
    (hU : ∀ y ∈ D, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k (X y) y) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ)))
    (W : Torus → ℝ) (hW : Continuous W) (hW0 : ∀ z, 0 ≤ W z) (δ : ℝ) (hδ : 0 ≤ δ)
    (htransport : ∀ z w : ℝ × ℝ,
      dist (liftIter k (-(B:ℤ)) z) (liftIter k (-(B:ℤ)) w) ≤
        8/growthBase k^((4/5:ℝ)*(B-1:ℕ)) →
      |W (liftProjection z)-W (liftProjection w)| ≤ δ) :
    (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc l u))*
      (∫⁻ y in D, ENNReal.ofReal (W (liftProjection (X y,y)))) ≤
    16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc l u))*
        ENNReal.ofReal δ*volume D := by
  classical
  have hp : 0 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have ha0 : 0 ≤ 24/growthBase k^((4/5:ℝ)) := by positivity
  have htrans : (24/growthBase k^((4/5:ℝ)))^2 < 1 := by nlinarith
  obtain ⟨Θ,J,hΘ,hbase,hlevel,hinj,hJ,hdet,hclose⟩ := actual_backward_carry_full k n hn hk hq hsmall D X X' l u hlen hXI hX hXs hXL htrans ht hU
  let w : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (W (liftProjection (X y,y)))
  have hwc : ContinuousOn w D := by
    apply ENNReal.continuous_ofReal.comp_continuousOn
    apply hW.comp_continuousOn
    apply continuous_liftProjection.comp_continuousOn
    have hxc : ContinuousOn X D := fun y hy => (hX y hy).hasDerivAt.continuousAt.continuousWithinAt
    exact hxc.prodMk continuousOn_id
  have hwm : Measurable (D.indicator w) := by
    exact hwc.measurable_piecewise continuousOn_const hD
  have hbound : (fun z : ℝ × ℝ => (z.1,Θ z)) '' (Icc l u ×ˢ D) ⊆
      Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2 := by
    rintro z ⟨v,hv,rfl⟩
    have hvu := hlu hv.1
    have hxu := hlu (hXI v.2 hv.2)
    have hd : |v.1-X v.2| ≤ 1 := by apply abs_le.mpr; constructor <;> linarith [hvu.1,hvu.2,hxu.1,hxu.2]
    have hc := (hclose v.2 hv.2 v.1 hv.1).1
    refine ⟨⟨by linarith [hvu.1],by linarith [hvu.2]⟩,interval_small_move v.2 (Θ v) (hDunit hv.2) ?_⟩
    exact hc.trans (by nlinarith [abs_nonneg (v.1-X v.2)])
  have htpt (z : ℝ × ℝ) (hz : z ∈ Icc l u ×ˢ D) :
      D.indicator w z.2 ≤ ENNReal.ofReal (W (liftProjection (z.1,Θ z)))+ENNReal.ofReal δ := by
    rw [indicator_of_mem hz.2]
    have he := graph_backward_endpoint_close k hk (z.1,Θ z) (X z.2,z.2) n B hn hB
      (hlevel z.2 hz.2 z.1 hz.1) (hclose z.2 hz.2 z.1 hz.1).2
    have hh := htransport (X z.2,z.2) (z.1,Θ z) (by simpa only [dist_comm] using he)
    calc
      _ ≤ ENNReal.ofReal (W (liftProjection (z.1,Θ z))+δ) := ENNReal.ofReal_le_ofReal (by have := (abs_le.mp hh).2; linarith)
      _ = _ := ENNReal.ofReal_add (hW0 _) hδ
  have hh := sweep_slice_bound (Icc l u) D (fun z : ℝ × ℝ => (z.1,Θ z)) J
    (D.indicator w) (fun z => ENNReal.ofReal (W z)) _ (ENNReal.ofReal δ)
    measurableSet_Icc hD hwm (ENNReal.continuous_ofReal.comp hW).measurable
    hJ hinj (fun z hz => (hdet z hz).1) hbound htpt
  simpa only [setLIntegral_indicator hD,inter_self,w] using hh
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.actual_backward_slice_q3_oai := @OAI.StandardMapEntropy.actual_backward_slice_q3_oai
