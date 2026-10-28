-- Prove2me | solution 1 for OAI.StandardMapEntropy.jointly_continuous_dirichlet_family_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:41:43.415001+00:00
-- url     : https://prove2.me/submissions/0bf62749-0bad-45ec-97b3-9b263e3de094

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
  all_goals try with_reducible_and_instances rfl
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
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq]
  unfold phiSecond
  ring

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
-- module Solutions.OAIQ44_CM.StandardMap_TransferCore
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
-- module Solutions.OAIQ44_CM.StandardMap_NonlinearDirichlet
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
-- module Solutions.OAIQ44_CM.StandardMap_BridgeWeights
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
-- module Solutions.OAIQ44_CM.StandardMap_BridgeNonlinear
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
-- module Solutions.OAIQ44_CM.StandardMap_DirichletOrbit
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
-- module Solutions.OAIQ44_CM.StandardMap_WeightedStability
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
-- module Solutions.OAIQ44_CM.StandardMap_GraphCalculus
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
  all_goals try with_reducible_and_instances rfl
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

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_FixedPointFamily
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
-- module Solutions.OAIQ44_CM.StandardMap_FixedPointContinuity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
-- module Solutions.OAIQ44_CM.StandardMap_ScaledContraction
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
-- module Solutions.OAIQ44_CM.StandardMap_GraphParameterContinuity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
-- module Solutions.OAIQ44_CM.StandardMap_JointGraphFamily
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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

lemma jointly_continuous_dirichlet_family_q44_oai (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
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

theorem solution : type_of% @OAI.StandardMapEntropy.jointly_continuous_dirichlet_family_q44_oai := @OAI.StandardMapEntropy.jointly_continuous_dirichlet_family_q44_oai
