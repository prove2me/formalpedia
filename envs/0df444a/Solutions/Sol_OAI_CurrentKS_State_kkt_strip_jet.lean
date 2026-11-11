-- Prove2me | solution 1 for OAI.CurrentKS.State.kkt_strip_jet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:57:09.185383+00:00
-- url     : https://prove2.me/submissions/38bfb8d5-9b73-45e4-9334-e503ff82fb29

import Mathlib
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_CurrentKS_Variational_jetBound_kktGiven

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ScalarPsi
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open scoped ContDiff

lemma base_pos {x : ℝ} (hx : |x| < 1) : 0 < 1-x^2 := by
  have h := (abs_lt.mp hx)
  nlinarith [sq_nonneg x]

lemma psi_pos {x : ℝ} (hx : |x| < 1) : 0 < psi x :=
  Real.rpow_pos_of_pos (base_pos hx) _

lemma psi_cube {x : ℝ} (hx : |x| < 1) : psi x ^ 3 = 1-x^2 := by
  rw [psi, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (base_pos hx))]
  norm_num

lemma psi_sq {x : ℝ} (hx : |x| < 1) : psi x ^ 2 = (1-x^2) ^ (2/3 : ℝ) := by
  rw [psi, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (base_pos hx))]
  norm_num

lemma psi_le_one {x : ℝ} (hx : |x| < 1) : psi x ≤ 1 := by
  have hp := psi_pos hx
  have hc := psi_cube hx
  nlinarith [sq_nonneg x, sq_nonneg (psi x - 1)]

lemma hasDerivAt_psi {x : ℝ} (hx : |x| < 1) : HasDerivAt psi (psi₁ x) x := by
  have hr := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).rpow_const
    (p := (1/3 : ℝ)) (Or.inl (ne_of_gt (base_pos hx)))
  convert hr using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  norm_num only [mul_one, zero_sub, Nat.cast_ofNat]
  simp only [id_eq, pow_one, Pi.sub_apply, Pi.pow_apply]
  rw [Real.rpow_neg (base_pos hx).le, ← psi_sq hx]
  unfold psi₁
  ring

lemma contDiffAt_psi {x : ℝ} (hx : |x| < 1) {n : WithTop ℕ∞} : ContDiffAt ℝ n psi x := by
  exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (base_pos hx))).comp x
    (contDiffAt_const.sub (contDiffAt_id.pow 2))

lemma hasDerivAt_psi₁ {x : ℝ} (hx : |x| < 1) : HasDerivAt psi₁ (-kappa x) x := by
  have hw : psi x ≠ 0 := ne_of_gt (psi_pos hx)
  have hp := hasDerivAt_psi hx
  have hd := ((hasDerivAt_id x).const_mul (-2)).div ((hp.pow 2).const_mul 3)
    (by positivity : (3 : ℝ) * psi x^2 ≠ 0)
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  unfold kappa psi₁
  have hc := psi_cube hx
  field_simp
  nlinarith [hc]

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_Kappa₁
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open scoped ContDiff

lemma hasDerivAt_kappa {x : ℝ} (hx : |x| < 1) : HasDerivAt kappa (kappa₁ x) x := by
  have hp := hasDerivAt_psi hx
  have hw : psi x ≠ 0 := (psi_pos hx).ne'
  have hd := (((hasDerivAt_const x (3:ℝ)).add ((hasDerivAt_id x).pow 2)).const_mul 2).div
    ((hp.pow 5).const_mul 9) (by positivity : (9:ℝ)*psi x^5 ≠ 0)
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,zero_add,Pi.add_apply]
  unfold kappa₁ psi₁
  field_simp
  ring

lemma strip_interior {σ x : ℝ} (hσ : 0 < σ) (hx : |x| ≤ 1-σ/2) : |x| < 1 := by linarith

lemma strip_base {σ x : ℝ} (hσ : 0 < σ) (hx : |x| ≤ 1-σ/2) : σ/2 ≤ 1-x^2 := by
  have hi := strip_interior hσ hx
  have ha := abs_nonneg x
  have h1 : |x| ≤ 1 := hi.le
  have hh := mul_nonneg (sub_nonneg.mpr h1) ha
  rw [sub_mul,one_mul] at hh
  nlinarith [sq_abs x]

lemma strip_denominator {σ x : ℝ} (hσ : 0 < σ) (hx : |x| ≤ 1-σ/2)
    (k : ℕ) (hk : k ≤ 9) : σ^3/8 ≤ psi x^k := by
  have hi := strip_interior hσ hx
  have hp := psi_pos hi
  have h1 := psi_le_one hi
  have hb := strip_base hσ hx
  have hc : (σ/2)^3 ≤ (1-x^2)^3 := pow_le_pow_left₀ (by positivity) hb 3
  have he : (1-x^2)^3 = psi x^9 := by rw [← psi_cube hi,← pow_mul]
  have hpow : psi x^9 ≤ psi x^k := by exact pow_le_pow_of_le_one hp.le h1 hk
  calc
    σ^3/8 = (σ/2)^3 := by ring
    _ ≤ _ := hc.trans_eq he
    _ ≤ _ := hpow

lemma scalar_fraction_strip {σ x u : ℝ} (hσ : 0 < σ) (hx : |x| ≤ 1-σ/2)
    (k : ℕ) (hk : k ≤ 9) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hu : |u| ≤ b) :
    |u/(a*psi x^k)| ≤ (8*b/a)/σ^3 := by
  have hp := psi_pos (strip_interior hσ hx)
  have hd := strip_denominator hσ hx k hk
  have ha' : 0 < a*psi x^k := mul_pos ha (pow_pos hp _)
  rw [abs_div,abs_of_pos ha']
  apply (div_le_div_iff₀ ha' (pow_pos hσ _)).mpr
  have hh := mul_le_mul_of_nonneg_left hd hb
  have hu' := mul_le_mul_of_nonneg_right hu (pow_nonneg hσ.le 3)
  have he : (8*b/a)*(a*psi x^k) = 8*b*psi x^k := by field_simp
  rw [he]
  nlinarith only [hh,hu']

theorem strip_derivative_bounds {σ x : ℝ} (hσ : 0 < σ) (hx : |x| ≤ 1-σ/2) :
    |psi₁ x| ≤ 800/σ^3 ∧ |kappa x| ≤ 800/σ^3 ∧ |kappa₁ x| ≤ 800/σ^3 := by
  have hi := strip_interior hσ hx
  have hx1 : |x| ≤ 1 := hi.le
  have hx2 : x^2 ≤ 1 := by nlinarith [sq_abs x,abs_nonneg x]
  have hn1 : |(-2:ℝ)*x| ≤ 2 := by rw [abs_mul]; norm_num; linarith
  have hn2 : |2*(3+x^2)| ≤ 8 := by rw [abs_of_nonneg (by positivity)]; nlinarith
  have hn3 : |(4:ℝ)*x| ≤ 4 := by rw [abs_mul]; norm_num; linarith
  have hn4 : |20*x*(3+x^2)| ≤ 80 := by
    rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤20),abs_of_nonneg (by positivity : (0:ℝ)≤3+x^2)]
    nlinarith [abs_nonneg x]
  have h₁ := scalar_fraction_strip hσ hx 2 (by norm_num) (by norm_num : (0:ℝ)<3) (by norm_num : (0:ℝ)≤2) hn1
  have h₂ := scalar_fraction_strip hσ hx 5 (by norm_num) (by norm_num : (0:ℝ)<9) (by norm_num : (0:ℝ)≤8) hn2
  have h₃ := scalar_fraction_strip hσ hx 5 (by norm_num) (by norm_num : (0:ℝ)<9) (by norm_num : (0:ℝ)≤4) hn3
  have h₄ := scalar_fraction_strip hσ hx 8 (by norm_num) (by norm_num : (0:ℝ)<27) (by norm_num : (0:ℝ)≤80) hn4
  refine ⟨h₁.trans ?_,h₂.trans ?_,?_⟩
  · exact div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hσ.le 3)
  · exact div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hσ.le 3)
  · calc
      |kappa₁ x| ≤ |4*x/(9*psi x^5)|+|20*x*(3+x^2)/(27*psi x^8)| := abs_add_le _ _
      _ ≤ (8*4/9)/σ^3+(8*80/27)/σ^3 := add_le_add h₃ h₄
      _ ≤ 800/σ^3 := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hσ.le 3)

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Calculus_IteratedNormCompLinear
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Calculus

section
open Set
open scoped Topology

variable {E F G D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma iterated_norm_comp_linear (L : E →L[ℝ] F) {f : F → G} {x : E} {n : ℕ}
    (hf : ContDiffAt ℝ n f (L x)) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖*‖L‖^n := by
  obtain ⟨u,hu,hxu,hfu⟩ := hf.contDiffOn' le_rfl (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hfu : ContDiffOn ℝ n f u := by simpa using hfu
  have hpre : IsOpen (L ⁻¹' u) := hu.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hfu hu.uniqueDiffOn hpre.uniqueDiffOn hxu (le_refl (n : WithTop ℕ∞))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn (hf.comp x L.contDiff.contDiffAt) hxu,
    iteratedFDerivWithin_eq_iteratedFDeriv hu.uniqueDiffOn hf hxu] at he
  rw [he]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)

lemma iterated_norm_comp_contraction (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    {f : F → G} {x : E} {n : ℕ} (hf : ContDiffAt ℝ n f (L x)) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ := by
  apply (iterated_norm_comp_linear L hf).trans
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

lemma iterated_norm_linear_ge_two (L : E →L[ℝ] F) (x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ (n+2) L x‖=0 := by
  rw [show n+2=(n+1)+1 by omega, ← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ L = fun _ => L := by funext y; exact L.fderiv
  rw [he,iteratedFDeriv_succ_const]
  simp

end

open Set

variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra ℝ R]

lemma iterated_norm_linear_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) {f : E → F} {x : E}
    {n : ℕ} (hf : ContDiffAt ℝ n f x) :
    ‖iteratedFDeriv ℝ n (L ∘ f) x‖ ≤ ‖L‖*‖iteratedFDeriv ℝ n f x‖ := by
  rw [L.iteratedFDeriv_comp_left hf le_rfl]
  exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _

end CurrentKS.Calculus

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Calculus_JetBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Calculus
noncomputable section
open Set

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma JetBound.mono {f : E → F} {x : E} {B C : ℝ} (h : JetBound f x B) (hBC : B ≤ C) :
    JetBound f x C := fun n hn => (h n hn).trans hBC

lemma JetBound.add {f g : E → F} {x : E} {B C : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x)
    (hB : JetBound f x B) (hC : JetBound g x C) : JetBound (fun y => f y+g y) x (B+C) := by
  intro n hn
  rw [fun_iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast hn)) (hg.of_le (by exact_mod_cast hn))]
  exact (norm_add_le _ _).trans (add_le_add (hB n hn) (hC n hn))

lemma JetBound.linear_comp {f : E → F} {x : E} {B C : ℝ} (L : F →L[ℝ] G)
    (hf : ContDiffAt ℝ 3 f x) (hB : JetBound f x B) (hL : ‖L‖ ≤ C) :
    JetBound (L ∘ f) x (C*B) := by
  intro n hn
  exact (iterated_norm_linear_comp L (hf.of_le (by exact_mod_cast hn))).trans
    (mul_le_mul hL (hB n hn) (norm_nonneg _) ((norm_nonneg L).trans hL))

lemma JetBound.comp_linear {f : F → G} {x : E} {B : ℝ} (L : E →L[ℝ] F)
    (hf : ContDiffAt ℝ 3 f (L x)) (hB : JetBound f (L x) B) (hL : ‖L‖ ≤ 1) :
    JetBound (f ∘ L) x B := by
  intro n hn
  exact (iterated_norm_comp_contraction L hL (hf.of_le (by exact_mod_cast hn))).trans (hB n hn)

lemma JetBound.const (v : F) (x : E) : JetBound (fun _ : E => v) x ‖v‖ := by
  intro n _
  cases n with
  | zero => simp only [norm_iteratedFDeriv_zero, le_refl]
  | succ n => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,norm_nonneg]

lemma JetBound.linear (L : E →L[ℝ] F) (x : E) {B : ℝ} (hLB : ‖L‖ ≤ B) (hx : ‖L x‖ ≤ B) :
    JetBound L x B := by
  intro n hn
  interval_cases n
  · simpa only [norm_iteratedFDeriv_zero] using hx
  · simpa only [norm_iteratedFDeriv_one,L.fderiv] using hLB
  · rw [iterated_norm_linear_ge_two L x 0]
    exact (norm_nonneg L).trans hLB
  · rw [iterated_norm_linear_ge_two L x 1]
    exact (norm_nonneg L).trans hLB

lemma JetBound.sum {ι : Type*} (s : Finset ι) {f : ι → E → F} {x : E} {B : ι → ℝ}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 3 (f i) x) (hB : ∀ i ∈ s, JetBound (f i) x (B i)) :
    JetBound (fun y => ∑ i ∈ s, f i y) x (∑ i ∈ s, B i) := by
  intro n hn
  rw [iteratedFDeriv_fun_sum_apply fun i hi => (hf i hi).of_le (by exact_mod_cast hn)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => hB i hi n hn))

end
end CurrentKS.Calculus

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_EventuallyInterior
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open Filter CurrentKS.Calculus
open scoped Topology

lemma eventually_interior {x : ℝ} (hx : |x| < 1) : ∀ᶠ y in 𝓝 x, |y| < 1 :=
  IsOpen.eventually_mem (isOpen_lt continuous_abs continuous_const) hx

lemma iteratedDeriv_psi_two {x : ℝ} (hx : |x| < 1) : iteratedDeriv 2 psi x = -kappa x := by
  have he : deriv psi =ᶠ[𝓝 x] psi₁ := by
    filter_upwards [eventually_interior hx] with y hy
    exact (hasDerivAt_psi hy).deriv
  rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,he.deriv_eq]
  exact (hasDerivAt_psi₁ hx).deriv

lemma iteratedDeriv_psi_three {x : ℝ} (hx : |x| < 1) : iteratedDeriv 3 psi x = -kappa₁ x := by
  have he : iteratedDeriv 2 psi =ᶠ[𝓝 x] fun y => -kappa y := by
    filter_upwards [eventually_interior hx] with y hy
    exact iteratedDeriv_psi_two hy
  rw [show (3:ℕ)=2+1 from rfl,iteratedDeriv_succ,he.deriv_eq]
  exact (hasDerivAt_kappa hx).neg.deriv

lemma jetBound_psi {σ x : ℝ} (hσ : 0 < σ) (hx : |x| ≤ 1-σ/2) :
    JetBound psi x (1+800/σ^3) := by
  have hi := strip_interior hσ hx
  obtain ⟨h₁,h₂,h₃⟩ := strip_derivative_bounds hσ hx
  have hp : |psi x| ≤ 1 := by rw [abs_of_pos (psi_pos hi)]; exact psi_le_one hi
  have hn : (0:ℝ)≤800/σ^3 := by positivity
  intro n hn'
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  interval_cases n
  · simpa only [iteratedDeriv_zero,Real.norm_eq_abs] using hp.trans (by linarith)
  · rw [iteratedDeriv_one,(hasDerivAt_psi hi).deriv,Real.norm_eq_abs]
    linarith
  · rw [iteratedDeriv_psi_two hi,norm_neg,Real.norm_eq_abs]
    linarith
  · rw [iteratedDeriv_psi_three hi,norm_neg,Real.norm_eq_abs]
    linarith
end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Calculus_NormSmulRightId
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Calculus
noncomputable section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma norm_smulRight_id_le (v : F) :
    ‖(ContinuousLinearMap.id ℝ ℝ).smulRight v‖ ≤ ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v)
  intro r
  change ‖r • v‖ ≤ ‖v‖*‖r‖
  rw [norm_smul,mul_comm]

lemma JetBound.smul_const {f : E → ℝ} {x : E} {B C : ℝ} (v : F)
    (hf : ContDiffAt ℝ 3 f x) (hB : JetBound f x B) (hC : ‖v‖ ≤ C) :
    JetBound (fun y => f y • v) x (C*B) := by
  exact hB.linear_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v) hf
    ((norm_smulRight_id_le v).trans hC)

lemma norm_comp_contractions (L : F →L[ℝ] G) (T : E →L[ℝ] F)
    (hL : ‖L‖ ≤ 1) (hT : ‖T‖ ≤ 1) : ‖L.comp T‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le L T).trans
    (by simpa only [one_mul] using mul_le_mul hL hT (norm_nonneg T) zero_le_one)

end
end CurrentKS.Calculus

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_NormRetractH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupMat_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealMat_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p5
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealSubtypeMatMemSubmoduleH_p5
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceMat_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p5
lemma norm_sandwichCLM_le (A : H d) : ‖(sandwichCLM A : H d →L[ℝ] H d)‖ ≤ ‖A‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro U
  change ‖(A:Mat d)*(U:Mat d)*(A:Mat d)‖ ≤ ‖A‖^2*‖U‖
  calc
    _ ≤ ‖(A:Mat d)‖*‖(U:Mat d)‖*‖(A:Mat d)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = _ := by change ‖A‖*‖U‖*‖A‖ = _; ring
end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormCoordinate
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_coordinate_le (i : Fin N) :
    ‖(ContinuousLinearMap.proj i : Coordinates N →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul]
  exact norm_le_pi_norm x i

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p5
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealSubtypeMatMemSubmoduleH_p5
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p5
attribute [local instance] OAI.CurrentKS.State.normCoordinateOperatorNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.State.normCoordinateOperatorNormedSpace
lemma jetBound_S (A : Fin N → H d) (hA : ∀ i, ‖A i‖ ≤ 1)
    (L : E →L[ℝ] Coordinates N) (hL : ‖L‖ ≤ 1) {z : E} (hz : Cube (L z)) :
    JetBound (S A ∘ L) z (N:ℝ) := by
  have hc (i : Fin N) : JetBound ((ContinuousLinearMap.proj i).comp L) z 1 := by
    apply JetBound.linear _ _ (norm_comp_contractions _ L (norm_coordinate_le i) hL)
    exact hz i
  have hh (i : Fin N) : JetBound (fun v => L v i • A i) z 1 := by
    have hhh := (hc i).smul_const (A i)
      ((ContinuousLinearMap.proj i).comp L).contDiff.contDiffAt (hA i)
    simp only [one_mul] at hhh
    exact hhh
  have hs := JetBound.sum Finset.univ
    (fun i _ => (((ContinuousLinearMap.proj i).comp L).contDiff.contDiffAt.smul
      (contDiffAt_const (c := A i)))) (fun i _ => hh i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at hs
  exact hs

lemma jetBound_psi_coordinate
    (L : E →L[ℝ] Coordinates N) (hL : ‖L‖ ≤ 1) {z : E} {σ : ℝ}
    (hσ : 0 < σ) (i : Fin N) (hz : |L z i| ≤ 1-σ/2) :
    JetBound (fun v => psi (L v i)) z (1+800/σ^3) := by
  exact (jetBound_psi hσ hz).comp_linear ((ContinuousLinearMap.proj i).comp L)
    (contDiffAt_psi (strip_interior hσ hz))
    (norm_comp_contractions _ L (norm_coordinate_le i) hL)

lemma norm_sandwich_coefficient (c : ℝ) (A : H d) (hA : ‖A‖ ≤ 1) :
    ‖c • sandwichCLM A‖ ≤ |c| := by
  rw [norm_smul, Real.norm_eq_abs]
  have hn : ‖sandwichCLM A‖ ≤ 1 := (norm_sandwichCLM_le A).trans
    (by nlinarith [norm_nonneg A,hA])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (abs_nonneg c)

lemma contDiffAt_psi_coordinate
    (L : E →L[ℝ] Coordinates N) {z : E} {σ : ℝ}
    (hσ : 0 < σ) (i : Fin N) (hz : |L z i| ≤ 1-σ/2) :
    ContDiffAt ℝ 3 (fun v => psi (L v i)) z :=
  (contDiffAt_psi (strip_interior hσ hz)).comp z
    (((ContinuousLinearMap.proj i).comp L).contDiff.contDiffAt)

lemma jetBound_eta_term (c : ℝ) (A : H d) (hA : ‖A‖ ≤ 1)
    (L : E →L[ℝ] Coordinates N) (hL : ‖L‖ ≤ 1) {z : E} {σ : ℝ}
    (hσ : 0 < σ) (i : Fin N) (hz : |L z i| ≤ 1-σ/2) :
    JetBound (fun v => psi (L v i) • (c • sandwichCLM A)) z
      (|c| *(1+800/σ^3)) :=
  (jetBound_psi_coordinate L hL hσ i hz).smul_const (c • sandwichCLM A)
    (contDiffAt_psi_coordinate L hσ i hz) (norm_sandwich_coefficient c A hA)

lemma jetBound_eta (c : ℝ) (A : Fin N → H d) (hA : ∀ i, ‖A i‖ ≤ 1)
    (L : E →L[ℝ] Coordinates N) (hL : ‖L‖ ≤ 1) {z : E} {σ : ℝ}
    (hσ : 0 < σ) (hz : ∀ i, |L z i| ≤ 1-σ/2) :
    JetBound (eta c A ∘ L) z ((N:ℝ)* |c| *(1+800/σ^3)) := by
  have hs := JetBound.sum Finset.univ
    (fun i _ => (contDiffAt_psi_coordinate L hσ i (hz i)).smul
      (contDiffAt_const (c := c • sandwichCLM (A i))))
    (fun i _ => jetBound_eta_term c (A i) (hA i) L hL hσ i (hz i))
  convert hs using 1
  · funext v
    change (∑ i : Fin N, (c * psi (L v i)) • sandwichCLM (A i)) =
      (∑ i : Fin N, psi (L v i) • (c • sandwichCLM (A i)))
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul,mul_comm]
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_CoarseBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealSubtypeMatMemSubmoduleH_p0
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupVars
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealVars
attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH
lemma contDiff_S (A : Fin N → H d) {n : WithTop ℕ∞} : ContDiff ℝ n (S A) := by
  apply ContDiff.sum
  intro i _
  exact (contDiff_apply ℝ ℝ i).smul contDiff_const

lemma contDiffAt_eta (c : ℝ) (A : Fin N → H d) {x : Coordinates N}
    (hx : ∀ i, |x i| < 1) {n : WithTop ℕ∞} : ContDiffAt ℝ n (eta c A) x := by
  apply ContDiffAt.sum
  intro i _
  have hp : ContDiffAt ℝ n (fun y : Coordinates N => psi (y i)) x :=
    (contDiffAt_psi (hx i)).comp x (contDiffAt_apply ℝ ℝ i x)
  have hc : ContDiffAt ℝ n (fun _ : Coordinates N => c) x := contDiffAt_const
  exact (hc.mul hp).smul (show ContDiffAt ℝ n (fun _ : Coordinates N => sandwichCLM (A i)) x from contDiffAt_const)

lemma coarseBudget_bounds {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    1 ≤ coarseBudget d N ε σ ∧ (d:ℝ)+1 ≤ coarseBudget d N ε σ ∧
    |ε| ≤ coarseBudget d N ε σ ∧
    200+(200/ε)*((d:ℝ)+1) ≤ coarseBudget d N ε σ ∧
    200*((d:ℝ)+1) ≤ coarseBudget d N ε σ ∧
    ((d:ℝ)+1)+N ≤ coarseBudget d N ε σ ∧
    384*N*(1+800/σ^3) ≤ coarseBudget d N ε σ := by
  have hd : 0 ≤ (d:ℝ)+1 := by positivity
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hp : 0 ≤ (200/ε)*((d:ℝ)+1) := by positivity
  have hr : 0 ≤ 384*(N:ℝ)*(1+800/σ^3) := by positivity
  have he := abs_nonneg ε
  dsimp [coarseBudget]
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor <;> linarith

attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceVars
lemma contDiffAt_face_eta (A : Fin N → H d) (x : Coordinates N) (z : Vars d)
    (hxi : ∀ i, |x i| < 1) :
    ContDiffAt ℝ 3 (fun v : Coordinates N × Vars d => eta 384 A v.1) (x,z) := by
  exact ContDiffAt.comp (f := fun v : Coordinates N × Vars d => v.1)
    (g := eta 384 A) (x,z) (contDiffAt_eta 384 A hxi)
    (contDiffAt_fst : ContDiffAt ℝ 3 (fun v : Coordinates N × Vars d => v.1) (x,z))

lemma strip_S_jet (A : Fin N → H d) (hA : ∀ i, ‖A i‖ ≤ 1)
    (S₀ : H d) (hS₀ : ‖S₀‖ ≤ (d:ℝ)+1) (x : Coordinates N) (z : Vars d)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) :
    JetBound (fun v : Coordinates N × Vars d => S₀+S A v.1) (x,z)
      (coarseBudget d N ε σ) := by
  have hxi (i : Fin N) : |x i| < 1 := strip_interior hσ (hx i)
  let L : (Coordinates N × Vars d) →L[ℝ] Coordinates N := ContinuousLinearMap.fst ℝ _ _
  have hLc : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ..
  have h := (JetBound.const S₀ (x,z)).add contDiffAt_const
    ((contDiff_S A).contDiffAt.comp (x,z) contDiffAt_fst)
    (jetBound_S A hA L hLc (fun i => (hxi i).le))
  exact h.mono (by linarith [(coarseBudget_bounds (d:=d) (N:=N) hε hσ).2.2.2.2.2.1])

lemma strip_eta_jet (A : Fin N → H d) (hA : ∀ i, ‖A i‖ ≤ 1)
    (x : Coordinates N) (z : Vars d) {ε σ : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hx : ∀ i, |x i| ≤ 1-σ/2) :
    JetBound (fun v : Coordinates N × Vars d => eta 384 A v.1) (x,z)
      (coarseBudget d N ε σ) := by
  let L : (Coordinates N × Vars d) →L[ℝ] Coordinates N := ContinuousLinearMap.fst ℝ _ _
  have hLc : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ..
  have h := jetBound_eta 384 A hA L hLc (z:=(x,z)) hσ hx
  apply h.mono
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<384)]
  nlinarith [(coarseBudget_bounds (d:=d) (N:=N) hε hσ).2.2.2.2.2.2]

lemma kkt_strip_jet_oai (A : Fin N → H d) (hA : ∀ i,‖A i‖ ≤ 1)
    (S₀ : H d) (hS₀ : ‖S₀‖ ≤ (d:ℝ)+1) (x : Coordinates N) {ε σ : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2)
    (z : Vars d) (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (hz : ‖z‖ ≤ 200+(200/ε)*((d:ℝ)+1))
    (hiX : ‖invH (xCoord d z)‖ ≤ 200*((d:ℝ)+1))
    (hiY : ‖invH (yCoord d z)‖ ≤ 200*((d:ℝ)+1))
    (hP : ‖mCoord d z‖ ≤ 1) (hQ : ‖nCoord d z‖ ≤ 1) :
    JetBound (fun v : Coordinates N × Vars d => kktSystem ε (S₀+S A v.1) (eta 384 A v.1) v.2)
      (x,z) (300*(coarseBudget d N ε σ)^5) := by
  obtain ⟨hb,hd,he,hzB,hiB,hSB,hηB⟩ := coarseBudget_bounds (d:=d) (N:=N) hε hσ
  let Z : (Coordinates N × Vars d) →L[ℝ] Vars d := ContinuousLinearMap.snd ℝ _ _
  have hZc : ‖Z‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ..
  exact jetBound_kktGiven Z hZc (hz.trans hzB) hb hd he hX hY
    (hiX.trans hiB) (hiY.trans hiB) hP hQ
    (contDiffAt_const.add ((contDiff_S A).contDiffAt.comp (x,z) contDiffAt_fst))
    (contDiffAt_face_eta A x z (fun i => strip_interior hσ (hx i)))
    (strip_S_jet A hA S₀ hS₀ x z hε hσ hx) (strip_eta_jet A hA x z hε hσ hx)

end
end CurrentKS.State

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.State.kkt_strip_jet_oai := @OAI.CurrentKS.State.kkt_strip_jet_oai
