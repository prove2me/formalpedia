-- Prove2me | solution 1 for OAI.CurrentKS.RationalFace.activePotential_regular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:32.610425+00:00
-- url     : https://prove2.me/submissions/f3de9a4e-06dd-4703-b9e1-bb52ee9889a5

import Mathlib
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_CurrentKS_State_value_strip_derivatives
import Theorems.Thm_OAI_CurrentKS_Variational_contDiffAt_value

section
-- module Solutions.OAIQ241_TT.Compat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
end OAICompat434

end OAI
end

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

end

open Set

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

lemma JetBound.comp_linear {f : F → G} {x : E} {B : ℝ} (L : E →L[ℝ] F)
    (hf : ContDiffAt ℝ 3 f (L x)) (hB : JetBound f (L x) B) (hL : ‖L‖ ≤ 1) :
    JetBound (f ∘ L) x B := by
  intro n hn
  exact (iterated_norm_comp_contraction L hL (hf.of_le (by exact_mod_cast hn))).trans (hB n hn)

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Calculus_Translate
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Calculus
noncomputable section
open scoped ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma JetBound.translate {f : E → F} {x a : E} {B : ℝ}
    (h : JetBound f (a+x) B) : JetBound (fun y => f (a+y)) x B := by
  intro n hn
  rw [iteratedFDeriv_comp_add_left]
  exact h n hn

lemma norm_lineMap_le_one (h : E) (hh : ‖h‖ ≤ 1) :
    ‖(ContinuousLinearMap.id ℝ ℝ).smulRight h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro r
  change ‖r • h‖ ≤ 1*‖r‖
  rw [norm_smul]
  nlinarith [norm_nonneg r]

lemma contDiffAt_translated_zero {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 3 f x) : ContDiffAt ℝ 3 (fun y => f (x+y)) (0:E) := by
  have H : ContDiffAt ℝ 3 f (x+0) := by simpa only [add_zero] using hf
  exact H.comp 0 (contDiffAt_const.add contDiffAt_id)

lemma JetBound.line {f : E → F} {x h : E} {B : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hB : JetBound f x B) (hh : ‖h‖ ≤ 1) :
    JetBound (fun t : ℝ => f (x+t • h)) 0 B := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight h
  have h0 : JetBound (fun y => f (x+y)) (0:E) B := by
    exact JetBound.translate (by simpa only [add_zero] using hB)
  have hf0 := contDiffAt_translated_zero hf
  have ht := JetBound.comp_linear (E:=ℝ) (F:=E) (G:=F) (x:=0) L
    (show ContDiffAt ℝ 3 (fun y => f (x+y)) (L 0) by simpa only [map_zero] using hf0)
    (show JetBound (fun y => f (x+y)) (L 0) B by simpa only [map_zero] using h0)
    (norm_lineMap_le_one h hh)
  exact ht

end
end CurrentKS.Calculus

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_HermitianMat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.invH_val _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_one _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace

variable {d : ℕ}

section OperatorNorm
open scoped Matrix.Norms.L2Operator MatrixOrder

theorem trace_mul_nonneg {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  let : CStarAlgebra (Mat d) := {}
  have hs : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have ht := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
  rw [hs.isHermitian.eq, Matrix.trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self A hA.nonneg] at ht
  exact (Complex.nonneg_iff.mp ht).1

end OperatorNorm

open scoped Matrix.Norms.Frobenius

theorem matrix_inner (d : ℕ) (A B : Mat d) :
    inner ℂ A B = (B * Aᴴ).trace := by
  change inner ℂ (asL2 A) (asL2 B) = _
  simp only [asL2, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1

theorem inner_eq_trace (A B : H d) :
    inner ℝ A B = ((A : Mat d) * (B : Mat d)).trace.re := by
  change (inner ℂ (A : Mat d) (B : Mat d)).re = _
  rw [matrix_inner, A.property.eq, Matrix.trace_mul_comm]

@[simp] theorem inner_one (A : H d) : inner ℝ one A = realTrace A := by
  rw [inner_eq_trace, one_val, one_mul]
  rfl

@[simp] theorem inner_one' (A : H d) : inner ℝ A one = realTrace A := by
  rw [real_inner_comm]
  exact inner_one A

theorem inner_nonneg_of_psd (A B : H d) (hA : A ∈ psdCone d) (hB : B ∈ psdCone d) :
    0 ≤ inner ℝ A B := by
  rw [inner_eq_trace]
  exact trace_mul_nonneg hA hB

theorem rankOne_mem_psdCone (v : Fin d → ℂ) : rankOne v ∈ psdCone d :=
  Matrix.posSemidef_vecMulVec_self_star v

theorem inner_rankOne (A : H d) (v : Fin d → ℂ) :
    inner ℝ A (rankOne v) = (star v ⬝ᵥ ((A : Mat d) *ᵥ v)).re := by
  rw [inner_eq_trace]
  change ((A : Mat d) * Matrix.vecMulVec v (star v)).trace.re = _
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem psd_of_inner_nonneg (A : H d)
    (h : ∀ B ∈ psdCone d, 0 ≤ inner ℝ A B) : A ∈ psdCone d := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨A.property, fun v => ?_⟩
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [inner_rankOne] using h (rankOne v) (rankOne_mem_psdCone v)
  · exact (A.property.im_star_dotProduct_mulVec_self v).symm

theorem isClosed_psdCone : IsClosed (psdCone d : Set (H d)) := by
  have he : (psdCone d : Set (H d)) =
      {A : H d | ∀ v : Fin d → ℂ, 0 ≤ (star v ⬝ᵥ ((A : Mat d) *ᵥ v)).re} := by
    ext A
    constructor
    · intro hA v
      exact hA.re_dotProduct_nonneg v
    · intro hA
      apply psd_of_inner_nonneg A

      have hp : (A : Mat d).PosSemidef :=
        Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨A.property, fun v =>
          Complex.nonneg_iff.mpr ⟨hA v, (A.property.im_star_dotProduct_mulVec_self v).symm⟩⟩
      exact fun B hB => inner_nonneg_of_psd A B hp hB
  rw [he]
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_le continuous_const
  exact Complex.continuous_re.comp (continuous_const.dotProduct
    (continuous_subtype_val.matrix_mulVec continuous_const))

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_InvH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

variable {d : ℕ}

lemma pd_smul {A : H d} (hA : A ∈ pd d) {a : ℝ} (ha : 0 < a) :
    a • A ∈ pd d := by
  change ((a : ℂ) • (A : Mat d)).PosDef
  exact hA.smul (by exact_mod_cast ha)

lemma isClosed_lowerBound (a : ℝ) :
    IsClosed {A : H d | (a • one : H d) ≤ A} := by
  change IsClosed ((fun A : H d => A - a • one) ⁻¹' (psdCone d : Set (H d)))
  exact (isClosed_psdCone (d := d)).preimage (continuous_id.sub continuous_const)

lemma isClosed_upperBound (b : ℝ) :
    IsClosed {A : H d | A ≤ (b • one : H d)} := by
  change IsClosed ((fun A : H d => b • one - A) ⁻¹' (psdCone d : Set (H d)))
  exact (isClosed_psdCone (d := d)).preimage (continuous_const.sub continuous_id)

lemma isClosed_orderBox (a b : ℝ) :
    IsClosed {A : H d | (a • one : H d) ≤ A ∧ A ≤ b • one} :=
  (isClosed_lowerBound a).inter (isClosed_upperBound b)

open scoped Matrix.Norms.L2Operator

theorem inverse_antitone {A B : Mat d} (hA : A.PosDef) (hB : B.PosDef) (hab : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  let : CStarAlgebra (Mat d) := {}
  obtain ⟨u, rfl⟩ := hA.isUnit
  obtain ⟨v, rfl⟩ := hB.isUnit
  simpa only [Matrix.coe_units_inv] using CStarAlgebra.inv_le_inv hA.posSemidef.nonneg hab

lemma scalar_posDef {a : ℝ} (ha : 0 < a) : ((a : ℂ) • (1 : Mat d)).PosDef :=
  Matrix.PosDef.one.smul (by exact_mod_cast ha)

lemma scalar_inv (a : ℝ) : (((a : ℂ) • (1 : Mat d))⁻¹) = (a⁻¹ : ℂ) • (1 : Mat d) := by
  by_cases ha : a = 0
  · simp [ha]
  · let : Invertible (a : ℂ) := invertibleOfNonzero (by exact_mod_cast ha)
    rw [Matrix.inv_smul _ _ (by simp), invOf_eq_inv]
    simp

theorem le_trace_smul_one {A : Mat d} (hA : A.PosSemidef) :
    A ≤ (A.trace.re : ℂ) • (1 : Mat d) := by
  let : CStarAlgebra (Mat d) := {}
  have heig (i : Fin d) : hA.isHermitian.eigenvalues i ≤ A.trace.re := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hc : 0 ≤ cfc (fun x : ℝ => A.trace.re - x) A := by
    apply (cfc_nonneg_iff _ A).mpr
    intro x hx
    obtain ⟨i, rfl⟩ := hA.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
    exact sub_nonneg.mpr (heig i)
  rw [cfc_sub (fun _ : ℝ => A.trace.re) (fun x : ℝ => x),
    cfc_const _ A hA.isHermitian.isSelfAdjoint] at hc
  change 0 ≤ (algebraMap ℝ (Mat d)) A.trace.re - cfc (id : ℝ → ℝ) A at hc
  rw [cfc_id ℝ A hA.isHermitian.isSelfAdjoint] at hc
  have hmap : (algebraMap ℝ (Mat d)) A.trace.re = (A.trace.re : ℂ) • (1 : Mat d) := by
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply]
  rw [hmap] at hc
  exact sub_nonneg.mp hc

theorem isCompact_orderBox (a b : ℝ) :
    IsCompact {A : H d | (a • one : H d) ≤ A ∧ A ≤ b • one} := by
  let : CStarAlgebra (Mat d) := {}
  let : ProperSpace (H d) := FiniteDimensional.proper ℝ (H d)
  apply (isCompact_closedBall (a • one : H d) ‖(b-a) • (one : H d)‖).of_isClosed_subset
    (isClosed_orderBox a b)
  intro A hA
  rw [Metric.mem_closedBall]
  change dist (A : Mat d) (a • (1 : Mat d)) ≤ ‖(b-a) • (1 : Mat d)‖
  rw [dist_eq_norm]
  have h₁ : a • (1 : Mat d) ≤ (A : Mat d) := hA.1
  have h₂ : (A : Mat d) ≤ b • (1 : Mat d) := hA.2
  apply CStarAlgebra.norm_le_norm_of_le_of_nonneg _ (sub_nonneg.mpr h₁)
  have hh := sub_le_sub_right h₂ (a • (1 : Mat d))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
    Complex.ofReal_sub]
  ring

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_TraceCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma realTrace_nonneg {A : H d} (hA : A ∈ psdCone d) : 0 ≤ realTrace A :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).1

lemma realTrace_mono {A B : H d} (hab : A ≤ B) : realTrace A ≤ realTrace B := by
  have hh := realTrace_nonneg (show B-A ∈ psdCone d from hab)
  simpa using hh

@[simp] lemma traceCLM_apply (A : H d) : traceCLM A = realTrace A := inner_one A

lemma continuous_realTrace : Continuous (realTrace : H d → ℝ) := by
  have he : (fun A : H d => traceCLM A) = realTrace := funext traceCLM_apply
  rw [← he]
  exact (traceCLM (d := d)).continuous

lemma continuousAt_invH {A : H d} (hA : A ∈ pd d) : ContinuousAt invH A := by
  have hm : ContinuousAt (Inv.inv : Mat d → Mat d) (A : Mat d) := by
    apply continuousAt_matrix_inv
    have he : (Ring.inverse : ℂ → ℂ) = Inv.inv := funext Ring.inverse_eq_inv
    rw [he]
    exact continuousAt_inv₀ hA.det_pos.ne'
  apply tendsto_subtype_rng.mpr
  exact hm.comp continuousAt_subtype_val

lemma pd_of_lower {a : ℝ} (ha : 0 < a) {A : H d} (hA : a • one ≤ A) : A ∈ pd d := by
  have hp : ((A : Mat d) - (a : ℂ) • 1).PosSemidef := hA
  have hs := (scalar_posDef ha).add_posSemidef hp
  simp only [add_sub_cancel] at hs
  exact hs

lemma inverse_bound_below {a : ℝ} (ha : 0 < a) {A : H d}
    (hA : A ∈ pd d) (he : invH A ≤ a • one) : a⁻¹ • one ≤ A := by
  let : Invertible (A : Mat d) := hA.isUnit.invertible
  have hi := inverse_antitone hA.inv (scalar_posDef ha) he
  rw [scalar_inv, Matrix.inv_inv_of_invertible] at hi
  change ((a⁻¹ : ℝ) : ℂ) • (1 : Mat d) ≤ (A : Mat d)
  simpa only [Complex.ofReal_inv] using hi

lemma psd_nonneg {A : H d} (hA : A ∈ psdCone d) : 0 ≤ A := hA.nonneg

lemma mem_psd_iff_nonneg (A : H d) : A ∈ psdCone d ↔ 0 ≤ A := by
  constructor
  · exact psd_nonneg
  · intro hA
    have hh : (0 : Mat d) ≤ (A : Mat d) := hA
    exact hh.posSemidef

lemma scalar_one_mono {r s : ℝ} (hrs : r ≤ s) :
    r • (one : H d) ≤ s • one := by
  apply sub_nonneg.mp
  erw [← sub_smul]
  exact psd_nonneg (psd_smul one_mem_psdCone (sub_nonneg.mpr hrs))

lemma trace_bound_above {A : H d} (hA : A ∈ psdCone d) : A ≤ realTrace A • one :=
  le_trace_smul_one hA

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealTraceSum
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma realTrace_sum {ι : Type*} (s : Finset ι) (A : ι → H d) :
    realTrace (∑ i ∈ s, A i) = ∑ i ∈ s, realTrace (A i) := by
  simp only [← inner_one, inner_sum]

lemma psd_sum {ι : Type*} (s : Finset ι) (A : ι → H d) (hA : ∀ i ∈ s, A i ∈ psdCone d) :
    (∑ i ∈ s, A i) ∈ psdCone d := by
  exact (mem_psd_iff_nonneg _).mpr (Finset.sum_nonneg fun i hi => (mem_psd_iff_nonneg _).mp (hA i hi))

lemma smul_order {A B : H d} (h : A ≤ B) {r : ℝ} (hr : 0 ≤ r) : r • A ≤ r • B := by
  apply sub_nonneg.mp
  rw [← smul_sub r B A]
  exact (mem_psd_iff_nonneg _).mp (psd_smul ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr h)) hr)

lemma scalar_mono_psd {A : H d} (hA : A ∈ psdCone d) {r s : ℝ} (hrs : r ≤ s) : r • A ≤ s • A := by
  apply sub_nonneg.mp
  rw [← sub_smul s r A]
  exact (mem_psd_iff_nonneg _).mp (psd_smul hA (sub_nonneg.mpr hrs))

lemma invH_scalar (a : ℝ) : invH (a • (Hermitian.one : H d)) = a⁻¹ • (Hermitian.one : H d) := by
  apply Subtype.ext
  change (a • (1 : Mat d))⁻¹ = a⁻¹ • (1 : Mat d)
  have h (r : ℝ) : r • (1 : Mat d) = (r : ℂ) • (1 : Mat d) := by
    ext i j
    exact Complex.real_smul
  rw [h a, h a⁻¹, Complex.ofReal_inv]
  exact scalar_inv a

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Sandwich
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section L2Operator

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

lemma sandwich_psd (A U : H d) (hU : U ∈ psdCone d) : sandwich A U ∈ psdCone d := by
  have hh := hU.mul_mul_conjTranspose_same (A : Mat d)
  rw [A.property.eq] at hh
  exact hh

end L2Operator

section Frobenius

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma inner_sandwich (A U P : H d) :
    inner ℝ P (sandwich A U) = inner ℝ (sandwich A P) U := by
  rw [inner_eq_trace, inner_eq_trace]
  change ((P : Mat d) * ((A : Mat d) * (U : Mat d) * (A : Mat d))).trace.re =
    ((A : Mat d) * (P : Mat d) * (A : Mat d) * (U : Mat d)).trace.re
  rw [← mul_assoc, ← mul_assoc, Matrix.trace_mul_comm ((P : Mat d) * (A : Mat d) * (U : Mat d))]
  simp only [mul_assoc]

end Frobenius

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Lookup
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
variable {N n : ℕ}

lemma lookup_some {e : Fin n → Fin N} {i : Fin N} {j : Fin n}
    (h : lookup e i=some j) : e j=i := by
  have hh := List.find?_some h
  exact of_decide_eq_true hh

lemma lookup_none_iff (e : Fin n → Fin N) (i : Fin N) :
    lookup e i=none ↔ ∀ j,e j≠i := by
  simp [lookup,List.find?_eq_none]

lemma lookup_self {e : Fin n → Fin N} (he : Function.Injective e) (j : Fin n) :
    lookup e (e j)=some j := by
  cases hh : lookup e (e j) with
  | none => exact False.elim ((lookup_none_iff e (e j)).mp hh j rfl)
  | some k =>
    have hk := he (lookup_some hh)
    cases hk
    rfl

lemma activeIndices_mem (x : Fin N → ℚ) (i : Fin N) :
    i∈activeIndices x ↔ |x i|<1 := by simp [activeIndices]

lemma activeIndex_injective (x : Fin N → ℚ) : Function.Injective (activeIndex x) := by
  exact ((List.nodup_finRange N).filter _).injective_get

lemma activeIndex_range (x : Fin N → ℚ) (i : Fin N) :
    (∃ j,activeIndex x j=i) ↔ |x i|<1 := by
  rw [←activeIndices_mem]
  exact List.mem_iff_get.symm

lemma sum_lookup {β : Type*} [AddCommMonoid β] (e : Fin n → Fin N)
    (he : Function.Injective e) (f : Fin N → Fin n → β) :
    (∑ i,(lookup e i).elim 0 (f i))=∑ j,f (e j) j := by
  symm
  apply Fintype.sum_of_injective e he
  · intro i hi
    have hn : ∀ j,e j≠i := fun j hj => hi ⟨j,hj⟩
    simp only [(lookup_none_iff e i).mpr hn,Option.elim_none]
  · intro j
    simp only [lookup_self he,Option.elim_some]

lemma sum_extend {β γ : Type*} [AddCommMonoid γ] (e : Fin n → Fin N)
    (he : Function.Injective e) (f : Fin N → β → γ) (base : Fin N → β) (y : Fin n → β) :
    (∑ i,f i (extend e base y i))=
      (∑ i,(lookup e i).elim (f i (base i)) (fun _ => 0))+(∑ j,f (e j) (y j)) := by
  rw [←sum_lookup e he (fun i j => f i (y j)),←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold extend
  cases lookup e i <;> simp

lemma real_active_outside_endpoint (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (i : Fin N)
    (hi : lookup (activeIndex x) i=none) : |(x i:ℝ)|=1 := by
  have hn : ¬|x i|<1 := by
    intro h
    obtain ⟨j,hj⟩ := (activeIndex_range x i).mpr h
    exact (lookup_none_iff _ _).mp hi j hj
  have he : |x i|=1 := le_antisymm (hx i) (le_of_not_gt hn)
  exact_mod_cast he

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Point
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma feasible_iff (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :
    z ∈ feasible S η ↔ z.2.1 ∈ pd d ∧ z.2.2 ∈ pd d ∧
      invH z.2.1 + S + η z.2.2 ≤ z.1 • (Hermitian.one : H d) ∧
      invH z.2.2 - S + η z.2.1 ≤ z.1 • (Hermitian.one : H d) := by
  simp only [feasible, domain, residual, mem_ofPred_eq, sub_nonpos]
  tauto

lemma continuous_objective (ε : ℝ) : Continuous (objective (d := d) ε) := by
  exact continuous_fst.add (continuous_const.mul
    (continuous_realTrace.comp ((continuous_fst.comp continuous_snd).add
      (continuous_snd.comp continuous_snd))))

lemma trace_bounds_of_feasible [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {z : Point d} (hz : z ∈ feasible S η) :
    0 ≤ z.1 ∧ 0 ≤ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.1 ∧ 0 ≤ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.2 := by
  obtain ⟨hX, hY, h₁, h₂⟩ := (feasible_iff S η z).mp hz
  have htr₁ := realTrace_mono h₁
  have htr₂ := realTrace_mono h₂
  have hiX := realTrace_nonneg (A := invH z.2.1) hX.inv.posSemidef
  have hiY := realTrace_nonneg (A := invH z.2.2) hY.inv.posSemidef
  have heX := realTrace_nonneg (hη _ hX.posSemidef)
  have heY := realTrace_nonneg (hη _ hY.posSemidef)
  simp only [realTrace_add, realTrace_sub, realTrace_smul, realTrace_one] at htr₁ htr₂
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  refine ⟨?_, realTrace_nonneg hX.posSemidef, realTrace_nonneg hY.posSemidef⟩
  nlinarith

lemma objective_bounds [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) {z : Point d} (hz : z ∈ feasible S η)
    (hf : objective ε z ≤ K) :
    0 ≤ z.1 ∧ z.1 ≤ K ∧ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.1 ≤ K / ε ∧ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.2 ≤ K / ε := by
  obtain ⟨ht, hX, hY⟩ := trace_bounds_of_feasible S η hη hz
  simp only [objective, realTrace_add] at hf
  refine ⟨ht, ?_, (le_div_iff₀ hε).mpr ?_, (le_div_iff₀ hε).mpr ?_⟩ <;>
    nlinarith [mul_nonneg hε.le hX, mul_nonneg hε.le hY]

lemma inverse_bounds (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    {z : Point d} (hz : z ∈ feasible S η) (ht : z.1 ≤ K) :
    invH z.2.1 ≤ (2*K) • (Hermitian.one : H d) ∧ invH z.2.2 ≤ (2*K) • (Hermitian.one : H d) := by
  obtain ⟨hX, hY, h₁, h₂⟩ := (feasible_iff S η z).mp hz
  have heX : 0 ≤ η z.2.1 := psd_nonneg (hη _ hX.posSemidef)
  have heY : 0 ≤ η z.2.2 := psd_nonneg (hη _ hY.posSemidef)
  have htk : z.1 • (Hermitian.one : H d) ≤ K • (Hermitian.one : H d) := scalar_one_mono ht
  constructor
  · have hh : invH z.2.1 + S ≤ K • (Hermitian.one : H d) :=
      (le_add_of_nonneg_right heY).trans (h₁.trans htk)
    have hx := add_le_add hh (neg_le_neg hS₁)
    convert hx using 1 <;> first | rfl | module
  · have hh : invH z.2.2 - S ≤ K • (Hermitian.one : H d) :=
      (le_add_of_nonneg_right heX).trans (h₂.trans htk)
    have hx := add_le_add hh hS₂
    convert hx using 1 <;> first | rfl | module

lemma sublevel_box [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    {z : Point d} (hz : z ∈ feasible S η) (hf : objective ε z ≤ K) :
    z.1 ∈ Icc 0 K ∧
    ((2*K)⁻¹ • (Hermitian.one : H d) ≤ z.2.1 ∧ z.2.1 ≤ (K/ε) • (Hermitian.one : H d)) ∧
    ((2*K)⁻¹ • (Hermitian.one : H d) ≤ z.2.2 ∧ z.2.2 ≤ (K/ε) • (Hermitian.one : H d)) := by
  obtain ⟨ht, htK, htrX, htrY⟩ := objective_bounds S η hη hε hz hf
  obtain ⟨hXi, hYi⟩ := inverse_bounds S η hη hS₁ hS₂ hz htK
  obtain ⟨hX,hY,-,-⟩ := (feasible_iff S η z).mp hz
  have hmul : ∀ r s : ℝ, r ≤ s → r • (Hermitian.one : H d) ≤ s • (Hermitian.one : H d) :=
    fun _ _ h => scalar_one_mono h
  exact ⟨⟨ht,htK⟩,
    ⟨inverse_bound_below (by positivity) hX hXi,
      (trace_bound_above hX.posSemidef).trans (hmul _ _ htrX)⟩,
    ⟨inverse_bound_below (by positivity) hY hYi,
      (trace_bound_above hY.posSemidef).trans (hmul _ _ htrY)⟩⟩

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PairCone
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma isClosed_pairCone : IsClosed (pairCone d : Set (H d × H d)) :=
  (isClosed_psdCone (d := d)).prod (isClosed_psdCone (d := d))

lemma feasible_iff_cone (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :
    z ∈ feasible S η ↔ z ∈ domain d ∧ -residual S η z ∈ pairCone d := by
  simp only [feasible, mem_ofPred_eq, mem_pairCone, Prod.fst_neg, Prod.snd_neg]
  simp only [mem_psd_iff_nonneg, neg_nonneg]

lemma continuousOn_residual (S : H d) (η : H d →L[ℝ] H d) :
    ContinuousOn (residual S η) (domain d) := by
  intro z hz
  have hiX : ContinuousAt (fun z : Point d => invH z.2.1) z :=
    (continuousAt_invH hz.1).comp (f := fun w : Point d => w.2.1) (x := z) (by fun_prop)
  have hiY : ContinuousAt (fun z : Point d => invH z.2.2) z :=
    (continuousAt_invH hz.2).comp (f := fun w : Point d => w.2.2) (x := z) (by fun_prop)
  have heX : ContinuousAt (fun z : Point d => η z.2.1) z :=
    η.continuous.continuousAt.comp (f := fun w : Point d => w.2.1) (x := z) (by fun_prop)
  have heY : ContinuousAt (fun z : Point d => η z.2.2) z :=
    η.continuous.continuousAt.comp (f := fun w : Point d => w.2.2) (x := z) (by fun_prop)
  exact (((hiX.add continuousAt_const).add heY).sub
    (continuousAt_fst.smul continuousAt_const)).prodMk
      (((hiY.sub continuousAt_const).add heX).sub
        (continuousAt_fst.smul continuousAt_const)) |>.continuousWithinAt

theorem exists_minimizer [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    (z₀ : Point d) (hz₀ : z₀ ∈ feasible S η) (hf₀ : objective ε z₀ ≤ K) :
    ∃ z ∈ feasible S η, objective ε z ≤ K ∧
      ∀ w ∈ feasible S η, objective ε z ≤ objective ε w := by
  let B : Set (Point d) := Icc 0 K ×ˢ
    ({A : H d | (2*K)⁻¹ • (Hermitian.one : H d) ≤ A ∧ A ≤ (K/ε) • (Hermitian.one : H d)} ×ˢ
      {A : H d | (2*K)⁻¹ • (Hermitian.one : H d) ≤ A ∧ A ≤ (K/ε) • (Hermitian.one : H d)})
  have hBc : IsCompact B := isCompact_Icc.prod
    ((isCompact_orderBox _ _).prod (isCompact_orderBox _ _))
  have hBD : B ⊆ domain d := by
    intro z hz
    exact ⟨pd_of_lower (by positivity) hz.2.1.1, pd_of_lower (by positivity) hz.2.2.1⟩
  let F : Point d → (H d × H d) × ℝ := fun z => (-residual S η z, objective ε z)
  have hFc : ContinuousOn F B := ((continuousOn_residual S η).mono hBD).neg.prodMk
    (continuous_objective ε).continuousOn
  let C : Set (Point d) := B ∩ F ⁻¹' ((pairCone d : Set (H d × H d)) ×ˢ Iic K)
  have hCc : IsClosed C := hFc.preimage_isClosed_of_isClosed hBc.isClosed
    (isClosed_pairCone.prod isClosed_Iic)
  have hCcompact : IsCompact C := hBc.of_isClosed_subset hCc inter_subset_left
  have hCm (z : Point d) : z ∈ C ↔ z ∈ B ∧ z ∈ feasible S η ∧ objective ε z ≤ K := by
    simp only [C, mem_inter_iff, mem_preimage, mem_prod, mem_Iic, F]
    constructor
    · rintro ⟨hz, hc, hf⟩
      exact ⟨hz, (feasible_iff_cone S η z).mpr ⟨hBD hz, hc⟩, hf⟩
    · rintro ⟨hz, hc, hf⟩
      exact ⟨hz, ((feasible_iff_cone S η z).mp hc).2, hf⟩
  have hnonempty : C.Nonempty := by
    refine ⟨z₀, (hCm z₀).mpr ⟨?_, hz₀, hf₀⟩⟩
    exact sublevel_box S η hη hε hK hS₁ hS₂ hz₀ hf₀
  obtain ⟨z, hz, hmin⟩ := hCcompact.exists_isMinOn hnonempty (continuous_objective ε).continuousOn
  have hzm := (hCm z).mp hz
  refine ⟨z, hzm.2.1, hzm.2.2, fun w hw => ?_⟩
  by_cases hfw : objective ε w ≤ K
  · apply hmin
    exact (hCm w).mpr ⟨sublevel_box S η hη hε hK hS₁ hS₂ hw hfw, hw, hfw⟩
  · exact hzm.2.2.trans (le_of_lt (lt_of_not_ge hfw))

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Coordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.State.line_zero _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r5cd019_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma eta_apply (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (Z : H d) :
    eta c A x Z = ∑ i, (c * psi (x i)) • sandwich (A i) Z := by
  simp [eta]

lemma psi_bounds {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ psi x ∧ psi x ≤ 1 := by
  have hr : 0 ≤ 1-x^2 := by have hh := abs_le.mp hx; nlinarith
  exact ⟨Real.rpow_nonneg hr _, Real.rpow_le_one hr (by nlinarith [sq_nonneg x]) (by norm_num)⟩

lemma eta_positive {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) {x : Coordinates N} (hx : Cube x) :
    ∀ Z ∈ psdCone d, eta c A x Z ∈ psdCone d := by
  intro Z hZ
  rw [eta_apply]
  exact psd_sum _ _ fun i _ => psd_smul (sandwich_psd _ _ hZ) (mul_nonneg hc (psi_bounds (hx i)).1)

lemma eta_symmetric (c : ℝ) (A : Fin N → H d) (x : Coordinates N) : SymmetricMap (eta c A x) := by
  intro U V
  change inner ℝ U (eta c A x V) = inner ℝ (eta c A x U) V
  simp only [eta_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (c*psi (x i)) * inner ℝ U (sandwich (A i) V) :=
      real_inner_smul_right U (sandwich (A i) V) (c*psi (x i))
    _ = (c*psi (x i)) * inner ℝ (sandwich (A i) U) V := by rw [inner_sandwich]
    _ = _ := (real_inner_smul_left (sandwich (A i) U) V (c*psi (x i))).symm

lemma sum_le_one (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i, _root_.OAI.CurrentKS.Hermitian.realTrace (A i) = 1) : (∑ i, A i) ≤ (Hermitian.one : H d) := by
  have hp := trace_bound_above (psd_sum Finset.univ A fun i _ => hA i)
  simpa only [realTrace_sum,htr,one_smul] using hp

lemma S_bounds (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i, _root_.OAI.CurrentKS.Hermitian.realTrace (A i) = 1) {x : Coordinates N} (hx : Cube x) :
    -(Hermitian.one : H d) ≤ S A x ∧ S A x ≤ (Hermitian.one : H d) := by
  have hsum := sum_le_one A hA htr
  have hupper : S A x ≤ ∑ i, A i := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [one_smul] using scalar_mono_psd (hA i) (abs_le.mp (hx i)).2
  have hlower : -(∑ i, A i) ≤ S A x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := scalar_mono_psd (hA i) (abs_le.mp (hx i)).1
    have he : (-1 : ℝ) • A i = -A i := neg_one_smul ℝ (A i)
    rw [he] at hh
    exact hh
  exact ⟨(neg_le_neg hsum).trans hlower,hupper.trans hsum⟩

lemma eta_one_bound {c ν : ℝ} (hc : 0 ≤ c) (A : Fin N → H d)
    (hν : (∑ i, sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    {x : Coordinates N} (hx : Cube x) : eta c A x (Hermitian.one : H d) ≤ (c*ν) • (Hermitian.one : H d) := by
  rw [eta_apply,SemigroupAction.mul_smul]
  apply le_trans _ (smul_order hν hc)
  rw [Finset.smul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact scalar_mono_psd (sandwich_psd _ _ one_mem_psdCone)
    (mul_le_of_le_one_right hc (psi_bounds (hx i)).2)

end CurrentKS.State

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma scalar_feasible (S : H d) (η : H d →L[ℝ] H d) {s b a : ℝ}
    (hs₁ : -s • (Hermitian.one : H d) ≤ S) (hs₂ : S ≤ s • (Hermitian.one : H d))
    (hb : η (Hermitian.one : H d) ≤ b • (Hermitian.one : H d)) (ha : 0 < a) :
    (s+a⁻¹+b*a, a • (Hermitian.one : H d), a • (Hermitian.one : H d)) ∈ feasible S η := by
  have hpd := pd_smul (show (Hermitian.one : H d) ∈ pd d from Matrix.PosDef.one) ha
  apply (feasible_iff _ _ _).mpr
  refine ⟨hpd,hpd,?_,?_⟩
  · change invH (a • (Hermitian.one : H d)) + S + η (a • (Hermitian.one : H d)) ≤
      (s+a⁻¹+b*a) • (Hermitian.one : H d)
    rw [invH_scalar,map_smul]
    calc
      _ ≤ a⁻¹ • (Hermitian.one : H d) + s • (Hermitian.one : H d) + a • (b • (Hermitian.one : H d)) :=
        show a⁻¹ • (Hermitian.one : H d) + S + a • η (Hermitian.one : H d) ≤ _ from
          add_le_add (add_le_add (le_refl (a⁻¹ • (Hermitian.one : H d))) hs₂) (smul_order hb ha.le)
      _ = (s+a⁻¹+b*a) • (Hermitian.one : H d) := by
        rw [smul_smul,← add_smul,← add_smul]
        congr 1
        ring
  · change invH (a • (Hermitian.one : H d)) - S + η (a • (Hermitian.one : H d)) ≤
      (s+a⁻¹+b*a) • (Hermitian.one : H d)
    rw [invH_scalar,map_smul]
    have hns : -S ≤ s • (Hermitian.one : H d) := by
      have hh := neg_le_neg hs₁
      rw [neg_smul s (Hermitian.one : H d), neg_neg] at hh
      exact hh
    change a⁻¹ • (Hermitian.one : H d) + -S + a • η (Hermitian.one : H d) ≤ _
    calc
      _ ≤ a⁻¹ • (Hermitian.one : H d) + s • (Hermitian.one : H d) + a • (b • (Hermitian.one : H d)) :=
        add_le_add (add_le_add (le_refl (a⁻¹ • (Hermitian.one : H d))) hns) (smul_order hb ha.le)
      _ = (s+a⁻¹+b*a) • (Hermitian.one : H d) := by
        rw [smul_smul,← add_smul,← add_smul]
        congr 1
        ring

lemma scalar_objective (ε s b a : ℝ) :
    objective ε (s+a⁻¹+b*a, a • (Hermitian.one : H d), a • (Hermitian.one : H d)) =
      s+a⁻¹+(b+2*d*ε)*a := by
  simp only [objective,realTrace_add,realTrace_smul,realTrace_one]
  ring

end CurrentKS.Variational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormalizedMinimizer
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

theorem normalized_minimizer [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d,η A ∈ psdCone d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε*d ≤ 1) (hlo : -(Hermitian.one : H d) ≤ S)
    (hhi : S ≤ (Hermitian.one : H d))
    (hηI : η (Hermitian.one : H d) ≤ (384:ℝ) • (Hermitian.one : H d)) :
    ∃ z ∈ feasible S η,objective ε z ≤ 100 ∧
      ∀ w ∈ feasible S η,objective ε z ≤ objective ε w := by
  have hlo' : -(100:ℝ) • (Hermitian.one : H d) ≤ S := by
    apply le_trans _ hlo
    have hc := scalar_mono_psd (d:=d) one_mem_psdCone (by norm_num : (-100:ℝ) ≤ -1)
    rw [neg_smul (1:ℝ) (Hermitian.one : H d),one_smul] at hc
    exact hc
  have hhi' : S ≤ (100:ℝ) • (Hermitian.one : H d) := by
    apply hhi.trans
    simpa only [one_smul] using scalar_mono_psd one_mem_psdCone (by norm_num : (1:ℝ) ≤ 100)
  let z₀ : Point d := (1+(1/20:ℝ)⁻¹+384*(1/20),(1/20:ℝ) • (Hermitian.one : H d),(1/20:ℝ) • (Hermitian.one : H d))
  have hz₀ : z₀ ∈ feasible S η :=
    scalar_feasible S η (s:=1) (b:=384) (a:=1/20)
      (by rw [neg_smul (1:ℝ) (Hermitian.one : H d),one_smul]; exact hlo)
      (by simpa only [one_smul] using hhi) hηI (by norm_num)
  have hf : objective ε z₀ ≤ 100 := by
    dsimp [z₀]
    rw [scalar_objective]
    norm_num
    nlinarith
  exact exists_minimizer S η hη hε (by norm_num) hlo' hhi' z₀ hz₀ hf
end CurrentKS.Variational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Potential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma psi_endpoint {t : ℝ} (ht : |t| = 1) : psi t = 0 := by
  have hh : t^2 = 1 := by nlinarith [sq_abs t]
  simp [psi,hh]

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_FixedPart
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Variational
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

variable {d N n : ℕ}

lemma S_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d) (y : Coordinates n) :
    S A (extend e base y)=fixedPart e base A+S (fun j => A (e j)) y := by
  exact sum_extend e he (fun (i : Fin N) (t : ℝ) => (t • A i : H d)) base y

lemma eta_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hb : ∀ i,lookup e i=none → |base i|=1) (y : Coordinates n) (c : ℝ) :
    eta c A (extend e base y)=eta c (fun j => A (e j)) y := by
  apply ContinuousLinearMap.ext
  intro Z
  rw [eta_apply,eta_apply]
  have hsum := sum_extend e he (fun (i : Fin N) (t : ℝ) => ((c*psi t) • sandwich (A i) Z : H d)) base y
  rw [hsum]
  have hz : (∑ i,(lookup e i).elim ((c*psi (base i)) • sandwich (A i) Z) (fun _ => 0))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    cases hi : lookup e i with
    | none => simp only [Option.elim_none,psi_endpoint (hb i hi),mul_zero,zero_smul]
    | some j => rfl
  rw [hz,zero_add]

end CurrentKS.RationalFace

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_CoarseBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
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

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Line
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Scalar Filter
open scoped BigOperators Topology

variable {N : ℕ}

lemma contDiffAt_penalty {x : Coordinates N} (hx : ∀ i, |x i| < 1) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n penalty x := by
  apply ContDiffAt.sum
  intro i _
  exact (contDiffAt_psi (hx i)).comp x (contDiffAt_apply ℝ ℝ i x)

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FacePotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Scalar CurrentKS.Calculus
open scoped BigOperators ContDiff

variable {d N : ℕ}

lemma norm_coordinate_projection_le_one (i : Fin N) :
    ‖(ContinuousLinearMap.proj i : Coordinates N →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  simp only [one_mul]
  exact norm_le_pi_norm y i

lemma contDiffAt_penalty_coordinate {x : Coordinates N} {σ : ℝ}
    (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) (i : Fin N) :
    ContDiffAt ℝ 3 (fun y : Coordinates N => psi (y i)) x := by
  exact ContDiffAt.comp (f := fun y : Coordinates N => y i) (g := psi) x
    (contDiffAt_psi (strip_interior hσ (hx i))) (contDiffAt_apply ℝ ℝ i x)

lemma penalty_coordinate_jet {x : Coordinates N} {σ : ℝ}
    (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) (i : Fin N) :
    JetBound (fun y : Coordinates N => psi (y i)) x (1+800/σ^3) := by
  exact JetBound.comp_linear (E:=Coordinates N) (F:=ℝ) (G:=ℝ) (f:=psi) (x:=x)
    (ContinuousLinearMap.proj i) (contDiffAt_psi (strip_interior hσ (hx i)))
    (jetBound_psi hσ (hx i)) (norm_coordinate_projection_le_one i)

lemma penalty_strip_jet {x : Coordinates N} {σ : ℝ}
    (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) :
    JetBound penalty x ((N:ℝ)*(1+800/σ^3)) := by
  have hh := JetBound.sum (E:=Coordinates N) (F:=ℝ) Finset.univ
    (fun i _ => contDiffAt_penalty_coordinate hσ hx i)
    (fun i _ => penalty_coordinate_jet hσ hx i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  exact hh

lemma penalty_strip_deriv {x h : Coordinates N} {σ : ℝ}
    (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) (hh : ‖h‖ ≤ 1)
    {n : ℕ} (hn : n ≤ 3) :
    |iteratedDeriv n (fun t : ℝ => penalty (x+t • h)) 0| ≤ (N:ℝ)*(1+800/σ^3) := by
  have hj := JetBound.line (E:=Coordinates N) (F:=ℝ)
    (contDiffAt_penalty (fun i => strip_interior hσ (hx i))) (penalty_strip_jet hσ hx) hh n hn
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs] using hj

open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff


lemma valueCurve_bounds_nonneg {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    0 ≤ valueCurve2Bound d N ε σ ∧ 0 ≤ valueCurve3Bound d N ε σ := by
  have hB := (coarseBudget_bounds (d:=d) (N:=N) hε hσ).1
  dsimp [valueCurve2Bound,valueCurve3Bound]
  constructor <;> positivity

lemma scalar_hundred_bounds {S : H d} (hlo : -(Hermitian.one : H d) ≤ S)
    (hhi : S ≤ (Hermitian.one : H d)) :
    -(100:ℝ) • (Hermitian.one : H d) ≤ S ∧ S ≤ (100:ℝ) • (Hermitian.one : H d) := by
  constructor
  · apply le_trans _ hlo
    have hc := scalar_mono_psd (d:=d) one_mem_psdCone (by norm_num : (-100:ℝ) ≤ -1)
    rw [neg_smul (1:ℝ) (Hermitian.one : H d),one_smul] at hc
    exact hc
  · apply hhi.trans
    simpa only [one_smul] using
      scalar_mono_psd (d:=d) one_mem_psdCone (by norm_num : (1:ℝ) ≤ 100)

theorem contDiffAt_facePotential [NeZero d] (A : Fin N → H d)
    (S₀ : H d) (x : Coordinates N) {ε lam : ℝ} (hε : 0 < ε) (hεd : ε*d ≤ 1)
    (hx : ∀ i,|x i| < 1)
    (hlo : -(Hermitian.one : H d) ≤ S₀+S A x)
    (hhi : S₀+S A x ≤ (Hermitian.one : H d))
    (hηI : eta 384 A x (Hermitian.one : H d) ≤ (384:ℝ) • (Hermitian.one : H d)) :
    ContDiffAt ℝ ∞ (facePotential ε lam S₀ A) x := by
  have hpos := eta_positive (by norm_num : (0:ℝ)≤384) A (fun i => (hx i).le)
  obtain ⟨z,hz,_,hmin⟩ := normalized_minimizer (S₀+S A x) (eta 384 A x)
    hpos hε hεd hlo hhi hηI
  have hS100 := scalar_hundred_bounds hlo hhi
  have hv := contDiffAt_value ε hε (fun y => S₀+S A y) (eta 384 A) x
    (contDiffAt_const.add (contDiff_S A).contDiffAt) (contDiffAt_eta 384 A hx)
    hpos (Filter.Eventually.of_forall (fun y => eta_symmetric 384 A y))
    hS100.1 hS100.2 z hz hmin
  exact hv.add (contDiffAt_const.mul (contDiffAt_penalty hx))

lemma line_potential_derivative_bound {f g : ℝ → ℝ} {n : ℕ} {lam B C : ℝ}
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0)
    (hB : |iteratedDeriv n f 0| ≤ B) (hC : |iteratedDeriv n g 0| ≤ C) :
    |iteratedDeriv n (fun t => f t+lam*g t) 0| ≤ B+|lam| *C := by
  rw [iteratedDeriv_fun_add hf (contDiffAt_const.mul hg),iteratedDeriv_const_mul_field]
  exact (abs_add_le _ _).trans (add_le_add hB (by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hC (abs_nonneg lam)))

theorem facePotential_strip_derivatives [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (hAn : ∀ i,‖A i‖ ≤ 1)
    (S₀ : H d) (hS₀ : ‖S₀‖ ≤ (d:ℝ)+1) (x h : Coordinates N)
    {ε σ lam : ℝ} (hε : 0 < ε) (hεd : ε*d ≤ 1)
    (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) (hh : ‖h‖ ≤ 1)
    (hlo : -(Hermitian.one : H d) ≤ S₀+S A x)
    (hhi : S₀+S A x ≤ (Hermitian.one : H d))
    (hηI : eta 384 A x (Hermitian.one : H d) ≤ (384:ℝ) • (Hermitian.one : H d)) :
    |iteratedDeriv 2 (fun t : ℝ => facePotential ε lam S₀ A (x+t • h)) 0| ≤
      potentialCurveBound d N ε σ lam ∧
    |iteratedDeriv 3 (fun t : ℝ => facePotential ε lam S₀ A (x+t • h)) 0| ≤
      potentialCurveBound d N ε σ lam := by
  have hxi (i : Fin N) := strip_interior hσ (hx i)
  have hpos := eta_positive (by norm_num : (0:ℝ)≤384) A (fun i => (hxi i).le)
  obtain ⟨z,hz,hz100,hmin⟩ := normalized_minimizer (S₀+S A x) (eta 384 A x)
    hpos hε hεd hlo hhi hηI
  have hS100 := scalar_hundred_bounds hlo hhi
  have hb := value_strip_derivatives A hA hAn S₀ hS₀ x h hε hσ hx hh
    hS100.1 hS100.2 z hz hz100 hmin
  change _ ≤ valueCurve2Bound d N ε σ ∧ _ ≤ valueCurve3Bound d N ε σ at hb
  have hline : ContDiff ℝ ∞ (fun t : ℝ => x+t • h) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hv := contDiffAt_value ε hε (fun y => S₀+S A y) (eta 384 A) x
    (contDiffAt_const.add (contDiff_S A).contDiffAt) (contDiffAt_eta 384 A hxi)
    hpos (Filter.Eventually.of_forall (fun y => eta_symmetric 384 A y))
    hS100.1 hS100.2 z hz hmin
  have hv0 : ContDiffAt ℝ ∞ (fun t : ℝ => value ε (S₀+S A (x+t • h)) (eta 384 A (x+t • h))) 0 := by
    have hv' : ContDiffAt ℝ ∞ (fun y => value ε (S₀+S A y) (eta 384 A y)) (x+(0:ℝ) • h) := by simpa using hv
    exact ContDiffAt.comp (f:=fun t : ℝ => x+t • h) (g:=fun y => value ε (S₀+S A y) (eta 384 A y)) 0 hv' hline.contDiffAt
  have hp0 : ContDiffAt ℝ ∞ (fun t : ℝ => penalty (x+t • h)) 0 := by
    have hp : ContDiffAt ℝ ∞ penalty (x+(0:ℝ) • h) := by simpa using contDiffAt_penalty hxi
    exact ContDiffAt.comp (f:=fun t : ℝ => x+t • h) (g:=penalty) 0 hp hline.contDiffAt
  have hp (n : ℕ) (hn : n ≤ 3) := penalty_strip_deriv hσ hx hh hn
  have hnon := valueCurve_bounds_nonneg (d:=d) (N:=N) hε hσ
  constructor
  · have ht := line_potential_derivative_bound (lam:=lam)
      (hv0.of_le (WithTop.coe_le_coe.mpr (show (2:ℕ∞) ≤ ⊤ from le_top)))
      (hp0.of_le (WithTop.coe_le_coe.mpr (show (2:ℕ∞) ≤ ⊤ from le_top))) hb.1 (hp 2 (by norm_num))
    change _ ≤ potentialCurveBound d N ε σ lam
    apply ht.trans
    dsimp [potentialCurveBound]
    nlinarith [hnon.2]
  · have ht := line_potential_derivative_bound (lam:=lam)
      (hv0.of_le (WithTop.coe_le_coe.mpr (show (3:ℕ∞) ≤ ⊤ from le_top)))
      (hp0.of_le (WithTop.coe_le_coe.mpr (show (3:ℕ∞) ≤ ⊤ from le_top))) hb.2 (hp 3 (by norm_num))
    apply ht.trans
    dsimp [potentialCurveBound]
    nlinarith [hnon.1]
end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RealExtendCube
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Variational
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d N n : ℕ}

lemma real_extend_cube (e : Fin n → Fin N) (base : Coordinates N) (y : Coordinates n)
    (hb : Cube base) (hy : Cube y) : Cube (extend e base y) := by
  intro i
  unfold extend
  cases lookup e i with
  | none => exact hb i
  | some j => exact hy j

lemma norm_psd_le_trace_h (A : H d) (hA : A∈psdCone d) : ‖A‖≤Hermitian.realTrace A := by
  have ht := trace_bound_above hA
  have hh := inner_nonneg_of_psd A (Hermitian.realTrace A • Hermitian.one-A) hA
    ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr ht))
  rw [inner_sub_right,real_inner_smul_right A (Hermitian.one : H d) (Hermitian.realTrace A),inner_one',real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg A,realTrace_nonneg hA]

lemma norm_atoms_le_one (A : Fin N → H d) (hA : ∀ i,A i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (A i)=1) (i : Fin N) : ‖A i‖≤1 := by
  apply (norm_psd_le_trace_h (A i) (hA i)).trans
  rw [←htr]
  exact Finset.single_le_sum (fun j _ => realTrace_nonneg (hA j)) (Finset.mem_univ i)

lemma fixedPart_norm_le_one (e : Fin n → Fin N) (base : Coordinates N)
    (A : Fin N → H d) (hA : ∀ i,A i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (A i)=1) (hb : Cube base) : ‖fixedPart e base A‖≤1 := by
  unfold fixedPart
  apply norm_sum_le _ _ |>.trans
  rw [←htr]
  apply Finset.sum_le_sum
  intro i _
  cases hi : lookup e i with
  | none =>
    simp only [Option.elim_none,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)).trans
      (by simpa only [one_mul] using norm_psd_le_trace_h (A i) (hA i))
  | some j => simpa only [Option.elim_some,norm_zero] using realTrace_nonneg (hA i)

lemma face_order_bounds (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    (hb : Cube base) (y : Coordinates n) (hy : Cube y) :
    -(Hermitian.one : H d)≤fixedPart e base A+S (fun j => A (e j)) y ∧
    fixedPart e base A+S (fun j => A (e j)) y≤(Hermitian.one : H d) := by
  rw [←S_extend e he]
  exact S_bounds A hA htr (real_extend_cube e base y hb hy)

lemma face_eta_one_bound (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(Hermitian.one : H d))
    (hb : Cube base) (hfixed : ∀ i,lookup e i=none → |base i|=1)
    (y : Coordinates n) (hy : Cube y) :
    eta 384 (fun j => A (e j)) y (Hermitian.one : H d)≤(384:ℝ) • (Hermitian.one : H d) := by
  rw [←eta_extend e he base A hfixed y]
  have hv : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(1:ℝ) • (Hermitian.one : H d) := by simpa using hvar
  simpa only [mul_one] using eta_one_bound (by norm_num : (0:ℝ)≤384) A hv
    (real_extend_cube e base y hb hy)

lemma strip_nearby (x y : Coordinates n) {σ r : ℝ} (hr : 0 ≤ r)
    (hx : ∀ i,|x i|≤1-σ) (hy : ‖y-x‖ ≤ r) (hrσ : r≤σ/2) :
    ∀ i,|y i|≤1-σ/2 := by
  intro i
  have hnorm := (pi_norm_le_iff_of_nonneg hr).mp hy i
  change ‖y i-x i‖ ≤ r at hnorm
  rw [Real.norm_eq_abs] at hnorm
  have hab := (abs_sub_le (y i) (x i) 0)
  simp only [sub_zero] at hab
  linarith [hx i]

theorem face_smooth_and_derivatives [NeZero d]
    (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(Hermitian.one : H d))
    (hb : Cube base) (hfixed : ∀ i,lookup e i=none → |base i|=1)
    {ε σ lam : ℝ} (hε : 0<ε) (hεd : ε*d≤1) (hσ : 0<σ)
    (y : Coordinates n) (hy : ∀ j,|y j|≤1-σ/2) :
    ContDiffAt ℝ ∞ (facePotential ε lam (fixedPart e base A) (fun j => A (e j))) y ∧
    ∀ u,‖u‖≤1 →
      |iteratedDeriv 2 (fun t : ℝ => facePotential ε lam (fixedPart e base A)
        (fun j => A (e j)) (y+t • u)) 0|≤potentialCurveBound d n ε σ lam ∧
      |iteratedDeriv 3 (fun t : ℝ => facePotential ε lam (fixedPart e base A)
        (fun j => A (e j)) (y+t • u)) 0|≤potentialCurveBound d n ε σ lam := by
  have hyi : ∀ j,|y j|<1 := fun j => strip_interior hσ (hy j)
  have hyc : Cube y := fun j => (hyi j).le
  have hord := face_order_bounds e he base A hA htr hb y hyc
  have hη := face_eta_one_bound e he base A hvar hb hfixed y hyc
  have hAn : ∀ j,‖A (e j)‖≤1 := fun j => norm_atoms_le_one A hA htr (e j)
  have hS₀ : ‖fixedPart e base A‖≤(d:ℝ)+1 := by
    have hh := fixedPart_norm_le_one e base A hA htr hb
    linarith [Nat.cast_nonneg (α:=ℝ) d]
  exact ⟨contDiffAt_facePotential _ _ y hε hεd hyi hord.1 hord.2 hη,
    fun u hu => facePotential_strip_derivatives _ (fun j => hA (e j)) hAn _ hS₀
      y u hε hεd hσ hy hu hord.1 hord.2 hη⟩

end
end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_MovementBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule

open CurrentKS.State

lemma coarseBudgetQ_cast (d n : ℕ) (ε σ : ℚ) :
    (coarseBudgetQ d n ε σ:ℝ)=coarseBudget d n (ε:ℝ) (σ:ℝ) := by
  simp only [coarseBudgetQ,coarseBudget,Rat.cast_add,Rat.cast_mul,Rat.cast_div,
    Rat.cast_pow,Rat.cast_natCast,Rat.cast_abs,Rat.cast_ofNat,Rat.cast_one]

lemma curveBudget_cast (d n : ℕ) (ε σ lam : ℚ) :
    (curveBudget d n ε σ lam:ℝ)=potentialCurveBound d n (ε:ℝ) (σ:ℝ) (lam:ℝ) := by
  simp only [curveBudget,potentialCurveBound,valueCurve2Q,valueCurve3Q,
    valueCurve2Bound,valueCurve3Bound,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_abs,Rat.cast_inv,Rat.cast_one,Rat.cast_ofNat,coarseBudgetQ_cast]

end CurrentKS.Schedule

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FaceState
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d N : ℕ}

lemma variance_le_one (A : Fin N → H d) {ν : ℚ} (hν1 : ν ≤ 1)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ (ν:ℝ) • (Hermitian.one : H d)) :
    (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ (Hermitian.one : H d) := by
  calc
    _ ≤ (ν:ℝ) • (Hermitian.one : H d) := hvar
    _ ≤ (1:ℝ) • (Hermitian.one : H d) := scalar_one_mono (by exact_mod_cast hν1)
    _ = _ := one_smul ℝ _

lemma epsilon_spec [NeZero d] {ν : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    0 < ν/(d:ℚ) ∧ ν/(d:ℚ) ≤ 1 ∧ ν/(d:ℚ)*(d:ℚ) ≤ 1 := by
  have hd : (0:ℚ) < d := by exact_mod_cast NeZero.pos d
  have hd1 : (1:ℚ) ≤ d := by exact_mod_cast NeZero.pos d
  refine ⟨div_pos hν hd,(div_le_one hd).mpr (hν1.trans hd1),?_⟩
  simpa only [div_mul_cancel₀ _ hd.ne'] using hν1

lemma activePotential_regular_oai [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam σ : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hσ : 0 < σ)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i| ≤ 1)
    (hx : ∀ i,|faceState base i| ≤ 1-σ)
    {r : ℝ} (hr : 0 ≤ r) (hrσ : r ≤ (σ:ℝ)/2)
    (y : Coordinates (activeIndices base).length) (hy : ‖y-pointCast (faceState base)‖ ≤ r) :
    ContDiffAt ℝ 3 (activePotential coords base ν lam) y ∧
      ∀ u,‖u‖ ≤ 1 →
        |iteratedDeriv 2 (fun t : ℝ => activePotential coords base ν lam (y+t • u)) 0| ≤
          (curveBudget d (activeIndices base).length (ν/(d:ℚ)) σ lam:ℝ) ∧
        |iteratedDeriv 3 (fun t : ℝ => activePotential coords base ν lam (y+t • u)) 0| ≤
          (curveBudget d (activeIndices base).length (ν/(d:ℚ)) σ lam:ℝ) := by
  have hep := epsilon_spec (d:=d) hν hν1
  have hbr : Cube (fun i => (base i:ℝ)) := fun i => (show |(base i:ℝ)| ≤ 1 by exact_mod_cast hb i)
  have hxr : ∀ i,|pointCast (faceState base) i| ≤ 1-(σ:ℝ) := fun i => (show |(faceState base i:ℝ)| ≤ 1-(σ:ℝ) by exact_mod_cast hx i)
  have hystrip := strip_nearby (pointCast (faceState base)) y hr hxr hy hrσ
  have hh := face_smooth_and_derivatives (ε:=((ν/(d:ℚ):ℚ):ℝ)) (σ:=(σ:ℝ)) (activeIndex base) (activeIndex_injective base)
    (fun i => (base i:ℝ)) (rationalAtoms coords) hA htr (variance_le_one _ hν1 hvar)
    hbr (real_active_outside_endpoint base hb) (by exact_mod_cast hep.1)
    (by exact_mod_cast hep.2.2) (by exact_mod_cast hσ) y hystrip (lam:=(lam:ℝ))
  refine ⟨hh.1.of_le (by decide),?_⟩
  simpa only [activePotential,curveBudget_cast] using hh.2

end
end CurrentKS.RationalFace

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.RationalFace.activePotential_regular_oai := @OAI.CurrentKS.RationalFace.activePotential_regular_oai
