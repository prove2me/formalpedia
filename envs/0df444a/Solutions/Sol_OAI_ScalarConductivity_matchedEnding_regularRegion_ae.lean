-- Prove2me | solution 1 for OAI.ScalarConductivity.matchedEnding_regularRegion_ae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:16:13.885056+00:00
-- url     : https://prove2.me/submissions/109d92c2-dba0-49b0-b069-b049f3838247

import Mathlib
import Definitions.Def_OAIQ059C008

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_ModeConnector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma connectorRate_smooth (K : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (connectorRate K) := by
  exact contDiff_const.add (contDiff_const.mul (smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const K)))

lemma connectorRate_left {K z : ℝ} (hK : 0 < K) (hz : z ≤ 1) :
    connectorRate K z = 1/2 := by
  rw [connectorRate,smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hK.le)]
  ring
lemma connectorRate_right {K z : ℝ} (hK : 0 < K) (hz : K+1 ≤ z) :
    connectorRate K z = 3 := by
  rw [connectorRate,smoothTransition.one_of_one_le
    ((le_div_iff₀ hK).mpr (by linarith))]
  ring

lemma connectorProfile_pos (K z : ℝ) : 0 < connectorProfile K z := exp_pos _
lemma connectorProfile_smooth (K : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (connectorProfile K) := by
  let r : SmoothScalar ℝ := ⟨connectorRate K,connectorRate_smooth K⟩
  exact ((smoothScalar_contDiff (smoothPrimitive r)).neg).exp

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma crossingOn_smooth (L : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingOn L) := by
  exact smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).div_const L |>.add contDiff_const)
lemma crossingOff_smooth (L : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingOff L) := by
  exact contDiff_const.sub (smoothTransition.contDiff.comp
    (((contDiff_const.mul contDiff_id).div_const L).sub contDiff_const))
lemma crossingFirst_smooth (L : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingFirst L) := by
  exact (crossingOff_smooth L).mul ((contDiff_const.mul contDiff_id).exp)
lemma crossingSecond_smooth (L : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingSecond L) := by
  exact (crossingOn_smooth L).mul (contDiff_id.neg.exp)

lemma crossingOn_eq_zero {L z : ℝ} (hL : 0 < L) (hz : z ≤ -3*L/4) :
    crossingOn L z = 0 := by
  apply smoothTransition.zero_of_nonpos
  have : 4*z/L ≤ -3 := (div_le_iff₀ hL).mpr (by linarith)
  linarith
lemma crossingOn_eq_one {L z : ℝ} (hL : 0 < L) (hz : -L/2 ≤ z) :
    crossingOn L z = 1 := by
  apply smoothTransition.one_of_one_le
  have : -2 ≤ 4*z/L := (le_div_iff₀ hL).mpr (by linarith)
  linarith
lemma crossingOff_eq_one {L z : ℝ} (hL : 0 < L) (hz : z ≤ L/2) :
    crossingOff L z = 1 := by
  have : 4*z/L ≤ 2 := (div_le_iff₀ hL).mpr (by linarith)
  rw [crossingOff,smoothTransition.zero_of_nonpos (by linarith),sub_zero]
lemma crossingOff_eq_zero {L z : ℝ} (hL : 0 < L) (hz : 3*L/4 ≤ z) :
    crossingOff L z = 0 := by
  have : 3 ≤ 4*z/L := (le_div_iff₀ hL).mpr (by linarith)
  rw [crossingOff,smoothTransition.one_of_one_le (by linarith),sub_self]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma connectorProfile_left {K z : ℝ} (hK : 0 < K) (hz : z ≤ 1) :
    connectorProfile K z = exp (-z/2) := by
  have hi : (∫ t in (0:ℝ)..z, connectorRate K t) = z/2 := by
    calc
      _ = ∫ _t in (0:ℝ)..z, (1/2:ℝ) := intervalIntegral.integral_congr (by
        intro t ht
        exact connectorRate_left hK ((le_max_iff.mp ht.2).elim (by intro h; linarith) (by intro h; linarith)))
      _ = _ := by simp; ring
  rw [connectorProfile,hi]
  congr 1
  ring

lemma connectorProfile_right {K z : ℝ} (hK : 0 < K) (hz : K+1 ≤ z) :
    connectorProfile K z = connectorProfile K (K+2)*exp (-3*(z-(K+2))) := by
  have hi : (∫ t in (K+2)..z, connectorRate K t) = 3*(z-(K+2)) := by
    calc
      _ = ∫ _t in (K+2)..z, (3:ℝ) := intervalIntegral.integral_congr (by
        intro t ht
        apply connectorRate_right hK
        exact le_trans (le_min (by linarith) hz) ht.1)
      _ = _ := by simp; ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((connectorRate_smooth K).continuous.intervalIntegrable 0 (K+2))
    ((connectorRate_smooth K).continuous.intervalIntegrable (K+2) z)
  rw [hi] at hadd
  unfold connectorProfile
  rw [←hadd,neg_add,exp_add]
  congr 2
  ring

lemma cascadeProfile_zero_left {L K t : ℝ} (hL : 0 < L) (ht : t ≤ -7*L/2) :
    cascadeProfile L K t = 0 := by
  rw [cascadeProfile,crossingOn_eq_zero hL (show t/2+L ≤ -3*L/4 by linarith),zero_mul,zero_mul]
lemma cascadeProfile_zero_right {L K t : ℝ} (hL : 0 < L) (ht : K+2+7*L/4 ≤ t) :
    cascadeProfile L K t = 0 := by
  rw [cascadeProfile,crossingOff_eq_zero hL (show 3*L/4 ≤ t-(K+2+L) by linarith),mul_zero]

lemma cascadeProfile_connector {L K t : ℝ} (hL : 0 < L) (ht₁ : 0 ≤ t) (ht₂ : t ≤ K+2) :
    cascadeProfile L K t = connectorProfile K t := by
  rw [cascadeProfile,crossingOn_eq_one hL (show -L/2 ≤ t/2+L by linarith),
    crossingOff_eq_one hL (show t-(K+2+L) ≤ L/2 by linarith)]
  ring

lemma cascadeProfile_incoming {L K t : ℝ} (hL : 0 < L) (hK : 0 < K) (ht : t ≤ 0) :
    cascadeProfile L K t = crossingOn L (t/2+L)*exp (-t/2) := by
  rw [cascadeProfile,connectorProfile_left hK (show t≤1 by linarith),
    crossingOff_eq_one hL (show t-(K+2+L) ≤ L/2 by linarith),mul_one]

lemma cascadeProfile_outgoing {L K t : ℝ} (hL : 0 < L) (hK : 0 < K) (ht : K+2 ≤ t) :
    cascadeProfile L K t = connectorProfile K (K+2)*exp (-3*(t-(K+2))) *
      crossingOff L (t-(K+2+L)) := by
  rw [cascadeProfile,crossingOn_eq_one hL (show -L/2≤t/2+L by linarith),one_mul,
    connectorProfile_right hK (show K+1≤t by linarith)]

lemma cascadeRatio_pos (L K : ℝ) : 0 < cascadeRatio L K :=
  mul_pos (exp_pos _) (connectorProfile_pos _ _)

lemma cascade_length_positive {L K : ℝ} (hL : 0 < L) (hK : 0 < K) :
    0 < cascadeLength L K := by unfold cascadeLength; linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeGeometry
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma cascadePhase_zero (D k t : ℝ) : cascadePhase D k 0 t = k*t := by
  simp [cascadePhase]

lemma cascadePhase_succ (D k t : ℝ) (j : ℕ) :
    cascadePhase D k (j+1) t = 2*(cascadePhase D k j t-D) := by
  unfold cascadePhase
  rw [pow_succ]
  ring

lemma cascadePhase_antitone {D k t : ℝ} (ht : k*t ≤ 2*D) :
    Antitone (fun j => cascadePhase D k j t) := by
  apply antitone_nat_of_succ_le
  intro j
  have hp : 0 ≤ (2:ℝ)^j := by positivity
  rw [cascadePhase_succ]
  have : cascadePhase D k j t ≤ 2*D := by
    unfold cascadePhase
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hp (by linarith : k*t-2*D≤0)]
  linarith

lemma cascadePhase_before {D k t : ℝ} (hD : 0 < D) {i j : ℕ}
    (hij : i < j) (hj : 0 ≤ cascadePhase D k j t) :
    D ≤ cascadePhase D k i t := by
  by_cases ht : k*t ≤ 2*D
  · have h := cascadePhase_antitone ht (show i+1≤j by omega)
    dsimp only at h
    rw [cascadePhase_succ] at h
    linarith
  · have hp : 0 ≤ (2:ℝ)^i := by positivity
    have : 0 ≤ (2:ℝ)^i*(k*t-2*D) := mul_nonneg hp (by linarith)
    unfold cascadePhase
    linarith

lemma cascadePhase_after {D k t : ℝ} (hD : 0 < D) {i j : ℕ}
    (hij : j+1 < i) (hj : cascadePhase D k j t ≤ D) :
    cascadePhase D k i t ≤ -2*D := by
  have ht : k*t ≤ 2*D := by
    by_contra hh
    have hp : 0 < (2:ℝ)^j := by positivity
    have : 0 < (2:ℝ)^j*(k*t-2*D) := mul_pos hp (by linarith)
    unfold cascadePhase at hj
    linarith
  have h := cascadePhase_antitone ht (show j + 2 ≤ i by omega)
  dsimp only at h
  rw [show j+2=(j+1)+1 by omega,cascadePhase_succ,cascadePhase_succ] at h
  linarith

lemma cascadeProfile_only_two {L K k t : ℝ} (hL : 0 < L) (hK : 0 < K)
    {j i : ℕ} (hj₁ : 0 ≤ cascadePhase (cascadeLength L K) k j t)
    (hj₂ : cascadePhase (cascadeLength L K) k j t ≤ cascadeLength L K)
    (hi : i ≠ j) (hi' : i ≠ j+1) :
    cascadeProfile L K (cascadePhase (cascadeLength L K) k i t) = 0 := by
  have hD := cascade_length_positive hL hK
  by_cases hij : i < j
  · apply cascadeProfile_zero_right hL
    have hh := cascadePhase_before hD hij hj₁
    change K+2+2*L ≤ cascadePhase (cascadeLength L K) k i t at hh
    linarith
  · apply cascadeProfile_zero_left hL
    have hh := cascadePhase_after hD (show j+1 < i by omega) hj₂
    change cascadePhase (cascadeLength L K) k i t ≤ -2*(K+2+2*L) at hh
    linarith

lemma cascadeProfile_terminal {L K k t : ℝ} (hL : 0 < L) (hK : 0 < K)
    (ht : 2*cascadeLength L K ≤ k*t) (j : ℕ) :
    cascadeProfile L K (cascadePhase (cascadeLength L K) k j t) = 0 := by
  apply cascadeProfile_zero_right hL
  have hp : 0 ≤ (2:ℝ)^j*(k*t-2*cascadeLength L K) :=
    mul_nonneg (by positivity) (by linarith)
  unfold cascadePhase cascadeLength at *
  linarith

lemma cascadeAxis_ne_zero (j : ℕ) : cascadeAxis j ≠ 0 := by
  unfold cascadeAxis
  split <;> decide

lemma cascadeAxis_succ (j : ℕ) : cascadeAxis (j+1) = if Even j then 2 else 1 := by
  simp only [cascadeAxis,Nat.even_add_one]
  split <;> simp_all

lemma cascade_dilation_time {k : ℝ} (hk : k ≠ 0) (D : ℝ) (j : ℕ) (x : Coord3) :
    ((k*2^j) • (x-cascadeCenter D k j)) 0 = cascadePhase D k j (x 0) := by
  simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,cascadeCenter,Pi.single_eq_same,cascadePhase]
  field_simp
  ring

lemma cascadeValue_terminal {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (A : ℝ)
    (x : Coord3) (hx : 2*cascadeLength L K ≤ k*x 0) : cascadeValue L K k A x = 0 := by
  change (∑' j : ℕ, cascadeTerm L K k A j x) = 0
  have h : ∀ j, cascadeTerm L K k A j x = 0 := by
    intro j
    rw [cascadeTerm,cascadeProfile_terminal hL hK hx,mul_zero,zero_mul]
  simp only [h,tsum_zero]

lemma cascadeValue_two_modes {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (A : ℝ)
    (x : Coord3) (j : ℕ) (hj₁ : 0 ≤ cascadePhase (cascadeLength L K) k j (x 0))
    (hj₂ : cascadePhase (cascadeLength L K) k j (x 0) ≤ cascadeLength L K) :
    cascadeValue L K k A x = cascadeTerm L K k A j x + cascadeTerm L K k A (j+1) x := by
  have h : (∑' i : ℕ, cascadeTerm L K k A i x) = ∑ i ∈ ({j,j+1} : Finset ℕ), cascadeTerm L K k A i x := tsum_eq_sum (s := ({j,j+1} : Finset ℕ)) (f := fun i => cascadeTerm L K k A i x) (by
    intro i hi
    have hi₁ : i ≠ j := by simpa using fun h => hi (by simp [h])
    have hi₂ : i ≠ j+1 := by simpa using fun h => hi (by simp [h])
    rw [cascadeTerm,cascadeProfile_only_two hL hK hj₁ hj₂ hi₁ hi₂,mul_zero,zero_mul])
  simpa [cascadeValue,Finset.sum_pair (show j ≠ j+1 by omega)] using h

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeStreams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma crossingResidualFirst_smooth (L : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingResidualFirst L) :=
  (smooth_deriv_infty (smooth_deriv_infty (crossingFirst_smooth L))).sub
    (contDiff_const.mul (crossingFirst_smooth L))
lemma crossingResidualSecond_smooth (L : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingResidualSecond L) :=
  (smooth_deriv_infty (smooth_deriv_infty (crossingSecond_smooth L))).sub (crossingSecond_smooth L)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_C1WeakDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma direction_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (v : E) : Continuous (direction v f) := by
  have hd : ContDiff ℝ 0 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact hd.continuous.clm_apply continuous_const

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CrossingBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma crossing_first_on_left {L z : ℝ} (hL : 0 < L) (hz : z ≤ 0) :
    crossingFirst L z = exp (-3*z) := by
  rw [crossingFirst,crossingOff_eq_one hL (by linarith),one_mul]
lemma crossing_second_on_right {L z : ℝ} (hL : 0 < L) (hz : 0 ≤ z) :
    crossingSecond L z = exp (-z) := by
  rw [crossingSecond,crossingOn_eq_one hL (by linarith),one_mul]

lemma cascadeProfile_next_connector_zero {L K s : ℝ} (hL : 0 < L)
    (hs : s ≤ K+2) : cascadeProfile L K (2*(s-cascadeLength L K)) = 0 := by
  apply cascadeProfile_zero_left hL
  unfold cascadeLength
  linarith

lemma cascadeProfile_crossing_current {L K s : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hs : K+2 ≤ s) :
    cascadeProfile L K s = connectorProfile K (K+2)*exp (-3*L)*
      crossingFirst L (s-(K+2+L)) := by
  rw [cascadeProfile_outgoing hL hK hs,crossingFirst]
  have he : exp (-3*(s-(K+2))) = exp (-3*L)*exp (-3*(s-(K+2+L))) := by
    rw [←exp_add]
    congr 1
    ring
  rw [he]
  ring

lemma cascadeProfile_crossing_next {L K s : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hs : s ≤ cascadeLength L K) :
    cascadeRatio L K*cascadeProfile L K (2*(s-cascadeLength L K)) =
      connectorProfile K (K+2)*exp (-3*L)*crossingSecond L (s-(K+2+L)) := by
  rw [cascadeProfile_incoming hL hK (by linarith),cascadeRatio,crossingSecond]
  have ha : 2*(s-cascadeLength L K)/2+L = s-(K+2+L) := by
    unfold cascadeLength
    ring
  rw [ha]
  have he : exp (-4*L)*exp (-(2*(s-cascadeLength L K))/2) =
      exp (-3*L)*exp (-(s-(K+2+L))) := by
    rw [←exp_add,←exp_add]
    congr 1
    unfold cascadeLength
    ring
  calc
    _ = connectorProfile K (K+2)*crossingOn L (s-(K+2+L))*
        (exp (-4*L)*exp (-(2*(s-cascadeLength L K))/2)) := by ring
    _ = _ := by rw [he]; ring

lemma cascade_overlap_value {L K s : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hs₁ : K+2 ≤ s) (hs₂ : s ≤ cascadeLength L K) (a x y : ℝ) :
    a*cascadeProfile L K s*cos x +
      (a*cascadeRatio L K)*cascadeProfile L K (2*(s-cascadeLength L K))*cos (2*y) =
    (a*connectorProfile K (K+2)*exp (-3*L))*crossingValue L (s-(K+2+L)) x y := by
  rw [cascadeProfile_crossing_current hL hK hs₁]
  have hh := cascadeProfile_crossing_next hL hK hs₂
  dsimp only [crossingValue]
  calc
    _ = a*(connectorProfile K (K+2)*exp (-3*L)*crossingFirst L (s-(K+2+L)))*cos x +
      a*(cascadeRatio L K*cascadeProfile L K (2*(s-cascadeLength L K)))*cos (2*y) := by ring
    _ = _ := by rw [hh]; ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma cascadePhase_lt_terminal {D k t : ℝ} {j : ℕ}
    (hj : cascadePhase D k j t  <  2*D) : k*t  <  2*D := by
  have hp : 0  <  (2:ℝ)^j := by positivity
  unfold cascadePhase at hj
  nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_DirectionCalculus
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

section Direction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}

lemma direction_add {f g : E → ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (v : E) : direction v (fun y => f y+g y) x = direction v f x+direction v g x := by
  simp only [direction,fderiv_fun_add hf hg,add_apply]
lemma direction_mul {f g : E → ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (v : E) : direction v (fun y => f y*g y) x = f x*direction v g x+g x*direction v f x := by
  simp only [direction,fderiv_fun_mul hf hg,add_apply,
    smul_apply,smul_eq_mul]
lemma direction_comp_real {f : E → ℝ} {g : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) (v : E) :
    direction v (fun y => g (f y)) x = deriv g (f x)*direction v f x := by
  have hh := hg.hasDerivAt.comp_hasFDerivAt x hf.hasFDerivAt
  change (fderiv ℝ (g ∘ f) x) v = deriv g (f x)*direction v f x
  rw [hh.fderiv]
  simp only [smul_apply,smul_eq_mul]
  rfl
end Direction

lemma direction_scalar_coord {f : ℝ → ℝ} (hf : Differentiable ℝ f) (i j : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => f (y j)) x =
      deriv f (x j)*(if j=i then 1 else 0) := by
  rw [direction_comp_real (differentiableAt_pi.1 differentiableAt_id j) (hf _) _,
    direction_coord]

lemma direction_dilation {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    (s r : ℝ) (c v x : Coord3) :
    direction v (fun y => s*f (r • (y-c))) x = s*r*direction v f (r • (x-c)) := by
  have hl : HasFDerivAt (fun y : Coord3 => r • (y-c)) (r • ContinuousLinearMap.id ℝ Coord3) x :=
    ((hasFDerivAt_id x).sub_const c).const_smul r
  have hh : HasFDerivAt (fun y => s*f (r • (y-c)))
      (s • (fderiv ℝ f (r • (x-c))).comp (r • ContinuousLinearMap.id ℝ Coord3)) x :=
    ((hf _).hasFDerivAt.comp x hl).const_mul s
  change (fderiv ℝ (fun y => s*f (r • (y-c))) x) v = _
  rw [hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul,direction]
  ring

lemma direction_cos_coord (r : ℝ) (i j : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => cos (r*y j)) x =
      -r*sin (r*x j)*(if j=i then 1 else 0) := by
  have hh (t : ℝ) : HasDerivAt (fun t => cos (r*t)) (-r*sin (r*t)) t := by
    convert ((hasDerivAt_id t).const_mul r).cos using 1 <;> simp [mul_comm]
  rw [direction_scalar_coord (fun t => (hh t).differentiableAt), (hh _).deriv]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CascadeStageCurl
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma cascadeAxis_ne_succ (m : ℕ) : cascadeAxis m ≠ cascadeAxis (m+1) := by
  rw [cascadeAxis_succ]
  unfold cascadeAxis
  split <;> decide

lemma cascade_dilation_coord (D k : ℝ) (m : ℕ) (x : Coord3) {a : Fin 3} (ha : a≠0) :
    ((k*2^m) • (x-cascadeCenter D k m)) a = k*2^m*x a := by
  simp [cascadeCenter,Pi.single_eq_of_ne ha]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingGradient
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma direction_scalar_cos {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (r : ℝ) (i a : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y : Coord3 => f (y 0)*cos (r*y a)) x =
      f (x 0)*(-r*sin (r*x a)*(if a=i then 1 else 0)) +
      cos (r*x a)*(deriv f (x 0)*(if (0:Fin 3)=i then 1 else 0)) := by
  rw [direction_mul (by fun_prop) (by fun_prop),direction_cos_coord,direction_scalar_coord hf]

lemma crossingValue3_diff (L : ℝ) (a b : Fin 3) : Differentiable ℝ (crossingValue3 L a b) := by
  have hf := (crossingFirst_smooth L).differentiable (by simp)
  have hg := (crossingSecond_smooth L).differentiable (by simp)
  unfold crossingValue3 crossingValue
  fun_prop

lemma crossingValue3_direction (L : ℝ) (a b i : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (crossingValue3 L a b) x =
      (if i=0 then crossingCurrentZ L (x 0) (x a) (x b) else 0) +
      (if i=a then -crossingFirst L (x 0)*sin (x a) else 0) +
      (if i=b then -2*crossingSecond L (x 0)*sin (2*x b) else 0) := by
  have hf := (crossingFirst_smooth L).differentiable (by simp)
  have hg := (crossingSecond_smooth L).differentiable (by simp)
  have he : crossingValue3 L a b = fun x =>
      crossingFirst L (x 0)*cos (1*x a)+crossingSecond L (x 0)*cos (2*x b) := by
    funext x; simp [crossingValue3,crossingValue]
  rw [he,direction_add (by fun_prop) (by fun_prop),direction_scalar_cos hf,direction_scalar_cos hg]
  simp only [one_mul,crossingCurrentZ]
  simp_rw [@eq_comm _ a i, @eq_comm _ b i, @eq_comm _ (0 : Fin 3) i]
  split_ifs <;> ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PureMode
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma pureModeValue_diff {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a : Fin 3) :
    Differentiable ℝ (pureModeValue f a) := by
  unfold pureModeValue
  fun_prop

lemma pureModeValue_direction {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (a i : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (pureModeValue f a) x =
      (if i=0 then deriv f (x 0)*cos (x a) else 0) +
      (if i=a then -f (x 0)*sin (x a) else 0) := by
  have h := direction_scalar_cos hf 1 i a x
  simp only [one_mul] at h
  unfold pureModeValue
  rw [h]
  simp_rw [@eq_comm _ a i,@eq_comm _ (0:Fin 3) i]
  split_ifs <;> ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeCoefficient
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma cascadeIndex_spec {D k : ℝ} (x : Coord3) (ht₀ : 0≤k*x 0) (ht : k*x 0<2*D) :
    0 ≤ cascadePhase D k (cascadeIndex D k x) (x 0) ∧
      cascadePhase D k (cascadeIndex D k x) (x 0)≤D := by
  have hs := Nat.find_spec (exists_cascade_index D k (x 0))
  have hu : cascadePhase D k (cascadeIndex D k x) (x 0)≤D := hs.resolve_right (not_le.mpr ht)
  refine ⟨?_,hu⟩
  cases hn : cascadeIndex D k x with
  | zero => simpa [cascadePhase_zero] using ht₀
  | succ n =>
    have hmin := Nat.find_min (exists_cascade_index D k (x 0)) (show n < cascadeIndex D k x by omega)
    have hprev : D < cascadePhase D k n (x 0) := lt_of_not_ge (fun h => hmin (Or.inl h))
    rw [cascadePhase_succ]
    linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_LocalConstitution
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma direction_affineShift {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    (s r : ℝ) (c d v x : Coord3) :
    direction v (fun y => s*f (r • (y-c)-d)) x = s*r*direction v f (r • (x-c)-d) := by
  have hT : Differentiable ℝ (fun y : Coord3 => f (y-d)) := hf.comp (differentiable_id.sub_const d)
  rw [direction_dilation hT]
  have hh := direction_dilation hf 1 1 d v (r • (x-c))
  simpa only [one_mul,one_smul] using congrArg (fun z => s*r*z) hh

lemma cascadeValue_crossing {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : K+2 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K) :
    cascadeValue L K k A x =
      ((A*cascadeRatio L K^m)*(connectorProfile K (K+2)*exp (-3*L)))*
      crossingValue3 L (cascadeAxis m) (cascadeAxis (m+1))
        ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)-Pi.single 0 (K+2+L)) := by
  rw [cascadeValue_two_modes hL hK A x m (by linarith) hs₂.le]
  have h := cascade_overlap_value hL hK hs₁.le hs₂.le (A*cascadeRatio L K^m)
    (k*2^m*x (cascadeAxis m)) (k*2^m*x (cascadeAxis (m+1)))
  simp only [crossingValue3,Pi.sub_apply,Pi.single_eq_same,
    Pi.single_eq_of_ne (cascadeAxis_ne_zero m),Pi.single_eq_of_ne (cascadeAxis_ne_zero (m+1)),
    sub_zero,cascade_dilation_time hk,cascade_dilation_coord _ _ _ _ (cascadeAxis_ne_zero m),
    cascade_dilation_coord _ _ _ _ (cascadeAxis_ne_zero (m+1))]
  rw [cascadeTerm,cascadeTerm,cascadePhase_succ,pow_succ]
  convert h using 1 <;> ring_nf

lemma cascade_crossing_nhds {L K k : ℝ} (x : Coord3) (m : ℕ)
    (hs₁ : K+2 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K) :
    {y : Coord3 | K+2 < cascadePhase (cascadeLength L K) k m (y 0) ∧
      cascadePhase (cascadeLength L K) k m (y 0) < cascadeLength L K} ∈ 𝓝 x := by
  have hc : Continuous (fun y : Coord3 => cascadePhase (cascadeLength L K) k m (y 0)) := by
    unfold cascadePhase
    fun_prop
  exact (hc.isOpen_preimage _ isOpen_Ioo).mem_nhds ⟨hs₁,hs₂⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_CascadeConnectorConstitution
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma cascadeValue_connector {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (m : ℕ)
    (hs₁ : 0 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0)<K+2) :
    cascadeValue L K k A x =
      (A*cascadeRatio L K^m)*pureModeValue (connectorProfile K) (cascadeAxis m)
        ((k*2^m) • (x-cascadeCenter (cascadeLength L K) k m)) := by
  rw [cascadeValue_two_modes hL hK A x m hs₁.le (by have hD : cascadeLength L K = K+2+2*L := rfl; linarith)]
  simp only [cascadeTerm,cascadePhase_succ,cascadeProfile_next_connector_zero hL hs₂.le,
    mul_zero,zero_mul,add_zero,cascadeProfile_connector hL hs₁.le hs₂.le,pureModeValue,
    cascade_dilation_time hk,cascade_dilation_coord _ _ _ _ (cascadeAxis_ne_zero m)]
  ring

lemma cascade_connector_nhds {L K k : ℝ} (x : Coord3) (m : ℕ)
    (hs₁ : 0 < cascadePhase (cascadeLength L K) k m (x 0))
    (hs₂ : cascadePhase (cascadeLength L K) k m (x 0)<K+2) :
    {y : Coord3 | 0 < cascadePhase (cascadeLength L K) k m (y 0) ∧
      cascadePhase (cascadeLength L K) k m (y 0)<K+2} ∈ 𝓝 x := by
  have hc : Continuous (fun y : Coord3 => cascadePhase (cascadeLength L K) k m (y 0)) := by
    unfold cascadePhase
    fun_prop
  exact (hc.isOpen_preimage _ isOpen_Ioo).mem_nhds ⟨hs₁,hs₂⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_CascadeConstitution
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma ae_coord3_ne (i : Fin 3) (r : ℝ) : ∀ᵐ x : Coord3, x i≠r := by
  exact MeasureTheory.Measure.ae_eval_ne (fun _ : Fin 3 => (volume : Measure ℝ)) i r

lemma ae_cascadePhase_ne {k : ℝ} (hk : k≠0) (D r : ℝ) (n : ℕ) :
    ∀ᵐ x : Coord3, cascadePhase D k n (x 0)≠r := by
  filter_upwards [ae_coord3_ne 0 ((r-2*D+2^n*(2*D))/(2^n*k))] with x hx
  intro he
  apply hx
  apply (eq_div_iff (mul_ne_zero (by positivity) hk)).mpr
  unfold cascadePhase at he
  nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_Ending
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Real Set Filter Topology MeasureTheory Matrix

lemma initialConnectorRate_smooth (a b K : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (initialConnectorRate a b K) := by
  exact contDiff_const.add (contDiff_const.mul (smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const K)))

lemma initialConnectorRate_left {a b K t : ℝ} (hK : 0 < K) (ht : t ≤ 1) :
    initialConnectorRate a b K t=a := by
  rw [initialConnectorRate,smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hK.le),mul_zero,add_zero]

lemma initialConnectorProfile_smooth (a b K : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (initialConnectorProfile a b K) := by
  let r : SmoothScalar ℝ := ⟨initialConnectorRate a b K,initialConnectorRate_smooth a b K⟩
  exact ((smoothScalar_contDiff (smoothPrimitive r)).neg).exp

lemma initialConnectorProfile_pos (a b K t : ℝ) : 0 < initialConnectorProfile a b K t := exp_pos _

lemma initialConnectorAngular_smooth (a b K : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (initialConnectorAngular a b K) :=
  ((initialConnectorRate_smooth a b K).pow 2).sub
    (smooth_deriv_infty (initialConnectorRate_smooth a b K))

lemma initialConnectorProfile_left {a b K t : ℝ} (hK : 0 < K) (ht : t ≤ 1) :
    initialConnectorProfile a b K t=exp (-a*t) := by
  have hi : (∫ r in (0:ℝ)..t,initialConnectorRate a b K r)=a*t := by
    calc
      _=∫ _r in (0:ℝ)..t,a := intervalIntegral.integral_congr (by
        intro r hr
        apply initialConnectorRate_left hK
        exact (le_max_iff.mp hr.2).elim (by intro h; linarith) (by intro h; linarith))
      _=_ := by simp; ring
  rw [initialConnectorProfile,hi]
  congr 1
  ring

end

section
open Set Filter Topology

lemma axial_paste_eventually_left {E F : Type*} [TopologicalSpace E]
    {f g : E → F} {t : E → ℝ} {c : ℝ} (ht : Continuous t) {x : E} (hx : t x < c) :
    (fun y => if t y < c then f y else g y)=ᶠ[𝓝 x] f := by
  filter_upwards [(isOpen_lt ht continuous_const).mem_nhds hx] with y hy
  exact ite_eq_left hy

lemma axial_paste_eventually_right {E F : Type*} [TopologicalSpace E]
    {f g : E → F} {t : E → ℝ} {c : ℝ} (ht : Continuous t) {x : E} (hx : c<t x) :
    (fun y => if t y < c then f y else g y)=ᶠ[𝓝 x] g := by
  filter_upwards [(isOpen_lt continuous_const ht).mem_nhds hx] with y hy
  exact ite_eq_right (not_lt.mpr hy.le)

end

section
open Real Set Filter Topology MeasureTheory Matrix

lemma finiteEndingValue_initial {a J L K : ℝ} (hJ : 0 < J) (x : Coord3) (hx : x 0 ≤ 1) :
    finiteEndingValue a J L K x=exp (-a*x 0)*cos (x 1) := by
  rw [finiteEndingValue,ite_eq_left (show x 0<J+2 by linarith),pureModeValue,
    initialConnectorProfile_left hJ hx]

end

open Real Set Filter Topology MeasureTheory Matrix

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_EndingCoordinateTransport
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma permutedDilation_quasiMeasurePreserving (e : Equiv.Perm (Fin 3)) {r : ℝ} (hr : r≠0) :
    Measure.QuasiMeasurePreserving (permutedDilation e r) volume volume := by
  have hp := (volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) e.symm).quasiMeasurePreserving
  have hs := Measure.quasiMeasurePreserving_smul (volume : Measure Coord3) hr
  convert hs.comp hp using 1
  all_goals try with_reducible_and_instances rfl
  funext x i
  simp [permutedDilation,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]

end ScalarConductivity



namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma angularAxisSwap_apply (i : Fin 3) : angularAxisSwap i=![0,2,1] i := by
  fin_cases i <;> decide

lemma alignedEnding_initial {lam k J L K : ℝ} (hk : 0<k) (hJ : 0<J) (x : Coord3) (ht : k*x 0≤1) :
    alignedEndingValue lam k J L K x=exp (-lam*x 0)*cos (k*x 2) := by
  have h0 : permutedDilation angularAxisSwap k x 0=k*x 0 := by simp [permutedDilation,angularAxisSwap_apply]
  have h1 : permutedDilation angularAxisSwap k x 1=k*x 2 := by simp [permutedDilation,angularAxisSwap_apply]
  rw [alignedEndingValue,finiteEndingValue_initial hJ _ (by simpa only [h0] using ht),h0,h1]
  congr 2
  field_simp

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_CascadeTensorLocality
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma cascadeIndex_eq_of_strict_phase {D k : ℝ} (hD : 0<D) (x : Coord3) (j : ℕ)
    (hj0 : 0 < cascadePhase D k j (x 0)) (hjD : cascadePhase D k j (x 0)<D) :
    cascadeIndex D k x=j := by
  have ht : k*x 0<2*D := cascadePhase_lt_terminal (by linarith : cascadePhase _ k j (x 0)<2*_)
  have ht0 : 0≤k*x 0 := by
    have hh := cascadePhase_antitone ht.le (Nat.zero_le j)
    dsimp only at hh
    rw [cascadePhase_zero] at hh
    exact le_trans hj0.le hh
  have hs := cascadeIndex_spec x ht0 ht
  rcases lt_trichotomy (cascadeIndex D k x) j with hij|he|hji
  · have hh := cascadePhase_antitone ht.le (show cascadeIndex D k x+1≤j by omega)
    dsimp only at hh
    rw [cascadePhase_succ] at hh
    linarith
  · exact he
  · have hh := cascadePhase_before hD hji hs.1
    linarith

lemma cascadeTensor_connector_eq {L K k : ℝ} (hL : 0<L) (hK : 0<K)
    (x : Coord3) (j : ℕ)
    (hj0 : 0 < cascadePhase (cascadeLength L K) k j (x 0))
    (hjK : cascadePhase (cascadeLength L K) k j (x 0)<K+2) :
    cascadeTensor L K k x =
      pureModeTensor (connectorAngular K (cascadePhase (cascadeLength L K) k j (x 0))) (cascadeAxis j) := by
  have hD : 0 < cascadeLength L K := by unfold cascadeLength; positivity
  have hjD : cascadePhase (cascadeLength L K) k j (x 0) < cascadeLength L K := by
    have he : cascadeLength L K=K+2+2*L := rfl
    linarith
  have ht := cascadePhase_lt_terminal (by linarith : cascadePhase _ k j (x 0)<2*_)
  have ht0 : 0≤k*x 0 := by
    have hh := cascadePhase_antitone ht.le (Nat.zero_le j)
    dsimp only at hh
    rw [cascadePhase_zero] at hh
    exact le_trans hj0.le hh
  rw [cascadeTensor,ite_eq_left ⟨ht0,ht⟩,cascadeIndex_eq_of_strict_phase hD x j hj0 hjD,
    cascadeStageTensor,ite_eq_left hjK]

lemma cascadeTensor_crossing_eq {L K k : ℝ} (hL : 0<L) (hK : 0<K)
    (x : Coord3) (j : ℕ)
    (hjK : K+2 < cascadePhase (cascadeLength L K) k j (x 0))
    (hjD : cascadePhase (cascadeLength L K) k j (x 0) < cascadeLength L K) :
    cascadeTensor L K k x = crossingTensor L (cascadeAxis j) (cascadeAxis (j+1))
      ((k*2^j) • (x-cascadeCenter (cascadeLength L K) k j)-Pi.single 0 (K+2+L)) := by
  have hD : 0 < cascadeLength L K := by unfold cascadeLength; positivity
  have hj0 : 0 < cascadePhase (cascadeLength L K) k j (x 0) := by linarith
  have ht := cascadePhase_lt_terminal (by linarith : cascadePhase _ k j (x 0)<2*_)
  have ht0 : 0≤k*x 0 := by
    have hh := cascadePhase_antitone ht.le (Nat.zero_le j)
    dsimp only at hh
    rw [cascadePhase_zero] at hh
    exact le_trans hj0.le hh
  rw [cascadeTensor,ite_eq_left ⟨ht0,ht⟩,cascadeIndex_eq_of_strict_phase hD x j hj0 hjD,
    cascadeStageTensor,ite_eq_right (not_lt.mpr hjK.le)]

lemma connectorAngular_smooth (K : ℝ) : ContDiff ℝ (↑(⊤:ℕ∞)) (connectorAngular K) := by
  unfold connectorAngular
  exact (smooth_deriv_infty (smooth_deriv_infty (connectorProfile_smooth K))).div
    (connectorProfile_smooth K) (fun x => (connectorProfile_pos K x).ne')

lemma crossingValue3_smooth (L : ℝ) (a b : Fin 3) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (crossingValue3 L a b) := by
  have hf := crossingFirst_smooth L
  have hg := crossingSecond_smooth L
  unfold crossingValue3 crossingValue
  fun_prop

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompactDepthReductionTwo
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma TwoFieldRankRegular.mono {u : Coord3 → Fin 2 → ℝ} {O W : Set Coord3}
    (h : TwoFieldRankRegular u O) (hW : W ⊆ O) : TwoFieldRankRegular u W := by
  rcases h with h | h | ⟨κ, hκ⟩
  · exact Or.inl (fun x hx => h x (hW hx))
  · obtain ⟨v, l, κ, hv, hl, hd, he⟩ := h
    exact Or.inr (Or.inl ⟨v, l, κ, hv.mono hW, hl, fun x hx => hd x (hW hx),
      fun x hx => he x (hW hx)⟩)
  · exact Or.inr (Or.inr ⟨κ, fun x hx => hκ x (hW hx)⟩)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularPatch
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma TwoFieldRankRegular.congr {u v : Coord3 → Fin 2 → ℝ} {O : Set Coord3}
    (hO : IsOpen O) (h : TwoFieldRankRegular u O) (he : EqOn v u O) :
    TwoFieldRankRegular v O := by
  rcases h with h | h | ⟨κ,hκ⟩
  · left
    intro x hx
    rw [fderiv_eq_of_eqOn_open hO he hx]
    exact h x hx
  · right; left
    obtain ⟨w,l,κ,hw,hl,hwd,hrel⟩ := h
    exact ⟨w,l,κ,hw,hl,hwd,fun x hx j => by rw [he hx]; exact hrel x hx j⟩
  · exact Or.inr (Or.inr ⟨κ,fun x hx => (he hx).trans (hκ x hx)⟩)

lemma RegularPatch.mono {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {O W : Set Coord3} (h : RegularPatch u A O) (hW : IsOpen W) (hWO : W ⊆ O) :
    RegularPatch u A W :=
  ⟨hW,h.2.1.mono hWO,h.2.2.1.mono hWO,h.2.2.2.mono hWO⟩

lemma RegularPatch.congr {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    {O : Set Coord3} (h : RegularPatch u A O) (hu : EqOn v u O) (hA : EqOn B A O) :
    RegularPatch v B O := by
  exact ⟨h.1,h.2.1.congr hu,h.2.2.1.congr (fun x hx => congrArg Subtype.val (hA hx)),
    h.2.2.2.congr h.1 hu⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_AxialPairRank
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma axialPair_smooth {f : Coord3 → ℝ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (axialPair f) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ 0
  · exact hf

lemma axialPair_gradient_zero {f : Coord3 → ℝ} {x : Coord3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    (gradientColumns (fderiv ℝ (axialPair f) x)).col 0 i=if (0:Fin 3)=i then 1 else 0 := by
  have hd (j : Fin 2) : DifferentiableAt ℝ (fun x => axialPair f x j) x := by
    fin_cases j
    · exact (differentiable_apply 0).differentiableAt
    · exact hf
  simp only [gradientColumns,Matrix.col,transpose_apply,LinearMap.toMatrix'_apply,
    ContinuousLinearMap.coe_coe,fderiv_pi hd,ContinuousLinearMap.pi_apply]
  exact direction_coord i 0 x

lemma axialPair_gradient_one {f : Coord3 → ℝ} {x : Coord3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    (gradientColumns (fderiv ℝ (axialPair f) x)).col 1 i=direction (Pi.single i 1) f x := by
  have hd (j : Fin 2) : DifferentiableAt ℝ (fun x => axialPair f x j) x := by
    fin_cases j
    · exact (differentiable_apply 0).differentiableAt
    · exact hf
  simp only [gradientColumns,Matrix.col,transpose_apply,LinearMap.toMatrix'_apply,
    ContinuousLinearMap.coe_coe,fderiv_pi hd,ContinuousLinearMap.pi_apply]
  rfl

lemma axialPair_gradient_independent {f : Coord3 → ℝ} {x : Coord3}
    (hf : DifferentiableAt ℝ f x) {i : Fin 3} (hi : i≠0)
    (hfi : direction (Pi.single i 1) f x≠0) :
    LinearIndependent ℝ (gradientColumns (fderiv ℝ (axialPair f) x)).col := by
  apply linearIndependent_fin2.mpr
  constructor
  · intro hz
    apply hfi
    have hh := congrFun hz i
    simpa only [axialPair_gradient_one hf,Pi.zero_apply] using hh
  · intro a he
    have hh := congrFun he i
    simp only [Pi.smul_apply,smul_eq_mul,axialPair_gradient_one hf,
      axialPair_gradient_zero hf,Ne.symm hi,ite_false] at hh
    have ha : a=0 := (mul_eq_zero.mp hh).resolve_right hfi
    have hh0 := congrFun he 0
    simp only [ha,Pi.smul_apply,zero_smul,axialPair_gradient_zero hf,
      ite_true] at hh0
    norm_num at hh0

lemma ae_sin_coord_ne_zero {r : ℝ} (hr : r≠0) (i : Fin 3) :
    ∀ᵐ x : Coord3,sin (r*x i)≠0 := by
  have h := ae_all_iff.mpr (fun n : ℤ => ae_coord3_ne i ((n:ℝ)*Real.pi/r))
  filter_upwards [h] with x hx
  intro hz
  obtain ⟨n,hn⟩ := sin_eq_zero_iff.mp hz
  exact hx n ((eq_div_iff hr).mpr (by linarith))

lemma axialPair_regularPatch {f : Coord3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f)
    {A : Coord3 → Symmetric3} (hA : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => (A x).val))
    {i : Fin 3} (hi : i≠0) {O : Set Coord3} (hO : IsOpen O)
    (hn : ∀ x∈O,direction (Pi.single i 1) f x≠0) :
    RegularPatch (axialPair f) A O := by
  exact ⟨hO,(axialPair_smooth hf).contDiffOn,hA.contDiffOn,
    Or.inl (fun x hx => axialPair_gradient_independent (hf.differentiable (by simp) x) hi (hn x hx))⟩

lemma axialPair_zero_rank (O : Set Coord3) : TwoFieldRankRegular (axialPair (fun _ => 0)) O := by
  refine Or.inr (Or.inl ⟨fun x : Coord3 => x 0,![1,0],0,(contDiff_apply ℝ ℝ (0:Fin 3)).contDiffOn,
    ⟨0,by norm_num⟩,?_,?_⟩)
  · intro x _ he
    have hh := congrArg (fun D : Coord3 →L[ℝ] ℝ => D (Pi.single 0 1)) he
    have hd := direction_coord 0 0 x
    change fderiv ℝ (fun y : Coord3 => y 0) x (Pi.single 0 1)=1 at hd
    simp only [he,_root_.zero_apply] at hd
    norm_num at hd
  · intro x _ j
    fin_cases j <;> simp [axialPair]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_AxialLocalRegularity
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma axialPair_mem_regularRegion_of_model
    {f F : Coord3 → ℝ} {A B : Coord3 → Symmetric3} {x : Coord3}
    (hF : ContDiff ℝ (↑(⊤:ℕ∞)) F)
    (hB : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => (B y).val))
    (hf : f =ᶠ[𝓝 x] F) (hA : A =ᶠ[𝓝 x] B)
    {i : Fin 3} (hi : i≠0) (hd : direction (Pi.single i 1) F x≠0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair f) A U := by
  have hc : Continuous (direction (Pi.single i 1) F) :=
    direction_continuous (hF.of_le (by simp)) _
  have hn : ∀ᶠ y in 𝓝 x,direction (Pi.single i 1) F y≠0 :=
    (isOpen_ne_fun hc continuous_const).mem_nhds hd
  have hh : {y | y∈U ∧ f y=F y ∧ A y=B y ∧ direction (Pi.single i 1) F y≠0}∈𝓝 x := by
    filter_upwards [hU.mem_nhds hx,hf,hA,hn] with y hy hfy hAy hny
    exact ⟨hy,hfy,hAy,hny⟩
  obtain ⟨O,hOsub,hO,hxO⟩ := mem_nhds_iff.mp hh
  refine mem_regularRegion_iff.mpr ⟨O,fun y hy => (hOsub hy).1,?_,hxO⟩
  apply (axialPair_regularPatch hF hB hi hO (fun y hy => (hOsub hy).2.2.2)).congr
  · intro y hy
    simp only [axialPair,(hOsub hy).2.1]
  · intro y hy
    exact (hOsub hy).2.2.1

lemma axialPair_mem_regularRegion_of_zero
    {f : Coord3 → ℝ} {A B : Coord3 → Symmetric3} {x : Coord3}
    (hB : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => (B y).val))
    (hf : f =ᶠ[𝓝 x] fun _ => 0) (hA : A =ᶠ[𝓝 x] B)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair f) A U := by
  have hh : {y | y∈U ∧ f y=0 ∧ A y=B y}∈𝓝 x := by
    filter_upwards [hU.mem_nhds hx,hf,hA] with y hy hfy hAy
    exact ⟨hy,hfy,hAy⟩
  obtain ⟨O,hOsub,hO,hxO⟩ := mem_nhds_iff.mp hh
  have hp : RegularPatch (axialPair (fun _ => 0)) B O :=
    ⟨hO,(axialPair_smooth contDiff_const).contDiffOn,hB.contDiffOn,axialPair_zero_rank O⟩
  refine mem_regularRegion_iff.mpr ⟨O,fun y hy => (hOsub hy).1,?_,hxO⟩
  apply hp.congr
  · intro y hy
    simp only [axialPair,(hOsub hy).2.1]
  · intro y hy
    exact (hOsub hy).2.2

lemma pureModeValue_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (a : Fin 3) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (pureModeValue f a) := by
  unfold pureModeValue
  fun_prop

lemma pureModeTensor_smooth {f : Coord3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (a : Fin 3) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => pureModeTensor (f x) a) := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  simp only [pureModeTensor,Matrix.diagonal_apply]
  split_ifs <;> first | exact hf | exact contDiff_const

lemma crossingTensor_smooth (L : ℝ) (a b : Fin 3) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (crossingTensor L a b) := by
  have hf := crossingResidualFirst_smooth L
  have hg := crossingResidualSecond_smooth L
  have hff := crossingFirst_smooth L
  have hgg := crossingSecond_smooth L
  have hxx : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => crossingXX L (x 0) (x a) (x b)) := by
    unfold crossingXX crossingHxx
    fun_prop (disch := intro x; positivity)
  have hyy : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => crossingYY L (x 0) (x a) (x b)) := by
    unfold crossingYY crossingHxx
    fun_prop (disch := intro x; positivity)
  have hxy : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => crossingXY L (x 0) (x a) (x b)) := by
    unfold crossingXY crossingHxy
    fun_prop (disch := intro x; positivity)
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  unfold crossingTensor
  split_ifs <;> fun_prop

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CascadeRankPieces
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma cascade_connector_regular {L K k A : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0) (hA : A≠0)
    (x : Coord3) (j : ℕ)
    (hj0 : 0 < cascadePhase (cascadeLength L K) k j (x 0))
    (hjK : cascadePhase (cascadeLength L K) k j (x 0)<K+2)
    (hsin : sin ((k*2^j)*x (cascadeAxis j))≠0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair (cascadeValue L K k A)) (cascadeSymmetricTensor L K k) U := by
  let s := A*cascadeRatio L K^j
  let r := k*2^j
  let c := cascadeCenter (cascadeLength L K) k j
  let F : Coord3 → ℝ := fun y => s*pureModeValue (connectorProfile K) (cascadeAxis j) (r • (y-c)-0)
  let B : Coord3 → Symmetric3 := fun y =>
    ⟨pureModeTensor (connectorAngular K (cascadePhase (cascadeLength L K) k j (y 0))) (cascadeAxis j),
      pureModeTensor_symm _ _⟩
  have hp := pureModeValue_smooth (connectorProfile_smooth K) (cascadeAxis j)
  have hF : ContDiff ℝ (↑(⊤:ℕ∞)) F := by
    dsimp only [F]
    exact contDiff_const.mul (hp.comp ((contDiff_id.sub contDiff_const).const_smul r |>.sub contDiff_const))
  have hB : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => (B y).val) := by
    apply pureModeTensor_smooth
    exact (connectorAngular_smooth K).comp (by unfold cascadePhase; fun_prop)
  apply axialPair_mem_regularRegion_of_model hF hB (i:=cascadeAxis j) ?_ ?_ (cascadeAxis_ne_zero j) ?_ hU hx
  · filter_upwards [cascade_connector_nhds x j hj0 hjK] with y hy
    simpa only [F,s,r,c,sub_zero] using cascadeValue_connector hL hK hk A y j hy.1 hy.2
  · filter_upwards [cascade_connector_nhds x j hj0 hjK] with y hy
    apply Subtype.ext
    exact cascadeTensor_connector_eq hL hK y j hy.1 hy.2
  · change direction (Pi.single (cascadeAxis j) 1)
      (fun y => s*pureModeValue (connectorProfile K) (cascadeAxis j) (r • (y-c)-0)) x≠0
    rw [direction_affineShift (pureModeValue_diff ((connectorProfile_smooth K).differentiable (by simp)) _)]
    rw [pureModeValue_direction ((connectorProfile_smooth K).differentiable (by simp))]
    simp only [cascadeAxis_ne_zero,ite_false,ite_true,zero_add,sub_zero]
    apply mul_ne_zero (mul_ne_zero ?_ ?_)
    · exact mul_ne_zero (neg_ne_zero.mpr (connectorProfile_pos K _).ne') (by
        simpa only [r,c,cascade_dilation_coord _ _ _ _ (cascadeAxis_ne_zero j)] using hsin)
    · exact mul_ne_zero hA (pow_ne_zero j (cascadeRatio_pos L K).ne')
    · exact mul_ne_zero hk (pow_ne_zero j (by norm_num : (2:ℝ)≠0))

lemma cascade_crossing_regular {L K k A : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0) (hA : A≠0)
    (x : Coord3) (j : ℕ)
    (hjK : K+2 < cascadePhase (cascadeLength L K) k j (x 0))
    (hjD : cascadePhase (cascadeLength L K) k j (x 0) < cascadeLength L K)
    (hsin : sin ((k*2^j)*x (cascadeAxis j))≠0)
    (hsin2 : sin ((k*2^(j+1))*x (cascadeAxis (j+1)))≠0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair (cascadeValue L K k A)) (cascadeSymmetricTensor L K k) U := by
  let s := (A*cascadeRatio L K^j)*(connectorProfile K (K+2)*exp (-3*L))
  let r := k*2^j
  let c := cascadeCenter (cascadeLength L K) k j
  let d : Coord3 := Pi.single 0 (K+2+L)
  let F : Coord3 → ℝ := fun y => s*crossingValue3 L (cascadeAxis j) (cascadeAxis (j+1)) (r • (y-c)-d)
  let B : Coord3 → Symmetric3 := fun y =>
    ⟨crossingTensor L (cascadeAxis j) (cascadeAxis (j+1)) (r • (y-c)-d),crossingTensor_symm _ _ _ _⟩
  have hF : ContDiff ℝ (↑(⊤:ℕ∞)) F := by
    dsimp only [F]
    exact contDiff_const.mul ((crossingValue3_smooth L _ _).comp
      ((contDiff_id.sub contDiff_const).const_smul r |>.sub contDiff_const))
  have hB : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => (B y).val) :=
    (crossingTensor_smooth L _ _).comp ((contDiff_id.sub contDiff_const).const_smul r |>.sub contDiff_const)
  have hf : cascadeValue L K k A =ᶠ[𝓝 x] F := by
    filter_upwards [cascade_crossing_nhds x j hjK hjD] with y hy
    exact cascadeValue_crossing hL hK hk A y j hy.1 hy.2
  have htensor : cascadeSymmetricTensor L K k =ᶠ[𝓝 x] B := by
    filter_upwards [cascade_crossing_nhds x j hjK hjD] with y hy
    apply Subtype.ext
    exact cascadeTensor_crossing_eq hL hK y j hy.1 hy.2
  have hs : s≠0 := mul_ne_zero (mul_ne_zero hA (pow_ne_zero j (cascadeRatio_pos L K).ne'))
    (mul_ne_zero (connectorProfile_pos K _).ne' (exp_pos _).ne')
  have hr : r≠0 := mul_ne_zero hk (pow_ne_zero j (by norm_num : (2:ℝ)≠0))
  have ha := cascadeAxis_ne_zero j
  have hb := cascadeAxis_ne_zero (j+1)
  have hab := cascadeAxis_ne_succ j
  by_cases hz : (r • (x-c)-d) 0≤0
  · apply axialPair_mem_regularRegion_of_model hF hB hf htensor ha ?_ hU hx
    change direction (Pi.single (cascadeAxis j) 1)
      (fun y => s*crossingValue3 L (cascadeAxis j) (cascadeAxis (j+1)) (r • (y-c)-d)) x≠0
    rw [direction_affineShift (crossingValue3_diff L _ _),crossingValue3_direction]
    simp only [ha,hab,ite_false,ite_true,zero_add,add_zero,crossing_first_on_left hL hz]
    apply mul_ne_zero (mul_ne_zero hs hr)
    apply mul_ne_zero (neg_ne_zero.mpr (exp_pos _).ne')
    simpa only [r,c,d,Pi.sub_apply,Pi.single_eq_of_ne ha,sub_zero,
      cascade_dilation_coord _ _ _ _ ha] using hsin
  · apply axialPair_mem_regularRegion_of_model hF hB hf htensor hb ?_ hU hx
    change direction (Pi.single (cascadeAxis (j+1)) 1)
      (fun y => s*crossingValue3 L (cascadeAxis j) (cascadeAxis (j+1)) (r • (y-c)-d)) x≠0
    rw [direction_affineShift (crossingValue3_diff L _ _),crossingValue3_direction]
    simp only [hb,Ne.symm hab,ite_false,ite_true,zero_add,add_zero,
      crossing_second_on_right hL (le_of_not_ge hz)]
    apply mul_ne_zero (mul_ne_zero hs hr)
    apply mul_ne_zero (mul_ne_zero (by norm_num) (exp_pos _).ne')
    have he : 2*(r • (x-c)-d) (cascadeAxis (j+1))=
        (k*2^(j+1))*x (cascadeAxis (j+1)) := by
      simp only [r,c,d,Pi.sub_apply,Pi.single_eq_of_ne hb,sub_zero,
        cascade_dilation_coord _ _ _ _ hb,pow_succ]
      ring
    rw [he]
    exact hsin2

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma cascade_terminal_regular {L K k A : ℝ} (hL : 0<L) (hK : 0<K)
    (x : Coord3) (ht : 2*cascadeLength L K<k*x 0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair (cascadeValue L K k A)) (cascadeSymmetricTensor L K k) U := by
  let B : Coord3 → Symmetric3 := fun _ => ⟨1,isSymm_one⟩
  have hn : {y : Coord3 | 2*cascadeLength L K<k*y 0}∈𝓝 x :=
    (isOpen_lt continuous_const (continuous_const.mul (continuous_apply 0))).mem_nhds ht
  apply axialPair_mem_regularRegion_of_zero (B:=B) contDiff_const ?_ ?_ hU hx
  · filter_upwards [hn] with y hy
    exact cascadeValue_terminal hL hK A y hy.le
  · filter_upwards [hn] with y hy
    apply Subtype.ext
    exact ite_eq_right (by intro hh; linarith [hh.2])

theorem cascade_regularRegion_ae {L K k A : ℝ} (hL : 0<L) (hK : 0<K)
    (hk : k≠0) (hA : A≠0) {U : Set Coord3} (hU : IsOpen U) :
    ∀ᵐ x : Coord3,x∈U → 0≤k*x 0 →
      x∈regularRegion (axialPair (cascadeValue L K k A)) (cascadeSymmetricTensor L K k) U := by
  have h0 : ∀ᵐ x : Coord3, ∀ n : ℕ, cascadePhase (cascadeLength L K) k n (x 0)≠0 :=
    ae_all_iff.mpr (fun n => ae_cascadePhase_ne hk _ _ n)
  have hD : ∀ᵐ x : Coord3, ∀ n : ℕ, cascadePhase (cascadeLength L K) k n (x 0)≠cascadeLength L K :=
    ae_all_iff.mpr (fun n => ae_cascadePhase_ne hk _ _ n)
  have hK2 : ∀ᵐ x : Coord3, ∀ n : ℕ, cascadePhase (cascadeLength L K) k n (x 0)≠K+2 :=
    ae_all_iff.mpr (fun n => ae_cascadePhase_ne hk _ _ n)
  have ht : ∀ᵐ x : Coord3, k*x 0≠2*cascadeLength L K := by
    simpa only [cascadePhase_zero] using ae_cascadePhase_ne hk (cascadeLength L K) (2*cascadeLength L K) 0
  have hsin : ∀ᵐ x : Coord3,∀ n : ℕ,sin ((k*2^n)*x (cascadeAxis n))≠0 :=
    ae_all_iff.mpr (fun n => ae_sin_coord_ne_zero (mul_ne_zero hk (pow_ne_zero n (by norm_num))) _)
  filter_upwards [h0,hD,hK2,ht,hsin] with x hx0 hxD hxK hxt hxs
  intro hxU hx
  by_cases hterm : k*x 0<2*cascadeLength L K
  · have hs := cascadeIndex_spec x hx hterm
    have hs₁ := lt_of_le_of_ne hs.1 (Ne.symm (hx0 _))
    have hs₂ := lt_of_le_of_ne hs.2 (hxD _)
    by_cases hc : cascadePhase (cascadeLength L K) k (cascadeIndex (cascadeLength L K) k x) (x 0)<K+2
    · exact cascade_connector_regular hL hK hk hA x _ hs₁ hc (hxs _) hU hxU
    · exact cascade_crossing_regular hL hK hk hA x _
        (lt_of_le_of_ne (le_of_not_gt hc) (Ne.symm (hxK _))) hs₂ (hxs _) (hxs _) hU hxU
  · exact cascade_terminal_regular hL hK x
      (lt_of_le_of_ne (le_of_not_gt hterm) (Ne.symm hxt)) hU hxU

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_RegularPatchTranslation
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma mem_regularRegion_congr_nhds {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3}
    {V U : Set Coord3} {x : Coord3} (h : x∈regularRegion u A V)
    (hu : v =ᶠ[𝓝 x] u) (hA : B =ᶠ[𝓝 x] A) (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion v B U := by
  obtain ⟨O,hOV,hO,hxO⟩ := mem_regularRegion_iff.mp h
  have hh : {y | y∈O ∧ y∈U ∧ v y=u y ∧ B y=A y}∈𝓝 x := by
    filter_upwards [hO.1.mem_nhds hxO,hU.mem_nhds hx,hu,hA] with y hy0 hyU hyu hyA
    exact ⟨hy0,hyU,hyu,hyA⟩
  obtain ⟨W,hWsub,hW,hxW⟩ := mem_nhds_iff.mp hh
  refine mem_regularRegion_iff.mpr ⟨W,fun y hy => (hWsub hy).2.1,?_,hxW⟩
  exact (hO.mono hW (fun y hy => (hWsub hy).1)).congr
    (fun y hy => (hWsub hy).2.2.1) (fun y hy => (hWsub hy).2.2.2)

lemma axialPair_translate (f : Coord3 → ℝ) (c x : Coord3) :
    axialPair f (x-c)+![c 0,0]=axialPair (fun y => f (y-c)) x := by
  ext i
  fin_cases i <;> simp [axialPair]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_FiniteEndingRegularity
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma finiteEnding_initial_regular (a J L K : ℝ) (x : Coord3)
    (ht : x 0<J+2) (hsin : sin (x 1)≠0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair (finiteEndingValue a J L K)) (finiteEndingSymmetricTensor a J L K) U := by
  let F := pureModeValue (initialConnectorProfile a (1/2) J) 1
  let B : Coord3 → Symmetric3 := fun y =>
    ⟨pureModeTensor (initialConnectorAngular a (1/2) J (y 0)) 1,pureModeTensor_symm _ _⟩
  have hF := pureModeValue_smooth (initialConnectorProfile_smooth a (1/2) J) (1:Fin 3)
  have hB : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => (B y).val) := by
    apply pureModeTensor_smooth
    exact (initialConnectorAngular_smooth a (1/2) J).comp (contDiff_apply ℝ ℝ 0)
  apply axialPair_mem_regularRegion_of_model hF hB (i:=1) ?_ ?_ (by decide) ?_ hU hx
  · exact axial_paste_eventually_left (continuous_apply 0) ht
  · filter_upwards [(isOpen_lt (continuous_apply (0:Fin 3)) continuous_const).mem_nhds ht] with y hy
    apply Subtype.ext
    exact ite_eq_left hy
  · rw [pureModeValue_direction ((initialConnectorProfile_smooth a (1/2) J).differentiable (by simp))]
    norm_num only [show (1:Fin 3)≠0 from by decide,ite_false,ite_true,zero_add]
    exact mul_ne_zero (neg_ne_zero.mpr (initialConnectorProfile_pos _ _ _ _).ne') hsin

lemma finiteEnding_cascade_regular {a J L K : ℝ} (x : Coord3) (ht : J+2<x 0)
    (hr : x-Pi.single 0 (J+2)∈regularRegion
      (axialPair (cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2))))
      (cascadeSymmetricTensor L K 1) univ)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair (finiteEndingValue a J L K)) (finiteEndingSymmetricTensor a J L K) U := by
  have htrans := mem_regularRegion_translate hr (![J+2,0])
  apply mem_regularRegion_congr_nhds htrans ?_ ?_ hU hx
  · have he : finiteEndingValue a J L K =ᶠ[𝓝 x]
        fun y => cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2)) (y-Pi.single 0 (J+2)) :=
      axial_paste_eventually_right (continuous_apply 0) ht
    filter_upwards [he] with y hy
    rw [show (![J+2,0] : Fin 2 → ℝ)=![(Pi.single 0 (J+2) : Coord3) 0,0] by simp,
      axialPair_translate]
    simp only [axialPair,hy]
  · filter_upwards [(isOpen_lt continuous_const (continuous_apply (0:Fin 3))).mem_nhds ht] with y hy
    apply Subtype.ext
    exact ite_eq_right (not_lt.mpr hy.le)

theorem finiteEnding_regularRegion_ae {a J L K : ℝ} (hL : 0<L) (hK : 0<K)
    {U : Set Coord3} (hU : IsOpen U) :
    ∀ᵐ x : Coord3,x∈U →
      x∈regularRegion (axialPair (finiteEndingValue a J L K)) (finiteEndingSymmetricTensor a J L K) U := by
  have he := (measurePreserving_add_right (volume : Measure Coord3) (-Pi.single 0 (J+2))).quasiMeasurePreserving.ae
    (cascade_regularRegion_ae hL hK (by norm_num : (1:ℝ)≠0)
      (initialConnectorProfile_pos a (1/2) J (J+2)).ne' isOpen_univ)
  simp only [←sub_eq_add_neg] at he
  have hsin : ∀ᵐ x : Coord3,sin (x 1)≠0 := by
    simpa only [one_mul] using ae_sin_coord_ne_zero (by norm_num : (1:ℝ)≠0) (1:Fin 3)
  filter_upwards [he,hsin,ae_coord3_ne 0 (J+2)] with x hr hxs hxt
  intro hx
  rcases lt_or_gt_of_ne hxt with hl|hh
  · exact finiteEnding_initial_regular a J L K x hl hxs hU hx
  · apply finiteEnding_cascade_regular x hh (hr (mem_univ _) ?_) hU hx
    simp only [one_mul,Pi.sub_apply,Pi.single_eq_same]
    linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_AlignedEndingRegularity
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma permutedDilationEquiv_apply (e : Equiv.Perm (Fin 3)) {k : ℝ} (hk : k≠0) (x : Coord3) :
    permutedDilationEquiv e hk x=permutedDilation e k x := by
  ext i
  simp [permutedDilationEquiv,permutedDilation,ContinuousLinearEquiv.piCongrLeft,
    Homeomorph.piCongrLeft,Equiv.piCongrLeft]

lemma axialPairScaling_apply {k : ℝ} (hk : k≠0) (v : Fin 2 → ℝ) (i : Fin 2) :
    axialPairScaling hk v i=(if i=0 then k⁻¹ else 1)*v i := rfl

lemma alignedEnding_axialPair {lam k J L K : ℝ} (hk : k≠0) (x : Coord3) :
    axialPairScaling hk (axialPair (finiteEndingValue (lam/k) J L K)
      (permutedDilationEquiv angularAxisSwap hk x))=axialPair (alignedEndingValue lam k J L K) x := by
  ext i
  fin_cases i <;> simp [axialPairScaling_apply,permutedDilationEquiv_apply,axialPair,
    permutedDilation,angularAxisSwap_apply,alignedEndingValue,hk]

lemma RegularPatch.alignedEnding {lam k J L K : ℝ} (hk : k≠0) {O : Set Coord3}
    (h : RegularPatch (axialPair (finiteEndingValue (lam/k) J L K))
      (finiteEndingSymmetricTensor (lam/k) J L K) O) :
    RegularPatch (axialPair (alignedEndingValue lam k J L K))
      (alignedEndingSymmetricTensor lam k J L K)
      ((permutedDilationEquiv angularAxisSwap hk) ⁻¹' O) := by
  let P := permutedDilationEquiv angularAxisSwap hk
  let Q := axialPairScaling hk
  have he : (fun x => Q (axialPair (finiteEndingValue (lam/k) J L K) (P x)))=
      axialPair (alignedEndingValue lam k J L K) := funext (alignedEnding_axialPair hk)
  refine ⟨h.1.preimage P.continuous,?_,?_,?_⟩
  · rw [←he]
    exact Q.contDiff.contDiffOn.comp (h.2.1.comp P.contDiff.contDiffOn (fun _ hx => hx))
      (fun _ _ => mem_univ _)
  · apply contDiffOn_pi.mpr; intro i
    apply contDiffOn_pi.mpr; intro j
    have hh := h.2.2.1.comp P.contDiff.contDiffOn (fun _ hx => hx)
    have hi := (contDiff_apply ℝ (Fin 3 → ℝ) (angularAxisSwap i)).contDiffOn.comp hh (fun _ _ => mem_univ _)
    have hj := (contDiff_apply ℝ ℝ (angularAxisSwap j)).contDiffOn.comp hi (fun _ _ => mem_univ _)
    change ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun x =>
      finiteEndingTensor (lam/k) J L K (P x) (angularAxisSwap i) (angularAxisSwap j)) (P ⁻¹' O) at hj
    convert hj using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [alignedEndingSymmetricTensor,alignedEndingTensor,
      P,permutedDilationEquiv_apply]
  · rw [←he]
    exact TwoFieldRankRegular.linearCoordinates h.1 h.2.1 h.2.2.2 P Q

theorem alignedEnding_regularRegion_ae {lam k J L K : ℝ} (hk : k≠0) (hL : 0<L) (hK : 0<K)
    {U : Set Coord3} (hU : IsOpen U) :
    ∀ᵐ x : Coord3,x∈U → x∈regularRegion (axialPair (alignedEndingValue lam k J L K))
      (alignedEndingSymmetricTensor lam k J L K) U := by
  have he := (permutedDilation_quasiMeasurePreserving angularAxisSwap hk).ae
    (finiteEnding_regularRegion_ae (a:=lam/k) (J:=J) hL hK isOpen_univ)
  filter_upwards [he] with x hx
  intro hxU
  obtain ⟨O,hOU,hO,hxO⟩ := mem_regularRegion_iff.mp (hx (mem_univ _))
  have hh : x∈regularRegion (axialPair (alignedEndingValue lam k J L K))
      (alignedEndingSymmetricTensor lam k J L K) univ := by
    apply mem_regularRegion_iff.mpr
    refine ⟨(permutedDilationEquiv angularAxisSwap hk) ⁻¹' O,subset_univ _,hO.alignedEnding hk,?_⟩
    simpa only [mem_preimage,permutedDilationEquiv_apply] using hxO
  exact mem_regularRegion_congr_nhds hh (Filter.EventuallyEq.rfl) (Filter.EventuallyEq.rfl) hU hxU

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma delayedEndingValue_initial_of_bound {lam k J L K R : ℝ} (hk : 0<k) (hJ : 0<J)
    (x : Coord3) (hx : k*(x 0-R)≤1) :
    delayedEndingValue lam k J L K R x=exp (-lam*x 0)*cos (k*x 2) := by
  rw [delayedEndingValue,alignedEnding_initial hk hJ _ (by simpa using hx)]
  simp only [Pi.sub_apply,Pi.single_eq_same,Pi.single_eq_of_ne (show (2:Fin 3)≠0 by decide),sub_zero]
  rw [←mul_assoc,←exp_add]
  congr 2
  ring

lemma delayedEndingValue_initial {lam k J L K R : ℝ} (hk : 0<k) (hJ : 0<J)
    (x : Coord3) (hx : x 0≤R) :
    delayedEndingValue lam k J L K R x=exp (-lam*x 0)*cos (k*x 2) := by
  apply delayedEndingValue_initial_of_bound hk hJ
  have hh := mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr hx)
  linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_DelayedEndingRegularity
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma axialAmplitudeEquiv_apply (a : ℝ) (ha : a≠0) (v : Fin 2 → ℝ) (i : Fin 2) :
    axialAmplitudeEquiv a ha v i=(if i=0 then 1 else a)*v i := rfl

lemma RegularPatch.amplitude {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {O : Set Coord3} (h : RegularPatch u A O) (a : ℝ) (ha : a≠0) :
    RegularPatch (fun x => axialAmplitudeEquiv a ha (u x)) A O := by
  refine ⟨h.1,(axialAmplitudeEquiv a ha).contDiff.contDiffOn.comp h.2.1 (fun _ _ => mem_univ _),h.2.2.1,?_⟩
  exact h.2.2.2.linearCoordinates h.1 h.2.1 (ContinuousLinearEquiv.refl ℝ Coord3) (axialAmplitudeEquiv a ha)

lemma delayedEnding_axialPair (lam k J L K R : ℝ) (x : Coord3) :
    axialAmplitudeEquiv (exp (-lam*R)) (exp_pos _).ne'
      (axialPair (alignedEndingValue lam k J L K) (x-Pi.single 0 R))+![R,0]=
        axialPair (delayedEndingValue lam k J L K R) x := by
  ext i
  fin_cases i <;> simp [axialAmplitudeEquiv_apply,axialPair,delayedEndingValue]

lemma RegularPatch.delayedEnding {lam k J L K R : ℝ} {O : Set Coord3}
    (h : RegularPatch (axialPair (alignedEndingValue lam k J L K))
      (alignedEndingSymmetricTensor lam k J L K) O) :
    RegularPatch (axialPair (delayedEndingValue lam k J L K R))
      (delayedEndingSymmetricTensor lam k J L K R) ((fun x : Coord3 => x-Pi.single 0 R) ⁻¹' O) := by
  have hh := (h.amplitude (exp (-lam*R)) (exp_pos _).ne').translate (Pi.single 0 R) ![R,0]
  convert hh using 1
  · funext x
    exact (delayedEnding_axialPair _ _ _ _ _ _ _).symm
  · rfl

lemma delayedEnding_regularRegion_ae {lam k J L K R : ℝ} (hk : k≠0) (hL : 0<L) (hK : 0<K)
    {U : Set Coord3} (hU : IsOpen U) :
    ∀ᵐ x : Coord3,x∈U → x∈regularRegion (axialPair (delayedEndingValue lam k J L K R))
      (delayedEndingSymmetricTensor lam k J L K R) U := by
  have he := (measurePreserving_add_right (volume : Measure Coord3) (-Pi.single 0 R)).quasiMeasurePreserving.ae
    (alignedEnding_regularRegion_ae (lam:=lam) (J:=J) hk hL hK isOpen_univ)
  simp only [←sub_eq_add_neg] at he
  filter_upwards [he] with x hx
  intro hxU
  obtain ⟨O,hOU,hO,hxO⟩ := mem_regularRegion_iff.mp (hx (mem_univ _))
  have hh : x∈regularRegion (axialPair (delayedEndingValue lam k J L K R))
      (delayedEndingSymmetricTensor lam k J L K R) univ := by
    apply mem_regularRegion_iff.mpr
    refine ⟨(fun y : Coord3 => y-Pi.single 0 R) ⁻¹' O,subset_univ _,?_,?_⟩
    · exact hO.delayedEnding (R:=R)
    · exact hxO
  exact mem_regularRegion_congr_nhds hh (Filter.EventuallyEq.rfl) (Filter.EventuallyEq.rfl) hU hxU

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_SimpleWallGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma real_section_hasDeriv {g : E × ℝ → ℝ} (hg : Differentiable ℝ g)
    (p : E) (z : ℝ) : HasDerivAt (fun t => g (p,t)) (wallDerivative g (p,z)) z := by
  simpa only [Function.comp_def,wallDerivative] using
    (hg (p,z)).hasFDerivAt.comp_hasDerivAt z ((hasDerivAt_const z p).prodMk (hasDerivAt_id z))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_RecenteredWallField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma wallDerivative_eq_of_hasDeriv {f : E×ℝ → ℝ} (hf : Differentiable ℝ f)
    {q : E} {z d : ℝ} (hd : HasDerivAt (fun t => f (q,t)) d z) :
    wallDerivative f (q,z)=d := (real_section_hasDeriv hf q z).unique hd

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PureModeWall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma pureWallMode_smooth (σ lam k : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (pureWallMode σ lam k) := by
  unfold pureWallMode
  fun_prop

lemma pureWallMode_normalDerivative (σ lam k : ℝ) (q : ℝ×ℝ) (z : ℝ) :
    wallDerivative (pureWallMode σ lam k) (q,z)=
      σ*exp (-lam*q.1)*(-sin (k*z)*k) := by
  apply wallDerivative_eq_of_hasDeriv ((pureWallMode_smooth σ lam k).differentiable (by simp))
  simpa only [pureWallMode,mul_one,id_eq] using
    (((hasDerivAt_id z).const_mul k).cos.const_mul (σ*exp (-lam*q.1)))

lemma pureWallMode_normalSecond (σ lam k : ℝ) (q : ℝ×ℝ) (z : ℝ) :
    wallDerivative (wallDerivative (pureWallMode σ lam k)) (q,z)=
      -(σ*exp (-lam*q.1)*cos (k*z)*k^2) := by
  apply wallDerivative_eq_of_hasDeriv
    ((wallDerivative_smooth (pureWallMode_smooth σ lam k)).differentiable (by simp))
  have h := (((((hasDerivAt_id z).const_mul k).sin.neg).mul_const k).const_mul
    (σ*exp (-lam*q.1)))
  convert! h using 1 <;> first | rfl | (simp only [pureWallMode_normalDerivative,id_eq,Pi.neg_apply] <;> ring)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_EndingJoinCutoff
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma endingJoinCutoff_smooth : ContDiff ℝ (↑(⊤:ℕ∞)) endingJoinCutoff :=
  smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma endingJoinCutoff_left {t : ℝ} (ht : t≤6) : endingJoinCutoff t=0 :=
  smoothTransition.zero_of_nonpos (by linarith)

lemma endingJoinCutoff_right {t : ℝ} (ht : 7≤t) : endingJoinCutoff t=1 :=
  smoothTransition.one_of_one_le (by linarith)

lemma endingJoinTensor_left (D : Coord3 → Mat3) (lam k J L K : ℝ) (x : Coord3) (hx : x 0≤6) :
    endingJoinTensor D lam k J L K x=D x := by
  simp [endingJoinTensor,endingJoinCutoff_left hx]

lemma endingJoinTensor_right (D : Coord3 → Mat3) (lam k J L K : ℝ) (x : Coord3) (hx : 7≤x 0) :
    endingJoinTensor D lam k J L K x=delayedEndingTensor lam k J L K 7 x := by
  simp [endingJoinTensor,endingJoinCutoff_right hx]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SimpleLevelNull
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

lemma simple_zeros_countable {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (U : Set ℝ)
    (hn : ∀ x∈U,f x=0 → deriv f x≠0) : ({x | x∈U ∧ f x=0} : Set ℝ).Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  have he := (hf.hasStrictDerivAt (by norm_num) (x:=x)).eventually_left_inverse (hn x hx.1 hx.2)
  obtain ⟨V,hVs,hV,hxV⟩ := mem_nhds_iff.mp he
  refine ⟨V,hV,?_⟩
  ext y
  constructor
  · intro hy
    have hxy := hVs hy.1
    change HasStrictDerivAt.localInverse f (deriv f x) x _ _ (f y)=y at hxy
    exact hxy.symm.trans ((congrArg (HasStrictDerivAt.localInverse f (deriv f x) x _ _)
      (hy.2.2.trans hx.2.symm)).trans he.self_of_nhds)
  · intro hy
    subst y
    exact ⟨hxV,hx⟩

lemma simple_wall_zero_null {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f)
    {U : Set Box3} (hU : MeasurableSet U)
    (hn : ∀ x∈U,f x=0 → wallDerivative f x≠0) : volume ({x | x∈U ∧ f x=0})=0 := by
  change (volume.prod volume) ({x : Box3 | x∈U ∧ f x=0})=0
  apply Measure.measure_prod_null_of_ae_null (hU.inter (isClosed_eq hf.continuous continuous_const).measurableSet)
  apply Filter.Eventually.of_forall
  intro q
  have hs : ContDiff ℝ 1 (fun z : ℝ => f (q,z)) :=
    (hf.comp (contDiff_const.prodMk contDiff_id)).of_le (show (1:WithTop ℕ∞)≤↑(⊤:ℕ∞) by norm_cast)
  have hh := simple_zeros_countable hs {z | (q,z)∈U} (by
    intro z hz he
    simpa only [←wallDerivative_slice (hf.differentiable (by simp))] using hn (q,z) hz he)
  exact hh.measure_zero volume

lemma wallDerivative_boxPullback {f : Coord3 → ℝ} (hf : Differentiable ℝ f) (p : Box3) :
    wallDerivative (fun y => f (boxCoordinates.symm y)) p=
      direction (Pi.single 2 1) f (boxCoordinates.symm p) := by
  have he := ((hf (boxCoordinates.symm p)).hasFDerivAt.comp p boxCoordinates.symm.hasFDerivAt).fderiv
  change fderiv ℝ (f ∘ boxCoordinates.symm) p (0,1)=_
  rw [he,ContinuousLinearMap.comp_apply]
  have hh : (boxCoordinates.symm : Box3 →L[ℝ] Coord3) (0,1)=Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp [boxCoordinates_symm_apply]
  rw [hh]
  rfl

lemma simple_coord_zero_ae {f : Coord3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f)
    {U : Set Coord3} (hU : MeasurableSet U)
    (hn : ∀ x∈U,f x=0 → direction (Pi.single 2 1) f x≠0) :
    ∀ᵐ x : Coord3,x∈U → f x≠0 := by
  have hh := simple_wall_zero_null (hf.comp boxCoordinates.symm.contDiff)
    (hU.preimage boxCoordinates.symm.continuous.measurable) (by
      intro p hp hz
      change wallDerivative (fun y => f (boxCoordinates.symm y)) p≠0
      rw [wallDerivative_boxPullback (hf.differentiable (by simp))]
      exact hn _ hp hz)
  have ha := boxCoordinates_volume.quasiMeasurePreserving.ae (compl_mem_ae_iff.mpr hh)
  filter_upwards [ha] with x hx
  simpa only [mem_compl_iff,mem_ofPred_eq,mem_preimage,Function.comp_def,boxCoordinates.symm_apply_apply,not_and] using hx

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma pairMinor_rank {u : Coord3 → Fin 2 → ℝ} {x : Coord3} (hn : pairMinor u x≠0) :
    LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col := by
  apply linearIndependent_fin2.mpr
  constructor
  · intro hz
    apply hn
    have h0 := congrFun hz 0
    have h2 := congrFun hz 2
    change fderiv ℝ u x (Pi.single 0 1) 1=0 at h0
    change fderiv ℝ u x (Pi.single 2 1) 1=0 at h2
    simp only [pairMinor,h0,h2,mul_zero,sub_self]
  · intro a he
    apply hn
    have h0 := congrFun he 0
    have h2 := congrFun he 2
    change a*fderiv ℝ u x (Pi.single 0 1) 1=fderiv ℝ u x (Pi.single 0 1) 0 at h0
    change a*fderiv ℝ u x (Pi.single 2 1) 1=fderiv ℝ u x (Pi.single 2 1) 0 at h2
    simp only [pairMinor,←h0,←h2]
    ring

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma pairMinor_smooth {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (pairMinor u) := by
  have hh (i : Fin 3) (j : Fin 2) : ContDiff ℝ (↑(⊤:ℕ∞))
      (fun x => fderiv ℝ u x (Pi.single i 1) j) :=
    (contDiff_apply ℝ ℝ j).comp ((hu.fderiv_right (by simp)).clm_apply contDiff_const)
  exact ((hh 0 0).mul (hh 2 1)).sub ((hh 2 0).mul (hh 0 1))

lemma regularRegion_ae_of_simple_minor {u : Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {A : Coord3 → Symmetric3}
    (hA : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => (A x).val))
    {U : Set Coord3} (hU : IsOpen U)
    (hn : ∀ x∈U,pairMinor u x=0 → direction (Pi.single 2 1) (pairMinor u) x≠0) :
    ∀ᵐ x : Coord3,x∈U → x∈regularRegion u A U := by
  have hm := pairMinor_smooth hu
  have ha := simple_coord_zero_ae hm hU.measurableSet hn
  let O := U∩{x | pairMinor u x≠0}
  have hO : IsOpen O := hU.inter (isOpen_ne_fun hm.continuous continuous_const)
  have hr : RegularPatch u A O :=
    ⟨hO,hu.contDiffOn,hA.contDiffOn,Or.inl (fun x hx => pairMinor_rank hx.2)⟩
  filter_upwards [ha] with x hx
  intro hxU
  exact mem_regularRegion_iff.mpr ⟨O,inter_subset_left,hr,⟨hxU,hx hxU⟩⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PeriodicBandCompactness
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Real

lemma pairMinor_wallCoordinatePair {v : Box3 → ℝ} (hv : Differentiable ℝ v) (x : Coord3) :
    pairMinor (wallCoordinatePair v) x=wallDerivative v (boxCoordinates x) := by
  simp [pairMinor,wallCoordinatePair_derivative hv,boxCoordinates_apply,wallDerivative]
  rfl

lemma direction_boxCoordinates {v : Box3 → ℝ} (hv : Differentiable ℝ v) (x : Coord3) :
    direction (Pi.single 2 1) (fun y => v (boxCoordinates y)) x=wallDerivative v (boxCoordinates x) := by
  change fderiv ℝ (v ∘ boxCoordinates) x (Pi.single 2 1)=_
  rw [boxCoordinates_fderiv v hv]
  simp [wallDerivative,boxCoordinates_apply]
  rfl

lemma pureMode_pairMinor_noncritical {σ lam k : ℝ} (hσ : σ≠0) (hk : k≠0) (x : Coord3) :
    pairMinor (wallCoordinatePair (pureWallMode σ lam k)) x≠0 ∨
      direction (Pi.single 2 1) (pairMinor (wallCoordinatePair (pureWallMode σ lam k))) x≠0 := by
  have hs := pureWallMode_smooth σ lam k
  have he : pairMinor (wallCoordinatePair (pureWallMode σ lam k))=
      fun x => wallDerivative (pureWallMode σ lam k) (boxCoordinates x) :=
    funext (pairMinor_wallCoordinatePair (hs.differentiable (by simp)))
  rw [he,direction_boxCoordinates ((wallDerivative_smooth hs).differentiable (by simp))]
  dsimp only
  rw [boxCoordinates_apply,pureWallMode_normalDerivative,pureWallMode_normalSecond]
  by_cases hz : sin (k*x 2)=0
  · right
    have hc : cos (k*x 2)≠0 := by
      intro hc
      have hh := sin_sq_add_cos_sq (k*x 2)
      rw [hz,hc] at hh
      norm_num at hh
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero hσ (exp_ne_zero _)) hc) (pow_ne_zero 2 hk))
  · left
    exact mul_ne_zero (mul_ne_zero hσ (exp_ne_zero _)) (mul_ne_zero (neg_ne_zero.mpr hz) hk)

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_EndingJoinMiddleModel
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma delayedInitialTensor_smooth (lam k J R : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (delayedInitialTensor lam k J R) := by
  have hq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => initialConnectorAngular (lam/k) (1/2) J (k*(x 0-R))) :=
    (initialConnectorAngular_smooth _ _ _).comp (contDiff_const.mul ((contDiff_apply ℝ ℝ 0).sub contDiff_const))
  have hh := pureModeTensor_smooth hq (1:Fin 3)
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  exact contDiff_pi.mp (contDiff_pi.mp hh (angularAxisSwap i)) (angularAxisSwap j)

lemma delayedEndingTensor_initial {lam k J L K R : ℝ} (x : Coord3) (hx : k*(x 0-R)<J+2) :
    delayedEndingTensor lam k J L K R x=delayedInitialTensor lam k J R x := by
  ext i j
  change finiteEndingTensor (lam/k) J L K (permutedDilation angularAxisSwap k (x-Pi.single 0 R))
    (angularAxisSwap i) (angularAxisSwap j)=_
  have ht : (permutedDilation angularAxisSwap k (x-Pi.single 0 R)) 0=k*(x 0-R) := by
    simp [permutedDilation,angularAxisSwap_apply]
  rw [finiteEndingTensor,ht,ite_eq_left hx]
  rfl

lemma endingJoinMiddleTensor_smooth (s : Fin 3 → ℝ) (lam k J : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => (endingJoinMiddleTensor s lam k J x).val) := by
  have hχ := endingJoinCutoff_smooth.comp (contDiff_apply ℝ ℝ (0:Fin 3))
  exact ((contDiff_const.sub hχ).smul contDiff_const).add (hχ.smul (delayedInitialTensor_smooth _ _ _ _))

lemma endingJoinMiddle_regular_ae (s : Fin 3 → ℝ) (lam J : ℝ) {k : ℝ} (hk : k≠0) :
    ∀ᵐ x : Coord3,x∈regularRegion (wallCoordinatePair (pureWallMode 1 lam k))
      (endingJoinMiddleTensor s lam k J) univ := by
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) (wallCoordinatePair (pureWallMode 1 lam k)) :=
    wallCoordinatePair_smooth (pureWallMode_smooth _ _ _)
  have hh := regularRegion_ae_of_simple_minor hu (endingJoinMiddleTensor_smooth s lam k J) isOpen_univ
    (fun x _ hx => (pureMode_pairMinor_noncritical (by norm_num : (1:ℝ)≠0) hk x).resolve_left (not_not.mpr hx))
  filter_upwards [hh] with x hx
  exact hx (mem_univ _)

lemma wallCoordinatePair_pure (lam k : ℝ) (x : Coord3) :
    wallCoordinatePair (pureWallMode 1 lam k) x=![x 0,exp (-lam*x 0)*cos (k*x 2)] := by
  simp [wallCoordinatePair,pureWallMode,boxCoordinates_apply]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothRankRegularity
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Real Matrix
open scoped Matrix.Norms.Elementwise

lemma smoothPair_gradientColumns_continuous {u : Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) :
    Continuous (fun x => (gradientColumns (fderiv ℝ u x)).col) := by
  apply continuous_pi; intro j
  apply continuous_pi; intro i
  exact (continuous_apply j).comp ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)

lemma smoothPair_mem_regularRegion {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hA : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => (A x).val))
    {x : Coord3} (hxrank : LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) : x∈regularRegion u A U := by
  let O := {y : Coord3 | LinearIndependent ℝ (gradientColumns (fderiv ℝ u y)).col}
  have hO : IsOpen O := isOpen_setOfPred_linearIndependent.preimage (smoothPair_gradientColumns_continuous hu)
  exact mem_regularRegion_iff.mpr ⟨U∩O,inter_subset_left,
    ⟨hU.inter hO,hu.contDiffOn,hA.contDiffOn,Or.inl (fun y hy => hy.2)⟩,hx,hxrank⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_MatchedEndingRegularity
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma matchedEndingPair_pure {u : Coord3 → Fin 2 → ℝ} {lam k J L K : ℝ}
    (hk : 0<k) (hJ : 0<J)
    (hu : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)])
    (x : Coord3) (hx : x 0∈Icc (4:ℝ) 7) :
    matchedEndingPair u lam k J L K x=wallCoordinatePair (pureWallMode 1 lam k) x := by
  rw [wallCoordinatePair_pure,matchedEndingPair]
  split_ifs
  · exact hu x hx.1
  · rw [delayedEndingValue_initial hk hJ x hx.2]

theorem matchedEnding_regularRegion_ae_oai {D : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hD : ContDiff ℝ (↑(⊤:ℕ∞)) D) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hDs : ∀ x,(D x).IsSymm) {s : Fin 3 → ℝ} {lam k J L K : ℝ}
    (hk : 0<k) (hJ : 0<J) (hL : 0<L) (hK : 0<K)
    (hum : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)])
    (hDm : ∀ x : Coord3,x 0∈Icc (6:ℝ) 7 → D x=flatBackgroundTensor s)
    (hur : ∀ᵐ x : Coord3,x 0∈Ioo 0 6 → LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col)
    {U : Set Coord3} (hU : IsOpen U) (hUpos : U⊆{x : Coord3 | 0<x 0}) :
    ∀ᵐ x : Coord3,x∈U → x∈regularRegion (matchedEndingPair u lam k J L K)
      (endingJoinSymmetricTensor D hDs lam k J L K) U := by
  have he := delayedEnding_regularRegion_ae (lam:=lam) (J:=J) (R:=7) hk.ne' hL hK isOpen_univ
  have hm := endingJoinMiddle_regular_ae s lam J hk.ne'
  filter_upwards [hur,he,hm,ae_coord3_ne 0 6,ae_coord3_ne 0 7] with x hxrank hxe hxm hx6 hx7
  intro hxU
  have hxpos := hUpos hxU
  by_cases ht6 : x 0<6
  · let A : Coord3 → Symmetric3 := fun y => ⟨D y,hDs y⟩
    have hr : x∈regularRegion u A univ :=
      smoothPair_mem_regularRegion hu hD (hxrank ⟨hxpos,ht6⟩) isOpen_univ (mem_univ _)
    apply mem_regularRegion_congr_nhds hr ?_ ?_ hU hxU
    · exact axial_paste_eventually_left (continuous_apply 0) (by linarith : x 0<13/2)
    · filter_upwards [(isOpen_lt (continuous_apply (0:Fin 3)) continuous_const).mem_nhds ht6] with y hy
      apply Subtype.ext
      exact endingJoinTensor_left _ _ _ _ _ _ _ hy.le
  · have h6 : 6<x 0 := lt_of_le_of_ne (le_of_not_gt ht6) (Ne.symm hx6)
    by_cases ht7 : x 0<7
    · apply mem_regularRegion_congr_nhds hxm ?_ ?_ hU hxU
      · filter_upwards [(isOpen_lt continuous_const (continuous_apply (0:Fin 3))).mem_nhds h6,
          (isOpen_lt (continuous_apply (0:Fin 3)) continuous_const).mem_nhds ht7] with y hy6 hy7
        exact matchedEndingPair_pure hk hJ hum y ⟨by linarith,hy7.le⟩
      · filter_upwards [(isOpen_lt continuous_const (continuous_apply (0:Fin 3))).mem_nhds h6,
          (isOpen_lt (continuous_apply (0:Fin 3)) continuous_const).mem_nhds ht7] with y hy6 hy7
        apply Subtype.ext
        change endingJoinTensor D lam k J L K y=_
        rw [endingJoinTensor,hDm y ⟨hy6.le,hy7.le⟩,
          delayedEndingTensor_initial y (show k*(y 0-7)<J+2 from
            (mul_neg_of_pos_of_neg hk (by linarith)).trans (by linarith))]
        rfl
    · have h7 : 7<x 0 := lt_of_le_of_ne (le_of_not_gt ht7) (Ne.symm hx7)
      apply mem_regularRegion_congr_nhds (hxe (mem_univ _)) ?_ ?_ hU hxU
      · exact axial_paste_eventually_right (continuous_apply 0) (by linarith : 13/2<x 0)
      · filter_upwards [(isOpen_lt continuous_const (continuous_apply (0:Fin 3))).mem_nhds h7] with y hy
        apply Subtype.ext
        exact endingJoinTensor_right _ _ _ _ _ _ _ hy.le

end ScalarConductivity

end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.matchedEnding_regularRegion_ae_oai := @OAI.ScalarConductivity.matchedEnding_regularRegion_ae_oai
