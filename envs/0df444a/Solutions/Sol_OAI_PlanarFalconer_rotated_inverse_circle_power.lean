-- Prove2me | solution 1 for OAI.PlanarFalconer.rotated_inverse_circle_power
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:25:29.925528+00:00
-- url     : https://prove2.me/submissions/ae714875-731f-4cf8-88e4-d9f3d3651c37

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_full_circle_stationary_expansion

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

namespace AngularDifferentialExpr

theorem cost_nonneg (p : AngularDifferentialExpr) : 0 ≤ p.cost := by
  induction p with
  | term c k => exact norm_nonneg c
  | add p q hp hq => exact add_nonneg hp hq
  | comp p q hp hq => exact mul_nonneg hp hq

theorem smooth_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

theorem apply_contDiff (p : AngularDifferentialExpr) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (p.apply f) := by
  induction p generalizing f with
  | term c k => exact contDiff_const.mul (smooth_iteratedDeriv hf k)
  | add p q hp hq => exact (hp hf).add (hq hf)
  | comp p q hp hq => exact hp (hq hf)

theorem iteratedDeriv_iterated (m k : ℕ) (f : ℝ → ℂ) :
    iteratedDeriv m (iteratedDeriv k f) = iteratedDeriv (m+k) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

theorem sum_apply (ps : List AngularDifferentialExpr) (f : ℝ → ℂ) (x : ℝ) :
    (sum ps).apply f x = (ps.map (fun p => p.apply f x)).sum := by
  induction ps with
  | nil => simp [sum, apply]
  | cons p ps ih => simp [sum, apply, ih]

theorem sum_order_le (ps : List AngularDifferentialExpr) (n : ℕ)
    (h : ∀ p ∈ ps, p.order ≤ n) : (sum ps).order ≤ n := by
  induction ps with
  | nil => exact Nat.zero_le n
  | cons p ps ih =>
    exact max_le (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

end AngularDifferentialExpr
end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDifferentialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology
namespace AngularDifferentialExpr

theorem smooth_finite {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (m : ℕ) (x : ℝ) :
    ContDiffAt ℝ m f x :=
  (hf.of_le (WithTop.coe_le_coe.mpr (show (m:ℕ∞) ≤ ⊤ from le_top))).contDiffAt

theorem derivative_bound (p : AngularDifferentialExpr) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (m : ℕ) (x : ℝ)
    (hb : ∀ k ≤ m+p.order, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ‖iteratedDeriv m (p.apply f) x‖ ≤ p.cost * (C*D^(m+p.order)) := by
  induction p generalizing f C m with
  | term c k =>
    simp only [apply, cost, order, iteratedDeriv_const_mul_field, iteratedDeriv_iterated,
      norm_mul]
    exact mul_le_mul_of_nonneg_left (hb (m+k) le_rfl) (norm_nonneg c)
  | add p q hp hq =>
    have hpord : m+p.order ≤ m+max p.order q.order := Nat.add_le_add_left (le_max_left _ _) _
    have hqord : m+q.order ≤ m+max p.order q.order := Nat.add_le_add_left (le_max_right _ _) _
    have hp' := hp hf hC m (fun k hk => hb k (hk.trans hpord))
    have hq' := hq hf hC m (fun k hk => hb k (hk.trans hqord))
    change ‖iteratedDeriv m (fun y => p.apply f y + q.apply f y) x‖ ≤ _
    rw [iteratedDeriv_fun_add (smooth_finite (p.apply_contDiff hf) m x)
      (smooth_finite (q.apply_contDiff hf) m x)]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ p.cost * (C*D^(m+max p.order q.order)) +
          q.cost * (C*D^(m+max p.order q.order)) := add_le_add
        (hp'.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hpord) hC) p.cost_nonneg))
        (hq'.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hqord) hC) q.cost_nonneg))
      _ = _ := by simp only [cost, order]; ring
  | comp p q hp hq =>
    have hCq : 0 ≤ q.cost*C*D^q.order := by
      exact mul_nonneg (mul_nonneg q.cost_nonneg hC) (pow_nonneg (zero_le_one.trans hD) _)
    have hbq : ∀ k ≤ m+p.order,
        ‖iteratedDeriv k (q.apply f) x‖ ≤ (q.cost*C*D^q.order)*D^k := by
      intro k hk
      have h := hq hf hC k (fun l hl => hb l (by
        simp only [order]; omega))
      apply h.trans_eq
      rw [pow_add]
      ring
    have h := hp (q.apply_contDiff hf) hCq m hbq
    apply h.trans_eq
    simp only [cost, order, pow_add]
    ring

theorem derivative_bound_of_order_le (p : AngularDifferentialExpr) {n : ℕ}
    (hn : p.order ≤ n) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (m : ℕ) (x : ℝ)
    (hb : ∀ k ≤ m+n, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ‖iteratedDeriv m (p.apply f) x‖ ≤ p.cost * (C*D^(m+n)) := by
  have hm := Nat.add_le_add_left hn m
  exact (p.derivative_bound hf hC hD m x (fun k hk => hb k (hk.trans hm))).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hm) hC) p.cost_nonneg)

end AngularDifferentialExpr
end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Frostman_FrostmanProfileCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal

theorem fixed_constant_absorbed {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ ((2:ℝ)^N)^lam := by
  have hb : 1 < (2:ℝ)^lam := Real.one_lt_rpow (by norm_num) hlam
  obtain ⟨N₀,hN₀⟩ := pow_unbounded_of_one_lt C hb
  refine ⟨N₀,fun N hN => ?_⟩
  have hh := hN₀.le.trans (pow_le_pow_right₀ hb.le hN)
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm,
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hh
  exact hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationarySineChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem stationarySineInverse_contDiffAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    ContDiffAt ℝ ∞ stationarySineInverse u := by
  have hi : ContDiffAt ℝ ∞ (fun x : ℝ => x/2) u := contDiffAt_id.div_const 2
  have hh : ContDiffAt ℝ ∞ Real.arcsin (u/2) :=
    Real.contDiffAt_arcsin (by linarith [hu.1]) (by linarith [hu.2])
  have ht : ContDiffAt ℝ ∞ (fun x : ℝ => Real.arcsin (x/2)) u :=
    ContDiffAt.comp (f := fun x : ℝ => x/2) (g := Real.arcsin) u hh hi
  exact contDiffAt_const.mul ht

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryChartCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

 theorem stationaryCutoff_tsupport : tsupport (stationaryCutoff : ℝ → ℝ) = Icc (-1:ℝ) 1 := by
  rw [ContDiffBump.tsupport_eq,Real.closedBall_eq_Icc]
  norm_num [stationaryCutoff]

 theorem stationaryChartCutoff_tsupport :
    tsupport (stationaryChartCutoff : ℝ → ℝ) = Icc (-3/2:ℝ) (3/2) := by
  rw [ContDiffBump.tsupport_eq,Real.closedBall_eq_Icc]
  norm_num [stationaryChartCutoff]

 theorem stationaryChartCutoff_one {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) :
    stationaryChartCutoff u = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa [Real.closedBall_eq_Icc,stationaryChartCutoff] using hu

 theorem contDiff_localized_real {χ f : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (fun x => χ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hf x hx)
  · have he : (fun y => χ y * f y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

 theorem stationarySineJacobian_contDiffAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    ContDiffAt ℝ ∞ stationarySineJacobian u := by
  have hp : 0 < 1-u^2/4 := by nlinarith [hu.1,hu.2]
  have hf : ContDiffAt ℝ ∞ (fun u : ℝ => 1-u^2/4) u :=
    contDiffAt_const.sub ((contDiffAt_id.pow 2).div_const 4)
  exact (hf.sqrt hp.ne').inv (Real.sqrt_pos.2 hp).ne'

 theorem extendedStationaryInverse_contDiff : ContDiff ℝ ∞ extendedStationaryInverse := by
  apply contDiff_localized_real stationaryChartCutoff.contDiff
  intro u hu
  rw [stationaryChartCutoff_tsupport] at hu
  exact stationarySineInverse_contDiffAt ⟨by linarith [hu.1],by linarith [hu.2]⟩

 theorem stationaryWeight_contDiff : ContDiff ℝ ∞ stationaryWeight := by
  apply contDiff_localized_real stationaryCutoff.contDiff
  intro u hu
  rw [stationaryCutoff_tsupport] at hu
  exact stationarySineJacobian_contDiffAt ⟨by linarith [hu.1],by linarith [hu.2]⟩

 theorem extendedStationaryInverse_eq {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) :
    extendedStationaryInverse u = stationarySineInverse u := by
  simp [extendedStationaryInverse,stationaryChartCutoff_one hu]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryRemainderScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem stationary_remainder_factor (n : ℕ) (Λ A C D : ℝ) :
    ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))*(A*C*D^(2*(n+1)+2)) =
      (((2*Real.pi^2)^(n+1)/(n.factorial:ℝ))*A)*C*D^2*(D^2/Λ)^(n+1) := by
  have he : Real.pi^2/(Λ/2) = (2*Real.pi^2)/Λ := by ring
  rw [he,div_pow,div_pow,pow_add D (2*(n+1)) 2,pow_mul D 2 (n+1)]
  ring

 theorem stationary_slack_power {R D Λ c sig : ℝ} (hR : 1 ≤ R) (hD : 0 ≤ D)
    (hΛ : 0 < Λ) (hupper : D ≤ R^(1+sig))
    (hratio : D^2/Λ ≤ R^(-c*sig)) (J : ℕ) :
    D^2*(D^2/Λ)^J ≤ R^(2+2*sig-c*sig*(J:ℝ)) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  calc
    _ ≤ (R^(1+sig))^2*(R^(-c*sig))^J :=
      mul_le_mul (pow_le_pow_left₀ hD hupper 2)
        (pow_le_pow_left₀ (by positivity) hratio J) (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul_natCast hRp.le,← Real.rpow_mul_natCast hRp.le,← Real.rpow_add hRp]
      congr 1
      push_cast
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularNonstationaryPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem angular_even_decay_half {Λ : ℝ} (hΛ : 1 ≤ Λ) {J : ℕ} (hJ : 1 ≤ J) :
    (Λ^J)⁻¹ ≤ Λ^(-1/2:ℝ) := by
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  rw [← Real.rpow_natCast,← Real.rpow_neg hΛp.le]
  apply Real.rpow_le_rpow_of_exponent_le hΛ
  have hJ' : (1:ℝ) ≤ J := by exact_mod_cast hJ
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryJetOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem extendedStationaryInverse_zero : extendedStationaryInverse 0 = 0 := by
  rw [extendedStationaryInverse_eq (by norm_num)]
  simp [stationarySineInverse]

 theorem stationaryWeight_zero : stationaryWeight 0 = 1 := by
  have h : stationaryCutoff (0:ℝ) = 1 := stationaryCutoff.one_of_mem_closedBall
    (by simp [stationaryCutoff])
  simp [stationaryWeight,stationarySineJacobian,h]

 theorem stationaryAmplitude_zero (f : ℝ → ℂ) : stationaryAmplitude f 0 = f 0 := by
  simp [stationaryAmplitude,stationaryWeight_zero,extendedStationaryInverse_zero]

 theorem stationaryJet_order {n k : ℕ} (_hk : k ∈ Finset.range (n+1))
    (c : OrderedFinpartition (n-k)) : c.length ≤ n := by
  exact c.length_le.trans (Nat.sub_le _ _)

 theorem stationaryAmplitude_jet (n : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv n (stationaryAmplitude f) 0 = stationaryJet n f := by
  have hw : ContDiff ℝ ∞ (fun u => (stationaryWeight u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp stationaryWeight_contDiff
  have hfn : ContDiffAt ℝ n (f ∘ extendedStationaryInverse) 0 :=
    ((hf.comp extendedStationaryInverse_contDiff).of_le
      (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  have hwn : ContDiffAt ℝ n (fun u => (stationaryWeight u : ℂ)) 0 :=
    (hw.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  change iteratedDeriv n (fun u => (stationaryWeight u : ℂ) *
    (f ∘ extendedStationaryInverse) u) 0 = _
  rw [iteratedDeriv_fun_mul hwn hfn]
  unfold stationaryJet
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hf.contDiffAt
    extendedStationaryInverse_contDiff.contDiffAt
      (WithTop.coe_le_coe.mpr (show ((n-k:ℕ):ℕ∞) ≤ ⊤ from le_top))]
  simp only [extendedStationaryInverse_zero,Complex.real_smul]

 theorem stationaryJet_zero {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    stationaryJet 0 f = f 0 := by
  rw [← stationaryAmplitude_jet 0 hf,iteratedDeriv_zero,stationaryAmplitude_zero]

 theorem directStationaryOperator_zero {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (θ : ℝ) :
    directStationaryOperator 0 f θ =
      ((Real.sqrt (2*Real.pi):ℂ) * Complex.exp (-(Real.pi:ℂ)/4*Complex.I)) * f θ := by
  unfold directStationaryOperator
  have ht : ContDiff ℝ ∞ (fun u => f (u+θ)) := hf.comp (contDiff_id.add contDiff_const)
  simp only [mul_zero]
  rw [stationaryJet_zero ht]
  simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleDirectCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem fresnelCoefficient_half {Λ : ℝ} (hΛ : 0 < Λ) :
    fresnelCoefficient (Λ/2) = ((Λ^(-1/2:ℝ):ℝ):ℂ) *
      ((Real.sqrt (2*Real.pi):ℂ)*Complex.exp (-(Real.pi:ℂ)/4*Complex.I)) := by
  have he : Real.pi/(Λ/2) = (2*Real.pi)/Λ := by ring
  have hp : (Real.pi/(Λ/2))^(1/2:ℝ) = Λ^(-1/2:ℝ)*Real.sqrt (2*Real.pi) := by
    rw [he,Real.div_rpow (by positivity) hΛ.le,Real.sqrt_eq_rpow]
    rw [show (-1/2:ℝ) = -(1/2:ℝ) by ring,Real.rpow_neg hΛ.le]
    ring
  simp only [fresnelCoefficient,hp,Complex.ofReal_mul]
  ring

 theorem quadratic_coefficient_normalization (k : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) (d : ℂ) :
    ((((k.factorial:ℝ)⁻¹*(Real.pi^2/(Λ/2))^k):ℝ):ℂ)*Complex.I^k *
      (((-2*(Real.pi:ℂ)*Complex.I)^(2*k))⁻¹*d) =
    ((Λ⁻¹:ℝ):ℂ)^k * (((k.factorial:ℝ)⁻¹:ℝ):ℂ) * (-Complex.I/2)^k*d := by
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΛ' : (Λ:ℂ) ≠ 0 := by exact_mod_cast hΛ.ne'
  have he : (((Real.pi^2/(Λ/2):ℝ):ℂ)*Complex.I*((-2*(Real.pi:ℂ)*Complex.I)^2)⁻¹) =
      ((Λ⁻¹:ℝ):ℂ)*(-Complex.I/2) := by
    push_cast
    field_simp
    simp [Complex.I_sq]
  calc
    _ = (((k.factorial:ℝ)⁻¹:ℝ):ℂ) *
        ((((Real.pi^2/(Λ/2):ℝ):ℂ)*Complex.I*((-2*(Real.pi:ℂ)*Complex.I)^2)⁻¹)^k) * d := by
      simp only [Complex.ofReal_mul,Complex.ofReal_pow,mul_pow,inv_pow,pow_mul]
      ring
    _ = _ := by rw [he,mul_pow]; ring

 theorem stationary_expansion_direct_operators {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    fresnelCoefficient (Λ/2) * stationaryDerivativeExpansion f n Λ =
      ((Λ^(-1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
        ((Λ⁻¹:ℝ):ℂ)^j * directStationaryOperator j f 0 := by
  rw [fresnelCoefficient_half hΛ,stationaryDerivativeExpansion,mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [quadratic_coefficient_normalization j hΛ,stationaryAmplitude_jet (2*j) hf]
  simp only [directStationaryOperator,add_zero]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_FullCircleDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem cosineOscillator_periodic (Λ : ℝ) : Function.Periodic (cosineOscillator Λ) (2*Real.pi) := by
  intro θ
  simp [cosineOscillator,Real.cos_add_two_pi]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_FullCircleStationaryPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff

 theorem quadratic_scale_half {Λ : ℝ} (hΛ : 0 < Λ) :
    (Real.pi/(Λ/2))^(1/2:ℝ) = Λ^(-1/2:ℝ)*Real.sqrt (2*Real.pi) := by
  have he : Real.pi/(Λ/2) = (2*Real.pi)/Λ := by ring
  rw [he,Real.div_rpow (by positivity) hΛ.le,Real.sqrt_eq_rpow]
  rw [show (-1/2:ℝ) = -(1/2:ℝ) by ring,Real.rpow_neg hΛ.le]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem angularFiniteSum_apply {α : Type*} (s : Finset α)
    (p : α → AngularDifferentialExpr) (f : ℝ → ℂ) (x : ℝ) :
    (angularFiniteSum s p).apply f x = ∑ a ∈ s, (p a).apply f x := by
  simp [angularFiniteSum, AngularDifferentialExpr.sum_apply, List.map_map,
    Finset.sum_map_toList, Function.comp_def]

theorem angularFiniteSum_order {α : Type*} (s : Finset α)
    (p : α → AngularDifferentialExpr) (n : ℕ) (h : ∀ a ∈ s, (p a).order ≤ n) :
    (angularFiniteSum s p).order ≤ n := by
  apply AngularDifferentialExpr.sum_order_le
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  exact h a (Finset.mem_toList.mp ha)

theorem stationaryLeadingConstant_ne_zero : stationaryLeadingConstant ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne'
  · exact Complex.exp_ne_zero _

theorem stationaryJetExpr_order (n : ℕ) : (stationaryJetExpr n).order ≤ n := by
  apply angularFiniteSum_order
  intro k hk
  apply angularFiniteSum_order
  intro c _
  exact stationaryJet_order hk c

theorem stationaryJetExpr_apply (n : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    (stationaryJetExpr n).apply f x = stationaryJet n (fun u => f (u+x)) := by
  simp only [stationaryJetExpr, angularFiniteSum_apply, AngularDifferentialExpr.apply,
    stationaryJet, iteratedDeriv_comp_add_const, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem directStationaryExpr_order (j : ℕ) : (directStationaryExpr j).order ≤ 2*j := by
  simpa [directStationaryExpr, AngularDifferentialExpr.order] using stationaryJetExpr_order (2*j)

theorem directStationaryExpr_apply (j : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    (directStationaryExpr j).apply f x = directStationaryOperator j f x := by
  simp [directStationaryExpr, AngularDifferentialExpr.apply, stationaryJetExpr_apply,
    directStationaryOperator, stationaryLeadingConstant]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseStationaryOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem inverseStationaryExpr_order (n : ℕ) : (inverseStationaryExpr n).order ≤ 2*n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [inverseStationaryExpr, AngularDifferentialExpr.order]
    | succ n =>
      simp only [inverseStationaryExpr, AngularDifferentialExpr.order, zero_add]
      apply angularFiniteSum_order
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have hi := ih (n-k) (by omega)
      have hd := directStationaryExpr_order (k+1)
      change (directStationaryExpr (k+1)).order + (inverseStationaryExpr (n-k)).order ≤ _
      omega

theorem inverseStationaryOperator_contDiff (n : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (inverseStationaryOperator n f) :=
  (inverseStationaryExpr n).apply_contDiff hf

theorem inverseStationaryOperator_zero (f : ℝ → ℂ) (x : ℝ) :
    inverseStationaryOperator 0 f x = stationaryLeadingConstant⁻¹ * f x := by
  simp [inverseStationaryOperator, inverseStationaryExpr, AngularDifferentialExpr.apply]

theorem inverseStationaryOperator_succ (n : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    inverseStationaryOperator (n+1) f x = -stationaryLeadingConstant⁻¹ *
      ∑ k ∈ Finset.range (n+1),
        directStationaryOperator (k+1) (inverseStationaryOperator (n-k) f) x := by
  simp only [inverseStationaryOperator, inverseStationaryExpr, AngularDifferentialExpr.apply,
    iteratedDeriv_zero, angularFiniteSum_apply, directStationaryExpr_apply]

theorem inverseStationaryOperator_derivative_bound (n m : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (x : ℝ)
    (hb : ∀ k ≤ m+2*n, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ‖iteratedDeriv m (inverseStationaryOperator n f) x‖ ≤
      (inverseStationaryExpr n).cost * (C*D^(m+2*n)) :=
  (inverseStationaryExpr n).derivative_bound_of_order_le
    (inverseStationaryExpr_order n) hf hC hD m x hb

theorem inverseStationaryOperator_cancellation_zero {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    directStationaryOperator 0 (inverseStationaryOperator 0 f) x = f x := by
  rw [directStationaryOperator_zero (inverseStationaryOperator_contDiff 0 hf),
    inverseStationaryOperator_zero]
  change stationaryLeadingConstant * (stationaryLeadingConstant⁻¹ * f x) = f x
  rw [← mul_assoc, mul_inv_cancel₀ stationaryLeadingConstant_ne_zero, one_mul]

theorem inverseStationaryOperator_cancellation_succ (n : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    directStationaryOperator 0 (inverseStationaryOperator (n+1) f) x +
      (∑ k ∈ Finset.range (n+1),
        directStationaryOperator (k+1) (inverseStationaryOperator (n-k) f) x) = 0 := by
  rw [directStationaryOperator_zero (inverseStationaryOperator_contDiff (n+1) hf),
    inverseStationaryOperator_succ]
  change stationaryLeadingConstant * (-stationaryLeadingConstant⁻¹ * _) + _ = 0
  rw [← mul_assoc, mul_neg, mul_inv_cancel₀ stationaryLeadingConstant_ne_zero]
  ring

theorem inverseStationaryOperator_cancellation (n : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    (∑ h ∈ Finset.range (n+1),
      directStationaryOperator h (inverseStationaryOperator (n-h) f) x) =
        if n = 0 then f x else 0 := by
  cases n with
  | zero => simpa using inverseStationaryOperator_cancellation_zero hf x
  | succ n =>
    rw [Finset.sum_range_succ']
    simpa [Nat.succ_sub_succ_eq_sub, add_comm] using
      inverseStationaryOperator_cancellation_succ n hf x

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseStationaryTriangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem inverseStationaryOperator_cancellation_reverse (n : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    (∑ j ∈ Finset.range (n+1),
      directStationaryOperator (n-j) (inverseStationaryOperator j f) x) =
        if n = 0 then f x else 0 := by
  rw [← inverseStationaryOperator_cancellation n hf x,
    ← Finset.sum_range_reflect (fun h =>
      directStationaryOperator h (inverseStationaryOperator (n-h) f) x) (n+1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := by have := Finset.mem_range.mp hj; omega
  simp [Nat.sub_sub_self hj']

theorem inverseStationaryOperator_triangle_reverse (n : ℕ) (z : ℂ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    (∑ j ∈ Finset.range (n+1), ∑ h ∈ Finset.range (n+1-j),
      z^(j+h) * directStationaryOperator h (inverseStationaryOperator j f) x) = f x := by
  rw [← Finset.sum_range_diag_flip]
  have he : ∀ k ∈ Finset.range (n+1),
      (∑ j ∈ Finset.range (k+1),
        z^(j+(k-j)) * directStationaryOperator (k-j) (inverseStationaryOperator j f) x) =
          z^k * (if k = 0 then f x else 0) := by
    intro k hk
    rw [← inverseStationaryOperator_cancellation_reverse k hf x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ k := by have := Finset.mem_range.mp hj; omega
    rw [Nat.add_sub_of_le hj']
  rw [Finset.sum_congr rfl he]
  simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryJetLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology ComplexConjugate

 theorem stationaryJet_congr {f g : ℝ → ℂ} (h : f =ᶠ[𝓝 0] g) (n : ℕ) :
    stationaryJet n f = stationaryJet n g := by
  unfold stationaryJet
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [Filter.EventuallyEq.iteratedDeriv_eq c.length h]

 theorem stationaryJet_zero_germ {f : ℝ → ℂ} (h : f =ᶠ[𝓝 0] (fun _ => 0)) (n : ℕ) :
    stationaryJet n f = 0 := by
  rw [stationaryJet_congr h]
  simp [stationaryJet]

 theorem directStationaryOperator_congr {f g : ℝ → ℂ} {θ : ℝ}
    (h : f =ᶠ[𝓝 θ] g) (j : ℕ) : directStationaryOperator j f θ = directStationaryOperator j g θ := by
  have ht : Filter.Tendsto (fun u : ℝ => u+θ) (𝓝 0) (𝓝 θ) := by
    simpa only [ContinuousAt, zero_add] using (show Continuous (fun u : ℝ => u+θ) from
      continuous_id.add continuous_const).continuousAt (x := (0:ℝ))
  have he : (fun u => f (u+θ)) =ᶠ[𝓝 0] (fun u => g (u+θ)) := h.comp_tendsto ht
  unfold directStationaryOperator
  rw [stationaryJet_congr he]

 theorem stationaryDerivativeExpansion_zero_germ {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (h : f =ᶠ[𝓝 0] (fun _ => 0)) (n : ℕ) (Λ : ℝ) : stationaryDerivativeExpansion f n Λ = 0 := by
  unfold stationaryDerivativeExpansion
  apply Finset.sum_eq_zero
  intro k _
  rw [stationaryAmplitude_jet (2*k) hf,stationaryJet_zero_germ h]
  simp

 theorem fullCircleStationaryExpansion_one_sided {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (h : f =ᶠ[𝓝 Real.pi] (fun _ => 0)) (n : ℕ) (Λ : ℝ) :
    fullCircleStationaryExpansion Λ f n =
      Complex.exp (Complex.I*(Λ:ℂ))*(fresnelCoefficient (Λ/2)*stationaryDerivativeExpansion f n Λ) := by
  have ht : Filter.Tendsto (fun u : ℝ => u+Real.pi) (𝓝 0) (𝓝 Real.pi) := by
    simpa only [ContinuousAt, zero_add] using (show Continuous (fun u : ℝ => u+Real.pi) from
      continuous_id.add continuous_const).continuousAt (x := (0:ℝ))
  have he : (fun u => conj (f (u+Real.pi))) =ᶠ[𝓝 0] (fun _ => 0) := by
    filter_upwards [h.comp_tendsto ht] with u hu
    simp only [Function.comp_apply] at hu
    simp [hu]
  have hfs : ContDiff ℝ ∞ (fun u => conj (f (u+Real.pi))) :=
    Complex.conjCLE.contDiff.comp (hf.comp (contDiff_id.add contDiff_const))
  simp only [fullCircleStationaryExpansion,stationaryDerivativeExpansion_zero_germ hfs he,
    mul_zero,map_zero,add_zero]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseStationaryCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

theorem AngularDifferentialExpr.apply_shift (p : AngularDifferentialExpr)
    (f : ℝ → ℂ) (a : ℝ) :
    p.apply (fun x => f (x+a)) = fun x => p.apply f (x+a) := by
  induction p generalizing f with
  | term c k => simp [apply, iteratedDeriv_comp_add_const]
  | add p q hp hq => simp [apply, hp, hq]
  | comp p q hp hq => simp only [apply, hq, hp]

theorem AngularDifferentialExpr.apply_periodic (p : AngularDifferentialExpr)
    {f : ℝ → ℂ} {a : ℝ} (hf : Function.Periodic f a) :
    Function.Periodic (p.apply f) a := by
  have he : (fun x => f (x+a)) = f := funext hf
  have h := p.apply_shift f a
  rw [he] at h
  intro x
  exact (congrFun h x).symm

theorem complex_product_derivative_bound {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {A B D : ℝ}
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hD : 0 ≤ D) (m : ℕ) (x : ℝ)
    (hfb : ∀ k ≤ m, ‖iteratedDeriv k f x‖ ≤ A*D^k)
    (hgb : ∀ k ≤ m, ‖iteratedDeriv k g x‖ ≤ B*D^k) :
    ‖iteratedDeriv m (fun y => f y*g y) x‖ ≤ 2^m*A*B*D^m := by
  rw [iteratedDeriv_fun_mul (AngularDifferentialExpr.smooth_finite hf m x)
    (AngularDifferentialExpr.smooth_finite hg m x)]
  calc
    _ ≤ ∑ k ∈ Finset.range (m+1), (m.choose k:ℝ)*(A*D^k)*(B*D^(m-k)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ m := by have := Finset.mem_range.mp hk; omega
      simp only [norm_mul, Complex.norm_natCast]
      gcongr
      · exact hfb k hk'
      · exact hgb (m-k) (Nat.sub_le _ _)
    _ = A*B*(D+D)^m := by
      rw [add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [← two_mul, mul_pow]; ring

theorem cutoff_inverse_derivative_bound (j K : ℕ) {ψ f : ℝ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hf : ContDiff ℝ ∞ f) {P C D : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hbψ : ∀ k ≤ K, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P)
    (hbf : ∀ k ≤ K+2*j, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ∀ m ≤ K, ∀ x, ‖iteratedDeriv m
      (fun y => ψ y * inverseStationaryOperator j f y) x‖ ≤
        (2^K*P*(inverseStationaryExpr j).cost*C*D^(2*j))*D^m := by
  intro m hm x
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hCj : 0 ≤ (inverseStationaryExpr j).cost*C*D^(2*j) :=
    mul_nonneg (mul_nonneg (AngularDifferentialExpr.cost_nonneg _) hC) (pow_nonneg hD0 _)
  have h := complex_product_derivative_bound hψ (inverseStationaryOperator_contDiff j hf)
    hP hCj hD0 m x
    (fun k hk => (hbψ k (hk.trans hm) x).trans (by
      simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ hD : 1 ≤ D^k) hP))
    (fun k hk => (inverseStationaryOperator_derivative_bound j k hf hC hD x
      (fun l hl => hbf l (by omega) x)).trans_eq (by rw [pow_add]; ring))
  apply h.trans
  calc
    _ ≤ 2^K*P*((inverseStationaryExpr j).cost*C*D^(2*j))*D^m := by
      gcongr
      norm_num
    _ = _ := by ring

theorem cutoff_inverse_jets (j h : ℕ) {ψ f : ℝ → ℂ} {x : ℝ}
    (hψ : ψ =ᶠ[𝓝 x] (fun _ => 1)) :
    directStationaryOperator h (fun y => ψ y*inverseStationaryOperator j f y) x =
      directStationaryOperator h (inverseStationaryOperator j f) x := by
  apply directStationaryOperator_congr
  filter_upwards [hψ] with y hy
  simp [hy]

theorem cutoff_inverse_opposite (j : ℕ) {ψ f : ℝ → ℂ}
    (hψ : ψ =ᶠ[𝓝 Real.pi] (fun _ => 0)) :
    (fun y => ψ y*inverseStationaryOperator j f y) =ᶠ[𝓝 Real.pi] (fun _ => 0) := by
  filter_upwards [hψ] with y hy
  simp [hy]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseStationaryRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

theorem cutoff_inverse_expansion_eq (q j : ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    {ψ f : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hf : ContDiff ℝ ∞ f)
    (hψ₀ : ψ =ᶠ[𝓝 0] (fun _ => 1)) (hψπ : ψ =ᶠ[𝓝 Real.pi] (fun _ => 0)) :
    fullCircleStationaryExpansion Λ (fun y => ψ y*inverseStationaryOperator j f y) q =
      inverseDirectExpansion q j Λ f := by
  have hs := hψ.mul (inverseStationaryOperator_contDiff j hf)
  rw [fullCircleStationaryExpansion_one_sided hs (cutoff_inverse_opposite j hψπ),
    stationary_expansion_direct_operators hΛ hs]
  unfold inverseDirectExpansion
  rw [mul_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro h _
  rw [cutoff_inverse_jets j h hψ₀]

theorem cutoff_inverse_raw_remainder (q j M : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
    ∀ {ψ f : ℝ → ℂ}, ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ f →
    Function.Periodic ψ (2*Real.pi) → Function.Periodic f (2*Real.pi) →
    ψ =ᶠ[𝓝 0] (fun _ => 1) → ψ =ᶠ[𝓝 Real.pi] (fun _ => 0) →
    ∀ {P C D Λ : ℝ}, 0 ≤ P → 0 ≤ C → 1 ≤ D → 0 < Λ →
    (∀ k ≤ max (2*(q+1)+2) M, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P) →
    (∀ k ≤ max (2*(q+1)+2) M + 2*j, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖(∫ θ in (-Real.pi)..Real.pi,
        cosineOscillator Λ θ * (ψ θ * inverseStationaryOperator j f θ)) -
          inverseDirectExpansion q j Λ f‖ ≤
      Λ^(-1/2:ℝ)*A*P*C*D^(2*j+2)*(D^2/Λ)^(q+1) +
        B*P*C*D^(2*j+M)/Λ^M := by
  obtain ⟨A,B,hA,hB,hbound⟩ := full_circle_stationary_expansion q M
  let K := max (2*(q+1)+2) M
  let V : ℝ := 2^K*(inverseStationaryExpr j).cost
  have hV : 0 ≤ V := mul_nonneg (by positivity) (AngularDifferentialExpr.cost_nonneg _)
  refine ⟨Real.sqrt (2*Real.pi)*((2*Real.pi^2)^(q+1)/(q.factorial:ℝ))*A*V,
    B*V, by positivity, mul_nonneg hB hV, ?_⟩
  intro ψ f hψ hf hpψ hpf hψ₀ hψπ P C D Λ hP hC hD hΛ hbψ hbf
  have hs := hψ.mul (inverseStationaryOperator_contDiff j hf)
  have hp : Function.Periodic (fun y => ψ y*inverseStationaryOperator j f y) (2*Real.pi) :=
    hpψ.mul ((inverseStationaryExpr j).apply_periodic hpf)
  have hb := cutoff_inverse_derivative_bound j K hψ hf hP hC hD hbψ hbf
  have hCj : 0 ≤ 2^K*P*(inverseStationaryExpr j).cost*C*D^(2*j) := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hP)
        (AngularDifferentialExpr.cost_nonneg _)) hC
    · exact pow_nonneg (zero_le_one.trans hD) _
  have h := hbound hs hp hΛ hCj hD hb
  rw [cutoff_inverse_expansion_eq q j hΛ hψ hf hψ₀ hψπ] at h
  apply h.trans_eq
  rw [mul_assoc, stationary_remainder_factor, quadratic_scale_half hΛ]
  dsimp [V]
  simp only [pow_add]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseStationaryScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem stationary_half_cancel {Λ : ℝ} (hΛ : 0 < Λ) :
    Λ^(1/2:ℝ)*Λ^(-1/2:ℝ) = 1 := by
  rw [← Real.rpow_add hΛ]
  norm_num

theorem inverse_local_remainder_factor (q j : ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    (A P C D : ℝ) :
    (Λ^(1/2:ℝ)*(Λ⁻¹)^j) *
      (Λ^(-1/2:ℝ)*A*P*C*D^(2*j+2)*(D^2/Λ)^(q+1)) =
        A*P*C*D^2*(D^2/Λ)^(q+1+j) := by
  calc
    _ = (Λ^(1/2:ℝ)*Λ^(-1/2:ℝ)) *
        (A*P*C*D^2*((Λ⁻¹)^j*D^(2*j))*(D^2/Λ)^(q+1)) := by
      rw [pow_add D (2*j) 2]; ring
    _ = A*P*C*D^2*(D^2/Λ)^(q+1+j) := by
      rw [stationary_half_cancel hΛ]
      simp only [div_pow, pow_add, pow_mul]
      ring

theorem inverse_nonstationary_remainder_factor (j J : ℕ) (Λ B P C D : ℝ) :
    (Λ^(1/2:ℝ)*(Λ⁻¹)^j) * (B*P*C*D^(2*j+2*J)/Λ^(2*J)) =
      B*P*C*(D^2/Λ)^j*(D^2/Λ)^J*(Λ^(1/2:ℝ)*(Λ^J)⁻¹) := by
  simp only [div_pow, pow_add, pow_mul]
  ring

theorem inverse_nonstationary_remainder_bound (j J : ℕ) (hJ : 1 ≤ J)
    {Λ B P C D : ℝ} (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hC : 0 ≤ C) (hD : 1 ≤ D) (hratio : D^2/Λ ≤ 1) :
    (Λ^(1/2:ℝ)*(Λ⁻¹)^j) * (B*P*C*D^(2*j+2*J)/Λ^(2*J)) ≤
      B*P*C*D^2*(D^2/Λ)^J := by
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hr0 : 0 ≤ D^2/Λ := by positivity
  have hrj : (D^2/Λ)^j ≤ 1 := pow_le_one₀ hr0 hratio
  have hh : Λ^(1/2:ℝ)*(Λ^J)⁻¹ ≤ 1 := by
    calc
      _ ≤ Λ^(1/2:ℝ)*Λ^(-1/2:ℝ) :=
        mul_le_mul_of_nonneg_left (angular_even_decay_half hΛ hJ) (by positivity)
      _ = 1 := stationary_half_cancel hΛp
  have hD2 : 1 ≤ D^2 := one_le_pow₀ hD
  rw [inverse_nonstationary_remainder_factor]
  calc
    _ ≤ B*P*C*1*(D^2/Λ)^J*1 := by gcongr
    _ ≤ B*P*C*D^2*(D^2/Λ)^J := by
      simp only [mul_one]
      exact mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right (by positivity) hD2) (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseStationaryWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

theorem inverseStationaryWeight_nonneg {Λ : ℝ} (hΛ : 0 ≤ Λ) (j : ℕ) :
    0 ≤ inverseStationaryWeight Λ j := by
  unfold inverseStationaryWeight
  positivity

theorem cutoff_inverse_weighted_remainder (n j : ℕ) (hj : j ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧
    ∀ {ψ f : ℝ → ℂ}, ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ f →
    Function.Periodic ψ (2*Real.pi) → Function.Periodic f (2*Real.pi) →
    ψ =ᶠ[𝓝 0] (fun _ => 1) → ψ =ᶠ[𝓝 Real.pi] (fun _ => 0) →
    ∀ {P C D Λ : ℝ}, 0 ≤ P → 0 ≤ C → 1 ≤ D → 1 ≤ Λ → D^2/Λ ≤ 1 →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖(inverseStationaryWeight Λ j:ℂ) *
      ((∫ θ in (-Real.pi)..Real.pi,
        cosineOscillator Λ θ * (ψ θ * inverseStationaryOperator j f θ)) -
          inverseDirectExpansion (n-j) j Λ f)‖ ≤
        A*P*C*D^2*(D^2/Λ)^(n+1) := by
  obtain ⟨A,B,hA,hB,hh⟩ := cutoff_inverse_raw_remainder (n-j) j (2*(n+1))
  refine ⟨A+B, add_nonneg hA hB, ?_⟩
  intro ψ f hψ hf hpψ hpf hψ₀ hψπ P C D Λ hP hC hD hΛ hr hbψ hbf
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hk : max (2*(n-j+1)+2) (2*(n+1)) + 2*j ≤ 4*(n+1)+2 := by omega
  have h := hh hψ hf hpψ hpf hψ₀ hψπ hP hC hD hΛp
    (fun k hk' => hbψ k (by omega)) (fun k hk' => hbf k (hk'.trans hk))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inverseStationaryWeight_nonneg hΛp.le j)]
  apply (mul_le_mul_of_nonneg_left h (inverseStationaryWeight_nonneg hΛp.le j)).trans
  rw [mul_add]
  change (Λ^(1/2:ℝ)*(Λ⁻¹)^j) * _ + (Λ^(1/2:ℝ)*(Λ⁻¹)^j) * _ ≤ _
  rw [inverse_local_remainder_factor _ _ hΛp]
  have he : n-j+1+j = n+1 := by omega
  rw [he]
  have hn := inverse_nonstationary_remainder_bound j (n+1) (by omega)
    hΛ hB hP hC hD hr
  calc
    _ ≤ A*P*C*D^2*(D^2/Λ)^(n+1) + B*P*C*D^2*(D^2/Λ)^(n+1) :=
      add_le_add (le_refl _) hn
    _ = _ := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseCircleAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

theorem inverseCircleIntegral_weighted (n : ℕ) (Λ : ℝ) (ψ f : ℝ → ℂ) :
    inverseCircleIntegral n Λ ψ f =
      ∑ j ∈ Finset.range (n+1), (inverseStationaryWeight Λ j:ℂ) *
        ∫ θ in (-Real.pi)..Real.pi,
          cosineOscillator Λ θ * (ψ θ * inverseStationaryOperator j f θ) := by
  simp [inverseCircleIntegral, inverseStationaryWeight, Finset.mul_sum, mul_assoc]

theorem weighted_inverse_expansions_cancel (n : ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    (∑ j ∈ Finset.range (n+1), (inverseStationaryWeight Λ j:ℂ) *
      inverseDirectExpansion (n-j) j Λ f) = Complex.exp (Complex.I*(Λ:ℂ))*f 0 := by
  have hhalf : ((Λ^(1/2:ℝ):ℝ):ℂ)*((Λ^(-1/2:ℝ):ℝ):ℂ) = 1 := by
    exact_mod_cast stationary_half_cancel hΛ
  conv_rhs => rw [← inverseStationaryOperator_triangle_reverse n ((Λ⁻¹:ℝ):ℂ) hf 0]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have he : n-j+1 = n+1-j := by omega
  simp only [inverseStationaryWeight, Complex.ofReal_mul, Complex.ofReal_pow,
    inverseDirectExpansion, he]
  calc
    _ = Complex.exp (Complex.I*(Λ:ℂ)) *
        (((Λ^(1/2:ℝ):ℝ):ℂ)*((Λ^(-1/2:ℝ):ℝ):ℂ)) *
          (((Λ⁻¹:ℝ):ℂ)^j * ∑ h ∈ Finset.range (n+1-j),
            ((Λ⁻¹:ℝ):ℂ)^h * directStationaryOperator h (inverseStationaryOperator j f) 0) := by ring
    _ = _ := by simp only [hhalf, mul_one, Finset.mul_sum, pow_add, mul_assoc]

theorem inverse_circle_ratio_remainder (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧
    ∀ {ψ f : ℝ → ℂ}, ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ f →
    Function.Periodic ψ (2*Real.pi) → Function.Periodic f (2*Real.pi) →
    ψ =ᶠ[𝓝 0] (fun _ => 1) → ψ =ᶠ[𝓝 Real.pi] (fun _ => 0) →
    ∀ {P C D Λ : ℝ}, 0 ≤ P → 0 ≤ C → 1 ≤ D → 1 ≤ Λ → D^2/Λ ≤ 1 →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖inverseCircleIntegral n Λ ψ f - Complex.exp (Complex.I*(Λ:ℂ))*f 0‖ ≤
      A*P*C*D^2*(D^2/Λ)^(n+1) := by
  choose A hA hbound using fun j : ℕ =>
    cutoff_inverse_weighted_remainder n (min j n) (min_le_right _ _)
  refine ⟨∑ j ∈ Finset.range (n+1), A j, Finset.sum_nonneg (fun j _ => hA j), ?_⟩
  intro ψ f hψ hf hpψ hpf hψ₀ hψπ P C D Λ hP hC hD hΛ hr hbψ hbf
  rw [inverseCircleIntegral_weighted,
    ← weighted_inverse_expansions_cancel n (zero_lt_one.trans_le hΛ) hf,
    ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), A j*P*C*D^2*(D^2/Λ)^(n+1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      simpa only [min_eq_left hj'] using
        hbound j hψ hf hpψ hpf hψ₀ hψπ hP hC hD hΛ hr hbψ hbf
    _ = _ := by simp only [Finset.sum_mul]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseCirclePower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

theorem inverse_circle_stationary_power {c sig T : ℝ} (hc : 0 < c) (hsig : 0 < sig) :
    ∃ n : ℕ, ∀ P C : ℝ, 0 ≤ P → 0 ≤ C → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ψ f : ℝ → ℂ}, ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ f →
    Function.Periodic ψ (2*Real.pi) → Function.Periodic f (2*Real.pi) →
    ψ =ᶠ[𝓝 0] (fun _ => 1) → ψ =ᶠ[𝓝 Real.pi] (fun _ => 0) →
    ∀ {D Λ : ℝ}, 1 ≤ D → ((2:ℝ)^N)^(c*sig) ≤ Λ →
    D ≤ ((2:ℝ)^N)^(1+sig) → D^2/Λ ≤ ((2:ℝ)^N)^(-c*sig) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖Complex.exp (Complex.I*(Λ:ℂ))*f 0 - inverseCircleIntegral n Λ ψ f‖ ≤
      ((2:ℝ)^N)^(-T) := by
  have hcs : 0 < c*sig := mul_pos hc hsig
  obtain ⟨n, hn⟩ := exists_nat_gt ((T+3+2*sig)/(c*sig))
  have hn' : T+3+2*sig < (n:ℝ)*(c*sig) := (div_lt_iff₀ hcs).mp hn
  have hexp : 2+2*sig-c*sig*((n+1:ℕ):ℝ) ≤ -T-1 := by push_cast; nlinarith
  obtain ⟨A,hA,hbound⟩ := inverse_circle_ratio_remainder n
  refine ⟨n, ?_⟩
  intro P C hP hC
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by norm_num : (0:ℝ)<1) (A*P*C)
  refine ⟨N₀, ?_⟩
  intro N hN ψ f hψ hf hpψ hpf hψ₀ hψπ D Λ hD hlower hupper hratio hbψ hbf
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hRp : 0 < (2:ℝ)^N := by positivity
  have hΛ : 1 ≤ Λ := (Real.one_le_rpow hR hcs.le).trans hlower
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hr : D^2/Λ ≤ 1 := hratio.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hR (by nlinarith))
  have hpow : D^2*(D^2/Λ)^(n+1) ≤ ((2:ℝ)^N)^(-T-1) :=
    (stationary_slack_power hR (zero_le_one.trans hD) hΛp hupper hratio (n+1)).trans
      (Real.rpow_le_rpow_of_exponent_le hR hexp)
  have hconst : A*P*C ≤ (2:ℝ)^N := by simpa using hN₀ N hN
  rw [norm_sub_rev]
  apply (hbound hψ hf hpψ hpf hψ₀ hψπ hP hC hD hΛ hr hbψ hbf).trans
  calc
    _ = (A*P*C)*(D^2*(D^2/Λ)^(n+1)) := by ring
    _ ≤ (2:ℝ)^N*((2:ℝ)^N)^(-T-1) :=
      mul_le_mul hconst hpow (by positivity) hRp.le
    _ = _ := by
      conv_lhs => arg 1; rw [← Real.rpow_one ((2:ℝ)^N)]
      rw [← Real.rpow_add hRp]
      congr 1
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedCircleIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

 theorem rotated_circle_integral (Λ θ₀ : ℝ) {f : ℝ → ℂ}
    (hp : Function.Periodic f (2*Real.pi)) :
    (∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ (θ-θ₀)*f θ) =
      ∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ*f (θ+θ₀) := by
  let G : ℝ → ℂ := fun θ => cosineOscillator Λ θ*f (θ+θ₀)
  have hG : Function.Periodic G (2*Real.pi) := by
    intro θ
    have he : θ+2*Real.pi+θ₀ = (θ+θ₀)+2*Real.pi := by ring
    simp only [G,cosineOscillator_periodic Λ θ,he,hp (θ+θ₀)]
  have he : (fun θ => cosineOscillator Λ (θ-θ₀)*f θ) = fun θ => G (θ-θ₀) := by
    funext θ
    simp only [G, sub_add_cancel]
  rw [he,intervalIntegral.integral_comp_sub_right]
  have hh := hG.intervalIntegral_add_eq (-Real.pi-θ₀) (-Real.pi)
  have ha : -Real.pi-θ₀+2*Real.pi = Real.pi-θ₀ := by ring
  have hb : -Real.pi+2*Real.pi = Real.pi := by ring
  simpa only [ha,hb] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedInverseCircle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

theorem rotatedInverseCircleIntegral_eq (n : ℕ) (Λ θ₀ : ℝ) {ψ f : ℝ → ℂ}
    (hpψ : Function.Periodic ψ (2*Real.pi)) (hpf : Function.Periodic f (2*Real.pi)) :
    rotatedInverseCircleIntegral n Λ θ₀ ψ f =
      inverseCircleIntegral n Λ (fun θ => ψ (θ+θ₀)) (fun θ => f (θ+θ₀)) := by
  unfold rotatedInverseCircleIntegral inverseCircleIntegral
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hp : Function.Periodic (fun θ => ψ θ * inverseStationaryOperator j f θ) (2*Real.pi) :=
    hpψ.mul ((inverseStationaryExpr j).apply_periodic hpf)
  rw [rotated_circle_integral Λ θ₀ hp]
  simp only [inverseStationaryOperator, AngularDifferentialExpr.apply_shift]

theorem shifted_periodic {f : ℝ → ℂ} {a : ℝ} (hf : Function.Periodic f a) (b : ℝ) :
    Function.Periodic (fun x => f (x+b)) a := by
  intro x
  change f (x+a+b) = f (x+b)
  rw [show x+a+b = (x+b)+a by ring, hf]

theorem shifted_germ {f g : ℝ → ℂ} {a b : ℝ} (h : f =ᶠ[𝓝 (a+b)] g) :
    (fun x => f (x+b)) =ᶠ[𝓝 a] (fun x => g (x+b)) := by
  exact h.comp_tendsto
    ((show Continuous (fun x : ℝ => x+b) from continuous_id.add continuous_const).continuousAt)

theorem rotated_inverse_circle_power_oai {c sig T : ℝ} (hc : 0 < c) (hsig : 0 < sig) :
    ∃ n : ℕ, ∀ P C : ℝ, 0 ≤ P → 0 ≤ C → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ψ f : ℝ → ℂ}, ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ f →
    Function.Periodic ψ (2*Real.pi) → Function.Periodic f (2*Real.pi) →
    ∀ θ₀ : ℝ, ψ =ᶠ[𝓝 θ₀] (fun _ => 1) → ψ =ᶠ[𝓝 (θ₀+Real.pi)] (fun _ => 0) →
    ∀ {D Λ : ℝ}, 1 ≤ D → ((2:ℝ)^N)^(c*sig) ≤ Λ →
    D ≤ ((2:ℝ)^N)^(1+sig) → D^2/Λ ≤ ((2:ℝ)^N)^(-c*sig) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖Complex.exp (Complex.I*(Λ:ℂ))*f θ₀ - rotatedInverseCircleIntegral n Λ θ₀ ψ f‖ ≤
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,hn⟩ := inverse_circle_stationary_power (T := T) hc hsig
  refine ⟨n, ?_⟩
  intro P C hP hC
  obtain ⟨N₀,hN₀⟩ := hn P C hP hC
  refine ⟨N₀, ?_⟩
  intro N hN ψ f hψ hf hpψ hpf θ₀ hψ₀ hψπ D Λ hD hlower hupper hratio hbψ hbf
  have hzero : (fun θ => ψ (θ+θ₀)) =ᶠ[𝓝 0] (fun _ => 1) :=
    shifted_germ (a := 0) (b := θ₀) (f := ψ) (g := fun _ => 1) (by simpa using hψ₀)
  have hpi : (fun θ => ψ (θ+θ₀)) =ᶠ[𝓝 Real.pi] (fun _ => 0) :=
    shifted_germ (a := Real.pi) (b := θ₀) (f := ψ) (g := fun _ => 0)
      (by simpa only [add_comm] using hψπ)
  rw [rotatedInverseCircleIntegral_eq n Λ θ₀ hpψ hpf]
  simpa only [zero_add] using hN₀ N hN
    (ψ := fun θ => ψ (θ+θ₀)) (f := fun θ => f (θ+θ₀))
    (hψ.comp (contDiff_id.add contDiff_const)) (hf.comp (contDiff_id.add contDiff_const))
    (shifted_periodic hpψ θ₀) (shifted_periodic hpf θ₀) hzero hpi
    hD hlower hupper hratio
    (fun k hk x => by rw [iteratedDeriv_comp_add_const]; exact hbψ k hk _)
    (fun k hk x => by rw [iteratedDeriv_comp_add_const]; exact hbf k hk _)

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.rotated_inverse_circle_power_oai := @OAI.PlanarFalconer.rotated_inverse_circle_power_oai
