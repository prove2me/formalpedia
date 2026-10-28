-- Prove2me | solution 1 for OAI.CoordinateSweeps.conditional_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:32:11.276101+00:00
-- url     : https://prove2.me/submissions/2d909249-6132-41fb-8ad5-6dff05717254

import Mathlib
import Definitions.Def_CoordinateSweeps
import Definitions.Def_OAIQ56Cs000
import Theorems.Thm_OAI_CoordinateSweeps_all_grid_moment

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Grid
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.Holes.columnChoicesFintype _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeColumnLocalChoices _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeRowLocalChoices _root_.OAI.CoordinateSweeps.Grid.Holes.rowChoicesFintype _root_.OAI.CoordinateSweeps.Grid.single_line_unique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps

/- A probability law on a finite sample space, with real-valued masses. -/

namespace Grid

theorem choiceWeight_pos (G : Grid) {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1)
    (ω : G.Choices) : 0 < G.choiceWeight z ω := by
  apply Finset.prod_pos
  intro j _
  apply Finset.prod_pos
  intro L _
  apply add_pos_of_pos_of_nonneg
  · apply mul_pos (sub_pos.mpr hz')
    exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  · exact mul_nonneg hz ((binaryLaw (G.bits j)).nonneg (ω j L))

end Grid

end CoordinateSweeps

end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Matrix_TensorMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps

theorem trace_moment_nonneg {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (q : ℕ) :
    0 ≤ (Matrix.trace ((A.conjTranspose * A)^q)).re :=
  ((Matrix.posSemidef_conjTranspose_mul_self A).pow q).trace_nonneg.1

end CoordinateSweeps
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Conditioning
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeColumnLocalChoices _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeRowLocalChoices _root_.OAI.CoordinateSweeps.Grid.single_line_unique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

noncomputable section
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps

namespace Grid.Holes

variable {G : Grid} {h : ℕ}

/- Average of the remaining random bijection, conditioned on the entire paths,
not only endpoints. The reference affects only unitary identifications. -/

theorem conditionalMoment_nonneg (H : G.Holes h) (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) (q : ℕ) :
    0 ≤ schattenMoment q (H.conditionalAverage hf z ρ) :=
  trace_moment_nonneg _ _

end Grid.Holes

/- Source constants a=1/100, c0=e0=a/100. -/

end CoordinateSweeps

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_SparseBound
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.single_line_unique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
universe u v
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators
open Filter Asymptotics
namespace CoordinateSweeps.SparseScalar
lemma pow_two_exp (k : ℕ) : (2:ℝ)^k=Real.exp ((k:ℝ)*Real.log 2) := by
  rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
lemma eventually_power_gt (ε C : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, C < s^ε := (tendsto_rpow_atTop hε).eventually (eventually_gt_atTop C)
lemma eventually_log_le_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, 1 < s ∧ Real.log s ≤ s^ε := by
  have hh := (isLittleO_log_rpow_rpow_atTop 1 hε).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with s hs h1
  simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg h1.le),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) ε),one_mul] using And.intro h1 hs

/- All scalar scale requirements for the sparse proof can be imposed before
R and the finite real perturbation interval are fixed. -/
lemma eventually_sparse_requirements :
    ∀ᶠ s : ℝ in atTop, 1 < s ∧
      Real.log s ≤ s^(theta/4) ∧ 2 ≤ s^(theta/4) ∧
      (B0+1 : ℝ) ≤ s^(theta/2) ∧
      4/s^(1/(4*(B0:ℝ))) ≤ theta/(64*B0) ∧
      Real.log (2*(B0:ℝ)+1)+Real.log 2 ≤ xi*Real.log s ∧
      Real.log 2 ≤ xi*Real.log s/8 := by
  have h1 := eventually_log_le_power (theta/4) (by norm_num [theta])
  have h2 := eventually_power_gt (theta/4) 2 (by norm_num [theta])
  have h3 := eventually_power_gt (theta/2) (B0+1) (by norm_num [theta])
  have h4 := eventually_power_gt (1/(4*B0)) (256*B0/theta) (by norm_num [B0])
  have ht : Tendsto (fun s : ℝ => xi*Real.log s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num [xi] : 0 < xi)).mpr Real.tendsto_log_atTop
  have h5 := ht.eventually (eventually_ge_atTop (Real.log (2*(B0:ℝ)+1)+Real.log 2))
  have h6 := ht.eventually (eventually_ge_atTop (8*Real.log 2))
  filter_upwards [h1,h2,h3,h4,h5,h6] with s hs h₂ h₃ h₄ h₅ h₆
  refine ⟨hs.1,hs.2,h₂.le,h₃.le,?_,h₅,by linarith⟩
  have hp : 0 < s^(1/(4*(B0:ℝ))) := Real.rpow_pos_of_pos (by linarith [hs.1]) _
  apply (div_le_iff₀ hp).mpr
  have hc : 0 < theta/(64*(B0:ℝ)) := by norm_num [theta,B0]
  have hh := mul_le_mul_of_nonneg_left h₄.le hc.le
  norm_num [theta,B0] at hh ⊢
  nlinarith

/- Arithmetic behind the many-coordinate HS bound, with its full literal
prefactor. The inputs are scalar size bounds derived from the allowed grid. -/
end CoordinateSweeps.SparseScalar

namespace CoordinateSweeps.Grid
lemma size_pos (G : Grid) : 0 < G.size := by unfold size; positivity
lemma log_size (G : Grid) : Real.log G.size = ∑ j, (G.bits j : ℝ)*Real.log 2 := by
  simp only [size,Nat.cast_prod,Nat.cast_pow,Nat.cast_ofNat]
  rw [Real.log_prod (fun j _ => by positivity)]
  simp only [Real.log_pow]
lemma log_size_lower (G : Grid) {r : ℕ} (hG : G.Allowed r) :
    (G.b : ℝ)*((r : ℝ)*Real.log 2) ≤ Real.log G.size := by
  rw [G.log_size]
  calc
    _ = ∑ _ : Fin G.b, (r : ℝ)*Real.log 2 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
      (by exact_mod_cast (hG j).1) (Real.log_nonneg (by norm_num)))

end CoordinateSweeps.Grid

namespace CoordinateSweeps.SparseScalar
lemma eventually_prefactor_small : ∀ᶠ s : ℝ in atTop,
    uniformRate ≤ xi*Real.log s/16 := by
  have ht : Tendsto (fun s : ℝ => xi*Real.log s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num [xi] : 0 < xi)).mpr Real.tendsto_log_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (16*uniformRate))] with s hs
  linarith
end CoordinateSweeps.SparseScalar

namespace CoordinateSweeps.Grid
/- Every choice mass is a real polynomial. No conditional law is extended to complex z. -/
lemma continuous_choiceWeight (G : Grid) (ω : G.Choices) : Continuous (fun z : ℝ => G.choiceWeight z ω) := by
  unfold choiceWeight
  fun_prop
/- Event-level l1 distance, independent of the representation and therefore
suitable for a single bounded-grid perturbation interval. -/
lemma eventMass_zero_pos (G : Grid) (E : Finset G.Choices) (hE : E.Nonempty) :
    0 < ∑ ω ∈ E, G.choiceWeight 0 ω := by
  exact Finset.sum_pos (fun _ _ => G.choiceWeight_pos le_rfl (by norm_num) _) hE
lemma continuousAt_eventDistance_zero (G : Grid) (E : Finset G.Choices) (hE : E.Nonempty) :
    ContinuousAt (G.eventDistance E) 0 := by
  unfold eventDistance
  apply tendsto_finsetSum
  intro ω hω
  apply ContinuousAt.abs
  apply ContinuousAt.sub _ continuousAt_const
  apply ContinuousAt.div (G.continuous_choiceWeight ω).continuousAt
  · exact (continuous_finsetSum _ (fun v _ => G.continuous_choiceWeight v)).continuousAt
  · exact (G.eventMass_zero_pos E hE).ne'
lemma eventually_eventDistance_small (G : Grid) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in nhds (0:ℝ), ∀ E : Finset G.Choices, E.Nonempty → G.eventDistance E z < ε := by
  have hE : ∀ E : Finset G.Choices, ∀ᶠ z in nhds (0:ℝ), E.Nonempty → G.eventDistance E z < ε := by
    intro E
    by_cases hn : E.Nonempty
    · have hh := (G.continuousAt_eventDistance_zero E hn).eventually (gt_mem_nhds (by simpa using hε : G.eventDistance E 0<ε))
      filter_upwards [hh] with z hz
      exact fun _ => hz
    · exact Filter.Eventually.of_forall (fun _ h => (hn h).elim)
  exact Filter.eventually_all.mpr hE
end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid
/- Literal finite parameter space of bounded ordered grids; no model of
irreducibles or of conditioned complex measures is involved. -/
theorem bounded_event_interval (B r : ℕ) (ε : Grid → ℝ) (hε : ∀ G, 0 < ε G) :
    ∃ zStar : ℝ, 0 < zStar ∧ zStar ≤ 1/2 ∧
      ∀ G : Grid, G.b ≤ B → (∀ j, G.bits j ≤ 2*r) →
      ∀ z ∈ Set.Icc 0 zStar, ∀ E : Finset G.Choices, E.Nonempty → G.eventDistance E z < ε G := by
  let : Fintype (BoundedCode B r) := Fintype.ofFinite _
  have hall : ∀ᶠ z in nhds (0:ℝ), ∀ x : BoundedCode B r,
      ∀ E : Finset x.grid.Choices, E.Nonempty → x.grid.eventDistance E z < ε x.grid := by
    exact Filter.eventually_all.mpr (fun x => x.grid.eventually_eventDistance_small (hε x.grid))
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨min (δ/2) (1/2),lt_min (by linarith) (by norm_num),min_le_right _ _,?_⟩
  intro G hb hbits z hz E hE
  have hdist : dist z (0:ℝ)<δ := by
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hz.1]
    have hh := hz.2.trans (min_le_left (δ/2) (1/2))
    linarith
  have hh := hd hdist (G.boundedCode B r hb hbits)
  cases G
  exact hh E hE
end CoordinateSweeps.Grid
end
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Scales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Work on the genuinely missing main statements of the pinned manuscript.
All definitions are finite and use the source's ordinary probability and trace
normalizations. No result of the manuscript is assumed.
-/

noncomputable section
open scoped BigOperators
open Filter Asymptotics
namespace CoordinateSweeps
-- Literal source constants (ConditionalTarget:509--514), not new hypotheses.

namespace ScalarInduction
/- A fixed polynomial logarithmic loss is uniformly negligible compared
with any strictly larger power, the quantitative choice needed in06. -/
lemma eventually_log_power_bound (u v r C : ℝ) (huv : u < v) (hC : 0 < C) :
    ∀ᶠ s : ℝ in atTop, 0 < s ∧ s^u*(Real.log s)^r ≤ C*s^v := by
  have hh := (isLittleO_log_rpow_rpow_atTop r (sub_pos.mpr huv)).bound hC
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with s hs hs1
  have hs0 : 0 < s := lt_trans zero_lt_one hs1
  have hl : 0 ≤ Real.log s := Real.log_nonneg hs1.le
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hl r),
    abs_of_nonneg (Real.rpow_nonneg hs0.le (v-u))] at hs
  refine ⟨hs0,?_⟩
  have hm := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hs0.le u)
  calc
    _ ≤ s^u*(C*s^(v-u)) := hm
    _ = C*s^v := by rw [← mul_assoc,mul_comm (s^u) C,mul_assoc,← Real.rpow_add hs0]; congr 2; ring

lemma eventually_constant_le_power (ε C : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, C ≤ s^ε :=
  (tendsto_atTop.1 (tendsto_rpow_atTop hε)) C

lemma eventually_absorb_hook (q : ℕ) :
    ∀ᶠ s : ℝ in atTop, 1 < s ∧
      (((2*q+1 : ℕ):ℝ)*4+82*c0)*2*s^((4:ℝ)/5+2*a)*Real.log (s+1) ≤ s^((9:ℝ)/10) := by
  let C : ℝ := (((2*q+1 : ℕ):ℝ)*4+82*c0)*4
  have hC : 0 < C := by dsimp [C,c0,a]; positivity
  have hp := eventually_log_power_bound ((4:ℝ)/5+2*a) ((9:ℝ)/10) 1 (1/C)
    (by norm_num [a]) (by positivity)
  filter_upwards [hp,eventually_ge_atTop (2:ℝ)] with s hs hs2
  refine ⟨by linarith,?_⟩
  have hl : Real.log (s+1) ≤ 2*Real.log s := by
    calc
      Real.log (s+1) ≤ Real.log (s*s) :=
        Real.log_le_log (by linarith) (by nlinarith)
      _ = 2*Real.log s := by rw [Real.log_mul hs.1.ne' hs.1.ne']; ring
  have hm := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ (((2*q+1 : ℕ):ℝ)*4+82*c0)*2*s^((4:ℝ)/5+2*a) by
      dsimp [c0,a]; positivity)
  have hh := mul_le_mul_of_nonneg_left hs.2 hC.le
  simp only [Real.rpow_one] at hh
  have hc : C*(1/C)=1 := mul_one_div_cancel hC.ne'
  calc
    _ ≤ (((2*q+1 : ℕ):ℝ)*4+82*c0)*2*s^((4:ℝ)/5+2*a)*(2*Real.log s) := hm
    _ = C*(s^((4:ℝ)/5+2*a)*Real.log s) := by dsimp [C]; ring
    _ ≤ s^((9:ℝ)/10) := by simpa only [← mul_assoc,hc,one_mul] using hh

lemma eventually_absorb_removed :
    ∀ᶠ s : ℝ in atTop, 1 < s ∧
      s^((9:ℝ)/10)+s^(1-a/2)*Real.log s ≤ s^(1-a/4)/(20*Real.sqrt (Real.log s)) := by
  have h1 := eventually_log_power_bound ((9:ℝ)/10) (1-a/4) ((1:ℝ)/2) (1/40)
    (by norm_num [a]) (by norm_num)
  have h2 := eventually_log_power_bound (1-a/2) (1-a/4) ((3:ℝ)/2) (1/40)
    (by norm_num [a]) (by norm_num)
  filter_upwards [h1,h2,eventually_gt_atTop (1:ℝ)] with s h₁ h₂ hs
  refine ⟨hs,?_⟩
  have hlog : 0 < Real.log s := Real.log_pos hs
  have hroot : 0 < Real.sqrt (Real.log s) := Real.sqrt_pos.mpr hlog
  have he : Real.log s*Real.sqrt (Real.log s)=(Real.log s)^((3:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow]
    nth_rw 1 [← Real.rpow_one (Real.log s)]
    rw [← Real.rpow_add hlog]
    norm_num
  rw [← Real.sqrt_eq_rpow] at h₁
  apply (le_div_iff₀ (by positivity : 0 < 20*Real.sqrt (Real.log s))).mpr
  have hh : s^((9:ℝ)/10)*Real.sqrt (Real.log s)+
    s^(1-a/2)*Real.log s*Real.sqrt (Real.log s) ≤ (1/20)*s^(1-a/4) := by
    rw [mul_assoc,he]
    linarith [h₁.2,h₂.2]
  nlinarith

/- Scalar endgame after the *actual* induced placement-cycle estimate.
All representation/path data enter only through their already derived
entropies, multiplicity and cost inequalities. -/
end ScalarInduction
end CoordinateSweeps
end

noncomputable section
open scoped BigOperators
open Filter Asymptotics
namespace CoordinateSweeps.ScalarInduction
lemma eventually_mainSizeReady (q : ℕ) : ∀ᶠ s : ℝ in atTop, MainSizeReady q s := by
  have hpow := eventually_constant_le_power (a/4-1/1600) 100004 (by norm_num [a])
  filter_upwards [hpow,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_absorb_hook q,eventually_absorb_removed] with s hp hL hh hr
  refine ⟨hL,?_,hh.2,hr.2⟩
  calc
    _ ≤ s^(a/4-1/1600)*s^(1-a/4) := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (by linarith [hh.1]) _)
    _ = _ := by rw [←Real.rpow_add (by linarith [hh.1] : 0 < s)]; congr 1; ring

end CoordinateSweeps.ScalarInduction

end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_BaseCase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Work on the genuinely missing main statements of the pinned manuscript.
All definitions are finite and use the source's ordinary probability and trace
normalizations. No result of the manuscript is assumed.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps

lemma exists_scaleLarge : ∃ r, ScaleLarge r := by
  let B : ℝ := max ((2/e0)^2) (4/e0)
  obtain ⟨r,hr⟩ := exists_nat_gt (max 1 (B/Real.log 2))
  have hr1 : (1 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hrB : B/Real.log 2 < r := lt_of_le_of_lt (le_max_right _ _) hr
  have hh : B ≤ (r : ℝ)*Real.log 2 :=
    ((div_lt_iff₀ (Real.log_pos (by norm_num))).mp hrB).le
  refine ⟨r,?_,?_,?_⟩
  · have hnat : 1 < r := by exact_mod_cast hr1
    omega
  · exact (le_max_left _ _).trans hh
  · exact (le_max_right _ _).trans hh

lemma logMoment_le_of_le {t u : ℝ} (ht : 0 ≤ t) (hu : 0 < u) (htu : t ≤ u) :
    logMoment t ≤ (Real.log u : EReal) := by
  by_cases ht0 : t=0
  · simp [logMoment,ht0]
  · rw [logMoment,ite_eq_right ht0]
    exact_mod_cast (Real.log_le_log_iff (lt_of_le_of_ne ht (Ne.symm ht0)) hu).mpr htu

end CoordinateSweeps

namespace CoordinateSweeps

lemma baseZeta_pos (r : ℕ) : 0 < baseZeta r := by
  have h := baseWidth_one_le r
  unfold baseZeta
  positivity

end CoordinateSweeps

end

open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Perturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
All definitions are finite and use the source's ordinary probability and trace
normalizations.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

/-! The alternating placement kernel from 04-sparse:eq7.
Endpoints below need not be injections; invalid specifications have probability
zero automatically. On valid endpoint placements this is exactly the source Q. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/- Necessary shared-line polynomial expansion for the sparse conditional main.
A variable names a LINE, not a particle. The tensor moment functional is merely
linear, never multiplicative when two factors use the same line. -/
noncomputable section
open scoped BigOperators
open MvPolynomial

/- The analytic light-line obligation 04-sparse.tex (11).  The distribution
is exactly Mathlib's Gamma(shape, unit rate). -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators

/- Finite subset rearrangements needed for the actual good/non-good path
alternation in source04:eq10. -/
noncomputable section
open scoped BigOperators

/- Required top-placement compression for the conditional main. The top space
is the annihilator of all functions depending on a proper set of coordinates.
This is the exact top level used in source04 around eq7. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

noncomputable section
universe u v
open scoped ComplexConjugate

noncomputable section
open scoped BigOperators

open scoped Matrix.Norms.L2Operator

noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace CoordinateSweeps.SparseScalar
lemma eventually_sizeReady : ∀ᶠ s : ℝ in atTop, SizeReady s := by
  have hp := eventually_power_gt xi 8 (by norm_num [xi])
  filter_upwards [eventually_sparse_requirements,eventually_prefactor_small,hp,eventually_ge_atTop (2:ℝ)]
    with s hs hf hp h2
  refine ⟨h2,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,?_,?_,hf,hs.2.2.2.2.2.2⟩
  · simpa only [add_comm] using hs.2.2.2.2.2.1
  · rw [Real.rpow_neg (by linarith : 0 ≤ s)]
    simpa only [one_div] using (inv_le_inv₀ (by linarith : 0 < s^xi) (by norm_num : (0:ℝ)<8)).mpr hp.le
lemma eventually_scaleReady : ∀ᶠ r : ℕ in atTop, ScaleReady r := by
  obtain ⟨S,hS⟩ := eventually_atTop.mp eventually_sizeReady
  have ht : Tendsto (fun r : ℕ => (r:ℝ)*Real.log 2) atTop atTop :=
    (tendsto_mul_const_atTop_of_pos (Real.log_pos (by norm_num))).mpr tendsto_natCast_atTop_atTop
  have h1 := ht.eventually (eventually_ge_atTop (1:ℝ))
  have h2 := ht.eventually (eventually_ge_atTop ((3*Real.log 2+2*(K0+1+Real.log 4))*8/theta))
  have hp : Tendsto (fun r : ℕ => (2:ℝ)^r) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [h1,h2,hp.eventually (eventually_ge_atTop S),eventually_ge_atTop (2:ℕ)] with r hr1 hr2 hrS hr
  refine ⟨hr,hr1,?_,fun s hs => hS s (hrS.trans hs)⟩
  have hh := mul_le_mul_of_nonneg_right hr2 (by norm_num [theta] : 0 ≤ theta)
  have hth : theta ≠ 0 := by norm_num [theta]
  rw [div_mul_cancel₀ _ hth] at hh
  nlinarith
/- Positive slack used by the uniform finite real perturbation. -/
lemma slack_pos (s : ℝ) : 0 < slack s := by
  unfold slack
  split_ifs with hs
  · exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (sub_pos.mpr
      (Real.one_lt_rpow hs (by norm_num [rho])))
  · norm_num
end CoordinateSweeps.SparseScalar
namespace CoordinateSweeps.Grid
open SparseScalar
lemma pow_r_le_size (G : Grid) {r : ℕ} (hG : G.Allowed r) : (2:ℝ)^r ≤ G.size := by
  have hb : (1:ℝ)≤G.b := by exact_mod_cast G.positive
  have hl := (le_mul_of_one_le_left (by positivity : 0≤(r:ℝ)*Real.log 2) hb).trans (G.log_size_lower hG)
  rw [pow_two_exp]
  exact (Real.exp_le_exp.mpr hl).trans_eq (Real.exp_log (by exact_mod_cast G.size_pos))
end CoordinateSweeps.Grid

namespace CoordinateSweeps
lemma exists_sparsePerturb (r : ℕ) : ∃ zStar, SparsePerturb r zStar := by
  obtain ⟨δ,hδ,hδh,hd⟩ := Grid.bounded_event_interval SparseScalar.B0 r
    (fun G => SparseScalar.slack G.size) (fun _ => SparseScalar.slack_pos _)
  refine ⟨min δ (baseZeta r),lt_min hδ (baseZeta_pos r),min_le_right _ _,?_⟩
  intro G hb hG z hz E hE
  exact hd G hb (fun j => (hG j).2) z ⟨hz.1,hz.2.trans (min_le_left _ _)⟩ E hE
end CoordinateSweeps

end
end
end
end
end
end
end
end
end

open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Matrix.Norms.L2Operator
namespace CoordinateSweeps
lemma logMoment_le_of_moment_le_exp {t B : ℝ} (ht : 0≤t) (h : t≤Real.exp B) :
    logMoment t ≤ (B:EReal) := by
  simpa only [Real.log_exp] using logMoment_le_of_le ht (Real.exp_pos B) h
end CoordinateSweeps

namespace CoordinateSweeps
open Filter
lemma eventually_scaleLarge : ∀ᶠ r : ℕ in atTop, ScaleLarge r := by
  obtain ⟨r₀,hr₀⟩ := exists_scaleLarge
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have hh : (r₀:ℝ)*Real.log 2 ≤ (r:ℝ)*Real.log 2 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (Real.log_nonneg (by norm_num))
  exact ⟨hr₀.1.trans hr,hr₀.2.1.trans hh,hr₀.2.2.trans hh⟩
lemma exists_main_scale : ∃ r : ℕ, ScaleLarge r ∧ SparseScalar.ScaleReady r ∧
    ∀ G : Grid, G.Allowed r → ScalarInduction.MainSizeReady SparseScalar.q G.size := by
  obtain ⟨S,hS⟩ := eventually_atTop.mp (ScalarInduction.eventually_mainSizeReady SparseScalar.q)
  have hp : Tendsto (fun r : ℕ => (2:ℝ)^r) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hall : ∀ᶠ r : ℕ in atTop, ScaleLarge r ∧ SparseScalar.ScaleReady r ∧ S≤(2:ℝ)^r := by
    filter_upwards [eventually_scaleLarge,SparseScalar.eventually_scaleReady,
      hp.eventually (eventually_ge_atTop S)] with r h1 h2 h3
    exact ⟨h1,h2,h3⟩
  obtain ⟨r,hr,hs,ht⟩ := hall.exists
  exact ⟨r,hr,hs,fun G hG => hS G.size (ht.trans (G.pow_r_le_size hG))⟩

/-- Manuscript03 thm:conditional / ac:main, with c₀=e₀=a/100,
a=1/100, natural logarithms, unnormalized integer Schatten moments,
all feasible disjoint paths (including none and all), and log(0)=−∞. -/
theorem conditional_main_oai : ConditionalMain := by
  obtain ⟨r,hr,hrS,hS⟩ := exists_main_scale
  obtain ⟨zStar,hζ⟩ := exists_sparsePerturb r
  have hq : 1≤SparseScalar.q := by norm_num [SparseScalar.q]
  refine ⟨r,SparseScalar.q,zStar,hr.1,hq,hζ.1,hζ.2.1.trans (baseZeta_le_half r),?_⟩
  intro G hG h H hf z hz σ
  exact logMoment_le_of_moment_le_exp (H.conditionalMoment_nonneg hf z σ SparseScalar.q)
    (all_grid_moment hr hrS hS hζ hz G hG h H hf σ)
end CoordinateSweeps

end OAI
end

theorem solution : type_of% @OAI.CoordinateSweeps.conditional_main_oai := @OAI.CoordinateSweeps.conditional_main_oai
