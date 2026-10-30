-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_vertex_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:15:34.286241+00:00
-- url     : https://prove2.me/submissions/9342c54b-cec9-41d3-9942-fdb2a4556851

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_AngularGrid_eventually_source_supported_selector_plane_integral
import Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_eventually_assigned_parent_marked_path_bound

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_EnvelopeSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Cauchy--Schwarz for actual packet synthesis, followed by
polynomially weighted whole-line energy bounds. -/

noncomputable section
open MeasureTheory
open FourierTransform
open scoped BigOperators
open scoped FourierTransform

namespace LipschitzHilbert

theorem packetSynthesis_apply {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (x : ℝ) :
    packetSynthesis c f x = ∑ i, c i * f i x := by
  simp only [packetSynthesis, sum_apply, smul_apply, smul_eq_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SequenceExponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional exponent comparison used in the Fourier gain. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem phaseConstant_pos : 0 < phaseConstant := by norm_num [phaseConstant]

omit [Fintype ι] in
theorem phaseParameter_range {D : ℝ} (hD : 1 ≤ D) :
    0 < phaseConstant / Real.log (2 * D) ∧
      phaseConstant / Real.log (2 * D) ≤ 1 / 3 := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 * D) := by
    have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    exact htwo.trans (Real.log_le_log (by norm_num) (by linarith))
  have hpos : 0 < Real.log (2 * D) := by linarith
  refine ⟨div_pos phaseConstant_pos hpos, (div_le_iff₀ hpos).2 ?_⟩
  have hc : phaseConstant ≤ (1 / 6 : ℝ) := by norm_num [phaseConstant]
  linarith

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual decaying top weights and their motion along a reference line. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem radius_nonnegative (T : SlopeBox) (z : ℝ × ℝ) : 0 ≤ T.radius z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem weight_pos (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) (z : ℝ × ℝ) :
    0 < T.weight K D z := by
  unfold weight
  have hr := T.radius_nonnegative z
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) D)
    (Real.rpow_pos_of_pos (by positivity) _)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SelectedTopInterval
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the finite band interval with the selected
scale sum, preserving the actual analyzing coefficients. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem planarPacketInterval_eq_selected
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
    (a b : ℕ) (hab : a ≤ b) (x y : ℝ) :
    planarPacketInterval c (fun j u k t s => f j u k t s) a b x y =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => a ≤ j.val ∧ j.val < b),
        vectorPacketSynthesis (c j) (fun u k => f j u k y) x := by
  ext k
  simp only [planarPacketInterval,bandIntervalSignal,WithLp.ofLp_toLp,scalarBandPartial,
    WithLp.ofLp_sum,Finset.sum_apply,vectorPacketSynthesis,packetSynthesis_apply,
    planarPacketBand,Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hja : j.val < a
  · have hjb : j.val < b := hja.trans_le hab
    simp only [hja,hjb,ite_true, if_true,sub_self,not_le.mpr hja,false_and,ite_false, if_false,WithLp.ofLp_zero,Pi.zero_apply]
  · by_cases hjb : j.val < b
    · simp only [hja,hjb,ite_true, if_true,ite_false, if_false,sub_zero,not_lt.mp hja,true_and]
    · simp only [hja,hjb,ite_false, if_false,sub_self,and_false,WithLp.ofLp_zero,Pi.zero_apply]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlicedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From almost-everywhere line estimates to planar estimates, including
the area-preserving coordinates of a fixed reference slope. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem integral_slopeShear (s : ℝ) (f : ℝ × ℝ → ℝ) :
    (∫ z, f (slopeShear s z) ∂volume.prod volume) = ∫ z, f z ∂volume.prod volume :=
  (slopeShear_measurePreserving s).integral_comp (slopeShear s).measurableEmbedding f

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and exact area scaling for the actual decaying top weights. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

theorem planeDivide_apply (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (z : ℝ × ℝ) :
    planeDivide a b ha hb z = (z.1 / a, z.2 / b) := by
  rfl

theorem map_planeDivide (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Measure.map (planeDivide a b ha hb) (volume.prod volume) =
      (ENNReal.ofReal |a| * ENNReal.ofReal |b|) • (volume.prod volume) := by
  have hmap (c : ℝ) (hc : c ≠ 0) :
      Measure.map (fun x : ℝ => x * c⁻¹) volume = ENNReal.ofReal |c| • volume := by
    simpa only [smul_eq_mul, Module.finrank_self, pow_one, inv_inv, mul_comm] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (inv_ne_zero hc))
  change Measure.map (Prod.map (fun x => x * a⁻¹) (fun y => y * b⁻¹)) _ = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) (by fun_prop), hmap a ha, hmap b hb,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

theorem integral_planeDivide (f : ℝ × ℝ → ℝ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∫ z, f (planeDivide a b ha hb z) ∂volume.prod volume) =
      (|a| * |b|) * ∫ z, f z ∂volume.prod volume := by
  rw [← integral_map_equiv (planeDivide a b ha hb), map_planeDivide, integral_smul_measure]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

namespace SlopeBox

theorem normalizedCoordinates_eq (T : SlopeBox) (K : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.normalizedCoordinates K hK z = (T.horizontal z / K, T.transverse z / K) := by
  ext <;> simp [normalizedCoordinates, planeDivide_apply, slopeShear, horizontal, transverse]
  <;> ring

theorem weight_eq_topProfile (T : SlopeBox) (K D : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.weight K D z = 2 ^ D * topProfile D (T.normalizedCoordinates K hK z) := by
  rw [normalizedCoordinates_eq]
  simp only [weight, topProfile, radius, abs_div, abs_of_pos hK, add_div]

/-- Exact area scaling: all dependence on the box and the dilation is
`K² * length * width`, while the remaining integral is a fixed constant. -/
theorem integral_weight (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) :
    (∫ z, T.weight K D z ∂volume.prod volume) =
      (2 ^ D * ∫ z, topProfile D z ∂volume.prod volume) *
        K ^ 2 * T.length * T.width := by
  have heq : T.weight K D = fun z => 2 ^ D *
      ((fun z => topProfile D (planeDivide (K * T.length) (K * T.width)
        (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)) ∘
        slopeShear (-T.slope)) (z - (T.x, T.y)) := by
    funext z
    exact T.weight_eq_topProfile K D hK z
  rw [heq, integral_const_mul, integral_sub_right_eq_self]
  simp only [Function.comp_apply]
  rw [integral_slopeShear (-T.slope) (fun z => topProfile D
    (planeDivide (K * T.length) (K * T.width)
      (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)),
    integral_planeDivide, abs_of_pos (mul_pos hK T.length_pos),
    abs_of_pos (mul_pos hK T.width_pos)]
  ring

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeBoxMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sinc mask in the manuscript's actual slope coordinates, with
parameters fixed uniformly before choosing the finite top family. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
namespace SlopeBox

theorem mask_continuous (T : SlopeBox) (L A : ℝ) : Continuous (T.mask L A) := by
  unfold mask topSincMask sincProductMask horizontal transverse
  apply Continuous.pow
  apply Continuous.mul
  · apply Real.continuous_sinc.comp
    fun_prop
  · apply Real.continuous_sinc.comp
    fun_prop

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translated nested angular grids and their actual eligible-top masses. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace AngularGrid

theorem index_parent (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    g.index (level + 1) slope / (g.branching : ℤ) = g.index level slope := by
  have hG : g.branching ≠ 0 := by have h := g.branching_ge_two; omega
  simpa only [index, pow_succ, mul_assoc] using
    (Int.mul_natCast_floor_div_cancel hG
      (((slope - g.origin) / g.rootWidth) * (g.branching : ℝ) ^ level))

variable {ι X : Type*}

theorem cellTops_subset_parent (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (level : ℕ) (child : ℤ) :
    g.cellTops tops slope precision cutoff (level + 1) child ⊆
      g.cellTops tops slope precision cutoff level (child / (g.branching : ℤ)) := by
  intro i hi
  obtain ⟨hit, hindex, heligible⟩ := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  apply (g.mem_cellTops _ _ _ _ _ _ _).2
  refine ⟨hit, ?_, g.eligible_parent (hp i hit) level heligible⟩
  rw [← g.index_parent level (slope i), hindex]

theorem mass_nonnegative (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 ≤ weight i x)
    (level : ℕ) (cell : ℤ) (x : X) :
    0 ≤ g.mass tops slope precision cutoff weight level cell x :=
  Finset.sum_nonneg fun i _ => hw i x

theorem mass_pos_of_member (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 < weight i x)
    (level : ℕ) (cell : ℤ) (x : X) {i : ι}
    (hi : i ∈ g.cellTops tops slope precision cutoff level cell) :
    0 < g.mass tops slope precision cutoff weight level cell x := by
  classical
  exact (hw i x).trans_le (Finset.single_le_sum (fun j _ => (hw j x).le) hi)

/-- An eligible top supplies a strictly positive summand on its own path. -/
theorem path_mass_pos (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 < weight i x)
    (level : ℕ) (top : ι) (htop : top ∈ tops) (heligible : g.eligible cutoff (precision top) level)
    (x : X) : 0 < g.mass tops slope precision cutoff weight level (g.index level (slope top)) x :=
  g.mass_pos_of_member tops slope precision cutoff weight hw level _ x
    ((g.mem_cellTops _ _ _ _ _ _ _).2 ⟨htop, rfl, heligible⟩)

/-- Every angular mass is a submass of the fixed total top weight. -/
theorem mass_le_total (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 ≤ weight i x)
    (level : ℕ) (cell : ℤ) (x : X) :
    g.mass tops slope precision cutoff weight level cell x ≤ ∑ i ∈ tops, weight i x := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro i _ _
    exact hw i x

/-- Child mass is at most parent mass, with the eligibility restriction
already built into both finite sums. -/
theorem mass_le_parent (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (hw : ∀ i x, 0 ≤ weight i x) (level : ℕ) (child : ℤ) (x : X) :
    g.mass tops slope precision cutoff weight (level + 1) child x ≤
      g.mass tops slope precision cutoff weight level (child / (g.branching : ℤ)) x := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (g.cellTops_subset_parent tops slope precision cutoff hp level child) (fun i _ _ => hw i x)

/-- Along any fixed top's angular path the actual mass is antitone. -/
theorem path_mass_antitone (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (hw : ∀ i x, 0 ≤ weight i x) (top : ι) (x : X) :
    Antitone fun level => g.mass tops slope precision cutoff weight level (g.index level (slope top)) x := by
  apply antitone_nat_of_succ_le
  intro level
  simpa only [g.index_parent] using
    g.mass_le_parent tops slope precision cutoff weight hp hw level (g.index (level + 1) (slope top)) x

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual last eligible angular level exists for every positive
precision. Packet stopping precedes the stopping of its assigned top. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem eligible_iff_le_lastEligible (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hstart : g.eligible cutoff precision 0) (n : ℕ) :
    g.eligible cutoff precision n ↔ n ≤ g.lastEligible cutoff precision hp := by
  let h := g.exists_ineligible cutoff precision hp
  have hfirst : 0 < Nat.find h := by
    by_contra hn
    have hz : Nat.find h = 0 := by omega
    apply Nat.find_spec h
    simpa only [hz] using hstart
  constructor
  · intro hn
    by_contra hle
    have hfind : Nat.find h ≤ n := by
      change ¬n ≤ Nat.find h - 1 at hle
      omega
    exact Nat.find_spec h (g.eligible_of_le hp.le hfind hn)
  · intro hn
    have hlt : n < Nat.find h := by
      change n ≤ Nat.find h - 1 at hn
      omega
    exact Classical.not_not.mp (Nat.find_min h hlt)

theorem eligible_lastEligible (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hstart : g.eligible cutoff precision 0) :
    g.eligible cutoff precision (g.lastEligible cutoff precision hp) :=
  (g.eligible_iff_le_lastEligible cutoff precision hp hstart _).mpr le_rfl

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlopeLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slope-label multiplicity assumption in §2 of the manuscript
gives a uniform number of labels active at a fixed source direction.
This includes vector-valued selectors: taking the union over all bin
components does not increase the count.  The last lemmas split the
active labels at every scale into a fixed finite set of lattice slots. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.SourceSlopeLabels

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

theorem window_card_le (labels : Finset ι) (slope : ι → ℝ)
    {t d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K) :
    (window labels slope t d radius).card ≤ (2 * K + 1) * M := by
  classical
  let active := window labels slope t d radius
  let bin : ι → ℤ := fun i => ⌊(slope i - t) / d⌋
  let bins : Finset ℤ := Finset.Icc (-(K : ℤ)) K
  have hmaps : (active : Set ι).MapsTo bin bins := by
    intro i hi
    have hwin : |slope i - t| ≤ radius * d := (Finset.mem_filter.mp hi).2
    have habs : |slope i - t| ≤ (K : ℝ) * d :=
      hwin.trans (mul_le_mul_of_nonneg_right hK hd.le)
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    have hlow : -(K : ℝ) ≤ (slope i - t) / d := by
      apply (le_div_iff₀ hd).mpr
      linarith
    have hupp : (slope i - t) / d < (K : ℝ) + 1 := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    exact Finset.mem_Icc.mpr ⟨Int.le_floor.mpr (by simpa using hlow),
      Int.floor_le_iff.mpr (by simpa using hupp)⟩
  have hfiber (b : ℤ) : (active.filter (fun i => bin i = b)).card ≤ M := by
    apply (Finset.card_le_card (show active.filter (fun i => bin i = b) ⊆
      labels.filter (fun i => t + (b : ℝ) * d ≤ slope i ∧
        slope i < (t + (b : ℝ) * d) + d) from ?_)).trans
      (hlocal (t + (b : ℝ) * d))
    intro i hi
    obtain ⟨hia, hib⟩ := Finset.mem_filter.mp hi
    have hil : i ∈ labels := (Finset.mem_filter.mp hia).1
    have h0 := Int.floor_le ((slope i - t) / d)
    have h1 := Int.lt_floor_add_one ((slope i - t) / d)
    change ⌊(slope i - t) / d⌋ = b at hib
    rw [hib] at h0 h1
    have h0' := (le_div_iff₀ hd).mp h0
    have h1' := (div_lt_iff₀ hd).mp h1
    exact Finset.mem_filter.mpr ⟨hil, by constructor <;> nlinarith⟩
  have hcount : bins.card = 2 * K + 1 := by
    have hcount' : (bins.card : ℤ) = 2 * (K : ℤ) + 1 := by
      dsimp [bins]
      rw [Int.card_Icc_of_le (a := -(K : ℤ)) (b := (K : ℤ)) (by omega)]
      omega
    exact_mod_cast hcount'
  calc
    active.card = ∑ b ∈ bins, (active.filter (fun i => bin i = b)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _b ∈ bins, M := Finset.sum_le_sum fun b _ => hfiber b
    _ = (2 * K + 1) * M := by simp [hcount]

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StoppingScaleIntervals
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopping-level bands are intervals of the original source length
index. This is the bridge from interval concentration to summation by
parts over angular stopping levels. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem rawInterval_eq_band_sum (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    P.rawInterval coeff i lower upper x y =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper),
        P.rawBand coeff i j x y := by
  have h := planarPacketInterval_eq_selected
    (ι := fun j => Σ l : P.labels j, Item j l)
    (fun j p => coeff j p.1 p.2)
    (fun j p k t => P.raw i j p.1 p.2 k t) lower upper hlu x y
  exact h

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineWeightAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested line averaging against the manuscript's actual top weight. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem continuous_weight (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) :
    Continuous (T.weight K D) := by
  have hr : Continuous (fun z => 1 + T.radius z / K) := by
    unfold radius horizontal transverse
    fun_prop
  unfold weight
  apply continuous_const.mul
  exact hr.rpow_const fun z => Or.inl (ne_of_gt (by
    have h := T.radius_nonnegative z
    positivity))

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketLatticeData
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite packet family before choosing a reference direction.
There is no small-shear condition on its slopes. That condition is proved
only for the labels retained in a short reference cone. -/
noncomputable section
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F / w)

local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_actualZ (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).actualZ j l u = P.actualZ j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u +
      (oldSlope - newSlope) * P.actualX j
        (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  dsimp [SourceLabeledLattice.actualZ, actualZ, actualX, referenceFamily,
    SourceLabeledLattice.length, length]
  ring

theorem referenceFamily_physicalPacket (j : Fin N) (l : (Q).labels j)
    (u : Item j l) (k : κ) :
    (Q).physicalPacket newSlope j l u k = P.physicalPacket oldSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k := by
  let l₀ := P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l
  have hx := P.referenceFamily_actualX oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  have hz := P.referenceFamily_actualZ oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  unfold SourceLabeledLattice.physicalPacket physicalPacket
  rw [hx, hz]
  have hc : P.actualZ j l₀ u + (oldSlope - newSlope) * P.actualX j l₀ u +
      newSlope * P.actualX j l₀ u = P.actualZ j l₀ u + oldSlope * P.actualX j l₀ u := by ring
  have hs : newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope)) =
      oldSlope + P.rowSlope j l₀ := by ring
  change physicalPlanarPacket (P.profile j l₀ u k) _ _ (P.length j) P.width
    (newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope))) (P.frequency k) _ _ = _
  rw [hc, hs]

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledRawEnvelope
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carrier-free raw bounds for the original labeled lattices, before
any bound on the total number of labels is imposed. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem raw_eq_physical_slice (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y t : ℝ) :
    P.raw i j l u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j l u k) (P.frequency k) P.scale i) y t := by
  have h := physicalPlanarPacket_jet_slice (P.profile j l u k) (P.actualX j l u)
    (P.actualZ j l u+t*P.actualX j l u) (P.length j) P.width
    (t+P.rowSlope j l) (P.frequency k) P.scale y t (P.length_pos j).ne' P.width_pos.ne' i
  have hc : P.actualZ j l u+t*P.actualX j l u-t*P.actualX j l u = P.actualZ j l u := by ring
  have hd : t-(t+P.rowSlope j l) = -P.rowSlope j l := by ring
  simpa only [hc,hd,raw,physicalPacket] using h.symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analyzing coefficients for unrestricted packet lattices and their
exact transport to the local reference lattice. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_multiplier_coefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope
      (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
      v g j l u =
    P.physicalMultiplierCoefficient oldSlope b v g j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  ext k
  simp only [SourceLabeledLattice.physicalMultiplierCoefficient,physicalMultiplierCoefficient,
    analyzingCoefficient,WithLp.ofLp_toLp]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  have hp := congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => f z)
    (P.referenceFamily_physicalPacket oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency j l u k)
  dsimp only [referenceSelector]
  rw [hp]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceConditions
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen main coefficients vanish outside the fixed selector cone.
Restricting the main reference family to that cone is an exact identity;
its carrier bound therefore does not inherit the wide error cone. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

/-- A finite source sum supported on the reference labels equals the
sum in the literal restricted family. -/
theorem sum_referenceLabels_of_zero {E : Type*} [AddCommMonoid E]
    (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E)
    (hzero : ∀ l, ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l →
      ∀ u, f l u = 0) :
    (∑ l : P.referenceLabels oldSlope newSlope referenceLength cone w j,
      ∑ u : Item j l, f (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have hrestrict := Equiv.sum_comp (P.referenceLabelsEquiv oldSlope newSlope referenceLength cone w j)
    (fun l => ∑ u : Item j l.val, f l.val u)
  have hz : (∑ l : {l : P.labels j //
      ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l},
      ∑ u : Item j l.val, f l.val u) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    exact Finset.sum_eq_zero (fun u _ => hzero l.val l.property u)
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (P.referenceCondition oldSlope newSlope referenceLength cone w j)
    (fun l : P.labels j => ∑ u : Item j l, f l u)
  rw [hz,add_zero] at hsum
  exact hrestrict.trans hsum

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftedDrop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path mass at shifted block endpoints is set to zero as soon as
the distinguished top becomes ineligible, even if other tops continue.
The actual drop has the same factor-two reference-window comparison,
including this terminal block. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem shiftedPathMass_nonneg {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 ≤ weight t x)
    (σ : Fin K) (top : ι) (x : X) (j : ℕ) :
    0 ≤ g.shiftedPathMass tops slope precision cutoff weight σ top x j := by
  unfold shiftedPathMass
  split_ifs
  · exact Finset.sum_nonneg fun t _ => hw t x
  · exact le_rfl

theorem shiftedPathMass_pos {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 < weight t x)
    (σ : Fin K) (top : ι) (htop : top ∈ tops) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j)) :
    0 < g.shiftedPathMass tops slope precision cutoff weight σ top x j := by
  rw [shiftedPathMass,ite_eq_left he]
  exact g.path_mass_pos tops slope precision cutoff weight hw _ top htop he x

theorem shiftedPathMass_le_total {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 ≤ weight t x)
    (σ : Fin K) (top : ι) (x : X) (j : ℕ) :
    g.shiftedPathMass tops slope precision cutoff weight σ top x j ≤
      ∑ t ∈ tops, weight t x := by
  unfold shiftedPathMass
  split_ifs
  · exact g.mass_le_total tops slope precision cutoff weight hw _ _ x
  · exact Finset.sum_nonneg fun t _ => hw t x

theorem shiftedPathMass_antitone {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 ≤ weight t x) (hK : 0 < K)
    (σ : Fin K) (top : ι) (htop : top ∈ tops) (x : X) :
    Antitone (g.shiftedPathMass tops slope precision cutoff weight σ top x) := by
  intro j k hjk
  have hlevel := (ShiftedBlocks.endpoint_strictMono hK σ).monotone hjk
  by_cases hk : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ k)
  · have hj := g.eligible_of_le (hp top htop) hlevel hk
    rw [shiftedPathMass,ite_eq_left hk,shiftedPathMass,ite_eq_left hj]
    exact g.path_mass_antitone tops slope precision cutoff weight hp hw top x hlevel
  · rw [shiftedPathMass,ite_eq_right hk]
    exact g.shiftedPathMass_nonneg tops slope precision cutoff weight hw σ top x j

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMassStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite mass stopping index. A terminal ineligible top has
zero path mass, so the source cutoff is attained without a positive lower
bound on any individual top weight. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem firstMassStop_spec (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) :
    firstMassStop n count M ≤ count ∧ n (firstMassStop n count M) ≤ M ∧
      ∀ j < firstMassStop n count M, M < n j := by
  have hex : ∃ j : ℕ, j ≤ count ∧ n j ≤ M := ⟨count,le_rfl,hlast⟩
  rw [firstMassStop,dite_eq_left hex]
  refine ⟨(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩
  intro j hj
  have hn := Nat.find_min hex hj
  have hcount := (Nat.le_of_lt hj).trans (Nat.find_spec hex).1
  exact lt_of_not_ge fun h => hn ⟨hcount,h⟩

theorem firstMassStop_after (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) (hanti : Antitone n) {j : ℕ}
    (hj : firstMassStop n count M ≤ j) : n j ≤ M :=
  (hanti hj).trans (firstMassStop_spec n count M hlast).2.1

theorem firstMassStop_active_iff (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) (hanti : Antitone n) (j : ℕ) :
    j < firstMassStop n count M ↔ M < n j := by
  constructor
  · exact (firstMassStop_spec n count M hlast).2.2 j
  · intro hj
    by_contra hn
    exact (not_lt_of_ge (firstMassStop_after n count M hlast hanti (Nat.le_of_not_gt hn))) hj

namespace AngularGrid

theorem measurable_shiftedPathMass {ι X : Type*} [MeasurableSpace X] {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t, Measurable (weight t))
    (σ : Fin K) (top : ι) (j : ℕ) :
    Measurable (fun x => g.shiftedPathMass tops slope precision cutoff weight σ top x j) := by
  classical
  unfold shiftedPathMass
  split_ifs
  · exact Finset.measurable_sum _ (fun t _ => hw t)
  · exact measurable_const

theorem shiftedPathMass_terminal_zero {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (σ : Fin K) (top : ι) (count : ℕ)
    (hterminal : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ count))
    (x : X) : g.shiftedPathMass tops slope precision cutoff weight σ top x count = 0 := by
  rw [shiftedPathMass,ite_eq_right hterminal]

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePhaseParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform phase and amplitude estimates at the actual source parameters. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert

open PhaseCombinatorics

theorem phaseMu_positive_le {D p : ℝ} (hD : 1 ≤ D) (hp : 0 < p) :
    0 < phaseMu D p ∧ phaseMu D p ≤ (4 / 3 : ℝ) / p := by
  have hθ := phaseParameter_range hD
  change 0 < phaseParameter D ∧ phaseParameter D ≤ 1 / 3 at hθ
  constructor
  · exact div_pos (by linarith [hθ.1]) hp
  · exact div_le_div_of_nonneg_right (by linarith [hθ.2]) hp.le

theorem source_phaseMu_small {D L : ℝ} (hD : 1 ≤ D) (hL : 256 ≤ L) :
    0 < phaseMu D (Real.sqrt L) ∧ phaseMu D (Real.sqrt L) ≤ 1 / 12 := by
  have hroot : (16 : ℝ) ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    exact hL
  have hp : 0 < Real.sqrt L := by linarith
  have hμ := phaseMu_positive_le hD hp
  refine ⟨hμ.1, hμ.2.trans ?_⟩
  exact (div_le_iff₀ hp).mpr (by linarith)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledStoppingVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original masked physical packets, grouped by their actual stopping
levels, have the same fixed length-variation bound used in the reference
event. This includes clamped prefixes and every disjoint unary run. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

theorem physicalMaskedValue_length_sum (y x : ℝ) (j : Fin N) :
    (∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => q.1 = j),
      P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x) q) =
        P.physicalMaskedBand alt hAlt t b v g T L A y j x := by
  classical
  rw [Finset.sum_filter,Fintype.sum_sigma,Finset.sum_eq_single j]
  · simp only [ite_true, if_true]
    ext k
    simp only [Fintype.sum_sigma,physicalMaskedValue,physicalMaskedBand,
      WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]
  · intro k _ hkj
    simp only [hkj,ite_false, if_false,Finset.sum_const_zero]
  · simp

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedSum
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact synthesis and separated-energy identities for the selected
reference lattice, with its cost expressed only in the original fixed
profile bounds. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem referenceEnvelopeConstant_pos :
    0<P.referenceEnvelopeConstant := by
  have hp := P.profileBound_pos
  have hr : 0<P.ratioBound := zero_lt_one.trans_le P.ratioBound_ge_one
  unfold referenceEnvelopeConstant
  positivity

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned top restrictions with common label and item types. The top
is part of the label, so each top family contains exactly its own packets
and the family-valued concentration and path estimates apply literally. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem sum_assignedTopPackets {E : Type*} [AddCommMonoid E]
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
    (f : P.PacketIndex → E) :
    (∑ q : (P.assignedTopFamily packets assigned top).PacketIndex,
      f ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩) =
      ∑ q ∈ packets.filter (fun q => assigned q = top), f q := by
  have h := Equiv.sum_comp (P.assignedTopPacketEquiv packets assigned top)
    (fun q => f q.val)
  exact h.trans (Finset.sum_subtype _ (p := fun q =>
    q ∈ packets.filter (fun q => assigned q = top)) (by simp) f).symm

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopAlternate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-type assigned top families have exactly the original
physical bands, including original selector coefficients and top masks. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

theorem sum_assignedTopPackets_filter {E : Type*} [AddCommMonoid E]
    (top : τ) (f : P.PacketIndex → E) (keep : P.PacketIndex → Prop) :
    (∑ q ∈ Finset.univ.filter (fun q : (P.assignedTopFamily packets assigned top).PacketIndex =>
      keep ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩),
      f ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩) =
      ∑ q ∈ (packets.filter (fun q => assigned q = top)).filter keep, f q := by
  simpa only [Finset.sum_filter] using
    P.sum_assignedTopPackets packets assigned top (fun q => if keep q then f q else 0)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceProperties
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical selector centers are invariant under recentering.
Restricting to the reference cone can only decrease their local count. -/

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physical_center (j : Fin N) (l : (Q).labels j) :
    newSlope+(Q).rowSlope j l = oldSlope+P.rowSlope j (orig j l) := by
  change newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) = _
  ring

theorem referenceFamily_localMultiplicity (j : Fin N) (d : ℝ) (M : ℕ)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) d M) :
    SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : (Q).labels j => newSlope+(Q).rowSlope j l) d M := by
  intro a
  apply (Finset.card_le_card_of_injOn (orig j) ?_ ?_).trans (hlocal a)
  · intro l hl
    obtain ⟨_,hlo,hhi⟩ := Finset.mem_filter.mp hl
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · change a ≤ newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) at hlo
      change a ≤ oldSlope+P.rowSlope j (orig j l)
      linarith
    · change newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) < a+d at hhi
      change oldSlope+P.rowSlope j (orig j l) < a+d
      linarith
  · intro l _ m _ heq
    apply Subtype.ext
    exact congrArg (fun u : P.labels j => u.val) heq

theorem referenceFamily_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l)) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u :=
  P.referenceFamily_multiplier_coefficient oldSlope newSlope R cone w F hw hcone hF hwide hfrequency b v f j l u

theorem referenceFamily_alternate_physicalPacket
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) (k : κ) :
    ((Q).withProfile (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))).physicalPacket
      newSlope j l u k = (P.withProfile alt hAlt).physicalPacket oldSlope j (orig j l) u k :=
  (P.withProfile alt hAlt).referenceFamily_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j l u k

/-- A selected set supported in the reference cone has the identical
sum after the literal label restriction, including empty item fibers. -/
theorem sum_referenceFamily_selected {E : Type*} [AddCommMonoid E]
    (S : Finset P.PacketIndex) (f : P.PacketIndex → E)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1) :
    (∑ u ∈ (Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S),
      f ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) = ∑ u ∈ S, f u := by
  have hs : (Finset.univ.filter fun u : P.PacketIndex => u ∈ S) = S := by
    ext u
    simp
  conv_rhs => rw [← hs,Finset.sum_filter]
  simp only [Finset.sum_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  exact P.sum_referenceLabels_of_zero oldSlope newSlope R cone w j
    (fun l u => if (⟨j,⟨l,u⟩⟩ : P.PacketIndex) ∈ S then f ⟨j,⟨l,u⟩⟩ else 0)
    (by
      intro l hl u
      rw [ite_eq_right]
      exact fun hu => hl (hS ⟨j,⟨l,u⟩⟩ hu))

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopSelector
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The assigned-top constructor preserves the original selectors,
packet spectra, and local label count. Its geometry is supplied by the
actual selected packets; the global longest-scale bound remains explicit. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)

theorem assignedTopLabel_first (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j) : l.val.1 = top :=
  Finset.mem_singleton.mp (Finset.mem_product.mp l.property).1

theorem assignedTopLabel_injective (j : Fin N) :
    Function.Injective (P.assignedTopLabel packets assigned top j) := by
  intro l m h
  apply Subtype.ext
  exact Prod.ext ((P.assignedTopLabel_first packets assigned top j l).trans
    (P.assignedTopLabel_first packets assigned top j m).symm) h

theorem assignedTopItem_mem (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (⟨j,⟨l.val.2,u.val⟩⟩ : P.PacketIndex) ∈ packets := u.property.1

theorem assignedTopItem_assignment (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    assigned ⟨j,⟨l.val.2,u.val⟩⟩ = top :=
  u.property.2.trans (P.assignedTopLabel_first packets assigned top j l)

theorem assignedTopFamily_localMultiplicity (t d : ℝ) (M : ℕ) (j : Fin N)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d M) :
    SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : (P.assignedTopFamily packets assigned top).labels j =>
        t+(P.assignedTopFamily packets assigned top).rowSlope j l) d M := by
  intro a
  apply (Finset.card_le_card_of_injOn (P.assignedTopLabel packets assigned top j) ?_ ?_).trans (hlocal a)
  · intro l hl
    obtain ⟨_,hlo,hhi⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlo,hhi⟩
  · intro l _ m _ h
    exact P.assignedTopLabel_injective packets assigned top j h


section Reference
variable (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
  (hF : 0 ≤ F) (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => referenceFamily (P.assignedTopFamily packets assigned top) oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => referenceOriginalLabel (P.assignedTopFamily packets assigned top) oldSlope newSlope R cone w

theorem assignedTopReference_physical_center (j : Fin N) (l : (Q).labels j) :
    newSlope+(Q).rowSlope j l = oldSlope+P.rowSlope j (orig j l).val.2 :=
  (P.assignedTopFamily packets assigned top).referenceFamily_physical_center oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j l

theorem assignedTopReference_localMultiplicity (j : Fin N) (d : ℝ) (M : ℕ)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) d M) :
    SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : (Q).labels j => newSlope+(Q).rowSlope j l) d M :=
  (P.assignedTopFamily packets assigned top).referenceFamily_localMultiplicity oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j d M
      (P.assignedTopFamily_localMultiplicity packets assigned top oldSlope d M j hlocal)

theorem assignedTopReference_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (l : (Q).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l).val.2) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l).val.2 u.val :=
  (P.assignedTopFamily packets assigned top).referenceFamily_physicalMultiplierCoefficient oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency (P.assignedTopSelector packets assigned top b) v f j l u

end Reference

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceInhabitedLabels
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing labels with no items preserves every packet and every
source band. Only genuinely populated assigned fibers enter label counts. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem inhabitedLabel_nonempty (j : Fin N) (l : P.inhabitedLabels j) : Nonempty (Item j l) :=
  (Finset.mem_filter.mp l.property).2

theorem sum_inhabited {E : Type*} [AddCommMonoid E] (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E) :
    (∑ l : P.inhabitedLabels j, ∑ u : Item j l, f (P.inhabitedOriginalLabel j l) u) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have h := Equiv.sum_comp (P.inhabitedItemsEquiv j)
    (fun p : Σ l : P.labels j, Item j l => f p.1 p.2)
  change (∑ p : Σ l : P.inhabitedLabels j, Item j l, f (P.inhabitedOriginalLabel j p.1) p.2) =
    ∑ p : Σ l : P.labels j, Item j l, f p.1 p.2 at h
  simpa only [Fintype.sum_sigma] using h

theorem inhabitedFamily_rawBand
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (j : Fin N) (x y : ℝ) :
    P.inhabitedFamily.rawBand (fun j l u => coeff j (P.inhabitedOriginalLabel j l) u) jet j x y =
      P.rawBand coeff jet j x y := by
  ext k
  simp only [rawBand,vectorPacketSynthesis,packetSynthesis_apply,WithLp.ofLp_toLp,Fintype.sum_sigma]
  exact P.sum_inhabited j (fun l u => coeff j l u k*P.raw jet j l u k y x)

theorem inhabitedFamily_rawInterval
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    P.inhabitedFamily.rawInterval (fun j l u => coeff j (P.inhabitedOriginalLabel j l) u)
      jet lower upper x y = P.rawInterval coeff jet lower upper x y := by
  rw [rawInterval_eq_band_sum _ _ _ _ _ hlu,rawInterval_eq_band_sum _ _ _ _ _ hlu]
  simp_rw [P.inhabitedFamily_rawBand]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedLabelCountAt
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only labels carrying assigned packets enter the local source model.
Their actual packet directions lie in the assignment window, so local
slope multiplicity gives a fixed slot bound independent of empty labels. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
  (hF : 0 ≤ F) (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => referenceFamily (P.assignedTopFamily packets assigned top)
  oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => referenceOriginalLabel (P.assignedTopFamily packets assigned top)
  oldSlope newSlope R cone w

theorem assignedReference_inhabited_label_count_at (j : Fin N) (d radius : ℝ) (H K : ℕ)
    (hd : 0 < d) (hradius : radius ≤ K)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) d H)
    (hangle : ∀ (l : P.labels j) (u : Item j l),
      (⟨j,⟨l,u⟩⟩ : P.PacketIndex) ∈ packets → assigned ⟨j,⟨l,u⟩⟩ = top →
      |oldSlope+P.rowSlope j l-newSlope| ≤ radius*d) :
    (((Q).inhabitedFamily).labels j).card ≤ (2*K+1)*H := by
  let labelSlope := fun l : (Q).labels j => newSlope+(Q).rowSlope j l
  have hlocalQ := P.assignedTopReference_localMultiplicity packets assigned top
    oldSlope newSlope R cone w F hw hcone hF hwide hfrequency j d H hlocal
  have hwindow := SourceSlopeLabels.window_card_le
    (Finset.univ : Finset ((Q).labels j)) labelSlope (t := newSlope) hd hlocalQ hradius
  have hcount : (Finset.univ : Finset ((Q).inhabitedLabels j)).card ≤
      (SourceSlopeLabels.window Finset.univ labelSlope newSlope d radius).card := by
    apply Finset.card_le_card_of_injOn ((Q).inhabitedOriginalLabel j)
    · intro l _
      obtain ⟨u⟩ := (Q).inhabitedLabel_nonempty j l
      let l' := orig j ((Q).inhabitedOriginalLabel j l)
      have hu : P.AssignedTopItem packets assigned j l' := u
      have hp := P.assignedTopItem_mem packets assigned top j l' hu
      have ha := P.assignedTopItem_assignment packets assigned top j l' hu
      have hs := hangle l'.val.2 hu.val hp ha
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change |newSlope+(Q).rowSlope j ((Q).inhabitedOriginalLabel j l)-newSlope| ≤ radius*d
      rw [P.assignedTopReference_physical_center packets assigned top oldSlope newSlope R
        cone w F hw hcone hF hwide hfrequency j ((Q).inhabitedOriginalLabel j l)]
      exact hs
    · intro l _ m _ h
      apply Subtype.ext
      exact congrArg (fun r : (Q).labels j => r.val) h
  change ((Q).inhabitedLabels j).card ≤ (2*K+1)*H
  simpa only [Finset.card_univ,Fintype.card_coe] using hcount.trans hwindow

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAmplitudeMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the actual finite source packet amplitudes. The
angular cells and packet stopping levels are fixed; only the spatial
weights and packet values vary. Vanishing masses are allowed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
namespace AngularGrid

variable {ι σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem measurable_mass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (level : ℕ) (cell : ℤ) :
    Measurable (g.mass tops slope precision cutoff weight level cell) :=
  Finset.measurable_sum _ (fun t _ => hw t)

theorem measurable_boundaryMass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (base level : ℕ) (gap s : ℝ) :
    Measurable (g.boundaryMass tops slope precision cutoff weight base level gap s) :=
  Finset.measurable_sum _ (fun t _ => hw t)

theorem measurable_sourceBoundaryMass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (level : ℕ) (cell : ℤ) :
    Measurable (g.sourceBoundaryMass tops slope precision cutoff weight K gap level cell) :=
  g.measurable_boundaryMass tops slope precision cutoff weight hw _ _ _ _

theorem measurable_sourceTransition (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (phase : ℕ → ℂ) (level : ℕ) (cell : ℤ) :
    Measurable (fun x =>
      g.sourceTransition tops slope precision cutoff weight K gap phase x level cell) := by
  unfold sourceTransition analyticTransition
  exact (measurable_const.mul (Complex.measurable_ofReal.comp
    ((g.measurable_mass tops slope precision cutoff weight hw (level+1) cell).div
      (g.measurable_sourceBoundaryMass tops slope precision cutoff weight hw K gap level cell)).log)).cexp

theorem measurable_packetPathProduct (g : AngularGrid) (transition : X → ℕ → ℤ → ℂ)
    (ht : ∀ level cell, Measurable (fun x => transition x level cell))
    (lower upper : ℕ) (slope : ℝ) :
    Measurable (fun x => g.packetPathProduct (transition x) lower upper slope) :=
  Finset.measurable_prod _ (fun j _ => ht j _)

theorem measurable_sourcePacketBase (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (assigned : σ → ι) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s)) (a : ℝ) (s : σ) :
    Measurable (fun x => g.sourcePacketBase tops slope precision cutoff weight assigned stop
      (value x) a x s) := by
  unfold sourcePacketBase
  exact (Complex.measurable_ofReal.comp
    ((g.measurable_mass tops slope precision cutoff weight hw _ _).pow_const (-a))).smul (hv s)

theorem measurable_sourcePacketAmplitude (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → ι) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s)) (phase : ℕ → ℂ)
    (a : ℝ) (level : ℕ) (cell : ℤ) :
    Measurable (fun x => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x level cell) := by
  unfold sourcePacketAmplitude packetAmplitude
  apply Finset.measurable_sum
  intro s _
  exact (g.measurable_packetPathProduct _
    (g.measurable_sourceTransition tops slope precision cutoff weight hw K gap phase) _ _ _).smul
    (g.measurable_sourcePacketBase tops slope precision cutoff weight hw assigned stop value hv a s)

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceNodeMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the original source node ratios and the finite active
path product. These are the integrands used for line-to-plane gluing,
independently of any selected snapshot predictors. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

variable {X : Type*} {ι κ : Type} [MeasurableSpace X] [Fintype ι] [Fintype κ]

theorem measurable_sourceNodeRatio (α p : ℝ) (n : X → ℝ) (c : X → ι → ℝ)
    (A : X → ι → EuclideanSpace ℂ κ) (parent : X → EuclideanSpace ℂ κ)
    (hn : Measurable n) (hc : ∀ i, Measurable (fun x => c x i))
    (hA : ∀ i, Measurable (fun x => A x i)) (hp : Measurable parent) :
    Measurable (fun x => sourceNodeRatio (n x) (c x) (A x) α p (parent x)) := by
  unfold sourceNodeRatio sourceNodeDenominator vertexAmount
  fun_prop

theorem measurable_sourceActiveProduct (n beta : X → ℕ → ℝ) (M : ℝ) (count : ℕ)
    (hn : ∀ j, Measurable (fun x => n x j))
    (hb : ∀ j, Measurable (fun x => beta x j)) :
    Measurable (sourceActiveProduct n beta M count) := by
  unfold sourceActiveProduct
  apply Finset.measurable_prod
  intro j _
  exact Measurable.ite (measurableSet_lt measurable_const (hn j)) (hb j) measurable_const

omit [MeasurableSpace X] in
theorem sourceActiveProduct_nonneg (n beta : X → ℕ → ℝ) (M : ℝ) (count : ℕ)
    (x : X) (hb : ∀ j < count, M < n x j → 0 ≤ beta x j) :
    0 ≤ sourceActiveProduct n beta M count x := by
  apply Finset.prod_nonneg
  intro j hj
  split_ifs with h
  · exact hb j (Finset.mem_range.mp hj) h
  · exact zero_le_one

omit [MeasurableSpace X] in
/-- The measurable active product agrees exactly with the finite prefix
ending at the first mass crossing. The terminal mass may be zero. -/
theorem sourceActiveProduct_eq_stopped_product (n beta : X → ℕ → ℝ)
    (M : ℝ) (count : ℕ) (x : X) (hfinal : n x count ≤ M) (hanti : Antitone (n x)) :
    sourceActiveProduct n beta M count x =
      ∏ j ∈ Finset.range (firstMassStop (n x) count M), beta x j := by
  let stop := firstMassStop (n x) count M
  have hs : stop ≤ count := (firstMassStop_spec (n x) count M hfinal).1
  unfold sourceActiveProduct
  calc
    _ = ∏ j ∈ Finset.range stop, if M < n x j then beta x j else 1 := by
      symm
      apply Finset.prod_subset (Finset.range_mono hs)
      intro j _ hj
      have hjs : ¬j < stop := fun h => hj (Finset.mem_range.mpr h)
      have hn : ¬M < n x j := fun h => hjs
        ((firstMassStop_active_iff (n x) count M hfinal hanti j).mpr h)
      simp only [ite_eq_right hn]
    _ = ∏ j ∈ Finset.range stop, beta x j := by
      apply Finset.prod_congr rfl
      intro j hj
      exact ite_eq_left ((firstMassStop_active_iff (n x) count M hfinal hanti j).mp
        (Finset.mem_range.mp hj))

theorem sourceNodeRatio_nonneg (n : ℝ) (hn : 0 ≤ n) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (A : ι → EuclideanSpace ℂ κ) (α p : ℝ)
    (parent : EuclideanSpace ℂ κ) : 0 ≤ sourceNodeRatio n c A α p parent := by
  unfold sourceNodeRatio sourceNodeDenominator vertexAmount
  exact div_nonneg
    (add_nonneg hn (mul_nonneg (Real.rpow_nonneg hn _) (Real.rpow_nonneg (norm_nonneg _) _)))
    (add_nonneg hn (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (Real.rpow_nonneg (hc i) _) (Real.rpow_nonneg (norm_nonneg _) _))))

namespace AngularGrid

/-- Actual packet amplitudes and original cell masses give measurable
node ratios, including at zero masses. -/
theorem source_packet_node_ratio_measurable {τ σ : Type*}
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hw : ∀ t, Measurable (weight t))
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s)) (phase : ℕ → ℂ) (a α p : ℝ)
    (lower upper : ℕ) (parent : ℤ) :
    let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
    Measurable (fun x => sourceNodeRatio
      (g.mass tops slope precision cutoff weight lower parent x)
      (fun i : cells => g.mass tops slope precision cutoff weight upper i.val x)
      (fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
        packets assigned stop (value x) phase a x upper i.val) α p
      (g.sourcePacketAmplitude tops slope precision cutoff weight K gap
        packets assigned stop (value x) phase a x lower parent)) := by
  dsimp only
  exact measurable_sourceNodeRatio α p _ _ _ _
    (g.measurable_mass tops slope precision cutoff weight hw lower parent)
    (fun i => g.measurable_mass tops slope precision cutoff weight hw upper i.val)
    (fun i => g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hw K gap
      packets assigned stop value hv phase a upper i.val)
    (g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hw K gap
      packets assigned stop value hv phase a lower parent)

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePathIntegrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original finite hierarchy path integrand, expressed only through
packet amplitudes, top weights and the stopping threshold. Its spatial
measurability does not involve the auxiliary snapshot choices. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {τ σ X : Type*} {κ : Type} [MeasurableSpace X] [Fintype κ]

theorem sourceActivePathValue_measurable {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t))
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s))
    (phase : ℕ → ℂ) (a α p M : ℝ) (tag : Fin Kb) (top : τ) (count : ℕ) :
    Measurable (g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned
      stop value phase a α p M tag top count) := by
  apply measurable_sourceActiveProduct
  · exact fun j => g.measurable_shiftedPathMass tops slope precision cutoff weight hw tag top j
  · intro j
    exact g.source_packet_node_ratio_measurable tops slope precision cutoff weight hw
      K gap packets assigned stop value hv phase a α p _ _ _

omit [MeasurableSpace X] in
theorem sourceBlockNodeRatio_nonneg (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p : ℝ) (lower upper : ℕ) (parent : ℤ) (x : X) :
    0 ≤ g.sourceBlockNodeRatio tops slope precision cutoff weight K gap packets assigned
      stop value phase a α p lower upper parent x := by
  unfold sourceBlockNodeRatio
  apply sourceNodeRatio_nonneg
  · exact g.mass_nonnegative tops slope precision cutoff weight hw lower parent x
  · intro i
    exact g.mass_nonnegative tops slope precision cutoff weight hw upper i.val x

omit [MeasurableSpace X] in
theorem sourceActivePathValue_nonneg {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p M : ℝ) (tag : Fin Kb) (top : τ) (count : ℕ) (x : X) :
    0 ≤ g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned
      stop value phase a α p M tag top count x := by
  apply sourceActiveProduct_nonneg
  intro j _ _
  exact g.sourceBlockNodeRatio_nonneg tops slope precision cutoff weight hw K gap packets
    assigned stop value phase a α p _ _ _ x

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTerminalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The least ineligible shifted endpoint provides a finite terminal
generation without enlarging the source root line window past its top.
This includes exactly one final block after the last eligible endpoint. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem firstIneligibleShiftedBlock_spec {K : ℕ} (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hK : 0 < K) (σ : Fin K) :
    ¬g.eligible cutoff precision
      (ShiftedBlocks.endpoint σ (g.firstIneligibleShiftedBlock cutoff precision hp hK σ)) :=
  Nat.find_spec (g.exists_shifted_terminal cutoff precision hp hK σ)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketRegroup
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact regrouping of original packet amplitudes by assigned top and
length. This connects the individual-packet residual estimates to the
same top-band amplitudes appearing in the physical path integrals. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable Classical.decEq

private theorem weighted_sum_fibers {σ ι E : Type*} [AddCommMonoid E] [Module ℂ E]
    (packets : Finset σ) (groups : Finset ι) (key : σ → ι)
    (hkey : ∀ q ∈ packets, key q ∈ groups) (weight : ι → ℂ) (value : σ → E) :
    (∑ i ∈ groups, weight i • ∑ q ∈ packets.filter (fun q => key q = i), value q) =
      ∑ q ∈ packets, weight (key q) • value q := by
  calc
    _ = ∑ i ∈ groups, ∑ q ∈ packets.filter (fun q => key q = i), weight (key q) • value q := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to hkey _

namespace AngularGrid
variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sourcePacketAmplitude_grouped_sum {N : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (lengthIndex : σ → Fin N) (stop : ι → Fin N → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned
      (fun q => stop (assigned q) (lengthIndex q)) value phase a x level cell =
    ∑ q ∈ packets, g.sourceGroupedCoefficient tops slope precision cutoff weight K gap
      stop phase a x level cell (assigned q,lengthIndex q) • value q := by
  simp only [sourcePacketAmplitude,packetAmplitude,packetSet,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  unfold sourceGroupedCoefficient sourcePacketBase
  split_ifs <;> simp only [smul_smul,zero_smul]

/-- The original packet amplitude equals its literal top/length regrouping.
No estimate, choice of signs, or bound on the number of fibers is used. -/
theorem sourcePacketAmplitude_regroup {N : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (lengthIndex : σ → Fin N) (stop : ι → Fin N → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned
      (fun q => stop (assigned q) (lengthIndex q)) value phase a x level cell =
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => ∑ q ∈ packets.filter (fun q => (assigned q,lengthIndex q) = p), value q)
      phase a x level cell := by
  rw [g.sourcePacketAmplitude_grouped_sum tops slope precision cutoff weight K gap packets
    assigned lengthIndex stop value phase a x level cell,
    g.sourcePacketAmplitude_grouped_sum tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst Prod.snd stop]
  symm
  convert weighted_sum_fibers packets (tops ×ˢ (Finset.univ : Finset (Fin N)))
    (fun q => (assigned q,lengthIndex q))
    (fun q hq => Finset.mem_product.mpr ⟨hassigned q hq,Finset.mem_univ _⟩)
    (g.sourceGroupedCoefficient tops slope precision cutoff weight K gap stop phase a x level cell)
    value using 1; congr 1; ext q; simp
  congr 1
  apply Finset.sum_congr
  · ext r
    simp
  · intro r _
    rfl

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePathAmplitudeCongr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact node amplitude identities preserve the path ratios and their
predictors. This permits literal regrouping of physical packets before
the marked path integral, without changing any mass or transition. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid
variable {τ σ σ' X : Type*} {κ : Type} [Fintype κ]
variable (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
  (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
  (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
  (value : X → σ → EuclideanSpace ℂ κ)
  (packets' : Finset σ') (assigned' : σ' → τ) (stop' : σ' → ℕ)
  (value' : X → σ' → EuclideanSpace ℂ κ)
  (phase : ℕ → ℂ) (a : ℝ) (x : X)
  (hamp : ∀ level cell,
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x level cell =
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets' assigned' stop' (value' x) phase a x level cell)

include hamp

theorem sourceShiftedPathPrediction_congr_amplitude {Kb : ℕ}
    (p μ : ℝ) (shift : Fin Kb) (top : τ) (j : ℕ) :
    g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap
      packets assigned stop value phase a p μ shift top x j =
    g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap
      packets' assigned' stop' value' phase a p μ shift top x j := by
  simp only [sourceShiftedPathPrediction,sourceBlockPrediction,hamp]

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedLabeledGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packetwise top geometry survives slotting and frozen-active label
restriction. These operations keep every retained center and length. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- The actual packet-center condition already controls retained lengths. -/
theorem supportedTopGeometry {T : SlopeBox} {K : ℝ} {D : ℕ}
    (hwidth : P.width ≤ K*T.width)
    (hx : ∀ j l u, |P.actualX j l u-T.x|+P.length j ≤ K*T.length)
    (hz : ∀ j l u, |P.actualZ j l u-(T.y-T.slope*T.x)|+P.width ≤ K*T.width)
    (horder : 3+2*(8*D+1) ≤ P.order) (hscale : P.scale = 4*(K*T.width)) :
    SourceSupportedLabeledTopGeometry P T K D where
  length_le := fun j l u => by linarith [hx j l u,abs_nonneg (P.actualX j l u-T.x)]
  width_le := hwidth
  centerX_le := hx
  centerZ_le := hz
  order_le := horder
  scale_eq := hscale

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAssignedStoppedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supported assigned-top estimates apply to the original individual
physical packets. These identities retain their analyzing coefficients,
alternate profiles, stopping levels, masks and source transitions. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- A constant top mask can be placed in the raw coefficients exactly. -/
theorem physicalMaskedBand_const_eq_rawBand (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (T : SlopeBox) (L A : ℝ)
    (z : ℝ×ℝ) (j : Fin N) :
    P.physicalMaskedBand alt hAlt t b v f (fun _ _ _ => T) L A (z.2-t*z.1) j z.1 =
      (P.withProfile alt hAlt).rawBand
        (fun j l u => T.mask L A z • P.physicalMultiplierCoefficient t b v f j l u)
        0 j z.1 (z.2-t*z.1) := by
  ext k
  have hpoint : (z.1,(z.2-t*z.1)+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  simp only [physicalMaskedBand,rawBand,vectorPacketSynthesis,packetSynthesis_apply,
    WithLp.ofLp_toLp,Fintype.sum_sigma,hpoint]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro u _
  have hp := congrArg (fun f : SchwartzMap ℝ ℂ => f z.1)
    ((P.withProfile alt hAlt).raw_eq_physical_slice 0 j l u k (z.2-t*z.1) t)
  change (P.withProfile alt hAlt).raw 0 j l u k (z.2-t*z.1) z.1 =
    (P.withProfile alt hAlt).physicalPacket t j l u k (z.1,(z.2-t*z.1)+t*z.1) at hp
  rw [hpoint] at hp
  simp only [PiLp.smul_apply,Complex.real_smul,hp]
  ring

variable (P : SourceLabeledLattice N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => assignedReferenceFamily P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

local notation "orig" => assignedReferenceOriginalLabel P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

local notation "alts" => assignedReferenceAlternate P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt

include hAlt in
theorem assignedReferenceAlternate_bound (top : τ) (j : Fin N) (l : (Q top).labels j)
    (u : P.AssignedTopItem packets assigned j l) (k : κ) :
    planarProfileConstant (alts top j l u k) (2*(Q top).order) ≤ (Q top).profileBound :=
  hAlt j (orig top j l) u.val k

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAssignedPathIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact adapters for applying the supported plane theorem to the
inhabited assigned reference families. The original packet values,
coefficient integrals and path predictions are preserved. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- Original coefficient masks and all three raw jets are unchanged. -/
theorem inhabitedFamily_maskedRawBand (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (mask : ℝ) (jet : Fin 3)
    (j : Fin N) (x y : ℝ) :
    (P.inhabitedFamily.withProfile (P.inhabitedAlternate alt)
      (P.inhabitedAlternate_bound alt hAlt)).rawBand
      (fun j l u => mask • P.inhabitedFamily.physicalMultiplierCoefficient t
        (fun j l => b j (P.inhabitedOriginalLabel j l)) v f j l u) jet j x y =
    (P.withProfile alt hAlt).rawBand
      (fun j l u => mask • P.physicalMultiplierCoefficient t b v f j l u) jet j x y := by
  exact (P.withProfile alt hAlt).inhabitedFamily_rawBand
    (fun j l u => mask • P.physicalMultiplierCoefficient t b v f j l u) jet j x y

theorem inhabitedFamily_rawInterval_original (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (jet : Fin 3)
    (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    (P.inhabitedFamily.withProfile (P.inhabitedAlternate alt)
      (P.inhabitedAlternate_bound alt hAlt)).rawInterval
      (P.inhabitedFamily.physicalMultiplierCoefficient t
        (fun j l => b j (P.inhabitedOriginalLabel j l)) v f) jet lower upper x y =
    (P.withProfile alt hAlt).rawInterval
      (P.physicalMultiplierCoefficient t b v f) jet lower upper x y := by
  exact (P.withProfile alt hAlt).inhabitedFamily_rawInterval
    (P.physicalMultiplierCoefficient t b v f) jet lower upper hlu x y

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataMaskedBand
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact physical length bands of unrestricted masked packets. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)

theorem physicalMaskedValue_length_sum (y x : ℝ) (j : Fin N) :
    (∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => q.1 = j),
      P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x) q) =
        P.physicalMaskedBand alt hAlt t b v g T L A y j x := by
  classical
  rw [Finset.sum_filter,Fintype.sum_sigma,Finset.sum_eq_single j]
  · simp only [ite_true, if_true]
    ext k
    simp only [Fintype.sum_sigma,physicalMaskedValue,physicalMaskedBand,
      WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]
  · intro k _ hkj
    simp only [hkj,ite_false, if_false,Finset.sum_const_zero]
  · simp

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedPhysical
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact assignment and length regrouping of the physical packet sum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)

theorem assignedPhysicalBands_eq (z : ℝ×ℝ) (p : τ×Fin N) :
    P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned z p =
      ∑ q∈packets.filter (fun q => (assigned q,q.1)=p),
        P.physicalMaskedValue alt hAlt t b v f T L A z q := rfl

/-- The angular amplitude of the original masked packets is exactly
its amplitude assembled from literal assigned-top physical bands. -/
theorem physicalMaskedAmplitude_top_bands
    (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → ℝ×ℝ → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (stop : τ → Fin N → ℕ) (phase : ℕ → ℂ) (a : ℝ)
    (z : ℝ×ℝ) (level : ℕ) (cell : ℤ) :
    grid.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned
      (fun q => stop (assigned q) q.1) (P.physicalMaskedValue alt hAlt t b v f T L A z)
      phase a z level cell =
    grid.sourcePacketAmplitude tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned z)
      phase a z level cell := by
  exact grid.sourcePacketAmplitude_regroup tops slope precision cutoff weight K gap
    packets assigned hassigned (fun q => q.1) stop
    (P.physicalMaskedValue alt hAlt t b v f T L A z) phase a z level cell

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned top bands retain the actual top mask and physical packet. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

theorem assignedTopFamily_physicalMaskedValue (top : τ) (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ)
    (q : (P.assignedTopFamily packets assigned top).PacketIndex) :
    (P.assignedTopFamily packets assigned top).physicalMaskedValue
      (P.assignedTopAlternate packets assigned alt top)
      (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
      (fun j l => b j l.val.2) v f (fun j l u => T j l.val.2 u.val) L A z q =
      P.physicalMaskedValue alt hAlt t b v f T L A z
        ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩ := rfl

theorem assignedTopFamily_physicalMaskedBand (top : τ) (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    (P.assignedTopFamily packets assigned top).physicalMaskedBand
      (P.assignedTopAlternate packets assigned alt top)
      (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
      (fun j l => b j l.val.2) v f (fun j l u => T j l.val.2 u.val)
      L A (z.2-t*z.1) j z.1 =
      P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned z (top,j) := by
  let Q := P.assignedTopFamily packets assigned top
  have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hband := Q.physicalMaskedValue_length_sum
    (P.assignedTopAlternate packets assigned alt top)
    (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
    (fun j l => b j l.val.2) v f (fun j l u => T j l.val.2 u.val) L A
    (z.2-t*z.1) z.1 j
  rw [hpoint] at hband
  apply hband.symm.trans
  have hs := P.sum_assignedTopPackets_filter packets assigned top
    (P.physicalMaskedValue alt hAlt t b v f T L A z) (fun q => q.1 = j)
  calc
    _ = ∑ q ∈ Finset.univ.filter (fun q : Q.PacketIndex => q.1 = j),
        P.physicalMaskedValue alt hAlt t b v f T L A z
          ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩ := by
      apply Finset.sum_congr rfl
      intro q _
      exact P.assignedTopFamily_physicalMaskedValue packets assigned alt hAlt top t b v f T L A z q
    _ = ∑ q ∈ (packets.filter (fun q => assigned q = top)).filter (fun q => q.1 = j),
        P.physicalMaskedValue alt hAlt t b v f T L A z q := by
      convert hs using 1 <;> first | (with_reducible_and_instances rfl) | (apply Finset.sum_congr)
      · ext q
        simp
      · intro q _
        rfl
      · ext q
        simp
      · intro q _
        rfl
    _ = _ := by
      rw [P.assignedPhysicalBands_eq alt hAlt t b v f T L A packets assigned z (top,j)]
      apply Finset.sum_congr
      · ext q
        simp only [Finset.mem_filter,Prod.mk.injEq,and_assoc]
      · intro q _
        rfl

/-- The mask on an assigned family is its single assigned top mask. -/
theorem assignedTopFamily_single_mask (top : τ) (T : τ → SlopeBox) :
    (fun j (l : (P.assignedTopFamily packets assigned top).labels j)
      (u : P.AssignedTopItem packets assigned j l) =>
        T (assigned ⟨j,⟨l.val.2,u.val⟩⟩)) = fun _ _ _ => T top := by
  funext j l u
  have ht : l.val.1 = top := Finset.mem_singleton.mp (Finset.mem_product.mp l.property).1
  rw [u.property.2,ht]

theorem assignedTopFamily_topMaskBand (top : τ) (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (T : τ → SlopeBox)
    (L A : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    (P.assignedTopFamily packets assigned top).physicalMaskedBand
      (P.assignedTopAlternate packets assigned alt top)
      (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
      (fun j l => b j l.val.2) v f (fun _ _ _ => T top) L A (z.2-t*z.1) j z.1 =
      P.assignedPhysicalBands alt hAlt t b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j) := by
  have h := P.assignedTopFamily_physicalMaskedBand packets assigned alt hAlt top t b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z j
  rw [P.assignedTopFamily_single_mask packets assigned top T] at h
  exact h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original assigned-packet cone condition gives the full-family
condition required to recenter each common-type top family. -/

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem assignedTopFamily_referenceCondition (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
    (oldSlope newSlope R cone w : ℝ)
    (hcondition : ∀ u ∈ packets, assigned u = top →
      P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1) :
    ∀ q : (P.assignedTopFamily packets assigned top).PacketIndex,
      (P.assignedTopFamily packets assigned top).referenceCondition
        oldSlope newSlope R cone w q.1 q.2.1 := by
  intro q
  have hq := (P.assignedTopPacketEquiv packets assigned top q).property
  change P.referenceCondition oldSlope newSlope R cone w q.1 q.2.1.val.2
  exact hcondition _ (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceMasked
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact masked amplitudes and residuals survive the local reference change. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F)
  (hwide : cone*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physicalMaskedValue
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ)
    (u : (Q).PacketIndex) :
    (Q).physicalMaskedValue (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
      newSlope (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l)) L A z u =
    P.physicalMaskedValue alt hAlt oldSlope b v f T L A z ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ := by
  ext k
  simp only [physicalMaskedValue,SourceLabeledLattice.physicalMaskedValue,WithLp.ofLp_toLp]
  rw [P.referenceFamily_physicalMultiplierCoefficient oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency]
  rw [P.referenceFamily_alternate_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceBand
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recentring an entire already-selected top family preserves its
physical length bands. Only the literal short-cone membership is needed. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem referenceFamily_physicalMaskedBand_all (P : PacketLatticeData N κ Label Item)
    (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (hcondition : ∀ u : P.PacketIndex,
      P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    Q.physicalMaskedBand (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
      newSlope (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l))
      L A (z.2-newSlope*z.1) j z.1 =
    P.physicalMaskedBand alt hAlt oldSlope b v f T L A (z.2-oldSlope*z.1) j z.1 := by
  intro Q orig
  have hpoint (s : ℝ) : (z.1,z.2-s*z.1+s*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hQ := Q.physicalMaskedValue_length_sum (fun j l => alt j (orig j l))
    (fun j l => hAlt j (orig j l)) newSlope (fun j l => b j (orig j l)) v f
    (fun j l => T j (orig j l)) L A (z.2-newSlope*z.1) z.1 j
  rw [hpoint newSlope] at hQ
  have hP := P.physicalMaskedValue_length_sum alt hAlt oldSlope b v f T L A
    (z.2-oldSlope*z.1) z.1 j
  rw [hpoint oldSlope] at hP
  apply hQ.symm.trans
  apply Eq.trans _ hP
  have h := P.sum_referenceFamily_selected oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency Finset.univ
    (fun u => if u.1 = j then P.physicalMaskedValue alt hAlt oldSlope b v f T L A z u else 0)
    (fun u _ => hcondition u)
  simp only [Finset.sum_filter,Finset.mem_univ,ite_true, if_true] at h
  simp only [Finset.sum_filter]
  calc
    _ = ∑ q : Q.PacketIndex, if q.1 = j then
        P.physicalMaskedValue alt hAlt oldSlope b v f T L A z
          ⟨q.1,⟨orig q.1 q.2.1,q.2.2⟩⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      split_ifs
      · exact P.referenceFamily_physicalMaskedValue oldSlope newSlope R cone w F
          hw hcone hF hwide hfrequency alt hAlt b v f T L A z q
      · rfl
    _ = _ := by convert h using 1

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only nonempty assigned scales impose a reference length restriction. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
  (oldSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
  (T : τ → SlopeBox)
local notation "Q" => referenceFamily (P.assignedTopFamily packets assigned top)
  oldSlope (SlopeBox.slope (T top)) R cone w F hw hcone hF hwide hfrequency
local notation "orig" => referenceOriginalLabel (P.assignedTopFamily packets assigned top)
  oldSlope (SlopeBox.slope (T top)) R cone w

/-- Empty long scales impose no artificial restriction on the global
longest-scale field. Every retained packet has the true assigned length. -/
theorem assignedTopReference_supported_length
    (hshort : ∀ q ∈ packets, P.length q.1 ≤ (T (assigned q)).length)
    (j : Fin N) (l : (Q).labels j) (u : P.AssignedTopItem packets assigned j l) :
    (Q).length j ≤ (T top).length := by
  have h := hshort ⟨j,⟨(orig j l).val.2,u.val⟩⟩
    (P.assignedTopItem_mem packets assigned top j (orig j l) u)
  have ht := P.assignedTopItem_assignment packets assigned top j (orig j l) u
  change P.length j ≤ (T top).length
  simpa only [ht] using h


/-- The supported assigned/reference bands remain the original physical
synthesis with its original top mask, including empty scales. -/
theorem assignedTopReference_topMaskBand_all
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope R cone w q.1 q.2.1)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (L maskExponent : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    (Q).physicalMaskedBand
      (fun j l u k => alt j (orig j l).val.2 u.val k)
      (fun j l u k => hAlt j (orig j l).val.2 u.val k)
      (T top).slope (fun j l => b j (orig j l).val.2) v f
      (fun _ _ _ => T top) L maskExponent (z.2-(T top).slope*z.1) j z.1 =
    P.assignedPhysicalBands alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent packets assigned z (top,j) := by
  have href := (P.assignedTopFamily packets assigned top).referenceFamily_physicalMaskedBand_all
    oldSlope (T top).slope R cone w F hw hcone hF hwide hfrequency
    (P.assignedTopFamily_referenceCondition packets assigned top oldSlope (T top).slope
      R cone w hcondition)
    (P.assignedTopAlternate packets assigned alt top)
    (P.assignedTopAlternate_bound packets assigned alt hAlt top)
    (P.assignedTopSelector packets assigned top b) v f (fun _ _ _ => T top) L maskExponent z j
  exact href.trans (P.assignedTopFamily_topMaskBand packets assigned alt hAlt top oldSlope
    b v f T L maskExponent z j)


end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedStoppedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual masked packet sum agrees with the bounded reference
families used in the supported stopped-path estimates. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

/-- The common-type recentered family used in the actual top envelopes. -/
local notation "Q" => assignedReferenceFamily P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

local notation "alts" => assignedReferenceAlternate P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt

local notation "halt" => assignedReferenceAlternate_bound P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt hAlt

variable (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)

local notation "selector" => assignedReferenceSelector P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency b

theorem assignedReference_rawBand_original (L A : ℝ) (z : ℝ×ℝ) (top : τ) (j : Fin N)
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope (R top) cone w q.1 q.2.1) :
    ((Q top).withProfile (alts top) (halt top)).rawBand
      (fun j l u => (T top).mask L A z •
        (Q top).physicalMultiplierCoefficient (T top).slope (selector top) v f j l u)
      0 j z.1 (z.2-(T top).slope*z.1) =
    P.assignedPhysicalBands alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j) := by
  have hr := (Q top).physicalMaskedBand_const_eq_rawBand (alts top) (halt top)
    (T top).slope (selector top) v f (T top) L A z j
  exact hr.symm.trans (P.assignedTopReference_topMaskBand_all packets assigned top
    oldSlope (R top) cone w F hw hcone hF hwide hfrequency T hcondition alt hAlt b v f L A z j)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedPathIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inhabited reference adapters preserve every actual coefficient
and masked path amplitude from the unrestricted data. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => assignedReferenceFamily P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

theorem assignedInhabitedReference_constant (top : τ) :
    (P.assignedInhabitedReference packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency top).constant = (F*cone+2)*P.referenceEnvelopeConstant := by
  change ((2^P.order*P.profileBound)*(F*cone+2)*P.ratioBound^2)*3^(2*P.order) = _
  unfold referenceEnvelopeConstant
  ring

theorem assignedInhabitedReference_short
    (hshort : ∀ q ∈ packets, P.length q.1 ≤ (T (assigned q)).length)
    (top : τ) (j : Fin N) (l : (Q top).inhabitedLabels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (Q top).inhabitedFamily.length j ≤ (T top).length :=
  P.assignedTopReference_supported_length packets assigned top oldSlope (R top)
    cone w F hw hcone hF hwide hfrequency T hshort j
    ((Q top).inhabitedOriginalLabel j l) u

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)

theorem assignedInhabitedBand_original (L A : ℝ) (z : ℝ×ℝ) (p : τ×Fin N)
    (hcondition : ∀ q ∈ packets,
      P.referenceCondition oldSlope (T (assigned q)).slope (R (assigned q)) cone w q.1 q.2.1) :
    P.assignedInhabitedBand packets assigned T oldSlope R cone w F hw hcone hF hwide hfrequency
      alt hAlt b v f L A z p =
    P.assignedPhysicalBands alt hAlt oldSlope b v f
      (fun j l u => T (assigned (Sigma.mk j (Sigma.mk l u)))) L A packets assigned z p := by
  unfold assignedInhabitedBand
  rw [(Q p.1).inhabitedFamily_maskedRawBand]
  exact P.assignedReference_rawBand_original packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A z p.1 p.2
    (fun q hq hqt => by simpa only [hqt] using hcondition q hq)


variable (L A : ℝ) (grid : AngularGrid) (tops : Finset τ)
  (precision : τ → ℝ) (cut : ℝ) (weight : τ → (ℝ×ℝ) → ℝ)
  (K : ℕ) (gap : ℕ → ℝ)
  (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
  (hcondition : ∀ q ∈ packets,
    P.referenceCondition oldSlope (T (assigned q)).slope (R (assigned q)) cone w q.1 q.2.1)
  (stop : τ → Fin N → ℕ) (phase : ℕ → ℂ) (a : ℝ)

local notation "original" => physicalMaskedValue P alt hAlt oldSlope b v f
  (fun j l u => T (assigned (Sigma.mk j (Sigma.mk l u)))) L A
local notation "bands" => assignedInhabitedBand P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt hAlt b v f L A

include hassigned hcondition in
theorem assignedInhabitedAmplitude_original (z : ℝ×ℝ) (level : ℕ) (cell : ℤ) :
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      packets assigned (fun q => stop (assigned q) q.1) (original z) phase a z level cell =
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (bands z) phase a z level cell := by
  rw [P.physicalMaskedAmplitude_top_bands alt hAlt oldSlope b v f
    (fun j l u => T (assigned (Sigma.mk j (Sigma.mk l u)))) L A grid tops (fun t => (T t).slope)
    precision cut weight K gap packets assigned hassigned stop phase a z level cell]
  apply congrArg (fun values : τ×Fin N → EuclideanSpace ℂ κ =>
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      values phase a z level cell)
  funext p
  exact (P.assignedInhabitedBand_original packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A z p hcondition).symm

include hassigned hcondition in
theorem assignedInhabitedPrediction_original {Kb : ℕ}
    (p μ : ℝ) (shift : Fin Kb) (top : τ) (j : ℕ) (z : ℝ×ℝ) :
    grid.sourceShiftedPathPrediction tops (fun t => (T t).slope) precision cut weight K gap
      packets assigned (fun q => stop (assigned q) q.1) original
      phase a p μ shift top z j =
    grid.sourceShiftedPathPrediction tops (fun t => (T t).slope) precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun q => stop q.1 q.2) bands
      phase a p μ shift top z j := by
  apply grid.sourceShiftedPathPrediction_congr_amplitude tops (fun t => (T t).slope) precision cut weight K gap
    packets assigned (fun q => stop (assigned q) q.1) original
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun q => stop q.1 q.2) bands
    phase a z _ p μ shift top j
  exact P.assignedInhabitedAmplitude_original packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A grid tops precision cut weight K gap
    hassigned hcondition stop phase a z

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedMarkedPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The marked product is invariant under the exact regrouping of the
original selected packets into inhabited assigned-top reference bands. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N Kb : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem assignedInhabitedMarkedProduct_original
    (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
    (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (L A : ℝ)
    (grid : AngularGrid) (tops : Finset τ) (precision : τ → ℝ) (cut : ℝ)
    (weight : τ → (ℝ×ℝ) → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (hcondition : ∀ q ∈ packets,
      P.referenceCondition oldSlope (T (assigned q)).slope (R (assigned q)) cone w q.1 q.2.1)
    (stop : τ → Fin N → ℕ) (phase : ℕ → ℂ) (a p μ : ℝ)
    (shift : Fin Kb) (top : τ) (count : ℕ)
    (line : FiniteLineGrid) (level : ℕ → ℕ) (marked : ℕ → ℕ → Prop) (y x : ℝ) :
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A
    let bands := P.assignedInhabitedBand packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v f L A
    (∏ j ∈ Finset.range count, reverseMarkedValue line level count marked
      (fun j xx => grid.sourceShiftedPathPrediction tops (fun t => (T t).slope) precision cut weight
        K gap packets assigned (fun q => stop (assigned q) q.1) original
        phase a p μ shift top (xx,y+(T top).slope*xx) j) j x) =
    (∏ j ∈ Finset.range count, reverseMarkedValue line level count marked
      (fun j xx => grid.sourceShiftedPathPrediction tops (fun t => (T t).slope) precision cut weight
        K gap (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun q => stop q.1 q.2) bands
        phase a p μ shift top (xx,y+(T top).slope*xx) j) j x) := by
  dsimp only
  apply Finset.prod_congr rfl
  intro j _
  unfold reverseMarkedValue FiniteLineGrid.markedValue
  split_ifs
  · exact P.assignedInhabitedPrediction_original packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v f L A grid tops precision cut weight K gap
      hassigned hcondition stop phase a p μ shift top j (x,y+(T top).slope*x)
  · rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedModelInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete covariant concentration input passes unchanged to the
inhabited assigned model, retaining the original analyzing coefficient. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => P.assignedReferenceFamily packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "orig" => P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "alts" => P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "halt" => P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "selector" => P.assignedReferenceSelector packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

theorem assignedInhabitedRawInterval_original
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (top : τ)
    (jet : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    ((Q top).inhabitedFamily.withProfile ((Q top).inhabitedAlternate (alts alt top))
      ((Q top).inhabitedAlternate_bound (alts alt top) (halt alt hAlt top))).rawInterval
      ((Q top).inhabitedFamily.physicalMultiplierCoefficient (T top).slope
        (fun j l => selector b top j ((Q top).inhabitedOriginalLabel j l)) v f)
      jet lower upper x y =
    ((Q top).withProfile (alts alt top) (halt alt hAlt top)).rawInterval
      (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
      jet lower upper x y := by
  rw [(Q top).inhabitedFamily_rawInterval_original (alts alt top) (halt alt hAlt top)
    (T top).slope (selector b top) v f jet lower upper hlu x y]
  have hcoeff : (Q top).physicalMultiplierCoefficient (T top).slope (selector b top) v f =
      (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val) := by
    funext j l u
    exact P.assignedTopReference_physicalMultiplierCoefficient packets assigned top oldSlope
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency b v f j l u
  rw [hcoeff]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceStoppedAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The amplitude on a distinguished top path stops when that top becomes
ineligible. Other surviving children remain in the original denominator. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

namespace AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

theorem source_active_path_eq_stopped_product {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hprecision : ∀ t ∈ tops, 0 ≤ precision t) (hweight : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ) (phase : ℕ → ℂ)
    (a α p M : ℝ) (hM : 0 ≤ M) (hKb : 0 < Kb) (tag : Fin Kb)
    (top : τ) (htop : top ∈ tops) (count : ℕ)
    (hterminal : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag count)) (x : X) :
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a α p M tag top count x =
    ∏ j ∈ Finset.range
      (firstMassStop (g.shiftedPathMass tops slope precision cutoff weight tag top x) count M),
      g.sourceShiftedPathRatio tops slope precision cutoff weight K gap packets assigned stop value
        phase a α p tag top x j := by
  apply sourceActiveProduct_eq_stopped_product
  · rw [g.shiftedPathMass_terminal_zero tops slope precision cutoff weight tag top count hterminal]
    exact hM
  · exact g.shiftedPathMass_antitone tops slope precision cutoff weight hprecision hweight
      hKb tag top htop x

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedSupportedGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned reference geometry follows from the centers of the selected
packets. No global longest-scale hypothesis is required. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)

theorem assignedTopReference_supportedTopGeometry
    (oldSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (T : SlopeBox) (K : ℝ) (D : ℕ)
    (hwidth : P.width ≤ K*T.width)
    (horder : 3+2*(8*D+1) ≤ P.order) (hscale : P.scale = 4*(K*T.width))
    (hX : ∀ q ∈ packets, assigned q = top →
      |P.actualX q.1 q.2.1 q.2.2-T.x|+P.length q.1 ≤ K*T.length)
    (hZ : ∀ q ∈ packets, assigned q = top →
      |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-T.slope)*P.actualX q.1 q.2.1 q.2.2-
        (T.y-T.slope*T.x)|+P.width ≤ K*T.width) :
    SourceSupportedLabeledTopGeometry
      ((P.assignedTopFamily packets assigned top).referenceFamily oldSlope T.slope R cone w F
        hw hcone hF hwide hfrequency) T K D := by
  let A := P.assignedTopFamily packets assigned top
  apply (A.referenceFamily oldSlope T.slope R cone w F
    hw hcone hF hwide hfrequency).supportedTopGeometry hwidth ?_ ?_ horder hscale
  · intro j l u
    let l' := A.referenceOriginalLabel oldSlope T.slope R cone w j l
    exact hX ⟨j,⟨l'.val.2,u.val⟩⟩
      (P.assignedTopItem_mem packets assigned top j l' u)
      (P.assignedTopItem_assignment packets assigned top j l' u)
  · intro j l u
    let l' := A.referenceOriginalLabel oldSlope T.slope R cone w j l
    have hz := A.referenceFamily_actualZ oldSlope T.slope R cone w F
      hw hcone hF hwide hfrequency j l u
    have he := congrArg (fun z : ℝ => |z-(T.y-T.slope*T.x)|+P.width) hz
    exact he.le.trans (hZ ⟨j,⟨l'.val.2,u.val⟩⟩
      (P.assignedTopItem_mem packets assigned top j l' u)
      (P.assignedTopItem_assignment packets assigned top j l' u))


end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedInhabitedGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing empty labels preserves packetwise top geometry. -/
noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

 theorem inhabitedFamily_supportedTopGeometry (P : SourceLabeledLattice N κ Label Item)
    {T : SlopeBox} {K : ℝ} {D : ℕ} (G : SourceSupportedLabeledTopGeometry P T K D) :
    SourceSupportedLabeledTopGeometry P.inhabitedFamily T K D where
  length_le := fun j l u => G.length_le j (P.inhabitedOriginalLabel j l) u
  width_le := G.width_le
  centerX_le := fun j l u => G.centerX_le j (P.inhabitedOriginalLabel j l) u
  centerZ_le := fun j l u => G.centerZ_le j (P.inhabitedOriginalLabel j l) u
  order_le := G.order_le
  scale_eq := G.scale_eq

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedSupportedPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual selected centers supply the geometry of the inhabited reference
families used by the supported plane estimate. Empty scales add no condition. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- The exact assigned-and-recentered family satisfies the supported
geometry using only the centers of packets actually assigned to this top. -/
theorem assignedInhabitedReference_supportedTopGeometry
    (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
    (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (top : τ) (K : ℝ) (D : ℕ)
    (hwidth : P.width ≤ K*(T top).width)
    (horder : 3+2*(8*D+1) ≤ P.order)
    (hscale : P.scale = 4*(K*(T top).width))
    (hX : ∀ q ∈ packets, assigned q = top →
      |P.actualX q.1 q.2.1 q.2.2-(T top).x|+P.length q.1 ≤ K*(T top).length)
    (hZ : ∀ q ∈ packets, assigned q = top →
      |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T top).slope)*P.actualX q.1 q.2.1 q.2.2-
        ((T top).y-(T top).slope*(T top).x)|+P.width ≤ K*(T top).width) :
    SourceSupportedLabeledTopGeometry
      (P.assignedInhabitedReference packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency top) (T top) K D := by
  apply SourceLabeledLattice.inhabitedFamily_supportedTopGeometry
  exact P.assignedTopReference_supportedTopGeometry packets assigned top oldSlope (R top)
    cone w F hw hcone hF hwide hfrequency (T top) K D hwidth horder hscale hX hZ

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlaneWeightCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source plane integral already has the exact top-weight mass.
The marked-path and conditional-average exponentials combine into a
fixed constant, independent of all packet and top scales. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem source_plane_weight_cost (T : SlopeBox) (K D cost : ℝ) (hK : 0 < K) :
    (((Real.exp 3*cost)*(Real.exp 1*Real.exp (2*D)))*
      (2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2*T.length*T.width =
    Real.exp (4+2*D)*cost*(∫ z, T.weight K D z ∂volume.prod volume) := by
  rw [T.integral_weight hK D,Real.exp_add,show (4:ℝ) = 3+1 by norm_num,Real.exp_add]
  ring

/-- The spatial estimate is exactly the weight integral required by the
finite-tree moment theorem; it has no residual area normalization. -/
theorem source_plane_bound_by_weight (T : SlopeBox) (K D cost I : ℝ) (hK : 0 < K)
    (h : I ≤ (((Real.exp 3*cost)*(Real.exp 1*Real.exp (2*D)))*
      (2^D*∫ z, topProfile D z ∂volume.prod volume))*K^2*T.length*T.width) :
    I ≤ Real.exp (4+2*D)*cost*(∫ z, T.weight K D z ∂volume.prod volume) :=
  h.trans_eq (source_plane_weight_cost T K D cost hK)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedPlaneIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original marked-packet estimate passes through the inhabited
assigned model to an actual plane integral. All model geometry,
coefficients, masks and prediction products are identified explicitly. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_model_plane_integral
    (pProfile qEnv Cmass Cweight F c0 A_M : ℝ) (Dweight Kcount Hcount : ℕ)
    (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hAM : 0 ≤ A_M) (hDweight : 2 < (Dweight:ℝ)) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ]
      (tops : Finset τ) (T : τ → SlopeBox)
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope cone w : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
      (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ k, c0/w ≤ |P.frequency k|) →
      (F*cone+2)*P.referenceEnvelopeConstant ≤ L^pProfile →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (maskExponent : ℝ), 0 ≤ maskExponent →
    let Kw := L^(maskExponent+2)
    let R := fun t => (T t).length
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt
    cone ≤ Kcount →
    (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hcount) →
    (∀ t ∈ tops, P.width ≤ Kw*(T t).width) →
    3+2*(8*Dweight+1) ≤ P.order →
    (∀ t ∈ tops, P.scale = 4*(Kw*(T t).width)) →
    (∀ u ∈ packets, |P.actualX u.1 u.2.1 u.2.2-(T (assigned u)).x|+P.length u.1 ≤
      Kw*(T (assigned u)).length) →
    (∀ u ∈ packets,
      |P.actualZ u.1 u.2.1 u.2.2+(oldSlope-(T (assigned u)).slope)*P.actualX u.1 u.2.1 u.2.2-
        ((T (assigned u)).y-(T (assigned u)).slope*(T (assigned u)).x)|+P.width ≤
      Kw*(T (assigned u)).width) →
    (∀ u ∈ packets, assigned u ∈ tops) →
    (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
    (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
      (R (assigned u)) cone w u.1 u.2.1) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) 0) →
    ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (shift : Fin (SourceParameters.blockCount L)) (phase : Fin (SourceParameters.blockCount L) → ℂ)
      (a Z A Dphase Nmass α : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (∀ k, ‖phase k‖ ≤ Z) →
      (∀ k, k ≠ shift → (phase k).re = 0) →
      (phase shift).re = PhaseCombinatorics.phaseMu Dphase (Real.sqrt L) →
      0 ≤ A → A ≤ L^qEnv → 2 ≤ Dphase → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (top : τ), top ∈ tops →
    ∀ (good : Set (ℝ×ℝ)), MeasurableSet good →
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let phaseAll := fun k => phase (ShiftedBlocks.tag hKb k)
    let count := g.firstIneligibleShiftedBlock cut (precision top)
      (div_pos hw (T top).length_pos) hKb shift
    let H := sourceLineScale g L w (ShiftedBlocks.endpoint shift count)
    let line := fun k : ℤ => sourceReverseLineGrid g L (H*k) hw shift count
    let active := g.sourceActivePathValue tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
      (fun u => stop u.1) original phaseAll a α (Real.sqrt L) (L^A_M) shift top count
    let n := fun y x => g.shiftedPathMass tops slope precision cut weight shift top (x,y+slope top*x)
    let beta := fun y j x => g.sourceShiftedPathPrediction tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
      (fun u => stop u.1) original phaseAll a (Real.sqrt L)
      (PhaseCombinatorics.phaseMu Dphase (Real.sqrt L)) shift top (x,y+slope top*x) j
    let marked := fun k y j i => sourceMarkedCell
      ((line k).cell (ShiftedBlocks.reverseLevel shift count (ShiftedBlocks.reverseIndex count j)) i)
      (fun x => n y x j) (fun x => n y x j-n y x (j+1)) (L^A_M)
    let cost := 1+(L^(qEnv+6))^(Real.sqrt L)*(L^A_M+1)^(α-1)
    Measurable active → (∀ z ∈ good, 0 ≤ active z) →
    (∀ z ∈ good, ∀ t ∈ tops, weight t z ≤ Cweight) →
    (∀ z ∈ good, Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L) →
    (∀ z ∈ good, (∑ t ∈ tops, weight t z) ≤ L^Cmass*Nmass) →
    (∀ z ∈ good, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N → ∀ yy,
      |yy-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      let V := ((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper
      ‖V z.1 yy‖+(T t).width*
        ‖covariantSignal P.frequency (fun k zz => V z.1 zz k) yy‖ ≤ A*(weight t z)^8) →
    (∀ j < count, ∀ z ∈ good, ∀ I : Finset τ, I ⊆ tops →
      (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, precision t ≤ g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ u ∈ I, |slope t-slope u| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))) →
      (∀ t ∈ I, ∀ u ∈ I, t ≠ u →
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1)) ≤ |slope t-slope u|) →
      (I.card:ℝ) ≤ Dphase/100) →
    (∀ (k : ℤ) (y x : ℝ), x ∈ (line k).root → (x,y+slope top*x) ∈ good →
      active (x,y+slope top*x) ≤ (Real.exp 3*cost)*
        ∏ j ∈ Finset.range count, reverseMarkedValue (line k) (ShiftedBlocks.reverseLevel shift count)
          count (marked k y) (beta y) j x) →
    Integrable (good.indicator (fun z => weight top z*active z)) (volume.prod volume) ∧
      (∫ z, good.indicator (fun z => weight top z*active z) z ∂volume.prod volume) ≤
        Real.exp (4+2*(Dweight:ℝ))*cost*(∫ z, weight top z ∂volume.prod volume) := by
  filter_upwards [AngularGrid.eventually_source_supported_selector_plane_integral
    pProfile qEnv Cmass Cweight F c0 A_M Dweight ((2*Kcount+1)*Hcount) hpProfile hqEnv hCmass
    hCweight hF hc0 hAM hDweight,eventually_ge_atTop (1:ℝ)] with L hplane hL
  intro τ κ _ tops T N Label Item _ P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 v hv f hf hf1 maskExponent hmask
    Kw R Q orig alts halt hconeK hlocal hwidth horder hscale hX hZ hassigned hshort hcondition
    g hbranch htopWidth hzero hroot hKb hKbL shift phase a Z A Dphase Nmass α
    ha ha1 hZ0 hZL hphase hother hreal hA hAq hD hNmass hlogN top htop good hgood
    cut slope precision weight stop original phaseAll count H line active n beta marked cost
    hactive hactive0 hweight htotal hmass hconc hcount hpath
  let model := P.assignedInhabitedReference packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hKw : 1 ≤ Kw := Real.one_le_rpow hL (by linarith)
  let modelAlt := fun t => (Q t).inhabitedAlternate (alts t)
  let modelAltBound := fun t => (Q t).inhabitedAlternate_bound (alts t) (halt t)
  let selector := fun t j (l : (model t).labels j) =>
    b j (orig t j ((Q t).inhabitedOriginalLabel j l))
  have hslots (t : τ) (_ht : t ∈ tops) (j : Fin N) :
      ((model t).labels j).card ≤ (2*Kcount+1)*Hcount := by
    apply P.assignedReference_inhabited_label_count_at packets assigned t oldSlope
      (T t).slope (R t) cone w F hw hcone hF hwide hfrequency
      j (w/P.length j) cone Hcount Kcount (div_pos hw (P.length_pos j)) hconeK (hlocal j)
    intro l u hu he
    have hc := (hcondition ⟨j,⟨l,u⟩⟩ hu).2
    simpa only [he,mul_div_assoc] using hc
  have hmodel (t : τ) (_ht : t ∈ tops) : (model t).constant ≤ L^pProfile := by
    rw [P.assignedInhabitedReference_constant packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency t]
    exact hP
  have hgeom (t : τ) (ht : t ∈ tops) :
      SourceSupportedLabeledTopGeometry (model t) (T t) Kw Dweight := by
    apply P.assignedInhabitedReference_supportedTopGeometry packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency t Kw Dweight (hwidth t ht) horder (hscale t ht)
    · intro u hu he
      simpa only [he] using hX u hu
    · intro u hu he
      simpa only [he] using hZ u hu
  let M := fun t => g.lastEligible cut (precision t) (div_pos hw (T t).length_pos)
  have hM t (ht : t ∈ tops) : g.eligible cut (precision t) (M t) :=
    g.eligible_lastEligible cut (precision t) (div_pos hw (T t).length_pos) (hroot t ht)
  have hMmax t (ht : t ∈ tops) j (hj : g.eligible cut (precision t) j) : j ≤ M t :=
    (g.eligible_iff_le_lastEligible cut (precision t) (div_pos hw (T t).length_pos) (hroot t ht) j).mp hj
  have hinterval (t : τ) (lower upper : ℕ) (hlu : lower ≤ upper) :
      ((model t).withProfile (modelAlt t) (modelAltBound t)).rawInterval
        ((model t).physicalMultiplierCoefficient (T t).slope (selector t) v f) 0 lower upper =
      ((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper := by
    funext x y
    exact P.assignedInhabitedRawInterval_original packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v f t 0 lower upper hlu x y
  have hcost : 0 ≤ Real.exp 3*cost := by dsimp [cost]; positivity
  have hp := hplane τ κ tops T N (fun j => τ×P.labels j) (P.AssignedTopItem packets assigned)
    model hslots hmodel modelAlt modelAltBound Kw hKw hgeom selector
    (fun t j l k => hb j _ k) (fun t j l k s => hb1 j _ k s) v hv f hf hf1
    g w hw hbranch htopWidth
    (fun t _ j l u => P.assignedInhabitedReference_short packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency hshort t j l u)
    (fun _ _ => hzero) hKb hKbL shift M hM hMmax phase a Z A maskExponent Dphase Nmass
    ha ha1 hZ0 hZL hphase hother hreal hA hAq hmask hD hNmass hlogN P.frequency
    hfrequencyLo hfrequency (fun _ _ => rfl) top htop (hroot top htop)
    good hgood active hactive hactive0 (Real.exp 3*cost) hcost hweight htotal hmass
    (by
      intro z hz t ht lower upper hlu hu yy hyy
      rw [hinterval t lower upper hlu]
      exact hconc z hz t ht lower upper hlu hu yy hyy)
    hcount
    (by
      intro k y x hx hz
      have hb := hpath k y x hx hz
      have heq := P.assignedInhabitedMarkedProduct_original packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency alt hAlt b v f L maskExponent g tops precision cut weight
        (SourceParameters.blockCount L) (g.sourceBoundaryGap L) hassigned hcondition
        (fun _ j => stop j) phaseAll a (Real.sqrt L)
        (PhaseCombinatorics.phaseMu Dphase (Real.sqrt L)) shift top count
        (line k) (ShiftedBlocks.reverseLevel shift count) (marked k y) y x
      exact hb.trans_eq (congrArg (fun r => (Real.exp 3*cost)*r) heq))
  refine ⟨hp.1,?_⟩
  exact source_plane_bound_by_weight (T top) Kw (Dweight:ℝ) cost _
    (zero_lt_one.trans_le hKw) hp.2

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataPathRegularity
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selected coefficients are fixed integrals. Spatial
regularity of the masked packets therefore requires no regularity of
the selecting direction field beyond that used to define them. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem physicalMaskedValue_continuous (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (q : P.PacketIndex) :
    Continuous (fun z => P.physicalMaskedValue alt hAlt t b v f T L A z q) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    ((T q.1 q.2.1 q.2.2).mask_continuous L A))).mul
    ((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k).continuous

theorem physicalMaskedPath_measurable {τ : Type*} {Kb : ℕ}
    (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (Tpacket : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)
    (g : AngularGrid) (tops : Finset τ) (T : τ → SlopeBox)
    (w cutoff Kw D : ℝ) (hKw : 0 < Kw)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (stop : P.PacketIndex → ℕ) (phase : ℕ → ℂ) (a alpha p M : ℝ)
    (shift : Fin Kb) (top : τ) (count : ℕ) :
    Measurable (g.sourceActivePathValue tops (fun u => (T u).slope) (fun u => w/(T u).length)
      cutoff (fun u z => (T u).weight Kw D z) K gap packets assigned stop
      (P.physicalMaskedValue alt hAlt t b v f Tpacket L A) phase a alpha p M shift top count) := by
  apply g.sourceActivePathValue_measurable
  · intro u
    exact ((T u).continuous_weight hKw D).measurable
  · intro q
    exact (P.physicalMaskedValue_continuous alt hAlt t b v f Tpacket L A q).measurable

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedParentPhysicalPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Literal physical reference events imply the original per-top plane bound.
The stopped-path comparison and all inhabited-model transports are proved
before applying the plane integral theorem. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_parent_physical_plane_integral
    (pProfile qEnv Cmass Cweight F c0 A_M : ℝ) (Dweight Kcount Hcount : ℕ)
    (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*pProfile+13) (2*pProfile+17)+3/2) ≤ A_M)
    (hDweight : 2 < (Dweight:ℝ)) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ]
      (tops : Finset τ) (T : τ → SlopeBox)
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope cone w : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
      (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ k, c0/w ≤ |P.frequency k|) →
      (F*cone+2)*P.referenceEnvelopeConstant ≤ L^pProfile →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (maskExponent shortVariation : ℝ), 0 ≤ maskExponent →
    let Kw := L^(maskExponent+2)
    let R := fun t => (T t).length
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt
    ∀ (hwideResidual : (cone+(SourceParameters.branching L)^2)*w ≤ P.width)
      (hwideParent : (cone+(SourceParameters.branching L)^3)*w ≤ P.width),
    cone ≤ Kcount →
    (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hcount) →
    (∀ t ∈ tops, P.width ≤ Kw*(T t).width) →
    3+2*(8*Dweight+1) ≤ P.order →
    (∀ t ∈ tops, P.scale = 4*(Kw*(T t).width)) →
    (∀ u ∈ packets, |P.actualX u.1 u.2.1 u.2.2-(T (assigned u)).x|+P.length u.1 ≤
      Kw*(T (assigned u)).length) →
    (∀ u ∈ packets,
      |P.actualZ u.1 u.2.1 u.2.2+(oldSlope-(T (assigned u)).slope)*P.actualX u.1 u.2.1 u.2.2-
        ((T (assigned u)).y-(T (assigned u)).slope*(T (assigned u)).x)|+P.width ≤
      Kw*(T (assigned u)).width) →
    (∀ u ∈ packets, assigned u ∈ tops) →
    (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
    (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
      (R (assigned u)) cone w u.1 u.2.1) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) 0) →
    ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (shift : Fin (SourceParameters.blockCount L)) (phase : Fin (SourceParameters.blockCount L) → ℂ)
      (a Z A Dphase Nmass α : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (∀ k, ‖phase k‖ ≤ Z) →
      (∀ k, k ≠ shift → (phase k).re = 0) →
      (phase shift).re = PhaseCombinatorics.phaseMu Dphase (Real.sqrt L) →
      0 ≤ A → A ≤ L^qEnv → 2 ≤ Dphase → 0 < Nmass → Real.log Nmass ≤ 2*L →
      1 ≤ α → α ≤ 3 → (α-1)/Real.sqrt L ≤ 1/12 →
      Real.sqrt L*PhaseCombinatorics.phaseMu Dphase (Real.sqrt L) = α-1 →
    ∀ (top : τ), top ∈ tops →
    ∀ (good : Set (ℝ×ℝ)), MeasurableSet good →
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let phaseAll := fun k => phase (ShiftedBlocks.tag hKb k)
    let count := g.firstIneligibleShiftedBlock cut (precision top)
      (div_pos hw (T top).length_pos) hKb shift
    let active := g.sourceActivePathValue tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
      (fun u => stop u.1) original phaseAll a α (Real.sqrt L) (L^A_M) shift top count
    let cost := 1+(L^(qEnv+6))^(Real.sqrt L)*(L^A_M+1)^(α-1)
    (∀ z ∈ good, ∀ t ∈ tops, weight t z ≤ Cweight) →
    (∀ z ∈ good, Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L) →
    (∀ z ∈ good, (∑ t ∈ tops, weight t z) ≤ L^Cmass*Nmass) →
    (∀ z ∈ good, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N → ∀ yy,
      |yy-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      let V := ((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper
      ‖V z.1 yy‖+(T t).width*
        ‖covariantSignal P.frequency (fun k zz => V z.1 zz k) yy‖ ≤ A*(weight t z)^8) →
    (∀ j < count, ∀ z ∈ good, ∀ I : Finset τ, I ⊆ tops →
      (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, precision t ≤ g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ u ∈ I, |slope t-slope u| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))) →
      (∀ t ∈ I, ∀ u ∈ I, t ≠ u →
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1)) ≤ |slope t-slope u|) →
      (I.card:ℝ) ≤ Dphase/100) →
    let squarePackets := sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => oldSlope+P.rowSlope u.1 u.2.1) (R top) (slope top)
      (cone+(SourceParameters.branching L)^3) w
    let Qsquare := P.referenceFamily oldSlope (slope top) (R top)
      (cone+(SourceParameters.branching L)^3) w F hw
      (add_nonneg hcone (pow_nonneg (SourceParameters.branching_pos L).le 3)) hF hwideParent hfrequency
    let origSquare := P.referenceOriginalLabel oldSlope (slope top) (R top)
      (cone+(SourceParameters.branching L)^3) w
    let squareSelected := (Finset.univ : Finset Qsquare.PacketIndex).filter
      (fun u => (⟨u.1,⟨origSquare u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ squarePackets)
    let S := g.fixedPathResidualPackets tops slope precision cut packets assigned
      (fun u => stop u.1) (ShiftedBlocks.endpoint shift) (count-1) (slope top)
    let Qref := P.referenceFamily oldSlope (slope top) (R top)
      (cone+(SourceParameters.branching L)^2) w F hw (by positivity) hF hwideResidual hfrequency
    let origRef := P.referenceOriginalLabel oldSlope (slope top) (R top)
      (cone+(SourceParameters.branching L)^2) w
    let selected := (Finset.univ : Finset Qref.PacketIndex).filter
      (fun u => (⟨u.1,⟨origRef u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
    (∀ z ∈ good, z ∉ (Qsquare.restrictPackets squareSelected).physicalReferenceBad
      (Qsquare.restrictedAlternate (fun j l => alt j (origSquare j l)) squareSelected)
      (Qsquare.restrictedAlternate_bound (fun j l => alt j (origSquare j l))
        (fun j l => hAlt j (origSquare j l)) squareSelected)
      (slope top) (w/P.topLength) (fun j l => b j (origSquare j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origSquare j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) shortVariation) →
    (∀ z ∈ good, z ∉ (Qref.restrictPackets selected).physicalReferenceBad
      (Qref.restrictedAlternate (fun j l => alt j (origRef j l)) selected)
      (Qref.restrictedAlternate_bound (fun j l => alt j (origRef j l))
        (fun j l => hAlt j (origRef j l)) selected)
      (slope top) (w/P.topLength) (fun j l => b j (origRef j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origRef j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) (2*pProfile+11)) →
    Integrable (good.indicator (fun z => weight top z*active z)) (volume.prod volume) ∧
      (∫ z, good.indicator (fun z => weight top z*active z) z ∂volume.prod volume) ≤
        Real.exp (4+2*(Dweight:ℝ))*cost*(∫ z, weight top z ∂volume.prod volume) := by
  filter_upwards [eventually_assigned_model_plane_integral pProfile qEnv Cmass Cweight F c0 A_M
    Dweight Kcount Hcount hpProfile hqEnv hCmass hCweight hF hc0 hAM.le hDweight,
    eventually_assigned_parent_marked_path_bound pProfile qEnv (Dweight:ℝ) Cmass A_M Cweight
      hpProfile (by linarith) hCmass hAM hchoice hCweight Kcount Hcount,
    eventually_ge_atTop (256:ℝ)] with L hplane hmarked hL
  intro τ κ _ tops T N Label Item _ P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation hmask
    Kw R Q orig alts halt hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ
    hassigned hshort hcondition g hbranch htopWidth hzero hroot hKb hKbL shift phase
    a Z A Dphase Nmass α ha ha1 hZ0 hZL hphase hother hreal hA hAq hD hNmass hlogN
    hα hα3 hμ hrelation top htop good hgood cut slope precision weight stop original phaseAll
    count active cost hweight htotal hmass hconc hcount
    squarePackets Qsquare origSquare squareSelected S Qref origRef selected hsquareEvent hrefEvent
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hKw : 1 ≤ Kw := Real.one_le_rpow hL1 (by linarith)
  have hwp (t : τ) (z : ℝ×ℝ) : 0 < weight t z :=
    (T t).weight_pos (zero_lt_one.trans_le hKw) (Dweight:ℝ) z
  have hwp0 (t : τ) (z : ℝ×ℝ) : 0 ≤ weight t z := (hwp t z).le
  have hactive : Measurable active :=
    P.physicalMaskedPath_measurable alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent g tops T w cut Kw
      (Dweight:ℝ) (zero_lt_one.trans_le hKw) (SourceParameters.blockCount L)
      (g.sourceBoundaryGap L) packets assigned (fun u => stop u.1) phaseAll
      a α (Real.sqrt L) (L^A_M) shift top count
  have hactive0 (z : ℝ×ℝ) (_hz : z ∈ good) : 0 ≤ active z :=
    g.sourceActivePathValue_nonneg tops slope precision cut weight hwp0
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
      (fun u => stop u.1) original phaseAll a α (Real.sqrt L) (L^A_M) shift top count z
  have hprecision (t : τ) (_ht : t ∈ tops) : 0 ≤ precision t :=
    (div_pos hw (T t).length_pos).le
  have hpacketOrder : 6 ≤ P.order := by
    have hd : 2 < Dweight := by exact_mod_cast hDweight
    omega
  have hP0 : P.referenceEnvelopeConstant ≤ L^pProfile := by
    have hc : 0 ≤ P.referenceEnvelopeConstant := P.referenceEnvelopeConstant_pos.le
    have hfac : 1 ≤ F*cone+2 := by nlinarith [mul_nonneg hF hcone]
    exact (le_mul_of_one_le_left hc hfac).trans hP
  have hphase0 (k : ℕ) : 0 ≤ (phaseAll k).re := by
    dsimp only [phaseAll]
    by_cases he : ShiftedBlocks.tag hKb k = shift
    · rw [he,hreal]
      exact (source_phaseMu_small (by linarith) hL).1.le
    · rw [hother _ he]
  have heligible (u : P.PacketIndex) (hu : u ∈ packets) :
      g.eligible cut (precision (assigned u)) (stop u.1) := by
    have hle : precision (assigned u) ≤ w/P.length u.1 :=
      div_le_div_of_nonneg_left hw.le (P.length_pos u.1) (hshort u hu)
    exact (mul_le_mul_of_nonneg_right hle (by positivity)).trans
      (g.eligible_lastEligible cut (w/P.length u.1) (div_pos hw (P.length_pos u.1)) (hzero u.1))
  have hangle (u : P.PacketIndex) (hu : u ∈ packets) :
      |oldSlope+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ cone*(w/P.length u.1) := by
    simpa only [mul_div_assoc] using (hcondition u hu).2
  apply hplane τ κ tops T N Label Item P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 v hv f hf hf1 maskExponent hmask
    hconeK hlocal hwidth horder hscale hX hZ hassigned hshort hcondition
    g hbranch htopWidth hzero hroot hKb hKbL shift phase a Z A Dphase Nmass α
    ha ha1 hZ0 hZL hphase hother hreal hA hAq hD hNmass hlogN top htop good hgood
    hactive hactive0 hweight htotal hmass hconc hcount
  intro k y x hx hz
  let z : ℝ×ℝ := (x,y+slope top*x)
  have hnpos : 0 < g.shiftedPathMass tops slope precision cut weight shift top z 0 := by
    apply g.shiftedPathMass_pos tops slope precision cut weight hwp shift top htop z 0
    simpa only [ShiftedBlocks.endpoint_zero] using hroot top htop
  have hnle := g.shiftedPathMass_le_total tops slope precision cut weight hwp0 shift top z 0
  have hnlog : Real.log (g.shiftedPathMass tops slope precision cut weight shift top z 0) ≤ 3*L :=
    (Real.log_le_log hnpos (hnle.trans (le_max_right 1 _))).trans (htotal z hz)
  have hmass0 : g.mass tops slope precision cut weight 0 (g.index 0 (slope top)) z ≤
      L^Cmass*Nmass :=
    (g.mass_le_total tops slope precision cut weight hwp0 0 (g.index 0 (slope top)) z).trans (hmass z hz)
  have hbnd := hmarked N κ Label Item P hpacketOrder hP0 alt hAlt oldSlope a
    (fun j => w/P.length j) (fun _ => cone) (fun j => div_pos hw (P.length_pos j))
    (fun _ => hconeK) hlocal b hb hb1 hsupp v hv f hf hf1 τ g tops T maskExponent
    shortVariation w (T top).length cone F hw (T top).length_pos hbranch hKb shift hzero
    hprecision top htop rfl (by positivity) hF hwideResidual hfrequency
      (add_nonneg hcone (pow_nonneg (SourceParameters.branching_pos L).le 3)) hwideParent
    phaseAll hphase0 Z Nmass α (PhaseCombinatorics.phaseMu Dphase (Real.sqrt L))
    ha ha1 hZ0 hZL (fun j => hphase _) hNmass hlogN hα hα3 hμ hrelation
    z packets assigned hassigned heligible hangle (hsquareEvent z hz) (hrefEvent z hz)
    (sourceLineScale g L w (ShiftedBlocks.endpoint shift count)*k) y x rfl hx hKw htopWidth
    A hA hAq hcone hshort hroot (hweight z hz) (htotal z hz) hnlog hmass0
    (by
      intro t ht lower upper hlu hu
      have hc := hconc z hz t ht lower upper hlu hu (z.2-(T t).slope*z.1) (by simpa using (T t).width_pos.le)
      exact (le_add_of_nonneg_right (mul_nonneg (T t).width_pos.le (norm_nonneg _))).trans hc)
  exact hbnd

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePathCountInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A terminal path is independent of how far the finite hierarchy is
extended. Thus the individual terminal counts used by the plane theorem
can be replaced by one finite count for every top in a root. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem firstMassStop_eq_of_terminal (n : ℕ → ℝ) (M : ℝ) (c d : ℕ)
    (hc : n c ≤ M) (hd : n d ≤ M) :
    firstMassStop n c M = firstMassStop n d M := by
  have hs := firstMassStop_spec n c M hc
  have ht := firstMassStop_spec n d M hd
  apply le_antisymm
  · by_contra h
    have hlt := hs.2.2 (firstMassStop n d M) (Nat.lt_of_not_ge h)
    exact (not_lt_of_ge ht.2.1) hlt
  · by_contra h
    have hlt := ht.2.2 (firstMassStop n c M) (Nat.lt_of_not_ge h)
    exact (not_lt_of_ge hs.2.1) hlt

namespace AngularGrid
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

theorem sourceActivePathValue_count_congr {Kb : ℕ}
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a alpha p M : ℝ) (hM : 0 ≤ M)
    (hKb : 0 < Kb) (shift : Fin Kb) (top : τ) (htop : top ∈ tops)
    (c d : ℕ)
    (hc : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift c))
    (hd : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift d)) (x : X) :
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a alpha p M shift top c x =
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a alpha p M shift top d x := by
  rw [g.source_active_path_eq_stopped_product tops slope precision cutoff weight hp hw
    K gap packets assigned stop value phase a alpha p M hM hKb shift top htop c hc x,
    g.source_active_path_eq_stopped_product tops slope precision cutoff weight hp hw
    K gap packets assigned stop value phase a alpha p M hM hKb shift top htop d hd x]
  congr 2
  apply firstMassStop_eq_of_terminal
  · rw [g.shiftedPathMass_terminal_zero tops slope precision cutoff weight shift top c hc x]
    exact hM
  · rw [g.shiftedPathMass_terminal_zero tops slope precision cutoff weight shift top d hd x]
    exact hM

/-- The maximum of the actual individual terminal counts is terminal
for every top in the finite root family. -/
theorem source_common_terminal {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (precision : τ → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hKb : 0 < Kb) (shift : Fin Kb) (count : τ → ℕ)
    (hterminal : ∀ t ∈ tops, ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift (count t))) :
    ∀ t ∈ tops, ¬g.eligible cutoff (precision t)
      (ShiftedBlocks.endpoint shift (tops.sup count)) := by
  intro t ht he
  have hle : ShiftedBlocks.endpoint shift (count t) ≤
      ShiftedBlocks.endpoint shift (tops.sup count) :=
    (ShiftedBlocks.endpoint_strictMono hKb shift).monotone (Finset.le_sup ht)
  exact hterminal t ht (g.eligible_of_le (hp t ht) hle he)

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCommonTerminalIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Per-top path integrals are unchanged when their terminal counts are
replaced by a common terminal count. The original good set, weights and
physical packet values are preserved. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ σ X : Type*} {κ : Type} [Fintype κ] [MeasurableSpace X]

theorem sourceActivePathValue_integral_count_congr {Kb : ℕ}
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a alpha p M : ℝ) (hM : 0 ≤ M)
    (hKb : 0 < Kb) (shift : Fin Kb) (top : τ) (htop : top ∈ tops)
    (c d : ℕ)
    (hc : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift c))
    (hd : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift d))
    (good : Set X) (μ : Measure X) (C : ℝ)
    (hbound :
      Integrable (good.indicator (fun x => weight top x *
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop
          value phase a alpha p M shift top c x)) μ ∧
      (∫ x, good.indicator (fun y => weight top y *
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop
          value phase a alpha p M shift top c y) x ∂μ) ≤ C*(∫ x, weight top x ∂μ)) :
    Integrable (good.indicator (fun x => weight top x *
      g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop
        value phase a alpha p M shift top d x)) μ ∧
    (∫ x, good.indicator (fun y => weight top y *
      g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop
        value phase a alpha p M shift top d y) x ∂μ) ≤ C*(∫ x, weight top x ∂μ) := by
  have heq : (fun x => g.sourceActivePathValue tops slope precision cutoff weight K gap
      packets assigned stop value phase a alpha p M shift top c x) =
      (fun x => g.sourceActivePathValue tops slope precision cutoff weight K gap
      packets assigned stop value phase a alpha p M shift top d x) := by
    funext x
    exact g.sourceActivePathValue_count_congr tops slope precision cutoff weight hp hw
      K gap packets assigned stop value phase a alpha p M hM hKb shift top htop c d hc hd x
  simpa only [heq] using hbound

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSharedGoodPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original per-top plane bounds descend to one common good set and
one terminal count. The latter is the supremum of the actual first
ineligible shifted endpoints, without an additional stopping premise. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

/-- Shrinking a good set preserves an integral bound for a nonnegative
integrand, even when integrability was proved only after restriction. -/
theorem nonnegative_integral_shared_good {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (localGood good : Set X) (B : ℝ)
    (hgood : MeasurableSet good) (hsub : good ⊆ localGood)
    (hf : ∀ x, 0 ≤ f x)
    (hbound : Integrable (localGood.indicator f) μ ∧
      (∫ x, localGood.indicator f x ∂μ) ≤ B) :
    Integrable (good.indicator f) μ ∧ (∫ x, good.indicator f x ∂μ) ≤ B := by
  classical
  have heq : good.indicator (localGood.indicator f) = good.indicator f := by
    funext x
    by_cases hx : x ∈ good
    · simp only [Set.indicator_of_mem hx,Set.indicator_of_mem (hsub hx)]
    · simp only [Set.indicator_of_notMem hx]
  have hi : Integrable (good.indicator f) μ := by
    rw [←heq]
    exact hbound.1.indicator hgood
  refine ⟨hi, (integral_mono hi hbound.1 ?_).trans hbound.2⟩
  intro x
  by_cases hx : x ∈ good
  · simp only [Set.indicator_of_mem hx,Set.indicator_of_mem (hsub hx),le_refl]
  · rw [Set.indicator_of_notMem hx]
    exact Set.indicator_nonneg (fun x _ => hf x) x

namespace AngularGrid
variable {τ σ : Type*} {κ : Type} [Fintype κ]

theorem source_top_shared_good_common_integral {Kb : ℕ}
    (g : AngularGrid) (tops : Finset τ) (T : τ → SlopeBox)
    (cutoff w Kw D : ℝ) (hw : 0 < w) (hKw : 0 < Kw)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : (ℝ×ℝ) → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a alpha p M : ℝ) (hM : 0 ≤ M)
    (hKb : 0 < Kb) (shift : Fin Kb)
    (localGood : τ → Set (ℝ×ℝ)) (good : Set (ℝ×ℝ)) (bad : τ → Set (ℝ×ℝ))
    (hgood : MeasurableSet good) (hbad : ∀ t ∈ tops, MeasurableSet (bad t))
    (hsub : ∀ t ∈ tops, good \ bad t ⊆ localGood t)
    (μ : Measure (ℝ×ℝ)) (C : ℝ)
    (hbound : ∀ t ∈ tops,
      Integrable ((localGood t).indicator (fun x => (T t).weight Kw D x *
        g.sourceActivePathValue tops (fun u => (T u).slope) (fun u => w/(T u).length)
          cutoff (fun u x => (T u).weight Kw D x) K gap packets assigned stop value
          phase a alpha p M shift t (g.sourceTopTerminalCount T cutoff w hw hKb shift t) x)) μ ∧
      (∫ x, (localGood t).indicator (fun y => (T t).weight Kw D y *
        g.sourceActivePathValue tops (fun u => (T u).slope) (fun u => w/(T u).length)
          cutoff (fun u x => (T u).weight Kw D x) K gap packets assigned stop value
          phase a alpha p M shift t (g.sourceTopTerminalCount T cutoff w hw hKb shift t) y) x ∂μ) ≤
        C*(∫ x, (T t).weight Kw D x ∂μ)) :
    ∀ t ∈ tops,
      Integrable ((good \ bad t).indicator (fun x => (T t).weight Kw D x *
        g.sourceActivePathValue tops (fun u => (T u).slope) (fun u => w/(T u).length)
          cutoff (fun u x => (T u).weight Kw D x) K gap packets assigned stop value
          phase a alpha p M shift t
          (tops.sup (g.sourceTopTerminalCount T cutoff w hw hKb shift)) x)) μ ∧
      (∫ x, (good \ bad t).indicator (fun y => (T t).weight Kw D y *
        g.sourceActivePathValue tops (fun u => (T u).slope) (fun u => w/(T u).length)
          cutoff (fun u x => (T u).weight Kw D x) K gap packets assigned stop value
          phase a alpha p M shift t
          (tops.sup (g.sourceTopTerminalCount T cutoff w hw hKb shift)) y) x ∂μ) ≤
        C*(∫ x, (T t).weight Kw D x ∂μ) := by
  have hw0 (t : τ) (x : ℝ×ℝ) : 0 ≤ (T t).weight Kw D x :=
    ((T t).weight_pos hKw D x).le
  let count := g.sourceTopTerminalCount T cutoff w hw hKb shift
  have hterminal t (_ht : t ∈ tops) :
      ¬g.eligible cutoff (w/(T t).length) (ShiftedBlocks.endpoint shift (count t)) :=
    g.firstIneligibleShiftedBlock_spec cutoff (w/(T t).length)
      (div_pos hw (T t).length_pos) hKb shift
  have hcommon := g.source_common_terminal tops (fun t => w/(T t).length) cutoff
    (fun t _ => (div_pos hw (T t).length_pos).le) hKb shift count hterminal
  intro t ht
  apply g.sourceActivePathValue_integral_count_congr tops
    (fun u => (T u).slope) (fun u => w/(T u).length) cutoff
    (fun u x => (T u).weight Kw D x)
    (fun u _ => (div_pos hw (T u).length_pos).le) hw0 K gap packets assigned stop value
    phase a alpha p M hM hKb shift t ht (count t) (tops.sup count)
    (hterminal t ht) (hcommon t ht) (good \ bad t) μ C
  apply nonnegative_integral_shared_good μ _ (localGood t) (good \ bad t) _
    (hgood.diff (hbad t ht)) (hsub t ht)
  · intro x
    exact mul_nonneg (hw0 t x)
      (g.sourceActivePathValue_nonneg tops (fun u => (T u).slope) (fun u => w/(T u).length)
        cutoff (fun u x => (T u).weight Kw D x) hw0 K gap packets assigned stop value
        phase a alpha p M shift t (g.sourceTopTerminalCount T cutoff w hw hKb shift t) x)
  · exact hbound t ht

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonnegative shift simplex and its vertex geometry. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

theorem sourceShiftSimplex_vertex [DecidableEq ι] {mu : ℝ} (hmu : 0 ≤ mu) (i : ι) :
    Pi.single i mu ∈ sourceShiftSimplex mu := by
  constructor
  · intro j
    by_cases hji : j = i
    · subst j; simpa using hmu
    · simp [hji]
  · simp [Pi.single_apply]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePhaseNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate bounds on the actual shift simplex, and the polynomial
budget for the linear node envelope at arbitrary imaginary phases. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

theorem sourceShiftSimplex_phase_norm {mu : ℝ} (a eta : ι → ℝ)
    (ha : a ∈ sourceShiftSimplex mu) (i : ι) :
    ‖phaseTubePoint a eta i‖ ≤ mu+Real.sqrt (∑ j, (eta j)^2) := by
  have hai : a i ≤ mu := by
    calc
      a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => ha.1 j) (Finset.mem_univ i)
      _ = mu := ha.2
  have hsq : (eta i)^2 ≤ ∑ j, (eta j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (eta j)) (Finset.mem_univ i)
  have heta : |eta i| ≤ Real.sqrt (∑ j, (eta j)^2) :=
    (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)).mpr
      (by simpa only [sq_abs] using hsq)
  calc
    ‖phaseTubePoint a eta i‖ ≤ ‖(a i:ℂ)‖+‖(eta i:ℂ)*Complex.I‖ := norm_add_le _ _
    _ = a i+|eta i| := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha.1 i),norm_mul,
        Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    _ ≤ _ := add_le_add hai heta

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceVertexPlaneParameters
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual simplex vertex satisfies every scalar phase condition
of the original physical plane estimate, uniformly in the shift count. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem source_vertex_plane_parameters (L D : ℝ) (K : ℕ)
    (hL : 256 ≤ L) (hD : 2 ≤ D) (hK : 0 < K)
    (i : Fin K) (eta : Fin K → ℝ)
    (heta : Real.sqrt (∑ j, (eta j)^2) ≤ L^2) :
    let p := Real.sqrt L
    let mu := PhaseCombinatorics.phaseMu D p
    let alpha := 2+PhaseCombinatorics.phaseParameter D
    let a := mu/(K:ℝ)
    let phase := phaseTubePoint (Pi.single i mu) eta
    0 ≤ a ∧ a ≤ 1 ∧ 1 ≤ alpha ∧ alpha ≤ 3 ∧
      (alpha-1)/p ≤ 1/12 ∧ p*mu = alpha-1 ∧
      (∀ j, ‖phase j‖ ≤ 2*L^2) ∧
      (∀ j, j ≠ i → (phase j).re = 0) ∧ (phase i).re = mu := by
  classical
  dsimp only
  let mu := PhaseCombinatorics.phaseMu D (Real.sqrt L)
  let alpha := 2+PhaseCombinatorics.phaseParameter D
  have hp : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  have hmu : 0 < mu ∧ mu ≤ 1/12 := source_phaseMu_small (by linarith) hL
  have htheta := PhaseCombinatorics.phaseParameter_range (by linarith : 1 ≤ D)
  change 0 < PhaseCombinatorics.phaseParameter D ∧
    PhaseCombinatorics.phaseParameter D ≤ 1/3 at htheta
  have hKreal : (1:ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K from hK)
  have halpha : 1 ≤ alpha ∧ alpha ≤ 3 := by
    dsimp only [alpha]
    constructor <;> linarith [htheta.1,htheta.2]
  have hquot : (alpha-1)/Real.sqrt L = mu := by
    dsimp only [alpha,mu,PhaseCombinatorics.phaseMu]
    congr 1
    ring
  have hrelation : Real.sqrt L*mu = alpha-1 := by
    rw [←hquot]
    exact mul_div_cancel₀ _ hp.ne'
  have ha0 : 0 ≤ mu/(K:ℝ) := div_nonneg hmu.1.le (zero_le_one.trans hKreal)
  have ha1 : mu/(K:ℝ) ≤ 1 :=
    (div_le_self hmu.1.le hKreal).trans (by linarith)
  refine ⟨ha0,ha1,halpha.1,halpha.2,?_,hrelation,?_,?_,?_⟩
  · rw [hquot]
    exact hmu.2
  · intro j
    have hn := sourceShiftSimplex_phase_norm (Pi.single i mu) eta
      (sourceShiftSimplex_vertex hmu.1.le i) j
    have hL2 : 1 ≤ L^2 := one_le_pow₀ (by linarith : 1 ≤ L)
    exact hn.trans (by linarith [hmu.2,heta])
  · intro j hji
    simp [phaseTubePoint,hji]
  · simp [phaseTubePoint]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedParentVertexIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual simplex vertices satisfy the physical plane hypotheses.
The original per-top packet integrals consequently hold on one common
measurable good set, with only that top's bad event removed, and with
the common terminal count used by finite-tree interpolation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_parent_vertex_integral_oai
    (pProfile qEnv Cmass Cweight F c0 A_M : ℝ) (Dweight Kcount Hcount : ℕ)
    (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*pProfile+13) (2*pProfile+17)+3/2) ≤ A_M)
    (hDweight : 2 < (Dweight:ℝ)) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ]
      (tops : Finset τ) (T : τ → SlopeBox)
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope cone w : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
      (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ k, c0/w ≤ |P.frequency k|) →
      (F*cone+2)*P.referenceEnvelopeConstant ≤ L^pProfile →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (maskExponent shortVariation : ℝ), 0 ≤ maskExponent →
    let Kw := L^(maskExponent+2)
    let R := fun t => (T t).length
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt
    ∀ (hwideResidual : (cone+(SourceParameters.branching L)^2)*w ≤ P.width)
      (hwideParent : (cone+(SourceParameters.branching L)^3)*w ≤ P.width),
    cone ≤ Kcount →
    (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hcount) →
    (∀ t ∈ tops, P.width ≤ Kw*(T t).width) →
    3+2*(8*Dweight+1) ≤ P.order →
    (∀ t ∈ tops, P.scale = 4*(Kw*(T t).width)) →
    (∀ u ∈ packets, |P.actualX u.1 u.2.1 u.2.2-(T (assigned u)).x|+P.length u.1 ≤
      Kw*(T (assigned u)).length) →
    (∀ u ∈ packets,
      |P.actualZ u.1 u.2.1 u.2.2+(oldSlope-(T (assigned u)).slope)*P.actualX u.1 u.2.1 u.2.2-
        ((T (assigned u)).y-(T (assigned u)).slope*(T (assigned u)).x)|+P.width ≤
      Kw*(T (assigned u)).width) →
    (∀ u ∈ packets, assigned u ∈ tops) →
    (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
    (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
      (R (assigned u)) cone w u.1 u.2.1) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) 0) →
    ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (Dphase Nmass A : ℝ), 2 ≤ Dphase → 0 < Nmass → Real.log Nmass ≤ 2*L →
      0 ≤ A → A ≤ L^qEnv →
    ∀ (shift : Fin (SourceParameters.blockCount L))
      (eta : Fin (SourceParameters.blockCount L) → ℝ),
      Real.sqrt (∑ j, (eta j)^2) ≤ L^2 →
    let p := Real.sqrt L
    let mu := PhaseCombinatorics.phaseMu Dphase p
    let alpha := 2+PhaseCombinatorics.phaseParameter Dphase
    let a := mu/(SourceParameters.blockCount L:ℝ)
    let phase := phaseTubePoint (Pi.single shift mu) eta
    let phaseAll := fun j => phase (ShiftedBlocks.tag hKb j)
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let countTop := g.sourceTopTerminalCount T cut w hw hKb shift
    let count := tops.sup countTop
    let cost := 1+(L^(qEnv+6))^p*(L^A_M+1)^(alpha-1)
    ∀ (good : Set (ℝ×ℝ)) (bad : τ → Set (ℝ×ℝ)), MeasurableSet good →
      (∀ t ∈ tops, MeasurableSet (bad t)) →
    (∀ z ∈ good, ∀ t ∈ tops, weight t z ≤ Cweight) →
    (∀ z ∈ good, Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L) →
    (∀ z ∈ good, (∑ t ∈ tops, weight t z) ≤ L^Cmass*Nmass) →
    (∀ z ∈ good, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N → ∀ yy,
      |yy-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      let V := ((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper
      ‖V z.1 yy‖+(T t).width*
        ‖covariantSignal P.frequency (fun k zz => V z.1 zz k) yy‖ ≤ A*(weight t z)^8) →
    (∀ j < count, ∀ z ∈ good, ∀ I : Finset τ, I ⊆ tops →
      (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, w/(T t).length ≤ g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ u ∈ I, |(T t).slope-(T u).slope| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))) →
      (∀ t ∈ I, ∀ u ∈ I, t ≠ u →
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1)) ≤ |(T t).slope-(T u).slope|) →
      (I.card:ℝ) ≤ Dphase/100) →
    let squarePackets := fun t => sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => oldSlope+P.rowSlope u.1 u.2.1) (R t) (T t).slope
      (cone+(SourceParameters.branching L)^3) w
    let Qsquare := fun t => P.referenceFamily oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^3) w F hw
      (add_nonneg hcone (pow_nonneg (SourceParameters.branching_pos L).le 3)) hF hwideParent hfrequency
    let origSquare := fun t => P.referenceOriginalLabel oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^3) w
    let squareSelected := fun t => (Finset.univ : Finset (Qsquare t).PacketIndex).filter
      (fun u => (⟨u.1,⟨origSquare t u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ squarePackets t)
    let S := fun t => g.fixedPathResidualPackets tops (fun u => (T u).slope)
      (fun u => w/(T u).length) cut packets assigned (fun u => stop u.1)
      (ShiftedBlocks.endpoint shift) (countTop t-1) (T t).slope
    let Qref := fun t => P.referenceFamily oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^2) w F hw (by positivity) hF hwideResidual hfrequency
    let origRef := fun t => P.referenceOriginalLabel oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^2) w
    let selected := fun t => (Finset.univ : Finset (Qref t).PacketIndex).filter
      (fun u => (⟨u.1,⟨origRef t u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S t)
    (∀ t ∈ tops, ∀ z ∈ good \ bad t, z ∉ ((Qsquare t).restrictPackets (squareSelected t)).physicalReferenceBad
      ((Qsquare t).restrictedAlternate (fun j l => alt j (origSquare t j l)) (squareSelected t))
      ((Qsquare t).restrictedAlternate_bound (fun j l => alt j (origSquare t j l))
        (fun j l => hAlt j (origSquare t j l)) (squareSelected t))
      (T t).slope (w/P.topLength) (fun j l => b j (origSquare t j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origSquare t j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) shortVariation) →
    (∀ t ∈ tops, ∀ z ∈ good \ bad t, z ∉ ((Qref t).restrictPackets (selected t)).physicalReferenceBad
      ((Qref t).restrictedAlternate (fun j l => alt j (origRef t j l)) (selected t))
      ((Qref t).restrictedAlternate_bound (fun j l => alt j (origRef t j l))
        (fun j l => hAlt j (origRef t j l)) (selected t))
      (T t).slope (w/P.topLength) (fun j l => b j (origRef t j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origRef t j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) (2*pProfile+11)) →
    ∀ top ∈ tops,
      Integrable ((good \ bad top).indicator (fun z => weight top z*
        g.sourceActivePathValue tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
          (fun u => stop u.1) original phaseAll a alpha p (L^A_M) shift top count z))
        (volume.prod volume) ∧
      (∫ z, (good \ bad top).indicator (fun x => weight top x*
        g.sourceActivePathValue tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
          (fun u => stop u.1) original phaseAll a alpha p (L^A_M) shift top count x) z
        ∂volume.prod volume) ≤
        Real.exp (4+2*(Dweight:ℝ))*cost*(∫ z, weight top z ∂volume.prod volume) := by
  filter_upwards [eventually_assigned_parent_physical_plane_integral pProfile qEnv Cmass Cweight F c0 A_M
    Dweight Kcount Hcount hpProfile hqEnv hCmass hCweight hF hc0 hAM hchoice hDweight,
    eventually_ge_atTop (256:ℝ)] with L hplane hL
  intro τ κ _ tops T N Label Item _ P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation
    hmask Kw R Q orig alts halt hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ
    hassigned hshort hcondition g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A
    hD hNmass hlogN hA hAq shift eta heta p mu alpha a phase phaseAll cut weight stop
    original countTop count cost good bad hgood hbad hweight htotal hmass hconc hcount
    squarePackets Qsquare origSquare squareSelected S Qref origRef selected hsquareEvent hrefEvent
  have hparams := source_vertex_plane_parameters L Dphase (SourceParameters.blockCount L)
    hL hD hKb shift eta heta
  change 0 ≤ a ∧ a ≤ 1 ∧ 1 ≤ alpha ∧ alpha ≤ 3 ∧ (alpha-1)/p ≤ 1/12 ∧
    p*mu = alpha-1 ∧ (∀ j, ‖phase j‖ ≤ 2*L^2) ∧
    (∀ j, j ≠ shift → (phase j).re = 0) ∧ (phase shift).re = mu at hparams
  obtain ⟨ha,ha1,halpha,halpha3,hmu,hrelation,hphase,hother,hreal⟩ := hparams
  have hKw : 0 < Kw := Real.rpow_pos_of_pos (by linarith) _
  have hM : 0 ≤ L^A_M := Real.rpow_nonneg (by linarith) _
  apply g.source_top_shared_good_common_integral tops T cut w Kw (Dweight:ℝ) hw hKw
    (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
    (fun u => stop u.1) original phaseAll a alpha p (L^A_M) hM hKb shift
    (fun t => good \ bad t) good bad hgood hbad (fun _ _ => Set.Subset.rfl)
    (volume.prod volume) (Real.exp (4+2*(Dweight:ℝ))*cost)
  intro top htop
  have hct : countTop top ≤ count := Finset.le_sup htop
  exact hplane τ κ tops T N Label Item P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation
    hmask hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ hassigned hshort hcondition
    g hbranch htopWidth hzero hroot hKb hKbL shift phase a (2*L^2) A Dphase Nmass alpha
    ha ha1 (by positivity) le_rfl hphase hother hreal hA hAq hD hNmass hlogN
    halpha halpha3 hmu hrelation top htop (good \ bad top) (hgood.diff (hbad top htop))
    (fun z hz => hweight z hz.1) (fun z hz => htotal z hz.1) (fun z hz => hmass z hz.1)
    (fun z hz => hconc z hz.1)
    (fun j hj z hz => hcount j (hj.trans_le hct) z hz.1)
    (hsquareEvent top htop) (hrefEvent top htop)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_vertex_integral_oai := @OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_vertex_integral_oai
