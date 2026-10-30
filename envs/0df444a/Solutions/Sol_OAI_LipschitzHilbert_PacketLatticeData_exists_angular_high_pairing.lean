-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketLatticeData.exists_angular_high_pairing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T19:57:56.261081+00:00
-- url     : https://prove2.me/submissions/e62d2782-cb82-4d69-8e15-12ffa47c3a28

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_exists_universal_ordinary_model_estimate
import Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_source_density_popular_recovery

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketPolarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact four-term polarization of a cross packet coefficient and
synthesizing wave. Both packets may have different planar profiles. -/

noncomputable section
namespace LipschitzHilbert

theorem packet_cross_polarization (a b f g : ℂ) :
    (a+b)*(f+g) - (a-b)*(f-g) -
        Complex.I*((a-Complex.I*b)*(f+Complex.I*g)) +
        Complex.I*((a+Complex.I*b)*(f-Complex.I*g)) = 4*(a*g) := by
  ring_nf
  simp [Complex.I_sq]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CoefficientPolarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Antilinearity of the actual analyzing integral supplies the
coefficients in the four-term packet polarization identity. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert
variable {Ω σ κ : Type*} [MeasurableSpace Ω]

theorem analyzingCoefficient_add_smul (μ : Measure Ω) (area : σ → ℝ)
    (f h : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ) (c : ℂ)
    (hf : ∀ s k, Integrable (fun z => g z k*conj (f s k z)) μ)
    (hh : ∀ s k, Integrable (fun z => g z k*conj (h s k z)) μ) (s : σ) :
    analyzingCoefficient μ area (fun s k z => f s k z+c*h s k z) g s =
      analyzingCoefficient μ area f g s + conj c • analyzingCoefficient μ area h g s := by
  ext k
  change ((↑(area s) : ℂ)⁻¹)*(∫ z, g z k*conj (f s k z+c*h s k z) ∂μ) =
    ((↑(area s) : ℂ)⁻¹)*(∫ z, g z k*conj (f s k z) ∂μ) +
      conj c*(((↑(area s) : ℂ)⁻¹)*(∫ z, g z k*conj (h s k z) ∂μ))
  have heq : (fun z => g z k*conj (f s k z+c*h s k z)) =
      (fun z => g z k*conj (f s k z)+conj c*(g z k*conj (h s k z))) := by
    funext z
    simp only [map_add,map_mul]
    ring
  rw [heq,integral_add (hf s k) ((hh s k).const_mul (conj c)),integral_const_mul]
  ring

end LipschitzHilbert

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

end SlopeBox

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

theorem integrable_planeDivide (f : ℝ × ℝ → ℝ)
    (hf : Integrable f (volume.prod volume)) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (fun z => f (planeDivide a b ha hb z)) (volume.prod volume) := by
  apply (integrable_map_equiv (planeDivide a b ha hb) f).mp
  rw [map_planeDivide]
  exact hf.smul_measure (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

theorem integral_planeDivide (f : ℝ × ℝ → ℝ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∫ z, f (planeDivide a b ha hb z) ∂volume.prod volume) =
      (|a| * |b|) * ∫ z, f z ∂volume.prod volume := by
  rw [← integral_map_equiv (planeDivide a b ha hb), map_planeDivide, integral_smul_measure]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

theorem topProfile_nonnegative (D : ℝ) (z : ℝ × ℝ) : 0 ≤ topProfile D z :=
  Real.rpow_nonneg (by positivity) _

theorem topProfile_continuous (D : ℝ) : Continuous (topProfile D) := by
  unfold topProfile
  apply Continuous.rpow_const (by fun_prop)
  intro z
  left
  positivity

/-- The fixed normalized profile is integrable once its decay exponent exceeds
its two-dimensional domain. -/
theorem topProfile_integrable {D : ℝ} (hD : 2 < D) :
    Integrable (topProfile D) (volume.prod volume) := by
  have hd : (Module.finrank ℝ (ℝ × ℝ) : ℝ) < D := by simpa using hD
  have h := integrable_one_add_norm (μ := (volume.prod volume)) hd
  apply h.mono' (topProfile_continuous D).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (topProfile_nonnegative D z)]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  simp only [Prod.norm_def, Real.norm_eq_abs]
  have hmax : max |z.1| |z.2| ≤ |z.1| + |z.2| :=
    max_le (by linarith [abs_nonneg z.2]) (by linarith [abs_nonneg z.1])
  linarith

namespace SlopeBox

theorem normalizedCoordinates_eq (T : SlopeBox) (K : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.normalizedCoordinates K hK z = (T.horizontal z / K, T.transverse z / K) := by
  ext <;> simp [normalizedCoordinates, planeDivide_apply, slopeShear, horizontal, transverse]
  <;> ring

theorem weight_eq_topProfile (T : SlopeBox) (K D : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.weight K D z = 2 ^ D * topProfile D (T.normalizedCoordinates K hK z) := by
  rw [normalizedCoordinates_eq]
  simp only [weight, topProfile, radius, abs_div, abs_of_pos hK, add_div]

/-- The actual top weight is integrable, uniformly over positions and slopes. -/
theorem weight_integrable (T : SlopeBox) {K D : ℝ} (hK : 0 < K) (hD : 2 < D) :
    Integrable (T.weight K D) (volume.prod volume) := by
  have hf := integrable_planeDivide (topProfile D) (topProfile_integrable hD)
    (K * T.length) (K * T.width)
    (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne')
  have hs := (slopeShear_measurePreserving (-T.slope)).integrable_comp_of_integrable hf
  have ht := hs.comp_sub_right (T.x, T.y)
  have heq : T.weight K D = fun z => 2 ^ D *
      ((fun z => topProfile D (planeDivide (K * T.length) (K * T.width)
        (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)) ∘
        slopeShear (-T.slope)) (z - (T.x, T.y)) := by
    funext z
    exact T.weight_eq_topProfile K D hK z
  rw [heq]
  exact ht.const_mul _

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityKeepers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decreasing-length selection of the actual spatial and angular density
tests. Keeper witnesses are disjoint even when their spatial boxes overlap. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem densityConflict_symm {ι : Type*} (T : ι → SlopeBox) (omega : ι → Set ℝ)
    (K : ℝ) {i j : ι} (h : densityConflict T omega K i j) :
    densityConflict T omega K j i := by
  simpa only [densityConflict,inter_comm] using h

theorem densityTest_disjoint_of_not_conflict {ι : Type*}
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (T : ι → SlopeBox)
    (omega : ι → Set ℝ) (K : ℝ) {i j : ι}
    (h : ¬densityConflict T omega K i j) :
    Disjoint (densityTest E u (T i) (omega i) K)
      (densityTest E u (T j) (omega j) K) := by
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  exact h ⟨⟨z,hzi.1.2,hzj.1.2⟩,⟨u z,hzi.2,hzj.2⟩⟩

theorem exists_density_keepers {ι : Type*} (candidates : Finset ι)
    (T : ι → SlopeBox) (omega : ι → Set ℝ) (K : ℝ) (hK : 0 ≤ K)
    (homega : ∀ i ∈ candidates, (omega i).Nonempty) :
    ∃ keepers : Finset ι, keepers ⊆ candidates ∧
      (∀ i ∈ keepers, ∀ j ∈ keepers, i ≠ j → ¬densityConflict T omega K i j) ∧
      (∀ i ∈ candidates, ∃ j ∈ keepers,
        (T i).length ≤ (T j).length ∧ densityConflict T omega K i j) := by
  classical
  induction candidates using Finset.strongInductionOn with
  | _ candidates ih =>
    by_cases hnonempty : candidates.Nonempty
    · obtain ⟨top,htop,hmax⟩ := candidates.exists_max_image (fun i => (T i).length) hnonempty
      have hself : densityConflict T omega K top top := by
        obtain ⟨s,hs⟩ := homega top htop
        refine ⟨⟨((T top).x,(T top).y),?_,?_⟩,⟨s,hs,hs⟩⟩ <;>
          simp only [densitySpatialBox,mem_ofPred_eq,sub_self,mul_zero,abs_zero]
        · exact ⟨mul_nonneg hK (T top).length_pos.le,mul_nonneg hK (T top).width_pos.le⟩
        · exact ⟨mul_nonneg hK (T top).length_pos.le,mul_nonneg hK (T top).width_pos.le⟩
      let rest := candidates.filter fun i => ¬densityConflict T omega K top i
      have hrest : rest ⊂ candidates := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.filter_subset _ _,?_⟩
        intro heq
        have : top ∈ rest := heq.symm ▸ htop
        exact (Finset.mem_filter.mp this).2 hself
      obtain ⟨keepers,hsub,hdisj,hcover⟩ := ih rest hrest
        (fun i hi => homega i (Finset.mem_filter.mp hi).1)
      refine ⟨insert top keepers,?_,?_,?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact htop
        · exact (Finset.mem_filter.mp (hsub hi)).1
      · intro i hi j hj hij
        rcases Finset.mem_insert.mp hi with hieq | hi'
        · subst i
          rcases Finset.mem_insert.mp hj with hjeq | hj'
          · exact (hij hjeq.symm).elim
          · exact (Finset.mem_filter.mp (hsub hj')).2
        · rcases Finset.mem_insert.mp hj with hjeq | hj'
          · subst j
            intro hconflict
            exact (Finset.mem_filter.mp (hsub hi')).2 (densityConflict_symm T omega K hconflict)
          · exact hdisj i hi' j hj' hij
      · intro i hi
        by_cases hc : densityConflict T omega K top i
        · exact ⟨top,Finset.mem_insert_self _ _,hmax i hi,densityConflict_symm T omega K hc⟩
        · obtain ⟨j,hj,hlen,hconflict⟩ := hcover i (Finset.mem_filter.mpr ⟨hi,hc⟩)
          exact ⟨j,Finset.mem_insert_of_mem hj,hlen,hconflict⟩
    · refine ⟨∅,Finset.empty_subset _,?_,?_⟩
      · simp
      · intro i hi
        exact (hnonempty ⟨i,hi⟩).elim

theorem density_keeper_area_budget {ι : Type*} (keepers : Finset ι)
    (T : ι → SlopeBox) (omega : ι → Set ℝ) (K eta : ℝ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (heta : 0 < eta)
    (hE : (volume.prod volume) E ≠ ∞)
    (hdisj : ∀ i ∈ keepers, ∀ j ∈ keepers, i ≠ j → ¬densityConflict T omega K i j)
    (hmeas : ∀ i ∈ keepers, MeasurableSet (densityTest E u (T i) (omega i) K))
    (hmass : ∀ i ∈ keepers, eta*(T i).area ≤
      (volume.prod volume).real (densityTest E u (T i) (omega i) K)) :
    ∑ i ∈ keepers, (T i).area ≤ (volume.prod volume).real E / eta := by
  have hsub (i : ι) : densityTest E u (T i) (omega i) K ⊆ E := fun _ hz => hz.1.1
  have hfinite (i : ι) : (volume.prod volume) (densityTest E u (T i) (omega i) K) ≠ ∞ :=
    measure_ne_top_of_subset (hsub i) hE
  have hpair : Set.PairwiseDisjoint (keepers : Set ι)
      (fun i => densityTest E u (T i) (omega i) K) := by
    intro i hi j hj hij
    exact densityTest_disjoint_of_not_conflict E u T omega K (hdisj i hi j hj hij)
  have hsum : (∑ i ∈ keepers, (volume.prod volume).real (densityTest E u (T i) (omega i) K)) ≤
      (volume.prod volume).real E := by
    rw [← measureReal_biUnion_finset hpair hmeas (fun i _ => hfinite i)]
    apply measureReal_mono _ hE
    intro z hz
    obtain ⟨i,hi,hz⟩ := mem_iUnion₂.mp hz
    exact hsub i hz
  apply (le_div_iff₀ heta).mpr
  calc
    (∑ i ∈ keepers, (T i).area)*eta = ∑ i ∈ keepers, eta*(T i).area := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ keepers, (volume.prod volume).real (densityTest E u (T i) (omega i) K) :=
      Finset.sum_le_sum hmass
    _ ≤ _ := hsum

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual geometry behind the density keeper assignment: intersecting
angular cells give slope control, and intersecting slope boxes then give
the required spatial enlargement. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem densitySpatialBox_measurable (T : SlopeBox) (K : ℝ) :
    MeasurableSet (densitySpatialBox T K) := by
  change MeasurableSet ({z : ℝ×ℝ | |z.1-T.x| ≤ K*T.length} ∩
    {z : ℝ×ℝ | |(z.2-T.y)-T.slope*(z.1-T.x)| ≤ K*T.width})
  exact (isClosed_le ((continuous_fst.sub continuous_const).abs) continuous_const).measurableSet.inter
    (isClosed_le (((continuous_snd.sub continuous_const).sub
      (continuous_const.mul (continuous_fst.sub continuous_const))).abs) continuous_const).measurableSet

theorem densityTest_measurable {E : Set (ℝ×ℝ)} {u : ℝ×ℝ → ℝ}
    {omega : Set ℝ} (hE : MeasurableSet E) (hu : Measurable u)
    (homega : MeasurableSet omega) (T : SlopeBox) (K : ℝ) :
    MeasurableSet (densityTest E u T omega K) :=
  (hE.inter (densitySpatialBox_measurable T K)).inter (hu homega)

theorem density_center_in_keeper (T S : SlopeBox) {K C : ℝ}
    (hK : 0 ≤ K) (hlen : T.length ≤ S.length) (hwidth : T.width = S.width)
    (hslope : |T.slope-S.slope| * T.length ≤ C*S.width)
    {z : ℝ×ℝ} (hT : z ∈ densitySpatialBox T K) (hS : z ∈ densitySpatialBox S K) :
    |T.x-S.x| ≤ 2*K*S.length ∧
      |(T.y-S.y)-S.slope*(T.x-S.x)| ≤ (2+C)*K*S.width := by
  have hx : |T.x-S.x| ≤ 2*K*S.length := by
    calc
      _ = |(z.1-S.x)-(z.1-T.x)| := by congr 1; ring
      _ ≤ |z.1-S.x|+|z.1-T.x| := abs_sub _ _
      _ ≤ K*S.length+K*T.length := add_le_add hS.1 hT.1
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlen hK]
  refine ⟨hx,?_⟩
  have hp : |T.slope-S.slope| * |z.1-T.x| ≤ C*K*S.width := by
    calc
      _ ≤ |T.slope-S.slope| * (K*T.length) :=
        mul_le_mul_of_nonneg_left hT.1 (abs_nonneg _)
      _ = K*(|T.slope-S.slope| * T.length) := by ring
      _ ≤ K*(C*S.width) := mul_le_mul_of_nonneg_left hslope hK
      _ = _ := by ring
  calc
    _ = |((z.2-S.y)-S.slope*(z.1-S.x)) -
        ((z.2-T.y)-T.slope*(z.1-T.x)) - (T.slope-S.slope)*(z.1-T.x)| := by
      congr 1
      ring
    _ ≤ |(z.2-S.y)-S.slope*(z.1-S.x)|+
        |(z.2-T.y)-T.slope*(z.1-T.x)|+|(T.slope-S.slope)*(z.1-T.x)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ K*S.width+K*T.width+C*K*S.width := by
      rw [abs_mul]
      exact add_le_add (add_le_add hS.2 hT.2) hp
    _ = _ := by rw [hwidth]; ring

theorem density_box_subset_keeper (T S : SlopeBox) {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hlen : T.length ≤ S.length)
    (hwidth : T.width = S.width)
    (hslope : |T.slope-S.slope| * T.length ≤ C*S.width)
    (hinter : (densitySpatialBox T K ∩ densitySpatialBox S K).Nonempty) :
    densitySpatialBox T K ⊆ densitySpatialBox S ((3+2*C)*K) := by
  obtain ⟨q,hqT,hqS⟩ := hinter
  obtain ⟨hcx,hcy⟩ := density_center_in_keeper T S hK hlen hwidth hslope hqT hqS
  intro z hz
  have hx : |z.1-S.x| ≤ 3*K*S.length := by
    calc
      _ = |(z.1-T.x)+(T.x-S.x)| := by congr 1; ring
      _ ≤ |z.1-T.x|+|T.x-S.x| := abs_add_le _ _
      _ ≤ K*T.length+2*K*S.length := add_le_add hz.1 hcx
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlen hK]
  have hp : |T.slope-S.slope| * |z.1-T.x| ≤ C*K*S.width := by
    calc
      _ ≤ |T.slope-S.slope| * (K*T.length) :=
        mul_le_mul_of_nonneg_left hz.1 (abs_nonneg _)
      _ = K*(|T.slope-S.slope| * T.length) := by ring
      _ ≤ K*(C*S.width) := mul_le_mul_of_nonneg_left hslope hK
      _ = _ := by ring
  constructor
  · exact hx.trans (by nlinarith [mul_nonneg (mul_nonneg hC hK) S.length_pos.le])
  · calc
      _ = |((z.2-T.y)-T.slope*(z.1-T.x)) +
          ((T.y-S.y)-S.slope*(T.x-S.x)) + (T.slope-S.slope)*(z.1-T.x)| := by
        congr 1
        ring
      _ ≤ |(z.2-T.y)-T.slope*(z.1-T.x)|+
          |(T.y-S.y)-S.slope*(T.x-S.x)|+|(T.slope-S.slope)*(z.1-T.x)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ K*T.width+(2+C)*K*S.width+C*K*S.width := by
        rw [abs_mul]
        exact add_le_add (add_le_add hz.2 hcy) hp
      _ = _ := by rw [hwidth]; ring

theorem density_angular_cell_slope {q k l i j : ℤ} {s t : ℝ}
    (hlk : l ≤ k) (hinter : (DyadicLineGrid.cell q k i ∩ DyadicLineGrid.cell q l j).Nonempty)
    (hs : s ∈ DyadicLineGrid.cell q k i) (ht : t ∈ DyadicLineGrid.cell q l j) :
    |s-t| ≤ DyadicLineGrid.scale k := by
  have ht' := DyadicLineGrid.cell_subset_of_intersect hlk
    (by simpa only [inter_comm] using hinter) ht
  have hnext : DyadicLineGrid.left q k (i+1) =
      DyadicLineGrid.left q k i+DyadicLineGrid.scale k := by
    unfold DyadicLineGrid.left
    push_cast
    ring
  change DyadicLineGrid.left q k i ≤ s ∧ s < DyadicLineGrid.left q k (i+1) at hs
  change DyadicLineGrid.left q k i ≤ t ∧ t < DyadicLineGrid.left q k (i+1) at ht'
  rw [hnext] at hs ht'
  exact abs_le.mpr ⟨by linarith [hs.1,ht'.2],by linarith [hs.2,ht'.1]⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityScaledForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular grid has physical scale w/topLength. Keeping that scale
explicit allows arbitrary vertical band width and dyadic source lengths. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem scaledAngularCell_measurable (unit : ℝ) (q k j : ℤ) :
    MeasurableSet (scaledAngularCell unit q k j) :=
  measurableSet_Ico.preimage (measurable_id.div_const unit)

theorem scaledAngularCell_nonempty {unit : ℝ} (hunit : 0 < unit) (q k j : ℤ) :
    (scaledAngularCell unit q k j).Nonempty := by
  obtain ⟨s,hs⟩ := DyadicLineGrid.cell_nonempty q k j
  refine ⟨s*unit,?_⟩
  simpa only [scaledAngularCell,mem_ofPred_eq,mul_div_cancel_right₀ _ hunit.ne'] using hs

theorem scaledAngularCell_subset {unit : ℝ} {q k l i j : ℤ} (hlk : l ≤ k)
    (hinter : (scaledAngularCell unit q k i ∩ scaledAngularCell unit q l j).Nonempty) :
    scaledAngularCell unit q l j ⊆ scaledAngularCell unit q k i := by
  obtain ⟨s,hs,ht⟩ := hinter
  have hnested := DyadicLineGrid.cell_subset_of_intersect hlk ⟨s/unit,ht,hs⟩
  intro t ht
  exact hnested ht

theorem scaledAngularCell_slope {unit : ℝ} (hunit : 0 < unit) {q k l i j : ℤ} {s t : ℝ}
    (hlk : l ≤ k)
    (hinter : (scaledAngularCell unit q k i ∩ scaledAngularCell unit q l j).Nonempty)
    (hs : s ∈ scaledAngularCell unit q k i) (ht : t ∈ scaledAngularCell unit q l j) :
    |s-t| ≤ unit*DyadicLineGrid.scale k := by
  obtain ⟨v,hv,hv'⟩ := hinter
  have h := density_angular_cell_slope hlk ⟨v/unit,hv,hv'⟩ hs ht
  rw [←sub_div,abs_div,abs_of_pos hunit] at h
  simpa only [mul_comm] using (div_le_iff₀ hunit).mp h

theorem exists_scaled_dyadic_density_forest {ι : Type*} (candidates : Finset ι)
    (T : ι → SlopeBox) (level cell : ι → ℤ) (q : ℤ) (unit K C eta : ℝ)
    (hunit : 0 < unit) (hK : 0 ≤ K) (hC : 0 ≤ C) (heta : 0 < eta)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (hE : MeasurableSet E)
    (hEfinite : (volume.prod volume) E ≠ ∞) (hu : Measurable u)
    (horder : ∀ i ∈ candidates, ∀ j ∈ candidates,
      (T i).length ≤ (T j).length → level j ≤ level i)
    (hwidth : ∀ i ∈ candidates, ∀ j ∈ candidates, (T i).width = (T j).width)
    (hslope : ∀ i ∈ candidates,
      (T i).slope ∈ scaledAngularCell unit q (level i) (cell i))
    (hangular : ∀ i ∈ candidates,
      (unit*DyadicLineGrid.scale (level i))*(T i).length ≤ C*(T i).width)
    (hmass : ∀ i ∈ candidates, eta*(T i).area ≤
      (volume.prod volume).real
        (densityTest E u (T i) (scaledAngularCell unit q (level i) (cell i)) K)) :
    ∃ keepers : Finset ι, keepers ⊆ candidates ∧
      (∀ i ∈ keepers, MeasurableSet
        (densityTest E u (T i) (scaledAngularCell unit q (level i) (cell i)) K)) ∧
      Set.PairwiseDisjoint (keepers : Set ι)
        (fun i => densityTest E u (T i) (scaledAngularCell unit q (level i) (cell i)) K) ∧
      (∑ i ∈ keepers, (T i).area) ≤ (volume.prod volume).real E/eta ∧
      (∀ i ∈ keepers, ∀ z ∈ densityTest E u (T i)
          (scaledAngularCell unit q (level i) (cell i)) K,
        z ∈ E ∧ |u z-(T i).slope| ≤ unit*DyadicLineGrid.scale (level i)) ∧
      (∀ i ∈ candidates, ∃ j ∈ keepers,
        (T i).length ≤ (T j).length ∧
        scaledAngularCell unit q (level j) (cell j) ⊆
          scaledAngularCell unit q (level i) (cell i) ∧
        densitySpatialBox (T i) K ⊆ densitySpatialBox (T j) ((3+2*C)*K)) := by
  let omega := fun i => scaledAngularCell unit q (level i) (cell i)
  obtain ⟨keepers,hsub,hdisj,hcover⟩ := exists_density_keepers candidates T omega K hK
    (fun i _ => scaledAngularCell_nonempty hunit q (level i) (cell i))
  have hm (i : ι) : MeasurableSet (densityTest E u (T i) (omega i) K) :=
    densityTest_measurable hE hu (scaledAngularCell_measurable unit q (level i) (cell i)) (T i) K
  refine ⟨keepers,hsub,fun i _ => hm i,?_,?_,?_,?_⟩
  · intro i hi j hj hij
    exact densityTest_disjoint_of_not_conflict E u T omega K (hdisj i hi j hj hij)
  · exact density_keeper_area_budget keepers T omega K eta E u heta hEfinite hdisj
      (fun i _ => hm i) (fun i hi => hmass i (hsub hi))
  · intro i hi z hz
    refine ⟨hz.1.1,?_⟩
    exact scaledAngularCell_slope hunit (le_refl (level i))
      ⟨(T i).slope,hslope i (hsub hi),hslope i (hsub hi)⟩ hz.2 (hslope i (hsub hi))
  · intro i hi
    obtain ⟨j,hj,hlen,hconflict⟩ := hcover i hi
    have hjc := hsub hj
    have hlevels := horder i hi j hjc hlen
    have hnested : omega j ⊆ omega i := scaledAngularCell_subset hlevels hconflict.2
    have hs : |(T i).slope-(T j).slope| * (T i).length ≤ C*(T j).width := by
      calc
        _ ≤ (unit*DyadicLineGrid.scale (level i))*(T i).length :=
          mul_le_mul_of_nonneg_right
            (scaledAngularCell_slope hunit hlevels hconflict.2 (hslope i hi) (hslope j hjc))
            (T i).length_pos.le
        _ ≤ C*(T i).width := hangular i hi
        _ = _ := by rw [hwidth i hi j hjc]
    exact ⟨j,hj,hlen,hnested,density_box_subset_keeper (T i) (T j) hK hC hlen
      (hwidth i hi j hjc) hs hconflict.1⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density kernel has a quantitative tail outside a dilated slope
box. This turns a weighted density test into the unweighted witness used
by the finite keeper construction. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace LipschitzHilbert
namespace SlopeBox

theorem densityKernel_nonneg (T : SlopeBox) (D : ℝ) (z : ℝ×ℝ) :
    0 ≤ T.densityKernel D z := Real.rpow_nonneg (by linarith [T.radius_nonnegative z]) _

theorem densityKernel_le_one (T : SlopeBox) {D : ℝ} (hD : 0 ≤ D) (z : ℝ×ℝ) :
    T.densityKernel D z ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [T.radius_nonnegative z]) (neg_nonpos.mpr hD)

theorem densityKernel_eq_weight (T : SlopeBox) (D : ℝ) (z : ℝ×ℝ) :
    T.densityKernel D z = ((2:ℝ)^D)⁻¹*T.weight 1 D z := by
  have htwo : (2:ℝ)^D ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) D).ne'
  simp only [densityKernel,weight,div_one,←mul_assoc,inv_mul_cancel₀ htwo,one_mul]

theorem densityKernel_integrable (T : SlopeBox) {D : ℝ} (hD : 2 < D) :
    Integrable (T.densityKernel D) (volume.prod volume) := by
  have h := (T.weight_integrable (by norm_num : (0:ℝ)<1) hD).const_mul (((2:ℝ)^D)⁻¹)
  exact h.congr (Eventually.of_forall (fun z => (T.densityKernel_eq_weight D z).symm))

theorem integral_densityKernel (T : SlopeBox) (D : ℝ) :
    (∫ z, T.densityKernel D z ∂volume.prod volume) =
      (∫ z, topProfile D z ∂volume.prod volume)*T.area := by
  simp_rw [T.densityKernel_eq_weight D]
  rw [integral_const_mul,T.integral_weight (by norm_num : (0:ℝ)<1) D]
  have htwo : (2:ℝ)^D ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) D).ne'
  simp only [one_pow,mul_one,SlopeBox.area]
  field_simp [htwo]

end SlopeBox

theorem densitySpatialBox_iff (T : SlopeBox) (K : ℝ) (z : ℝ×ℝ) :
    z ∈ densitySpatialBox T K ↔ |T.horizontal z| ≤ K ∧ |T.transverse z| ≤ K := by
  simp only [densitySpatialBox,mem_ofPred_eq,SlopeBox.horizontal,SlopeBox.transverse,
    abs_div,abs_of_pos T.length_pos,abs_of_pos T.width_pos,
    div_le_iff₀ T.length_pos,div_le_iff₀ T.width_pos]

theorem densitySpatialBox_radius_lt (T : SlopeBox) (K : ℝ) {z : ℝ×ℝ}
    (hz : z ∉ densitySpatialBox T K) : K < T.radius z := by
  by_contra h
  have hr : T.radius z ≤ K := le_of_not_gt h
  apply hz
  rw [densitySpatialBox_iff]
  constructor
  · exact (le_add_of_nonneg_right (abs_nonneg _)).trans hr
  · exact (le_add_of_nonneg_left (abs_nonneg _)).trans hr

theorem densityKernel_tail (T : SlopeBox) {K D : ℝ} (hK : 1 ≤ K) (hD : 3 ≤ D) :
    (∫ z in (densitySpatialBox T K)ᶜ, T.densityKernel D z ∂volume.prod volume) ≤
      K^(3-D)*(∫ z, topProfile 3 z ∂volume.prod volume)*T.area := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hker := T.densityKernel_integrable (by linarith : 2 < D)
  have hthree := T.densityKernel_integrable (by norm_num : (2:ℝ)<3)
  have hpoint (z : ℝ×ℝ) (hz : z ∈ (densitySpatialBox T K)ᶜ) :
      T.densityKernel D z ≤ K^(3-D)*T.densityKernel 3 z := by
    have hr : K ≤ 1+T.radius z := by linarith [densitySpatialBox_radius_lt T K hz]
    have hb : 0 < 1+T.radius z := by linarith [T.radius_nonnegative z]
    have hp := Real.rpow_le_rpow_of_nonpos hKpos hr (by linarith : 3-D ≤ 0)
    calc
      _ = (1+T.radius z)^(3-D)*T.densityKernel 3 z := by
        unfold SlopeBox.densityKernel
        rw [← Real.rpow_add hb]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (T.densityKernel_nonneg 3 z)
  calc
    _ ≤ ∫ z in (densitySpatialBox T K)ᶜ, K^(3-D)*T.densityKernel 3 z ∂volume.prod volume :=
      setIntegral_mono_on hker.integrableOn (hthree.const_mul _).integrableOn
        (densitySpatialBox_measurable T K).compl hpoint
    _ ≤ ∫ z, K^(3-D)*T.densityKernel 3 z ∂volume.prod volume :=
      setIntegral_le_integral (hthree.const_mul _) (Eventually.of_forall
        (fun z => mul_nonneg (Real.rpow_nonneg hKpos.le _) (T.densityKernel_nonneg 3 z)))
    _ = _ := by rw [integral_const_mul,T.integral_densityKernel 3]; ring

theorem density_witness_mass (T : SlopeBox) {K D eta : ℝ}
    (hK : 1 ≤ K) (hD : 3 ≤ D) (_heta : 0 ≤ eta)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (omega : Set ℝ)
    (hE : MeasurableSet E) (hEfinite : (volume.prod volume) E ≠ ∞)
    (hu : Measurable u) (homega : MeasurableSet omega)
    (htail : K^(3-D)*(∫ z, topProfile 3 z ∂volume.prod volume) ≤ eta/2)
    (hdensity : eta*T.area ≤ ∫ z in E ∩ u ⁻¹' omega,
      T.densityKernel D z ∂volume.prod volume) :
    (eta/2)*T.area ≤ (volume.prod volume).real (densityTest E u T omega K) := by
  let A := E ∩ u ⁻¹' omega
  have hA : MeasurableSet A := hE.inter (hu homega)
  have hker := T.densityKernel_integrable (by linarith : 2 < D)
  have hbox := densitySpatialBox_measurable T K
  have hsplit := integral_inter_add_sdiff hbox (hker.integrableOn :
    IntegrableOn (T.densityKernel D) A (volume.prod volume))
  have htest : A ∩ densitySpatialBox T K = densityTest E u T omega K := by
    ext z
    exact and_right_comm
  have htestFinite : (volume.prod volume) (A ∩ densitySpatialBox T K) ≠ ∞ :=
    measure_ne_top_of_subset (fun _ hz => hz.1.1) hEfinite
  have hinside : (∫ z in A ∩ densitySpatialBox T K, T.densityKernel D z ∂volume.prod volume) ≤
      (volume.prod volume).real (A ∩ densitySpatialBox T K) := by
    have h := setIntegral_mono_on hker.integrableOn
      (integrableOn_const htestFinite : IntegrableOn (fun _ : ℝ×ℝ => (1:ℝ))
        (A ∩ densitySpatialBox T K) (volume.prod volume)) (hA.inter hbox)
      (fun z _ => T.densityKernel_le_one (by linarith : 0 ≤ D) z)
    simpa only [setIntegral_const,smul_eq_mul,mul_one] using h
  have houtside : (∫ z in A\densitySpatialBox T K, T.densityKernel D z ∂volume.prod volume) ≤
      (eta/2)*T.area := by
    have hmono := setIntegral_mono_set
      (hker.integrableOn : IntegrableOn (T.densityKernel D) (densitySpatialBox T K)ᶜ (volume.prod volume))
      (Eventually.of_forall (fun z => T.densityKernel_nonneg D z))
      (Eventually.of_forall (fun z (hz : z ∈ A\densitySpatialBox T K) => hz.2))
    exact hmono.trans ((densityKernel_tail T hK hD).trans
      (mul_le_mul_of_nonneg_right htail (by exact mul_nonneg T.length_pos.le T.width_pos.le)))
  rw [htest] at hinside
  rw [htest] at hsplit
  linarith

/-- A fixed decay order gives the manuscript's small polynomial spatial
enlargement at every polynomial density threshold. -/
theorem density_tail_at_power_scale (a : ℝ) (ha : 0 ≤ a) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      (L^(a/100+1))^(3-(203:ℝ))*(∫ z, topProfile 3 z ∂volume.prod volume) ≤ L^(-a)/2 := by
  let C := ∫ z, topProfile 3 z ∂volume.prod volume
  have hC : 0 ≤ C := integral_nonneg (topProfile_nonnegative 3)
  refine ⟨max 1 (2*C),le_max_left _ _,?_⟩
  intro L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hCL : 2*C ≤ L := (le_max_right _ _).trans hL
  have hratio : C/L ≤ (1/2:ℝ) := (div_le_iff₀ hLpos).mpr (by linarith)
  have hpower : (L^(a/100+1))^(3-(203:ℝ)) = L^(-2*a-200) := by
    rw [← Real.rpow_mul hLpos.le]
    congr 1
    ring
  change (L^(a/100+1))^(3-(203:ℝ))*C ≤ L^(-a)/2
  rw [hpower]
  calc
    _ ≤ L^(-a-1)*C := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hC
    _ = L^(-a)*(C/L) := by
      rw [sub_eq_add_neg,Real.rpow_add hLpos,Real.rpow_neg_one]
      ring
    _ ≤ L^(-a)*(1/2) := mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hLpos.le _)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityPowerForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At the manuscript's polynomial density threshold, the selected actual
witnesses obey the polynomial radius, precision and area hypotheses used
by concentration. The threshold is fixed before all finite data. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem density_dyadic_length_order {w : ℝ} (hw : 0 < w) {i j : ℤ}
    (h : w/DyadicLineGrid.scale i ≤ w/DyadicLineGrid.scale j) : j ≤ i := by
  have hmul := (div_le_div_iff₀ (DyadicLineGrid.scale_pos i) (DyadicLineGrid.scale_pos j)).mp h
  have hscale : DyadicLineGrid.scale j ≤ DyadicLineGrid.scale i :=
    (mul_le_mul_iff_right₀ hw).mp (by simpa only [mul_comm] using hmul)
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp hscale

theorem densitySpatialBox_radius_le (T : SlopeBox) (K : ℝ) {z : ℝ×ℝ}
    (hz : z ∈ densitySpatialBox T K) : T.radius z ≤ 2*K := by
  have h := (densitySpatialBox_iff T K z).mp hz
  change |T.horizontal z|+|T.transverse z| ≤ 2*K
  linarith [h.1,h.2]

theorem exists_power_density_forest (a : ℝ) (ha : 0 ≤ a) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (ι : Type*) (candidates : Finset ι) (T : ι → SlopeBox)
      (level cell : ι → ℤ) (q : ℤ) (ell0 w W : ℝ), 0 < ell0 → 0 < w → 12*w ≤ W →
      (∀ i ∈ candidates, (T i).length = ell0/DyadicLineGrid.scale (level i)) →
      (∀ i ∈ candidates, (T i).width = W) →
      (∀ i ∈ candidates, (T i).slope ∈ scaledAngularCell (w/ell0) q (level i) (cell i)) →
    ∀ (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ), MeasurableSet E →
      (volume.prod volume) E ≠ ∞ → Measurable u →
      (∀ i ∈ candidates, L^(-a)*(T i).area ≤ ∫ z in E ∩
        u ⁻¹' scaledAngularCell (w/ell0) q (level i) (cell i), (T i).densityKernel 203 z
        ∂volume.prod volume) →
      let K := L^(a/100+1)
      let witness := fun i => densityTest E u (T i) (scaledAngularCell (w/ell0) q (level i) (cell i)) K
      ∃ keepers : Finset ι, keepers ⊆ candidates ∧
        (∀ i ∈ keepers, MeasurableSet (witness i)) ∧
        Set.PairwiseDisjoint (keepers : Set ι) witness ∧
        (∑ i ∈ keepers, (T i).area) ≤ 2*L^a*(volume.prod volume).real E ∧
        (∀ i ∈ keepers, L^(-(a+2))*(T i).area ≤ (volume.prod volume).real (witness i)) ∧
        (∀ i ∈ keepers, ∀ z ∈ witness i, z ∈ E ∧ (T i).radius z ≤ L^(a+2) ∧
          |u z-(T i).slope| ≤ w/(T i).length ∧
          |u z-(T i).slope| ≤ (T i).width/(12*(T i).length)) ∧
        (∀ i ∈ candidates, ∃ j ∈ keepers, (T i).length ≤ (T j).length ∧
          scaledAngularCell (w/ell0) q (level j) (cell j) ⊆ scaledAngularCell (w/ell0) q (level i) (cell i) ∧
          ∀ z ∈ densitySpatialBox (T i) K, (T j).radius z ≤ L^(a+2)) := by
  obtain ⟨Ltail,hLtail,htail⟩ := density_tail_at_power_scale a ha
  refine ⟨max Ltail 10,by linarith [le_max_right Ltail (10:ℝ)],?_⟩
  intro L hL ι candidates T level cell q ell0 w W hell0 hw hW hlength hwidth hslope E u hE hEfin hu hdensity
    K witness
  have hLt : Ltail ≤ L := (le_max_left _ _).trans hL
  have hL10 : 10 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hK : 1 ≤ K := Real.one_le_rpow hL1 (by linarith)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKb : 10*K ≤ L^(a+2) := by
    calc
      _ ≤ L*K := mul_le_mul_of_nonneg_right hL10 hKpos.le
      _ = L^(a/100+2) := by
        dsimp only [K]
        conv_lhs => lhs; rw [← Real.rpow_one L]
        rw [← Real.rpow_add hLp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hmass (i : ι) (hi : i ∈ candidates) : (L^(-a)/2)*(T i).area ≤
      (volume.prod volume).real (witness i) :=
    density_witness_mass (T i) hK (by norm_num) (Real.rpow_nonneg hLp.le _)
      E u (scaledAngularCell (w/ell0) q (level i) (cell i)) hE hEfin hu
      (scaledAngularCell_measurable (w/ell0) q (level i) (cell i))
      (htail L hLt) (hdensity i hi)
  have horder (i : ι) (hi : i ∈ candidates) (j : ι) (hj : j ∈ candidates)
      (hij : (T i).length ≤ (T j).length) : level j ≤ level i :=
    density_dyadic_length_order hell0 (by simpa only [hlength i hi,hlength j hj] using hij)
  have hang (i : ι) (hi : i ∈ candidates) :
      ((w/ell0)*DyadicLineGrid.scale (level i))*(T i).length ≤ 1*(T i).width := by
    rw [hlength i hi,hwidth i hi,one_mul]
    have hs := DyadicLineGrid.scale_pos (level i)
    have heq : ((w/ell0)*DyadicLineGrid.scale (level i))*(ell0/DyadicLineGrid.scale (level i)) = w := by
      field_simp [hell0.ne',hs.ne']
    rw [heq]
    linarith
  obtain ⟨keepers,hsub,hmeas,hdisj,harea,hinside,hcover⟩ := exists_scaled_dyadic_density_forest
    candidates T level cell q (w/ell0) K 1 (L^(-a)/2) (div_pos hw hell0) hKpos.le (by norm_num) (by positivity)
    E u hE hEfin hu horder
    (fun i hi j hj => (hwidth i hi).trans (hwidth j hj).symm) hslope hang hmass
  have hlower : L^(-(a+2)) ≤ L^(-a)/2 := by
    calc
      _ ≤ L^(-a-1) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L^(-a)/L := by
        rw [sub_eq_add_neg,Real.rpow_add hLp,Real.rpow_neg_one]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hLp.le _) (by norm_num) (by linarith)
  refine ⟨keepers,hsub,hmeas,hdisj,?_,?_,?_,?_⟩
  · apply harea.trans_eq
    rw [Real.rpow_neg hLp.le]
    field_simp [(Real.rpow_pos_of_pos hLp a).ne']
  · intro i hi
    exact (mul_le_mul_of_nonneg_right hlower (T i).area_pos.le).trans (hmass i (hsub hi))
  · intro i hi z hz
    have hs := hinside i hi z hz
    have hrad := densitySpatialBox_radius_le (T i) K hz.1.2
    have hprec : |u z-(T i).slope| ≤ w/(T i).length := by
      convert hs.2 using 1
      all_goals try with_reducible_and_instances rfl
      rw [hlength i (hsub hi)]
      field_simp [hw.ne',hell0.ne',(DyadicLineGrid.scale_pos (level i)).ne']
    refine ⟨hs.1,hrad.trans (by linarith),hprec,hprec.trans ?_⟩
    rw [hwidth i (hsub hi)]
    apply (div_le_div_iff₀ (T i).length_pos (mul_pos (by norm_num) (T i).length_pos)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hW (T i).length_pos.le]
  · intro i hi
    obtain ⟨j,hj,hlen,hnested,hboxes⟩ := hcover i hi
    refine ⟨j,hj,hlen,hnested,?_⟩
    intro z hz
    have hr := densitySpatialBox_radius_le (T j) ((3+2*(1:ℝ))*K) (hboxes hz)
    exact hr.trans (by nlinarith)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceDensityPacketGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the actual density-forest radial assignment into the two
coordinate bounds required by original-packet concentration. -/
noncomputable section
namespace LipschitzHilbert

theorem SlopeBox.coordinates_of_radius_le (T : SlopeBox) {z : ℝ×ℝ} {K : ℝ}
    (h : T.radius z ≤ K) :
    |z.1-T.x| ≤ K*T.length ∧ |(z.2-T.y)-T.slope*(z.1-T.x)| ≤ K*T.width := by
  have hx : |T.horizontal z| ≤ K :=
    (le_add_of_nonneg_right (abs_nonneg (T.transverse z))).trans h
  have hy : |T.transverse z| ≤ K :=
    (le_add_of_nonneg_left (abs_nonneg (T.horizontal z))).trans h
  change |(z.1-T.x)/T.length| ≤ K at hx
  change |((z.2-T.y)-T.slope*(z.1-T.x))/T.width| ≤ K at hy
  rw [abs_div,abs_of_pos T.length_pos] at hx
  rw [abs_div,abs_of_pos T.width_pos] at hy
  exact ⟨(div_le_iff₀ T.length_pos).mp hx,(div_le_iff₀ T.width_pos).mp hy⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary density is the supremum of the manuscript's actual
weighted box tests. Exceeding a threshold supplies a concrete test, which
can then be fed to the finite keeper construction. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem densityAverage_le (T : SlopeBox) (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ)
    (omega : Set ℝ) : densityAverage T E u omega ≤ ∫ z, topProfile 203 z ∂volume.prod volume := by
  unfold densityAverage
  apply (div_le_iff₀ T.area_pos).mpr
  have h := setIntegral_le_integral (s := E ∩ u ⁻¹' omega)
    (T.densityKernel_integrable (by norm_num : (2:ℝ)<203))
    (Filter.Eventually.of_forall (fun z => T.densityKernel_nonneg 203 z))
  exact h.trans_eq (T.integral_densityKernel 203)

namespace OrdinaryDensityTile

theorem densityValues_nonempty (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    (tile.densityValues ell0 w W tau q E u).Nonempty := ⟨0,Or.inl rfl⟩

theorem densityValues_bddAbove (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    BddAbove (tile.densityValues ell0 w W tau q E u) := by
  refine ⟨∫ z, topProfile 203 z ∂volume.prod volume,?_⟩
  intro x hx
  rcases hx with rfl | ⟨test,rfl⟩
  · exact integral_nonneg (topProfile_nonnegative 203)
  · exact densityAverage_le test.top E u _

theorem density_le (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    tile.density ell0 w W tau q E u ≤ ∫ z, topProfile 203 z ∂volume.prod volume := by
  apply csSup_le (tile.densityValues_nonempty ell0 w W tau q E u)
  intro x hx
  rcases hx with rfl | ⟨test,rfl⟩
  · exact integral_nonneg (topProfile_nonnegative 203)
  · exact densityAverage_le test.top E u _

theorem exists_test_of_lt_density (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) {eta : ℝ} (heta : 0 ≤ eta)
    (h : eta < tile.density ell0 w W tau q E u) :
    ∃ test : OrdinaryDensityTest ell0 w W tau q tile,
      eta*test.top.area < ∫ z in E ∩
        u ⁻¹' scaledAngularCell (w/ell0) q test.level test.cell,
        test.top.densityKernel 203 z ∂volume.prod volume := by
  obtain ⟨x,hx,hlt⟩ := (lt_csSup_iff
    (tile.densityValues_bddAbove ell0 w W tau q E u)
    (tile.densityValues_nonempty ell0 w W tau q E u)).mp h
  rcases hx with rfl | ⟨test,rfl⟩
  · exact (not_lt_of_ge heta hlt).elim
  · exact ⟨test,(lt_div_iff₀ test.top.area_pos).mp hlt⟩

end OrdinaryDensityTile
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceHighDensityForest
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High ordinary density supplies concrete tests and then a finite
popular forest. Every tile receives a keeper whose direction belongs to
the tile's original dyadic interval. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem densitySpatialBox_mono (T : SlopeBox) {K K' : ℝ} (h : K ≤ K') :
    densitySpatialBox T K ⊆ densitySpatialBox T K' := by
  intro z hz
  exact ⟨hz.1.trans (mul_le_mul_of_nonneg_right h T.length_pos.le),
    hz.2.trans (mul_le_mul_of_nonneg_right h T.width_pos.le)⟩

theorem exists_high_density_forest (a : ℝ) (ha : 0 ≤ a) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (ι : Type*) (tiles : Finset ι) (tile : ι → OrdinaryDensityTile)
      (ell0 w W tau : ℝ) (q : ℤ), 0 < ell0 → 0 < w → 12*w ≤ W →
    ∀ (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ), MeasurableSet E →
      (volume.prod volume) E ≠ ∞ → Measurable u →
      (∀ i ∈ tiles, L^(-a) < (tile i).density ell0 w W tau q E u) →
    ∃ (test : ∀ i : tiles, OrdinaryDensityTest ell0 w W tau q (tile i))
      (keepers : Finset tiles) (assigned : tiles → keepers),
      let witness := fun i : tiles => densityTest E u (test i).top
        (scaledAngularCell (w/ell0) q (test i).level (test i).cell) (L^(a/100+1))
      (∀ i ∈ keepers, MeasurableSet (witness i)) ∧
      Set.PairwiseDisjoint (keepers : Set tiles) witness ∧
      (∑ i ∈ keepers, (test i).top.area) ≤ 2*L^a*(volume.prod volume).real E ∧
      (∀ i ∈ keepers, L^(-(a+2))*(test i).top.area ≤ (volume.prod volume).real (witness i)) ∧
      (∀ i ∈ keepers, ∀ z ∈ witness i, z ∈ E ∧ (test i).top.radius z ≤ L^(a+2) ∧
        |u z-(test i).top.slope| ≤ w/(test i).top.length ∧
        |u z-(test i).top.slope| ≤ (test i).top.width/(12*(test i).top.length)) ∧
      (∀ i : tiles,
        ell0/DyadicLineGrid.scale (tile i).level ≤ (test (assigned i).val).top.length ∧
        (test (assigned i).val).top.radius (tile i).center ≤ L^(a+2) ∧
        (test (assigned i).val).top.slope ∈
          scaledAngularCell (w/ell0) q (tile i).level (tile i).cell) := by
  classical
  obtain ⟨L0,hL0,hforest⟩ := exists_power_density_forest a ha
  refine ⟨L0,hL0,?_⟩
  intro L hL ι tiles tile ell0 w W tau q hell0 hw hW E u hE hEfin hu hdensity
  have hLp : 0 < L := by linarith [hL0.trans hL]
  have hL1 : 1 ≤ L := by linarith [hL0.trans hL]
  have htest (i : tiles) : ∃ test : OrdinaryDensityTest ell0 w W tau q (tile i),
      L^(-a)*test.top.area < ∫ z in E ∩
        u ⁻¹' scaledAngularCell (w/ell0) q test.level test.cell,
        test.top.densityKernel 203 z ∂volume.prod volume :=
    (tile i).exists_test_of_lt_density ell0 w W tau q E u (Real.rpow_nonneg hLp.le _)
      (hdensity i i.property)
  let test := fun i : tiles => Classical.choose (htest i)
  have hchosen (i : tiles) := Classical.choose_spec (htest i)
  obtain ⟨keepers,hsub,hmeas,hdisj,harea,hsize,hinside,hcover⟩ := hforest L hL tiles
    Finset.univ (fun i => (test i).top) (fun i => (test i).level) (fun i => (test i).cell)
    q ell0 w W hell0 hw hW (fun i _ => (test i).length_eq) (fun i _ => (test i).width_eq)
    (fun i _ => (test i).slope_mem_self) E u hE hEfin hu (fun i _ => (hchosen i).le)
  let assigned : tiles → keepers := fun i =>
    ⟨Classical.choose (hcover i (Finset.mem_univ i)),
      (Classical.choose_spec (hcover i (Finset.mem_univ i))).1⟩
  refine ⟨test,keepers,assigned,hmeas,hdisj,harea,hsize,hinside,?_⟩
  intro i
  have hassigned := (Classical.choose_spec (hcover i (Finset.mem_univ i))).2
  change (test i).top.length ≤ (test (assigned i).val).top.length ∧
      scaledAngularCell (w/ell0) q (test (assigned i).val).level (test (assigned i).val).cell ⊆
        scaledAngularCell (w/ell0) q (test i).level (test i).cell ∧
      ∀ z ∈ densitySpatialBox (test i).top (L^(a/100+1)),
        (test (assigned i).val).top.radius z ≤ L^(a+2) at hassigned
  have hK : (1/2:ℝ) ≤ L^(a/100+1) :=
    (by norm_num : (1/2:ℝ) ≤ 1).trans (Real.one_le_rpow hL1 (by linarith))
  have hcenter := densitySpatialBox_mono (test i).top hK (test i).center_mem
  have hlevels : (test i).level ≤ (tile i).level := density_dyadic_length_order hell0
    (by simpa only [(test i).length_eq] using (test i).tile_length_le)
  have hnested : scaledAngularCell (w/ell0) q (test i).level (test i).cell ⊆
      scaledAngularCell (w/ell0) q (tile i).level (tile i).cell :=
    scaledAngularCell_subset hlevels
      ⟨(test i).top.slope,(test i).slope_mem_tile,(test i).slope_mem_self⟩
  exact ⟨(test i).tile_length_le.trans hassigned.1,hassigned.2.2 _ hcenter,
    hnested (hassigned.2.1 (test (assigned i).val).slope_mem_self)⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataOrdinaryDensityForest
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary density selection, retaining its sharp witness radius
and original angular cells. Empty packet sets require no dummy keeper. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem densityTile_length (P : PacketLatticeData N κ Label Item) (oldSlope : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (q : P.PacketIndex) :
    P.topLength/DyadicLineGrid.scale (P.densityTile oldSlope cell q).level = P.length q.1 := by
  simp only [densityTile,DyadicLineGrid.scale,zpow_natCast,PacketLatticeData.length]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedBandSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized coordinates and support geometry in the packet
representation of the annular band multiplier (§2). -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

/-- The wave slopes stay in a fixed multiple of the angular scale
around the lattice label. -/
theorem frequency_slope_margin (l w xi eta theta c C : ℝ)
    (hl : 0<l) (hw : 0<w) (hc : 0 < c) (hC : 0≤C)
    (hV : c≤w*eta) (hX : |symbolX l xi eta theta|≤C) :
    |(-xi/eta)-theta|≤(C/c)*(w/l) := by
  have heta : 0<eta := pos_of_mul_pos_right (hc.trans_le hV) hw.le
  have hscale : |(-xi/eta)-theta|=|symbolX l xi eta theta|/(l*eta) := by
    unfold symbolX
    rw [abs_mul, abs_of_pos hl]
    have hid : -xi/eta-theta=-(xi+theta*eta)/eta := by field_simp; ring
    rw [hid, abs_div, abs_neg, abs_of_pos heta]
    field_simp
  rw [hscale]
  apply (div_le_iff₀ (mul_pos hl heta)).2
  calc
    _ ≤ C := hX
    _ ≤ (C/c)*(w/l)*(l*eta) := by
      have hb : C≤(C/c)*(w*eta) := by
        calc
          C = (C/c)*c := by field_simp
          _ ≤ (C/c)*(w*eta) := mul_le_mul_of_nonneg_left hV (div_nonneg hC hc.le)
      convert hb using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceThreeGridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal three-grid covering lemma for the nested alternating
one-third grids. It supplies the interval comparison in the maximal
kernel estimate. -/
noncomputable section
open Set
namespace LipschitzHilbert.DyadicLineGrid

theorem shift_signed_third (k : ℤ) : shift (k.negOnePow:ℤ) k=1/3 := by
  simp only [shift,←Units.val_mul,Int.units_mul_self,Units.val_one,Int.cast_one]

theorem signed_third_in_range (k : ℤ) : (k.negOnePow:ℤ)∈Finset.Icc (-1) 1 := by
  rw [Finset.mem_Icc]
  exact abs_le.mp (le_of_eq (Int.abs_negOnePow k))

/-- A closed interval of radius less than one sixth of a grid cell
fits in a cell of one of the three fixed nested grids. -/
theorem exists_three_grid_cover (k : ℤ) (c r : ℝ) (_hr : 0 ≤ r)
    (hsmall : 6*r < scale k) :
    ∃ q∈Finset.Icc (-1) 1, ∃ j : ℤ, Icc (c-r) (c+r)⊆cell q k j := by
  let m := index 0 k c
  let a := left 0 k m
  have hc := mem_index_cell 0 k c
  have hright : left 0 k (m+1)=a+scale k := by
    dsimp [a,left,shift]
    push_cast
    ring
  change a ≤ c ∧ c<left 0 k (m+1) at hc
  rw [hright] at hc
  by_cases hleft : a ≤ c-r
  · by_cases hend : c+r<a+scale k
    · refine ⟨0,by simp, m,?_⟩
      intro x hx
      exact ⟨hleft.trans hx.1,hx.2.trans_lt (by simpa only [hright] using hend)⟩
    · refine ⟨(k.negOnePow:ℤ),signed_third_in_range k,m,?_⟩
      intro x hx
      change left (k.negOnePow:ℤ) k m≤x ∧ x<left (k.negOnePow:ℤ) k (m+1)
      have hl : left (k.negOnePow:ℤ) k m=a+scale k/3 := by
        simp only [left,shift_signed_third]
        dsimp [a,left,shift]
        push_cast
        ring
      have hu : left (k.negOnePow:ℤ) k (m+1)=a+4*scale k/3 := by
        simp only [left,shift_signed_third]
        dsimp [a,left,shift]
        push_cast
        ring
      rw [hl,hu]
      constructor <;> linarith [hx.1,hx.2]
  · refine ⟨(k.negOnePow:ℤ),signed_third_in_range k,m-1,?_⟩
    intro x hx
    change left (k.negOnePow:ℤ) k (m-1)≤x ∧
      x<left (k.negOnePow:ℤ) k (m-1+1)
    have hl : left (k.negOnePow:ℤ) k (m-1)=a-2*scale k/3 := by
      simp only [left,shift_signed_third]
      dsimp [a,left,shift]
      push_cast
      ring
    have hu : left (k.negOnePow:ℤ) k (m-1+1)=a+scale k/3 := by
      simp only [left,shift_signed_third]
      dsimp [a,left,shift]
      push_cast
      ring
    rw [hl,hu]
    constructor <;> linarith [hx.1,hx.2]

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketAngularCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-scale angular cells containing both the packet spectrum and
its selector support. The three nested grids are the existing literal
alternating one-third grids. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketRepresentation

theorem exists_scaled_three_grid_cover (unit : ℝ) (hu : 0<unit)
    (k : ℤ) (c r : ℝ) (hr : 0 ≤ r)
    (hsmall : 6*r<unit*DyadicLineGrid.scale k) :
    ∃ grid∈Finset.Icc (-1) 1, ∃ cell : ℤ,
      Icc (c-r) (c+r) ⊆ scaledAngularCell unit grid k cell := by
  have hs : 6*(r/unit)<DyadicLineGrid.scale k := by
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ hu).2
    simpa only [mul_comm] using hsmall
  obtain ⟨grid,hg,cell,hc⟩ := DyadicLineGrid.exists_three_grid_cover k
    (c/unit) (r/unit) (div_nonneg hr hu.le) hs
  refine ⟨grid,hg,cell,?_⟩
  intro x hx
  apply hc
  constructor
  · have h := (div_le_div_iff_of_pos_right hu).mpr hx.1
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have h := (div_le_div_iff_of_pos_right hu).mpr hx.2
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring

theorem frequency_margin_subset {S : Set ℝ} (l w xi eta theta c C margin : ℝ)
    (hl : 0<l) (hw : 0<w) (hc : 0 < c) (hC : 0≤C) (_hm : 0 ≤ margin)
    (hV : c≤w*eta) (hX : |symbolX l xi eta theta|≤C)
    (hcell : Icc (theta-(C/c+margin)*(w/l))
      (theta+(C/c+margin)*(w/l)) ⊆ S) :
    Icc (-xi/eta-margin*(w/l)) (-xi/eta+margin*(w/l)) ⊆ S := by
  have hs := abs_le.mp (frequency_slope_margin l w xi eta theta c C hl hw hc hC hV hX)
  intro s hs'
  apply hcell
  constructor <;> nlinarith only [hs.1,hs.2,hs'.1,hs'.2]

/-- A single selected angular cell contains the selector support and the
entire spectrum with the requested margin. -/
theorem exists_packet_angular_cell (unit : ℝ) (hu : 0<unit) (k : ℤ)
    (l w theta c C margin radius : ℝ) (hl : 0<l) (hw : 0<w)
    (hc : 0 < c) (hC : 0≤C) (hm : 0 ≤ margin) (hr : 0 ≤ radius)
    (hprecision : w/l=unit*DyadicLineGrid.scale k)
    (hsmall : 6*max radius (C/c+margin)<1) :
    ∃ grid∈Finset.Icc (-1) 1, ∃ cell : ℤ,
      (∀ s, |s-theta| ≤ radius*(w/l) → s∈scaledAngularCell unit grid k cell) ∧
      (∀ xi eta, c≤w*eta → |symbolX l xi eta theta|≤C →
        Icc (-xi/eta-margin*(w/l)) (-xi/eta+margin*(w/l)) ⊆
          scaledAngularCell unit grid k cell) := by
  have hd : 0<w/l := div_pos hw hl
  let R := max radius (C/c+margin)
  have hR : 0≤R := hr.trans (le_max_left _ _)
  obtain ⟨grid,hg,cell,hcell⟩ := exists_scaled_three_grid_cover unit hu k theta
    (R*(w/l)) (mul_nonneg hR hd.le) (by
      rw [←hprecision]
      have h := mul_lt_mul_of_pos_right hsmall hd
      convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring)
  refine ⟨grid,hg,cell,?_,?_⟩
  · intro s hs
    apply hcell
    have hs' := abs_le.mp hs
    have hle := mul_le_mul_of_nonneg_right (le_max_left radius (C/c+margin)) hd.le
    constructor <;> dsimp only [R] at * <;> linarith
  · intro xi eta hV hX
    apply frequency_margin_subset l w xi eta theta c C margin hl hw hc hC hm hV hX
    intro s hs
    apply hcell
    have hle := mul_le_mul_of_nonneg_right (le_max_right radius (C/c+margin)) hd.le
    constructor <;> dsimp only [R] at * <;> linarith only [hs.1,hs.2,hle]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceThreeGridMaximal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual interval maximal majorant built from three nested grids.
The exceptional set is independent of the real interval parameters. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.DyadicLineGrid

theorem gridChoice_card : Fintype.card GridChoice=3 := by
  simp [GridChoice]

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketAngularAssignment
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous choice of one of three angular grids for every
label. Its cells carry both the selector and the spectral margin. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem precision_eq_scaled_grid (w : ℝ) (j : Fin N) :
    w/P.length j = (w/P.topLength)*DyadicLineGrid.scale (j.val:ℤ) := by
  rw [length,DyadicLineGrid.scale,zpow_natCast]
  field_simp [P.topLength_pos.ne',pow_ne_zero _ (by norm_num : (2:ℝ)≠0)]

theorem exists_angular_assignment (w cStar cEta margin radius : ℝ)
    (hw : 0<w) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hm : 0 ≤ margin) (hr : 0 ≤ radius)
    (hsmall : 6*max radius (cStar/cEta+margin)<1) :
    ∃ grid : ∀ j, P.labels j → DyadicLineGrid.GridChoice,
    ∃ cell : ∀ j, P.labels j → ℤ,
      ∀ j (l : P.labels j),
        (∀ s, |s-P.rowSlope j l| ≤ radius*(w/P.length j) →
          s∈scaledAngularCell (w/P.topLength) (grid j l).val j.val (cell j l)) ∧
        (∀ xi eta, cEta≤w*eta →
          |xi+P.rowSlope j l*eta| ≤ cStar/P.length j →
          Icc (-xi/eta-margin*(w/P.length j)) (-xi/eta+margin*(w/P.length j)) ⊆
            scaledAngularCell (w/P.topLength) (grid j l).val j.val (cell j l)) := by
  classical
  have h (j : Fin N) (l : P.labels j) :
      ∃ g : DyadicLineGrid.GridChoice, ∃ cell : ℤ,
        (∀ s, |s-P.rowSlope j l| ≤ radius*(w/P.length j) →
          s∈scaledAngularCell (w/P.topLength) g.val j.val cell) ∧
        (∀ xi eta, cEta≤w*eta →
          |xi+P.rowSlope j l*eta| ≤ cStar/P.length j →
          Icc (-xi/eta-margin*(w/P.length j)) (-xi/eta+margin*(w/P.length j)) ⊆
            scaledAngularCell (w/P.topLength) g.val j.val cell) := by
    obtain ⟨g,hg,cell,hsel,hspec⟩ := PacketRepresentation.exists_packet_angular_cell
      (w/P.topLength) (div_pos hw P.topLength_pos) j.val
      (P.length j) w (P.rowSlope j l) cEta cStar margin radius
      (P.length_pos j) hw hcEta hcStar hm hr (P.precision_eq_scaled_grid w j) hsmall
    refine ⟨⟨g,hg⟩,cell,hsel,?_⟩
    intro xi eta hV hX
    apply hspec xi eta hV
    rw [PacketRepresentation.symbolX,abs_mul,abs_of_pos (P.length_pos j)]
    have hh := (le_div_iff₀ (P.length_pos j)).mp hX
    simpa only [mul_comm] using hh
  choose grid cell hcell using h
  exact ⟨grid,cell,hcell⟩

end LipschitzHilbert.PacketLatticeData

namespace LipschitzHilbert.PacketRepresentation

theorem angular_cell_subset_unit (unit : ℝ) (hu : 0<unit) (grid level cell : ℤ)
    (theta : ℝ) (htheta : theta∈scaledAngularCell unit grid level cell)
    (hsmall : |theta|+unit*DyadicLineGrid.scale level≤1) :
    scaledAngularCell unit grid level cell ⊆ Icc (-1) 1 := by
  intro s hs
  have hd := scaledAngularCell_slope hu (le_refl level) ⟨theta,htheta,htheta⟩ hs htheta
  have hb : |s|≤1 := calc
    _ = |(s-theta)+theta| := by congr 1; ring
    _ ≤ |s-theta|+|theta| := abs_add_le _ _
    _ ≤ 1 := by linarith
  exact abs_le.mp hb

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataReferenceSelection
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite portion of an unrestricted packet family inside a reference
cone embeds into the bounded reference lattice without changing a wave.
This is the bridge used after a density keeper has been selected. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem reference_bounds_of_density_cell (oldSlope : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w cone : ℝ)
    (hw : 0<w) (hcone : 1 ≤ cone) (q : P.PacketIndex) (T : SlopeBox)
    (hshort : P.length q.1≤T.length)
    (hrow : oldSlope+P.rowSlope q.1 q.2.1∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (htop : T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    P.length q.1≤T.length ∧
      |oldSlope+P.rowSlope q.1 q.2.1-T.slope| ≤ cone*w/P.length q.1 := by
  refine ⟨hshort,?_⟩
  have hs := scaledAngularCell_slope (div_pos hw P.topLength_pos)
    (le_refl (q.1.val:ℤ)) ⟨oldSlope+P.rowSlope q.1 q.2.1,hrow,hrow⟩ hrow htop
  rw [←P.precision_eq_scaled_grid w q.1] at hs
  apply hs.trans
  apply div_le_div_of_nonneg_right _ (P.length_pos q.1).le
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcone hw.le

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rounded dyadic parameters in the manuscript. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem log_step_bounds {L : ℝ} (hL : 0 ≤ L) :
    L ^ (7 / 10 : ℝ) ≤ Real.log (step L) ∧
      Real.log (step L) ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0 ≤ L ^ (7 / 10 : ℝ) / (2 * Real.log 2) := by positivity
  have hlo := Nat.le_ceil (L ^ (7 / 10 : ℝ) / (2 * Real.log 2))
  have hhi := (Nat.ceil_lt_add_one hr).le
  rw [step, Real.log_pow, stepExponent, Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · have h := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : L ^ (7 / 10 : ℝ) / (2 * Real.log 2) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) := div_mul_cancel₀ _ (by positivity)
    rw [heq] at h
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : (L ^ (7 / 10 : ℝ) / (2 * Real.log 2) + 1) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
      rw [add_mul, div_mul_cancel₀ _ (by positivity), one_mul]
    rw [heq] at h
    nlinarith

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
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

theorem physical_multiplier_analyzing_integrable (t : ℝ) (m : ℝ×ℝ → ℂ)
    (hm : Measurable m) (hm1 : ∀ z, ‖m z‖ ≤ 1)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) :
    Integrable (fun z => g z k*conj (m z*P.physicalPacket t j l u k z))
      (volume.prod volume) := by
  have hgm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply (P.physicalPacket t j l u k).integrable.norm.mono'
    (hgm.mul (continuous_star.measurable.comp
      (hm.mul (P.physicalPacket t j l u k).continuous.measurable))).aestronglyMeasurable
  filter_upwards [] with z
  change ‖g z k*conj (m z*P.physicalPacket t j l u k z)‖ ≤ ‖P.physicalPacket t j l u k z‖
  rw [norm_mul,Complex.norm_conj,norm_mul]
  have hgk : ‖g z k‖ ≤ 1 := (PiLp.norm_apply_le (g z) k).trans (hg1 z)
  calc
    _ ≤ 1*(1*‖P.physicalPacket t j l u k z‖) := mul_le_mul hgk
      (mul_le_mul_of_nonneg_right (hm1 z) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceTransverseTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining transverse tail in the long-tree density estimate:
412 powers in squared energy absorb twice the density loss 203, leaving
the summable sixth power. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem transverseTailConstant_nonneg : 0≤transverseTailConstant :=
  tsum_nonneg (fun _ => by positivity)

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataModelConfig
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed geometric and selector data for the ordinary model. None of
these parameters depends on the input function or the tested set. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem referenceTreeConstant_nonneg (P : PacketLatticeData N κ Label Item)
    (C : ℝ) (B K : ℕ) (Lip : ℝ) (hLip : 0≤Lip) : 0≤P.referenceTreeConstant C B K Lip := by
  have ht := transverseTailConstant_nonneg
  have hp := P.profileBound_pos
  dsimp [referenceTreeConstant,referenceEnvelopeConstant]
  positivity

namespace OrdinaryModelConfig
variable {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

theorem sizeAreaConstant_nonneg (d : OrdinaryModelConfig P initial) (CS : ℝ) :
    0≤d.sizeAreaConstant CS := by
  dsimp [sizeAreaConstant,selectedNearConstant]
  positivity

theorem stepConstant_nonneg (d : OrdinaryModelConfig P initial) (CD CS CT : ℝ) :
    0≤d.stepConstant CD CS CT := by
  have hd := P.referenceTreeConstant_nonneg CD ((2*d.R+1)*d.M) d.K d.Lip d.hLip
  have ht := P.referenceTreeConstant_nonneg CT ((2*d.R+1)*d.M) d.K d.Lip d.hLip
  have hs := d.sizeAreaConstant_nonneg CS
  dsimp only [stepConstant]
  positivity

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceThresholdSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform summation over any finite family of dyadic density thresholds. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem ordinaryThresholdRatio_lt_one : ordinaryThresholdRatio<1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataUniversalEstimate
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit uniform model cost, including zero energy, zero tested
measure, and all positive density thresholds. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

namespace OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

theorem modelCost_pos (d : OrdinaryModelConfig P initial) (CD CS CT : ℝ) :
    0<d.modelCost CD CS CT := by
  have hU : 0<ordinaryDensityUpper := zero_lt_one.trans_le (le_max_left _ _)
  have hD : 0<1-ordinaryThresholdRatio := sub_pos.mpr ordinaryThresholdRatio_lt_one
  have hstep := d.stepConstant_nonneg CD CS CT
  dsimp only [modelCost]
  positivity

end OrdinaryModelConfig

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataModelCostPolynomial
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial dependence of the explicit model cost on the two packet
adaptation bounds. All remaining factors involve fixed geometric data. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem referenceTreeConstant_le_unit (P : PacketLatticeData N κ Label Item)
    (C : ℝ) (B K : ℕ) (Lip bound : ℝ) (hLip : 0≤Lip)
    (hprofile : P.profileBound≤bound) (habsolute : P.referenceEnvelopeConstant≤bound) :
    P.referenceTreeConstant C B K Lip≤ordinaryTreeUnitCost C B K Lip*bound := by
  have ht := transverseTailConstant_nonneg
  dsimp only [referenceTreeConstant,ordinaryTreeUnitCost]
  calc
    _ ≤ 27*288*(4*Real.pi)^2*(B:ℝ)*32*3^203*bound+
      Real.sqrt (C*(B:ℝ))*bound+
      32^106*(B:ℝ)*bound*(2+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4)*
        (32*2^203)*9*transverseTailConstant := by gcongr
    _ = _ := by ring

namespace OrdinaryModelConfig
variable {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

theorem sizeAreaConstant_le_unit (d : OrdinaryModelConfig P initial) (CS bound : ℝ)
    (hCS : 0≤CS)
    (hprofile : P.profileBound≤bound) (habsolute : P.referenceEnvelopeConstant≤bound) :
    d.sizeAreaConstant CS≤d.unitSizeAreaCost CS*bound^2 := by
  have hp := P.profileBound_pos.le
  have ha := P.referenceEnvelopeConstant_pos.le
  let U := selectedFarUnitCost d.cb (Real.sqrt 2) CS d.packGap d.M d.Q
  have hU : 0≤U := by dsimp only [U,selectedFarUnitCost]; positivity
  have heFar : selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q=
      U*P.profileBound^2*P.referenceEnvelopeConstant^2 := by
    dsimp only [selectedFarConstant,U,selectedFarUnitCost]
    ring
  have hFar : 2*selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q≤(2*U)*(bound^2)^2 := by
    rw [heFar]
    calc
      _ ≤ 2*(U*bound^2*bound^2) := by gcongr
      _ = _ := by ring
  have hNear : selectedNearConstant P d.gap d.M d.Q ≤ selectedNearUnitCost d.gap d.M d.Q*bound^2 := by
    dsimp only [selectedNearConstant,selectedNearUnitCost]
    calc
      _ = (((2*d.gap+1:ℕ):ℝ)*(((2*d.Q+1)*d.M:ℕ):ℝ)*((4*Real.pi)^2*Real.pi^2))*P.profileBound^2 := by ring
      _ ≤ _ := by gcongr
  have hSqrt : Real.sqrt (2*selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q)≤
      Real.sqrt (2*U)*bound^2 := by
    calc
      _ ≤ Real.sqrt ((2*U)*(bound^2)^2) := Real.sqrt_le_sqrt hFar
      _ = _ := by rw [Real.sqrt_mul (by positivity : 0≤2*U),Real.sqrt_sq (sq_nonneg bound)]
  calc
    _ ≤ 4*(selectedNearUnitCost d.gap d.M d.Q*bound^2+2*(Real.sqrt (2*U)*bound^2)) := by
      dsimp only [sizeAreaConstant]
      gcongr
    _ = _ := by dsimp only [unitSizeAreaCost,U]; ring

theorem modelCost_le_cubic (d : OrdinaryModelConfig P initial) (CD CS CT bound : ℝ)
    (hCS : 0≤CS) (hbound : 1≤bound)
    (hprofile : P.profileBound≤bound) (habsolute : P.referenceEnvelopeConstant≤bound) :
    d.modelCost CD CS CT≤d.unitModelCost CD CS CT*bound^3 := by
  let td := ordinaryTreeUnitCost CD ((2*d.R+1)*d.M) d.K d.Lip
  let tt := ordinaryTreeUnitCost CT ((2*d.R+1)*d.M) d.K d.Lip
  let sz := d.unitSizeAreaCost CS
  let sp := (((4*d.D0+1)^2:ℕ):ℝ)
  have ht := transverseTailConstant_nonneg
  have hLip := d.hLip
  have htd : 0≤td := by dsimp only [td,ordinaryTreeUnitCost]; positivity
  have htt : 0≤tt := by dsimp only [tt,ordinaryTreeUnitCost]; positivity
  have hsz : 0 ≤ sz := by dsimp only [sz,unitSizeAreaCost,selectedNearUnitCost]; positivity
  have hsp : 0 ≤ sp := Nat.cast_nonneg _
  have htdb := P.referenceTreeConstant_le_unit CD ((2*d.R+1)*d.M) d.K d.Lip bound d.hLip hprofile habsolute
  have httb := P.referenceTreeConstant_le_unit CT ((2*d.R+1)*d.M) d.K d.Lip bound d.hLip hprofile habsolute
  have hsizeNonneg := d.sizeAreaConstant_nonneg CS
  have hszb := d.sizeAreaConstant_le_unit CS bound hCS hprofile habsolute
  have hb3 : bound≤bound^3 := by
    have h := mul_nonneg (sub_nonneg.mpr hbound)
      (by positivity : 0≤bound^2+bound)
    nlinarith
  have hstep : d.stepConstant CD CS CT≤d.unitStepCost CD CS CT*bound^3 := by
    calc
      _ ≤ Real.sqrt 2*(2*(625*densityRadiusConstant^2*(td*bound))+
          sp*(tt*bound)*(sz*bound^2)) := by
        dsimp only [stepConstant]
        gcongr
      _ = Real.sqrt 2*((2*625*densityRadiusConstant^2*td)*bound+(sp*tt*sz)*bound^3) := by ring
      _ ≤ Real.sqrt 2*((2*625*densityRadiusConstant^2*td)*bound^3+(sp*tt*sz)*bound^3) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hb3 (by positivity)) le_rfl) (Real.sqrt_nonneg 2)
      _ = _ := by dsimp only [unitStepCost,td,tt,sz,sp]; ring
  have hG : 0≤8*ordinaryDensityUpper/(1-ordinaryThresholdRatio) := by
    have hU : 0<ordinaryDensityUpper := zero_lt_one.trans_le (le_max_left _ _)
    have hr := sub_pos.mpr ordinaryThresholdRatio_lt_one
    positivity
  calc
    _ ≤ 1+(8*ordinaryDensityUpper/(1-ordinaryThresholdRatio))*(d.unitStepCost CD CS CT*bound^3) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hstep hG)
    _ ≤ bound^3+(8*ordinaryDensityUpper/(1-ordinaryThresholdRatio))*(d.unitStepCost CD CS CT*bound^3) :=
      add_le_add (hbound.trans hb3) le_rfl
    _ = _ := by dsimp only [unitModelCost]; ring

theorem modelCost_le_rpow (d : OrdinaryModelConfig P initial) (CD CS CT K L p : ℝ)
    (hCS : 0≤CS) (hL : 1≤L) (hKL : K≤L) (hp : 0≤p)
    (hunit : d.unitModelCost CD CS CT≤K)
    (hprofile : P.profileBound≤L^p) (habsolute : P.referenceEnvelopeConstant≤L^p) :
    d.modelCost CD CS CT≤L^(3*p+1) := by
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hpow : 1≤L^p := Real.one_le_rpow hL hp
  have hc := d.modelCost_le_cubic CD CS CT (L^p) hCS hpow hprofile habsolute
  have he : (L^p)^3=L^(3*p) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hLp.le]
    congr 1
    norm_num
    ring
  calc
    _ ≤ d.unitModelCost CD CS CT*(L^p)^3 := hc
    _ ≤ K*(L^p)^3 := mul_le_mul_of_nonneg_right hunit (by positivity)
    _ ≤ L*(L^p)^3 := mul_le_mul_of_nonneg_right hKL (by positivity)
    _ = L^(1:ℝ)*L^(3*p) := by rw [he,Real.rpow_one]
    _ = _ := by rw [←Real.rpow_add hLp]; congr 1; ring

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_OrdinaryModelConstructionCost
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cost of the constructed ordinary models is a fixed number.
In particular it has no dependence on the finite lattice or translation. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData

theorem OrdinaryModelConfig.unitModelCost_of_numeric_fields
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}
    (d : OrdinaryModelConfig P initial) (cStar cEta cb radius : ℝ)
    (num : OrdinaryModelNumerics cStar cEta cb radius) (M : ℕ) (CD CS CT : ℝ)
    (hcb : d.cb=cb) (hM : d.M=M) (hQ : d.Q=1) (hR : d.R=1)
    (hgap : d.gap=num.gap) (hpack : d.packGap=num.packGap)
    (hK : d.K=num.K) (hD0 : d.D0=5) (hLip : d.Lip=1) :
    d.unitModelCost CD CS CT=num.modelUnitCost M CD CS CT := by
  simp only [OrdinaryModelConfig.unitModelCost,OrdinaryModelConfig.unitStepCost,
    OrdinaryModelConfig.unitSizeAreaCost,hcb,hM,hQ,hR,hgap,hpack,hK,hD0,hLip]
  rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SupportedInnerIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded tests supported on a measurable set turn local norm bounds
into literal global pairings. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem supported_inner_integral_le {X κ : Type*} [MeasurableSpace X] [Fintype κ]
    (mu : Measure X) (E : Set X) (hE : MeasurableSet E)
    (F g : X → EuclideanSpace ℂ κ) (hF : IntegrableOn F E mu)
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖≤1) (hgs : ∀ x, x∉E → g x=0) :
    Integrable (fun x => inner ℂ (F x) (g x)) mu ∧
      ‖∫ x, inner ℂ (F x) (g x) ∂mu‖≤∫ x in E, ‖F x‖ ∂mu := by
  have hp (x : X) : ‖inner ℂ (F x) (g x)‖≤‖F x‖ :=
    (norm_inner_le_norm (𝕜:=ℂ) _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hg1 x))
  have hlocal : IntegrableOn (fun x => inner ℂ (F x) (g x)) E mu :=
    hF.norm.mono' (hF.aestronglyMeasurable.inner hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall hp)
  have he (x : X) : E.indicator (fun x => inner ℂ (F x) (g x)) x=inner ℂ (F x) (g x) := by
    by_cases hx : x∈E
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,hgs x hx,inner_zero_right]
  have hglobal := ((integrable_indicator_iff hE).2 hlocal).congr (Filter.Eventually.of_forall he)
  refine ⟨hglobal,?_⟩
  have hI : (∫ x, inner ℂ (F x) (g x) ∂mu)=∫ x in E, inner ℂ (F x) (g x) ∂mu := by
    rw [←integral_indicator hE,funext he]
  rw [hI]
  exact (norm_integral_le_integral_norm _).trans (integral_mono hlocal.norm hF.norm hp)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzingBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite synthesis/analysis duality with arbitrary synthesizing coefficients. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

theorem finite_analyzing_pairing {X I K : Type*} [MeasurableSpace X] [Fintype K]
    (mu : Measure X) (area : I → ℝ) (wave : I → K → X → ℂ)
    (g : X → EuclideanSpace ℂ K) (c : I → EuclideanSpace ℂ K) (S : Finset I)
    (ha : ∀ i∈S, area i≠0)
    (hint : ∀ i∈S, ∀ k, Integrable (fun x => g x k*conj (wave i k x)) mu) :
    (∫ x, inner ℂ (∑ i∈S, WithLp.toLp 2 (fun k => c i k*wave i k x)) (g x) ∂mu)=
      ∑ i∈S, (area i:ℂ)*inner ℂ (c i) (analyzingCoefficient mu area wave g i) := by
  have hterm (i : I) (hi : i∈S) :
      (area i:ℂ)*inner ℂ (c i) (analyzingCoefficient mu area wave g i)=
        ∑ k, conj (c i k)*(∫ x, g x k*conj (wave i k x) ∂mu) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have harea : (area i:ℂ)*analyzingCoefficient mu area wave g i k=
        ∫ x, g x k*conj (wave i k x) ∂mu := by
      change (area i:ℂ)*(((area i)⁻¹:ℂ)*_)=_
      rw [←mul_assoc,mul_inv_cancel₀ (by exact_mod_cast ha i hi),one_mul]
    rw [←harea]
    ring
  have hInt (i : I) (hi : i∈S) (k : K) :
      Integrable (fun x => conj (c i k)*(g x k*conj (wave i k x))) mu :=
    (hint i hi k).const_mul _
  symm
  calc
    _ = ∑ i∈S, ∑ k, conj (c i k)*(∫ x, g x k*conj (wave i k x) ∂mu) :=
      Finset.sum_congr rfl hterm
    _ = ∫ x, ∑ i∈S, ∑ k, conj (c i k)*(g x k*conj (wave i k x)) ∂mu := by
      simp_rw [←integral_const_mul]
      rw [integral_finsetSum S (fun i hi => integrable_finsetSum _ (fun k _ => hInt i hi k))]
      apply Finset.sum_congr rfl
      intro i hi
      exact (integral_finsetSum Finset.univ (fun k _ => hInt i hi k)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [PiLp.inner_apply,RCLike.inner_apply,WithLp.ofLp_sum,Finset.sum_apply,
        map_sum,map_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAdjoint
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal finite adjoint duality for the ordinary masked packets. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem masked_physical_packet_memLp
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (q : P.PacketIndex) (k : κ) :
    MemLp (fun z => b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      2 (volume.prod volume) := by
  apply ((P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2 (volume.prod volume)).mono
    ((((hb q.1 q.2.1 k).comp hu).mul
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k).continuous.measurable).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z‖≤_
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb1 q.1 q.2.1 k (u z))

theorem ordinaryAdjointSum_memLp (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    MemLp (P.ordinaryAdjointSum S b u g) 2 (volume.prod volume) :=
  memLp_finsetSum S (fun q _ => P.packetVector_memLp _ q)

theorem ordinary_forward_pairing (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : MemLp g 2 (volume.prod volume)) :
    (∫ z, inner ℂ (P.ordinaryForwardSum S b u f z) (g z) ∂volume.prod volume)=
      ∑ q∈S, ((P.length q.1*P.width:ℝ):ℂ)*inner ℂ
        (P.ordinaryCoefficient f q.1 q.2.1 q.2.2)
        (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2) := by
  let area := fun q : P.PacketIndex => P.length q.1*P.width
  let masked := fun (q : P.PacketIndex) (k : κ) (z : ℝ×ℝ) =>
    b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z
  let cf := fun q : P.PacketIndex => P.ordinaryCoefficient f q.1 q.2.1 q.2.2
  have ha (q : P.PacketIndex) (_hq : q∈S) : area q≠0 := (mul_pos (P.length_pos _) P.width_pos).ne'
  have hm (q : P.PacketIndex) (_hq : q∈S) (k : κ) :
      Integrable (fun z => g z k*conj (masked q k z)) (volume.prod volume) :=
    ((memLp_piLp_iff.mp hg) k).integrable_mul (P.masked_physical_packet_memLp b hb hb1 u hu q k).star
  have h := finite_analyzing_pairing (volume.prod volume) area masked g cf S ha hm
  have he (z : ℝ×ℝ) : (∑ q∈S, WithLp.toLp 2 (fun k => cf q k*masked q k z))=
      P.ordinaryForwardSum S b u f z := by
    apply Finset.sum_congr rfl
    intro q _
    apply WithLp.ofLp_injective
    funext k
    change cf q k*(b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)=
      cf q k*b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z
    ring
  have hc (q : P.PacketIndex) : analyzingCoefficient (volume.prod volume) area masked g q=
      P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 := rfl
  simp_rw [he,hc] at h
  exact h

theorem ordinary_adjoint_pairing (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : MemLp f 2 (volume.prod volume)) :
    (∫ z, inner ℂ (P.ordinaryAdjointSum S b u g z) (f z) ∂volume.prod volume)=
      ∑ q∈S, ((P.length q.1*P.width:ℝ):ℂ)*inner ℂ
        (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2)
        (P.ordinaryCoefficient f q.1 q.2.1 q.2.2) := by
  apply finite_analyzing_pairing (volume.prod volume)
    (fun q : P.PacketIndex => P.length q.1*P.width)
    (fun q k => P.physicalPacket 0 q.1 q.2.1 q.2.2 k) f
    (fun q => P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2) S
  · intro q _
    exact (mul_pos (P.length_pos _) P.width_pos).ne'
  · intro q _ k
    exact ((memLp_piLp_iff.mp hf) k).integrable_mul
      ((P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2 (volume.prod volume)).star

theorem ordinary_forward_adjoint_pairing (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume)) :
    (∫ z, inner ℂ (P.ordinaryForwardSum S b u f z) (g z) ∂volume.prod volume)=
      conj (∫ z, inner ℂ (P.ordinaryAdjointSum S b u g z) (f z) ∂volume.prod volume) := by
  rw [P.ordinary_forward_pairing S b hb hb1 u hu f g hg,P.ordinary_adjoint_pairing S b u f g hf,map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_mul,Complex.conj_ofReal,inner_conj_symm]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAdjointPairingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a tested ordinary forward estimate to its literal adjoint
pairing. All integrals retain their actual packet sums. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert

theorem integrable_euclidean_inner {X κ : Type*} [MeasurableSpace X] [Fintype κ]
    (μ : Measure X) {f g : X → EuclideanSpace ℂ κ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun z => inner ℂ (f z) (g z)) μ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply]
  exact integrable_finsetSum _ (fun k _ =>
    ((memLp_piLp_iff.mp hg) k).integrable_mul (((memLp_piLp_iff.mp hf) k).star))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAdjointPairingBound
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Forward-adjoint duality for the unrestricted physical packet data. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem ordinary_adjoint_pairing_bound (P : PacketLatticeData N κ Label Item)
    (S : Finset P.PacketIndex) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume))
    (hgm : Measurable g) (hgb : ∀ z, ‖g z‖≤1)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (hgs : ∀ z, z∉E → g z=0)
    (hint : IntegrableOn (P.ordinaryForwardSum S b u f) E (volume.prod volume)) :
    Integrable (fun z => inner ℂ (P.ordinaryAdjointSum S b u g z) (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (P.ordinaryAdjointSum S b u g z) (f z) ∂volume.prod volume‖≤
        ∫ z in E, ‖P.ordinaryForwardSum S b u f z‖ ∂volume.prod volume := by
  refine ⟨integrable_euclidean_inner _ (P.ordinaryAdjointSum_memLp S b u g) hf,?_⟩
  have h := P.ordinary_forward_adjoint_pairing S b hb hb1 u hu f g hf hg
  have hn := congrArg norm h
  rw [RCLike.norm_conj] at hn
  rw [←hn]
  exact (supported_inner_integral_le (volume.prod volume) E hE _ g hint hgm hgb hgs).2

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCrossValue
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distinct-profile, masked analyzing packet sum. No auxiliary
jet is needed for the physical bilinear operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)

theorem crossPacketValue_memLp (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (p : ℝ≥0∞) (q : P.PacketIndex) :
    MemLp (fun z => P.crossPacketValue alt hAlt t b v g z q) p (volume.prod volume) := by
  apply memLp_piLp_iff.mpr
  intro k
  exact (((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k).memLp p
    (volume.prod volume)).const_mul _

theorem crossSum_memLp (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (p : ℝ≥0∞) (S : Finset P.PacketIndex) :
    MemLp (fun z => ∑ q∈S, P.crossPacketValue alt hAlt t b v g z q) p (volume.prod volume) :=
  memLp_finsetSum S (fun q _ => P.crossPacketValue_memLp alt hAlt t b v g p q)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAdjointPolarization
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact polarization for masked analyzing coefficients and their
unmasked, distinct-profile adjoint synthesis. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)

theorem polarize_multiplier_coefficient (c : ℂ) (hc : ‖c‖=1)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖≤1)
    (j : Fin N) (l : P.labels j) (a : Item j l) :
    (P.polarize alt hAlt c hc).physicalMultiplierCoefficient 0 b u g j l a=
      P.physicalMultiplierCoefficient 0 b u g j l a+
        conj c • (P.withProfile alt hAlt).physicalMultiplierCoefficient 0 b u g j l a := by
  let f := fun (a : Item j l) (k : κ) (z : ℝ×ℝ) => b j l k (u z)*P.physicalPacket 0 j l a k z
  let h := fun (a : Item j l) (k : κ) (z : ℝ×ℝ) =>
    b j l k (u z)*(P.withProfile alt hAlt).physicalPacket 0 j l a k z
  have he : (fun (a : Item j l) (k : κ) (z : ℝ×ℝ) =>
      b j l k (u z)*(P.polarize alt hAlt c hc).physicalPacket 0 j l a k z)=
      fun a k z => f a k z+c*h a k z := by
    funext a k z
    rw [P.polarize_physicalPacket alt hAlt c hc]
    change b j l k (u z)*(P.physicalPacket 0 j l a k z+c*(P.withProfile alt hAlt).physicalPacket 0 j l a k z)=_
    dsimp only [f,h]
    ring
  change analyzingCoefficient (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    (fun a k z => b j l k (u z)*(P.polarize alt hAlt c hc).physicalPacket 0 j l a k z) g a=_
  rw [he]
  exact analyzingCoefficient_add_smul (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    f h g c
    (fun a k => P.physical_multiplier_analyzing_integrable 0 (fun z => b j l k (u z))
      ((hb j l k).comp hu) (fun z => hb1 j l k (u z)) g hg hg1 j l a k)
    (fun a k => (P.withProfile alt hAlt).physical_multiplier_analyzing_integrable 0 (fun z => b j l k (u z))
      ((hb j l k).comp hu) (fun z => hb1 j l k (u z)) g hg hg1 j l a k) a

theorem cross_adjoint_polarization (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖≤1)
    (z : ℝ×ℝ) :
    (4:ℂ) • (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q)=
      (P.polarize alt hAlt 1 (by simp)).ordinaryAdjointSum S b u g z-
      (P.polarize alt hAlt (-1) (by simp)).ordinaryAdjointSum S b u g z-
      Complex.I • (P.polarize alt hAlt Complex.I (by simp)).ordinaryAdjointSum S b u g z+
      Complex.I • (P.polarize alt hAlt (-Complex.I) (by simp)).ordinaryAdjointSum S b u g z := by
  have hcross (q : P.PacketIndex) : P.crossPacketValue alt hAlt 0 b u g z q=
      WithLp.toLp 2 (fun k => P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k*
        (P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z) := rfl
  have hterm (c : ℂ) (hc : ‖c‖=1) (q : P.PacketIndex) (k : κ) :
      (P.polarize alt hAlt c hc).packetVector
        ((P.polarize alt hAlt c hc).physicalMultiplierCoefficient 0 b u g) q z k=
      (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k+
        conj c*(P.withProfile alt hAlt).physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k)*
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z+c*(P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z) := by
    change (P.polarize alt hAlt c hc).physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k*
      (P.polarize alt hAlt c hc).physicalPacket 0 q.1 q.2.1 q.2.2 k z=_
    rw [P.polarize_multiplier_coefficient alt hAlt c hc b hb hb1 u hu g hg hg1,
      P.polarize_physicalPacket alt hAlt c hc]
    simp only [PiLp.add_apply,PiLp.smul_apply,add_apply,smul_apply,smul_eq_mul]
  apply WithLp.ofLp_injective
  funext k
  simp only [hcross,ordinaryAdjointSum,WithLp.ofLp_sum,Finset.sum_apply,
    WithLp.ofLp_smul,WithLp.ofLp_add,WithLp.ofLp_sub,
    Pi.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul]
  simp only [hterm]
  simp only [map_one,map_neg,Complex.conj_I,one_mul,neg_mul,neg_neg,
    Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have h := packet_cross_polarization
    (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k)
    ((P.withProfile alt hAlt).physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k)
    (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
    ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  linear_combination -h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCrossPairingBound
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four exact polarized adjoint pairings control the distinct-profile
pairing with no loss in a common bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem cross_pairing_bound (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (S : Finset P.PacketIndex) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (g f : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖≤1)
    (hf : MemLp f 2 (volume.prod volume)) (B : ℝ)
    (hbound : ∀ (c : ℂ) (hc : ‖c‖=1),
      ‖∫ z, inner ℂ ((P.polarize alt hAlt c hc).ordinaryAdjointSum S b u g z) (f z)
        ∂volume.prod volume‖≤B) :
    Integrable (fun z => inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q)
      (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q)
        (f z) ∂volume.prod volume‖≤B := by
  let A := (P.polarize alt hAlt 1 (by simp)).ordinaryAdjointSum S b u g
  let Bv := (P.polarize alt hAlt (-1) (by simp)).ordinaryAdjointSum S b u g
  let C := (P.polarize alt hAlt Complex.I (by simp)).ordinaryAdjointSum S b u g
  let D := (P.polarize alt hAlt (-Complex.I) (by simp)).ordinaryAdjointSum S b u g
  let X := fun z => ∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q
  have hA : Integrable (fun z => inner ℂ (A z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt 1 (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  have hB : Integrable (fun z => inner ℂ (Bv z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt (-1) (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  have hC : Integrable (fun z => inner ℂ (C z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt Complex.I (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  have hD : Integrable (fun z => inner ℂ (D z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt (-Complex.I) (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  refine ⟨integrable_euclidean_inner _ (P.crossSum_memLp alt hAlt 0 b u g 2 S) hf,?_⟩
  have hpoint (z : ℝ×ℝ) : (4:ℂ)*inner ℂ (X z) (f z)=
      inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
        Complex.I*inner ℂ (C z) (f z)-Complex.I*inner ℂ (D z) (f z) := by
    have h := congrArg (fun v => inner ℂ v (f z))
      (P.cross_adjoint_polarization alt hAlt S b hb hb1 u hu g hg hg1 z)
    simpa only [inner_smul_left,inner_add_left,inner_sub_left,map_ofNat,
      Complex.conj_I,neg_mul,sub_neg_eq_add,←sub_eq_add_neg] using h
  let ia := ∫ z, inner ℂ (A z) (f z) ∂volume.prod volume
  let ib := ∫ z, inner ℂ (Bv z) (f z) ∂volume.prod volume
  let ic := ∫ z, inner ℂ (C z) (f z) ∂volume.prod volume
  let idv := ∫ z, inner ℂ (D z) (f z) ∂volume.prod volume
  have hint : (4:ℂ)*(∫ z, inner ℂ (X z) (f z) ∂volume.prod volume)=
      ia-ib+Complex.I*ic-Complex.I*idv := by
    calc
      _ = ∫ z, (4:ℂ)*inner ℂ (X z) (f z) ∂volume.prod volume := (integral_const_mul _ _).symm
      _ = ∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
          Complex.I*inner ℂ (C z) (f z)-Complex.I*inner ℂ (D z) (f z)
          ∂volume.prod volume := integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = _ := by
        have hs : (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
            Complex.I*inner ℂ (C z) (f z)-Complex.I*inner ℂ (D z) (f z) ∂volume.prod volume)=
            (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
              Complex.I*inner ℂ (C z) (f z) ∂volume.prod volume)-
            (∫ z, Complex.I*inner ℂ (D z) (f z) ∂volume.prod volume) :=
          integral_sub ((hA.sub hB).add (hC.const_mul Complex.I)) (hD.const_mul Complex.I)
        have ha : (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
            Complex.I*inner ℂ (C z) (f z) ∂volume.prod volume)=
            (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z) ∂volume.prod volume)+
            (∫ z, Complex.I*inner ℂ (C z) (f z) ∂volume.prod volume) :=
          integral_add (hA.sub hB) (hC.const_mul Complex.I)
        have hb : (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z) ∂volume.prod volume)=ia-ib :=
          integral_sub hA hB
        rw [hs,ha,hb,integral_const_mul,integral_const_mul]
  have hnorm : 4*‖∫ z, inner ℂ (X z) (f z) ∂volume.prod volume‖≤
      ‖ia‖+‖ib‖+‖ic‖+‖idv‖ := by
    calc
      _ = ‖(4:ℂ)*(∫ z, inner ℂ (X z) (f z) ∂volume.prod volume)‖ := by
        rw [norm_mul]; norm_num
      _ = ‖ia-ib+Complex.I*ic-Complex.I*idv‖ := congrArg norm hint
      _ ≤ (‖ia‖+‖ib‖)+‖ic‖+‖idv‖ := by
        calc
          _ ≤ ‖ia-ib+Complex.I*ic‖+‖Complex.I*idv‖ := norm_sub_le _ _
          _ ≤ (‖ia-ib‖+‖Complex.I*ic‖)+‖Complex.I*idv‖ :=
            add_le_add (norm_add_le _ _) le_rfl
          _ ≤ ((‖ia‖+‖ib‖)+‖Complex.I*ic‖)+‖Complex.I*idv‖ := by
            gcongr; exact norm_sub_le _ _
          _ = _ := by simp only [norm_mul,Complex.norm_I,one_mul]
  have ha : ‖ia‖≤B := hbound 1 (by simp)
  have hb' : ‖ib‖≤B := hbound (-1) (by simp)
  have hc : ‖ic‖≤B := hbound Complex.I (by simp)
  have hd : ‖idv‖≤B := hbound (-Complex.I) (by simp)
  nlinarith

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDensityGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual center geometry for the density assignment. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem assigned_packet_geometry_of_density {τ : Type*}
    (P : PacketLatticeData N κ Label Item) (packets : Finset P.PacketIndex)
    (assigned : P.PacketIndex → τ) (T : τ → SlopeBox) (oldSlope L a : ℝ)
    (hL : 2 ≤ L) (ha : 0 ≤ a)
    (hshort : ∀ q ∈ packets, P.length q.1 ≤ (T (assigned q)).length)
    (hwidth : ∀ q ∈ packets, P.width ≤ (T (assigned q)).width)
    (hrad : ∀ q ∈ packets, (T (assigned q)).radius
      (P.actualX q.1 q.2.1 q.2.2,
        P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2) ≤ L^a) :
    (∀ q ∈ packets,
      |P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x|+P.length q.1 ≤
        L^(a+1)*(T (assigned q)).length) ∧
    (∀ q ∈ packets,
      |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T (assigned q)).slope)*
        P.actualX q.1 q.2.1 q.2.2-
        ((T (assigned q)).y-(T (assigned q)).slope*(T (assigned q)).x)|+P.width ≤
          L^(a+1)*(T (assigned q)).width) := by
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hp : 1 ≤ L^a := Real.one_le_rpow hL1 ha
  have hpow : L^a+1 ≤ L^(a+1) := by
    rw [Real.rpow_add hLp,Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hLp.le a)]
  constructor
  · intro q hq
    have hx := ((T (assigned q)).coordinates_of_radius_le (hrad q hq)).1
    change |P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x| ≤
      L^a*(T (assigned q)).length at hx
    have hh := mul_le_mul_of_nonneg_right hpow (T (assigned q)).length_pos.le
    linarith [hshort q hq]
  · intro q hq
    have hy := ((T (assigned q)).coordinates_of_radius_le (hrad q hq)).2
    have heq :
        (P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2-
          (T (assigned q)).y)-(T (assigned q)).slope*
            (P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x) =
        P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T (assigned q)).slope)*
          P.actualX q.1 q.2.1 q.2.2-
          ((T (assigned q)).y-(T (assigned q)).slope*(T (assigned q)).x) := by ring
    change |(P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2-
      (T (assigned q)).y)-(T (assigned q)).slope*
        (P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x)| ≤ L^a*(T (assigned q)).width at hy
    rw [heq] at hy
    have hh := mul_le_mul_of_nonneg_right hpow (T (assigned q)).width_pos.le
    linarith [hwidth q hq]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDensityForest
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary density produces the literal top assignment and witnesses
needed for packet concentration. No disjoint-witness premise is imposed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem exists_packet_density_forest_in_cells (a : ℝ) (ha : 0 ≤ a) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (packets : Finset P.PacketIndex),
      packets.Nonempty →
    ∀ (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (cone w tau : ℝ), 1 ≤ cone → 0 < w → 12*w ≤ P.width →
    ∀ (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ), MeasurableSet E →
      (volume.prod volume) E ≠ ∞ → Measurable u →
      (∀ q ∈ packets, L^(-a) < P.ordinaryDensity oldSlope cell grid w tau E u q) →
      (∀ q ∈ packets, oldSlope+P.rowSlope q.1 q.2.1 ∈
        scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      ∃ forest : PacketDensityForest P packets oldSlope L a cone w tau E u,
        (∀ i, (forest.top i).slope ∈ scaledAngularCell (w/P.topLength) grid
          i.val.val.1.val (cell i.val.val.1 i.val.val.2.1)) ∧
        (∀ q ∈ packets, (forest.top (forest.assigned q)).slope ∈
          scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) := by
  classical
  obtain ⟨L0,hL0,hforest⟩ := exists_high_density_forest a ha
  refine ⟨L0,hL0,?_⟩
  intro L hL N κ Label Item _ _ P packets hpackets oldSlope cell grid cone w tau hcone hw hW E u hE hEfin hu hdensity hcell
  obtain ⟨test,keepers,choose,hmeas,hdisj,harea,hmass,hinside,hassign⟩ :=
    hforest L hL P.PacketIndex packets (P.densityTile oldSlope cell)
      P.topLength w P.width tau grid P.topLength_pos hw hW E u hE hEfin hu hdensity
  obtain ⟨q0,hq0⟩ := hpackets
  let assigned : P.PacketIndex → keepers := fun q =>
    if hq : q ∈ packets then choose ⟨q,hq⟩ else choose ⟨q0,hq0⟩
  let T : keepers → SlopeBox := fun i => (test i.val).top
  let W : keepers → Set (ℝ×ℝ) := fun i => densityTest E u (T i)
    (scaledAngularCell (w/P.topLength) grid (test i.val).level (test i.val).cell) (L^(a/100+1))
  have hassigned (q : P.PacketIndex) (hq : q ∈ packets) :
      assigned q = choose ⟨q,hq⟩ := dite_eq_left hq
  have hshort (q : P.PacketIndex) (hq : q ∈ packets) :
      P.length q.1 ≤ (T (assigned q)).length := by
    rw [hassigned q hq]
    simpa only [T,P.densityTile_length] using (hassign ⟨q,hq⟩).1
  have hrad (q : P.PacketIndex) (hq : q ∈ packets) :
      (T (assigned q)).radius
        (P.actualX q.1 q.2.1 q.2.2,
          P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2) ≤ L^(a+2) := by
    rw [hassigned q hq]
    exact (hassign ⟨q,hq⟩).2.1
  have hgeometry := P.assigned_packet_geometry_of_density packets assigned T oldSlope L (a+2)
    (hL0.trans hL) (by linarith) hshort
    (fun q _ => (test (assigned q).val).width_eq.ge) hrad
  have hfinite (i : keepers) : (volume.prod volume) (W i) ≠ ∞ :=
    measure_ne_top_of_subset (fun _ hz => (hinside i.val i.property _ hz).1) hEfin
  refine ⟨{
    keepers := keepers
    top := T
    assigned := assigned
    witness := W
    measurable := fun i => hmeas i.val i.property
    disjoint := ?_
    subset := fun i z hz => (hinside i.val i.property z hz).1
    finite := hfinite
    mass := ?_
    radius := fun i z hz => (hinside i.val i.property z hz).2.1
    precision := fun i z hz => (hinside i.val i.property z hz).2.2.1
    close := fun i z hz => (hinside i.val i.property z hz).2.2.2
    width := fun i => (test i.val).width_eq
    short := fun i => (test i.val).length_le
    seed_short := fun i => by
      simpa only [P.densityTile_length] using (test i.val).tile_length_le
    area := ?_
    area_pos := ?_
    reference := ?_
    horizontal := ?_
    transverse := ?_ },?_,?_⟩
  · intro i j hij
    exact hdisj i.property j.property (fun h => hij (Subtype.ext h))
  · intro i
    have h := ENNReal.ofReal_le_ofReal (hmass i.val i.property)
    rw [Measure.real,ENNReal.ofReal_toReal (hfinite i)] at h
    simpa only [SlopeBox.area,mul_assoc] using h
  · change (∑ i : keepers, (fun j => (test j).top.area) i.val) ≤ _
    rw [Finset.sum_coe_sort keepers (fun j => (test j).top.area)]
    exact harea
  · exact Finset.sum_pos (fun i _ => (T i).area_pos) (Finset.univ_nonempty_iff.mpr
      ⟨choose ⟨q0,hq0⟩⟩)
  · intro q hq
    apply P.reference_bounds_of_density_cell oldSlope cell grid w cone hw hcone q _ (hshort q hq)
      (hcell q hq)
    rw [hassigned q hq]
    exact (hassign ⟨q,hq⟩).2.2
  · simpa only [show a+2+1=a+3 by ring] using hgeometry.1
  · simpa only [show a+2+1=a+3 by ring] using hgeometry.2
  · intro i
    exact (test i.val).slope_mem_tile
  · intro q hq
    change (T (assigned q)).slope ∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)
    rw [hassigned q hq]
    exact (hassign ⟨q,hq⟩).2.2

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataHighDensityPopularRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High ordinary density supplies the actual popular forest. Its retained
angular cells put every keeper in the source direction chart, so both
the top-direction and root-interval hypotheses of recovery are derived. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_high_density_popular_recovery
    (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 qEnergy decay : ℝ)
    (D K H J₀ : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hcone : 1 ≤ cone) (hconeK : cone ≤ K) (hLip : 0 ≤ Lip)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0) (hqEnergy : 0 ≤ qEnergy)
    (hdecay : 0 ≤ decay) (hD : 4 ≤ D)
    (hgap : cStar < cEta*cb) (hJ : 2*cone+1 ≤ (2:ℝ)^J₀) :
    ∃ A L0 : ℝ, aDensity+3 < A ∧ 16 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (oldSlope w tau : ℝ), 0 < w →
      P.scale = 4*(L^(A+2)*P.width) → P.ratioBound = 4*L^(A+2) →
      (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
      6+2*(8*D+1) ≤ P.order → packets.Nonempty →
    ∀ (Eset Fset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      MeasurableSet Eset → (volume.prod volume) Eset ≠ ∞ →
      (∀ q ∈ packets, L^(-aDensity) < P.ordinaryDensity oldSlope cell grid w tau Eset
        (fun z => field (planeCoordinates z)) q) →
      (∀ q ∈ packets, oldSlope+P.rowSlope q.1 q.2.1 ∈
        scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q ∈ packets, scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ⊆ Icc (-1) 1) →
    ∀ (l r : ℝ), LipschitzWith 1 field → 600*(r-l) ≤ 1 →
      (∀ z ∈ Eset, z.1 ∈ Icc l r) → (∀ z ∈ Fset, z.1 ∈ Icc l r) →
      MeasurableSet Fset → (volume.prod volume) Fset ≠ ∞ →
      0 < (volume.prod volume).real Fset →
    ∀ (ratio widthScale : ℝ), 0 < ratio → L/2 ≤ Real.log ratio → Real.log ratio ≤ 2*L →
      (volume.prod volume).real Eset = ratio^2*(volume.prod volume).real Fset →
      Real.exp (L^(9/10:ℝ)) ≤ widthScale → widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
      P.width = widthScale*w → 0 ≤ tau → tau ≤ Real.exp (-(L^(97/100:ℝ))) →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
      (∀ j l k s, b j l k s ≠ 0 →
        cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
          |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) H) →
      (∀ k, c0/w ≤ |P.frequency k|) → (∀ k, |P.frequency k| ≤ F/w) →
      (∀ j l u k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      2 ≤ g.rootWidth →
      (∫ z, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖^2
        ∂volume.prod volume) ≤ (L^qEnergy)^2*(volume.prod volume).real Eset →
      (∫ z in Fset, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖
        ∂volume.prod volume) ≤ L^(-decay)*ratio*(volume.prod volume).real Fset := by
  obtain ⟨A,Lbase,haA,hLbase,hmain⟩ := source_density_popular_recovery
    hVariation hLL cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 qEnergy decay D K H J₀
    hcStar hcEta hCEta hcb hCb hF hc0 (by linarith only [hcone]) hconeK hLip
    haDensity hp0 hqEnergy hdecay hD hgap hJ
  obtain ⟨Lforest,hLforest,hforest⟩ := exists_packet_density_forest_in_cells aDensity haDensity
  obtain ⟨Lwidth,hwidth⟩ := eventually_atTop.mp
    ((Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<9/10))).eventually_ge_atTop 12)
  refine ⟨A,max Lbase (max Lforest Lwidth),haA,hLbase.trans (le_max_left _ _),?_⟩
  intro L hL κ _ N Label Item _ P packets oldSlope w tau hw hscale hratioBound hprofile horder hpackets
    Eset Fset field cell grid hEset hEfinite hdensity hcell hcellrange
    l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt b hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency hspectrum haltSpectrum
    v hv f hf hf1 g hbranch hzero hrootWidth henergy
  have hLb : Lbase ≤ L := (le_max_left _ _).trans hL
  have hLf : Lforest ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLw : Lwidth ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hW : 12*w ≤ P.width := by
    rw [hwidthEq]
    exact mul_le_mul_of_nonneg_right ((hwidth L hLw).trans hwidthLow) hw.le
  obtain ⟨forest,hseed,_⟩ := hforest L hLf N κ Label Item P packets hpackets oldSlope cell grid
    cone w tau hcone hw hW Eset (fun z => field (planeCoordinates z)) hEset hEfinite
    (product_slope_lipschitz field hfield).continuous.measurable hdensity hcell
  have htop (i : forest.keepers) : (forest.top i).slope ∈ Icc (-1:ℝ) 1 :=
    hcellrange i.val.val i.val.property (hseed i)
  exact hmain L hLb κ N Label Item P packets oldSlope w tau hw hscale hratioBound hprofile horder
    Eset Fset field forest (fun i => abs_le.mpr (htop i))
    l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt b hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency hspectrum haltSpectrum
    v hv f hf hf1 g (-1) hbranch hzero
    (fun i => ⟨(htop i).1,(htop i).2.trans (by linarith only [hrootWidth])⟩) henergy

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundedInputEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-support bounded inputs have finite energy, bounded by support area. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert

theorem bounded_supported_input {κ : Type} [Fintype κ]
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g)
    (hbound : ∀ z, ‖g z‖≤1) (F : Set (ℝ×ℝ))
    (hF : MeasurableSet F) (hFfin : (volume.prod volume) F≠∞)
    (hsupport : ∀ z, z∉F → g z=0) :
    MemLp g 2 (volume.prod volume) ∧
      (∫ z, ‖g z‖^2 ∂volume.prod volume)≤(volume.prod volume).real F := by
  have hI : MemLp (F.indicator (fun _ => (1:ℝ))) 2 (volume.prod volume) :=
    memLp_indicator_const 2 hF 1 (Or.inr hFfin)
  have hb (z : ℝ×ℝ) : ‖g z‖≤F.indicator (fun _ => (1:ℝ)) z := by
    by_cases hz : z∈F
    · simpa only [Set.indicator_of_mem hz] using hbound z
    · simp only [Set.indicator_of_notMem hz,hsupport z hz,norm_zero,le_refl]
  have hMem : MemLp g 2 (volume.prod volume) :=
    hI.mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨hMem,?_⟩
  have hsq (z : ℝ×ℝ) : ‖g z‖^2≤F.indicator (fun _ => (1:ℝ)) z := by
    by_cases hz : z∈F
    · rw [Set.indicator_of_mem hz]
      nlinarith [hbound z,norm_nonneg (g z)]
    · simp only [Set.indicator_of_notMem hz,hsupport z hz,norm_zero,zero_pow (by decide : 2≠0),le_refl]
  have hle := integral_mono_ae (hMem.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    ((integrable_indicator_iff hF).2 (integrableOn_const (μ:=volume.prod volume) (C:=(1:ℝ)) hFfin))
    (Filter.Eventually.of_forall hsq)
  simpa only [integral_indicator_const (1:ℝ) hF,smul_eq_mul,mul_one] using hle

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataUniversalAdjointEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit adjoint energy with the same analytic constants selected
before all lattices in the ordinary estimate. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_universal_ordinary_adjoint_energy (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar < cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ S : Finset P.PacketIndex, S⊆initial →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ E : Set (ℝ×ℝ), MeasurableSet E → (volume.prod volume) E≠∞ →
      (∀ z, z∉E → g z=0) → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∫ z, ‖P.ordinaryAdjointSum S d.selector u g z‖^2 ∂volume.prod volume)≤
        (d.modelCost CD CS CT*ordinaryDensityUpper^(1/4:ℝ))^2*(volume.prod volume).real E := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hAll⟩ := exists_universal_ordinary_model_estimate hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P initial d h₁ h₂ h₃ h₄ h₅
  let C := d.modelCost CD CS CT
  have hC : 0<C := d.modelCost_pos CD CS CT
  let U := ordinaryDensityUpper
  have hU : 0<U := zero_lt_one.trans_le (le_max_left _ _)
  have hModel := hAll N κ Label Item P initial d h₁ h₂ h₃ h₄ h₅
  intro S hS g hgm hgb E hE hEfin hsupport u hu
  have hg := (bounded_supported_input g hgm hgb E hE hEfin hsupport).1
  let f := P.ordinaryAdjointSum S d.selector u g
  have hf : MemLp f 2 (volume.prod volume) := P.ordinaryAdjointSum_memLp S d.selector u g
  have hd (q : P.PacketIndex) (_hq : q∈S) : P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤U :=
    ((P.densityTile 0 d.cell q).density_le P.topLength d.w P.width d.tau d.grid E u).trans
      (le_max_right _ _)
  have h := hModel S hS f hf E hE hEfin u hu U hU hd
  let F := P.ordinaryForwardSum S d.selector u f
  change IntegrableOn F E (volume.prod volume) ∧
    (∫ z in E, ‖F z‖ ∂volume.prod volume)≤
      C*Real.sqrt (∫ z, ‖f z‖^2 ∂volume.prod volume)*
        Real.sqrt ((volume.prod volume).real E)*U^(1/4:ℝ) at h
  let energy := ∫ z, ‖f z‖^2 ∂volume.prod volume
  have henergy : 0≤energy := integral_nonneg (fun z => sq_nonneg ‖f z‖)
  have hpair := P.ordinary_forward_adjoint_pairing S d.selector d.measurable d.bounded u hu f g hf hg
  have hself : (∫ z, inner ℂ (f z) (f z) ∂volume.prod volume)=(energy:ℂ) := by
    simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow]
    exact integral_ofReal (μ:=volume.prod volume) (f:=fun z : ℝ×ℝ => ‖f z‖^2)
  change (∫ z, inner ℂ (F z) (g z) ∂volume.prod volume)=
    conj (∫ z, inner ℂ (f z) (f z) ∂volume.prod volume) at hpair
  rw [hself,Complex.conj_ofReal] at hpair
  have hpairNorm : ‖∫ z, inner ℂ (F z) (g z) ∂volume.prod volume‖=energy := by
    rw [hpair,Complex.norm_real,Real.norm_of_nonneg henergy]
  have hset : (∫ z, inner ℂ (F z) (g z) ∂volume.prod volume)=
      ∫ z in E, inner ℂ (F z) (g z) ∂volume.prod volume := by
    calc
      _ = ∫ z, E.indicator (fun z => inner ℂ (F z) (g z)) z ∂volume.prod volume := by
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z∈E
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz,hsupport z hz,inner_zero_right]
      _ = _ := integral_indicator hE
  have hpoint (z : ℝ×ℝ) : ‖inner ℂ (F z) (g z)‖≤‖F z‖ :=
    (norm_inner_le_norm (𝕜:=ℂ) _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hgb z))
  have hInt : IntegrableOn (fun z => inner ℂ (F z) (g z)) E (volume.prod volume) :=
    h.1.norm.mono' (h.1.aestronglyMeasurable.inner hgm.aestronglyMeasurable)
      (Filter.Eventually.of_forall hpoint)
  have he : energy≤C*Real.sqrt energy*Real.sqrt ((volume.prod volume).real E)*U^(1/4:ℝ) := by
    calc
      _ = ‖∫ z, inner ℂ (F z) (g z) ∂volume.prod volume‖ := hpairNorm.symm
      _ = ‖∫ z in E, inner ℂ (F z) (g z) ∂volume.prod volume‖ := congrArg norm hset
      _ ≤ ∫ z in E, ‖inner ℂ (F z) (g z)‖ ∂volume.prod volume := norm_integral_le_integral_norm _
      _ ≤ ∫ z in E, ‖F z‖ ∂volume.prod volume := integral_mono hInt.norm h.1.norm hpoint
      _ ≤ _ := h.2
  have hroot : Real.sqrt energy≤C*Real.sqrt ((volume.prod volume).real E)*U^(1/4:ℝ) := by
    by_cases hz : Real.sqrt energy=0
    · rw [hz]
      positivity
    · have hp : 0<Real.sqrt energy := lt_of_le_of_ne (Real.sqrt_nonneg energy) (Ne.symm hz)
      nlinarith [Real.sq_sqrt henergy]
  calc
    _ = (Real.sqrt energy)^2 := (Real.sq_sqrt henergy).symm
    _ ≤ (C*Real.sqrt ((volume.prod volume).real E)*U^(1/4:ℝ))^2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg energy) hroot 2
    _ = (C*U^(1/4:ℝ))^2*(Real.sqrt ((volume.prod volume).real E))^2 := by ring
    _ = _ := by rw [Real.sq_sqrt measureReal_nonneg]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCrossAdjointEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cross-profile adjoint energy from four genuine ordinary packet families. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem four_polarization_norm_sq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (v a b c d : V) (h : (4:ℂ) • v=a-b-Complex.I • c+Complex.I • d) :
    ‖v‖^2≤‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2 := by
  have hn : 4*‖v‖≤‖a‖+‖b‖+‖c‖+‖d‖ := by
    calc
      _ = ‖(4:ℂ) • v‖ := by rw [norm_smul]; norm_num
      _ = ‖a-b-Complex.I • c+Complex.I • d‖ := congrArg norm h
      _ ≤ ‖a-b-Complex.I • c‖+‖Complex.I • d‖ := norm_add_le _ _
      _ ≤ (‖a-b‖+‖Complex.I • c‖)+‖Complex.I • d‖ :=
        add_le_add (norm_sub_le (a-b) (Complex.I • c)) le_rfl
      _ ≤ ((‖a‖+‖b‖)+‖Complex.I • c‖)+‖Complex.I • d‖ :=
        add_le_add (add_le_add (norm_sub_le a b) le_rfl) le_rfl
      _ = _ := by simp only [norm_smul,Complex.norm_I,one_mul]
  have hs := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ)≤4) (norm_nonneg v)) hn 2
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖c‖-‖d‖),sq_nonneg (‖a‖+‖b‖-‖c‖-‖d‖)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataUniformCrossEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform polynomial energy bound for the actual cross-profile sum.
The remaining cost conditions concern only explicit fixed geometric data. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_uniform_cross_energy (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar < cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
    ∀ (_hSpectrum : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta)
    (_hMargin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
    (_hBin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤d.Cv/P.width), ∀ L p : ℝ, 2≤L → 0≤p → d.unitModelCost CD CS CT≤L →
    ordinaryDensityUpper^(1/4:ℝ)≤L → P.profileBound≤L^p → P.referenceEnvelopeConstant≤L^p →
    ∀ S : Finset P.PacketIndex, S⊆initial →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ E : Set (ℝ×ℝ), MeasurableSet E → (volume.prod volume) E≠∞ →
      (∀ z, z∉E → g z=0) → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∫ z, ‖∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q‖^2
        ∂volume.prod volume)≤(L^(3*p+6))^2*(volume.prod volume).real E := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hAll⟩ := exists_universal_ordinary_adjoint_energy hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P initial d h₁eq h₂eq h₃eq h₄eq h₅eq alt hAlt
    hSpectrum hMargin hBin L p hL hp hunit hU hprofile habsolute
  have hLpos : 0<L := by linarith
  have hLone : 1≤L := by linarith
  have hDensityPos : 0<ordinaryDensityUpper := zero_lt_one.trans_le (le_max_left _ _)
  have hscale : 2*L^p≤L^(p+1) := by
    rw [Real.rpow_add hLpos,Real.rpow_one]
    nlinarith [Real.rpow_nonneg hLpos.le p]
  let Q := fun (c : ℂ) (hc : ‖c‖=1) => P.polarize alt hAlt c hc
  have hFor (c : ℂ) (hc : ‖c‖=1) :
      ∀ S : Finset P.PacketIndex, S⊆initial →
      ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖≤1) →
      ∀ E : Set (ℝ×ℝ), MeasurableSet E → (volume.prod volume) E≠∞ →
        (∀ z, z∉E → g z=0) → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
        (∫ z, ‖(Q c hc).ordinaryAdjointSum S d.selector u g z‖^2 ∂volume.prod volume)≤
          (L^(3*p+5))^2*(volume.prod volume).real E := by
    let dp := d.polarize alt hAlt c hc hSpectrum hMargin hBin
    have hunitp : dp.unitModelCost CD CS CT≤L := hunit
    have hprofilep : (Q c hc).profileBound≤L^(p+1) :=
      (mul_le_mul_of_nonneg_left hprofile (by norm_num : (0:ℝ)≤2)).trans hscale
    have habsoluteEq : (Q c hc).referenceEnvelopeConstant=2*P.referenceEnvelopeConstant := by
      dsimp only [Q,polarize,referenceEnvelopeConstant]
      ring
    have habsolutep : (Q c hc).referenceEnvelopeConstant≤L^(p+1) := by
      rw [habsoluteEq]
      exact (mul_le_mul_of_nonneg_left habsolute (by norm_num : (0:ℝ)≤2)).trans hscale
    have hcost := dp.modelCost_le_rpow CD CS CT L L (p+1) hCS.le hLone le_rfl
      (by linarith) hunitp hprofilep habsolutep
    have hcost' : dp.modelCost CD CS CT≤L^(3*p+4) := by
      convert hcost using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    have hcU : dp.modelCost CD CS CT*ordinaryDensityUpper^(1/4:ℝ)≤L^(3*p+5) := by
      calc
        _ ≤ L^(3*p+4)*L := mul_le_mul hcost' hU (Real.rpow_nonneg hDensityPos.le _) (Real.rpow_nonneg hLpos.le _)
        _ = L^(3*p+4)*L^(1:ℝ) := by rw [Real.rpow_one]
        _ = L^((3*p+4)+1) := (Real.rpow_add hLpos _ _).symm
        _ = _ := by congr 1; ring
    intro S hS g hg hg1 E hE hEfin hgs u hu
    have h := hAll N κ Label Item (Q c hc) initial dp h₁eq h₂eq h₃eq h₄eq h₅eq
      S hS g hg hg1 E hE hEfin hgs u hu
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg (dp.modelCost_pos CD CS CT).le
        (Real.rpow_nonneg hDensityPos.le _)) hcU 2) measureReal_nonneg)
  have h₁ := hFor 1 (by simp)
  have h₂ := hFor (-1) (by simp)
  have h₃ := hFor Complex.I (by simp)
  have h₄ := hFor (-Complex.I) (by simp)
  have hfinal : 4*(L^(3*p+5))^2≤(L^(3*p+6))^2 := by
    have hn : 2*L^(3*p+5)≤L^(3*p+6) := by
      calc
        _ ≤ L^(3*p+5)*L := by nlinarith [Real.rpow_nonneg hLpos.le (3*p+5)]
        _ = L^(3*p+5)*L^(1:ℝ) := by rw [Real.rpow_one]
        _ = L^((3*p+5)+1) := (Real.rpow_add hLpos _ _).symm
        _ = _ := by congr 1; ring
    have hs := pow_le_pow_left₀ (by positivity) hn 2
    nlinarith
  intro S hS g hg hg1 E hE hEfin hgs u hu
  let A := (Q 1 (by simp)).ordinaryAdjointSum S d.selector u g
  let B := (Q (-1) (by simp)).ordinaryAdjointSum S d.selector u g
  let C := (Q Complex.I (by simp)).ordinaryAdjointSum S d.selector u g
  let D := (Q (-Complex.I) (by simp)).ordinaryAdjointSum S d.selector u g
  let X := fun z => ∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q
  have hA := ((Q 1 (by simp)).ordinaryAdjointSum_memLp S d.selector u g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hB := ((Q (-1) (by simp)).ordinaryAdjointSum_memLp S d.selector u g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hC := ((Q Complex.I (by simp)).ordinaryAdjointSum_memLp S d.selector u g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hD := ((Q (-Complex.I) (by simp)).ordinaryAdjointSum_memLp S d.selector u g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hX := (P.crossSum_memLp alt hAlt 0 d.selector u g 2 S).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hp (z : ℝ×ℝ) : ‖X z‖^2≤‖A z‖^2+‖B z‖^2+‖C z‖^2+‖D z‖^2 :=
    four_polarization_norm_sq _ _ _ _ _ (P.cross_adjoint_polarization alt hAlt S d.selector
      d.measurable d.bounded u hu g hg hg1 z)
  calc
    _ ≤ ∫ z, ‖A z‖^2+‖B z‖^2+‖C z‖^2+‖D z‖^2 ∂volume.prod volume :=
      integral_mono hX (((hA.add hB).add hC).add hD) hp
    _ = (∫ z, ‖A z‖^2 ∂volume.prod volume)+(∫ z, ‖B z‖^2 ∂volume.prod volume)+
        (∫ z, ‖C z‖^2 ∂volume.prod volume)+(∫ z, ‖D z‖^2 ∂volume.prod volume) := by
      have hab : (∫ z, ‖A z‖^2+‖B z‖^2 ∂volume.prod volume)=
          (∫ z, ‖A z‖^2 ∂volume.prod volume)+(∫ z, ‖B z‖^2 ∂volume.prod volume) := integral_add hA hB
      have habc : (∫ z, ‖A z‖^2+‖B z‖^2+‖C z‖^2 ∂volume.prod volume)=
          (∫ z, ‖A z‖^2+‖B z‖^2 ∂volume.prod volume)+(∫ z, ‖C z‖^2 ∂volume.prod volume) :=
        integral_add (hA.add hB) hC
      calc
        _ = (∫ z, ‖A z‖^2+‖B z‖^2+‖C z‖^2 ∂volume.prod volume)+
            (∫ z, ‖D z‖^2 ∂volume.prod volume) := integral_add ((hA.add hB).add hC) hD
        _ = _ := by rw [habc,hab]
    _ ≤ (L^(3*p+5))^2*(volume.prod volume).real E+(L^(3*p+5))^2*(volume.prod volume).real E+
        (L^(3*p+5))^2*(volume.prod volume).real E+(L^(3*p+5))^2*(volume.prod volume).real E :=
      add_le_add (add_le_add (add_le_add (h₁ S hS g hg hg1 E hE hEfin hgs u hu)
        (h₂ S hS g hg hg1 E hE hEfin hgs u hu))
        (h₃ S hS g hg hg1 E hE hEfin hgs u hu)) (h₄ S hS g hg hg1 E hE hEfin hgs u hu)
    _ = (4*(L^(3*p+5))^2)*(volume.prod volume).real E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfinal measureReal_nonneg

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataIntrinsicCrossEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cross-profile energy is independent of the auxiliary
jet scale. Its polynomial exponent is fixed before the mask exponent. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_intrinsic_cross_energy (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar < cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
    ∀ (_hSpectrum : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta)
    (_hMargin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
    (_hBin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤d.Cv/P.width), ∀ L p : ℝ, 2≤L → 0≤p → d.unitModelCost CD CS CT≤L →
    ordinaryDensityUpper^(1/4:ℝ)≤L → (2^P.order*P.profileBound)*3^(2*P.order)≤L^p →
    ∀ S : Finset P.PacketIndex, S⊆initial →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ E : Set (ℝ×ℝ), MeasurableSet E → (volume.prod volume) E≠∞ →
      (∀ z, z∉E → g z=0) → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∫ z, ‖∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q‖^2
        ∂volume.prod volume)≤(L^(3*p+6))^2*(volume.prod volume).real E := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hAll⟩ := exists_uniform_cross_energy hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅ alt hAlt
    hSpectrum hMargin hBin L p hL hp hunit hU hprofile S hS g hg hg1 E hE hEfin hgs u hu
  let Q := P.withJetControl 0 1 (by norm_num) (by simp)
  let dq := d.withJetControl 0 1 (by norm_num) (by simp)
  have hb : P.profileBound≤(2^P.order*P.profileBound)*3^(2*P.order) := by
    have h₂ : (1:ℝ)≤2^P.order := one_le_pow₀ (by norm_num)
    have h₃ : (1:ℝ)≤3^(2*P.order) := one_le_pow₀ (by norm_num)
    calc
      _ ≤ 2^P.order*P.profileBound := le_mul_of_one_le_left P.profileBound_pos.le h₂
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (pow_nonneg (by norm_num) _) P.profileBound_pos.le) h₃
  have hprofileQ : Q.profileBound≤L^p := hb.trans hprofile
  have habsoluteQ : Q.referenceEnvelopeConstant≤L^p := by
    simpa only [Q,referenceEnvelopeConstant,PacketLatticeData.withJetControl,one_pow,mul_one] using hprofile
  have h := hAll N κ Label Item Q initial dq heq₁ heq₂ heq₃ heq₄ heq₅ alt hAlt
    hSpectrum hMargin hBin L p hL hp hunit hU hprofileQ habsoluteQ
    S hS g hg hg1 E hE hEfin hgs u hu
  change (∫ z, ‖∑ q∈S, Q.crossPacketValue alt hAlt 0 d.selector u g z q‖^2
    ∂volume.prod volume)≤(L^(3*p+6))^2*(volume.prod volume).real E at h
  have he (z : ℝ×ℝ) (q : P.PacketIndex) :
      Q.crossPacketValue alt hAlt 0 d.selector u g z q=
        P.crossPacketValue alt hAlt 0 d.selector u g z q :=
    P.withJetControl_crossPacketValue 0 1 (by norm_num) (by simp)
      alt hAlt 0 d.selector u g z q
  simpa only [he] using h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataHighDensityEnergyRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Popular recovery for the actual high-density sum. The energy bound
follows from ordinary model estimates. The hypotheses concern explicit
packet geometry and a bounded supported input. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_high_density_energy_recovery
    (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F c0 cone Lip Cv aDensity p0 decay : ℝ)
    (D K H J₀ : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
    (hcb : 0 < cb) (hcbQuarter : cb ≤ 1/4) (hCv : 0 ≤ Cv) (hCb : 0 ≤ Cb) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hcone : 1 ≤ cone) (hconeK : cone ≤ K) (hLip : 0 ≤ Lip)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0)
    (hdecay : 0 ≤ decay) (hD : 4 ≤ D)
    (hgap : cStar < cEta*cb) (hJ : 2*cone+1 ≤ (2:ℝ)^J₀) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ ∃ A L0 : ℝ, aDensity+3 < A ∧ 16 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (w tau : ℝ), 0 < w →
      P.scale = 4*(L^(A+2)*P.width) → P.ratioBound = 4*L^(A+2) →
      (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
      6+2*(8*D+1) ≤ P.order → packets.Nonempty →
    ∀ (d : OrdinaryModelConfig P packets),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
      d.w=w → d.tau=tau → d.unitModelCost CD CS CT≤L →
    ∀ (Eset Fset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      MeasurableSet Eset → (volume.prod volume) Eset ≠ ∞ →
      (∀ q ∈ packets, L^(-aDensity) < P.ordinaryDensity 0 cell grid w tau Eset
        (fun z => field (planeCoordinates z)) q) →
      (∀ q ∈ packets, 0+P.rowSlope q.1 q.2.1 ∈
        scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q ∈ packets, scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ⊆ Icc (-1) 1) →
    ∀ (l r : ℝ), LipschitzWith 1 field → 600*(r-l) ≤ 1 →
      (∀ z ∈ Eset, z.1 ∈ Icc l r) → (∀ z ∈ Fset, z.1 ∈ Icc l r) →
      MeasurableSet Fset → (volume.prod volume) Fset ≠ ∞ →
      0 < (volume.prod volume).real Fset →
    ∀ (ratio widthScale : ℝ), 0 < ratio → L/2 ≤ Real.log ratio → Real.log ratio ≤ 2*L →
      (volume.prod volume).real Eset = ratio^2*(volume.prod volume).real Fset →
      Real.exp (L^(9/10:ℝ)) ≤ widthScale → widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
      P.width = widthScale*w → 0 ≤ tau → tau ≤ Real.exp (-(L^(97/100:ℝ))) →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (_hMargin : ∀ q∈packets, ∀ k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
      (_hBin : ∀ q∈packets, ∀ k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
          |et-P.frequency k|≤d.Cv/P.width)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ), b=d.selector →
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(0+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
      (∀ j l k s, b j l k s ≠ 0 →
        cb*w/P.length j ≤ |s-(0+P.rowSlope j l)| ∧
          |s-(0+P.rowSlope j l)| ≤ Cb*w/P.length j) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => 0+P.rowSlope j l) (w/P.length j) H) →
      (∀ k, c0/w ≤ |P.frequency k|) → (∀ k, |P.frequency k| ≤ F/w) →
      (∀ j l u k xi eta,
        planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta) ≠ 0 →
          |xi+(0+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l u k) (xi,eta) ≠ 0 →
          |xi+(0+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
      (∀ z, z∉Eset → f z=0) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      2 ≤ g.rootWidth →
      (∫ z in Fset, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt 0 b v f z q‖
        ∂volume.prod volume) ≤ L^(-decay)*ratio*(volume.prod volume).real Fset := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hEnergy⟩ := exists_intrinsic_cross_energy hVariation
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hgap
  obtain ⟨A,Lbase,haA,hLbase,hmain⟩ := source_high_density_popular_recovery
    hVariation hLL cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 (3*p0+6) decay D K H J₀
    hcStar hcEta hCEta hcb.le hCb hF hc0 hcone hconeK hLip haDensity hp0
    (by positivity) hdecay hD hgap hJ
  refine ⟨CD,CS,CT,hCD,hCS,hCT,A,max Lbase (ordinaryDensityUpper^(1/4:ℝ)),haA,
    hLbase.trans (le_max_left _ _),?_⟩
  intro L hL κ _ N Label Item _ P packets w tau hw hscale hratioBound hprofile horder hpackets
    d heq₁ heq₂ heq₃ heq₄ heq₅ hwEq htauEq hunit
    Eset Fset field cell grid hEset hEfinite hdensity hcell hcellrange
    l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt hMargin hBin b hbEq hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency
    hspectrum haltSpectrum v hv f hf hf1 hfs g hbranch hzero hrootWidth
  have hLb : Lbase≤L := (le_max_left _ _).trans hL
  have hLtwo : 2≤L := by linarith [hLbase.trans hLb]
  have hU : ordinaryDensityUpper^(1/4:ℝ)≤L := (le_max_right _ _).trans hL
  have halt : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta := by
    intro j l a k xi et hn
    simpa only [zero_add,heq₁,heq₂,heq₃,hwEq] using haltSpectrum j l a k xi et hn
  have henergy := hEnergy N κ Label Item P packets d heq₁ heq₂ heq₃ heq₄ heq₅ alt hAlt
    halt hMargin hBin L p0 hLtwo hp0 hunit hU hprofile packets (Finset.Subset.refl _)
    f hf hf1 Eset hEset hEfinite hfs v hv
  rw [←hbEq] at henergy
  exact hmain L hLb κ N Label Item P packets 0 w tau hw hscale hratioBound hprofile horder hpackets
    Eset Fset field cell grid hEset hEfinite hdensity hcell hcellrange
    l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt b hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency hspectrum haltSpectrum
    v hv f hf hf1 g hbranch hzero hrootWidth henergy

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataIntrinsicDensityPairing
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinct-profile bilinear density estimate, with uniform
polynomial cost and no dependence on the auxiliary jet normalization. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_intrinsic_density_pairing (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar < cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
    ∀ (_hSpectrum : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta)
    (_hMargin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
    (_hBin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤d.Cv/P.width), ∀ L p : ℝ, 2≤L → 0≤p → d.unitModelCost CD CS CT≤L →
    (2^P.order*P.profileBound)*3^(2*P.order)≤L^p →
    ∀ S : Finset P.PacketIndex, S⊆initial →
    ∀ (g f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → Measurable f →
      (∀ z, ‖g z‖≤1) → (∀ z, ‖f z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F →
      (volume.prod volume) E≠∞ → (volume.prod volume) F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u → ∀ eta : ℝ, 0<eta →
      (∀ q∈S, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤eta) →
      Integrable (fun z => inner ℂ
        (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)
        ∂volume.prod volume‖≤L^(3*p+4)*Real.sqrt ((volume.prod volume).real F)*
          Real.sqrt ((volume.prod volume).real E)*eta^(1/4:ℝ) := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hAll⟩ := exists_universal_ordinary_model_estimate hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,hCD,hCS,hCT,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅ alt hAlt
    hSpectrum hMargin hBin L p hL hp hunit hprofile S hS g f hgm hfm hgb hfb
    E F hE hF hEfin hFfin hgs hfs u hu eta heta hdensity
  let Q := P.withJetControl 0 1 (by norm_num) (by simp)
  let dq := d.withJetControl 0 1 (by norm_num) (by simp)
  have hLp : 0<L := by linarith
  have hLone : 1≤L := by linarith
  have hb : P.profileBound≤(2^P.order*P.profileBound)*3^(2*P.order) := by
    have h₂ : (1:ℝ)≤2^P.order := one_le_pow₀ (by norm_num)
    have h₃ : (1:ℝ)≤3^(2*P.order) := one_le_pow₀ (by norm_num)
    calc
      _ ≤ 2^P.order*P.profileBound := le_mul_of_one_le_left P.profileBound_pos.le h₂
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (pow_nonneg (by norm_num) _) P.profileBound_pos.le) h₃
  have hbase : Q.referenceEnvelopeConstant≤L^p := by
    simpa only [Q,referenceEnvelopeConstant,PacketLatticeData.withJetControl,one_pow,mul_one] using hprofile
  have hscale : 2*L^p≤L^(p+1) := by
    rw [Real.rpow_add hLp,Real.rpow_one]
    nlinarith [Real.rpow_nonneg hLp.le p]
  obtain ⟨hf,hfenergy⟩ := bounded_supported_input f hfm hfb F hF hFfin hfs
  have hg := (bounded_supported_input g hgm hgb E hE hEfin hgs).1
  have hFor (c : ℂ) (hc : ‖c‖=1) :
      ‖∫ z, inner ℂ ((Q.polarize alt hAlt c hc).ordinaryAdjointSum S d.selector u g z) (f z)
        ∂volume.prod volume‖≤L^(3*p+4)*Real.sqrt ((volume.prod volume).real F)*
          Real.sqrt ((volume.prod volume).real E)*eta^(1/4:ℝ) := by
    let R := Q.polarize alt hAlt c hc
    let dr := OrdinaryModelConfig.polarize (P:=Q) alt hAlt dq c hc hSpectrum hMargin hBin
    have hpr : R.profileBound≤L^(p+1) :=
      (mul_le_mul_of_nonneg_left (hb.trans hprofile) (by norm_num : (0:ℝ)≤2)).trans hscale
    have harEq : R.referenceEnvelopeConstant=2*Q.referenceEnvelopeConstant := by
      dsimp only [R,polarize,referenceEnvelopeConstant]
      ring
    have har : R.referenceEnvelopeConstant≤L^(p+1) := by
      rw [harEq]
      exact (mul_le_mul_of_nonneg_left hbase (by norm_num : (0:ℝ)≤2)).trans hscale
    have hcost := dr.modelCost_le_rpow CD CS CT L L (p+1) hCS.le hLone le_rfl
      (by linarith) hunit hpr har
    have hcost' : dr.modelCost CD CS CT≤L^(3*p+4) := by
      convert hcost using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    have hm := hAll N κ Label Item R initial dr heq₁ heq₂ heq₃ heq₄ heq₅
      S hS f hf E hE hEfin u hu eta heta hdensity
    change IntegrableOn (R.ordinaryForwardSum S d.selector u f) E (volume.prod volume) ∧
      (∫ z in E, ‖R.ordinaryForwardSum S d.selector u f z‖ ∂volume.prod volume)≤
      dr.modelCost CD CS CT*Real.sqrt (∫ z, ‖f z‖^2 ∂volume.prod volume)*
        Real.sqrt ((volume.prod volume).real E)*eta^(1/4:ℝ) at hm
    have ha := R.ordinary_adjoint_pairing_bound S d.selector d.measurable d.bounded
      u hu f g hf hg hgm hgb E hE hgs hm.1
    apply ha.2.trans (hm.2.trans ?_)
    gcongr
  have h := Q.cross_pairing_bound alt hAlt S d.selector d.measurable d.bounded u hu
    g f hgm hgb hf _ hFor
  have he (z : ℝ×ℝ) (q : P.PacketIndex) :
      Q.crossPacketValue alt hAlt 0 d.selector u g z q=
        P.crossPacketValue alt hAlt 0 d.selector u g z q :=
    P.withJetControl_crossPacketValue 0 1 (by norm_num) (by simp)
      alt hAlt 0 d.selector u g z q
  have hsum (z : ℝ×ℝ) : (∑ q∈S, Q.crossPacketValue alt hAlt 0 d.selector u g z q)=
      ∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q :=
    Finset.sum_congr rfl (fun q _ => he z q)
  have hpair (z : ℝ×ℝ) :
      inner ℂ (∑ q∈S, Q.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)=
      inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z) :=
    congrArg (fun v => inner ℂ v (f z)) (hsum z)
  refine ⟨h.1.congr (Filter.Eventually.of_forall hpair),?_⟩
  have hi : (∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)
      ∂volume.prod volume)=
      ∫ z, inner ℂ (∑ q∈S, Q.crossPacketValue alt hAlt 0 d.selector u g z q) (f z)
        ∂volume.prod volume :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => (hpair z).symm))
  rw [hi]
  exact h.2

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataModelBilinearRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete low/high density assembly for the actual finite
bilinear model in a direction chart. The high family is constructed
from the original collection; no energy or counting premise remains. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq

theorem source_model_bilinear_recovery
    (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F c0 cone Lip Cv aDensity p0 decay : ℝ)
    (D K H J₀ : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
    (hcb : 0 < cb) (hcbQuarter : cb ≤ 1/4) (hCv : 0 ≤ Cv) (hCb : 0 ≤ Cb) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hcone : 1 ≤ cone) (hconeK : cone ≤ K) (hLip : 0 ≤ Lip)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0)
    (hdecay : 0 ≤ decay) (hbudget : 4*(3*p0+4+decay)≤aDensity) (hD : 4 ≤ D)
    (hgap : cStar < cEta*cb) (hJ : 2*cone+1 ≤ (2:ℝ)^J₀) :
    ∃ CD CS CT LD LS LT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<LD ∧ 0<LS ∧ 0<LT ∧ ∃ A L0 : ℝ, aDensity+3 < A ∧ 16 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (w tau : ℝ), 0 < w →
      P.scale = 4*(L^(A+2)*P.width) → P.ratioBound = 4*L^(A+2) →
      (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
      6+2*(8*D+1) ≤ P.order → packets.Nonempty →
    ∀ (d : OrdinaryModelConfig P packets),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
      d.w=w → d.tau=tau → d.unitModelCost CD CS CT≤L → d.unitModelCost LD LS LT≤L →
    ∀ (Eset Fset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ), cell=d.cell → grid=d.grid →
      MeasurableSet Eset → (volume.prod volume) Eset ≠ ∞ →
      (∀ q ∈ packets, 0+P.rowSlope q.1 q.2.1 ∈
        scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q ∈ packets, scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ⊆ Icc (-1) 1) →
    ∀ (l r : ℝ), LipschitzWith 1 field → 600*(r-l) ≤ 1 →
      (∀ z ∈ Eset, z.1 ∈ Icc l r) → (∀ z ∈ Fset, z.1 ∈ Icc l r) →
      MeasurableSet Fset → (volume.prod volume) Fset ≠ ∞ →
      0 < (volume.prod volume).real Fset →
    ∀ (ratio widthScale : ℝ), 0 < ratio → L/2 ≤ Real.log ratio → Real.log ratio ≤ 2*L →
      (volume.prod volume).real Eset = ratio^2*(volume.prod volume).real Fset →
      Real.exp (L^(9/10:ℝ)) ≤ widthScale → widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
      P.width = widthScale*w → 0 ≤ tau → tau ≤ Real.exp (-(L^(97/100:ℝ))) →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (_hMargin : ∀ q∈packets, ∀ k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
      (_hBin : ∀ q∈packets, ∀ k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
          |et-P.frequency k|≤d.Cv/P.width)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ), b=d.selector →
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(0+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
      (∀ j l k s, b j l k s ≠ 0 →
        cb*w/P.length j ≤ |s-(0+P.rowSlope j l)| ∧
          |s-(0+P.rowSlope j l)| ≤ Cb*w/P.length j) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => 0+P.rowSlope j l) (w/P.length j) H) →
      (∀ k, c0/w ≤ |P.frequency k|) → (∀ k, |P.frequency k| ≤ F/w) →
      (∀ j l u k xi eta,
        planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta) ≠ 0 →
          |xi+(0+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l u k) (xi,eta) ≠ 0 →
          |xi+(0+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
      (∀ z, z∉Eset → f z=0) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      2 ≤ g.rootWidth →
    ∀ (test : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖≤1) →
      (∀ z, z∉Fset → test z=0) →
      Integrable (fun z => inner ℂ
        (∑ q∈packets, P.crossPacketValue alt hAlt 0 b
          (fun z => field (planeCoordinates z)) f z q) (test z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈packets, P.crossPacketValue alt hAlt 0 b
        (fun z => field (planeCoordinates z)) f z q) (test z) ∂volume.prod volume‖≤
          2*L^(-decay)*ratio*(volume.prod volume).real Fset := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,A,L0,haA,hL0,hHigh⟩ := source_high_density_energy_recovery
    hVariation hLL cStar cEta CEta cb Cb F c0 cone Lip Cv aDensity p0 decay D K H J₀
    hcStar hcEta hCEta hcb hcbQuarter hCv hCb hF hc0 hcone hconeK hLip haDensity hp0
    hdecay hD hgap hJ
  obtain ⟨LD,LS,LT,hLD,hLS,hLT,hLow⟩ := exists_intrinsic_density_pairing hVariation
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hgap
  refine ⟨CD,CS,CT,LD,LS,LT,hCD,hCS,hCT,hLD,hLS,hLT,A,L0,haA,hL0,?_⟩
  intro L hL κ _ N Label Item _ P packets w tau hw hscale hratioBound hprofile horder hpackets
    d heq₁ heq₂ heq₃ heq₄ heq₅ hwEq htauEq hunitHigh hunitLow
    Eset Fset field cell grid hcellEq hgridEq hEset hEfinite hcell hcellrange
    l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt hMargin hBin b hbEq hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency
    hspectrum haltSpectrum f hf hf1 hfs g hbranch hzero hrootWidth test htest htest1 htests
  let v : ℝ×ℝ → ℝ := fun z => field (planeCoordinates z)
  have hv : Measurable v := (product_slope_lipschitz field hfield).continuous.measurable
  have hLtwo : 2≤L := by linarith only [hL0.trans hL]
  have hLone : 1≤L := (by norm_num : (1:ℝ)≤2).trans hLtwo
  have hLp : 0<L := zero_lt_one.trans_le hLone
  let eta := L^(-aDensity)
  have heta : 0<eta := Real.rpow_pos_of_pos hLp _
  let high := packets.filter (fun q => eta<P.ordinaryDensity 0 cell grid w tau Eset v q)
  let low := packets\high
  have hhigh : high⊆packets := Finset.filter_subset _ _
  have hlow : low⊆packets := Finset.sdiff_subset
  have hdhigh (q : P.PacketIndex) (hq : q∈high) :
      L^(-aDensity)<P.ordinaryDensity 0 cell grid w tau Eset v q := (Finset.mem_filter.mp hq).2
  have hdlow (q : P.PacketIndex) (hq : q∈low) :
      P.ordinaryDensity 0 d.cell d.grid d.w d.tau Eset v q≤eta := by
    have hq' := Finset.mem_sdiff.mp hq
    have hn : ¬eta<P.ordinaryDensity 0 cell grid w tau Eset v q := by
      intro hn
      exact hq'.2 (Finset.mem_filter.mpr ⟨hq'.1,hn⟩)
    simpa only [hcellEq,hgridEq,hwEq,htauEq] using le_of_not_gt hn
  have halt : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta := by
    intro j l a k xi et hn
    simpa only [zero_add,heq₁,heq₂,heq₃,hwEq] using haltSpectrum j l a k xi et hn
  have hlowPair := hLow N κ Label Item P packets d heq₁ heq₂ heq₃ heq₄ heq₅
    alt hAlt halt hMargin hBin L p0 hLtwo hp0 hunitLow hprofile low hlow
    f test hf htest hf1 htest1 Eset Fset hEset hFset hEfinite hFfinite hfs htests v hv eta heta hdlow
  rw [←hbEq] at hlowPair
  let V := fun (S : Finset P.PacketIndex) (z : ℝ×ℝ) =>
    ∑ q∈S, P.crossPacketValue alt hAlt 0 b v f z q
  have hhighInt : IntegrableOn (V high) Fset (volume.prod volume) :=
    (memLp_one_iff_integrable.mp (P.crossSum_memLp alt hAlt 0 b v f 1 high)).integrableOn
  have hhighBound : (∫ z in Fset, ‖V high z‖ ∂volume.prod volume)≤
      L^(-decay)*ratio*(volume.prod volume).real Fset := by
    by_cases hn : high.Nonempty
    · let dh := d.restrict high hhigh
      exact hHigh L hL κ N Label Item P high w tau hw hscale hratioBound hprofile horder hn
        dh heq₁ heq₂ heq₃ heq₄ heq₅ hwEq htauEq hunitHigh
        Eset Fset field cell grid hEset hEfinite hdhigh
        (fun q hq => hcell q (hhigh hq)) (fun q hq => hcellrange q (hhigh hq))
        l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
        ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
        alt hAlt (fun q hq => hMargin q (hhigh hq)) (fun q hq => hBin q (hhigh hq))
        b hbEq hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency hspectrum haltSpectrum
        v hv f hf hf1 hfs g hbranch hzero hrootWidth
    · have hz : high=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [V,hz,Finset.sum_empty,norm_zero,integral_zero]
      positivity
  have hhighPair := supported_inner_integral_le (volume.prod volume) Fset hFset
    (V high) test hhighInt htest htest1 htests
  have hroot : Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real Eset)=
      ratio*(volume.prod volume).real Fset := by
    rw [hratioEq,Real.sqrt_mul (sq_nonneg ratio),Real.sqrt_sq hratio.le]
    calc
      _ = ratio*(Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real Fset)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt measureReal_nonneg]
  have hpower : L^(3*p0+4)*eta^(1/4:ℝ)≤L^(-decay) := by
    dsimp only [eta]
    rw [←Real.rpow_mul hLp.le,←Real.rpow_add hLp]
    exact Real.rpow_le_rpow_of_exponent_le hLone (by linarith only [hbudget])
  have hlowBound : ‖∫ z, inner ℂ (V low z) (test z) ∂volume.prod volume‖≤
      L^(-decay)*ratio*(volume.prod volume).real Fset := by
    apply hlowPair.2.trans
    calc
      _ = (L^(3*p0+4)*eta^(1/4:ℝ))*
          (Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real Eset)) := by ring
      _ ≤ L^(-decay)*(Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real Eset)) :=
        mul_le_mul_of_nonneg_right hpower (by positivity)
      _ = _ := by rw [hroot]; ring
  have hsplit (z : ℝ×ℝ) : V packets z=V low z+V high z := by
    exact (Finset.sum_sdiff hhigh (f:=fun q => P.crossPacketValue alt hAlt 0 b v f z q)).symm
  have hpairSplit (z : ℝ×ℝ) : inner ℂ (V packets z) (test z)=
      inner ℂ (V low z) (test z)+inner ℂ (V high z) (test z) := by rw [hsplit,inner_add_left]
  have hInt : Integrable (fun z => inner ℂ (V packets z) (test z)) (volume.prod volume) :=
    (hlowPair.1.add hhighPair.1).congr (Filter.Eventually.of_forall (fun z => (hpairSplit z).symm))
  refine ⟨hInt,?_⟩
  calc
    _ = ‖(∫ z, inner ℂ (V low z) (test z) ∂volume.prod volume)+
        (∫ z, inner ℂ (V high z) (test z) ∂volume.prod volume)‖ := by
      rw [←integral_add hlowPair.1 hhighPair.1]
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall hpairSplit)
    _ ≤ ‖∫ z, inner ℂ (V low z) (test z) ∂volume.prod volume‖+
        ‖∫ z, inner ℂ (V high z) (test z) ∂volume.prod volume‖ := norm_add_le _ _
    _ ≤ (L^(-decay)*ratio*(volume.prod volume).real Fset)+
        (L^(-decay)*ratio*(volume.prod volume).real Fset) :=
      add_le_add hlowBound (hhighPair.2.trans hhighBound)
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketAngularPartition
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction after the three-grid split. The selector for
each piece agrees with the original one on every retained packet. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem sum_angularPackets (P : PacketLatticeData N κ Label Item)
    (initial : Finset P.PacketIndex) (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice)
    {E : Type*} [AddCommMonoid E] (f : P.PacketIndex → E) :
    (∑ g : DyadicLineGrid.GridChoice, ∑ a∈P.angularPackets initial tag g, f a)=
      ∑ a∈initial, f a := by
  simp only [angularPackets,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem crossPacketValue_congr_selector (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (t : ℝ) (b c : ∀ j, P.labels j → κ → ℝ → ℂ)
    (u : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) (a : P.PacketIndex)
    (h : ∀ k s, b a.1 a.2.1 k s=c a.1 a.2.1 k s) :
    P.crossPacketValue alt hAlt t b u g z a=P.crossPacketValue alt hAlt t c u g z a := by
  have he : b a.1 a.2.1=c a.1 a.2.1 := funext (fun k => funext (h k))
  simp only [crossPacketValue,physicalMultiplierCoefficient,he]

theorem crossPacketValue_angularSelector (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (initial : Finset P.PacketIndex) (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice)
    (grid : DyadicLineGrid.GridChoice) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (t : ℝ) (u : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (z : ℝ×ℝ) (a : P.PacketIndex) (ha : a∈P.angularPackets initial tag grid) :
    P.crossPacketValue alt hAlt t (P.angularSelector tag grid b) u g z a=
      P.crossPacketValue alt hAlt t b u g z a := by
  apply P.crossPacketValue_congr_selector alt hAlt t _ _ u g z a
  intro k s
  simp only [angularSelector,(Finset.mem_filter.mp ha).2,ite_true, if_true]

theorem sum_crossPacketValue_angularPartition (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (initial : Finset P.PacketIndex) (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (t : ℝ) (u : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    (∑ grid : DyadicLineGrid.GridChoice, ∑ a∈P.angularPackets initial tag grid,
      P.crossPacketValue alt hAlt t (P.angularSelector tag grid b) u g z a)=
      ∑ a∈initial, P.crossPacketValue alt hAlt t b u g z a := by
  calc
    _ = ∑ grid : DyadicLineGrid.GridChoice, ∑ a∈P.angularPackets initial tag grid,
        P.crossPacketValue alt hAlt t b u g z a := by
      apply Finset.sum_congr rfl
      intro grid _
      exact Finset.sum_congr rfl (fun a ha =>
        P.crossPacketValue_angularSelector alt hAlt initial tag grid b t u g z a ha)
    _ = _ := P.sum_angularPackets initial tag _

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceFullAngularGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common source grid for every row of a finite collection. Its root
is chosen after the row precisions; no extra eligibility hypothesis is
needed in the application of the packet recovery theorem. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem exists_source_full_angular_grid {ι : Type*} [Fintype ι]
    (L : ℝ) (hL : 1 ≤ L) (precision : ι → ℝ)
    (hp : ∀ i, 0 ≤ precision i) :
    ∃ g : AngularGrid, (g.branching : ℝ) = SourceParameters.step L ∧
      2 ≤ g.rootWidth ∧
      ∀ i, g.eligible (g.rootWidth / SourceParameters.branching L ^ 2) (precision i) 0 := by
  classical
  have he : 0 < SourceParameters.stepExponent L := by
    by_contra hn
    have hz : SourceParameters.stepExponent L = 0 := by omega
    have hb := (SourceParameters.log_step_bounds (by linarith : 0 ≤ L)).1
    simp only [SourceParameters.step, hz, pow_zero, Real.log_one] at hb
    exact (not_le_of_gt (Real.rpow_pos_of_pos (by linarith : 0 < L) _)) hb
  have hbranch : 2 ≤ 2 ^ SourceParameters.stepExponent L := by
    simpa using (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) he)
  let R := 2 + SourceParameters.branching L ^ 2 * ∑ i, precision i
  have hsum : 0 ≤ ∑ i, precision i := Finset.sum_nonneg (fun i _ => hp i)
  have hR : 2 ≤ R := by
    dsimp only [R]
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hsum)
  let g : AngularGrid := ⟨2 ^ SourceParameters.stepExponent L, hbranch, 0, R, by linarith⟩
  refine ⟨g, ?_, hR, ?_⟩
  · simp only [g, SourceParameters.step, Nat.cast_pow, Nat.cast_ofNat]
  · intro i
    change precision i * (g.branching : ℝ)^0 ≤ R / SourceParameters.branching L ^ 2
    rw [pow_zero, mul_one, le_div_iff₀ (pow_pos (SourceParameters.branching_pos L) 2)]
    have hi : precision i ≤ ∑ j, precision j :=
      Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
    have hb := mul_le_mul_of_nonneg_right hi (sq_nonneg (SourceParameters.branching L))
    dsimp only [R]
    nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketAngularHighPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full high-disparity estimate for the actual three angular pieces.
All model costs are absorbed before choosing the finite lattice. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_angular_high_pairing_oai (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cv radius F c0 cone p0 decay : ℝ) (D K H J : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0≤CEta) (hCv : 0≤Cv)
    (hcb : 0 < cb) (hcbQuarter : cb≤1/4) (hsmall : cStar/cEta < cb/4)
    (hr : 0 ≤ radius) (hF : 0≤F) (hc0 : 0 < c0) (hcone : 1 ≤ cone)
    (hrcone : radius ≤ cone) (hconeK : cone≤K) (hp0 : 0≤p0) (hdecay : 0≤decay)
    (hD : 4≤D) (hJ : 2*cone+1≤(2:ℝ)^J)
    (hcoverSmall : 6*max radius (cStar/cEta+cb)<1)
    (num : OrdinaryModelNumerics cStar cEta cb radius) :
    ∃ A L0 : ℝ, 0≤A ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex) (w : ℝ),
      0<w → w≤P.width → 207≤P.order → 6+2*(8*D+1)≤P.order →
      P.scale=4*(L^(A+2)*P.width) → P.ratioBound=4*L^(A+2) →
      (2^P.order*P.profileBound)*3^(2*P.order)≤L^p0 →
      P.topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ k, c0/w≤|P.frequency k|) → (∀ k, |P.frequency k|≤F/w) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) H) →
      (∀ j l, |P.rowSlope j l|+w/P.length j≤1) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
      (∀ j l a k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ j l a k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖≤1) →
      (∀ j l k s, b j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|) →
      (∀ j l k s, b j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖≤|s-t|/(w/P.length j)) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      0<(volume.prod volume).real Fset →
      (∀ z, z∉E → f z=0) → (∀ z, z∉Fset → g z=0) →
    ∀ l r ratio widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z∈E, z.1∈Icc l r) → (∀ z∈Fset, z.1∈Icc l r) →
      0 < ratio → L/2≤Real.log ratio → Real.log ratio≤2*L →
      (volume.prod volume).real E=ratio^2*(volume.prod volume).real Fset →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      P.width=widthScale*w →
      Integrable (fun z => inner ℂ
        (∑ a∈S, P.crossPacketValue alt hAlt 0 b (fun z => field (planeCoordinates z)) f z a) (g z))
        (volume.prod volume) ∧
      ‖∫ z, inner ℂ
        (∑ a∈S, P.crossPacketValue alt hAlt 0 b (fun z => field (planeCoordinates z)) f z a) (g z)
        ∂volume.prod volume‖≤6*L^(-decay)*ratio*(volume.prod volume).real Fset := by
  have hsep : cStar < cEta*cb := by
    have h : cStar/cEta < cb := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hcEta).mp h
  let aDensity := 4*(3*p0+4+decay)
  obtain ⟨CD,CS,CT,LD,LS,LT,_hCD,_hCS,_hCT,_hLD,_hLS,_hLT,A,Lbase,hA,hbase,hmain⟩ :=
    source_model_bilinear_recovery hVariation hLL cStar cEta CEta cb radius F c0 cone 1 Cv
      aDensity p0 decay D K H J hcStar hcEta hCEta hcb hcbQuarter hCv hr hF hc0
      hcone hconeK (by norm_num) (by dsimp only [aDensity]; positivity) hp0 hdecay
      (le_refl _) hD hsep hJ
  let L0 := max Lbase (max (num.modelUnitCost H CD CS CT) (num.modelUnitCost H LD LS LT))
  have haDensity : 0≤aDensity := by dsimp only [aDensity]; positivity
  refine ⟨A,L0,by linarith,hbase.trans (le_max_left _ _),?_⟩
  intro L hL N κ Label Item _ _ P S w hw hW horder hDorder hscale hratioBound hprofile
    hshort hfrequencyLo hfrequency hlocal hunitRange spectrum bin alt hAlt altSpectrum altBin
    b hb hb1 haway hradius hLip field hfield f g hfm hgm hfb hgb E Fset hE hFset hEfin hFfin
    hFpos hfs hgs l r ratio widthScale hstrip hEstrip hFstrip hratio hloglo hloghi hratioEq
    hwidthLo hwidthHi hwidthEq
  classical
  have hLb : Lbase≤L := (le_max_left _ _).trans hL
  have hL16 : 16≤L := hbase.trans hLb
  have hhigh : num.modelUnitCost H CD CS CT≤L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hlow : num.modelUnitCost H LD LS LT≤L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  obtain ⟨tag,cell,hcover⟩ := P.exists_angular_assignment w cStar cEta cb radius
    hw hcStar hcEta hcb.le hr hcoverSmall
  let d := fun gamma => angularModelConfig P S cStar cEta CEta cb Cv w F radius H
    hcStar hcEta hCEta hCv hcb hcbQuarter hsmall num hw hW hF hr horder hfrequency hlocal
    tag cell hcover spectrum bin b hb hb1 haway hradius (fun j l k s t _ => hLip j l k s t) gamma
  obtain ⟨grid,hbranch,hroot,hzero⟩ := exists_source_full_angular_grid L (by linarith : 1≤L)
    (fun j => w/P.length j) (fun j => (div_pos hw (P.length_pos j)).le)
  let V := fun (gamma : DyadicLineGrid.GridChoice) (z : ℝ×ℝ) =>
    ∑ a∈P.angularPackets S tag gamma, P.crossPacketValue alt hAlt 0
      (P.angularSelector tag gamma b) (fun z => field (planeCoordinates z)) f z a
  have hpiece (gamma : DyadicLineGrid.GridChoice) :
      Integrable (fun z => inner ℂ (V gamma z) (g z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (V gamma z) (g z) ∂volume.prod volume‖≤
        2*L^(-decay)*ratio*(volume.prod volume).real Fset := by
    by_cases hne : (P.angularPackets S tag gamma).Nonempty
    · have hcost (X Y Z : ℝ) : (d gamma).unitModelCost X Y Z=num.modelUnitCost H X Y Z :=
        OrdinaryModelConfig.unitModelCost_of_numeric_fields (d gamma) cStar cEta cb radius num H
          X Y Z rfl rfl rfl rfl rfl rfl rfl rfl rfl
      have htag (j : Fin N) (a : P.labels j) (k : κ) (s : ℝ)
          (hn : P.angularSelector tag gamma b j a k s≠0) : tag j a=gamma ∧ b j a k s≠0 := by
        by_cases ht : tag j a=gamma
        · exact ⟨ht,by simpa [angularSelector,ht] using hn⟩
        · simp [angularSelector,ht] at hn
      have hcell (a : P.PacketIndex) (ha : a∈P.angularPackets S tag gamma) :
          P.rowSlope a.1 a.2.1 ∈ scaledAngularCell (w/P.topLength) gamma.val a.1.val (cell a.1 a.2.1) := by
        have ht := (Finset.mem_filter.mp ha).2
        have hs := (hcover a.1 a.2.1).1 (P.rowSlope a.1 a.2.1) (by
          simpa only [sub_self,abs_zero] using mul_nonneg hr (div_pos hw (P.length_pos a.1)).le)
        simpa only [ht] using hs
      have hcellrange (a : P.PacketIndex) (ha : a∈P.angularPackets S tag gamma) :
          scaledAngularCell (w/P.topLength) gamma.val a.1.val (cell a.1 a.2.1) ⊆ Icc (-1) 1 := by
        apply PacketRepresentation.angular_cell_subset_unit _ (div_pos hw P.topLength_pos)
          gamma.val a.1.val (cell a.1 a.2.1) (P.rowSlope a.1 a.2.1) (hcell a ha)
        rw [← P.precision_eq_scaled_grid w a.1]
        exact hunitRange a.1 a.2.1
      have hmargin (a : P.PacketIndex) (ha : a∈P.angularPackets S tag gamma)
          (k : κ) (xi et : ℝ)
          (hs : planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 a.1 a.2.1 a.2.2 k) (xi,et)≠0) :
          Icc (-xi/et-(d gamma).margin*((d gamma).w/P.length a.1))
            (-xi/et+(d gamma).margin*((d gamma).w/P.length a.1))⊆
            scaledAngularCell ((d gamma).w/P.topLength) (d gamma).grid a.1.val
              ((d gamma).cell a.1 a.2.1) := by
        have ht := (Finset.mem_filter.mp ha).2
        have sp := altSpectrum a.1 a.2.1 a.2.2 k xi et hs
        change Icc (-xi/et-cb*(w/P.length a.1)) (-xi/et+cb*(w/P.length a.1))⊆
          scaledAngularCell (w/P.topLength) gamma.val a.1.val (cell a.1 a.2.1)
        simpa only [ht] using (hcover a.1 a.2.1).2 xi et sp.2.1 sp.1
      have hmeas (j : Fin N) (a : P.labels j) (k : κ) :
          Measurable (P.angularSelector tag gamma b j a k) := by
        change Measurable (fun s => if tag j a=gamma then b j a k s else 0)
        by_cases ht : tag j a=gamma
        · simpa [ht] using hb j a k
        · simp [ht]
      have hbound (j : Fin N) (a : P.labels j) (k : κ) (s : ℝ) :
          ‖P.angularSelector tag gamma b j a k s‖≤1 := by
        by_cases ht : tag j a=gamma
        · simpa [angularSelector,ht] using hb1 j a k s
        · simp [angularSelector,ht]
      have hsupp (j : Fin N) (a : P.labels j) (k : κ) (s : ℝ)
          (hn : P.angularSelector tag gamma b j a k s≠0) :
          |s-(0+P.rowSlope j a)| ≤ cone*(w/P.length j) := by
        simpa only [zero_add] using (hradius j a k s (htag j a k s hn).2).trans
          (mul_le_mul_of_nonneg_right hrcone (div_pos hw (P.length_pos j)).le)
      have hlip (j : Fin N) (a : P.labels j) (k : κ) (s t : ℝ) :
          ‖P.angularSelector tag gamma b j a k s-P.angularSelector tag gamma b j a k t‖≤
            1*(|s-t|/(w/P.length j)) := by
        by_cases ht : tag j a=gamma
        · simpa [angularSelector,ht,one_mul] using hLip j a k s t
        · simp only [angularSelector,ht,ite_false, if_false,sub_self,norm_zero,one_mul]
          exact div_nonneg (abs_nonneg _) (div_pos hw (P.length_pos j)).le
      have hactive (j : Fin N) (a : P.labels j) (k : κ) (s : ℝ)
          (hn : P.angularSelector tag gamma b j a k s≠0) :
          cb*w/P.length j≤|s-(0+P.rowSlope j a)| ∧
            |s-(0+P.rowSlope j a)| ≤ radius*w/P.length j := by
        constructor
        · simpa only [zero_add,abs_sub_comm] using haway j a k s (htag j a k s hn).2
        · simpa only [zero_add,mul_div_assoc] using hradius j a k s (htag j a k s hn).2
      exact hmain L hLb κ N Label Item P (P.angularPackets S tag gamma) w P.topLength hw
        hscale hratioBound hprofile hDorder hne (d gamma) rfl rfl rfl rfl rfl rfl rfl
        (by rw [hcost]; exact hhigh) (by rw [hcost]; exact hlow)
        E Fset field cell gamma.val rfl rfl hE hEfin
        (by simpa only [zero_add] using hcell) hcellrange l r hfield hstrip hEstrip hFstrip
        hFset hFfin hFpos ratio widthScale hratio hloglo hloghi hratioEq
        hwidthLo hwidthHi hwidthEq P.topLength_pos.le hshort alt hAlt hmargin
        (fun a _ k xi et hs => altBin a.1 a.2.1 a.2.2 k xi et hs)
        (P.angularSelector tag gamma b) rfl hmeas hbound hsupp hlip hactive
        (by simpa only [zero_add] using hlocal) hfrequencyLo hfrequency
        (by simpa only [zero_add] using spectrum) (by simpa only [zero_add] using altSpectrum)
        f hfm hfb hfs grid hbranch hzero hroot g hgm hgb hgs
    · have he : P.angularPackets S tag gamma=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [V,he,Finset.sum_empty,inner_zero_left,integral_zero,norm_zero]
      exact ⟨integrable_zero _ _ _, by positivity⟩
  have heq (z : ℝ×ℝ) : (∑ gamma, inner ℂ (V gamma z) (g z))=
      inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b
        (fun z => field (planeCoordinates z)) f z a) (g z) := by
    rw [←sum_inner]
    exact congrArg (fun x => inner ℂ x (g z))
      (P.sum_crossPacketValue_angularPartition alt hAlt S tag b 0
        (fun z => field (planeCoordinates z)) f z)
  refine ⟨(integrable_finsetSum _ (fun gamma _ => (hpiece gamma).1)).congr
    (Filter.Eventually.of_forall heq),?_⟩
  rw [←integral_congr_ae (Filter.Eventually.of_forall heq),
    integral_finsetSum _ (fun gamma _ => (hpiece gamma).1)]
  calc
    _ ≤ ∑ gamma : DyadicLineGrid.GridChoice,
        ‖∫ z, inner ℂ (V gamma z) (g z) ∂volume.prod volume‖ := norm_sum_le _ _
    _ ≤ ∑ _gamma : DyadicLineGrid.GridChoice, 2*L^(-decay)*ratio*(volume.prod volume).real Fset :=
      Finset.sum_le_sum (fun gamma _ => (hpiece gamma).2)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,DyadicLineGrid.gridChoice_card,nsmul_eq_mul,
        Nat.cast_ofNat]
      ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketLatticeData.exists_angular_high_pairing_oai := @OAI.LipschitzHilbert.PacketLatticeData.exists_angular_high_pairing_oai
