-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketRepresentation.dyadic_smooth_product_embedding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:03:53.484455+00:00
-- url     : https://prove2.me/submissions/b9db115d-ad95-48ce-a459-8e0df4385064

import Mathlib
import Definitions.Def_OAIQ090A000
import Definitions.Def_OAIQ090A001

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FiniteCarlesonPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite laminar Carleson family packs on the union of every selected
subfamily. Repeated occurrences are allowed; maximal geometric sets are
counted only once. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace LipschitzHilbert

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

theorem finite_laminar_carleson_packing (Q : ι → Set X) (mu : Measure X)
    (hQ : ∀ i, MeasurableSet (Q i))
    (hlam : ∀ i j, Q i⊆Q j ∨ Q j⊆Q i ∨ Disjoint (Q i) (Q j))
    (a : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (hcar : ∀ j, (∑ i, if Q i⊆Q j then a i else 0)≤C*mu (Q j))
    (I : Finset ι) :
    (∑ i∈I, a i)≤C*mu (⋃ i∈I, Q i) := by
  classical
  let F : Finset (Set X) := I.image Q
  let R := F.filter (fun A => Maximal (fun B => B∈F) A)
  have hcover (i : ι) (hi : i∈I) : ∃ A∈R, Q i⊆A := by
    obtain ⟨A,hiA,hmax⟩ := F.exists_le_maximal (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    exact ⟨A,Finset.mem_filter.mpr ⟨hmax.1,hmax⟩,hiA⟩
  have hrepr {A : Set X} (hA : A∈R) : ∃ i∈I, Q i=A :=
    Finset.mem_image.mp (Finset.mem_filter.mp hA).1
  have hdisj : (↑R : Set (Set X)).PairwiseDisjoint id := by
    intro A hA B hB hne
    obtain ⟨i,hi,rfl⟩ := hrepr hA
    obtain ⟨j,hj,rfl⟩ := hrepr hB
    rcases hlam i j with hij | hji | hd
    · have he : Q i=Q j := subset_antisymm hij ((Finset.mem_filter.mp hA).2.2
        (Finset.mem_filter.mp hB).1 hij)
      exact (hne he).elim
    · have he : Q i=Q j := subset_antisymm ((Finset.mem_filter.mp hB).2.2
        (Finset.mem_filter.mp hA).1 hji) hji
      exact (hne he).elim
    · exact hd
  have hmeas (A : Set X) (hA : A∈R) : MeasurableSet A := by
    obtain ⟨i,_,rfl⟩ := hrepr hA
    exact hQ i
  have hunion : (⋃ A∈R, A)=(⋃ i∈I, Q i) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨A,hA,hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨i,hi,rfl⟩ := hrepr hA
      exact mem_iUnion₂.mpr ⟨i,hi,hx⟩
    · intro x hx
      obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨A,hA,hisub⟩ := hcover i hi
      exact mem_iUnion₂.mpr ⟨A,hA,hisub hx⟩
  calc
    _ ≤ ∑ i∈I, ∑ A∈R, if Q i⊆A then a i else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨A,hA,hisub⟩ := hcover i hi
      calc
        a i = if Q i⊆A then a i else 0 := (ite_eq_left hisub).symm
        _ ≤ _ := Finset.single_le_sum (a:=A) (f:=fun B : Set X => if Q i⊆B then a i else 0) (fun _ _ => zero_le) hA
    _ = ∑ A∈R, ∑ i∈I, if Q i⊆A then a i else 0 := Finset.sum_comm
    _ ≤ ∑ A∈R, ∑ i, if Q i⊆A then a i else 0 := by
      apply Finset.sum_le_sum
      intro A _
      exact Finset.sum_le_univ_sum_of_nonneg (fun _ => zero_le)
    _ ≤ ∑ A∈R, C*mu A := by
      apply Finset.sum_le_sum
      intro A hA
      obtain ⟨i,_,rfl⟩ := hrepr hA
      exact hcar i
    _ = C*mu (⋃ i∈I, Q i) := by
      have hm : mu (⋃ A∈R, A)=∑ A∈R, mu A := by
        simpa only [id_eq] using (measure_biUnion_finset (μ:=mu) hdisj hmeas)
      rw [←Finset.mul_sum,←hm,hunion]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteCarlesonEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Carleson embedding for a finite laminar family. The proof
uses maximal selected sets and the layer-cake formula. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace LipschitzHilbert
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]
attribute [local instance] Classical.propDecidable

theorem finite_carleson_embedding_ae (Q : ι → Set X) (mu : Measure X)
    (hQ : ∀ i, MeasurableSet (Q i))
    (hlam : ∀ i j, Q i⊆Q j ∨ Q j⊆Q i ∨ Disjoint (Q i) (Q j))
    (a : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (hcar : ∀ j, (∑ i, if Q i⊆Q j then a i else 0)≤C*mu (Q j))
    (v : ι → ℝ) (hv : ∀ i, 0≤v i) (g : X → ℝ)
    (hg : Measurable g) (hgnonneg : ∀ x, 0≤g x)
    (hvg : ∀ i, ∀ᵐ x ∂mu.restrict (Q i), v i≤g x) :
    (∑ i, a i*ENNReal.ofReal (v i))≤C*∫⁻ x, ENNReal.ofReal (g x) ∂mu := by
  classical
  let : MeasurableSpace ι := ⊤
  let nu : Measure ι := ∑ i, a i • Measure.dirac i
  have hnu (S : Set ι) : nu S=∑ i, if i∈S then a i else 0 := by
    simp [nu,Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply',Set.indicator_apply,mul_ite]
  have hnu_integral : (∫⁻ i, ENNReal.ofReal (v i) ∂nu)=∑ i, a i*ENNReal.ofReal (v i) := by
    simp [nu,lintegral_finsetSum_measure,lintegral_smul_measure,lintegral_dirac]
  have hvmeas : Measurable v := measurable_of_countable v
  rw [←hnu_integral,lintegral_eq_lintegral_meas_lt nu
    (Filter.Eventually.of_forall hv) hvmeas.aemeasurable,
    lintegral_eq_lintegral_meas_lt mu (Filter.Eventually.of_forall hgnonneg) hg.aemeasurable]
  have htail : Measurable (fun t : ℝ => mu {x | t<g x}) := by
    apply Antitone.measurable
    intro a b hab
    exact measure_mono (fun x hx => lt_of_le_of_lt hab hx)
  rw [←lintegral_const_mul C htail]
  apply lintegral_mono
  intro t
  change nu {i | t<v i}≤C*mu {x | t<g x}
  rw [hnu]
  let I : Finset ι := Finset.univ.filter (fun i => t<v i)
  have he : (∑ i, if i∈{i | t<v i} then a i else 0)=∑ i∈I, a i := by
    simp only [I,Finset.sum_filter,mem_ofPred_eq]
  rw [he]
  apply (finite_laminar_carleson_packing Q mu hQ hlam a C hcar I).trans
  apply mul_le_mul' le_rfl
  apply measure_mono_ae
  have hgood : ∀ᵐ x ∂mu, ∀ i, x∈Q i → v i≤g x :=
    ae_all_iff.mpr (fun i => (ae_restrict_iff' (hQ i)).mp (hvg i))
  filter_upwards [hgood] with x hx hmem
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hmem
  exact lt_of_lt_of_le (Finset.mem_filter.mp hi).2 (hx i hxi)


end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CarlesonProductEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Carleson embedding applied to actual local product energies.
A common maximal-function majorant controls all low-frequency factors. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace LipschitzHilbert
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]
attribute [local instance] Classical.propDecidable

theorem carleson_product_energy_ae (Q : ι → Set X) (mu : Measure X)
    (hQ : ∀ i, MeasurableSet (Q i))
    (hlam : ∀ i j, Q i⊆Q j ∨ Q j⊆Q i ∨ Disjoint (Q i) (Q j))
    (w : ι → X → ℝ≥0∞) (C : ℝ≥0∞)
    (hcar : ∀ j, (∑ i, if Q i⊆Q j then ∫⁻ x in Q i, w i x ∂mu else 0)≤C*mu (Q j))
    (h : ι → X → ℂ) (v : ι → ℝ) (hv : ∀ i, 0≤v i)
    (G : X → ℝ) (hG : Measurable G)
    (hh : ∀ i, ∀ x∈Q i, ‖h i x‖≤v i)
    (hvG : ∀ i, ∀ᵐ x ∂mu.restrict (Q i), v i≤G x) :
    (∑ i, ∫⁻ x in Q i, w i x*ENNReal.ofReal (‖h i x‖^2) ∂mu)≤
      C*∫⁻ x, ENNReal.ofReal (G x^2) ∂mu := by
  calc
    _ ≤ ∑ i, (∫⁻ x in Q i, w i x ∂mu)*ENNReal.ofReal (v i^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [←lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hQ i)] with x hx
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg _) (hh i x hx) 2))
    _ ≤ _ := finite_carleson_embedding_ae Q mu hQ hlam
      (fun i => ∫⁻ x in Q i, w i x ∂mu) C hcar (fun i => v i^2)
      (fun _ => sq_nonneg _) (fun x => G x^2) (hG.pow_const 2)
      (fun _ => sq_nonneg _) (fun i => (hvG i).mono (fun _ hx => pow_le_pow_left₀ (hv i) hx 2))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_DyadicLineGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nested alternating one-third grids in the line-counting argument. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

theorem cell_length (q k j : ℤ) : MeasureTheory.volume.real (cell q k j) = scale k := by
  rw [cell, Real.volume_real_Ico_of_le]
  · unfold left
    push_cast
    ring
  · unfold left
    have hs := scale_pos k
    push_cast
    nlinarith

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineNesting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary-depth nesting and uniqueness in the alternating line grids. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

theorem cells_nested_or_disjoint (q k l i j : ℤ) :
    cell q k i ⊆ cell q l j ∨ cell q l j ⊆ cell q k i ∨
      Disjoint (cell q k i) (cell q l j) := by
  by_cases h : (cell q k i ∩ cell q l j).Nonempty
  · rcases le_total k l with hkl | hlk
    · exact Or.inl (cell_subset_of_intersect hkl h)
    · exact Or.inr (Or.inl (cell_subset_of_intersect hlk (by simpa only [inter_comm] using h)))
  · exact Or.inr (Or.inr (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h)))

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GeometricScaleWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform row and column bounds for the actual geometric scale kernel. -/

open scoped BigOperators

noncomputable section

namespace LipschitzHilbert

theorem sum_half_powers_le_two (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) ≤ 2 := by
  have heq : (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) =
      2 * (1 - (1 / 2 : ℝ) ^ N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [heq]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteTimeKernelMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first absolute moment of the retained time kernel is bounded
by twice the largest scale, independently of the number of scales. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem schwartz_first_absolute_moment_integrable (k : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => |t| *‖k t‖) := by
  simpa only [pow_one,Real.norm_eq_abs] using k.integrable_pow_mul volume 1

theorem scaledTimeKernel_moment1_pointwise (k : ℝ → ℂ) (l t : ℝ) (hl : 0<l) :
    |t| *‖scaledTimeKernel k l t‖=|t/l| *‖k (t/l)‖ := by
  simp only [scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg hl.le,abs_div,abs_of_pos hl]
  ring

theorem scaledTimeKernel_moment1 (k : SchwartzMap ℝ ℂ) (l : ℝ) (hl : 0<l) :
    (∫ t, |t| *‖scaledTimeKernel k l t‖)=l*(∫ t, |t| *‖k t‖) := by
  simp_rw [scaledTimeKernel_moment1_pointwise k l _ hl]
  rw [Measure.integral_comp_div (fun t => |t| *‖k t‖) l,abs_of_pos hl,smul_eq_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularCutoffConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit real annular cutoffs and the low-pass difference underlying
the geometric frequency partition. All supports stay inside fixed bands. -/
noncomputable section
open MeasureTheory Function Set
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyLow_one (s : ℝ) (hs : |s|≤1) : reassemblyLow s=1 := by
  have hd : s∈Metric.closedBall (0:ℝ) reassemblyLowBump.rIn := by
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,reassemblyLowBump] using hs
  simp only [reassemblyLow_apply,reassemblyLowBump.one_of_mem_closedBall hd,Complex.ofReal_one]

theorem reassemblyLow_zero (s : ℝ) (hs : 13/12≤|s|) : reassemblyLow s=0 := by
  have hd : reassemblyLowBump.rOut≤dist s 0 := by
    simpa only [Real.dist_eq,sub_zero,reassemblyLowBump] using hs
  simp only [reassemblyLow_apply,reassemblyLowBump.zero_of_le_dist hd,Complex.ofReal_zero]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_AnnularSquareBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric annular cutoffs have a uniform finite square sum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyLow_norm (s : ℝ) : ‖reassemblyLow s‖≤1 := by
  rw [reassemblyLow_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg reassemblyLowBump.nonneg]
  exact reassemblyLowBump.le_one

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicSmoothCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine binary low-pass difference for the dyadic commutator
proof, with its scale-independent Fourier square bound. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicDifference_small (x : ℝ) (hx : |x|≤1) : dyadicDifference x=0 := by
  have hh : |x/2|≤1 := by rw [abs_div]; norm_num; linarith
  simp only [dyadicDifference_apply,reassemblyLow_one x hx,reassemblyLow_one _ hh,sub_self]

theorem dyadicDifference_large (x : ℝ) (hx : 13/6≤|x|) : dyadicDifference x=0 := by
  have hh : 13/12≤|x/2| := by rw [abs_div]; norm_num; linarith
  simp only [dyadicDifference_apply,reassemblyLow_zero x (by linarith),
    reassemblyLow_zero _ hh,sub_self]

theorem dyadicDifference_norm (x : ℝ) : ‖dyadicDifference x‖≤2 := by
  rw [dyadicDifference_apply]
  exact (norm_sub_le _ _).trans (by linarith [reassemblyLow_norm (x/2),reassemblyLow_norm x])

theorem dyadicDifference_separated (j k : ℤ) (x : ℝ) (hjk : j+2≤k) :
    dyadicDifference ((2:ℝ)^j*x)=0 ∨ dyadicDifference ((2:ℝ)^k*x)=0 := by
  by_contra hn
  have hj : dyadicDifference ((2:ℝ)^j*x)≠0 := fun h => hn (Or.inl h)
  have hk : dyadicDifference ((2:ℝ)^k*x)≠0 := fun h => hn (Or.inr h)
  have hjlo : 1 < |(2:ℝ)^j*x| := lt_of_not_ge (fun h => hj (dyadicDifference_small _ h))
  have hkhi : |(2:ℝ)^k*x|<13/6 := lt_of_not_ge (fun h => hk (dyadicDifference_large _ h))
  have hp : (2:ℝ)^j*4≤(2:ℝ)^k := by
    calc
      _ = (2:ℝ)^(j+2) := by rw [zpow_add₀ (by norm_num)]; norm_num
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) hjk
  have hm := mul_le_mul_of_nonneg_right hp (abs_nonneg x)
  have ha (n : ℤ) : |(2:ℝ)^n*x|=(2:ℝ)^n*|x| := by
    rw [abs_mul,abs_of_pos (zpow_pos (by norm_num) _)]
  rw [ha j] at hjlo
  rw [ha k] at hkhi
  nlinarith only [hm,hjlo,hkhi]

theorem dyadicDifference_nonzero_count (I : Finset ℤ) (x : ℝ) :
    (I.filter (fun n => dyadicDifference ((2:ℝ)^n*x)≠0)).card≤3 := by
  classical
  let A := I.filter (fun n => dyadicDifference ((2:ℝ)^n*x)≠0)
  change A.card≤3
  by_cases hne : A.Nonempty
  · obtain ⟨j,hj⟩ := hne
    have hjnz := (Finset.mem_filter.mp hj).2
    have hsub : A⊆Finset.Icc (j-1) (j+1) := by
      intro k hk
      have hknz := (Finset.mem_filter.mp hk).2
      apply Finset.mem_Icc.mpr
      constructor
      · by_contra hn
        exact (dyadicDifference_separated k j x (by omega)).elim hknz hjnz
      · by_contra hn
        exact (dyadicDifference_separated j k x (by omega)).elim hjnz hknz
    apply (Finset.card_le_card hsub).trans
    rw [Int.card_Icc]
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega

theorem dyadicDifference_square_sum (I : Finset ℤ) (x : ℝ) :
    (∑ n∈I, ‖dyadicDifference ((2:ℝ)^n*x)‖^2)≤12 := by
  classical
  let A := I.filter (fun n => dyadicDifference ((2:ℝ)^n*x)≠0)
  have he : (∑ n∈I, ‖dyadicDifference ((2:ℝ)^n*x)‖^2)=
      ∑ n∈A, ‖dyadicDifference ((2:ℝ)^n*x)‖^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnA
    have hz : dyadicDifference ((2:ℝ)^n*x)=0 := by
      by_contra h
      exact hnA (Finset.mem_filter.mpr ⟨hn,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  rw [he]
  calc
    _ ≤ ∑ _n∈A, (4:ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [show (2:ℝ)^2=4 by norm_num] using
        pow_le_pow_left₀ (norm_nonneg _) (dyadicDifference_norm ((2:ℝ)^n*x)) 2
    _ = (A.card:ℝ)*4 := by simp
    _ ≤ 12 := by
      have hc : (A.card:ℝ)≤3 := by exact_mod_cast dyadicDifference_nonzero_count I x
      linarith

theorem dyadicDifference_inverse_square_sum (I : Finset ℕ) (d eta : ℝ) :
    (∑ n∈I, ‖dyadicDifference ((d/(2:ℝ)^n)*eta)‖^2)≤12 := by
  classical
  have h := dyadicDifference_square_sum (I.image (fun n : ℕ => -(n:ℤ))) (d*eta)
  rw [Finset.sum_image] at h
  · convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro n _
    rw [zpow_neg,zpow_natCast]
    have he : d/(2:ℝ)^n*eta=((2:ℝ)^n)⁻¹*(d*eta) := by ring
    rw [he]
  · intro n _ m _ hnm
    exact_mod_cast (neg_injective hnm)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceL2Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact L2 Gram identities for the finite physical packet sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem memLp_inner_integral (mu : Measure X) (f g : X → E)
    (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    inner ℂ (hf.toLp f) (hg.toLp g)=∫ x, inner ℂ (f x) (g x) ∂mu := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hfx hgx
  rw [hfx,hgx]

theorem memLp_toL2_norm_sq (mu : Measure X) (f : X → E) (hf : MemLp f 2 mu) :
    ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂mu := by
  have h := memLp_inner_integral mu f f hf hf
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  change ((‖hf.toLp f‖^2 : ℝ) : ℂ)=(∫ x, ((‖f x‖^2 : ℝ) : ℂ) ∂mu) at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineFrequencyProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth frequency projections on the line and their finite
square-function bound. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_fourier (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (f : SchwartzMap ℝ ℂ) (eta : ℝ) :
    (𝓕 (lineSchwartzProjection q W hW f)) eta=q (W*eta)*(𝓕 f) eta := by
  simp only [lineSchwartzProjection,FourierTransform.fourier_fourierInv_eq]
  rw [SchwartzMap.smulLeftCLM_apply_apply (dilatedSlopeWindow q W hW).hasTemperateGrowth,
    dilatedSlopeWindow_apply,smul_eq_mul]

theorem lineSchwartzProjection_energy (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (M : ℝ) (hM : ∀ eta, ‖q eta‖≤M) (f : SchwartzMap ℝ ℂ) :
    (∫ x, ‖lineSchwartzProjection q W hW f x‖^2)≤M^2*∫ x, ‖f x‖^2 := by
  rw [←SchwartzMap.integral_norm_sq_fourier (lineSchwartzProjection q W hW f),
    ←SchwartzMap.integral_norm_sq_fourier f,←integral_const_mul]
  apply integral_mono
  · exact ((𝓕 (lineSchwartzProjection q W hW f) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  · exact (((𝓕 f : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)).const_mul _
  · intro x
    change ‖(𝓕 (lineSchwartzProjection q W hW f)) x‖^2≤M^2*‖(𝓕 f) x‖^2
    rw [lineSchwartzProjection_fourier,norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM (W*x)) 2) (sq_nonneg _)

theorem lineSchwartzProjection_frame {ι : Type*} (I : Finset ι)
    (q : ι → SchwartzMap ℝ ℂ) (W : ι → ℝ) (hW : ∀ i, W i≠0)
    (M : ℝ) (hM : ∀ eta, (∑ i∈I, ‖q i (W i*eta)‖^2)≤M)
    (f : SchwartzMap ℝ ℂ) :
    (∑ i∈I, ∫ x, ‖lineSchwartzProjection (q i) (W i) (hW i) f x‖^2)≤
      M*∫ x, ‖f x‖^2 := by
  have hi (i : ι) : Integrable (fun eta =>
      ‖(𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f)) eta‖^2) :=
    ((𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  have hf : Integrable (fun eta => ‖(𝓕 f) eta‖^2) :=
    ((𝓕 f : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  calc
    _ = ∑ i∈I, ∫ eta, ‖(𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f)) eta‖^2 :=
      Finset.sum_congr rfl (fun i _ => (SchwartzMap.integral_norm_sq_fourier _).symm)
    _ = ∫ eta, ∑ i∈I, ‖(𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f)) eta‖^2 :=
      (integral_finsetSum I (fun i _ => hi i)).symm
    _ ≤ M*∫ eta, ‖(𝓕 f) eta‖^2 := by
      rw [←integral_const_mul]
      apply integral_mono (integrable_finsetSum I (fun i _ => hi i)) (hf.const_mul M)
      intro eta
      change (∑ i∈I, ‖(𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f)) eta‖^2)≤_
      simp only [lineSchwartzProjection_fourier,norm_mul,mul_pow]
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hM eta) (sq_nonneg _)
    _ = _ := by rw [SchwartzMap.integral_norm_sq_fourier]

theorem lineProjectionToL2_bound (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (M : ℝ) (hM : 0≤M) (hq : ∀ eta, ‖q eta‖≤M) (f : SchwartzMap ℝ ℂ) :
    ‖lineProjectionToL2 q W hW f‖≤M*‖f.toLp 2 volume‖ := by
  have h := lineSchwartzProjection_energy q W hW M hq f
  have ho := memLp_toL2_norm_sq volume _ ((lineSchwartzProjection q W hW f).memLp 2 volume)
  have hf := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  change ‖lineProjectionToL2 q W hW f‖^2=_ at ho
  change ‖f.toLp 2 volume‖^2=_ at hf
  rw [←ho,←hf] at h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).1 (by simpa only [mul_pow] using h)

theorem lineL2Projection_onSchwartz (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (f : SchwartzMap ℝ ℂ) :
    lineL2Projection q W hW (f.toLp 2 volume)=(lineSchwartzProjection q W hW f).toLp 2 volume := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · refine ⟨SchwartzMap.seminorm ℝ 0 0 q,?_⟩
    exact lineProjectionToL2_bound q W hW _ (apply_nonneg _ _)
      (fun eta => SchwartzMap.norm_le_seminorm ℝ q eta)

theorem lineL2Projection_bound (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (M : ℝ) (hM : 0≤M) (hq : ∀ eta, ‖q eta‖≤M) :
    ‖lineL2Projection q W hW‖≤M := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact hM
  · exact lineProjectionToL2_bound q W hW M hM hq

theorem lineL2Projection_frame {ι : Type*} (I : Finset ι)
    (q : ι → SchwartzMap ℝ ℂ) (W : ι → ℝ) (hW : ∀ i, W i≠0)
    (M : ℝ) (hM : ∀ eta, (∑ i∈I, ‖q i (W i*eta)‖^2)≤M)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (∑ i∈I, ‖lineL2Projection (q i) (W i) (hW i) f‖^2)≤M*‖f‖^2 := by
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on f (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro g
  have h := lineSchwartzProjection_frame I q W hW M hM g
  have heq (i : ι) : ‖lineL2Projection (q i) (W i) (hW i) (g.toLp 2 volume)‖^2=
      ∫ x, ‖lineSchwartzProjection (q i) (W i) (hW i) g x‖^2 := by
    rw [lineL2Projection_onSchwartz]
    exact memLp_toL2_norm_sq volume _ ((lineSchwartzProjection (q i) (W i) (hW i) g).memLp 2 volume)
  have hg : ‖g.toLp 2 volume‖^2=∫ x, ‖g x‖^2 :=
    memLp_toL2_norm_sq volume _ (g.memLp 2 volume)
  simpa only [heq,hg] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineProjectionKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The line Fourier projection is the actual convolution with its
inverse-Fourier kernel. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_eq_convolution (q : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    lineSchwartzProjection q W hW f x=lineConvolution (lineProjectionKernel q W hW) f x := by
  have he : lineSchwartzProjection q W hW f=
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (lineProjectionKernel q W hW) f := by
    apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
    ext eta
    change (𝓕 (lineSchwartzProjection q W hW f)) eta=
      (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (lineProjectionKernel q W hW) f)) eta
    rw [lineSchwartzProjection_fourier,SchwartzMap.fourier_convolution]
    simp only [SchwartzMap.pairing_apply_apply,lineProjectionKernel,
      FourierTransform.fourier_fourierInv_eq,dilatedSlopeWindow_apply,ContinuousLinearMap.mul_apply']
  rw [he,SchwartzMap.convolution_apply,convolution_def]
  rfl

theorem lineConvolution_sub_of_bounded (K f g : ℝ → ℂ)
    (hK : Integrable K) (hfm : Measurable f) (hgm : Measurable g)
    (Bf Bg : ℝ) (hf : ∀ x, ‖f x‖≤Bf) (hg : ∀ x, ‖g x‖≤Bg) :
    lineConvolution K (f-g)=lineConvolution K f-lineConvolution K g := by
  funext x
  unfold lineConvolution
  simp only [Pi.sub_apply,mul_sub]
  exact integral_sub (lineConvolution_integrand_of_bounded K f hK hfm Bf hf x)
    (lineConvolution_integrand_of_bounded K g hK hgm Bg hg x)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConvolutionContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual convolution on bounded L2 functions agrees with the continuous
extension of the corresponding Schwartz Fourier multiplier. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_L2_difference (K f g : ℝ → ℂ)
    (hK : Integrable K) (hKm : Measurable K) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hcf : MemLp (lineConvolution K f) 2 volume) (hcg : MemLp (lineConvolution K g) 2 volume)
    (Bf Bg : ℝ) (hfb : ∀ x, ‖f x‖≤Bf) (hgb : ∀ x, ‖g x‖≤Bg) :
    ‖hcf.toLp (lineConvolution K f)-hcg.toLp (lineConvolution K g)‖≤
      (∫ t, ‖K t‖)*‖hf.toLp f-hg.toLp g‖ := by
  have he := (lineConvolution_energy_bound K hK hKm (f-g) (hfm.sub hgm) (hf.sub hg)).2
  rw [lineConvolution_sub_of_bounded K f g hK hfm hgm Bf Bg hfb hgb] at he
  have ho := memLp_toL2_norm_sq volume _ (hcf.sub hcg)
  have hi := memLp_toL2_norm_sq volume _ (hf.sub hg)
  rw [hcf.toLp_sub hcg] at ho
  rw [hf.toLp_sub hg] at hi
  rw [←ho,←hi] at he
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg _))).1
    (by simpa only [mul_pow] using he)

theorem lineL2Projection_on_bounded (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume)
    (B : ℝ) (hB : ∀ x, ‖f x‖≤B) :
    lineL2Projection q W hW (hf.toLp f)=
      (lineConvolution_energy_bound (lineProjectionKernel q W hW)
        (lineProjectionKernel q W hW).integrable (lineProjectionKernel q W hW).continuous.measurable
        f hfm hf).1.toLp (lineConvolution (lineProjectionKernel q W hW) f) := by
  let K := lineProjectionKernel q W hW
  let C := SchwartzMap.seminorm ℝ 0 0 q
  let L := ∫ t, ‖K t‖
  let T := lineL2Projection q W hW
  let y := (lineConvolution_energy_bound K K.integrable K.continuous.measurable f hfm hf).1.toLp
    (lineConvolution K f)
  change T (hf.toLp f)=y
  have hC : 0≤C := apply_nonneg _ _
  have hL : 0≤L := integral_nonneg fun _ => norm_nonneg _
  have hT : ‖T‖≤C := lineL2Projection_bound q W hW C hC (fun x => SchwartzMap.norm_le_seminorm ℝ q x)
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  by_contra hn
  have hdpos : 0<‖T (hf.toLp f)-y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  let eps := ‖T (hf.toLp f)-y‖/(2*(C+L+1))
  have heps : 0<eps := div_pos hdpos (by positivity)
  obtain ⟨g,hg⟩ := hd.exists_dist_lt (hf.toLp f) heps
  let yg := (lineConvolution_energy_bound K K.integrable K.continuous.measurable
    g g.continuous.measurable (g.memLp 2 volume)).1.toLp (lineConvolution K g)
  have hTg : T (g.toLp 2 volume)=yg := by
    change lineL2Projection q W hW (g.toLp 2 volume)=_
    rw [lineL2Projection_onSchwartz]
    apply Lp.ext
    filter_upwards [(lineSchwartzProjection q W hW g).coeFn_toLp 2 volume,
      (lineConvolution_energy_bound K K.integrable K.continuous.measurable
        g g.continuous.measurable (g.memLp 2 volume)).1.coeFn_toLp] with x hx hy
    dsimp only [yg]
    rw [hx,hy]
    exact lineSchwartzProjection_eq_convolution q W hW g x
  have hc : ‖yg-y‖≤L*‖g.toLp 2 volume-hf.toLp f‖ :=
    lineConvolution_L2_difference K g f K.integrable K.continuous.measurable
      g.continuous.measurable hfm (g.memLp 2 volume) hf _ _
      (SchwartzMap.seminorm ℝ 0 0 g) B (fun x => SchwartzMap.norm_le_seminorm ℝ g x) hB
  have ht : ‖T (hf.toLp f)-T (g.toLp 2 volume)‖≤C*‖hf.toLp f-g.toLp 2 volume‖ := by
    rw [←map_sub]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have htri := norm_add_le (T (hf.toLp f)-T (g.toLp 2 volume)) (T (g.toLp 2 volume)-y)
  rw [sub_add_sub_cancel,hTg] at htri
  rw [norm_sub_rev (g.toLp 2 volume) (hf.toLp f)] at hc
  simp only [dist_eq_norm] at hg
  have hmul : (C+L+1)*eps=‖T (hf.toLp f)-y‖/2 := by
    unfold eps
    field_simp [show C+L+1≠0 by positivity]
  rw [hTg] at ht
  have hs : ‖T (hf.toLp f)-y‖≤(C+L)*‖hf.toLp f-g.toLp 2 volume‖ := by
    nlinarith only [htri,ht,hc]
  have hsmall : (C+L)*‖hf.toLp f-g.toLp 2 volume‖<(C+L+1)*eps := by
    calc
      _ ≤ (C+L)*eps := mul_le_mul_of_nonneg_left hg.le (add_nonneg hC hL)
      _ < _ := by nlinarith only [heps]
  rw [hmul] at hsmall
  linarith only [hs,hsmall,hdpos]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_LineConvolutionFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite square bounds for the actual convolution of any bounded L2
input, including the localized bounded functions used in the Carleson proof. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_frame {ι : Type*} (I : Finset ι)
    (q : ι → SchwartzMap ℝ ℂ) (W : ι → ℝ) (hW : ∀ i, W i≠0)
    (M : ℝ) (hM : ∀ eta, (∑ i∈I, ‖q i (W i*eta)‖^2)≤M)
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume)
    (B : ℝ) (hB : ∀ x, ‖f x‖≤B) :
    (∑ i∈I, ∫ x, ‖lineConvolution (lineProjectionKernel (q i) (W i) (hW i)) f x‖^2)≤
      M*∫ x, ‖f x‖^2 := by
  have h := lineL2Projection_frame I q W hW M hM (hf.toLp f)
  have heq (i : ι) : ‖lineL2Projection (q i) (W i) (hW i) (hf.toLp f)‖^2=
      ∫ x, ‖lineConvolution (lineProjectionKernel (q i) (W i) (hW i)) f x‖^2 := by
    rw [lineL2Projection_on_bounded (q i) (W i) (hW i) f hfm hf B hB]
    exact memLp_toL2_norm_sq volume _ _
  rw [memLp_toL2_norm_sq volume f hf] at h
  simpa only [heq] using h

theorem bounded_indicator_memLp (f : ℝ → ℂ) (hfm : Measurable f)
    (S : Set ℝ) (hS : MeasurableSet S) (hSf : volume S≠⊤)
    (B : ℝ) (hB : ∀ x, ‖f x‖≤B) : MemLp (S.indicator f) 2 volume := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hSf
  rw [memLp_indicator_iff_restrict hS]
  exact MemLp.of_bound hfm.aestronglyMeasurable.restrict B
    (Filter.Eventually.of_forall hB)

theorem lineConvolution_local_frame {ι : Type*} (I : Finset ι)
    (q : ι → SchwartzMap ℝ ℂ) (W : ι → ℝ) (hW : ∀ i, W i≠0)
    (M : ℝ) (hMnonneg : 0≤M) (hM : ∀ eta, (∑ i∈I, ‖q i (W i*eta)‖^2)≤M)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B)
    (S : Set ℝ) (hS : MeasurableSet S) (hSf : volume S≠⊤) :
    (∑ i∈I, ∫ x, ‖lineConvolution (lineProjectionKernel (q i) (W i) (hW i)) (S.indicator f) x‖^2)≤
      M*(B^2*volume.real S) := by
  have hf := bounded_indicator_memLp f hfm S hS hSf B hfb
  have hb (x : ℝ) : ‖S.indicator f x‖≤B := by
    by_cases hx : x∈S
    · simpa only [Set.indicator_of_mem hx] using hfb x
    · simp only [Set.indicator_of_notMem hx,norm_zero]
      exact hB
  apply (lineConvolution_frame I q W hW M hM (S.indicator f) (hfm.indicator hS) hf B hb).trans
  apply mul_le_mul_of_nonneg_left _ hMnonneg
  have heq : (fun x => ‖S.indicator f x‖^2)=S.indicator (fun x => ‖f x‖^2) := by
    funext x
    by_cases hx : x∈S <;> simp [hx]
  have hint := hf.integrable_norm_pow (by decide : 2≠0)
  rw [heq,integrable_indicator_iff hS] at hint
  rw [heq,integral_indicator hS]
  calc
    _ ≤ ∫ _x in S, B^2 := integral_mono
      hint
      (integrableOn_const hSf) (fun x => pow_le_pow_left₀ (norm_nonneg _) (hfb x) 2)
    _ = _ := by rw [setIntegral_const,smul_eq_mul,mul_comm]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineKernelScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual line projection kernel has the expected physical scale,
including its exact first absolute moment. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_moment1 (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    (∫ t, |t| *‖lineProjectionKernel q W hW.ne' t‖)=
      W*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖) := by
  have he (t : ℝ) : lineProjectionKernel q W hW.ne' t=
      scaledTimeKernel (𝓕⁻ q : SchwartzMap ℝ ℂ) W t := by
    rw [lineProjectionKernel_eq_scaled]
    exact scaledSchwartzKernel_apply q W hW t
  simp_rw [he]
  exact scaledTimeKernel_moment1 (𝓕⁻ q) W hW

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_LineConvolutionFar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First kernel moments control the contribution of bounded data outside
an enlarged interval. This is the far part of the smooth Carleson measure. -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_bound_of_gap (K : ℝ → ℂ)
    (hK : Integrable (fun t => |t| *‖K t‖)) (f : ℝ → ℂ)
    (B d x : ℝ) (hB : 0≤B) (hd : 0<d) (hfb : ∀ y, ‖f y‖≤B)
    (hgap : ∀ t, |t|<d → f (x-t)=0) :
    ‖lineConvolution K f x‖≤(B/d)*(∫ t, |t| *‖K t‖) := by
  have h := norm_integral_le_of_norm_le (hK.const_mul (B/d))
    (Filter.Eventually.of_forall (fun t => show ‖K t*f (x-t)‖≤(B/d)*(|t| *‖K t‖) from by
      by_cases ht : |t|<d
      · rw [hgap t ht,mul_zero,norm_zero]
        positivity
      · have htd : d≤|t| := le_of_not_gt ht
        have hb : B≤(B/d)*|t| := by
          calc
            B = (B/d)*d := (div_mul_cancel₀ B hd.ne').symm
            _ ≤ _ := mul_le_mul_of_nonneg_left htd (div_nonneg hB hd.le)
        rw [norm_mul]
        calc
          _ ≤ ‖K t‖*((B/d)*|t|) := mul_le_mul_of_nonneg_left ((hfb _).trans hb) (norm_nonneg _)
          _ = _ := by ring))
  simpa only [lineConvolution,integral_const_mul] using h

theorem lineProjection_far_bound (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (f : ℝ → ℂ) (B d x : ℝ) (hB : 0≤B) (hd : 0<d)
    (hfb : ∀ y, ‖f y‖≤B) (hgap : ∀ t, |t|<d → f (x-t)=0) :
    ‖lineConvolution (lineProjectionKernel q W hW.ne') f x‖≤
      (B*W/d)*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖) := by
  have h := lineConvolution_bound_of_gap (lineProjectionKernel q W hW.ne')
    (schwartz_first_absolute_moment_integrable _) f B d x hB hd hfb hgap
  rw [lineProjectionKernel_moment1 q W hW] at h
  convert h using 1 <;> first | rfl | ring

theorem lineProjection_far_energy (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (f : ℝ → ℂ) (B d : ℝ) (hB : 0≤B) (hd : 0<d) (hfb : ∀ y, ‖f y‖≤B)
    (J : Set ℝ) (hJ : volume J<⊤)
    (hgap : ∀ x∈J, ∀ t, |t|<d → f (x-t)=0) :
    (∫ x in J, ‖lineConvolution (lineProjectionKernel q W hW.ne') f x‖^2)≤
      ((B*W/d)*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖))^2*volume.real J := by
  have h := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=J)
    (f:=fun x => ‖lineConvolution (lineProjectionKernel q W hW.ne') f x‖^2)
    (C:=((B*W/d)*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖))^2) hJ (fun x hx => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (lineProjection_far_bound q W hW f B d x hB hd hfb (hgap x hx)) 2)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at h
  exact h

theorem outside_enlarged_interval_gap (f : ℝ → ℂ) (a b d x t : ℝ)
    (hx : x∈Icc a b) (ht : |t|<d) :
    (Icc (a-d) (b+d))ᶜ.indicator f (x-t)=0 := by
  apply indicator_of_notMem
  intro hnot
  apply hnot
  have hab := abs_lt.mp ht
  exact ⟨by linarith [hx.1,hab.2],by linarith [hx.2,hab.1]⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineSmoothCarleson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local and far parts of the actual smooth projection Carleson
estimate on a finite dyadic scale range. -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_indicator_split (K f : ℝ → ℂ)
    (hK : Integrable K) (hfm : Measurable f) (B : ℝ)
    (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B) (S : Set ℝ)
    (hS : MeasurableSet S) (x : ℝ) :
    lineConvolution K f x=lineConvolution K (S.indicator f) x+
      lineConvolution K (Sᶜ.indicator f) x := by
  have hb (T : Set ℝ) (y : ℝ) : ‖T.indicator f y‖≤B := by
    by_cases hy : y∈T
    · simpa only [indicator_of_mem hy] using hfb y
    · simpa only [indicator_of_notMem hy,norm_zero] using hB
  have hs := lineConvolution_integrand_of_bounded K (S.indicator f) hK
    (hfm.indicator hS) B (hb S) x
  have ht := lineConvolution_integrand_of_bounded K (Sᶜ.indicator f) hK
    (hfm.indicator hS.compl) B (hb Sᶜ) x
  unfold lineConvolution
  rw [←integral_add hs ht]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hy : x-t∈S <;> simp [hy]

theorem lineProjection_far_integrable (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (f : ℝ → ℂ) (hfm : Measurable f) (B d : ℝ) (hB : 0≤B) (hd : 0<d)
    (hfb : ∀ y, ‖f y‖≤B) (J : Set ℝ) (hJ : MeasurableSet J) (hJf : volume J≠⊤)
    (hgap : ∀ x∈J, ∀ t, |t|<d → f (x-t)=0) :
    IntegrableOn (fun x => ‖lineConvolution (lineProjectionKernel q W hW.ne') f x‖^2) J := by
  apply (integrableOn_const (C:=((B*W/d)*
    (∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖))^2) hJf).mono'
    ((lineConvolution_measurable _ (lineProjectionKernel q W hW.ne').continuous.measurable
      f hfm).norm.pow_const 2).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem hJ] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (lineProjection_far_bound q W hW f B d x hB hd hfb (hgap x hx)) 2

/-- A bounded function produces a Carleson square sum for any fixed smooth
annular window having the indicated finite Fourier square bound. -/
theorem lineProjection_smooth_carleson (q : SchwartzMap ℝ ℂ) (N : ℕ)
    (a b : ℝ) (hab : a<b) (M : ℝ) (hM : 0≤M)
    (hframe : ∀ eta, (∑ n∈Finset.range N,
      ‖q (((b-a)/(2:ℝ)^n)*eta)‖^2)≤M)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B)
    (hfb : ∀ x, ‖f x‖≤B) :
    (∑ n∈Finset.range N, ∫ x in Icc a b,
      ‖lineConvolution (lineProjectionKernel q ((b-a)/(2:ℝ)^n)
        (by positivity)) f x‖^2)≤
      (6*M+4*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖)^2)*B^2*(b-a) := by
  let d := b-a
  let S := Icc (a-d) (b+d)
  let W := fun n : ℕ => d/(2:ℝ)^n
  let K := fun n => lineProjectionKernel q (W n) (by dsimp [W,d]; positivity)
  let near := S.indicator f
  let far := Sᶜ.indicator f
  let A := ∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖
  have hd : 0<d := sub_pos.mpr hab
  have hW (n : ℕ) : 0<W n := by dsimp [W]; positivity
  have hS : MeasurableSet S := measurableSet_Icc
  have hnear : Measurable near := hfm.indicator hS
  have hfar : Measurable far := hfm.indicator hS.compl
  have hb (T : Set ℝ) (x : ℝ) : ‖T.indicator f x‖≤B := by
    by_cases hx : x∈T
    · simpa only [indicator_of_mem hx] using hfb x
    · simpa only [indicator_of_notMem hx,norm_zero] using hB
  have hn := bounded_indicator_memLp f hfm S hS measure_Icc_lt_top.ne B hfb
  have hni (n : ℕ) : Integrable (fun x => ‖lineConvolution (K n) near x‖^2) :=
    (lineConvolution_energy_bound (K n) (K n).integrable (K n).continuous.measurable
      near hnear hn).1.integrable_norm_pow (by decide : 2≠0)
  have hgap (x : ℝ) (hx : x∈Icc a b) (t : ℝ) (ht : |t|<d) : far (x-t)=0 :=
    outside_enlarged_interval_gap f a b d x t hx ht
  have hfi (n : ℕ) : IntegrableOn (fun x => ‖lineConvolution (K n) far x‖^2) (Icc a b) :=
    lineProjection_far_integrable q (W n) (hW n) far hfar B d hB hd
      (hb Sᶜ) _ measurableSet_Icc measure_Icc_lt_top.ne hgap
  have hsplit (n : ℕ) (x : ℝ) : lineConvolution (K n) f x=
      lineConvolution (K n) near x+lineConvolution (K n) far x :=
    lineConvolution_indicator_split (K n) f (K n).integrable hfm B hB hfb S hS x
  have hs (n : ℕ) : (∫ x in Icc a b, ‖lineConvolution (K n) f x‖^2)≤
      2*(∫ x, ‖lineConvolution (K n) near x‖^2)+
      2*(∫ x in Icc a b, ‖lineConvolution (K n) far x‖^2) := by
    calc
      _ ≤ ∫ x in Icc a b, 2*‖lineConvolution (K n) near x‖^2+
          2*‖lineConvolution (K n) far x‖^2 := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
          (((hni n).integrableOn.const_mul 2).add ((hfi n).const_mul 2))
        filter_upwards [] with x
        rw [hsplit]
        change ‖lineConvolution (K n) near x+lineConvolution (K n) far x‖^2≤
          2*‖lineConvolution (K n) near x‖^2+2*‖lineConvolution (K n) far x‖^2
        have ht := norm_add_le (lineConvolution (K n) near x) (lineConvolution (K n) far x)
        have ht2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
        nlinarith [sq_nonneg (‖lineConvolution (K n) near x‖-‖lineConvolution (K n) far x‖)]
      _ = 2*(∫ x in Icc a b, ‖lineConvolution (K n) near x‖^2)+
          2*(∫ x in Icc a b, ‖lineConvolution (K n) far x‖^2) := by
        rw [integral_add ((hni n).integrableOn.const_mul 2) ((hfi n).const_mul 2),
          integral_const_mul,integral_const_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hni n)) (by norm_num : (0:ℝ)≤2)) le_rfl
  have hv : volume.real S=3*d := by
    change volume.real (Icc (a-d) (b+d))=3*d
    rw [Real.volume_real_Icc_of_le (by dsimp [d]; linarith)]
    dsimp [d]; ring
  have hlocal : (∑ n∈Finset.range N, ∫ x, ‖lineConvolution (K n) near x‖^2)≤
      3*M*B^2*d := by
    have hh := lineConvolution_local_frame (Finset.range N) (fun _ => q) W
      (fun n => (hW n).ne') M hM hframe f hfm B hB hfb S hS measure_Icc_lt_top.ne
    rw [hv] at hh
    convert hh using 1 <;> first | rfl | ring
  have hfarbound (n : ℕ) : (∫ x in Icc a b, ‖lineConvolution (K n) far x‖^2)≤
      B^2*A^2*d*(1/2:ℝ)^n := by
    have hh := lineProjection_far_energy q (W n) (hW n) far B d hB hd (hb Sᶜ)
      (Icc a b) measure_Icc_lt_top hgap
    rw [Real.volume_real_Icc_of_le hab.le] at hh
    have he : ((B*W n/d)*A)^2*(b-a)=B^2*A^2*d*((1/2:ℝ)^n)^2 := by
      dsimp [W]
      rw [div_pow,one_pow]
      field_simp
      ring
    rw [he] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hp : (1/2:ℝ)^n≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) n]
  have hfarSum : (∑ n∈Finset.range N, ∫ x in Icc a b,
      ‖lineConvolution (K n) far x‖^2)≤2*B^2*A^2*d := by
    calc
      _ ≤ ∑ n∈Finset.range N, B^2*A^2*d*(1/2:ℝ)^n := Finset.sum_le_sum fun n _ => hfarbound n
      _ = B^2*A^2*d*(∑ n∈Finset.range N, (1/2:ℝ)^n) := by rw [Finset.mul_sum]
      _ ≤ B^2*A^2*d*2 := mul_le_mul_of_nonneg_left (sum_half_powers_le_two N) (by positivity)
      _ = _ := by ring
  change (∑ n∈Finset.range N, ∫ x in Icc a b, ‖lineConvolution (K n) f x‖^2)≤_
  calc
    _ ≤ ∑ n∈Finset.range N, (2*(∫ x, ‖lineConvolution (K n) near x‖^2)+
        2*(∫ x in Icc a b, ‖lineConvolution (K n) far x‖^2)) :=
      Finset.sum_le_sum fun n _ => hs n
    _ = 2*(∑ n∈Finset.range N, ∫ x, ‖lineConvolution (K n) near x‖^2)+
        2*(∑ n∈Finset.range N, ∫ x in Icc a b, ‖lineConvolution (K n) far x‖^2) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
    _ ≤ 2*(3*M*B^2*d)+2*(2*B^2*A^2*d) := by linarith
    _ = _ := by dsimp [A,d]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicProjectionCarleson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth Carleson condition for the actual binary line projections,
first on intervals and then on the nested dyadic line cells. -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicCarlesonConstant_pos : 0<dyadicCarlesonConstant := by
  unfold dyadicCarlesonConstant
  positivity

theorem dyadic_projection_carleson_interval (N : ℕ) (a b : ℝ) (hab : a<b)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B) :
    (∑ n∈Finset.range N, ∫ x in Icc a b,
      ‖lineConvolution (lineProjectionKernel dyadicDifference ((b-a)/(2:ℝ)^n)
        (by positivity)) f x‖^2)≤dyadicCarlesonConstant*B^2*(b-a) := by
  simpa only [dyadicCarlesonConstant,show (6:ℝ)*12=72 by norm_num] using
    lineProjection_smooth_carleson dyadicDifference N a b hab 12 (by norm_num)
    (fun eta => dyadicDifference_inverse_square_sum (Finset.range N) (b-a) eta)
    f hfm B hB hfb

open DyadicLineGrid in
theorem dyadic_projection_carleson_cell (N : ℕ) (q j i : ℤ)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B) :
    (∑ n∈Finset.range N, ∫ x in cell q j i,
      ‖lineConvolution (lineProjectionKernel dyadicDifference (scale (j-(n:ℤ)))
        (scale_pos _).ne') f x‖^2)≤dyadicCarlesonConstant*B^2*scale j := by
  have hwidth : left q j (i+1)-left q j i=scale j := by
    unfold left
    push_cast
    ring
  have hab : left q j i<left q j (i+1) := by
    have hs := scale_pos j
    linarith
  have hscale (n : ℕ) : (left q j (i+1)-left q j i)/(2:ℝ)^n=scale (j-(n:ℤ)) := by
    rw [hwidth]
    simp only [scale,zpow_sub₀ (by norm_num : (2:ℝ)≠0),zpow_natCast]
  have h := dyadic_projection_carleson_interval N (left q j i) (left q j (i+1))
    hab f hfm B hB hfb
  simp_rw [hscale] at h
  simpa only [integral_Icc_eq_integral_Ico,hwidth,cell] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineConvolutionLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded line convolutions have finite local square energy. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_bound (K f : ℝ → ℂ) (hK : Integrable K)
    (B : ℝ) (hf : ∀ x, ‖f x‖≤B) (x : ℝ) :
    ‖lineConvolution K f x‖≤(∫ t, ‖K t‖)*B := by
  have h := norm_integral_le_of_norm_le (hK.norm.mul_const B)
    (Filter.Eventually.of_forall (fun t => show ‖K t*f (x-t)‖≤‖K t‖*B from by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)))
  simpa only [lineConvolution,integral_mul_const] using h

theorem lineConvolution_integrableOn_sq (K : SchwartzMap ℝ ℂ) (f : ℝ → ℂ)
    (hfm : Measurable f) (B : ℝ) (hf : ∀ x, ‖f x‖≤B)
    (S : Set ℝ) (hS : volume S≠⊤) :
    IntegrableOn (fun x => ‖lineConvolution K f x‖^2) S := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS
  have hh : MemLp (lineConvolution K f) 2 (volume.restrict S) :=
    MemLp.of_bound (lineConvolution_measurable K K.continuous.measurable f hfm).aestronglyMeasurable.restrict
      ((∫ t, ‖K t‖)*B) (Filter.Eventually.of_forall (lineConvolution_bound K f K.integrable B hf))
  exact hh.integrable_norm_pow (by decide : 2≠0)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_DyadicProjectionPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite collections of the actual dyadic projection cell energies
satisfy the Carleson packing condition. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert.DyadicLineGrid

theorem cell_level_le_of_subset {q k l i j : ℤ}
    (hsub : cell q k i⊆cell q l j) : k≤l := by
  have hv := ENNReal.toReal_mono (show volume (cell q l j)≠⊤ from measure_Ico_lt_top.ne)
    (measure_mono hsub)
  change volume.real (cell q k i)≤volume.real (cell q l j) at hv
  rw [cell_length,cell_length] at hv
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp hv

theorem sum_cell_integral_le {ι : Type*} (I : Finset ι) (q k top root : ℤ)
    (pos : ι → ℤ) (hinj : Set.InjOn pos I)
    (hsub : ∀ i∈I, cell q k (pos i)⊆cell q top root)
    (g : ℝ → ℝ) (hg : IntegrableOn g (cell q top root)) (hg0 : ∀ x, 0≤g x) :
    (∑ i∈I, ∫ x in cell q k (pos i), g x)≤∫ x in cell q top root, g x := by
  classical
  have hd : (↑I : Set ι).PairwiseDisjoint (fun i => cell q k (pos i)) := by
    intro i hi j hj hij
    exact cells_disjoint q k (fun he => hij (hinj hi hj he))
  rw [←integral_biUnion_finset I (fun _ _ => cell_measurable _ _ _) hd
    (fun i hi => hg.mono_set (hsub i hi))]
  apply setIntegral_mono_set hg (Filter.Eventually.of_forall hg0)
  apply Filter.Eventually.of_forall
  intro x hx
  obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
  exact hsub i hi hx

end LipschitzHilbert.DyadicLineGrid
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem dyadic_projection_carleson_packing {ι : Type*} (I : Finset ι)
    (q top root : ℤ) (level pos : ι → ℤ)
    (hinj : ∀ i∈I, ∀ j∈I, level i=level j → pos i=pos j → i=j)
    (hsub : ∀ i∈I, cell q (level i) (pos i)⊆cell q top root)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B) :
    (∑ i∈I, ∫ x in cell q (level i) (pos i),
      ‖lineConvolution (lineProjectionKernel dyadicDifference (scale (level i))
        (scale_pos _).ne') f x‖^2)≤dyadicCarlesonConstant*B^2*scale top := by
  classical
  let index := fun i => (top-level i).toNat
  let N := I.sup index+1
  have hindex (i : ι) (hi : i∈I) : index i∈Finset.range N := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hi))
  have hlevel (i : ι) (hi : i∈I) : level i=top-(index i:ℤ) := by
    have hh := cell_level_le_of_subset (hsub i hi)
    dsimp [index]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  let energy := fun i => ∫ x in cell q (level i) (pos i),
    ‖lineConvolution (lineProjectionKernel dyadicDifference (scale (level i))
      (scale_pos _).ne') f x‖^2
  have hgroup (n : ℕ) : (∑ i∈I with index i=n, energy i)≤
      ∫ x in cell q top root,
        ‖lineConvolution (lineProjectionKernel dyadicDifference (scale (top-(n:ℤ)))
          (scale_pos _).ne') f x‖^2 := by
    let g := fun x => ‖lineConvolution
      (lineProjectionKernel dyadicDifference (scale (top-(n:ℤ))) (scale_pos _).ne') f x‖^2
    have he (i : ι) (hi : i∈I.filter (fun i => index i=n)) :
        energy i=∫ x in cell q (top-(n:ℤ)) (pos i), g x := by
      have hl := hlevel i (Finset.mem_filter.mp hi).1
      rw [(Finset.mem_filter.mp hi).2] at hl
      dsimp [energy]
      simp only [hl,g]
    calc
      _ = ∑ i∈I with index i=n, ∫ x in cell q (top-(n:ℤ)) (pos i), g x :=
        Finset.sum_congr rfl he
      _ ≤ _ := sum_cell_integral_le _ q (top-(n:ℤ)) top root pos
        (by
          intro i hi j hj hp
          exact hinj i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
            (by rw [hlevel i (Finset.mem_filter.mp hi).1,hlevel j (Finset.mem_filter.mp hj).1,
              (Finset.mem_filter.mp hi).2,(Finset.mem_filter.mp hj).2]) hp)
        (by
          intro i hi
          have hs := hsub i (Finset.mem_filter.mp hi).1
          rw [hlevel i (Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2] at hs
          exact hs)
        g (lineConvolution_integrableOn_sq _ f hfm B hfb _ measure_Ico_lt_top.ne)
        (fun _ => sq_nonneg _)
  calc
    _ = ∑ n∈Finset.range N, ∑ i∈I with index i=n, energy i :=
      (Finset.sum_fiberwise_of_maps_to hindex energy).symm
    _ ≤ ∑ n∈Finset.range N, ∫ x in cell q top root,
        ‖lineConvolution (lineProjectionKernel dyadicDifference (scale (top-(n:ℤ)))
          (scale_pos _).ne') f x‖^2 := Finset.sum_le_sum fun n _ => hgroup n
    _ ≤ _ := dyadic_projection_carleson_cell N q top root f hfm B hB hfb

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_DyadicSmoothEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth projection Carleson coefficients in the finite
product embedding. The low-pass majorant is allowed to hold almost everywhere. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem dyadic_smooth_product_embedding_oai {ι : Type*} [Fintype ι]
    (q : ℤ) (level pos : ι → ℤ)
    (hinj : ∀ i j, level i=level j → pos i=pos j → i=j)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B)
    (h : ι → ℝ → ℂ) (v : ι → ℝ) (hv : ∀ i, 0≤v i)
    (G : ℝ → ℝ) (hG : Measurable G)
    (hh : ∀ i, ∀ x∈cell q (level i) (pos i), ‖h i x‖≤v i)
    (hvG : ∀ i, ∀ᵐ x ∂volume.restrict (cell q (level i) (pos i)), v i≤G x) :
    (∑ i, ∫⁻ x in cell q (level i) (pos i),
      ENNReal.ofReal (‖lineConvolution (lineProjectionKernel dyadicDifference (scale (level i))
        (scale_pos _).ne') f x‖^2)*ENNReal.ofReal (‖h i x‖^2))≤
      ENNReal.ofReal (dyadicCarlesonConstant*B^2)*∫⁻ x, ENNReal.ofReal (G x^2) := by
  classical
  let Q := fun i => cell q (level i) (pos i)
  let w := fun i x => ‖lineConvolution
    (lineProjectionKernel dyadicDifference (scale (level i)) (scale_pos _).ne') f x‖^2
  have hw (i : ι) : IntegrableOn (w i) (Q i) :=
    lineConvolution_integrableOn_sq _ f hfm B hfb _ measure_Ico_lt_top.ne
  have he (i : ι) : (∫⁻ x in Q i, ENNReal.ofReal (w i x))=ENNReal.ofReal (∫ x in Q i, w i x) :=
    (ofReal_integral_eq_lintegral_ofReal (hw i) (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
  have hcar (j : ι) : (∑ i, if Q i⊆Q j then ∫⁻ x in Q i, ENNReal.ofReal (w i x) else 0)≤
      ENNReal.ofReal (dyadicCarlesonConstant*B^2)*volume (Q j) := by
    let I := Finset.univ.filter (fun i => Q i⊆Q j)
    have hr := dyadic_projection_carleson_packing I q (level j) (pos j) level pos
      (fun i _ k _ => hinj i k) (fun i hi => (Finset.mem_filter.mp hi).2) f hfm B hB hfb
    have hs : (∑ i, if Q i⊆Q j then ∫⁻ x in Q i, ENNReal.ofReal (w i x) else 0)=
        ENNReal.ofReal (∑ i∈I, ∫ x in Q i, w i x) := by
      simp only [he,←Finset.sum_filter]
      exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg (fun _ => sq_nonneg _))).symm
    rw [hs]
    apply (ENNReal.ofReal_le_ofReal hr).trans_eq
    rw [ENNReal.ofReal_mul (mul_nonneg dyadicCarlesonConstant_pos.le (sq_nonneg B))]
    congr 1
    rw [←cell_length q (level j) (pos j)]
    exact ENNReal.ofReal_toReal measure_Ico_lt_top.ne
  exact carleson_product_energy_ae Q volume (fun i => cell_measurable q (level i) (pos i))
    (fun i j => cells_nested_or_disjoint q (level i) (level j) (pos i) (pos j))
    (fun i x => ENNReal.ofReal (w i x)) (ENNReal.ofReal (dyadicCarlesonConstant*B^2))
    hcar h v hv G hG hh hvG

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.LipschitzHilbert.PacketRepresentation.dyadic_smooth_product_embedding_oai.{u_1} := @OAI.LipschitzHilbert.PacketRepresentation.dyadic_smooth_product_embedding_oai.{u_1}
