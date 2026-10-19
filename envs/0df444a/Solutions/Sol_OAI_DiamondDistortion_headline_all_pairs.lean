-- Prove2me | solution 1 for OAI.DiamondDistortion.headline_all_pairs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:11:31.514171+00:00
-- url     : https://prove2.me/submissions/51ae035b-f82e-4201-b46e-4f46e2948865

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAIQWDD000

section
-- module Solutions.OAIQW_DiamondDistortion.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_DiamondDistortion.FiniteAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace FiniteAverage
variable {Ω : Type*} [Fintype Ω]

lemma jensen_sq (w f : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω, w ω = 1) :
    (∑ ω, w ω * f ω) ^ 2 ≤ ∑ ω, w ω * f ω ^ 2 := by
  let m := ∑ ω, w ω * f ω
  have hpos : 0 ≤ ∑ ω, w ω * (f ω - m) ^ 2 := by
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hw ω) (sq_nonneg _))
  have he : (∑ ω, w ω * (f ω - m) ^ 2) =
      (∑ ω, w ω * f ω ^ 2) - 2*m*(∑ ω, w ω*f ω) + m^2*(∑ ω,w ω) := by
    calc
      _ = ∑ ω, (w ω * f ω ^ 2 - (2*m)*(w ω*f ω) + m^2*w ω) := by
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  rw [he, hs] at hpos
  dsimp [m] at hpos
  nlinarith

lemma sum_mul_sq_le (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hs : ∑ ω,w ω = 1) (f : Ω → ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hf : (∑ ω, w ω * f ω ^ 2) ≤ V) :
    |∑ ω, w ω * f ω| ≤ Real.sqrt V := by
  have h := (jensen_sq w f hw hs).trans hf
  exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp (by
    rw [sq_abs, Real.sq_sqrt hV]
    exact h)

lemma double_product (w f g : Ω → ℝ) :
    (∑ ω, w ω * f ω) * (∑ ω, w ω * g ω) =
      ∑ ω, ∑ ν, w ω * w ν * (f ω * g ν) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  ring

lemma norm_mean_le_sqrt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω,w ω = 1)
    (z : Ω → E) {V : ℝ} (hV : 0 ≤ V)
    (hz : (∑ ω, w ω * ‖z ω‖ ^ 2) ≤ V) :
    ‖∑ ω, w ω • z ω‖ ≤ Real.sqrt V := by
  calc
    _ ≤ ∑ ω, ‖w ω • z ω‖ := norm_sum_le _ _
    _ = ∑ ω, w ω * ‖z ω‖ := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw ω)]
    _ ≤ |∑ ω, w ω * ‖z ω‖| := le_abs_self _
    _ ≤ _ := sum_mul_sq_le w hw hs (fun ω => ‖z ω‖) hV hz

/-- Averaged opposite-sign cancellation, including the error's gate energy. -/
lemma pooled_mass {κ : Type*} [Fintype κ]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω,w ω = 1)
    (b W : Ω → κ → ℝ) (V L : Ω → ℝ)
    (hmean : ∀ g, (∑ ω,w ω*b ω g) = -(∑ ω,w ω*W ω g))
    (hW : ∀ ω, (∑ g,W ω g ^ 2) ≤ V ω)
    (hopp : ∀ ω ν, (∑ g, (|b ω g| * |b ν g| - b ω g*b ν g)) ≤ L ω + L ν) :
    (∑ g, (∑ ω,w ω* |b ω g|)^2) ≤ (∑ ω,w ω*V ω) + 2*(∑ ω,w ω*L ω) := by
  have hsign : (∑ g, (∑ ω,w ω*b ω g)^2) ≤ ∑ ω,w ω*V ω := by
    calc
      _ ≤ ∑ g, ∑ ω,w ω*(W ω g)^2 := by
        apply Finset.sum_le_sum
        intro g _
        rw [hmean g, neg_sq]
        exact jensen_sq w (fun ω => W ω g) hw hs
      _ = ∑ ω,w ω*(∑ g,W ω g^2) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hW ω) (hw ω)
  have hleft : (∑ g, ((∑ ω,w ω* |b ω g|)^2 - (∑ ω,w ω*b ω g)^2)) =
      ∑ ω,∑ ν,w ω*w ν*(∑ g,(|b ω g| * |b ν g| - b ω g*b ν g)) := by
    calc
      _ = ∑ g, ∑ ω,∑ ν,w ω*w ν*(|b ω g| * |b ν g| - b ω g*b ν g) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [sq, sq, double_product, double_product, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro ν _
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro ω _
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
  have hright : (∑ ω,∑ ν,w ω*w ν*(L ω+L ν)) = 2*(∑ ω,w ω*L ω) := by
    calc
      _ = (∑ ω,w ω*L ω)*(∑ ν,w ν) + (∑ ω,w ω)*(∑ ν,w ν*L ν) := by
        simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        apply Finset.sum_congr rfl
        intro ν _
        ring
      _ = _ := by rw [hs]; ring
  have hcross : (∑ ω,∑ ν,w ω*w ν*(∑ g,(|b ω g| * |b ν g| - b ω g*b ν g))) ≤
      ∑ ω,∑ ν,w ω*w ν*(L ω+L ν) := by
    apply Finset.sum_le_sum
    intro ω _
    apply Finset.sum_le_sum
    intro ν _
    exact mul_le_mul_of_nonneg_left (hopp ω ν) (mul_nonneg (hw ω) (hw ν))
  rw [← hleft, hright, Finset.sum_sub_distrib] at hcross
  linarith

lemma joint_budget (w : Ω → ℝ) (hw : ∀ ω,0 ≤ w ω) (hs : ∑ ω,w ω=1)
    (I : Ω → Type*) [∀ ω,Fintype (I ω)] (a b : ∀ ω,I ω→ℝ) {r R : ℝ}
    (he : ∀ ω,(∑ i,a ω i^2) ≤ R^2)
    (hc : (∑ ω,w ω*(∑ i,a ω i*b ω i)) = r^2) :
    (∑ ω,w ω*(∑ i,(a ω i-b ω i)^2)) +
      (∑ ω,w ω*(r^2-∑ i,b ω i^2)) ≤ R^2-r^2 := by
  have hrow (ω : Ω) : (∑ i,(a ω i-b ω i)^2) + (r^2-∑ i,b ω i^2) =
      (∑ i,a ω i^2) - 2*(∑ i,a ω i*b ω i) + r^2 := by
    have hex : (∑ i,(a ω i-b ω i)^2) =
        (∑ i,a ω i^2) - 2*(∑ i,a ω i*b ω i) + (∑ i,b ω i^2) := by
      calc
        _ = ∑ i,(a ω i^2 - 2*(a ω i*b ω i) + b ω i^2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hex]
    ring
  have hid : (∑ ω,w ω*(∑ i,(a ω i-b ω i)^2)) +
      (∑ ω,w ω*(r^2-∑ i,b ω i^2)) = (∑ ω,w ω*(∑ i,a ω i^2)) - r^2 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← mul_add, hrow]
    calc
      _ = (∑ ω,w ω*(∑ i,a ω i^2)) - 2*(∑ ω,w ω*(∑ i,a ω i*b ω i)) +
          r^2*(∑ ω,w ω) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = _ := by rw [hc,hs]; ring
  rw [hid]
  apply sub_le_sub_right
  calc
    _ ≤ ∑ ω,w ω*R^2 := Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (he ω) (hw ω)
    _ = R^2 := by rw [← Finset.sum_mul,hs,one_mul]

lemma sqrt_pooled {η θ : ℝ} (hη : 0 ≤ η) (hθ : 0 ≤ θ) :
    Real.sqrt η + Real.sqrt (η+2*θ) ≤ 2*Real.sqrt (η+θ) := by
  have h2 : 0 ≤ η+2*θ := by positivity
  have h1 : 0 ≤ η+θ := add_nonneg hη hθ
  have he0 := Real.sq_sqrt hη
  have he1 := Real.sq_sqrt h1
  have he2 := Real.sq_sqrt h2
  have hp : Real.sqrt η * Real.sqrt (η+2*θ) ≤ η+θ := by
    have he : (Real.sqrt η * Real.sqrt (η+2*θ))^2 = η*(η+2*θ) := by
      rw [mul_pow, he0, he2]
    have hn := mul_nonneg (Real.sqrt_nonneg η) (Real.sqrt_nonneg (η+2*θ))
    nlinarith [sq_nonneg θ]
  apply (sq_le_sq₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
  nlinarith

end FiniteAverage

end DiamondDistortion

end

end OAI
end

section
-- module Solutions.OAIQW_DiamondDistortion.SegmentNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

variable (T)

lemma test_energy_le {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (hS : ∀ i, T.IsSegment (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (u : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ S i, u v) ^ 2) ≤ (T.primalSeminorm u) ^ 2 := by
  let F := T.familyOfFintype S hS hd
  have hb := pow_le_pow_left₀ (norm_nonneg (F.test u)) (T.test_le_primal F u) 2
  rw [EuclideanSpace.norm_sq_eq] at hb
  change (∑ i : Fin (Fintype.card κ),
    ‖∑ v ∈ S ((Fintype.equivFin κ).symm i), u v‖ ^ 2) ≤ _ at hb
  rw [(Fintype.equivFin κ).symm.sum_comp (fun i : κ => ‖∑ v ∈ S i, u v‖ ^ 2)] at hb
  simpa only [Real.norm_eq_abs, sq_abs] using hb

/-- Empty pieces in a partition may be discarded; they contribute no energy. -/
lemma test_energy_le_allow_empty {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (hS : ∀ i, (S i).Nonempty → T.IsSegment (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (u : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ S i, u v) ^ 2) ≤ (T.primalSeminorm u) ^ 2 := by
  classical
  let K := {i : κ // (S i).Nonempty}
  have h := T.test_energy_le (fun i : K => S i.val) (fun i => hS _ i.property)
    (by intro i j hij; exact hd (fun he => hij (Subtype.ext he))) u
  have hz : (∑ i : {i : κ // ¬ (S i).Nonempty}, (∑ v ∈ S i.val, u v) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : S i.val = ∅ := Finset.not_nonempty_iff_eq_empty.mp i.property
    simp [hi]
  have he := Fintype.sum_subtype_add_sum_subtype
    (fun i : κ => (S i).Nonempty) (fun i => (∑ v ∈ S i, u v) ^ 2)
  rw [hz, add_zero] at he
  rwa [← he]

lemma sub_filterPrimal (p : ι → Prop) (u : T.Primal) :
    u - T.filterPrimal p u = T.filterPrimal (fun x => ¬ p x) u := by
  apply Finsupp.ext
  intro v
  change T.ofPrimal (u - T.filterPrimal p u) v =
    T.ofPrimal (T.filterPrimal (fun x => ¬ p x) u) v
  simp only [ofPrimal_sub, ofPrimal_filter, Finsupp.sub_apply, Finsupp.filter_apply]
  split_ifs <;> simp_all

lemma sum_units_eq_filter (H : Finset ι) (u : T.Primal) :
    (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v) = T.filterPrimal (· ∈ H) u := by
  classical
  apply Finsupp.ext
  intro w
  change T.ofPrimal (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v) w =
    T.ofPrimal (T.filterPrimal (· ∈ H) u) w
  simp only [ofPrimal_sum, ofPrimal_smul, ofPrimal_filter, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  simp [ofPrimal, unitFinite, Finsupp.single_apply,
    mul_ite, Finset.sum_ite_eq']
  convert (Finsupp.filter_apply (· ∈ H) (T.ofPrimal u) w).symm using 1
  all_goals congr

lemma headPrimal_coe (H : Finset ι) (u : T.Primal) :
    T.headPrimal H (u : T.JamesSpace) =
      (T.filterPrimal (· ∈ H) u : T.JamesSpace) := by
  classical
  rw [headPrimal_apply, ← T.sum_units_eq_filter]
  simp only [coordinate_coe, unitVector]
  change (∑ v ∈ H, T.ofPrimal u v •
    (UniformSpace.Completion.toComplL (𝕜 := ℝ)) (T.unitFinite v)) =
    (UniformSpace.Completion.toComplL (𝕜 := ℝ)) (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v)
  simp only [map_sum, map_smul]

lemma headDual_apply_apply (H : Finset ι) (x : T.Dual) (u : T.JamesSpace) :
    T.headDual H x u = x (T.headPrimal H u) := by
  simp [headDual_apply, headPrimal_apply, mul_comm]

lemma tailDual_apply_apply (H : Finset ι) (x : T.Dual) (u : T.JamesSpace) :
    T.tailDual H x u = x (u - T.headPrimal H u) := by
  simp [tailDual_apply, mul_comm]

lemma combine_sub {κ : Type*} [Fintype κ] (S : κ → Finset ι) (a b : κ → ℝ) :
    T.combine S (a-b) = T.combine S a - T.combine S b := by
  unfold combine
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact sub_smul (a i) (b i) (T.segmentFunctional (S i))

lemma combine_unit_of_mem (F : T.Family) (a : Fin F.n → ℝ)
    (i : Fin F.n) {v : ι} (hv : v ∈ F.seg i) :
    T.combine F.seg a (T.unitVector v) = a i := by
  classical
  rw [combine_unit, Finset.sum_eq_single i]
  · simp only [ite_eq_left hv]
  · intro j _ hji
    rw [ite_eq_right (fun h => Finset.disjoint_left.mp (F.disjoint hji) h hv)]
  · simp

/-- Cauchy--Schwarz for represented disjoint segment coefficients, with empty
    pieces permitted after a projection. -/
lemma norm_combine_le {κ : Type*} [Fintype κ] (S : κ → Finset ι) (a : κ → ℝ)
    (hS : ∀ i, (S i).Nonempty → T.IsSegment (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    ‖T.combine S a‖ ≤ Real.sqrt (∑ i, (a i) ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [combine_coe, Real.norm_eq_abs, UniformSpace.Completion.norm_coe, norm_eq_primal]
    have htest : Real.sqrt (∑ i, (∑ v ∈ S i, T.ofPrimal u v) ^ 2) ≤
        T.primalSeminorm (T.ofPrimal u) := by
      exact (Real.sqrt_le_left (apply_nonneg _ _)).mpr
        (T.test_energy_le_allow_empty S hS hd (T.ofPrimal u))
    calc
      |∑ i, a i * (∑ v ∈ S i, T.ofPrimal u v)| ≤
          ∑ i, |a i * (∑ v ∈ S i, T.ofPrimal u v)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |a i| * |∑ v ∈ S i, T.ofPrimal u v| := by simp only [abs_mul]
      _ ≤ Real.sqrt (∑ i, (a i) ^ 2) *
          Real.sqrt (∑ i, (∑ v ∈ S i, T.ofPrimal u v) ^ 2) := by
        simpa only [sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun i => |a i|) (fun i => |∑ v ∈ S i, T.ofPrimal u v|)
      _ ≤ _ := mul_le_mul_of_nonneg_left htest (Real.sqrt_nonneg _)

/-- A finite family of disjoint cones can be tested by independently maximizing
    each cone's represented segment. This is the finite dual reconstruction bound. -/
lemma norm_cone_mean_le {Ω κ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype κ]
    (S : Ω → κ → Finset ι) (a : Ω → κ → ℝ) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hS : ∀ ω g, (S ω g).Nonempty → T.IsSegment (S ω g))
    (hd : ∀ g h, g ≠ h → ∀ ω ν, Disjoint (S ω g) (S ν h)) :
    ‖∑ ω, w ω • T.combine (S ω) (a ω)‖ ≤
      Real.sqrt (∑ g, (∑ ω, w ω * |a ω g|) ^ 2) := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [sum_apply]
    simp only [smul_apply, smul_eq_mul, combine_coe, Real.norm_eq_abs,
      UniformSpace.Completion.norm_coe, norm_eq_primal]
    choose idx hidx hmax using fun g : κ => Finset.exists_max_image Finset.univ
      (fun ω => |∑ v ∈ S ω g, T.ofPrimal u v|) Finset.univ_nonempty
    let t : κ → ℝ := fun g => |∑ v ∈ S (idx g) g, T.ofPrimal u v|
    have ht (ω : Ω) (g : κ) : |∑ v ∈ S ω g, T.ofPrimal u v| ≤ t g :=
      hmax g ω (Finset.mem_univ _)
    have htest : Real.sqrt (∑ g, t g ^ 2) ≤ T.primalSeminorm (T.ofPrimal u) := by
      apply (Real.sqrt_le_left (apply_nonneg _ _)).2
      simpa only [t, sq_abs] using T.test_energy_le_allow_empty
        (fun g => S (idx g) g) (fun g => hS (idx g) g)
        (fun {g h} hgh => hd g h hgh (idx g) (idx h)) (T.ofPrimal u)
    calc
      |∑ ω, w ω * ∑ g, a ω g * (∑ v ∈ S ω g, T.ofPrimal u v)| ≤
          ∑ ω, |w ω * ∑ g, a ω g * (∑ v ∈ S ω g, T.ofPrimal u v)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ ω, w ω * |∑ g, a ω g * (∑ v ∈ S ω g, T.ofPrimal u v)| := by
        simp only [abs_mul, abs_of_nonneg (hw _)]
      _ ≤ ∑ ω, w ω * (∑ g, |a ω g| * t g) := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        calc
          _ ≤ ∑ g, |a ω g * (∑ v ∈ S ω g, T.ofPrimal u v)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro g _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (ht ω g) (abs_nonneg _)
      _ = ∑ g, (∑ ω, w ω * |a ω g|) * t g := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro g _
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ ≤ Real.sqrt (∑ g, (∑ ω, w ω * |a ω g|) ^ 2) * Real.sqrt (∑ g, t g ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left htest (Real.sqrt_nonneg _)

lemma combine_smul {κ : Type*} [Fintype κ] (S : κ → Finset ι) (a : κ → ℝ) (c : ℝ) :
    T.combine S (fun i => c * a i) = c • T.combine S a := by
  simp only [combine, mul_smul, Finset.smul_sum]

lemma headDual_eq_self {H : Finset ι} {x : T.Dual}
    (hx : ∀ v, v ∉ H → x (T.unitVector v) = 0) : T.headDual H x = x := by
  apply T.dual_ext
  intro v
  rw [headDual_unit]
  split_ifs with hv
  · rfl
  · exact (hx v hv).symm

lemma headDual_finite_apply {H : Finset ι} (x : T.Dual) (u : T.Primal)
    (hu : (T.ofPrimal u).support ⊆ H) :
    T.headDual H x (u : T.JamesSpace) = x (u : T.JamesSpace) := by
  rw [dual_coe_apply, dual_coe_apply]
  apply Finset.sum_congr rfl
  intro v hv
  rw [headDual_unit, ite_eq_left (hu hv)]

lemma headDual_commute (H K : Finset ι) (x : T.Dual) :
    T.headDual H (T.headDual K x) = T.headDual K (T.headDual H x) := by
  apply T.dual_ext
  intro v
  simp only [headDual_unit]
  split_ifs <;> rfl

lemma tailDual_headDual (H K : Finset ι) (x : T.Dual) :
    T.tailDual H (T.headDual K x) = T.headDual K (T.tailDual H x) := by
  rw [tailDual_apply, tailDual_apply, map_sub, headDual_commute]

lemma headArray_outside (H : Finset ι) (u : T.JamesSpace) {v : ι} (hv : v ∉ H) :
    T.headArray H u v = 0 := by
  classical
  simp [headArray, Finsupp.finsetSum_apply, Finsupp.single_apply, hv,
    Finset.sum_ite_eq']

lemma finiteEmbedding_headArray (H : Finset ι) (u : T.JamesSpace) :
    T.finiteEmbedding (T.headArray H u) = T.headPrimal H u := by
  simp only [headArray, map_sum, map_smul, finiteEmbedding_single, one_smul,
    headPrimal_apply]

lemma coordinateTest_not_mem (K : Finset ι) (a : T.Coordinates K)
    {v : ι} (hv : v ∉ K) : T.coordinateTest K a v = 0 := by simp [coordinateTest, hv]

lemma coordinateTest_sum (K S : Finset ι) (a : T.Coordinates K) (hSK : S ⊆ K) :
    (∑ v ∈ S, T.coordinateTest K a v) =
      ∑ v : K, if v.val ∈ S then a v else 0 := by
  classical
  have hfilter : K.filter (· ∈ S) = S := by ext v; simp; exact fun h => hSK h
  calc
    _ = ∑ v ∈ K, if v ∈ S then T.coordinateTest K a v else 0 := by
      rw [← Finset.sum_filter, hfilter]
    _ = ∑ v : K, if v.val ∈ S then T.coordinateTest K a v.val else 0 :=
      (Finset.sum_coe_sort K _).symm
    _ = _ := by simp only [coordinateTest_mem]

lemma functional_pi_formula (K : Finset ι) (f : T.Coordinates K →L[ℝ] ℝ)
    (z : T.Coordinates K) : f z = ∑ v : K, z v * f (Pi.single v 1) := by
  classical
  have hz : z = ∑ v : K, z v • (Pi.single v 1 : T.Coordinates K) := by
    ext w
    simp [Pi.single_apply, Finset.sum_apply, mul_ite, Finset.sum_ite_eq]
  conv_lhs => rw [hz]
  simp only [map_sum, map_smul, smul_eq_mul]

variable {T}

lemma LocalFamily.asFamily_subset {K : Finset ι} (F : T.LocalFamily K)
    (i : Fin F.asFamily.n) : F.asFamily.seg i ⊆ K :=
  T.localFamily_subset F _

variable (T)

lemma functional_localMap {K : Finset ι} (F : T.LocalFamily K)
    (f : T.Coordinates K →L[ℝ] ℝ) (a : EuclideanSpace ℝ (T.LocalIndex F)) :
    f (T.localMap F a) = ∑ S : T.LocalIndex F, a S *
      (∑ v ∈ S.val, T.coordinateTest K (fun w => f (Pi.single w 1)) v) := by
  classical
  rw [T.functional_pi_formula]
  simp only [localMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [T.coordinateTest_sum K S.val _ (T.localFamily_subset F S), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp

lemma finiteEmbedding_norm (p : ι →₀ ℝ) :
    ‖T.finiteEmbedding p‖ = T.primalSeminorm p := by
  rw [finiteEmbedding_apply, UniformSpace.Completion.norm_coe]
  rfl

lemma coordinateTest_pairing (K : Finset ι) (a : T.Coordinates K) (x : T.Dual) :
    x (T.finiteEmbedding (T.coordinateTest K a)) =
      ∑ v : K, a v * x (T.unitVector v.val) := by
  classical
  rw [finiteEmbedding_apply, dual_coe_apply]
  change (∑ v ∈ (T.coordinateTest K a).support,
    T.coordinateTest K a v * x (T.unitVector v)) = _
  have hs : (T.coordinateTest K a).support ⊆ K := by
    intro v hv
    by_contra hn
    exact Finsupp.mem_support_iff.mp hv (T.coordinateTest_not_mem K a hn)
  calc
    _ = ∑ v ∈ K, T.coordinateTest K a v * x (T.unitVector v) := by
      apply Finset.sum_subset hs
      intro v _ hv
      rw [Finsupp.notMem_support_iff.mp hv, zero_mul]
    _ = ∑ v : K, T.coordinateTest K a v.val * x (T.unitVector v.val) :=
      (Finset.sum_coe_sort K _).symm
    _ = _ := by simp only [coordinateTest_mem]

lemma local_energy_le_of_functional_bound {K : Finset ι} (F : T.LocalFamily K)
    (f : T.Coordinates K →L[ℝ] ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hf : ∀ a : EuclideanSpace ℝ (T.LocalIndex F), ‖a‖ ≤ 1 →
      f (T.localMap F a) ≤ u) :
    (∑ S : T.LocalIndex F, (∑ v ∈ S.val,
      T.coordinateTest K (fun w => f (Pi.single w 1)) v) ^ 2) ≤ u ^ 2 := by
  classical
  let b : EuclideanSpace ℝ (T.LocalIndex F) := WithLp.toLp 2
    (fun S => ∑ v ∈ S.val, T.coordinateTest K (fun w => f (Pi.single w 1)) v)
  have he : (∑ S : T.LocalIndex F, (∑ v ∈ S.val,
      T.coordinateTest K (fun w => f (Pi.single w 1)) v) ^ 2) = ‖b‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [b, Real.norm_eq_abs, sq_abs]
  rw [he]
  apply (sq_le_sq₀ (norm_nonneg _) hu).2
  by_cases hb : b = 0
  · simpa only [hb, norm_zero] using hu
  have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hbn : ‖‖b‖⁻¹ • b‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hn]
  have h := hf (‖b‖⁻¹ • b) hbn
  rw [T.functional_localMap] at h
  have hsum : (∑ S : T.LocalIndex F, (‖b‖⁻¹ • b) S *
      (∑ v ∈ S.val, T.coordinateTest K (fun w => f (Pi.single w 1)) v)) = ‖b‖ := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    change (∑ S, ‖b‖⁻¹ * b S * b S) = ‖b‖
    simp_rw [mul_assoc, ← sq]
    rw [← Finset.mul_sum]
    have hb2 : (∑ S, b S ^ 2) = ‖b‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
    rw [hb2, sq, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  rwa [hsum] at h

lemma coefficientBall_compact (K : Finset ι) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (T.coefficientBall K R) := by
  apply (isCompact_closedBall (0 : T.Coefficients K) R).of_isClosed_subset
  · exact isClosed_le (by fun_prop) continuous_const
  · intro c hc
    simp only [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro F
    exact (Finset.single_le_sum (fun G _ => norm_nonneg (c G)) (Finset.mem_univ F)).trans hc

lemma coefficientBall_convex (K : Finset ι) (R : ℝ) :
    Convex ℝ (T.coefficientBall K R) := by
  intro c hc d hd a b ha hb hab
  change ∑ F, ‖a • c F + b • d F‖ ≤ R
  calc
    _ ≤ ∑ F, (a * ‖c F‖ + b * ‖d F‖) := by
      apply Finset.sum_le_sum
      intro F _
      calc
        ‖a • c F + b • d F‖ ≤ ‖a • c F‖ + ‖b • d F‖ := norm_add_le _ _
        _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a * (∑ F, ‖c F‖) + b * (∑ F, ‖d F‖) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ a * R + b * R := add_le_add (mul_le_mul_of_nonneg_left hc ha)
      (mul_le_mul_of_nonneg_left hd hb)
    _ = R := by rw [← add_mul, hab, one_mul]

lemma totalMap_single (K : Finset ι) (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) :
    T.totalMap K (Pi.single F a) = T.localMap F a := by
  classical
  rw [totalMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_eq_single F]
  · rw [Pi.single_eq_same]
  · intro G _ hGF
    rw [Pi.single_eq_of_ne hGF, map_zero]
  · simp

lemma single_mem_coefficientBall (K : Finset ι) (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) {R : ℝ} (ha : ‖a‖ ≤ R) :
    Pi.single F a ∈ T.coefficientBall K R := by
  classical
  change ∑ G, ‖(Pi.single F a : T.Coefficients K) G‖ ≤ R
  rw [Finset.sum_eq_single F]
  · simpa only [Pi.single_eq_same] using ha
  · intro G _ hGF
    rw [Pi.single_eq_of_ne hGF, norm_zero]
  · simp

lemma lawOfCoefficients_subset {K : Finset ι} (x : T.Dual) {R : ℝ} (hR : 0 < R)
    (c : T.Coefficients K) (hc : c ∈ T.coefficientBall K R)
    (hce : T.totalMap K c = fun v : K => x (T.unitVector v.val))
    (ω : Option (T.LocalFamily K))
    (i : Fin ((T.lawOfCoefficients x hR c hc hce).atom ω).family.n) :
    ((T.lawOfCoefficients x hR c hc hce).atom ω).family.seg i ⊆ K := by
  cases ω with
  | none => exact Fin.elim0 i
  | some F => exact F.asFamily_subset i

lemma pairLaws_subset {Ω : Type*} [Fintype Ω] {R : ℝ} {x y : T.Dual}
    (Lp : T.AtomLaw Ω R (x+y)) (Lm : T.AtomLaw Ω R (x-y)) (K : Finset ι)
    (hp : ∀ ω i, (Lp.atom ω).family.seg i ⊆ K)
    (hm : ∀ ω i, (Lm.atom ω).family.seg i ⊆ K) :
    ∀ ω i, ((T.pairLaws Lp Lm).atom ω).family.seg i ⊆ K := by
  rintro ⟨b,ω⟩ i
  cases b
  · exact hm ω i
  · exact hp ω i

lemma span_coordinates_finite_support {x : T.Dual}
    (hx : x ∈ Submodule.span ℝ (Set.range T.coordinate)) :
    ∃ S : Finset ι, ∀ v, v ∉ S → x (T.unitVector v)=0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,rfl⟩ := hx
    refine ⟨{v}, ?_⟩
    intro w hw
    simp only [Finset.mem_singleton] at hw
    simp [coordinate_unitVector,hw]
  | zero => exact ⟨∅, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨S,hS⟩ := hx
    obtain ⟨U,hU⟩ := hy
    refine ⟨S ∪ U, ?_⟩
    intro v hv
    have hvS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
    have hvU : v ∉ U := fun h => hv (Finset.mem_union_right _ h)
    simp only [add_apply,hS v hvS,hU v hvU,add_zero]
  | smul a x _ hx =>
    obtain ⟨S,hS⟩ := hx
    exact ⟨S, fun v hv => by simp only [smul_apply,hS v hv,smul_zero]⟩

end SegmentSystem

end DiamondDistortion

end

end OAI
end

section
-- module Solutions.OAIQW_DiamondDistortion.Ancestry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Ancestry
open scoped Classical
variable {ι : Type*} [A : Ancestry ι]

attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
lemma ancestral_not_above (c : ι) : A.Ancestral {v | ¬ c ≤ v} := by
  intro a b hab hb ha
  exact hb (ha.trans hab)

lemma interval_chain {S : Finset ι} (hS : A.segments.IsSegment S) :
    ∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a := by
  obtain ⟨l, r, _, hmem⟩ := hS
  intro a ha b hb
  exact A.predecessors_total ((hmem a).mp ha).2 ((hmem b).mp hb).2

lemma segment_filter_head {S : Finset ι} (hS : A.segments.IsSegment S)
    {H : Set ι} (hH : A.Ancestral H) :
    (S.filter (· ∈ H)).Nonempty → A.segments.IsSegment (S.filter (· ∈ H)) := by
  classical
  intro hne
  obtain ⟨c, hc, hmax⟩ := Finset.exists_maximal hne
  have hcS : c ∈ S := (Finset.mem_filter.mp hc).1
  have hcH : c ∈ H := (Finset.mem_filter.mp hc).2
  have hgreat : ∀ v ∈ S.filter (· ∈ H), v ≤ c := by
    intro v hv
    rcases A.interval_chain hS c hcS v (Finset.mem_filter.mp hv).1 with h | h
    · exact hmax hv h
    · exact h
  obtain ⟨a, b, hab, hmem⟩ := hS
  refine ⟨a, c, ((hmem c).mp hcS).1, ?_⟩
  intro v
  simp only [Finset.mem_filter]
  constructor
  · intro hv
    exact ⟨((hmem v).mp hv.1).1, hgreat v (Finset.mem_filter.mpr hv)⟩
  · intro hv
    exact ⟨(hmem v).mpr ⟨hv.1, hv.2.trans ((hmem c).mp hcS).2⟩, hH hv.2 hcH⟩

lemma segment_filter_tail {S : Finset ι} (hS : A.segments.IsSegment S)
    {H : Set ι} (hH : A.Ancestral H) :
    (S.filter (· ∉ H)).Nonempty → A.segments.IsSegment (S.filter (· ∉ H)) := by
  classical
  intro hne
  obtain ⟨c, hc, hmin⟩ := Finset.exists_minimal hne
  have hcS : c ∈ S := (Finset.mem_filter.mp hc).1
  have hcH : c ∉ H := (Finset.mem_filter.mp hc).2
  have hleast : ∀ v ∈ S.filter (· ∉ H), c ≤ v := by
    intro v hv
    rcases A.interval_chain hS c hcS v (Finset.mem_filter.mp hv).1 with h | h
    · exact h
    · exact hmin hv h
  obtain ⟨a, b, hab, hmem⟩ := hS
  refine ⟨c, b, ((hmem c).mp hcS).2, ?_⟩
  intro v
  simp only [Finset.mem_filter]
  constructor
  · intro hv
    exact ⟨hleast v (Finset.mem_filter.mpr hv), ((hmem v).mp hv.1).2⟩
  · intro hv
    refine ⟨(hmem v).mpr ⟨((hmem c).mp hcS).1.trans hv.1, hv.2⟩, ?_⟩
    exact fun hvH => hcH (hH hv.1 hvH)

/-- Splitting each member of a disjoint family at its own ancestral cut preserves
    the testing budget. This is the simultaneous, not one-gate-at-a-time, estimate. -/
lemma split_energy_le (F : A.segments.Family) (H : Fin F.n → Set ι)
    (hH : ∀ i, A.Ancestral (H i)) (u : ι →₀ ℝ) :
    (∑ i, ((∑ v ∈ (F.seg i).filter (· ∈ H i), u v) ^ 2 +
      (∑ v ∈ (F.seg i).filter (· ∉ H i), u v) ^ 2)) ≤
      (A.segments.primalSeminorm u) ^ 2 := by
  classical
  let P : Fin F.n × Bool → Finset ι := fun z =>
    if z.2 then (F.seg z.1).filter (· ∉ H z.1) else (F.seg z.1).filter (· ∈ H z.1)
  have hp : ∀ z, (P z).Nonempty → A.segments.IsSegment (P z) := by
    rintro ⟨i, b⟩
    cases b
    · exact A.segment_filter_head (F.allowed i) (hH i)
    · exact A.segment_filter_tail (F.allowed i) (hH i)
  have hs : ∀ z, P z ⊆ F.seg z.1 := by
    rintro ⟨i, b⟩
    cases b <;> exact Finset.filter_subset _ _
  have hd : Pairwise (fun z w => Disjoint (P z) (P w)) := by
    intro z w hzw
    by_cases h : z.1 = w.1
    · obtain ⟨i, b⟩ := z
      obtain ⟨j, c⟩ := w
      dsimp at h
      subst j
      apply Finset.disjoint_left.mpr
      intro v hv hw
      cases b <;> cases c
      · exact hzw rfl
      · simp only [P, Bool.false_eq_true, ↓reduceIte, Finset.mem_filter] at hv hw
        exact hw.2 hv.2
      · simp only [P, Bool.false_eq_true, ↓reduceIte, Finset.mem_filter] at hv hw
        exact hv.2 hw.2
      · exact hzw rfl
    · exact (F.disjoint h).mono (hs z) (hs w)
  have he := A.segments.test_energy_le_allow_empty P hp hd u
  simpa only [Fintype.sum_prod_type, Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte,
    add_comm] using he

/-- The explicit increase in the squared test after simultaneous splitting. -/
lemma split_gain_le (F : A.segments.Family) (H : Fin F.n → Set ι)
    (hH : ∀ i, A.Ancestral (H i)) (u : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ F.seg i, u v) ^ 2) +
      2 * (∑ i : Fin F.n, ((∑ v ∈ (F.seg i).filter (· ∉ H i), u v) ^ 2 -
        (∑ v ∈ F.seg i, u v) * (∑ v ∈ (F.seg i).filter (· ∉ H i), u v))) ≤
        (A.segments.primalSeminorm u) ^ 2 := by
  classical
  have he := A.split_energy_le F H hH u
  have hp (i : Fin F.n) :
      (∑ v ∈ (F.seg i).filter (· ∈ H i), u v) +
      (∑ v ∈ (F.seg i).filter (· ∉ H i), u v) = ∑ v ∈ F.seg i, u v := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : v ∈ H i <;> simp [h]
  convert he using 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hp i]
  ring

lemma gates_eq_of_le {H : Set ι} {g h : ι} (hg : A.Gate H g)
    (hh : A.Gate H h) (hgh : g ≤ h) : g = h := by
  by_contra hne
  exact hg.1 (hh.2 g (lt_of_le_of_ne hgh hne))

lemma gates_eq_of_common_upper {H : Set ι} {g h v : ι} (hg : A.Gate H g)
    (hh : A.Gate H h) (hgv : g ≤ v) (hhv : h ≤ v) : g = h := by
  rcases A.predecessors_total hgv hhv with h | h
  · exact A.gates_eq_of_le hg hh h
  · exact (A.gates_eq_of_le hh hg h).symm

lemma gate_unique_in_segment {H : Set ι} {S : Finset ι}
    (hS : A.segments.IsSegment S) {g h : ι} (hg : A.Gate H g)
    (hh : A.Gate H h) (hgS : g ∈ S) (hhS : h ∈ S) : g = h := by
  rcases A.interval_chain hS g hgS h hhS with h | h
  · exact A.gates_eq_of_le hg hh h
  · exact (A.gates_eq_of_le hh hg h).symm

lemma exists_gate_le {H : Set ι} {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    {v : ι} (hvK : v ∈ K) (hvH : v ∉ H) :
    ∃ g ∈ K, A.Gate H g ∧ g ≤ v := by
  classical
  let S := K.filter (fun a => a ≤ v ∧ a ∉ H)
  have hvS : v ∈ S := by simp [S, hvK, hvH]
  obtain ⟨g, hg, hmin⟩ := Finset.exists_minimal ⟨v, hvS⟩
  have hgK := (Finset.mem_filter.mp hg).1
  have hgv := (Finset.mem_filter.mp hg).2.1
  have hgH := (Finset.mem_filter.mp hg).2.2
  refine ⟨g, hgK, ⟨hgH, ?_⟩, hgv⟩
  intro a hag
  by_contra haH
  have haS : a ∈ S := by
    exact Finset.mem_filter.mpr ⟨hK hag.le hgK, hag.le.trans hgv, haH⟩
  exact (not_le_of_gt hag) (hmin haS hag.le)

lemma first_spec (F : A.segments.Family) (i : Fin F.n) :
    ∃ b, A.first F i ≤ b ∧ ∀ v, v ∈ F.seg i ↔ A.first F i ≤ v ∧ v ≤ b :=
  Classical.choose_spec (F.allowed i)

lemma first_le_of_mem (F : A.segments.Family) (i : Fin F.n) {v : ι}
    (hv : v ∈ F.seg i) : A.first F i ≤ v := by
  obtain ⟨b, _, hm⟩ := A.first_spec F i
  exact ((hm v).mp hv).1

/-- Two heads through a common exterior vertex are nested; cutting the longer
    at the shorter's first vertex preserves exactly the shorter head sum. -/
lemma crossing_cut_sum {H : Set ι} (hH : A.Ancestral H) (p : ι →₀ ℝ)
    (hp : ∀ v, v ∉ H → p v = 0) (F G : A.segments.Family)
    (i : Fin F.n) (j : Fin G.n) {g : ι} (hg : g ∉ H)
    (hgF : g ∈ F.seg i) (hgG : g ∈ G.seg j)
    (hfirst : A.first F i ≤ A.first G j) :
    (∑ v ∈ (F.seg i).filter (fun v => A.first G j ≤ v), p v) =
      ∑ v ∈ G.seg j, p v := by
  classical
  obtain ⟨b, hfb, hFm⟩ := A.first_spec F i
  obtain ⟨d, hgd, hGm⟩ := A.first_spec G j
  have hhead : ∀ S, A.segments.IsSegment S → g ∈ S → ∀ v ∈ S, v ∈ H → v ≤ g := by
    intro S hS hgS v hv hvH
    rcases A.interval_chain hS v hv g hgS with h | h
    · exact h
    · exact False.elim (hg (hH h hvH))
  have he : ((F.seg i).filter (fun v => A.first G j ≤ v)).filter (· ∈ H) =
      (G.seg j).filter (· ∈ H) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hvF, hvfirst⟩, hvH⟩
      refine ⟨(hGm v).mpr ⟨hvfirst, ?_⟩, hvH⟩
      exact (hhead _ (F.allowed i) hgF v hvF hvH).trans ((hGm g).mp hgG).2
    · rintro ⟨hvG, hvH⟩
      have hvg := hhead _ (G.allowed j) hgG v hvG hvH
      exact ⟨⟨(hFm v).mpr ⟨hfirst.trans ((hGm v).mp hvG).1,
        hvg.trans ((hFm g).mp hgF).2⟩, ((hGm v).mp hvG).1⟩, hvH⟩
  have hf (S : Finset ι) : (∑ v ∈ S.filter (· ∈ H), p v) = ∑ v ∈ S, p v := by
    apply Finset.sum_filter_of_ne
    intro v _ hpv
    by_contra hvH
    exact hpv (hp v hvH)
  rw [← hf ((F.seg i).filter (fun v => A.first G j ≤ v)), he, hf]

/-- Zero-extension along a finite injection preserves the finite sum. -/
lemma sum_extend_zero {κ ν : Type*} [Fintype κ] [Fintype ν]
    (e : κ ↪ ν) (f : κ → ℝ) :
    (∑ i, Function.extend e f (fun _ => 0) i) = ∑ a, f a := by
  classical
  let I := Finset.univ.image e
  have hz : ∀ i ∈ Finset.univ, i ∉ I → Function.extend e f (fun _ => 0) i = 0 := by
    intro i _ hi
    apply Function.extend_apply'
    simpa [I] using hi
  rw [← Finset.sum_subset (Finset.subset_univ I) hz,
    Finset.sum_image (fun _ _ _ _ h => e.injective h)]
  apply Finset.sum_congr rfl
  intro a _
  exact e.injective.extend_apply _ _ _

/-- Simultaneous splitting restricted to any injected list of original segments. -/
lemma matched_split_gain_le {κ : Type*} [Fintype κ]
    (F : A.segments.Family) (e : κ ↪ Fin F.n) (c : κ → ι) (p : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ F.seg i, p v) ^ 2) +
      2 * (∑ a, ((∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v) ^ 2 -
        (∑ v ∈ F.seg (e a), p v) *
          (∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v))) ≤
      (A.segments.primalSeminorm p) ^ 2 := by
  classical
  let H : Fin F.n → Set ι := Function.extend e (fun a => {v | ¬ c a ≤ v}) (fun _ => Set.univ)
  have he (a : κ) : H (e a) = {v | ¬ c a ≤ v} := e.injective.extend_apply _ _ _
  have hout (i : Fin F.n) (hi : ¬ ∃ a, e a = i) : H i = Set.univ :=
    Function.extend_apply' _ _ _ hi
  have hH : ∀ i, A.Ancestral (H i) := by
    intro i
    by_cases hi : ∃ a, e a = i
    · obtain ⟨a, rfl⟩ := hi
      rw [he]
      exact A.ancestral_not_above (c a)
    · rw [hout i hi]
      intro a b _ _
      trivial
  have hb := A.split_gain_le F H hH p
  let q : κ → ℝ := fun a =>
    (∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v) ^ 2 -
      (∑ v ∈ F.seg (e a), p v) *
        (∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v)
  have hid : (fun i => (∑ v ∈ (F.seg i).filter (· ∉ H i), p v) ^ 2 -
      (∑ v ∈ F.seg i, p v) * (∑ v ∈ (F.seg i).filter (· ∉ H i), p v)) =
        Function.extend e q (fun _ => 0) := by
    funext i
    by_cases hi : ∃ a, e a = i
    · obtain ⟨a, rfl⟩ := hi
      rw [he, e.injective.extend_apply]
      simp [q]
    · rw [hout i hi, Function.extend_apply' _ _ _ hi]
      simp
  rw [hid, sum_extend_zero] at hb
  exact hb

/-- Opposite head sums, matched injectively in both families, spend only the
    combined testing deficits. This is the simultaneous boundary cancellation. -/
lemma opposite_matching_le {κ : Type*} [Fintype κ]
    {H : Set ι} (hH : A.Ancestral H) (p : ι →₀ ℝ)
    (hp : ∀ v, v ∉ H → p v = 0) (F G : A.segments.Family)
    (eF : κ ↪ Fin F.n) (eG : κ ↪ Fin G.n) (g : κ → ι)
    (hgH : ∀ a, g a ∉ H) (hgF : ∀ a, g a ∈ F.seg (eF a))
    (hgG : ∀ a, g a ∈ G.seg (eG a))
    (hopp : ∀ a, (∑ v ∈ F.seg (eF a), p v) * (∑ v ∈ G.seg (eG a), p v) < 0) :
    2 * (∑ a, |(∑ v ∈ F.seg (eF a), p v) * (∑ v ∈ G.seg (eG a), p v)|) ≤
      ((A.segments.primalSeminorm p) ^ 2 - ∑ i, (∑ v ∈ F.seg i, p v) ^ 2) +
      ((A.segments.primalSeminorm p) ^ 2 - ∑ j, (∑ v ∈ G.seg j, p v) ^ 2) := by
  classical
  let P : κ → Prop := fun a => A.first F (eF a) ≤ A.first G (eG a)
  let L := {a : κ // P a}
  let U := {a : κ // ¬ P a}
  let eL : L ↪ Fin F.n := ⟨fun a => eF a.val,
    fun a b h => Subtype.ext (eF.injective h)⟩
  let eU : U ↪ Fin G.n := ⟨fun a => eG a.val,
    fun a b h => Subtype.ext (eG.injective h)⟩
  have hcutL (a : L) :
      (∑ v ∈ (F.seg (eL a)).filter (fun v => A.first G (eG a.val) ≤ v), p v) =
        ∑ v ∈ G.seg (eG a.val), p v :=
    A.crossing_cut_sum hH p hp F G (eF a.val) (eG a.val)
      (hgH a.val) (hgF a.val) (hgG a.val) a.property
  have hcutU (a : U) :
      (∑ v ∈ (G.seg (eU a)).filter (fun v => A.first F (eF a.val) ≤ v), p v) =
        ∑ v ∈ F.seg (eF a.val), p v := by
    have hfirst : A.first G (eG a.val) ≤ A.first F (eF a.val) := by
      rcases A.predecessors_total (A.first_le_of_mem F _ (hgF a.val))
        (A.first_le_of_mem G _ (hgG a.val)) with h | h
      · exact False.elim (a.property h)
      · exact h
    exact A.crossing_cut_sum hH p hp G F (eG a.val) (eF a.val)
      (hgH a.val) (hgG a.val) (hgF a.val) hfirst
  have hF := A.matched_split_gain_le F eL (fun a => A.first G (eG a.val)) p
  have hG := A.matched_split_gain_le G eU (fun a => A.first F (eF a.val)) p
  simp_rw [hcutL] at hF
  simp_rw [hcutU] at hG
  have hL : (∑ a : L, |(∑ v ∈ F.seg (eF a.val), p v) *
      (∑ v ∈ G.seg (eG a.val), p v)|) ≤
      ∑ a : L, ((∑ v ∈ G.seg (eG a.val), p v) ^ 2 -
        (∑ v ∈ F.seg (eL a), p v) * (∑ v ∈ G.seg (eG a.val), p v)) := by
    apply Finset.sum_le_sum
    intro a _
    rw [abs_of_neg (hopp a.val)]
    change -( (∑ v ∈ F.seg (eF a.val), p v) * (∑ v ∈ G.seg (eG a.val), p v)) ≤
      (∑ v ∈ G.seg (eG a.val), p v) ^ 2 -
        (∑ v ∈ F.seg (eF a.val), p v) * (∑ v ∈ G.seg (eG a.val), p v)
    nlinarith [sq_nonneg (∑ v ∈ G.seg (eG a.val), p v)]
  have hU : (∑ a : U, |(∑ v ∈ F.seg (eF a.val), p v) *
      (∑ v ∈ G.seg (eG a.val), p v)|) ≤
      ∑ a : U, ((∑ v ∈ F.seg (eF a.val), p v) ^ 2 -
        (∑ v ∈ G.seg (eU a), p v) * (∑ v ∈ F.seg (eF a.val), p v)) := by
    apply Finset.sum_le_sum
    intro a _
    rw [abs_of_neg (hopp a.val)]
    change -( (∑ v ∈ F.seg (eF a.val), p v) * (∑ v ∈ G.seg (eG a.val), p v)) ≤
      (∑ v ∈ F.seg (eF a.val), p v) ^ 2 -
        (∑ v ∈ G.seg (eG a.val), p v) * (∑ v ∈ F.seg (eF a.val), p v)
    nlinarith [sq_nonneg (∑ v ∈ F.seg (eF a.val), p v)]
  have hsum := Fintype.sum_subtype_add_sum_subtype P (fun a =>
    |(∑ v ∈ F.seg (eF a), p v) * (∑ v ∈ G.seg (eG a), p v)|)
  change (∑ a : L, _) + (∑ a : U, _) = _ at hsum
  linarith

lemma boundaryCoeff_eq (F : A.segments.Family) (p : ι →₀ ℝ)
    (i : Fin F.n) {g : ι} (hg : g ∈ F.seg i) :
    A.boundaryCoeff F p g = ∑ v ∈ F.seg i, p v := by
  classical
  rw [boundaryCoeff, Finset.sum_eq_single i]
  · simp [hg]
  · intro j _ hji
    have hj : g ∉ F.seg j := fun h => Finset.disjoint_left.mp (F.disjoint hji) h hg
    simp [hj]
  · simp

lemma boundaryCoeff_nonzero_mem (F : A.segments.Family) (p : ι →₀ ℝ)
    {g : ι} (h : A.boundaryCoeff F p g ≠ 0) : ∃ i, g ∈ F.seg i := by
  classical
  by_contra hn
  have hm : ∀ i, g ∉ F.seg i := by simpa using hn
  exact h (by simp [boundaryCoeff, hm])

/-- Exact two-family opposite-crossing estimate, written without a sign-filter
    so that it can be averaged over independent finite endpoint laws. -/
lemma opposite_crossing_le {κ : Type*} [Fintype κ]
    {H : Set ι} (hH : A.Ancestral H) (p : ι →₀ ℝ)
    (hp : ∀ v, v ∉ H → p v = 0) (F G : A.segments.Family)
    (gate : κ ↪ ι) (hgate : ∀ a, A.Gate H (gate a)) :
    (∑ a, (|A.boundaryCoeff F p (gate a)| * |A.boundaryCoeff G p (gate a)| -
      A.boundaryCoeff F p (gate a) * A.boundaryCoeff G p (gate a))) ≤
      ((A.segments.primalSeminorm p) ^ 2 - ∑ i, (∑ v ∈ F.seg i, p v) ^ 2) +
      ((A.segments.primalSeminorm p) ^ 2 - ∑ j, (∑ v ∈ G.seg j, p v) ^ 2) := by
  classical
  let P : κ → Prop := fun a => A.boundaryCoeff F p (gate a) *
    A.boundaryCoeff G p (gate a) < 0
  let M := {a : κ // P a}
  have hnF (a : M) : A.boundaryCoeff F p (gate a.val) ≠ 0 := by
    intro he
    have := a.property
    change A.boundaryCoeff F p (gate a.val) * A.boundaryCoeff G p (gate a.val) < 0 at this
    simp [he] at this
  have hnG (a : M) : A.boundaryCoeff G p (gate a.val) ≠ 0 := by
    intro he
    have := a.property
    change A.boundaryCoeff F p (gate a.val) * A.boundaryCoeff G p (gate a.val) < 0 at this
    simp [he] at this
  choose iF hiF using fun a : M => A.boundaryCoeff_nonzero_mem F p (hnF a)
  choose iG hiG using fun a : M => A.boundaryCoeff_nonzero_mem G p (hnG a)
  have hiFinj : Function.Injective iF := by
    intro a b hab
    apply Subtype.ext
    apply gate.injective
    exact A.gate_unique_in_segment (F.allowed (iF a)) (hgate a.val) (hgate b.val)
      (hiF a) (by rw [hab]; exact hiF b)
  have hiGinj : Function.Injective iG := by
    intro a b hab
    apply Subtype.ext
    apply gate.injective
    exact A.gate_unique_in_segment (G.allowed (iG a)) (hgate a.val) (hgate b.val)
      (hiG a) (by rw [hab]; exact hiG b)
  have hbF (a : M) := A.boundaryCoeff_eq F p (iF a) (hiF a)
  have hbG (a : M) := A.boundaryCoeff_eq G p (iG a) (hiG a)
  have hb := A.opposite_matching_le hH p hp F G ⟨iF, hiFinj⟩ ⟨iG, hiGinj⟩
    (fun a => gate a.val) (fun a => (hgate a.val).1) hiF hiG (by
      intro a
      change (∑ v ∈ F.seg (iF a), p v) * (∑ v ∈ G.seg (iG a), p v) < 0
      rw [← hbF, ← hbG]
      exact a.property)
  simp only [Function.Embedding.coeFn_mk, ← hbF, ← hbG] at hb
  let f : κ → ℝ := fun a => |A.boundaryCoeff F p (gate a)| *
    |A.boundaryCoeff G p (gate a)| - A.boundaryCoeff F p (gate a) * A.boundaryCoeff G p (gate a)
  have hzero : (∑ a : {a : κ // ¬ P a}, f a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    dsimp [f]
    rw [← abs_mul, abs_of_nonneg (le_of_not_gt a.property), sub_self]
  have heq : (∑ a : M, f a.val) =
      2 * ∑ a : M, |A.boundaryCoeff F p (gate a.val) * A.boundaryCoeff G p (gate a.val)| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [f]
    rw [← abs_mul, abs_of_neg a.property]
    ring
  have hs := Fintype.sum_subtype_add_sum_subtype P f
  rw [hzero, add_zero, heq] at hs
  simpa only [hs] using hb

lemma gate_coefficient_energy {κ : Type*} [Fintype κ] {H : Set ι}
    (F : A.segments.Family) (a : Fin F.n → ℝ)
    (gate : κ ↪ ι) (hg : ∀ g, A.Gate H (gate g)) :
    (∑ g, (A.segments.combine F.seg a (A.segments.unitVector (gate g))) ^ 2) ≤
      ∑ i, a i ^ 2 := by
  classical
  let P : κ → Prop := fun g => ∃ i, gate g ∈ F.seg i
  let M := {g : κ // P g}
  choose idx hidx using fun g : M => g.property
  have hinj : Function.Injective idx := by
    intro g h he
    apply Subtype.ext
    apply gate.injective
    exact A.gate_unique_in_segment (F.allowed (idx g)) (hg g.val) (hg h.val)
      (hidx g) (by rw [he]; exact hidx h)
  have hz : (∑ g : {g : κ // ¬ P g},
      (A.segments.combine F.seg a (A.segments.unitVector (gate g.val))) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro g _
    rw [SegmentSystem.combine_unit]
    have hgn : ∀ i, gate g.val ∉ F.seg i := by simpa only [P, not_exists] using g.property
    simp only [hgn, ↓reduceIte, Finset.sum_const_zero, zero_pow (by norm_num : 2 ≠ 0)]
  have he := Fintype.sum_subtype_add_sum_subtype P
    (fun g => (A.segments.combine F.seg a (A.segments.unitVector (gate g))) ^ 2)
  rw [hz, add_zero] at he
  rw [← he]
  calc
    _ = ∑ g : M, a (idx g) ^ 2 := by
      apply Finset.sum_congr rfl
      intro g _
      rw [A.segments.combine_unit_of_mem F a (idx g) (hidx g)]
    _ = ∑ i ∈ Finset.univ.image idx, a i ^ 2 :=
      (Finset.sum_image (s := Finset.univ) (f := fun i : Fin F.n => a i ^ 2)
        (fun _ _ _ _ h => hinj h)).symm
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun i => sq_nonneg _)

lemma tailAt_eq (F : A.segments.Family) (H : Finset ι)
    (i : Fin F.n) {g : ι} (hg : g ∈ F.seg i) :
    A.tailAt F H g = (F.seg i).filter (· ∉ H) := by
  classical
  have h : ∃ i, g ∈ F.seg i := ⟨i,hg⟩
  have he : h.choose = i := by
    by_contra hn
    exact Finset.disjoint_left.mp (F.disjoint hn) h.choose_spec hg
  simp only [tailAt, dite_eq_left h]
  rw [he]

lemma tailAt_mem {F : A.segments.Family} {H : Finset ι} {g v : ι}
    (hv : v ∈ A.tailAt F H g) : ∃ i, g ∈ F.seg i ∧ v ∈ F.seg i ∧ v ∉ H := by
  classical
  unfold tailAt at hv
  split_ifs at hv with h
  · exact ⟨h.choose, h.choose_spec, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
  · simp at hv

lemma tailAt_outside {F : A.segments.Family} {H : Finset ι} {g v : ι}
    (hv : v ∈ A.tailAt F H g) : v ∉ H := (A.tailAt_mem hv).choose_spec.2.2

lemma tailAt_allowed (F : A.segments.Family) {H : Finset ι}
    (hH : A.Ancestral (H : Set ι)) (g : ι) (hne : (A.tailAt F H g).Nonempty) :
    A.segments.IsSegment (A.tailAt F H g) := by
  classical
  obtain ⟨v,hv⟩ := hne
  obtain ⟨i, hgi, _, _⟩ := A.tailAt_mem hv
  rw [A.tailAt_eq F H i hgi] at hv ⊢
  convert A.segment_filter_tail (F.allowed i) hH ?_ using 1
  · ext w
    simp only [Finset.mem_filter, Finset.mem_coe]
  · simpa only [Finset.filter_nonempty_iff, Finset.mem_coe] using
      (show ((F.seg i).filter (· ∉ H)).Nonempty from ⟨v,hv⟩)

lemma tailAt_cone {F : A.segments.Family} {H : Finset ι} {g v : ι}
    (hg : A.Gate (H : Set ι) g) (hv : v ∈ A.tailAt F H g) : g ≤ v := by
  obtain ⟨i,hgi,hvi,hvH⟩ := A.tailAt_mem hv
  rcases A.interval_chain (F.allowed i) g hgi v hvi with h | h
  · exact h
  · by_contra hn
    have hvne : v ≠ g := fun he => hn (he ▸ le_rfl)
    exact hvH (hg.2 v (lt_of_le_of_ne h hvne))

lemma gate_on_nonzero_segment {H K : Finset ι} (hH : A.Ancestral (H : Set ι))
    (hK : A.Ancestral (K : Set ι)) (F : A.segments.Family)
    (hFK : ∀ i, F.seg i ⊆ K) (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0)
    (i : Fin F.n) (hi : (∑ v ∈ F.seg i, p v) ≠ 0) {v : ι}
    (hvi : v ∈ F.seg i) (hvH : v ∉ H) :
    ∃ g ∈ K, A.Gate (H : Set ι) g ∧ g ∈ F.seg i := by
  classical
  obtain ⟨w, hwi, hpw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  have hwH : w ∈ H := by by_contra hn; exact hpw (hp w hn)
  have hfH : A.first F i ∈ H := hH (A.first_le_of_mem F i hwi) hwH
  obtain ⟨g,hgK,hg,hgv⟩ := A.exists_gate_le hK (hFK i hvi) hvH
  obtain ⟨b,hfb,hm⟩ := A.first_spec F i
  have hfg : A.first F i ≤ g := by
    rcases A.predecessors_total (A.first_le_of_mem F i hvi) hgv with h | h
    · exact h
    · exact False.elim (hg.1 (hH h hfH))
  exact ⟨g,hgK,hg,(hm g).mpr ⟨hfg,hgv.trans ((hm v).mp hvi).2⟩⟩

lemma mem_gateSet {H K : Finset ι} {g : ι} :
    g ∈ A.gateSet H K ↔ g ∈ K ∧ A.Gate (H : Set ι) g := Finset.mem_filter

/-- Replacement coefficients have no wholly exterior contribution. Their entire
    tail is the sum of their crossing tails at the finitely represented gates. -/
lemma replaced_tail_eq {H K : Finset ι} (hH : A.Ancestral (H : Set ι))
    (hK : A.Ancestral (K : Set ι)) (F : A.segments.Family)
    (hFK : ∀ i, F.seg i ⊆ K) (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0) :
    A.segments.tailDual H (A.segments.combine F.seg (fun i => ∑ v ∈ F.seg i, p v)) =
      A.segments.combine (fun g : A.gateSet H K => A.tailAt F H g.val)
        (fun g : A.gateSet H K => A.boundaryCoeff F p g.val) := by
  classical
  apply A.segments.dual_ext
  intro v
  rw [SegmentSystem.tailDual_apply, sub_apply, SegmentSystem.headDual_unit]
  by_cases hvH : v ∈ H
  · rw [ite_eq_left hvH, sub_self, SegmentSystem.combine_unit]
    symm
    apply Finset.sum_eq_zero
    intro g _
    rw [ite_eq_right (fun hv => A.tailAt_outside hv hvH)]
  rw [ite_eq_right hvH, sub_zero]
  by_cases hhas : ∃ i, v ∈ F.seg i
  · obtain ⟨i,hvi⟩ := hhas
    rw [A.segments.combine_unit_of_mem F _ i hvi, SegmentSystem.combine_unit]
    by_cases hi : (∑ w ∈ F.seg i, p w) = 0
    · rw [hi]
      symm
      apply Finset.sum_eq_zero
      intro g _
      split_ifs with hv
      · obtain ⟨j,hgj,hvj,_⟩ := A.tailAt_mem hv
        have hji : j = i := by
          by_contra hn
          exact Finset.disjoint_left.mp (F.disjoint hn) hvj hvi
        subst j
        rwa [A.boundaryCoeff_eq F p i hgj]
      · rfl
    obtain ⟨g,hgK,hg,hgi⟩ := A.gate_on_nonzero_segment hH hK F hFK p hp i hi hvi hvH
    let g' : A.gateSet H K := ⟨g, A.mem_gateSet.mpr ⟨hgK,hg⟩⟩
    have hvJ : v ∈ A.tailAt F H g := by
      rw [A.tailAt_eq F H i hgi]
      exact Finset.mem_filter.mpr ⟨hvi,hvH⟩
    rw [Finset.sum_eq_single g']
    · rw [ite_eq_left hvJ, A.boundaryCoeff_eq F p i hgi]
    · intro h _ hh
      rw [ite_eq_right]
      intro hv
      have he : h.val = g := A.gates_eq_of_common_upper
        (A.mem_gateSet.mp h.property).2 hg
        (A.tailAt_cone (A.mem_gateSet.mp h.property).2 hv) (A.tailAt_cone hg hvJ)
      exact hh (Subtype.ext he)
    · simp
  · have hn : ∀ i, v ∉ F.seg i := by simpa only [not_exists] using hhas
    rw [SegmentSystem.combine_unit, SegmentSystem.combine_unit]
    have hz : (∑ i, if v ∈ F.seg i then (∑ w ∈ F.seg i,p w) else 0) = 0 := by simp [hn]
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro g _
    rw [ite_eq_right]
    intro hv
    obtain ⟨i,_,hvi,_⟩ := A.tailAt_mem hv
    exact hn i hvi

lemma primal_filter_le {H : Set ι} (hH : A.Ancestral H) (u : ι →₀ ℝ) :
    A.segments.primalSeminorm (u.filter (· ∈ H)) ≤ A.segments.primalSeminorm u := by
  classical
  rw [SegmentSystem.primalSeminorm,
    Seminorm.iSup_apply A.segments.families_bddAbove]
  apply ciSup_le
  intro F
  have h := A.segments.test_energy_le_allow_empty
    (fun i => (F.seg i).filter (· ∈ H))
    (fun i hne => A.segment_filter_head (F.allowed i) hH hne)
    (fun i j hij => (F.disjoint hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)) u
  have he : ‖F.test (u.filter (· ∈ H))‖ ^ 2 =
      ∑ i, (∑ v ∈ (F.seg i).filter (· ∈ H), u v) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [SegmentSystem.Family.test, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
    congr 1
    simp [Finsupp.filter_apply, Finset.sum_filter]
  rw [← he] at h
  exact (sq_le_sq₀ (norm_nonneg _) (apply_nonneg _ _)).mp h

lemma primal_filter_tail_le {H : Set ι} (hH : A.Ancestral H) (u : ι →₀ ℝ) :
    A.segments.primalSeminorm (u.filter (· ∉ H)) ≤ A.segments.primalSeminorm u := by
  classical
  rw [SegmentSystem.primalSeminorm,
    Seminorm.iSup_apply A.segments.families_bddAbove]
  apply ciSup_le
  intro F
  have h := A.segments.test_energy_le_allow_empty
    (fun i => (F.seg i).filter (· ∉ H))
    (fun i hne => A.segment_filter_tail (F.allowed i) hH hne)
    (fun i j hij => (F.disjoint hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)) u
  have he : ‖F.test (u.filter (· ∉ H))‖ ^ 2 =
      ∑ i, (∑ v ∈ (F.seg i).filter (· ∉ H), u v) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [SegmentSystem.Family.test, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
    congr 1
    simp [Finsupp.filter_apply, Finset.sum_filter]
  rw [← he] at h
  exact (sq_le_sq₀ (norm_nonneg _) (apply_nonneg _ _)).mp h

/-- Restricting any test family to a finite ancestral set gives one of the
    finitely many local families, with exactly the same energy for supported tests. -/
lemma localize_family_energy {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (F : A.segments.Family) (p : ι →₀ ℝ) (hp : ∀ v, v ∉ K → p v = 0) :
    ∃ G : A.segments.LocalFamily K,
      (∑ i, (∑ v ∈ F.seg i, p v) ^ 2) =
        ∑ S : A.segments.LocalIndex G, (∑ v ∈ S.val, p v) ^ 2 := by
  classical
  let P : Fin F.n → Prop := fun i => ((F.seg i).filter (· ∈ K)).Nonempty
  let I := {i : Fin F.n // P i}
  let f : I → Finset ι := fun i => (F.seg i.val).filter (· ∈ K)
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    by_contra hne
    obtain ⟨v, hv⟩ := i.property
    have hvj : v ∈ f j := by rw [← he]; exact hv
    exact Finset.disjoint_left.mp (F.disjoint hne)
      (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hvj).1
  let Gset := Finset.univ.image f
  have hGK : Gset ∈ K.powerset.powerset := by
    apply Finset.mem_powerset.mpr
    intro S hS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    apply Finset.mem_powerset.mpr
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hGa : ∀ S ∈ Gset, A.segments.IsSegment S := by
    intro S hS
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    convert A.segment_filter_head (F.allowed i.val) hK (by
      have hi := i.property
      change ((F.seg i.val).filter (fun v => v ∈ K)).Nonempty at hi
      simpa only [Finset.filter_nonempty_iff, Finset.mem_coe] using hi) using 1
    ext v
    simp only [f, Finset.mem_filter, Finset.mem_coe]

  have hGd : (Gset : Set (Finset ι)).Pairwise Disjoint := by
    intro S hS U hU hSU
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hU
    have hij : i.val ≠ j.val := fun h => hSU (congrArg f (Subtype.ext h))
    exact (F.disjoint hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  let G : A.segments.LocalFamily K := ⟨Gset, hGK, hGa, hGd⟩
  refine ⟨G, ?_⟩
  have hsum (i : Fin F.n) : (∑ v ∈ F.seg i, p v) =
      ∑ v ∈ (F.seg i).filter (· ∈ K), p v := by
    symm
    apply Finset.sum_filter_of_ne
    intro v _ hv
    by_contra hn
    exact hv (hp v hn)
  have hzero : (∑ i : {i : Fin F.n // ¬ P i},
      (∑ v ∈ (F.seg i.val).filter (· ∈ K), p v) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : (F.seg i.val).filter (· ∈ K) = ∅ := Finset.not_nonempty_iff_eq_empty.mp i.property
    rw [hi]
    simp
  have he := Fintype.sum_subtype_add_sum_subtype P
    (fun i => (∑ v ∈ (F.seg i).filter (· ∈ K), p v) ^ 2)
  rw [hzero, add_zero] at he
  simp_rw [hsum]
  rw [← he]
  change (∑ i : I, (∑ v ∈ f i, p v) ^ 2) =
    ∑ S : ↥Gset, (∑ v ∈ S.val, p v) ^ 2
  calc
    _ = ∑ S ∈ Gset, (∑ v ∈ S, p v) ^ 2 :=
      (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ = _ := (Finset.sum_coe_sort Gset (fun S => (∑ v ∈ S, p v) ^ 2)).symm

lemma primal_le_of_local_energies {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (p : ι →₀ ℝ) (hp : ∀ v, v ∉ K → p v = 0) {M : ℝ} (hM : 0 ≤ M)
    (hlocal : ∀ G : A.segments.LocalFamily K,
      (∑ S : A.segments.LocalIndex G, (∑ v ∈ S.val, p v) ^ 2) ≤ M ^ 2) :
    A.segments.primalSeminorm p ≤ M := by
  rw [SegmentSystem.primalSeminorm, Seminorm.iSup_apply A.segments.families_bddAbove]
  apply ciSup_le
  intro F
  obtain ⟨G, he⟩ := A.localize_family_energy hK F p hp
  have h := hlocal G
  rw [← he] at h
  have hnorm : ‖F.test p‖ ^ 2 = ∑ i, (∑ v ∈ F.seg i, p v) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [SegmentSystem.Family.test_apply, Real.norm_eq_abs, sq_abs]
  rw [← hnorm] at h
  exact (sq_le_sq₀ (norm_nonneg _) hM).mp h

/-- Finite atomic-ball formula: exact inherited dual restrictions, derived by
    finite-dimensional separation rather than assumed as model data. -/
lemma finite_atomic_representation {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (x : A.segments.Dual) (hx : ‖x‖ ≤ 1) :
    ∃ c ∈ A.segments.coefficientBall K 1,
      A.segments.totalMap K c = fun v : K => x (A.segments.unitVector v.val) := by
  classical
  let C := A.segments.totalMap K '' A.segments.coefficientBall K 1
  let z : A.segments.Coordinates K := fun v => x (A.segments.unitVector v.val)
  suffices z ∈ C by exact this
  by_contra hn
  have hCc : Convex ℝ C := (A.segments.coefficientBall_convex K 1).linear_image _
  have hCk : IsCompact C := (A.segments.coefficientBall_compact K (by norm_num : (0:ℝ) ≤ 1)).image
    (A.segments.totalMap K).continuous_of_finiteDimensional
  obtain ⟨f, u, hfu, huz⟩ := geometric_hahn_banach_closed_point hCc hCk.isClosed hn
  have hzC : (0 : A.segments.Coordinates K) ∈ C := by
    refine ⟨0, ?_, map_zero _⟩
    change (∑ F : A.segments.LocalFamily K, ‖(0 : A.segments.Coefficients K) F‖) ≤ 1
    simp
  have hu : 0 < u := by simpa only [map_zero] using hfu 0 hzC
  let p := A.segments.coordinateTest K (fun w => f (Pi.single w 1))
  have hp : ∀ v, v ∉ K → p v = 0 := by
    intro v hv
    exact A.segments.coordinateTest_not_mem K _ hv
  have hpbound : A.segments.primalSeminorm p ≤ u := by
    apply A.primal_le_of_local_energies hK p hp hu.le
    intro F
    apply A.segments.local_energy_le_of_functional_bound F f hu.le
    intro a ha
    apply (hfu _ ?_).le
    refine ⟨Pi.single F a, A.segments.single_mem_coefficientBall K F a ha, ?_⟩
    exact A.segments.totalMap_single K F a
  have he : f z = x (A.segments.finiteEmbedding p) := by
    rw [A.segments.functional_pi_formula, A.segments.coordinateTest_pairing]
    apply Finset.sum_congr rfl
    intro v _
    exact mul_comm _ _
  have hle : f z ≤ u := by
    rw [he]
    calc
      x (A.segments.finiteEmbedding p) ≤ ‖x (A.segments.finiteEmbedding p)‖ := Real.le_norm_self _
      _ ≤ ‖x‖ * ‖A.segments.finiteEmbedding p‖ := x.le_opNorm _
      _ ≤ 1 * A.segments.primalSeminorm p := by
        rw [A.segments.finiteEmbedding_norm]
        exact mul_le_mul_of_nonneg_right hx (apply_nonneg _ _)
      _ ≤ u := by simpa using hpbound
  exact (not_lt_of_ge hle) huz

lemma finite_atomic_representation_radius {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (x : A.segments.Dual) {R : ℝ} (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) :
    ∃ c ∈ A.segments.coefficientBall K R,
      A.segments.totalMap K c = fun v : K => x (A.segments.unitVector v.val) := by
  classical
  rcases eq_or_lt_of_le hR with hR0 | hRpos
  · have hx0 : x = 0 := norm_eq_zero.mp (le_antisymm (by simpa [← hR0] using hx) (norm_nonneg _))
    refine ⟨0, ?_, ?_⟩
    · simp [SegmentSystem.coefficientBall, ← hR0]
    · rw [map_zero]
      ext v
      simp [hx0]
  have hxn : ‖R⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
    exact (inv_mul_le_iff₀ hRpos).mpr (by simpa using hx)
  obtain ⟨c, hc, hce⟩ := A.finite_atomic_representation hK (R⁻¹ • x) hxn
  refine ⟨R • c, ?_, ?_⟩
  · change (∑ F, ‖R • c F‖) ≤ R
    simp_rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hc hRpos.le).trans_eq (mul_one _)
  · rw [map_smul, hce]
    ext v
    simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hRpos.ne', one_mul]

lemma headPrimal_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (u : A.segments.JamesSpace) : ‖A.segments.headPrimal H u‖ ≤ ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [SegmentSystem.headPrimal_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    exact A.primal_filter_le hH u

lemma tailPrimal_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (u : A.segments.JamesSpace) : ‖u - A.segments.headPrimal H u‖ ≤ ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [SegmentSystem.headPrimal_coe, ← UniformSpace.Completion.coe_sub,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    rw [SegmentSystem.sub_filterPrimal, SegmentSystem.norm_eq_primal,
      SegmentSystem.norm_eq_primal, SegmentSystem.ofPrimal_filter]
    convert A.primal_filter_tail_le hH (A.segments.ofPrimal u) using 1
    congr 2

lemma headDual_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (x : A.segments.Dual) : ‖A.segments.headDual H x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  rw [SegmentSystem.headDual_apply_apply]
  exact (x.le_opNorm _).trans (mul_le_mul_of_nonneg_left (A.headPrimal_norm_le hH u)
    (norm_nonneg _))

lemma tailDual_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (x : A.segments.Dual) : ‖A.segments.tailDual H x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  rw [SegmentSystem.tailDual_apply_apply]
  exact (x.le_opNorm _).trans (mul_le_mul_of_nonneg_left (A.tailPrimal_norm_le hH u)
    (norm_nonneg _))

lemma replacement_error_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (F : A.segments.Family) (a b : Fin F.n → ℝ) :
    ‖A.segments.tailDual H (A.segments.combine F.seg a - A.segments.combine F.seg b)‖ ^ 2 ≤
      ∑ i, (a i - b i) ^ 2 := by
  have hV : 0 ≤ ∑ i,(a i-b i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc := A.tailDual_norm_le hH (A.segments.combine F.seg a - A.segments.combine F.seg b)
  rw [← SegmentSystem.combine_sub] at hc
  have ha := A.segments.norm_combine_le F.seg (a-b) (fun i _ => F.allowed i) F.disjoint
  have h := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 (hc.trans ha)
  simpa only [Pi.sub_apply, Real.sq_sqrt hV, SegmentSystem.combine_sub] using h

lemma replacement_error_gate {H : Finset ι} (F : A.segments.Family)
    (a : Fin F.n → ℝ) (q : ι →₀ ℝ) {g : ι} (hg : g ∉ H) :
    A.segments.tailDual H (A.segments.combine F.seg a -
      A.segments.combine F.seg (fun i => ∑ v ∈ F.seg i,q v)) (A.segments.unitVector g) =
      A.segments.combine F.seg a (A.segments.unitVector g) - A.boundaryCoeff F q g := by
  rw [SegmentSystem.tailDual_apply, sub_apply, SegmentSystem.headDual_unit, ite_eq_right hg,
    sub_zero, sub_apply]
  simp only [SegmentSystem.combine_unit, boundaryCoeff]

lemma replacement_cross (F : A.segments.Family) (a : Fin F.n → ℝ) (p : ι →₀ ℝ) (r : ℝ) :
    (∑ i, a i * (∑ v ∈ F.seg i,(r • p) v)) =
      r * A.segments.combine F.seg a (A.segments.finiteEmbedding p) := by
  rw [SegmentSystem.finiteEmbedding_apply, SegmentSystem.combine_coe]
  change (∑ i,a i*(∑ v ∈ F.seg i,(r • p) v)) = r*(∑ i,a i*(∑ v ∈ F.seg i,p v))
  simp_rw [Finsupp.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma replacement_mass_norm {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {H K : Finset ι} (hH : A.Ancestral (H : Set ι)) (hK : A.Ancestral (K : Set ι))
    (F : Ω → A.segments.Family) (hFK : ∀ ω i, (F ω).seg i ⊆ K)
    (q : ι →₀ ℝ) (hq : ∀ v,v ∉ H → q v=0)
    (w σ : Ω → ℝ) (hw : ∀ ω,0 ≤ w ω) (hσ : ∀ ω,|σ ω|=1) :
    ‖∑ ω,w ω • (σ ω • A.segments.tailDual H
      (A.segments.combine (F ω).seg (fun i => ∑ v ∈ (F ω).seg i,q v)))‖ ≤
      Real.sqrt (∑ g : A.gateSet H K, (∑ ω,w ω * |A.boundaryCoeff (F ω) q g.val|)^2) := by
  classical
  let gate : A.gateSet H K ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  have hg (g : A.gateSet H K) : A.Gate (H : Set ι) (gate g) :=
    (A.mem_gateSet.mp g.property).2
  have h := A.segments.norm_cone_mean_le
    (fun ω (g : A.gateSet H K) => A.tailAt (F ω) H g.val)
    (fun ω g => σ ω * A.boundaryCoeff (F ω) q g.val) w hw
    (fun ω g => A.tailAt_allowed (F ω) hH g.val) (by
      intro g h hgh ω ν
      apply Finset.disjoint_left.mpr
      intro v hvg hvh
      exact hgh (gate.injective (A.gates_eq_of_common_upper (hg g) (hg h)
        (A.tailAt_cone (hg g) hvg) (A.tailAt_cone (hg h) hvh))))
  simp only [abs_mul, hσ, one_mul] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [A.replaced_tail_eq hH hK (F ω) (hFK ω) q hq, SegmentSystem.combine_smul]

/-- The finite pooled coefficient/slack bound, before taking the supremum over
    head tests. No lens or convexity modulus is postulated for the space. -/
lemma pooled_tail_test {Ω : Type*} [Fintype Ω] {H K : Finset ι}
    (hH : A.Ancestral (H : Set ι)) (hK : A.Ancestral (K : Set ι))
    {R : ℝ} {x y : A.segments.Dual} (law : A.segments.BipolarLaw Ω R x y)
    (hFK : ∀ ω i,(law.atom ω).family.seg i ⊆ K)
    (hx : ∀ v,v ∉ H → x (A.segments.unitVector v)=0)
    (p : ι →₀ ℝ) (hp : ∀ v,v ∉ H → p v=0) (hpn : A.segments.primalSeminorm p ≤ 1) :
    ‖A.segments.tailDual H y‖ ≤
      2*Real.sqrt (R^2 - (x (A.segments.finiteEmbedding p))^2) := by
  classical
  have : Nonempty Ω := by
    by_contra hn
    have : IsEmpty Ω := not_nonempty_iff.mp hn
    have h := law.sum_one
    simp at h
  let r : ℝ := x (A.segments.finiteEmbedding p)
  let q : ι →₀ ℝ := r • p
  let F : Ω → A.segments.Family := fun ω => (law.atom ω).family
  let a : (ω : Ω) → Fin (F ω).n → ℝ := fun ω => (law.atom ω).coeff
  let β : (ω : Ω) → Fin (F ω).n → ℝ := fun ω i => ∑ v ∈ (F ω).seg i,q v
  let Ac : Ω → A.segments.Dual := fun ω => A.segments.combine (F ω).seg (β ω)
  let W : Ω → A.segments.Dual := fun ω =>
    A.segments.tailDual H ((law.atom ω).value - Ac ω)
  let V : Ω → ℝ := fun ω => ∑ i,(a ω i-β ω i)^2
  let L : Ω → ℝ := fun ω => r^2-∑ i,β ω i^2
  let η : ℝ := ∑ ω,law.weight ω*V ω
  let θ : ℝ := ∑ ω,law.weight ω*L ω
  have hq (v : ι) (hv : v ∉ H) : q v = 0 := by simp only [q,Finsupp.smul_apply,hp v hv,smul_zero]
  have hqn : A.segments.primalSeminorm q ≤ |r| := by
    dsimp [q]
    rw [map_smul_eq_mul, Real.norm_eq_abs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpn (abs_nonneg r)
  have hqn2 : (A.segments.primalSeminorm q)^2 ≤ r^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (apply_nonneg _ _) (abs_nonneg r)).2 hqn
  have hV (ω : Ω) : 0 ≤ V ω := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hL (ω : Ω) : 0 ≤ L ω := by
    apply sub_nonneg.mpr
    exact (A.segments.test_energy_le_allow_empty (F ω).seg
      (fun i _ => (F ω).allowed i) (F ω).disjoint q).trans hqn2
  have hη : 0 ≤ η := Finset.sum_nonneg (fun ω _ => mul_nonneg (law.nonneg ω) (hV ω))
  have hθ : 0 ≤ θ := Finset.sum_nonneg (fun ω _ => mul_nonneg (law.nonneg ω) (hL ω))
  have hcross : (∑ ω,law.weight ω*(∑ i,a ω i*β ω i)) = r^2 := by
    have hm := congrArg (fun z : A.segments.Dual => z (A.segments.finiteEmbedding p)) law.mean
    simp only [sum_apply, smul_apply, smul_eq_mul] at hm
    calc
      _ = r*(∑ ω,law.weight ω*(law.atom ω).value (A.segments.finiteEmbedding p)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        have hr := A.replacement_cross (F ω) (a ω) p r
        change (∑ i,a ω i*β ω i) = r*(law.atom ω).value (A.segments.finiteEmbedding p) at hr
        rw [hr]
        ring
      _ = r^2 := by rw [hm]; dsimp [r]; ring
  have hbudget : η+θ ≤ R^2-r^2 :=
    FiniteAverage.joint_budget law.weight law.nonneg law.sum_one (fun ω => Fin (F ω).n)
      a β (fun ω => (law.atom ω).energy_le) hcross
  have hWnorm (ω : Ω) : ‖W ω‖^2 ≤ V ω :=
    A.replacement_error_le hH (F ω) (a ω) (β ω)
  let gate : A.gateSet H K ↪ ι := ⟨Subtype.val,Subtype.val_injective⟩
  have hg (g : A.gateSet H K) : A.Gate (H : Set ι) (gate g) :=
    (A.mem_gateSet.mp g.property).2
  let b : Ω → A.gateSet H K → ℝ := fun ω g => A.boundaryCoeff (F ω) q g.val
  let e : Ω → A.gateSet H K → ℝ := fun ω g => W ω (A.segments.unitVector g.val)
  have he (ω : Ω) (g : A.gateSet H K) :
      e ω g = (law.atom ω).value (A.segments.unitVector g.val) - b ω g :=
    A.replacement_error_gate (F ω) (a ω) q (hg g).1
  have hgateEnergy (ω : Ω) : (∑ g,e ω g^2) ≤ V ω := by
    have heq (g : A.gateSet H K) : e ω g =
        A.segments.combine (F ω).seg (a ω-β ω) (A.segments.unitVector g.val) := by
      rw [SegmentSystem.combine_sub]
      rw [sub_apply]
      simpa only [SegmentSystem.Atom.value, SegmentSystem.combine_unit, b, β,
        boundaryCoeff, F, a] using he ω g
    simp_rw [heq]
    exact A.gate_coefficient_energy (F ω) (a ω-β ω) gate hg
  have hmean (g : A.gateSet H K) :
      (∑ ω,law.weight ω*b ω g) = -(∑ ω,law.weight ω*e ω g) := by
    have hm := congrArg (fun z : A.segments.Dual => z (A.segments.unitVector g.val)) law.mean
    simp only [sum_apply,smul_apply,smul_eq_mul,hx g.val (hg g).1] at hm
    have heq : (∑ ω,law.weight ω*b ω g)+(∑ ω,law.weight ω*e ω g) =
        ∑ ω,law.weight ω*(law.atom ω).value (A.segments.unitVector g.val) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      rw [he]
      ring
    rw [hm] at heq
    linarith
  have hopp (ω ν : Ω) : (∑ g,(|b ω g| * |b ν g|-b ω g*b ν g)) ≤ L ω+L ν := by
    have h := A.opposite_crossing_le hH q hq (F ω) (F ν) gate hg
    change (∑ g,(|b ω g| * |b ν g|-b ω g*b ν g)) ≤
      ((A.segments.primalSeminorm q)^2 - ∑ i,β ω i^2) +
      ((A.segments.primalSeminorm q)^2 - ∑ i,β ν i^2) at h
    exact h.trans (add_le_add (sub_le_sub_right hqn2 _) (sub_le_sub_right hqn2 _))
  have hmass : (∑ g,(∑ ω,law.weight ω* |b ω g|)^2) ≤ η+2*θ :=
    FiniteAverage.pooled_mass law.weight law.nonneg law.sum_one b e V L hmean hgateEnergy hopp
  have herr : ‖∑ ω,law.weight ω • (law.sign ω • W ω)‖ ≤ Real.sqrt η := by
    apply FiniteAverage.norm_mean_le_sqrt law.weight law.nonneg law.sum_one _ hη
    apply Finset.sum_le_sum
    intro ω _
    rw [norm_smul,Real.norm_eq_abs,law.abs_sign,one_mul]
    exact mul_le_mul_of_nonneg_left (hWnorm ω) (law.nonneg ω)
  have hrec : ‖∑ ω,law.weight ω • (law.sign ω • A.segments.tailDual H (Ac ω))‖ ≤
      Real.sqrt (η+2*θ) := by
    exact (A.replacement_mass_norm hH hK F hFK q hq law.weight law.sign law.nonneg law.abs_sign).trans
      (Real.sqrt_le_sqrt hmass)
  have hdec : A.segments.tailDual H y =
      (∑ ω,law.weight ω • (law.sign ω • W ω)) +
      (∑ ω,law.weight ω • (law.sign ω • A.segments.tailDual H (Ac ω))) := by
    conv_lhs => rw [← law.signed_mean]
    rw [map_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    simp only [map_smul, W, map_sub, smul_sub]
    module
  calc
    ‖A.segments.tailDual H y‖ ≤ Real.sqrt η+Real.sqrt (η+2*θ) := by
      rw [hdec]
      exact (norm_add_le _ _).trans (add_le_add herr hrec)
    _ ≤ 2*Real.sqrt (η+θ) := FiniteAverage.sqrt_pooled hη hθ
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbudget) (by norm_num)

/-- Pair the two exact finite atomic representations, retaining their common
    ancestral support and their actual endpoints. -/
lemma finite_lens_test {H K : Finset ι}
    (hH : A.Ancestral (H : Set ι)) (hK : A.Ancestral (K : Set ι)) (hHK : H ⊆ K)
    {R : ℝ} (hR : 0 < R) {x y : A.segments.Dual}
    (hx : ∀ v, v ∉ H → x (A.segments.unitVector v) = 0)
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R)
    (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0) (hpn : A.segments.primalSeminorm p ≤ 1) :
    ‖A.segments.tailDual H (A.segments.headDual K y)‖ ≤
      2*Real.sqrt (R^2 - (x (A.segments.finiteEmbedding p))^2) := by
  classical
  obtain ⟨cp,hcp,hcep⟩ := A.finite_atomic_representation_radius hK (x+y) hR.le hplus
  obtain ⟨cm,hcm,hcem⟩ := A.finite_atomic_representation_radius hK (x-y) hR.le hminus
  have hxK : A.segments.headDual K x = x :=
    A.segments.headDual_eq_self (fun v hv => hx v (fun h => hv (hHK h)))
  let Lp0 := A.segments.lawOfCoefficients (x+y) hR cp hcp hcep
  let Lm0 := A.segments.lawOfCoefficients (x-y) hR cm hcm hcem
  let Lp : A.segments.AtomLaw (Option (A.segments.LocalFamily K)) R
      (x+A.segments.headDual K y) :=
    { Lp0 with mean := by rw [Lp0.mean, map_add, hxK] }
  let Lm : A.segments.AtomLaw (Option (A.segments.LocalFamily K)) R
      (x-A.segments.headDual K y) :=
    { Lm0 with mean := by rw [Lm0.mean, map_sub, hxK] }
  apply A.pooled_tail_test hH hK (A.segments.pairLaws Lp Lm) _ hx p hp hpn
  apply A.segments.pairLaws_subset Lp Lm K
  · exact A.segments.lawOfCoefficients_subset (x+y) hR cp hcp hcep
  · exact A.segments.lawOfCoefficients_subset (x-y) hR cm hcm hcem

/-- Finite restrictions suffice for the full dual estimate: no shrinking or
    reflexivity hypothesis is needed for this intrinsic finite-head bound. -/
lemma intrinsic_tail_test
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {H : Finset ι} (hH : A.Ancestral (H : Set ι)) {R : ℝ} (hR : 0 < R)
    {x y : A.segments.Dual} (hx : ∀ v, v ∉ H → x (A.segments.unitVector v) = 0)
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R)
    (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0) (hpn : A.segments.primalSeminorm p ≤ 1) :
    ‖A.segments.tailDual H y‖ ≤
      2*Real.sqrt (R^2 - (x (A.segments.finiteEmbedding p))^2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  intro u
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    obtain ⟨K,hsub,hK⟩ := hfin (H ∪ (A.segments.ofPrimal u).support)
    have hHK : H ⊆ K := Finset.Subset.trans Finset.subset_union_left hsub
    have huK : (A.segments.ofPrimal u).support ⊆ K :=
      Finset.Subset.trans Finset.subset_union_right hsub
    have ht := A.finite_lens_test hH hK hHK hR hx hplus hminus p hp hpn
    calc
      _ = ‖A.segments.tailDual H (A.segments.headDual K y) (u : A.segments.JamesSpace)‖ := by
        rw [SegmentSystem.tailDual_headDual, A.segments.headDual_finite_apply _ u huK]
      _ ≤ ‖A.segments.tailDual H (A.segments.headDual K y)‖ * ‖(u : A.segments.JamesSpace)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)

lemma norm_center_le {x y : A.segments.Dual} {R : ℝ}
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R) : ‖x‖ ≤ R := by
  have h := (norm_add_le (x+y) (x-y)).trans (add_le_add hplus hminus)
  have he : (x+y)+(x-y) = (2:ℝ) • x := by module
  rw [he, norm_smul, Real.norm_eq_abs] at h
  norm_num at h
  linarith

lemma intrinsic_tail_sq
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {H : Finset ι} (hH : A.Ancestral (H : Set ι)) {R : ℝ} (hR : 0 ≤ R)
    {x y : A.segments.Dual} (hx : ∀ v, v ∉ H → x (A.segments.unitVector v) = 0)
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R) :
    ‖A.segments.tailDual H y‖^2 + 4*‖x‖^2 ≤ 4*R^2 := by
  have hxr := A.norm_center_le hplus hminus
  rcases eq_or_lt_of_le hR with hR0 | hRpos
  · have hx0 : x=0 := norm_eq_zero.mp (le_antisymm (by simpa [← hR0] using hxr) (norm_nonneg _))
    have hy0 : y=0 := norm_eq_zero.mp (le_antisymm (by simpa [← hR0,hx0] using hplus) (norm_nonneg _))
    simp [hx0,hy0,← hR0]
  let t := ‖A.segments.tailDual H y‖
  have ht : 0 ≤ t := norm_nonneg _
  have htn : t ≤ 2*R := by
    have h := A.intrinsic_tail_test hfin hH hRpos hx hplus hminus 0 (by simp) (by simp)
    simpa only [map_zero, zero_pow (by decide : 2 ≠ 0), sub_zero,
      Real.sqrt_sq_eq_abs, abs_of_nonneg hR] using h
  have ht2 : t^2 ≤ (2*R)^2 := (sq_le_sq₀ ht (by positivity)).2 htn
  have hrad : 0 ≤ R^2-t^2/4 := by nlinarith
  have hxn : ‖x‖ ≤ Real.sqrt (R^2-t^2/4) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro u hu
    let p := A.segments.headArray H u
    have hp : ∀ v, v ∉ H → p v=0 := fun v hv => A.segments.headArray_outside H u hv
    have hpn : A.segments.primalSeminorm p ≤ 1 := by
      rw [← SegmentSystem.finiteEmbedding_norm, SegmentSystem.finiteEmbedding_headArray]
      exact (A.headPrimal_norm_le hH u).trans hu.le
    have he : x (A.segments.finiteEmbedding p) = x u := by
      rw [SegmentSystem.finiteEmbedding_headArray, ← SegmentSystem.headDual_apply_apply,
        A.segments.headDual_eq_self hx]
    have hval : |x u| ≤ R := by
      have h := x.le_opNorm u
      rw [Real.norm_eq_abs, hu, mul_one] at h
      exact h.trans hxr
    have hval2 : (x u)^2 ≤ R^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).2 hval
    have h := A.intrinsic_tail_test hfin hH hRpos hx hplus hminus p hp hpn
    rw [he] at h
    have hsq : t^2 ≤ (2*Real.sqrt (R^2-(x u)^2))^2 :=
      (sq_le_sq₀ ht (by positivity)).2 h
    have hs := Real.sq_sqrt (sub_nonneg.mpr hval2)
    have hv2 : (x u)^2 ≤ R^2-t^2/4 := by nlinarith
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt hrad]
    exact hv2
  have hxn2 := (sq_le_sq₀ (norm_nonneg x) (Real.sqrt_nonneg _)).2 hxn
  rw [Real.sq_sqrt hrad] at hxn2
  change t^2+4*‖x‖^2 ≤ 4*R^2
  nlinarith

lemma finite_heads_of_predecessors
    (hpred : ∀ b : ι, ({a : ι | a ≤ b} : Set ι).Finite) :
    ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι) := by
  classical
  intro S
  let U : Set ι := ⋃ b ∈ (S : Set ι), {a : ι | a ≤ b}
  have hU : U.Finite := S.finite_toSet.biUnion (fun b _ => hpred b)
  refine ⟨hU.toFinset, ?_, ?_⟩
  · intro b hb
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, le_rfl⟩⟩
  · intro a b hab hb
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hb ⊢
    obtain ⟨c,hc,hbc⟩ := Set.mem_iUnion₂.mp hb
    exact Set.mem_iUnion₂.mpr ⟨c,hc,hab.trans hbc⟩

lemma coordinate_predual_approximation
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {x : A.segments.Dual} (hx : x ∈ A.segments.CoordinatePredual)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Finset ι, A.Ancestral (H : Set ι) ∧ ‖A.segments.tailDual H x‖ < ε := by
  have hxcl : x ∈ closure (Submodule.span ℝ (Set.range A.segments.coordinate) : Set A.segments.Dual) := hx
  obtain ⟨z,hz,hclose⟩ := Metric.mem_closure_iff.mp hxcl ε hε
  obtain ⟨S,hS⟩ := A.segments.span_coordinates_finite_support hz
  obtain ⟨H,hSH,hH⟩ := hfin S
  have hPH : A.segments.headDual H z = z :=
    A.segments.headDual_eq_self (fun v hv => hS v (fun h => hv (hSH h)))
  refine ⟨H,hH,?_⟩
  have he : A.segments.tailDual H x = A.segments.tailDual H (x-z) := by
    simp only [map_sub, SegmentSystem.tailDual_apply, hPH, sub_self, sub_zero]
  rw [he]
  exact lt_of_le_of_lt (A.tailDual_norm_le hH (x-z)) (by simpa only [dist_eq_norm] using hclose)

/-- Finite-dimensional compactness compares distinct members of any bounded
    sequence; no maximum over the infinitely many children is asserted. -/
lemma finite_head_pair {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (z : ℕ → A.segments.Dual) {R η : ℝ} (hz : ∀ i, ‖z i‖ ≤ R) (hη : 0 < η) :
    ∃ i j : ℕ, i ≠ j ∧ ‖A.segments.headDual H ((1/2:ℝ) • (z i-z j))‖ < η := by
  classical
  let M := Submodule.span ℝ (A.segments.coordinate '' (H : Set ι))
  have : FiniteDimensional ℝ M :=
    FiniteDimensional.span_of_finite ℝ (H.finite_toSet.image A.segments.coordinate)
  have hm (w : A.segments.Dual) : A.segments.headDual H w ∈ M := by
    rw [SegmentSystem.headDual_apply]
    apply Submodule.sum_mem
    intro v hv
    exact Submodule.smul_mem M _ (Submodule.subset_span ⟨v,hv,rfl⟩)
  let Z : ℕ → M := fun i => ⟨A.segments.headDual H (z i),hm (z i)⟩
  have hZ (i : ℕ) : Z i ∈ Metric.closedBall (0 : M) R := by
    rw [Metric.mem_closedBall]
    change dist (A.segments.headDual H (z i)) 0 ≤ R
    rw [dist_zero_right]
    exact (A.headDual_norm_le hH (z i)).trans (hz i)
  obtain ⟨a,_,φ,hφ,hconv⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hZ
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq (2*η) (by positivity)
  have hd := hN N le_rfl (N+1) (by omega)
  change dist (Z (φ N)) (Z (φ (N+1))) < 2*η at hd
  change dist (A.segments.headDual H (z (φ N))) (A.segments.headDual H (z (φ (N+1)))) < 2*η at hd
  rw [dist_eq_norm] at hd
  change ‖A.segments.headDual H (z (φ N)) - A.segments.headDual H (z (φ (N+1)))‖ < 2*η at hd
  refine ⟨φ N, φ (N+1), hφ.injective.ne (by omega), ?_⟩
  rw [map_smul,norm_smul,map_sub,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  linarith

lemma average_lens {x : A.segments.Dual} (z : ℕ → A.segments.Dual) {R : ℝ}
    (hplus : ∀ i, ‖x+z i‖ ≤ R) (hminus : ∀ i, ‖x-z i‖ ≤ R) (i j : ℕ) :
    ‖x+(1/2:ℝ) • (z i-z j)‖ ≤ R ∧ ‖x-(1/2:ℝ) • (z i-z j)‖ ≤ R := by
  have hp : x+(1/2:ℝ) • (z i-z j) = (1/2:ℝ) • ((x+z i)+(x-z j)) := by module
  have hm : x-(1/2:ℝ) • (z i-z j) = (1/2:ℝ) • ((x-z i)+(x+z j)) := by module
  constructor
  · rw [hp,norm_smul,Real.norm_eq_abs]
    norm_num
    have h := (norm_add_le (x+z i) (x-z j)).trans (add_le_add (hplus i) (hminus j))
    linarith
  · rw [hm,norm_smul,Real.norm_eq_abs]
    norm_num
    have h := (norm_add_le (x-z i) (x+z j)).trans (add_le_add (hminus i) (hplus j))
    linarith

/-- Exact separated-lens consequence of the intrinsic estimate. Its only
    approximation input is explicitly proved for each target model below. -/
lemma separated_lens
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {x : A.segments.Dual}
    (happrox : ∀ η > 0, ∃ H : Finset ι, A.Ancestral (H : Set ι) ∧ ‖A.segments.tailDual H x‖ < η)
    (z : ℕ → A.segments.Dual) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hplus : ∀ i, ‖x+z i‖ ≤ R) (hminus : ∀ i, ‖x-z i‖ ≤ R)
    (hsep : ∀ i j, i ≠ j → ε ≤ ‖z i-z j‖) :
    ‖x‖^2+ε^2/16 ≤ R^2 := by
  have hxr : ‖x‖ ≤ R := A.norm_center_le (hplus 0) (hminus 0)
  have hz (i : ℕ) : ‖z i‖ ≤ R := by
    apply A.norm_center_le (x := z i) (y := x)
    · simpa only [add_comm] using hplus i
    · simpa only [norm_sub_rev] using hminus i
  apply le_of_forall_pos_le_add
  intro δ hδ
  let C : ℝ := 8*R+8*‖x‖+ε+4
  have hC : 0 < C := by dsimp [C]; positivity
  let η : ℝ := min (ε/4) (min 1 (δ/C))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by norm_num) (div_pos hδ hC))
  have hηε : η < ε/2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hηδ : C*η ≤ δ := by
    have hh : η ≤ δ/C := (min_le_right _ _).trans (min_le_right _ _)
    nlinarith [(le_div_iff₀ hC).mp hh]
  obtain ⟨H,hH,hclose⟩ := happrox η hη
  let p := A.segments.headDual H x
  have hp : ∀ v, v ∉ H → p (A.segments.unitVector v)=0 := by
    intro v hv
    exact (A.segments.headDual_unit H x v).trans (ite_eq_right hv)
  have hpn : ‖p‖ ≤ ‖x‖ := A.headDual_norm_le hH x
  have hsmall : ‖x-p‖ < η := hclose
  have hplower : ‖x‖-η ≤ ‖p‖ := by
    have h := norm_sub_norm_le x p
    linarith
  obtain ⟨i,j,hij,hhead⟩ := A.finite_head_pair hH z hz hη
  let w := (1/2:ℝ) • (z i-z j)
  have hw : ε/2 ≤ ‖w‖ := by
    dsimp [w]
    rw [norm_smul,Real.norm_eq_abs]
    norm_num
    linarith [hsep i j hij]
  have hwl : ε/2-η ≤ ‖A.segments.tailDual H w‖ := by
    have h := norm_sub_norm_le w (A.segments.headDual H w)
    change ‖w‖-‖A.segments.headDual H w‖ ≤ ‖A.segments.tailDual H w‖ at h
    linarith
  obtain ⟨hwp,hwm⟩ := A.average_lens z hplus hminus i j
  have hpp : ‖p+w‖ ≤ R+η := by
    have he : p+w = (x+w)-(x-p) := by module
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hwp hsmall.le)
  have hpm : ‖p-w‖ ≤ R+η := by
    have he : p-w = (x-w)-(x-p) := by module
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hwm hsmall.le)
  have hbudget := A.intrinsic_tail_sq hfin hH (add_nonneg hR hη.le) hp hpp hpm
  have hpsq : ‖x‖^2 - 2*‖x‖*η ≤ ‖p‖^2 := by
    nlinarith [sq_nonneg (‖x‖-‖p‖),mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hplower)]
  have hw2 : (ε/2)^2-ε*η ≤ ‖A.segments.tailDual H w‖^2 := by
    have hh := (sq_le_sq₀ (by linarith : 0 ≤ ε/2-η) (norm_nonneg _)).2 hwl
    nlinarith
  have hη2 : η^2 ≤ η := by nlinarith
  dsimp [C] at hηδ
  nlinarith

end Ancestry

end DiamondDistortion

end

end OAI
end

section
-- module Solutions.OAIQW_DiamondDistortion.Orthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι κ : Type*} (T : SegmentSystem ι)

lemma primal_sq_le (p : ι →₀ ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ F : T.Family, (∑ i, (∑ v ∈ F.seg i,p v)^2) ≤ M) :
    (T.primalSeminorm p)^2 ≤ M := by
  have hbound : T.primalSeminorm p ≤ Real.sqrt M := by
    rw [primalSeminorm, Seminorm.iSup_apply T.families_bddAbove]
    apply ciSup_le
    intro F
    have h := hF F
    have he : ‖F.test p‖^2 = (∑ i, (∑ v ∈ F.seg i,p v)^2) := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Family.test_apply,Real.norm_eq_abs,sq_abs]
    rw [← he, ← Real.sq_sqrt hM] at h
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp h
  have h := (sq_le_sq₀ (apply_nonneg _ _) (Real.sqrt_nonneg _)).2 hbound
  rwa [Real.sq_sqrt hM] at h

/-- Segment families in disjoint components spend orthogonal testing energies. -/
lemma block_add_sq (c : ι → κ)
    (hsame : ∀ S, T.IsSegment S → ∀ u ∈ S, ∀ v ∈ S, c u=c v)
    (p q : ι →₀ ℝ) (hd : Disjoint (T.colorSupport c p) (T.colorSupport c q)) :
    (T.primalSeminorm (p+q))^2 ≤ (T.primalSeminorm p)^2+(T.primalSeminorm q)^2 := by
  classical
  apply T.primal_sq_le (p+q) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  intro F
  have hz (i : Fin F.n) : (∑ v ∈ F.seg i,p v)*(∑ v ∈ F.seg i,q v)=0 := by
    by_cases hp : (∑ v ∈ F.seg i,p v)=0
    · rw [hp,zero_mul]
    by_cases hq : (∑ v ∈ F.seg i,q v)=0
    · rw [hq,mul_zero]
    obtain ⟨u,hu,hpu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
    obtain ⟨v,hv,hqv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    have he := hsame _ (F.allowed i) u hu v hv
    exact False.elim (Finset.disjoint_left.mp hd
      (Finset.mem_image.mpr ⟨u,Finsupp.mem_support_iff.mpr hpu,rfl⟩)
      (Finset.mem_image.mpr ⟨v,Finsupp.mem_support_iff.mpr hqv,he.symm⟩))
  have he (i : Fin F.n) : (∑ v ∈ F.seg i,(p+q) v)^2 =
      (∑ v ∈ F.seg i,p v)^2+(∑ v ∈ F.seg i,q v)^2 := by
    simp only [Finsupp.add_apply,Finset.sum_add_distrib]
    nlinarith [hz i]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  exact add_le_add
    (T.test_energy_le_allow_empty F.seg (fun i _ => F.allowed i) F.disjoint p)
    (T.test_energy_le_allow_empty F.seg (fun i _ => F.allowed i) F.disjoint q)

/-- A functional on an orthogonal sum is uniformly small outside finitely many
    components. The proof uses finite blocks only, not a reflexivity library. -/
lemma small_color_tail_upper (c : ι → κ)
    (hsame : ∀ S, T.IsSegment S → ∀ u ∈ S, ∀ v ∈ S, c u=c v)
    (x : T.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset κ, ∀ p : ι →₀ ℝ, (∀ v ∈ p.support, c v ∉ C) →
      x (T.finiteEmbedding p) ≤ ε*T.primalSeminorm p := by
  classical
  by_contra hn
  push Not at hn
  have hchoose (C : Finset κ) : ∃ q : ι →₀ ℝ,
      (∀ v ∈ q.support,c v ∉ C) ∧ T.primalSeminorm q=1 ∧ ε < x (T.finiteEmbedding q) := by
    obtain ⟨p,hout,hval⟩ := hn C
    have hpn0 : T.primalSeminorm p ≠ 0 := by
      intro he
      have hp0 := (T.primal_eq_zero_iff p).mp he
      simp only [hp0,map_zero,mul_zero,lt_self_iff_false] at hval
    have hpn : 0 < T.primalSeminorm p := lt_of_le_of_ne (apply_nonneg _ _) hpn0.symm
    let q := (T.primalSeminorm p)⁻¹ • p
    refine ⟨q, ?_, ?_, ?_⟩
    · intro v hv
      apply hout v
      apply Finsupp.mem_support_iff.mpr
      intro hpv
      have hqv : q v=0 := by simp [q,Finsupp.smul_apply,hpv]
      exact (Finsupp.mem_support_iff.mp hv) hqv
    · simp only [q,map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpn)]
      exact inv_mul_cancel₀ hpn0
    · simp only [q,map_smul,smul_eq_mul]
      rw [inv_mul_eq_div]
      exact (lt_div_iff₀ hpn).mpr hval
  have hblocks : ∀ n : ℕ, ∃ p : ι →₀ ℝ,
      (T.primalSeminorm p)^2 ≤ (n : ℝ) ∧ (n : ℝ)*ε ≤ x (T.finiteEmbedding p) := by
    intro n
    induction n with
    | zero => exact ⟨0,by simp only [map_zero,zero_pow (by decide : 2 ≠ 0),Nat.cast_zero,le_refl],
        by simp only [map_zero,Nat.cast_zero,zero_mul,le_refl]⟩
    | succ n ih =>
      obtain ⟨p,hpn,hpx⟩ := ih
      obtain ⟨q,hqout,hqn,hqx⟩ := hchoose (T.colorSupport c p)
      have hd : Disjoint (T.colorSupport c p) (T.colorSupport c q) := by
        apply Finset.disjoint_left.mpr
        intro a hap haq
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp haq
        exact hqout v hv hap
      refine ⟨p+q, ?_, ?_⟩
      · have h := T.block_add_sq c hsame p q hd
        rw [hqn] at h
        push_cast
        nlinarith
      · simp only [map_add,Nat.cast_add,Nat.cast_one]
        nlinarith
  obtain ⟨n,hn⟩ := exists_nat_gt (‖x‖^2/ε^2)
  have hn0 : (0:ℝ) < n := lt_of_le_of_lt (div_nonneg (sq_nonneg _) (sq_nonneg _)) hn
  have hnε : ‖x‖^2 < (n:ℝ)*ε^2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hn
  obtain ⟨p,hpn,hpx⟩ := hblocks n
  have hxb : x (T.finiteEmbedding p) ≤ ‖x‖*T.primalSeminorm p := by
    calc
      _ ≤ ‖x (T.finiteEmbedding p)‖ := Real.le_norm_self _
      _ ≤ ‖x‖*‖T.finiteEmbedding p‖ := x.le_opNorm _
      _ = _ := by rw [T.finiteEmbedding_norm]
  have hprod : (n:ℝ)*ε ≤ ‖x‖*T.primalSeminorm p := hpx.trans hxb
  have hsquare := (sq_le_sq₀ (mul_nonneg hn0.le hε.le)
    (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))).2 hprod
  have hmul := mul_le_mul_of_nonneg_left hpn (sq_nonneg ‖x‖)
  have hcontra := mul_pos hn0 (sub_pos.mpr hnε)
  nlinarith

lemma small_color_tail (c : ι → κ)
    (hsame : ∀ S, T.IsSegment S → ∀ u ∈ S, ∀ v ∈ S, c u=c v)
    (x : T.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset κ, ∀ p : ι →₀ ℝ, (∀ v ∈ p.support, c v ∉ C) →
      |x (T.finiteEmbedding p)| ≤ ε*T.primalSeminorm p := by
  obtain ⟨C,hC⟩ := T.small_color_tail_upper c hsame x hε
  refine ⟨C,?_⟩
  intro p hp
  apply abs_le.mpr
  refine ⟨?_,hC p hp⟩
  have h := hC (-p) (by simpa only [Finsupp.support_neg] using hp)
  simp only [map_neg,map_neg_eq_map] at h
  linarith

/-- No nonzero coordinate is lost by using the actual Finsupp support. -/
lemma sum_sq_le_support (p : ι →₀ ℝ) (S : Finset ι) :
    (∑ v ∈ S,p v^2) ≤ ∑ v ∈ p.support,p v^2 := by
  classical
  have h : (∑ v ∈ S,p v^2) ≤ ∑ v ∈ S ∪ p.support,p v^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => sq_nonneg _)
  have he : (∑ v ∈ p.support,p v^2) = ∑ v ∈ S ∪ p.support,p v^2 := by
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hv
    rw [Finsupp.notMem_support_iff.mp hv]
    norm_num
  exact h.trans_eq he.symm

lemma coordinate_energy_le (p : ι →₀ ℝ) (S : Finset ι) :
    (∑ v ∈ S,p v^2) ≤ (T.primalSeminorm p)^2 := by
  classical
  have h := T.test_energy_le (fun v : S => {v.val}) (fun v => T.singleton v.val)
    (by
      intro v w hvw
      exact Finset.disjoint_singleton.mpr (fun he => hvw (Subtype.ext he))) p
  simp only [Finset.sum_singleton] at h
  calc
    _ = ∑ v : S,p v.val^2 := (Finset.sum_coe_sort S (fun v => p v^2)).symm
    _ ≤ _ := h

lemma primal_sq_le_of_segment (p : ι →₀ ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hS : ∀ S, T.IsSegment S → (∑ v ∈ S,p v)^2 ≤ L*(∑ v ∈ S,p v^2)) :
    (T.primalSeminorm p)^2 ≤ L*(∑ v ∈ p.support,p v^2) := by
  classical
  apply T.primal_sq_le p (mul_nonneg hL (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  intro F
  have he : (∑ i,∑ v ∈ F.seg i,p v^2) = ∑ v ∈ Finset.univ.biUnion F.seg,p v^2 := by
    symm
    apply Finset.sum_biUnion
    intro i _ j _ hij
    exact F.disjoint hij
  calc
    _ ≤ ∑ i,L*(∑ v ∈ F.seg i,p v^2) := Finset.sum_le_sum (fun i _ => hS _ (F.allowed i))
    _ = L*(∑ v ∈ Finset.univ.biUnion F.seg,p v^2) := by rw [← Finset.mul_sum,he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_sq_le_support p _) hL

lemma finiteArray_apply (S : Finset ι) (a : ι → ℝ) (v : ι) :
    finiteArray S a v = if v ∈ S then a v else 0 := by
  classical
  simp [finiteArray,Finsupp.finsetSum_apply,Finsupp.single_apply,Finset.sum_ite_eq']

lemma finiteArray_support (S : Finset ι) (a : ι → ℝ) : (finiteArray S a).support ⊆ S := by
  intro v hv
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hv) (by rw [finiteArray_apply,ite_eq_right hn])

lemma finiteArray_energy (S : Finset ι) (a : ι → ℝ) :
    (∑ v ∈ (finiteArray S a).support,finiteArray S a v^2) = ∑ v ∈ S,a v^2 := by
  calc
    _ = ∑ v ∈ S,finiteArray S a v^2 := by
      apply Finset.sum_subset (finiteArray_support S a)
      intro v _ hv
      rw [Finsupp.notMem_support_iff.mp hv]
      norm_num
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [finiteArray_apply,ite_eq_left hv]

lemma finiteArray_pairing (S : Finset ι) (a : ι → ℝ) (x : T.Dual) :
    x (T.finiteEmbedding (finiteArray S a)) = ∑ v ∈ S,a v*x (T.unitVector v) := by
  simp only [finiteArray,map_sum,map_smul,finiteEmbedding_single,one_smul,smul_eq_mul]

/-- Bounded nonnegative finite square sums have uniformly small disjoint tails.
    This is proved directly from a real supremum, with no countability assumption. -/
lemma finite_square_tails (a : ι → ℝ) {M : ℝ}
    (hM : ∀ S : Finset ι,(∑ v ∈ S,a v^2) ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset ι, ∀ U : Finset ι, Disjoint S U → (∑ v ∈ U,a v^2) < δ := by
  classical
  let E : Set ℝ := Set.range (fun S : Finset ι => ∑ v ∈ S,a v^2)
  have hEb : BddAbove E := ⟨M,by rintro _ ⟨S,rfl⟩; exact hM S⟩
  have hEn : E.Nonempty := ⟨0,∅,by simp⟩
  obtain ⟨b,⟨S,rfl⟩,hS⟩ := exists_lt_of_lt_csSup hEn (sub_lt_self (sSup E) hδ)
  refine ⟨S,?_⟩
  intro U hU
  have h := le_csSup hEb (show (∑ v ∈ S ∪ U,a v^2) ∈ E from ⟨S ∪ U,rfl⟩)
  rw [Finset.sum_union hU] at h
  linarith

end SegmentSystem

end DiamondDistortion

end

end OAI
end

section
-- module Solutions.OAIQW_DiamondDistortion.ForestModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

lemma infinite_finite_heads : ∀ S : Finset (List ℕ), ∃ K : Finset (List ℕ),
    S ⊆ K ∧ Ancestry.Ancestral (A := infiniteAncestry) (K : Set (List ℕ)) := by
  apply Ancestry.finite_heads_of_predecessors (A := infiniteAncestry)
  intro b
  exact b.inits.toFinset.finite_toSet.subset (by
    intro a ha
    exact List.mem_toFinset.mpr ((List.mem_inits a b).mpr ha))

lemma forest_finite_heads : ∀ S : Finset ForestNode, ∃ K : Finset ForestNode,
    S ⊆ K ∧ Ancestry.Ancestral (A := forestAncestry) (K : Set ForestNode) := by
  apply Ancestry.finite_heads_of_predecessors (A := forestAncestry)
  intro b
  have hfin : (({b.val.1} : Set ℕ) ×ˢ (b.val.2.inits.toFinset : Set (List ℕ))).Finite :=
    (Set.finite_singleton _).prod b.val.2.inits.toFinset.finite_toSet
  have hpre := hfin.preimage (f := (Subtype.val : ForestNode → ℕ × List ℕ)) Subtype.val_injective.injOn
  apply hpre.subset
  intro a ha
  exact ⟨ha.1, List.mem_toFinset.mpr ((List.mem_inits _ _).mpr ha.2)⟩

namespace Forest

lemma same_component (S : Finset ForestNode) (hS : forestSegments.IsSegment S)
    (u : ForestNode) (hu : u ∈ S) (v : ForestNode) (hv : v ∈ S) :
    component u=component v := by
  obtain ⟨a,b,_,hm⟩ := hS
  exact ((hm u).mp hu).2.1.trans ((hm v).mp hv).2.1.symm

lemma segment_card_le (S : Finset ForestNode) (hS : forestSegments.IsSegment S)
    (u : ForestNode) (hu : u ∈ S) : S.card ≤ component u+1 := by
  obtain ⟨a,b,_,hm⟩ := hS
  have hcard : S.card ≤ (Finset.range (component b+1)).card := by
    apply Finset.card_le_card_of_injOn (fun v : ForestNode => v.val.2.length)
    · intro v hv
      have hvb := ((hm v).mp hv).2
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (hvb.2.length_le.trans b.property.2)
    · intro v hv w hw he
      have hvb := ((hm v).mp hv).2
      have hwb := ((hm w).mp hw).2
      have hword : v.val.2=w.val.2 := by
        rcases List.prefix_or_prefix_of_prefix hvb.2 hwb.2 with h | h
        · exact h.eq_of_length he
        · exact (h.eq_of_length he.symm).symm
      exact Subtype.ext (Prod.ext (hvb.1.trans hwb.1.symm) hword)
  rw [Finset.card_range] at hcard
  have he : component u=component b := ((hm u).mp hu).2.1
  rwa [he]

lemma primal_sq_bounded_components (C : Finset ℕ) (p : ForestNode →₀ ℝ)
    (hp : ∀ v ∈ p.support, component v ∈ C) :
    (forestSegments.primalSeminorm p)^2 ≤ (((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1)*(∑ v ∈ p.support,p v^2) := by
  apply forestSegments.primal_sq_le_of_segment p (by positivity)
  intro S hS
  by_cases hz : (∑ v ∈ S,p v)=0
  · rw [hz,zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity
  obtain ⟨u,hu,hpu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hcu := hp u (Finsupp.mem_support_iff.mpr hpu)
  have hcard : (S.card : ℝ) ≤ ((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1 := by
    have h := (segment_card_le S hS u hu).trans (Nat.add_le_add_right (Finset.le_sup (f := id) hcu) 1)
    exact_mod_cast h
  exact sq_sum_le_card_mul_sum_sq.trans (mul_le_mul_of_nonneg_right hcard
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

lemma coefficients_bounded (C : Finset ℕ) (x : forestSegments.Dual) (S : Finset ForestNode) :
    (∑ v ∈ S,coefficients C x v^2) ≤ (((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1)*‖x‖^2 := by
  classical
  let a := coefficients C x
  let p := SegmentSystem.finiteArray S a
  let B := ∑ v ∈ S,a v^2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : ∀ v ∈ p.support,component v ∈ C := by
    intro v hv
    by_contra hn
    have hav : a v=0 := ite_eq_right hn
    have hpv : p v=0 := by rw [SegmentSystem.finiteArray_apply,hav]; split_ifs <;> rfl
    exact (Finsupp.mem_support_iff.mp hv) hpv
  have hpenergy := primal_sq_bounded_components C p hp
  rw [SegmentSystem.finiteArray_energy] at hpenergy
  have he : x (forestSegments.finiteEmbedding p)=B := by
    rw [forestSegments.finiteArray_pairing]
    apply Finset.sum_congr rfl
    intro v _
    dsimp [a,coefficients]
    split_ifs <;> ring
  have hval : B ≤ ‖x‖*forestSegments.primalSeminorm p := by
    rw [← he]
    exact (Real.le_norm_self _).trans (by
      simpa only [SegmentSystem.finiteEmbedding_norm] using x.le_opNorm (forestSegments.finiteEmbedding p))
  have hsq := (sq_le_sq₀ hB
    (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))).2 hval
  have hmul := mul_le_mul_of_nonneg_left hpenergy (sq_nonneg ‖x‖)
  change B ≤ (((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1)*‖x‖^2
  by_contra hn
  have hpos : 0 < B := lt_of_le_of_lt (by positivity) (lt_of_not_ge hn)
  have hc := mul_pos hpos (sub_pos.mpr (lt_of_not_ge hn))
  change (forestSegments.primalSeminorm p)^2 ≤ (((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1)*B at hpenergy
  change ‖x‖^2*(forestSegments.primalSeminorm p)^2 ≤ ‖x‖^2*((((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1)*B) at hmul
  nlinarith only [hsq,hmul,hc]

lemma finite_component_tail (C : Finset ℕ) (x : forestSegments.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ForestNode, ∀ p : ForestNode →₀ ℝ,
      (∀ v ∈ p.support, component v ∈ C) → (∀ v ∈ p.support,v ∉ S) →
      |x (forestSegments.finiteEmbedding p)| ≤ ε*forestSegments.primalSeminorm p := by
  classical
  obtain ⟨S,hS⟩ := SegmentSystem.finite_square_tails (coefficients C x)
    (coefficients_bounded C x) (sq_pos_of_pos hε)
  refine ⟨S,?_⟩
  intro p hp hout
  have hd : Disjoint S p.support := Finset.disjoint_left.mpr (fun v hv hvs => hout v hvs hv)
  have ha : Real.sqrt (∑ v ∈ p.support,coefficients C x v^2) ≤ ε :=
    (Real.sqrt_le_left hε.le).mpr (hS p.support hd).le
  have hb : Real.sqrt (∑ v ∈ p.support,p v^2) ≤ forestSegments.primalSeminorm p :=
    (Real.sqrt_le_left (apply_nonneg _ _)).mpr (forestSegments.coordinate_energy_le p p.support)
  have he : x (forestSegments.finiteEmbedding p) =
      ∑ v ∈ p.support,p v*coefficients C x v := by
    rw [SegmentSystem.finiteEmbedding_apply,SegmentSystem.dual_coe_apply]
    apply Finset.sum_congr rfl
    intro v hv
    rw [coefficients,ite_eq_left (hp v hv)]
    rfl
  rw [he]
  calc
    _ ≤ ∑ v ∈ p.support, |p v| * |coefficients C x v| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun v => p v*coefficients C x v) p.support
    _ ≤ Real.sqrt (∑ v ∈ p.support,p v^2) * Real.sqrt (∑ v ∈ p.support,coefficients C x v^2) := by
      simpa only [sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt p.support
        (fun v => |p v|) (fun v => |coefficients C x v|)
    _ ≤ forestSegments.primalSeminorm p * ε := mul_le_mul hb ha (Real.sqrt_nonneg _) (apply_nonneg _ _)
    _ = _ := mul_comm _ _

lemma component_set_ancestral (C : Finset ℕ) :
    Ancestry.Ancestral (A := forestAncestry) {v : ForestNode | component v ∈ C} := by
  intro a b hab hb
  change ForestAncestor a b at hab
  change component a ∈ C
  change component b ∈ C at hb
  have he : component a=component b := hab.1
  rwa [he]

/-- The full finite-height forest dual really has finite ancestral head
    approximation. Both the component tail and coordinate tail arguments are
    proved from its disjoint-segment norm, rather than imposed as hypotheses. -/
lemma full_dual_approximation (x : forestSegments.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Finset ForestNode, Ancestry.Ancestral (A := forestAncestry) (H : Set ForestNode) ∧
      ‖forestSegments.tailDual H x‖ < ε := by
  classical
  have hd : 0 < ε/4 := by positivity
  obtain ⟨C,hC⟩ := forestSegments.small_color_tail component same_component x hd
  obtain ⟨S,hS⟩ := finite_component_tail C x hd
  obtain ⟨H,hSH,hH⟩ := forest_finite_heads S
  refine ⟨H,hH,?_⟩
  have hbound : ‖forestSegments.tailDual H x‖ ≤ ε/2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    induction u using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih u =>
      let p := forestSegments.ofPrimal u
      let q := p.filter (fun v => v ∉ H)
      let qi := q.filter (fun v => component v ∈ C)
      let qo := q.filter (fun v => component v ∉ C)
      have hqi : ∀ v ∈ qi.support,component v ∈ C := by
        intro v hv
        rw [Finsupp.support_filter] at hv
        exact (Finset.mem_filter.mp hv).2
      have hqiS : ∀ v ∈ qi.support,v ∉ S := by
        intro v hv hvs
        rw [Finsupp.support_filter] at hv
        have hvq := (Finset.mem_filter.mp hv).1
        rw [Finsupp.support_filter] at hvq
        exact (Finset.mem_filter.mp hvq).2 (hSH hvs)
      have hqo : ∀ v ∈ qo.support,component v ∉ C := by
        intro v hv
        rw [Finsupp.support_filter] at hv
        exact (Finset.mem_filter.mp hv).2
      have hi := hS qi hqi hqiS
      have ho := hC qo hqo
      have hqin : forestSegments.primalSeminorm qi ≤ forestSegments.primalSeminorm q := by
        change (Ancestry.segments (A := forestAncestry)).primalSeminorm qi ≤
          (Ancestry.segments (A := forestAncestry)).primalSeminorm q
        convert Ancestry.primal_filter_le (A := forestAncestry) (component_set_ancestral C) q using 1
        all_goals dsimp [qi,qo]; congr
      have hqon : forestSegments.primalSeminorm qo ≤ forestSegments.primalSeminorm q := by
        change (Ancestry.segments (A := forestAncestry)).primalSeminorm qo ≤
          (Ancestry.segments (A := forestAncestry)).primalSeminorm q
        convert Ancestry.primal_filter_tail_le (A := forestAncestry) (component_set_ancestral C) q using 1
        all_goals dsimp [qi,qo]; congr
      have hqn : forestSegments.primalSeminorm q ≤ forestSegments.primalSeminorm p := by
        change (Ancestry.segments (A := forestAncestry)).primalSeminorm q ≤
          (Ancestry.segments (A := forestAncestry)).primalSeminorm p
        convert Ancestry.primal_filter_tail_le (A := forestAncestry) hH p using 1
        all_goals dsimp [q]; congr
      have hsum : qi+qo=q := by
        apply Finsupp.ext
        intro v
        by_cases hv : component v ∈ C <;> simp [qi,qo]
      have he : forestSegments.tailDual H x (u : forestSegments.JamesSpace) =
          x (forestSegments.finiteEmbedding q) := by
        rw [SegmentSystem.tailDual_apply_apply,SegmentSystem.headPrimal_coe,
          ← UniformSpace.Completion.coe_sub,SegmentSystem.sub_filterPrimal]
        congr 2
        apply Finsupp.ext
        intro v
        simp [SegmentSystem.filterPrimal,q,p,SegmentSystem.ofPrimal]
        congr
      rw [he,Real.norm_eq_abs,UniformSpace.Completion.norm_coe,SegmentSystem.norm_eq_primal]
      calc
        _ = |x (forestSegments.finiteEmbedding qi)+x (forestSegments.finiteEmbedding qo)| := by
          rw [← hsum,map_add,map_add]
        _ ≤ |x (forestSegments.finiteEmbedding qi)|+|x (forestSegments.finiteEmbedding qo)| := abs_add_le _ _
        _ ≤ (ε/4)*forestSegments.primalSeminorm qi+(ε/4)*forestSegments.primalSeminorm qo := add_le_add hi ho
        _ ≤ (ε/4)*forestSegments.primalSeminorm q+(ε/4)*forestSegments.primalSeminorm q :=
          add_le_add (mul_le_mul_of_nonneg_left hqin hd.le) (mul_le_mul_of_nonneg_left hqon hd.le)
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hqn hd.le]
  exact lt_of_le_of_lt hbound (by linarith)

end Forest

end DiamondDistortion

end

end OAI
end

section
-- module Solutions.OAIQW_DiamondDistortion.DiamondGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Diamond

lemma endpoint_ne (n : ℕ) (e : Edge n) : endpoint n e false ≠ endpoint n e true := by
  cases n with
  | zero => simp [endpoint]
  | succ n =>
    rcases e with ⟨e,i,b⟩
    cases b <;> simp [endpoint]

lemma adj_iff {n : ℕ} {u v : Vertex n} : (graph n).Adj u v ↔
    ∃ e : Edge n, (u=endpoint n e false ∧ v=endpoint n e true) ∨
      (u=endpoint n e true ∧ v=endpoint n e false) := by
  rw [graph,SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_,⟨e,hu,hv⟩ | ⟨e,hv,hu⟩⟩
    · exact ⟨e,Or.inl ⟨hu,hv⟩⟩
    · exact ⟨e,Or.inr ⟨hu,hv⟩⟩
  · rintro ⟨e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact ⟨endpoint_ne n e,Or.inl ⟨e,rfl,rfl⟩⟩
    · exact ⟨(endpoint_ne n e).symm,Or.inr ⟨e,rfl,rfl⟩⟩

lemma adj_endpoint (n : ℕ) (e : Edge n) :
    (graph n).Adj (endpoint n e false) (endpoint n e true) :=
  adj_iff.mpr ⟨e,Or.inl ⟨rfl,rfl⟩⟩

lemma adj_old_mid {n : ℕ} {u : Vertex n} {e : Edge n} {i : ℕ} :
    (graph (n+1)).Adj (Sum.inl u) (Sum.inr (e,i)) ↔
      u=endpoint n e false ∨ u=endpoint n e true := by
  rw [adj_iff]
  constructor
  · rintro ⟨⟨d,j,b⟩,h⟩
    cases b <;> simp [endpoint] at h
    · rcases h with ⟨hu,he,hj⟩
      subst d
      exact Or.inl hu
    · rcases h with ⟨hu,he,hj⟩
      subst d
      exact Or.inr hu
  · rintro (rfl | rfl)
    · exact ⟨(e,i,false),Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨(e,i,true),Or.inr ⟨rfl,rfl⟩⟩

lemma not_adj_new {n : ℕ} (u v : Edge n × ℕ) :
    ¬(graph (n+1)).Adj (Sum.inr u) (Sum.inr v) := by
  rintro h
  rcases adj_iff.mp h with ⟨⟨e,i,b⟩,h⟩
  cases b <;> simp [endpoint] at h

lemma replace_adj {n : ℕ} {u v : Vertex n} (h : (graph n).Adj u v) :
    ∃ p : (graph (n+1)).Walk (Sum.inl u) (Sum.inl v), p.length=2 := by
  obtain ⟨e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := adj_iff.mp h
  · exact ⟨.cons ((adj_old_mid (i := 0)).mpr (Or.inl rfl))
      (.cons (adj_old_mid.mpr (Or.inr rfl)).symm .nil),rfl⟩
  · exact ⟨.cons ((adj_old_mid (i := 0)).mpr (Or.inr rfl))
      (.cons (adj_old_mid.mpr (Or.inl rfl)).symm .nil),rfl⟩

lemma replace_walk {n : ℕ} {u v : Vertex n} (p : (graph n).Walk u v) :
    ∃ q : (graph (n+1)).Walk (Sum.inl u) (Sum.inl v),q.length=2*p.length := by
  induction p with
  | nil => exact ⟨.nil,rfl⟩
  | cons h p ih =>
    obtain ⟨q,hq⟩ := ih
    obtain ⟨r,hr⟩ := replace_adj h
    refine ⟨r.append q,?_⟩
    rw [SimpleGraph.Walk.length_append,hr,hq,SimpleGraph.Walk.length_cons]
    omega

lemma connected (n : ℕ) : (graph n).Connected := by
  induction n with
  | zero =>
    have : Nonempty (Vertex 0) := ⟨false⟩
    refine ⟨?_⟩
    intro u v
    cases u <;> cases v
    · exact ⟨.nil⟩
    · exact (adj_endpoint 0 ()).reachable
    · exact (adj_endpoint 0 ()).symm.reachable
    · exact ⟨.nil⟩
  | succ n ih =>
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨Sum.inl (endpoint n (baseEdge n) false),?_⟩
    intro v
    cases v with
    | inl v =>
      obtain ⟨p⟩ := ih (endpoint n (baseEdge n) false) v
      obtain ⟨q,hq⟩ := replace_walk p
      exact ⟨q⟩
    | inr v =>
      obtain ⟨e,i⟩ := v
      obtain ⟨p⟩ := ih (endpoint n (baseEdge n) false) (endpoint n e false)
      obtain ⟨q,hq⟩ := replace_walk p
      exact ⟨q.append (adj_old_mid.mpr (Or.inl rfl)).toWalk⟩

lemma potential_walk {V : Type*} {G : SimpleGraph V} (φ : V → ℝ)
    (hφ : ∀ u v,G.Adj u v → |φ u-φ v| ≤ 1) {u v : V} (p : G.Walk u v) :
    |φ u-φ v| ≤ p.length := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have ht : |φ u-φ w| ≤ |φ u-φ v|+|φ v-φ w| := abs_sub_le _ _ _
    have h := hφ u v h
    simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

lemma distance_potential (n : ℕ) (a : Vertex n) :
    ∀ u v,(graph n).Adj u v →
      |((graph n).dist a u : ℝ)-(graph n).dist a v| ≤ 1 := by
  intro u v h
  have huv := (connected n).dist_triangle (u := a) (v := u) (w := v)
  have hvu := (connected n).dist_triangle (u := a) (v := v) (w := u)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h] at huv
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h.symm] at hvu
  have hu : ((graph n).dist a v : ℝ) ≤ (graph n).dist a u+1 := by exact_mod_cast huv
  have hv : ((graph n).dist a u : ℝ) ≤ (graph n).dist a v+1 := by exact_mod_cast hvu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma extendPotential_adj {n : ℕ} (φ : Vertex n → ℝ)
    (hφ : ∀ u v,(graph n).Adj u v → |φ u-φ v| ≤ 1) :
    ∀ u v,(graph (n+1)).Adj u v → |extendPotential φ u-extendPotential φ v| ≤ 1 := by
  intro u v h
  rcases adj_iff.mp h with ⟨⟨e,i,b⟩,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ <;>
    cases b <;> dsimp [endpoint,extendPotential]
  all_goals
    have h := hφ _ _ (adj_endpoint n e)
    have ha := (abs_le.mp h).1
    have hb := (abs_le.mp h).2
    apply abs_le.mpr
    constructor <;> linarith

/-- One subdivision doubles unweighted old-vertex distances. -/
lemma dist_old (n : ℕ) (u v : Vertex n) :
    (graph (n+1)).dist (Sum.inl u) (Sum.inl v)=2*(graph n).dist u v := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := (connected n).exists_walk_length_eq_dist u v
    obtain ⟨q,hq⟩ := replace_walk p
    exact (SimpleGraph.dist_le q).trans (by rw [hq,hp])
  · obtain ⟨p,hp⟩ := (connected (n+1)).exists_walk_length_eq_dist (Sum.inl u) (Sum.inl v)
    have h := potential_walk (extendPotential (fun w => ((graph n).dist u w : ℝ)))
      (extendPotential_adj _ (distance_potential n u)) p
    rw [hp] at h
    simp only [extendPotential,SimpleGraph.dist_self,Nat.cast_zero,mul_zero,zero_sub,abs_neg] at h
    rw [abs_of_nonneg (by positivity)] at h
    exact_mod_cast h

lemma dist_siblings (n : ℕ) (e : Edge n) {i j : ℕ} (hij : i ≠ j) :
    (graph (n+1)).dist (Sum.inr (e,i)) (Sum.inr (e,j))=2 := by
  apply le_antisymm
  · exact SimpleGraph.dist_le (.cons (adj_old_mid.mpr (Or.inl rfl)).symm
      (.cons (adj_old_mid.mpr (Or.inl rfl)) .nil))
  · apply Nat.succ_le_of_lt
    apply (connected (n+1)).one_lt_dist_of_ne_of_not_adj
    · intro h
      exact hij (Prod.mk.inj (Sum.inr.inj h)).2
    · exact not_adj_new _ _

lemma distance_old (n : ℕ) (u v : Vertex n) :
    distance (n+1) (Sum.inl u) (Sum.inl v)=distance n u v := by
  rw [distance,distance,dist_old,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
  field_simp

lemma distance_edge (n : ℕ) (e : Edge n) :
    distance n (endpoint n e false) (endpoint n e true)=1/(2:ℝ)^n := by
  rw [distance,SimpleGraph.dist_eq_one_iff_adj.mpr (adj_endpoint n e),Nat.cast_one,Nat.cast_ofNat]

lemma distance_siblings (n : ℕ) (e : Edge n) {i j : ℕ} (hij : i ≠ j) :
    distance (n+1) (Sum.inr (e,i)) (Sum.inr (e,j))=2/(2:ℝ)^(n+1) := by
  rw [distance,dist_siblings n e hij,Nat.cast_ofNat]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma slope_plus_deviation {n : ℕ} (f : Vertex (n+1) → X) (e : Edge n) (i : ℕ) :
    slope (fun v => f (Sum.inl v)) e+deviation f e i=slope f (e,i,false) := by
  dsimp [slope,deviation,endpoint]
  rw [pow_succ]
  module

lemma slope_minus_deviation {n : ℕ} (f : Vertex (n+1) → X) (e : Edge n) (i : ℕ) :
    slope (fun v => f (Sum.inl v)) e-deviation f e i=slope f (e,i,true) := by
  dsimp [slope,deviation,endpoint]
  rw [pow_succ]
  module

lemma deviation_sub {n : ℕ} (f : Vertex (n+1) → X) (e : Edge n) (i j : ℕ) :
    deviation f e i-deviation f e j=
      (2:ℝ)^(n+1) • (f (Sum.inr (e,i))-f (Sum.inr (e,j))) := by
  dsimp [deviation]
  rw [pow_succ]
  module

lemma deviation_separated {n : ℕ} (f : Vertex (n+1) → X) {s : ℝ}
    (hl : ∀ u v,s*distance (n+1) u v ≤ ‖f u-f v‖) (e : Edge n)
    {i j : ℕ} (hij : i ≠ j) : 2*s ≤ ‖deviation f e i-deviation f e j‖ := by
  rw [deviation_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(2:ℝ)^(n+1))]
  calc
    2*s = (2:ℝ)^(n+1)*(s*distance (n+1) (Sum.inr (e,i)) (Sum.inr (e,j))) := by
      rw [distance_siblings n e hij]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hl _ _) (by positivity)

/-- Supremum-free squared stretch-loss induction. The bound on all final-edge
    slopes loses s²/4 at each backward step. No maximum child is used. -/
lemma squared_stretch_loss (hX : QuadraticLens X) (k : ℕ) (f : Vertex k → X)
    {s B : ℝ} (hs : 0 < s)
    (hl : ∀ u v,s*distance k u v ≤ ‖f u-f v‖)
    (hb : ∀ e,‖slope f e‖^2 ≤ B) : s^2*(1+(k:ℝ)/4) ≤ B := by
  induction k generalizing B with
  | zero =>
    have h := hl (endpoint 0 () false) (endpoint 0 () true)
    rw [distance_edge] at h
    have h0 := hb ()
    simp only [slope,pow_zero,one_smul,norm_sub_rev] at h0
    norm_num at h ⊢
    nlinarith [sq_nonneg (s-‖f (endpoint 0 () false)-f (endpoint 0 () true)‖)]
  | succ n ih =>
    have hB : 0 ≤ B := (sq_nonneg _).trans (hb (baseEdge (n+1)))
    have hold : ∀ e,‖slope (fun v => f (Sum.inl v)) e‖^2 ≤ B-s^2/4 := by
      intro e
      have hp : ∀ i,‖slope (fun v => f (Sum.inl v)) e+deviation f e i‖ ≤ Real.sqrt B := by
        intro i
        rw [slope_plus_deviation]
        exact (Real.le_sqrt (norm_nonneg _) hB).mpr (hb _)
      have hm : ∀ i,‖slope (fun v => f (Sum.inl v)) e-deviation f e i‖ ≤ Real.sqrt B := by
        intro i
        rw [slope_minus_deviation]
        exact (Real.le_sqrt (norm_nonneg _) hB).mpr (hb _)
      have h := hX (slope (fun v => f (Sum.inl v)) e) (deviation f e)
        (Real.sqrt B) (2*s) (Real.sqrt_nonneg _) (by positivity) hp hm
        (fun _ _ hij => deviation_separated f hl e hij)
      rw [Real.sq_sqrt hB] at h
      nlinarith
    have hlo : ∀ u v,s*distance n u v ≤ ‖f (Sum.inl u)-f (Sum.inl v)‖ := by
      intro u v
      simpa only [distance_old] using hl (Sum.inl u) (Sum.inl v)
    have hind := ih (fun v => f (Sum.inl v)) hlo hold
    push_cast
    linarith

lemma distortion_bound (hX : QuadraticLens X) (k : ℕ) (f : Vertex k → X)
    (D s : ℝ) (h : HasDistortion k f D s) : 1+(k:ℝ)/4 ≤ D^2 := by
  obtain ⟨hD,hs,h⟩ := h
  have hbound : ∀ e,‖slope f e‖^2 ≤ (D*s)^2 := by
    intro e
    have he := (h (endpoint k e false) (endpoint k e true)).2
    rw [distance_edge] at he
    have hh : ‖slope f e‖ ≤ D*s := by
      rw [slope,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(2:ℝ)^k),norm_sub_rev]
      calc
        _ ≤ (2:ℝ)^k*(D*s*(1/(2:ℝ)^k)) := mul_le_mul_of_nonneg_left he (by positivity)
        _ = _ := by field_simp
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) hs.le)).mpr hh
  have hb := squared_stretch_loss hX k f hs (fun u v => (h u v).1) hbound
  have hp : 0 < s^2 := sq_pos_of_pos hs
  have hmul : s^2*(1+(k:ℝ)/4) ≤ s^2*D^2 := by nlinarith only [hb]
  exact (mul_le_mul_iff_right₀ hp).mp hmul

end Diamond

/-- The finite forest lens property follows from the proved pooled estimate and
    the proved approximation of its full dual. -/
theorem forest_quadratic_lens : Diamond.QuadraticLens ForestDual := by
  intro x z R ε hR hε hp hm hs
  exact Ancestry.separated_lens (A := forestAncestry) forest_finite_heads
    (fun η hη => Forest.full_dual_approximation x hη) z hR hε hp hm hs

/-- The infinite-height assertion is only for its closed coordinate span,
    not for the full infinite-height dual. -/
theorem infinite_quadratic_lens : Diamond.QuadraticLens InfinitePredual := by
  intro x z R ε hR hε hp hm hs
  exact Ancestry.separated_lens (A := infiniteAncestry) infinite_finite_heads
    (fun η hη => Ancestry.coordinate_predual_approximation (A := infiniteAncestry)
      infinite_finite_heads x.property hη) (fun i => (z i).val) hR hε hp hm hs

theorem headline : Headline := by
  constructor
  · exact fun k f D s h => Diamond.distortion_bound forest_quadratic_lens k f D s h
  · exact fun k f D s h => Diamond.distortion_bound infinite_quadratic_lens k f D s h

end DiamondDistortion

end

end OAI
end

section
-- module Solutions.OAIQW_DiamondDistortion.StartModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace StartModel

section
/-- A local bundle used only to recurse over the finite tree height. -/
structure RealNormed where
  carrier : Type
  [group : NormedAddCommGroup carrier]
  [space : NormedSpace ℝ carrier]
attribute [instance] RealNormed.group RealNormed.space
instance instCoeSortRealNormedType : CoeSort RealNormed Type := ⟨RealNormed.carrier⟩

end

end StartModel

end DiamondDistortion

end

end OAI
end

section
-- module Solutions.OAIQW_DiamondDistortion.Descent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace Diamond
variable {X : Type*} [NormedAddCommGroup X]
/-- The redundant conventional condition D≥1 follows from the
    all-pairs inequalities alone; thus HasDistortion adds no standing hypothesis. -/
lemma hasDistortion_iff_all_pairs {k : ℕ} (f : Vertex k → X) (D s : ℝ) :
    HasDistortion k f D s ↔ 0 < s ∧ ∀ u v,
      s*distance k u v ≤ ‖f u-f v‖ ∧ ‖f u-f v‖ ≤ D*s*distance k u v := by
  constructor
  · exact fun h => h.2
  · rintro ⟨hs,h⟩
    have hh := (h (endpoint k (baseEdge k) false) (endpoint k (baseEdge k) true)).1.trans
      (h (endpoint k (baseEdge k) false) (endpoint k (baseEdge k) true)).2
    rw [distance_edge] at hh
    have hp : 0 < s*(1/(2:ℝ)^k) := by positivity
    have hD : 1 ≤ D := (mul_le_mul_iff_left₀ hp).mp (by calc
      (1:ℝ)*(s*(1/(2:ℝ)^k)) = s*(1/(2:ℝ)^k) := one_mul _
      _ ≤ D*s*(1/(2:ℝ)^k) := hh
      _ = D*(s*(1/(2:ℝ)^k)) := by ring)
    exact ⟨hD,hs,h⟩
end Diamond

theorem headline_all_pairs_oai :
    (∀ (k : ℕ) (f : Diamond.Vertex k → ForestDual) (D s : ℝ),
      0 < s → (∀ u v,s*Diamond.distance k u v ≤ ‖f u-f v‖ ∧
        ‖f u-f v‖ ≤ D*s*Diamond.distance k u v) → 1+(k:ℝ)/4 ≤ D^2) ∧
    (∀ (k : ℕ) (f : Diamond.Vertex k → InfinitePredual) (D s : ℝ),
      0 < s → (∀ u v,s*Diamond.distance k u v ≤ ‖f u-f v‖ ∧
        ‖f u-f v‖ ≤ D*s*Diamond.distance k u v) → 1+(k:ℝ)/4 ≤ D^2) := by
  constructor
  · intro k f D s hs h
    exact headline.1 k f D s ((Diamond.hasDistortion_iff_all_pairs f D s).mpr ⟨hs,h⟩)
  · intro k f D s hs h
    exact headline.2 k f D s ((Diamond.hasDistortion_iff_all_pairs f D s).mpr ⟨hs,h⟩)

end DiamondDistortion

end

end OAI
end

theorem solution : type_of% @OAI.DiamondDistortion.headline_all_pairs_oai := @OAI.DiamondDistortion.headline_all_pairs_oai
