-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.RationalBundles.scan_geometry_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:42:08.515661+00:00
-- url     : https://prove2.me/submissions/747d1a33-563e-433e-9658-c10b99f1a961

import Mathlib
import Definitions.Def_OAIQ053K078
import Theorems.Thm_OAI_MetricKMedian_Preparation_RationalSuppliers_Data_scan_feasible_s53
import Theorems.Thm_OAI_MetricKMedian_Preparation_distant_assignments_s53
import Theorems.Thm_OAI_MetricKMedian_Preparation_nearby_assignments_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem prob_nonneg (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] : 0 ≤ μ.prob E := by
  apply μ.expect_nonneg
  intro ω
  split_ifs <;> norm_num

end FiniteLaw

end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_Conditioning
attribute [-simp] _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω : Type*} [Fintype Ω]

 theorem condition_support (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) (ω : Ω) :
    0 < (condition μ P hP).weight ω ↔ P ω ∧ 0 < μ.weight ω := by
  change 0 < (if P ω then μ.weight ω/μ.prob P else 0) ↔ P ω ∧ 0 < μ.weight ω
  split_ifs with hp
  · simp only [hp, true_and]
    exact div_pos_iff_of_pos_right hP
  · simp [hp]

 theorem condition_expect_le (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    (condition μ P hP).expect f ≤ μ.expect f/μ.prob P := by
  have he : (condition μ P hP).expect f=
      μ.expect (fun ω => if P ω then f ω else 0)/μ.prob P := by
    unfold expect condition
    simp only [sum_div]
    apply sum_congr rfl
    intro ω _
    split_ifs <;> simp [div_mul_eq_mul_div]
  rw [he]
  apply div_le_div_of_nonneg_right _ hP.le
  apply μ.expect_mono
  intro ω
  split_ifs
  · exact le_rfl
  · exact hf ω

 theorem exists_support_le_expect (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    ∃ ω, 0 < μ.weight ω ∧ f ω ≤ μ.expect f := by
  classical
  have hn : ∃ ω, 0 < μ.weight ω := by
    by_contra h
    push Not at h
    have hz : ∀ ω, μ.weight ω=0 := fun ω => le_antisymm (h ω) (μ.nonneg ω)
    have ht := μ.total
    simp only [hz, sum_const_zero] at ht
    norm_num at ht
  by_contra h
  push Not at h
  have hs : μ.expect (fun _ => μ.expect f) < μ.expect f := by
    apply sum_lt_sum
    · intro ω _
      by_cases hp : 0 < μ.weight ω
      · exact mul_le_mul_of_nonneg_left (h ω hp).le (μ.nonneg ω)
      · rw [le_antisymm (le_of_not_gt hp) (μ.nonneg ω), zero_mul, zero_mul]
    · obtain ⟨ω,hω⟩ := hn
      exact ⟨ω, mem_univ _, mul_lt_mul_of_pos_left (h ω hω) hω⟩
  rw [expect_const] at hs
  exact lt_irrefl _ hs

theorem select_success (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    ∃ ω, 0 < μ.weight ω ∧ P ω ∧ f ω ≤ μ.expect f/μ.prob P := by
  obtain ⟨ω,hω,hfω⟩ := (condition μ P hP).exists_support_le_expect f
  obtain ⟨hp,hw⟩ := (condition_support μ P hP ω).mp hω
  exact ⟨ω,hw,hp,hfω.trans (condition_expect_le μ P hP f hf)⟩

 theorem select_success_bound (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (f : Ω → ℝ) {p C : ℝ} (hp : 0 < p) (hP : p ≤ μ.prob P)
    (hf : ∀ ω, 0 ≤ f ω) (hE : μ.expect f ≤ C) :
    ∃ ω, 0 < μ.weight ω ∧ P ω ∧ f ω ≤ C/p := by
  obtain ⟨ω,hw,hgood,hcost⟩ := select_success μ P (hp.trans_le hP) f hf
  refine ⟨ω,hw,hgood,hcost.trans ?_⟩
  exact (div_le_div_of_nonneg_right hE (prob_nonneg μ P)).trans
    (div_le_div_of_nonneg_left ((μ.expect_nonneg hf).trans hE) hp hP)

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteJoint
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

theorem expect_joint (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (f : Ω × Ξ → ℝ) :
    (joint μ κ).expect f=μ.expect (fun ω => (κ ω).expect (fun ξ => f (ω, ξ))) := by
  simp only [expect, joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem support_joint (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (z : Ω × Ξ)
    (h : 0 < (joint μ κ).weight z) : 0 < μ.weight z.1 ∧ 0 < (κ z.1).weight z.2 := by
  exact ⟨pos_of_mul_pos_left h ((κ z.1).nonneg z.2), pos_of_mul_pos_right h (μ.nonneg z.1)⟩

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_CoupledGeometry
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

theorem physical_cap {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (hy1 : ∀ i, y i ≤ 1)
    (z : L.Ω × (T → Finset I)) (hz : 0 < (L.ν.joint L.κ).weight z) :
    ∀ a, 0 ≤ physicalOpen L z a ∧ physicalOpen L z a ≤ 1 := by
  obtain ⟨hω,hξ⟩ := L.ν.support_joint L.κ z hz
  intro a
  refine ⟨mul_nonneg hg (Nat.cast_nonneg _),?_⟩
  cases a with
  | inl i =>
    apply L.open_cap z.1 hω (.inl i)
    dsimp only [weight]
    split_ifs
    · exact hy1 i
    · norm_num
  | inr ti =>
    exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ((L.pieces z.1 z.2 hξ ti.1).2.1 ti.2)) hg).trans_eq hunit

theorem physical_mass {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (z : L.Ω × (T → Finset I)) (hξ : 0 < (L.κ z.1).weight z.2) :
    (∑ a, physicalOpen L z a)=
      (∑ e, flag e*(g*(L.O z.1 e:ℝ)))+(∑ t, g*(L.K z.1 t:ℝ)) := by
  simp only [physicalOpen,physicalCount,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    flag,one_mul,zero_mul,sum_const_zero,add_zero,Fintype.sum_prod_type]
  congr 1
  apply sum_congr rfl
  intro t _
  rw [← mul_sum,← Nat.cast_sum,(L.pieces z.1 z.2 hξ t).1]

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_NearestAssignmentGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

omit [Fintype I] [DecidableEq I] in

theorem assignment_radius (F : Finset I) (y : I → ℝ) (d : I → ℝ)
    (hunit : ∑ a ∈ F, y a=1) (hd : ∀ a, 0 ≤ d a)
    (hnearest : ∀ a ∈ F, ∀ b ∉ F, d a ≤ d b) :
    ∃ R : ℝ, 0 ≤ R ∧ (∃ a ∈ F, R=d a) ∧
      (∀ a ∈ F, d a ≤ R) ∧ (∀ b ∉ F, R ≤ d b) := by
  have hF : F.Nonempty := by
    by_contra he
    rw [not_nonempty_iff_eq_empty.mp he,sum_empty] at hunit
    exact zero_ne_one hunit
  obtain ⟨a,ha,hmax⟩ := exists_max_image F d hF
  exact ⟨d a,hd a,⟨a,ha,rfl⟩,hmax,fun b hb => hnearest a ha b hb⟩

omit [Fintype I] [Fintype T] [DecidableEq T] in
theorem assigned_radius_ge {F : T → Finset I} {y : I → ℝ} {s : T → X} {i : I → X}
    {V : T → ℝ} {M δ : ℝ} (G : BundleGeometry F y s i V M δ)
    (hδ1 : δ ≤ 1) (t : T) {R : ℝ} (hR : 0 ≤ R)
    (hmax : ∀ a ∈ F t, dist (s t) (i a) ≤ R) :
    δ*relevantRadius (G.c t) (G.L t) R ≤ R := by
  dsimp only [relevantRadius]
  split_ifs with hc
  · have hn : G.next t ≠ t := fun ht => (ne_of_gt hc) (G.self_zero t ht)
    have hA : (G.A t).Nonempty := by
      by_contra he
      have hz := G.deficit_mass t
      rw [not_nonempty_iff_eq_empty.mp he,sum_empty] at hz
      exact (ne_of_gt hc) hz.symm
    obtain ⟨a,ha⟩ := hA
    have haF : a ∈ F t := (mem_sdiff.mp ((G.missing t) ▸ ha)).1
    exact (G.outside_radius t hn a ha).le.trans (hmax a haF)
  · exact mul_le_of_le_one_left hR hδ1

theorem distant_scales {c L R M δ T₁ v D : ℝ}
    (_hc : 0 ≤ c) (hM : 0 ≤ M) (hδ : 0 < δ) (hT : 0 < T₁)
    (hD : D ≤ M*v) (hR : δ*relevantRadius c L R ≤ R)
    (hfar : T₁*v < relevantRadius c L R) :
    D ≤ (M/(δ*T₁))*R ∧ (0 < c → D ≤ (M/T₁)*L) := by
  have hv : v ≤ relevantRadius c L R/T₁ := (le_div_iff₀ hT).mpr (by nlinarith only [hfar])
  have hr : relevantRadius c L R ≤ R/δ := (le_div_iff₀ hδ).mpr (by nlinarith only [hR])
  constructor
  · calc
      D ≤ M*v := hD
      _ ≤ M*(relevantRadius c L R/T₁) := mul_le_mul_of_nonneg_left hv hM
      _ ≤ M*((R/δ)/T₁) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hr hT.le) hM
      _ = _ := by ring
  · intro hc'
    have hL : relevantRadius c L R=L := ite_eq_left hc'
    rw [hL] at hv
    exact (hD.trans (mul_le_mul_of_nonneg_left hv hM)).trans_eq (by ring)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationClientAssignments
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

theorem client_assignments (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ T₁ g γ B v : ℝ} {Δ : ℕ}
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c g γ B Δ)
    (hy : ∀ a, 0 ≤ y a) (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1/4)
    (hT : 0 < T₁) (hθ : 1/(M*δ) ≤ 1/8) (hα : M/(δ*T₁) ≤ 1/4)
    (hg : 0 < g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (j : X) (t : T) (Fj : Finset I) (hmj : ∑ a ∈ Fj, y a=1)
    (hms : ∑ a ∈ F t, y a=1) (hvj : ∑ a ∈ Fj, y a*dist j (i a)=v)
    (hnearest : ∀ a ∈ F t, ∀ b ∉ F t, dist (s t) (i a) ≤ dist (s t) (i b))
    (hV : V t ≤ v) (hD : dist j (s t) ≤ M*v) :
    let p₀ := 1-1/(M*δ)
    ∃ r : (L.Ω × (T → Finset I)) → Physical I T → ℝ,
      (∀ z, 0 < (L.ν.joint L.κ).weight z →
        (∀ a, 0 ≤ r z a ∧ r z a ≤ physicalOpen L z a) ∧ (∑ a, r z a)=1) ∧
      (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*
        (Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2)) a)) ≤
        max (farFactor δ p₀ (M/(δ*T₁)) (M/T₁) γ)
          (nearFactor p₀ (M+(1+δ)*T₁) γ g)*v := by
  dsimp only
  have hp₀ : 0 < 1-1/(M*δ) := by linarith only [hθ]
  have hp₀1 : 1-1/(M*δ) ≤ 1 := sub_le_self _ (by positivity)
  have hv : 0 ≤ v := (sum_nonneg (fun a _ => mul_nonneg (hy a) dist_nonneg)).trans_eq hvj
  obtain ⟨R,hR,_,hmax,hmin⟩ := assignment_radius (F t) y (fun a => dist (s t) (i a))
    hms (fun _ => dist_nonneg) hnearest
  by_cases hnear : relevantRadius (G.c t) (G.L t) R ≤ T₁*v
  · have hL : 0 < G.c t → G.L t ≤ T₁*v := by
      intro hc
      simpa only [relevantRadius,ite_eq_left hc] using hnear
    have hRad : G.c t=0 → ∀ a ∈ F t, dist (s t) (i a) ≤ T₁*v := by
      intro hc a ha
      have hr : R ≤ T₁*v := by simpa only [relevantRadius,hc,lt_self_iff_false,ite_false] using hnear
      exact (hmax a ha).trans hr
    obtain ⟨r,hr,hc⟩ := nearby_assignments_s53 F y s i V G L hy hM.le hδ.le hT.le hg.le hγ hunit
      hp₀ hp₀1 G.large j t Fj hmj hvj hD hL hRad
    exact ⟨r,hr,hc.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hv)⟩
  · have hscale := distant_scales (G.nonneg t) hM.le hδ hT hD
      (assigned_radius_ge G (by linarith only [hδ1]) t hR hmax) (lt_of_not_ge hnear)
    have hb : M/T₁=δ*(M/(δ*T₁)) := by field_simp
    have hb0 : 0 ≤ M/T₁ := by positivity
    have hb1 : M/T₁ ≤ 1/4 := by
      rw [hb]
      calc
        δ*(M/(δ*T₁)) ≤ δ*(1/4) := mul_le_mul_of_nonneg_left hα hδ.le
        _ ≤ 1/4 := by linarith only [hδ1]
    have hsep : M/T₁+δ < 1 := by linarith only [hb1,hδ1]
    obtain ⟨r,hr,hc⟩ := distant_assignments_s53 F y s i V G L hy hδ hb0 hsep hg hγ hunit
      hp₀ G.large (by positivity) (by linarith only [hα]) j t Fj hmj hms hvj hV R hscale.1 hmax hmin hscale.2
    exact ⟨r,hr,hc.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)⟩

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SelectedPreparationOutcome
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T J X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [Fintype J] [Nonempty J] [PseudoMetricSpace X]

theorem selected_preparation_outcome (F : T → Finset I) (Fj : J → Finset I) (y : I → ℝ)
    (s : T → X) (j : J → X) (i : I → X) (V : T → ℝ) (v : J → ℝ) (rep : J → T)
    {M δ T₁ g γ : ℝ} {Δ : ℕ}
    (hy : ∀ a, 0 < y a) (hy1 : ∀ a, y a ≤ 1)
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1/4) (hT : 0 < T₁)
    (hθ : 1/(M*δ) ≤ 1/8) (hα : M/(δ*T₁) ≤ 1/4)
    (hg : 0 < g) (hγ : 0 < γ) (_ : γ ≤ 1) (_ : Even Δ) (hunit : g*(Δ:ℝ)=1)
    (hfail : failureFactor γ g < 1)
    (hsunit : ∀ t, ∑ a ∈ F t, y a=1)
    (hjunit : ∀ c, ∑ a ∈ Fj c, y a=1)
    (_ : ∀ t, ∑ a ∈ F t, y a*dist (s t) (i a)=V t)
    (hjcost : ∀ c, ∑ a ∈ Fj c, y a*dist (j c) (i a)=v c)
    (hnearest : ∀ t, ∀ a ∈ F t, ∀ b ∉ F t, dist (s t) (i a) ≤ dist (s t) (i b))
    (_ : ∀ t u, t ≠ u → M*max (V t) (V u) < dist (s t) (s u))
    (hrepV : ∀ c, V (rep c) ≤ v c) (hrepD : ∀ c, dist (j c) (s (rep c)) ≤ M*v c)
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c
      g γ (∑ a, y a) Δ) :
    ∃ z : L.Ω × (T → Finset I), 0 < (L.ν.joint L.κ).weight z ∧
    ∃ r : J → Physical I T → ℝ,
      let n := physicalCount L z;
      (∀ a, n a ≤ Δ) ∧
      1 ≤ ∑ a, g*(n a:ℝ) ∧ (∑ a, g*(n a:ℝ)) ≤ (∑ a, y a)+3*g ∧
      (∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ g*(n a:ℝ)) ∧ (∑ a, r c a)=1) ∧
      (∑ c, ∑ a, r c a*dist (j c) (Sum.elim i (fun ti => i ti.2) a)) ≤
        (max (farFactor δ (1-1/(M*δ)) (M/(δ*T₁)) (M/T₁) γ)
        (nearFactor (1-1/(M*δ)) (M+(1+δ)*T₁) γ g)/(1-failureFactor γ g))*(∑ c, v c) := by
  classical
  let μ := L.ν.joint L.κ
  let H := max (farFactor δ (1-1/(M*δ)) (M/(δ*T₁)) (M/T₁) γ)
    (nearFactor (1-1/(M*δ)) (M+(1+δ)*T₁) γ g)
  choose r hr hc using fun c => client_assignments F y s i V G L (fun a => (hy a).le)
    hM hδ hδ1 hT hθ hα hg hγ.le hunit (j c) (rep c) (Fj c) (hjunit c)
    (hsunit (rep c)) (hjcost c) (hnearest (rep c)) (hrepV c) (hrepD c)
  let cost := fun z => ∑ c, ∑ a, r c z a*dist (j c) (Sum.elim i (fun ti => i ti.2) a)
  have hcost0 : ∀ z, 0 < μ.weight z → 0 ≤ cost z := by
    intro z hz
    exact sum_nonneg (fun c _ => sum_nonneg (fun a _ => mul_nonneg ((hr c z hz).1 a).1 dist_nonneg))
  have hcost : μ.expect (fun z => max 0 (cost z)) ≤ H*(∑ c, v c) := by
    calc
      _ = μ.expect cost := μ.expect_congr_support (fun z hz => max_eq_right (hcost0 z hz))
      _ = ∑ c, μ.expect (fun z => ∑ a, r c z a*dist (j c) (Sum.elim i (fun ti => i ti.2) a)) :=
        FiniteLaw.expect_sum _ _ _
      _ ≤ ∑ c, H*v c := by
        apply sum_le_sum
        intro c _
        have he : ∀ a : Physical I T, dist (j c) (Sum.elim i (fun ti => i ti.2) a)=
            Sum.elim (fun a => dist (j c) (i a)) (fun ti => dist (j c) (i ti.2)) a := by
          intro a; cases a <;> rfl
        simpa only [← he] using hc c
      _ = _ := (mul_sum _ _ _).symm
  let good := fun z : L.Ω × (T → Finset I) =>
    (∑ e, flag e*(g*(L.O z.1 e:ℝ)))+(∑ t, g*(L.K z.1 t:ℝ)) ≤ (∑ a, y a)+3*g
  have hgood : 1-failureFactor γ g ≤ μ.prob good := by
    have he : μ.prob good=L.ν.prob (fun ω =>
        (∑ e, flag e*(g*(L.O ω e:ℝ)))+(∑ t, g*(L.K ω t:ℝ)) ≤ (∑ a, y a)+3*g) := by
      simp only [FiniteLaw.prob,μ,FiniteLaw.expect_joint,good,FiniteLaw.expect_const]
    rw [he]
    exact L.budget
  obtain ⟨z,hz,hzgood,hzcost⟩ := μ.select_success_bound good (fun z => max 0 (cost z))
    (sub_pos.mpr hfail) hgood (fun _ => le_max_left _ _) hcost
  obtain ⟨_,hξ⟩ := L.ν.support_joint L.κ z hz
  refine ⟨z,hz,fun c => r c z,?_,?_,?_,fun c => hr c z hz,?_⟩
  · intro a
    have ha := (physical_cap L hg.le hunit hy1 z hz a).2
    change g*(physicalCount L z a:ℝ) ≤ 1 at ha
    rw [← hunit] at ha
    exact_mod_cast (mul_le_mul_iff_right₀ hg).mp ha
  · obtain ⟨c⟩ := ‹Nonempty J›
    rw [← (hr c z hz).2]
    exact sum_le_sum (fun a _ => ((hr c z hz).1 a).2)
  · exact (physical_mass L z hξ).le.trans hzgood
  · exact ((le_max_right 0 (cost z)).trans hzcost).trans_eq (by ring)

end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalGeometryScan
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalBundles
open Finset SupplierStars RationalSuppliers
variable {f n j : ℕ} {X : Type} [PseudoMetricSpace X]

 theorem scan_geometry_s53_oai {τ : ℝ} (qR : FixedBatch.RationalParameters τ)
    (heven : Even qR.Δ) (hτ0 : 0<τ) (hτ : τ<1) (hj : 0<j)
    (F : Fin n → Finset (Fin f)) (Fj : Fin j → Finset (Fin f)) (y : Fin f → ℚ)
    (s : Fin n → X) (i : Fin f → X) (client : Fin j → X)
    (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
    (V : Fin n → ℚ) (v : Fin j → ℚ) (rep : Fin j → Fin n) (M δ γ T₁ B : ℚ)
    (hd : ∀ t u, dist (s t) (s u)=(d t u:ℝ))
    (hdi : ∀ t a, dist (s t) (i a)=(di t a:ℝ))
    (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
    (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
    (hy : ∀ a, 0 < y a) (hy1 : ∀ a, y a≤1)
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : (δ:ℝ) ≤ 1/4)
    (hθ : 1/((M:ℝ)*(δ:ℝ)) ≤ 1/8) (hγ : 0<γ) (hγ1 : γ≤1) (hT : 0<T₁)
    (hα : (M:ℝ)/((δ:ℝ)*(T₁:ℝ)) ≤ 1/4)
    (hfail : failureFactor (γ:ℝ) (qR.g:ℝ)<1)
    (hB : (∑ a, (y a:ℝ))+3*(qR.g:ℝ)+(qR.allowance:ℝ) ≤ (B:ℝ))
    (hu : ∀ t, ∑ a ∈ F t, y a=1)
    (hv : ∀ t, ∑ a ∈ F t, y a*di t a=V t)
    (hju : ∀ c, ∑ a ∈ Fj c, y a=1)
    (hjv : ∀ c, ∑ a ∈ Fj c, y a*dc c a=v c)
    (hs : ∀ t u, t ≠ u → M*max (V t) (V u) < d t u)
    (hnearest : ∀ t, ∀ a ∈ F t, ∀ b ∉ F t, di t a≤di t b)
    (hrepV : ∀ c, V (rep c)≤v c) (hrepD : ∀ c, dist (client c) (s (rep c))≤(M:ℝ)*(v c:ℝ)) :
    let D := suppliers F y s i d di V M δ γ hd hdi hy hM hδ (by linarith only [hδ1]) hθ hγ hγ1 hu hv hs;
    ∃ O : Finset (Fin f), D.scan qR df dc B=some O ∧ O.Nonempty ∧
      (O.card:ℝ)≤(B:ℝ) ∧ (Completion.Rational.score dc O:ℝ) ≤
      ((1+2/Real.exp 1+τ)/(1-τ)) *
      (max (farFactor (δ:ℝ) (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)/((δ:ℝ)*(T₁:ℝ))) ((M:ℝ)/(T₁:ℝ)) (γ:ℝ))
        (nearFactor (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)+(1+(δ:ℝ))*(T₁:ℝ)) (γ:ℝ) (qR.g:ℝ)) /
        (1-failureFactor (γ:ℝ) (qR.g:ℝ)))*(∑ c, (v c:ℝ)) := by
  intro D
  let : Nonempty (Fin j) := ⟨⟨0,hj⟩⟩
  let G := geometry F y s i d di V M δ hd hdi hy hM hδ (by linarith only [hδ1]) hu hv hs
  obtain ⟨z,hz,r,hcap,hm,hbudget,hr,hcost⟩ := selected_preparation_outcome F Fj
    (fun a => (y a:ℝ)) s client i (fun t => (V t:ℝ)) (fun c => (v c:ℝ)) rep
    (fun a => by exact_mod_cast hy a) (fun a => by exact_mod_cast hy1 a)
    (by exact_mod_cast hM) (by exact_mod_cast hδ) hδ1 (by exact_mod_cast hT) hθ hα
    qR.gpos (by exact_mod_cast hγ) (by exact_mod_cast hγ1) heven qR.unit hfail
    (fun t => by exact_mod_cast hu t) (fun c => by exact_mod_cast hju c)
    (fun t => by simp only [hdi]; exact_mod_cast hv t)
    (fun c => by simp only [hdc]; exact_mod_cast hjv c)
    (fun t a ha b hb => by simp only [hdi]; exact_mod_cast hnearest t a ha b hb)
    (fun t u htu => by simp only [hd]; exact_mod_cast hs t u htu)
    (fun c => by exact_mod_cast hrepV c) hrepD G (D.coupled qR heven)
  obtain ⟨O,hO,hOn,hOc,hOs⟩ := D.scan_feasible_s53 qR heven hτ hj df dc i client hdf hdc B
    z hz hcap hm (by
      calc
        _ ≤ ((∑ a, (y a:ℝ))+3*(qR.g:ℝ))+(qR.allowance:ℝ) := add_le_add hbudget le_rfl
        _ ≤ (B:ℝ) := hB) r hr
  refine ⟨O,hO,hOn,hOc,?_⟩
  rw [mul_assoc]
  exact hOs.trans (mul_le_mul_of_nonneg_left hcost (by
    apply div_nonneg _ (by linarith only [hτ])
    positivity))

end MetricKMedian.Preparation.RationalBundles
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.RationalBundles.scan_geometry_s53_oai := @OAI.MetricKMedian.Preparation.RationalBundles.scan_geometry_s53_oai
