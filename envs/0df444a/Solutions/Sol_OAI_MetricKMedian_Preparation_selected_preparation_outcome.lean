-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.selected_preparation_outcome
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:42:18.476691+00:00
-- url     : https://prove2.me/submissions/848b97e2-b6fa-4a35-a33f-bdbab2455de3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K036
import Theorems.Thm_OAI_MetricKMedian_Preparation_client_assignments

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteLaws
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
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteJoint
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
-- module Solutions.OAIQ035_KM.KMedian_Preparation_CoupledGeometry
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
-- module Solutions.OAIQ035_KM.KMedian_Probability_Conditioning
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
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SelectedPreparationOutcome
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

theorem selected_preparation_outcome_oai (F : T → Finset I) (Fj : J → Finset I) (y : I → ℝ)
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

theorem solution : type_of% @OAI.MetricKMedian.Preparation.selected_preparation_outcome_oai := @OAI.MetricKMedian.Preparation.selected_preparation_outcome_oai
