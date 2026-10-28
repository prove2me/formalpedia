-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.physical_old_estimates_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:12:02.604781+00:00
-- url     : https://prove2.me/submissions/5a1bb65d-cfe3-409a-bc9f-97ac4ca1e4f9

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K036
import Theorems.Thm_OAI_MetricKMedian_Preparation_shortfall_from_deviation_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

omit [Fintype Ξ] in
theorem variance_const (μ : FiniteLaw Ω) (c : ℝ) : μ.variance (fun _ => c)=0 := by
  rw [variance_eq, expect_const, expect_const, sub_self]

end MetricKMedian.FiniteLaw

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

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

omit [Fintype I] [Fintype T] [DecidableEq T] in

theorem rescaled_subset_mean {Ξ : Type} [Fintype Ξ] (μ : FiniteLaw Ξ)
    (Y : Ξ → T × I → ℝ) (P : T → Finset I) (y : I → ℝ) (p p' : T → ℝ)
    (hm : ∀ t i, μ.expect (fun ξ => Y ξ (t,i))=if i ∈ P t then p' t*y i/p t else 0)
    (F : Finset I) (d : I → ℝ) (t : T) :
    μ.expect (fun ξ => ∑ i ∈ F, Y ξ (t,i)*d i)=
      (p' t/p t)*(∑ i ∈ F ∩ P t, y i*d i) := by
  rw [FiniteLaw.expect_sum]
  simp_rw [FiniteLaw.expect_mul_right,hm]
  have he : ∀ i, (if i ∈ P t then p' t*y i/p t else 0)*d i=
      if i ∈ P t then (p' t/p t)*(y i*d i) else 0 := by
    intro i
    split_ifs <;> ring
  simp_rw [he]
  rw [sum_ite_mem,mul_sum]

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationOldCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T Ω Ξ : Type} [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype Ω] [Fintype Ξ]

omit [DecidableEq T] in

theorem preparation_old_cost (ν : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ)
    (P : T → Finset I) (y d : I → ℝ) (p : T → ℝ) (p' : Ω → T → ℝ)
    (U : Ω → I → ℝ) (Y : Ω → Ξ → T × I → ℝ) (F : Finset I) {p₀ : ℝ}
    (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hp : ∀ t, p₀ ≤ p t) (hcap : ∀ ω t, p' ω t ≤ 1)
    (hUm : ∀ i, ν.expect (fun ω => U ω i)=y i)
    (hYm : ∀ ω t i, (κ ω).expect (fun ξ => Y ω ξ (t,i))=
      if i ∈ P t then p' ω t*y i/p t else 0) :
    (ν.joint κ).expect (fun z =>
      (∑ i ∈ F ∩ SupplierStars.outside P, U z.1 i*d i)+
      (∑ t, ∑ i ∈ F, Y z.1 z.2 (t,i)*d i)) ≤ (∑ i ∈ F, y i*d i)/p₀ := by
  let a := fun t => ∑ i ∈ F ∩ P t, y i*d i
  let u := ∑ i ∈ F ∩ SupplierStars.outside P, y i*d i
  have ha : ∀ t, 0 ≤ a t := fun t => sum_nonneg (fun i _ => mul_nonneg (hy i) (hd i))
  have hu : 0 ≤ u := sum_nonneg (fun i _ => mul_nonneg (hy i) (hd i))
  have hpart : u+(∑ t, a t)=∑ i ∈ F, y i*d i := SupplierStars.mass_partition (fun i => y i*d i) P hP F
  have hinner : ∀ ω, (κ ω).expect (fun ξ => ∑ t, ∑ i ∈ F, Y ω ξ (t,i)*d i)=
      ∑ t, (p' ω t/p t)*a t := by
    intro ω
    rw [FiniteLaw.expect_sum]
    exact sum_congr rfl (fun t _ => rescaled_subset_mean (κ ω) (Y ω) P y p (p' ω) (hYm ω) F d t)
  have hbound : ∀ ω, (∑ t, (p' ω t/p t)*a t) ≤ (∑ t, a t)/p₀ := by
    intro ω
    rw [sum_div]
    apply sum_le_sum
    intro t _
    have hpp : 0 < p t := hp₀.trans_le (hp t)
    calc
      (p' ω t/p t)*a t ≤ (1/p t)*a t := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hcap ω t) hpp.le) (ha t)
      _ ≤ (1/p₀)*a t := mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hp₀ (hp t)) (ha t)
      _ = a t/p₀ := by ring
  have hout : ν.expect (fun ω => ∑ i ∈ F ∩ SupplierStars.outside P, U ω i*d i)=u := by
    rw [FiniteLaw.expect_sum]
    simp only [FiniteLaw.expect_mul_right,hUm,u]
  rw [FiniteLaw.expect_joint]
  simp only [FiniteLaw.expect_add,FiniteLaw.expect_const,hinner]
  rw [hout]
  have he := (ν.expect_mono hbound).trans_eq (ν.expect_const _)
  have hue : u ≤ u/p₀ := (le_div_iff₀ hp₀).mpr (mul_le_of_le_one_right hu hp₀1)
  calc
    _ ≤ u/p₀+(∑ t, a t)/p₀ := add_le_add hue he
    _ = (u+∑ t, a t)/p₀ := (add_div _ _ _).symm
    _ = _ := by rw [hpart]

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_CoupledNoise
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

theorem nominal_extension (P A : T → Finset I) (y : I → ℝ) (p c : T → ℝ)
    {g γ B : ℝ} {Δ : ℕ} (hg : 0 ≤ g) (hy : ∀ i, 0 ≤ y i)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ) :
    let U := fun ω i => if i ∈ outside P then L.N ω (.inl i) else y i
    (∀ i, L.ν.expect (fun ω => U ω i)=y i) ∧
    (∀ i, L.ν.variance (fun ω => U ω i) ≤ g*y i) ∧
    (∀ i j, i ≠ j → L.ν.expect (fun ω => U ω i*U ω j) ≤ y i*y j) := by
  classical
  dsimp only
  have hm : ∀ i, i ∈ outside P → L.ν.expect (fun ω => L.N ω (.inl i))=y i := by
    intro i hi
    simpa only [weight,ite_eq_left hi] using L.nominal_mean (.inl i)
  refine ⟨?_,?_,?_⟩
  · intro i
    by_cases hi : i ∈ outside P
    · simp only [ite_eq_left hi,hm i hi]
    · simp only [ite_eq_right hi,FiniteLaw.expect_const]
  · intro i
    by_cases hi : i ∈ outside P
    · simp only [ite_eq_left hi]
      simpa only [weight,ite_eq_left hi] using L.nominal_variance (.inl i)
    · simp only [ite_eq_right hi,FiniteLaw.variance_const]
      exact mul_nonneg hg (hy i)
  · intro i j hij
    by_cases hi : i ∈ outside P <;> by_cases hj : j ∈ outside P
    · simp only [ite_eq_left hi,ite_eq_left hj]
      simpa only [weight,ite_eq_left hi,ite_eq_left hj] using L.nominal_pair (.inl i) (.inl j)
        (fun h => hij (Sum.inl.inj h))
    · simp only [ite_eq_left hi,ite_eq_right hj,FiniteLaw.expect_mul_right,hm i hi,le_refl]
    · simp only [ite_eq_right hi,ite_eq_left hj,FiniteLaw.expect_mul,hm j hj,le_refl]
    · simp only [ite_eq_right hi,ite_eq_right hj,FiniteLaw.expect_const,le_refl]

theorem coupled_old_estimates (P A : T → Finset I) (y : I → ℝ) (p c : T → ℝ)
    {g γ B p₀ : ℝ} {Δ : ℕ} (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hy : ∀ i, 0 ≤ y i) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hp : ∀ t, p₀ ≤ p t)
    (_hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (F : Finset I) (hF : ∑ i ∈ F, y i=1) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    let μ := L.ν.joint L.κ
    let U := fun ω i => if i ∈ outside P then L.N ω (.inl i) else y i
    let Y := fun ω ξ ti => g*(L.C ω ξ ti:ℝ)
    μ.expect (fun z => max
      (1-(∑ i ∈ F ∩ outside P, U z.1 i)-(∑ t, ∑ i ∈ F, Y z.1 z.2 (t,i))) 0) ≤
      Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀ ∧
    μ.expect (fun z => (∑ i ∈ F ∩ outside P, U z.1 i*d i)+
      (∑ t, ∑ i ∈ F, Y z.1 z.2 (t,i)*d i)) ≤ (∑ i ∈ F, y i*d i)/p₀ := by
  classical
  dsimp only
  obtain ⟨hUm,hUv,hUp⟩ := nominal_extension P A y p c hg hy L
  have hcap : ∀ ω t, g*(L.K ω t:ℝ) ≤ 1 := fun ω t =>
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (L.total_cap ω t)) hg).trans_eq hunit
  have hdev : ∀ t, L.ν.expect (fun ω => |g*(L.K ω t:ℝ)-p t|) ≤ γ+Real.sqrt (g*(1+γ)) := by
    intro t
    apply (L.total_deviation t).trans
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_left (hc1 t) hγ).trans_eq (mul_one _)
    · exact Real.sqrt_le_sqrt ((mul_le_mul_of_nonneg_left (hc1 t)
        (mul_nonneg hg (by linarith only [hγ]))).trans_eq (mul_one _))
  constructor
  · exact shortfall_from_deviation_s35 L.ν L.κ P y p
      (fun ω t => g*(L.K ω t:ℝ))
      (fun ω i => if i ∈ outside P then L.N ω (.inl i) else y i)
      (fun ω ξ ti => g*(L.C ω ξ ti:ℝ)) F hg hγ hp₀ hy hF hP hp hcap hdev
      hUm hUv hUp L.piece_mean L.piece_variance L.piece_pair
  · exact preparation_old_cost L.ν L.κ P y d p
      (fun ω t => g*(L.K ω t:ℝ))
      (fun ω i => if i ∈ outside P then L.N ω (.inl i) else y i)
      (fun ω ξ ti => g*(L.C ω ξ ti:ℝ)) F hy hd hp₀ hp₀1 hP hp hcap hUm L.piece_mean

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalOldMass
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

 theorem old_mass_id {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (F : Finset I) (z : L.Ω × (T → Finset I)) :
    (∑ a, oldAssignment L F z a)=
      (∑ i ∈ F ∩ outside P, (if i ∈ outside P then L.N z.1 (.inl i) else y i))+
      (∑ t, ∑ i ∈ F, g*(L.C z.1 z.2 (t,i):ℝ)) := by
  simp only [oldAssignment,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Sum.elim_inl,Sum.elim_inr,sum_ite_mem,univ_inter]
  congr 1
  apply sum_congr rfl
  intro i hi
  exact (ite_eq_left (mem_inter.mp hi).2).symm

 theorem old_cost_id {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (F : Finset I) (z : L.Ω × (T → Finset I)) (d : I → ℝ) :
    (∑ a, oldAssignment L F z a*(Sum.elim d (fun ti => d ti.2) a))=
      (∑ i ∈ F ∩ outside P, (if i ∈ outside P then L.N z.1 (.inl i) else y i)*d i)+
      (∑ t, ∑ i ∈ F, (g*(L.C z.1 z.2 (t,i):ℝ))*d i) := by
  simp only [oldAssignment,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Sum.elim_inl,Sum.elim_inr,ite_mul,zero_mul,sum_ite_mem,univ_inter]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [ite_eq_left (mem_inter.mp hi).2]

theorem physical_old_estimates_s35_oai {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ}
    {g γ B p₀ : ℝ} {Δ : ℕ} (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hy : ∀ i, 0 ≤ y i) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hp : ∀ t, p₀ ≤ p t)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (F : Finset I) (hF : ∑ i ∈ F, y i=1) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (L.ν.joint L.κ).expect (fun z => max (1-∑ a, oldAssignment L F z a) 0) ≤
      Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀ ∧
    (L.ν.joint L.κ).expect (fun z => ∑ a, oldAssignment L F z a*(Sum.elim d (fun ti => d ti.2) a)) ≤
      (∑ i ∈ F, y i*d i)/p₀ := by
  have he := coupled_old_estimates P A y p c hg hγ hunit L hy hp₀ hp₀1 hp hc0 hc1 hP F hF d hd
  dsimp only at he
  simpa only [old_mass_id,old_cost_id,sub_add_eq_sub_sub] using he

end MetricKMedian.Preparation
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.physical_old_estimates_s35_oai := @OAI.MetricKMedian.Preparation.physical_old_estimates_s35_oai
