-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.nearby_assignments_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:11:18.786982+00:00
-- url     : https://prove2.me/submissions/0954a92b-7acc-4a48-80f1-016245ac6dc6

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K036
import Theorems.Thm_OAI_MetricKMedian_Preparation_physical_old_estimates_s35
import Theorems.Thm_OAI_MetricKMedian_Preparation_support_repaired_cost_s35

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

theorem zero_deficit_total {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (t : T) (hc : c t=0) (hp : p t+c t=1) :
    ∀ ω, 0 < L.ν.weight ω → g*(L.K ω t:ℝ)=1 := by
  have hp' : p t=1 := by simpa only [hc,add_zero] using hp
  have he := L.total_deviation t
  simp only [hp',hc,mul_zero,Real.sqrt_zero,add_zero] at he
  have hz : L.ν.expect (fun ω => |g*(L.K ω t:ℝ)-1|)=0 :=
    le_antisymm he (L.ν.expect_nonneg (fun _ => abs_nonneg _))
  intro ω hω
  exact sub_eq_zero.mp (abs_eq_zero.mp
    (L.ν.nonneg_expect_zero_support _ (fun _ => abs_nonneg _) hz ω hω))

theorem bundle_ball_mass {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hg : 0 ≤ g) (z : L.Ω × (T → Finset I)) (hξ : 0 < (L.κ z.1).weight z.2)
    (d : I → ℝ) (r : ℝ) (H : Finset T) (hH : ∀ t ∈ H, ∀ i ∈ P t, d i ≤ r) :
    (∑ t ∈ H, g*(L.K z.1 t:ℝ)) ≤
      ∑ a ∈ univ.filter (fun a : Physical I T => Sum.elim d (fun ti => d ti.2) a ≤ r),
        physicalOpen L z a := by
  classical
  let f := fun t => ∑ i, if d i ≤ r then g*(L.C z.1 z.2 (t,i):ℝ) else 0
  have hf : ∀ t, 0 ≤ f t := fun t => sum_nonneg (fun i _ => by
    split_ifs <;> [exact mul_nonneg hg (Nat.cast_nonneg _); exact le_rfl])
  have he : ∀ t ∈ H, f t=g*(L.K z.1 t:ℝ) := by
    intro t ht
    rw [← (L.pieces z.1 z.2 hξ t).1,Nat.cast_sum,mul_sum]
    apply sum_congr rfl
    intro i _
    by_cases hi : d i ≤ r
    · exact ite_eq_left hi
    · have hn : i ∉ P t := fun hiP => hi (hH t ht i hiP)
      simp only [ite_eq_right hi,(L.pieces z.1 z.2 hξ t).2.2 i hn,Nat.cast_zero,mul_zero]
  have hsum : (∑ t ∈ H, g*(L.K z.1 t:ℝ)) ≤ ∑ t, f t := by
    calc
      _ = ∑ t ∈ H, f t := sum_congr rfl (fun t ht => (he t ht).symm)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ H) (fun t _ _ => hf t)
  rw [sum_filter,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [Sum.elim_inl,Sum.elim_inr,physicalOpen,physicalCount]
  have hout : 0 ≤ ∑ i, if d i ≤ r then g*(L.O z.1 (.inl i):ℝ) else 0 :=
    sum_nonneg (fun i _ => by
      split_ifs <;> [exact mul_nonneg hg (Nat.cast_nonneg _); exact le_rfl])
  exact hsum.trans (le_add_of_nonneg_left hout)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_NearbyBall
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

theorem nearby_ball (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ g γ B T₁ v : ℝ} {Δ : ℕ}
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c g γ B Δ)
    (hδ : 0 ≤ δ) (hT₁ : 0 ≤ T₁) (hv : 0 ≤ v) (hg : 0 ≤ g)
    (j : X) (t : T) (hD : dist j (s t) ≤ M*v)
    (hL : 0 < G.c t → G.L t ≤ T₁*v)
    (hR : G.c t=0 → ∀ a ∈ F t, dist (s t) (i a) ≤ T₁*v)
    (z : L.Ω × (T → Finset I)) (hz : 0 < (L.ν.joint L.κ).weight z) :
    1 ≤ ∑ a ∈ univ.filter (fun a : Physical I T =>
      Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2)) a ≤
        (M+(1+δ)*T₁)*v), physicalOpen L z a := by
  obtain ⟨hω,hξ⟩ := L.ν.support_joint L.κ z hz
  have hTv := mul_nonneg hT₁ hv
  by_cases hc : G.c t=0
  · have hrad : ∀ a ∈ G.P t, dist j (i a) ≤ (M+(1+δ)*T₁)*v := by
      intro a ha
      have hh := hR hc a (G.sub t ha)
      have htri := dist_triangle j (s t) (i a)
      have hδT := mul_nonneg hδ hTv
      nlinarith only [hh,htri,hD,hδT]
    have hb := bundle_ball_mass L hg z hξ (fun a => dist j (i a))
      ((M+(1+δ)*T₁)*v) {t} (by simpa only [mem_singleton,forall_eq] using hrad)
    simpa only [sum_singleton,zero_deficit_total L t hc (G.unit t) z.1 hω] using hb
  · have hc' : 0 < G.c t := lt_of_le_of_ne (G.nonneg t) (Ne.symm hc)
    have hn : G.next t ≠ t := fun ht => hc (G.self_zero t ht)
    have hLn : G.L (G.next t) ≤ G.L t := by
      calc
        G.L (G.next t) ≤ dist (s (G.next t)) (s t) := G.closest _ _ hn
        _ = G.L t := (dist_comm _ _).trans (G.next_distance t).symm
    have hown : ∀ a ∈ G.P t, dist j (i a) ≤ (M+(1+δ)*T₁)*v := by
      intro a ha
      have hh := (G.radius t hn a ha).trans (mul_le_mul_of_nonneg_left (hL hc') hδ)
      have htri := dist_triangle j (s t) (i a)
      nlinarith only [hh,htri,hD,hTv]
    have hother : ∀ a ∈ G.P (G.next t), dist j (i a) ≤ (M+(1+δ)*T₁)*v := by
      intro a ha
      have hn' : G.next (G.next t) ≠ G.next t := by
        intro ht
        exact hn (G.self_singleton (G.next t) ht t).symm
      have hr := G.radius (G.next t) hn' a ha
      have hr' := hr.trans (mul_le_mul_of_nonneg_left hLn hδ)
      have htri := dist_triangle j (s t) (i a)
      have htri' := dist_triangle (s t) (s (G.next t)) (i a)
      rw [← G.next_distance t] at htri'
      have hδL := mul_le_mul_of_nonneg_left (hL hc') hδ
      nlinarith only [hr',htri,htri',hD,hL hc',hδL]
    have hb := bundle_ball_mass L hg z hξ (fun a => dist j (i a))
      ((M+(1+δ)*T₁)*v) {t,G.next t} (by
        intro u hu
        rcases mem_insert.mp hu with rfl | hu
        · exact hown
        · rw [mem_singleton] at hu
          simpa only [hu] using hother)
    have hh := add_le_add (L.half z.1 t) (L.half z.1 (G.next t))
    have he : (∑ u ∈ ({t,G.next t} : Finset T), g*(L.K z.1 u:ℝ))=
        g*(L.K z.1 t:ℝ)+g*(L.K z.1 (G.next t):ℝ) := by simp [hn.symm]
    rw [he] at hb
    exact (by linarith only [hh] : (1:ℝ) ≤ _).trans hb

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

 theorem old_feasible {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hg : 0 ≤ g) (F : Finset I) (z : L.Ω × (T → Finset I))
    (hz : 0 < (L.ν.joint L.κ).weight z) :
    ∀ a, 0 ≤ oldAssignment L F z a ∧ oldAssignment L F z a ≤ physicalOpen L z a := by
  have hω := (L.ν.support_joint L.κ z hz).1
  rintro (i | ti)
  · dsimp only [oldAssignment,physicalOpen,physicalCount,Sum.elim_inl]
    split_ifs
    · exact ⟨L.nominal_nonneg z.1 hω _,L.nominal_cap z.1 hω _⟩
    · exact ⟨le_rfl,mul_nonneg hg (Nat.cast_nonneg _)⟩
  · dsimp only [oldAssignment,physicalOpen,physicalCount,Sum.elim_inr]
    split_ifs
    · exact ⟨mul_nonneg hg (Nat.cast_nonneg _),le_rfl⟩
    · exact ⟨le_rfl,mul_nonneg hg (Nat.cast_nonneg _)⟩

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_NearbyAssignments
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

theorem nearby_assignments_s35_oai (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ g γ B T₁ v p₀ : ℝ} {Δ : ℕ}
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c g γ B Δ)
    (hy : ∀ a, 0 ≤ y a) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hT₁ : 0 ≤ T₁)
    (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hp : ∀ t, p₀ ≤ G.p t)
    (j : X) (t : T) (Fj : Finset I) (hmj : ∑ a ∈ Fj, y a=1)
    (hvj : ∑ a ∈ Fj, y a*dist j (i a)=v)
    (hD : dist j (s t) ≤ M*v) (hL : 0 < G.c t → G.L t ≤ T₁*v)
    (hR : G.c t=0 → ∀ a ∈ F t, dist (s t) (i a) ≤ T₁*v) :
    ∃ r : (L.Ω × (T → Finset I)) → Physical I T → ℝ,
      (∀ z, 0 < (L.ν.joint L.κ).weight z →
        (∀ a, 0 ≤ r z a ∧ r z a ≤ physicalOpen L z a) ∧ (∑ a, r z a)=1) ∧
      (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*
        (Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2)) a)) ≤
        nearFactor p₀ (M+(1+δ)*T₁) γ g*v := by
  classical
  have hv : 0 ≤ v := (sum_nonneg (fun a _ => mul_nonneg (hy a) dist_nonneg)).trans_eq hvj
  have hc1 : ∀ t, G.c t ≤ 1 := by
    intro t
    have hu := G.unit t
    have hpp := hp t
    linarith only [hu,hpp,hp₀]
  obtain ⟨hshort,hcost⟩ := physical_old_estimates_s35 hg hγ hunit L hy hp₀ hp₀1 hp
    G.nonneg hc1 G.disjoint Fj hmj (fun a => dist j (i a)) (fun _ => dist_nonneg)
  rw [hvj] at hcost
  let d : Physical I T → ℝ := Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2))
  let ball := univ.filter (fun a => d a ≤ (M+(1+δ)*T₁)*v)
  have hrad : 0 ≤ (M+(1+δ)*T₁)*v := by positivity
  obtain ⟨r,hr,hc⟩ := support_repaired_cost_s35 (L.ν.joint L.κ) ball
    (physicalOpen L) (oldAssignment L Fj) d hrad
    (fun z hz a => (old_feasible L hg Fj z hz a).1)
    (fun z hz a => (old_feasible L hg Fj z hz a).2)
    (fun a => by cases a <;> exact dist_nonneg)
    (fun a ha => (mem_filter.mp ha).2)
    (nearby_ball F y s i V G L hδ hT₁ hv hg j t hD hL hR)
    hcost hshort
  refine ⟨r,hr,hc.trans_eq ?_⟩
  dsimp only [nearFactor,shortfallFactor]
  ring

end MetricKMedian.Preparation
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.nearby_assignments_s35_oai := @OAI.MetricKMedian.Preparation.nearby_assignments_s35_oai
