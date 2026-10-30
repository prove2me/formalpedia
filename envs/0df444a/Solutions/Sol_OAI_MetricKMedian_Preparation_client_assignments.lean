-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.client_assignments
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:41:55.202019+00:00
-- url     : https://prove2.me/submissions/366dacaf-d148-4ce2-be8d-0a579c897530

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K036
import Theorems.Thm_OAI_MetricKMedian_Preparation_distant_assignments
import Theorems.Thm_OAI_MetricKMedian_Preparation_nearby_assignments

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_NearestAssignmentGeometry
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
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationClientAssignments
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

theorem client_assignments_oai (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
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
    obtain ⟨r,hr,hc⟩ := nearby_assignments F y s i V G L hy hM.le hδ.le hT.le hg.le hγ hunit
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
    obtain ⟨r,hr,hc⟩ := distant_assignments F y s i V G L hy hδ hb0 hsep hg hγ hunit
      hp₀ G.large (by positivity) (by linarith only [hα]) j t Fj hmj hms hvj hV R hscale.1 hmax hmin hscale.2
    exact ⟨r,hr,hc.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)⟩

end MetricKMedian.Preparation
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.client_assignments_oai := @OAI.MetricKMedian.Preparation.client_assignments_oai
