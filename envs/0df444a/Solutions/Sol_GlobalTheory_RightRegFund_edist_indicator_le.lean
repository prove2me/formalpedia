-- Prove2me | solution 1 for GlobalTheory.RightRegFund.edist_indicator_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:56:32.351864+00:00
-- url     : https://prove2.me/submissions/db554dfd-12c6-41b6-b976-137b0e973294

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep
import Theorems.Thm_GlobalTheory_RightRegFund_rep_eq
import Theorems.Thm_GlobalTheory_RightRegFund_ae_rep
import Theorems.Thm_GlobalTheory_RightRegFund_ae_good_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise
open GlobalTheory GlobalTheory.RightRegFund
variable {G : Type} [Group G]
variable {Γ : Subgroup G} {D : Set G} {r : G → G}
variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ]
variable [μ.IsMulRightInvariant]
variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}
namespace GlobalTheory.RightRegFund
theorem _root_.solution (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g)))
    (c : ℂ) {s : Set G} (hs : MeasurableSet s) (hμs : μ.restrict D s ≠ ∞) (g g₀ : G) :
    edist (R g (indicatorConstLp 2 hs hμs c)) (R g₀ (indicatorConstLp 2 hs hμs c)) ≤
      ‖c‖ₑ * μ (((fun x => x * g) ⁻¹' (s ∩ D)) ∆ ((fun x => x * g₀) ⁻¹' (s ∩ D))) ^
        (1 / (2 : ℝ≥0∞).toReal) := by
  set F := indicatorConstLp 2 hs hμs c with hF
  set S := ((fun x => x * g) ⁻¹' (s ∩ D)) ∆ ((fun x => x * g₀) ⁻¹' (s ∩ D)) with hS
  have h1 : ∀ᵐ y ∂μ, (F : G → ℂ) (r y) = s.indicator (fun _ => c) (r y) :=
    ae_rep hDm hr (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c))
  have key : ∀ a b x : G, Good Γ D (x * b) → r (x * a) ∈ s → r (x * b) ∉ s →
      ∃ γ : Γ, (γ : G) * x * a ∈ s ∩ D ∧ (γ : G) * x * b ∉ s ∩ D := by
    intro a b x hb h2 h3
    obtain ⟨γ, e1, e2⟩ := hr (x * a)
    refine ⟨γ, by rw [mul_assoc, ← e1]; exact ⟨h2, e2⟩, fun h => h3 ?_⟩
    rw [mul_assoc] at h
    rw [rep_eq hr hb h.2]; exact h.1
  have hU : μ.restrict D (⋃ γ : Γ, γ • S) ≤ μ S := by
    rw [hD.measure_eq_tsum S]
    refine (measure_iUnion_le _).trans (le_of_eq (tsum_congr fun γ => ?_))
    rw [Measure.restrict_apply' hDm]
  rw [Lp.edist_def]
  calc eLpNorm (⇑(R g F) - ⇑(R g₀ F)) 2 (μ.restrict D)
      ≤ eLpNorm ((⋃ γ : Γ, γ • S).indicator fun _ => c) 2 (μ.restrict D) := by
        refine eLpNorm_mono_enorm_ae ?_
        filter_upwards [hR g F, hR g₀ F,
          ae_restrict_of_ae ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h1),
          ae_restrict_of_ae ((measurePreserving_mul_right μ g₀).quasiMeasurePreserving.ae h1),
          ae_restrict_of_ae (ae_good_mul hD g), ae_restrict_of_ae (ae_good_mul hD g₀)]
          with x e1 e2 e3 e4 e5 e6
        rw [Pi.sub_apply, e1, e2, e3, e4]
        by_cases a : r (x * g) ∈ s <;> by_cases b : r (x * g₀) ∈ s
        · simp [a, b]
        · obtain ⟨γ, k1, k2⟩ := key g g₀ x e6 a b
          have : x ∈ ⋃ γ : Γ, γ • S :=
            mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inl ⟨k1, k2⟩)⟩
          rw [indicator_of_mem this]; simp [a, b]
        · obtain ⟨γ, k1, k2⟩ := key g₀ g x e5 b a
          have : x ∈ ⋃ γ : Γ, γ • S :=
            mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inr ⟨k1, k2⟩)⟩
          rw [indicator_of_mem this]; simp [a, b]
        · simp [a, b]
    _ ≤ _ := eLpNorm_indicator_const_le c 2
    _ ≤ _ := by gcongr
end GlobalTheory.RightRegFund
