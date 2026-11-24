-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.exists_famF_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:40:26.988619+00:00
-- url     : https://prove2.me/submissions/028f2083-3c7f-4c7f-bda9-307c4503a2cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulReStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwist
import Theorems.Thm_GlobalTheory_GodementJacquet_famF_apply
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_eventually_det_trivial
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one
import Theorems.Thm_GlobalTheory_T_exists_schwartz_bump_near_identity


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published ValuativeRel GlobalTheory.RootEx
open scoped TensorProduct Topology
open GlobalTheory GlobalTheory.GodementJacquet
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
local notation "e₀" => stdSum (rfl : _ + _ = _ + _)
variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
  [m.IsMulLeftInvariant] [m.IsOpenPosMeasure] (hσ : IsSmooth σ)
  (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
  (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
  (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
    Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
    Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)
namespace GlobalTheory.GodementJacquet
theorem _root_.solution (hμ : IsSmoothChar μ) {v : V} (hv : v ≠ 0) :
    ∃ Φ : SB (Matrix (Fin (r + t)) (Fin r) k), famF hσ hs hp hu hI hμ Φ v ≠ 0 := by
  set S : Set (GL (Fin r) k) := {g | σ g v = v ∧ μ (Matrix.GeneralLinearGroup.det g) = 1 ∧
    nabs k (Matrix.GeneralLinearGroup.det g) = 1} with hSdef
  have hS1 : S ∈ 𝓝 (1 : GL (Fin r) k) := by
    filter_upwards [(hσ v).mem_nhds (by simp), eventually_det_trivial (Fin r) hμ] with g h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨Φ, hΦ, hΦ1, h01, hΦS⟩ := GlobalTheory.T.exists_schwartz_bump_near_identity k r t (interior S) isOpen_interior
    (mem_interior_iff_mem_nhds.2 hS1)
  refine ⟨⟨Φ, hΦ⟩, fun h0 => ?_⟩
  have hcont : Continuous fun g : GL (Fin r) k => Φ (eMat k r t * g.val) :=
    (hΦ.1.comp_continuous (continuous_const.matrix_mul Units.continuous_val)).continuous
  set φ : GL (Fin r) k → ℝ := fun g => (Φ (eMat k r t * g.val)).re with hφ
  have hom : ∀ g : GL (Fin r) k, om μ g 1 Φ (eMat k r t) = (φ g : ℂ) := by
    intro g
    have hm : ((1 : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * g.val = eMat k r t * g.val := by
      simp
    simp only [om, hm]
    by_cases hg : Φ (eMat k r t * g.val) = 0
    · simp [hφ, hg]
    · obtain ⟨-, h2, h3⟩ := interior_subset (hΦS g hg)
      have h4 : Φ (eMat k r t * g.val) = 1 := (h01 _).resolve_left hg
      simp [hφ, h2, h3, h4, nabs_one]
  have hint : Integrable φ m := by
    have := (hI 1 Φ hΦ).re
    refine this.congr (ae_of_all _ fun g => ?_)
    simp [hom g]
  have hnn : 0 ≤ φ := fun g => by
    rcases h01 (eMat k r t * g.val) with h | h <;> simp [hφ, h]
  have hpos : 0 < ∫ g, φ g ∂m := by
    refine (integral_pos_iff_support_of_nonneg hnn hint).2 ?_
    have hc : Continuous φ := Complex.continuous_re.comp hcont
    refine hc.isOpen_support.measure_pos m ⟨1, ?_⟩
    have : eMat k r t * (1 : GL (Fin r) k).val = eMat k r t := by simp
    simp [hφ, this, hΦ1]
  have hval : gjInt m μ σ Bf Φ 1 v v = ((∫ g, φ g ∂m : ℝ) : ℂ) * Bf v v := by
    rw [← integral_complex_ofReal, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    show om μ g 1 Φ (eMat k r t) * coef σ Bf v v g = (φ g : ℂ) * Bf v v
    rw [hom g]
    by_cases hg : Φ (eMat k r t * g.val) = 0
    · simp [hφ, hg]
    · obtain ⟨h1, -, -⟩ := interior_subset (hΦS g hg)
      simp only [coef]
      rw [fix_inv h1]
  have hz : gjInt m μ σ Bf Φ 1 v v = 0 := by
    have h1 := famF_apply hσ hs hp hu hI hμ ⟨Φ, hΦ⟩ v 1 (v ⊗ₜ (1 : ℂ))
    rw [h0] at h1
    simpa using h1.symm
  rw [hval] at hz
  rcases mul_eq_zero.1 hz with h | h
  · exact hpos.ne' (by exact_mod_cast h)
  · have := hp v hv
    simp [h] at this
end GlobalTheory.GodementJacquet
