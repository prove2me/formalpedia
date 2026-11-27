-- Prove2me | solution 1 for GlobalTheory.AdjRead.span_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:41:35.633864+00:00
-- url     : https://prove2.me/submissions/86dcb5f8-76ca-430d-bb83-fd9bdf50e2e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGenRosati
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigidStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsAdjReadingOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AdjRead
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
variable {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.AdjRead
theorem _root_.solution {N : ℕ} (C : (Fin N → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) × (Fin g → ℂ)) (lat : AddSubgroup (Fin g → ℂ))
    (h : Submodule.span ℝ (lat : Set (Fin g → ℂ)) = ⊤) :
    Submodule.span ℝ (((lat.prod lat).comap C.toAddEquiv.toAddMonoidHom : AddSubgroup (Fin N → ℂ)) :
      Set (Fin N → ℂ)) = ⊤ := by
  set s : Set ((Fin g → ℂ) × (Fin g → ℂ)) := ((lat.prod lat : AddSubgroup ((Fin g → ℂ) × (Fin g → ℂ))) :
    Set ((Fin g → ℂ) × (Fin g → ℂ))) with hs
  have key : Submodule.span ℝ s = ⊤ := by
    have h1 : ∀ x ∈ Submodule.span ℝ (lat : Set (Fin g → ℂ)),
        ((x, 0) : (Fin g → ℂ) × (Fin g → ℂ)) ∈ Submodule.span ℝ s := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (AddSubgroup.mem_prod.mpr ⟨hy, zero_mem lat⟩)
      | zero => rw [Prod.mk_zero_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz =>
        have := Submodule.add_mem _ hy hz
        rwa [Prod.mk_add_mk, add_zero] at this
      | smul r y _ hy =>
        have := Submodule.smul_mem _ r hy
        rwa [Prod.smul_mk, smul_zero] at this
    have h2 : ∀ x ∈ Submodule.span ℝ (lat : Set (Fin g → ℂ)),
        ((0, x) : (Fin g → ℂ) × (Fin g → ℂ)) ∈ Submodule.span ℝ s := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (AddSubgroup.mem_prod.mpr ⟨zero_mem lat, hy⟩)
      | zero => rw [Prod.mk_zero_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz =>
        have := Submodule.add_mem _ hy hz
        rwa [Prod.mk_add_mk, add_zero] at this
      | smul r y _ hy =>
        have := Submodule.smul_mem _ r hy
        rwa [Prod.smul_mk, smul_zero] at this
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have ha : a ∈ Submodule.span ℝ (lat : Set (Fin g → ℂ)) := h ▸ Submodule.mem_top
    have hb : b ∈ Submodule.span ℝ (lat : Set (Fin g → ℂ)) := h ▸ Submodule.mem_top
    have := Submodule.add_mem _ (h1 a ha) (h2 b hb)
    rwa [Prod.mk_add_mk, add_zero, zero_add] at this
  set Cr : (Fin N → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) × (Fin g → ℂ) := C.restrictScalars ℝ
  rw [eq_top_iff]
  intro v _
  have hv : Cr v ∈ Submodule.span ℝ s := key ▸ Submodule.mem_top
  have hm : v ∈ (Submodule.span ℝ s).map
      (Cr.symm : ((Fin g → ℂ) × (Fin g → ℂ)) →ₗ[ℝ] (Fin N → ℂ)) := ⟨Cr v, hv, by simp⟩
  rw [← Submodule.span_image] at hm
  simp only [LinearEquiv.coe_coe] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨w, hw, rfl⟩
  show C (Cr.symm w) ∈ lat.prod lat
  simpa [Cr, hs] using hw
end GlobalTheory.AdjRead
