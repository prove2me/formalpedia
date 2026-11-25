-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.thetaPair_prod_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:20.957688+00:00
-- url     : https://prove2.me/submissions/06ace57c-9a15-448d-ac43-abc264f93e6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulReStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwist
import Theorems.Thm_GlobalTheory_GodementJacquet_abstract_equiv
import Theorems.Thm_GlobalTheory_GodementJacquet_exists_pairing
import Theorems.Thm_GlobalTheory_GodementJacquet_exists_famF_ne_zero
import Theorems.Thm_GlobalTheory_SmGL_InductionContragredient_nonempty_equiv
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_comp
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_extTensor
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_ofChar_iff
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_SplitWeil_volGL_haar
import Theorems.Thm_GlobalTheory_T_theta_integral_integrable


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
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published
namespace GlobalTheory.GodementJacquet
theorem _root_.solution : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V), r < t → IsSmoothChar μ → IsUnitaryChar μ → IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → ThetaPair μ σ (prod₂ σ (detRep (Fin t) μ)) := by
  intro hBZ k _ _ _ _ r t μ V _ _ σ hrt hμ hμu hσ hirr huni
  obtain ⟨hadmAll, -, -, hIC⟩ := hBZ k
  have hadm := hadmAll (Fin r) V σ hσ hirr
  obtain ⟨Bf, hs, hp, hu⟩ := huni
  have hV : ∃ v : V, v ≠ 0 := by
    by_contra hc
    push_neg at hc
    haveI : IsSimpleOrder (Subrepresentation σ) := hirr
    refine bot_ne_top (α := Subrepresentation σ) (Subrepresentation.toSubmodule_injective ?_)
    ext x
    rw [hc x]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  obtain ⟨v, hv⟩ := hV
  borelize k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨i1, i2, i3, -, -, -, i7, i8⟩ := volGL_haar k (Fin r) (MeasureTheory.Measure.addHaar : MeasureTheory.Measure k)
  have hI := fun h Φ hΦ => GlobalTheory.T.theta_integral_integrable k (MeasureTheory.Measure.addHaar : MeasureTheory.Measure k) r t μ hrt.le hμ hμu h Φ hΦ
  have hρ : IsSmooth (GlobalTheory.GodementJacquet.leviRep t μ σ) :=
    isSmooth_comp (isSmooth_extTensor hσ ((isSmooth_ofChar_iff _).2 hμ.detChar)) _
      ((continuous_apply false).prodMk (continuous_apply true))
  obtain ⟨Ψ⟩ := hIC.nonempty_equiv (GlobalTheory.SmGL.two (stdSum (rfl : r + t = r + t))) hρ
  obtain ⟨P, hP, hQ⟩ := GlobalTheory.GodementJacquet.abstract_equiv _ _ Ψ
  obtain ⟨Φ₀, hne⟩ := GlobalTheory.GodementJacquet.exists_famF_ne_zero hσ hs hp hu hI hμ hv
  exact GlobalTheory.GodementJacquet.exists_pairing hσ hs hp hu hI hμ hadm P hP hQ Φ₀ v hne
end GlobalTheory.GodementJacquet
