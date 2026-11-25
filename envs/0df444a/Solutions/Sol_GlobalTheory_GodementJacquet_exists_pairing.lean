-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.exists_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:33.700588+00:00
-- url     : https://prove2.me/submissions/97885cff-0ab8-4010-8bc7-5b3bdbe4c31f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulReStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwist
import Theorems.Thm_GlobalTheory_GodementJacquet_famF_add_fun
import Theorems.Thm_GlobalTheory_GodementJacquet_famF_smul_fun
import Theorems.Thm_GlobalTheory_GodementJacquet_famF_add_right
import Theorems.Thm_GlobalTheory_GodementJacquet_famF_smul_right
import Theorems.Thm_GlobalTheory_GodementJacquet_famF_translate
import Theorems.Thm_GlobalTheory_GodementJacquet_famF_shift
import Theorems.Thm_GlobalTheory_GodementJacquet_form_injective
import Theorems.Thm_GlobalTheory_GodementJacquet_abstract_pairing
import Theorems.Thm_GlobalTheory_GodementJacquet_exists_stab
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_om_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul
import Theorems.Thm_GlobalTheory_T_unitary_admissible_matrix_coefficient


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
  [m.IsMulLeftInvariant] [m.IsMulRightInvariant] (hσ : IsSmooth σ)
  (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
  (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
  (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
    Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
    Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)
namespace GlobalTheory.GodementJacquet
theorem _root_.solution (hμ : IsSmoothChar μ) (hadm : IsAdmissible σ)
    (P : IndSp (two (stdSum (rfl : r + t = r + t))) (contra (leviRep t μ σ)) →ₗ[ℂ]
      IndSp (two (stdSum (rfl : r + t = r + t))) (leviRep t μ σ) →ₗ[ℂ] ℂ)
    (hP : ∀ (h : GL (Fin (r + t)) k) a f,
      P (parInd (two (stdSum (rfl : r + t = r + t))) (contra (leviRep t μ σ)) h a)
        (parInd (two (stdSum (rfl : r + t = r + t))) (leviRep t μ σ) h f) = P a f)
    (hQ : ∀ a, (∀ f, P a f = 0) → a = 0)
    (Φ₀ : SB (Matrix (Fin (r + t)) (Fin r) k)) (w₀ : V)
    (hne : famF hσ hs hp hu hI hμ Φ₀ w₀ ≠ 0) :
    ThetaPair μ σ (prod₂ σ (detRep (Fin t) μ)) := by
  obtain ⟨B, hB⟩ := abstract_pairing hp P (famF hσ hs hp hu hI hμ)
    (famF_add_fun hσ hs hp hu hI hμ) (fun c Φ w => famF_smul_fun hσ hs hp hu hI hμ c Φ w)
    (famF_add_right hσ hs hp hu hI hμ) (fun c Φ w => famF_smul_right hσ hs hp hu hI hμ c Φ w)
    (fun Φ f L hL => by
      obtain ⟨S, hSo, hS⟩ := exists_stab (t := t) hμ Φ
      refine GlobalTheory.T.unitary_admissible_matrix_coefficient k r V σ Bf hadm hs hp hu L S hSo fun s hsS w => ?_
      have := famF_shift hσ hs hp hu hI hμ Φ Φ s⁻¹ (hS _ (inv_mem hsS)).symm w
      rw [inv_inv] at this
      rw [hL, hL, ← this])
  refine ⟨B, fun h0 => hne (hQ _ fun f => ?_), fun g h Φ Φ' hΦ' f => form_injective hp _ _ fun w => ?_⟩
  · rw [← hB, h0]
    simp
  · have hw : Bf (σ g (B Φ f)) w = Bf (B Φ f) (σ g⁻¹ w) := by
      rw [← hu g (B Φ f) (σ g⁻¹ w), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    let Φ₁ : SB (Matrix (Fin (r + t)) (Fin r) k) := ⟨om μ g 1 Φ.1, om_mem_SB μ g 1 Φ.2⟩
    have h1 : Φ'.1 = om μ 1 h Φ₁.1 := by
      have := om_mul μ 1 g h 1 Φ.1
      rw [one_mul, mul_one] at this
      exact hΦ'.trans this
    have e1 : Bf (B Φ' (parInd (two (stdSum (rfl : r + t = r + t))) (leviRep t μ σ) h f)) w =
        P (famF hσ hs hp hu hI hμ Φ' w) (parInd (two (stdSum (rfl : r + t = r + t))) (leviRep t μ σ) h f) :=
      hB Φ' _ w
    have e2 : Bf (B Φ f) (σ g⁻¹ w) = P (famF hσ hs hp hu hI hμ Φ (σ g⁻¹ w)) f := hB Φ f _
    have e3 := famF_shift hσ hs hp hu hI hμ Φ Φ₁ g rfl w
    have e4 := famF_translate hσ hs hp hu hI hμ Φ₁ Φ' h h1 w
    refine e1.trans (Eq.trans ?_ (hw.trans e2).symm)
    exact (congrArg (fun a => P a (parInd (two (stdSum (rfl : r + t = r + t))) (leviRep t μ σ) h f)) e4).symm.trans
      ((hP h _ f).trans (congrArg (fun a => P a f) e3))
end GlobalTheory.GodementJacquet
