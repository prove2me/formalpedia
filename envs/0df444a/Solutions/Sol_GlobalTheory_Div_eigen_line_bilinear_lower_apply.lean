-- Prove2me | solution 1 for GlobalTheory.Div.eigen_line_bilinear.lower_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:53:46.136384+00:00
-- url     : https://prove2.me/submissions/3380aa47-5595-4c2a-b0d2-e54cb84e079d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodProductIntegral
import Theorems.Thm_GlobalTheory_Div_eigen_line_bilinear_eq_smul_of_line
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.eigen_line_bilinear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
namespace GlobalTheory.Div.eigen_line_bilinear
theorem _root_.solution {ρ : orderC c →+* Module.End O H} {τ : E →+* K} {e f : H} {N : Module.End K (K ⊗[O] H)}
    (hdir : DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ)) (hline : Module.finrank K (eigK ρ τ) = 1)
    (he : inK (O := O) K H e ∈ eigK ρ τ) (he0 : inK (O := O) K H e ≠ 0) (hN : IsLower ρ τ e f N) (x : K ⊗[O] H) :
    ∃ a : K, N x = a • inK (O := O) K H f := by
  have hx : x ∈ ⨆ σ : E →+* K, eigK ρ σ := by
    rw [hdir.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction (fun σ : E →+* K => eigK ρ σ) (motive := fun x => ∃ a : K, N x = a • inK (O := O) K H f) hx
    ?_ ⟨0, by simp⟩ ?_
  · intro σ y hy
    by_cases hσ : σ = τ
    · subst hσ
      obtain ⟨a, rfl⟩ := eq_smul_of_line hline he he0 hy
      exact ⟨a, by rw [map_smul, hN.1]⟩
    · exact ⟨0, by rw [hN.2 σ hσ y hy, zero_smul]⟩
  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [map_add, ha, hb, add_smul]⟩
end GlobalTheory.Div.eigen_line_bilinear
