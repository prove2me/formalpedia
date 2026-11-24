-- Prove2me | solution 1 for GlobalTheory.CharIndep.exists_smoothOp_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:33.616382+00:00
-- url     : https://prove2.me/submissions/dbf44529-9826-4a99-8f32-cc8b3a7151ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonemptyEquivOfSmoothTraceEqAdmissible
import Theorems.Thm_GlobalTheory_OpTrace_IsHilbertSchmidt_smul
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_add
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_comp_left
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_smul
import Theorems.Thm_GlobalTheory_OpTrace_eq_of_forall_dual
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_map_smoothOp
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_add
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_smul
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
open GlobalTheory GlobalTheory.CharIndep
namespace GlobalTheory.CharIndep
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] {f₀ : G → ℂ} (hf : IsLocallyConstant f₀) (hc : HasCompactSupport f₀)
    (a : MonoidAlgebra ℂ G) :
    ∃ f : G → ℂ, IsLocallyConstant f ∧ HasCompactSupport f ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ →
        smoothOp ρ μ f = ρ.asAlgebraHom a ∘ₗ smoothOp ρ μ f₀ := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    have h1 : IsLocallyConstant fun x => f₀ (g⁻¹ * x) :=
      hf.comp_continuous (continuous_const.mul continuous_id)
    have h2 : HasCompactSupport fun x => f₀ (g⁻¹ * x) :=
      hc.comp_homeomorph (Homeomorph.mulLeft g⁻¹)
    refine ⟨_, h1, h2, fun V _ _ ρ hρ => ?_⟩
    ext v
    refine eq_of_forall_dual fun l => ?_
    rw [hρ.map_smoothOp h1 h2 l, ← integral_mul_left_eq_self _ g]
    simpa using (hρ.map_smoothOp (μ := μ) hf hc (l ∘ₗ ρ g) v).symm
  | add a b ha hb =>
    obtain ⟨f, f1, f2, f3⟩ := ha
    obtain ⟨f', f1', f2', f3'⟩ := hb
    refine ⟨f + f', f1.add f1', f2.add f2', fun V _ _ ρ hρ => ?_⟩
    rw [hρ.smoothOp_add f1 f2 f1' f2', f3 V ρ hρ, f3' V ρ hρ, map_add, LinearMap.add_comp]
  | smul c a ha =>
    obtain ⟨f, f1, f2, f3⟩ := ha
    refine ⟨c • f, f1.comp (c • ·), f2.comp_left (g := (c • ·)) (smul_zero c),
      fun V _ _ ρ hρ => ?_⟩
    rw [hρ.smoothOp_smul f1 f2, f3 V ρ hρ, map_smul, LinearMap.smul_comp]
end GlobalTheory.CharIndep
