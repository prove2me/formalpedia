-- Prove2me | solution 1 for GlobalTheory.SmGL.not_isCuspidal_detRep_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:16.162795+00:00
-- url     : https://prove2.me/submissions/2147c1e3-8d59-4388-91b3-4a9e9c15ad25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_twKer_detRep
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL
theorem _root_.solution (χ : kˣ →* ℂˣ) : ¬ IsCuspidal (detRep (Fin 2) χ) := by
  intro h
  let e : (Σ _ : Fin 2, Fin 1) ≃ Fin 2 := Equiv.sigmaUnique _ _
  let u : GL (Fin 2) k := GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp)
  have hu : u ∈ unipRad k e := by
    refine mem_unipRad.2 ⟨mem_parab_iff.2 fun a b i j hab => ?_, fun a i j => ?_⟩
    · show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) k) a b = 0
      fin_cases a <;> fin_cases b <;> simp at hab ⊢
    · show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) k) a a = _
      rw [Subsingleton.elim i j]
      fin_cases a <;> simp
  have hne : unipRad k e ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.mem_bot] at hu
    have : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) k) 0 1 = (1 : Matrix (Fin 2) (Fin 2) k) 0 1 :=
      congrArg (fun g : GL (Fin 2) k => (g : Matrix (Fin 2) (Fin 2) k) 0 1) hu
    simp at this
  have := Submodule.Quotient.subsingleton_iff.1 (h.2 2 (fun _ => 1) e hne)
  rw [twKer_detRep] at this
  exact bot_ne_top this
end GlobalTheory.SmGL
