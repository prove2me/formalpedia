-- Prove2me | solution 1 for GlobalTheory.Cyc.FrameTorsion.modify
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:30.27958+00:00
-- url     : https://prove2.me/submissions/5fe8d163-08bb-4f86-8469-ae8de4eef690

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTateMaximalIdealKillsFirstCohomologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGeneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGeneratorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleTwistCoboundaryOnBall
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_tw_sub
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_tw_pow
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_ball_sub
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_ball_pow
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_tw_ball
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_tw_mul
import Theorems.Thm_GlobalTheory_Cyc_FrameTorsion_tw_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FrameTorsion
variable {l : ℕ} [Fact l.Prime] {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
  {χ : GQ l →* ℚ_[l]ˣ} {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {i : ℤ}
variable {K : FinExt l} {m : ℕ} {g : GQ l}
namespace GlobalTheory.Cyc.FrameTorsion
theorem _root_.solution (ha : IsActC act) (hχ : IsCyc χ) (hU : Frame χ K m U g) (n : ℕ)
    {c : GQ l → Fin r → PadicComplex l} (hc : CocOn (Gj K m) (twAct act χ i U) (ball l r) c)
    {x : Fin r → PadicComplex l} (hx : x ∈ ball l r) :
    CocOn (Gj K m) (twAct act χ i U) (ball l r)
      (fun σ => (l : PadicComplex l) ^ n • c σ - (twAct act χ i U σ x - x)) := by
  obtain ⟨hcont, hmem, hcoc⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContinuousOn (fun σ => ((l : PadicComplex l) ^ n) • c σ) (Gj K m) :=
      (continuousOn_const (c := (l : PadicComplex l) ^ n)).smul hcont
    exact h1.sub ((tw_cont ha hχ hU x).sub continuousOn_const)
  · intro σ hσ
    exact ball_sub (ball_pow n (hmem σ hσ)) (ball_sub (tw_ball ha hχ hU hσ hx) hx)
  · intro σ hσ τ hτ
    simp only
    rw [hcoc σ hσ τ hτ, tw_mul ha hU hσ hτ, tw_sub, tw_sub, tw_pow, smul_add]
    abel
end GlobalTheory.Cyc.FrameTorsion
