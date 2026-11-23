-- Prove2me | solution 1 for GlobalTheory.JHMult.occurs_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:04.501036+00:00
-- url     : https://prove2.me/submissions/35afb829-b8fb-4377-adf8-747d3d019607

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
import Theorems.Thm_GlobalTheory_JHMult_subMap_mono
import Theorems.Thm_GlobalTheory_JHMult_subComap_mono
import Theorems.Thm_GlobalTheory_JHMult_step_iff
import Theorems.Thm_GlobalTheory_JHMult_step_map
import Theorems.Thm_GlobalTheory_JHMult_step_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.JHMult
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
variable {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
  {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
namespace GlobalTheory.JHMult
theorem _root_.solution (hι : Function.Injective ι) (hp : Function.Surjective p)
    (h0 : ∀ u, p (ι u) = 0) {a b : ℕ} (ha : OccursTimes σ ρ₁ a) (hb : OccursTimes σ ρ₂ b) :
    OccursTimes σ ρ (a + b) := by
  obtain ⟨S, T, h1, h2, h3⟩ := ha
  obtain ⟨S', T', h1', h2', h3'⟩ := hb
  refine ⟨Fin.append (fun i => subMap ι (S i)) (fun i => subComap p (S' i)),
    Fin.append (fun i => subMap ι (T i)) (fun i => subComap p (T' i)), fun i => ?_,
    fun i j => ?_, fun i => step_iff.2 ?_⟩
  · induction i using Fin.addCases with
    | left i => simpa using subMap_mono ι (h1 i)
    | right i => simpa using subComap_mono p (h1' i)
  · induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        intro h
        simpa using subMap_mono ι (h2 i j h)
      | right j =>
        intro _
        simp only [Fin.append_left, Fin.append_right]
        rintro _ ⟨u, _, rfl⟩
        show p (ι u) ∈ (T' j).toSubmodule
        rw [h0]
        exact zero_mem _
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        intro h
        have := j.2
        simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at h
        omega
      | right j =>
        intro h
        have h' : i < j := by
          simp only [Fin.lt_def, Fin.val_natAdd] at h ⊢
          omega
        simpa using subComap_mono p (h2' i j h')
  · induction i using Fin.addCases with
    | left i => simpa using step_map ι hι (step_iff.1 (h3 i))
    | right i => simpa using step_comap p hp (step_iff.1 (h3' i))
end GlobalTheory.JHMult
