-- Prove2me | solution 1 for GlobalTheory.PosOne.covers_opE_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:05:10.122685+00:00
-- url     : https://prove2.me/submissions/40b5e6d7-38aa-40ed-9164-ec3722ebc68d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LocalZetaIntegralOpenSubgroup
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
import Theorems.Thm_GlobalTheory_RootEx_exists_isOpen_addSubgroup_add_eq
import Theorems.Thm_GlobalTheory_RootEx_opE_support_compact_mod_R
import Theorems.Thm_GlobalTheory_StepData_IntM_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open GlobalTheory GlobalTheory.PosOne
namespace GlobalTheory.PosOne
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (J : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (J : Set (GL (n ⊕ Fin c) k))) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), ∃ T, Covers p J T fun h => opE ψ ν p (om μ 1 h Φ.1) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψc hψ ν _ μ _ J hJ Φ
  classical
  obtain ⟨Λ, hΛ, hper⟩ := exists_isOpen_addSubgroup_add_eq Φ.2.1 Φ.2.2
  obtain ⟨Ω, hΩ, hcov⟩ := opE_support_compact_mod_R k n n' c p hp1 hpc ψ hψc hψ ν (tsupport Φ.1) Φ.2.2 Λ hΛ
  obtain ⟨F, hF⟩ := hΩ.elim_finite_subcover (fun w : GL (n ⊕ Fin c) k => (fun g => w⁻¹ * g) ⁻¹' (J : Set _))
    (fun w => hJ.preimage (continuous_const.mul continuous_id))
    (fun w _ => Set.mem_iUnion.2 ⟨w, by simp [J.one_mem]⟩)
  let rep : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k := fun w => Quotient.out (DoubleCoset.mk (R k n c p) J w)
  have hrep : ∀ w, DoubleCoset.mk (R k n c p) J (rep w) = DoubleCoset.mk (R k n c p) J w :=
    fun w => DoubleCoset.out_eq' _ _ _
  refine ⟨F.image rep, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_image, Set.mem_image] at ha hb
    obtain ⟨w₁, -, rfl⟩ := ha
    obtain ⟨w₂, -, rfl⟩ := hb
    rw [hrep, hrep] at hab
    simp only [rep, hab]
  · intro h hh
    obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hh
    obtain ⟨r, hr, w, hw, rfl⟩ := hcov μ Φ.1 (subset_tsupport _) (fun x y hy => hper x y hy) (fun _ => 1)
      (IsLocallyConstant.const 1) h x₀ (by simpa using hx₀)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hF hw)
    obtain ⟨hiF, hiw⟩ := Set.mem_iUnion.1 hi
    refine ⟨rep i, Finset.mem_image_of_mem _ hiF, ?_⟩
    rw [hrep, eq_comm, DoubleCoset.eq]
    exact ⟨r, hr, i⁻¹ * w, hiw, by group⟩
end GlobalTheory.PosOne
