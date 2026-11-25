-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuExpMem.expMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:11:51.584155+00:00
-- url     : https://prove2.me/submissions/524121ba-da91-4b46-a0b2-30a20fd4b6be

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExponentialMembership
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuExpMem_ex_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuExpMem_ex_entry
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
namespace GlobalTheory.CompanionTheory.BmuExpMem
private theorem exp_mul_eq_mul_exp_of_semiconj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (B C H : 𝔸) (h : B * H = H * C) : NormedSpace.exp B * H = H * NormedSpace.exp C := by
  have hp : ∀ m : ℕ, B ^ m * H = H * C ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have e1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B).mul_right H
  have e2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) C).mul_left H
  have hf : (fun m : ℕ => ((m.factorial : ℂ)⁻¹ • B ^ m) * H) =
      fun m => H * (((m.factorial : ℂ)⁻¹) • C ^ m) := by
    funext m
    rw [smul_mul_assoc, hp m, mul_smul_comm]
  rw [hf] at e1
  exact e1.unique e2
end GlobalTheory.CompanionTheory.BmuExpMem
end
end

set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuExpMem
namespace GlobalTheory.CompanionTheory.BmuExpMem
theorem _root_.solution : ExpMem := by
  intro k r z X t
  have hint : ∀ B C H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, B * H = H * C →
      NormedSpace.exp B * H = H * NormedSpace.exp C := by
    intro B C H h
    letI : NormedRing (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
      Matrix.linftyOpNormedAlgebra
    exact exp_mul_eq_mul_exp_of_semiconj B C H h
  have hU : Lie (Formalism.QuantumDeterminants.Hpk k r) X → ex X t ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    intro hX
    have hX' : Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -(Formalism.QuantumDeterminants.Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
    have hAH : ((t : ℂ) • X)ᴴ * Formalism.QuantumDeterminants.Hpk k r = Formalism.QuantumDeterminants.Hpk k r * (-((t : ℂ) • X)) := by
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, hX', Matrix.mul_neg, Matrix.mul_smul, smul_neg]
      simp [Complex.star_def, Complex.conj_ofReal]
    show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp ((t : ℂ) • X) =
      Formalism.QuantumDeterminants.Hpk k r
    rw [← Matrix.exp_conjTranspose, hint _ _ _ hAH, mul_assoc,
      ← Matrix.exp_add_of_commute (-((t : ℂ) • X)) ((t : ℂ) • X) (Commute.neg_left (Commute.refl _)),
      neg_add_cancel, NormedSpace.exp_zero, mul_one]
  refine ⟨fun h => ⟨hU h.1, fun a => ⟨ex_mulVec X t _ (h.2.1 a).1, ex_mulVec X t _ (h.2.1 a).2⟩,
    ex_mulVec X t z h.2.2⟩, fun h => ⟨hU h.1, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩⟩
  · refine ex_entry X t (a : ℕ) (Formalism.QuantumDeterminants.eI k r a) (fun i' l hi' hl => ?_) (fun i' hi' => h.2.1 a i' hi') i hi
    have hlr : l.val < r := lt_trans hl a.isLt
    have := h.2.1 ⟨l.val, hlr⟩ i' (le_of_lt (lt_of_lt_of_le hl hi'))
    simpa [Formalism.QuantumDeterminants.eI] using this
  · refine ex_entry X t r j (fun i' l hi' hl => ?_) (fun i' hi' => h.2.2 i' j hj1 hj2 hi') i hi
    have := h.2.1 ⟨l.val, hl⟩ i' (le_of_lt (lt_of_lt_of_le hl hi'))
    simpa [Formalism.QuantumDeterminants.eI] using this
end GlobalTheory.CompanionTheory.BmuExpMem
