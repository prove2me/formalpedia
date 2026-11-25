-- Prove2me | solution 1 for MassDataIdxCore.key_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:19.474699+00:00
-- url     : https://prove2.me/submissions/62bd3dac-27ba-41ee-afd0-c72653e64c74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitSmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_KerBack
import Theorems.Thm_MassDataIdxCore_p_pinv
import Theorems.Thm_MassDataIdxCore_map_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n] {θ : T ≃ₐ[K] K × K} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap) (J : Matrix n n T)
  (P : GL n K)
include hs
namespace MassDataIdxCore
theorem _root_.solution (g : GL n T) (hg : g ∈ Formalism.UG.UJ s J) :
    ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) * (g : Matrix n n T).map (t2 θ) =
      (conjPrime₂ θ P g⁻¹)ᵀ * ((P : Matrix n n K)ᵀ * (J.map (t1 θ))ᵀ) := by
  have ht : ∀ x, t1 θ (s x) = t2 θ x := fun x => by simp [t1, t2, hs]
  have hg' : Formalism.UG.cT s (g : Matrix n n T) * J * (g : Matrix n n T) = J := hg
  have h1 := congrArg (fun M : Matrix n n T => M.map (t1 θ)) hg'
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h1
  have hcomp : (⇑(t1 θ) ∘ ⇑s) = ⇑(t2 θ) := funext ht
  rw [hcomp] at h1
  have h2 := congrArg Matrix.transpose h1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at h2
  have hinv : (((g⁻¹ : GL n T) : Matrix n n T).map (t1 θ))ᵀ * ((g : Matrix n n T).map (t1 θ))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, MassDataIdxCore.map_mul_inv, Matrix.transpose_one]
  have key : (J.map (t1 θ))ᵀ * (g : Matrix n n T).map (t2 θ) =
      (((g⁻¹ : GL n T) : Matrix n n T).map (t1 θ))ᵀ * (J.map (t1 θ))ᵀ := by
    calc (J.map (t1 θ))ᵀ * (g : Matrix n n T).map (t2 θ)
        = ((((g⁻¹ : GL n T) : Matrix n n T).map (t1 θ))ᵀ * ((g : Matrix n n T).map (t1 θ))ᵀ) *
          ((J.map (t1 θ))ᵀ * (g : Matrix n n T).map (t2 θ)) := by rw [hinv, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, h2]
  have hPP : ((P⁻¹ : GL n K) : Matrix n n K)ᵀ * (P : Matrix n n K)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, p_pinv P, Matrix.transpose_one]
  unfold conjPrime₂
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (((P⁻¹ : GL n K) : Matrix n n K)ᵀ), hPP, Matrix.one_mul, key]
end MassDataIdxCore
