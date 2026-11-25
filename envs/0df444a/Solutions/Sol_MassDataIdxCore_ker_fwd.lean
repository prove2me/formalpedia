-- Prove2me | solution 1 for MassDataIdxCore.ker_fwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:27.594808+00:00
-- url     : https://prove2.me/submissions/936e85af-13cb-4aa8-a25d-3c72055f9818

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PsiKerIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitSmul
import Theorems.Thm_MassDataIdxCore_firstSplit_smul
import Theorems.Thm_MassDataIdxCore_map_sub_one

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
  [DecidableEq n] (θ : T ≃ₐ[K] K × K) (s : T →+* T) (J : Matrix n n T) (P : GL n K)
namespace MassDataIdxCore
theorem _root_.solution (c : K) (g : GL n T)
    (hg : ∀ y ∈ Lat O θ J P, ∃ z ∈ Lat O θ J P, ((g : Matrix n n T) - 1) *ᵥ y = c • z) :
    ∀ i j, ∃ w ∈ O, (conjPrime₂ θ P g - 1) i j = c * w := by
  intro i j

  let y : n → T := fun k => θ.symm ((P : Matrix n n K) k j, 0)
  have ht1 : (fun k => t1 θ (y k)) = fun k => (P : Matrix n n K) k j := by
    funext k
    simp [y, t1]
  have ht2 : (fun k => t2 θ (y k)) = 0 := by
    funext k
    simp [y, t2]
  have hcol : (fun k => (P : Matrix n n K) k j) = (P : Matrix n n K) *ᵥ Pi.single j 1 := by
    funext k
    simp [Matrix.mulVec_single_one]
  have hPinv : ((P⁻¹ : GL n K) : Matrix n n K) * (P : Matrix n n K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hyL : y ∈ Lat O θ J P := by
    unfold Lat
    simp only [Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rw [ht1, hcol, Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec]
      unfold IntV
      intro k
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    · rw [ht2, Matrix.mulVec_zero]
      unfold IntV
      intro k
      simp
  obtain ⟨z, hz, e⟩ := hg y hyL
  unfold Lat at hz
  simp only [Set.mem_setOf_eq] at hz
  have e1 : ((g : Matrix n n T).map (t1 θ) - 1) *ᵥ (fun k => (P : Matrix n n K) k j) =
      c • (fun k => t1 θ (z k)) := by
    funext k
    have h1 : t1 θ ((((g : Matrix n n T) - 1) *ᵥ y) k) = t1 θ ((c • z) k) := by rw [e]
    rw [RingHom.map_mulVec, map_sub_one, Pi.smul_apply, firstSplit_smul] at h1
    rw [Pi.smul_apply, smul_eq_mul, ← h1, ← ht1]
    rfl
  refine ⟨(((P⁻¹ : GL n K) : Matrix n n K) *ᵥ fun k => t1 θ (z k)) i, hz.1 i, ?_⟩
  have key : (conjPrime₂ θ P g - 1) *ᵥ Pi.single j 1 =
      c • (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ fun k => t1 θ (z k)) := by
    have hc : (conjPrime₂ θ P g - 1 : Matrix n n K) =
        ((P⁻¹ : GL n K) : Matrix n n K) * ((g : Matrix n n T).map (t1 θ) - 1) * (P : Matrix n n K) := by
      unfold conjPrime₂
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPinv]
    rw [hc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hcol, e1, Matrix.mulVec_smul]
  have h2 := congrFun key i
  rw [Matrix.mulVec_single_one] at h2
  simpa using h2
end MassDataIdxCore
