-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.IdxFour.indexFour
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:36:17.307156+00:00
-- url     : https://prove2.me/submissions/1c777ee3-4f28-4869-be18-30f93b1ca611

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2RootIndexOfCardSq
import Theorems.Thm_GlobalTheory_SatakeWeyl_IdxFour_exists_hom
import Theorems.Thm_GlobalTheory_SatakeWeyl_IdxFour_mat_of_mem
import Theorems.Thm_GlobalTheory_SatakeWeyl_IdxFour_mem_root
import Theorems.Thm_GlobalTheory_SatakeWeyl_IdxFour_mem_K_iff
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_injective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.IdxFour
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl.IdxFour
theorem _root_.solution (hI : IntIndex) : IndexFour := by
  intro L _ _ ϖ σ q hU s₀ hs
  obtain ⟨φ, hφ⟩ := exists_hom hU.1
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    have := hU.2.2.2.1
    simp at this
  have hinj : Function.Injective φ := fun a b h => by
    have := congrFun (congrFun ((hφ a).symm.trans ((congrArg mat h).trans (hφ b))) 0) 1
    simpa [rootMat] using this
  have hK : KU σ 4 ⊓ rootU σ ![0, 0, 1, 1] = (AddSubgroup.toSubgroup (intL L).toAddSubgroup).map φ := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      have e := mat_of_mem hU.1 h2
      exact ⟨Multiplicative.ofAdd (mat g 0 1), (mem_K_iff hU.2.1 e).1 h1, mat_injective ((hφ _).trans e.symm)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(mem_K_iff hU.2.1 (hφ x)).2 hx, mem_root (hφ x)⟩
  have hc : ∀ x : L, s₀ * φ (Multiplicative.ofAdd x) * s₀⁻¹ = φ (Multiplicative.ofAdd (ϖ * x)) := by
    intro x
    rw [mul_inv_eq_iff_eq_mul]
    apply mat_injective
    rw [mat_mul, mat_mul, hφ, hφ, hs]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [rootMat, hU.2.2.1]
    field_simp
  have hK' : ((AddSubgroup.toSubgroup (intL L).toAddSubgroup).map φ).map (MulAut.conj s₀).toMonoidHom =
      (AddSubgroup.toSubgroup ((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ))).map φ := by
    ext g
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨Multiplicative.ofAdd (ϖ * x.toAdd), ⟨x.toAdd, hx, rfl⟩, (hc x.toAdd).symm⟩
    · rintro ⟨y, ⟨x, hx, e⟩, rfl⟩
      refine ⟨φ (Multiplicative.ofAdd x), ⟨_, hx, rfl⟩, (hc x).trans (congrArg φ ?_)⟩
      exact congrArg Multiplicative.ofAdd e
  rw [hK, hK', Subgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_toSubgroup]
  exact hI L ϖ σ q hU
end GlobalTheory.SatakeWeyl.IdxFour
