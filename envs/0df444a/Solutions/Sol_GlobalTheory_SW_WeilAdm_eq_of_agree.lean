-- Prove2me | solution 1 for GlobalTheory.SW.WeilAdm.eq_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:29:44.650575+00:00
-- url     : https://prove2.me/submissions/c74b5de1-e32a-42f8-b59e-f1a35c83153a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction
import Theorems.Thm_GlobalTheory_SW_WeilLevel_colsIn_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilAdm
open WeilLevel Base
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ Λ' : Lt E n}
omit [IsCMField E]
namespace GlobalTheory.SW.WeilAdm
theorem _root_.solution {s L : ℕ} (hs : s.Coprime L) (h2 : ∀ v ∈ Λ', (s : E) • v ∈ Λ)
    {φ ψ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : LevelL Λ' L φ) (hψ : LevelL Λ' L ψ)
    (h : ∀ x, ColsIn Λ ((L : E) • x) → ColsIn Λ' ((L : E) • x) → φ x = ψ x) : φ = ψ := by
  funext x
  by_cases hx : ColsIn Λ' ((L : E) • x)
  · obtain ⟨a, b, hab⟩ : IsCoprime (s : ℤ) ((L * L : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.mul_right hs hs)
    have hab' : (a : E) * s + b * (L * L) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → E) hab
    have z : ∀ (Γ : Lt E n) (k : ℤ) (y : Matrix (Fin n) (Fin N) E), ColsIn Γ y →
        ColsIn Γ ((k : E) • y) := fun Γ k y hy i => by
      have := Γ.toAddSubgroup.zsmul_mem (hy i) k
      rwa [← Int.cast_smul_eq_zsmul E] at this
    have hy := z Λ' (-b) _ hx
    have e : (L : E) • (x + (L : E) • ((-b : ℤ) : E) • (L : E) • x) =
        (a : E) • (s : E) • (L : E) • x := by
      ext k i
      simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      push_cast
      linear_combination (-(L : E) * x k i) * hab'
    rw [← hφ.2 x _ hy, ← hψ.2 x _ hy]
    refine h _ ?_ ?_ <;> rw [e]
    · exact z _ _ _ fun i => h2 _ (hx i)
    · exact z _ _ _ (colsIn_smul _ hx)
  · rw [not_not.1 fun h => hx (hφ.1 x h), not_not.1 fun h => hx (hψ.1 x h)]
end GlobalTheory.SW.WeilAdm
