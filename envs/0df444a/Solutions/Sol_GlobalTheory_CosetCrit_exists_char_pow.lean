-- Prove2me | solution 1 for GlobalTheory.CosetCrit.exists_char_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:37.445093+00:00
-- url     : https://prove2.me/submissions/7c560355-7895-46bb-b0a3-959a986c7eac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorsionTwistTsumNormGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.CosetCrit
namespace GlobalTheory.CosetCrit
theorem _root_.solution {C X : Type} [Field C] [IsAlgClosed C] [AddCommGroup X] [Module.Free ℤ X]
    (t : Multiplicative X →* Cˣ) {k : ℕ} (hk : 0 < k) : ∃ t' : Multiplicative X →* Cˣ, t' ^ k = t := by
  have hroot : ∀ u : Cˣ, ∃ v : Cˣ, v ^ k = u := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : C) hk
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hk.ne'] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose r hr using hroot
  let e := Module.Free.chooseBasis ℤ X
  let f : X →ₗ[ℤ] Additive Cˣ :=
    e.constr ℤ fun i => Additive.ofMul (r (t (Multiplicative.ofAdd (e i))))
  have hf : k • f = (MonoidHom.toAdditiveRight t).toIntLinearMap := e.ext fun i => by
    simp only [f, LinearMap.smul_apply, Module.Basis.constr_basis, ← ofMul_pow, hr]
    rfl
  refine ⟨AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun hf x.toAdd)
end GlobalTheory.CosetCrit
