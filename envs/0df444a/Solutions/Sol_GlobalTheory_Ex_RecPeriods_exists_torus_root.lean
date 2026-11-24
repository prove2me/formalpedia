-- Prove2me | solution 1 for GlobalTheory.Ex.RecPeriods.exists_torus_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:44:33.969735+00:00
-- url     : https://prove2.me/submissions/02fd4ef3-c4cb-4787-b2bb-a6c0c2f67ac6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG

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
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.RecPeriods
namespace GlobalTheory.Ex.RecPeriods
theorem _root_.solution {C : Type} [Field C] [IsAlgClosed C] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    (k : ℕ) (hk : k ≠ 0) (t : Multiplicative X →* Cˣ) : ∃ t' : Multiplicative X →* Cˣ, t' ^ k = t := by
  have hs : Function.Surjective ((k : ℤ) • (LinearMap.id : Additive Cˣ →ₗ[ℤ] Additive Cˣ)) := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul u : Cˣ) : C) (Nat.pos_of_ne_zero hk)
    have z0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hk] at hz
      exact (Additive.toMul u).ne_zero hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z z0), ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    simpa using hz
  obtain ⟨f, hf⟩ := Module.projective_lifting_property _ (MonoidHom.toAdditiveRight t).toIntLinearMap hs
  refine ⟨AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  have := congrArg Additive.toMul (LinearMap.congr_fun hf x.toAdd)
  simpa using this
end GlobalTheory.Ex.RecPeriods
