-- Prove2me | solution 1 for GlobalTheory.Ex.QStr.split_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:44:47.071454+00:00
-- url     : https://prove2.me/submissions/15e86ba8-5c41-474a-b601-c6a1a5a5299b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed

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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
namespace GlobalTheory.Ex.QStr
theorem _root_.solution {M : Type} [CommGroup M] (k a d : ℕ) [NeZero k] (hM : ∀ x : M, x ^ k = 1)
    (i : Multiplicative (Fin d → ZMod k) →* M) (π : M →* Multiplicative (Fin a → ZMod k))
    (hi : Function.Injective i) (hπ : Function.Surjective π) (hex : ∀ x, π x = 1 ↔ ∃ y, i y = x) :
    Nonempty (M ≃* Multiplicative (Fin (a + d) → ZMod k)) := by
  letI : Module (ZMod k) (Additive M) := AddCommGroup.zmodModule (n := k) (G := Additive M) fun x => hM x.toMul
  let i' : (Fin d → ZMod k) →ₗ[ZMod k] Additive M := (MonoidHom.toAdditiveRight i).toZModLinearMap k
  let π' : Additive M →ₗ[ZMod k] (Fin a → ZMod k) := (MonoidHom.toAdditiveLeft π).toZModLinearMap k
  obtain ⟨s, hs⟩ := π'.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hπ)
  have hE : Function.Exact i' π' := fun x => hex x.toMul
  let e := (hE.splitSurjectiveEquiv hi ⟨s, hs⟩).1
  let e' : Additive M ≃ₗ[ZMod k] (Fin (a + d) → ZMod k) :=
    e.trans ((LinearEquiv.prodComm _ _ _).trans ((LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm.trans
      (LinearEquiv.funCongrLeft _ _ finSumFinEquiv.symm)))
  exact ⟨AddEquiv.toMultiplicativeRight e'.toAddEquiv⟩
end GlobalTheory.Ex.QStr
