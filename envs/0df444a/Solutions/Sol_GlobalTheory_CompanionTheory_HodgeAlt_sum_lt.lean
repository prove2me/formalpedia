-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:28:14.489742+00:00
-- url     : https://prove2.me/submissions/f45027cc-1ebb-467e-b35e-512ef514dce6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R V V' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [Module R V] [Module R V']
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution {M : Type} [AddCommGroup M] [Module R M] {n : ℕ} (u v : Fin n → R)
    (c : Fin n → Fin n → M) (hd : ∀ i, c i i = 0) (ha : ∀ i j, c j i = -c i j) :
    ∑ i, ∑ j, (u i * v j) • c i j =
      ∑ i, ∑ j, if i < j then (u i * v j - u j * v i) • c i j else 0 := by
  have e1 : ∀ i j, (u i * v j) • c i j = (if i < j then (u i * v j) • c i j else 0) +
      (if j < i then (u i * v j) • c i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.not_gt]
    · subst h; simp [hd]
    · simp [h, h.not_gt]
  have e2 : ∀ i j, (if i < j then (u i * v j - u j * v i) • c i j else 0) =
      (if i < j then (u i * v j) • c i j else 0) + (if i < j then (u j * v i) • c j i else 0) := by
    intro i j
    split_ifs
    · rw [ha i j, sub_smul, smul_neg, sub_eq_add_neg]
    · simp
  calc ∑ i, ∑ j, (u i * v j) • c i j
      = ∑ i, ∑ j, ((if i < j then (u i * v j) • c i j else 0) +
          (if j < i then (u i * v j) • c i j else 0)) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ e1 i j
    _ = ∑ i, ∑ j, (if i < j then (u i * v j) • c i j else 0) +
          ∑ i, ∑ j, (if j < i then (u i * v j) • c i j else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, (if i < j then (u i * v j) • c i j else 0) +
          ∑ i, ∑ j, (if i < j then (u j * v i) • c j i else 0) :=
        congrArg (_ + ·) Finset.sum_comm
    _ = _ := by simp only [e2, Finset.sum_add_distrib]
end GlobalTheory.CompanionTheory.HodgeAlt
