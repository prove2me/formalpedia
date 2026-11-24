-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.pointed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:44.562269+00:00
-- url     : https://prove2.me/submissions/f92ef48e-c0d8-4dab-9cb2-e5c50c3ca58d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_altSum
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_dn_E
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_dn_const
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc
variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
variable (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (a₀ : P)
  (hb : ∀ T : Pᵒᵖ, Function.Bijective (mp F ((th a₀).app T)))
include hb
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution (hH : HtpySt) (n : ℕ) (z : Cn F (n + 1)) (hz : dn F (n + 1) z = 0) :
    ∃ y, dn F n y = z := by
  obtain ⟨-, h1⟩ := hH R Pᵒᵖ F Pᵒᵖ F (CoefMap.id F) (m1 F a₀ hb) (th a₀)
    (fun T b ↦ (io F a₀ hb T).symm_apply_apply b)
  obtain ⟨-, h2⟩ := hH R Pᵒᵖ F Pᵒᵖ F (m2 F a₀ hb) (m1 F a₀ hb) (th' a₀) (fun T b ↦ rfl)
  obtain ⟨y₁, e₁⟩ := h1 n z hz
  obtain ⟨y₂, e₂⟩ := h2 n z hz
  set t : F.obj (op a₀) := z ((Functor.const (Fin (n + 2))).obj (op a₀)) with ht
  have k := dn_const F a₀ (n + 1) z
  rw [hz] at k
  have k' : (∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ)) • t = 0 := k.symm
  have e0 : pulln (CoefMap.id F) (n + 1) z = z := rfl
  have e2 : pulln (m2 F a₀ hb) (n + 1) z = E F a₀ hb (n + 1) t := rfl
  have s : (∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ)) + ∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ) = 1 := by
    have := altSum (R := R) (n + 2)
    rw [Fin.sum_univ_castSucc (n := n + 2)]
    simp only [Fin.val_castSucc, Fin.val_last]
    linear_combination this
  have e3 : E F a₀ hb (n + 1) t = dn F n (E F a₀ hb n t) := by
    funext c
    rw [dn_E]
    have : (∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ)) • E F a₀ hb (n + 1) t c = 0 := by
      have h0 := (m2 F a₀ hb).smul (c.obj (Fin.last (n + 1))) (∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ)) t
      exact h0.symm.trans ((congrArg ((m2 F a₀ hb).α (c.obj (Fin.last (n + 1)))) k').trans (map_zero _))
    calc E F a₀ hb (n + 1) t c = (1 : R) • E F a₀ hb (n + 1) t c := (one_smul _ _).symm
      _ = ((∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ)) + ∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ)) •
          E F a₀ hb (n + 1) t c := by rw [s]
      _ = _ := by rw [add_smul, this, add_zero]
  refine ⟨y₁ - y₂ + E F a₀ hb n t, ?_⟩
  rw [map_add, map_sub, ← e₁, ← e₂, ← e3, e0, e2]
  abel
end GlobalTheory.CompanionTheory.AffAcyc
