-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_isLevelAutAt_apply_conj_of_coeffMap_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a34e597c-89d2-5c7a-b709-d41ba9372c23

import Mathlib
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_apply_conj_of_coeffMap_ringEquiv

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 0

open scoped MatrixGroups

theorem solution
    (L : Type) [Field L] [CharZero L] (n : ℕ) (ζ : L) (m : ℕ) [NeZero m]
    (N₀ : ℕ) (H : Subgroup (ZMod N₀)ˣ) (γ : SL(2, ℤ))
    (K : IntermediateField L (LaurentSeries L))
    (σL : L ≃+* L) (τc : ↥K ≃+* ↥K)
    (hτc : ∀ x : ↥K, ((τc x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L))
    (σ : ↥K ≃ₐ[L] ↥K) (hσ : ModularCurve.FullLevel.IsLevelAutAt L n ζ m N₀ H γ K σ) :
    ∃ σ' : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L n (σL ζ) m N₀ H γ K σ' ∧
      ∀ x : ↥K, σ' x = τc (σ (τc.symm x)) := by
  classical

  have hτc' : ∀ y : ↥K, ((τc.symm y : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.symm.toRingHom ((y : ↥K) : LaurentSeries L) := by
    intro y
    have h := hτc (τc.symm y)
    rw [RingEquiv.apply_symm_apply] at h
    rw [h, ModularCurve.coeffMap_coeffMap]
    have : σL.symm.toRingHom.comp σL.toRingHom = RingHom.id L := RingHom.ext fun a => σL.symm_apply_apply a
    rw [this, ModularCurve.coeffMap_id]

  have hconst : ∀ c : L, ((algebraMap L ↥K c : ↥K) : LaurentSeries L) = algebraMap L (LaurentSeries L) c := fun c => rfl
  have hτc_alg : ∀ c : L, τc (algebraMap L ↥K c) = algebraMap L ↥K (σL c) := by
    intro c; apply Subtype.ext
    rw [hτc, hconst, hconst, ModularCurve.coeffMap_algebraMap]; rfl
  have hτc'_alg : ∀ c : L, τc.symm (algebraMap L ↥K c) = algebraMap L ↥K (σL.symm c) := by
    intro c; apply Subtype.ext
    rw [hτc', hconst, hconst, ModularCurve.coeffMap_algebraMap]; rfl

  let e : ↥K ≃+* ↥K := (τc.symm.trans σ.toRingEquiv).trans τc
  have he : ∀ x : ↥K, e x = τc (σ (τc.symm x)) := fun x => rfl
  have hcomm : ∀ c : L, e (algebraMap L ↥K c) = algebraMap L ↥K c := by
    intro c
    rw [he, hτc'_alg, AlgEquiv.commutes, hτc_alg, RingEquiv.apply_symm_apply]
  let σ' : ↥K ≃ₐ[L] ↥K := AlgEquiv.ofRingEquiv (f := e) hcomm
  have hσ' : ∀ x : ↥K, σ' x = τc (σ (τc.symm x)) := fun x => rfl
  refine ⟨σ', ?_, hσ'⟩

  intro k f g pf pg hf hg hg0 x hx ι' hι'

  have hfix : τc.symm x = x := by
    apply Subtype.ext
    rw [hτc', hx, ModularCurve.coeffEmb, ModularCurve.coeffMap_coeffMap]
    exact ModularCurve.coeffMap_congr (RingHom.ext_rat _ _) _
  have h1 : ((σ' x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((σ x : ↥K) : LaurentSeries L) := by
    rw [hσ', hfix, hτc]
  rw [h1, ModularCurve.coeffMap_coeffMap]
  exact hσ k f g pf pg hf hg hg0 x hx (ι'.comp σL.toRingHom) (by simpa using hι')

end S_ModularCurve_FullLevel_exists_isLevelAutAt_apply_conj_of_coeffMap_ringEquiv
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_apply_conj_of_coeffMap_ringEquiv (solution)
