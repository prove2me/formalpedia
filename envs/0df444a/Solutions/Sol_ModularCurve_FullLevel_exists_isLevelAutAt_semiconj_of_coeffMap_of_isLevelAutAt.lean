-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/d5f73415-eeb4-5813-ba9d-852591988699

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

namespace SemiconjKit

variable {L : Type} [Field L] {K : IntermediateField L (LaurentSeries L)}

theorem apply_eq_self_of_coeffEmb [CharZero L] (σ : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.toRingHom ((x : ↥K) : LaurentSeries L))
    (x : ↥K) (r : LaurentSeries ℚ) (hx : ((x : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L r) :
    τ x = x := by
  apply Subtype.ext
  rw [hτ, hx, ModularCurve.coeffEmb, ModularCurve.coeffMap_coeffMap,
    ModularCurve.coeffMap_congr (RingHom.ext_rat (σ.toRingHom.comp (algebraMap ℚ L)) (algebraMap ℚ L))]

theorem coe_symm_apply (σ : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.toRingHom ((x : ↥K) : LaurentSeries L))
    (y : ↥K) :
    ((τ.symm y : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.symm.toRingHom ((y : ↥K) : LaurentSeries L) := by
  have h1 := hτ (τ.symm y)
  rw [RingEquiv.apply_symm_apply] at h1
  conv_rhs => rw [h1]
  rw [ModularCurve.coeffMap_coeffMap]
  have hcomp : σ.symm.toRingHom.comp σ.toRingHom = RingHom.id L := by
    ext c; simp
  rw [ModularCurve.coeffMap_congr hcomp, ModularCurve.coeffMap_id]

theorem apply_algebraMap (σ : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.toRingHom ((x : ↥K) : LaurentSeries L))
    (c : L) : τ (algebraMap L ↥K c) = algebraMap L ↥K (σ c) := by
  apply Subtype.ext
  rw [hτ]
  show ModularCurve.coeffMap σ.toRingHom (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries L) (σ c)
  rw [ModularCurve.coeffMap_algebraMap]
  rfl

theorem symm_apply_algebraMap (σ : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.toRingHom ((x : ↥K) : LaurentSeries L))
    (c : L) : τ.symm (algebraMap L ↥K c) = algebraMap L ↥K (σ.symm c) := by
  apply τ.injective
  rw [RingEquiv.apply_symm_apply, apply_algebraMap σ τ hτ, RingEquiv.apply_symm_apply]

noncomputable def conj (σ : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.toRingHom ((x : ↥K) : LaurentSeries L))
    (g : ↥K ≃ₐ[L] ↥K) : ↥K ≃ₐ[L] ↥K :=
  { (τ.trans g.toRingEquiv).trans τ.symm with
    commutes' := by
      intro c
      show τ.symm (g (τ (algebraMap L ↥K c))) = algebraMap L ↥K c
      rw [apply_algebraMap σ τ hτ, AlgEquiv.commutes, symm_apply_algebraMap σ τ hτ, RingEquiv.symm_apply_apply] }

theorem conj_apply (σ : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.toRingHom ((x : ↥K) : LaurentSeries L))
    (g : ↥K ≃ₐ[L] ↥K) (x : ↥K) : conj σ τ hτ g x = τ.symm (g (τ x)) := rfl

theorem apply_conj (σ : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.toRingHom ((x : ↥K) : LaurentSeries L))
    (g : ↥K ≃ₐ[L] ↥K) (x : ↥K) : τ (conj σ τ hτ g x) = g (τ x) := by
  rw [conj_apply, RingEquiv.apply_symm_apply]

theorem isLevelAutAt_conj [CharZero L] (σ : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.toRingHom ((x : ↥K) : LaurentSeries L))
    (n : ℕ) (ξ : L) (m : ℕ) [NeZero m] (N₀ : ℕ) (H : Subgroup (ZMod N₀)ˣ) (γ : SL(2, ℤ))
    (g : ↥K ≃ₐ[L] ↥K) (hg : ModularCurve.FullLevel.IsLevelAutAt L n ξ m N₀ H γ K g) :
    ModularCurve.FullLevel.IsLevelAutAt L n (σ.symm ξ) m N₀ H γ K (conj σ τ hτ g) := by
  intro k f₁ f₂ pf pg hf₁ hf₂ hg0 x hx ι hι
  have hτx : τ x = x := apply_eq_self_of_coeffEmb σ τ hτ x _ hx
  have h1 : ((conj σ τ hτ g x : ↥K) : LaurentSeries L) =
      ModularCurve.coeffMap σ.symm.toRingHom ((g x : ↥K) : LaurentSeries L) := by
    rw [conj_apply, hτx, coe_symm_apply σ τ hτ]
  rw [h1, ModularCurve.coeffMap_coeffMap]
  exact hg k f₁ f₂ pf pg hf₁ hf₂ hg0 x hx (ι.comp σ.symm.toRingHom) (by simpa using hι)

end SemiconjKit

theorem solution
    (L : Type) [Field L] [CharZero L]
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (m : ℕ) [NeZero m] (hqm : q ∣ m) (hmM : Nat.Coprime m M')
    (ξ : L) (hξ : IsPrimitiveRoot ξ m)
    (K : IntermediateField L (LaurentSeries L))
    (σ : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σ.toRingHom ((x : ↥K) : LaurentSeries L)) :
    ∃ d : (ZMod q)ˣ,
      ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ (g : ↥K ≃ₐ[L] ↥K),
        ModularCurve.FullLevel.IsLevelAutAt L m ξ m (m ^ 2 * M') (ModularCurve.FullLevel.levelH m M') γ K g →
        ∃ (γ' : SL(2, ℤ)) (g' : ↥K ≃ₐ[L] ↥K),
          γ' ∈ CongruenceSubgroup.Gamma0 M' ∧
          (γ ∈ CongruenceSubgroup.Gamma q → γ' ∈ CongruenceSubgroup.Gamma q) ∧
          redQ q γ' = diagOneElem q d * redQ q γ * (diagOneElem q d)⁻¹ ∧
          (∀ x : ↥K, τ (g' x) = g (τ x)) ∧
          ModularCurve.FullLevel.IsLevelAutAt L m ξ m (m ^ 2 * M') (ModularCurve.FullLevel.levelH m M') γ' K g' := by
  have hξ' : IsPrimitiveRoot (σ.symm ξ) m := hξ.map_of_injective σ.symm.injective
  obtain ⟨d, hd⟩ := ModularCurve.FullLevel.exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot
    L q M' m hqm hmM ξ (σ.symm ξ) hξ hξ' K
  refine ⟨d, fun γ hγ g hg => ?_⟩
  obtain ⟨γ', h0, hq', hred, hatt⟩ := hd γ hγ (SemiconjKit.conj σ τ hτ g)
    (SemiconjKit.isLevelAutAt_conj σ τ hτ m ξ m (m ^ 2 * M') (ModularCurve.FullLevel.levelH m M') γ g hg)
  exact ⟨γ', SemiconjKit.conj σ τ hτ g, h0, hq', hred, fun x => SemiconjKit.apply_conj σ τ hτ g x, hatt⟩

end S_ModularCurve_FullLevel_exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_semiconj_of_coeffMap_of_isLevelAutAt (solution)
