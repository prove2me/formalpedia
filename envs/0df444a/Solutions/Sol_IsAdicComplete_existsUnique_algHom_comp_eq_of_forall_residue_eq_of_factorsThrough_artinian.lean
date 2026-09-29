-- Prove2me | solution 1 for IsAdicComplete.existsUnique_algHom_comp_eq_of_forall_residue_eq_of_factorsThrough_artinian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b9a83a34-8b90-592e-85d8-6f0c30ac57cb

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsAdicComplete_existsUnique_algHom_comp_eq_of_forall_residue_eq_of_factorsThrough_artinian

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (A₀ : Type) [CommRing A₀]
    (B : Type) [CommRing B] [Algebra A₀ B]
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra A₀ R] (ι : B →ₐ[A₀] R)
    (k : Type) [Field k]
    (resR : R →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R)
    (W₀ : Type) [CommRing W₀]
    (res₀ : W₀ →+* k)
    [Algebra W₀ R] [Algebra A₀ W₀] [IsScalarTower A₀ W₀ R]
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R w) = res₀ w)
    (hfac : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : B →ₐ[A₀] T, (∀ b : B, resT (φ b) = resR (ι b)) →
          ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ ∀ b : B, Φ (ι b) = φ b)
    (φ : B →ₐ[A₀] R) (hφ : ∀ b : B, resR (φ b) = resR (ι b)) :
    ∃! Φ : R →ₐ[W₀] R, (∀ r : R, resR (Φ r) = resR r) ∧ ∀ b : B, Φ (ι b) = φ b := by
  classical

  have hpowker : ∀ (n : ℕ) (a : R), a ∈ maximalIdeal R ^ (n + 1) → resR a = 0 := by
    intro n a ha
    have : a ∈ RingHom.ker resR := hkerR.symm ▸ (Ideal.pow_le_self (Nat.succ_ne_zero n) ha)
    exact (RingHom.mem_ker).mp this
  let resT : (n : ℕ) → (R ⧸ maximalIdeal R ^ (n + 1)) →+* k := fun n =>
    Ideal.Quotient.lift (maximalIdeal R ^ (n + 1)) resR (hpowker n)
  have hresT_mk : ∀ (n : ℕ) (a : R), resT n (Ideal.Quotient.mk _ a) = resR a := fun n a => Ideal.Quotient.lift_mk _ _ _
  have hsurjT : ∀ n : ℕ, Function.Surjective (resT n) := by
    intro n y
    obtain ⟨a, rfl⟩ := hresR y
    exact ⟨Ideal.Quotient.mk _ a, hresT_mk n a⟩
  have hne : ∀ n : ℕ, maximalIdeal R ^ (n + 1) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero n))
  have key : ∀ n : ℕ, ∃! Φ : R →ₐ[W₀] R ⧸ maximalIdeal R ^ (n + 1),
      (∀ r : R, resT n (Φ r) = resR r) ∧ ∀ b : B, Φ (ι b) = Ideal.Quotient.mk _ (φ b) := by
    intro n
    haveI hnt : Nontrivial (R ⧸ maximalIdeal R ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr (hne n)
    haveI hloc : IsLocalRing (R ⧸ maximalIdeal R ^ (n + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) Ideal.Quotient.mk_surjective
    have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) =
        maximalIdeal (R ⧸ maximalIdeal R ^ (n + 1)) := by
      ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp [sup_eq_left.mpr (le_maximalIdeal (hne n))]
    haveI hart : IsArtinianRing (R ⧸ maximalIdeal R ^ (n + 1)) := by
      rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
      refine ⟨n + 1, ?_⟩
      rw [← hmap, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    have hkerT : RingHom.ker (resT n) = maximalIdeal (R ⧸ maximalIdeal R ^ (n + 1)) :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (resT n) (hsurjT n))
    have hresT₀ : ∀ w : W₀, resT n (algebraMap W₀ (R ⧸ maximalIdeal R ^ (n + 1)) w) = res₀ w := by
      intro w
      rw [← Ideal.Quotient.mk_algebraMap, hresT_mk, hresR₀]
    have hφn : ∀ b : B, resT n (((Ideal.Quotient.mkₐ A₀ (maximalIdeal R ^ (n + 1))).comp φ) b) = resR (ι b) := by
      intro b
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hresT_mk, hφ]
    exact hfac (R ⧸ maximalIdeal R ^ (n + 1)) (resT n) (hsurjT n) hkerT hresT₀
      ((Ideal.Quotient.mkₐ A₀ (maximalIdeal R ^ (n + 1))).comp φ) hφn

  let Φ' : (n : ℕ) → (R →ₐ[W₀] R ⧸ maximalIdeal R ^ (n + 1)) := fun n => (key n).exists.choose
  have hΦ'res : ∀ (n : ℕ) (r : R), resT n (Φ' n r) = resR r := fun n => (key n).exists.choose_spec.1
  have hΦ'ι : ∀ (n : ℕ) (b : B), Φ' n (ι b) = Ideal.Quotient.mk _ (φ b) := fun n => (key n).exists.choose_spec.2
  have hcompat : ∀ (m n : ℕ) (h : m ≤ n),
      (Ideal.Quotient.factorₐ W₀ (Ideal.pow_le_pow_right (Nat.succ_le_succ h))).comp (Φ' n) = Φ' m := by
    intro m n h
    apply (key m).unique _ ⟨hΦ'res m, hΦ'ι m⟩
    refine ⟨fun r => ?_, fun b => ?_⟩
    · obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Φ' n r)
      have h1 : resT n (Φ' n r) = resR r := hΦ'res n r
      rw [AlgHom.comp_apply, ← hy, Ideal.Quotient.factorₐ_apply_mk, hresT_mk]
      rw [← hy, hresT_mk] at h1
      exact h1
    · rw [AlgHom.comp_apply, hΦ'ι n b, Ideal.Quotient.factorₐ_apply_mk]

  let f : (n : ℕ) → (R →ₐ[W₀] R ⧸ maximalIdeal R ^ n) := fun n =>
    (Ideal.Quotient.factorₐ W₀ (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (Φ' n)
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ W₀ (Ideal.pow_le_pow_right hle)).comp (f n) = f m := by
    intro m n hle
    apply AlgHom.ext
    intro r
    dsimp only [f]
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, ← hcompat m n hle, AlgHom.comp_apply]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Φ' n r)
    rw [← hy]
    simp only [Ideal.Quotient.factorₐ_apply_mk]
  let Φ : R →ₐ[W₀] R := IsAdicComplete.liftAlgHom (maximalIdeal R) f hf
  have hΦmk : ∀ (n : ℕ) (r : R), Ideal.Quotient.mk (maximalIdeal R ^ n) (Φ r) = f n r := by
    intro n r
    have := AlgHom.congr_fun (IsAdicComplete.mkₐ_comp_liftAlgHom (maximalIdeal R) f hf n) r
    rwa [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this

  have hΦ' : ∀ (n : ℕ) (r : R), Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) (Φ r) = Φ' n r := by
    intro n r
    rw [hΦmk]
    show ((Ideal.Quotient.factorₐ W₀ _).comp (Φ' (n + 1))) r = Φ' n r
    rw [hcompat n (n + 1) (Nat.le_succ n)]
  refine ⟨Φ, ⟨fun r => ?_, fun b => ?_⟩, fun Ψ hΨ => ?_⟩
  ·
    rw [← hresT_mk 0 (Φ r), hΦ' 0 r, hΦ'res 0 r]
  ·
    have hmem : ∀ n : ℕ, Φ (ι b) - φ b ∈ maximalIdeal R ^ n := by
      intro n
      cases n with
      | zero => simp
      | succ n =>
        rw [← Ideal.Quotient.eq, hΦ' n (ι b), hΦ'ι n b]
    have h0 : Φ (ι b) - φ b = 0 := by
      refine IsHausdorff.haus (I := maximalIdeal R) inferInstance _ fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact hmem n
    exact sub_eq_zero.mp h0
  ·
    apply IsAdicComplete.algHom_ext (maximalIdeal R)
    intro n
    have hΨn : ∀ m : ℕ, (Ideal.Quotient.mkₐ W₀ (maximalIdeal R ^ (m + 1))).comp Ψ = Φ' m := by
      intro m
      apply (key m).unique _ ⟨hΦ'res m, hΦ'ι m⟩
      refine ⟨fun r => ?_, fun b => ?_⟩
      · rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hresT_mk, hΨ.1]
      · rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hΨ.2]
    rw [IsAdicComplete.mkₐ_comp_liftAlgHom]
    apply AlgHom.ext
    intro r
    dsimp only [f]
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, ← hΨn n, AlgHom.comp_apply,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.factorₐ_apply_mk]

end S_IsAdicComplete_existsUnique_algHom_comp_eq_of_forall_residue_eq_of_factorsThrough_artinian
end P2MW
export P2MW.S_IsAdicComplete_existsUnique_algHom_comp_eq_of_forall_residue_eq_of_factorsThrough_artinian (solution)
