-- Prove2me | solution 1 for N25.frickeCuspCharacter_psi
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:08.639883+00:00
-- url     : https://prove2.me/submissions/0783bb06-0c8a-47db-b9c1-fe89c19bfa60

import Mathlib
import Theorems.Thm_N25_frickeCuspCharacter
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_Endgame_pG25_degree
import Theorems.Thm_ModularCurve_diamondHBar_mul
import Theorems.Thm_ModularCurve_diamondHBar_apply_eq_self_of_mem
import Definitions.Def_N25
import Theorems.Thm_N25_psiBar_two
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_N25_level25_subgroup_membership
import Theorems.Thm_N25_psiBar_ker
import Theorems.Thm_N25_psi_kernel_index
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_N25_characterField_comparison
import Definitions.Def_N25_CharacterField
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace N25

open AlgebraicCurve Endgame

/-- The Fricke cusp line carries the named quintic character. Its point
stabilizer is the kernel of that character and cuts out the quintic field. -/
theorem _root_.solution
    (ι : Qbar →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (25 : ℝ), 0])
    (hcoeff : pointDiff (pG25 0) (pG25 2)
        ((pG25_degree 0).trans (pG25_degree 2).symm) =
      (6 : ℤ) • pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm))
    (h71 : (71 : ℤ) • pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm) = 0)
    (hne : pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm) ≠ 0) :
    let t : J := pointDiff (pG25 0) (pG25 1)
      ((pG25_degree 0).trans (pG25_degree 1).symm)
    ∃ w : FG ≃ₐ[Qbar] FG,
      (∀ (x : FG) (k : ℤ)
          (f g : ModularForm (CohCarrier.GammaH 25 H25 : Subgroup (GL (Fin 2) ℝ)) k),
        ModularCurve.coeffMap ι (x : LaurentSeries Qbar) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
        ModularCurve.coeffMap ι (w x : LaurentSeries Qbar) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W))) ∧
      gamma (SemilinearAut.ofAlgAut w • t) =
        (57 : ℤ) • (SemilinearAut.ofAlgAut w • t) ∧
      (∀ σ : Gal, σ • (SemilinearAut.ofAlgAut w • t) =
        (psi σ : ZMod 71).val • (SemilinearAut.ofAlgAut w • t)) ∧
      (∀ σ : Gal, σ • (SemilinearAut.ofAlgAut w • t) =
        SemilinearAut.ofAlgAut w • t ↔ σ ∈ psi.ker) ∧
      psi.ker.index = 5 ∧
      Nonempty (characterField ≃ₐ[ℚ] IntermediateField.fixedField psi.ker) := by
  let t : J := pointDiff (pG25 0) (pG25 1)
    ((pG25_degree 0).trans (pG25_degree 1).symm)
  obtain ⟨w, hspec, hww, heigen, hformula⟩ := frickeCuspCharacter ι W hW hcoeff h71
  let a : J := SemilinearAut.ofAlgAut w • t
  have ha71 : (71 : ℕ) • a = 0 := by
    have hi : (71 : ℤ) • a = 0 := by
      rw [show (71 : ℤ) • a = SemilinearAut.ofAlgAut w • ((71 : ℤ) • t) from
        (map_zsmul (DistribSMul.toAddMonoidHom J (SemilinearAut.ofAlgAut w)) 71 t).symm, h71]
      exact map_zero (DistribSMul.toAddMonoidHom J (SemilinearAut.ofAlgAut w))
    exact_mod_cast hi
  have hane : a ≠ 0 := by
    intro ha
    apply hne
    change t = 0
    rw [← hww t, show SemilinearAut.ofAlgAut w • t = a from rfl, ha]
    exact map_zero (DistribSMul.toAddMonoidHom J (SemilinearAut.ofAlgAut w))
  have horder : addOrderOf a = 71 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 71)).mp
        (addOrderOf_dvd_of_nsmul_eq_zero ha71) with h | h
    · exact False.elim (hane (AddMonoid.addOrderOf_eq_one_iff.mp h))
    · exact h
  have haction (σ : Gal) : σ • a = (psi σ : ZMod 71).val • a := by
    let c : ℕ := (chi25 σ : ZMod 25).val
    have hc : c.Coprime 25 := (ZMod.isUnit_iff_coprime c 25).mp (by
      simp [c])
    have hu : ZMod.unitOfCoprime c hc = chi25 σ := by
      apply Units.ext
      simp [c]
    have hχ : ∀ ζ : Qbar, ζ ^ 25 = 1 → σ ζ = ζ ^ c := by
      intro ζ hζ
      have hz : ζ ≠ 0 := by intro hz; simp [hz] at hζ
      let z : Qbarˣ := Units.mk0 ζ hz
      have hm : z ∈ rootsOfUnity 25 Qbar := (mem_rootsOfUnity' 25 z).mpr hζ
      exact modularCyclotomicCharacter.spec Qbar
        (IsAlgClosed.card_rootsOfUnity_eq Qbar 25) σ.toRingEquiv hm
    have hcosets : ∀ u : (ZMod 25)ˣ, ∃ k : Fin 5, ∃ h : (ZMod 25)ˣ,
        h ∈ H25 ∧ u = (ZMod.unitOfCoprime 2 (by decide)) ^ k.val * h := by
      simp_rw [level25_subgroup_membership]
      decide
    obtain ⟨k, h, hh, hcoset⟩ := hcosets (chi25 σ)
    have hscalar := hformula σ c hc k.val ⟨h, hh⟩ hχ (hu.trans hcoset)
    have hψ : psi σ = (ZMod.unitOfCoprime 57 (by decide)) ^ k.val := by
      change psiBar (chi25 σ) = _
      have hhker : psiBar h = 1 := MonoidHom.mem_ker.mp (by rw [psiBar_ker]; exact hh)
      rw [hcoset, map_mul, map_pow, psiBar_two, hhker, mul_one]
    have hmod : (psi σ : ZMod 71).val % 71 = 57 ^ k.val % 71 := by
      rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]
      have hv := congrArg (fun u : (ZMod 71)ˣ => (u : ZMod 71).val) hψ
      change (psi σ : ZMod 71).val = ((57 : ZMod 71) ^ k.val).val at hv
      have he : ((57 ^ k.val : ℕ) : ZMod 71) = (57 : ZMod 71) ^ k.val := by simp
      rw [← he, ZMod.val_natCast] at hv
      exact hv
    calc σ • a = (57 ^ k.val : ℕ) • a := by exact_mod_cast hscalar
      _ = (psi σ : ZMod 71).val • a := by
        apply nsmul_eq_nsmul_iff_modEq.mpr
        rw [horder]
        change (57 ^ k.val : ℕ) % 71 = (psi σ : ZMod 71).val % 71
        exact hmod.symm
  refine ⟨w, hspec, heigen, haction, ?_, psi_kernel_index, characterField_comparison.2⟩
  intro σ
  rw [haction]
  change (psi σ : ZMod 71).val • a = a ↔ σ ∈ psi.ker
  rw [MonoidHom.mem_ker]
  have hi : (psi σ : ZMod 71).val • a = a ↔
      Nat.ModEq (addOrderOf a) (psi σ : ZMod 71).val 1 := by
    simpa only [one_nsmul] using
      (nsmul_eq_nsmul_iff_modEq (x := a) (n := (psi σ : ZMod 71).val) (m := 1))
  rw [hi, horder]
  change (psi σ : ZMod 71).val % 71 = 1 % 71 ↔ psi σ = 1
  rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]
  change (psi σ : ZMod 71).val = 1 ↔ psi σ = 1
  constructor
  · intro h
    apply Units.ext
    apply ZMod.val_injective
    change (psi σ : ZMod 71).val = (1 : ZMod 71).val
    rw [ZMod.val_one_eq_one_mod]
    exact h
  · intro h
    rw [h]
    rfl

end N25
