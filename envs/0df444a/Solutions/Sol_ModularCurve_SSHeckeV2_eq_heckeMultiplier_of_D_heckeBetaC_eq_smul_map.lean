-- Prove2me | solution 1 for ModularCurve.SSHeckeV2.eq_heckeMultiplier_of_D_heckeBetaC_eq_smul_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/353ff69a-42b6-5320-a434-1560f567fe30

import Mathlib
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSHeckeV2_eq_heckeMultiplier_of_D_heckeBetaC_eq_smul_map
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve

noncomputable section

namespace FltWs24
namespace HM

variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
  (N : ℕ) [NeZero N] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

include hp in
theorem roof_eq (hN : (N : K) ≠ 0) (hℓK : (ℓ : K) ≠ 0) :
    charLDegeneracyRoof K N ℓ = modularFunctionFieldC K (N * ℓ) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩
  have hpNl : ¬ p ∣ N * ℓ := by
    intro h
    have : ((N * ℓ : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K p _).2 h
    push_cast at this
    exact mul_ne_zero hN hℓK this
  rw [charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul K p N ℓ hpNl,
    ← modularFunctionFieldC_eq_modularFunctionFieldFullC K p (N * ℓ) hpNl]

omit [IsAlgClosed K] [DecidableEq K] in
include hp in
theorem isSeparable_of_eq (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (S : IntermediateField K (LaurentSeries K)) (hS : S = modularFunctionFieldC K M) (hj : jqModC K ∈ S) :
    Algebra.IsSeparable (IntermediateField.adjoin K ({(⟨jqModC K, hj⟩ : ↥S)} : Set ↥S)) ↥S := by
  subst hS
  obtain ⟨data⟩ := nonempty_modularPolynomialData M
  exact (finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC K M data
    (isSeparable_jqNModC_of_natCast_ne_zero K M hM)).2

include hp in

theorem alpha_side (hN : (N : K) ≠ 0) (hℓK : (ℓ : K) ≠ 0) :
    Transcendental K (heckeAlphaC K N ℓ (jGeomGen K N)) ∧
    Algebra.IsSeparable (IntermediateField.adjoin K ({heckeAlphaC K N ℓ (jGeomGen K N)} : Set ↥(charLDegeneracyRoof K N ℓ))) ↥(charLDegeneracyRoof K N ℓ) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩
  set x : ↥(charLDegeneracyRoof K N ℓ) := heckeAlphaC K N ℓ (jGeomGen K N) with hxdef
  have hxcoe : (x : LaurentSeries K) = jqModC K := coe_heckeAlphaC K N ℓ (jGeomGen K N)
  have hjmem : jqModC K ∈ charLDegeneracyRoof K N ℓ := hxcoe ▸ x.2
  have hxeq : x = ⟨jqModC K, hjmem⟩ := Subtype.ext hxcoe
  refine ⟨?_, ?_⟩
  · intro halg
    exact transcendental_jqModC K (hxcoe ▸ IntermediateField.isAlgebraic_iff.1 halg)
  · rw [hxeq]
    exact isSeparable_of_eq p K (N * ℓ) (by push_cast; exact mul_ne_zero hN hℓK) _ (roof_eq p K N ℓ hN hℓK) hjmem

include hp in
theorem spec (hN : (N : K) ≠ 0) (hℓK : (ℓ : K) ≠ 0) :
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ);
    haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ);
    KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N))
      = ModularCurve.heckeMultiplier N K ℓ • KaehlerDifferential.map K K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
          (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  obtain ⟨hxt, hsep⟩ := alpha_side p K N ℓ hN hℓK
  haveI := hsep
  obtain ⟨c, hc, -⟩ := KaehlerDifferential.exists_unique_smul_D_of_transcendental K _ hxt
    (KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N)))
  letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
  haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ)
  have hex : ∃ h : ↥(charLDegeneracyRoof K N ℓ),
      KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N))
        = h • KaehlerDifferential.map K K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) :=
    ⟨c, by rw [KaehlerDifferential.map_D]; exact hc⟩
  exact Classical.epsilon_spec hex

include hp in

theorem map_D_ne_zero (hN : (N : K) ≠ 0) (hℓK : (ℓ : K) ≠ 0) :
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ);
    haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ);
    KaehlerDifferential.map K K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) ≠ 0 := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  obtain ⟨hxt, hsep⟩ := alpha_side p K N ℓ hN hℓK
  haveI := hsep
  letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
  haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ)
  rw [KaehlerDifferential.map_D]
  exact KaehlerDifferential.D_ne_zero_of_transcendental K _ hxt

include hp in

theorem D_heckeBetaC_ne_zero (hN : (N : K) ≠ 0) (hℓK : (ℓ : K) ≠ 0) :
    KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N)) ≠ 0 := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩
  have hpNl : ¬ p ∣ N * ℓ := by
    intro h
    have : ((N * ℓ : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K p _).2 h
    push_cast at this
    exact mul_ne_zero hN hℓK this

  set y : ↥(charLDegeneracyRoof K N ℓ) := heckeBetaC K N ℓ (jGeomGen K N) with hydef
  have hycoe : (y : LaurentSeries K) = jqNModC K ℓ := by
    rw [hydef, coe_heckeBetaC]; rfl
  have hyt : Transcendental K y := by
    intro halg
    exact transcendental_jqNModC K ℓ (hycoe ▸ IntermediateField.isAlgebraic_iff.1 halg)

  set E : IntermediateField K ↥(modularFunctionFieldC K N) := IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N)) with hE
  haveI hEC : Algebra.IsSeparable ↥E ↥(modularFunctionFieldC K N) := by
    have := isSeparable_of_eq p K N hN (modularFunctionFieldC K N) rfl (jqModC_mem K N)
    exact this
  letI := AlgebraicCurve.algebraAlong (heckeBetaC K N ℓ)
  haveI := AlgebraicCurve.isScalarTower_along (heckeBetaC K N ℓ)
  haveI : Algebra.IsSeparable ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) := (separableAlong_heckeAlphaC_heckeBetaC K (ℓ := p) N ℓ hpNl).2
  haveI hER : Algebra.IsSeparable ↥E ↥(charLDegeneracyRoof K N ℓ) := Algebra.IsSeparable.trans ↥E ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
  have hmap : E.map (heckeBetaC K N ℓ) = IntermediateField.adjoin K ({y} : Set ↥(charLDegeneracyRoof K N ℓ)) := by
    rw [hE, IntermediateField.adjoin_map, Set.image_singleton]
  let e : ↥E ≃ₐ[K] ↥(E.map (heckeBetaC K N ℓ)) := E.equivMap (heckeBetaC K N ℓ)
  letI : Algebra ↥E ↥(E.map (heckeBetaC K N ℓ)) := e.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower ↥E ↥(E.map (heckeBetaC K N ℓ)) ↥(charLDegeneracyRoof K N ℓ) :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have hsep : Algebra.IsSeparable ↥(E.map (heckeBetaC K N ℓ)) ↥(charLDegeneracyRoof K N ℓ) :=
    Algebra.isSeparable_tower_top_of_isSeparable ↥E ↥(E.map (heckeBetaC K N ℓ)) ↥(charLDegeneracyRoof K N ℓ)
  rw [hmap] at hsep
  haveI := hsep
  exact KaehlerDifferential.D_ne_zero_of_transcendental K y hyt

end FltWs24.HM

end

open FltWs24.HM in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (h : ↥(charLDegeneracyRoof K N ℓ))
    (hD : letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ);
          haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ);
          KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N))
            = h • KaehlerDifferential.map K K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
                (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N))) :
    h = ModularCurve.heckeMultiplier N K ℓ := by
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h0
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).mp
      ((CharP.cast_eq_zero_iff K p ℓ).mp h0)).symm
  have hs := spec p K N ℓ hN hℓK
  have hω := map_D_ne_zero p K N ℓ hN hℓK
  have key : (h - ModularCurve.heckeMultiplier N K ℓ) •
      (letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ);
       haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ);
       KaehlerDifferential.map K K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
         (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N))) = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr (hD.symm.trans hs)
  rcases smul_eq_zero.mp key with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hω

end S_ModularCurve_SSHeckeV2_eq_heckeMultiplier_of_D_heckeBetaC_eq_smul_map
end P2MW
export P2MW.S_ModularCurve_SSHeckeV2_eq_heckeMultiplier_of_D_heckeBetaC_eq_smul_map (solution)
