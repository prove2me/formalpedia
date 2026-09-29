-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6e7c4696-6531-5043-8327-a62951aacad8

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_schwartz_godementZeta2_whittaker_eq_godementZeta2_section_and_dual_of_equivariant_embedding
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_gamma_forall_rational_godementZeta2_principalSeries2_and_clearedFE
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_whittaker_transposeInvN_shift
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_linearMap_principalSeries2_of_jacquet_ne_top
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible
import Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_matFourier22
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_RankinSelberg_eval_mul_cpow_eq_mul_cpow_mul_eval_of_laurent_fe_of_rational_fe
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.mem_sigmaCentralizer_iff LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

open scoped Topology
noncomputable section

open Polynomial

namespace GammaUniq

theorem injective_rpow_neg (N : ℕ) (hN : 1 < N) : Function.Injective fun t : ℝ => (N : ℂ) ^ (-(t : ℂ)) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  intro t₁ t₂ ht
  have e1 : ∀ t : ℝ, (N : ℂ) ^ (-(t : ℂ)) = (((N : ℝ) ^ (-t) : ℝ) : ℂ) := by
    intro t
    rw [Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ (N : ℝ))]
    push_cast
    rfl
  simp only [e1] at ht
  have ht2 : (N : ℝ) ^ (-t₁) = (N : ℝ) ^ (-t₂) := by exact_mod_cast ht
  have hmono : StrictMono fun t : ℝ => (N : ℝ) ^ t := fun a b hab => (Real.rpow_lt_rpow_left_iff hN1).2 hab
  have := hmono.injective ht2
  linarith

theorem poly_form_eq (N : ℕ) (hN : 1 < N) (S : Set ℝ) (hS : S.Infinite) (f : ℝ → ℂ)
    (P Q P' Q' : ℂ[X]) (m m' : ℤ)
    (h : ∀ t : ℝ, t ∈ S → f t * Q.eval ((N : ℂ) ^ (-(t : ℂ))) = (N : ℂ) ^ ((m : ℂ) * (t : ℂ)) * P.eval ((N : ℂ) ^ (-(t : ℂ))))
    (h' : ∀ t : ℝ, t ∈ S → f t * Q'.eval ((N : ℂ) ^ (-(t : ℂ))) = (N : ℂ) ^ ((m' : ℂ) * (t : ℂ)) * P'.eval ((N : ℂ) ^ (-(t : ℂ)))) :
    Polynomial.X ^ (m' - m).toNat * (P * Q') = Polynomial.X ^ (m - m').toNat * (P' * Q) := by
  classical
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  set e : ℕ := (m' - m).toNat with he
  set e' : ℕ := (m - m').toNat with he'
  set M : ℤ := max m m' with hM
  have hMe : (M : ℤ) - m = e := by
    simp only [he, hM]; rcases le_total m m' with hle | hle
    · rw [max_eq_right hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]
    · rw [max_eq_left hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]; simp
  have hMe' : (M : ℤ) - m' = e' := by
    simp only [he', hM]; rcases le_total m m' with hle | hle
    · rw [max_eq_right hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]; simp
    · rw [max_eq_left hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]
  have hx : ∀ (k : ℤ) (n : ℕ) (t : ℝ), (M : ℤ) - k = n →
      (N : ℂ) ^ ((k : ℂ) * (t : ℂ)) * (N : ℂ) ^ (-((M : ℂ) * (t : ℂ))) = ((N : ℂ) ^ (-(t : ℂ))) ^ n := by
    intro k n t hk
    rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_nat_mul]
    congr 1
    have : (n : ℂ) = (M : ℂ) - (k : ℂ) := by exact_mod_cast hk.symm
    rw [this]; ring
  have hA : ∀ t : ℝ, t ∈ S →
      (Polynomial.X ^ e * (P * Q')).eval ((N : ℂ) ^ (-(t : ℂ))) =
        (Polynomial.X ^ e' * (P' * Q)).eval ((N : ℂ) ^ (-(t : ℂ))) := by
    intro t ht
    have h1 := h t ht
    have h2 := h' t ht
    have key : (N : ℂ) ^ ((m : ℂ) * (t : ℂ)) * P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ))) =
        (N : ℂ) ^ ((m' : ℂ) * (t : ℂ)) * P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ))) := by
      calc (N : ℂ) ^ ((m : ℂ) * (t : ℂ)) * P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ)))
          = (f t * Q.eval ((N : ℂ) ^ (-(t : ℂ)))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ))) := by rw [h1]
        _ = (f t * Q'.eval ((N : ℂ) ^ (-(t : ℂ)))) * Q.eval ((N : ℂ) ^ (-(t : ℂ))) := by ring
        _ = (N : ℂ) ^ ((m' : ℂ) * (t : ℂ)) * P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ))) := by rw [h2]
    have key2 := congrArg (fun z => z * (N : ℂ) ^ (-((M : ℂ) * (t : ℂ)))) key
    have l1 := hx m e t hMe
    have l2 := hx m' e' t hMe'
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    calc ((N : ℂ) ^ (-(t : ℂ))) ^ e * (P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ))))
        = ((N : ℂ) ^ ((m : ℂ) * (t : ℂ)) * P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ)))) *
            (N : ℂ) ^ (-((M : ℂ) * (t : ℂ))) := by rw [← l1]; ring
      _ = ((N : ℂ) ^ ((m' : ℂ) * (t : ℂ)) * P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ)))) *
            (N : ℂ) ^ (-((M : ℂ) * (t : ℂ))) := key2
      _ = ((N : ℂ) ^ (-(t : ℂ))) ^ e' * (P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ)))) := by rw [← l2]; ring
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := (fun t : ℝ => (N : ℂ) ^ (-(t : ℂ))) '' S) ?_ ?_
  · rintro x ⟨t, ht, rfl⟩; exact hA t ht
  · exact hS.image (injective_rpow_neg N hN).injOn

theorem eval_identity (N : ℕ) (hN : 1 < N) (A B : ℂ[X]) (i j : ℕ) (a b : ℤ) (hij : (i : ℤ) + a = (j : ℤ) + b)
    (h : Polynomial.X ^ i * A = Polynomial.X ^ j * B) (s : ℂ) :
    A.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s) = B.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((b : ℂ) * s) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hev := congrArg (Polynomial.eval ((N : ℂ) ^ (-s))) h
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hev
  have hi : ((N : ℂ) ^ (-s)) ^ i * (N : ℂ) ^ (((i : ℤ) + a : ℂ) * s) = (N : ℂ) ^ ((a : ℂ) * s) := by
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hN0]; congr 1; push_cast; ring
  have hj : ((N : ℂ) ^ (-s)) ^ j * (N : ℂ) ^ (((j : ℤ) + b : ℂ) * s) = (N : ℂ) ^ ((b : ℂ) * s) := by
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hN0]; congr 1; push_cast; ring
  have hc : (((i : ℤ) + a : ℂ)) = (((j : ℤ) + b : ℂ)) := by exact_mod_cast hij
  calc A.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s)
      = A.eval ((N : ℂ) ^ (-s)) * (((N : ℂ) ^ (-s)) ^ i * (N : ℂ) ^ (((i : ℤ) + a : ℂ) * s)) := by rw [hi]
    _ = (((N : ℂ) ^ (-s)) ^ i * A.eval ((N : ℂ) ^ (-s))) * (N : ℂ) ^ (((i : ℤ) + a : ℂ) * s) := by ring
    _ = (((N : ℂ) ^ (-s)) ^ j * B.eval ((N : ℂ) ^ (-s))) * (N : ℂ) ^ (((j : ℤ) + b : ℂ) * s) := by rw [hev, hc]
    _ = B.eval ((N : ℂ) ^ (-s)) * (((N : ℂ) ^ (-s)) ^ j * (N : ℂ) ^ (((j : ℤ) + b : ℂ) * s)) := by ring
    _ = B.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((b : ℂ) * s) := by rw [hj]

theorem toNat_sub_toNat (k l : ℤ) : (((k - l).toNat : ℤ)) - (((l - k).toNat : ℤ)) = k - l := by
  rw [show l - k = -(k - l) by ring]; exact Int.toNat_sub_toNat_neg (k - l)

theorem gamma_unique (N : ℕ) (hN : 1 < N) (Z Zd : ℂ → ℂ) (E : ℂ) (e : ℤ)
    (P Pd : ℂ[X]) (m md : ℤ) (σ₀ σ₁ : ℝ)
    (hZ : ∀ s : ℂ, σ₀ < s.re → Z s = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)))
    (hZd : ∀ s : ℂ, s.re < σ₁ → Zd s = (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)))
    (hE : ∀ s : ℂ, (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) =
      (E * (N : ℂ) ^ ((e : ℂ) * s)) * ((N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))))
    (P' Q' Pd' Qd' Γn Γd : ℂ[X]) (m' md' a : ℤ) (σ₀' σ₁' : ℝ) (hQ' : Q' ≠ 0) (hQd' : Qd' ≠ 0)
    (hZ' : ∀ s : ℂ, σ₀' < s.re → Z s * Q'.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s)))
    (hZd' : ∀ s : ℂ, s.re < σ₁' → Zd s * Qd'.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((md' : ℂ) * s) * Pd'.eval ((N : ℂ) ^ (-s)))
    (hΓ : ∀ s : ℂ, Γd.eval ((N : ℂ) ^ (-s)) * ((N : ℂ) ^ ((md' : ℂ) * s) * Pd'.eval ((N : ℂ) ^ (-s))) * Q'.eval ((N : ℂ) ^ (-s)) =
      Γn.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s) * ((N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s))) * Qd'.eval ((N : ℂ) ^ (-s)))
    (hP : P ≠ 0) :
    ∀ s : ℂ, Γn.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s) = E * (N : ℂ) ^ ((e : ℂ) * s) * Γd.eval ((N : ℂ) ^ (-s)) := by
  classical
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)

  have B1 := poly_form_eq N hN (Set.Ioi (max σ₀ σ₀')) (Set.Ioi_infinite _) (fun t => Z t) P 1 P' Q' m m' ?_ ?_
  rotate_left
  · intro t ht
    have : σ₀ < ((t : ℂ)).re := by simp only [Complex.ofReal_re]; exact lt_of_le_of_lt (le_max_left _ _) ht
    simp only [Polynomial.eval_one, mul_one]; exact hZ _ this
  · intro t ht
    have : σ₀' < ((t : ℂ)).re := by simp only [Complex.ofReal_re]; exact lt_of_le_of_lt (le_max_right _ _) ht
    exact hZ' _ this

  have B2 := poly_form_eq N hN (Set.Iio (min σ₁ σ₁')) (Set.Iio_infinite _) (fun t => Zd t) Pd 1 Pd' Qd' md md' ?_ ?_
  rotate_left
  · intro t ht
    have : ((t : ℂ)).re < σ₁ := by simp only [Complex.ofReal_re]; exact lt_of_lt_of_le ht (min_le_left _ _)
    simp only [Polynomial.eval_one, mul_one]; exact hZd _ this
  · intro t ht
    have : ((t : ℂ)).re < σ₁' := by simp only [Complex.ofReal_re]; exact lt_of_lt_of_le ht (min_le_right _ _)
    exact hZd' _ this

  have B3 := poly_form_eq N hN Set.univ Set.infinite_univ
    (fun t => (N : ℂ) ^ ((md : ℂ) * (t : ℂ)) * Pd.eval ((N : ℂ) ^ (-(t : ℂ)))) Pd 1 (Polynomial.C E * P) 1 md (m + e) ?_ ?_
  rotate_left
  · intro t _; simp only [Polynomial.eval_one, mul_one]
  · intro t _
    simp only [Polynomial.eval_one, mul_one]
    rw [hE, Polynomial.eval_mul, Polynomial.eval_C]
    rw [show (((m + e : ℤ)) : ℂ) * (t : ℂ) = (e : ℂ) * (t : ℂ) + (m : ℂ) * (t : ℂ) by push_cast; ring, Complex.cpow_add _ _ hN0]
    ring

  have B4 := poly_form_eq N hN Set.univ Set.infinite_univ
    (fun t => Γd.eval ((N : ℂ) ^ (-(t : ℂ))) * ((N : ℂ) ^ ((md' : ℂ) * (t : ℂ)) * Pd'.eval ((N : ℂ) ^ (-(t : ℂ)))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ))))
    (Γd * Pd' * Q') 1 (Γn * P' * Qd') 1 md' (a + m') ?_ ?_
  rotate_left
  · intro t _; simp only [Polynomial.eval_one, mul_one, Polynomial.eval_mul]; ring
  · intro t _
    simp only [Polynomial.eval_one, mul_one]
    rw [hΓ, Polynomial.eval_mul, Polynomial.eval_mul]
    rw [show (((a + m' : ℤ)) : ℂ) * (t : ℂ) = (a : ℂ) * (t : ℂ) + (m' : ℂ) * (t : ℂ) by push_cast; ring, Complex.cpow_add _ _ hN0]
    ring

  set i₁ := (m' - m).toNat; set j₁ := (m - m').toNat
  set i₂ := (md' - md).toNat; set j₂ := (md - md').toNat
  set i₃ := (m + e - md).toNat; set j₃ := (md - (m + e)).toNat
  set i₄ := (a + m' - md').toNat; set j₄ := (md' - (a + m')).toNat
  have hG : Polynomial.X ^ (j₄ + j₂ + i₁ + i₃) * Γn * (P * Q' * Qd') =
      Polynomial.X ^ (i₄ + j₁ + i₂ + j₃) * (Polynomial.C E * Γd) * (P * Q' * Qd') := by
    linear_combination (Polynomial.X ^ (j₄ + j₂ + i₃) * Γn * Qd') * B1 + (-(Polynomial.X ^ (i₄ + j₁ + i₃) * Γd * Q')) * B2 +
      (Polynomial.X ^ (i₄ + j₁ + i₂) * Γd * Qd' * Q') * B3 + (-(Polynomial.X ^ (j₁ + j₂ + i₃))) * B4
  have hnz : P * Q' * Qd' ≠ 0 := mul_ne_zero (mul_ne_zero hP hQ') hQd'
  have hpoly : Polynomial.X ^ (j₄ + j₂ + i₁ + i₃) * Γn = Polynomial.X ^ (i₄ + j₁ + i₂ + j₃) * (Polynomial.C E * Γd) :=
    mul_right_cancel₀ hnz hG

  have r₁ := toNat_sub_toNat m' m
  have r₂ := toNat_sub_toNat md' md
  have r₃ := toNat_sub_toNat (m + e) md
  have r₄ := toNat_sub_toNat (a + m') md'
  intro s
  have := eval_identity N hN Γn (Polynomial.C E * Γd) (j₄ + j₂ + i₁ + i₃) (i₄ + j₁ + i₂ + j₃) a e
    (by push_cast; omega) hpoly s
  rw [Polynomial.eval_mul, Polynomial.eval_C] at this
  rw [this]; ring

end GammaUniq

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.higherUnitsAt RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_godementZeta2_section_and_dual_of_equivariant_embedding RankinSelberg.exists_gamma_forall_rational_godementZeta2_principalSeries2_and_clearedFE RankinSelberg.forall_exists_integrable_godementZeta2_whittaker_transposeInvN_shift CubicInduction.exists_linearMap_principalSeries2_of_jacquet_ne_top RankinSelberg.exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible CubicInduction.isSchwartzBruhat_matFourier22 TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.addCharLevel_psiLocal_rat TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.psiLocal_ne_one RankinSelberg.eval_mul_cpow_eq_mul_cpow_mul_eval_of_laurent_fe_of_rational_fe RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "exists_schwartz_godementZeta2_whittaker_eq_godementZeta2_section_and_dual_of_equivariant_embedding exists_gamma_forall_rational_godementZeta2_principalSeries2_and_clearedFE forall_exists_integrable_godementZeta2_whittaker_transposeInvN_shift exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible eval_mul_cpow_eq_mul_cpow_mul_eval_of_laurent_fe_of_rational_fe exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable"
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

namespace R2Alg
open Polynomial

theorem extend_identity (N : ℕ) (hN : 1 < N) (S : Set ℝ) (hS : S.Infinite) (A B : ℂ[X]) (a b : ℤ)
    (h : ∀ t : ℝ, t ∈ S → A.eval ((N : ℂ) ^ (-(t : ℂ))) * (N : ℂ) ^ ((a : ℂ) * (t : ℂ)) =
      B.eval ((N : ℂ) ^ (-(t : ℂ))) * (N : ℂ) ^ ((b : ℂ) * (t : ℂ))) :
    ∀ s : ℂ, A.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s) = B.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((b : ℂ) * s) := by
  have hpoly := GammaUniq.poly_form_eq N hN S hS (fun t => A.eval ((N : ℂ) ^ (-(t : ℂ))) * (N : ℂ) ^ ((a : ℂ) * (t : ℂ)))
    A 1 B 1 a b (fun t _ => by simp only [Polynomial.eval_one, mul_one]; ring)
    (fun t ht => by simp only [Polynomial.eval_one, mul_one]; rw [h t ht]; ring)
  simp only [mul_one] at hpoly
  intro s
  exact GammaUniq.eval_identity N hN A B _ _ a b (by have := GammaUniq.toNat_sub_toNat b a; omega) hpoly s

theorem cancel_identity (N : ℕ) (hN : 1 < N) (Γ A B : ℂ[X]) (hΓ : Γ ≠ 0) (a b : ℤ)
    (h : ∀ s : ℂ, Γ.eval ((N : ℂ) ^ (-s)) * (A.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s)) =
      Γ.eval ((N : ℂ) ^ (-s)) * (B.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((b : ℂ) * s))) :
    ∀ s : ℂ, A.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s) = B.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((b : ℂ) * s) := by
  have hpoly := GammaUniq.poly_form_eq N hN (Set.univ : Set ℝ) Set.infinite_univ
    (fun t => Γ.eval ((N : ℂ) ^ (-(t : ℂ))) * (A.eval ((N : ℂ) ^ (-(t : ℂ))) * (N : ℂ) ^ ((a : ℂ) * (t : ℂ))))
    (Γ * A) 1 (Γ * B) 1 a b
    (fun t _ => by simp only [Polynomial.eval_one, Polynomial.eval_mul, mul_one]; ring)
    (fun t _ => by simp only [Polynomial.eval_one, Polynomial.eval_mul, mul_one]; rw [h (t : ℂ)]; ring)
  simp only [mul_one] at hpoly
  have hc : Polynomial.X ^ (b - a).toNat * A = Polynomial.X ^ (a - b).toNat * B := by
    apply mul_left_cancel₀ hΓ
    calc Γ * (X ^ (b - a).toNat * A) = X ^ (b - a).toNat * (Γ * A) := by ring
      _ = X ^ (a - b).toNat * (Γ * B) := hpoly
      _ = Γ * (X ^ (a - b).toNat * B) := by ring
  intro s
  exact GammaUniq.eval_identity N hN A B _ _ a b (by have := GammaUniq.toNat_sub_toNat b a; omega) hc s

theorem eval_cpow_eq_reflect (N : ℕ) (hN : 1 < N) (R : ℂ[X]) (d : ℕ) (hd : R.natDegree ≤ d) (s : ℂ) :
    R.eval ((N : ℂ) ^ s) = (Polynomial.reflect d R).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((d : ℂ) * s) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hx : (N : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hN0)
  letI : Invertible ((N : ℂ) ^ s) := invertibleOfNonzero hx
  have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) ((N : ℂ) ^ s) d R hd
  simp only [Polynomial.eval₂_id] at h
  have hinv : (⅟((N : ℂ) ^ s) : ℂ) = (N : ℂ) ^ (-s) := by
    rw [invOf_eq_inv, Complex.cpow_neg]
  rw [← h, hinv, ← Complex.cpow_nat_mul]

end R2Alg

namespace R2Alg
open Polynomial

theorem cpow_N_ne_zero (N : ℕ) (hN : 1 < N) (z : ℂ) : (N : ℂ) ^ z ≠ 0 :=
  Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast (show N ≠ 0 by omega)))

theorem transport (N : ℕ) (hN : 1 < N)
    (P Pd Q Qd PA PdA QA QdA : ℂ[X]) (m md mA mdA : ℤ) (E : ℂ) (e : ℤ) (hQA : QA ≠ 0) (hQdA : QdA ≠ 0)
    (R1 : ∀ s : ℂ, (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) * QA.eval ((N : ℂ) ^ (-s)) =
      (N : ℂ) ^ ((mA : ℂ) * s) * PA.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ (-s)))
    (R2 : ∀ s : ℂ, (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) * QdA.eval ((N : ℂ) ^ (-s)) =
      (N : ℂ) ^ ((mdA : ℂ) * s) * PdA.eval ((N : ℂ) ^ (-s)) * Qd.eval ((N : ℂ) ^ (-s)))
    (hvA : ∀ s : ℂ, (N : ℂ) ^ ((mdA : ℂ) * s) * PdA.eval ((N : ℂ) ^ (-s)) * QA.eval ((N : ℂ) ^ s) =
      E * (N : ℂ) ^ ((e : ℂ) * s) * ((N : ℂ) ^ ((mA : ℂ) * (-s)) * PA.eval ((N : ℂ) ^ s)) * QdA.eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ s) =
      E * (N : ℂ) ^ ((e : ℂ) * s) * ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s)) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  set dQ := Q.natDegree with hdQ
  set dP := P.natDegree with hdP
  set dA := QA.natDegree with hdA
  have rQ : ∀ s : ℂ, Q.eval ((N : ℂ) ^ s) = (reflect dQ Q).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((dQ : ℂ) * s) :=
    fun s => eval_cpow_eq_reflect N hN Q dQ le_rfl s
  have rP : ∀ s : ℂ, P.eval ((N : ℂ) ^ s) = (reflect dP P).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((dP : ℂ) * s) :=
    fun s => eval_cpow_eq_reflect N hN P dP le_rfl s
  have rA : ∀ s : ℂ, QA.eval ((N : ℂ) ^ s) = (reflect dA QA).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((dA : ℂ) * s) :=
    fun s => eval_cpow_eq_reflect N hN QA dA le_rfl s
  have hΓ : reflect dA QA * QdA ≠ 0 := mul_ne_zero (fun h => hQA (reflect_eq_zero_iff.1 h)) hQdA

  have h1 : ∀ s : ℂ,
      ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ s)) *
          (QA.eval ((N : ℂ) ^ s) * QdA.eval ((N : ℂ) ^ (-s))) =
        (E * (N : ℂ) ^ ((e : ℂ) * s) * ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s))) *
          (QA.eval ((N : ℂ) ^ s) * QdA.eval ((N : ℂ) ^ (-s))) := by
    intro s
    have r1 := R1 (-s)
    simp only [neg_neg] at r1
    have r2 := R2 s
    have hv := hvA s
    linear_combination (Q.eval ((N : ℂ) ^ s) * QA.eval ((N : ℂ) ^ s)) * r2 + (Qd.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ s)) * hv +
      (-(E * (N : ℂ) ^ ((e : ℂ) * s) * QdA.eval ((N : ℂ) ^ (-s)) * Qd.eval ((N : ℂ) ^ (-s)))) * r1

  set a : ℤ := md + (dQ : ℤ) + (dA : ℤ) with ha
  set b : ℤ := e - m + (dP : ℤ) + (dA : ℤ) with hb
  have hNa : ∀ s : ℂ, (N : ℂ) ^ ((a : ℂ) * s) = (N : ℂ) ^ ((md : ℂ) * s) * (N : ℂ) ^ ((dQ : ℂ) * s) * (N : ℂ) ^ ((dA : ℂ) * s) := by
    intro s; rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0]; congr 1; simp only [ha]; push_cast; ring
  have hNb : ∀ s : ℂ, (N : ℂ) ^ ((b : ℂ) * s) =
      (N : ℂ) ^ ((e : ℂ) * s) * (N : ℂ) ^ ((m : ℂ) * (-s)) * (N : ℂ) ^ ((dP : ℂ) * s) * (N : ℂ) ^ ((dA : ℂ) * s) := by
    intro s; rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0]; congr 1
    simp only [hb]; push_cast; ring
  have h2 : ∀ s : ℂ, (reflect dA QA * QdA).eval ((N : ℂ) ^ (-s)) *
        ((Pd * reflect dQ Q).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s)) =
      (reflect dA QA * QdA).eval ((N : ℂ) ^ (-s)) *
        ((E • (reflect dP P * Qd)).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((b : ℂ) * s)) := by
    intro s
    have := h1 s
    rw [rQ s, rP s, rA s] at this
    simp only [eval_mul, eval_smul, smul_eq_mul, hNa s, hNb s]
    linear_combination this
  have h3 := cancel_identity N hN _ _ _ hΓ a b h2

  intro s
  have := h3 s
  simp only [eval_mul, eval_smul, smul_eq_mul, hNa s, hNb s] at this
  rw [rQ s, rP s]
  apply mul_right_cancel₀ (cpow_N_ne_zero N hN ((dA : ℂ) * s))
  linear_combination this

end R2Alg

namespace R2Alg
open Polynomial

theorem natDegree_reflect_le' {d : ℕ} {R : ℂ[X]} (hd : R.natDegree ≤ d) : (reflect d R).natDegree ≤ d :=
  natDegree_reflect_le.trans (max_le le_rfl hd)

theorem eval_reflect_cpow (N : ℕ) (hN : 1 < N) (R : ℂ[X]) (d : ℕ) (hd : R.natDegree ≤ d) (s : ℂ) :
    (reflect d R).eval ((N : ℂ) ^ s) = R.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((d : ℂ) * s) := by
  have := eval_cpow_eq_reflect N hN (reflect d R) d (natDegree_reflect_le' hd) s
  rw [reflect_reflect] at this
  exact this

theorem gamma_pin (N : ℕ) (hN : 1 < N) (Z Zd : ℂ → ℂ) (E₀ : ℂ) (e₀ : ℤ)
    (P₀ Pd₀ : ℂ[X]) (m₀ md₀ : ℤ) (σ₀ σ₁ : ℝ)
    (hZ : ∀ s : ℂ, σ₀ < s.re → Z s = (N : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval ((N : ℂ) ^ (-s)))
    (hZd : ∀ s : ℂ, s.re < σ₁ → Zd s = (N : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((N : ℂ) ^ (-s)))
    (hE : ∀ s : ℂ, (N : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((N : ℂ) ^ (-s)) =
      (E₀ * (N : ℂ) ^ ((e₀ : ℂ) * s)) * ((N : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval ((N : ℂ) ^ (-s))))
    (hP₀ : P₀ ≠ 0)
    (C : ℂ) (hC : C ≠ 0) (PA PdA QA QdA Γn Γd : ℂ[X]) (mA mdA eΓ : ℤ) (ρ ρ' : ℝ) (hQA : QA ≠ 0) (hQdA : QdA ≠ 0)
    (hZ' : ∀ s : ℂ, ρ < s.re → C * Z s * QA.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mA : ℂ) * s) * PA.eval ((N : ℂ) ^ (-s)))
    (hZd' : ∀ s : ℂ, s.re < ρ' → C * Zd s * QdA.eval ((N : ℂ) ^ s) = (N : ℂ) ^ ((mdA : ℂ) * (-s)) * PdA.eval ((N : ℂ) ^ s))
    (hvA : ∀ s : ℂ, (N : ℂ) ^ ((mdA : ℂ) * s) * PdA.eval ((N : ℂ) ^ (-s)) * QA.eval ((N : ℂ) ^ s) * Γd.eval ((N : ℂ) ^ (-s)) =
      Γn.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((eΓ : ℂ) * s) * ((N : ℂ) ^ ((mA : ℂ) * (-s)) * PA.eval ((N : ℂ) ^ s)) *
        QdA.eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, Γn.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((eΓ : ℂ) * s) =
      E₀ * (N : ℂ) ^ (((-e₀ : ℤ) : ℂ) * s) * Γd.eval ((N : ℂ) ^ (-s)) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  set dqd := QdA.natDegree with hdqd
  set dpd := PdA.natDegree with hdpd
  set dgn := Γn.natDegree with hdgn
  set dgd := Γd.natDegree with hdgd
  have rQd : ∀ s : ℂ, QdA.eval ((N : ℂ) ^ s) = (reflect dqd QdA).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((dqd : ℂ) * s) :=
    fun s => eval_cpow_eq_reflect N hN QdA dqd le_rfl s
  have rPd : ∀ s : ℂ, PdA.eval ((N : ℂ) ^ s) = (reflect dpd PdA).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((dpd : ℂ) * s) :=
    fun s => eval_cpow_eq_reflect N hN PdA dpd le_rfl s
  have rGn : ∀ s : ℂ, Γn.eval ((N : ℂ) ^ s) = (reflect dgn Γn).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((dgn : ℂ) * s) :=
    fun s => eval_cpow_eq_reflect N hN Γn dgn le_rfl s
  have rGd : ∀ s : ℂ, Γd.eval ((N : ℂ) ^ s) = (reflect dgd Γd).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((dgd : ℂ) * s) :=
    fun s => eval_cpow_eq_reflect N hN Γd dgd le_rfl s
  have hQd'' : reflect dqd QdA ≠ 0 := fun h => hQdA (reflect_eq_zero_iff.1 h)
  set md' : ℤ := (dpd : ℤ) - (dqd : ℤ) - mdA with hmd'
  set a : ℤ := (dgn : ℤ) - (dgd : ℤ) - eΓ with ha

  set Zt : ℂ → ℂ := fun s => C * Z s with hZt
  set Zdt : ℂ → ℂ := fun s => C * Zd s with hZdt
  have tZ : ∀ s : ℂ, σ₀ < s.re → Zt s = (N : ℂ) ^ ((m₀ : ℂ) * s) * (C • P₀).eval ((N : ℂ) ^ (-s)) := by
    intro s hs; simp only [hZt, hZ s hs, eval_smul, smul_eq_mul]; ring
  have tZd : ∀ s : ℂ, s.re < σ₁ → Zdt s = (N : ℂ) ^ ((md₀ : ℂ) * s) * (C • Pd₀).eval ((N : ℂ) ^ (-s)) := by
    intro s hs; simp only [hZdt, hZd s hs, eval_smul, smul_eq_mul]; ring
  have tE : ∀ s : ℂ, (N : ℂ) ^ ((md₀ : ℂ) * s) * (C • Pd₀).eval ((N : ℂ) ^ (-s)) =
      (E₀ * (N : ℂ) ^ ((e₀ : ℂ) * s)) * ((N : ℂ) ^ ((m₀ : ℂ) * s) * (C • P₀).eval ((N : ℂ) ^ (-s))) := by
    intro s; simp only [eval_smul, smul_eq_mul]; linear_combination C * hE s
  have tP : C • P₀ ≠ 0 := smul_ne_zero hC hP₀
  have gZ' : ∀ s : ℂ, ρ < s.re → Zt s * QA.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mA : ℂ) * s) * PA.eval ((N : ℂ) ^ (-s)) :=
    fun s hs => by simp only [hZt]; exact hZ' s hs
  have gZd' : ∀ s : ℂ, s.re < ρ' →
      Zdt s * (reflect dqd QdA).eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((md' : ℂ) * s) * (reflect dpd PdA).eval ((N : ℂ) ^ (-s)) := by
    intro s hs
    have h0 := hZd' s hs
    rw [rQd s, rPd s] at h0
    simp only [hZdt]
    have e1 : (N : ℂ) ^ ((mdA : ℂ) * (-s)) * (N : ℂ) ^ ((dpd : ℂ) * s) = (N : ℂ) ^ ((md' : ℂ) * s) * (N : ℂ) ^ ((dqd : ℂ) * s) := by
      rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0]; congr 1; simp only [hmd']; push_cast; ring
    apply mul_right_cancel₀ (cpow_N_ne_zero N hN ((dqd : ℂ) * s))
    linear_combination h0 + ((reflect dpd PdA).eval ((N : ℂ) ^ (-s))) * e1
  have gΓ : ∀ s : ℂ, (reflect dgd Γd).eval ((N : ℂ) ^ (-s)) *
        ((N : ℂ) ^ ((md' : ℂ) * s) * (reflect dpd PdA).eval ((N : ℂ) ^ (-s))) * QA.eval ((N : ℂ) ^ (-s)) =
      (reflect dgn Γn).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s) *
        ((N : ℂ) ^ ((mA : ℂ) * s) * PA.eval ((N : ℂ) ^ (-s))) * (reflect dqd QdA).eval ((N : ℂ) ^ (-s)) := by
    intro s
    have h0 := hvA (-s)
    simp only [neg_neg] at h0
    rw [rQd s, rPd s, rGn s, rGd s] at h0
    have e1 : (N : ℂ) ^ ((mdA : ℂ) * (-s)) * (N : ℂ) ^ ((dpd : ℂ) * s) = (N : ℂ) ^ ((md' : ℂ) * s) * (N : ℂ) ^ ((dqd : ℂ) * s) := by
      rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0]; congr 1; simp only [hmd']; push_cast; ring
    have e2 : (N : ℂ) ^ ((dgn : ℂ) * s) * (N : ℂ) ^ ((eΓ : ℂ) * (-s)) = (N : ℂ) ^ ((a : ℂ) * s) * (N : ℂ) ^ ((dgd : ℂ) * s) := by
      rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0]; congr 1; simp only [ha]; push_cast; ring
    apply mul_right_cancel₀ (mul_ne_zero (cpow_N_ne_zero N hN ((dgd : ℂ) * s)) (cpow_N_ne_zero N hN ((dqd : ℂ) * s)))
    linear_combination h0 -
      ((reflect dpd PdA).eval ((N : ℂ) ^ (-s)) * QA.eval ((N : ℂ) ^ (-s)) * (reflect dgd Γd).eval ((N : ℂ) ^ (-s)) *
        (N : ℂ) ^ ((dgd : ℂ) * s)) * e1 +
      ((reflect dgn Γn).eval ((N : ℂ) ^ (-s)) * PA.eval ((N : ℂ) ^ (-s)) * (reflect dqd QdA).eval ((N : ℂ) ^ (-s)) *
        (N : ℂ) ^ ((mA : ℂ) * s) * (N : ℂ) ^ ((dqd : ℂ) * s)) * e2
  have G := LanglandsTunnell.RankinSelberg.eval_mul_cpow_eq_mul_cpow_mul_eval_of_laurent_fe_of_rational_fe N hN Zt Zdt E₀ e₀
    (C • P₀) (C • Pd₀) m₀ md₀ σ₀ σ₁ tZ tZd tE PA QA (reflect dpd PdA) (reflect dqd QdA) (reflect dgn Γn) (reflect dgd Γd)
    mA md' a ρ ρ' hQA hQd'' gZ' gZd' gΓ tP
  intro s
  have h0 := G (-s)
  simp only [neg_neg] at h0
  rw [eval_reflect_cpow N hN Γn dgn le_rfl, eval_reflect_cpow N hN Γd dgd le_rfl] at h0
  have e3 : (N : ℂ) ^ ((dgn : ℂ) * s) * (N : ℂ) ^ ((a : ℂ) * (-s)) = (N : ℂ) ^ ((eΓ : ℂ) * s) * (N : ℂ) ^ ((dgd : ℂ) * s) := by
    rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0]; congr 1; simp only [ha]; push_cast; ring
  have e4 : (N : ℂ) ^ ((e₀ : ℂ) * (-s)) = (N : ℂ) ^ (((-e₀ : ℤ) : ℂ) * s) := by congr 1; push_cast; ring
  apply mul_right_cancel₀ (cpow_N_ne_zero N hN ((dgd : ℂ) * s))
  linear_combination h0 - (Γn.eval ((N : ℂ) ^ (-s))) * e3 + (E₀ * Γd.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((dgd : ℂ) * s)) * e4

theorem fe_monomial_of_gamma_pin (N : ℕ) (hN : 1 < N) (E₀ : ℂ) (e₀ : ℤ)
    (PA PdA QA QdA Γn Γd : ℂ[X]) (mA mdA eΓ : ℤ) (hΓd : Γd ≠ 0)
    (hpin : ∀ s : ℂ, Γn.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((eΓ : ℂ) * s) =
      E₀ * (N : ℂ) ^ (((-e₀ : ℤ) : ℂ) * s) * Γd.eval ((N : ℂ) ^ (-s)))
    (hvA : ∀ s : ℂ, (N : ℂ) ^ ((mdA : ℂ) * s) * PdA.eval ((N : ℂ) ^ (-s)) * QA.eval ((N : ℂ) ^ s) * Γd.eval ((N : ℂ) ^ (-s)) =
      Γn.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((eΓ : ℂ) * s) * ((N : ℂ) ^ ((mA : ℂ) * (-s)) * PA.eval ((N : ℂ) ^ s)) *
        QdA.eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, (N : ℂ) ^ ((mdA : ℂ) * s) * PdA.eval ((N : ℂ) ^ (-s)) * QA.eval ((N : ℂ) ^ s) =
      E₀ * (N : ℂ) ^ (((-e₀ : ℤ) : ℂ) * s) * ((N : ℂ) ^ ((mA : ℂ) * (-s)) * PA.eval ((N : ℂ) ^ s)) * QdA.eval ((N : ℂ) ^ (-s)) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  set dA := QA.natDegree with hdA
  set dP := PA.natDegree with hdP
  have rA : ∀ s : ℂ, QA.eval ((N : ℂ) ^ s) = (reflect dA QA).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((dA : ℂ) * s) :=
    fun s => eval_cpow_eq_reflect N hN QA dA le_rfl s
  have rP : ∀ s : ℂ, PA.eval ((N : ℂ) ^ s) = (reflect dP PA).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((dP : ℂ) * s) :=
    fun s => eval_cpow_eq_reflect N hN PA dP le_rfl s
  set a : ℤ := mdA + (dA : ℤ) with ha
  set b : ℤ := -e₀ - mA + (dP : ℤ) with hb
  have hNa : ∀ s : ℂ, (N : ℂ) ^ ((a : ℂ) * s) = (N : ℂ) ^ ((mdA : ℂ) * s) * (N : ℂ) ^ ((dA : ℂ) * s) := by
    intro s; rw [← Complex.cpow_add _ _ hN0]; congr 1; simp only [ha]; push_cast; ring
  have hNb : ∀ s : ℂ, (N : ℂ) ^ ((b : ℂ) * s) = (N : ℂ) ^ (((-e₀ : ℤ) : ℂ) * s) * (N : ℂ) ^ ((mA : ℂ) * (-s)) * (N : ℂ) ^ ((dP : ℂ) * s) := by
    intro s; rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0]; congr 1; simp only [hb]; push_cast; ring
  have h2 : ∀ s : ℂ, Γd.eval ((N : ℂ) ^ (-s)) * ((PdA * reflect dA QA).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((a : ℂ) * s)) =
      Γd.eval ((N : ℂ) ^ (-s)) * ((E₀ • (reflect dP PA * QdA)).eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((b : ℂ) * s)) := by
    intro s
    have h0 := hvA s
    rw [rA s, rP s, hpin s] at h0
    simp only [eval_mul, eval_smul, smul_eq_mul, hNa s, hNb s]
    linear_combination h0
  have h3 := cancel_identity N hN _ _ _ hΓd a b h2
  intro s
  have := h3 s
  simp only [eval_mul, eval_smul, smul_eq_mul, hNa s, hNb s] at this
  rw [rA s, rP s]
  linear_combination this

end R2Alg

namespace R2

section Helpers
variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "Mat" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

theorem one_lt_absNorm : 1 < Ideal.absNorm p.asIdeal := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
  exact_mod_cast this

theorem v_eq_one_of_v_sub_one_le {a : F} {M : ℤ} (hM : 1 ≤ M) (h : Valued.v (a - 1) ≤ WithZero.exp (-M)) : Valued.v a = 1 := by
  have hlt : Valued.v (a - 1) < 1 := by
    refine lt_of_le_of_lt h ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have := Valuation.map_one_add_of_lt (Valued.v : Valuation F _) hlt
  rwa [add_sub_cancel] at this

theorem exists_uniformizer : ∃ ϖ : F, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer ℚ p
  exact ⟨((WithVal.equiv (HeightOneSpectrum.valuation ℚ p)).symm π : F),
    by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ⟩

theorem v_uniformizer_zpow {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (j : ℤ) : Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem isOpen_vball (m : ℤ) : IsOpen {x : F | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer p
  have hset : {x : F | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ m * x) ⁻¹' (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_uniformizer_zpow p hϖ, WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m := mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp m * ((WithZero.exp m)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp m * 1 := mul_le_mul_right h _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

theorem isLocallyConstant_of_higherUnitsAt (lam : (F)ˣ →* ℂˣ) (c : ℕ)
    (h : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p c, lam u = 1) : IsLocallyConstant lam := by
  set B : Set (F)ˣ := {u | Valued.v ((u : F) - 1) ≤ WithZero.exp (-((c + 1 : ℕ) : ℤ))} with hB
  have hBopen : IsOpen B :=
    (isOpen_vball p (-((c + 1 : ℕ) : ℤ))).preimage ((Units.continuous_val.sub continuous_const))
  have hBsub : B ⊆ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p c := by
    intro u hu
    refine ⟨v_eq_one_of_v_sub_one_le p (M := ((c + 1 : ℕ) : ℤ)) (by push_cast; omega) hu, ?_⟩
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exact Or.inl h0
    · right; exact hu.trans (WithZero.exp_le_exp.2 (by push_cast; omega))
  have h1B : (1 : (F)ˣ) ∈ B := by simp [hB]
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  have hcont : Continuous fun y : (F)ˣ => a⁻¹ * y := continuous_const.mul continuous_id
  have hmem : (fun y : (F)ˣ => a⁻¹ * y) ⁻¹' B ∈ 𝓝 a :=
    (hBopen.preimage hcont).mem_nhds (by simp [h1B])
  filter_upwards [hmem] with y hy
  have := h _ (hBsub hy)
  calc lam y = lam (a * (a⁻¹ * y)) := by rw [mul_inv_cancel_left]
    _ = lam a * lam (a⁻¹ * y) := map_mul _ _ _
    _ = lam a := by rw [this, mul_one]

def mulLeftHomeo (t : G2) : Mat ≃ₜ Mat where
  toFun X := ((t⁻¹ : G2) : Mat) * X
  invFun X := (t : Mat) * X
  left_inv X := by
    show (t : Mat) * (((t⁻¹ : G2) : Mat) * X) = X
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  right_inv X := by
    show ((t⁻¹ : G2) : Mat) * ((t : Mat) * X) = X
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem lc_translate (Φ : Mat → ℂ) (hΦ : IsLocallyConstant Φ) (t : G2) :
    IsLocallyConstant (fun X : Mat => Φ (((t⁻¹ : G2) : Mat) * X)) :=
  hΦ.comp_continuous (continuous_const.mul continuous_id)

theorem cs_translate (Φ : Mat → ℂ) (hΦc : HasCompactSupport Φ) (t : G2) :
    HasCompactSupport (fun X : Mat => Φ (((t⁻¹ : G2) : Mat) * X)) :=
  hΦc.comp_homeomorph (mulLeftHomeo p t)

theorem psi_level_zero :
    (∀ x : F, Valued.v x ≤ WithZero.exp (0 : ℤ) → NumberField.StandardAddChar.psiLocal ℚ p x = 1) ∧
      ∃ x : F, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ NumberField.StandardAddChar.psiLocal ℚ p x ≠ 1 := by
  have hk : ∃ k : ℤ, ∀ x : F, Valued.v x ≤ WithZero.exp k → NumberField.StandardAddChar.psiLocal ℚ p x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa using hx
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p
    (NumberField.StandardAddChar.psiLocal ℚ p) hk (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h

theorem lc_cs_matFourier22 (Φ : Mat → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    IsLocallyConstant (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) ∧
      HasCompactSupport (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) :=
  LanglandsTunnell.CubicInduction.isSchwartzBruhat_matFourier22 p _ 0 (psi_level_zero p).1 (psi_level_zero p).2 Φ ⟨hΦ, hΦc⟩

theorem le_sum_abs {ι : Type*} (S : Finset ι) (f : ι → ℝ) {t : ι} (ht : t ∈ S) : f t ≤ ∑ i ∈ S, |f i| :=
  (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |f i|) (fun _ _ => abs_nonneg _) ht)

end Helpers

end R2
end LanglandsTunnell.RankinSelberg

open Polynomial in

/-!            -/

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)

    (E₀ : ℂ) (e₀ : ℤ)
    (hfe : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))

    (χ₁ ω₁ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (ℓB : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] ℂ)
    (hℓB0 : ∃ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ℓB v ≠ 0)
    (hℓBN : ∀ (x : (p.adicCompletion ℚ)), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * unipotent x)) = ℓB v)
    (hℓBD : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * diagOne a)) = ((χ₁ a : ℂˣ) : ℂ) * ℓB v)
    (hℓBZ : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = ((ω₁ a : ℂˣ) : ℂ) * ℓB v)
    :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) →

            (∀ s : ℂ, σ₂ < s.re →
              godementZeta2 p μ₂ w Φ χ (s + 1 / 2) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w (transposeInvN (Fin 2) g) *
                  matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) →

            (∀ s : ℂ, σ₃ < s.re →
              godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g))
                  (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ (s + 3 / 2) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              ((1 : Polynomial ℂ)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                ((Polynomial.C E₀).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-e₀ : ℤ) : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI iGL : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI iBGL : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  intro μ₂ _ w hw Φ hΦ hΦc P Pd Q Qd m md σ₂ σ₃ hQ hQd hi hii hiii hiv
  classical

  set V : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) :=
    Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) with hV
  set Nn : ℕ := Ideal.absNorm p.asIdeal with hNn
  have hN1 : 1 < Nn := LanglandsTunnell.RankinSelberg.R2.one_lt_absNorm p

  have hJ : ∃ W ∈ V, W ∉ Submodule.span ℂ {D : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ W' ∈ V,
      ∃ t : p.adicCompletion ℚ, D = fun g : GL (Fin 2) (p.adicCompletion ℚ) => W' (g * unipotent t) - W' g} := by
    obtain ⟨v, hv, hv0⟩ := hℓB0
    refine ⟨v, hv, fun hmem => hv0 ?_⟩
    have hle : Submodule.span ℂ {D : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ W' ∈ V,
        ∃ t : p.adicCompletion ℚ, D = fun g : GL (Fin 2) (p.adicCompletion ℚ) => W' (g * unipotent t) - W' g} ≤ LinearMap.ker ℓB := by
      refine Submodule.span_le.2 ?_
      rintro D ⟨W', hW', t, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      have h1 := hℓBN t W' hW'
      have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => W' (g * unipotent t) - W' g) =
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => W' (g * unipotent t)) - W' := by funext g; rfl
      rw [this, map_sub, h1, sub_self]
    exact LinearMap.mem_ker.1 (hle hmem)
  obtain ⟨lam, cexp, Φe, hlamU, hΦeq, hΦinj, hΦPS⟩ :=
    LanglandsTunnell.CubicInduction.exists_linearMap_principalSeries2_of_jacquet_ne_top p N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hJ
  have hlam : ∀ i, IsLocallyConstant (lam i) := fun i =>
    LanglandsTunnell.RankinSelberg.R2.isLocallyConstant_of_higherUnitsAt p (lam i) (cexp i) (hlamU i)

  obtain ⟨Γn, Γd, eΓ, hΓn, hΓd, hA⟩ :=
    LanglandsTunnell.RankinSelberg.exists_gamma_forall_rational_godementZeta2_principalSeries2_and_clearedFE p lam hlam χ hχ

  have hK := LanglandsTunnell.RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_godementZeta2_section_and_dual_of_equivariant_embedding
    p N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm lam Φe hΦeq hΦinj hΦPS χ hχ μ₂

  obtain ⟨Φt, hΦt, hΦtc, S, hKS⟩ := hK w hw Φ hΦ hΦc
  obtain ⟨PA, PdA, QA, QdA, mA, mdA, τ₂, τ₃, hQA, hQdA, hAi, hAii, hAiii, hAiv, hAv⟩ :=
    hA μ₂ (Φe w) (hΦPS w hw) Φt hΦt hΦtc

  have hAt : ∀ t : GL (Fin 2) (p.adicCompletion ℚ), ∃ τ τ' : ℝ,
      (∀ s : ℂ, τ < s.re → Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        Φe w g * (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => Φ (((t⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X))
          (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) ∧
      (∀ s : ℂ, τ' < s.re → Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        Φe w (transposeInvN (Fin 2) g) *
          matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p)
            (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => Φ (((t⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X))
            (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) := by
    intro t
    obtain ⟨_, _, _, _, _, _, τ, τ', _, _, h1, _, h3, _, _⟩ := hA μ₂ (Φe w) (hΦPS w hw) _
      (LanglandsTunnell.RankinSelberg.R2.lc_translate p Φ hΦ t) (LanglandsTunnell.RankinSelberg.R2.cs_translate p Φ hΦc t)
    exact ⟨τ, τ', h1, h3⟩
  choose τf τf' hτf hτf' using hAt
  set ρ : ℝ := max σ₂ (max τ₂ (∑ t ∈ S, |τf t|)) with hρ
  set ρd : ℝ := max σ₃ (max τ₃ (∑ t ∈ S, |τf' t|)) with hρd

  have R1half : ∀ r : ℝ, r ∈ Set.Ioi ρ →
      (P * QA).eval ((Nn : ℂ) ^ (-(r : ℂ))) * (Nn : ℂ) ^ ((m : ℂ) * (r : ℂ)) =
        (PA * Q).eval ((Nn : ℂ) ^ (-(r : ℂ))) * (Nn : ℂ) ^ ((mA : ℂ) * (r : ℂ)) := by
    intro r hr
    have hr' : ρ < ((r : ℂ)).re := by simpa using hr
    have h2 : σ₂ < ((r : ℂ)).re := lt_of_le_of_lt (le_max_left _ _) hr'
    have hτ2 : τ₂ < ((r : ℂ)).re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hr'
    have hS : ∀ t ∈ S, τf t < ((r : ℂ)).re := fun t ht =>
      lt_of_le_of_lt ((LanglandsTunnell.RankinSelberg.R2.le_sum_abs S τf ht).trans ((le_max_right _ _).trans (le_max_right _ _))) hr'
    have hKeq := ((hKS ((r : ℂ) + 1 / 2)).1 (hi _ h2) (fun t ht => hτf t _ (hS t ht)))
    have e1 := hii _ h2
    have e2 := hAii _ hτ2
    rw [hKeq] at e1
    simp only [Polynomial.eval_mul, hNn]
    linear_combination (-(QA.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(r : ℂ))))) * e1 +
      (Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(r : ℂ)))) * e2
  have R1all := LanglandsTunnell.RankinSelberg.R2Alg.extend_identity Nn hN1 (Set.Ioi ρ) (Set.Ioi_infinite ρ) (P * QA) (PA * Q) m mA R1half
  have R1 : ∀ s : ℂ, (Nn : ℂ) ^ ((m : ℂ) * s) * P.eval ((Nn : ℂ) ^ (-s)) * QA.eval ((Nn : ℂ) ^ (-s)) =
      (Nn : ℂ) ^ ((mA : ℂ) * s) * PA.eval ((Nn : ℂ) ^ (-s)) * Q.eval ((Nn : ℂ) ^ (-s)) := by
    intro s; have := R1all s; simp only [Polynomial.eval_mul] at this; linear_combination this

  have R2half : ∀ r : ℝ, r ∈ Set.Ioi ρd →
      (Pd * QdA).eval ((Nn : ℂ) ^ (-(r : ℂ))) * (Nn : ℂ) ^ ((md : ℂ) * (r : ℂ)) =
        (PdA * Qd).eval ((Nn : ℂ) ^ (-(r : ℂ))) * (Nn : ℂ) ^ ((mdA : ℂ) * (r : ℂ)) := by
    intro r hr
    have hr' : ρd < ((r : ℂ)).re := by simpa using hr
    have h3 : σ₃ < ((r : ℂ)).re := lt_of_le_of_lt (le_max_left _ _) hr'
    have hτ3 : τ₃ < ((r : ℂ)).re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hr'
    have hS : ∀ t ∈ S, τf' t < ((r : ℂ)).re := fun t ht =>
      lt_of_le_of_lt ((LanglandsTunnell.RankinSelberg.R2.le_sum_abs S τf' ht).trans ((le_max_right _ _).trans (le_max_right _ _))) hr'
    have hKeq := ((hKS ((r : ℂ) + 3 / 2)).2 (hiii _ h3) (fun t ht => hτf' t _ (hS t ht)))
    have e1 := hiv _ h3
    have e2 := hAiv _ hτ3
    rw [hKeq] at e1
    simp only [Polynomial.eval_mul, hNn]
    linear_combination (-(QdA.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(r : ℂ))))) * e1 +
      (Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(r : ℂ)))) * e2
  have R2all := LanglandsTunnell.RankinSelberg.R2Alg.extend_identity Nn hN1 (Set.Ioi ρd) (Set.Ioi_infinite ρd) (Pd * QdA) (PdA * Qd) md mdA R2half
  have R2 : ∀ s : ℂ, (Nn : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Nn : ℂ) ^ (-s)) * QdA.eval ((Nn : ℂ) ^ (-s)) =
      (Nn : ℂ) ^ ((mdA : ℂ) * s) * PdA.eval ((Nn : ℂ) ^ (-s)) * Qd.eval ((Nn : ℂ) ^ (-s)) := by
    intro s; have := R2all s; simp only [Polynomial.eval_mul] at this; linear_combination this

  obtain ⟨c₁, -, hc₁, -, ⟨w₁, hw₁, hw₁z⟩, -⟩ :=
    LanglandsTunnell.RankinSelberg.exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible
      p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ χ hχ
  obtain ⟨P₁, Pd₁, m₁, md₁, σ₀₁, σ₁₁, h1i, h1ii, h1iii, h1iv, h1v⟩ := hfe w₁ hw₁
  have hP₁ : P₁ ≠ 0 := by
    intro h0
    have hs : σ₀₁ < (((σ₀₁ + 1 : ℝ)) : ℂ).re := by simp
    have := (hw₁z ((σ₀₁ + 1 : ℝ) : ℂ)).2
    rw [h1ii _ hs, h0, Polynomial.eval_zero, mul_zero] at this
    exact hc₁ this.symm
  obtain ⟨Φ₀, hΦ₀, hΦ₀c, C, hC, hLp, hLd⟩ :=
    LanglandsTunnell.RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable
      p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hcentral wJ hwJ χ hχ μ₂ w₁ hw₁
  obtain ⟨Φt₀, hΦt₀, hΦt₀c, S₀, hKS₀⟩ := hK w₁ hw₁ Φ₀ hΦ₀ hΦ₀c
  obtain ⟨PB, PdB, QB, QdB, mB, mdB, κ₂, κ₃, hQB, hQdB, hBi, hBii, hBiii, hBiv, hBv⟩ :=
    hA μ₂ (Φe w₁) (hΦPS w₁ hw₁) Φt₀ hΦt₀ hΦt₀c
  have hBt : ∀ t : GL (Fin 2) (p.adicCompletion ℚ), ∃ τ τ' : ℝ,
      (∀ s : ℂ, τ < s.re → Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        Φe w₁ g * (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => Φ₀ (((t⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X))
          (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) ∧
      (∀ s : ℂ, τ' < s.re → Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        Φe w₁ (transposeInvN (Fin 2) g) *
          matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p)
            (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => Φ₀ (((t⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X))
            (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) := by
    intro t
    obtain ⟨_, _, _, _, _, _, τ, τ', _, _, h1, _, h3, _, _⟩ := hA μ₂ (Φe w₁) (hΦPS w₁ hw₁) _
      (LanglandsTunnell.RankinSelberg.R2.lc_translate p Φ₀ hΦ₀ t) (LanglandsTunnell.RankinSelberg.R2.cs_translate p Φ₀ hΦ₀c t)
    exact ⟨τ, τ', h1, h3⟩
  choose τg τg' hτg hτg' using hBt

  obtain ⟨hΨlc, hΨcs⟩ := LanglandsTunnell.RankinSelberg.R2.lc_cs_matFourier22 p Φ₀ hΦ₀ hΦ₀c
  obtain ⟨σcd, hcd⟩ :=
    LanglandsTunnell.RankinSelberg.forall_exists_integrable_godementZeta2_whittaker_transposeInvN_shift
      p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral χ hχ μ₂ w₁ hw₁ _ hΨlc hΨcs (3 / 2)
  set ρ₀ : ℝ := max σ₀₁ (max κ₂ (∑ t ∈ S₀, |τg t|)) with hρ₀
  set ρ₀' : ℝ := max σcd (max κ₃ (∑ t ∈ S₀, |τg' t|)) with hρ₀'

  set Z : ℂ → ℂ := fun s => ∫ y : (p.adicCompletion ℚ)ˣ,
      w₁ (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) with hZ
  set Zd : ℂ → ℂ := fun s => ∫ y : (p.adicCompletion ℚ)ˣ,
      w₁ (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
        ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) with hZd
  have gZ' : ∀ s : ℂ, ρ₀ < s.re → C * Z s * QB.eval ((Nn : ℂ) ^ (-s)) = (Nn : ℂ) ^ ((mB : ℂ) * s) * PB.eval ((Nn : ℂ) ^ (-s)) := by
    intro s hs
    have h0 : σ₀₁ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hκ : κ₂ < s.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
    have hS : ∀ t ∈ S₀, τg t < s.re := fun t ht =>
      lt_of_le_of_lt ((LanglandsTunnell.RankinSelberg.R2.le_sum_abs S₀ τg ht).trans ((le_max_right _ _).trans (le_max_right _ _))) hs
    obtain ⟨hIgj, hZeq⟩ := hLp s (h1i s h0)
    have hKeq := (hKS₀ (s + 1 / 2)).1 hIgj (fun t ht => hτg t _ (hS t ht))
    have e2 := hBii s hκ
    rw [← hKeq, hZeq] at e2
    simp only [hZ, hNn]
    linear_combination e2
  have gZd' : ∀ s : ℂ, s.re < -ρ₀' → C * Zd s * QdB.eval ((Nn : ℂ) ^ s) = (Nn : ℂ) ^ ((mdB : ℂ) * (-s)) * PdB.eval ((Nn : ℂ) ^ s) := by
    intro s hs
    have ht : ρ₀' < (-s).re := by rw [Complex.neg_re]; linarith
    have hcd' : σcd < (-s).re := lt_of_le_of_lt (le_max_left _ _) ht
    have hκ : κ₃ < (-s).re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) ht
    have hS : ∀ t ∈ S₀, τg' t < (-s).re := fun t ht' =>
      lt_of_le_of_lt ((LanglandsTunnell.RankinSelberg.R2.le_sum_abs S₀ τg' ht').trans ((le_max_right _ _).trans (le_max_right _ _))) ht
    have hIgj := hcd (-s) hcd'
    obtain ⟨-, hZeq⟩ := hLd (-s) hIgj
    have hKeq := (hKS₀ ((-s) + 3 / 2)).2 hIgj (fun t ht' => hτg' t _ (hS t ht'))
    have e2 := hBiv (-s) hκ
    rw [← hKeq, hZeq] at e2
    simp only [neg_neg] at e2
    have hexp : (fun y : (p.adicCompletion ℚ)ˣ => w₁ (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
        ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 + -s)) =
        fun y : (p.adicCompletion ℚ)ˣ => w₁ (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
        ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) := by
      funext y; rw [← sub_eq_add_neg]
    rw [hexp] at e2
    simp only [hZd, hNn]
    linear_combination e2
  have hpin := LanglandsTunnell.RankinSelberg.R2Alg.gamma_pin Nn hN1 Z Zd E₀ e₀ P₁ Pd₁ m₁ md₁ σ₀₁ σ₁₁
    (fun s hs => by simp only [hZ, hNn]; exact h1ii s hs) (fun s hs => by simp only [hZd, hNn]; exact h1iv s hs)
    (fun s => by simp only [hNn]; exact h1v s) hP₁
    C hC PB PdB QB QdB Γn Γd mB mdB eΓ ρ₀ (-ρ₀') hQB hQdB gZ' gZd' (fun s => by simp only [hNn]; exact hBv s)

  have hvE := LanglandsTunnell.RankinSelberg.R2Alg.fe_monomial_of_gamma_pin Nn hN1 E₀ e₀ PA PdA QA QdA Γn Γd mA mdA eΓ hΓd hpin
    (fun s => by simp only [hNn]; exact hAv s)
  have hfin := LanglandsTunnell.RankinSelberg.R2Alg.transport Nn hN1 P Pd Q Qd PA PdA QA QdA m md mA mdA E₀ (-e₀) hQA hQdA
    R1 R2 (fun s => by have := hvE s; push_cast at this ⊢; linear_combination this)
  intro s
  have := hfin s
  simp only [hNn] at this
  simp only [Polynomial.eval_one, Polynomial.eval_C, one_mul]
  push_cast at this ⊢
  linear_combination this

end

end S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional (solution)
