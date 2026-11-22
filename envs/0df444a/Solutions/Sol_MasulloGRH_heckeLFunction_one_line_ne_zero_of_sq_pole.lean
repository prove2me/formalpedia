-- Prove2me | solution 1 for MasulloGRH.heckeLFunction_one_line_ne_zero_of_sq_pole
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T19:58:32.904175+00:00
-- url     : https://prove2.me/submissions/e0fdb4ef-dbd9-44cd-8046-03dffb09037f

import Definitions.Def_MasulloGRH_HeckeLFunction
import Definitions.Def_MusicOfPrimes_HeckeL
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Data.Countable.Small
import Mathlib.Data.Rat.Encodable
import Mathlib.LinearAlgebra.Countable
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Theorems.Thm_MasulloGRH_exists_tate_hecke_character_preserving_local_prime_values
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_sub_mul_eulerProduct_and_eq_mul_prod_Gamma_mul_of_eq_normPowChar
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq

open Filter Set
open scoped Topology

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open scoped Classical
private theorem small_number_field_model (F : Type*) [Field F] [NumberField F] :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), Nonempty (F ≃+* K) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  let e := (equivShrink.{0} F).symm
  letI : Field (Shrink.{0} F) := e.field
  let r : Shrink.{0} F ≃+* F := e.ringEquiv
  letI : NumberField (Shrink.{0} F) := NumberField.of_ringEquiv F _ r.symm
  exact ⟨Shrink.{0} F, inferInstance, inferInstance, ⟨r.symm⟩⟩

private theorem angular_tate_primes_norm
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm v.asIdeal =
      Ideal.absNorm ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv r) v).asIdeal) := by
  let R := RingOfIntegers.mapRingEquiv r
  change Nat.card (𝓞 F ⧸ v.asIdeal) =
      Nat.card (𝓞 K ⧸ v.asIdeal.comap (R.symm : 𝓞 K →+* 𝓞 F))
  exact Nat.card_congr (Ideal.quotientEquiv _ _ R (Ideal.comap_symm R)).toEquiv

private theorem exists_small_tate_hecke_character_preserving_prime_factors
    (F : Type*) [Field F] [NumberField F] (χ : MasulloGRH.HeckeCharacter F) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (η : MusicOfPrimes.HeckeChar K)
      (e : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 K)),
      (∀ v, Ideal.absNorm v.asIdeal = Ideal.absNorm (e v).asIdeal) ∧
      (∀ v, χ.primeValue v =
        if IsUnramifiedCharAt η.toFun (e v) then
          ((η.toFun (uniformizerIdele K (e v)) : ℂˣ) : ℂ) else 0) := by
  obtain ⟨K, hF, hN, ⟨r⟩⟩ := small_number_field_model F
  obtain ⟨η, hη⟩ :=
    MasulloGRH.exists_tate_hecke_character_preserving_local_prime_values F K r χ
  exact ⟨K, hF, hN, η, HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv r),
    angular_tate_primes_norm r, hη⟩

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open scoped Classical
private theorem angular_tate_reindex
    {F : Type*} [Field F] [NumberField F] (χ : MasulloGRH.HeckeCharacter F)
    {K : Type} [Field K] [NumberField K] (η : MusicOfPrimes.HeckeChar K)
    (e : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 K))
    (hn : ∀ v, Ideal.absNorm v.asIdeal = Ideal.absNorm (e v).asIdeal)
    (hz : ∀ v, χ.primeValue v =
      if IsUnramifiedCharAt η.toFun (e v) then
        ((η.toFun (uniformizerIdele K (e v)) : ℂˣ) : ℂ) else 0)
    (s : ℂ) :
    MasulloGRH.heckeEulerProduct χ s = MusicOfPrimes.heckeEulerProduct K η s := by
  classical
  unfold MasulloGRH.heckeEulerProduct MusicOfPrimes.heckeEulerProduct
  simpa only [hz, hn] using
    (e.tprod_eq (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - (if IsUnramifiedCharAt η.toFun v then
        ((η.toFun (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹))


open scoped Classical BigOperators
open NumberField IsDedekindDomain NumberField.TateGlobal AutomorphicForm Complex

private theorem angular_tate_small (K : Type) [Field K] [NumberField K]
    (η : MusicOfPrimes.HeckeChar K) (t : ℝ) :
    ∃ g Q : ℂ → ℂ, ContinuousAt g (1 + (t : ℂ) * I) ∧
      ContinuousAt Q (1 + (t : ℂ) * I) ∧ Q (1 + (t : ℂ) * I) ≠ 0 ∧
      ∀ w : ℂ, 1 < w.re → Q w = g w * MusicOfPrimes.heckeEulerProduct K η w := by
  classical
  have hcont : Continuous η.toFun := by
    refine Units.continuous_iff.2 ⟨η.cont, ?_⟩
    simpa only [Function.comp_def, map_inv] using η.cont.comp continuous_inv
  obtain ⟨S, hS⟩ := exists_finset_forall_isUnramifiedCharAt_of_continuous K η.toFun hcont
  obtain ⟨c, C, A, hc, _, H⟩ :=
    exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq
      K S (localChar η.toFun)
  obtain ⟨hN, hP⟩ := H η.toFun η.cont η.unitary η.classChar hS
    (fun _ _ _ _ _ => rfl)
  by_cases hp : MusicOfPrimes.IsNormPowChar K η
  · obtain ⟨a, ha⟩ := hp
    obtain ⟨Q, _, hQ, _, hmatch, _⟩ :=
      exists_differentiable_eq_sub_mul_eulerProduct_and_eq_mul_prod_Gamma_mul_of_eq_normPowChar
        K η.toFun η.cont η.unitary η.classChar (MusicOfPrimes.archτ K η)
          (MusicOfPrimes.archm K η) (MusicOfPrimes.archτ_spec K η)
          (MusicOfPrimes.archm_spec K η) a ha
    have hlog : 0 ≤ Real.log (2 + |t + a|) :=
      Real.log_nonneg (by linarith [abs_nonneg (t + a)])
    have hne := (hP a ha Q hQ hmatch t 1 (sub_le_self _ (div_nonneg hc.le hlog))
      (by norm_num)).1
    refine ⟨fun w => w - (1 - (a : ℂ) * I), Q, continuousAt_id.sub continuousAt_const,
      hQ.continuous.continuousAt, ?_, hmatch⟩
    simpa only [Complex.ofReal_one] using hne
  · let L := MusicOfPrimes.heckeLFinNe K η hp
    have hL := MusicOfPrimes.heckeLFinNe_spec K η hp
    have hsum : 0 ≤ ∑ v : InfinitePlace K,
        (|MusicOfPrimes.archτ K η v| + (|MusicOfPrimes.archm K η v| : ℝ)) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hlog : 0 ≤ Real.log (2 + |t| + ∑ v : InfinitePlace K,
        (|MusicOfPrimes.archτ K η v| + (|MusicOfPrimes.archm K η v| : ℝ))) :=
      Real.log_nonneg (by linarith [abs_nonneg t])
    have hne := (hN (MusicOfPrimes.archτ K η) (MusicOfPrimes.archm K η)
      (MusicOfPrimes.archτ_spec K η) (MusicOfPrimes.archm_spec K η)
      (fun a ha => hp ⟨a, ha⟩) L hL.1 hL.2 t 1
      (sub_le_self _ (div_nonneg hc.le hlog)) (by norm_num)).1
    refine ⟨fun _ => 1, L, continuousAt_const, hL.1.continuous.continuousAt, ?_, ?_⟩
    · simpa only [Complex.ofReal_one] using hne
    · intro w hw
      simpa only [one_mul] using hL.2 w hw

private theorem angular_boundary_order (f g Q : ℂ → ℂ) (z : ℂ) (hz : z.re = 1)
    (hf : MeromorphicNFAt f z) (hg : ContinuousAt g z) (hQ : ContinuousAt Q z)
    (hQz : Q z ≠ 0) (hmatch : ∀ w : ℂ, 1 < w.re → Q w = g w * f w) :
    meromorphicOrderAt f z ≤ 0 := by
  by_contra! hp
  have hfc : ContinuousAt f z :=
    (hf.meromorphicOrderAt_nonneg_iff_analyticAt.1 hp.le).continuousAt
  have hfz : f z = 0 := by
    by_contra hn
    exact hp.ne' (hf.meromorphicOrderAt_eq_zero_iff.2 hn)
  have hzcl : z ∈ closure {w : ℂ | 1 < w.re} := by
    rw [Complex.closure_setOfPred_lt_re]
    exact hz.ge
  have he : Q z = g z * f z :=
    tendsto_nhds_unique_of_frequently_eq hQ (hg.mul hfc)
      ((mem_closure_iff_frequently.1 hzcl).mono (fun w hw => hmatch w hw))
  exact hQz (by simpa [hfz] using he)

open MasulloGRH

theorem solution (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (t : ℝ)
    (_hpole : meromorphicOrderAt (heckeLFunction (χ * χ)) (1 + ((2 * t : ℝ) : ℂ) * Complex.I) < 0) :
    meromorphicOrderAt (heckeLFunction χ) (1 + (t : ℂ) * Complex.I) ≤ 0 := by
  classical
  obtain ⟨K, kField, kNumber, η, e, hn, hz⟩ :=
    exists_small_tate_hecke_character_preserving_prime_factors F χ
  obtain ⟨g, Q, hg, hQ, hQz, hmatch⟩ := angular_tate_small K η t
  have hc := heckeLFunction_exists_meromorphic_continuation F χ
  have hspec : MeromorphicNFOn (heckeLFunction χ) Set.univ ∧
      ∀ w : ℂ, 1 < w.re → heckeLFunction χ w = MasulloGRH.heckeEulerProduct χ w := by
    unfold heckeLFunction
    rw [dif_pos hc]
    exact hc.choose_spec
  apply angular_boundary_order (heckeLFunction χ) g Q _ (by simp) (hspec.1 (Set.mem_univ _))
    hg hQ hQz
  intro w hw
  rw [hspec.2 w hw, angular_tate_reindex χ η e hn hz w]
  exact hmatch w hw

