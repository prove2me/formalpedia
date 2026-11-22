-- Prove2me | solution 1 for MasulloGRH.heckeLFunction_boundary_order_nonpositive_small
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T20:01:30.340944+00:00
-- url     : https://prove2.me/submissions/930dcab1-3250-4377-b43f-69e98905ed69

import Definitions.Def_MasulloGRH_HeckeLFunction
import Definitions.Def_MusicOfPrimes_HeckeL
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_sub_mul_eulerProduct_and_eq_mul_prod_Gamma_mul_of_eq_normPowChar
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RestrictedProduct Filter Set
open scoped Topology

open NumberField IsDedekindDomain NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open scoped Classical

private theorem phase_single_eq {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    MasulloGRH.ideleSingle v x = Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v x) := by
  classical
  apply Units.ext
  refine Prod.ext ?_ ?_
  · rfl
  refine Subtype.ext (funext fun w => ?_)
  change ((RestrictedProduct.mulSingle
    (fun v : HeightOneSpectrum (𝓞 K) => (Submonoid.ofClass (v.adicCompletionIntegers K)).units)
      v x w : (w.adicCompletion K)ˣ) : w.adicCompletion K) =
    ((localUnit (𝓞 K) K v x : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w
  by_cases h : w = v
  · subst w
    rw [RestrictedProduct.mulSingle_eq_same, localUnit_apply_self]
  · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ h, localUnit_apply_of_ne _ _ _ _ h]
    rfl

private noncomputable def phase_tate_lift {K : Type} [Field K] [NumberField K]
    (χ : MasulloGRH.HeckeCharacter K) : MusicOfPrimes.HeckeChar K where
  toFun := Circle.toUnits.comp (χ.toMonoidHom.comp (QuotientGroup.mk' (MasulloGRH.principalIdeles K)))
  cont := continuous_subtype_val.comp (χ.continuous.comp QuotientGroup.continuous_mk)
  unitary := fun x => Circle.norm_coe _
  classChar := by
    intro u
    change Circle.toUnits (χ (QuotientGroup.mk (MasulloGRH.principalIdele K u))) = 1
    have hm : MasulloGRH.principalIdele K u ∈ MasulloGRH.principalIdeles K := ⟨u,rfl⟩
    rw [(QuotientGroup.eq_one_iff _).mpr hm, map_one, map_one]

private theorem phase_local_eq {K : Type} [Field K] [NumberField K]
    (χ : MasulloGRH.HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    χ.localComponent v x = ((localChar (phase_tate_lift χ).toFun v x : ℂˣ) : ℂ) := by
  unfold MasulloGRH.HeckeCharacter.localComponent
  rw [phase_single_eq]
  rfl

private theorem phase_unram_iff {K : Type} [Field K] [NumberField K]
    (χ : MasulloGRH.HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    χ.IsUnramifiedAt v ↔ IsUnramifiedCharAt (phase_tate_lift χ).toFun v := by
  constructor
  · intro hu x hx hx'
    apply Units.ext
    rw [← phase_local_eq]
    apply hu x
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx hx'
    rw [Units.val_inv_eq_inv_val, map_inv₀] at hx'
    exact le_antisymm hx ((inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr x.ne_zero))).mp hx')
  · intro hu x hx
    have hx1 : (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hx]
    have hx2 : ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
    rw [phase_local_eq, hu x hx1 hx2]
    rfl

private theorem phase_prime_eq {K : Type} [Field K] [NumberField K]
    (χ : MasulloGRH.HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    χ.primeValue v = if IsUnramifiedCharAt (phase_tate_lift χ).toFun v then
      (((phase_tate_lift χ).toFun (uniformizerIdele K v) : ℂˣ) : ℂ) else 0 := by
  classical
  unfold MasulloGRH.HeckeCharacter.primeValue
  by_cases hu : χ.IsUnramifiedAt v
  · have hv : ∃ x : (v.adicCompletion K)ˣ, MasulloGRH.IsUniformizerAt v x :=
      ⟨uniformizerUnit K v, valued_uniformizerUnit K v⟩
    rw [dif_pos ⟨hu,hv⟩, if_pos ((phase_unram_iff χ v).mp hu)]
    let z := hv.choose
    have hz : MasulloGRH.IsUniformizerAt v z := hv.choose_spec
    let t := uniformizerUnit K v
    have ht := valued_uniformizerUnit K v
    have hunit : Valued.v ((z/t : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
      change Valued.v (((z : v.adicCompletion K) / (t : v.adicCompletion K))) = 1
      rw [map_div₀, show Valued.v (z : v.adicCompletion K) = WithZero.exp (-1 : ℤ) from hz,
        show Valued.v (t : v.adicCompletion K) = WithZero.exp (-1 : ℤ) from ht,
        div_self WithZero.exp_ne_zero]
    have he := hu (z/t) hunit
    rw [phase_local_eq] at he
    have heu : localChar (phase_tate_lift χ).toFun v (z/t) = 1 := Units.ext he
    rw [map_div, div_eq_one] at heu
    exact (phase_local_eq χ v z).trans (congrArg Units.val heu)
  · rw [dif_neg (fun h => hu h.1), if_neg (fun h => hu ((phase_unram_iff χ v).mpr h))]

private theorem phase_same_field {K : Type} [Field K] [NumberField K]
    (χ : MasulloGRH.HeckeCharacter K) :
    ∃ η : MusicOfPrimes.HeckeChar K, ∀ v, χ.primeValue v = if IsUnramifiedCharAt η.toFun v
      then ((η.toFun (uniformizerIdele K v) : ℂˣ) : ℂ) else 0 :=
  ⟨phase_tate_lift χ, phase_prime_eq χ⟩

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

theorem solution (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F) (t : ℝ) :
    meromorphicOrderAt (heckeLFunction χ) (1 + (t : ℂ) * Complex.I) ≤ 0 := by
  classical
  obtain ⟨η, hη⟩ := phase_same_field χ
  have heq (w : ℂ) : MasulloGRH.heckeEulerProduct χ w = MusicOfPrimes.heckeEulerProduct F η w := by
    unfold MasulloGRH.heckeEulerProduct MusicOfPrimes.heckeEulerProduct
    simp_rw [hη]
  obtain ⟨g, Q, hg, hQ, hQz, hmatch⟩ := angular_tate_small F η t
  have hc := heckeLFunction_exists_meromorphic_continuation F χ
  have hspec : MeromorphicNFOn (heckeLFunction χ) Set.univ ∧
      ∀ w : ℂ, 1 < w.re → heckeLFunction χ w = MasulloGRH.heckeEulerProduct χ w := by
    unfold heckeLFunction
    rw [dif_pos hc]
    exact hc.choose_spec
  apply angular_boundary_order (heckeLFunction χ) g Q _ (by simp) (hspec.1 (Set.mem_univ _)) hg hQ hQz
  intro w hw
  rw [hspec.2 w hw, heq w]
  exact hmatch w hw
