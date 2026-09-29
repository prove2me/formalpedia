-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e6674ecc-2008-52e8-80f0-53871b4780f5

import Mathlib
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_finset_forall_rsLocalIntegral_eq_sum_mul_setIntegral_of_forall_setIntegral_torusShell_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal Topology

namespace KcFlatSpecialise

noncomputable section

section Generic

theorem isLocallyConstant_of_mul_invariant {M X : Type*} [TopologicalSpace M] [Group M] [ContinuousMul M]
    (U : Set M) (hU : IsOpen U) (h1 : (1 : M) ∈ U) (f : M → X) (hf : ∀ x, ∀ h ∈ U, f (x * h) = f x) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen ((fun h => x * h) '' U) := isOpenMap_mul_left x U hU
  have hmem : x ∈ (fun h => x * h) '' U := ⟨1, h1, mul_one x⟩
  filter_upwards [hopen.mem_nhds hmem] with y hy
  obtain ⟨h, hh, rfl⟩ := hy
  exact hf x h hh

theorem continuous_of_rightInvariant {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] {U : Subgroup G}
    (hU : IsOpen (U : Set G)) {f : G → X} (hf : ∀ k ∈ U, ∀ g : G, f (g * k) = f g) : Continuous f :=
  (isLocallyConstant_of_mul_invariant (U : Set G) hU U.one_mem f fun x h hh => hf h hh x).continuous

theorem eq_of_differentiable_of_eqOn_re {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (σ : ℝ) (h : ∀ z : ℂ, σ < z.re → f z = g z) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hga : AnalyticOnNhd ℂ g Set.univ := hg.differentiableOn.analyticOnNhd isOpen_univ
  have hopen : IsOpen {z : ℂ | σ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz₀ : ((σ + 1 : ℝ) : ℂ) ∈ {z : ℂ | σ < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith
  have hev : f =ᶠ[𝓝 ((σ + 1 : ℝ) : ℂ)] g := by
    filter_upwards [hopen.mem_nhds hz₀] with z hz
    exact h z hz
  exact hfa.eq_of_eventuallyEq hga hev

end Generic

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => (HeightOneSpectrum.adicCompletion K v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers K v)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_localGL : SecondCountableTopology G₂ :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G₂ := locallyCompactSpace_localGL K v

abbrev kzero : Subgroup G₂ := AdelicDock.localLevelOne (𝓞 K) K v ⊤

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ (O)) :
    AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_iff (k : G₂) :
    k ∈ kzero K v ↔ (∀ i j, (k : Mat) i j ∈ (O)) ∧ ∀ i j, ((k⁻¹ : G₂) : Mat) i j ∈ (O) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral K v h1, isLocalLevelOne_top_of_integral K v h2⟩

theorem coe_kzero_eq_localIntegralSet :
    ((kzero K v : Subgroup G₂) : Set G₂) = localIntegralSet K v := by
  ext k
  rw [SetLike.mem_coe, mem_kzero_iff, mem_localIntegralSet]

theorem isOpen_kzero : IsOpen ((kzero K v : Subgroup G₂) : Set G₂) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isOpen_localIntegralSet K v

theorem isCompact_kzero : IsCompact ((kzero K v : Subgroup G₂) : Set G₂) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isCompact_localIntegralSet K v

abbrev qC : ℂ := (Ideal.absNorm v.asIdeal : ℂ)

theorem qC_ne_zero : qC K v ≠ 0 := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)

section Family

variable {K v}
variable (Kb : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)))
  (A : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ)
  (E : ℤ → GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ)
  (hEK : ∀ i : ℤ, ∀ k ∈ Kb, ∀ g : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v), E i (g * k) = E i g)
  (hAE : ∀ (i : ℤ) (x : HeightOneSpectrum.adicCompletion K v) (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)),
    A (unipotent x * g) * E i (unipotent x * g) = A g * E i g)
  (hEfin : ∀ C : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)), IsCompact C →
    {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite)
  (cf : ℤ → ℂ) (B : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ)
  (hB : ∀ g : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v), B g = ∑ᶠ i : ℤ, cf i * E i g)

include hEfin in

theorem support_finite (g : G₂) : (Function.support fun i : ℤ => cf i * E i g).Finite := by
  refine (hEfin {g} isCompact_singleton).subset ?_
  intro i hi
  rw [Function.mem_support] at hi
  exact ⟨g, rfl, right_ne_zero_of_mul hi⟩

include hEK hB in

theorem B_mul_right : ∀ k ∈ Kb, ∀ g : G₂, B (g * k) = B g := by
  intro k hk g
  rw [hB, hB]
  exact finsum_congr fun i => by rw [hEK i k hk g]

include hAE hEfin hB in

theorem AB_unipotent (x : F) (g : G₂) : A (unipotent x * g) * B (unipotent x * g) = A g * B g := by
  rw [hB, hB, mul_finsum' _ _ (support_finite E hEfin cf _), mul_finsum' _ _ (support_finite E hEfin cf _)]
  refine finsum_congr fun i => ?_
  rw [mul_left_comm, hAE i x g, mul_left_comm]

include hEK hB in
theorem continuous_B (hKb : IsOpen (Kb : Set G₂)) : Continuous B :=
  continuous_of_rightInvariant hKb (B_mul_right Kb E hEK cf B hB)

include hEK in
theorem continuous_E (hKb : IsOpen (Kb : Set G₂)) (i : ℤ) : Continuous (E i) :=
  continuous_of_rightInvariant hKb (hEK i)

include hB in

theorem B_eq_sum (C : Set G₂) (I : Finset ℤ) (hI : ∀ g ∈ C, ∀ i : ℤ, E i g ≠ 0 → i ∈ I) (g : G₂) (hg : g ∈ C) :
    B g = ∑ i ∈ I, cf i * E i g := by
  rw [hB]
  refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
  rw [Function.mem_support] at hi
  exact hI g hg i (right_ne_zero_of_mul hi)

include hEK hB in

theorem setIntegral_shell_eq_sum (hKb : IsOpen (Kb : Set G₂)) (hAc : Continuous A)
    (μ₂ : Measure G₂) [IsFiniteMeasureOnCompacts μ₂] (a : G₂) (I : Finset ℤ)
    (hI : ∀ k ∈ (kzero K v : Set G₂), ∀ i : ℤ, E i (a * k) ≠ 0 → i ∈ I) :
    ∫ k in (kzero K v : Set G₂), A (a * k) * B (a * k) ∂μ₂ =
      ∑ i ∈ I, cf i * ∫ k in (kzero K v : Set G₂), A (a * k) * E i (a * k) ∂μ₂ := by
  have hpt : ∀ k ∈ (kzero K v : Set G₂), A (a * k) * B (a * k) = ∑ i ∈ I, cf i * (A (a * k) * E i (a * k)) := by
    intro k hk
    rw [B_eq_sum E cf B hB ((a * ·) '' (kzero K v : Set G₂)) I ?_ (a * k) ⟨k, hk, rfl⟩, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun i _ => by ring
    · rintro g ⟨k', hk', rfl⟩ i hi
      exact hI k' hk' i hi
  rw [setIntegral_congr_fun (isOpen_kzero K v).measurableSet hpt, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_const_mul _ _
  · intro i _
    refine Integrable.const_mul ?_ _
    exact (((hAc.comp (continuous_const.mul continuous_id)).mul
      ((continuous_E Kb E hEK hKb i).comp (continuous_const.mul continuous_id))).continuousOn.integrableOn_compact
        (isCompact_kzero K v))

end Family

section Explicit

def Lfun (T : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (I : Finset ℤ) (M : ℤ × ℤ → ℤ → ℂ) (cf : ℤ → ℂ) (s : ℂ) : ℂ :=
  ∑ dn ∈ T, ∑ i ∈ I, c dn * (qC K v) ^ (-((dn.1 + 2 * dn.2 : ℤ) : ℂ) * s) * (cf i * M dn i)

def cfu (u : ℂ) (i : ℤ) : ℂ := (qC K v) ^ (-(i : ℂ) * u)

theorem cfu_zero : cfu K v 0 = fun _ => 1 := by
  funext i
  simp [cfu]

theorem differentiable_qC_cpow_mul (a : ℂ) : Differentiable ℂ fun z : ℂ => (qC K v) ^ (a * z) :=
  (differentiable_id.const_mul a).const_cpow (Or.inl (qC_ne_zero K v))

theorem differentiable_Lfun_s (T : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (I : Finset ℤ) (M : ℤ × ℤ → ℤ → ℂ)
    (cf : ℤ → ℂ) : Differentiable ℂ fun s => Lfun K v T c I M cf s := by
  unfold Lfun
  refine Differentiable.fun_sum fun dn _ => Differentiable.fun_sum fun i _ => ?_
  exact ((differentiable_qC_cpow_mul K v _).const_mul _).mul_const _

theorem differentiable_Lfun_u (T : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (I : Finset ℤ) (M : ℤ × ℤ → ℤ → ℂ)
    (s : ℂ) : Differentiable ℂ fun u => Lfun K v T c I M (cfu K v u) s := by
  unfold Lfun cfu
  refine Differentiable.fun_sum fun dn _ => Differentiable.fun_sum fun i _ => ?_
  exact ((differentiable_qC_cpow_mul K v _).mul_const _).const_mul _

theorem differentiable_laurent (m : ℤ) (P : Polynomial ℂ) :
    Differentiable ℂ fun s : ℂ => (qC K v) ^ ((m : ℂ) * s) * P.eval ((qC K v) ^ (-s)) := by
  refine (differentiable_qC_cpow_mul K v _).mul ?_
  have h1 : Differentiable ℂ fun s : ℂ => (qC K v) ^ (-s) :=
    differentiable_id.neg.const_cpow (Or.inl (qC_ne_zero K v))
  exact P.differentiable.comp h1

def eExp (dn : ℤ × ℤ) : ℤ := dn.1 + 2 * dn.2

def mShift (T : Finset (ℤ × ℤ)) : ℤ := ∑ dn ∈ T, |eExp dn|

theorem mShift_add_nonneg (T : Finset (ℤ × ℤ)) {dn : ℤ × ℤ} (hdn : dn ∈ T) : 0 ≤ mShift T + eExp dn := by
  have h1 : |eExp dn| ≤ mShift T :=
    Finset.single_le_sum (f := fun dn => |eExp dn|) (fun _ _ => abs_nonneg _) hdn
  have h2 : -eExp dn ≤ |eExp dn| := neg_le_abs _
  omega

def poly (κ : ℤ × ℤ → ℂ) (T : Finset (ℤ × ℤ)) : Polynomial ℂ :=
  ∑ dn ∈ T, Polynomial.C (κ dn) * Polynomial.X ^ (mShift T + eExp dn).toNat

theorem poly_term_eq (κ : ℤ × ℤ → ℂ) (T : Finset (ℤ × ℤ)) (s : ℂ) {dn : ℤ × ℤ} (hdn : dn ∈ T) :
    (qC K v) ^ ((mShift T : ℂ) * s) * (κ dn * ((qC K v) ^ (-s)) ^ (mShift T + eExp dn).toNat) =
      κ dn * (qC K v) ^ (-((eExp dn : ℤ) : ℂ) * s) := by
  have hN : (((mShift T + eExp dn).toNat : ℕ) : ℂ) = ((mShift T : ℤ) : ℂ) + ((eExp dn : ℤ) : ℂ) := by
    have := Int.toNat_of_nonneg (mShift_add_nonneg T hdn)
    exact_mod_cast this
  rw [← Complex.cpow_nat_mul, hN, mul_left_comm, ← Complex.cpow_add _ _ (qC_ne_zero K v)]
  congr 2
  ring

theorem laurent_eval_eq_sum (κ : ℤ × ℤ → ℂ) (T : Finset (ℤ × ℤ)) (s : ℂ) :
    (qC K v) ^ ((mShift T : ℂ) * s) * (poly κ T).eval ((qC K v) ^ (-s)) =
      ∑ dn ∈ T, κ dn * (qC K v) ^ (-((dn.1 + 2 * dn.2 : ℤ) : ℂ) * s) := by
  rw [poly, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun dn hdn => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact poly_term_eq K v κ T s hdn

theorem Lfun_one_eq (T : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (I : Finset ℤ) (M : ℤ × ℤ → ℤ → ℂ) (s : ℂ) :
    Lfun K v T c I M (fun _ => 1) s =
      ∑ dn ∈ T, (c dn * ∑ i ∈ I, M dn i) * (qC K v) ^ (-((dn.1 + 2 * dn.2 : ℤ) : ℂ) * s) := by
  unfold Lfun
  refine Finset.sum_congr rfl fun dn _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => by ring

end Explicit

end

end KcFlatSpecialise
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell.KcFlatSpecialise"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

open KcFlatSpecialise in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ)

    (Kb₁ Kb₂ : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hKb₁ : IsOpen (Kb₁ : Set (GL (Fin 2) (v.adicCompletion K))))
    (hKb₁K : Kb₁ ≤ AdelicDock.localLevelOne (𝓞 K) K v ⊤)
    (hKb₁c : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
        - 1) i j) ≤ WithZero.exp (-(b : ℤ))) → k ∈ Kb₁)
    (hKb₂ : IsOpen (Kb₂ : Set (GL (Fin 2) (v.adicCompletion K))))
    (hKb₂K : Kb₂ ≤ AdelicDock.localLevelOne (𝓞 K) K v ⊤)
    (hKb₂c : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
        - 1) i j) ≤ WithZero.exp (-(b : ℤ))) → k ∈ Kb₂)

    (A₁ A₂ : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hA₁ : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion K)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (v.adicCompletion K), A₁ (g * k) = A₁ g)
    (hA₂ : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion K)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (v.adicCompletion K), A₂ (g * k) = A₂ g)

    (E₁ E₂ : ℤ → GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hE₁K : ∀ i : ℤ, ∀ k ∈ Kb₁, ∀ g : GL (Fin 2) (v.adicCompletion K), E₁ i (g * k) = E₁ i g)
    (hE₂K : ∀ i : ℤ, ∀ k ∈ Kb₂, ∀ g : GL (Fin 2) (v.adicCompletion K), E₂ i (g * k) = E₂ i g)
    (hAE₁ : ∀ (i : ℤ) (x : v.adicCompletion K) (g : GL (Fin 2) (v.adicCompletion K)),
      A₁ (unipotent x * g) * E₁ i (unipotent x * g) = A₁ g * E₁ i g)
    (hAE₂ : ∀ (i : ℤ) (x : v.adicCompletion K) (g : GL (Fin 2) (v.adicCompletion K)),
      A₂ (unipotent x * g) * E₂ i (unipotent x * g) = A₂ g * E₂ i g)
    (hE₁fin : ∀ C : Set (GL (Fin 2) (v.adicCompletion K)), IsCompact C →
      {i : ℤ | ∃ g ∈ C, E₁ i g ≠ 0}.Finite)
    (hE₂fin : ∀ C : Set (GL (Fin 2) (v.adicCompletion K)), IsCompact C →
      {i : ℤ | ∃ g ∈ C, E₂ i g ≠ 0}.Finite)

    (w₁ w₂ : ℂ → GL (Fin 2) (v.adicCompletion K) → ℂ) (wc₁ wc₂ : GL (Fin 2) (v.adicCompletion K) → ℂ) (u₁ : ℝ)
    (hw₁ : ∀ u : ℂ, u₁ < u.re → ∀ g : GL (Fin 2) (v.adicCompletion K),
      w₁ u g = ∑ᶠ i : ℤ, (Ideal.absNorm v.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E₁ i g)
    (hw₂ : ∀ u : ℂ, u₁ < u.re → ∀ g : GL (Fin 2) (v.adicCompletion K),
      w₂ u g = ∑ᶠ i : ℤ, (Ideal.absNorm v.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E₂ i g)
    (hwc₁ : ∀ g : GL (Fin 2) (v.adicCompletion K), wc₁ g = ∑ᶠ i : ℤ, E₁ i g)
    (hwc₂ : ∀ g : GL (Fin 2) (v.adicCompletion K), wc₂ g = ∑ᶠ i : ℤ, E₂ i g)

    (γ : ℂ → ℂ) (e : ℤ) :
    letI := localBorel K v
    letI := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := v.adicCompletion K)).range) [μN₂.IsHaarMeasure]
      (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure],

      (∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤, ∀ (η : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ),
        HasConductorExponentAt K v η c → c ≤ b →
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
              (∫ k in ((Kb₁ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
                  A₁ (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν) = 0) →
      (∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤, ∀ (η : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ),
        HasConductorExponentAt K v η c → c ≤ b →
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
              (∫ k in ((Kb₂ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
                  A₂ (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν) = 0) →

      (∃ u₀ : ℝ, ∀ u : ℂ, u₀ < u.re →
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (A₁ g * w₁ u g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
                v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (A₂ g * w₂ u g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
                v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) ∧
          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
                (fun g : GL (Fin 2) (v.adicCompletion K) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
                s A₁ (w₁ u) =
              (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
                (fun g : GL (Fin 2) (v.adicCompletion K) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
                s A₂ (w₂ u) =
              (Ideal.absNorm v.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ,
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
              (γ s * (Ideal.absNorm v.asIdeal : ℂ) ^ ((e : ℂ) * u)) *
                ((Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ s)))) →

      (∃ σc : ℝ, ∀ s : ℂ, σc < s.re →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (A₁ g * wc₁ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
                v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂)) ∧
          Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (A₂ g * wc₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
                v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) →

      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
        (∀ s : ℂ, σ₂ < s.re →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
            (A₁ g * wc₁ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
              v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
            (A₂ g * wc₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
              v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂))) ∧
        (∀ s : ℂ, σ₂ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
              (fun g : GL (Fin 2) (v.adicCompletion K) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
              s A₁ wc₁ =
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
              (fun g : GL (Fin 2) (v.adicCompletion K) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
              s A₂ wc₂ =
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            γ s * ((Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ s))) := by
  intro μ₂ _ μN₂ _ ν _ hTF₁ hTF₂ hFE hcentre
  classical
  obtain ⟨u₀, hFE⟩ := hFE
  obtain ⟨σc, hcentre⟩ := hcentre
  obtain ⟨U₁, hU₁, hAU₁⟩ := hA₁
  obtain ⟨U₂, hU₂, hAU₂⟩ := hA₂
  have hA₁c : Continuous A₁ := continuous_of_rightInvariant hU₁ hAU₁
  have hA₂c : Continuous A₂ := continuous_of_rightInvariant hU₂ hAU₂

  obtain ⟨T₁, c₁, hX₁⟩ :=
    LanglandsTunnell.RankinSelberg.exists_finset_forall_rsLocalIntegral_eq_sum_mul_setIntegral_of_forall_setIntegral_torusShell_eq_zero
      K v hπ hϖ b Kb₁ hKb₁ hKb₁K hKb₁c A₁ ⟨U₁, hU₁, hAU₁⟩ μ₂ μN₂ ν hTF₁
  obtain ⟨T₂, c₂, hX₂⟩ :=
    LanglandsTunnell.RankinSelberg.exists_finset_forall_rsLocalIntegral_eq_sum_mul_setIntegral_of_forall_setIntegral_torusShell_eq_zero
      K v hπ hϖ b Kb₂ hKb₂ hKb₂K hKb₂c A₂ ⟨U₂, hU₂, hAU₂⟩ μ₂ μN₂ ν hTF₂

  set rep : ℤ × ℤ → GL (Fin 2) (v.adicCompletion K) := fun dn =>
    scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ dn.2 *
      diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ dn.1 with hrep
  have hshellC : ∀ dn : ℤ × ℤ, IsCompact ((rep dn * ·) '' (kzero K v : Set (GL (Fin 2) (v.adicCompletion K)))) :=
    fun dn => (isCompact_kzero K v).image (continuous_const.mul continuous_id)
  set C₁ : Set (GL (Fin 2) (v.adicCompletion K)) := ⋃ dn ∈ T₁, (rep dn * ·) '' (kzero K v : Set _) with hC₁
  set C₂ : Set (GL (Fin 2) (v.adicCompletion K)) := ⋃ dn ∈ T₂, (rep dn * ·) '' (kzero K v : Set _) with hC₂
  have hC₁c : IsCompact C₁ := T₁.isCompact_biUnion fun dn _ => hshellC dn
  have hC₂c : IsCompact C₂ := T₂.isCompact_biUnion fun dn _ => hshellC dn
  set I₁ : Finset ℤ := (hE₁fin C₁ hC₁c).toFinset with hI₁
  set I₂ : Finset ℤ := (hE₂fin C₂ hC₂c).toFinset with hI₂
  have hI₁mem : ∀ dn ∈ T₁, ∀ k ∈ (kzero K v : Set (GL (Fin 2) (v.adicCompletion K))), ∀ i : ℤ,
      E₁ i (rep dn * k) ≠ 0 → i ∈ I₁ := by
    intro dn hdn k hk i hi
    rw [hI₁, Set.Finite.mem_toFinset]
    refine ⟨rep dn * k, ?_, hi⟩
    rw [hC₁]
    exact Set.mem_biUnion hdn ⟨k, hk, rfl⟩
  have hI₂mem : ∀ dn ∈ T₂, ∀ k ∈ (kzero K v : Set (GL (Fin 2) (v.adicCompletion K))), ∀ i : ℤ,
      E₂ i (rep dn * k) ≠ 0 → i ∈ I₂ := by
    intro dn hdn k hk i hi
    rw [hI₂, Set.Finite.mem_toFinset]
    refine ⟨rep dn * k, ?_, hi⟩
    rw [hC₂]
    exact Set.mem_biUnion hdn ⟨k, hk, rfl⟩

  set M₁ : ℤ × ℤ → ℤ → ℂ := fun dn i =>
    ∫ k in (kzero K v : Set (GL (Fin 2) (v.adicCompletion K))), A₁ (rep dn * k) * E₁ i (rep dn * k) ∂μ₂ with hM₁
  set M₂ : ℤ × ℤ → ℤ → ℂ := fun dn i =>
    ∫ k in (kzero K v : Set (GL (Fin 2) (v.adicCompletion K))), A₂ (rep dn * k) * E₂ i (rep dn * k) ∂μ₂ with hM₂

  have compute₁ : ∀ (cf : ℤ → ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ),
      (∀ g, B g = ∑ᶠ i : ℤ, cf i * E₁ i g) → ∀ s : ℂ,
      Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
        (A₁ g * B g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
          v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂)) →
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
          (fun g : GL (Fin 2) (v.adicCompletion K) =>
            (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
          s A₁ B = Lfun K v T₁ c₁ I₁ M₁ cf s := by
    intro cf B hB s hint
    rw [hX₁ B (B_mul_right Kb₁ E₁ hE₁K cf B hB) (AB_unipotent A₁ E₁ hAE₁ hE₁fin cf B hB) s hint, Lfun]
    refine Finset.sum_congr rfl fun dn hdn => ?_
    have hshell := setIntegral_shell_eq_sum Kb₁ A₁ E₁ hE₁K cf B hB hKb₁ hA₁c μ₂ (rep dn) I₁ (hI₁mem dn hdn)
    change c₁ dn * (qC K v) ^ (-((dn.1 + 2 * dn.2 : ℤ) : ℂ) * s) *
        ∫ k in (kzero K v : Set (GL (Fin 2) (v.adicCompletion K))), A₁ (rep dn * k) * B (rep dn * k) ∂μ₂ = _
    rw [hshell, Finset.mul_sum]
  have compute₂ : ∀ (cf : ℤ → ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ),
      (∀ g, B g = ∑ᶠ i : ℤ, cf i * E₂ i g) → ∀ s : ℂ,
      Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
        (A₂ g * B g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
          v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂)) →
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
          (fun g : GL (Fin 2) (v.adicCompletion K) =>
            (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
          s A₂ B = Lfun K v T₂ c₂ I₂ M₂ cf s := by
    intro cf B hB s hint
    rw [hX₂ B (B_mul_right Kb₂ E₂ hE₂K cf B hB) (AB_unipotent A₂ E₂ hAE₂ hE₂fin cf B hB) s hint, Lfun]
    refine Finset.sum_congr rfl fun dn hdn => ?_
    have hshell := setIntegral_shell_eq_sum Kb₂ A₂ E₂ hE₂K cf B hB hKb₂ hA₂c μ₂ (rep dn) I₂ (hI₂mem dn hdn)
    change c₂ dn * (qC K v) ^ (-((dn.1 + 2 * dn.2 : ℤ) : ℂ) * s) *
        ∫ k in (kzero K v : Set (GL (Fin 2) (v.adicCompletion K))), A₂ (rep dn * k) * B (rep dn * k) ∂μ₂ = _
    rw [hshell, Finset.mul_sum]

  have hw₁' : ∀ u : ℂ, u₁ < u.re → ∀ g, w₁ u g = ∑ᶠ i : ℤ, cfu K v u i * E₁ i g := fun u hu g => hw₁ u hu g
  have hw₂' : ∀ u : ℂ, u₁ < u.re → ∀ g, w₂ u g = ∑ᶠ i : ℤ, cfu K v u i * E₂ i g := fun u hu g => hw₂ u hu g
  have hwc₁' : ∀ g, wc₁ g = ∑ᶠ i : ℤ, (fun _ : ℤ => (1 : ℂ)) i * E₁ i g := fun g => by simpa using hwc₁ g
  have hwc₂' : ∀ g, wc₂ g = ∑ᶠ i : ℤ, (fun _ : ℤ => (1 : ℂ)) i * E₂ i g := fun g => by simpa using hwc₂ g

  have hFEexp : ∀ u : ℂ, max u₀ u₁ < u.re → ∀ s : ℂ,
      Lfun K v T₂ c₂ I₂ M₂ (cfu K v u) s =
        (γ s * (qC K v) ^ ((e : ℂ) * u)) * Lfun K v T₁ c₁ I₁ M₁ (cfu K v u) (-s) := by
    intro u hu
    have hu₀ : u₀ < u.re := lt_of_le_of_lt (le_max_left _ _) hu
    have hu₁ : u₁ < u.re := lt_of_le_of_lt (le_max_right _ _) hu
    obtain ⟨P, Pd, m, md, σ₂, σ₃, h1, h2, h3, h4, h5⟩ := hFE u hu₀

    have hL₁ : (fun s => Lfun K v T₁ c₁ I₁ M₁ (cfu K v u) s) =
        fun s => (qC K v) ^ ((m : ℂ) * s) * P.eval ((qC K v) ^ (-s)) := by
      refine eq_of_differentiable_of_eqOn_re (differentiable_Lfun_s K v T₁ c₁ I₁ M₁ _)
        (differentiable_laurent K v m P) σ₂ fun s hs => ?_
      rw [← compute₁ (cfu K v u) (w₁ u) (hw₁' u hu₁) s (h1 s hs)]
      exact h3 s hs

    have hL₂ : (fun s => Lfun K v T₂ c₂ I₂ M₂ (cfu K v u) s) =
        fun s => (qC K v) ^ ((md : ℂ) * s) * Pd.eval ((qC K v) ^ (-s)) := by
      refine eq_of_differentiable_of_eqOn_re (differentiable_Lfun_s K v T₂ c₂ I₂ M₂ _)
        (differentiable_laurent K v md Pd) σ₃ fun s hs => ?_
      rw [← compute₂ (cfu K v u) (w₂ u) (hw₂' u hu₁) s (h2 s hs)]
      exact h4 s hs
    intro s
    have e2 := congrFun hL₂ s
    have e1 := congrFun hL₁ (-s)
    rw [e2, e1, neg_neg]
    exact h5 s

  have hFEcentre : ∀ s : ℂ,
      Lfun K v T₂ c₂ I₂ M₂ (fun _ => 1) s = γ s * Lfun K v T₁ c₁ I₁ M₁ (fun _ => 1) (-s) := by
    intro s
    have hfun : (fun u => Lfun K v T₂ c₂ I₂ M₂ (cfu K v u) s) =
        fun u => (γ s * (qC K v) ^ ((e : ℂ) * u)) * Lfun K v T₁ c₁ I₁ M₁ (cfu K v u) (-s) := by
      refine eq_of_differentiable_of_eqOn_re (differentiable_Lfun_u K v T₂ c₂ I₂ M₂ s) ?_ (max u₀ u₁)
        fun u hu => hFEexp u hu s
      exact ((differentiable_qC_cpow_mul K v _).const_mul _).mul (differentiable_Lfun_u K v T₁ c₁ I₁ M₁ (-s))
    have h0 := congrFun hfun 0
    simp only [cfu_zero, mul_zero, Complex.cpow_zero, mul_one] at h0
    exact h0

  set κ₁ : ℤ × ℤ → ℂ := fun dn => c₁ dn * ∑ i ∈ I₁, M₁ dn i with hκ₁
  set κ₂ : ℤ × ℤ → ℂ := fun dn => c₂ dn * ∑ i ∈ I₂, M₂ dn i with hκ₂
  have hpack₁ : ∀ s : ℂ, Lfun K v T₁ c₁ I₁ M₁ (fun _ => 1) s =
      (qC K v) ^ ((mShift T₁ : ℂ) * s) * (poly κ₁ T₁).eval ((qC K v) ^ (-s)) := by
    intro s
    rw [laurent_eval_eq_sum, Lfun_one_eq]
  have hpack₂ : ∀ s : ℂ, Lfun K v T₂ c₂ I₂ M₂ (fun _ => 1) s =
      (qC K v) ^ ((mShift T₂ : ℂ) * s) * (poly κ₂ T₂).eval ((qC K v) ^ (-s)) := by
    intro s
    rw [laurent_eval_eq_sum, Lfun_one_eq]

  refine ⟨poly κ₁ T₁, poly κ₂ T₂, mShift T₁, mShift T₂, σc, σc, fun s hs => (hcentre s hs).1,
    fun s hs => (hcentre s hs).2, fun s hs => ?_, fun s hs => ?_, fun s => ?_⟩
  · rw [compute₁ (fun _ => 1) wc₁ hwc₁' s (hcentre s hs).1]
    exact hpack₁ s
  · rw [compute₂ (fun _ => 1) wc₂ hwc₂' s (hcentre s hs).2]
    exact hpack₂ s
  · have h := hFEcentre s
    rw [hpack₂ s, hpack₁ (-s), neg_neg] at h
    exact h

end S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_dual_eq_mul_finsum_of_forall_re_rsLocalIntegral_dual_eq_mul_finsum_cpow_of_torusShell (solution)
