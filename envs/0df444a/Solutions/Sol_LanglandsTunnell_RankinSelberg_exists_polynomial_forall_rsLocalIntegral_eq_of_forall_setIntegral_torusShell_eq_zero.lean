-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_polynomial_forall_rsLocalIntegral_eq_of_forall_setIntegral_torusShell_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/f9204add-58f3-5b02-9b89-500eaa5c9eaa

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
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_finset_forall_exists_eq_sum_of_forall_mem_higherUnitsAt
import Theorems.Thm_AutomorphicForm_hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_eq_of_forall_setIntegral_torusShell_eq_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal Topology

namespace KcTorusPoly

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

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem setIntegral_eq_setIntegral_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure G) [μ.IsMulLeftInvariant] {S T : Set G} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (k₀ : G) (hST : ∀ y, y ∈ T ↔ k₀⁻¹ * y ∈ S) (f : G → E) :
    ∫ y in T, f y ∂μ = ∫ x in S, f (k₀ * x) ∂μ := by
  rw [← integral_indicator hT, ← integral_indicator hS]
  have hpt : ∀ x, S.indicator (fun x => f (k₀ * x)) x = T.indicator f (k₀ * x) := by
    intro x
    by_cases hx : x ∈ S
    · have : k₀ * x ∈ T := by rw [hST, inv_mul_cancel_left]; exact hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem this]
    · have : k₀ * x ∉ T := by rw [hST, inv_mul_cancel_left]; exact hx
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]
  simp_rw [hpt]
  exact (integral_mul_left_eq_self _ k₀).symm

theorem setIntegral_subgroup_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure G) [μ.IsMulLeftInvariant] (H : Subgroup G) (hH : MeasurableSet (H : Set G))
    {k₀ : G} (hk₀ : k₀ ∈ H) (f : G → E) :
    ∫ x in (H : Set G), f (k₀ * x) ∂μ = ∫ x in (H : Set G), f x ∂μ := by
  refine (setIntegral_eq_setIntegral_comp_mul_left μ hH hH k₀ (fun y => ?_) f).symm
  simp only [SetLike.mem_coe]
  constructor
  · intro hy; exact H.mul_mem (H.inv_mem hk₀) hy
  · intro hy; simpa using H.mul_mem hk₀ hy

omit [MeasurableSpace G] [BorelSpace G] in

theorem continuous_of_rightInvariant {X : Type*} [TopologicalSpace X] {U : Subgroup G}
    (hU : IsOpen (U : Set G)) {f : G → X} (hf : ∀ k ∈ U, ∀ g : G, f (g * k) = f g) : Continuous f :=
  (isLocallyConstant_of_mul_invariant (U : Set G) hU U.one_mem f fun x h hh => hf h hh x).continuous

end Generic

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => (HeightOneSpectrum.adicCompletion K v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers K v)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))

scoped instance borelSpace_units_adic : BorelSpace (HeightOneSpectrum.adicCompletion K v)ˣ := borelSpace_units

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

theorem diagUnitGL2_mem_kzero {u : (HeightOneSpectrum.adicCompletion K v)ˣ} (hu : Valued.v (u : F) = 1) :
    diagUnitGL2 u ∈ kzero K v := by
  have hu' : Valued.v ((u⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have hinv : (diagUnitGL2 u)⁻¹ = diagUnitGL2 u⁻¹ := by
    rw [← diagHom_apply, ← diagHom_apply, map_inv]
  rw [mem_kzero_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, coe_diagUnitGL2]
    fin_cases i <;> fin_cases j <;> simp [hu]
  · rw [hinv, HeightOneSpectrum.mem_adicCompletionIntegers, coe_diagUnitGL2]
    have hu'' : (Valued.v (u : F))⁻¹ ≤ 1 := by rw [hu, inv_one]
    fin_cases i <;> fin_cases j <;> simp [hu'']

theorem valuation_det_of_mem_kzero {k : G₂} (hk : k ∈ kzero K v) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) = 1 := by
  rw [mem_kzero_iff] at hk
  have hint : ∀ (m : Mat), (∀ i j, m i j ∈ (O)) → Valued.v m.det ≤ 1 := by
    intro m hm
    rw [Matrix.det_fin_two]
    have h := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm i j)
    calc Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0)
        ≤ max (Valued.v (m 0 0 * m 1 1)) (Valued.v (m 0 1 * m 1 0)) := Valuation.map_sub _ _ _
      _ ≤ 1 := by
          refine max_le ?_ ?_
          · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
          · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)
  have h1 := hint _ hk.1
  have h2 := hint _ hk.2
  have hprod : Valued.v ((k : Mat).det) * Valued.v (((k⁻¹ : G₂) : Mat).det) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  apply le_antisymm h1
  by_contra hlt
  push Not at hlt
  have : Valued.v ((k : Mat).det) * Valued.v (((k⁻¹ : G₂) : Mat).det) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [hprod] at this
  exact lt_irrefl _ this

variable (b : ℕ) (Kb : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)))
  (hKbK : Kb ≤ AdelicDock.localLevelOne (𝓞 K) K v ⊤)
  (hKbc : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
    (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :
      Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) - 1) i j) ≤ WithZero.exp (-(b : ℤ))) → k ∈ Kb)

include hKbc in

theorem conj_diagUnitGL2_mem {k : G₂} (hk : k ∈ kzero K v) {h : (HeightOneSpectrum.adicCompletion K v)ˣ}
    (hh : h ∈ higherUnitsAt K v b) : k⁻¹ * diagUnitGL2 h * k ∈ Kb := by
  have hh1 : Valued.v (h : F) = 1 := hh.1
  have hmem : k⁻¹ * diagUnitGL2 h * k ∈ kzero K v :=
    (kzero K v).mul_mem ((kzero K v).mul_mem ((kzero K v).inv_mem hk) (diagUnitGL2_mem_kzero K v hh1)) hk
  refine hKbc _ hmem fun i j => ?_

  have hk' := (mem_kzero_iff K v k).mp hk
  have hkint := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk'.1 i j)
  have hkiint := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk'.2 i j)
  have hexp : (((k⁻¹ * diagUnitGL2 h * k : G₂) : Mat) - 1) =
      ((k⁻¹ : G₂) : Mat) * (((diagUnitGL2 h : G₂) : Mat) - 1) * (k : Mat) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    have : ((k⁻¹ : G₂) : Mat) * (k : Mat) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this]
    push_cast
    ring_nf

  have hd : ∀ i j, Valued.v ((((diagUnitGL2 h : G₂) : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ)) := by
    intro i j
    rcases hh.2 with hb0 | hle
    · subst hb0
      fin_cases i <;> fin_cases j <;> simp
      calc Valued.v ((h : F) - 1) ≤ max (Valued.v (h : F)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
        _ ≤ 1 := by rw [hh1, map_one, max_self]
    · have hle' : Valued.v ((h : F) - 1) ≤ (WithZero.exp (b : ℤ))⁻¹ := by rwa [← WithZero.exp_neg]
      fin_cases i <;> fin_cases j <;> simp [hle']
  rw [hexp]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]

  have hterm : ∀ i l m j, Valued.v (((k⁻¹ : G₂) : Mat) i l * (((diagUnitGL2 h : G₂) : Mat) - 1) l m * (k : Mat) m j)
      ≤ WithZero.exp (-(b : ℤ)) := by
    intro i l m j
    rw [map_mul, map_mul]
    calc Valued.v (((k⁻¹ : G₂) : Mat) i l) * Valued.v ((((diagUnitGL2 h : G₂) : Mat) - 1) l m) * Valued.v ((k : Mat) m j)
        ≤ 1 * WithZero.exp (-(b : ℤ)) * 1 := by
          gcongr
          · exact hkiint i l
          · exact hd l m
          · exact hkint m j
      _ = WithZero.exp (-(b : ℤ)) := by rw [one_mul, mul_one]
  rw [add_mul, add_mul]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · exact (Valuation.map_add _ _ _).trans (max_le (hterm i 0 0 j) (hterm i 1 0 j))
  · exact (Valuation.map_add _ _ _).trans (max_le (hterm i 0 1 j) (hterm i 1 1 j))

scoped instance compactSpace_kzero : CompactSpace (kzero K v) :=
  isCompact_iff_compactSpace.mp (isCompact_kzero K v)

abbrev KbIn : Subgroup (kzero K v) := Kb.subgroupOf (kzero K v)

abbrev Q : Type := (kzero K v) ⧸ KbIn K v Kb

theorem finite_Q (hKb : IsOpen (Kb : Set G₂)) : Finite (Q K v Kb) :=
  Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hKb)

def rq (q : Q K v Kb) : G₂ := ((Quotient.out q : kzero K v) : G₂)

theorem rq_mem (q : Q K v Kb) : rq K v Kb q ∈ kzero K v := (Quotient.out q).2

def coset (q : Q K v Kb) : Set G₂ := {g | (rq K v Kb q)⁻¹ * g ∈ Kb}

theorem isOpen_coset (hKb : IsOpen (Kb : Set G₂)) (q : Q K v Kb) : IsOpen (coset K v Kb q) :=
  hKb.preimage (continuous_const.mul continuous_id)

include hKbK in
theorem coset_subset (q : Q K v Kb) : coset K v Kb q ⊆ (kzero K v : Set G₂) := by
  intro g hg
  have h1 : (rq K v Kb q)⁻¹ * g ∈ kzero K v := hKbK hg
  have : g = rq K v Kb q * ((rq K v Kb q)⁻¹ * g) := by rw [mul_inv_cancel_left]
  rw [SetLike.mem_coe, this]
  exact (kzero K v).mul_mem (rq_mem K v Kb q) h1

theorem mem_coset_iff_mk_eq {g : G₂} (hg : g ∈ kzero K v) (q : Q K v Kb) :
    g ∈ coset K v Kb q ↔ (QuotientGroup.mk (⟨g, hg⟩ : kzero K v) : Q K v Kb) = q := by
  have hq : (QuotientGroup.mk (Quotient.out q : kzero K v) : Q K v Kb) = q := Quotient.out_eq q
  conv_rhs => rw [← hq]
  rw [eq_comm, QuotientGroup.eq]
  rfl

include hKbK in
theorem pairwise_disjoint_coset : Pairwise (fun q q' : Q K v Kb => Disjoint (coset K v Kb q) (coset K v Kb q')) := by
  intro q q' hqq'
  rw [Set.disjoint_left]
  intro g hg hg'
  have hgK : g ∈ kzero K v := coset_subset K v Kb hKbK q hg
  apply hqq'
  rw [← (mem_coset_iff_mk_eq K v Kb hgK q).mp hg, ← (mem_coset_iff_mk_eq K v Kb hgK q').mp hg']

include hKbK in
theorem iUnion_coset : (⋃ q, coset K v Kb q) = (kzero K v : Set G₂) := by
  apply subset_antisymm
  · exact Set.iUnion_subset fun q => coset_subset K v Kb hKbK q
  · intro g hg
    rw [Set.mem_iUnion]
    exact ⟨QuotientGroup.mk (⟨g, hg⟩ : kzero K v), (mem_coset_iff_mk_eq K v Kb hg _).mpr rfl⟩

include hKbK in

theorem setIntegral_kzero_eq_sum [Fintype (Q K v Kb)] (hKb : IsOpen (Kb : Set G₂))
    (μ : Measure G₂) [μ.IsMulLeftInvariant]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : G₂ → E)
    (hf : IntegrableOn f (kzero K v : Set G₂) μ) :
    ∫ x in (kzero K v : Set G₂), f x ∂μ = ∑ q : Q K v Kb, ∫ x in (Kb : Set G₂), f (rq K v Kb q * x) ∂μ := by
  have hU : (kzero K v : Set G₂) = ⋃ q ∈ (Finset.univ : Finset (Q K v Kb)), coset K v Kb q := by
    rw [← iUnion_coset K v Kb hKbK]
    simp
  rw [hU, integral_biUnion_finset _ (fun q _ => (isOpen_coset K v Kb hKb q).measurableSet)
    (fun q _ q' _ h => pairwise_disjoint_coset K v Kb hKbK h)
    (fun q _ => hf.mono_set (coset_subset K v Kb hKbK q))]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact setIntegral_eq_setIntegral_comp_mul_left μ hKb.measurableSet (isOpen_coset K v Kb hKb q).measurableSet
    (rq K v Kb q) (fun y => Iff.rfl) f

variable (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
  (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) ϖ ≠ 0)

abbrev piU : (HeightOneSpectrum.adicCompletion K v)ˣ := Units.mk0 (algebraMap _ F ϖ) hπ

def rep (dn : ℤ × ℤ) : G₂ :=
  scalarPi (algebraMap _ F ϖ) hπ ^ dn.2 * diagZ (algebraMap _ F ϖ) hπ dn.1

theorem diagZ_eq_diagUnitGL2 (d : ℤ) : diagZ (algebraMap _ F ϖ) hπ d = diagUnitGL2 (piU K v ϖ hπ ^ d) := by
  refine Units.ext ?_
  rw [coe_diagUnitGL2]
  simp [diagZ, Units.val_zpow_eq_zpow_val]

theorem rep_mul_diagUnitGL2 (dn : ℤ × ℤ) (u : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    rep K v ϖ hπ dn * diagUnitGL2 u =
      scalarPi (algebraMap _ F ϖ) hπ ^ dn.2 * diagUnitGL2 (piU K v ϖ hπ ^ dn.1 * u) := by
  rw [rep, diagZ_eq_diagUnitGL2, mul_assoc, ← diagHom_apply, ← diagHom_apply, ← diagHom_apply, ← map_mul]

theorem val_det_scalarPi :
    ((Matrix.GeneralLinearGroup.det (scalarPi (algebraMap _ F ϖ) hπ) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)
      = algebraMap _ F ϖ * algebraMap _ F ϖ := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [scalarPi, Matrix.det_fin_two]

theorem val_det_diagZ (d : ℤ) :
    ((Matrix.GeneralLinearGroup.det (diagZ (algebraMap _ F ϖ) hπ d) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)
      = algebraMap _ F ϖ ^ d := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [diagZ, Matrix.det_fin_two]

theorem val_det_rep (dn : ℤ × ℤ) :
    ((Matrix.GeneralLinearGroup.det (rep K v ϖ hπ dn) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)
      = algebraMap _ F ϖ ^ (dn.1 + 2 * dn.2) := by
  rw [rep, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, val_det_scalarPi, val_det_diagZ,
    ← pow_two, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hπ]
  congr 1
  push_cast
  ring

theorem norm_uniformizer (hϖ : Valued.v (algebraMap _ F ϖ) = WithZero.exp (-1 : ℤ)) :
    ‖algebraMap _ F ϖ‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have : Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ)))) = -1 := rfl
  rw [this]
  simp

theorem norm_eq_one_of_valuation_eq_one {x : F} (hx : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, hx, map_one, NNReal.coe_one]

theorem coe_modulus_eq_norm (x : F) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm]

theorem modulus_det_rep (hϖ : Valued.v (algebraMap _ F ϖ) = WithZero.exp (-1 : ℤ)) (dn : ℤ × ℤ) :
    ((modulus ((Matrix.GeneralLinearGroup.det (rep K v ϖ hπ dn) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ)
        : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) ^ (((-(dn.1 + 2 * dn.2) : ℤ) : ℂ)) := by
  rw [coe_modulus_eq_norm, val_det_rep, norm_zpow, norm_uniformizer K v ϖ hϖ, inv_zpow', Complex.ofReal_zpow,
    ← Complex.cpow_intCast]
  push_cast
  rfl

theorem modulus_det_mul_of_mem_kzero (a : G₂) {k : G₂} (hk : k ∈ kzero K v) :
    (modulus ((Matrix.GeneralLinearGroup.det (a * k) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) =
      (modulus ((Matrix.GeneralLinearGroup.det a : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) := by
  rw [map_mul, Units.val_mul, modulus_mul, NNReal.coe_mul, coe_modulus_eq_norm K v ((Matrix.GeneralLinearGroup.det k : _ˣ) : F),
    norm_eq_one_of_valuation_eq_one K v (valuation_det_of_mem_kzero K v hk), mul_one]

def sph : Set (HeightOneSpectrum.adicCompletion K v)ˣ := {u | Valued.v (u : F) = 1}

theorem val_eq_one_iff_norm_eq_one (x : F) : Valued.v x = 1 ↔ ‖x‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def]
  have h1 : (1 : ℝ) = ((1 : NNReal) : ℝ) := rfl
  rw [h1, NNReal.coe_inj, WithZeroMulInt.toNNReal_eq_one_iff _ (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
    (ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v))]

theorem image_val_sph : Units.val '' sph K v = Metric.sphere (0 : F) 1 := by
  ext x
  simp only [Set.mem_image, sph, Set.mem_setOf_eq, mem_sphere_zero_iff_norm]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (val_eq_one_iff_norm_eq_one K v _).mp hu
  · intro hx
    have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hx; exact zero_ne_one hx
    exact ⟨Units.mk0 x hx0, (val_eq_one_iff_norm_eq_one K v _).mpr hx, rfl⟩

theorem sph_eq_preimage : sph K v = Units.val ⁻¹' Metric.sphere (0 : F) 1 := by
  ext u
  simp only [sph, Set.mem_setOf_eq, Set.mem_preimage, mem_sphere_zero_iff_norm]
  exact val_eq_one_iff_norm_eq_one K v _

theorem isOpen_sph : IsOpen (sph K v) := by
  rw [sph_eq_preimage]
  exact (IsUltrametricDist.isOpen_sphere (0 : F) one_ne_zero).preimage Units.continuous_val

theorem isCompact_sph : IsCompact (sph K v) := by
  rw [Units.isEmbedding_val₀.isCompact_iff, image_val_sph]
  exact isCompact_sphere _ _

theorem one_mem_sph : (1 : (HeightOneSpectrum.adicCompletion K v)ˣ) ∈ sph K v := by
  simp [sph]

theorem measurableSet_sph : MeasurableSet (sph K v) := (isOpen_sph K v).measurableSet

theorem isOpen_higherUnitsAt : IsOpen (higherUnitsAt K v b) := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    have : higherUnitsAt K v 0 = sph K v := by
      ext u; rw [mem_higherUnitsAt_zero_iff]; rfl
    rw [this]; exact isOpen_sph K v
  ·
    set r : ℝ := ((WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp (-(b : ℤ))) : NNReal) : ℝ)
      with hr
    have hrpos : 0 < r := by
      rw [hr]
      exact_mod_cast WithZeroMulInt.toNNReal_pos (NumberField.HeightOneSpectrum.absNorm_ne_zero v) WithZero.exp_ne_zero
    have hset : higherUnitsAt K v b = sph K v ∩ Units.val ⁻¹' Metric.closedBall (1 : F) r := by
      ext u
      simp only [mem_higherUnitsAt_iff, sph, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
        Metric.mem_closedBall, dist_eq_norm]
      have hb0 : b ≠ 0 := by omega
      simp only [hb0, false_or]
      apply and_congr Iff.rfl
      rw [NumberField.FinitePlace.norm_def, hr, NNReal.coe_le_coe]
      exact ((WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le).symm
    rw [hset]
    exact (isOpen_sph K v).inter
      ((IsUltrametricDist.isOpen_closedBall (1 : F) hrpos.ne').preimage Units.continuous_val)

theorem continuous_of_higherUnits_invariant {X : Type*} [TopologicalSpace X]
    (f : (HeightOneSpectrum.adicCompletion K v)ˣ → X)
    (hf : ∀ u, ∀ h ∈ higherUnitsAt K v b, f (u * h) = f u) : Continuous f :=
  (isLocallyConstant_of_mul_invariant (higherUnitsAt K v b) (isOpen_higherUnitsAt K v b)
    (one_mem_higherUnitsAt K v b) f hf).continuous

theorem continuous_char {η : (HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ} {c : ℕ}
    (hη : HasConductorExponentAt K v η c) (hcb : c ≤ b) :
    Continuous fun u => ((η u : ℂˣ) : ℂ) := by
  refine continuous_of_higherUnits_invariant K v b _ fun u h hh => ?_
  have h1 : η h = 1 := hη.1 h (higherUnitsAt_antitone K v hcb hh)
  simp [map_mul, h1]

theorem continuous_diagUnitGL2 : Continuous fun u : (HeightOneSpectrum.adicCompletion K v)ˣ => (diagUnitGL2 u : G₂) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa using Units.continuous_val
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using continuous_const
  · have hinv : ∀ u : (HeightOneSpectrum.adicCompletion K v)ˣ, ((diagUnitGL2 u : G₂)⁻¹ : G₂) = diagUnitGL2 u⁻¹ := by
      intro u; rw [← diagHom_apply, ← diagHom_apply, map_inv]
    have hfun : (fun u : (HeightOneSpectrum.adicCompletion K v)ˣ => ((diagUnitGL2 u : G₂)⁻¹ : Units _).val) =
        fun u => ((diagUnitGL2 u⁻¹ : G₂) : Mat) := by
      funext u; rw [← hinv u]
    change Continuous fun u : (HeightOneSpectrum.adicCompletion K v)ˣ => ((diagUnitGL2 u : G₂)⁻¹ : Units _).val
    rw [hfun]
    refine continuous_matrix fun i j => ?_
    have hci : Continuous fun u : (HeightOneSpectrum.adicCompletion K v)ˣ => ((u⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) :=
      Units.continuous_coe_inv
    fin_cases i <;> fin_cases j
    · simpa using hci
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using continuous_const

section Vanishing

variable (A B : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ)
  (μ₂ : Measure (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)))

def Sshell (a : G₂) : ℂ := ∫ k in (kzero K v : Set G₂), A (a * k) * B (a * k) ∂μ₂

def αfun (a r : G₂) (u : (HeightOneSpectrum.adicCompletion K v)ˣ) : ℂ :=
  ∫ k in (Kb : Set G₂), A (a * diagUnitGL2 u * (r * k)) ∂μ₂

def βfun (a r : G₂) (u : (HeightOneSpectrum.adicCompletion K v)ˣ) : ℂ := B (a * diagUnitGL2 u * r)

variable {A B}
variable (hAc : Continuous A) (hBc : Continuous B)
  (hB : ∀ k ∈ Kb, ∀ g : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v), B (g * k) = B g)
  [μ₂.IsHaarMeasure]

include hAc hBc in
theorem continuous_AB (a x : G₂) : Continuous fun k : G₂ => A (a * (x * k)) * B (a * (x * k)) :=
  (hAc.comp (continuous_const.mul (continuous_const.mul continuous_id))).mul
    (hBc.comp (continuous_const.mul (continuous_const.mul continuous_id)))

include hAc hBc in
theorem integrableOn_AB (a x : G₂) :
    IntegrableOn (fun k : G₂ => A (a * (x * k)) * B (a * (x * k))) (kzero K v : Set G₂) μ₂ :=
  (continuous_AB K v hAc hBc a x).continuousOn.integrableOn_compact (isCompact_kzero K v)

theorem setIntegral_unit_eq_Sshell (a : G₂) {u : (HeightOneSpectrum.adicCompletion K v)ˣ} (hu : Valued.v (u : F) = 1) :
    ∫ k in (kzero K v : Set G₂), A (a * (diagUnitGL2 u * k)) * B (a * (diagUnitGL2 u * k)) ∂μ₂ = Sshell K v A B μ₂ a :=
  setIntegral_subgroup_comp_mul_left μ₂ (kzero K v) (isOpen_kzero K v).measurableSet
    (diagUnitGL2_mem_kzero K v hu) (fun k => A (a * k) * B (a * k))

include hKbK hAc hBc hB in

theorem setIntegral_unit_eq_sum [Fintype (Q K v Kb)] (hKb : IsOpen (Kb : Set G₂)) (a : G₂)
    (u : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    ∫ k in (kzero K v : Set G₂), A (a * (diagUnitGL2 u * k)) * B (a * (diagUnitGL2 u * k)) ∂μ₂ =
      ∑ q : Q K v Kb, αfun K v Kb A μ₂ a (rq K v Kb q) u * βfun K v B a (rq K v Kb q) u := by
  rw [setIntegral_kzero_eq_sum K v Kb hKbK hKb μ₂ _ (integrableOn_AB K v μ₂ hAc hBc a (diagUnitGL2 u))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [αfun, βfun, ← integral_mul_const]
  refine setIntegral_congr_fun hKb.measurableSet fun k hk => ?_
  have h1 : a * (diagUnitGL2 u * (rq K v Kb q * k)) = a * diagUnitGL2 u * (rq K v Kb q * k) := by group
  have h2 : a * diagUnitGL2 u * (rq K v Kb q * k) = a * diagUnitGL2 u * rq K v Kb q * k := by group
  rw [h1, h2, hB k hk]

omit [μ₂.IsHaarMeasure] in
include hKbc hB in

theorem βfun_mul (a : G₂) {r : G₂} (hr : r ∈ kzero K v) (u : (HeightOneSpectrum.adicCompletion K v)ˣ)
    {h : (HeightOneSpectrum.adicCompletion K v)ˣ} (hh : h ∈ higherUnitsAt K v b) :
    βfun K v B a r (u * h) = βfun K v B a r u := by
  have hκ := conj_diagUnitGL2_mem K v b Kb hKbc hr hh
  rw [βfun, βfun, ← diagHom_apply, map_mul, diagHom_apply, diagHom_apply]
  have : a * (diagUnitGL2 u * diagUnitGL2 h) * r = a * diagUnitGL2 u * r * (r⁻¹ * diagUnitGL2 h * r) := by group
  rw [this, hB _ hκ]

include hKbc in

theorem αfun_mul (hKb : IsOpen (Kb : Set G₂)) (a : G₂) {r : G₂} (hr : r ∈ kzero K v)
    (u : (HeightOneSpectrum.adicCompletion K v)ˣ)
    {h : (HeightOneSpectrum.adicCompletion K v)ˣ} (hh : h ∈ higherUnitsAt K v b) :
    αfun K v Kb A μ₂ a r (u * h) = αfun K v Kb A μ₂ a r u := by
  have hκ := conj_diagUnitGL2_mem K v b Kb hKbc hr hh
  rw [αfun, αfun, ← diagHom_apply, map_mul, diagHom_apply, diagHom_apply]
  have hpt : ∀ k, a * (diagUnitGL2 u * diagUnitGL2 h) * (r * k) =
      a * diagUnitGL2 u * (r * ((r⁻¹ * diagUnitGL2 h * r) * k)) := fun k => by group
  simp_rw [hpt]
  exact setIntegral_subgroup_comp_mul_left μ₂ Kb hKb.measurableSet hκ (fun k => A (a * diagUnitGL2 u * (r * k)))

include hKbc hB in
theorem continuous_βfun (a : G₂) {r : G₂} (hr : r ∈ kzero K v) : Continuous (βfun K v B a r) :=
  continuous_of_higherUnits_invariant K v b _ fun u _ hh => βfun_mul K v b Kb hKbc hB a hr u hh

include hKbc in
theorem continuous_αfun (hKb : IsOpen (Kb : Set G₂)) (a : G₂) {r : G₂} (hr : r ∈ kzero K v) :
    Continuous (αfun K v Kb A μ₂ a r) :=
  continuous_of_higherUnits_invariant K v b _ fun u _ hh => αfun_mul K v b Kb hKbc μ₂ hKb a hr u hh

theorem measure_sph_ne (ν : Measure (HeightOneSpectrum.adicCompletion K v)ˣ) [ν.IsHaarMeasure] :
    ν (sph K v) ≠ 0 ∧ ν (sph K v) ≠ ⊤ :=
  ⟨((isOpen_sph K v).measure_pos ν ⟨1, one_mem_sph K v⟩).ne', (isCompact_sph K v).measure_lt_top.ne⟩

include hKbK hKbc hAc hBc hB in

theorem Sshell_eq_zero [Fintype (Q K v Kb)] (hKb : IsOpen (Kb : Set G₂))
    (ν : Measure (HeightOneSpectrum.adicCompletion K v)ˣ) [ν.IsHaarMeasure]
    (S : Finset ((HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ))
    (hS1 : ∀ η ∈ S, ∃ m ≤ b, HasConductorExponentAt K v η m)
    (hS3 : ∀ g : (HeightOneSpectrum.adicCompletion K v)ˣ → ℂ,
      (∀ u : (HeightOneSpectrum.adicCompletion K v)ˣ, Valued.v (u : F) = 1 →
        ∀ h ∈ higherUnitsAt K v b, g (u * h) = g u) →
      ∃ c : ((HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ) → ℂ,
        ∀ u : (HeightOneSpectrum.adicCompletion K v)ˣ, Valued.v (u : F) = 1 →
          g u = ∑ η ∈ S, c η * ((η u : ℂˣ) : ℂ))
    (a : G₂)
    (hvan : ∀ q : Q K v Kb, ∀ η ∈ S,
      ∫ u in sph K v, αfun K v Kb A μ₂ a (rq K v Kb q) u * ((η u : ℂˣ) : ℂ) ∂ν = 0) :
    Sshell K v A B μ₂ a = 0 := by
  have hSph := measure_sph_ne K v ν
  have hreal : ν.real (sph K v) ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]; exact hSph

  have hq : ∀ q : Q K v Kb,
      ∫ u in sph K v, αfun K v Kb A μ₂ a (rq K v Kb q) u * βfun K v B a (rq K v Kb q) u ∂ν = 0 := by
    intro q
    have hr := rq_mem K v Kb q
    obtain ⟨c, hc⟩ := hS3 (βfun K v B a (rq K v Kb q)) fun u _ h hh => βfun_mul K v b Kb hKbc hB a hr u hh
    have hαc := continuous_αfun K v b Kb hKbc μ₂ hKb a hr (A := A)
    calc ∫ u in sph K v, αfun K v Kb A μ₂ a (rq K v Kb q) u * βfun K v B a (rq K v Kb q) u ∂ν
        = ∫ u in sph K v, ∑ η ∈ S, c η * (αfun K v Kb A μ₂ a (rq K v Kb q) u * ((η u : ℂˣ) : ℂ)) ∂ν := by
          refine setIntegral_congr_fun (measurableSet_sph K v) fun u hu => ?_
          rw [hc u hu, Finset.mul_sum]
          refine Finset.sum_congr rfl fun η _ => ?_
          ring
      _ = ∑ η ∈ S, ∫ u in sph K v, c η * (αfun K v Kb A μ₂ a (rq K v Kb q) u * ((η u : ℂˣ) : ℂ)) ∂ν := by
          refine integral_finsetSum _ fun η hη => ?_
          obtain ⟨m, hmb, hηm⟩ := hS1 η hη
          exact ((hαc.mul (continuous_char K v b hηm hmb)).continuousOn.integrableOn_compact
            (isCompact_sph K v)).const_mul (c η)
      _ = ∑ η ∈ S, c η * ∫ u in sph K v, αfun K v Kb A μ₂ a (rq K v Kb q) u * ((η u : ℂˣ) : ℂ) ∂ν := by
          refine Finset.sum_congr rfl fun η _ => ?_
          exact integral_const_mul _ _
      _ = 0 := by
          refine Finset.sum_eq_zero fun η hη => ?_
          rw [hvan q η hη, mul_zero]

  have key : ν.real (sph K v) • Sshell K v A B μ₂ a = 0 := by
    rw [← setIntegral_const]
    calc ∫ _ in sph K v, Sshell K v A B μ₂ a ∂ν
        = ∫ u in sph K v, ∑ q : Q K v Kb, αfun K v Kb A μ₂ a (rq K v Kb q) u * βfun K v B a (rq K v Kb q) u ∂ν := by
          refine setIntegral_congr_fun (measurableSet_sph K v) fun u hu => ?_
          rw [← setIntegral_unit_eq_Sshell K v μ₂ a hu, setIntegral_unit_eq_sum K v Kb hKbK μ₂ hAc hBc hB hKb a u]
      _ = ∑ q : Q K v Kb, ∫ u in sph K v, αfun K v Kb A μ₂ a (rq K v Kb q) u * βfun K v B a (rq K v Kb q) u ∂ν := by
          refine integral_finsetSum _ fun q _ => ?_
          have hr := rq_mem K v Kb q
          exact ((continuous_αfun K v b Kb hKbc μ₂ hKb a hr (A := A)).mul
            (continuous_βfun K v b Kb hKbc hB a hr)).continuousOn.integrableOn_compact (isCompact_sph K v)
      _ = 0 := Finset.sum_eq_zero fun q _ => hq q
  exact (smul_eq_zero.mp key).resolve_left hreal

end Vanishing

section Assembly

variable (A B : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ)
  (μ₂ : Measure (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)))

def fS (s : ℂ) (g : G₂) : ℂ :=
  (A g * B g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) ^ (s - 1 / 2)

abbrev qC : ℂ := (Ideal.absNorm v.asIdeal : ℂ)

theorem qC_ne_zero : qC K v ≠ 0 := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)

theorem log_qC_im : (Complex.log (qC K v)).im = 0 := by
  rw [qC, show ((Ideal.absNorm v.asIdeal : ℂ)) = ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) by norm_cast,
    ← Complex.ofReal_log (by positivity), Complex.ofReal_im]

theorem qC_cpow_cpow (y z : ℂ) (hy : y.im = 0) : ((qC K v) ^ y) ^ z = (qC K v) ^ (y * z) := by
  rw [Complex.cpow_mul]
  · rw [Complex.mul_im, log_qC_im, hy]; simp [Real.pi_pos]
  · rw [Complex.mul_im, log_qC_im, hy]; simp [Real.pi_pos.le]

variable {A B}

theorem continuous_modulus_det :
    Continuous fun g : G₂ =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) := by
  have h : (fun g : G₂ => ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ))
      = fun g : G₂ => ((‖(g : Mat).det‖ : ℝ) : ℂ) := by
    funext g
    rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [h]
  exact Complex.continuous_ofReal.comp ((Units.continuous_val.matrix_det).norm)

theorem measurable_fS (hAc : Continuous A) (hBc : Continuous B) (s : ℂ) : Measurable (fS K v A B s) := by
  unfold fS
  exact (hAc.measurable.mul hBc.measurable).mul ((continuous_modulus_det K v).measurable.pow_const _)

theorem exists_eq_unipotent {x : G₂} (hx : x ∈ (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion K v)).range) :
    ∃ y : F, x = unipotent y := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨Multiplicative.toAdd z, Units.ext ?_⟩
  simp [unipotentGL2Hom, unipotent, unipotentGL2_coe]

theorem det_unipotent (y : F) : Matrix.GeneralLinearGroup.det (unipotent y : G₂) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [unipotent, Matrix.det_fin_two]

theorem fS_unip (hAB : ∀ (x : F) (g : G₂), A (unipotent x * g) * B (unipotent x * g) = A g * B g) (s : ℂ) :
    ∀ x ∈ (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion K v)).range, ∀ g : G₂,
      fS K v A B s (x * g) = fS K v A B s g := by
  intro x hx g
  obtain ⟨y, rfl⟩ := exists_eq_unipotent K v hx
  rw [fS, fS, hAB, map_mul, det_unipotent, one_mul]

theorem setIntegral_fS_mul (s : ℂ) (a : G₂) :
    ∫ k in (kzero K v : Set G₂), fS K v A B s (a * k) ∂μ₂ =
      ((modulus ((Matrix.GeneralLinearGroup.det a : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) ^ (s - 1 / 2) *
        Sshell K v A B μ₂ a := by
  rw [Sshell, ← integral_const_mul]
  refine setIntegral_congr_fun (isOpen_kzero K v).measurableSet fun k hk => ?_
  rw [fS, modulus_det_mul_of_mem_kzero K v a hk, mul_comm]

variable (ϖ' : HeightOneSpectrum.adicCompletionIntegers K v)
  (hπ' : algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) ϖ' ≠ 0)

def eExp (dn : ℤ × ℤ) : ℤ := dn.1 + 2 * dn.2

def mShift (T' : Finset (ℤ × ℤ)) : ℤ := ∑ dn ∈ T', |eExp dn|

theorem mShift_add_nonneg (T' : Finset (ℤ × ℤ)) {dn : ℤ × ℤ} (hdn : dn ∈ T') : 0 ≤ mShift T' + eExp dn := by
  have h1 : |eExp dn| ≤ mShift T' :=
    Finset.single_le_sum (f := fun dn => |eExp dn|) (fun _ _ => abs_nonneg _) hdn
  have h2 : -eExp dn ≤ |eExp dn| := neg_le_abs _
  omega

def coef (w : ℤ × ℤ → ℝ) (dn : ℤ × ℤ) : ℂ :=
  ((w dn : ℝ) : ℂ) * Sshell K v A B μ₂ (rep K v ϖ' hπ' dn) * (qC K v) ^ (((eExp dn : ℤ) : ℂ) / 2)

def poly (w : ℤ × ℤ → ℝ) (T' : Finset (ℤ × ℤ)) : Polynomial ℂ :=
  ∑ dn ∈ T', Polynomial.C (coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn) * Polynomial.X ^ (mShift T' + eExp dn).toNat

theorem shell_term_eq (hϖ : Valued.v (algebraMap _ F ϖ') = WithZero.exp (-1 : ℤ)) (w : ℤ × ℤ → ℝ) (s : ℂ) (dn : ℤ × ℤ) :
    ((w dn : ℝ) : ℂ) * ∫ k in (kzero K v : Set G₂), fS K v A B s (rep K v ϖ' hπ' dn * k) ∂μ₂ =
      coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * (qC K v) ^ (-((eExp dn : ℤ) : ℂ) * s) := by
  rw [setIntegral_fS_mul, modulus_det_rep K v ϖ' hπ' hϖ, coef, qC_cpow_cpow]
  · have hexp : (((-(dn.1 + 2 * dn.2) : ℤ) : ℂ)) * (s - 1 / 2) =
        ((eExp dn : ℤ) : ℂ) / 2 + (-((eExp dn : ℤ) : ℂ) * s) := by
      simp only [eExp]; push_cast; ring
    rw [hexp, Complex.cpow_add _ _ (qC_ne_zero K v)]
    ring
  · push_cast; simp

theorem poly_term_eq (w : ℤ × ℤ → ℝ) (T' : Finset (ℤ × ℤ)) (s : ℂ) {dn : ℤ × ℤ} (hdn : dn ∈ T') :
    (qC K v) ^ ((mShift T' : ℂ) * s) *
        (coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * ((qC K v) ^ (-s)) ^ (mShift T' + eExp dn).toNat) =
      coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * (qC K v) ^ (-((eExp dn : ℤ) : ℂ) * s) := by
  have hN : (((mShift T' + eExp dn).toNat : ℕ) : ℂ) = ((mShift T' : ℤ) : ℂ) + ((eExp dn : ℤ) : ℂ) := by
    have := Int.toNat_of_nonneg (mShift_add_nonneg T' hdn)
    exact_mod_cast this
  rw [← Complex.cpow_nat_mul, hN, mul_left_comm, ← Complex.cpow_add _ _ (qC_ne_zero K v)]
  congr 2
  ring

theorem finish (hϖ : Valued.v (algebraMap _ F ϖ') = WithZero.exp (-1 : ℤ)) (w : ℤ × ℤ → ℝ) (T' : Finset (ℤ × ℤ))
    (hS0 : ∀ dn : ℤ × ℤ, dn ∉ T' → Sshell K v A B μ₂ (rep K v ϖ' hπ' dn) = 0) (s Ψ : ℂ)
    (hHS : HasSum (fun dn : ℤ × ℤ =>
      ((w dn : ℝ) : ℂ) * ∫ k in (kzero K v : Set G₂), fS K v A B s (rep K v ϖ' hπ' dn * k) ∂μ₂) Ψ) :
    Ψ = (qC K v) ^ ((mShift T' : ℂ) * s) * (poly K v μ₂ ϖ' hπ' (A := A) (B := B) w T').eval ((qC K v) ^ (-s)) := by
  have hfun : (fun dn : ℤ × ℤ =>
      ((w dn : ℝ) : ℂ) * ∫ k in (kzero K v : Set G₂), fS K v A B s (rep K v ϖ' hπ' dn * k) ∂μ₂) =
      fun dn => coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * (qC K v) ^ (-((eExp dn : ℤ) : ℂ) * s) := by
    funext dn; exact shell_term_eq K v μ₂ ϖ' hπ' hϖ w s dn
  rw [hfun] at hHS
  have hzero : ∀ dn ∉ T', coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * (qC K v) ^ (-((eExp dn : ℤ) : ℂ) * s) = 0 := by
    intro dn hdn
    rw [coef, hS0 dn hdn]; ring
  have hfin : HasSum (fun dn => coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * (qC K v) ^ (-((eExp dn : ℤ) : ℂ) * s))
      (∑ dn ∈ T', coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * (qC K v) ^ (-((eExp dn : ℤ) : ℂ) * s)) :=
    hasSum_sum_of_ne_finset_zero hzero
  rw [hHS.unique hfin, poly, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun dn hdn => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact (poly_term_eq K v μ₂ ϖ' hπ' w T' s hdn).symm

end Assembly

end

end KcTorusPoly
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_eq_of_forall_setIntegral_torusShell_eq_zero.KcTorusPoly"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

open KcTorusPoly in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ)
    (Kb : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hKb : IsOpen (Kb : Set (GL (Fin 2) (v.adicCompletion K))))
    (hKbK : Kb ≤ AdelicDock.localLevelOne (𝓞 K) K v ⊤)
    (hKbc : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
        - 1) i j) ≤ WithZero.exp (-(b : ℤ))) → k ∈ Kb)
    (A B : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hA : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion K)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (v.adicCompletion K), A (g * k) = A g)
    (hB : ∀ k ∈ Kb, ∀ g : GL (Fin 2) (v.adicCompletion K), B (g * k) = B g)
    (hAB : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (v.adicCompletion K)),
      A (unipotent x * g) * B (unipotent x * g) = A g * B g) :
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
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν) = 0) →
      ∃ (P : Polynomial ℂ) (m : ℤ), ∀ s : ℂ,
        Integrable (fun g : GL (Fin 2) (v.adicCompletion K) =>
          (A g * B g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) :
            v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂)) →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion K)).range μN₂
            (fun g : GL (Fin 2) (v.adicCompletion K) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) : ℝ))
            s A B =
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  intro μ₂ _ μN₂ _ ν _ hβ
  classical
  haveI : Fintype (Q K v Kb) := @Fintype.ofFinite _ (finite_Q K v Kb hKb)
  obtain ⟨U, hU, hAU⟩ := hA
  have hAc : Continuous A := continuous_of_rightInvariant hU hAU
  have hBc : Continuous B := continuous_of_rightInvariant hKb hB
  obtain ⟨S, hS1, -, hS3⟩ :=
    LanglandsTunnell.TateLocal.exists_finset_forall_exists_eq_sum_of_forall_mem_higherUnitsAt K v b

  have key : ∀ (q : Q K v Kb) (η : ↥S), ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
      (∫ u in sph K v,
          (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
              A (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ n.2 *
                diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
                  ^ n.1 * u) * (rq K v Kb q * k)) ∂μ₂) * ((η.1 u : ℂˣ) : ℂ) ∂ν) = 0 := by
    intro q η
    obtain ⟨m, hmb, hηm⟩ := hS1 η.1 η.2
    exact hβ (rq K v Kb q) (rq_mem K v Kb q) η.1 m hηm hmb
  choose Tf hTf using key
  set T' : Finset (ℤ × ℤ) := Finset.univ.biUnion fun q => Finset.univ.biUnion fun η : ↥S => Tf q η with hT'
  have hS0 : ∀ dn : ℤ × ℤ, dn ∉ T' → Sshell K v A B μ₂ (rep K v ϖ hπ dn) = 0 := by
    intro dn hdn
    refine Sshell_eq_zero K v b Kb hKbK hKbc μ₂ hAc hBc hB hKb ν S hS1 hS3 _ fun q η hη => ?_
    have hdn' : dn ∉ Tf q ⟨η, hη⟩ := by
      intro h
      apply hdn
      rw [hT']
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨q, ⟨η, hη⟩, h⟩
    have h0 := hTf q ⟨η, hη⟩ dn hdn'
    simp only [αfun, rep_mul_diagUnitGL2]
    exact h0

  let w : ℤ × ℤ → ℝ := fun dn =>
    ((μN₂ {x : ↥(unipotentGL2Hom (R := v.adicCompletion K)).range |
        (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1)⁻¹ *
          (x : GL (Fin 2) (v.adicCompletion K)) *
          (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1) ∈
        AdelicDock.localLevelOne (𝓞 K) K v ⊤})⁻¹).toReal
  refine ⟨poly K v μ₂ ϖ hπ (A := A) (B := B) w T', mShift T', fun s hint => ?_⟩
  obtain ⟨-, -, hHS⟩ :=
    AutomorphicForm.hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2 K v ϖ hπ hϖ μ₂ μN₂
      (fS K v A B s) (measurable_fS K v hAc hBc s) (fS_unip K v hAB s) hint
  exact finish K v μ₂ ϖ hπ hϖ w T' hS0 s _ hHS

end S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_eq_of_forall_setIntegral_torusShell_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_eq_of_forall_setIntegral_torusShell_eq_zero (solution)
