-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_torusShell_eq_sum_mul_torusShellArray_of_shellRecurrence_of_central
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/dee46796-91d4-5e18-a94b-e2e0bd5a9826

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_torusShell_eq_sum_mul_torusShellArray_of_shellRecurrence_of_central
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal Topology

namespace SEShellExp

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

section ValueForm

def synth (S : Finset ((HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ)) :
    (↥S → ℂ) →ₗ[ℂ] (↥(sph K v) → ℂ) where
  toFun c := fun u => ∑ η : ↥S, c η * ((η.1 u.1 : ℂˣ) : ℂ)
  map_add' c c' := by
    funext u
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem synth_apply (S : Finset ((HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ)) (c : ↥S → ℂ) (u : ↥(sph K v)) :
    synth K v S c u = ∑ η : ↥S, c η * ((η.1 u.1 : ℂˣ) : ℂ) := rfl

theorem restrict_mem_range_synth (S : Finset ((HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ))
    (g : (HeightOneSpectrum.adicCompletion K v)ˣ → ℂ)
    (hg : ∃ c : ((HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ) → ℂ,
      ∀ u : (HeightOneSpectrum.adicCompletion K v)ˣ, Valued.v (u : F) = 1 → g u = ∑ η ∈ S, c η * ((η u : ℂˣ) : ℂ)) :
    (fun u : ↥(sph K v) => g u) ∈ LinearMap.range (synth K v S) := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨fun η => c η.1, ?_⟩
  funext u
  rw [synth_apply, hc u.1 u.2]
  exact Finset.sum_coe_sort S (fun η => c η * ((η u.1 : ℂˣ) : ℂ))

variable (A B : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ)
  (μ₂ : Measure (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)))

variable {A B}
variable (hAc : Continuous A) (hBc : Continuous B)
  (hB : ∀ k ∈ Kb, ∀ g : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v), B (g * k) = B g)
  [μ₂.IsHaarMeasure]

include hKbK hKbc hAc hBc hB in

theorem real_smul_Sshell_eq_sum [Fintype (Q K v Kb)] (hKb : IsOpen (Kb : Set G₂))
    (ν : Measure (HeightOneSpectrum.adicCompletion K v)ˣ) [ν.IsHaarMeasure] (a : G₂) :
    ν.real (sph K v) • Sshell K v A B μ₂ a =
      ∑ q : Q K v Kb, ∫ u in sph K v, αfun K v Kb A μ₂ a (rq K v Kb q) u * βfun K v B a (rq K v Kb q) u ∂ν := by
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

include hKbc in

theorem integral_αfun_mul_eq_sum (hKb : IsOpen (Kb : Set G₂))
    (ν : Measure (HeightOneSpectrum.adicCompletion K v)ˣ) [ν.IsHaarMeasure]
    (S : Finset ((HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ))
    (hS1 : ∀ η ∈ S, ∃ m ≤ b, HasConductorExponentAt K v η m)
    (a : G₂) {r : G₂} (hr : r ∈ kzero K v)
    (β : (HeightOneSpectrum.adicCompletion K v)ˣ → ℂ) (d : ℂ) (cc : ↥S → ℂ)
    (hβ : ∀ u : (HeightOneSpectrum.adicCompletion K v)ˣ, Valued.v (u : F) = 1 →
      β u = d * ∑ η : ↥S, cc η * ((η.1 u : ℂˣ) : ℂ)) :
    ∫ u in sph K v, αfun K v Kb A μ₂ a r u * β u ∂ν =
      ∑ η : ↥S, d * cc η * ∫ u in sph K v, αfun K v Kb A μ₂ a r u * ((η.1 u : ℂˣ) : ℂ) ∂ν := by
  have hαc := continuous_αfun K v b Kb hKbc μ₂ hKb a hr (A := A)
  calc ∫ u in sph K v, αfun K v Kb A μ₂ a r u * β u ∂ν
      = ∫ u in sph K v, ∑ η : ↥S, d * cc η * (αfun K v Kb A μ₂ a r u * ((η.1 u : ℂˣ) : ℂ)) ∂ν := by
        refine setIntegral_congr_fun (measurableSet_sph K v) fun u hu => ?_
        rw [hβ u hu, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun η _ => ?_
        ring
    _ = ∑ η : ↥S, ∫ u in sph K v, d * cc η * (αfun K v Kb A μ₂ a r u * ((η.1 u : ℂˣ) : ℂ)) ∂ν := by
        refine integral_finsetSum _ fun η _ => ?_
        obtain ⟨m, hmb, hηm⟩ := hS1 η.1 η.2
        exact ((hαc.mul (continuous_char K v b hηm hmb)).continuousOn.integrableOn_compact
          (isCompact_sph K v)).const_mul (d * cc η)
    _ = ∑ η : ↥S, d * cc η * ∫ u in sph K v, αfun K v Kb A μ₂ a r u * ((η.1 u : ℂˣ) : ℂ) ∂ν := by
        refine Finset.sum_congr rfl fun η _ => ?_
        exact integral_const_mul _ _

end ValueForm

section Growth

open Finset

theorem norm_le_geom (c : ℤ → ℂ) (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ) (hD : D.eval 0 ≠ 0)
    (h0 : ∀ m : ℤ, m < N₁ → c m = 0)
    (hrec : ∀ m : ℕ, M ≤ m →
      ∑ j ∈ Finset.range (D.natDegree + 1), D.coeff j * c (N₁ + (m : ℤ) - (j : ℤ)) = 0) :
    ∃ C₀ ρ : ℝ, 0 ≤ C₀ ∧ 1 ≤ ρ ∧ ∀ n : ℕ, ‖c (N₁ + (n : ℤ))‖ ≤ C₀ * ρ ^ n := by
  classical
  set d : ℕ := D.natDegree with hd
  have ha0 : D.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
  have ha0' : 0 < ‖D.coeff 0‖ := norm_pos_iff.mpr ha0
  set L : ℝ := ∑ j ∈ Finset.range d, ‖D.coeff (j + 1)‖ with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set ρ : ℝ := max 1 (L / ‖D.coeff 0‖) with hρ
  have hρ1 : 1 ≤ ρ := le_max_left _ _
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ1
  set T : ℕ := max M (d + 1) with hT
  set C₀ : ℝ := ∑ j ∈ Finset.range T, ‖c (N₁ + (j : ℤ))‖ with hC₀
  have hC₀0 : 0 ≤ C₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C₀, ρ, hC₀0, hρ1, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < T
    · calc ‖c (N₁ + (n : ℤ))‖ ≤ C₀ :=
            Finset.single_le_sum (f := fun j : ℕ => ‖c (N₁ + (j : ℤ))‖) (fun _ _ => norm_nonneg _)
              (Finset.mem_range.mpr hn)
        _ ≤ C₀ * ρ ^ n := le_mul_of_one_le_right hC₀0 (one_le_pow₀ hρ1)
    · have hn : T ≤ n := not_lt.mp hn
      have hMn : M ≤ n := le_trans (le_max_left _ _) hn
      have hdn : d + 1 ≤ n := le_trans (le_max_right _ _) hn

      have hr := hrec n hMn
      rw [Finset.sum_range_succ'] at hr
      simp only [Nat.cast_zero, sub_zero] at hr

      have hkey : D.coeff 0 * c (N₁ + (n : ℤ)) =
          -∑ j ∈ Finset.range d, D.coeff (j + 1) * c (N₁ + (n : ℤ) - ((j + 1 : ℕ) : ℤ)) := by
        linear_combination hr

      have hterm : ∀ j ∈ Finset.range d,
          ‖D.coeff (j + 1) * c (N₁ + (n : ℤ) - ((j + 1 : ℕ) : ℤ))‖ ≤ ‖D.coeff (j + 1)‖ * (C₀ * ρ ^ (n - 1)) := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hlt : n - (j + 1) < n := by omega
        have hih := ih (n - (j + 1)) hlt
        have hcast : N₁ + (n : ℤ) - ((j + 1 : ℕ) : ℤ) = N₁ + ((n - (j + 1) : ℕ) : ℤ) := by
          push_cast
          omega
        rw [hcast]
        refine hih.trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hC₀0
        exact pow_le_pow_right₀ hρ1 (by omega)
      have hsum : ‖∑ j ∈ Finset.range d, D.coeff (j + 1) * c (N₁ + (n : ℤ) - ((j + 1 : ℕ) : ℤ))‖ ≤
          L * (C₀ * ρ ^ (n - 1)) := by
        refine (norm_sum_le _ _).trans ?_
        rw [hL, Finset.sum_mul]
        exact Finset.sum_le_sum hterm
      have h1 : ‖D.coeff 0‖ * ‖c (N₁ + (n : ℤ))‖ ≤ L * (C₀ * ρ ^ (n - 1)) := by
        rw [← norm_mul, hkey, norm_neg]
        exact hsum
      have h2 : ‖c (N₁ + (n : ℤ))‖ ≤ (L / ‖D.coeff 0‖) * (C₀ * ρ ^ (n - 1)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ ha0', mul_comm]
        exact h1
      have h3 : L / ‖D.coeff 0‖ ≤ ρ := le_max_right _ _
      calc ‖c (N₁ + (n : ℤ))‖ ≤ (L / ‖D.coeff 0‖) * (C₀ * ρ ^ (n - 1)) := h2
        _ ≤ ρ * (C₀ * ρ ^ (n - 1)) := mul_le_mul_of_nonneg_right h3 (mul_nonneg hC₀0 (pow_nonneg hρ0.le _))
        _ = C₀ * ρ ^ n := by
          rw [show ρ ^ n = ρ ^ (n - 1) * ρ from by rw [← pow_succ]; congr 1; omega]; ring

theorem norm_le_rpow (c : ℤ → ℂ) (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ) (hD : D.eval 0 ≠ 0)
    (h0 : ∀ m : ℤ, m < N₁ → c m = 0)
    (hrec : ∀ m : ℕ, M ≤ m →
      ∑ j ∈ Finset.range (D.natDegree + 1), D.coeff j * c (N₁ + (m : ℤ) - (j : ℤ)) = 0)
    (q : ℝ) (hq : 1 < q) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ m : ℤ, ‖c m‖ ≤ C * q ^ (A * ((max m 0 : ℤ) : ℝ)) := by
  obtain ⟨C₀, ρ, hC₀, hρ1, hgeom⟩ := norm_le_geom c N₁ D M hD h0 hrec
  have hq0 : 0 < q := lt_trans one_pos hq
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ1
  have hlogq : 0 < Real.log q := Real.log_pos hq
  set A : ℝ := Real.log ρ / Real.log q with hA
  have hA0 : 0 ≤ A := div_nonneg (Real.log_nonneg hρ1) hlogq.le
  have hqA : q ^ A = ρ := by
    rw [Real.rpow_def_of_pos hq0, hA, mul_div_cancel₀ _ hlogq.ne', Real.exp_log hρ0]
  have hpow : ∀ t : ℕ, q ^ (A * (t : ℝ)) = ρ ^ t := by
    intro t
    rw [Real.rpow_mul hq0.le, hqA, Real.rpow_natCast]
  refine ⟨C₀ * ρ ^ N₁.natAbs, A, mul_nonneg hC₀ (pow_nonneg hρ0.le _), hA0, fun m => ?_⟩
  by_cases hm : m < N₁
  · rw [h0 m hm, norm_zero]
    exact mul_nonneg (mul_nonneg hC₀ (pow_nonneg hρ0.le _)) (Real.rpow_nonneg hq0.le _)
  · have hm : N₁ ≤ m := not_lt.mp hm
    have hcast : ((max m 0 : ℤ) : ℝ) = (((max m 0).toNat : ℕ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (le_max_right _ _)]
    rw [hcast, hpow]
    have h1 := hgeom (m - N₁).toNat
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hm), add_sub_cancel] at h1
    refine h1.trans ?_
    have hle : (m - N₁).toNat ≤ N₁.natAbs + (max m 0).toNat := by omega
    calc C₀ * ρ ^ (m - N₁).toNat ≤ C₀ * ρ ^ (N₁.natAbs + (max m 0).toNat) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ1 hle) hC₀
      _ = C₀ * ρ ^ N₁.natAbs * ρ ^ (max m 0).toNat := by rw [pow_add, mul_assoc]

end Growth

section Central

variable (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
  (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) ϖ ≠ 0)

theorem scalarPi_eq_scalar :
    scalarPi (algebraMap _ F ϖ) hπ = Matrix.GeneralLinearGroup.scalar (Fin 2) (piU K v ϖ hπ) := by
  refine Units.ext ?_
  change ((scalarPi (algebraMap _ F ϖ) hπ : G₂) : Mat) = Matrix.scalar (Fin 2) ((piU K v ϖ hπ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarPi, Matrix.scalar]

theorem scalarPi_zpow_eq_scalar (n : ℤ) :
    scalarPi (algebraMap _ F ϖ) hπ ^ n = Matrix.GeneralLinearGroup.scalar (Fin 2) (piU K v ϖ hπ ^ n) := by
  rw [scalarPi_eq_scalar, map_zpow]

theorem apply_scalarPi_zpow_mul {B : G₂ → ℂ} {ω : (HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ}
    (hBcen : ∀ (z : (HeightOneSpectrum.adicCompletion K v)ˣ) (g : G₂),
      B (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * B g)
    (n : ℤ) (g : G₂) :
    B (scalarPi (algebraMap _ F ϖ) hπ ^ n * g) = (((ω (piU K v ϖ hπ)) : ℂˣ) : ℂ) ^ n * B g := by
  rw [scalarPi_zpow_eq_scalar, hBcen, map_zpow, Units.val_zpow_eq_zpow_val]

end Central

end

end SEShellExp
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_torusShell_eq_sum_mul_torusShellArray_of_shellRecurrence_of_central.SEShellExp"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

open SEShellExp in
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

    (ω : (v.adicCompletion K)ˣ →* ℂˣ)
    (hBcen : ∀ (z : (v.adicCompletion K)ˣ) (g : GL (Fin 2) (v.adicCompletion K)),
      B (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * B g)

    (hBgr : ∃ (C A' : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
      ‖B (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ m * k)‖ ≤ C * (Ideal.absNorm v.asIdeal : ℝ) ^ (A' * m))

    (hBrec : ∃ (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
        (∀ m : ℤ, m < N₁ → B (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ m * k) = 0) ∧
        (∀ m : ℕ, M ≤ m →
          ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * B (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0)) :
    letI := localBorel K v
    letI := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ₂.IsHaarMeasure]
      (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure],
      ∃ (n : ℕ) (k₀ : Fin n → GL (Fin 2) (v.adicCompletion K)) (η : Fin n → ((v.adicCompletion K)ˣ →* ℂˣ)) (cη : Fin n → ℕ)
        (c : Fin n → ℤ → ℂ) (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ) (C' A'' : ℝ),
        (∀ i, k₀ i ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤) ∧
        (∀ i, HasConductorExponentAt K v (η i) (cη i) ∧ cη i ≤ b) ∧
        D.eval 0 ≠ 0 ∧
        (∀ i, (∀ m : ℤ, m < N₁ → c i m = 0) ∧
          (∀ m : ℕ, M ≤ m →
            ∑ j ∈ Finset.range (D.natDegree + 1), D.coeff j * c i (N₁ + (m : ℤ) - (j : ℤ)) = 0)) ∧
        (∀ i (m : ℤ), ‖c i m‖ ≤ C' * (Ideal.absNorm v.asIdeal : ℝ) ^ (A'' * ((max m 0 : ℤ) : ℝ))) ∧
        ∀ dn : ℤ × ℤ,
          ((ν {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1}).toReal : ℂ) *
            ∫ k in ((AdelicDock.localLevelOne (𝓞 K) K v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
              A (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ dn.1 * k) *
              B (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ dn.1 * k) ∂μ₂ =
          ∑ i, (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ) : ℂˣ) : ℂ) ^ dn.2 * c i dn.1 *
            ∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ dn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ dn.1 * u) * (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ) ∂ν) := by
  intro μ₂ _ ν _
  classical
  haveI : Fintype (Q K v Kb) := @Fintype.ofFinite _ (finite_Q K v Kb hKb)
  obtain ⟨U, hU, hAU⟩ := hA
  have hAc : Continuous A := continuous_of_rightInvariant hU hAU
  have hBc : Continuous B := continuous_of_rightInvariant hKb hB
  obtain ⟨S, hS1, -, hS3⟩ :=
    LanglandsTunnell.TateLocal.exists_finset_forall_exists_eq_sum_of_forall_mem_higherUnitsAt K v b
  obtain ⟨N₁, D, M, hD0, hrecB⟩ := hBrec

  obtain ⟨ψ, hψ⟩ := LinearMap.exists_rightInverse_of_surjective (synth K v S).rangeRestrict
    (LinearMap.range_rangeRestrict _)

  have hmem : ∀ r ∈ kzero K v, ∀ m : ℤ,
      (fun u : ↥(sph K v) => βfun K v B (diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ m) r u) ∈
        LinearMap.range (synth K v S) := by
    intro r hr m
    exact restrict_mem_range_synth K v S _ (hS3 _ fun u _ h hh => βfun_mul K v b Kb hKbc hB _ hr u hh)

  let coef : ∀ r : GL (Fin 2) (v.adicCompletion K), r ∈ kzero K v → ℤ → (↥S → ℂ) :=
    fun r hr m => ψ ⟨_, hmem r hr m⟩

  have hexp : ∀ (r : GL (Fin 2) (v.adicCompletion K)) (hr : r ∈ kzero K v) (m : ℤ) (u : (v.adicCompletion K)ˣ),
      Valued.v (u : v.adicCompletion K) = 1 →
      βfun K v B (diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ m) r u =
        ∑ η : ↥S, coef r hr m η * ((η.1 u : ℂˣ) : ℂ) := by
    intro r hr m u hu
    have h1 : synth K v S (ψ ⟨_, hmem r hr m⟩) =
        fun u : ↥(sph K v) => βfun K v B (diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ m) r u := by
      have := LinearMap.ext_iff.mp hψ ⟨_, hmem r hr m⟩
      rw [LinearMap.comp_apply, LinearMap.id_apply] at this
      exact congrArg Subtype.val this
    have h2 := congrFun h1 ⟨u, hu⟩
    rw [synth_apply] at h2
    exact h2.symm

  have hcoef_rec : ∀ (r : GL (Fin 2) (v.adicCompletion K)) (hr : r ∈ kzero K v) (m : ℕ), M ≤ m → ∀ η : ↥S,
      ∑ j ∈ Finset.range (D.natDegree + 1), D.coeff j * coef r hr (N₁ + (m : ℤ) - (j : ℤ)) η = 0 := by
    intro r hr m hm η
    have hzero : (∑ j ∈ Finset.range (D.natDegree + 1),
        D.coeff j • (⟨_, hmem r hr (N₁ + (m : ℤ) - (j : ℤ))⟩ : ↥(LinearMap.range (synth K v S)))) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      funext u
      simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hk : diagUnitGL2 (u : (v.adicCompletion K)ˣ) * r ∈ kzero K v :=
        (kzero K v).mul_mem (diagUnitGL2_mem_kzero K v u.2) hr
      have := (hrecB _ hk).2 m hm
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) this
      simp only [βfun, mul_assoc]
    have := congrArg (fun x => ψ x η) hzero
    simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact this

  have hcoef_zero : ∀ (r : GL (Fin 2) (v.adicCompletion K)) (hr : r ∈ kzero K v) (m : ℤ), m < N₁ →
      ∀ η : ↥S, coef r hr m η = 0 := by
    intro r hr m hm η
    have hzero : (⟨_, hmem r hr m⟩ : ↥(LinearMap.range (synth K v S))) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_zero]
      funext u
      simp only [Pi.zero_apply]
      have hk : diagUnitGL2 (u : (v.adicCompletion K)ˣ) * r ∈ kzero K v :=
        (kzero K v).mul_mem (diagUnitGL2_mem_kzero K v u.2) hr
      have := (hrecB _ hk).1 m hm
      simpa only [βfun, mul_assoc] using this
    show ψ ⟨_, hmem r hr m⟩ η = 0
    rw [hzero, map_zero, Pi.zero_apply]

  have hmain : ∀ dn : ℤ × ℤ,
      ((ν.real (sph K v) : ℝ) : ℂ) * Sshell K v A B μ₂ (rep K v ϖ hπ dn) =
        ∑ q : Q K v Kb, ∑ η : ↥S,
          (((ω (piU K v ϖ hπ)) : ℂˣ) : ℂ) ^ dn.2 * coef (rq K v Kb q) (rq_mem K v Kb q) dn.1 η *
            ∫ u in sph K v, αfun K v Kb A μ₂ (rep K v ϖ hπ dn) (rq K v Kb q) u * ((η.1 u : ℂˣ) : ℂ) ∂ν := by
    intro dn
    have h1 := real_smul_Sshell_eq_sum K v b Kb hKbK hKbc μ₂ hAc hBc hB hKb ν (rep K v ϖ hπ dn)
    rw [Complex.real_smul] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun q _ => ?_
    refine integral_αfun_mul_eq_sum K v b Kb hKbc μ₂ hKb ν S hS1 (rep K v ϖ hπ dn) (rq_mem K v Kb q)
      (βfun K v B (rep K v ϖ hπ dn) (rq K v Kb q)) ((((ω (piU K v ϖ hπ)) : ℂˣ) : ℂ) ^ dn.2)
      (coef (rq K v Kb q) (rq_mem K v Kb q) dn.1) fun u hu => ?_
    rw [← hexp _ (rq_mem K v Kb q) dn.1 u hu]
    simp only [βfun, rep, mul_assoc]
    rw [apply_scalarPi_zpow_mul K v ϖ hπ hBcen]

  let e : Fin (Fintype.card (Q K v Kb × ↥S)) ≃ Q K v Kb × ↥S := (Fintype.equivFin _).symm
  have hcond : ∀ η : ↥S, ∃ m : ℕ, HasConductorExponentAt K v η.1 m ∧ m ≤ b := fun η => by
    obtain ⟨m, hmb, hm⟩ := hS1 η.1 η.2
    exact ⟨m, hm, hmb⟩
  choose cexp hcexp using hcond
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hgrow : ∀ p : Q K v Kb × ↥S, ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ m : ℤ,
      ‖coef (rq K v Kb p.1) (rq_mem K v Kb p.1) m p.2‖ ≤
        C * (Ideal.absNorm v.asIdeal : ℝ) ^ (A * ((max m 0 : ℤ) : ℝ)) :=
    fun p => norm_le_rpow (fun m => coef (rq K v Kb p.1) (rq_mem K v Kb p.1) m p.2) N₁ D M hD0
      (fun m hm => hcoef_zero (rq K v Kb p.1) (rq_mem K v Kb p.1) m hm p.2)
      (fun m hm => hcoef_rec (rq K v Kb p.1) (rq_mem K v Kb p.1) m hm p.2) _ hq1
  choose Cf Af hCf hAf hgrowf using hgrow
  refine ⟨Fintype.card (Q K v Kb × ↥S), fun i => rq K v Kb (e i).1, fun i => ((e i).2).1, fun i => cexp (e i).2,
    fun i m => coef (rq K v Kb (e i).1) (rq_mem K v Kb (e i).1) m (e i).2, N₁, D, M,
    ∑ p, Cf p, ∑ p, Af p, fun i => rq_mem K v Kb (e i).1, fun i => hcexp (e i).2, hD0,
    fun i => ⟨fun m hm => hcoef_zero (rq K v Kb (e i).1) (rq_mem K v Kb (e i).1) m hm (e i).2,
      fun m hm => hcoef_rec (rq K v Kb (e i).1) (rq_mem K v Kb (e i).1) m hm (e i).2⟩,
    fun i m => ?_, fun dn => ?_⟩
  ·
    refine (hgrowf (e i) m).trans ?_
    have hC : Cf (e i) ≤ ∑ p, Cf p := Finset.single_le_sum (fun p _ => hCf p) (Finset.mem_univ _)
    have hA : Af (e i) ≤ ∑ p, Af p := Finset.single_le_sum (fun p _ => hAf p) (Finset.mem_univ _)
    have ht : 0 ≤ ((max m 0 : ℤ) : ℝ) := by exact_mod_cast le_max_right m 0
    exact mul_le_mul hC (Real.rpow_le_rpow_of_exponent_le hq1.le (mul_le_mul_of_nonneg_right hA ht))
      (Real.rpow_nonneg (zero_le_one.trans hq1.le) _) (Finset.sum_nonneg fun p _ => hCf p)
  ·
    have h := hmain dn
    simp only [αfun, rep_mul_diagUnitGL2] at h
    rw [← Fintype.sum_prod_type'] at h
    exact h.trans (Fintype.sum_equiv e _ _ (fun i => rfl)).symm

end S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_torusShell_eq_sum_mul_torusShellArray_of_shellRecurrence_of_central
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_torusShell_eq_sum_mul_torusShellArray_of_shellRecurrence_of_central (solution)
