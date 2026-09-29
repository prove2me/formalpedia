-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_invariant_notMem_of_endChartPole_of_rigidChart_of_eq_levelH_inf_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/3d408999-3ccc-59d8-92a6-3116593fd9f9

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff

import Theorems.Thm_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_ValuationSubring_forall_monic_aeval_not_mem_maximalIdeal_iff_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_invariant_notMem_of_endChartPole_of_rigidChart_of_eq_levelH_inf_ker
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 0
set_option maxHeartbeats 0

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace S3C4Pernode

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section PartB

variable (G : Subgroup (K ≃ₐ[k] K))
  (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
  (Õ : Subring K) [IsLocalRing ↥Õ] (hBÕ : B ≤ Õ)
  (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)

include hBG hBÕ hloc

end PartB

end S3C4Pernode

namespace S3C4Glue

open IsLocalRing Polynomial

@[reducible] noncomputable def traceNode {k₀ : Type} [Field k₀] {Kℓ : Type} [Field Kℓ] [Algebra k₀ Kℓ]
    (K₀ : IntermediateField k₀ Kℓ) (O : Subring Kℓ) : Subring ↥K₀ :=
  O.comap (algebraMap ↥K₀ Kℓ)

theorem mem_traceNode {k₀ : Type} [Field k₀] {Kℓ : Type} [Field Kℓ] [Algebra k₀ Kℓ]
    (K₀ : IntermediateField k₀ Kℓ) (O : Subring Kℓ) (f : ↥K₀) :
    f ∈ traceNode K₀ O ↔ (f : Kℓ) ∈ O := Iff.rfl

theorem isUnit_mk_iff {K : Type} [Field K] (O : Subring K) (x : K) (hx : x ∈ O) :
    IsUnit (⟨x, hx⟩ : ↥O) ↔ ∃ y : K, y ∈ O ∧ x * y = 1 := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨((u⁻¹ : (↥O)ˣ) : ↥O), ((u⁻¹ : (↥O)ˣ) : ↥O).2, ?_⟩
    have h := congrArg (fun z : ↥O => (z : K)) u.mul_inv
    rw [hu] at h
    simpa using h
  · rintro ⟨y, hy, hxy⟩
    exact IsUnit.of_mul_eq_one (b := (⟨y, hy⟩ : ↥O)) (Subtype.ext hxy)

theorem mem_maximalIdeal_iff_lt {K : Type} [Field K] (V : ValuationSubring K) (x : K) (hx : x ∈ V) :
    (⟨x, hx⟩ : ↥V) ∈ maximalIdeal ↥V ↔ V.valuation x < 1 :=
  V.valuation_lt_one_iff ⟨x, hx⟩

theorem exists_valuationSubring_extension {k K : Type} [Field k] [Field K] [Algebra k K]
    (K₀ : IntermediateField k K) (V₀ : ValuationSubring ↥K₀) :
    ∃ V : ValuationSubring K, (∀ f : ↥K₀, f ∈ V₀ ↔ (f : K) ∈ V) ∧
      (∀ (f : ↥K₀) (hf : f ∈ V₀) (hf' : (f : K) ∈ V),
        (⟨f, hf⟩ : ↥V₀) ∈ maximalIdeal ↥V₀ ↔ (⟨(f : K), hf'⟩ : ↥V) ∈ maximalIdeal ↥V) := by
  classical

  set A : Subring K := V₀.toSubring.map (algebraMap ↥K₀ K) with hA
  have hmemA : ∀ x : K, x ∈ A ↔ ∃ f : ↥K₀, f ∈ V₀ ∧ (f : K) = x := by
    intro x
    rw [hA, Subring.mem_map]
    simp only [ValuationSubring.mem_toSubring, IntermediateField.algebraMap_apply]

  set I : Ideal ↥A := Ideal.span {a : ↥A | ∃ (f : ↥K₀) (hf : f ∈ V₀), (⟨f, hf⟩ : ↥V₀) ∈ maximalIdeal ↥V₀ ∧ (f : K) = (a : K)} with hI

  have hinj : Function.Injective (algebraMap ↥K₀ K) := (algebraMap ↥K₀ K).injective
  let e : ↥V₀ →+* ↥A :=
    { toFun := fun f => ⟨((f : ↥K₀) : K), (hmemA _).mpr ⟨f, f.2, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have he : ∀ f : ↥V₀, ((e f : ↥A) : K) = ((f : ↥K₀) : K) := fun _ => rfl
  have hesurj : Function.Surjective e := by
    intro a
    have hob1 := (hmemA a).mp a.2
    obtain ⟨f, hf, hfa⟩ := hob1
    exact ⟨⟨f, hf⟩, Subtype.ext hfa⟩
  have heinj : Function.Injective e := by
    intro a b hab
    have h1 : ((a : ↥K₀) : K) = ((b : ↥K₀) : K) := by rw [← he, ← he, hab]
    exact Subtype.ext (Subtype.ext h1)

  have hIle : I ≤ (maximalIdeal ↥V₀).map e := by
    rw [hI, Ideal.span_le]
    rintro a ⟨f, hf, hm, hfa⟩
    have : a = e ⟨f, hf⟩ := Subtype.ext (by rw [he]; exact hfa.symm)
    rw [this]
    exact Ideal.mem_map_of_mem _ hm
  have hItop : I ≠ ⊤ := by
    intro htop
    have h1 : (maximalIdeal ↥V₀).map e = ⊤ := top_le_iff.mp (htop ▸ hIle)
    have h2 : (1 : ↥A) ∈ (maximalIdeal ↥V₀).map e := h1 ▸ Submodule.mem_top
    rw [Ideal.mem_map_iff_of_surjective e hesurj] at h2
    obtain ⟨x, hx, hx1⟩ := h2
    have : x = 1 := heinj (by rw [hx1, map_one])
    rw [this] at hx
    exact (maximalIdeal.isMaximal ↥V₀).ne_top (Ideal.eq_top_of_isUnit_mem _ hx isUnit_one)
  have hob2 := Ideal.image_subset_nonunits_valuationSubring I hItop
  obtain ⟨V, hAV, hIV⟩ := hob2

  have hsub : ∀ f : ↥K₀, f ∈ V₀ → (f : K) ∈ V := fun f hf => hAV ((hmemA _).mpr ⟨f, hf, rfl⟩)
  have hmax : ∀ (f : ↥K₀) (hf : f ∈ V₀), (⟨f, hf⟩ : ↥V₀) ∈ maximalIdeal ↥V₀ → V.valuation (f : K) < 1 := by
    intro f hf hm
    have ha : (⟨(f : K), (hmemA _).mpr ⟨f, hf, rfl⟩⟩ : ↥A) ∈ I := by
      rw [hI]
      exact Ideal.subset_span ⟨f, hf, hm, rfl⟩
    have := hIV ⟨_, ha, rfl⟩
    exact (V.mem_nonunits_iff).mp this
  refine ⟨V, ?_, ?_⟩
  · intro f
    refine ⟨hsub f, fun hfV => ?_⟩

    by_contra hf
    have hf0 : f ≠ 0 := fun h0 => hf (h0 ▸ V₀.zero_mem)
    have hinv : f⁻¹ ∈ V₀ := by
      rcases V₀.mem_or_inv_mem f with h | h
      · exact (hf h).elim
      · exact h
    have hinvm : (⟨f⁻¹, hinv⟩ : ↥V₀) ∈ maximalIdeal ↥V₀ := by
      rw [mem_maximalIdeal_iff_lt]
      rcases V₀.valuation_lt_one_or_eq_one ⟨f⁻¹, hinv⟩ with h | h
      · exact h
      · exfalso
        apply hf
        have hu : IsUnit (⟨f⁻¹, hinv⟩ : ↥V₀) := (V₀.valuation_eq_one_iff _).mpr h
        obtain ⟨y, hy, hy1⟩ : ∃ y : ↥K₀, y ∈ V₀ ∧ f⁻¹ * y = 1 := by
          obtain ⟨u, hu⟩ := hu
          refine ⟨((u⁻¹ : (↥V₀)ˣ) : ↥V₀), ((u⁻¹ : (↥V₀)ˣ) : ↥V₀).2, ?_⟩
          have h := congrArg (fun z : ↥V₀ => (z : ↥K₀)) u.mul_inv
          rw [hu] at h
          simpa using h
        have : y = f := by
          have := eq_inv_of_mul_eq_one_right hy1
          rw [this, inv_inv]
        exact this ▸ hy
    have h1 := hmax _ hinv hinvm
    have h2 : V.valuation (f : K) ≤ 1 := (V.valuation_le_one_iff _).mpr hfV
    have h3 : V.valuation ((f⁻¹ : ↥K₀) : K) * V.valuation ((f : ↥K₀) : K) = 1 := by
      rw [← map_mul, ← Subsemiring.coe_mul]
      push_cast
      rw [inv_mul_cancel₀ (by exact_mod_cast hf0 : ((f : ↥K₀) : K) ≠ 0), map_one]
    have h4 : V.valuation ((f⁻¹ : ↥K₀) : K) * V.valuation ((f : ↥K₀) : K) < 1 :=
      mul_lt_one_of_lt_of_le h1 h2
    rw [h3] at h4
    exact lt_irrefl _ h4
  · intro f hf hf'
    constructor
    · intro hm
      rw [mem_maximalIdeal_iff_lt]
      exact hmax f hf hm
    · intro hm

      rw [mem_maximalIdeal_iff_lt] at hm
      by_contra hnm
      have hu : IsUnit (⟨f, hf⟩ : ↥V₀) := by
        rcases V₀.valuation_lt_one_or_eq_one ⟨f, hf⟩ with h | h
        · exact (hnm ((mem_maximalIdeal_iff_lt V₀ f hf).mpr h)).elim
        · exact (V₀.valuation_eq_one_iff _).mpr h
      obtain ⟨u, hu⟩ := hu
      have hinv : (((u⁻¹ : (↥V₀)ˣ) : ↥V₀) : ↥K₀) ∈ V₀ := ((u⁻¹ : (↥V₀)ˣ) : ↥V₀).2
      have hK : (f : K) * ((((u⁻¹ : (↥V₀)ˣ) : ↥V₀) : ↥K₀) : K) = 1 := by
        have h := congrArg (fun z : ↥V₀ => ((z : ↥K₀) : K)) u.mul_inv
        rw [hu] at h
        simpa using h
      have hv1 : V.valuation ((((u⁻¹ : (↥V₀)ˣ) : ↥V₀) : ↥K₀) : K) ≤ 1 :=
        (V.valuation_le_one_iff _).mpr (hsub _ hinv)
      have := mul_lt_one_of_lt_of_le hm hv1
      rw [← map_mul, hK, map_one] at this
      exact lt_irrefl _ this

theorem mem_maximalIdeal_comap_algEquiv_iff {k K : Type} [Field k] [Field K] [Algebra k K]
    (τ : K ≃ₐ[k] K) (V : ValuationSubring K) (x : K) (hx : x ∈ V.comap (τ : K →+* K)) (hx' : τ x ∈ V) :
    (⟨x, hx⟩ : ↥(V.comap (τ : K →+* K))) ∈ maximalIdeal ↥(V.comap (τ : K →+* K)) ↔
      (⟨τ x, hx'⟩ : ↥V) ∈ maximalIdeal ↥V := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  have key : ∀ (y : K) (hy : y ∈ V.comap (τ : K →+* K)) (hy' : τ y ∈ V),
      IsUnit (⟨y, hy⟩ : ↥(V.comap (τ : K →+* K))) ↔ ∃ z : K, τ z ∈ V ∧ y * z = 1 := by
    intro y hy hy'
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨((u⁻¹ : (↥(V.comap (τ : K →+* K)))ˣ) : ↥(V.comap (τ : K →+* K))), ?_, ?_⟩
      · exact ((u⁻¹ : (↥(V.comap (τ : K →+* K)))ˣ) : ↥(V.comap (τ : K →+* K))).2
      · have h := congrArg (fun z : ↥(V.comap (τ : K →+* K)) => (z : K)) u.mul_inv
        rw [hu] at h
        simpa using h
    · rintro ⟨z, hz, hyz⟩
      exact IsUnit.of_mul_eq_one (b := (⟨z, hz⟩ : ↥(V.comap (τ : K →+* K)))) (Subtype.ext hyz)
  rw [key x hx hx']
  constructor
  · rintro ⟨z, hz, hxz⟩
    exact IsUnit.of_mul_eq_one (b := (⟨τ z, hz⟩ : ↥V)) (Subtype.ext (by
      show τ x * τ z = 1
      rw [← map_mul, hxz, map_one]))
  · rintro ⟨u, hu⟩
    refine ⟨τ.symm (((u⁻¹ : (↥V)ˣ) : ↥V) : K), ?_, ?_⟩
    · show τ (τ.symm _) ∈ V
      rw [AlgEquiv.apply_symm_apply]
      exact ((u⁻¹ : (↥V)ˣ) : ↥V).2
    · apply τ.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, map_one]
      have h := congrArg (fun z : ↥V => (z : K)) u.mul_inv
      rw [hu] at h
      simpa using h

theorem mem_valuationSubring_of_isIntegral {K : Type} [Field K] {R : Type} [CommRing R] [Algebra R K]
    (V : ValuationSubring K) (S : Set K) (hS : ∀ s : K, s ∈ S → s ∈ V) (hR : ∀ r : R, algebraMap R K r ∈ V)
    (x : K) (hx : IsIntegral ↥(Algebra.adjoin R S) x) : x ∈ V := by
  have hle : ∀ z : K, z ∈ Algebra.adjoin R S → z ∈ V := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz => exact hS z hz
    | algebraMap r => exact hR r
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  have hT : ∀ z : K, z ∈ V.valuation.integer ↔ z ∈ V := by
    intro z
    rw [ValuationSubring.integer_valuation]
    exact V.mem_toSubring z
  let φ : ↥(Algebra.adjoin R S) →+* ↥(V.valuation.integer) :=
    { toFun := fun z => ⟨(z : K), (hT _).mpr (hle z z.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hx' : IsIntegral ↥(V.valuation.integer) x :=
    IsIntegral.map_of_comp_eq (R := ↥(Algebra.adjoin R S)) (S := K) (T := ↥(V.valuation.integer)) (U := K)
      φ (RingHom.id K) (by ext z; rfl) hx
  exact (hT x).mp ((Valuation.integer.integers V.valuation).mem_of_integral hx')

theorem jsharp_package
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ]
    [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ) (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (jℓ ≠ 0)] :
    ∃ (hjK : (coeffEmb ↥k₀ jq) ∈ Kℓ),
      (⟨_, hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ ∧
      ∀ z : ↥Kℓ, z ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ →
        IsIntegral ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({(⟨_, hjK⟩ : ↥Kℓ)} : Set ↥Kℓ)) z := by
  have hjK : (coeffEmb ↥k₀ jq) ∈ Kℓ := hjℓ ▸ jℓ.2
  have ej : (⟨_, hjK⟩ : ↥Kℓ) = jℓ := Subtype.ext hjℓ.symm
  refine ⟨hjK, ?_, ?_⟩
  · rw [ej]; exact (jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ).2
  · intro z hz
    rw [ej]
    exact (mem_chartAlg_iff _ _).mp hz

theorem C3aux_exists_emb (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (m : ℕ) [NeZero m]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / m) := by
  haveI hQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.isAlgebraic ℚ
    convert h
    rfl
    rfl
  haveI : Algebra.IsAlgebraic ℚ ↥k₀ :=
    Algebra.IsAlgebraic.of_injective (k₀.val) (k₀.val).toRingHom.injective
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic m ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hξ (Nat.pos_of_ne_zero (NeZero.ne m))).symm
  have hroot : Complex.exp (2 * Real.pi * Complex.I / m) ∈ (minpoly ℚ ξ).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero m ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp m (NeZero.ne m))).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ξ] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

open IsLocalRing

open IsLocalRing

open IsLocalRing

end S3C4Glue

namespace S3C4Glue

open IsLocalRing

end S3C4Glue

open S3C4Glue in

theorem S3C4Glue.prod_not_mem_of_forall_not_mem {K : Type} [Field K] {ι : Type} [Fintype ι] [Nonempty ι]
    (V : ValuationSubring K) (x : ι → K) (hx : ∀ i, x i ∉ V) : (∏ i, x i) ∉ V := by
  classical
  intro hmem
  have hx0 : ∀ i, x i ≠ 0 := fun i h0 => hx i (by rw [h0]; exact V.zero_mem)
  have hinv : ∀ i, (x i)⁻¹ ∈ V := fun i => (V.mem_or_inv_mem (x i)).resolve_left (hx i)
  have hinvm : ∀ i, (⟨(x i)⁻¹, hinv i⟩ : ↥V) ∈ maximalIdeal ↥V := by
    intro i
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hob78 := (isUnit_mk_iff V.toSubring _ (hinv i)).mp hu
    obtain ⟨y, hy, hxy⟩ := hob78
    apply hx i
    have : y = x i := by
      have := eq_inv_of_mul_eq_one_right hxy
      rw [this, inv_inv]
    rw [← this]; exact hy

  have hob79 := ‹Nonempty ι›
  obtain ⟨i₀⟩ := hob79
  have hprodinv : (∏ i, (x i)⁻¹) ∈ V := prod_mem (fun i _ => hinv i)
  have hprodm : (⟨∏ i, (x i)⁻¹, hprodinv⟩ : ↥V) ∈ maximalIdeal ↥V := by
    have heq : (⟨∏ i, (x i)⁻¹, hprodinv⟩ : ↥V) = ∏ i, (⟨(x i)⁻¹, hinv i⟩ : ↥V) := by
      apply Subtype.ext; push_cast; rfl
    rw [heq, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
    exact Ideal.mul_mem_right _ _ (hinvm i₀)

  have hne : (∏ i, x i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hx0 i)
  have hunit : IsUnit (⟨∏ i, (x i)⁻¹, hprodinv⟩ : ↥V) := by
    refine (isUnit_mk_iff V.toSubring _ hprodinv).mpr ⟨∏ i, x i, hmem, ?_⟩
    rw [Finset.prod_inv_distrib, inv_mul_cancel₀ hne]
  exact ((IsLocalRing.mem_maximalIdeal _).mp hprodm) hunit

open S3C4Glue in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ) (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (jℓ ≠ 0)]
    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hy : y.IsMaximal)
    (hϖy : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) →+* Ω), RingHom.ker φ = y → φ (jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∈ ModularCurve.ssJSet q Ω)

    (hover :
    (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
          ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
      ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ)
        (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
      ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
        (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
            algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y))
    (hjK : ModularCurve.jqNModC ↥k₀ q ∈ Kℓ)
    (hjC : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha₀y : (⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ), hjC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) a₀ ∈ y)
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q)
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)) (hGfin : Finite ↥G)
    (hGatt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ)
    (K₀ : IntermediateField ↥k₀ ↥Kℓ) (hK₀ : K₀ = IntermediateField.fixedField G)
    (Õ : Subring ↥Kℓ) (O : Subring ↥K₀) (hOdef : O = Õ.comap (algebraMap ↥K₀ ↥Kℓ))
    (Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (hBxG : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ Bx → σ f ∈ Bx)
    (hRN9 : (∃ b : ↥Kℓ, b ∈ Bx ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
                (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                    ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                      (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                  (∃ f : ↥Kℓ, f ∈ Õ ∧ f ∉ V) → b ∉ V))) :
    (∃ b : ↥K₀, b ∈ Bx.toSubring.comap (algebraMap ↥K₀ ↥Kℓ) ∧ ∀ V : ValuationSubring ↥K₀,
                  (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ V) →
                  (∀ hπV : algebraMap ↥k₀ ↥K₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  ∀ (hjK' : (coeffEmb ↥k₀ jq) ∈ Kℓ) (hjF : (⟨(coeffEmb ↥k₀ jq), hjK'⟩ : ↥Kℓ) ∈ K₀) (hjV : (⟨_, hjF⟩ : ↥K₀) ∈ V),
                    (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                      ∀ hp : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p.map (algebraMap ↥k₀ ↥K₀)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                  (∃ f : ↥K₀, f ∈ O ∧ f ∉ V) → b ∉ V) := by
  classical
  subst hOdef
  haveI := hGfin
  haveI : Fintype ↥G := Fintype.ofFinite ↥G
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hfixK : ∀ x : ↥Kℓ, x ∈ K₀ ↔ ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ x = x := by
    intro x; rw [hK₀, IntermediateField.mem_fixedField_iff]
  have hob80 := S3C4Glue.C3aux_exists_emb k₀ q ξ hξ
  obtain ⟨ι, hι'⟩ := hob80
  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q) := ⟨ι, hι'⟩

  have hCG : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → ∀ f : ↥Kℓ, f ∈ (chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) → σ f ∈ (chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) := by
    intro σ hσ f hf
    have hob81 := hGatt σ hσ
    obtain ⟨γ, -, h0, hatt⟩ := hob81
    exact ModularCurve.FullLevel.map_mem_chartAlgFin_of_isLevelAutAt q M' ↥k₀ q ξ ⟨ι, hι'⟩ Kℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) jℓ hjℓ H₁ γ⁻¹ σ hatt f hf
  have hob82 := jsharp_package q M' A k₀ Kℓ jℓ hjℓ
  obtain ⟨hjKs, hjCs, hint⟩ := hob82

  obtain ⟨b, hbBx, hb⟩ := hRN9
  set Nb : ↥Kℓ := ∏ σ : ↥G, (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) b with hNb
  have hNbBx : Nb ∈ Bx := prod_mem (fun σ _ => hBxG σ σ.2 b hbBx)
  have hNbfix : ∀ ρ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ρ ∈ G → ρ Nb = Nb := by
    intro ρ hρ
    rw [hNb, map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨ρ, hρ⟩ : ↥G)) _ _ (fun σ => by simp [AlgEquiv.mul_apply])
  have hNbK₀ : Nb ∈ K₀ := (hfixK _).mpr hNbfix
  refine ⟨⟨Nb, hNbK₀⟩, hNbBx, ?_⟩
  intro V₀ hconst hπV₀ hjK' hjF hjV₀ htrans hfO hNbV₀
  obtain ⟨f, hfO, hfV₀⟩ := hfO

  have hob83 := exists_valuationSubring_extension K₀ V₀
  obtain ⟨V, hVK₀, hVmax⟩ := hob83

  have hconstV : ∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x := by
    intro x
    have h1 : algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ algebraMap ↥k₀ ↥K₀ x ∈ V₀ := (hVK₀ (algebraMap ↥k₀ ↥K₀ x)).symm
    rw [h1, ← hconst]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hAV : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ V := by
    intro a; rw [IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]; exact (hconstV _).mpr ⟨a, rfl⟩

  have hπeq : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ = ((algebraMap ↥k₀ ↥K₀ π₀ : ↥K₀) : ↥Kℓ) := IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ ⟨π₀, hπ⟩
  have hπV₀' : algebraMap ↥k₀ ↥K₀ π₀ ∈ V₀ := (hconst π₀).mp hπ
  have hπVm : ∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨_, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V := by
    intro hϖV
    have h1 := (hVmax _ hπV₀' (hπeq ▸ hϖV)).mp (hπV₀ hπV₀')
    have : (⟨_, hϖV⟩ : ↥V) = ⟨_, hπeq ▸ hϖV⟩ := Subtype.ext hπeq
    rw [this]; exact h1
  have hmV : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), a ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) → (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a, hAV a⟩ : ↥V) ∈ maximalIdeal ↥V := by
    intro a ha
    rw [hunif, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    have : (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ (⟨π₀, hπ⟩ * c), hAV _⟩ : ↥V) = ⟨_, hAV ⟨π₀, hπ⟩⟩ * ⟨_, hAV c⟩ :=
      Subtype.ext (map_mul (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ) ⟨π₀, hπ⟩ c)
    rw [this]
    exact Ideal.mul_mem_right _ _ (hπVm (hAV _))

  have hjsK₀ : (⟨_, hjKs⟩ : ↥Kℓ) ∈ K₀ := hjF
  have hjsV : (⟨(coeffEmb ↥k₀ jq), hjKs⟩ : ↥Kℓ) ∈ V := (hVK₀ ⟨_, hjF⟩).mp hjV₀
  have hCV : ∀ z : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (z : ↥Kℓ) ∈ V := fun z =>
    mem_valuationSubring_of_isIntegral V {(⟨_, hjKs⟩ : ↥Kℓ)} (fun s hs => by rw [Set.mem_singleton_iff.mp hs]; exact hjsV) hAV _ (hint z z.2)

  have hjstr : ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic → ∀ hp : Polynomial.aeval (⟨_, hjKs⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
      (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V := by
    intro p hpm hp hm
    set p₀ : Polynomial ↥k₀ := p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀) with hp₀
    have hp₀m : p₀.Monic := hpm.map _
    have hp₀A : ∀ i : ℕ, ((p₀.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A := by
      intro i; rw [hp₀, Polynomial.coeff_map]; exact (p.coeff i).2
    have heval : (((Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p₀.map (algebraMap ↥k₀ ↥K₀)) : ↥K₀) : ↥Kℓ)) =
        Polynomial.aeval (⟨_, hjKs⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) := by
      change algebraMap ↥K₀ ↥Kℓ (Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p₀.map (algebraMap ↥k₀ ↥K₀))) = _
      rw [← Polynomial.aeval_algebraMap_apply, Polynomial.aeval_map_algebraMap, hp₀, Polynomial.aeval_map_algebraMap]
      rw [Polynomial.aeval_map_algebraMap]
      rfl
    have hpV₀ : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p₀.map (algebraMap ↥k₀ ↥K₀)) ∈ V₀ := by
      rw [hVK₀, heval]; exact hp
    apply htrans p₀ hp₀m hp₀A hpV₀
    rw [hVmax _ hpV₀ (heval.symm ▸ hp)]
    have : (⟨_, heval.symm ▸ hp⟩ : ↥V) = ⟨_, hp⟩ := Subtype.ext heval
    rw [this]; exact hm

  have hfÕ : (f : ↥Kℓ) ∈ Õ := (mem_traceNode K₀ Õ f).mp hfO
  have hfV : (f : ↥Kℓ) ∉ V := fun h => hfV₀ ((hVK₀ f).mpr h)

  have hjℓC : (jℓ : ↥Kℓ) ∈ (chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) := by
    show IsIntegral _ _
    exact isIntegral_algebraMap (R := ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({(jℓ : ↥Kℓ)} : Set ↥Kℓ))) (A := ↥Kℓ)
      (x := ⟨jℓ, Algebra.self_mem_adjoin_singleton ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (jℓ : ↥Kℓ)⟩)
  have hjsfix : ∀ σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, σ ∈ G → σ (⟨_, hjKs⟩ : ↥Kℓ) = ⟨_, hjKs⟩ := (hfixK _).mp hjF
  have hσb : ∀ σ : ↥G, (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) b ∉ V := by
    intro σ hσbV
    set τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ := (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) with hτ
    have hmemc : ∀ x : ↥Kℓ, x ∈ V.comap (τ : ↥Kℓ →+* ↥Kℓ) ↔ τ x ∈ V := fun x => Iff.rfl
    have hτA : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), τ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a := by
      intro a; rw [IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]; exact τ.commutes _

    let τA : ↥Kℓ →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] ↥Kℓ :=
      { toRingHom := (τ : ↥Kℓ →+* ↥Kℓ), commutes' := hτA }
    have hτA_apply : ∀ x : ↥Kℓ, τA x = τ x := fun _ => rfl
    have hyx : IsIntegral ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({τ (jℓ : ↥Kℓ)} : Set ↥Kℓ)) (⟨_, hjKs⟩ : ↥Kℓ) := by
      have h0 : IsIntegral ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({(jℓ : ↥Kℓ)} : Set ↥Kℓ)) (⟨_, hjKs⟩ : ↥Kℓ) := hjCs
      have hmap : (Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({(jℓ : ↥Kℓ)} : Set ↥Kℓ)).map τA = Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({τ (jℓ : ↥Kℓ)} : Set ↥Kℓ) := by
        rw [AlgHom.map_adjoin, Set.image_singleton]; rfl
      let φ : ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({(jℓ : ↥Kℓ)} : Set ↥Kℓ)) →+* ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({τ (jℓ : ↥Kℓ)} : Set ↥Kℓ)) :=
        { toFun := fun c => ⟨τ c, hmap ▸ ⟨c, c.2, rfl⟩⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun a b => Subtype.ext (by simp)
          map_zero' := Subtype.ext (by simp)
          map_add' := fun a b => Subtype.ext (by simp) }
      have hcomp : (τ : ↥Kℓ →+* ↥Kℓ).comp (algebraMap ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({(jℓ : ↥Kℓ)} : Set ↥Kℓ)) ↥Kℓ) =
          (algebraMap ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({τ (jℓ : ↥Kℓ)} : Set ↥Kℓ)) ↥Kℓ).comp φ := RingHom.ext (fun c => rfl)
      have h1 := h0.map_of_comp_eq φ (τ : ↥Kℓ →+* ↥Kℓ) hcomp
      rwa [show (τ : ↥Kℓ →+* ↥Kℓ) (⟨_, hjKs⟩ : ↥Kℓ) = ⟨_, hjKs⟩ from hjsfix τ σ.2] at h1
    have hxy : IsIntegral ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({(⟨_, hjKs⟩ : ↥Kℓ)} : Set ↥Kℓ)) (τ (jℓ : ↥Kℓ)) :=
      hint _ (hCG τ σ.2 _ hjℓC)
    have hjVσ : (jℓ : ↥Kℓ) ∈ V.comap (τ : ↥Kℓ →+* ↥Kℓ) := (hmemc _).mpr (hCV ⟨_, hCG τ σ.2 _ hjℓC⟩)
    refine hb (V.comap (τ : ↥Kℓ →+* ↥Kℓ)) ?_ ?_ hjVσ ?_ ?_ ((hmemc b).mpr hσbV)
    · intro x
      rw [hmemc, show τ (algebraMap ↥k₀ ↥Kℓ x) = algebraMap ↥k₀ ↥Kℓ x from τ.commutes x]
      exact hconstV x
    · intro hϖVσ
      rw [mem_maximalIdeal_comap_algEquiv_iff τ V _ hϖVσ ((hτA ⟨π₀, hπ⟩).symm ▸ hAV ⟨π₀, hπ⟩)]
      have : (⟨τ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩), (hτA ⟨π₀, hπ⟩).symm ▸ hAV ⟨π₀, hπ⟩⟩ : ↥V) = ⟨_, hAV ⟨π₀, hπ⟩⟩ :=
        Subtype.ext (hτA _)
      rw [this]; exact hπVm (hAV _)
    · intro p hpm hp
      have hyV : τ (jℓ : ↥Kℓ) ∈ V := (hmemc _).mp hjVσ
      have hcomm : τ (Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ))) =
          Polynomial.aeval (τ (jℓ : ↥Kℓ)) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) := by
        rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_map_algebraMap, ← hτA_apply, ← hτA_apply (jℓ : ↥Kℓ)]
        exact (Polynomial.aeval_algHom_apply τA (jℓ : ↥Kℓ) p).symm
      have htr := (ValuationSubring.forall_monic_aeval_not_mem_maximalIdeal_iff_of_isIntegral_adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ V hAV hmV
        (⟨_, hjKs⟩ : ↥Kℓ) (τ (jℓ : ↥Kℓ)) hjsV hyV hxy hyx).mp hjstr
      rw [mem_maximalIdeal_comap_algEquiv_iff τ V _ hp ((hmemc _).mp hp)]
      have hpV : Polynomial.aeval (τ (jℓ : ↥Kℓ)) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V := hcomm ▸ (hmemc _).mp hp
      have : (⟨τ (Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ))), (hmemc _).mp hp⟩ : ↥V) = ⟨_, hpV⟩ :=
        Subtype.ext hcomm
      rw [this]
      exact htr p hpm hpV
    · exact ⟨f, hfÕ, fun h => hfV (by rw [hmemc, (hfixK _).mp f.2 _ σ.2] at h; exact h)⟩

  have hNbV : Nb ∉ V := by
    rw [hNb]; exact S3C4Glue.prod_not_mem_of_forall_not_mem V _ hσb
  exact hNbV ((hVK₀ ⟨Nb, hNbK₀⟩).mp hNbV₀)

end S_ModularCurve_FullLevel_Diamond_exists_invariant_notMem_of_endChartPole_of_rigidChart_of_eq_levelH_inf_ker
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_invariant_notMem_of_endChartPole_of_rigidChart_of_eq_levelH_inf_ker (solution)
