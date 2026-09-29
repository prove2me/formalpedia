-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_mem_invariants_forall_igusaValuation_not_mem_of_rigidChart_framed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/d3028326-9bd0-55a9-8454-1bb895d7770d

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
import Definitions.Def_ModularCurve_RigidDescentHyps
import Mathlib
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ValuationSubring_forall_monic_aeval_not_mem_maximalIdeal_iff_of_isIntegral_adjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_mem_invariants_forall_igusaValuation_not_mem_of_rigidChart_framed
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 0

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace E1Kit
open IsLocalRing

theorem C3aux_exists_emb (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (m : ℕ) [NeZero m]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / m) := by
  haveI hQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.isAlgebraic ℚ
    convert h <;> first | rfl | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
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
    obtain ⟨f, hf, hfa⟩ := (hmemA a).mp a.2
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
  obtain ⟨V, hAV, hIV⟩ := Ideal.image_subset_nonunits_valuationSubring I hItop

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

theorem mul_not_mem {K : Type*} [Field K] (V : ValuationSubring K) {x y : K}
    (hx : x ∉ V) (hy : y ∉ V) : x * y ∉ V := by
  intro hxy
  have hxi : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hx
  apply hy
  have hx0 : x ≠ 0 := fun h => hx (h ▸ V.zero_mem)
  have : y = x⁻¹ * (x * y) := by field_simp
  rw [this]
  exact V.mul_mem _ _ hxi hxy

theorem prod_univ_not_mem {K : Type*} [Field K] (V : ValuationSubring K) {ι : Type*} [Fintype ι]
    [Nonempty ι] (f : ι → K) (h : ∀ i, f i ∉ V) : (∏ i, f i) ∉ V := by
  classical
  have key : ∀ s : Finset ι, s.Nonempty → (∏ i ∈ s, f i) ∉ V := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro hs; exact absurd hs Finset.not_nonempty_empty
    | insert a s ha ih =>
      intro _
      rw [Finset.prod_insert ha]
      by_cases hs' : s.Nonempty
      · exact mul_not_mem V (h a) (ih hs')
      · rw [Finset.not_nonempty_iff_eq_empty.mp hs', Finset.prod_empty, mul_one]; exact h a
  exact key Finset.univ Finset.univ_nonempty

def comapEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (V : ValuationSubring L) : (V.comap (e : K →+* L)) ≃+* V where
  toFun x := ⟨e x, x.2⟩
  invFun y := ⟨e.symm y, by show e (e.symm y) ∈ V; rw [e.apply_symm_apply]; exact y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

theorem mem_maximalIdeal_comap_iff {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (V : ValuationSubring L) (x : V.comap (e : K →+* L)) :
    x ∈ maximalIdeal (V.comap (e : K →+* L)) ↔ (comapEquiv e V x) ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact ⟨fun h => by simpa using h.map (comapEquiv e V).toRingHom,
    fun h => by simpa using h.map (comapEquiv e V).symm.toRingHom⟩

theorem apply_aeval_map {A K : Type*} [CommRing A] [Field K] (f : A →+* K) (σ : K ≃+* K)
    (hσ : ∀ a, σ (f a) = f a) (x : K) (p : Polynomial A) :
    σ (Polynomial.aeval x (p.map f)) = Polynomial.aeval (σ x) (p.map f) := by
  rw [Polynomial.coe_aeval_eq_eval, Polynomial.coe_aeval_eq_eval, Polynomial.eval_map, Polynomial.eval_map,
    show (σ : K → K) = (σ : K →+* K) from rfl, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext hσ

theorem isIntegral_of_le {A K : Type*} [CommRing A] [Field K] [Algebra A K] (B : Subalgebra A K) (V : ValuationSubring K)
    (hle : ∀ x : K, x ∈ B → x ∈ V) (y : K) (hy : IsIntegral ↥B y) : y ∈ V := by
  let f : ↥B →+* ↥V :=
    { toFun := fun x => ⟨x, hle x x.2⟩
      map_one' := rfl
      map_mul' := (fun _ _ => rfl)
      map_zero' := rfl
      map_add' := (fun _ _ => rfl) }
  have hy' : IsIntegral ↥V y :=
    hy.map_of_comp_eq f (RingHom.id K) (by ext; rfl)
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := K)).mp hy'
  rw [← hz]; exact z.2

theorem hom_aeval_map {A K L : Type*} [CommRing A] [Field K] [Field L] (f : A →+* K) (ι : K →+* L)
    (x : K) (p : Polynomial A) :
    ι (Polynomial.aeval x (p.map f)) = Polynomial.aeval (ι x) (p.map (ι.comp f)) := by
  rw [Polynomial.coe_aeval_eq_eval, Polynomial.coe_aeval_eq_eval, Polynomial.eval_map, Polynomial.eval_map,
    Polynomial.hom_eval₂]

end E1Kit

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ)
    [Fact q.Prime]
    (M' : ℕ)
    [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (π₀ : ↥k₀)
    (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (ℓ : ℕ)
    (ζ₀ : ↥k₀)
    (ϖt : ↥k₀)
    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (Ab : ValuationSubring ↥Kb)
    (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (ϖb : ↥Ab)
    (ℓ' : ℕ)
    [Fact ℓ'.Prime]
    (ξ : ↥k₀)
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ]
    [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ)
    [Fact (jℓ ≠ 0)]
    (ϖt' : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ))
    (Bt : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (Wt : ValuationSubring ↥Kℓ)
    (hBW : ∀ f : ↥Kℓ, f ∈ Bt → f ∈ Wt)
    (n : ℕ)
    (γ₀ : SL(2, ℤ))
    (τ₀ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
    (m : ℕ)
    (ζc : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hjK : ModularCurve.jqNModC ↥k₀ (q * ℓ') ∈ Kℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (ends : Finset (Subring ↥Kℓ))
    (ℱ : ModularCurve.FullLevel.RigidDescentHyps q M' A W hle R₀ s k₀ π₀ hπ ℓ ζ₀ ϖt Kb Ab hAb ϖb ℓ' ξ Kℓ jℓ ϖt' y Bt Wt hBW n γ₀ τ₀ m ζc hjK a₀ ends)
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ))
    (hG : G = Subgroup.closure {τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ})
    (K₀ : IntermediateField ↥k₀ ↥Kℓ)
    (hK₀ : K₀ = IntermediateField.fixedField G)
    (B₀ : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (hB₀ : ∀ f : ↥Kℓ, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ f = f)
    (W₀' : ValuationSubring ↥K₀)
    (hW₀' : ∀ f : ↥K₀, f ∈ W₀' ↔ ((f : ↥Kℓ)) ∈ Wt)
    :
    (∃ b : ↥K₀, (b : ↥Kℓ) ∈ B₀ ∧ ∀ V : ValuationSubring ↥K₀,
          (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ V) →
          (∀ hπV : algebraMap ↥k₀ ↥K₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
          ∀ (hjK' : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq) ∈ Kℓ) (hjF : (⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq), hjK'⟩ : ↥Kℓ) ∈ K₀) (hjV : (⟨_, hjF⟩ : ↥K₀) ∈ V),
            (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
              ∀ hp : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p.map (algebraMap ↥k₀ ↥K₀)) ∈ V,
                (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
          b ∉ V):= by
  obtain ⟨hq, hqM', hA, hW, hR₀, hdvr, hunif, hhens, hres, hκ, hℓ, hℓ3, hℓq, hℓM', hζ₀, hϖtA, hϖt, hKb, hϖb, hϖb0, hℓ'3, hℓ'q, hℓ'M, htame, hξ, hKℓ, hjℓ, hϖt', hy, hϖy, hss, hover, hOrbit, hS1, hn1, hnq, hγ₀Γ, hγ₀Γ0, hτ₀, hτ₀W, hm1, hm, hζc, hζcprim, hjC, ha₀y, hR7, hR9, hR10, hn⟩ := ℱ
  classical
  haveI hmne : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero⟩

  have hObt1 := E1Kit.C3aux_exists_emb k₀ (q * ℓ') ξ hξ
  obtain ⟨ι, hι'⟩ := hObt1
  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')) :=
    ⟨ι, by rw [hι']; simp only [Nat.cast_mul]⟩
  have hObt2 := ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ
  obtain ⟨huniq, hmul, hone⟩ := hObt2
  obtain ⟨Gfull, hGfin, hGmem⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom
      q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ
  have hex := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
      q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ hι Kℓ hKℓ

  have hGle : G ≤ Gfull := by
    rw [hG, Subgroup.closure_le]
    rintro τ ⟨γ, -, hγ0, hτ⟩
    exact (hGmem τ).mpr ⟨γ, hγ0, hτ⟩
  haveI hGfinite : Finite ↥G := by
    haveI := hGfin
    exact Finite.of_injective (Subgroup.inclusion hGle) (Subgroup.inclusion_injective hGle)
  have hGatt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G →
      ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ := by
    intro τ hτ
    rw [hG] at hτ
    refine Subgroup.closure_induction (p := fun τ _ => ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
        γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ) ?_ ?_ ?_ ?_ hτ
    · intro τ h; exact h
    · exact ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, by rw [inv_one]; exact hone 1 (Subgroup.one_mem _) (Subgroup.one_mem _)⟩
    · rintro τ σ - - ⟨γ, hγq, hγ0, hτ⟩ ⟨δ, hδq, hδ0, hσ⟩
      refine ⟨γ * δ, Subgroup.mul_mem _ hγq hδq, Subgroup.mul_mem _ hγ0 hδ0, ?_⟩
      rw [mul_inv_rev]
      exact hmul γ⁻¹ δ⁻¹ (Subgroup.inv_mem _ hγ0) (Subgroup.inv_mem _ hδ0) τ σ hτ hσ
    · rintro τ - ⟨γ, hγq, hγ0, hτ⟩
      have hObt3 := hex γ⁻¹ (Subgroup.inv_mem _ hγ0)
      obtain ⟨σ, hσ⟩ := hObt3
      rw [inv_inv] at hσ
      have h1 : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') (γ * γ⁻¹) Kℓ (τ * σ) := hmul γ⁻¹ γ (Subgroup.inv_mem _ hγ0) hγ0 τ σ hτ hσ
      rw [mul_inv_cancel] at h1
      have h2 : τ * σ = 1 := huniq 1 (Subgroup.one_mem _) _ _ h1 (hone 1 (Subgroup.one_mem _) (Subgroup.one_mem _))
      have h3 : τ⁻¹ = σ := inv_eq_of_mul_eq_one_right h2
      refine ⟨γ⁻¹, Subgroup.inv_mem _ hγq, Subgroup.inv_mem _ hγ0, ?_⟩
      rw [inv_inv, h3]; exact hσ

  obtain ⟨hR1a, hR1b, hR2a, hR2b, hR2c, hR3a, hR3b, hR3c, hR3d, hR3e, hR46, hR5a, hR5b, hR5c⟩ := hS1
  have hGBt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → ∀ f : ↥Kℓ, f ∈ Bt → τ f ∈ Bt := by
    intro τ hτ f hf
    have hObt4 := hGatt τ hτ
    obtain ⟨γ, -, hγ0, hτ'⟩ := hObt4
    exact hR5a γ hγ0 τ hτ' f hf
  haveI : Fintype ↥G := Fintype.ofFinite ↥G

  obtain ⟨bt, hbtBt, hbt⟩ := hR9
  have hbBt : (∏ σ : ↥G, (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) bt) ∈ Bt :=
    Bt.prod_mem (fun σ _ => hGBt σ σ.2 bt hbtBt)
  have hbfix : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ (∏ σ : ↥G, (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) bt) = ∏ σ : ↥G, (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) bt := by
    intro τ hτ
    rw [map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨τ, hτ⟩ : ↥G)) _ _ (fun σ => rfl)
  have hbK₀ : (∏ σ : ↥G, (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) bt) ∈ K₀ := by
    rw [hK₀]; exact (IntermediateField.mem_fixedField_iff G _).mpr (fun τ hτ => hbfix τ hτ)
  have hbB₀ : (∏ σ : ↥G, (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) bt) ∈ B₀ := (hB₀ _).mpr ⟨hbBt, hbfix⟩
  refine ⟨⟨_, hbK₀⟩, hbB₀, ?_⟩
  intro V₀ hV₀A hV₀π hjK' hjF hjV₀ hres₀ hbV₀

  obtain ⟨V, hVtr, hVmax⟩ := E1Kit.exists_valuationSubring_extension K₀ V₀
  have hbV : (∏ σ : ↥G, (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) bt) ∈ V := (hVtr ⟨_, hbK₀⟩).mp hbV₀

  have halg : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a = ((algebraMap ↥k₀ ↥K₀ (a : ↥k₀) : ↥K₀) : ↥Kℓ) :=
    fun a => IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ a
  have hAV : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ V := by
    intro a; rw [halg]; exact (hVtr _).mp ((hV₀A (a : ↥k₀)).mp a.2)
  have hπ₀V₀ : algebraMap ↥k₀ ↥K₀ π₀ ∈ V₀ := (hV₀A π₀).mp hπ
  have hπV : ∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨_, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V := by
    intro hϖV
    have hϖV' : ((algebraMap ↥k₀ ↥K₀ π₀ : ↥K₀) : ↥Kℓ) ∈ V := by rw [← halg ⟨π₀, hπ⟩]; exact hϖV
    have h := (hVmax _ hπ₀V₀ hϖV').mp (hV₀π hπ₀V₀)
    have heq : (⟨_, hϖV⟩ : ↥V) = ⟨_, hϖV'⟩ := Subtype.ext (halg ⟨π₀, hπ⟩)
    rw [heq]; exact h
  have hmV : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), a ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) → (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a, hAV a⟩ : ↥V) ∈ maximalIdeal ↥V := by
    intro a ha
    rw [hunif, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    have heq : (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ (⟨π₀, hπ⟩ * c), hAV _⟩ : ↥V) = ⟨_, hAV ⟨π₀, hπ⟩⟩ * ⟨_, hAV c⟩ :=
      Subtype.ext (map_mul _ _ _)
    rw [heq]; exact Ideal.mul_mem_right _ _ (hπV (hAV _))

  set jS : ↥Kℓ := ⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq), hjK'⟩ with hjSdef
  have hjSfix : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ jS = jS := by
    have h := hjF; rw [hK₀] at h; exact (IntermediateField.mem_fixedField_iff G _).mp h
  have hjSV : jS ∈ V := (hVtr ⟨_, hjF⟩).mp hjV₀

  have hint1 : IsIntegral ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({(jℓ : ↥Kℓ)} : Set ↥Kℓ)) jS := by
    obtain ⟨hj1, hj10, hjK2, hmemC⟩ := ModularCurve.FullLevel.qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField
      q M' ℓ' ↥k₀ Kℓ hKℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
    have hjeq : (⟨_, hj1⟩ : ↥Kℓ) = jℓ := Subtype.ext hjℓ.symm
    rw [hjeq] at hmemC
    exact hmemC

  have hint2 : IsIntegral ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({jS} : Set ↥Kℓ)) (jℓ : ↥Kℓ) := by
    obtain ⟨Φd⟩ := ModularCurve.nonempty_modularPolynomialData ℓ'
    have hsymm := ModularCurve.ModularPolynomialData.evalSymm_of_one_lt ℓ' (by omega) Φd
    have hroot : Φd.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.jqN ℓ')).toRingHom ModularCurve.jq = 0 := by
      rw [← hsymm]; exact Φd.eval_eq_zero
    have hjB : jS ∈ Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({jS} : Set ↥Kℓ) := Algebra.self_mem_adjoin_singleton ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) jS
    let φ : Polynomial ℤ →+* ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({jS} : Set ↥Kℓ)) :=
      Polynomial.eval₂RingHom (Int.castRingHom _) ⟨jS, hjB⟩
    have hφX : φ Polynomial.X = ⟨jS, hjB⟩ := by simp [φ]
    have hcomp : (Kℓ.val.toRingHom.comp ((algebraMap ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({jS} : Set ↥Kℓ)) ↥Kℓ).comp φ)) =
        (coeffEmb ↥k₀).comp (Polynomial.aeval (R := ℤ) (ModularCurve.jqN ℓ')).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        rw [show (Polynomial.C a : Polynomial ℤ) = (a : Polynomial ℤ) by rw [← Polynomial.C_eq_intCast, Int.cast_id],
          map_intCast, map_intCast]
      · rw [RingHom.comp_apply, RingHom.comp_apply, hφX, RingHom.comp_apply]
        change ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq) = coeffEmb ↥k₀ ((Polynomial.aeval (R := ℤ) (ModularCurve.jqN ℓ')).toRingHom Polynomial.X)
        rw [show (Polynomial.aeval (R := ℤ) (ModularCurve.jqN ℓ')).toRingHom Polynomial.X = ModularCurve.jqN ℓ' by simp]
        change ModularCurve.qExpand ↥k₀ ℓ' (coeffMap (algebraMap ℚ ↥k₀) jq) = coeffMap (algebraMap ℚ ↥k₀) (ModularCurve.qExpand ℚ ℓ' jq)
        rw [ModularCurve.coeffMap_qExpand]
    refine ⟨Φd.Φ.map φ, Φd.monic.map φ, ?_⟩
    apply Subtype.ext
    rw [Polynomial.eval₂_map]
    change Kℓ.val.toRingHom (Polynomial.eval₂ ((algebraMap _ ↥Kℓ).comp φ) (jℓ : ↥Kℓ) Φd.Φ) = 0
    rw [Polynomial.hom_eval₂, hcomp]
    have h0 := congrArg (coeffEmb ↥k₀) hroot
    rw [map_zero, Polynomial.hom_eval₂] at h0
    convert h0 using 2 <;> first | rfl | exact hjℓ | exact hjℓ.symm

  have IG : ∀ (V'' : ValuationSubring ↥Kℓ) (hAV'' : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ V'')
      (hmV'' : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), a ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) → (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a, hAV'' a⟩ : ↥V'') ∈ maximalIdeal ↥V'')
      (hj'' : jS ∈ V'')
      (hres'' : ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic → ∀ hp : Polynomial.aeval jS (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V'',
        (⟨_, hp⟩ : ↥V'') ∉ maximalIdeal ↥V''),
      ∃ hjℓ'' : (jℓ : ↥Kℓ) ∈ V'', ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
        ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V'', (⟨_, hp⟩ : ↥V'') ∉ maximalIdeal ↥V'' := by
    intro V'' hAV'' hmV'' hj'' hres''
    have hle : ∀ x : ↥Kℓ, x ∈ Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({jS} : Set ↥Kℓ) → x ∈ V'' := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact hj''
      | algebraMap a => exact hAV'' a
      | add y z _ _ hy hz => exact V''.add_mem _ _ hy hz
      | mul y z _ _ hy hz => exact V''.mul_mem _ _ hy hz
    have hjℓV : (jℓ : ↥Kℓ) ∈ V'' := E1Kit.isIntegral_of_le _ V'' hle _ hint2
    exact ⟨hjℓV, (ValuationSubring.forall_monic_aeval_not_mem_maximalIdeal_iff_of_isIntegral_adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ V'' hAV'' hmV''
      jS (jℓ : ↥Kℓ) hj'' hjℓV hint2 hint1).mp hres''⟩

  have hresV : ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic → ∀ hp : Polynomial.aeval jS (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
      (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V := by
    intro p hp hpV
    have hp' : (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)).Monic := hp.map _
    have hcoef : ∀ i : ℕ, (((p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)).coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A := by
      intro i; rw [Polynomial.coeff_map]; exact (p.coeff i).2
    have hval : ((Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) ((p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)).map (algebraMap ↥k₀ ↥K₀)) : ↥K₀) : ↥Kℓ) =
        Polynomial.aeval jS (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) := by
      rw [show (((Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) ((p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)).map (algebraMap ↥k₀ ↥K₀)) : ↥K₀) : ↥Kℓ)) =
          (algebraMap ↥K₀ ↥Kℓ) (Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) ((p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)).map (algebraMap ↥k₀ ↥K₀))) from rfl,
        Polynomial.map_map, E1Kit.hom_aeval_map]
      have hcomp3 : (algebraMap ↥K₀ ↥Kℓ).comp ((algebraMap ↥k₀ ↥K₀).comp (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ :=
        RingHom.ext fun a => (by rw [IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ a]; rfl)
      rw [hcomp3]
      rfl
    have hpV' : ((Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) ((p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)).map (algebraMap ↥k₀ ↥K₀)) : ↥K₀) : ↥Kℓ) ∈ V := by
      rw [hval]; exact hpV
    have hpV₀ : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) ((p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)).map (algebraMap ↥k₀ ↥K₀)) ∈ V₀ := (hVtr _).mpr hpV'
    have h1 := hres₀ _ hp' hcoef hpV₀
    intro hm; apply h1
    rw [hVmax _ hpV₀ hpV']
    have heq : (⟨_, hpV'⟩ : ↥V) = ⟨_, hpV⟩ := Subtype.ext hval
    rw [heq]; exact hm

  haveI : Nonempty ↥G := ⟨1⟩
  refine E1Kit.prod_univ_not_mem V (fun σ : ↥G => (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) bt) ?_ hbV
  intro σ hσV
  have hσA : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ((σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv : ↥Kℓ →+* ↥Kℓ) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a := by
    intro a
    show (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a
    rw [IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ a]; exact (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).commutes _
  have hσj : ((σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv : ↥Kℓ →+* ↥Kℓ) jS = jS := hjSfix σ σ.2

  have hAV' : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ V.comap ((σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv : ↥Kℓ →+* ↥Kℓ) := by
    intro a; show _ ∈ V; rw [hσA]; exact hAV a
  have hmV' : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), a ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →
      (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a, hAV' a⟩ : ↥(V.comap ((σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv : ↥Kℓ →+* ↥Kℓ))) ∈ maximalIdeal _ := by
    intro a ha
    rw [E1Kit.mem_maximalIdeal_comap_iff]
    have heq : E1Kit.comapEquiv _ V ⟨_, hAV' a⟩ = ⟨_, hAV a⟩ := Subtype.ext (hσA a)
    rw [heq]; exact hmV a ha
  have hj' : jS ∈ V.comap ((σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv : ↥Kℓ →+* ↥Kℓ) := by
    show _ ∈ V; rw [hσj]; exact hjSV
  have hres' : ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
      ∀ hp : Polynomial.aeval jS (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V.comap ((σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv : ↥Kℓ →+* ↥Kℓ),
      (⟨_, hp⟩ : ↥(V.comap ((σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv : ↥Kℓ →+* ↥Kℓ))) ∉ maximalIdeal _ := by
    intro p hp hp'
    have heqv : ((σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv : ↥Kℓ →+* ↥Kℓ) (Polynomial.aeval jS (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ))) =
        Polynomial.aeval jS (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) := by
      rw [show (((σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv : ↥Kℓ →+* ↥Kℓ) : ↥Kℓ → ↥Kℓ) = ((σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv : ↥Kℓ → ↥Kℓ) from rfl,
        E1Kit.apply_aeval_map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ) (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv hσA jS p]
      show Polynomial.aeval ((σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv jS) _ = _
      rw [show (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv jS = jS from hσj]
    have hpV : Polynomial.aeval jS (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V := by rw [← heqv]; exact hp'
    rw [E1Kit.mem_maximalIdeal_comap_iff]
    have heq : E1Kit.comapEquiv _ V ⟨_, hp'⟩ = ⟨_, hpV⟩ := Subtype.ext heqv
    rw [heq]; exact hresV p hp hpV
  obtain ⟨hjℓ', hresℓ'⟩ := IG _ hAV' hmV' hj' hres'
  refine hbt (V.comap ((σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).toRingEquiv : ↥Kℓ →+* ↥Kℓ)) ?_ ?_ hjℓ' hresℓ' hσV
  ·
    intro x
    show (σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (algebraMap ↥k₀ ↥Kℓ x) ∈ V ↔ _
    rw [(σ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ).commutes]
    constructor
    · intro h
      exact ⟨⟨x, (hV₀A x).mpr ((hVtr (algebraMap ↥k₀ ↥K₀ x)).mpr h)⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact (hVtr _).mp ((hV₀A _).mp a.2)
  ·
    intro hϖ
    rw [E1Kit.mem_maximalIdeal_comap_iff]
    have hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V := by
      have h := hϖ; change _ ∈ V at h; rwa [hσA] at h
    have heq : E1Kit.comapEquiv _ V ⟨_, hϖ⟩ = ⟨_, hϖV⟩ := Subtype.ext (hσA _)
    rw [heq]; exact hπV hϖV

end S_ModularCurve_FullLevel_AuxLevel_exists_mem_invariants_forall_igusaValuation_not_mem_of_rigidChart_framed
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_mem_invariants_forall_igusaValuation_not_mem_of_rigidChart_framed (solution)
