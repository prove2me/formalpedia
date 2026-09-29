-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.AuxLevel.exists_mem_invariants_forall_igusaValuation_not_mem_of_rigidChart_linkedScalars_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/060e0d90-90d3-51a5-8704-df3baa285404

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
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Mathlib
import Theorems.Thm_ModularCurve_FullLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
import Theorems.Thm_ValuationSubring_forall_monic_aeval_not_mem_maximalIdeal_iff_of_isIntegral_adjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_exists_mem_invariants_forall_igusaValuation_not_mem_of_rigidChart_linkedScalars_of_eq_two_of_dvd

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 51200000

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

attribute [local instance 10000] SubalgebraClass.toAlgebra Algebra.toSMul Algebra.toModule

theorem solution
    (q : ℕ)
    [Fact q.Prime]
    (hq2 : q = 2)
    (M' : ℕ)
    [NeZero M']

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
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
    (ξ : ↥k₀)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
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
    (hjK : ModularCurve.jqNModC ↥k₀ q ∈ Kℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (ends : Finset (Subring ↥Kℓ))
    (hqM' : ¬ q ∣ M')
    (hA : A.LiesOverPrime q)
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
          ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue ↥A) y)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
        Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (hℓ : ℓ.Prime)
    (hℓ3 : 3 ≤ ℓ)
    (hℓq : ℓ ≠ q)
    (hℓM' : ¬ ℓ ∣ M')
    (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))
    (hKb : Kb = ⊥)
    (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb})
    (hϖb0 : ϖb ≠ 0)
    (htame : IsUnit (((ℓg - 1) / 2 : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hξ : IsPrimitiveRoot ξ q)
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq)
    (hϖt' : (ϖt' : ↥k₀) = ϖt)
    (hy : y.IsMaximal)
    (hϖy : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) →+* Ω), RingHom.ker φ = y → φ (jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∈ ModularCurve.ssJSet q Ω)
    (hover : (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
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
    (hOrbit : ∀ y' : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), y'.IsMaximal →
        algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y' →
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
                  algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y') →
        ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q) (_ : γ ∈ CongruenceSubgroup.Gamma0 M')
          (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ),
          ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ ∧
          (∀ f : ↥Kℓ, f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ →
            τ f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∧
          (∀ (f : ↥Kℓ) (hf : f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
            (hf' : τ f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
            (⟨f, hf⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y ↔ (⟨τ f, hf'⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'))
    (hS1 :
        chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ ≤ Bt ∧
        (∀ f : ↥Kℓ, ∃ g h : ↥Bt, (h : ↥Kℓ) ≠ 0 ∧ f * (h : ↥Kℓ) = (g : ↥Kℓ)) ∧

        Algebra.FormallySmooth ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ∧ Algebra.FinitePresentation ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ∧
        Ring.KrullDimLE 1 (↥Bt ⧸ Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩}) ∧

        (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wt ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
        maximalIdeal ↥Wt = Ideal.span {(⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hBW _ (Bt.algebraMap_mem ⟨π₀, hπ⟩)⟩ : ↥Wt)} ∧
        IsDiscreteValuationRing ↥Wt ∧
        (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ↔
          ∃ hb : (b : ↥Kℓ) ∈ Wt, (⟨(b : ↥Kℓ), hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
        (∀ f : ↥Kℓ, f ∈ Wt ↔ ∃ g h : ↥Bt, (⟨(h : ↥Kℓ), hBW _ h.2⟩ : ↥Wt) ∉ maximalIdeal ↥Wt ∧ f * (h : ↥Kℓ) = (g : ↥Kℓ)) ∧

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),
          ∃ (ρ : ↥Bt →+* DrinfeldCurve.CoordRing q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),
            Function.Surjective ρ ∧
            (∀ b : ↥Bt, ρ b = 0 ↔ (⟨(b : ↥Kℓ), hBW _ b.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
            (∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ρ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt a) = algebraMap (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (DrinfeldCurve.CoordRing q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) a)) ∧
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) →
                ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                  (∀ (b : ↥Bt) (hb : τ (b : ↥Kℓ) ∈ Bt), ρ ⟨τ (b : ↥Kℓ), hb⟩ = DrinfeldCurve.hAction q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨_, hmem⟩ (ρ b)) ∧
                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥Kℓ, τ k = k) → c ≠ 1) ∧

                  (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
                      (_ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ'⁻¹ Kℓ τ') (_ : ∀ f : ↥Kℓ, f ∈ Wt ↔ τ' f ∈ Wt)
                      (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c) ∈ DrinfeldCurve.hSubgroup q),
                    ∀ (b : ↥Bt) (hb : τ' (b : ↥Kℓ) ∈ Bt), ρ ⟨τ' (b : ↥Kℓ), hb⟩ = DrinfeldCurve.hAction q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨_, hmem'⟩ (ρ b)))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
            ∀ f : ↥Kℓ, f ∈ Bt → τ f ∈ Bt) ∧
        (∀ Q : Ideal ↥Bt, Q.IsPrime → algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ ∈ Q →
          ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
            ∃ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ ∧
              ∀ b : ↥Bt, (⟨(b : ↥Kℓ), hBW _ b.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt → τ (b : ↥Kℓ) ∈ Bt ∧ ∀ hb : τ (b : ↥Kℓ) ∈ Bt, (⟨τ (b : ↥Kℓ), hb⟩ : ↥Bt) ∈ Q) ∧
        (∀ b : ↥Bt, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              ∀ hb : τ (b : ↥Kℓ) ∈ Bt, (⟨τ (b : ↥Kℓ), hBW _ hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) →
          algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ ∣ b))
    (hn1 : 1 ≤ n)
    (hnq : n ∣ q + 1)
    (hγ₀Γ : γ₀ ∈ CongruenceSubgroup.Gamma q)
    (hγ₀Γ0 : γ₀ ∈ CongruenceSubgroup.Gamma0 M')
    (hτ₀ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ₀⁻¹ Kℓ τ₀)
    (hτ₀W : ∀ f : ↥Kℓ, f ∈ Wt ↔ τ₀ f ∈ Wt)
    (hm1 : 1 ≤ m)
    (hm : ∃ w : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), IsUnit w ∧ ⟨π₀, hπ⟩ ^ m = ϖt' * w)
    (hζc : ζc ^ n = 1)
    (hζcprim : ∀ k : ℕ, 0 < k → k < n → IsUnit (ζc ^ k - 1))
    (hjC : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
    (ha₀y : (⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ), hjC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) a₀ ∈ y)
    (hR7 : (∀ f : ↥Kℓ, f ∈ Bt → (τ₀ ^ n) f = f) ∧
          (∀ k : ℕ, 0 < k → k < n → ∃ f : ↥Kℓ, f ∈ Bt ∧ (τ₀ ^ k) f ≠ f) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) → ∃ k : ℕ, k < n ∧ ∀ f : ↥Kℓ, f ∈ Bt → τ f = (τ₀ ^ k) f) ∧
          ends.card = q + 1 ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) → ∀ O ∈ ends, ∃ O' ∈ ends, ∀ f : ↥Kℓ, f ∈ O ↔ τ f ∈ O') ∧
          (∀ O ∈ ends, ∀ O' ∈ ends, ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (_ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ),
            (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) ∧ ∀ f : ↥Kℓ, f ∈ O ↔ τ f ∈ O') ∧
          (∀ O ∈ ends, ∀ f : ↥Kℓ, f ∈ O ↔ τ₀ f ∈ O) ∧
          (∀ O ∈ ends, ∀ O' ∈ ends, O ≠ O' → ∃ (f : ↥Kℓ) (hf : f ∈ O) (hf' : f ∈ O'),
            ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) ∧

          (∃ Bc : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ, Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bc ∧
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                ∀ f : ↥Kℓ, f ∈ Bc → τ f ∈ Bc) ∧
            ∀ O ∈ ends, (∀ f : ↥Kℓ, f ∈ Bc → f ∈ O) ∧
              (∀ f : ↥Kℓ, f ∈ O ↔ ∃ g h : ↥Kℓ, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)) ∧

          (∀ O ∈ ends, ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                (∀ f : ↥Kℓ, f ∈ O → τ f ∈ Wt) → ∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) ∧
          (∀ O ∈ ends,

            (∀ f : ↥Kℓ, f ∈ O → f ∈ Wt) ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ O) ∧
            (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ O ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
            (∀ (f : ↥Kℓ) (hf : f ∈ O), ∃ (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ O), ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, ha⟩)) ∧

            (∃ (hϖO : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ) (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)))
               (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))ˣ) (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) ≃ₐ[(AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))] (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) (ζc' : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (_ : ζc * ζc' = 1)
               (_ : IsLocalRing (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))),
              cx * cy = (⟨_, hϖO⟩ : ↥O) ^ m * (u : ↥O) ∧
              (∀ (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ O), ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, ha⟩) = UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) a)) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∧
              (∀ hcy : (cy : ↥Kℓ) ∈ Wt, (⟨(cy : ↥Kℓ), hcy⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
              (∀ hcx : (cx : ↥Kℓ) ∈ Wt, (⟨(cx : ↥Kℓ), hcx⟩ : ↥Wt) ∉ maximalIdeal ↥Wt) ∧

              (∃ (hjaO : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀ ∈ O) (e : ℕ) (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))ˣ), 1 ≤ e ∧
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀, hjaO⟩) =
                  (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) ^ e) ∧
              (∀ (f : ↥Kℓ) (hf : f ∈ O) (hf' : τ₀ f ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hf'⟩) = θ₀ (ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨f, hf⟩))) ∧
              θ₀ (UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) - UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ζc * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∈
                (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) ^ 2 ∧
              θ₀ (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) - UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ζc' * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∈
                (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) ^ 2 ∧

              (∃ Wx : ValuationSubring ↥Kℓ,
                (∀ f : ↥Kℓ, f ∈ O → f ∈ Wx) ∧
                (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) ∧
                (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
                IsDiscreteValuationRing ↥Wx ∧
                (∃ hϖWx : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hϖWx⟩ : ↥Wx)}) ∧
                (∃ (t : ↥Wx), ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
                  (∃ hm : Polynomial.aeval (t : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧

                (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
                  (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
                (∀ hcx : (cx : ↥Kℓ) ∈ Wx, (⟨(cx : ↥Kℓ), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcy : (cy : ↥Kℓ) ∈ Wx, (⟨(cy : ↥Kℓ), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
                (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y) ∧
                (∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧

                (∀ O' ∈ ends, O' ≠ O → ∃ f : ↥Kℓ, f ∈ O' ∧ f ∉ Wx) ∧

                (∀ O' ∈ ends, ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
                  ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                    (∀ f : ↥Kℓ, f ∈ O' → τ f ∈ Wx) → O' = O)) ∧

              (∃ Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ,
                (∀ f : ↥Kℓ, f ∈ Bx → f ∈ Bt ∧ f ∈ O) ∧
                Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bx ∧
                (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
                  ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                    ∀ f : ↥Kℓ, f ∈ Bx → τ f ∈ Bx) ∧
                (∀ f : ↥Kℓ, f ∈ Bx → ∀ P : AlgebraicCurve.Place ↥k₀ ↥Kℓ, 0 ≤ P.ord jℓ → 0 ≤ P.ord f) ∧
                (∀ f : ↥Kℓ, f ∈ O ↔ ∃ g h : ↥Kℓ, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) ∧

                (∃ b : ↥Kℓ, b ∈ Bx ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
                  (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                      ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                    (∃ f : ↥Kℓ, f ∈ O ∧ f ∉ V) → b ∉ V))))) ∧

          (∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ V) →
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y → ∀ hb : (b : ↥Kℓ) ∈ V, (⟨(b : ↥Kℓ), hb⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ f : ↥Kℓ, f ∈ Bt → f ∈ V) ∨
            (∃ O ∈ ends, ∀ (f : ↥Kℓ) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V))))
    (hR9 : (∃ b : ↥Kℓ, b ∈ Bt ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
            (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                  (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) → b ∉ V)))
    (hR10 : (∀ y'' : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), y''.IsMaximal → algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y'' →
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                ¬ (∀ (b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hb : τ (b : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
                    b ∈ y ↔ (⟨τ (b : ↥Kℓ), hb⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'')) →
            ∃ b : ↥Kℓ, b ∈ Bt ∧ ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              ∀ V : ValuationSubring ↥Kℓ,
                (∀ c : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (c : ↥Kℓ) ∈ V) →
                (∀ (c : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hc : τ.symm (c : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
                    (⟨τ.symm (c : ↥Kℓ), hc⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'' → ∀ hcV : (c : ↥Kℓ) ∈ V, (⟨(c : ↥Kℓ), hcV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                b ∉ V))
    (hn : n = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ))
    (hG : G = Subgroup.closure {τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ})
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
          ∀ (hjK' : (coeffEmb ↥k₀ jq) ∈ Kℓ) (hjF : (⟨(coeffEmb ↥k₀ jq), hjK'⟩ : ↥Kℓ) ∈ K₀) (hjV : (⟨_, hjF⟩ : ↥K₀) ∈ V),
            (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
              ∀ hp : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p.map (algebraMap ↥k₀ ↥K₀)) ∈ V,
                (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
          b ∉ V) := by
  classical
  haveI hmne : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  have hObt1 := E1Kit.C3aux_exists_emb k₀ q ξ hξ
  obtain ⟨ι, hι'⟩ := hObt1
  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q) := ⟨ι, hι'⟩
  have hObt2 := ModularCurve.FullLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker q M' hqM' ℓg hℓgM' ↥k₀ ξ hξ hι H₁ hH₁ Kℓ hKℓ
  obtain ⟨huniq, hmul, hone⟩ := hObt2
  obtain ⟨Gfull, hGfin, hGmem⟩ :=
    ModularCurve.FullLevel.exists_finite_subgroup_forall_mem_iff_exists_isLevelAutAt_of_exists_ringHom_of_eq_levelH_inf_ker q M' hqM' ℓg hℓgM' ↥k₀ ξ hξ hι H₁ hH₁ Kℓ hKℓ
  have hex := ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker q M' hqM' ℓg hℓgM' ↥k₀ ξ hξ H₁ hH₁ Kℓ hKℓ

  have hGle : G ≤ Gfull := by
    rw [hG, Subgroup.closure_le]
    rintro τ ⟨γ, -, hγ0, hτ⟩
    exact (hGmem τ).mpr ⟨γ, hγ0, hτ⟩
  haveI hGfinite : Finite ↥G := by
    haveI := hGfin
    exact Finite.of_injective (Subgroup.inclusion hGle) (Subgroup.inclusion_injective hGle)
  have hGatt : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G →
      ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ := by
    intro τ hτ
    rw [hG] at hτ
    refine Subgroup.closure_induction (p := fun τ _ => ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
        γ ∈ CongruenceSubgroup.Gamma0 M' ∧ ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ) ?_ ?_ ?_ ?_ hτ
    · intro τ h; exact h
    · exact ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, by rw [inv_one]; exact hone 1 (Subgroup.one_mem _) (Subgroup.one_mem _) (by simp)⟩
    · rintro τ σ - - ⟨γ, hγq, hγ0, hτ⟩ ⟨δ, hδq, hδ0, hσ⟩
      refine ⟨γ * δ, Subgroup.mul_mem _ hγq hδq, Subgroup.mul_mem _ hγ0 hδ0, ?_⟩
      rw [mul_inv_rev]
      exact hmul γ⁻¹ δ⁻¹ (Subgroup.inv_mem _ hγ0) (Subgroup.inv_mem _ hδ0) τ σ hτ hσ
    · rintro τ - ⟨γ, hγq, hγ0, hτ⟩
      have hObt3 := hex γ⁻¹ (Subgroup.inv_mem _ hγ0)
      obtain ⟨σ, hσ⟩ := hObt3
      rw [inv_inv] at hσ
      have h1 : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ (γ * γ⁻¹) Kℓ (τ * σ) := hmul γ⁻¹ γ (Subgroup.inv_mem _ hγ0) hγ0 τ σ hτ hσ
      rw [mul_inv_cancel] at h1
      have h2 : τ * σ = 1 := huniq 1 (Subgroup.one_mem _) _ _ h1 (hone 1 (Subgroup.one_mem _) (Subgroup.one_mem _) (by simp))
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

  set jS : ↥Kℓ := ⟨coeffEmb ↥k₀ jq, hjK'⟩ with hjSdef
  have hjSfix : ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ jS = jS := by
    have h := hjF; rw [hK₀] at h; exact (IntermediateField.mem_fixedField_iff G _).mp h
  have hjSV : jS ∈ V := (hVtr ⟨_, hjF⟩).mp hjV₀

  have hjSℓ : jS = (jℓ : ↥Kℓ) := Subtype.ext hjℓ.symm
  have IG : ∀ (V'' : ValuationSubring ↥Kℓ) (hAV'' : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ V'')
      (hmV'' : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), a ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) → (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a, hAV'' a⟩ : ↥V'') ∈ maximalIdeal ↥V'')
      (hj'' : jS ∈ V'')
      (hres'' : ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic → ∀ hp : Polynomial.aeval jS (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V'',
        (⟨_, hp⟩ : ↥V'') ∉ maximalIdeal ↥V''),
      ∃ hjℓ'' : (jℓ : ↥Kℓ) ∈ V'', ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
        ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V'', (⟨_, hp⟩ : ↥V'') ∉ maximalIdeal ↥V'' := by
    intro V'' hAV'' hmV'' hj'' hres''
    rw [hjSℓ] at hj'' hres''
    exact ⟨hj'', hres''⟩

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

end S_ModularCurve_FullLevel_Diamond_AuxLevel_exists_mem_invariants_forall_igusaValuation_not_mem_of_rigidChart_linkedScalars_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_AuxLevel_exists_mem_invariants_forall_igusaValuation_not_mem_of_rigidChart_linkedScalars_of_eq_two_of_dvd (solution)
