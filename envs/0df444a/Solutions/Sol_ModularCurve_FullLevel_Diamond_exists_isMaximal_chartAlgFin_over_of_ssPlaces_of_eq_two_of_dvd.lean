-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_isMaximal_chartAlgFin_over_of_ssPlaces_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f6b9a02d-54de-5f85-bfea-273aceaec1a7

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_linearIndependent_coeffEmb_of_linearIndependent
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_isMaximal_chartAlgFin_over_of_ssPlaces_of_eq_two_of_dvd

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 8000000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups TensorProduct

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace S0A

theorem nonneg_ord_iff_mem {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E) (f : E) :
    0 ≤ v.ord f ↔ f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp [Place.ord_zero]
  constructor
  · exact Place.mem_toValuationSubring_of_ord_nonneg_alt v hf0
  · intro hf
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
    have hcoe : f = ((u : v.toValuationSubring) : E) * ((π : E) ^ (n : ℤ)) := by
      have h := congrArg (Subtype.val) hu
      push_cast at h
      rw [zpow_natCast]
      exact h
    rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
    exact Int.natCast_nonneg n

theorem sum_mul_eq_zero_of_sum_smul_coeffEmb_eq_zero
    (L : Type) [Field L] [CharZero L] {κ : Type} [CommRing κ]
    {A₀ : Type} [AddCommGroup A₀] (emb : A₀ →+ L) (hemb : Function.Injective emb) (χ : A₀ →+ κ)
    (N : AddSubgroup (LaurentSeries ℚ)) (ev : ↥N →+ κ)
    {ι : Type} [Fintype ι] (a : ι → A₀) (g : ι → ↥N)
    (h : ∑ i, emb (a i) • ModularCurve.coeffEmb L (g i : LaurentSeries ℚ) = 0) :
    ∑ i, χ (a i) * ev (g i) = 0 := by
  classical
  let v : ι → LaurentSeries ℚ := fun i => (g i : LaurentSeries ℚ)
  let V : Submodule ℤ (LaurentSeries ℚ) := Submodule.span ℤ (Set.range v)
  have hV : ∀ i, v i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hVN : ∀ x ∈ V, x ∈ N := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact (g i).2
    | zero => exact N.zero_mem
    | add x y _ _ hx hy => exact N.add_mem hx hy
    | smul n x _ hx => exact N.zsmul_mem hx n

  let s' : ι → ↥V := fun i => ⟨v i, hV i⟩
  have hs' : Submodule.span ℤ (Set.range s') = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => exact (Submodule.span ℤ (Set.range s')).zero_mem
    | add y z hy hz ihy ihz => exact (Submodule.span ℤ (Set.range s')).add_mem ihy ihz
    | smul n y hy ihy => exact (Submodule.span ℤ (Set.range s')).smul_mem n ihy
  haveI : IsAddTorsionFree (LaurentSeries ℚ) := IsAddTorsionFree.of_module_rat _
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree hs'

  let r : ι → Fin n → ℤ := fun i k => b.repr (s' i) k
  have hsum : ∀ i, s' i = ∑ k, r i k • b k := fun i => (b.sum_repr (s' i)).symm
  have hsumL : ∀ i, v i = ∑ k, r i k • ((b k : ↥V) : LaurentSeries ℚ) := by
    intro i
    have := congrArg (fun x : ↥V => (x : LaurentSeries ℚ)) (hsum i)
    simpa using this

  have hbZ : LinearIndependent ℤ (fun k => ((b k : ↥V) : LaurentSeries ℚ)) :=
    b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hbQ : LinearIndependent ℚ (fun k => ((b k : ↥V) : LaurentSeries ℚ)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hbZ
  have hbL := ModularCurve.linearIndependent_coeffEmb_of_linearIndependent L hbQ

  have hrel : ∑ k, (∑ i, (r i k) • emb (a i)) • ModularCurve.coeffEmb L ((b k : ↥V) : LaurentSeries ℚ) = 0 := by
    rw [← h]
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show ∑ k, (r i k • emb (a i)) • coeffEmb L ((b k : ↥V) : LaurentSeries ℚ) = emb (a i) • coeffEmb L (v i)
    rw [hsumL i, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_zsmul, smul_comm, smul_assoc]
  have hcoef : ∀ k, ∑ i, (r i k) • emb (a i) = 0 :=
    fun k => Fintype.linearIndependent_iff.mp hbL _ hrel k
  have hcoefA : ∀ k, ∑ i, (r i k) • a i = 0 := by
    intro k
    apply hemb
    rw [map_sum, map_zero]
    simpa only [map_zsmul] using hcoef k

  let g' : Fin n → ↥N := fun k => ⟨((b k : ↥V) : LaurentSeries ℚ), hVN _ (b k).2⟩
  have hg : ∀ i, g i = ∑ k, r i k • g' k := by
    intro i
    apply Subtype.ext
    show v i = ((∑ k, r i k • g' k : ↥N) : LaurentSeries ℚ)
    rw [hsumL i, AddSubgroup.val_finsetSum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [AddSubgroupClass.coe_zsmul]
  calc ∑ i, χ (a i) * ev (g i) = ∑ i, ∑ k, (r i k • χ (a i)) * ev (g' k) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hg i, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [map_zsmul, smul_mul_assoc, mul_smul_comm]
    _ = ∑ k, χ (∑ i, r i k • a i) * ev (g' k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_zsmul]
    _ = 0 := by simp [hcoefA]

section Frame

variable (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
  (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
  (s : (Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')))
  (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
  (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
  [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
  (j : ↥K) [Fact (j ≠ 0)]

def gbar (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M') : ↥(modularFunctionFieldBar M') :=
  ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩

omit A R₀ s k₀ K j in
theorem gbar_add (g₁ g₂ : LaurentSeries ℚ) (h₁ : g₁ ∈ modularFunctionFieldFull M') (h₂ : g₂ ∈ modularFunctionFieldFull M') :
    gbar M' (g₁ + g₂) (add_mem h₁ h₂) = gbar M' g₁ h₁ + gbar M' g₂ h₂ := Subtype.ext (map_add _ _ _)
omit A R₀ s k₀ K j in
theorem gbar_mul (g₁ g₂ : LaurentSeries ℚ) (h₁ : g₁ ∈ modularFunctionFieldFull M') (h₂ : g₂ ∈ modularFunctionFieldFull M') :
    gbar M' (g₁ * g₂) (mul_mem h₁ h₂) = gbar M' g₁ h₁ * gbar M' g₂ h₂ := Subtype.ext (map_mul _ _ _)
omit A R₀ s k₀ K j in
theorem gbar_neg (g : LaurentSeries ℚ) (h : g ∈ modularFunctionFieldFull M') :
    gbar M' (-g) (neg_mem h) = -gbar M' g h := Subtype.ext (map_neg _ _)
omit A R₀ s k₀ K j in
theorem gbar_zero : gbar M' 0 (zero_mem _) = 0 := Subtype.ext (map_zero _)
omit A R₀ s k₀ K j in
theorem gbar_one : gbar M' 1 (one_mem _) = 1 := Subtype.ext (map_one _)

def Adm (g : LaurentSeries ℚ) : Prop :=
  ∃ (hg : g ∈ modularFunctionFieldFull M') (hgi : gbar M' g hg ∈ R₀.integers),
    (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((gbar M' jq (modularFunctionField_le_full M' (jq_mem M')) : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((gbar M' g hg : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) ∧
    (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈ s.toValuationSubring ∧
    ∃ (hgK : coeffEmb ↥k₀ g ∈ K),
      (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j

def N₀ : Subring (LaurentSeries ℚ) where
  carrier := {g | Adm M' A R₀ s k₀ K j g}
  mul_mem' := by
    rintro g₁ g₂ ⟨hg₁, hgi₁, hc₁, hr₁, hK₁, hC₁⟩ ⟨hg₂, hgi₂, hc₂, hr₂, hK₂, hC₂⟩
    have hg : g₁ * g₂ ∈ modularFunctionFieldFull M' := mul_mem hg₁ hg₂
    have hgi : gbar M' (g₁ * g₂) hg ∈ R₀.integers := by
      rw [gbar_mul M' g₁ g₂ hg₁ hg₂]; exact mul_mem hgi₁ hgi₂
    refine ⟨hg, hgi, ?_, ?_, ?_⟩
    · intro P hP
      rw [gbar_mul M' g₁ g₂ hg₁ hg₂, S0A.nonneg_ord_iff_mem]
      push_cast
      exact mul_mem ((S0A.nonneg_ord_iff_mem P _).mp (hc₁ P hP)) ((S0A.nonneg_ord_iff_mem P _).mp (hc₂ P hP))
    · have e2 : (⟨gbar M' (g₁ * g₂) hg, hgi⟩ : ↥R₀.integers) = ⟨_, hgi₁⟩ * ⟨_, hgi₂⟩ :=
        Subtype.ext (gbar_mul M' g₁ g₂ hg₁ hg₂)
      rw [e2, map_mul]
      exact mul_mem hr₁ hr₂
    · have hK : coeffEmb ↥k₀ (g₁ * g₂) ∈ K := by
        rw [map_mul]; exact mul_mem hK₁ hK₂
      refine ⟨hK, ?_⟩
      have e3 : (⟨_, hK⟩ : ↥K) = ⟨_, hK₁⟩ * ⟨_, hK₂⟩ := Subtype.ext (by push_cast; rw [map_mul])
      rw [e3]; exact mul_mem hC₁ hC₂
  one_mem' := by
    refine ⟨one_mem _, ?_, ?_, ?_, ?_⟩
    · rw [gbar_one]; exact one_mem _
    · intro P _; rw [gbar_one]; push_cast; rw [Place.ord_one]
    · have e2 : (⟨gbar M' 1 (one_mem _), ((gbar_one M').symm ▸ one_mem _ : gbar M' 1 (one_mem _) ∈ R₀.integers)⟩ : ↥R₀.integers) = 1 :=
        Subtype.ext (gbar_one M')
      rw [e2, map_one]; exact one_mem _
    · have hK : coeffEmb ↥k₀ 1 ∈ K := by rw [map_one]; exact one_mem _
      refine ⟨hK, ?_⟩
      have e3 : (⟨_, hK⟩ : ↥K) = 1 := Subtype.ext (by push_cast; rw [map_one])
      rw [e3]; exact one_mem _
  add_mem' := by
    rintro g₁ g₂ ⟨hg₁, hgi₁, hc₁, hr₁, hK₁, hC₁⟩ ⟨hg₂, hgi₂, hc₂, hr₂, hK₂, hC₂⟩
    have hg : g₁ + g₂ ∈ modularFunctionFieldFull M' := add_mem hg₁ hg₂
    have hgi : gbar M' (g₁ + g₂) hg ∈ R₀.integers := by
      rw [gbar_add M' g₁ g₂ hg₁ hg₂]; exact add_mem hgi₁ hgi₂
    refine ⟨hg, hgi, ?_, ?_, ?_⟩
    · intro P hP
      rw [gbar_add M' g₁ g₂ hg₁ hg₂, S0A.nonneg_ord_iff_mem]
      push_cast
      exact add_mem ((S0A.nonneg_ord_iff_mem P _).mp (hc₁ P hP)) ((S0A.nonneg_ord_iff_mem P _).mp (hc₂ P hP))
    · have e2 : (⟨gbar M' (g₁ + g₂) hg, hgi⟩ : ↥R₀.integers) = ⟨_, hgi₁⟩ + ⟨_, hgi₂⟩ :=
        Subtype.ext (gbar_add M' g₁ g₂ hg₁ hg₂)
      rw [e2, map_add]
      exact add_mem hr₁ hr₂
    · have hK : coeffEmb ↥k₀ (g₁ + g₂) ∈ K := by
        rw [map_add]; exact add_mem hK₁ hK₂
      refine ⟨hK, ?_⟩
      have e3 : (⟨_, hK⟩ : ↥K) = ⟨_, hK₁⟩ + ⟨_, hK₂⟩ := Subtype.ext (by push_cast; rw [map_add])
      rw [e3]; exact add_mem hC₁ hC₂
  zero_mem' := by
    refine ⟨zero_mem _, ?_, ?_, ?_, ?_⟩
    · rw [gbar_zero]; exact zero_mem _
    · intro P _; rw [gbar_zero]; push_cast; rw [Place.ord_zero]
    · have e2 : (⟨gbar M' 0 (zero_mem _), ((gbar_zero M').symm ▸ zero_mem _ : gbar M' 0 (zero_mem _) ∈ R₀.integers)⟩ : ↥R₀.integers) = 0 :=
        Subtype.ext (gbar_zero M')
      rw [e2, map_zero]; exact zero_mem _
    · have hK : coeffEmb ↥k₀ 0 ∈ K := by rw [map_zero]; exact zero_mem _
      refine ⟨hK, ?_⟩
      have e3 : (⟨_, hK⟩ : ↥K) = 0 := Subtype.ext (by push_cast; rw [map_zero])
      rw [e3]; exact zero_mem _
  neg_mem' := by
    rintro g ⟨hg₁, hgi₁, hc₁, hr₁, hK₁, hC₁⟩
    have hg : -g ∈ modularFunctionFieldFull M' := neg_mem hg₁
    have hgi : gbar M' (-g) hg ∈ R₀.integers := by rw [gbar_neg M' g hg₁]; exact neg_mem hgi₁
    refine ⟨hg, hgi, ?_, ?_, ?_⟩
    · intro P hP
      rw [gbar_neg M' g hg₁, S0A.nonneg_ord_iff_mem]
      push_cast
      exact neg_mem ((S0A.nonneg_ord_iff_mem P _).mp (hc₁ P hP))
    · have e2 : (⟨gbar M' (-g) hg, hgi⟩ : ↥R₀.integers) = -⟨_, hgi₁⟩ :=
        Subtype.ext (gbar_neg M' g hg₁)
      rw [e2, map_neg]
      exact neg_mem hr₁
    · have hK : coeffEmb ↥k₀ (-g) ∈ K := by rw [map_neg]; exact neg_mem hK₁
      refine ⟨hK, ?_⟩
      have e3 : (⟨_, hK⟩ : ↥K) = -⟨_, hK₁⟩ := Subtype.ext (by push_cast; rw [map_neg])
      rw [e3]; exact neg_mem hC₁

theorem mem_N₀ (g : LaurentSeries ℚ) : g ∈ N₀ M' A R₀ s k₀ K j ↔ Adm M' A R₀ s k₀ K j g := Iff.rfl

def ιR : ↥(N₀ M' A R₀ s k₀ K j) →+* ↥R₀.integers where
  toFun g := ⟨gbar M' (g : LaurentSeries ℚ) g.2.1, g.2.2.1⟩
  map_one' := Subtype.ext (gbar_one M')
  map_mul' g₁ g₂ := Subtype.ext (gbar_mul M' _ _ g₁.2.1 g₂.2.1)
  map_zero' := Subtype.ext (gbar_zero M')
  map_add' g₁ g₂ := Subtype.ext (gbar_add M' _ _ g₁.2.1 g₂.2.1)

def Ψ : ↥(N₀ M' A R₀ s k₀ K j) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) where
  toFun g := ⟨⟨coeffEmb ↥k₀ (g : LaurentSeries ℚ), g.2.2.2.2.2.1⟩, g.2.2.2.2.2.2⟩
  map_one' := Subtype.ext (Subtype.ext (by push_cast; rw [map_one]))
  map_mul' g₁ g₂ := Subtype.ext (Subtype.ext (by push_cast; rw [map_mul]))
  map_zero' := Subtype.ext (Subtype.ext (by push_cast; rw [map_zero]))
  map_add' g₁ g₂ := Subtype.ext (Subtype.ext (by push_cast; rw [map_add]))

theorem Ψ_apply (g : ↥(N₀ M' A R₀ s k₀ K j)) :
    Ψ M' A R₀ s k₀ K j g = ⟨⟨coeffEmb ↥k₀ (g : LaurentSeries ℚ), g.2.2.2.2.2.1⟩, g.2.2.2.2.2.2⟩ := rfl

theorem residue_ιR_mem (g : ↥(N₀ M' A R₀ s k₀ K j)) :
    R₀.residue (ιR M' A R₀ s k₀ K j g) ∈ s.toValuationSubring := g.2.2.2.2.1

noncomputable def evf (g : ↥(N₀ M' A R₀ s k₀ K j)) : ResidueField ↥A :=
  s.evalAt (R₀.residue (ιR M' A R₀ s k₀ K j g))

theorem algebraMap_evf (hs : s.IsRational) (g : ↥(N₀ M' A R₀ s k₀ K j)) :
    algebraMap (ResidueField ↥A) _ (evf M' A R₀ s k₀ K j g) =
      IsLocalRing.residue _ (⟨_, residue_ιR_mem M' A R₀ s k₀ K j g⟩ : ↥s.toValuationSubring) :=
  Place.algebraMap_evalAt _ hs _

noncomputable def ev (hs : s.IsRational) : ↥(N₀ M' A R₀ s k₀ K j) →+* ResidueField ↥A where
  toFun := evf M' A R₀ s k₀ K j
  map_one' := by
    apply s.algebraMap_residueField_injective
    have h1 : (⟨_, residue_ιR_mem M' A R₀ s k₀ K j 1⟩ : ↥s.toValuationSubring) = 1 :=
      Subtype.ext (show R₀.residue (ιR M' A R₀ s k₀ K j 1) = (1 : modularFunctionFieldC (ResidueField ↥A) M') by
        rw [map_one, map_one])
    rw [algebraMap_evf M' A R₀ s k₀ K j hs, h1]
    exact (map_one _).trans (map_one _).symm
  map_mul' g₁ g₂ := by
    apply s.algebraMap_residueField_injective
    rw [map_mul (algebraMap (ResidueField ↥A) _), algebraMap_evf M' A R₀ s k₀ K j hs, algebraMap_evf M' A R₀ s k₀ K j hs,
      algebraMap_evf M' A R₀ s k₀ K j hs, ← map_mul (IsLocalRing.residue ↥s.toValuationSubring)]
    congr 1
    exact Subtype.ext (show R₀.residue (ιR M' A R₀ s k₀ K j (g₁ * g₂)) =
      R₀.residue (ιR M' A R₀ s k₀ K j g₁) * R₀.residue (ιR M' A R₀ s k₀ K j g₂) by rw [map_mul, map_mul])
  map_zero' := by
    apply s.algebraMap_residueField_injective
    have h0 : (⟨_, residue_ιR_mem M' A R₀ s k₀ K j 0⟩ : ↥s.toValuationSubring) = 0 :=
      Subtype.ext (show R₀.residue (ιR M' A R₀ s k₀ K j 0) = (0 : modularFunctionFieldC (ResidueField ↥A) M') by
        rw [map_zero, map_zero])
    rw [algebraMap_evf M' A R₀ s k₀ K j hs, h0]
    exact (map_zero _).trans (map_zero _).symm
  map_add' g₁ g₂ := by
    apply s.algebraMap_residueField_injective
    rw [map_add (algebraMap (ResidueField ↥A) _), algebraMap_evf M' A R₀ s k₀ K j hs, algebraMap_evf M' A R₀ s k₀ K j hs,
      algebraMap_evf M' A R₀ s k₀ K j hs, ← map_add (IsLocalRing.residue ↥s.toValuationSubring)]
    congr 1
    exact Subtype.ext (show R₀.residue (ιR M' A R₀ s k₀ K j (g₁ + g₂)) =
      R₀.residue (ιR M' A R₀ s k₀ K j g₁) + R₀.residue (ιR M' A R₀ s k₀ K j g₂) by rw [map_add, map_add])

theorem ev_apply (hs : s.IsRational) (g : ↥(N₀ M' A R₀ s k₀ K j)) :
    ev M' A R₀ s k₀ K j hs g = s.evalAt (R₀.residue ⟨gbar M' (g : LaurentSeries ℚ) g.2.1, g.2.2.1⟩) := rfl

def θC : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j) →ₐ[ℤ] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) :=
  Algebra.TensorProduct.lift (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)).toIntAlgHom (Ψ M' A R₀ s k₀ K j).toIntAlgHom
    (fun _ _ => Commute.all _ _)

theorem θC_tmul (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (g : ↥(N₀ M' A R₀ s k₀ K j)) :
    θC M' A R₀ s k₀ K j (a ⊗ₜ[ℤ] g) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) a * Ψ M' A R₀ s k₀ K j g :=
  Algebra.TensorProduct.lift_tmul _ _ _ a g

theorem K2_isIntegral
    (hj : ((j : ↥K) : LaurentSeries ↥k₀) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq)
    (hjN : jq ∈ N₀ M' A R₀ s k₀ K j) :
    letI : Algebra (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) := (θC M' A R₀ s k₀ K j).toRingHom.toAlgebra
    Algebra.IsIntegral (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) := by
  classical
  letI algTC : Algebra (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) := (θC M' A R₀ s k₀ K j).toRingHom.toAlgebra

  let θK : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j) →+* ↥K :=
    (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j).val.toRingHom.comp (θC M' A R₀ s k₀ K j).toRingHom
  letI algTK : Algebra (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) ↥K := θK.toAlgebra
  haveI : IsScalarTower (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ↥K :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hθK : ∀ t, algebraMap (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) ↥K t = ((θC M' A R₀ s k₀ K j t : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) := fun _ => rfl

  let f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)] ↥K :=
    { (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j).val.toRingHom with commutes' := fun _ => rfl }
  have hf : Function.Injective f := fun x y hxy => Subtype.ext (by exact hxy)

  set jsh : ↥K := ⟨coeffEmb ↥k₀ jq, hjN.2.2.2.2.1⟩ with hjsh_def
  have hjj : jsh = j := Subtype.ext hj.symm
  have hj0 : (j : ↥K) ≠ 0 := Fact.out
  haveI : Fact (jsh ≠ 0) := ⟨by
    intro h0
    apply hj0
    have h1 : coeffEmb ↥k₀ jq = 0 := by
      have := congrArg (fun z : ↥K => (z : LaurentSeries ↥k₀)) h0
      exact this
    exact Subtype.ext (hj.trans h1)⟩
  have hjmem : (j : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) jsh := by
    have h : jsh ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j := hjN.2.2.2.2.2
    rw [hjj] at h ⊢; exact h
  have hjint : IsIntegral ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({jsh} : Set ↥K)) (j : ↥K) :=
    (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K)).mp hjmem

  have hrange : ∀ c : ↥K, c ∈ Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({jsh} : Set ↥K) → c ∈ Set.range θK := by
    intro c hc
    induction hc using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨(1 : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⊗ₜ[ℤ] (⟨jq, hjN⟩ : ↥(N₀ M' A R₀ s k₀ K j)), ?_⟩
      show ((θC M' A R₀ s k₀ K j ((1 : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⊗ₜ[ℤ] (⟨jq, hjN⟩ : ↥(N₀ M' A R₀ s k₀ K j))) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) = jsh
      rw [θC_tmul, map_one, one_mul]
      rfl
    | algebraMap a =>
      refine ⟨a ⊗ₜ[ℤ] (1 : ↥(N₀ M' A R₀ s k₀ K j)), ?_⟩
      show ((θC M' A R₀ s k₀ K j (a ⊗ₜ[ℤ] (1 : ↥(N₀ M' A R₀ s k₀ K j))) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K a
      rw [θC_tmul, map_one, mul_one, Subalgebra.coe_algebraMap]
    | add x y _ _ hx hy =>
      obtain ⟨tx, rfl⟩ := hx
      obtain ⟨ty, rfl⟩ := hy
      exact ⟨tx + ty, map_add θK tx ty⟩
    | mul x y _ _ hx hy =>
      obtain ⟨tx, rfl⟩ := hx
      obtain ⟨ty, rfl⟩ := hy
      exact ⟨tx * ty, map_mul θK tx ty⟩

  have hjT : IsIntegral (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) (j : ↥K) := by
    obtain ⟨p, hpm, hpr⟩ := hjint
    set p' : Polynomial ↥K := p.map (algebraMap ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({jsh} : Set ↥K)) ↥K) with hp'
    have hp'm : p'.Monic := hpm.map _
    have hlifts : p' ∈ Polynomial.lifts θK := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      rw [hp', Polynomial.coeff_map]
      exact hrange _ (p.coeff i).2
    obtain ⟨q', hq'p, -, hq'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp'm
    refine ⟨q', hq'm, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, show algebraMap (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) ↥K = θK from rfl, hq'p, hp',
      ← Polynomial.eval₂_eq_eval_map]
    exact hpr

  have hjIC : (j : ↥K) ∈ integralClosure (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) ↥K := hjT
  have hadj : ∀ c : ↥K, c ∈ Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({(j : ↥K)} : Set ↥K) → c ∈ integralClosure (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) ↥K := by
    intro c hc
    induction hc using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hjIC
    | algebraMap a =>
      have : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K a = algebraMap (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) ↥K (a ⊗ₜ[ℤ] (1 : ↥(N₀ M' A R₀ s k₀ K j))) := by
        rw [hθK, θC_tmul, map_one, mul_one, Subalgebra.coe_algebraMap]
      rw [this]
      exact isIntegral_algebraMap
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  constructor
  intro x
  have hxint : IsIntegral ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({(j : ↥K)} : Set ↥K)) ((x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) :=
    (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K)).mp x.2

  let φ : ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({(j : ↥K)} : Set ↥K)) →+* ↥(integralClosure (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) ↥K) :=
    { toFun := fun c => ⟨(c : ↥K), hadj _ c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hxIC : IsIntegral ↥(integralClosure (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) ↥K) ((x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) :=
    hxint.map_of_comp_eq φ (RingHom.id ↥K) (by ext; rfl)
  have hxT : IsIntegral (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(N₀ M' A R₀ s k₀ K j)) ((x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) := isIntegral_trans _ hxIC
  exact (isIntegral_algHom_iff f hf).mp hxT

end Frame

end S0A

end

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
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
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (hjK : (coeffEmb ↥k₀ jq) ∈ K)
    (hjC : (⟨_, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) :
    ∃ y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
      y.IsMaximal ∧

      algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨π₀, hπ⟩ ∈ y ∧

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
        ∀ (hgK : (coeffEmb ↥k₀ g) ∈ K)
          (hgC : (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
        ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
          residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
          (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) -
              algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨c, hc⟩ ∈ y) := by
  classical
  have hsW : (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) ∈ ssPlaces q M' (ResidueField ↥A) := (hW s).mp s.2
  have hsrat : (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')).IsRational := ((mem_ssPlaces_iff q M' (ResidueField ↥A)).mp hsW).1

  let inclA : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* ↥A :=
    { toFun := fun a => ⟨((a : ↥k₀) : AlgebraicClosure ℚ), a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let χ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* (ResidueField ↥A) := (IsLocalRing.residue ↥A).comp inclA
  have hχapp : ∀ (c : ↥k₀) (hc : (c : AlgebraicClosure ℚ) ∈ A), χ ⟨c, hc⟩ = residue A ⟨(c : AlgebraicClosure ℚ), hc⟩ :=
    fun _ _ => rfl
  have hχsurj : Function.Surjective χ := by
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨c, hcA, hsub, hm⟩ := hκ a a.2
    refine ⟨⟨c, hcA⟩, ?_⟩
    show IsLocalRing.residue ↥A ⟨(c : AlgebraicClosure ℚ), hcA⟩ = IsLocalRing.residue ↥A a
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hm
  have hχπ : χ ⟨π₀, hπ⟩ = 0 := by
    show IsLocalRing.residue ↥A ⟨(π₀ : AlgebraicClosure ℚ), hπ⟩ = 0
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hπmax : (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
      rw [hunif]; exact Ideal.mem_span_singleton_self _
    apply (IsLocalRing.mem_maximalIdeal _ |>.mp hπmax)
    obtain ⟨u, hu'⟩ := hu
    have hne : ((π₀ : ↥k₀) : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0; apply u.ne_zero; rw [hu']; exact Subtype.ext h0
    have hne0 : (π₀ : ↥k₀) ≠ 0 := fun h0 => hne (by rw [h0]; rfl)
    have hvinv : (((u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) * ((π₀ : ↥k₀) : AlgebraicClosure ℚ) = 1 := by
      have h := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) u.inv_mul
      simp only [hu'] at h
      push_cast at h
      exact h
    have hinv : ((π₀ : ↥k₀)⁻¹ : ↥k₀) ∈ A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) := by
      show algebraMap ↥k₀ (AlgebraicClosure ℚ) (π₀⁻¹) ∈ A
      rw [map_inv₀, show algebraMap ↥k₀ (AlgebraicClosure ℚ) π₀ = ((π₀ : ↥k₀) : AlgebraicClosure ℚ) from rfl,
        inv_eq_of_mul_eq_one_left hvinv]
      exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
    exact isUnit_iff_exists_inv.mpr ⟨⟨π₀⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne0)⟩

  let θC := S0A.θC M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j
  let θκ := Algebra.TensorProduct.lift (R := ℤ) (S := ℤ) χ.toIntAlgHom (S0A.ev M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j hsrat).toIntAlgHom
      (fun _ _ => Commute.all _ _)
  have θC_tmul : ∀ (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (g : ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j)), θC (a ⊗ₜ[ℤ] g) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) a * S0A.Ψ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j g :=
    fun a g => S0A.θC_tmul M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j a g
  have θκ_tmul : ∀ (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (g : ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j)), θκ (a ⊗ₜ[ℤ] g) = χ a * S0A.ev M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j hsrat g :=
    fun a g => Algebra.TensorProduct.lift_tmul _ _ _ a g

  have K1 : ∀ t : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j), θC t = 0 → θκ t = 0 := by
    intro t ht
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset t

    let φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →+* LaurentSeries ↥k₀ :=
      K.val.toRingHom.comp (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j).val.toRingHom
    have hφ : ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j), φ x = ((x : ↥K) : LaurentSeries ↥k₀) := fun _ => rfl
    have hφa : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), φ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) a) = HahnSeries.C ((a : ↥k₀)) := by
      intro a
      rw [hφ, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K a]
      show ((algebraMap ↥k₀ ↥K (a : ↥k₀) : ↥K) : LaurentSeries ↥k₀) = HahnSeries.C (a : ↥k₀)
      rw [show ((algebraMap ↥k₀ ↥K (a : ↥k₀) : ↥K) : LaurentSeries ↥k₀) = algebraMap ↥k₀ (LaurentSeries ↥k₀) (a : ↥k₀) from rfl,
        ModularCurve.algebraMap_laurentSeries_eq_single]
      rfl
    have hφΨ : ∀ g : ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j), φ (S0A.Ψ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j g) = coeffEmb ↥k₀ (g : LaurentSeries ℚ) :=
      fun _ => rfl
    have h1 : ∑ p ∈ S, HahnSeries.C ((p.1 : ↥k₀)) * coeffEmb ↥k₀ (p.2 : LaurentSeries ℚ) = 0 := by
      have hh : φ (θC (∑ p ∈ S, p.1 ⊗ₜ[ℤ] p.2)) = 0 := by rw [ht, map_zero]
      rw [map_sum, map_sum] at hh
      refine (Finset.sum_congr rfl (fun p _ => ?_)).trans hh
      rw [θC_tmul, map_mul, hφa, hφΨ]
    have h3 : ∑ p ∈ S, ((p.1 : ↥k₀)) • coeffEmb ↥k₀ (p.2 : LaurentSeries ℚ) = 0 := by
      have h2' : ∑ p ∈ S, HahnSeries.C ((p.1 : ↥k₀)) * coeffEmb ↥k₀ (p.2 : LaurentSeries ℚ) = 0 := h1
      refine (Finset.sum_congr rfl (fun p _ => ?_)).trans h2'
      rw [HahnSeries.C_mul_eq_smul]

    have h4 : ∑ p : ↥S, (((p : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) × ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j)).1 : ↥k₀)) • coeffEmb ↥k₀ (((p : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) × ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j)).2 : LaurentSeries ℚ)) = 0 := by
      have h3' := h3
      rw [← Finset.sum_coe_sort] at h3'
      exact h3'
    let emb : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+ ↥k₀ := (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀).toAddMonoidHom
    have hemb : Function.Injective emb := fun x y hxy => Subtype.ext hxy
    have key := S0A.sum_mul_eq_zero_of_sum_smul_coeffEmb_eq_zero ↥k₀ emb hemb χ.toAddMonoidHom
      (S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j).toAddSubgroup (S0A.ev M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j hsrat).toAddMonoidHom
      (fun p : ↥S => (p : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) × ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j)).1)
      (fun p : ↥S => ⟨((p : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) × ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j)).2 : LaurentSeries ℚ), (p : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) × ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j)).2.2⟩) h4

    rw [map_sum, ← Finset.sum_coe_sort]
    refine (Finset.sum_congr rfl (fun p _ => ?_)).trans key
    rw [θκ_tmul]
    rfl

  letI algTC : Algebra (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) := θC.toRingHom.toAlgebra
  have halgTC : ∀ t, algebraMap (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) t = θC t := fun _ => rfl

  have hjN : jq ∈ S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j := by
    rw [S0A.mem_N₀]
    have hmapA : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq := by
      change (jqModC ↥A).map A.subtype = (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ))
      rw [map_jqModC, map_jqModC]
    have hjqBar : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
      rw [hmapA]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
    obtain ⟨hjint, hjres⟩ := hR₀ (jqModC ↥A) hjqBar
    have helt : S0A.gbar M' jq (modularFunctionField_le_full M' (jq_mem M')) = ⟨coeffMap A.subtype (jqModC ↥A), hjqBar⟩ :=
      Subtype.ext hmapA.symm
    have hgi : S0A.gbar M' jq (modularFunctionField_le_full M' (jq_mem M')) ∈ R₀.integers := by rw [helt]; exact hjint
    have hresj : R₀.residue ⟨_, hgi⟩ = jGeomGen (ResidueField ↥A) M' := by
      have h1 : (⟨_, hgi⟩ : ↥R₀.integers) = ⟨_, hjint⟩ := Subtype.ext helt
      rw [h1]
      apply Subtype.ext
      rw [hjres, coe_jGeomGen]
      change (jqModC ↥A).map (IsLocalRing.residue ↥A) = jqModC (ResidueField ↥A)
      exact map_jqModC _
    refine ⟨modularFunctionField_le_full M' (jq_mem M'), hgi, fun P h => h, ?_, hjK, hjC⟩
    rw [hresj]
    exact ((mem_ssPlaces_iff q M' (ResidueField ↥A)).mp hsW).2.1.1
  haveI K2 : Algebra.IsIntegral (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j)) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) := S0A.K2_isIntegral M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j hj hjN

  have hθκsurj : Function.Surjective θκ := by
    intro r
    obtain ⟨a, rfl⟩ := hχsurj r
    exact ⟨a ⊗ₜ[ℤ] 1, by rw [θκ_tmul, map_one, mul_one]⟩
  haveI K3 : (RingHom.ker θκ.toRingHom).IsMaximal := RingHom.ker_isMaximal_of_surjective θκ.toRingHom hθκsurj
  obtain ⟨y, hymax, hy⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) (RingHom.ker θκ.toRingHom)
    (fun t ht => by rw [RingHom.mem_ker] at ht ⊢; exact K1 t ht)
  have hmem : ∀ t : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⊗[ℤ] ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j), θκ t = 0 → θC t ∈ y := by
    intro t ht
    rw [← halgTC, ← Ideal.mem_comap, hy, RingHom.mem_ker]
    exact ht
  refine ⟨y, hymax, ?_, ?_⟩
  · have e : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨π₀, hπ⟩ = θC (⟨π₀, hπ⟩ ⊗ₜ[ℤ] (1 : ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j))) := by
      rw [θC_tmul, map_one, mul_one]
    rw [e]
    apply hmem
    rw [θκ_tmul, map_one, mul_one, hχπ]
  · intro g hg hgi hcusp hreg hgK hgC c hc hval
    have hadm : S0A.Adm M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j g := ⟨hg, hgi, hcusp, hreg, hgK, hgC⟩
    have e : (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨c, hc⟩ =
        θC ((1 : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⊗ₜ[ℤ] (⟨g, hadm⟩ : ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j)) - ⟨c, hc⟩ ⊗ₜ[ℤ] (1 : ↥(S0A.N₀ M' A R₀ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) k₀ K j))) := by
      rw [map_sub, θC_tmul, θC_tmul, map_one, one_mul, map_one, mul_one]
      rfl
    rw [e]
    apply hmem
    rw [map_sub, θκ_tmul, θκ_tmul, map_one, one_mul, map_one, mul_one, hχapp, hval, S0A.ev_apply, sub_eq_zero]
    rfl

end S_ModularCurve_FullLevel_Diamond_exists_isMaximal_chartAlgFin_over_of_ssPlaces_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_isMaximal_chartAlgFin_over_of_ssPlaces_of_eq_two_of_dvd (solution)
