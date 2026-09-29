-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_qExpand_mem_chartAlgFin_and_forall_mem_closure_levelAutBar_exists_algEquiv_levelField_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/08dc88f1-ac93-5cfb-8528-b83a922771e5

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Mathlib
import Theorems.Thm_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coe_mem_fieldBar_of_mem
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_FullLevel_exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_qExpand_mem_chartAlgFin_and_forall_mem_closure_levelAutBar_exists_algEquiv_levelField_of_eq_three
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

namespace TH1Transport

open Polynomial

section Chart

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]

theorem isIntegral_adjoin_map (τ : K →ₐ[A] K) (t b : K)
    (hb : IsIntegral (Algebra.adjoin A ({t} : Set K)) b) :
    IsIntegral (Algebra.adjoin A ({τ t} : Set K)) (τ b) := by
  have hmap : (Algebra.adjoin A ({t} : Set K)).map τ = Algebra.adjoin A {τ t} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
  let φ : Algebra.adjoin A ({t} : Set K) →+* Algebra.adjoin A ({τ t} : Set K) :=
    { toFun := fun s => ⟨τ s, by rw [← hmap]; exact Subalgebra.mem_map.mpr ⟨s, s.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  exact hb.map_of_comp_eq φ τ.toRingHom (by ext s; rfl)

theorem isIntegral_trans_subalgebra (S : Subalgebra A K) (b : K) (hb : IsIntegral (integralClosure S K) b) :
    IsIntegral S b := by
  haveI : IsScalarTower S (integralClosure S K) K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact isIntegral_trans b hb

theorem isIntegral_adjoin_of_isIntegral_adjoin {t t' b : K}
    (ht' : IsIntegral (Algebra.adjoin A ({t} : Set K)) t')
    (hb : IsIntegral (Algebra.adjoin A ({t'} : Set K)) b) :
    IsIntegral (Algebra.adjoin A ({t} : Set K)) b := by
  exact isIntegral_trans_subalgebra (Algebra.adjoin A ({t} : Set K)) b
    (by
      have hle : Algebra.adjoin A ({t'} : Set K) ≤
          (integralClosure (Algebra.adjoin A ({t} : Set K)) K).restrictScalars A := by
        rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
        exact ht'
      have hle' : (Algebra.adjoin A ({t'} : Set K)).toSubring ≤
          (integralClosure (Algebra.adjoin A ({t} : Set K)) K).toSubring := fun x hx => hle hx
      exact hb.map_of_comp_eq (Subring.inclusion hle') (RingHom.id K) (by ext; rfl))

theorem chartAlg_singleton_eq_of_isIntegral {t t' : K}
    (h1 : IsIntegral (Algebra.adjoin A ({t} : Set K)) t') (h2 : IsIntegral (Algebra.adjoin A ({t'} : Set K)) t) :
    AlgebraicCurve.TwoChartIntegralModel.chartAlg A K {t} = AlgebraicCurve.TwoChartIntegralModel.chartAlg A K {t'} := by
  ext b
  rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff, AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff]
  exact ⟨isIntegral_adjoin_of_isIntegral_adjoin h2, isIntegral_adjoin_of_isIntegral_adjoin h1⟩

end Chart

section ModEq

variable {L : Type} [Field L] [CharZero L]

theorem exists_monic_eval₂_coeffEmb (p : ℕ) [Fact p.Prime] [NeZero p] :
    ∃ Φ : Polynomial (Polynomial ℤ), Φ.Monic ∧
      Φ.eval₂ (aeval (ModularCurve.coeffEmb L ModularCurve.jq)).toRingHom
        (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) = 0 ∧
      Φ.eval₂ (aeval (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))).toRingHom
        (ModularCurve.coeffEmb L ModularCurve.jq) = 0 := by
  obtain ⟨data, hsymm⟩ := ModularCurve.exists_modularPolynomialData_evalSymm p
  have h0 : data.Φ.eval₂ (aeval ModularCurve.jq).toRingHom (ModularCurve.qExpand ℚ p ModularCurve.jq) = 0 := by
    have := data.eval_eq_zero
    rwa [ModularCurve.evalAtJ_def] at this
  have h1 : data.Φ.eval₂ (aeval (ModularCurve.qExpand ℚ p ModularCurve.jq)).toRingHom ModularCurve.jq = 0 := by
    rw [← hsymm]; exact h0
  have key : ∀ x y : LaurentSeries ℚ,
      (ModularCurve.coeffEmb L) (data.Φ.eval₂ (aeval x).toRingHom y)
        = data.Φ.eval₂ (aeval (ModularCurve.coeffEmb L x)).toRingHom (ModularCurve.coeffEmb L y) := by
    intro x y
    rw [hom_eval₂]
    congr 1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp
    · simp
  refine ⟨data.Φ, data.monic, ?_, ?_⟩
  · rw [← key, h0, map_zero]
  · rw [← key, h1, map_zero]

end ModEq

section Generic

variable {A T S : Type} [CommRing A] [Field T] [CommRing S] [Algebra A T]

theorem isIntegral_adjoin_of_eval₂_hom (ι : T →+* S) (hι : Function.Injective ι) (a b : T)
    (Φ : Polynomial (Polynomial ℤ)) (hm : Φ.Monic)
    (h : Φ.eval₂ (aeval (ι a)).toRingHom (ι b) = 0) :
    IsIntegral (Algebra.adjoin A ({a} : Set T)) b := by
  let a' : Algebra.adjoin A ({a} : Set T) := ⟨a, Algebra.self_mem_adjoin_singleton A a⟩
  let θ : Polynomial ℤ →+* Algebra.adjoin A ({a} : Set T) := (aeval a').toRingHom
  refine ⟨Φ.map θ, hm.map θ, ?_⟩
  rw [eval₂_map]
  apply hι
  rw [hom_eval₂, map_zero]
  convert h using 2
  refine Polynomial.ringHom_ext (fun n => by simp) ?_
  simp [θ, a']

theorem mem_chartAlg_singleton_iff_map_mem (σ : T ≃ₐ[A] T) {t t' : T}
    (h1 : IsIntegral (Algebra.adjoin A ({t} : Set T)) t') (h2 : IsIntegral (Algebra.adjoin A ({t'} : Set T)) t)
    (hfix : σ t' = t') (b : T) :
    b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg A T {t} ↔
      σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg A T {t} := by
  rw [chartAlg_singleton_eq_of_isIntegral h1 h2, AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff,
    AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff]
  have hfix' : σ.symm t' = t' := by
    conv_lhs => rw [← hfix]
    exact σ.symm_apply_apply t'
  constructor
  · intro hb
    have := isIntegral_adjoin_map (σ : T →ₐ[A] T) t' b hb
    rwa [AlgEquiv.coe_algHom, hfix] at this
  · intro hb
    have := isIntegral_adjoin_map (σ.symm : T →ₐ[A] T) t' (σ b) hb
    rwa [AlgEquiv.coe_algHom, hfix', AlgEquiv.symm_apply_apply] at this

end Generic

section JQ

theorem isIntegral_adjoin_jq_qExpand {A T : Type} [CommRing A] [Field T] [Algebra A T]
    (p : ℕ) [Fact p.Prime] (a b : T)
    (ι : T →+* LaurentSeries (AlgebraicClosure ℚ)) (hι : Function.Injective ι)
    (ha : ι a = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq)
    (hb : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ι b = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ p ModularCurve.jq)) :
    IsIntegral (Algebra.adjoin A ({a} : Set T)) b ∧ IsIntegral (Algebra.adjoin A ({b} : Set T)) a := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨Φ, hm, h1, h2⟩ := exists_monic_eval₂_coeffEmb (L := AlgebraicClosure ℚ) p
  refine ⟨isIntegral_adjoin_of_eval₂_hom ι hι a b Φ hm ?_, isIntegral_adjoin_of_eval₂_hom ι hι b a Φ hm ?_⟩
  · convert h1 using 2 <;> first | rfl | exact Polynomial.ringHom_ext (fun n => by simp) (by simp [ha])
  · convert h2 using 2 <;> first | rfl | exact Polynomial.ringHom_ext (fun n => by simp) (by simp [hb])

end JQ

end TH1Transport

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

namespace TH1AuxIg

section Closure

variable {G : Type*} [Group G]

theorem forall_mem_closure_of_generators (s : Set G) (p : G → Prop)
    (h1 : p 1) (hmul : ∀ x y, p x → p y → p (x * y))
    (hgen : ∀ x ∈ s, p x) (hfin : ∀ x ∈ s, IsOfFinOrder x) :
    ∀ g ∈ Subgroup.closure s, p g := by
  have hpow : ∀ x, p x → ∀ n : ℕ, p (x ^ n) := by
    intro x hx n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hx
  intro g hg
  induction hg using Subgroup.closure_induction'' with
  | mem x hx => exact hgen x hx
  | inv_mem x hx =>
      have h := hfin x hx
      have : x⁻¹ = x ^ (orderOf x - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, tsub_add_cancel_of_le (by exact h.orderOf_pos),
          pow_orderOf_eq_one]
      rw [this]
      exact hpow x (hgen x hx) _
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy

end Closure

section Comap

theorem mem_nonunits_comap_iff
    {F : Type} [Field F] (V : ValuationSubring F) (g : F ≃+* F) (f : F) :
    f ∈ (V.comap g.toRingHom).nonunits ↔ g f ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀, map_eq_zero_iff _ g.injective]

theorem mem_comap_iff'
    {F : Type} [Field F] (V : ValuationSubring F) (g : F ≃+* F) (f : F) :
    f ∈ V.comap g.toRingHom ↔ g f ∈ V :=
  ValuationSubring.mem_comap

end Comap

section W1

theorem closure_comap_igusaRing_perm
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (OIg : CuspidalType.ProjLine q → ValuationSubring ↥(fieldBar q M'))
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))
    (g : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M'))
    (hg : g ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') | ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}) :
    ∃ σ : Equiv.Perm (CuspidalType.ProjLine q), ∀ ℓ, (OIg ℓ).comap g.toAlgHom.toRingHom = OIg (σ ℓ) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨ζ', γ, hγ, rfl⟩ := hx
      exact hIg_perm ζ' γ hγ
  | one => exact ⟨1, fun i => by ext f; rfl⟩
  | mul x y _ _ hx hy =>
      obtain ⟨σ, hσ⟩ := hx
      obtain ⟨ρ, hρ⟩ := hy
      refine ⟨ρ * σ, fun i => ?_⟩
      have : (OIg i).comap (x * y).toAlgHom.toRingHom =
          ((OIg i).comap x.toAlgHom.toRingHom).comap y.toAlgHom.toRingHom := by
        ext f; rfl
      rw [this, hσ, hρ, Equiv.Perm.mul_apply]
  | inv x _ hx =>
      obtain ⟨σ, hσ⟩ := hx
      refine ⟨σ⁻¹, fun i => ?_⟩
      have h := hσ (σ⁻¹ i)
      rw [show σ (σ⁻¹ i) = i from by simp] at h
      have : ((OIg (σ⁻¹ i)).comap x.toAlgHom.toRingHom).comap x⁻¹.toAlgHom.toRingHom = OIg (σ⁻¹ i) := by
        ext f
        show x (x⁻¹ f) ∈ OIg (σ⁻¹ i) ↔ f ∈ OIg (σ⁻¹ i)
        rw [show x (x⁻¹ f) = f from by simp]
      rw [← this, h]

end W1

section LevelAut

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem isOfFinOrder_levelAutBar (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ζ : Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    IsOfFinOrder (levelAutBar q M' ζ γ) := by
  obtain ⟨G, hGfin, hmem, -⟩ := ModularCurve.FullLevel.exists_finite_subgroup_forall_levelAutBar_mem q M' hqM' ζ
  haveI := hGfin
  have h : IsOfFinOrder (⟨levelAutBar q M' ζ γ, hmem γ hγ⟩ : ↥G) := isOfFinOrder_of_finite _
  exact MonoidHom.isOfFinOrder G.subtype h

end LevelAut

section W2

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem exists_qExpand_and_forall_closure_exists_algEquiv_restrict
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →
    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∃ j' : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀),
      ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) ∧
      ∀ g ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') | ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
        ∃ σ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ≃ₐ[↥A₁] ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀),
          (∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), ((σ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) = g (f : ↥(fieldBar q M'))) ∧
          (∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), ((σ.symm f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) = g.symm (f : ↥(fieldBar q M'))) ∧
          σ j' = j' := by
  intro F₀ hK1 hSTAB hLD hRAT instA halg
  haveI : IsScalarTower ↥k₀ (AlgebraicClosure ℚ) ↥(fieldBar q M') := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  have hjq : ∀ (N : ℕ) [NeZero N], coeffEmb (AlgebraicClosure ℚ) jq ∈
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 N)) := by
    intro N _
    refine coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) ?_
    rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact modularFunctionField_le_full N (jq_mem N)
  have hcoe : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) =
      qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq) :=
    ModularCurve.coeffSemilinearAut.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) q jq
  have hj'mem : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) ∈ fieldBar q M' := by
    rw [hcoe]
    exact ModularCurve.FullLevel.qExpand_coe_mem_fieldBar_of_mem q M' hqM' _ (hjq (q * M'))
  let j'F : ↥(fieldBar q M') := ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq), hj'mem⟩
  have hj'T : j'F ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) :=
    (le_sup_right : F₀ ≤ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) (hRAT j'F ⟨qExpand ℚ q jq, rfl⟩)

  have hfix : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → levelAutBar q M' ζ' γ j'F = j'F := fun ζ' γ hγ =>
    ModularCurve.FullLevel.levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0 q M' hqM' ζ' γ hγ
      (coeffEmb (AlgebraicClosure ℚ) jq) (hjq M') j'F hcoe

  have hstab : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∀ f : ↥(fieldBar q M'), f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → levelAutBar q M' ζ' γ f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) := by
    intro ζ' γ hγ
    let τ' : ↥(fieldBar q M') →ₐ[↥k₀] ↥(fieldBar q M') := (levelAutBar q M' ζ' γ).toAlgHom.restrictScalars ↥k₀
    suffices h : (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ≤ ((IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).comap τ' by
      intro f hf
      exact h hf
    refine sup_le ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      rintro f ⟨x, hx, rfl⟩
      show τ' (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x) ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)
      rw [show τ' (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x
        from (levelAutBar q M' ζ' γ).commutes x]
      exact le_sup_left (b := F₀) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
    · intro f hf
      show levelAutBar q M' ζ' γ f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)
      exact le_sup_right (a := IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ)))) (hSTAB ζ' γ hγ f hf)

  have hP : ∀ g ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') | ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
      (∀ f : ↥(fieldBar q M'), f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → g f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ∧ g j'F = j'F := by
    refine forall_mem_closure_of_generators _ _ ⟨fun f hf => hf, rfl⟩ ?_ ?_ ?_
    · intro x y hx hy
      exact ⟨fun f hf => by rw [AlgEquiv.mul_apply]; exact hx.1 _ (hy.1 f hf), by rw [AlgEquiv.mul_apply, hy.2, hx.2]⟩
    · rintro τ ⟨ζ', γ, hγ, rfl⟩
      exact ⟨hstab ζ' γ hγ, hfix ζ' γ hγ⟩
    · rintro τ ⟨ζ', γ, hγ, rfl⟩
      exact isOfFinOrder_levelAutBar q M' hqM' ζ' γ hγ
  refine ⟨⟨j'F, hj'T⟩, rfl, fun g hg => ?_⟩
  obtain ⟨hg1, hg2⟩ := hP g hg
  obtain ⟨hi1, hi2⟩ := hP g⁻¹ (Subgroup.inv_mem _ hg)
  refine ⟨{ toFun := fun f => ⟨g (f : ↥(fieldBar q M')), hg1 _ f.2⟩
            invFun := fun f => ⟨g⁻¹ (f : ↥(fieldBar q M')), hi1 _ f.2⟩
            left_inv := fun f => Subtype.ext (by simp)
            right_inv := fun f => Subtype.ext (by simp)
            map_mul' := fun a b => Subtype.ext (by simp)
            map_add' := fun a b => Subtype.ext (by simp)
            commutes' := fun a => Subtype.ext (by
              dsimp only
              rw [halg]
              exact g.commutes _) }, fun f => rfl, fun f => ?_, Subtype.ext hg2⟩
  show g⁻¹ (f : ↥(fieldBar q M')) = g.symm (f : ↥(fieldBar q M'))
  rfl

end W2

section W4

open AlgebraicCurve.TwoChartIntegralModel in

theorem isIntegral_adjoin_map' {A : Type*} [CommRing A] {K K' : Type*} [Field K] [Field K'] [Algebra A K] [Algebra A K']
    (τ : K →ₐ[A] K') (t b : K) (hb : IsIntegral (Algebra.adjoin A ({t} : Set K)) b) :
    IsIntegral (Algebra.adjoin A ({τ t} : Set K')) (τ b) := by
  have hmap : (Algebra.adjoin A ({t} : Set K)).map τ = Algebra.adjoin A {τ t} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
  let φ : Algebra.adjoin A ({t} : Set K) →+* Algebra.adjoin A ({τ t} : Set K') :=
    { toFun := fun s => ⟨τ s, by rw [← hmap]; exact Subalgebra.mem_map.mpr ⟨s, s.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  exact hb.map_of_comp_eq φ τ.toRingHom (by ext s; rfl)

theorem mem_chartAlgInf_iff_of_algEquiv {A : Type} [CommRing A] {K K' : Type} [Field K] [Field K'] [Algebra A K]
    [Algebra A K'] (φ : K ≃ₐ[A] K') (t : K) (t' : K') (ht : φ t = t') (y : K) :
    y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A K t ↔
      φ y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A K' t' := by
  subst ht
  rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff, AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff]
  constructor
  · intro h
    have := isIntegral_adjoin_map' (φ : K →ₐ[A] K') t⁻¹ y h
    rwa [AlgEquiv.coe_algHom, map_inv₀] at this
  · intro h
    have := isIntegral_adjoin_map' (φ.symm : K' →ₐ[A] K) (φ t)⁻¹ (φ y) h
    rwa [AlgEquiv.coe_algHom, map_inv₀, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply] at this

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun s => HahnSeries.coeff s k) h
  simpa [coeffMap_coeff] using this

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in

theorem poleChart_bridge
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →
    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],
    ∀ (j' : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) →
    (∀ c, c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' →
      ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁ ∧
        (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁ ∧ s = 1 + j₁⁻¹ * a) ∧
        s * c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁) ∧
    (∀ c, c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁ →
      ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' ∧
        (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' ∧ s = 1 + j'⁻¹ * a) ∧
        s * c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j')  := by
  intro F₀ hK1 hLD hRAT instA halg j₁ hj₁ instj₁ j' hj'
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  obtain ⟨e, he⟩ := ModularCurve.FullLevel.exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap q M' k₀ K₁ hK₁
    F₀ hK1 (hLD K₁ hK₁) hRAT
  letI algAK : Algebra ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) := ((algebraMap ↥K₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))).comp (algebraMap ↥A₁ ↥K₁)).toAlgebra
  haveI hsc : @IsScalarTower ↥A₁ ↥K₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) inferInstance inferInstance algAK.toSMul :=
    @IsScalarTower.of_algebraMap_eq ↥A₁ ↥K₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) _ _ _ _ _ algAK (fun _ => rfl)
  have hι : Function.Injective (algebraMap ↥K₁ (AlgebraicClosure ℚ)) := fun a b h => Subtype.ext h
  have hιcomp : (algebraMap ↥K₁ (AlgebraicClosure ℚ)).comp (algebraMap ℚ ↥K₁) = algebraMap ℚ (AlgebraicClosure ℚ) :=
    Subsingleton.elim _ _
  have hcc : ∀ x : LaurentSeries ℚ, coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) (coeffEmb ↥K₁ x) =
      coeffEmb (AlgebraicClosure ℚ) x := fun x => by
    show coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) (coeffMap (algebraMap ℚ ↥K₁) x) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) x
    rw [coeffMap_coeffMap, hιcomp]

  have hecomm : ∀ a : ↥A₁, e (algebraMap ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) a) = algebraMap ↥A₁ _ a := by
    intro a
    have h1 := halg a
    have h2 : ((algebraMap ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) a : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries ↥K₁) = HahnSeries.single 0 ((a : ↥K₁)) := by
      rw [← algebraMap_laurentSeries_eq_single]; rfl
    apply Subtype.ext
    apply Subtype.ext
    rw [he, h2, h1, coeffMap_single]
    show HahnSeries.single 0 ((a : ↥K₁) : AlgebraicClosure ℚ) = ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))
    rw [← algebraMap_laurentSeries_eq_single]; rfl
  let eA : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) ≃ₐ[↥A₁] _ := AlgEquiv.ofRingEquiv (f := e) hecomm
  have heA : ∀ f, eA f = e f := fun _ => rfl

  let jK : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) := e.symm j₁
  let j'K : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) := e.symm j'
  have hejK : e jK = j₁ := e.apply_symm_apply j₁
  have hej'K : e j'K = j' := e.apply_symm_apply j'
  have hj₁coe : (((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [hj₁]; rfl
  have hqjq : qExpand ℚ q jq ≠ 0 := by
    intro h0
    have := congrArg (fun s => HahnSeries.coeff s ((q : ℤ) * (-1))) h0
    simp only [qExpand_coeff_mul, coeff_jq_neg_one] at this
    simp at this

  have hjKc : coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((jK : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries ↥K₁) =
      coeffEmb (AlgebraicClosure ℚ) jq := by rw [← he, hejK, hj₁coe]
  have hj'Kc : coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((j'K : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries ↥K₁) =
      coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) := by rw [← he, hej'K, hj']
  haveI : Fact (jK ≠ 0) := ⟨fun h0 => jq_ne_zero (coeffMap_injective (algebraMap ℚ (AlgebraicClosure ℚ))
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective (by
      show coeffEmb (AlgebraicClosure ℚ) jq = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) 0
      rw [← hjKc, h0, map_zero]; simp))⟩
  haveI : Fact (j'K ≠ 0) := ⟨fun h0 => hqjq (coeffMap_injective (algebraMap ℚ (AlgebraicClosure ℚ))
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective (by
      show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) 0
      rw [← hj'Kc, h0, map_zero]; simp))⟩
  obtain ⟨-, -, H3, H4⟩ :=
    ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
      q hq1 ↥K₁ (laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) ↥A₁ jK
      (by apply coeffMap_injective _ hι; rw [hjKc, hcc])
      j'K
      (by apply coeffMap_injective _ hι; rw [hj'Kc, hcc])
  have heAj : eA jK = j₁ := hejK
  have heAj' : eA j'K = j' := hej'K
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have hcK : e.symm c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) j'K := by
      rw [mem_chartAlgInf_iff_of_algEquiv eA j'K j' heAj', heA, e.apply_symm_apply]; exact hc
    obtain ⟨sK, hsK, ⟨aK, haK, hsdef⟩, hsc⟩ := H3 _ hcK
    refine ⟨e sK, ?_, ⟨e aK, ?_, ?_⟩, ?_⟩
    · rw [← heA, ← mem_chartAlgInf_iff_of_algEquiv eA jK j₁ heAj]; exact hsK
    · rw [← heA, ← mem_chartAlgInf_iff_of_algEquiv eA jK j₁ heAj]; exact haK
    · rw [hsdef, map_add, map_one, map_mul, map_inv₀, hejK]
    · have : e sK * c = e (sK * e.symm c) := by rw [map_mul, e.apply_symm_apply]
      rw [this, ← heA, ← mem_chartAlgInf_iff_of_algEquiv eA jK j₁ heAj]; exact hsc
  · have hcK : e.symm c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) jK := by
      rw [mem_chartAlgInf_iff_of_algEquiv eA jK j₁ heAj, heA, e.apply_symm_apply]; exact hc
    obtain ⟨sK, hsK, ⟨aK, haK, hsdef⟩, hsc⟩ := H4 _ hcK
    refine ⟨e sK, ?_, ⟨e aK, ?_, ?_⟩, ?_⟩
    · rw [← heA, ← mem_chartAlgInf_iff_of_algEquiv eA j'K j' heAj']; exact hsK
    · rw [← heA, ← mem_chartAlgInf_iff_of_algEquiv eA j'K j' heAj']; exact haK
    · rw [hsdef, map_add, map_one, map_mul, map_inv₀, hej'K]
    · have : e sK * c = e (sK * e.symm c) := by rw [map_mul, e.apply_symm_apply]
      rw [this, ← heA, ← mem_chartAlgInf_iff_of_algEquiv eA j'K j' heAj']; exact hsc

end W4

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

section ModEq

variable {L : Type} [Field L] [CharZero L]

theorem exists_monic_eval₂_coeffEmb (p : ℕ) [Fact p.Prime] [NeZero p] :
    ∃ Φ : Polynomial (Polynomial ℤ), Φ.Monic ∧
      Φ.eval₂ (aeval (ModularCurve.coeffEmb L ModularCurve.jq)).toRingHom
        (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) = 0 ∧
      Φ.eval₂ (aeval (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))).toRingHom
        (ModularCurve.coeffEmb L ModularCurve.jq) = 0 := by
  obtain ⟨data, hsymm⟩ := ModularCurve.exists_modularPolynomialData_evalSymm p
  have h0 : data.Φ.eval₂ (aeval ModularCurve.jq).toRingHom (ModularCurve.qExpand ℚ p ModularCurve.jq) = 0 := by
    have := data.eval_eq_zero
    rwa [ModularCurve.evalAtJ_def] at this
  have h1 : data.Φ.eval₂ (aeval (ModularCurve.qExpand ℚ p ModularCurve.jq)).toRingHom ModularCurve.jq = 0 := by
    rw [← hsymm]; exact h0
  have key : ∀ x y : LaurentSeries ℚ,
      (ModularCurve.coeffEmb L) (data.Φ.eval₂ (aeval x).toRingHom y)
        = data.Φ.eval₂ (aeval (ModularCurve.coeffEmb L x)).toRingHom (ModularCurve.coeffEmb L y) := by
    intro x y
    rw [hom_eval₂]
    congr 1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp
    · simp
  refine ⟨data.Φ, data.monic, ?_, ?_⟩
  · rw [← key, h0, map_zero]
  · rw [← key, h1, map_zero]

end ModEq

section Generic

variable {A T S : Type} [CommRing A] [Field T] [CommRing S] [Algebra A T]

theorem isIntegral_adjoin_of_eval₂_hom (ι : T →+* S) (hι : Function.Injective ι) (a b : T)
    (Φ : Polynomial (Polynomial ℤ)) (hm : Φ.Monic)
    (h : Φ.eval₂ (aeval (ι a)).toRingHom (ι b) = 0) :
    IsIntegral (Algebra.adjoin A ({a} : Set T)) b := by
  let a' : Algebra.adjoin A ({a} : Set T) := ⟨a, Algebra.self_mem_adjoin_singleton A a⟩
  let θ : Polynomial ℤ →+* Algebra.adjoin A ({a} : Set T) := (aeval a').toRingHom
  refine ⟨Φ.map θ, hm.map θ, ?_⟩
  rw [eval₂_map]
  apply hι
  rw [hom_eval₂, map_zero]
  convert h using 2
  refine Polynomial.ringHom_ext (fun n => by simp) ?_
  simp [θ, a']

end Generic

section JQ

private theorem _root_.TH1AuxIg.isIntegral_adjoin_jq_qExpand {A T : Type} [CommRing A] [Field T] [Algebra A T]
    (p : ℕ) [Fact p.Prime] (a b : T)
    (ι : T →+* LaurentSeries (AlgebraicClosure ℚ)) (hι : Function.Injective ι)
    (ha : ι a = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq)
    (hb : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ι b = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ p ModularCurve.jq)) :
    IsIntegral (Algebra.adjoin A ({a} : Set T)) b ∧ IsIntegral (Algebra.adjoin A ({b} : Set T)) a := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨Φ, hm, h1, h2⟩ := exists_monic_eval₂_coeffEmb (L := AlgebraicClosure ℚ) p
  refine ⟨isIntegral_adjoin_of_eval₂_hom ι hι a b Φ hm ?_, isIntegral_adjoin_of_eval₂_hom ι hι b a Φ hm ?_⟩
  · convert h1 using 2 <;> first | rfl | exact Polynomial.ringHom_ext (fun n => by simp) (by simp [ha])
  · convert h2 using 2 <;> first | rfl | exact Polynomial.ringHom_ext (fun n => by simp) (by simp [hb])

p2m_export "TH1AuxIg" "isIntegral_adjoin_jq_qExpand"
end JQ

section W6

theorem evalAt_algebraMap' {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] (P : Place K Fb) (hP : P.IsRational)
    (c : K) : P.evalAt (algebraMap K Fb c) = c := by
  apply P.algebraMap_residueField_injective
  rw [P.algebraMap_evalAt hP (P.algebraMap_mem' c)]
  rw [show (⟨algebraMap K Fb c, P.algebraMap_mem' c⟩ : ↥P.toValuationSubring) = algebraMap K ↥P.toValuationSubring c from
    Subtype.ext (by rw [Place.coe_algebraMap])]
  rfl

noncomputable def resEquiv' {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] (P : Place K Fb) (hP : P.IsRational) :
    K ≃+* P.ResidueField :=
  RingEquiv.ofBijective (algebraMap K P.ResidueField) ⟨P.algebraMap_residueField_injective, hP⟩

noncomputable def evalHom' {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] (P : Place K Fb) (hP : P.IsRational) :
    ↥P.toValuationSubring →+* K :=
  (resEquiv' P hP).symm.toRingHom.comp (IsLocalRing.residue ↥P.toValuationSubring)

theorem evalHom'_apply {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] (P : Place K Fb) (hP : P.IsRational)
    (f : ↥P.toValuationSubring) : evalHom' P hP f = P.evalAt (f : Fb) := by
  apply (resEquiv' P hP).injective
  show resEquiv' P hP ((resEquiv' P hP).symm (IsLocalRing.residue _ f)) = algebraMap K P.ResidueField (P.evalAt (f : Fb))
  rw [RingEquiv.apply_symm_apply, Place.algebraMap_evalAt P hP f.2]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem mem_and_evalAt_mem_of_qExpand
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →
    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],
    ∀ (j' : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) →
    ∀ (Q : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), Q.IsRational →
      (j' : ↥(fieldBar q M')) ∈ Q.toValuationSubring → Q.evalAt (j' : ↥(fieldBar q M')) ∈ A →
      (j₁ : ↥(fieldBar q M')) ∈ Q.toValuationSubring ∧ Q.evalAt (j₁ : ↥(fieldBar q M')) ∈ A  := by
  intro F₀ hK1 hLD hRAT instA halg j₁ hj₁ instj₁ j' hj' Q hQ hj'Q hj'A
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hj₁coe : (((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [hj₁]; rfl

  letI algAF : Algebra ↥A ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥A (AlgebraicClosure ℚ))).toAlgebra
  have halgA : ∀ a : ↥A, algebraMap ↥A ↥(fieldBar q M') a =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ) := fun _ => rfl

  obtain ⟨-, hint⟩ := isIntegral_adjoin_jq_qExpand (A := ↥A) q (j₁ : ↥(fieldBar q M')) (j' : ↥(fieldBar q M'))
    (algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ)))
    (fun a b h => Subtype.ext h) hj₁coe hj'

  have hS : ∀ z ∈ Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M')), z ∈ Q.toValuationSubring := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        rw [hx]; exact hj'Q
    | algebraMap a => rw [halgA]; exact Q.algebraMap_mem' _
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  let φ : ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M'))) →+* ↥Q.toValuationSubring :=
    { toFun := fun z => ⟨(z : ↥(fieldBar q M')), hS z z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }

  have hint₁ : IsIntegral ↥Q.toValuationSubring ((j₁ : ↥(fieldBar q M'))) :=
    hint.map_of_comp_eq φ (RingHom.id ↥(fieldBar q M')) (by ext z; rfl)
  obtain ⟨J, hJ⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥Q.toValuationSubring) (K := ↥(fieldBar q M'))).mp hint₁
  have hj₁Q : (j₁ : ↥(fieldBar q M')) ∈ Q.toValuationSubring := by rw [← hJ]; exact J.2
  refine ⟨hj₁Q, ?_⟩

  let θ : ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M'))) →+* AlgebraicClosure ℚ :=
    (evalHom' Q hQ).comp φ
  have hθ : ∀ z, θ z = Q.evalAt (z : ↥(fieldBar q M')) := fun z => evalHom'_apply Q hQ (φ z)
  have hθA : ∀ z : ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M'))), θ z ∈ A := by
    intro z
    obtain ⟨z, hz⟩ := z
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [hθ]; exact hj'A
    | algebraMap a =>
        rw [hθ]
        dsimp only
        rw [halgA, evalAt_algebraMap' Q hQ]
        exact a.2
    | add x y hx' hy' hx hy =>
        have : (⟨x + y, Subalgebra.add_mem _ hx' hy'⟩ :
            ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M')))) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
        rw [this, map_add]; exact add_mem hx hy
    | mul x y hx' hy' hx hy =>
        have : (⟨x * y, Subalgebra.mul_mem _ hx' hy'⟩ :
            ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M')))) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
        rw [this, map_mul]; exact mul_mem hx hy
  let θA : ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M'))) →+* ↥A :=
    θ.codRestrict A.toSubring hθA

  obtain ⟨P, hPm, hPj⟩ := hint
  have hJcoe : ((J : ↥Q.toValuationSubring) : ↥(fieldBar q M')) = (j₁ : ↥(fieldBar q M')) := hJ
  have hevJ : Polynomial.eval₂ φ J P = 0 := by
    apply Subtype.val_injective
    have h1 : (((Polynomial.eval₂ φ J P : ↥Q.toValuationSubring)) : ↥(fieldBar q M')) =
        Polynomial.eval₂ ((algebraMap ↥Q.toValuationSubring ↥(fieldBar q M')).comp φ)
          ((algebraMap ↥Q.toValuationSubring ↥(fieldBar q M')) J) P :=
      Polynomial.hom_eval₂ P φ (algebraMap ↥Q.toValuationSubring ↥(fieldBar q M')) J
    rw [h1, show (algebraMap ↥Q.toValuationSubring ↥(fieldBar q M')).comp φ =
        algebraMap ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M'))) ↥(fieldBar q M') from
          RingHom.ext fun z => rfl,
      show (algebraMap ↥Q.toValuationSubring ↥(fieldBar q M')) J = (j₁ : ↥(fieldBar q M')) from hJ, ZeroMemClass.coe_zero]
    exact hPj
  have hint₂ : IsIntegral ↥A (Q.evalAt (j₁ : ↥(fieldBar q M'))) := by
    refine ⟨P.map θA, hPm.map θA, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥A (AlgebraicClosure ℚ)).comp θA = (evalHom' Q hQ).comp φ := by
      ext z; rfl
    have hev : Q.evalAt (j₁ : ↥(fieldBar q M')) = evalHom' Q hQ J := by rw [evalHom'_apply, hJcoe]
    rw [hcomp, hev, ← Polynomial.hom_eval₂, hevJ, map_zero]
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hint₂
  rw [← ha]; exact a.2

end W6

end TH1AuxIg

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →
    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∃ j' : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀),
      ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) ∧
      j' ∈ TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ ∧
      j₁ ∈ TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j' ∧
      ∀ g ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
        ∃ σ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ≃ₐ[↥A₁] ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀),
          (∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), ((σ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) = g (f : ↥(fieldBar q M'))) ∧
          (∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), ((σ.symm f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) = g.symm (f : ↥(fieldBar q M'))) ∧
          σ j' = j' ∧
          (∀ b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), b ∈ TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ ↔ σ b ∈ TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∧
          (∀ b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), b ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j' ↔ σ b ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j') ∧
          (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
            (g • P).IsRational ∧
            ∀ f : ↥(fieldBar q M'), (g • P).evalAt (g f) = P.evalAt f ∧
              (g f ∈ (g • P).toValuationSubring ↔ f ∈ P.toValuationSubring)) := by
  intro F₀ hK1 hSTAB hLD hRAT instA₁ halg j₁ hj₁
  obtain ⟨j', hj', hW2⟩ :=
    TH1AuxIg.exists_qExpand_and_forall_closure_exists_algEquiv_restrict q hq3 M' hqM' k₀ K₁ hK₁ A₁ F₀ hK1 hSTAB hLD hRAT halg
  have hι : Function.Injective ((algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ))).comp (algebraMap (type_of% j₁) ↥(fieldBar q M')) :
      (type_of% j₁) →+* LaurentSeries (AlgebraicClosure ℚ)) := by
    intro a b h
    exact Subtype.ext (Subtype.ext h)
  have hmut := TH1Transport.isIntegral_adjoin_jq_qExpand (A := ↥A₁) q j₁ j'
    ((algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ))).comp (algebraMap (type_of% j₁) ↥(fieldBar q M'))) hι
    (by show ((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = _; rw [hj₁]; rfl)
    (by show ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = _; rw [hj'])
  refine ⟨j', hj', (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff ↥A₁ _).2 hmut.1,
    (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff ↥A₁ _).2 hmut.2, fun g hg => ?_⟩
  obtain ⟨σ, hσ, hσsymm, hσj'⟩ := hW2 g hg
  have hσj'inv : σ j'⁻¹ = j'⁻¹ := by rw [map_inv₀, hσj']
  have hself : IsIntegral ↥(Algebra.adjoin ↥A₁ ({j'⁻¹} : Set _)) j'⁻¹ :=
    isIntegral_algebraMap (x := (⟨j'⁻¹, Algebra.self_mem_adjoin_singleton ↥A₁ j'⁻¹⟩ : ↥(Algebra.adjoin ↥A₁ ({j'⁻¹} : Set _))))
  refine ⟨σ, hσ, hσsymm, hσj', fun b => TH1Transport.mem_chartAlg_singleton_iff_map_mem σ hmut.1 hmut.2 hσj' b,
    fun b => TH1Transport.mem_chartAlg_singleton_iff_map_mem σ hself hself hσj'inv b, fun P hP => ?_⟩
  exact ⟨(Place.Transport.isRational_smul_iff g P).2 hP,
    fun f => ⟨Place.Transport.evalAt_smul g P hP f, Place.Transport.mem_smul_iff' g P f⟩⟩

end S_ModularCurve_FullLevel_exists_qExpand_mem_chartAlgFin_and_forall_mem_closure_levelAutBar_exists_algEquiv_levelField_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_qExpand_mem_chartAlgFin_and_forall_mem_closure_levelAutBar_exists_algEquiv_levelField_of_eq_three (solution)
