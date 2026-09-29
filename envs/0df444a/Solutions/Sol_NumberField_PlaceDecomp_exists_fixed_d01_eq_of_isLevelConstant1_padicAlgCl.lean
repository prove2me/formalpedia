-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4d7d7fe3-2246-5618-8956-b35f078b5324

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_groupCohomology_exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup
import Theorems.Thm_groupCohomology_exists_isGalois_of_isLevelConstant1
import Theorems.Thm_localGaloisToGlobal_mem_fixingSubgroup_iff
import Theorems.Thm_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image
import Theorems.Thm_IntermediateField_exists_le_adjoin_padicEmbedding_image
import Theorems.Thm_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory NumberField P2MW.S_NumberField_PlaceDecomp_exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl.NumberField IsDedekindDomain ExtCitation"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl.NumberField.PlaceDecomp NumberField.InfPlaceDecomp"

namespace NumberField
p2m_export "NumberField" "PlaceDecomp.decomp"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp"
namespace H90PadicAlgCl
p2m_open "NumberField.PlaceDecomp NumberField"

open groupCohomology

section Abstract

variable {k : Type} [CommRing k] {G D : Type} [Group G] [Group D]

variable (π : G →* D) (α : Type) (A : Rep k G) in

noncomputable def asLin : ((ihom (Rep.res π (Rep.free k D α))).obj A) →ₗ[k] ((Rep.res π (Rep.free k D α)) →ₗ[k] A) :=
  LinearMap.id

lemma asLin_injective (π : G →* D) (α : Type) (A : Rep k G) : Function.Injective (asLin π α A) :=
  fun _ _ h => h

lemma asLin_ρ_single (π : G →* D) (α : Type) (A : Rep k G)
    (g : G) (f : (ihom (Rep.res π (Rep.free k D α))).obj A) (a : α) (d : D) (n : k) :
    asLin π α A (((ihom (Rep.res π (Rep.free k D α))).obj A).ρ g f) (Finsupp.single a (MonoidAlgebra.single d n)) =
      A.ρ g (asLin π α A f (Finsupp.single a (MonoidAlgebra.single ((π g)⁻¹ * d) n))) := by
  erw [Rep.ihom_obj_ρ_apply]
  change A.ρ g (asLin π α A f ((Rep.res π (Rep.free k D α)).ρ g⁻¹ (Finsupp.single a (MonoidAlgebra.single d n)))) = _
  have h : (Rep.res π (Rep.free k D α)).ρ g⁻¹ (Finsupp.single a (MonoidAlgebra.single d n)) =
      Finsupp.single a (MonoidAlgebra.single (π g⁻¹ * d) n) :=
    Representation.free_single_single (π g⁻¹) d a n
  rw [h, map_inv]

theorem exists_fixed_d01_eq_abstract (π : G →* D) (s : D → G) (hs : ∀ d, π (s d) = d)
    (α : Type) (A : Rep k G)
    (u : cocycles₁ ((ihom (Rep.res π (Rep.free k D α))).obj A))
    (m : α → A)
    (hm : ∀ (a : α) (h : G), π h = 1 →
      asLin π α A (u h) (Finsupp.single a (MonoidAlgebra.single 1 1)) = A.ρ h (m a) - m a)
    (T : Set G)
    (hTm : ∀ t ∈ T, ∀ (g : G) (a : α), A.ρ t (A.ρ g (m a)) = A.ρ g (m a))
    (hTπ : ∀ t ∈ T, π t = 1)
    (hTu : ∀ t ∈ T, ∀ g : G, ((ihom (Rep.res π (Rep.free k D α))).obj A).ρ t (u g) = u g) :
    ∃ χ : (ihom (Rep.res π (Rep.free k D α))).obj A,
      (∀ t ∈ T, ∀ x, A.ρ t (LinearMap.toAddMonoidHom χ x) = LinearMap.toAddMonoidHom χ x) ∧
      (d₀₁ _).hom χ = (u : G → (ihom (Rep.res π (Rep.free k D α))).obj A) := by
  classical
  let e : α → D → Rep.res π (Rep.free k D α) := fun a d => Finsupp.single a (MonoidAlgebra.single d 1)
  let U : G → α → D → A := fun g a d => asLin π α A (u g) (e a d)
  have hcoc : ∀ g h : G, u (g * h) = ((ihom (Rep.res π (Rep.free k D α))).obj A).ρ g (u h) + u g :=
    (mem_cocycles₁_iff (u : G → _)).1 u.2

  have hU : ∀ (g h : G) (a : α) (d : D), U (g * h) a d = A.ρ g (U h a ((π g)⁻¹ * d)) + U g a d := by
    intro g h a d
    simp only [U, e]
    rw [hcoc g h, map_add, LinearMap.add_apply, asLin_ρ_single]

  let val : α → D → A := fun a d => A.ρ (s d) (m a) - U (s d) a d
  have hval : ∀ (a : α) (d : D) (g : G), π g = d → A.ρ g (m a) - U g a d = val a d := by
    intro a d g hg
    have hπh : π ((s d)⁻¹ * g) = 1 := by rw [map_mul, map_inv, hs, hg, inv_mul_cancel]
    have h1 := hU (s d) ((s d)⁻¹ * g) a d
    rw [mul_inv_cancel_left, hs d, inv_mul_cancel] at h1
    have h2 : U ((s d)⁻¹ * g) a 1 = A.ρ ((s d)⁻¹ * g) (m a) - m a := hm a _ hπh
    rw [h2, map_sub, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1
    simp only [val]
    rw [h1]
    abel
  let χ : (Rep.res π (Rep.free k D α)) →ₗ[k] A :=
    Finsupp.lsum k fun a => (Finsupp.lsum k fun d => LinearMap.toSpanSingleton k A (val a d)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
  have hχ : ∀ a d, χ (e a d) = val a d := by
    intro a d
    change (Finsupp.lsum k fun a => (Finsupp.lsum k fun d => LinearMap.toSpanSingleton k A (val a d)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) (Finsupp.single a (MonoidAlgebra.single d 1)) = val a d
    rw [Finsupp.lsum_single, LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidAlgebra.coeffLinearEquiv_apply,
      MonoidAlgebra.coeff_single, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, one_smul]
  have hasLinχ : asLin π α A χ = χ := rfl
  refine ⟨χ, ?_, ?_⟩
  ·
    intro t ht
    suffices hcomp : (A.ρ t) ∘ₗ χ = χ from fun x => LinearMap.congr_fun hcomp x
    refine Finsupp.lhom_ext' fun a => MonoidAlgebra.lhom_ext' fun d => LinearMap.ext_ring ?_
    change A.ρ t (χ (e a d)) = χ (e a d)
    rw [hχ]
    simp only [val, map_sub]
    rw [hTm t ht]
    congr 1
    have h2 := congrArg (fun f => asLin π α A f (e a d)) (hTu t ht (s d))
    dsimp only at h2
    rw [asLin_ρ_single, hTπ t ht, inv_one, one_mul] at h2
    exact h2
  ·
    funext g
    rw [d₀₁_hom_apply]
    apply asLin_injective π α A
    rw [map_sub, hasLinχ]
    refine Finsupp.lhom_ext' fun a => MonoidAlgebra.lhom_ext' fun d => LinearMap.ext_ring ?_
    change asLin π α A (((ihom (Rep.res π (Rep.free k D α))).obj A).ρ g χ) (e a d) - χ (e a d) = U g a d
    rw [asLin_ρ_single, hasLinχ, hχ, hχ]
    have hkey := hval a d (g * s ((π g)⁻¹ * d)) (by rw [map_mul, hs, mul_inv_cancel_left])
    rw [← hkey]
    simp only [val, map_sub, map_mul, Module.End.mul_apply]
    rw [hU g (s ((π g)⁻¹ * d)) a d]
    abel

end Abstract

section Galois

lemma map_conj_eq_one_iff {G H : Type*} [Group G] [Group H] (φ : G →* H) (σ g : G) :
    φ (σ⁻¹ * g * σ) = 1 ↔ φ g = 1 := by
  rw [map_mul, map_mul, map_inv, mul_eq_one_iff_eq_inv, inv_mul_eq_iff_eq_mul, mul_inv_cancel]

lemma restrictNormalHom_eq_one_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] [Normal K E] (g : L ≃ₐ[K] L) :
    AlgEquiv.restrictNormalHom E g = 1 ↔ ∀ x : E, g (algebraMap E L x) = algebraMap E L x := by
  constructor
  · intro h x
    have hc := AlgEquiv.restrictNormal_commutes g E x
    change algebraMap E L (AlgEquiv.restrictNormalHom E g x) = g (algebraMap E L x) at hc
    rw [h] at hc
    exact hc.symm
  · intro h
    ext x
    apply (algebraMap E L).injective
    change algebraMap E L (g.restrictNormal E x) = algebraMap E L x
    rw [AlgEquiv.restrictNormal_commutes]
    exact h x

lemma conj_mem_fixingSubgroup_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [Normal K E] (σ g : L ≃ₐ[K] L) :
    σ⁻¹ * g * σ ∈ E.fixingSubgroup ↔ g ∈ E.fixingSubgroup := by
  have key : ∀ h : L ≃ₐ[K] L, h ∈ E.fixingSubgroup ↔ AlgEquiv.restrictNormalHom E h = 1 := fun h => by
    rw [restrictNormalHom_eq_one_iff, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun H x => H x x.2, fun H x hx => H ⟨x, hx⟩⟩
  rw [key, key, map_conj_eq_one_iff]

end Galois

section Generic

variable {k : Type} [CommRing k] {G D : Type} [Group G] [Group D]

theorem exists_fixed_d01_eq_of_h90
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (π : G →* D) (hπs : Function.Surjective π)
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ t, r t ∈ F.fixingSubgroup → π t = 1)
    (A : Rep k G)
    (h90 : ∀ v : G → A, (∀ g h, π g = 1 → v (g * h) = A.ρ g (v h) + v g) → IsLevelConstant₁ r v →
      ∃ m : A, (∃ Fm : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ Fm ∧
          ∀ t, r t ∈ Fm.fixingSubgroup → A.ρ t m = m) ∧
        ∀ h, π h = 1 → v h = A.ρ h m - m)
    (α : Type) [Finite α] (u : cocycles₁ ((ihom (Rep.res π (Rep.free k D α))).obj A))
    (hu : IsLevelConstant₁ r u) :
    ∃ χ : (ihom (Rep.res π (Rep.free k D α))).obj A,
      (∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₂ ∧
        ∀ t, r t ∈ F₂.fixingSubgroup → ∀ x, A.ρ t (LinearMap.toAddMonoidHom χ x) = LinearMap.toAddMonoidHom χ x) ∧
      (d₀₁ _).hom χ = (u : G → _) := by
  classical

  choose s hs using hπs

  obtain ⟨F₁, hF₁fd, _, hF₁⟩ := groupCohomology.exists_isGalois_of_isLevelConstant1 hu
  have hu1 : u 1 = 0 := cocycles₁_map_one u
  have hcoc : ∀ g h, u (g * h) = ((ihom (Rep.res π (Rep.free k D α))).obj A).ρ g (u h) + u g :=
    (mem_cocycles₁_iff (u : G → _)).1 u.2
  have hut : ∀ t, r t ∈ F₁.fixingSubgroup → u t = 0 := fun t ht =>
    ((congrArg (fun g => u g) (one_mul t)).symm.trans (hF₁ 1 t ht).1).trans hu1
  have huinv : ∀ t, r t ∈ F₁.fixingSubgroup → ∀ g,
      ((ihom (Rep.res π (Rep.free k D α))).obj A).ρ t (u g) = u g := fun t ht g => by
    have h := hcoc t g
    rw [(hF₁ g t ht).2, hut t ht, add_zero] at h
    exact h.symm

  have h90a : ∀ a : α, ∃ m : A, (∃ Fm : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ Fm ∧
        ∀ t, r t ∈ Fm.fixingSubgroup → A.ρ t m = m) ∧
      ∀ h, π h = 1 → asLin π α A (u h) (Finsupp.single a (MonoidAlgebra.single 1 1)) = A.ρ h m - m := by
    intro a
    refine h90 (fun g => asLin π α A (u g) (Finsupp.single a (MonoidAlgebra.single 1 1))) (fun g h hg => ?_)
      (hu.comp (fun x => asLin π α A x (Finsupp.single a (MonoidAlgebra.single 1 1))))
    dsimp only
    rw [hcoc g h, map_add, LinearMap.add_apply, asLin_ρ_single, hg, inv_one, one_mul]
  choose m hmlev hm using h90a
  choose Fa hFafd hFa using hmlev

  have hmlc : IsLevelConstant₁ r (fun g => fun a => A.ρ g (m a)) := by
    haveI : ∀ a, FiniteDimensional ℚ (Fa a) := hFafd
    refine ⟨⨆ a, Fa a, inferInstance, fun g t ht => ?_⟩
    funext a
    show A.ρ (g * t) (m a) = A.ρ g (m a)
    rw [map_mul, Module.End.mul_apply, hFa a t (IntermediateField.fixingSubgroup_antitone (le_iSup Fa a) ht)]
  obtain ⟨Fm, hFmfd, _, hFm⟩ := groupCohomology.exists_isGalois_of_isLevelConstant1 hmlc

  obtain ⟨F, hFfd, hF⟩ := hπlev
  haveI := hF₁fd; haveI := hFmfd; haveI := hFfd
  obtain ⟨χ, hχT, hχ⟩ := exists_fixed_d01_eq_abstract π s hs α A u m hm
    {t | r t ∈ (F ⊔ F₁ ⊔ Fm).fixingSubgroup}
    (fun t ht g a => by
      have h1 : A.ρ (t * g) (m a) = A.ρ g (m a) :=
        congrFun (hFm g t (IntermediateField.fixingSubgroup_antitone le_sup_right ht)).2 a
      rw [map_mul, Module.End.mul_apply] at h1
      exact h1)
    (fun t ht => hF t (IntermediateField.fixingSubgroup_antitone (le_sup_left.trans le_sup_left) ht))
    (fun t ht g => huinv t (IntermediateField.fixingSubgroup_antitone (le_sup_right.trans le_sup_left) ht) g)
  exact ⟨χ, ⟨F ⊔ F₁ ⊔ Fm, inferInstance, hχT⟩, hχ⟩

end Generic

theorem h90_padicAlgCl (q : ℕ) [Fact q.Prime] {D : Type} [Group D]
    (π : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) →* D)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F]
    (hker : ∀ g, π g = 1 ↔ localGaloisToGlobal q g ∈ F.fixingSubgroup)
    (v : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))
    (hv : ∀ g h, π g = 1 → v (g * h) = (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ g (v h) + v g)
    (hlc : IsLevelConstant₁ (localGaloisToGlobal q) v) :
    ∃ m : Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q),
      (∃ Fm : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ Fm ∧
        ∀ t, localGaloisToGlobal q t ∈ Fm.fixingSubgroup → (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ t m = m) ∧
      ∀ h, π h = 1 → v h = (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ h m - m := by
  classical
  let KF : IntermediateField ℚ_[q] (PadicAlgCl q) :=
    IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ)))
  haveI : FiniteDimensional ℚ_[q] KF := IntermediateField.finiteDimensional_adjoin_padicEmbedding_image q F
  have hKF : ∀ τ, π τ = 1 ↔ τ ∈ KF.fixingSubgroup := fun τ =>
    (hker τ).trans (localGaloisToGlobal_mem_fixingSubgroup_iff q F τ)
  have hMρ : ∀ (g : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (x : (PadicAlgCl q)ˣ),
      (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ g (Additive.ofMul x) = Additive.ofMul (g • x) := fun _ _ => rfl
  have hMρ' : ∀ (g : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (y : Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)),
      (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ g y =
        Additive.ofMul (g • Additive.toMul (α := (PadicAlgCl q)ˣ) y) := fun _ _ => rfl
  have hsmul : ∀ (g : ↥KF.fixingSubgroup) (x : (PadicAlgCl q)ˣ), g • x = (g : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) • x :=
    fun _ _ => rfl
  obtain ⟨F₁, hF₁fd, hF₁⟩ := hlc
  let v' : ↥KF.fixingSubgroup → (PadicAlgCl q)ˣ := fun h => Additive.toMul (v (h : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q))
  have hv' : IsMulCocycle₁ v' := by
    intro g h
    apply Additive.ofMul.injective
    have hg1 : π (g : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) = 1 := (hKF g).2 g.2
    simp only [v', ofMul_mul, ofMul_toMul, Subgroup.coe_mul]
    rw [hv _ _ hg1, hMρ', hsmul]
    try rfl
  obtain ⟨mα, hmα⟩ := groupCohomology.exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup KF hv'
    ⟨IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F₁ : Set (AlgebraicClosure ℚ))),
      @IntermediateField.finiteDimensional_adjoin_padicEmbedding_image q _ F₁ hF₁fd, fun g t ht => by
        have ht' : localGaloisToGlobal q t ∈ F₁.fixingSubgroup :=
          (localGaloisToGlobal_mem_fixingSubgroup_iff q F₁ t).2 ht
        simp only [v', Subgroup.coe_mul, hF₁ _ _ ht']⟩

  obtain ⟨E, hEfd, hE⟩ :=
    IntermediateField.exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq (K := ℚ_[q]) mα
  haveI := hEfd
  obtain ⟨Fm, hFmfd, hle⟩ := IntermediateField.exists_le_adjoin_padicEmbedding_image q E
  refine ⟨Additive.ofMul mα, ⟨Fm, hFmfd, fun t ht => ?_⟩, fun h hh => ?_⟩
  · rw [hMρ, hE t (IntermediateField.fixingSubgroup_antitone hle
      ((localGaloisToGlobal_mem_fixingSubgroup_iff q Fm t).1 ht))]
    try rfl
  · have key : Additive.toMul (α := (PadicAlgCl q)ˣ) (v h) = h • mα / mα := hmα ⟨h, (hKF h).1 hh⟩
    show (v h : Additive (PadicAlgCl q)ˣ) = (Additive.ofMul (h • mα) : Additive (PadicAlgCl q)ˣ) - Additive.ofMul mα
    rw [← ofMul_div, ← key]
    try rfl

end NumberField.PlaceDecomp.H90PadicAlgCl

open NumberField.PlaceDecomp.H90PadicAlgCl groupCohomology in

theorem solution
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (hmem : ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) ∈ NumberField.PlaceDecomp.decomp ℚ ↥F w)
    (hsurj : ∀ d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w), ∃ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ))
    (heqv : ∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
      (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) →
      ∀ x : w.adicCompletion ↥F, Φ (d • x) = τ (Φ x))
    (hcont : Continuous Φ) :
    ∀ (α : Type) [Finite α]
        (π : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
        (_ : ∀ τ, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
          AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ))
        (u : groupCohomology.cocycles₁ ((ihom (Rep.res π (Rep.free ℤ ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) α))).obj
          (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))),
      groupCohomology.IsLevelConstant₁ (localGaloisToGlobal q)
        (u : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → (ihom (Rep.res π (Rep.free ℤ ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) α))).obj
          (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) →
      ∃ χ : (ihom (Rep.res π (Rep.free ℤ ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) α))).obj (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)),
        (∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₂ ∧
          ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, localGaloisToGlobal q τ ∈ F₂.fixingSubgroup →
            ∀ x, (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ τ (LinearMap.toAddMonoidHom χ x) = LinearMap.toAddMonoidHom χ x) ∧
        (groupCohomology.d₀₁ _).hom χ = (u : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → _) := by
  intro α _ π hπ u hu
  have hker : ∀ τ, π τ = 1 ↔ localGaloisToGlobal q τ ∈ F.fixingSubgroup := fun τ => by
    rw [← OneMemClass.coe_eq_one, hπ τ, map_conj_eq_one_iff, restrictNormalHom_eq_one_iff,
      IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.2⟩
  exact exists_fixed_d01_eq_of_h90 (localGaloisToGlobal q) π
    (fun d => (hsurj d).imp fun τ hτ => Subtype.ext ((hπ τ).trans hτ.symm))
    ⟨F, inferInstance, fun t ht => (hker t).2 ht⟩ _ (h90_padicAlgCl q π F hker) α u hu

end S_NumberField_PlaceDecomp_exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_fixed_d01_eq_of_isLevelConstant1_padicAlgCl (solution)
