-- Prove2me | solution 1 for IsRegularLocalRing.exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/9930fa8d-5b3f-55c3-8313-59d531ef49e8

import Mathlib
import Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Theorems.Thm_IsRegularLocalRing_of_etale_of_isLocalRing_of_maximalIdeal_eq_span_pair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem

set_option autoImplicit false

open scoped TensorProduct
namespace SmoothBC44
namespace G

theorem algebraMap_tensorProduct_ne_zero {W B W' : Type*} [CommRing W] [CommRing B] [Algebra W B]
    [CommRing W'] [Algebra W W'] [Module.Flat W W'] (hinj : Function.Injective (algebraMap W B))
    (w : W) (hw : algebraMap W W' w ≠ 0) : algebraMap W (B ⊗[W] W') w ≠ 0 := by
  rw [Algebra.TensorProduct.algebraMap_apply']
  intro h
  apply hw
  apply Algebra.TensorProduct.includeRight_injective (R := W) (A := B) (B := W') hinj
  rw [Algebra.TensorProduct.includeRight_apply, h, map_zero]

theorem isNoetherianRing_tensorProduct {W B W' : Type*} [CommRing W] [CommRing B] [Algebra W B]
    [IsNoetherianRing B] [CommRing W'] [Algebra W W'] [Module.Finite W W'] : IsNoetherianRing (B ⊗[W] W') :=
  isNoetherianRing_iff.mpr (isNoetherian_of_tower B (isNoetherian_of_isNoetherianRing_of_finite B (B ⊗[W] W')))

theorem exists_sub_one_tmul_mem_map {W B W' : Type*} [CommRing W] [CommRing B] [Algebra W B] [IsLocalRing B]
    [CommRing W'] [Algebra W W']
    (hres : ∀ b : B, ∃ w : W, b - algebraMap W B w ∈ IsLocalRing.maximalIdeal B)
    (z : B ⊗[W] W') : ∃ w' : W', z - (1 : B) ⊗ₜ[W] w' ∈
      (IsLocalRing.maximalIdeal B).map (algebraMap B (B ⊗[W] W')) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [TensorProduct.tmul_zero, sub_zero]; exact Ideal.zero_mem _⟩
  | tmul b w' =>
    obtain ⟨w, hw⟩ := hres b
    refine ⟨algebraMap W W' w * w', ?_⟩
    have h1 : (1 : B) ⊗ₜ[W] (algebraMap W W' w * w') = algebraMap W B w ⊗ₜ[W] w' := by
      rw [← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    have h2 : b ⊗ₜ[W] w' - algebraMap W B w ⊗ₜ[W] w' =
        algebraMap B (B ⊗[W] W') (b - algebraMap W B w) * ((1 : B) ⊗ₜ[W] w') := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.sub_tmul]
    rw [h1, h2]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hw)
  | add x y hx hy =>
    obtain ⟨w₁, h₁⟩ := hx
    obtain ⟨w₂, h₂⟩ := hy
    refine ⟨w₁ + w₂, ?_⟩
    rw [TensorProduct.tmul_add, show x + y - ((1 : B) ⊗ₜ[W] w₁ + (1 : B) ⊗ₜ[W] w₂) =
      (x - (1 : B) ⊗ₜ[W] w₁) + (y - (1 : B) ⊗ₜ[W] w₂) by abel]
    exact Ideal.add_mem _ h₁ h₂

theorem isLocalRing_tensorProduct {W B W' : Type*} [CommRing W] [CommRing B] [Algebra W B] [IsLocalRing B]
    [CommRing W'] [Algebra W W'] [IsLocalRing W'] [Module.Finite W W'] [Module.Flat W W']
    (hinj : Function.Injective (algebraMap W B))
    (hres : ∀ b : B, ∃ w : W, b - algebraMap W B w ∈ IsLocalRing.maximalIdeal B) :
    IsLocalRing (B ⊗[W] W') := by
  haveI : Nontrivial (B ⊗[W] W') :=
    (Algebra.TensorProduct.includeRight_injective (R := W) (A := B) (B := W') hinj).nontrivial
  set J : Ideal (B ⊗[W] W') := (IsLocalRing.maximalIdeal B).map (algebraMap B (B ⊗[W] W')) with hJ

  have hker : RingHom.ker (algebraMap B (B ⊗[W] W')) ≤ IsLocalRing.maximalIdeal B :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨𝔐, h𝔐, h𝔐c⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B ⊗[W] W') (IsLocalRing.maximalIdeal B) hker
  have hJle : ∀ 𝔐' : Ideal (B ⊗[W] W'), 𝔐'.IsMaximal → J ≤ 𝔐' := fun 𝔐' h' => by
    rw [hJ, Ideal.map_le_iff_le_comap,
      ← IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := B) 𝔐')]
  have hJtop : J ≠ ⊤ := fun h => h𝔐.ne_top (top_le_iff.mp (h ▸ hJle 𝔐 h𝔐))

  haveI : Nontrivial ((B ⊗[W] W') ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  let ψ : W' →+* (B ⊗[W] W') ⧸ J := (Ideal.Quotient.mk J).comp
    (Algebra.TensorProduct.includeRight (R := W) (A := B) (B := W')).toRingHom
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨w', hw'⟩ := exists_sub_one_tmul_mem_map hres z
    refine ⟨w', ?_⟩
    change Ideal.Quotient.mk J ((1 : B) ⊗ₜ[W] w') = Ideal.Quotient.mk J z
    rw [Ideal.Quotient.eq]
    rw [← neg_sub]
    exact Submodule.neg_mem _ hw'
  haveI : IsLocalRing ((B ⊗[W] W') ⧸ J) := IsLocalRing.of_surjective' ψ hψ

  refine IsLocalRing.of_unique_max_ideal ⟨𝔐, h𝔐, fun 𝔐' h𝔐' => ?_⟩
  let mk : (B ⊗[W] W') →+* ((B ⊗[W] W') ⧸ J) := Ideal.Quotient.mk J
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hkermk : RingHom.ker mk = J := Ideal.mk_ker
  let M₀ : Ideal (B ⊗[W] W') := (IsLocalRing.maximalIdeal ((B ⊗[W] W') ⧸ J)).comap mk
  have hM₀ : M₀ ≠ ⊤ := Ideal.comap_ne_top mk (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have hback : ∀ 𝔑 : Ideal (B ⊗[W] W'), 𝔑.IsMaximal → 𝔑 = M₀ := by
    intro 𝔑 h𝔑
    refine h𝔑.eq_of_le hM₀ ?_
    have hne : 𝔑.map mk ≠ ⊤ := by
      intro h
      apply h𝔑.ne_top
      have := Ideal.comap_map_of_surjective mk hmk 𝔑
      rw [h, Ideal.comap_top] at this
      rw [eq_top_iff, this, sup_le_iff]
      refine ⟨le_rfl, ?_⟩
      rw [← RingHom.ker_eq_comap_bot, hkermk]
      exact hJle 𝔑 h𝔑
    exact Ideal.map_le_iff_le_comap.mp (IsLocalRing.le_maximalIdeal hne)
  rw [hback 𝔐' h𝔐', hback 𝔐 h𝔐]

theorem exists_sub_mem_maximalIdeal_tensorProduct {W B W' : Type*} [CommRing W] [CommRing B] [Algebra W B]
    [IsLocalRing B] [CommRing W'] [Algebra W W'] [Module.Finite W W'] [IsLocalRing (B ⊗[W] W')]
    (hres : ∀ b : B, ∃ w : W, b - algebraMap W B w ∈ IsLocalRing.maximalIdeal B)
    (c : W' → B ⊗[W] W') (hc : ∀ w', c w' = (1 : B) ⊗ₜ[W] w') (z : B ⊗[W] W') :
    ∃ w' : W', z - c w' ∈ IsLocalRing.maximalIdeal (B ⊗[W] W') := by
  obtain ⟨w', hw'⟩ := exists_sub_one_tmul_mem_map hres z
  refine ⟨w', ?_⟩
  rw [hc]
  refine (Ideal.map_le_iff_le_comap.mpr ?_) hw'
  rw [← IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := B) (IsLocalRing.maximalIdeal (B ⊗[W] W')))]

theorem map_toAlgHom_injective {W R₀ B W' : Type*} [CommRing W] [CommRing R₀] [Algebra W R₀]
    [CommRing B] [Algebra W B] [Algebra R₀ B] [IsScalarTower W R₀ B]
    [CommRing W'] [Algebra W W'] [Module.Flat W W'] [FaithfulSMul R₀ B] :
    Function.Injective (Algebra.TensorProduct.map (IsScalarTower.toAlgHom W R₀ B) (AlgHom.id W W')) := by
  have h : ∀ z, Algebra.TensorProduct.map (IsScalarTower.toAlgHom W R₀ B) (AlgHom.id W W') z =
      ((IsScalarTower.toAlgHom W R₀ B).toLinearMap.rTensor W') z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul r w => rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective R₀ B) hab

theorem map_toAlgHom_finite {W R₀ B W' : Type*} [CommRing W] [CommRing R₀] [Algebra W R₀]
    [CommRing B] [Algebra W B] [Algebra R₀ B] [IsScalarTower W R₀ B] [Module.Finite R₀ B]
    [CommRing W'] [Algebra W W'] :
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom W R₀ B) (AlgHom.id W W')).toRingHom.Finite := by
  classical
  let φ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom W R₀ B) (AlgHom.id W W')
  letI alg : Algebra (R₀ ⊗[W] W') (B ⊗[W] W') := φ.toRingHom.toAlgebra
  have hsmul : ∀ (a : R₀ ⊗[W] W') (z : B ⊗[W] W'), a • z = φ a * z := fun _ _ => rfl
  change Module.Finite (R₀ ⊗[W] W') (B ⊗[W] W')
  obtain ⟨s, hs⟩ := Module.finite_def.mp ‹Module.Finite R₀ B›
  refine Module.finite_def.mpr ⟨s.image fun b => b ⊗ₜ[W] (1 : W'), ?_⟩
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul b w =>
    have hb : b ∈ Submodule.span R₀ (s : Set B) := by rw [hs]; exact Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx =>
      have : x ⊗ₜ[W] w = ((1 : R₀) ⊗ₜ[W] w) • (x ⊗ₜ[W] (1 : W')) := by
        rw [hsmul, Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        change _ = x ⊗ₜ[W] (w * 1)
        rw [mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_image_of_mem _ hx))
    | zero => rw [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have : (r • x) ⊗ₜ[W] w = (r ⊗ₜ[W] (1 : W')) • (x ⊗ₜ[W] w) := by
        rw [hsmul, Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          IsScalarTower.coe_toAlgHom', Algebra.smul_def]
      rw [this]
      exact Submodule.smul_mem _ _ hx
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end G
end SmoothBC44

namespace SmoothBC44
namespace Frame

universe u v uK uF

section Action

variable {W : Type u} [CommRing W]
  {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀] [Algebra W R₀]
  {B : Type v} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra W B] [Algebra R₀ B]
  [IsScalarTower W R₀ B] [Module.Finite R₀ B]
  {K₀ : Type uK} {F : Type uF} [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
  [Field F] [Algebra K₀ F] [Algebra R₀ F] [IsScalarTower R₀ K₀ F] [Algebra B F] [IsScalarTower R₀ B F]
  [IsFractionRing B F] [FiniteDimensional K₀ F]
  {W' : Type u} [CommRing W'] [Algebra W W']

variable (W R₀ B K₀ F W') in

noncomputable def actHom : (F ≃ₐ[K₀] F) →* ((B ⊗[W] W') ≃ₐ[W] (B ⊗[W] W')) where
  toFun g := Algebra.TensorProduct.congr ((galRestrict R₀ K₀ F B g).restrictScalars W) (AlgEquiv.refl : W' ≃ₐ[W] W')
  map_one' := by
    apply AlgEquiv.ext
    intro z
    rw [Algebra.TensorProduct.congr_apply, map_one]
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; rfl
    | tmul b w => rw [Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, hx, hy]; rfl
  map_mul' g h := by
    apply AlgEquiv.ext
    intro z
    rw [AlgEquiv.mul_apply, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.congr_apply, map_mul]
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b w => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]

theorem actHom_tmul (g : F ≃ₐ[K₀] F) (b : B) (w : W') :
    actHom W R₀ B K₀ F W' g (b ⊗ₜ[W] w) = (galRestrict R₀ K₀ F B g b) ⊗ₜ[W] w := by
  change Algebra.TensorProduct.congr _ _ (b ⊗ₜ[W] w) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  rfl

variable (W R₀ B K₀ F W') in

noncomputable def act : MulSemiringAction (F ≃ₐ[K₀] F) (B ⊗[W] W') :=
  MulSemiringAction.compHom (B ⊗[W] W') (actHom W R₀ B K₀ F W')

theorem act_smul_tmul (g : F ≃ₐ[K₀] F) (b : B) (w : W') :
    letI := act W R₀ B K₀ F W'
    g • (b ⊗ₜ[W] w) = (galRestrict R₀ K₀ F B g b) ⊗ₜ[W] w :=
  actHom_tmul g b w

noncomputable def actB (R₀ B K₀ F : Type*) [CommRing R₀] [CommRing B] [Algebra R₀ B] [Field K₀] [Field F]
    [Algebra R₀ K₀] [IsFractionRing R₀ K₀] [Algebra K₀ F] [Algebra R₀ F] [IsScalarTower R₀ K₀ F]
    [Algebra B F] [IsScalarTower R₀ B F] [IsIntegralClosure B R₀ F] [Algebra.IsAlgebraic K₀ F] :
    MulSemiringAction (F ≃ₐ[K₀] F) B :=
  MulSemiringAction.compHom B (galRestrict R₀ K₀ F B).toMonoidHom

omit [IsDomain R₀] [IsDomain B] [IsScalarTower W R₀ B] in
theorem actB_smul (g : F ≃ₐ[K₀] F) (b : B) :
    letI := actB R₀ B K₀ F
    g • b = galRestrict R₀ K₀ F B g b := rfl

theorem isGaloisGroup_B [IsGalois K₀ F] :
    letI := actB R₀ B K₀ F
    IsGaloisGroup (F ≃ₐ[K₀] F) R₀ B := by
  letI := actB R₀ B K₀ F
  haveI : SMulDistribClass (F ≃ₐ[K₀] F) B F := ⟨fun g b x => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', actB_smul, algebraMap_galRestrict_apply]
    rfl⟩
  exact IsGaloisGroup.of_isFractionRing (F ≃ₐ[K₀] F) R₀ B K₀ F

end Action

attribute [local instance] FractionRing.liftAlgebra in

theorem galois_frame
    {W : Type u} [CommRing W]
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀] [Algebra W R₀]
    {B : Type v} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra W B] [Algebra R₀ B]
    [IsScalarTower W R₀ B] [Module.Finite R₀ B]
    {K₀ : Type uK} {F : Type uF} [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Field F] [Algebra K₀ F] [Algebra R₀ F] [IsScalarTower R₀ K₀ F] [Algebra B F] [IsScalarTower R₀ B F]
    [IsFractionRing B F] [FiniteDimensional K₀ F] [IsGalois K₀ F]
    (hcyc : IsCyclic (F ≃ₐ[K₀] F)) (n : ℕ) (hdeg : Module.finrank K₀ F = n)
    {W' : Type u} [CommRing W'] [Algebra W W'] [Module.Free W W'] [Module.Finite W W']
    (hBS : Function.Injective (algebraMap B (B ⊗[W] W')))
    (R₀' : Type u) [CommRing R₀'] [IsDomain R₀'] [Algebra R₀' (B ⊗[W] W')] [IsDomain (B ⊗[W] W')]
    [FaithfulSMul R₀' (B ⊗[W] W')]
    (hrange : ∀ s : B ⊗[W] W', s ∈ Set.range (algebraMap R₀' (B ⊗[W] W')) ↔
      s ∈ Set.range (Algebra.TensorProduct.map (IsScalarTower.toAlgHom W R₀ B) (AlgHom.id W W'))) :
    ∃ (K₀' : Type u) (_ : Field K₀') (_ : Algebra R₀' K₀') (_ : IsFractionRing R₀' K₀')
      (F' : Type (max u v)) (_ : Field F') (_ : Algebra K₀' F') (_ : Algebra R₀' F')
      (_ : IsScalarTower R₀' K₀' F')
      (_ : Algebra (B ⊗[W] W') F') (_ : IsScalarTower R₀' (B ⊗[W] W') F') (_ : IsFractionRing (B ⊗[W] W') F')
      (_ : FiniteDimensional K₀' F') (_ : IsGalois K₀' F'),
      IsCyclic (F' ≃ₐ[K₀'] F') ∧ Module.finrank K₀' F' = n := by
  classical
  letI iB := actB R₀ B K₀ F
  letI iS := act W R₀ B K₀ F W'
  have hGB := isGaloisGroup_B (R₀ := R₀) (B := B) (K₀ := K₀) (F := F)

  set toB' := Algebra.TensorProduct.map (IsScalarTower.toAlgHom W R₀ B) (AlgHom.id W W') with htoB'
  have hfix_toB' : ∀ (g : F ≃ₐ[K₀] F) (z : R₀ ⊗[W] W'), g • toB' z = toB' z := by
    intro g z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]
    | tmul r w =>
      rw [htoB', Algebra.TensorProduct.map_tmul, act_smul_tmul, IsScalarTower.coe_toAlgHom', AlgEquiv.commutes]
    | add x y hx hy => rw [map_add, smul_add, hx, hy]

  have hGS : IsGaloisGroup (F ≃ₐ[K₀] F) R₀' (B ⊗[W] W') := by
    refine ⟨⟨fun {g₁ g₂} h => ?_⟩, ⟨fun g r s => ?_⟩, ⟨fun s hs => ?_⟩⟩
    ·
      apply hGB.faithful.eq_of_smul_eq_smul
      intro b
      apply hBS
      have := h (b ⊗ₜ[W] (1 : W'))
      rw [act_smul_tmul, act_smul_tmul] at this
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, RingHom.id_apply]
      exact this
    ·
      obtain ⟨z, hz⟩ := (hrange (algebraMap R₀' (B ⊗[W] W') r)).mp ⟨r, rfl⟩
      rw [Algebra.smul_def, Algebra.smul_def, smul_mul', ← hz, hfix_toB']
    ·
      let bW := Module.Free.chooseBasis W W'
      let bS := Algebra.TensorProduct.basis B bW
      have hrepr : ∀ (a : B) (j : Module.Free.ChooseBasisIndex W W'),
          bS.repr (a ⊗ₜ[W] bW j) = Finsupp.single j a := fun a j => by
        rw [Algebra.TensorProduct.basis_repr_tmul, Module.Basis.repr_self, Finsupp.mapRange_single, map_one,
          Finsupp.smul_single_one]
      have hs' : s = ∑ j ∈ (bS.repr s).support, (bS.repr s j) ⊗ₜ[W] bW j := by
        conv_lhs => rw [← bS.linearCombination_repr s, Finsupp.linearCombination_apply, Finsupp.sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.TensorProduct.basis_repr_symm_apply' bW]
      have hcoord : ∀ (g : F ≃ₐ[K₀] F) (i : Module.Free.ChooseBasisIndex W W'),
          bS.repr (g • s) i = g • bS.repr s i := by
        intro g i
        have hgs : g • s = ∑ j ∈ (bS.repr s).support, (g • bS.repr s j) ⊗ₜ[W] bW j := by
          conv_lhs => rw [hs', Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [act_smul_tmul]; rfl
        rw [hgs, map_sum, Finsupp.finsetSum_apply]
        simp only [hrepr, Finsupp.single_apply]
        rw [Finset.sum_ite_eq']
        by_cases h0 : bS.repr s i = 0
        · rw [if_neg (by rw [Finsupp.mem_support_iff, not_not]; exact h0), h0, smul_zero]
        · rw [if_pos (Finsupp.mem_support_iff.mpr h0)]
      have hfixc : ∀ i, ∃ r : R₀, algebraMap R₀ B r = bS.repr s i := fun i =>
        hGB.isInvariant.isInvariant _ fun g => by rw [← hcoord, hs g]
      choose r hr using hfixc
      refine (hrange s).mpr ⟨∑ j ∈ (bS.repr s).support, r j ⊗ₜ[W] bW j, ?_⟩
      rw [map_sum]
      conv_rhs => rw [← bS.linearCombination_repr s, Finsupp.linearCombination_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom', hr, Algebra.TensorProduct.basis_repr_symm_apply' bW]
      rfl

  haveI : Finite (F ≃ₐ[K₀] F) := inferInstance
  haveI : Module.IsTorsionFree R₀' (B ⊗[W] W') := Module.IsTorsionFree.of_smul_eq_zero fun r s h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun h0 => FaithfulSMul.algebraMap_injective R₀' (B ⊗[W] W') (by rw [h0, map_zero])
  haveI := hGS
  letI actF' := IsFractionRing.mulSemiringAction (F ≃ₐ[K₀] F) (B ⊗[W] W')
    (FractionRing (B ⊗[W] W'))
  have hGF : IsGaloisGroup (F ≃ₐ[K₀] F) (FractionRing R₀') (FractionRing (B ⊗[W] W')) :=
    IsGaloisGroup.toFractionRing (F ≃ₐ[K₀] F) R₀' (B ⊗[W] W')
  haveI := hGF
  haveI hfd : FiniteDimensional (FractionRing R₀') (FractionRing (B ⊗[W] W')) :=
    IsGaloisGroup.finiteDimensional (F ≃ₐ[K₀] F) _ _
  haveI hgal : IsGalois (FractionRing R₀') (FractionRing (B ⊗[W] W')) :=
    IsGaloisGroup.isGalois (F ≃ₐ[K₀] F) _ _
  have hcyc' : IsCyclic ((FractionRing (B ⊗[W] W')) ≃ₐ[FractionRing R₀'] (FractionRing (B ⊗[W] W'))) :=
    isCyclic_of_surjective _ (IsGaloisGroup.mulEquivAlgEquiv (F ≃ₐ[K₀] F) (FractionRing R₀')
      (FractionRing (B ⊗[W] W'))).surjective
  have hdeg' : Module.finrank (FractionRing R₀') (FractionRing (B ⊗[W] W')) = n := by
    rw [← IsGaloisGroup.card_eq_finrank (F ≃ₐ[K₀] F), IsGalois.card_aut_eq_finrank, hdeg]
  exact ⟨FractionRing R₀', inferInstance, inferInstance, inferInstance, FractionRing (B ⊗[W] W'), inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hfd, hgal, hcyc', hdeg'⟩

end Frame
end SmoothBC44

namespace SmoothBC44
namespace U

theorem height_eq_one_of_ne_bot_of_not_isMaximal {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hdim : ringKrullDim R = 2) (𝔭 : Ideal R) [𝔭.IsPrime] (h0 : 𝔭 ≠ ⊥) (hm : ¬ 𝔭.IsMaximal) :
    𝔭.height = 1 := by
  have hmax : (IsLocalRing.maximalIdeal R).height = 2 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hdim] at this
    exact WithBot.coe_injective (by rw [this]; rfl)
  haveI : (IsLocalRing.maximalIdeal R).FiniteHeight :=
    Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hmax]; decide))
  have hlt : 𝔭 < IsLocalRing.maximalIdeal R :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top') fun h => hm (h ▸ inferInstance)
  have h2 : 𝔭.height < 2 := hmax ▸ Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
  haveI : (⊥ : Ideal R).FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [Ideal.height_bot]; decide))
  have h1 : (⊥ : Ideal R).height < 𝔭.height := Ideal.height_strict_mono_of_isPrime (bot_lt_iff_ne_bot.mpr h0)
  rw [Ideal.height_bot] at h1
  have hne : 𝔭.height ≠ ⊤ := ne_top_of_lt h2
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hk] at h1 h2 ⊢
  have h1' : 0 < k := by exact_mod_cast h1
  have h2' : k < 2 := by exact_mod_cast h2
  have : k = 1 := by omega
  rw [this]; rfl

theorem isUnramifiedAt_of_not_isMaximal
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] (hdim : ringKrullDim R₀ = 2)
    {B : Type*} [CommRing B] [IsDomain B] [Algebra R₀ B] [Module.Finite R₀ B]
    (K₀ F : Type*) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀] [Field F] [Algebra K₀ F] [Algebra R₀ F]
    [IsScalarTower R₀ K₀ F] [Algebra B F] [IsScalarTower R₀ B F] [IsFractionRing B F] [Algebra.IsSeparable K₀ F]
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (𝔭.comap (algebraMap R₀ B)).height = 1 → Algebra.IsUnramifiedAt R₀ 𝔭)
    (𝔮 : Ideal B) [𝔮.IsPrime] (hm : ¬ 𝔮.IsMaximal) : Algebra.IsUnramifiedAt R₀ 𝔮 := by
  by_cases h0 : 𝔮 = ⊥
  · subst h0

    haveI : Algebra.FormallyUnramified R₀ K₀ :=
      Algebra.FormallyUnramified.of_isLocalization (Rₘ := K₀) (nonZeroDivisors R₀)
    haveI : Algebra.FormallyUnramified K₀ F := Algebra.FormallyUnramified.of_isSeparable K₀ F
    haveI : Algebra.FormallyUnramified R₀ F := Algebra.FormallyUnramified.comp R₀ K₀ F
    haveI : IsLocalization ((⊥ : Ideal B).primeCompl) F := by
      rw [Ideal.primeCompl_bot]; infer_instance
    let e : Localization.AtPrime (⊥ : Ideal B) ≃ₐ[B] F :=
      IsLocalization.algEquiv ((⊥ : Ideal B).primeCompl) (Localization.AtPrime (⊥ : Ideal B)) F
    exact Algebra.FormallyUnramified.of_equiv (e.restrictScalars R₀).symm
  · have hne : 𝔮.comap (algebraMap R₀ B) ≠ ⊥ := fun h => h0 (Ideal.eq_bot_of_comap_eq_bot h)
    have hnm : ¬ (𝔮.comap (algebraMap R₀ B)).IsMaximal := fun h =>
      hm (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R₀) 𝔮 h)
    exact hunr 𝔮 (height_eq_one_of_ne_bot_of_not_isMaximal hdim _ hne hnm)

theorem isUnramifiedAt_baseChange_of_height_eq_one
    {W : Type*} [CommRing W]
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] [Algebra W R₀] (hdim : ringKrullDim R₀ = 2)
    {B : Type*} [CommRing B] [IsDomain B] [Algebra W B] [Algebra R₀ B] [IsScalarTower W R₀ B] [Module.Finite R₀ B]
    (K₀ F : Type*) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀] [Field F] [Algebra K₀ F] [Algebra R₀ F]
    [IsScalarTower R₀ K₀ F] [Algebra B F] [IsScalarTower R₀ B F] [IsFractionRing B F] [Algebra.IsSeparable K₀ F]
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (𝔭.comap (algebraMap R₀ B)).height = 1 → Algebra.IsUnramifiedAt R₀ 𝔭)
    {W' : Type*} [CommRing W'] [Algebra W W'] [Algebra.FormallyUnramified W W'] [Module.Finite W W']
    (R₀' : Type*) [CommRing R₀'] [IsLocalRing R₀'] (hdim' : ringKrullDim R₀' = 2)
    [Algebra R₀' (B ⊗[W] W')] [Module.Finite R₀' (B ⊗[W] W')]
    [Algebra R₀ R₀'] [IsScalarTower R₀ R₀' (B ⊗[W] W')]
    (𝔭 : Ideal (B ⊗[W] W')) [𝔭.IsPrime] (hht : (𝔭.comap (algebraMap R₀' (B ⊗[W] W'))).height = 1) :
    Algebra.IsUnramifiedAt R₀' 𝔭 := by

  have hnm : ¬ 𝔭.IsMaximal := by
    intro hmax𝔭
    haveI : (𝔭.comap (algebraMap R₀' (B ⊗[W] W'))).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔭
    have h2 : (𝔭.comap (algebraMap R₀' (B ⊗[W] W'))).height = 2 := by
      rw [IsLocalRing.eq_maximalIdeal (inferInstance : (𝔭.comap (algebraMap R₀' (B ⊗[W] W'))).IsMaximal)]
      have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R₀')
      rw [hdim'] at this
      exact WithBot.coe_injective (by rw [this]; rfl)
    rw [h2] at hht
    exact absurd hht (by decide)

  have hqnm : ¬ (𝔭.under B).IsMaximal := fun h =>
    hnm (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := B) 𝔭 h)

  haveI : Algebra.IsUnramifiedAt R₀ (𝔭.under B) := isUnramifiedAt_of_not_isMaximal hdim K₀ F hunr _ hqnm
  haveI : Algebra.IsUnramifiedAt B 𝔭 := inferInstance
  haveI : Algebra.IsUnramifiedAt R₀ 𝔭 := Algebra.IsUnramifiedAt.comp (𝔭.under B) 𝔭
  exact Algebra.IsUnramifiedAt.of_restrictScalars R₀ 𝔭

end U
end SmoothBC44

namespace SmoothBC44
namespace U2

theorem isUnramifiedAt_of_not_isMaximal_off
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] (hdim : ringKrullDim R₀ = 2) (s : R₀)
    {B : Type*} [CommRing B] [IsDomain B] [Algebra R₀ B] [Module.Finite R₀ B]
    (K₀ F : Type*) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀] [Field F] [Algebra K₀ F] [Algebra R₀ F]
    [IsScalarTower R₀ K₀ F] [Algebra B F] [IsScalarTower R₀ B F] [IsFractionRing B F] [Algebra.IsSeparable K₀ F]
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (𝔭.comap (algebraMap R₀ B)).height = 1 →
      s ∉ 𝔭.comap (algebraMap R₀ B) → Algebra.IsUnramifiedAt R₀ 𝔭)
    (𝔮 : Ideal B) [𝔮.IsPrime] (hm : ¬ 𝔮.IsMaximal) (hs : s ∉ 𝔮.comap (algebraMap R₀ B)) :
    Algebra.IsUnramifiedAt R₀ 𝔮 := by
  by_cases h0 : 𝔮 = ⊥
  · subst h0
    haveI : Algebra.FormallyUnramified R₀ K₀ :=
      Algebra.FormallyUnramified.of_isLocalization (Rₘ := K₀) (nonZeroDivisors R₀)
    haveI : Algebra.FormallyUnramified K₀ F := Algebra.FormallyUnramified.of_isSeparable K₀ F
    haveI : Algebra.FormallyUnramified R₀ F := Algebra.FormallyUnramified.comp R₀ K₀ F
    haveI : IsLocalization ((⊥ : Ideal B).primeCompl) F := by
      rw [Ideal.primeCompl_bot]; infer_instance
    let e : Localization.AtPrime (⊥ : Ideal B) ≃ₐ[B] F :=
      IsLocalization.algEquiv ((⊥ : Ideal B).primeCompl) (Localization.AtPrime (⊥ : Ideal B)) F
    exact Algebra.FormallyUnramified.of_equiv (e.restrictScalars R₀).symm
  · have hne : 𝔮.comap (algebraMap R₀ B) ≠ ⊥ := fun h => h0 (Ideal.eq_bot_of_comap_eq_bot h)
    have hnm : ¬ (𝔮.comap (algebraMap R₀ B)).IsMaximal := fun h =>
      hm (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R₀) 𝔮 h)
    exact hunr 𝔮 (U.height_eq_one_of_ne_bot_of_not_isMaximal hdim _ hne hnm) hs

theorem isUnramifiedAt_baseChange_of_height_eq_one_off
    {W : Type*} [CommRing W]
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] [Algebra W R₀] (hdim : ringKrullDim R₀ = 2) (s : R₀)
    {B : Type*} [CommRing B] [IsDomain B] [Algebra W B] [Algebra R₀ B] [IsScalarTower W R₀ B] [Module.Finite R₀ B]
    (K₀ F : Type*) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀] [Field F] [Algebra K₀ F] [Algebra R₀ F]
    [IsScalarTower R₀ K₀ F] [Algebra B F] [IsScalarTower R₀ B F] [IsFractionRing B F] [Algebra.IsSeparable K₀ F]
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (𝔭.comap (algebraMap R₀ B)).height = 1 →
      s ∉ 𝔭.comap (algebraMap R₀ B) → Algebra.IsUnramifiedAt R₀ 𝔭)
    {W' : Type*} [CommRing W'] [Algebra W W'] [Algebra.FormallyUnramified W W'] [Module.Finite W W']
    (R₀' : Type*) [CommRing R₀'] [IsLocalRing R₀'] (hdim' : ringKrullDim R₀' = 2)
    [Algebra R₀' (B ⊗[W] W')] [Module.Finite R₀' (B ⊗[W] W')]
    [Algebra R₀ R₀'] [IsScalarTower R₀ R₀' (B ⊗[W] W')]
    (𝔭 : Ideal (B ⊗[W] W')) [𝔭.IsPrime] (hht : (𝔭.comap (algebraMap R₀' (B ⊗[W] W'))).height = 1)
    (hs' : algebraMap R₀ R₀' s ∉ 𝔭.comap (algebraMap R₀' (B ⊗[W] W'))) :
    Algebra.IsUnramifiedAt R₀' 𝔭 := by
  have hnm : ¬ 𝔭.IsMaximal := by
    intro hmax𝔭
    haveI : (𝔭.comap (algebraMap R₀' (B ⊗[W] W'))).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔭
    have h2 : (𝔭.comap (algebraMap R₀' (B ⊗[W] W'))).height = 2 := by
      rw [IsLocalRing.eq_maximalIdeal (inferInstance : (𝔭.comap (algebraMap R₀' (B ⊗[W] W'))).IsMaximal)]
      have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R₀')
      rw [hdim'] at this
      exact WithBot.coe_injective (by rw [this]; rfl)
    rw [h2] at hht
    exact absurd hht (by decide)
  have hqnm : ¬ (𝔭.under B).IsMaximal := fun h =>
    hnm (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := B) 𝔭 h)
  have hqs : s ∉ (𝔭.under B).comap (algebraMap R₀ B) := by
    intro h
    apply hs'
    rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply R₀ R₀' (B ⊗[W] W') s]
    rw [Ideal.mem_comap, Ideal.under_def, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply R₀ B (B ⊗[W] W') s] at h
    exact h
  haveI : Algebra.IsUnramifiedAt R₀ (𝔭.under B) := isUnramifiedAt_of_not_isMaximal_off hdim s K₀ F hunr _ hqnm hqs
  haveI : Algebra.IsUnramifiedAt B 𝔭 := inferInstance
  haveI : Algebra.IsUnramifiedAt R₀ 𝔭 := Algebra.IsUnramifiedAt.comp (𝔭.under B) 𝔭
  exact Algebra.IsUnramifiedAt.of_restrictScalars R₀ 𝔭

end U2
end SmoothBC44

universe u v w x

open IsLocalRing Polynomial

attribute [local instance] FractionRing.liftAlgebra in
open SmoothBC44 in
theorem solution
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [IsAdicComplete (maximalIdeal R) R]
    (ϖ s : R) (hmax : maximalIdeal R = Ideal.span {ϖ, s}) (hdim : ringKrullDim R = 2)
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R))
    (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (K₀ : Type w) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type x) [Field F] [Algebra K₀ F] [Algebra R F] [IsScalarTower R K₀ F]
    [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F)) (hdeg : Module.finrank K₀ F = e)
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (𝔭.comap (algebraMap R B)).height = 1 →
      s ∉ 𝔭.comap (algebraMap R B) → Algebra.IsUnramifiedAt R 𝔭)
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B)
    (R' : Type u) [CommRing R'] [IsRegularLocalRing R'] [IsDomain R'] [Algebra R R']
    [Module.Finite R R'] [Module.Free R R'] [FaithfulSMul R R'] [Algebra.Etale R R']
    [IsAdicComplete (maximalIdeal R') R'] :
    ∃ (B' : Type (max u v)) (_ : CommRing B') (_ : IsDomain B') (_ : IsIntegrallyClosed B') (_ : IsLocalRing B')
      (_ : IsNoetherianRing B') (_ : Algebra R' B') (_ : Module.Finite R' B') (_ : FaithfulSMul R' B')
      (K₀' : Type u) (_ : Field K₀') (_ : Algebra R' K₀') (_ : IsFractionRing R' K₀')
      (F' : Type (max u v)) (_ : Field F') (_ : Algebra K₀' F') (_ : Algebra R' F') (_ : IsScalarTower R' K₀' F')
      (_ : Algebra B' F') (_ : IsScalarTower R' B' F') (_ : IsFractionRing B' F')
      (_ : FiniteDimensional K₀' F') (_ : IsGalois K₀' F'),
      IsCyclic (F' ≃ₐ[K₀'] F') ∧ Module.finrank K₀' F' = e ∧
      (∀ (𝔭 : Ideal B') [𝔭.IsPrime], (𝔭.comap (algebraMap R' B')).height = 1 →
        algebraMap R R' s ∉ 𝔭.comap (algebraMap R' B') → Algebra.IsUnramifiedAt R' 𝔭) ∧
      (∀ b : B', ∃ r : R', b - algebraMap R' B' r ∈ maximalIdeal B') ∧
      Nonempty (R' ⊗[R] B ≃ₐ[R'] B') := by
  classical
  have hRB : Function.Injective (algebraMap R B) := FaithfulSMul.algebraMap_injective R B
  have hRR' : Function.Injective (algebraMap R R') := FaithfulSMul.algebraMap_injective R R'

  let toB' : R ⊗[R] R' →ₐ[R] B ⊗[R] R' :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R B) (AlgHom.id R R')
  let lid : R ⊗[R] R' ≃ₐ[R] R' := Algebra.TensorProduct.lid R R'
  letI algR'B' : Algebra R' (B ⊗[R] R') := (toB'.toRingHom.comp lid.symm.toRingEquiv.toRingHom).toAlgebra
  have halg : ∀ r' : R', algebraMap R' (B ⊗[R] R') r' = (1 : B) ⊗ₜ[R] r' := by
    intro r'
    show toB' (lid.symm r') = _
    rw [Algebra.TensorProduct.lid_symm_apply, Algebra.TensorProduct.map_tmul, map_one]
    rfl

  haveI : IsLocalRing (B ⊗[R] R') := G.isLocalRing_tensorProduct hRB hres
  haveI : IsNoetherianRing (B ⊗[R] R') := G.isNoetherianRing_tensorProduct
  obtain ⟨hdomB', hicB'⟩ :=
    Algebra.Etale.isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing (W := R) B R'
  haveI := hdomB'
  haveI := hicB'
  haveI : UniqueFactorizationMonoid R :=
    IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two R hdim.le
  haveI : IsIntegrallyClosed R := inferInstance
  haveI hfinB' : Module.Finite R' (B ⊗[R] R') := by
    change (toB'.toRingHom.comp lid.symm.toRingEquiv.toRingHom).Finite
    exact G.map_toAlgHom_finite.comp (RingHom.Finite.of_surjective _ lid.symm.surjective)
  haveI hfaithB' : FaithfulSMul R' (B ⊗[R] R') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      change Function.Injective (toB'.toRingHom.comp lid.symm.toRingEquiv.toRingHom)
      exact G.map_toAlgHom_injective.comp lid.symm.injective)

  obtain ⟨K₀', iK1, iK2, iK3, F', iF1, iF2, iF3, iF4, iF5, iF6, iF7, iF8, iF9, hcyc', hdeg'⟩ :
      ∃ (K₀' : Type u) (_ : Field K₀') (_ : Algebra R' K₀') (_ : IsFractionRing R' K₀')
        (F' : Type (max u v)) (_ : Field F') (_ : Algebra K₀' F') (_ : Algebra R' F')
        (_ : IsScalarTower R' K₀' F')
        (_ : Algebra (B ⊗[R] R') F') (_ : IsScalarTower R' (B ⊗[R] R') F') (_ : IsFractionRing (B ⊗[R] R') F')
        (_ : FiniteDimensional K₀' F') (_ : IsGalois K₀' F'),
        IsCyclic (F' ≃ₐ[K₀'] F') ∧ Module.finrank K₀' F' = e := by
    have hBS : Function.Injective (algebraMap B (B ⊗[R] R')) := by
      rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
      intro b hb
      rw [RingHom.mem_ker, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at hb
      let bW := Module.Free.chooseBasis R R'
      let bS := Algebra.TensorProduct.basis B bW
      have h1 : bW.repr 1 ≠ 0 := by
        intro h
        apply one_ne_zero (α := R')
        exact bW.repr.injective (by rw [h, map_zero])
      obtain ⟨i, hi⟩ : ∃ i, bW.repr 1 i ≠ 0 := by
        by_contra h
        push_neg at h
        exact h1 (Finsupp.ext h)
      have h2 : bS.repr (b ⊗ₜ[R] (1 : R')) i = b * algebraMap R B (bW.repr 1 i) := by
        rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
      rw [hb, map_zero, Finsupp.zero_apply] at h2
      rcases mul_eq_zero.mp h2.symm with h | h
      · exact h
      · exact absurd ((map_eq_zero_iff _ hRB).mp h) hi
    have hrange : ∀ z : B ⊗[R] R', z ∈ Set.range (algebraMap R' (B ⊗[R] R')) ↔ z ∈ Set.range toB' := fun z => by
      constructor
      · rintro ⟨r, rfl⟩
        exact ⟨lid.symm r, rfl⟩
      · rintro ⟨x, rfl⟩
        refine ⟨lid x, ?_⟩
        change toB' (lid.symm (lid x)) = toB' x
        rw [AlgEquiv.symm_apply_apply]
    exact Frame.galois_frame hcyc e hdeg hBS R' hrange

  have hunr' : ∀ (𝔭 : Ideal (B ⊗[R] R')) [𝔭.IsPrime], (𝔭.comap (algebraMap R' (B ⊗[R] R'))).height = 1 →
      algebraMap R R' s ∉ 𝔭.comap (algebraMap R' (B ⊗[R] R')) → Algebra.IsUnramifiedAt R' 𝔭 := by
    intro 𝔭 _ hht hs'
    haveI : IsScalarTower R R' (B ⊗[R] R') := IsScalarTower.of_algebraMap_eq fun r => by
      rw [halg, Algebra.TensorProduct.algebraMap_apply]
      show algebraMap R B r ⊗ₜ[R] (1 : R') = (1 : B) ⊗ₜ[R] (algebraMap R R' r)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
    have hdimR' : ringKrullDim R' = 2 :=
      (IsRegularLocalRing.of_etale_of_isLocalRing_of_maximalIdeal_eq_span_pair ϖ s hmax hdim R').2.1
    exact U2.isUnramifiedAt_baseChange_of_height_eq_one_off hdim s K₀ F hunr R' hdimR' 𝔭 hht hs'

  have hres' : ∀ b : B ⊗[R] R', ∃ r : R', b - algebraMap R' (B ⊗[R] R') r ∈ maximalIdeal (B ⊗[R] R') :=
    fun b => G.exists_sub_mem_maximalIdeal_tensorProduct hres _ halg b

  have eBC : R' ⊗[R] B ≃ₐ[R'] B ⊗[R] R' :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R R' B).toRingEquiv) (fun r' => by
      rw [halg]
      show Algebra.TensorProduct.comm R R' B (algebraMap R' (R' ⊗[R] B) r') = _
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.comm_tmul])
  exact ⟨B ⊗[R] R', inferInstance, hdomB', hicB', inferInstance, inferInstance, algR'B', hfinB', hfaithB',
    K₀', iK1, iK2, iK3, F', iF1, iF2, iF3, iF4, iF5, iF6, iF7, iF8, iF9, hcyc', hdeg', hunr', hres', ⟨eBC⟩⟩

end S_IsRegularLocalRing_exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem
end P2MW
export P2MW.S_IsRegularLocalRing_exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem (solution)
