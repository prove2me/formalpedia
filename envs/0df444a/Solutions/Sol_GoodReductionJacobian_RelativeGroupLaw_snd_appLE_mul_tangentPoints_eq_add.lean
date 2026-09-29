-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.snd_appLE_mul_tangentPoints_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/efa64f31-f32b-5ad3-9cdf-40d156d8e8f6

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_snd_appLE_mul_tangentPoints_eq_add

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

open NeronModelInfra

namespace N3B

open TrivSqZeroExt

variable {K : Type u} [Field K]
variable {V : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

theorem asIdeal_eq (p : PrimeSpectrum (TrivSqZeroExt K V)) :
    p.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom K K V).toRingHom := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker]
    by_contra h
    have hu : IsUnit z := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (Ne.isUnit h)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz hu)
  · intro z hz
    rw [RingHom.mem_ker] at hz
    have hz' : z = TrivSqZeroExt.inr z.snd := by
      ext <;> simp [show z.fst = 0 from hz]
    apply p.isPrime.mem_of_pow_mem 2
    rw [hz', pow_two, TrivSqZeroExt.inr_mul_inr]
    exact p.asIdeal.zero_mem

theorem point_eq (p q : ↥(SquareZero.spec K V)) : p = q :=
  PrimeSpectrum.ext (by rw [asIdeal_eq, asIdeal_eq])

theorem top_le_preimage_of_comp {W' : Type u} [AddCommGroup W'] [Module K W'] [Module Kᵐᵒᵖ W'] [IsCentralScalar K W']
    {A : Scheme.{u}} (g : SquareZero.spec K W' ⟶ A) (ψ : SquareZero.spec K V ⟶ SquareZero.spec K W')
    (W : A.Opens) (h : ⊤ ≤ (ψ ≫ g) ⁻¹ᵁ W) : ⊤ ≤ g ⁻¹ᵁ W := by
  intro p _
  let q : ↥(SquareZero.spec K V) := ⟨RingHom.ker (TrivSqZeroExt.fstHom K K V).toRingHom, RingHom.ker_isPrime _⟩
  have hq : q ∈ (ψ ≫ g) ⁻¹ᵁ W := h (Set.mem_univ q)
  have : p = ψ.base q := point_eq _ _
  rw [this]
  exact hq

theorem read_comp {W' : Type u} [AddCommGroup W'] [Module K W'] [Module Kᵐᵒᵖ W'] [IsCentralScalar K W']
    {A : Scheme.{u}} (g : SquareZero.spec K W' ⟶ A) (φ : W' →ₗ[K] V)
    (W : A.Opens) (hg : ⊤ ≤ g ⁻¹ᵁ W) (h : ⊤ ≤ (SquareZero.specMap K φ ≫ g) ⁻¹ᵁ W) (a : Γ(A, W)) :
    ((SquareZero.specMap K φ ≫ g).appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K V))).hom).hom a =
      TrivSqZeroExt.map φ ((g.appLE W ⊤ hg ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K W'))).hom).hom a) := by
  have e1 : (SquareZero.specMap K φ ≫ g).appLE W ⊤ h =
      g.appLE W ⊤ hg ≫ (SquareZero.specMap K φ).appLE ⊤ ⊤ (by simp) := by
    rw [Scheme.Hom.appLE_comp_appLE]
  have e2 : (SquareZero.specMap K φ).appLE ⊤ ⊤ (by simp) = (SquareZero.specMap K φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [e1, e2, Category.assoc, SquareZero.specMap, Scheme.ΓSpecIso_naturality, ← Category.assoc]
  rfl

theorem appLE_congr {X Y : Scheme.{u}} {g₁ g₂ : X ⟶ Y} (e : g₁ = g₂) (U : Y.Opens) (h₁ : ⊤ ≤ g₁ ⁻¹ᵁ U)
    (h₂ : ⊤ ≤ g₂ ⁻¹ᵁ U) : g₁.appLE U ⊤ h₁ = g₂.appLE U ⊤ h₂ := by
  subst e; rfl

theorem specMap_zero {W' : Type u} [AddCommGroup W'] [Module K W'] [Module Kᵐᵒᵖ W'] [IsCentralScalar K W'] :
    SquareZero.specMap K (0 : W' →ₗ[K] V) = SquareZero.toBase K V ≫ SquareZero.basePoint K W' := by
  rw [SquareZero.specMap, SquareZero.toBase, SquareZero.basePoint, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  change TrivSqZeroExt.map (0 : W' →ₗ[K] V) z = algebraMap K (TrivSqZeroExt K V) (TrivSqZeroExt.fstHom K K W' z)
  ext
  · simp [TrivSqZeroExt.fst_map, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [TrivSqZeroExt.snd_map, TrivSqZeroExt.algebraMap_eq_inl]

end N3B

theorem solution
    {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
    (v₁ v₂ : TangentPoints f (L.one (𝟙 _)).1 V)
    (W : A.Opens) (a : Γ(A, W))
    (h₁ : ⊤ ≤ v₁.1 ⁻¹ᵁ W) (h₂ : ⊤ ≤ v₂.1 ⁻¹ᵁ W)
    (hμ : ⊤ ≤ (L.mul (SquareZero.toBase K V) ⟨v₁.1, v₁.2.1⟩ ⟨v₂.1, v₂.2.1⟩).1 ⁻¹ᵁ W) :
    (((L.mul (SquareZero.toBase K V) ⟨v₁.1, v₁.2.1⟩ ⟨v₂.1, v₂.2.1⟩).1.appLE W ⊤ hμ ≫
        (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K V))).hom).hom a).snd =
      ((v₁.1.appLE W ⊤ h₁ ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K V))).hom).hom a).snd +
      ((v₂.1.appLE W ⊤ h₂ ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K V))).hom).hom a).snd := by
  classical

  let σ : V × V →ₗ[K] V := LinearMap.fst K V V + LinearMap.snd K V V
  let ρ₁ : V × V →ₗ[K] V := LinearMap.fst K V V
  let ρ₂ : V × V →ₗ[K] V := LinearMap.snd K V V
  let ι₁ : V →ₗ[K] V × V := LinearMap.inl K V V
  let ι₂ : V →ₗ[K] V × V := LinearMap.inr K V V
  have hσ₁ : σ ∘ₗ ι₁ = LinearMap.id := by ext m; simp [σ, ι₁]
  have hσ₂ : σ ∘ₗ ι₂ = LinearMap.id := by ext m; simp [σ, ι₂]
  have h₁₁ : ρ₁ ∘ₗ ι₁ = LinearMap.id := by ext m; simp [ρ₁, ι₁]
  have h₂₂ : ρ₂ ∘ₗ ι₂ = LinearMap.id := by ext m; simp [ρ₂, ι₂]
  have h₁₂ : ρ₁ ∘ₗ ι₂ = 0 := by ext m; simp [ρ₁, ι₂]
  have h₂₁ : ρ₂ ∘ₗ ι₁ = 0 := by ext m; simp [ρ₂, ι₁]

  let w₁ := v₁.map ι₁
  let w₂ := v₂.map ι₂
  let T := L.mul (SquareZero.toBase K (V × V)) ⟨w₁.1, w₁.2.1⟩ ⟨w₂.1, w₂.2.1⟩

  have hcomp : ∀ (φ : V × V →ₗ[K] V) (v : TangentPoints f (L.one (𝟙 _)).1 V) (ι : V →ₗ[K] V × V),
      schemeHomOverComp (SquareZero.specMap K φ) (SquareZero.specMap_toBase K φ)
        (⟨(v.map ι).1, (v.map ι).2.1⟩ : SchemeHomOver (SquareZero.toBase K (V × V)) f) =
        ⟨(v.map (φ ∘ₗ ι)).1, (v.map (φ ∘ₗ ι)).2.1⟩ := by
    intro φ v ι
    apply Subtype.ext
    simp only [schemeHomOverComp_coe, TangentPoints.map_coe, ← Category.assoc, ← SquareZero.specMap_comp]
  have hid : ∀ v : TangentPoints f (L.one (𝟙 _)).1 V,
      (⟨(v.map (LinearMap.id : V →ₗ[K] V)).1, (v.map LinearMap.id).2.1⟩ : SchemeHomOver (SquareZero.toBase K V) f) =
        ⟨v.1, v.2.1⟩ := by
    intro v; apply Subtype.ext; simp [TangentPoints.map_coe, SquareZero.specMap_id]
  have hzero : ∀ v : TangentPoints f (L.one (𝟙 _)).1 V,
      (⟨(v.map (0 : V →ₗ[K] V)).1, (v.map 0).2.1⟩ : SchemeHomOver (SquareZero.toBase K V) f) =
        L.one (SquareZero.toBase K V) := by
    intro v
    rw [← L.one_natural (𝟙 _) (SquareZero.toBase K V) (SquareZero.toBase K V) (Category.comp_id _)]
    apply Subtype.ext
    simp only [TangentPoints.map_coe, schemeHomOverComp_coe, N3B.specMap_zero, Category.assoc, v.2.2]

  have F1 : SquareZero.specMap K σ ≫ T.1 = (L.mul (SquareZero.toBase K V) ⟨v₁.1, v₁.2.1⟩ ⟨v₂.1, v₂.2.1⟩).1 := by
    have := L.mul_natural (SquareZero.toBase K (V × V)) (SquareZero.toBase K V) (SquareZero.specMap K σ)
      (SquareZero.specMap_toBase K σ) ⟨w₁.1, w₁.2.1⟩ ⟨w₂.1, w₂.2.1⟩
    rw [hcomp, hcomp, hσ₁, hσ₂, hid, hid] at this
    exact (congrArg Subtype.val this)

  have F2 : SquareZero.specMap K ρ₁ ≫ T.1 = v₁.1 := by
    have := L.mul_natural (SquareZero.toBase K (V × V)) (SquareZero.toBase K V) (SquareZero.specMap K ρ₁)
      (SquareZero.specMap_toBase K ρ₁) ⟨w₁.1, w₁.2.1⟩ ⟨w₂.1, w₂.2.1⟩
    rw [hcomp, hcomp, h₁₁, h₁₂, hid, hzero, L.mul_one] at this
    exact (congrArg Subtype.val this)
  have F3 : SquareZero.specMap K ρ₂ ≫ T.1 = v₂.1 := by
    have := L.mul_natural (SquareZero.toBase K (V × V)) (SquareZero.toBase K V) (SquareZero.specMap K ρ₂)
      (SquareZero.specMap_toBase K ρ₂) ⟨w₁.1, w₁.2.1⟩ ⟨w₂.1, w₂.2.1⟩
    rw [hcomp, hcomp, h₂₁, h₂₂, hzero, hid, L.one_mul] at this
    exact (congrArg Subtype.val this)

  have hT : ⊤ ≤ T.1 ⁻¹ᵁ W := N3B.top_le_preimage_of_comp T.1 (SquareZero.specMap K σ) W (by rw [F1]; exact hμ)

  have Rσ := N3B.read_comp T.1 σ W hT (by rw [F1]; exact hμ) a
  have R₁ := N3B.read_comp T.1 ρ₁ W hT (by rw [F2]; exact h₁) a
  have R₂ := N3B.read_comp T.1 ρ₂ W hT (by rw [F3]; exact h₂) a
  rw [N3B.appLE_congr F1 W _ hμ] at Rσ
  rw [N3B.appLE_congr F2 W _ h₁] at R₁
  rw [N3B.appLE_congr F3 W _ h₂] at R₂
  rw [Rσ, R₁, R₂, TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_map]
  simp [σ, ρ₁, ρ₂]

end S_GoodReductionJacobian_RelativeGroupLaw_snd_appLE_mul_tangentPoints_eq_add
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_snd_appLE_mul_tangentPoints_eq_add (solution)
