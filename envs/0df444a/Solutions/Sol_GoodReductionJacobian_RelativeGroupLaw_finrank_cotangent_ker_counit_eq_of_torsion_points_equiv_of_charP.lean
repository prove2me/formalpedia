-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/11dcb201-c116-5c4f-a2e3-30de19492347

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_sqZero_of_natCast_eq_zero
import Theorems.Thm_AlgebraicGeometry_finrank_cotangentSpace_eq_of_smoothOfRelativeDimension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

noncomputable section

namespace LieTorsP2m

section Dict

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Bialgebra K B]
variable {V : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

variable (K B) in

abbrev augIdeal : Ideal B := RingHom.ker (Bialgebra.counitAlgHom K B)

variable (K B V) in

abbrev Tan : Type u :=
  {D : B →ₐ[K] TrivSqZeroExt K V // ∀ b : B, (D b).fst = Bialgebra.counitAlgHom K B b}

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in
lemma mem_augIdeal {b : B} : b ∈ augIdeal K B ↔ Bialgebra.counitAlgHom K B b = 0 := RingHom.mem_ker

def dI (D : B →ₐ[K] TrivSqZeroExt K V) : ↥(augIdeal K B) →ₗ[K] V :=
  (TrivSqZeroExt.sndHom K V).comp (D.toLinearMap.comp ((augIdeal K B).subtype.restrictScalars K))

@[scoped simp] lemma dI_apply (D : B →ₐ[K] TrivSqZeroExt K V) (x : ↥(augIdeal K B)) :
    dI D x = (D (x : B)).snd := rfl

lemma dI_mul (D : Tan K B V) (x y : ↥(augIdeal K B)) : dI D.1 (x * y) = 0 := by
  have hx : Bialgebra.counitAlgHom K B (x : B) = 0 := mem_augIdeal.mp x.2
  have hy : Bialgebra.counitAlgHom K B (y : B) = 0 := mem_augIdeal.mp y.2
  rw [dI_apply]
  have : ((x * y : ↥(augIdeal K B)) : B) = (x : B) * (y : B) := rfl
  rw [this, map_mul, TrivSqZeroExt.snd_mul, D.2, D.2, hx, hy, zero_smul, MulOpposite.op_zero, zero_smul, add_zero]

def gamma (D : Tan K B V) : (augIdeal K B).Cotangent →ₗ[K] V :=
  Ideal.Cotangent.lift (dI D.1) (dI_mul D)

@[scoped simp] lemma gamma_toCotangent (D : Tan K B V) (x : ↥(augIdeal K B)) :
    gamma D ((augIdeal K B).toCotangent x) = (D.1 (x : B)).snd := by
  simp [gamma]

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in

def proj : B →ₗ[K] ↥(augIdeal K B) where
  toFun b := ⟨b - algebraMap K B (Bialgebra.counitAlgHom K B b), by
    rw [mem_augIdeal, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]⟩
  map_add' a b := by
    ext
    simp only [map_add, Submodule.coe_add]
    ring
  map_smul' r b := by
    ext
    simp only [RingHom.id_apply, Submodule.coe_smul_of_tower, map_mul, Algebra.smul_def,
      AlgHom.commutes, Algebra.algebraMap_self_apply]
    ring

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in
@[scoped simp] lemma coe_proj (b : B) :
    (proj (K := K) b : B) = b - algebraMap K B (Bialgebra.counitAlgHom K B b) := rfl

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in
lemma proj_of_mem (x : ↥(augIdeal K B)) : proj (K := K) (x : B) = x := by
  ext
  rw [coe_proj, mem_augIdeal.mp x.2, map_zero, sub_zero]

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in
lemma proj_one : proj (K := K) (B := B) 1 = 0 := by
  ext
  simp

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in
lemma toCotangent_proj_mul (a b : B) :
    (augIdeal K B).toCotangent (proj (a * b)) =
      Bialgebra.counitAlgHom K B a • (augIdeal K B).toCotangent (proj b) +
        Bialgebra.counitAlgHom K B b • (augIdeal K B).toCotangent (proj a) := by
  rw [← (augIdeal K B).toCotangent.map_smul_of_tower (Bialgebra.counitAlgHom K B a) (proj b),
    ← (augIdeal K B).toCotangent.map_smul_of_tower (Bialgebra.counitAlgHom K B b) (proj a), ← map_add,
    Ideal.toCotangent_eq, pow_two]
  have ha : a - algebraMap K B (Bialgebra.counitAlgHom K B a) ∈ augIdeal K B := (proj (K := K) a).2
  have hb : b - algebraMap K B (Bialgebra.counitAlgHom K B b) ∈ augIdeal K B := (proj (K := K) b).2
  convert Ideal.mul_mem_mul ha hb using 1
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, coe_proj, map_mul, Algebra.smul_def]
  ring

def delta (ℓ : (augIdeal K B).Cotangent →ₗ[K] V) : B →ₗ[K] V :=
  ℓ ∘ₗ ((augIdeal K B).toCotangent.restrictScalars K) ∘ₗ proj

@[scoped simp] lemma delta_apply (ℓ : (augIdeal K B).Cotangent →ₗ[K] V) (b : B) :
    delta ℓ b = ℓ ((augIdeal K B).toCotangent (proj b)) := rfl

def DLin (ℓ : (augIdeal K B).Cotangent →ₗ[K] V) : B →ₗ[K] TrivSqZeroExt K V :=
  (Algebra.linearMap K (TrivSqZeroExt K V)) ∘ₗ (Bialgebra.counitAlgHom K B).toLinearMap +
    (TrivSqZeroExt.inrHom K V) ∘ₗ delta ℓ

@[scoped simp] lemma fst_DLin (ℓ : (augIdeal K B).Cotangent →ₗ[K] V) (b : B) :
    (DLin ℓ b).fst = Bialgebra.counitAlgHom K B b := by
  simp [DLin, Algebra.linearMap_apply, TrivSqZeroExt.algebraMap_eq_inl]

@[scoped simp] lemma snd_DLin (ℓ : (augIdeal K B).Cotangent →ₗ[K] V) (b : B) :
    (DLin ℓ b).snd = delta ℓ b := by
  simp [DLin, Algebra.linearMap_apply, TrivSqZeroExt.algebraMap_eq_inl]

def DAlg (ℓ : (augIdeal K B).Cotangent →ₗ[K] V) : B →ₐ[K] TrivSqZeroExt K V :=
  AlgHom.ofLinearMap (DLin ℓ)
    (by
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [fst_DLin, map_one, TrivSqZeroExt.fst_one]
      · rw [snd_DLin, TrivSqZeroExt.snd_one, delta_apply, proj_one, map_zero, map_zero])
    (by
      intro a b
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [fst_DLin, TrivSqZeroExt.fst_mul, fst_DLin, fst_DLin, map_mul]
      · rw [snd_DLin, TrivSqZeroExt.snd_mul, fst_DLin, fst_DLin, snd_DLin, snd_DLin, delta_apply,
          toCotangent_proj_mul, map_add, LinearMap.map_smul, LinearMap.map_smul, delta_apply,
          delta_apply, op_smul_eq_smul, add_comm])

@[scoped simp] lemma DAlg_apply (ℓ : (augIdeal K B).Cotangent →ₗ[K] V) (b : B) : DAlg ℓ b = DLin ℓ b := rfl

def DTan (ℓ : (augIdeal K B).Cotangent →ₗ[K] V) : Tan K B V := ⟨DAlg ℓ, fun b => by simp⟩

def gammaEquiv : Tan K B V ≃ ((augIdeal K B).Cotangent →ₗ[K] V) where
  toFun := gamma
  invFun := DTan
  left_inv D := by
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [DTan, DAlg_apply, fst_DLin]
      exact (D.2 b).symm
    · simp only [DTan, DAlg_apply, snd_DLin, delta_apply, gamma_toCotangent, coe_proj, map_sub,
        TrivSqZeroExt.snd_sub, AlgHom.commutes]
      rw [TrivSqZeroExt.algebraMap_eq_inl]
      simp
  right_inv ℓ := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := (augIdeal K B).toCotangent_surjective v
    change gamma (DTan ℓ) _ = _
    rw [gamma_toCotangent]
    simp only [DTan, DAlg_apply, snd_DLin, delta_apply, proj_of_mem]

lemma gammaEquiv_apply (D : Tan K B V) : gammaEquiv D = gamma D := rfl

def Tan.map (φ : V →ₗ[K] W) (D : Tan K B V) : Tan K B W :=
  ⟨(TrivSqZeroExt.map φ).comp D.1, fun b => by
    change (TrivSqZeroExt.map φ (D.1 b)).fst = _
    rw [TrivSqZeroExt.fst_map]; exact D.2 b⟩

@[scoped simp] lemma Tan.map_coe (φ : V →ₗ[K] W) (D : Tan K B V) (b : B) :
    (Tan.map φ D).1 b = TrivSqZeroExt.map φ (D.1 b) := rfl

p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP.LieTorsP2m.Tan"

lemma gammaEquiv_map (φ : V →ₗ[K] W) (D : Tan K B V) :
    gammaEquiv (Tan.map φ D) = φ ∘ₗ gammaEquiv D := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := (augIdeal K B).toCotangent_surjective v
  rw [gammaEquiv_apply, gammaEquiv_apply, gamma_toCotangent, LinearMap.comp_apply, gamma_toCotangent,
    Tan.map_coe, TrivSqZeroExt.snd_map]

end Dict
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP.LieTorsP2m.Tan"

section BridgePrelim

variable {K : Type u} [Field K]

theorem natCast_eq_zero_trivSqZeroExt (p : ℕ) [CharP K p]
    (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] :
    ((p : ℕ) : TrivSqZeroExt K V) = 0 := by
  have : ((p : ℕ) : TrivSqZeroExt K V) = algebraMap K (TrivSqZeroExt K V) (p : K) := by
    rw [map_natCast]
  rw [this, CharP.cast_eq_zero, map_zero]

theorem ker_fstHom_sq_eq_bot
    (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] :
    RingHom.ker (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K V).toRingHom).hom ^ 2 = ⊥ := by
  rw [eq_bot_iff, pow_two, Ideal.mul_le]
  intro a ha b hb
  rw [RingHom.mem_ker] at ha hb
  change a.fst = 0 at ha
  change b.fst = 0 at hb
  rw [Ideal.mem_bot]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, ha, hb, mul_zero, TrivSqZeroExt.fst_zero]
  · rw [TrivSqZeroExt.snd_mul, ha, hb, zero_smul, MulOpposite.op_zero, zero_smul, add_zero, TrivSqZeroExt.snd_zero]

variable {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)

abbrev origin : Spec (CommRingCat.of K) ⟶ A := (L.one (𝟙 _)).1

theorem origin_comp : origin f L ≫ f = 𝟙 _ := (L.one (𝟙 _)).2

theorem one_val_eq_origin (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)) (ht : 𝟙 _ = t) :
    (L.one t).1 = origin f L := by
  have h := congrArg Subtype.val (L.one_natural (𝟙 _) t (𝟙 _) (by rw [Category.id_comp]; exact ht))
  change 𝟙 _ ≫ (L.one (𝟙 _)).1 = (L.one t).1 at h
  rw [Category.id_comp] at h
  exact h.symm

theorem one_algebraMap_val :
    (L.one (Spec.map (CommRingCat.ofHom (algebraMap K K)))).1 = origin f L := by
  apply one_val_eq_origin
  change 𝟙 _ = Spec.map (CommRingCat.ofHom (RingHom.id K))
  rw [CommRingCat.ofHom_id]
  exact (Spec.map_id _).symm

end BridgePrelim
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP.LieTorsP2m.Tan"

section Bridge

variable {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
  {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
  (H : Type u) [CommRing H] [HopfAlgebra K H]
  (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
    WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) p)
  (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
    ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
  (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
      (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
    ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)

include he_mul he_nat

theorem e_one_val (T : Type u) [CommRing T] [Algebra K T] :
    ((e T 1).val : SchemeHomOver _ f) = L.one _ := by
  have _ := he_nat
  set x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f := (e T 1).val with hx
  have h : L.mul _ x x = x := by rw [hx, ← he_mul T 1 1, mul_one]
  calc x = L.mul _ (L.one _) x := (L.one_mul _ x).symm
    _ = L.mul _ (L.mul _ (L.inv _ x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul _ (L.inv _ x) (L.mul _ x x) := L.mul_assoc _ _ _ _
    _ = L.mul _ (L.inv _ x) x := by rw [h]
    _ = L.one _ := L.inv_mul_cancel _ x

variable {V : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

omit he_mul he_nat in

theorem isTorsionPoint_of_tangentPoints (v : TangentPoints f (origin f L) V) :
    ⟨v.1, v.2.1⟩ ∈ L.torsionSubset (SquareZero.toBase K V) p := by
  rw [RelativeGroupLaw.mem_torsionSubset]
  refine L.nsmul_eq_one_of_sqZero_of_natCast_eq_zero p (CommRingCat.of (TrivSqZeroExt K V)) (CommRingCat.of K)
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K V).toRingHom)
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩) (ker_fstHom_sq_eq_bot V)
    (natCast_eq_zero_trivSqZeroExt p V) (SquareZero.toBase K V) ⟨v.1, v.2.1⟩ ?_
  apply Subtype.ext
  change SquareZero.basePoint K V ≫ v.1 = (L.one (SquareZero.basePoint K V ≫ SquareZero.toBase K V)).1
  rw [v.2.2]
  exact (one_val_eq_origin f L _ (by rw [SquareZero.basePoint_toBase])).symm

theorem fst_symm_apply (v : TangentPoints f (origin f L) V) (b : H) :
    (((e (TrivSqZeroExt K V)).symm ⟨⟨v.1, v.2.1⟩, isTorsionPoint_of_tangentPoints p f L v⟩).ofConv b).fst =
      Bialgebra.counitAlgHom K H b := by
  set D := ((e (TrivSqZeroExt K V)).symm ⟨⟨v.1, v.2.1⟩, isTorsionPoint_of_tangentPoints p f L v⟩) with hD
  have hpt : ((e K (.toConv ((TrivSqZeroExt.fstHom K K V).comp D.ofConv))).val : SchemeHomOver _ f).1 =
      origin f L := by
    rw [he_nat (TrivSqZeroExt K V) K (TrivSqZeroExt.fstHom K K V) D]
    have : ((e (TrivSqZeroExt K V) D).val : SchemeHomOver _ f).1 = v.1 := by
      rw [hD, Equiv.apply_symm_apply]
    rw [this]
    exact v.2.2
  have h1 : ((e K 1).val : SchemeHomOver _ f).1 = origin f L := by
    rw [e_one_val p f L H e he_mul he_nat K]
    exact one_algebraMap_val f L
  have heq : (WithConv.toConv ((TrivSqZeroExt.fstHom K K V).comp D.ofConv) : WithConv (H →ₐ[K] K)) = 1 := by
    apply (e K).injective
    apply Subtype.ext
    apply Subtype.ext
    rw [hpt, h1]
  have heq' := congrArg (fun ψ : WithConv (H →ₐ[K] K) => ψ.ofConv b) heq
  exact heq'

def toTan (v : TangentPoints f (origin f L) V) : Tan K H V :=
  ⟨((e (TrivSqZeroExt K V)).symm ⟨⟨v.1, v.2.1⟩, isTorsionPoint_of_tangentPoints p f L v⟩).ofConv,
    fst_symm_apply p f L H e he_mul he_nat v⟩

@[scoped simp] theorem toTan_coe (v : TangentPoints f (origin f L) V) :
    (toTan p f L H e he_mul he_nat v).1 =
      ((e (TrivSqZeroExt K V)).symm ⟨⟨v.1, v.2.1⟩, isTorsionPoint_of_tangentPoints p f L v⟩).ofConv := rfl

theorem basePoint_comp_e (D : Tan K H V) :
    SquareZero.basePoint K V ≫ ((e (TrivSqZeroExt K V) (.toConv D.1)).val : SchemeHomOver _ f).1 = origin f L := by
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K V).toRingHom) ≫ _ = _
  rw [← he_nat (TrivSqZeroExt K V) K (TrivSqZeroExt.fstHom K K V) (.toConv D.1)]
  have hD : (TrivSqZeroExt.fstHom K K V).comp D.1 = (1 : WithConv (H →ₐ[K] K)).ofConv := by
    apply AlgHom.ext
    intro b
    change (D.1 b).fst = algebraMap K K (Bialgebra.counitAlgHom K H b)
    rw [D.2 b, Algebra.algebraMap_self_apply]
  change ((e K (.toConv ((TrivSqZeroExt.fstHom K K V).comp D.1))).val : SchemeHomOver _ f).1 = _
  rw [hD, WithConv.toConv_ofConv, e_one_val p f L H e he_mul he_nat K]
  exact one_algebraMap_val f L

def ofTan (D : Tan K H V) : TangentPoints f (origin f L) V :=
  ⟨((e (TrivSqZeroExt K V) (.toConv D.1)).val : SchemeHomOver _ f).1,
    ((e (TrivSqZeroExt K V) (.toConv D.1)).val : SchemeHomOver _ f).2,
    basePoint_comp_e p f L H e he_mul he_nat D⟩

@[scoped simp] theorem ofTan_coe (D : Tan K H V) :
    (ofTan p f L H e he_mul he_nat D).1 = ((e (TrivSqZeroExt K V) (.toConv D.1)).val : SchemeHomOver _ f).1 := rfl

def beta : TangentPoints f (origin f L) V ≃ Tan K H V where
  toFun := toTan p f L H e he_mul he_nat
  invFun := ofTan p f L H e he_mul he_nat
  left_inv v := by
    apply TangentPoints.ext
    rw [ofTan_coe, toTan_coe, WithConv.toConv_ofConv, Equiv.apply_symm_apply]
  right_inv D := by
    apply Subtype.ext
    rw [toTan_coe]
    have : (⟨⟨(ofTan p f L H e he_mul he_nat D).1, (ofTan p f L H e he_mul he_nat D).2.1⟩,
        isTorsionPoint_of_tangentPoints p f L (ofTan p f L H e he_mul he_nat D)⟩ :
          ↥(L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K V)))) p)) =
        e (TrivSqZeroExt K V) (.toConv D.1) := by
      apply Subtype.ext; apply Subtype.ext; rfl
    rw [this, Equiv.symm_apply_apply]

theorem beta_apply (v : TangentPoints f (origin f L) V) :
    beta p f L H e he_mul he_nat v = toTan p f L H e he_mul he_nat v := rfl

theorem beta_symm_apply (D : Tan K H V) :
    (beta p f L H e he_mul he_nat).symm D = ofTan p f L H e he_mul he_nat D := rfl

theorem beta_map (φ : V →ₗ[K] W) (v : TangentPoints f (origin f L) V) :
    beta p f L H e he_mul he_nat (v.map φ) = Tan.map φ (beta p f L H e he_mul he_nat v) := by
  have hinj := (beta p f L H e he_mul he_nat (V := W)).symm.injective
  apply hinj
  rw [Equiv.symm_apply_apply, beta_symm_apply]
  apply TangentPoints.ext
  rw [ofTan_coe, TangentPoints.map_coe]
  change _ = ((e (TrivSqZeroExt K W) (.toConv ((TrivSqZeroExt.map φ).comp
    (toTan p f L H e he_mul he_nat v).1))).val : SchemeHomOver _ f).1
  rw [toTan_coe, he_nat (TrivSqZeroExt K V) (TrivSqZeroExt K W) (TrivSqZeroExt.map φ), Equiv.apply_symm_apply]
  rfl

end Bridge
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP.LieTorsP2m.Tan"

section LinAlg

variable {K : Type u} [Field K] {T T' : Type u} [AddCommGroup T] [Module K T] [AddCommGroup T'] [Module K T']

theorem nonempty_dual_linearEquiv_dual
    (Φ : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V],
      (T →ₗ[K] V) → (T' →ₗ[K] V))
    (hnat : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
      (W : Type u) [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
      (φ : V →ₗ[K] W) (f : T →ₗ[K] V), Φ W (φ ∘ₗ f) = φ ∘ₗ (Φ V f))
    (hbij : Function.Bijective (Φ K)) :
    Nonempty (Module.Dual K T ≃ₗ[K] Module.Dual K T') := by
  have hadd : ∀ f g : T →ₗ[K] K, Φ K (f + g) = Φ K f + Φ K g := by
    intro f g
    have h1 : LinearMap.fst K K K ∘ₗ f.prod g = f := LinearMap.fst_prod f g
    have h2 : LinearMap.snd K K K ∘ₗ f.prod g = g := LinearMap.snd_prod f g
    have h3 : (LinearMap.fst K K K + LinearMap.snd K K K) ∘ₗ f.prod g = f + g := by
      rw [LinearMap.add_comp, h1, h2]
    calc Φ K (f + g) = Φ K ((LinearMap.fst K K K + LinearMap.snd K K K) ∘ₗ f.prod g) := by rw [h3]
      _ = (LinearMap.fst K K K + LinearMap.snd K K K) ∘ₗ (Φ (K × K) (f.prod g)) := hnat _ _ _ _
      _ = LinearMap.fst K K K ∘ₗ (Φ (K × K) (f.prod g)) + LinearMap.snd K K K ∘ₗ (Φ (K × K) (f.prod g)) := by
          rw [LinearMap.add_comp]
      _ = Φ K f + Φ K g := by rw [← hnat, ← hnat, h1, h2]
  have hsmul : ∀ (a : K) (f : T →ₗ[K] K), Φ K (a • f) = a • Φ K f := by
    intro a f
    have : (a • LinearMap.id : K →ₗ[K] K) ∘ₗ f = a • f := by rw [LinearMap.smul_comp, LinearMap.id_comp]
    rw [← this, hnat, LinearMap.smul_comp, LinearMap.id_comp]
  let Ψ : Module.Dual K T →ₗ[K] Module.Dual K T' := { toFun := Φ K, map_add' := hadd, map_smul' := hsmul }
  exact ⟨LinearEquiv.ofBijective Ψ hbij⟩

end LinAlg
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP.LieTorsP2m.Tan"

section Rational

variable {K : Type u} [Field K]

theorem surjective_residueFieldMap_of_section {X Y : Scheme.{u}} (f : X ⟶ Y) (z : Y ⟶ X)
    (hz : z ≫ f = 𝟙 Y) (y : Y) :
    Function.Surjective (f.residueFieldMap (z.base y)) := by
  have h1 : (z ≫ f).residueFieldMap y = f.residueFieldMap (z.base y) ≫ z.residueFieldMap y :=
    Scheme.residueFieldMap_comp z f y
  have hy : (z ≫ f).base y = (𝟙 Y : Y ⟶ Y).base y := by rw [hz]
  set ε := Y.residueFieldCongr hy with hε
  have h2 : (z ≫ f).residueFieldMap y = ε.hom ≫ (𝟙 Y : Y ⟶ Y).residueFieldMap y :=
    Scheme.Hom.residueFieldMap_congr hz y
  have key : f.residueFieldMap (z.base y) ≫ z.residueFieldMap y = ε.hom ≫ (𝟙 Y : Y ⟶ Y).residueFieldMap y :=
    h1.symm.trans h2
  rw [Scheme.residueFieldMap_id] at key
  intro c
  refine ⟨ε.inv (z.residueFieldMap y c), ?_⟩
  apply (z.residueFieldMap y).hom.injective
  have h3 := congrArg (fun φ => φ.hom (ε.inv (z.residueFieldMap y c))) key
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
  rw [h3]
  change (ε.inv ≫ ε.hom ≫ 𝟙 _).hom (z.residueFieldMap y c) = _
  rw [Iso.inv_hom_id_assoc]
  rfl

theorem surjective_evaluation_top_Spec_field (K : Type u) [Field K] (y : Spec (CommRingCat.of K)) :
    Function.Surjective ((Spec (CommRingCat.of K)).evaluation ⊤ y trivial) := by
  have hy : y.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  haveI : y.asIdeal.IsMaximal := by rw [hy]; exact Ideal.bot_isMaximal
  have hs : Function.Surjective (algebraMap K y.asIdeal.ResidueField) :=
    Ideal.algebraMap_residueField_surjective _
  have key := Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of K) y
  have h1 : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec (CommRingCat.of K)).presheaf.germ ⊤ y trivial ≫ (Spec (CommRingCat.of K)).residue y) := by
    rw [← key]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (Scheme.Spec.residueFieldIso (CommRingCat.of K) y).symm.commRingCatIsoToRingEquiv.surjective.comp hs
  intro c
  obtain ⟨a, ha⟩ := h1 c
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).inv a, ha⟩

theorem bijective_algebraMap_residueField {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (pt : Spec (CommRingCat.of K) ⟶ X) (hpt : pt ≫ x = 𝟙 _) :
    letI : Algebra K (X.presheaf.stalk (pt.base (IsLocalRing.closedPoint K))) :=
      ((X.presheaf.germ ⊤ (pt.base (IsLocalRing.closedPoint K)) trivial).hom.comp
        (x.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
    Function.Bijective (algebraMap K
      (IsLocalRing.ResidueField (X.presheaf.stalk (pt.base (IsLocalRing.closedPoint K))))) := by
  set p := pt.base (IsLocalRing.closedPoint K)
  letI : Algebra K (X.presheaf.stalk p) :=
    ((X.presheaf.germ ⊤ p trivial).hom.comp (x.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
  have hcomp : algebraMap K (IsLocalRing.ResidueField (X.presheaf.stalk p)) =
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Spec (CommRingCat.of K)).evaluation ⊤ (x.base p) trivial ≫
        x.residueFieldMap p).hom := by
    rw [IsScalarTower.algebraMap_eq K (X.presheaf.stalk p) (IsLocalRing.ResidueField _),
      IsLocalRing.ResidueField.algebraMap_eq, Scheme.evaluation_naturality x p (V := ⊤) trivial]
    rfl
  constructor
  · exact RingHom.injective _
  · rw [hcomp]
    simp only [CommRingCat.hom_comp]
    exact ((surjective_residueFieldMap_of_section x pt hpt _).comp
      (surjective_evaluation_top_Spec_field K (x.base p))).comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective

theorem finrank_cotangentSpace_residueField_eq {S : Type u} [CommRing S] [IsLocalRing S] [Algebra K S]
    (hK : Function.Bijective (algebraMap K (IsLocalRing.ResidueField S))) :
    Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.CotangentSpace S) =
      Module.finrank K (IsLocalRing.CotangentSpace S) := by
  symm
  unfold Module.finrank
  congr 1
  refine rank_eq_of_equiv_equiv (algebraMap K (IsLocalRing.ResidueField S)) (AddEquiv.refl _) hK ?_
  intro r m
  change r • m = (algebraMap K (IsLocalRing.ResidueField S) r) • m
  rw [IsScalarTower.algebraMap_apply K S (IsLocalRing.ResidueField S) r, IsScalarTower.algebraMap_smul,
    IsScalarTower.algebraMap_smul]

end Rational
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP.LieTorsP2m.Tan"

end LieTorsP2m
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP.LieTorsP2m.Tan P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP.LieTorsP2m"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP.LieTorsP2m.Tan P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP.LieTorsP2m"

open LieTorsP2m in
theorem solution
    (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (H : Type u) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) p)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1) :
    Module.finrank K (RingHom.ker (Bialgebra.counitAlgHom K H)).Cotangent = g := by
  classical

  letI alg : Algebra K (A.presheaf.stalk ((origin f L).base (IsLocalRing.closedPoint K))) :=
    ((A.presheaf.germ ⊤ ((origin f L).base (IsLocalRing.closedPoint K)) trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra

  obtain ⟨γ, hγ⟩ :=
    Scheme.exists_tangentPoints_equiv_linearMap_cotangentSpace f (origin f L) (origin_comp f L)

  let Φ : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V],
      (IsLocalRing.CotangentSpace (A.presheaf.stalk ((origin f L).base (IsLocalRing.closedPoint K))) →ₗ[K] V) →
        ((augIdeal K H).Cotangent →ₗ[K] V) :=
    fun V _ _ _ _ g' => gammaEquiv (beta p f L H e he_mul he_nat ((γ V).symm g'))
  have hnat : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
      (W : Type u) [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
      (φ : V →ₗ[K] W) (g' : IsLocalRing.CotangentSpace _ →ₗ[K] V),
      Φ W (φ ∘ₗ g') = φ ∘ₗ (Φ V g') := by
    intro V _ _ _ _ W _ _ _ _ φ g'
    have hv : (γ W).symm (φ ∘ₗ g') = ((γ V).symm g').map φ := by
      apply (γ W).injective
      rw [Equiv.apply_symm_apply, hγ, Equiv.apply_symm_apply]
    change gammaEquiv (beta p f L H e he_mul he_nat ((γ W).symm (φ ∘ₗ g'))) =
      φ ∘ₗ gammaEquiv (beta p f L H e he_mul he_nat ((γ V).symm g'))
    rw [hv, beta_map, gammaEquiv_map]
  have hbij : Function.Bijective (Φ K) :=
    (gammaEquiv.bijective.comp (beta p f L H e he_mul he_nat).bijective).comp (γ K).symm.bijective
  obtain ⟨eDual⟩ := nonempty_dual_linearEquiv_dual Φ hnat hbij

  have hK := bijective_algebraMap_residueField f (origin f L) (origin_comp f L)
  have hg := AlgebraicGeometry.finrank_cotangentSpace_eq_of_smoothOfRelativeDimension f g (origin f L) (origin_comp f L)
  rw [finrank_cotangentSpace_residueField_eq hK] at hg
  change Module.finrank K (augIdeal K H).Cotangent = g
  rw [← Subspace.dual_finrank_eq, ← eDual.finrank_eq, Subspace.dual_finrank_eq]
  exact hg

end S_GoodReductionJacobian_RelativeGroupLaw_finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finrank_cotangent_ker_counit_eq_of_torsion_points_equiv_of_charP (solution)
