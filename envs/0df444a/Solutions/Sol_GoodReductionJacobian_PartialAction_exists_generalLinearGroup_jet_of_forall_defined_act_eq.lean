-- Prove2me | solution 1 for GoodReductionJacobian.PartialAction.exists_generalLinearGroup_jet_of_forall_defined_act_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4b2e368f-dbea-546f-b2b6-1165cdca4512

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat
import Theorems.Thm_IsLocalRing_moduleFinite_quotient_maximalIdeal_pow_of_residueField_map_surjective
import Theorems.Thm_AlgebraicGeometry_exists_comp_specMap_quotient_maximalIdeal_pow_eq_of_section_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_PartialAction_exists_generalLinearGroup_jet_of_forall_defined_act_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_exists_generalLinearGroup_jet_of_forall_defined_act_eq.GoodReductionJacobian"
open TensorProduct

universe u

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw PartialAction"
namespace PartialAction
p2m_export "GoodReductionJacobian.PartialAction" "pair Defined liftDom liftDom_ι act act_coe UnitActs Assoc hom_comp mk dom hom"
namespace JetLinearisationB5b
p2m_open "GoodReductionJacobian.PartialAction GoodReductionJacobian"

section Blocks

variable {R S : Type u} [CommRing R] [CommRing S]

noncomputable def blockHom {m : ℕ} (d : Fin m → ℕ) :
    (∀ i : Fin m, Matrix (Fin (d i)) (Fin (d i)) R) →+* Matrix (Fin (∑ i, d i)) (Fin (∑ i, d i)) R :=
  ((Matrix.reindexAlgEquiv R R (finSigmaFinEquiv (n := d))).toRingEquiv.toRingHom).comp
    (Matrix.blockDiagonal'RingHom (fun i => Fin (d i)) R)

theorem blockHom_apply {m : ℕ} (d : Fin m → ℕ) (M : ∀ i : Fin m, Matrix (Fin (d i)) (Fin (d i)) R) :
    blockHom d M = Matrix.reindex (finSigmaFinEquiv (n := d)) (finSigmaFinEquiv (n := d))
      (Matrix.blockDiagonal' M) := rfl

theorem blockHom_injective {m : ℕ} (d : Fin m → ℕ) : Function.Injective (blockHom (R := R) d) := by
  intro M N h
  rw [blockHom_apply, blockHom_apply] at h
  exact Matrix.blockDiagonal'_injective ((Matrix.reindex _ _).injective h)

theorem blockHom_map {m : ℕ} (d : Fin m → ℕ) (φ : R →+* S)
    (M : ∀ i : Fin m, Matrix (Fin (d i)) (Fin (d i)) R) :
    (blockHom d M).map φ = blockHom d (fun i => (M i).map φ) := by
  rw [blockHom_apply, blockHom_apply]
  have h : (Matrix.blockDiagonal' M).map φ = Matrix.blockDiagonal' fun i => (M i).map φ :=
    Matrix.blockDiagonal'_map M φ (map_zero φ)
  ext a b
  exact congrFun (congrFun h _) _

noncomputable def blockGL {m : ℕ} (d : Fin m → ℕ) (M : ∀ i : Fin m, GL (Fin (d i)) R) :
    GL (Fin (∑ i, d i)) R :=
  Units.map (blockHom d).toMonoidHom (MulEquiv.piUnits.symm M)

theorem blockGL_val {m : ℕ} (d : Fin m → ℕ) (M : ∀ i : Fin m, GL (Fin (d i)) R) :
    (blockGL d M : Matrix _ _ R) = blockHom d (fun i => (M i : Matrix _ _ R)) := rfl

theorem blockGL_mul {m : ℕ} (d : Fin m → ℕ) (M N : ∀ i : Fin m, GL (Fin (d i)) R) :
    blockGL d (M * N) = blockGL d M * blockGL d N := by
  simp only [blockGL, map_mul]

theorem blockGL_eq_one_iff {m : ℕ} (d : Fin m → ℕ) (M : ∀ i : Fin m, GL (Fin (d i)) R) :
    blockGL d M = 1 ↔ ∀ i, M i = 1 := by
  constructor
  · intro h i
    have hv : (blockGL d M).val = (1 : GL (Fin (∑ i, d i)) R).val := by
      rw [h]
    rw [blockGL_val, Units.val_one, ← map_one (blockHom (R := R) d)] at hv
    have h2 := congrFun (blockHom_injective d hv) i
    exact Units.ext h2
  · intro h
    have : M = 1 := funext h
    subst this
    simp only [blockGL, map_one]

theorem blockGL_map {m : ℕ} (d : Fin m → ℕ) (φ : R →+* S) (M : ∀ i : Fin m, GL (Fin (d i)) R) :
    Matrix.GeneralLinearGroup.map φ (blockGL d M) =
      blockGL d (fun i => Matrix.GeneralLinearGroup.map φ (M i)) := by
  apply Units.ext
  have h1 : (Matrix.GeneralLinearGroup.map φ (blockGL d M)).val = (blockGL d M).val.map φ := by
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  have h2 : (fun i => (Matrix.GeneralLinearGroup.map φ (M i)).val) =
      fun i => (M i).val.map φ := by
    funext i
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  rw [h1, blockGL_val, blockGL_val, h2, blockHom_map]

end Blocks

section OnePoint

variable {k : Type u} [Field k]

theorem fst_injective_of_section {X S : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (s : S ⟶ Spec (CommRingCat.of k)) (σ : Spec (CommRingCat.of k) ⟶ S) (hσ : σ ≫ s = 𝟙 _)
    [Subsingleton ↥S] : Function.Injective (pullback.fst x s) := by
  haveI : Surjective σ := ⟨Function.surjective_to_subsingleton _⟩
  haveI : IsIso (σ ≫ s) := by rw [hσ]; infer_instance
  let π : pullback (pullback.snd x s) σ ⟶ pullback x s := pullback.fst (pullback.snd x s) σ
  have key : π ≫ pullback.fst x s =
      (pullbackLeftPullbackSndIso x s σ).hom ≫ pullback.fst x (σ ≫ s) :=
    (pullbackLeftPullbackSndIso_hom_fst x s σ).symm
  have hinj : Function.Injective (π ≫ pullback.fst x s) := by
    rw [key]
    exact (pullback.fst x (σ ≫ s)).injective.comp (pullbackLeftPullbackSndIso x s σ).hom.injective
  intro z₁ z₂ h
  obtain ⟨w₁, rfl⟩ := π.surjective z₁
  obtain ⟨w₂, rfl⟩ := π.surjective z₂
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply] at h
  rw [hinj h]

theorem subsingleton_primeSpectrum_quotient (O : Type u) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Subsingleton (PrimeSpectrum (O ⧸ IsLocalRing.maximalIdeal O ^ n)) := by
  have hcomap : ∀ Q : PrimeSpectrum (O ⧸ IsLocalRing.maximalIdeal O ^ n),
      Q.asIdeal.comap (Ideal.Quotient.mk _) = IsLocalRing.maximalIdeal O := by
    intro Q
    haveI : (Q.asIdeal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))).IsPrime :=
      Ideal.IsPrime.comap _
    have hle : IsLocalRing.maximalIdeal O ≤ Q.asIdeal.comap (Ideal.Quotient.mk _) := by
      intro a ha
      have han : a ^ n ∈ Q.asIdeal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)) := by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ha n)]
        exact Q.asIdeal.zero_mem
      exact Ideal.IsPrime.mem_of_pow_mem inferInstance n han
    exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le
      (Ideal.IsPrime.ne_top inferInstance) hle).symm
  refine ⟨fun Q₁ Q₂ => ?_⟩
  apply PrimeSpectrum.ext
  rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))
      Ideal.Quotient.mk_surjective Q₁.asIdeal,
    ← Ideal.map_comap_of_surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))
      Ideal.Quotient.mk_surjective Q₂.asIdeal, hcomap, hcomap]

end OnePoint

section Coords

variable {k : Type u} [Field k]

theorem coords_bijective {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace ↥Y] [QuasiSeparatedSpace ↥Y]
    (A : Type u) [CommRing A] [Algebra k A] {ι : Type} [Fintype ι] (b : Module.Basis ι k A) :
    Function.Bijective (fun c : ι → Γ(Y, ⊤) => ∑ i,
      (pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop.hom (c i) *
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (b i))) := by
  set ΓY : Type u := Γ(Y, ⊤) with hΓY
  letI algY : Algebra k ΓY := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ y.appTop).hom.toAlgebra
  have H : IsPushout (CommRingCat.ofHom (algebraMap k A)) (CommRingCat.ofHom (algebraMap k ΓY))
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop)
      (pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop :=
    AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat y A
  let ε : CommRingCat.of (A ⊗[k] ΓY) ≅ Γ(pullback y (Spec.map (CommRingCat.ofHom (algebraMap k A))), ⊤) :=
    IsPushout.isoIsPushout _ _ (CommRingCat.isPushout_tensorProduct k A ΓY) H
  let εr : A ⊗[k] ΓY →+* Γ(pullback y (Spec.map (CommRingCat.ofHom (algebraMap k A))), ⊤) :=
    ε.hom.hom
  have hεbij : Function.Bijective εr := by
    refine ⟨fun w₁ w₂ h => ?_, fun z => ⟨ε.inv.hom z, ?_⟩⟩
    · have h1 : ε.inv.hom (εr w₁) = ε.inv.hom (εr w₂) := by rw [h]
      have h2 : ∀ w, ε.inv.hom (εr w) = w := fun w => by
        change (ε.hom ≫ ε.inv).hom w = w
        rw [Iso.hom_inv_id]; rfl
      rwa [h2, h2] at h1
    · change (ε.inv ≫ ε.hom).hom z = z
      rw [Iso.inv_hom_id]; rfl
  have hεl : ∀ a : A, εr (a ⊗ₜ 1) =
      (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
    intro a
    have h := IsPushout.inl_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct k A ΓY) H
    have h' := congr($(h).hom a)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at h'
    exact h'
  have hεr' : ∀ s : ΓY, εr (1 ⊗ₜ s) =
      (pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop.hom s := by
    intro s
    have h := IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct k A ΓY) H
    have h' := congr($(h).hom s)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at h'
    exact h'

  let bY : Module.Basis ι ΓY (ΓY ⊗[k] A) := Algebra.TensorProduct.basis ΓY b
  let sw : ΓY ⊗[k] A ≃ₐ[k] A ⊗[k] ΓY := Algebra.TensorProduct.comm k ΓY A
  have hfun : (fun c : ι → ΓY => ∑ i,
      (pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop.hom (c i) *
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (b i))) =
      fun c => εr (sw (bY.equivFun.symm c)) := by
    funext c
    rw [Module.Basis.equivFun_symm_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : c i • bY i = c i ⊗ₜ[k] b i := by
      simp only [bY, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1]
    have h2 : sw (c i ⊗ₜ[k] b i) = b i ⊗ₜ[k] c i := rfl
    have hsplit : b i ⊗ₜ[k] c i = (b i ⊗ₜ[k] (1 : ΓY)) * ((1 : A) ⊗ₜ[k] c i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h2, hsplit, map_mul, hεl, hεr', mul_comm]
  rw [hfun]
  exact hεbij.comp (sw.bijective.comp bY.equivFun.symm.bijective)

end Coords

section Precomp

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

theorem defined_of_pair_eq (a : PartialAction k f p)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (z : SchemeHomOver t p) (hd : a.Defined γ z)
    (γ' : SchemeHomOver t' f) (z' : SchemeHomOver t' p) (θ : T' ⟶ T)
    (h : pair γ' z' = θ ≫ pair γ z) : a.Defined γ' z' := by
  intro w hw
  rw [h, Scheme.Hom.comp_base] at hw
  obtain ⟨w', rfl⟩ := hw
  exact hd ⟨θ w', rfl⟩

theorem act_coe_of_pair_eq (a : PartialAction k f p)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (z : SchemeHomOver t p) (hd : a.Defined γ z)
    (γ' : SchemeHomOver t' f) (z' : SchemeHomOver t' p) (θ : T' ⟶ T)
    (h : pair γ' z' = θ ≫ pair γ z) (hd' : a.Defined γ' z') :
    (a.act γ' z' hd').1 = θ ≫ (a.act γ z hd).1 := by
  have hl : a.liftDom γ' z' hd' = θ ≫ a.liftDom γ z hd := by
    rw [← cancel_mono a.dom.ι, liftDom_ι, Category.assoc, liftDom_ι, h]
  rw [act_coe, act_coe, hl, Category.assoc]

theorem act_coe_congr (a : PartialAction k f p)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (z₁ z₂ : SchemeHomOver t p) (h : z₁ = z₂)
    (h₁ : a.Defined γ z₁) (h₂ : a.Defined γ z₂) :
    (a.act γ z₁ h₁).1 = (a.act γ z₂ h₂).1 := by
  subst h; rfl

theorem pair_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (γ : SchemeHomOver t f) (z : SchemeHomOver t p) :
    pair (GoodReductionJacobian.schemeHomOverComp ψ hψ γ) (GoodReductionJacobian.schemeHomOverComp ψ hψ z) =
      ψ ≫ pair γ z := by
  apply pullback.hom_ext
  · simp only [pair, pullback.lift_fst, Category.assoc, GoodReductionJacobian.schemeHomOverComp_coe]
  · simp only [pair, pullback.lift_snd, Category.assoc, GoodReductionJacobian.schemeHomOverComp_coe]

end Precomp

section Small

theorem comp_appTop_apply {X Y Z : Scheme.{u}} (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z) (s : Γ(Z, ⊤)) :
    (g₁ ≫ g₂).appTop.hom s = g₁.appTop.hom (g₂.appTop.hom s) := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem sum_swap {R : Type u} [CommRing R] {ι : Type} [Fintype ι] (x : ι → R) (y : ι → ι → R)
    (s : ι → R) : ∑ i, x i * ∑ l, y l i * s l = ∑ l, (∑ i, y l i * x i) * s l := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sum_one_apply_mul {R : Type u} [CommRing R] {d : ℕ} (s : Fin d → R) (j : Fin d)
    {S : Type u} [CommRing S] (ψ : S →+* R) :
    ∑ i, ψ ((1 : Matrix (Fin d) (Fin d) S) i j) * s i = s j := by
  rw [Finset.sum_eq_single j]
  · rw [Matrix.one_apply_eq, map_one, one_mul]
  · intro i _ hij
    rw [Matrix.one_apply_ne hij, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

end Small

section MainPos

variable {k : Type u} [Field k]

theorem main_zero {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    (a : PartialAction k f p)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p) :
    ∃ (d : ℕ) (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
        SchemeHomOver t f → GL (Fin d) Γ(T, ⊤)),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        ρ t (L.mul t x y) = ρ t x * ρ t y) ∧
      (∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
        (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
        (x : SchemeHomOver t f),
        ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
          Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
        (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k)) ⧸
            IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k))) ^ 0))
            ⟶ P),
        jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P.fromSpecStalk _ →
        ρ t x = 1 →
        ∃ hd : a.Defined
            (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
            (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
          (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) := by
  refine ⟨0, fun _ _ => 1, fun _ _ _ => (mul_one _).symm, fun _ _ _ _ _ => (map_one _).symm, ?_⟩
  intro T t x jn hjn _
  haveI : Subsingleton (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k)) ⧸
      IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k))) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
  haveI hE : IsEmpty (PrimeSpectrum (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k)) ⧸
      IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k))) ^ 0)) :=
    inferInstance
  haveI : IsEmpty ↥(pullback t (jn ≫ p)) := @Function.isEmpty _ _ hE (pullback.snd t (jn ≫ p))
  refine ⟨?_, (isInitialOfIsEmpty (X := pullback t (jn ≫ p))).hom_ext _ _⟩
  rintro _ ⟨w, rfl⟩
  exact isEmptyElim w

set_option maxHeartbeats 6400000 in

theorem main_pos {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hall : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
        a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
          GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (d : ℕ) (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
        SchemeHomOver t f → GL (Fin d) Γ(T, ⊤)),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        ρ t (L.mul t x y) = ρ t x * ρ t y) ∧
      (∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
        (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
        (x : SchemeHomOver t f),
        ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
          Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
        (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k)) ⧸
            IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k))) ^ n))
            ⟶ P),
        jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P.fromSpecStalk _ →
        ρ t x = 1 →
        ∃ hd : a.Defined
            (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
            (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
          (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) := by

  haveI : CompactSpace ↥G := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace ↥G := quasiSeparatedSpace_of_quasiSeparated f
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p

  set y₀ : ↥P := P₀.1.base (IsLocalRing.closedPoint k) with hy₀
  set O : CommRingCat.{u} := P.presheaf.stalk y₀ with hO

  let e₀ : O ⟶ CommRingCat.of k := Scheme.stalkClosedPointTo P₀.1
  have he₀ : ∀ b : O, b ∈ IsLocalRing.maximalIdeal O ↔ e₀.hom b = 0 := by
    intro b
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff e₀.hom b, isUnit_iff_ne_zero,
      not_not]
  let kO : CommRingCat.of k ⟶ O :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ P.presheaf.germ ⊤ y₀ trivial
  have hSkO : Spec.map kO = P.fromSpecStalk y₀ ≫ p := by
    have h1 : Spec.map (P.presheaf.germ ⊤ y₀ trivial) = P.fromSpecStalk y₀ ≫ P.toSpecΓ :=
      (Scheme.fromSpecStalk_toSpecΓ P y₀).symm
    have h2 : P.toSpecΓ ≫ Spec.map p.appTop = p ≫ (Spec (CommRingCat.of k)).toSpecΓ :=
      (Scheme.toSpecΓ_naturality p).symm
    have h3 : (Spec (CommRingCat.of k)).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv =
        𝟙 _ := by
      rw [← AlgebraicGeometry.SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
    calc Spec.map kO
        = Spec.map (P.presheaf.germ ⊤ y₀ trivial) ≫ Spec.map p.appTop ≫
            Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
          simp only [kO, Spec.map_comp, Category.assoc]
      _ = P.fromSpecStalk y₀ ≫ (P.toSpecΓ ≫ Spec.map p.appTop) ≫
            Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
          rw [h1]; simp only [Category.assoc]
      _ = P.fromSpecStalk y₀ ≫ p ≫ ((Spec (CommRingCat.of k)).toSpecΓ ≫
            Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv) := by
          rw [h2]; simp only [Category.assoc]
      _ = P.fromSpecStalk y₀ ≫ p := by rw [h3, Category.comp_id]
  have hkO : kO ≫ e₀ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hSkO, ← Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    exact P₀.2
  have hkO' : ∀ c : k, e₀.hom (kO.hom c) = c := fun c => by
    change (kO ≫ e₀).hom c = c
    rw [hkO]; rfl

  letI algO : Algebra k O := kO.hom.toAlgebra
  let A : Type u := O ⧸ IsLocalRing.maximalIdeal O ^ n
  have halgA : ∀ c : k, algebraMap k A c = Ideal.Quotient.mk _ (kO.hom c) := fun c => rfl
  have hq : ∀ b ∈ IsLocalRing.maximalIdeal O ^ n, e₀.hom b = 0 := by
    intro b hb
    exact (he₀ b).mp (Ideal.pow_le_self (Nat.one_le_iff_ne_zero.mp hn) hb)
  let q : A →+* k := Ideal.Quotient.lift _ e₀.hom hq
  have hqalg : ∀ c : k, q (algebraMap k A c) = c := fun c => by
    rw [halgA]; exact hkO' c

  obtain ⟨sA, hsA⟩ : ∃ s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k),
      s = Spec.map (CommRingCat.ofHom (algebraMap k A)) := ⟨_, rfl⟩
  let σ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom q)
  have hσs : σ ≫ sA = 𝟙 _ := by
    rw [hsA]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  obtain ⟨jA, hjA⟩ : ∃ j : Spec (CommRingCat.of A) ⟶ P,
      j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) ≫
        P.fromSpecStalk y₀ := ⟨_, rfl⟩
  have hσj : σ ≫ jA = P₀.1 := by
    have e1 : σ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) =
        Spec.map e₀ := by
      change Spec.map _ ≫ Spec.map _ = _
      rw [← Spec.map_comp]
      congr 1
    calc σ ≫ jA
        = σ ≫ (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) ≫ P.fromSpecStalk y₀) := _ ≫= hjA
      _ = (σ ≫ Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)))) ≫ P.fromSpecStalk y₀ :=
          (Category.assoc _ _ _).symm
      _ = Spec.map e₀ ≫ P.fromSpecStalk y₀ := e1 =≫ _
      _ = P₀.1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk P₀.1
  have hjs : jA ≫ p = sA := by
    have e1 : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ CommRingCat.of A) =
        kO ≫ CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)) := rfl
    calc jA ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) ≫
          (P.fromSpecStalk y₀ ≫ p) := by rw [hjA, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) ≫
          Spec.map kO := by rw [hSkO]
      _ = Spec.map (kO ≫ CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) :=
          (Spec.map_comp _ _).symm
      _ = sA := by rw [← e1, hsA]
  haveI : Mono jA := by
    rw [hjA]
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance

  haveI : Subsingleton ↥(Spec (CommRingCat.of A)) := subsingleton_primeSpectrum_quotient O n
  haveI : IsLocalHom (algebraMap k O) := by
    refine ⟨fun c hc => ?_⟩
    by_contra h0
    rw [isUnit_iff_ne_zero, not_not] at h0
    rw [h0, map_zero] at hc
    exact not_isUnit_zero hc
  have hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap k O)) := by
    intro r
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine ⟨IsLocalRing.residue k (e₀.hom o), ?_⟩
    rw [IsLocalRing.ResidueField.map_residue]
    change IsLocalRing.residue O (kO.hom (e₀.hom o)) = IsLocalRing.residue O o
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, he₀, map_sub, hkO', sub_self]
  haveI : Module.Finite k A :=
    IsLocalRing.moduleFinite_quotient_maximalIdeal_pow_of_residueField_map_surjective hres n
  let dA : ℕ := Module.finrank k A
  let b : Module.Basis (Fin dA) k A := Module.finBasis k A
  let bt : Fin dA → Γ(Spec (CommRingCat.of A), ⊤) := fun i =>
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (b i)

  have hsc : ∀ r : k, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (algebraMap k A r) =
      sA.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r) := by
    intro r
    have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A))
    rw [← hsA] at h
    exact congr($(h).hom r)
  have hbt : ∀ s : Γ(Spec (CommRingCat.of A), ⊤), s = ∑ i,
      sA.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        (b.repr ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom s) i)) * bt i := by
    intro s
    have h1 : s = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom s) := by
      change s = ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv).hom s
      rw [Iso.hom_inv_id]; rfl
    conv_lhs => rw [h1, ← b.sum_repr ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom s)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, hsc]

  let uA : SchemeHomOver (pullback.fst f sA ≫ f) f := ⟨pullback.fst f sA, rfl⟩
  let zA : SchemeHomOver (pullback.fst f sA ≫ f) p :=
    ⟨pullback.snd f sA ≫ jA, by rw [Category.assoc, hjs]; exact pullback.condition.symm⟩
  have huA : uA.1 = pullback.fst f sA := rfl
  have hzA : zA.1 = pullback.snd f sA ≫ jA := rfl
  have hlw : 𝟙 G ≫ f = (f ≫ σ) ≫ sA := by
    rw [Category.assoc, hσs, Category.comp_id, Category.id_comp]
  let lam : G ⟶ pullback f sA := pullback.lift (𝟙 G) (f ≫ σ) hlw
  have hlam_fst : lam ≫ pullback.fst f sA = 𝟙 G := pullback.lift_fst _ _ _
  have hlam_snd : lam ≫ pullback.snd f sA = f ≫ σ := pullback.lift_snd _ _ _
  have hlamf : lam ≫ (pullback.fst f sA ≫ f) = f := by
    rw [← Category.assoc, hlam_fst, Category.id_comp]
  have hlamsurj : ∀ w : ↥(pullback f sA), ∃ w', lam w' = w := fun w =>
    ⟨pullback.fst f sA w, fst_injective_of_section f sA σ hσs (by
      rw [← Scheme.Hom.comp_apply, hlam_fst]; rfl)⟩
  let P₀G : SchemeHomOver f p := GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) P₀
  let γ₀ : SchemeHomOver f f := GoodReductionJacobian.schemeHomOverComp lam hlamf uA
  have hzA0 : GoodReductionJacobian.schemeHomOverComp lam hlamf zA = P₀G := by
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe, hzA,
      ← Category.assoc, hlam_snd, Category.assoc, hσj]
  have hpair0 : pair γ₀ P₀G = lam ≫ pair uA zA := by
    rw [← hzA0]; exact pair_comp lam hlamf uA zA
  obtain ⟨hd0, hact0⟩ := hall f γ₀
  have hdA : a.Defined uA zA := by
    rintro _ ⟨w₁, rfl⟩
    obtain ⟨w', rfl⟩ := hlamsurj w₁
    apply hd0
    exact ⟨w', by rw [hpair0]; rfl⟩
  obtain ⟨α, hα⟩ : ∃ α' : pullback f sA ⟶ P, α' = (a.act uA zA hdA).1 := ⟨_, rfl⟩
  have hαp : α ≫ p = pullback.fst f sA ≫ f := by rw [hα]; exact (a.act uA zA hdA).2
  have hια : lam ≫ α = f ≫ P₀.1 := by
    have h1 := act_coe_of_pair_eq a uA zA hdA γ₀ P₀G lam hpair0 hd0
    rw [hact0] at h1
    rw [hα, ← h1]
    rfl

  obtain ⟨β, hβ⟩ :=
    AlgebraicGeometry.exists_comp_specMap_quotient_maximalIdeal_pow_eq_of_section_comp_eq
      p P₀.1 P₀.2 n jA hjA sA hjs σ hσj f lam hlam_fst hlam_snd α hια
  have hβs : β ≫ sA = pullback.fst f sA ≫ f := by
    have h : β ≫ (jA ≫ p) = pullback.fst f sA ≫ f := by rw [← Category.assoc, hβ, hαp]
    rwa [hjs] at h

  have hΘG := coords_bijective f A b
  rw [← hsA] at hΘG
  let ΘG : (Fin dA → Γ(G, ⊤)) ≃ Γ(pullback f sA, ⊤) := Equiv.ofBijective _ hΘG
  let c : Matrix (Fin dA) (Fin dA) Γ(G, ⊤) := fun i j => ΘG.symm (β.appTop.hom (bt j)) i
  have hc : ∀ j, β.appTop.hom (bt j) = ∑ i, (pullback.fst f sA).appTop.hom (c i j) *
      (pullback.snd f sA).appTop.hom (bt i) := by
    intro j
    exact (ΘG.apply_symm_apply (β.appTop.hom (bt j))).symm

  have hθw : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)), βT ≫ sA = t → γ.1 ≫ f = βT ≫ sA :=
    fun γ βT hβT => by rw [γ.2, hβT]
  have hzw : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
      (βT : T ⟶ Spec (CommRingCat.of A)), βT ≫ sA = t → (βT ≫ jA) ≫ p = t :=
    fun βT hβT => by rw [Category.assoc, hjs, hβT]
  have S1 : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)) (hβT : βT ≫ sA = t),
      a.Defined γ ⟨βT ≫ jA, hzw βT hβT⟩ := by
    intro T t γ βT hβT
    refine defined_of_pair_eq a uA zA hdA γ _ (pullback.lift γ.1 βT (hθw γ βT hβT)) ?_
    apply pullback.hom_ext
    · simp only [pair, Category.assoc, pullback.lift_fst, huA]
    · simp only [pair, Category.assoc, pullback.lift_snd, hzA]
      rw [← Category.assoc, pullback.lift_snd]
  have S2 : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)) (hβT : βT ≫ sA = t)
      (hd : a.Defined γ ⟨βT ≫ jA, hzw βT hβT⟩),
      (a.act γ ⟨βT ≫ jA, hzw βT hβT⟩ hd).1 = (pullback.lift γ.1 βT (hθw γ βT hβT) ≫ β) ≫ jA := by
    intro T t γ βT hβT hd
    have hpair : pair γ ⟨βT ≫ jA, hzw βT hβT⟩ = pullback.lift γ.1 βT (hθw γ βT hβT) ≫ pair uA zA := by
      apply pullback.hom_ext
      · simp only [pair, Category.assoc, pullback.lift_fst, huA]
      · simp only [pair, Category.assoc, pullback.lift_snd, hzA]
        rw [← Category.assoc, pullback.lift_snd]
    rw [act_coe_of_pair_eq a uA zA hdA γ _ (pullback.lift γ.1 βT (hθw γ βT hβT)) hpair hd, ← hα, ← hβ,
      Category.assoc]
    try rfl
  have S2s : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)) (hβT : βT ≫ sA = t),
      (pullback.lift γ.1 βT (hθw γ βT hβT) ≫ β) ≫ sA = t := by
    intro T t γ βT hβT
    rw [Category.assoc, hβs, ← Category.assoc, pullback.lift_fst, γ.2]
  have S3 : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)) (hβT : βT ≫ sA = t) (j : Fin dA),
      (pullback.lift γ.1 βT (hθw γ βT hβT) ≫ β).appTop.hom (bt j) =
        ∑ i, γ.1.appTop.hom (c i j) * βT.appTop.hom (bt i) := by
    intro T t γ βT hβT j
    rw [comp_appTop_apply, hc j, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← comp_appTop_apply, ← comp_appTop_apply, pullback.lift_fst, pullback.lift_snd]

  let f₂ : pullback f f ⟶ Spec (CommRingCat.of k) := pullback.fst f f ≫ f
  haveI : CompactSpace ↥(pullback f f) := QuasiCompact.compactSpace_of_compactSpace f₂
  haveI : QuasiSeparatedSpace ↥(pullback f f) := quasiSeparatedSpace_of_quasiSeparated f₂
  let p₁ : SchemeHomOver f₂ f := ⟨pullback.fst f f, rfl⟩
  let p₂ : SchemeHomOver f₂ f := ⟨pullback.snd f f, pullback.condition.symm⟩
  have hp₁ : p₁.1 = pullback.fst f f := rfl
  have hp₂ : p₂.1 = pullback.snd f f := rfl
  obtain ⟨μ, hμ⟩ : ∃ m : pullback f f ⟶ G, m = (L.mul f₂ p₁ p₂).1 := ⟨_, rfl⟩
  have hΘW := coords_bijective f₂ A b
  rw [← hsA] at hΘW
  have E3 : ∀ l j : Fin dA, μ.appTop.hom (c l j) =
      ∑ i, (pullback.snd f f).appTop.hom (c l i) * (pullback.fst f f).appTop.hom (c i j) := by

    let tW : pullback f₂ sA ⟶ Spec (CommRingCat.of k) := pullback.fst f₂ sA ≫ f₂
    let γ₁ : SchemeHomOver tW f := GoodReductionJacobian.schemeHomOverComp (pullback.fst f₂ sA) rfl p₁
    let γ₂ : SchemeHomOver tW f := GoodReductionJacobian.schemeHomOverComp (pullback.fst f₂ sA) rfl p₂
    have hγ₁ : γ₁.1 = pullback.fst f₂ sA ≫ pullback.fst f f := rfl
    have hγ₂ : γ₂.1 = pullback.fst f₂ sA ≫ pullback.snd f f := rfl
    have hγ12 : (L.mul tW γ₁ γ₂).1 = pullback.fst f₂ sA ≫ μ := by
      have h := L.mul_natural f₂ tW (pullback.fst f₂ sA) rfl p₁ p₂
      rw [hμ, ← congrArg Subtype.val h, GoodReductionJacobian.schemeHomOverComp_coe]
    have hβW : pullback.snd f₂ sA ≫ sA = tW := pullback.condition.symm

    have hd₁ := S1 γ₂ (pullback.snd f₂ sA) hβW
    have hβ' := S2s γ₂ (pullback.snd f₂ sA) hβW
    have hz' : a.act γ₂ ⟨pullback.snd f₂ sA ≫ jA, hzw _ hβW⟩ hd₁ =
        ⟨(pullback.lift γ₂.1 (pullback.snd f₂ sA) (hθw γ₂ _ hβW) ≫ β) ≫ jA, hzw _ hβ'⟩ :=
      Subtype.ext (S2 γ₂ (pullback.snd f₂ sA) hβW hd₁)
    have hd₂ : a.Defined γ₁ (a.act γ₂ ⟨pullback.snd f₂ sA ≫ jA, hzw _ hβW⟩ hd₁) := by
      rw [hz']; exact S1 γ₁ _ hβ'
    obtain ⟨hd₃, hassoc⟩ := ha tW γ₁ γ₂ ⟨pullback.snd f₂ sA ≫ jA, hzw _ hβW⟩ hd₁ hd₂
    have hL : (a.act γ₁ (a.act γ₂ ⟨pullback.snd f₂ sA ≫ jA, hzw _ hβW⟩ hd₁) hd₂).1 =
        (pullback.lift γ₁.1 _ (hθw γ₁ _ hβ') ≫ β) ≫ jA := by
      rw [act_coe_congr a γ₁ _ _ hz' hd₂ (S1 γ₁ _ hβ'), S2 γ₁ _ hβ']
    have hR : (a.act (L.mul tW γ₁ γ₂) ⟨pullback.snd f₂ sA ≫ jA, hzw _ hβW⟩ hd₃).1 =
        (pullback.lift (L.mul tW γ₁ γ₂).1 (pullback.snd f₂ sA) (hθw _ _ hβW) ≫ β) ≫ jA :=
      S2 _ (pullback.snd f₂ sA) hβW hd₃
    have E1 : pullback.lift γ₁.1 _ (hθw γ₁ _ hβ') ≫ β =
        pullback.lift (L.mul tW γ₁ γ₂).1 (pullback.snd f₂ sA) (hθw _ _ hβW) ≫ β := by
      rw [← cancel_mono jA, ← hL, ← hR, hassoc]

    intro l j
    have E2 := congrArg (fun φ : pullback f₂ sA ⟶ Spec (CommRingCat.of A) => φ.appTop.hom (bt j)) E1
    simp only at E2
    rw [S3 γ₁ _ hβ' j, S3 _ _ hβW j, hγ₁, hγ12] at E2
    simp_rw [S3 γ₂ _ hβW, hγ₂, comp_appTop_apply] at E2
    rw [sum_swap] at E2
    simp_rw [← map_mul, ← map_sum] at E2
    have hinj := hΘW.1 E2
    exact (congrFun hinj l).symm

  have hC : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      c.map (L.mul t x y).1.appTop.hom = c.map y.1.appTop.hom * c.map x.1.appTop.hom := by
    intro T t x y
    let xy : T ⟶ pullback f f := pullback.lift x.1 y.1 (by rw [x.2, y.2])
    have hxy : xy ≫ f₂ = t := by
      change xy ≫ pullback.fst f f ≫ f = t
      rw [← Category.assoc, pullback.lift_fst, x.2]
    have hx : GoodReductionJacobian.schemeHomOverComp xy hxy p₁ = x := Subtype.ext (pullback.lift_fst _ _ _)
    have hy : GoodReductionJacobian.schemeHomOverComp xy hxy p₂ = y := Subtype.ext (pullback.lift_snd _ _ _)
    have hm : (L.mul t x y).1 = xy ≫ μ := by
      have h := L.mul_natural f₂ t xy hxy p₁ p₂
      rw [hx, hy] at h
      rw [← h, GoodReductionJacobian.schemeHomOverComp_coe, hμ]
    ext i j
    rw [Matrix.map_apply, hm, comp_appTop_apply, E3, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, ← comp_appTop_apply, ← comp_appTop_apply, pullback.lift_snd, pullback.lift_fst,
      Matrix.map_apply, Matrix.map_apply]

  have hΘk := coords_bijective (𝟙 (Spec (CommRingCat.of k))) A b
  rw [← hsA] at hΘk
  have E5 : c.map (L.one (𝟙 (Spec (CommRingCat.of k)))).1.appTop.hom = 1 := by

    have hone1 : (L.one sA).1 = sA ≫ (L.one (𝟙 (Spec (CommRingCat.of k)))).1 :=
      (congrArg Subtype.val (L.one_natural (𝟙 _) sA sA (Category.comp_id sA))).symm
    have hβ1 : 𝟙 (Spec (CommRingCat.of A)) ≫ sA = sA := Category.id_comp _
    have hd1 := S1 (L.one sA) (𝟙 _) hβ1
    have hunit := hu sA ⟨𝟙 _ ≫ jA, hzw _ hβ1⟩ hd1
    have E4 : pullback.lift (L.one sA).1 (𝟙 _) (hθw _ _ hβ1) ≫ β = 𝟙 _ := by
      rw [← cancel_mono jA, ← S2 (L.one sA) (𝟙 _) hβ1 hd1, hunit]
    have E4' : ∀ j, ∑ i, sA.appTop.hom ((L.one (𝟙 (Spec (CommRingCat.of k)))).1.appTop.hom (c i j)) *
        bt i = bt j := by
      intro j
      have h := S3 (L.one sA) (𝟙 _) hβ1 j
      rw [E4, hone1] at h
      simp_rw [comp_appTop_apply] at h
      have h__af := h.symm
      simp only [Scheme.Hom.id_appTop] at h__af
      exact h__af

    ext i j
    have hcond : pullback.fst (𝟙 (Spec (CommRingCat.of k))) sA ≫ 𝟙 _ = pullback.snd (𝟙 _) sA ≫ sA :=
      pullback.condition
    have key : (fun i => (L.one (𝟙 (Spec (CommRingCat.of k)))).1.appTop.hom (c i j)) =
        fun i => (1 : Matrix (Fin dA) (Fin dA) Γ(Spec (CommRingCat.of k), ⊤)) i j := by
      apply hΘk.1
      simp only
      have h2 := congrArg (fun s => (pullback.snd (𝟙 (Spec (CommRingCat.of k))) sA).appTop.hom s) (E4' j)
      have hsf : ∀ v, (pullback.snd (𝟙 (Spec (CommRingCat.of k))) sA).appTop.hom (sA.appTop.hom v) =
          (pullback.fst (𝟙 (Spec (CommRingCat.of k))) sA).appTop.hom v := fun v => by
        rw [← comp_appTop_apply, ← hcond, comp_appTop_apply, Scheme.Hom.id_appTop]; rfl
      simp only [map_sum, map_mul, hsf] at h2
      rw [sum_one_apply_mul _ j]
      exact h2
    have := congrFun key i
    rw [Matrix.map_apply, this]
  have hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      c.map (L.one t).1.appTop.hom = 1 := by
    intro T t
    have h1 : (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of k)))).1 :=
      (congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id t))).symm
    have h2 : c.map (L.one t).1.appTop.hom =
        (c.map (L.one (𝟙 (Spec (CommRingCat.of k)))).1.appTop.hom).map t.appTop.hom := by
      ext i j
      simp only [Matrix.map_apply]
      rw [h1, comp_appTop_apply]
    rw [h2, E5, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinv1 : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      c.map x.1.appTop.hom * c.map (L.inv t x).1.appTop.hom = 1 := by
    intro T t x
    rw [← hC, L.inv_mul_cancel, hone]
  have hinv2 : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      c.map (L.inv t x).1.appTop.hom * c.map x.1.appTop.hom = 1 := by
    intro T t x
    rw [← hC, L.mul_inv_cancel, hone]

  let ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      SchemeHomOver t f → GL (Fin dA) Γ(T, ⊤) := fun t x =>
    ⟨(c.map x.1.appTop.hom).transpose, (c.map (L.inv t x).1.appTop.hom).transpose,
      by rw [← Matrix.transpose_mul, hinv2, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, hinv1, Matrix.transpose_one]⟩
  have hρval : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      (ρ t x).val = (c.map x.1.appTop.hom).transpose := fun _ _ => rfl
  refine ⟨dA, ρ, ?_, ?_, ?_⟩
  ·
    intro T t x y
    apply Units.ext
    rw [Units.val_mul, hρval, hρval, hρval, hC, Matrix.transpose_mul]
  ·
    intro T T' t t' ψ hψ x
    apply Units.ext
    rw [hρval]
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hρval, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.transpose_apply, Matrix.map_apply, GoodReductionJacobian.schemeHomOverComp_coe,
      comp_appTop_apply]
  ·
    intro T t x jn hjn h1
    obtain rfl : jn = jA := hjn.trans hjA.symm
    have hCx : c.map x.1.appTop.hom = 1 := by
      have h2 := congrArg (fun U : GL (Fin dA) Γ(T, ⊤) => U.val.transpose) h1
      simp only [hρval, Matrix.transpose_transpose, Units.val_one, Matrix.transpose_one] at h2
      exact h2
    have hβT : pullback.snd t (jn ≫ p) ≫ sA = pullback.fst t (jn ≫ p) ≫ t :=
      ((pullback.condition (f := t) (g := jn ≫ p)).trans (pullback.snd t (jn ≫ p) ≫= hjs)).symm
    refine ⟨S1 (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x)
      (pullback.snd t (jn ≫ p)) hβT, ?_⟩
    rw [S2 _ _ hβT]
    congr 1

    apply ext_of_isAffine
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    have hgen : ∀ (θ : pullback t (jn ≫ p) ⟶ Spec (CommRingCat.of A)),
        θ ≫ sA = pullback.fst t (jn ≫ p) ≫ t →
        (∀ j, θ.appTop.hom (bt j) = (pullback.snd t (jn ≫ p)).appTop.hom (bt j)) →
        θ.appTop.hom s = (pullback.snd t (jn ≫ p)).appTop.hom s := by
      intro θ hθ hθb
      rw [hbt s, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, hθb i, ← comp_appTop_apply, ← comp_appTop_apply, hθ, hβT]
    apply hgen _ (S2s _ _ hβT)
    intro j
    rw [S3 _ _ hβT j]
    simp_rw [GoodReductionJacobian.schemeHomOverComp_coe, comp_appTop_apply]
    have hx1 : ∀ i, x.1.appTop.hom (c i j) = (1 : Matrix (Fin dA) (Fin dA) Γ(T, ⊤)) i j := by
      intro i
      have := congrFun (congrFun hCx i) j
      rwa [Matrix.map_apply] at this
    simp_rw [hx1]
    exact sum_one_apply_mul _ j (pullback.fst t (jn ≫ p)).appTop.hom

theorem main_all {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hall : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
        a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
          GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀)
    (n : ℕ) :
    ∃ (d : ℕ) (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
        SchemeHomOver t f → GL (Fin d) Γ(T, ⊤)),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        ρ t (L.mul t x y) = ρ t x * ρ t y) ∧
      (∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
        (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
        (x : SchemeHomOver t f),
        ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
          Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
        (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k)) ⧸
            IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k))) ^ n))
            ⟶ P),
        jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P.fromSpecStalk _ →
        ρ t x = 1 →
        ∃ hd : a.Defined
            (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
            (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
          (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) := by
  rcases n with _ | n
  · exact main_zero f L p a P₀
  · exact main_pos f L p a hu ha P₀ hall (n + 1) (Nat.succ_pos n)

end MainPos

end GoodReductionJacobian.PartialAction.JetLinearisationB5b

open GoodReductionJacobian.PartialAction.JetLinearisationB5b in

theorem solution
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hall : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
        a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
          GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) :
    ∃ (d : ℕ → ℕ)
      (ρ : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
        SchemeHomOver t f → GL (Fin (d n)) Γ(T, ⊤)),
      (∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        ρ n t (L.mul t x y) = ρ n t x * ρ n t y) ∧
      (∀ (n : ℕ) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
        (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
        (x : SchemeHomOver t f),
        ρ n t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
          Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ n t x)) ∧
      (∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
        ρ (n + 1) t x = 1 → ρ n t x = 1) ∧
      (∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
        (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k)) ⧸
            IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k))) ^ n))
            ⟶ P),
        jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P.fromSpecStalk _ →
        ρ n t x = 1 →
        ∃ hd : a.Defined
            (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
            (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
          (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) := by
  choose d ρ hmul hnat hfaith using fun n => main_all f L p a hu ha P₀ hall n
  refine ⟨fun n => ∑ i : Fin (n + 1), d i,
    fun n {T} t x => blockGL (fun i : Fin (n + 1) => d i) (fun i => ρ i t x), ?_, ?_, ?_, ?_⟩
  · intro n T t x y
    show blockGL (fun i : Fin (n + 1) => d i) (fun i => ρ i t (L.mul t x y)) =
      blockGL (fun i : Fin (n + 1) => d i) (fun i => ρ i t x) *
        blockGL (fun i : Fin (n + 1) => d i) (fun i => ρ i t y)
    rw [← blockGL_mul]
    congr 1
    funext i
    exact hmul i t x y
  · intro n T T' t t' ψ hψ x
    show blockGL (fun i : Fin (n + 1) => d i)
        (fun i => ρ i t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)) =
      Matrix.GeneralLinearGroup.map ψ.appTop.hom
        (blockGL (fun i : Fin (n + 1) => d i) (fun i => ρ i t x))
    rw [blockGL_map]
    congr 1
    funext i
    exact hnat i t t' ψ hψ x
  · intro n T t x h
    rw [blockGL_eq_one_iff] at h ⊢
    intro i
    exact h (Fin.castSucc i)
  · intro n T t x jn hjn h
    rw [blockGL_eq_one_iff] at h
    exact hfaith n t x jn hjn (h (Fin.last n))

end S_GoodReductionJacobian_PartialAction_exists_generalLinearGroup_jet_of_forall_defined_act_eq
end P2MW
export P2MW.S_GoodReductionJacobian_PartialAction_exists_generalLinearGroup_jet_of_forall_defined_act_eq (solution)
