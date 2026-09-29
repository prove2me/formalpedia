-- Prove2me | solution 1 for NumberField.IdeleClassGroup.nonempty_quotientToInvariants_iso_of_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/12babac1-68ea-5c30-b41c-28402a16bec6

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleClassGroup_nonempty_quotientToInvariants_iso_of_isScalarTower

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

noncomputable section

namespace IdeleClassFixedField

open scoped TensorProduct

section GaloisTensor

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable (A : Type*) [CommRing A] [Algebra K A]

private def tensorAct (σ : L ≃ₐ[K] L) : A ⊗[K] L ≃ₐ[A] A ⊗[K] L :=
  Algebra.TensorProduct.congr AlgEquiv.refl σ

private theorem tensorAct_tmul (σ : L ≃ₐ[K] L) (a : A) (l : L) :
    tensorAct K L A σ (a ⊗ₜ l) = a ⊗ₜ σ l := rfl

private theorem tensorAct_algebraMap (σ : L ≃ₐ[K] L) (a : A) :
    tensorAct K L A σ (algebraMap A (A ⊗[K] L) a) = algebraMap A (A ⊗[K] L) a :=
  (tensorAct K L A σ).commutes a

private theorem algebraMap_tensor_injective [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Function.Injective (algebraMap A (A ⊗[K] L)) := by
  obtain ⟨d, hd⟩ := Algebra.trace_surjective K L 1
  let ε : L →ₗ[K] K := (Algebra.trace K L).comp (LinearMap.mulLeft K d)
  have hε : ε 1 = 1 := by simp [ε, hd]
  let r : A ⊗[K] L →ₗ[A] A := (TensorProduct.AlgebraTensorModule.rid K A A).toLinearMap ∘ₗ (ε.baseChange A)
  intro a b hab
  have h := congrArg r hab
  simpa [r, Algebra.TensorProduct.algebraMap_apply, LinearMap.baseChange_tmul, hε] using h

section Transport

variable {C : Type*} [CommRing C] [Algebra A C]

private def conjTensorAct (te : A ⊗[K] L ≃ₐ[A] C) (σ : L ≃ₐ[K] L) : C ≃ₐ[A] C :=
  te.symm.trans ((tensorAct K L A σ).trans te)

private theorem conjTensorAct_apply (te : A ⊗[K] L ≃ₐ[A] C) (σ : L ≃ₐ[K] L) (c : C) :
    conjTensorAct K L A te σ c = te (tensorAct K L A σ (te.symm c)) := rfl

end Transport

section Fixed

variable [FiniteDimensional K L] [IsGalois K L]

private theorem forall_tensorAct_eq_self_iff (x : A ⊗[K] L) :
    (∀ σ : L ≃ₐ[K] L, tensorAct K L A σ x = x) ↔ x ∈ Set.range (algebraMap A (A ⊗[K] L)) := by
  constructor
  · intro hx
    obtain ⟨d, hd⟩ := Algebra.trace_surjective K L 1
    let P : L →ₗ[K] L := (Algebra.linearMap K L) ∘ₗ (Algebra.trace K L) ∘ₗ (LinearMap.mulLeft K d)
    have hP : ∀ l : L, P l = ∑ σ : L ≃ₐ[K] L, σ (d * l) := fun l => by
      simp only [P, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, Algebra.linearMap_apply]
      exact trace_eq_sum_automorphisms (d * l)
    let Q : A ⊗[K] L →ₗ[A] A ⊗[K] L := P.baseChange A
    have hQ : ∀ y : A ⊗[K] L, Q y = ∑ σ : L ≃ₐ[K] L, ((1 : A) ⊗ₜ[K] σ d) * tensorAct K L A σ y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a l =>
          simp only [Q, LinearMap.baseChange_tmul, hP, tensorAct_tmul, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul, map_mul, TensorProduct.tmul_sum]
      | add y z hy hz => simp only [map_add, hy, hz, mul_add, Finset.sum_add_distrib]
    have hQr : ∀ y : A ⊗[K] L, Q y ∈ Set.range (algebraMap A (A ⊗[K] L)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul a l =>
          refine ⟨Algebra.trace K L (d * l) • a, ?_⟩
          simp only [Q, LinearMap.baseChange_tmul]
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
            TensorProduct.smul_tmul]
          congr 1
          simp only [P, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, Algebra.linearMap_apply,
            Algebra.algebraMap_eq_smul_one]
      | add y z hy hz =>
          obtain ⟨a, ha⟩ := hy; obtain ⟨b, hb⟩ := hz
          exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    have hfix : Q x = x := by
      rw [hQ]
      simp_rw [hx]
      rw [← Finset.sum_mul, ← TensorProduct.tmul_sum, ← trace_eq_sum_automorphisms, hd, map_one,
        ← Algebra.TensorProduct.one_def, one_mul]
    rw [← hfix]
    exact hQr x
  · rintro ⟨a, rfl⟩ σ
    exact tensorAct_algebraMap K L A σ a

variable {C : Type*} [CommRing C] [Algebra A C]

private theorem forall_conjTensorAct_eq_self_iff (te : A ⊗[K] L ≃ₐ[A] C) (c : C) :
    (∀ σ : L ≃ₐ[K] L, conjTensorAct K L A te σ c = c) ↔ c ∈ Set.range (algebraMap A C) := by
  have key : (∀ σ : L ≃ₐ[K] L, conjTensorAct K L A te σ c = c) ↔
      ∀ σ : L ≃ₐ[K] L, tensorAct K L A σ (te.symm c) = te.symm c := by
    refine forall_congr' fun σ => ?_
    rw [conjTensorAct_apply, ← te.symm.injective.eq_iff, AlgEquiv.symm_apply_apply]
  rw [key, forall_tensorAct_eq_self_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← te.apply_symm_apply c, ← ha, AlgEquiv.commutes]
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [AlgEquiv.commutes]⟩

private theorem algebraMap_injective_of_equiv (te : A ⊗[K] L ≃ₐ[A] C) :
    Function.Injective (algebraMap A C) := by
  intro a b h
  apply algebraMap_tensor_injective K L A
  apply te.injective
  rw [AlgEquiv.commutes, AlgEquiv.commutes, h]

private theorem forall_conjTensorAct_units_eq_self_iff (te : A ⊗[K] L ≃ₐ[A] C) (u : Cˣ) :
    (∀ σ : L ≃ₐ[K] L, conjTensorAct K L A te σ (u : C) = u) ↔
      u ∈ (Units.map (algebraMap A C : A →* C)).range := by
  constructor
  · intro hu
    obtain ⟨a, ha⟩ := (forall_conjTensorAct_eq_self_iff K L A te (u : C)).mp hu
    have hu' : ∀ σ : L ≃ₐ[K] L, conjTensorAct K L A te σ (↑u⁻¹ : C) = ↑u⁻¹ := by
      intro σ
      have h1 : conjTensorAct K L A te σ (↑u⁻¹ : C) * (u : C) = 1 := by
        conv_lhs => rw [← hu σ, ← map_mul, Units.inv_mul, map_one]
      calc conjTensorAct K L A te σ (↑u⁻¹ : C)
            = conjTensorAct K L A te σ (↑u⁻¹ : C) * (u : C) * (↑u⁻¹ : C) := by
              rw [mul_assoc, Units.mul_inv, mul_one]
        _ = ↑u⁻¹ := by rw [h1, one_mul]
    obtain ⟨b, hb⟩ := (forall_conjTensorAct_eq_self_iff K L A te (↑u⁻¹ : C)).mp hu'
    have hab : a * b = 1 := by
      apply algebraMap_injective_of_equiv K L A te
      rw [map_mul, ha, hb, Units.mul_inv, map_one]
    refine ⟨Units.mkOfMulEqOne a b hab, Units.ext ?_⟩
    simp [ha]
  · rintro ⟨v, rfl⟩ σ
    simp only [Units.coe_map, MonoidHom.coe_coe]
    exact (forall_conjTensorAct_eq_self_iff K L A te _).mpr ⟨v, rfl⟩ σ

end Fixed

end GaloisTensor

section ClassAct

variable {R B L : Type*} [CommRing R] [IsDedekindDomain R] [Field B] [Field L] [Algebra R L]
  [IsFractionRing R L] [Algebra B L]

private theorem classAct_mk (D : IdeleGaloisDescent R B L) (g : L ≃ₐ[B] L) (u : (AdeleRing R L)ˣ) :
    D.classAct g (QuotientGroup.mk u) = QuotientGroup.mk (D.unitsAct g u) := rfl

private theorem unitsAct_map_algebraMap (D : IdeleGaloisDescent R B L) (g : L ≃ₐ[B] L) (x : Lˣ) :
    D.unitsAct g (Units.map (algebraMap L (AdeleRing R L) : L →* AdeleRing R L) x) =
      Units.map (algebraMap L (AdeleRing R L) : L →* AdeleRing R L) (Units.map (g : L →* L) x) :=
  Units.ext (D.compat g x)

end ClassAct

section Hilbert90

open groupCohomology

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private abbrev unitsDiag : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)

private theorem unitsDiag_injective : Function.Injective (unitsDiag : Lˣ →* (AdeleRing (𝓞 L) L)ˣ) :=
  Units.map_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 L) L)

omit [NumberField K] in
private theorem unitsAct_unitsDiag (D : IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) (x : Lˣ) :
    D.unitsAct τ (unitsDiag x) = unitsDiag (Units.map (τ : L →* L) x) :=
  Units.ext (D.compat τ x)

private theorem mem_sup_of_forall_inv_mul_mem (D : IdeleGaloisDescent (𝓞 L) K L)
    (β : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L)
    (hfix : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      (∀ τ : L ≃ₐ[K] L, D.unitsAct τ u = u) ↔ u ∈ (Units.map β.toMonoidHom).range)
    (u : (AdeleRing (𝓞 L) L)ˣ)
    (hall : ∀ τ : L ≃ₐ[K] L, (D.unitsAct τ u)⁻¹ * u ∈ principalIdeles (𝓞 L) L) :
    u ∈ (Units.map β.toMonoidHom).range ⊔ principalIdeles (𝓞 L) L := by

  let ℓ : (L ≃ₐ[K] L) → Lˣ := fun τ => (hall τ).choose
  have hℓ : ∀ τ, unitsDiag (ℓ τ) = (D.unitsAct τ u)⁻¹ * u := fun τ => (hall τ).choose_spec

  have hcoc : IsMulCocycle₁ ℓ := by
    intro σ τ
    apply unitsDiag_injective
    rw [AlgEquiv.smul_units_def, map_mul, ← unitsAct_unitsDiag D σ, hℓ σ, hℓ τ, hℓ (σ * τ),
      map_mul D.unitsAct, MulAut.mul_apply, map_mul, map_inv]
    rw [mul_assoc, mul_inv_cancel_left]

  obtain ⟨b, hb⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units ℓ hcoc

  have hfixed : ∀ τ, D.unitsAct τ (u * unitsDiag b) = u * unitsDiag b := fun τ => by
    have : unitsDiag (τ • b) = (D.unitsAct τ u)⁻¹ * u * unitsDiag b := by
      rw [div_eq_iff_eq_mul.mp (hb τ), map_mul, hℓ τ]
    rw [map_mul, unitsAct_unitsDiag D τ, ← AlgEquiv.smul_units_def, this, mul_comm u (unitsDiag b),
      ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_comm]
  have hrange := (hfix (u * unitsDiag b)).mp hfixed
  have : u = (u * unitsDiag b) * (unitsDiag b)⁻¹ := by rw [mul_inv_cancel_right]
  rw [this]
  exact Subgroup.mul_mem_sup hrange (Subgroup.inv_mem _ ⟨b, rfl⟩)

end Hilbert90

section Tower

open M4aHerbrand.Bridge M4aHerbrand.GenuineDescent

variable {E F K : Type*} [Field E] [Field F] [Field K] [Algebra E F] [Algebra E K] [Algebra K F]
  [IsScalarTower E K F]

private def resHom : (F ≃ₐ[K] F) →* (F ≃ₐ[E] F) where
  toFun τ := τ.restrictScalars E
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

private theorem resHom_apply (τ : F ≃ₐ[K] F) (x : F) : resHom (E := E) τ x = τ x := rfl

private theorem resHom_commutes (τ : F ≃ₐ[K] F) (x : K) :
    resHom (E := E) τ (algebraMap K F x) = algebraMap K F x :=
  τ.commutes x

private def liftFixing (h : F ≃ₐ[E] F) (hh : ∀ x : K, h (algebraMap K F x) = algebraMap K F x) :
    F ≃ₐ[K] F :=
  { h.toRingEquiv with commutes' := hh }

private theorem resHom_liftFixing (h : F ≃ₐ[E] F) (hh : ∀ x : K, h (algebraMap K F x) = algebraMap K F x) :
    resHom (E := E) (liftFixing h hh) = h :=
  AlgEquiv.ext fun _ => rfl

variable [NumberField F] [NumberField K]

omit [NumberField K] in

private def restrictDescent (D : IdeleGaloisDescent (𝓞 F) E F) : IdeleGaloisDescent (𝓞 F) K F where
  act := D.act.comp resHom
  compat τ x := D.compat (resHom τ) x
  continuous_act τ := D.continuous_act (resHom τ)

omit [NumberField K] in
private theorem restrictDescent_act (D : IdeleGaloisDescent (𝓞 F) E F) (τ : F ≃ₐ[K] F) :
    (restrictDescent (K := K) D).act τ = D.act (resHom τ) := rfl

omit [NumberField K] in
private theorem restrictDescent_unitsAct (D : IdeleGaloisDescent (𝓞 F) E F) (τ : F ≃ₐ[K] F) :
    (restrictDescent (K := K) D).unitsAct τ = D.unitsAct (resHom τ) := rfl

private theorem restrictDescent_eq_genuine (D : IdeleGaloisDescent (𝓞 F) E F) :
    restrictDescent (K := K) D = genuineDescentDatum K F :=
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) K F
  Subsingleton.elim _ _

private theorem unitsAct_genuine_eq (τ : F ≃ₐ[K] F) (u : (AdeleRing (𝓞 F) F)ˣ) :
    (genuineDescentDatum K F).unitsAct τ u =
      letI := (genuineβ K F).toAlgebra
      Units.map (conjTensorAct K F (AdeleRing (𝓞 K) K) (genuineTensorEquiv K F) τ :
        AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F) u :=
  Units.ext rfl

private theorem algebraMap_genuine_eq :
    (letI := (genuineβ K F).toAlgebra;
      (algebraMap (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 F) F) : AdeleRing (𝓞 K) K →* AdeleRing (𝓞 F) F)) =
      (genuineβ K F).toMonoidHom := rfl

private theorem algebraMap_genuine_eq' :
    (letI := (genuineβ K F).toAlgebra;
      (algebraMap (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 F) F) : AdeleRing (𝓞 K) K → AdeleRing (𝓞 F) F)) =
      genuineβ K F := rfl

private theorem genuineβ_injective [IsGalois K F] : Function.Injective (genuineβ K F) := by
  letI := (genuineβ K F).toAlgebra
  exact algebraMap_injective_of_equiv K F (AdeleRing (𝓞 K) K) (genuineTensorEquiv K F)

private theorem forall_act_genuine_iff [IsGalois K F] (x : AdeleRing (𝓞 F) F) :
    (∀ τ : F ≃ₐ[K] F, (genuineDescentDatum K F).act τ x = x) ↔ x ∈ Set.range (genuineβ K F) := by
  letI := (genuineβ K F).toAlgebra
  rw [← algebraMap_genuine_eq',
    ← forall_conjTensorAct_eq_self_iff K F (AdeleRing (𝓞 K) K) (genuineTensorEquiv K F) x]
  exact Iff.rfl

private theorem forall_unitsAct_genuine_iff [IsGalois K F] (u : (AdeleRing (𝓞 F) F)ˣ) :
    (∀ τ : F ≃ₐ[K] F, (genuineDescentDatum K F).unitsAct τ u = u) ↔
      u ∈ (Units.map (genuineβ K F).toMonoidHom).range := by
  letI := (genuineβ K F).toAlgebra
  rw [← algebraMap_genuine_eq,
    ← forall_conjTensorAct_units_eq_self_iff K F (AdeleRing (𝓞 K) K) (genuineTensorEquiv K F) u]
  refine forall_congr' fun τ => ?_
  rw [unitsAct_genuine_eq τ u, Units.ext_iff, Units.coe_map, MonoidHom.coe_coe]

private theorem forall_act_eq_self_iff [IsGalois K F] (D : IdeleGaloisDescent (𝓞 F) E F)
    (x : AdeleRing (𝓞 F) F) :
    (∀ τ : F ≃ₐ[K] F, D.act (resHom τ) x = x) ↔ x ∈ Set.range (genuineβ K F) := by
  have h : ∀ τ : F ≃ₐ[K] F, D.act (resHom (E := E) τ) = (genuineDescentDatum K F).act τ := fun τ => by
    rw [← restrictDescent_act, restrictDescent_eq_genuine]
  simp only [h]
  exact forall_act_genuine_iff x

private theorem forall_unitsAct_eq_self_iff [IsGalois K F] (D : IdeleGaloisDescent (𝓞 F) E F)
    (u : (AdeleRing (𝓞 F) F)ˣ) :
    (∀ τ : F ≃ₐ[K] F, (restrictDescent (K := K) D).unitsAct τ u = u) ↔
      u ∈ (Units.map (genuineβ K F).toMonoidHom).range := by
  rw [restrictDescent_eq_genuine]
  exact forall_unitsAct_genuine_iff u

private theorem isInducing_genuineβ [IsGalois K F] : Topology.IsInducing (genuineβ K F) := by

  have hrange : Set.range (genuineβ K F) = ⋂ τ : F ≃ₐ[K] F, {x | (genuineDescentDatum K F).act τ x = x} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact (forall_act_genuine_iff x).symm
  have hclosed : IsClosed (Set.range (genuineβ K F)) := by
    rw [hrange]
    exact isClosed_iInter fun τ => isClosed_eq ((genuineDescentDatum K F).continuous_act τ) continuous_id
  let βa : AdeleRing (𝓞 K) K →+ AdeleRing (𝓞 F) F := (genuineβ K F).toAddMonoidHom
  have hrange' : (βa.range : Set (AdeleRing (𝓞 F) F)) = Set.range (genuineβ K F) := AddMonoidHom.coe_range βa
  have hfun : (Subtype.val ∘ βa.rangeRestrict : AdeleRing (𝓞 K) K → AdeleRing (𝓞 F) F) = genuineβ K F :=
    funext fun _ => rfl
  haveI : LocallyCompactSpace (AdeleRing (𝓞 F) F) := locallyCompactSpace_adeleRing (𝓞 F) F
  haveI : LocallyCompactSpace βa.range := by
    have h := hclosed.locallyCompactSpace
    rwa [← hrange'] at h
  have hcont : Continuous βa.rangeRestrict := by
    rw [continuous_induced_rng, hfun]
    exact continuous_genuineβ K F
  have hopen : IsOpenMap βa.rangeRestrict :=
    AddMonoidHom.isOpenMap_of_sigmaCompact βa.rangeRestrict (AddMonoidHom.rangeRestrict_surjective βa) hcont
  have hinj : Function.Injective βa.rangeRestrict := fun a b h =>
    genuineβ_injective (K := K) (F := F) (congrArg Subtype.val h)
  rw [← hfun]
  exact Topology.IsInducing.subtypeVal.comp
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen).isInducing

section Descend

variable [IsGalois K F] (D : IdeleGaloisDescent (𝓞 F) E F) (N : Subgroup (F ≃ₐ[E] F)) [N.Normal]
  (hN : ∀ g : F ≃ₐ[E] F, g ∈ N ↔ ∀ x : K, g (algebraMap K F x) = algebraMap K F x)
include hN

private theorem act_apply_mem_range (g : F ≃ₐ[E] F) (a : AdeleRing (𝓞 K) K) :
    D.act g (genuineβ K F a) ∈ Set.range (genuineβ K F) := by
  rw [← forall_act_eq_self_iff (K := K) D]
  intro τ
  have hτN : resHom (E := E) τ ∈ N := (hN _).mpr (resHom_commutes τ)
  have hconj : g⁻¹ * resHom (E := E) τ * g ∈ N := Subgroup.Normal.conj_mem' inferInstance _ hτN g
  have hfixa : D.act (resHom (E := E) (liftFixing (g⁻¹ * resHom (E := E) τ * g) ((hN _).mp hconj)))
      (genuineβ K F a) = genuineβ K F a :=
    (forall_act_eq_self_iff (K := K) D _).mpr ⟨a, rfl⟩ _
  rw [resHom_liftFixing] at hfixa
  have hmul : resHom (E := E) τ * g = g * (g⁻¹ * resHom (E := E) τ * g) := by group
  calc D.act (resHom τ) (D.act g (genuineβ K F a))
        = D.act (resHom (E := E) τ * g) (genuineβ K F a) := by
          rw [map_mul D.act (resHom (E := E) τ) g]; rfl
    _ = D.act (g * (g⁻¹ * resHom (E := E) τ * g)) (genuineβ K F a) := by rw [hmul]
    _ = D.act g (D.act (g⁻¹ * resHom (E := E) τ * g) (genuineβ K F a)) := by
          rw [map_mul D.act g (g⁻¹ * resHom (E := E) τ * g)]; rfl
    _ = D.act g (genuineβ K F a) := by rw [hfixa]

private def descendFun (g : F ≃ₐ[E] F) (a : AdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K :=
  (act_apply_mem_range D N hN g a).choose

private theorem β_descendFun (g : F ≃ₐ[E] F) (a : AdeleRing (𝓞 K) K) :
    genuineβ K F (descendFun D N hN g a) = D.act g (genuineβ K F a) :=
  (act_apply_mem_range D N hN g a).choose_spec

private theorem descendFun_eq_iff (g : F ≃ₐ[E] F) (a b : AdeleRing (𝓞 K) K) :
    descendFun D N hN g a = b ↔ D.act g (genuineβ K F a) = genuineβ K F b := by
  rw [← (genuineβ_injective (K := K) (F := F)).eq_iff, β_descendFun]

private theorem descendFun_one (a : AdeleRing (𝓞 K) K) : descendFun D N hN 1 a = a := by
  rw [descendFun_eq_iff, map_one]; rfl

private theorem descendFun_mul (g h : F ≃ₐ[E] F) (a : AdeleRing (𝓞 K) K) :
    descendFun D N hN (g * h) a = descendFun D N hN g (descendFun D N hN h a) := by
  rw [descendFun_eq_iff, map_mul, β_descendFun, β_descendFun]; rfl

private theorem descendFun_add (g : F ≃ₐ[E] F) (a b : AdeleRing (𝓞 K) K) :
    descendFun D N hN g (a + b) = descendFun D N hN g a + descendFun D N hN g b := by
  rw [descendFun_eq_iff, map_add, map_add, map_add, β_descendFun, β_descendFun]

private theorem descendFun_mul' (g : F ≃ₐ[E] F) (a b : AdeleRing (𝓞 K) K) :
    descendFun D N hN g (a * b) = descendFun D N hN g a * descendFun D N hN g b := by
  rw [descendFun_eq_iff, map_mul, map_mul, map_mul, β_descendFun, β_descendFun]

private theorem descendFun_of_mem (n : F ≃ₐ[E] F) (hn : n ∈ N) (a : AdeleRing (𝓞 K) K) :
    descendFun D N hN n a = a := by
  rw [descendFun_eq_iff]
  have h := (forall_act_eq_self_iff (K := K) D (genuineβ K F a)).mpr ⟨a, rfl⟩ (liftFixing n ((hN n).mp hn))
  rwa [resHom_liftFixing] at h

private def descendRingEquiv (g : F ≃ₐ[E] F) : AdeleRing (𝓞 K) K ≃+* AdeleRing (𝓞 K) K where
  toFun := descendFun D N hN g
  invFun := descendFun D N hN g⁻¹
  left_inv a := by rw [← descendFun_mul, inv_mul_cancel, descendFun_one]
  right_inv a := by rw [← descendFun_mul, mul_inv_cancel, descendFun_one]
  map_mul' := descendFun_mul' D N hN g
  map_add' := descendFun_add D N hN g

private def descendHom : (F ≃ₐ[E] F) →* RingAut (AdeleRing (𝓞 K) K) where
  toFun := descendRingEquiv D N hN
  map_one' := RingEquiv.ext fun a => descendFun_one D N hN a
  map_mul' g h := RingEquiv.ext fun a => descendFun_mul D N hN g h a

private theorem le_ker_descendHom : N ≤ (descendHom D N hN).ker := fun n hn =>
  MonoidHom.mem_ker.mpr (RingEquiv.ext fun a => descendFun_of_mem D N hN n hn a)

private def descendQuot : (F ≃ₐ[E] F) ⧸ N →* RingAut (AdeleRing (𝓞 K) K) :=
  QuotientGroup.lift N (descendHom D N hN) (le_ker_descendHom D N hN)

private theorem descendQuot_mk_apply (g : F ≃ₐ[E] F) (a : AdeleRing (𝓞 K) K) :
    descendQuot D N hN (QuotientGroup.mk g) a = descendFun D N hN g a := by
  show QuotientGroup.lift N (descendHom D N hN) (le_ker_descendHom D N hN) (QuotientGroup.mk g) a = _
  rw [QuotientGroup.lift_mk]
  rfl

private theorem continuous_descendFun (g : F ≃ₐ[E] F) : Continuous (descendFun D N hN g) := by
  rw [(isInducing_genuineβ (K := K) (F := F)).continuous_iff]
  have : genuineβ K F ∘ descendFun D N hN g = D.act g ∘ genuineβ K F := funext (β_descendFun D N hN g)
  rw [this]
  exact (D.continuous_act g).comp (continuous_genuineβ K F)

variable (ι : (F ≃ₐ[E] F) ⧸ N ≃* (K ≃ₐ[E] K))
  (hι : ∀ (g : F ≃ₐ[E] F) (x : K), algebraMap K F (ι (QuotientGroup.mk g) x) = g (algebraMap K F x))
include hι

private def descendDescent : IdeleGaloisDescent (𝓞 K) E K where
  act := (descendQuot D N hN).comp ι.symm.toMonoidHom
  compat h x := by
    obtain ⟨q, rfl⟩ := ι.surjective h
    induction q using QuotientGroup.induction_on with
    | H g =>
      show descendQuot D N hN (ι.symm (ι (QuotientGroup.mk g))) (algebraMap K _ x) = _
      rw [MulEquiv.symm_apply_apply, descendQuot_mk_apply, descendFun_eq_iff, genuineβ_compat, genuineβ_compat,
        D.compat, hι]
  continuous_act h := by
    obtain ⟨q, rfl⟩ := ι.surjective h
    induction q using QuotientGroup.induction_on with
    | H g =>
      have hfun : ((descendQuot D N hN).comp ι.symm.toMonoidHom (ι (QuotientGroup.mk g)) :
          AdeleRing (𝓞 K) K → AdeleRing (𝓞 K) K) = descendFun D N hN g := by
        funext a
        show descendQuot D N hN (ι.symm (ι (QuotientGroup.mk g))) a = _
        rw [MulEquiv.symm_apply_apply, descendQuot_mk_apply]
      rw [hfun]
      exact continuous_descendFun D N hN g

private theorem β_act_eq (D₂ : IdeleGaloisDescent (𝓞 K) E K) (g : F ≃ₐ[E] F) (a : AdeleRing (𝓞 K) K) :
    genuineβ K F (D₂.act (ι (QuotientGroup.mk g)) a) = D.act g (genuineβ K F a) := by
  have hD₂ : D₂ = descendDescent D N hN ι hι :=
    haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 K) E K
    Subsingleton.elim _ _
  rw [hD₂, ← β_descendFun D N hN g a]
  congr 1
  show descendQuot D N hN (ι.symm (ι (QuotientGroup.mk g))) a = _
  rw [MulEquiv.symm_apply_apply, descendQuot_mk_apply]

private theorem map_unitsAct_eq (D₂ : IdeleGaloisDescent (𝓞 K) E K) (g : F ≃ₐ[E] F)
    (v : (AdeleRing (𝓞 K) K)ˣ) :
    Units.map (genuineβ K F).toMonoidHom (D₂.unitsAct (ι (QuotientGroup.mk g)) v) =
      D.unitsAct g (Units.map (genuineβ K F).toMonoidHom v) :=
  Units.ext (β_act_eq D N hN ι hι D₂ g v)

end Descend

section Classes

variable [IsGalois K F]

omit [IsGalois K F] in

private theorem map_principalIdeles_le :
    (principalIdeles (𝓞 K) K).map (Units.map (genuineβ K F).toMonoidHom) ≤ principalIdeles (𝓞 F) F := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨Units.map (algebraMap K F).toMonoidHom x, Units.ext (genuineβ_compat K F x).symm⟩

private theorem map_mem_principalIdeles_iff (v : (AdeleRing (𝓞 K) K)ˣ) :
    Units.map (genuineβ K F).toMonoidHom v ∈ principalIdeles (𝓞 F) F ↔ v ∈ principalIdeles (𝓞 K) K := by
  constructor
  · rintro ⟨x, hx⟩
    have hfixed : ∀ τ : F ≃ₐ[K] F, τ (x : F) = x := by
      intro τ
      have h1 : (genuineDescentDatum K F).unitsAct τ (Units.map (genuineβ K F).toMonoidHom v) =
          Units.map (genuineβ K F).toMonoidHom v :=
        (forall_unitsAct_genuine_iff _).mpr ⟨v, rfl⟩ τ
      rw [← hx, unitsAct_map_algebraMap] at h1
      exact NumberField.AdeleRing.algebraMap_injective (𝓞 F) F
        (congrArg (fun w : (AdeleRing (𝓞 F) F)ˣ => (w : AdeleRing (𝓞 F) F)) h1)
    obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (x : F)).mpr hfixed
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [map_zero] at hk
      exact x.ne_zero hk.symm
    refine ⟨Units.mk0 k hk0, ?_⟩
    apply Units.ext
    apply genuineβ_injective (K := K) (F := F)
    show genuineβ K F (algebraMap K (AdeleRing (𝓞 K) K) k) = genuineβ K F v
    rw [genuineβ_compat, hk]
    exact congrArg (fun w : (AdeleRing (𝓞 F) F)ˣ => (w : AdeleRing (𝓞 F) F)) hx
  · intro hv
    exact map_principalIdeles_le ⟨v, hv, rfl⟩

private def classMap : IdeleClassGroup (𝓞 K) K →* IdeleClassGroup (𝓞 F) F :=
  QuotientGroup.map (principalIdeles (𝓞 K) K) (principalIdeles (𝓞 F) F) (Units.map (genuineβ K F).toMonoidHom)
    (Subgroup.map_le_iff_le_comap.mp map_principalIdeles_le)

omit [IsGalois K F] in
private theorem classMap_mk (v : (AdeleRing (𝓞 K) K)ˣ) :
    classMap (K := K) (F := F) (QuotientGroup.mk v) = QuotientGroup.mk (Units.map (genuineβ K F).toMonoidHom v) :=
  rfl

private theorem classMap_injective : Function.Injective (classMap (K := K) (F := F)) := by
  intro c₁ c₂ h
  induction c₁ using QuotientGroup.induction_on with
  | H v₁ =>
    induction c₂ using QuotientGroup.induction_on with
    | H v₂ =>
      rw [classMap_mk, classMap_mk, QuotientGroup.eq, ← map_inv, ← map_mul, map_mem_principalIdeles_iff] at h
      exact QuotientGroup.eq.mpr h

variable (D : IdeleGaloisDescent (𝓞 F) E F) (N : Subgroup (F ≃ₐ[E] F))
  (hN : ∀ g : F ≃ₐ[E] F, g ∈ N ↔ ∀ x : K, g (algebraMap K F x) = algebraMap K F x)
include hN

private theorem classAct_classMap (n : F ≃ₐ[E] F) (hn : n ∈ N) (c : IdeleClassGroup (𝓞 K) K) :
    D.classAct n (classMap c) = classMap c := by
  induction c using QuotientGroup.induction_on with
  | H v =>
    rw [classMap_mk, classAct_mk]
    congr 1
    have h := (forall_unitsAct_eq_self_iff (K := K) D (Units.map (genuineβ K F).toMonoidHom v)).mpr ⟨v, rfl⟩
      (liftFixing n ((hN n).mp hn))
    rwa [restrictDescent_unitsAct, resHom_liftFixing] at h

private theorem mem_range_classMap (c : IdeleClassGroup (𝓞 F) F) (hc : ∀ n ∈ N, D.classAct n c = c) :
    c ∈ Set.range (classMap (K := K) (F := F)) := by
  induction c using QuotientGroup.induction_on with
  | H u =>
    have hall : ∀ τ : F ≃ₐ[K] F,
        ((restrictDescent (K := K) D).unitsAct τ u)⁻¹ * u ∈ principalIdeles (𝓞 F) F := by
      intro τ
      rw [← QuotientGroup.eq, restrictDescent_unitsAct, ← classAct_mk]
      exact hc _ ((hN _).mpr (resHom_commutes τ))
    obtain ⟨_, ⟨v, rfl⟩, p, hp, hvp⟩ :=
      Subgroup.mem_sup.mp (mem_sup_of_forall_inv_mul_mem (restrictDescent D) (genuineβ K F)
        (forall_unitsAct_eq_self_iff (K := K) D) u hall)
    refine ⟨QuotientGroup.mk v, ?_⟩
    rw [classMap_mk, QuotientGroup.eq, ← hvp, inv_mul_cancel_left]
    exact hp

end Classes

end Tower

section Packaging

private theorem nonempty_quotientToInvariants_iso_res
    {G H C M : Type} [Group G] [Group H] [CommGroup C] [CommGroup M]
    [MulDistribMulAction G C] [MulDistribMulAction H M]
    (N : Subgroup G) [N.Normal] (ι : G ⧸ N ≃* H)
    (j : M →* C) (hinj : Function.Injective j)
    (hinv : ∀ n : G, n ∈ N → ∀ m : M, n • j m = j m)
    (hsurj : ∀ c : C, (∀ n : G, n ∈ N → n • c = c) → c ∈ Set.range j)
    (hequiv : ∀ (g : G) (m : M), j (ι (QuotientGroup.mk g) • m) = g • j m) :
    Nonempty ((Rep.ofMulDistribMulAction G C).quotientToInvariants N ≅
      Rep.res ι.toMonoidHom (Rep.ofMulDistribMulAction H M)) := by

  let f : (Rep.ofMulDistribMulAction H M).V →ₗ[ℤ] (Rep.ofMulDistribMulAction G C).V :=
    (MonoidHom.toAdditive j).toIntLinearMap
  have hf : ∀ m, f m = Additive.ofMul (j (Additive.toMul (α := M) m)) := fun _ => rfl
  have hmem : ∀ m,
      f m ∈ Representation.invariants ((Rep.ofMulDistribMulAction G C).ρ.comp N.subtype) := by
    intro m
    refine (Representation.mem_invariants ((Rep.ofMulDistribMulAction G C).ρ.comp N.subtype) (f m)).mpr
      fun n => ?_
    show (Rep.ofMulDistribMulAction G C).ρ n (f m) = f m
    rw [hf, Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul, hinv _ n.2]
  let φ : Representation.IntertwiningMap ((Rep.ofMulDistribMulAction H M).ρ.comp ι.toMonoidHom)
      ((Rep.ofMulDistribMulAction G C).ρ.quotientToInvariants N) :=
    { toLinearMap := f.codRestrict _ hmem
      isIntertwining' := fun q => QuotientGroup.induction_on q fun g => LinearMap.ext fun m => Subtype.ext (by
        show f ((Rep.ofMulDistribMulAction H M).ρ (ι (QuotientGroup.mk g)) m) =
          (Rep.ofMulDistribMulAction G C).ρ g (f m)
        rw [hf, hf, Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply,
          toMul_ofMul, toMul_ofMul, hequiv]) }
  have hφ : ∀ m, (φ m).1 = f m := fun _ => rfl
  have hbij : Function.Bijective φ := by
    constructor
    · intro x y h
      have h' : f x = f y := by rw [← hφ, ← hφ, h]
      rw [hf, hf] at h'
      exact (Additive.toMul (α := M)).injective (hinj ((Additive.ofMul (α := C)).injective h'))
    · rintro ⟨c, hc⟩
      have hc' : ∀ n : G, n ∈ N → n • Additive.toMul (α := C) c = Additive.toMul (α := C) c := fun n hn =>
        congrArg (Additive.toMul (α := C))
          ((Representation.mem_invariants ((Rep.ofMulDistribMulAction G C).ρ.comp N.subtype) c).mp hc ⟨n, hn⟩)
      obtain ⟨m, hm⟩ := hsurj _ hc'
      refine ⟨Additive.ofMul (α := M) m, Subtype.ext ?_⟩
      rw [hφ, hf]
      show Additive.ofMul (j m) = c
      rw [hm]
      exact ofMul_toMul (α := C) c
  exact ⟨(Rep.mkIso (φ.ofBijective hbij)).symm⟩

end Packaging

section Assembly

private theorem nonempty_iso_of_level {E F K : Type} [Field E] [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra E F] [Algebra E K] [Algebra K F] [IsScalarTower E K F] [IsGalois K F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (N : Subgroup (F ≃ₐ[E] F)) [N.Normal]
    (hN : ∀ g : F ≃ₐ[E] F, g ∈ N ↔ ∀ x : K, g (algebraMap K F x) = algebraMap K F x)
    (D₂ : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (IdeleClassGroup (𝓞 K) K)]
    (hact₂ : ∀ (g : K ≃ₐ[E] K) (c : IdeleClassGroup (𝓞 K) K), g • c = D₂.classAct g c)
    (ι : (F ≃ₐ[E] F) ⧸ N ≃* (K ≃ₐ[E] K))
    (hι : ∀ (g : F ≃ₐ[E] F) (x : K), algebraMap K F (ι (QuotientGroup.mk g) x) = g (algebraMap K F x)) :
    Nonempty ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)).quotientToInvariants N ≅
      Rep.res ι.toMonoidHom
        (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (IdeleClassGroup (𝓞 K) K))) := by
  refine nonempty_quotientToInvariants_iso_res N ι (classMap (K := K) (F := F))
    (classMap_injective (K := K) (F := F)) ?_ ?_ ?_
  · intro n hn m
    rw [hact]
    exact classAct_classMap D N hN n hn m
  · intro c hc
    exact mem_range_classMap D N hN c fun n hn => by rw [← hact]; exact hc n hn
  · intro g m
    induction m using QuotientGroup.induction_on with
    | H v =>
      rw [hact₂, hact, classAct_mk, classMap_mk, classMap_mk, classAct_mk, map_unitsAct_eq D N hN ι hι D₂ g v]

end Assembly

end IdeleClassFixedField

end

theorem solution
    (E F N : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field N] [NumberField N]
    [Algebra E F] [Algebra E N] [Algebra F N] [IsScalarTower E F N] [IsGalois E N]
    (D : IdeleGaloisDescent (𝓞 N) E N)
    [MulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)]
    (hact : ∀ (g : N ≃ₐ[E] N) (c : IdeleClassGroup (𝓞 N) N), g • c = D.classAct g c)
    (D' : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact' : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D'.classAct g c)
    (S : Subgroup (N ≃ₐ[E] N)) [S.Normal]
    (ι : (N ≃ₐ[E] N) ⧸ S ≃* (F ≃ₐ[E] F))
    (hι : ∀ (g : N ≃ₐ[E] N) (x : F),
      algebraMap F N (ι (QuotientGroup.mk g) x) = g (algebraMap F N x)) :
    Nonempty
      ((Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).quotientToInvariants S ≅
        Rep.res ι.toMonoidHom
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) := by
  haveI : IsGalois F N := IsGalois.tower_top_of_isGalois E F N
  refine IdeleClassFixedField.nonempty_iso_of_level (K := F) D hact S (fun g => ?_) D' hact' ι hι
  rw [← QuotientGroup.eq_one_iff g, ← ι.map_eq_one_iff (x := QuotientGroup.mk g), AlgEquiv.ext_iff]
  refine forall_congr' fun x => ?_
  rw [AlgEquiv.one_apply, ← (algebraMap F N).injective.eq_iff, hι]

end S_NumberField_IdeleClassGroup_nonempty_quotientToInvariants_iso_of_isScalarTower
end P2MW
export P2MW.S_NumberField_IdeleClassGroup_nonempty_quotientToInvariants_iso_of_isScalarTower (solution)
