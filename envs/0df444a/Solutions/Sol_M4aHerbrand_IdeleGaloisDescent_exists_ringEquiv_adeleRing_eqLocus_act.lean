-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.exists_ringEquiv_adeleRing_eqLocus_act
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5630941a-2051-5874-80f5-5d9c930cd93b

import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_ringEquiv_adeleRing_eqLocus_act

set_option autoImplicit false

noncomputable section

namespace R4H2T

open NumberField TensorProduct M4aHerbrand M4aHerbrand.Bridge M4aHerbrand.GenuineDescent

section FieldLevel

variable (K L E : Type) [Field K] [Field L] [Algebra K L] [Field E] [Algebra E L]
  (σ : L ≃ₐ[K] L) (hE : ∀ x : L, σ x = x ↔ x ∈ Set.range (algebraMap E L))

def σE : L ≃ₐ[E] L :=
  AlgEquiv.ofRingEquiv (f := (σ : L ≃+* L)) (fun a => (hE _).mpr ⟨a, rfl⟩)

theorem σE_apply (x : L) : σE K L E σ hE x = σ x := rfl

include hE in

theorem commutes_K (τ : L ≃ₐ[E] L) (k : K) : τ (algebraMap K L k) = algebraMap K L k := by
  obtain ⟨a, ha⟩ := (hE _).mp (σ.commutes k)
  rw [← ha]
  exact τ.commutes a

def φ : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L) where
  toFun τ := AlgEquiv.ofRingEquiv (f := (τ : L ≃+* L)) (fun k => commutes_K K L E σ hE τ k)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem φ_apply (τ : L ≃ₐ[E] L) (x : L) : φ K L E σ hE τ x = τ x := rfl

theorem φ_σE : φ K L E σ hE (σE K L E σ hE) = σ := by
  ext x; rfl

def σsub : L →ₗ[E] L := (σE K L E σ hE).toLinearMap - LinearMap.id

theorem σsub_apply (y : L) : σsub K L E σ hE y = σ y - y := rfl

include hE in
theorem exact_algebraMap_σsub : Function.Exact (Algebra.linearMap E L) (σsub K L E σ hE) := by
  intro y
  rw [σsub_apply, sub_eq_zero]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (hE y).mp h
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    exact (hE _).mpr ⟨a, rfl⟩

end FieldLevel

section Descent

variable (K L E : Type) [Field K] [Field L] [NumberField L] [Algebra K L] [Field E] [NumberField E] [Algebra E L]
  (σ : L ≃ₐ[K] L) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
  (hE : ∀ x : L, σ x = x ↔ x ∈ Set.range (algebraMap E L))

def DE : IdeleGaloisDescent (𝓞 L) E L where
  act := D.act.comp (φ K L E σ hE)
  compat τ x := by
    show D.act (φ K L E σ hE τ) (algebraMap L _ x) = _
    rw [D.compat]
    rfl
  continuous_act τ := D.continuous_act (φ K L E σ hE τ)

omit [NumberField E] in
theorem DE_act (τ : L ≃ₐ[E] L) : (DE K L E σ D hE).act τ = D.act (φ K L E σ hE τ) := rfl

theorem act_σ_eq :
    D.act σ = (genuineDescentDatum E L).act (σE K L E σ hE) := by
  have h : DE K L E σ D hE = genuineDescentDatum E L :=
    haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) E L
    Subsingleton.elim _ _
  rw [← h, DE_act, φ_σE]

end Descent

section Invariants

variable (K L E : Type) [Field K] [Field L] [Algebra K L] [Field E] [NumberField E] [Algebra E L]
  (σ : L ≃ₐ[K] L) (hE : ∀ x : L, σ x = x ↔ x ∈ Set.range (algebraMap E L))

def inl : AdeleRing (𝓞 E) E →+* (AdeleRing (𝓞 E) E) ⊗[E] L :=
  Algebra.TensorProduct.includeLeftRingHom

theorem inl_apply (x : AdeleRing (𝓞 E) E) : inl L E x = x ⊗ₜ[E] (1 : L) := rfl

theorem lTensor_σ_tmul (x : AdeleRing (𝓞 E) E) (l : L) :
    (LinearMap.lTensor (AdeleRing (𝓞 E) E) (σE K L E σ hE).toLinearMap) (x ⊗ₜ[E] l) = x ⊗ₜ[E] σ l := by
  rw [LinearMap.lTensor_tmul]
  rfl

theorem exists_eq_inl_of_lTensor_eq (z : (AdeleRing (𝓞 E) E) ⊗[E] L)
    (hz : (LinearMap.lTensor (AdeleRing (𝓞 E) E) (σE K L E σ hE).toLinearMap) z = z) :
    ∃ x : AdeleRing (𝓞 E) E, z = x ⊗ₜ[E] (1 : L) := by
  have hex := Module.Flat.lTensor_exact (AdeleRing (𝓞 E) E) (exact_algebraMap_σsub K L E σ hE)
  have hker : (LinearMap.lTensor (AdeleRing (𝓞 E) E) (σsub K L E σ hE)) z = 0 := by
    unfold σsub
    rw [LinearMap.lTensor_sub, LinearMap.sub_apply, hz, LinearMap.lTensor_id, LinearMap.id_apply, sub_self]
  obtain ⟨w, hw⟩ := (hex z).mp hker
  refine ⟨TensorProduct.rid E (AdeleRing (𝓞 E) E) w, ?_⟩
  have hw' : w = (TensorProduct.rid E (AdeleRing (𝓞 E) E) w) ⊗ₜ[E] (1 : E) := by
    have h := ((TensorProduct.rid E (AdeleRing (𝓞 E) E)).symm_apply_apply w).symm
    rwa [TensorProduct.rid_symm_apply] at h
  have h2 := congrArg (LinearMap.lTensor (AdeleRing (𝓞 E) E) (Algebra.linearMap E L)) hw'
  rw [← hw, h2, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]

theorem inl_injective : Function.Injective (inl L E) := by
  intro x x' h
  rw [inl_apply, inl_apply] at h
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := AdeleRing (𝓞 E) E)
    (Algebra.linearMap E L) (algebraMap E L).injective
  have h1 : ∀ y : AdeleRing (𝓞 E) E, y ⊗ₜ[E] (1 : L) =
      (LinearMap.lTensor (AdeleRing (𝓞 E) E) (Algebra.linearMap E L)) (y ⊗ₜ[E] (1 : E)) := by
    intro y
    rw [LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]
  rw [h1, h1] at h
  have h2 := hinj h
  have h3 := congrArg (TensorProduct.rid E (AdeleRing (𝓞 E) E)) h2
  simpa using h3

end Invariants

section Main

variable (K L E : Type) [Field K] [Field L] [NumberField L] [Algebra K L] [Field E] [NumberField E] [Algebra E L]
  (σ : L ≃ₐ[K] L) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
  (hE : ∀ x : L, σ x = x ↔ x ∈ Set.range (algebraMap E L))

include hE in

theorem main :
    ∃ e : (AdeleRing (𝓞 E) E ≃+*
        RingHom.eqLocus ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (RingHom.id (AdeleRing (𝓞 L) L))),
      ∀ a : E, (e (algebraMap E (AdeleRing (𝓞 E) E) a) : AdeleRing (𝓞 L) L) =
        algebraMap L (AdeleRing (𝓞 L) L) (algebraMap E L a) := by
  letI instAlg : Algebra (AdeleRing (𝓞 E) E) (AdeleRing (𝓞 L) L) := (genuineβ E L).toAlgebra
  set te := genuineTensorEquiv E L with hte_def
  set g : ((AdeleRing (𝓞 E) E) ⊗[E] L) ≃ₐ[AdeleRing (𝓞 E) E] ((AdeleRing (𝓞 E) E) ⊗[E] L) :=
    Algebra.TensorProduct.congr AlgEquiv.refl (σE K L E σ hE) with hg_def

  have hact : ∀ y : AdeleRing (𝓞 L) L, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) y = te (g (te.symm y)) := by
    intro y
    rw [act_σ_eq K L E σ D hE]
    rfl

  have hg : ∀ z : (AdeleRing (𝓞 E) E) ⊗[E] L,
      g z = (LinearMap.lTensor (AdeleRing (𝓞 E) E) (σE K L E σ hE).toLinearMap) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x l =>
        rw [lTensor_σ_tmul, hg_def, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
        rfl
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  have hg_inl : ∀ x : AdeleRing (𝓞 E) E, g (x ⊗ₜ[E] (1 : L)) = x ⊗ₜ[E] (1 : L) := by
    intro x
    rw [hg, lTensor_σ_tmul, map_one]

  have hte : ∀ x : AdeleRing (𝓞 E) E, te (x ⊗ₜ[E] (1 : L)) = genuineβ E L x := fun x =>
    genuineTensorEquiv_tmul_one E L x

  have hmem : ∀ x : AdeleRing (𝓞 E) E, genuineβ E L x ∈
      RingHom.eqLocus ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (RingHom.id (AdeleRing (𝓞 L) L)) := by
    intro x
    rw [RingHom.mem_eqLocus]
    show (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (genuineβ E L x) = genuineβ E L x
    rw [hact, ← hte, AlgEquiv.symm_apply_apply, hg_inl]
  let e₀ : AdeleRing (𝓞 E) E →+*
      RingHom.eqLocus ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (RingHom.id (AdeleRing (𝓞 L) L)) :=
    (genuineβ E L).codRestrict _ hmem
  have he₀ : ∀ x, ((e₀ x : _) : AdeleRing (𝓞 L) L) = genuineβ E L x := fun _ => rfl

  have hinj : Function.Injective e₀ := by
    intro x x' h
    have h' : genuineβ E L x = genuineβ E L x' := by
      rw [← he₀, ← he₀, h]
    rw [← hte, ← hte] at h'
    exact inl_injective L E (te.injective h')
  have hsurj : Function.Surjective e₀ := by
    rintro ⟨y, hy⟩
    rw [RingHom.mem_eqLocus] at hy
    change (D.act σ : RingAut (AdeleRing (𝓞 L) L)) y = y at hy
    rw [hact] at hy
    have hfix : g (te.symm y) = te.symm y := by
      apply te.injective
      rw [hy, AlgEquiv.apply_symm_apply]
    rw [hg] at hfix
    obtain ⟨x, hx⟩ := exists_eq_inl_of_lTensor_eq K L E σ hE (te.symm y) hfix
    refine ⟨x, Subtype.ext ?_⟩
    rw [he₀, ← hte, ← hx, AlgEquiv.apply_symm_apply]
  refine ⟨RingEquiv.ofBijective e₀ ⟨hinj, hsurj⟩, ?_⟩
  intro a
  show ((e₀ (algebraMap E (AdeleRing (𝓞 E) E) a) : _) : AdeleRing (𝓞 L) L) = _
  rw [he₀]
  exact genuineβ_compat E L a

end Main

end R4H2T

end

open NumberField in
theorem solution
    (K L E : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [Field E] [NumberField E] [Algebra E L]
    (σ : L ≃ₐ[K] L) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (hE : ∀ x : L, σ x = x ↔ x ∈ Set.range (algebraMap E L)) :
    ∃ e : (AdeleRing (𝓞 E) E ≃+*
        RingHom.eqLocus ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (RingHom.id (AdeleRing (𝓞 L) L))),
      ∀ a : E, (e (algebraMap E (AdeleRing (𝓞 E) E) a) : AdeleRing (𝓞 L) L) =
        algebraMap L (AdeleRing (𝓞 L) L) (algebraMap E L a) :=
  R4H2T.main K L E σ D hE

end S_M4aHerbrand_IdeleGaloisDescent_exists_ringEquiv_adeleRing_eqLocus_act
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_ringEquiv_adeleRing_eqLocus_act (solution)
