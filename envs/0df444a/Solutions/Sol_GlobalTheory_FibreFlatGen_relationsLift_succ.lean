-- Prove2me | solution 1 for GlobalTheory.FibreFlatGen.relationsLift_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:22.67708+00:00
-- url     : https://prove2.me/submissions/beec00ec-1c63-4e11-97fe-960b3b550de7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatOfIsFiniteOfFlatGeometricFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RTensorInjectiveOfFlatBaseChange
import Theorems.Thm_GlobalTheory_FiniteFibreFlat_lTensor_map_injective
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_LocalFlat_range_lTensor_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory GlobalTheory.FibreFlatGen
open LocalFlat
universe u
namespace GlobalTheory.FibreFlatGen
theorem _root_.solution {R : Type*} {A : Type u} {M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Flat R M] (J : Ideal R) (k : ℕ)
    (hinj : ∀ (N' N : Type u) [AddCommGroup N'] [AddCommGroup N]
      [Module (A ⧸ J.map (algebraMap R A)) N'] [Module (A ⧸ J.map (algebraMap R A)) N]
      [Module A N'] [Module A N] [IsScalarTower A (A ⧸ J.map (algebraMap R A)) N']
      [IsScalarTower A (A ⧸ J.map (algebraMap R A)) N]
      (ι : N' →ₗ[A ⧸ J.map (algebraMap R A)] N), Function.Injective ι →
        Function.Injective ((ι.restrictScalars A).lTensor M))
    (h : RelationsLift (J.map (algebraMap R A) ^ k) M) :
    RelationsLift (J.map (algebraMap R A) ^ (k + 1)) M := by
  set I := J.map (algebraMap R A) with hI
  let C := A ⧸ I
  have hC : Function.Surjective (algebraMap A C) := Ideal.Quotient.mk_surjective
  intro F _ _ f x hx
  let P : Ideal A := I ^ k
  let G : Submodule A F := Submodule.comap f P
  obtain ⟨x₁, rfl⟩ := h F f x
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ k)) hx)
  let f' : G →ₗ[A] P := (f.domRestrict G).codRestrict P fun g => g.2
  have hPeq : P = (J ^ k).map (algebraMap R A) := by rw [Ideal.map_pow]
  have hT : Function.Injective ((TensorProduct.rid A M).toLinearMap ∘ₗ P.subtype.lTensor M) := by
    rw [hPeq]
    exact (TensorProduct.rid A M).injective.comp (FiniteFibreFlat.lTensor_map_injective (J ^ k))
  have hsub : P.subtype ∘ₗ f' = f ∘ₗ G.subtype := rfl
  have hle : I ^ (k + 1) ≤ P := Ideal.pow_le_pow_right (Nat.le_succ k)
  let incl : ↥(I ^ (k + 1)) →ₗ[A] P := Submodule.inclusion hle
  have hsurj : ∀ v ∈ (I ^ (k + 1) • ⊤ : Submodule A M), ∃ z : M ⊗[A] ↥(I ^ (k + 1)),
      TensorProduct.rid A M ((I ^ (k + 1)).subtype.lTensor M z) = v := by
    intro v hv
    refine Submodule.smul_induction_on hv (fun r hr n _ => ?_) ?_
    · exact ⟨n ⊗ₜ ⟨r, hr⟩, by simp⟩
    · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, by simp only [map_add]⟩
  obtain ⟨z, hz⟩ := hsurj _ hx
  have hy : f'.lTensor M x₁ = incl.lTensor M z := by
    apply hT
    simp only [comp_apply, LinearEquiv.coe_coe, ← lTensor_comp_apply]
    have he : P.subtype ∘ₗ incl = (I ^ (k + 1)).subtype := rfl
    rw [hsub, he, hz, lTensor_comp_apply]
  let Q := C ⊗[A] P
  let p : P →ₗ[A] Q := TensorProduct.mk A C P 1
  have hker : ∀ t : P, p t = 0 ↔ (t : A) ∈ I ^ (k + 1) := by
    intro t
    have h1 : ker p = I • (⊤ : Submodule A P) := LinearMap.ker_tensorProductMk P
    rw [← mem_ker, h1, Submodule.mem_smul_top_iff, pow_succ', smul_eq_mul]
  let g : G →ₗ[A] Q := p ∘ₗ f'
  let Pc : Submodule C Q :=
    { carrier := Set.range g
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, map_add _ _ _⟩
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        obtain ⟨c, rfl⟩ := hC c
        exact ⟨c • a, by rw [map_smul, algebraMap_smul]⟩ }
  let g' : G →ₗ[A] Pc := g.codRestrict (Pc.restrictScalars A) fun a => ⟨a, rfl⟩
  have hg' : Function.Surjective g' := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  have hι := hinj Pc Q Pc.subtype Subtype.val_injective
  have h0 : g'.lTensor M x₁ = 0 := by
    apply hι
    rw [map_zero, ← lTensor_comp_apply]
    have e1 : (Pc.subtype.restrictScalars A) ∘ₗ g' = p ∘ₗ f' := rfl
    rw [e1, lTensor_comp_apply, hy, ← lTensor_comp_apply]
    have e2 : p ∘ₗ incl = 0 := by
      ext t
      exact (hker _).2 t.2
    rw [e2]
    simp
  have hex := lTensor_exact M (LinearMap.exact_subtype_ker_map g') hg'
  obtain ⟨w, rfl⟩ := (hex x₁).1 h0
  rw [← lTensor_comp_apply]
  refine range_lTensor_le (M := M) (G.subtype ∘ₗ (ker g').subtype) _ (fun u => ?_) ⟨w, rfl⟩
  have hu : g' u.1 = 0 := u.2
  have hu' : p (f' u.1) = 0 := congrArg Subtype.val hu
  exact (hker _).1 hu'
end GlobalTheory.FibreFlatGen
