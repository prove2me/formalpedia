-- Prove2me | solution 1 for GlobalTheory.quot_tensor_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:30:33.820186+00:00
-- url     : https://prove2.me/submissions/154541d2-8046-4554-b728-2ec0ab247ce7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TensorQuotientOntoAndInjectiveModIdealPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open TensorProduct
set_option maxHeartbeats 1000000
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C')), (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (I ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ (C : Subalgebra R C') (gm : ∀ e : ℕ, (O ⧸ (I ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (I ^ (e + 1)).map (algebraMap R C))), (∀ e (x : O) (c : C), gm e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x) → (∀ y : C', ∃ t : TensorProduct R C R', y - Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ (I.map (algebraMap R C)).map (algebraMap C C')) ∧ ∀ (n : ℕ) (t : TensorProduct R C R'), Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C C') → t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C (TensorProduct R C R')) := by
  intro R _ I R' _ _ C' _ _ _ _ O _ _ i hi C gm hcomp

  have hJ : ∀ k : ℕ, ((I.map (algebraMap R C)) ^ k).map (algebraMap C C') =
      (I ^ k).map (algebraMap R C') := by
    intro k
    rw [← Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  set φ := Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C')
    (fun _ _ => Commute.all _ _) with hφ
  have hφt : ∀ (c : C) (r : R'), φ (c ⊗ₜ r) = (c : C') * algebraMap R' C' r := by
    intro c r
    simp [φ, Algebra.TensorProduct.lift_tmul]
  refine ⟨?_, ?_⟩
  · intro y
    have key : ∀ s : O ⊗[R] R', ∃ t : C ⊗[R] R',
        Algebra.TensorProduct.lift (i 0) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C'))
          (fun _ _ => Commute.all _ _) s = Ideal.Quotient.mk _ (φ t) := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul x r =>
        obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (gm 0 (Ideal.Quotient.mk _ x))
        refine ⟨c ⊗ₜ r, ?_⟩
        rw [Algebra.TensorProduct.lift_tmul, hφt, ← hcomp 0 x c hc.symm]
        simp [map_mul]
      | add a b ha hb =>
        obtain ⟨ta, hta⟩ := ha
        obtain ⟨tb, htb⟩ := hb
        exact ⟨ta + tb, by rw [map_add, hta, htb, map_add, map_add]⟩
    obtain ⟨s, hs⟩ := (hi 0).1 (Ideal.Quotient.mk _ y)
    obtain ⟨t, ht⟩ := key s
    refine ⟨t, ?_⟩
    have h1 := (Ideal.Quotient.eq).1 (hs.symm.trans ht)
    have h2 := hJ 1
    rw [pow_one] at h2
    rw [h2]
    simpa using h1
  · intro n t ht
    cases n with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
      exact Submodule.mem_top
    | succ e =>
    rw [← Ideal.map_pow] at ht ⊢
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at ht
    set K := (I ^ (e + 1)).map (algebraMap R C) with hK
    set πC : C ⊗[R] R' →ₐ[R] (C ⧸ K) ⊗[R] R' :=
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R K) (AlgHom.id R R') with hπC
    have hker : RingHom.ker πC = K.map (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') := by
      rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective R K)]
      congr 1
      ext a
      simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    have hinc : K.map (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') =
        K.map (algebraMap C (C ⊗[R] R')) := by
      have : ((Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] R') : C →+* C ⊗[R] R') =
          algebraMap C (C ⊗[R] R') := by
        ext c
        simp [Algebra.TensorProduct.algebraMap_apply]
      rw [← this]
      rfl
    have hvan : ∀ a ∈ K, ((Ideal.Quotient.mkₐ R ((I ^ (e + 1)).map (algebraMap R C'))).comp C.val) a = 0 := by
      intro a ha
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      have : (a : C') ∈ K.map (algebraMap C C') := Ideal.mem_map_of_mem _ ha
      rwa [hK, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at this
    set Λ : (C ⧸ K) ⊗[R] R' →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C') :=
      Algebra.TensorProduct.lift (Ideal.Quotient.liftₐ K _ hvan)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _) with hΛ
    have hL : ∀ c : C, Ideal.Quotient.liftₐ K _ hvan (Ideal.Quotient.mk K c) =
        Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C') := fun c => rfl
    set G : O ⊗[R] R' →ₐ[R] (C ⧸ K) ⊗[R] R' :=
      Algebra.TensorProduct.map ((gm e).toAlgHom.comp (Ideal.Quotient.mkₐ R _)) (AlgHom.id R R') with hG
    have hGs : Function.Surjective G :=
      Algebra.TensorProduct.map_surjective _ _
        ((gm e).surjective.comp (Ideal.Quotient.mkₐ_surjective R _)) Function.surjective_id
    have hΛG : ∀ s, Λ (G s) = Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _) s := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul x r =>
        obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (gm e (Ideal.Quotient.mk _ x))
        have hc' := hcomp e x c hc.symm
        simp only [G, Λ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
        show Ideal.Quotient.liftₐ K _ hvan (gm e (Ideal.Quotient.mk _ x)) * _ = _
        rw [← hc, ← hc']
        congr 1
      | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
    have hΛπ' : Λ.comp πC = (Ideal.Quotient.mkₐ R _).comp (φ.restrictScalars R) := by
      refine Algebra.TensorProduct.ext' fun c r => ?_
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, πC, Λ, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.lift_tmul, hφt]
      rw [map_mul]
      congr 1
    have hΛπ : ∀ u, Λ (πC u) = Ideal.Quotient.mk _ (φ u) := fun u => by
      have := congrArg (fun f => f u) hΛπ'
      simpa using this
    obtain ⟨s, hs⟩ := hGs (πC t)
    have hs0 : s ∈ RingHom.ker (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _)) := by
      rw [RingHom.mem_ker, ← hΛG, hs, hΛπ, Ideal.Quotient.eq_zero_iff_mem]
      exact ht
    rw [(hi e).2] at hs0
    have hGz : G s = 0 := by
      have hle : (I ^ (e + 1)).map (algebraMap R (O ⊗[R] R')) ≤ RingHom.ker G.toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
          IsScalarTower.algebraMap_apply R (C ⧸ K) ((C ⧸ K) ⊗[R] R'), ← Ideal.Quotient.mk_algebraMap,
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha), map_zero]
      exact hle hs0
    rw [← hinc, ← hker, RingHom.mem_ker, ← hs, hGz]
end GlobalTheory
