-- Prove2me | solution 1 for Module.forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/18fcf0f6-861e-554d-a13d-5f9cb4e9fb15

import Mathlib
import Theorems.Thm_Module_forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field

set_option autoImplicit false

universe u

open TensorProduct

namespace FibreAcyclic

theorem transfer {X Y : ℕ → Type u} [∀ i, AddCommGroup (X i)] [∀ i, AddCommGroup (Y i)]
    (dX : ∀ i, X i →+ X (i + 1)) (dY : ∀ i, Y i →+ Y (i + 1)) (e : ∀ i, X i ≃+ Y i)
    (comm : ∀ i (x : X i), e (i + 1) (dX i x) = dY i (e i x))
    (hY0 : ∀ z : Y 0, dY 0 z = 0 → z = 0)
    (hYS : ∀ (i : ℕ) (z : Y (i + 1)), dY (i + 1) z = 0 → ∃ w : Y i, dY i w = z) :
    (∀ z : X 0, dX 0 z = 0 → z = 0) ∧
      ∀ (i : ℕ) (z : X (i + 1)), dX (i + 1) z = 0 → ∃ w : X i, dX i w = z := by
  refine ⟨fun z hz => ?_, fun i z hz => ?_⟩
  · have h : dY 0 (e 0 z) = 0 := by rw [← comm, hz, map_zero]
    have := hY0 _ h
    exact (e 0).injective (by rw [this, map_zero])
  · have h : dY (i + 1) (e (i + 1) z) = 0 := by rw [← comm, hz, map_zero]
    obtain ⟨w', hw'⟩ := hYS i _ h
    refine ⟨(e i).symm w', (e (i + 1)).injective ?_⟩
    rw [comm, AddEquiv.apply_symm_apply, hw']

variable {S : Type u} [CommRing S]

theorem subsingleton_tensor (A : Type u) [CommRing A] [Algebra S A] (M : Type u) [AddCommGroup M] [Module S M]
    [Subsingleton M] : Subsingleton (A ⊗[S] M) := by
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : A ⊗[S] M, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul a m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [hx x, hx y]

end FibreAcyclic

open FibreAcyclic in
theorem solution
    (S : Type u) [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] (n : ℕ)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module S (K i)]
    [∀ i, Module.Finite S (K i)] [∀ i, Module.Projective S (K i)]
    (hbdd : ∀ i, n < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[S] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (B : Type u) [Field B] [Algebra S B] (hB : Function.Surjective (algebraMap S B))
    (h𝔪 : 𝔪 ≤ RingHom.ker (algebraMap S B))
    (h0 : ∀ z : B ⊗[S] K 0, (δ 0).baseChange B z = 0 → z = 0)
    (hS : ∀ (i : ℕ) (z : B ⊗[S] K (i + 1)), (δ (i + 1)).baseChange B z = 0 →
      z ∈ LinearMap.range ((δ i).baseChange B)) :
    (∀ z : Localization.AtPrime 𝔪 ⊗[S] K 0, (δ 0).baseChange (Localization.AtPrime 𝔪) z = 0 → z = 0) ∧
      ∀ (i : ℕ) (z : Localization.AtPrime 𝔪 ⊗[S] K (i + 1)),
        (δ (i + 1)).baseChange (Localization.AtPrime 𝔪) z = 0 →
          z ∈ LinearMap.range ((δ i).baseChange (Localization.AtPrime 𝔪)) := by
  classical
  set R := Localization.AtPrime 𝔪 with hR
  letI κ := R ⧸ IsLocalRing.maximalIdeal R

  haveI : Nontrivial B := inferInstance
  have hkerB : RingHom.ker (algebraMap S B) = 𝔪 :=
    (Ideal.IsMaximal.eq_of_le inferInstance (RingHom.ker_ne_top _) h𝔪).symm
  have hκsurj : Function.Surjective (algebraMap S κ) := Ideal.algebraMap_residueField_surjective 𝔪
  have hkerκ : RingHom.ker (algebraMap S κ) = 𝔪 := by
    refine (Ideal.IsMaximal.eq_of_le inferInstance (RingHom.ker_ne_top _) fun s hs => ?_).symm
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply S R κ, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R 𝔪 s).mpr hs
  let qB : (S ⧸ RingHom.ker (algebraMap S B)) ≃ₐ[S] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId S B) hB
  let qκ : (S ⧸ RingHom.ker (algebraMap S κ)) ≃ₐ[S] κ :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId S κ) hκsurj
  let eκB : κ ≃ₗ[S] B :=
    (qκ.symm.trans ((Ideal.quotientEquivAlgOfEq S (hkerκ.trans hkerB.symm)).trans qB)).toLinearEquiv

  haveI hfinR : ∀ i, Module.Finite R (R ⊗[S] K i) := fun i => inferInstance
  haveI hfreeR : ∀ i, Module.Free R (R ⊗[S] K i) := fun i => Module.free_of_flat_of_isLocalRing
  have hbddR : ∀ i, n < i → Subsingleton (R ⊗[S] K i) := fun i hi => by
    haveI := hbdd i hi; exact subsingleton_tensor R (K i)
  have hddR : ∀ i, (δ (i + 1)).baseChange R ∘ₗ (δ i).baseChange R = 0 := fun i => by
    rw [← LinearMap.baseChange_comp, hdd, LinearMap.baseChange_zero]

  let e : ∀ i, κ ⊗[R] (R ⊗[S] K i) ≃+ B ⊗[S] K i := fun i =>
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange S R κ κ (K i)).toAddEquiv).trans
      (TensorProduct.congr eκB (LinearEquiv.refl S (K i))).toAddEquiv
  have comm : ∀ i (x : κ ⊗[R] (R ⊗[S] K i)),
      e (i + 1) ((((δ i).baseChange R).baseChange κ) x) = (δ i).baseChange B (e i x) := by
    intro i x
    induction x using TensorProduct.induction_on with
    | zero => rw [LinearMap.map_zero, AddEquiv.map_zero, AddEquiv.map_zero, LinearMap.map_zero]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero, LinearMap.map_zero, AddEquiv.map_zero, AddEquiv.map_zero, LinearMap.map_zero]
      | tmul r k =>
        simp [e, LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      | add a b ha hb =>
        rw [TensorProduct.tmul_add, LinearMap.map_add, AddEquiv.map_add, ha, hb, AddEquiv.map_add,
          LinearMap.map_add]
    | add a b ha hb =>
      rw [LinearMap.map_add, AddEquiv.map_add, ha, hb, AddEquiv.map_add, LinearMap.map_add]
  obtain ⟨h0κ, hSκ⟩ := transfer
    (fun i => (((δ i).baseChange R).baseChange κ).toAddMonoidHom)
    (fun i => ((δ i).baseChange B).toAddMonoidHom) e comm h0
    (fun i z hz => by obtain ⟨w, hw⟩ := hS i z hz; exact ⟨w, hw⟩)

  have hnak := Module.forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free
    R n (fun i => R ⊗[S] K i) hbddR (fun i => (δ i).baseChange R) hddR
    (fun z hz => h0κ z hz)
    (fun i z hz => by obtain ⟨w, hw⟩ := hSκ i z hz; exact ⟨w, hw⟩)
  exact ⟨hnak.1, fun i z hz => hnak.2 i z hz⟩

end S_Module_forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field
end P2MW
export P2MW.S_Module_forall_baseChange_localization_eq_zero_and_mem_range_of_forall_baseChange_field (solution)
