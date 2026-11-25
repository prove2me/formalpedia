-- Prove2me | solution 1 for GlobalTheory.isBaseChange_subtype_of_basis_after_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:41:09.892996+00:00
-- url     : https://prove2.me/submissions/51738943-91fc-4699-9729-3d5edc97c1c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsBaseChangeLatticeOfBasisAfterExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (S A EE O W RW D Y : Type) [CommRing S] [CommRing A] [CommRing EE] [CommRing O] [CommRing W] [CommRing RW] [Algebra O A] [Algebra A EE] [Algebra O EE] [IsScalarTower O A EE] [Algebra O RW] [AddCommGroup D] [Module EE D] [Module A D] [IsScalarTower A EE D] [AddCommGroup Y] [Module RW Y] (a : S →+* A) (ι : EE →ₐ[O] RW) (c : W →+* RW) (jD : D →+ Y), Function.Injective ι → (∀ e, IsUnit (ι e) → IsUnit e) → (∀ (e : EE) (x : D), jD (e • x) = ι e • jD x) → (∀ s, ι (algebraMap A EE (a s)) ∈ Set.range c) → ∀ (d r : ℕ) (o : Fin d → O), (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j) → Nonempty (Module.Basis (Fin r) EE D) → ∀ (q : ℕ) (x : Fin q → D), q = d * r → (∀ y : Y, ∃! w : Fin q → W, y = ∑ i, c (w i) • jD (x i)) → ∀ N : Submodule A D, (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → IsBaseChange EE N.subtype := by
  intro S A EE O W RW D Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a ι c jD hinj hunit hjD ha d r o ho
    ⟨b⟩ q x hq huniq N hN
  classical
  subst hq
  have hxN : ∀ i, x i ∈ N := by
    intro i
    refine (hN _).2 ⟨Pi.single i 1, ?_⟩
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  have hjsum : ∀ e : Fin (d * r) → EE, ∀ v : Fin (d * r) → D,
      jD (∑ i, e i • v i) = ∑ i, ι (e i) • jD (v i) := by
    intro e v
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hjD _ _

  have hspan : ∀ y : D, y ∈ Submodule.span EE (Set.range x) := by
    choose e' he' hdec using ho
    choose w' hw' using he'
    let u : Fin (d * r) → D := fun l =>
      algebraMap O EE (o (finProdFinEquiv.symm l).1) • b (finProdFinEquiv.symm l).2
    let C' : Matrix (Fin (d * r)) (Fin (d * r)) EE := fun i l =>
      e' (b.repr (x i) (finProdFinEquiv.symm l).2) (finProdFinEquiv.symm l).1
    let C : Matrix (Fin (d * r)) (Fin (d * r)) W := fun i l =>
      w' (b.repr (x i) (finProdFinEquiv.symm l).2) (finProdFinEquiv.symm l).1
    have hCC : ∀ i l, c (C i l) = ι (C' i l) := fun i l => hw' _ _
    have hx : ∀ i, x i = ∑ l, C' i l • u l := by
      intro i
      rw [← finProdFinEquiv.sum_comp]
      simp only [C', u, Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      conv_lhs => rw [← b.sum_repr (x i)]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [hdec (b.repr (x i) k)]
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, Algebra.smul_def, mul_comm]
    choose B hB using fun l => (huniq (jD (u l))).exists
    have hCB : C * Matrix.of B = 1 := by
      ext i m
      have h1 : jD (x i) = ∑ m, c ((C * Matrix.of B) i m) • jD (x m) := by
        conv_lhs => rw [hx i, hjsum]
        simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Matrix.of_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hB l, Finset.smul_sum, ← hCC]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_smul]
      have h2 : jD (x i) = ∑ m, c ((1 : Matrix _ _ W) i m) • jD (x m) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Matrix.one_apply_ne hj.symm]
        · simp
      exact congrFun ((huniq _).unique h1 h2) m
    have hdetC : IsUnit C.det := Matrix.isUnit_det_of_right_inverse hCB
    have hdetC' : IsUnit C'.det := by
      apply hunit
      have h1 : ι C'.det = c C.det := by
        rw [RingHom.map_det, AlgHom.map_det]
        congr 1
        ext i l
        simp [hCC]
      rw [h1]
      exact hdetC.map c
    have hu : ∀ l, u l ∈ Submodule.span EE (Set.range x) := by
      intro l
      have h1 : u l = ∑ i, C'⁻¹ l i • x i := by
        have h2 : ∑ i, C'⁻¹ l i • x i = ∑ m, (C'⁻¹ * C') l m • u m := by
          simp only [Matrix.mul_apply, Finset.sum_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hx i, Finset.smul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [smul_smul]
        rw [h2, Matrix.nonsing_inv_mul _ hdetC', Finset.sum_eq_single l]
        · simp
        · intro j _ hj
          simp [Matrix.one_apply_ne hj.symm]
        · simp
      rw [h1]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hb : ∀ k, b k ∈ Submodule.span EE (Set.range x) := by
      intro k
      have h1 : b k = ∑ j, e' 1 j • u (finProdFinEquiv (j, k)) := by
        conv_lhs => rw [← one_smul EE (b k), hdec 1, Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [u, Equiv.symm_apply_apply]
        rw [smul_smul, Algebra.smul_def, mul_comm]
      rw [h1]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hu _)
    intro y
    rw [← b.sum_repr y]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hb k)

  have hnf : ∀ t : EE ⊗[A] N, ∃ e : Fin (d * r) → EE, (∀ i, ι (e i) ∈ c.range) ∧
      t = ∑ i, e i ⊗ₜ[A] (⟨x i, hxN i⟩ : N) := by
    let P : AddSubmonoid (EE ⊗[A] N) :=
      { carrier := {t | ∃ e : Fin (d * r) → EE, (∀ i, ι (e i) ∈ c.range) ∧
          t = ∑ i, e i ⊗ₜ[A] (⟨x i, hxN i⟩ : N)}
        zero_mem' := ⟨0, fun i => by simp, by simp⟩
        add_mem' := by
          rintro _ _ ⟨e₁, h₁, rfl⟩ ⟨e₂, h₂, rfl⟩
          refine ⟨e₁ + e₂, fun i => ?_, ?_⟩
          · rw [Pi.add_apply, map_add]
            exact add_mem (h₁ i) (h₂ i)
          · simp [TensorProduct.add_tmul, Finset.sum_add_distrib] }
    have hP : ∀ (e : EE) (n : N), ι e ∈ c.range → e ⊗ₜ[A] n ∈ P := by
      intro e n he
      obtain ⟨s, hs⟩ := (hN n).1 n.2
      have hn : n = ∑ i, a (s i) • (⟨x i, hxN i⟩ : N) := by
        apply Subtype.ext
        rw [hs]
        simp
      refine ⟨fun i => a (s i) • e, fun i => ?_, ?_⟩
      · beta_reduce
        rw [Algebra.smul_def, map_mul]
        exact mul_mem (ha (s i)) he
      · rw [hn, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.smul_tmul]
    intro t
    change t ∈ P
    induction t using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add _ _ h₁ h₂ => exact add_mem h₁ h₂
    | tmul e n =>
      obtain ⟨e', he', hdec⟩ := ho e
      rw [hdec, TensorProduct.sum_tmul]
      refine sum_mem fun j _ => ?_
      rw [← algebraMap_smul A (o j) (e' j), TensorProduct.smul_tmul]
      exact hP _ _ (he' j)
  have hbij : Function.Bijective (N.subtype.liftBaseChange EE) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro t ht
      obtain ⟨e, he, rfl⟩ := hnf t
      choose w hw using he
      have h1 : ∑ i, e i • x i = 0 := by
        simpa [map_sum, LinearMap.liftBaseChange_tmul] using ht
      have h2 : (0 : Y) = ∑ i, c (w i) • jD (x i) := by
        simp only [hw]
        rw [← hjsum, h1, map_zero]
      have h3 : (0 : Y) = ∑ i, c ((0 : Fin (d * r) → W) i) • jD (x i) := by simp
      have h4 : w = 0 := (huniq 0).unique h2 h3
      have h5 : ∀ i, e i = 0 := by
        intro i
        apply hinj
        rw [← hw, h4]
        simp
      simp [h5]
    · rw [← LinearMap.range_eq_top, eq_top_iff]
      intro y _
      refine Submodule.span_le.2 ?_ (hspan y)
      rintro _ ⟨i, rfl⟩
      exact ⟨1 ⊗ₜ[A] (⟨x i, hxN i⟩ : N), by simp [LinearMap.liftBaseChange_tmul]⟩
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbij) fun n => ?_
  simp [LinearMap.liftBaseChange_tmul]
end GlobalTheory
