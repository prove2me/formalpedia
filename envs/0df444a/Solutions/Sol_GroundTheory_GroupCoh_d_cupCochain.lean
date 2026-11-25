-- Prove2me | solution 1 for GroundTheory.GroupCoh.d_cupCochain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:17:28.362671+00:00
-- url     : https://prove2.me/submissions/47f96a54-4565-45d3-8ae6-1838b917d07d

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
import Theorems.Thm_GroundTheory_GroupCoh_partialProd_contractNth_of_lt
import Theorems.Thm_GroundTheory_GroupCoh_partialProd_contractNth_of_le
import Theorems.Thm_GroundTheory_GroupCoh_contractNth_prefix
import Theorems.Thm_GroundTheory_GroupCoh_contractNth_prefix_of_le
import Theorems.Thm_GroundTheory_GroupCoh_contractNth_suffix_of_lt
import Theorems.Thm_GroundTheory_GroupCoh_contractNth_suffix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (h : p + q = n) (f : (Fin p → G) → A) (g : (Fin q → G) → B) :
    (inhomogeneousCochains.d (A ⊗ B) n).hom (cupCochain h f g) =
      cupCochain (by omega) ((inhomogeneousCochains.d A p).hom f) g +
        (-1 : k) ^ p • cupCochain (by omega) f ((inhomogeneousCochains.d B q).hom g) := by
  subst h
  funext x
  simp only [inhomogeneousCochains.d_hom_apply, cupCochain_apply, Pi.add_apply, Pi.smul_apply]
  have hs : ∀ {M : Type u} [AddCommMonoid M] (F : Fin (p + q + 1) → M),
      ∑ j, F j = ∑ i : Fin p, F (Fin.castAdd (q + 1) i) + ∑ m : Fin (q + 1), F (Fin.natAdd p m) :=
    fun F => Fin.sum_univ_add (a := p) (b := q + 1) F
  rw [hs, Fin.sum_univ_castSucc (n := p)]
  have e0 : ((A ⊗ B).ρ (x 0))
      ((f fun i : Fin p => x (⟨i, by omega⟩ : Fin (p + q)).succ) ⊗ₜ[k]
        B.ρ (Fin.partialProd (fun i : Fin (p + q) => x i.succ) ⟨p, by omega⟩)
          (g fun j : Fin q => x (⟨p + j, by omega⟩ : Fin (p + q)).succ)) =
      A.ρ (x 0) (f fun i : Fin p => x (⟨i, by omega⟩ : Fin (p + q)).succ) ⊗ₜ[k]
        B.ρ (Fin.partialProd x ⟨p + 1, by omega⟩) (g fun j : Fin q => x ⟨p + 1 + j, by omega⟩) := by
    rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul, ← Module.End.mul_apply,
      ← map_mul]
    have hP : x 0 * Fin.partialProd (fun i : Fin (p + q) => x i.succ) ⟨p, by omega⟩ =
        Fin.partialProd x ⟨p + 1, by omega⟩ := by
      have := Fin.partialProd_succ' x ⟨p, by omega⟩
      simp only [Fin.succ_mk] at this
      rw [this]
      rfl
    have hg : (fun j : Fin q => x (⟨p + j, by omega⟩ : Fin (p + q)).succ) =
        fun j : Fin q => x ⟨p + 1 + j, by omega⟩ := by
      funext j
      congr 1
      ext
      simp only [Fin.val_succ]
      omega
    rw [hP, hg]
  have e1 : ∀ i : Fin p, (-1 : k) ^ ((Fin.castAdd (q + 1) i : Fin (p + q + 1)) + 1 : ℕ) •
      ((f fun l : Fin p =>
          Fin.contractNth (n := p + q) (Fin.castAdd (q + 1) i) (· * ·) x ⟨l, by omega⟩) ⊗ₜ[k]
        B.ρ (Fin.partialProd
            (Fin.contractNth (n := p + q) (Fin.castAdd (q + 1) i) (· * ·) x) ⟨p, by omega⟩)
          (g fun j : Fin q =>
            Fin.contractNth (n := p + q) (Fin.castAdd (q + 1) i) (· * ·) x ⟨p + j, by omega⟩)) =
      ((-1 : k) ^ ((Fin.castSucc i : ℕ) + 1) •
          f (Fin.contractNth (Fin.castSucc i) (· * ·) fun l : Fin (p + 1) => x ⟨l, by omega⟩)) ⊗ₜ[k]
        B.ρ (Fin.partialProd x ⟨p + 1, by omega⟩) (g fun j : Fin q => x ⟨p + 1 + j, by omega⟩) := by
    intro i
    rw [contractNth_prefix _ x _ (Fin.castSucc i) (by omega) (by simp),
      partialProd_contractNth_of_lt _ _ (by omega) (by simp),
      contractNth_suffix_of_lt _ x _ (by omega) (by simp), TensorProduct.smul_tmul']
    simp
  have e2 : ∀ m : Fin (q + 1), (-1 : k) ^ ((Fin.natAdd p m : Fin (p + q + 1)) + 1 : ℕ) •
      ((f fun l : Fin p =>
          Fin.contractNth (n := p + q) (Fin.natAdd p m) (· * ·) x ⟨l, by omega⟩) ⊗ₜ[k]
        B.ρ (Fin.partialProd
            (Fin.contractNth (n := p + q) (Fin.natAdd p m) (· * ·) x) ⟨p, by omega⟩)
          (g fun j : Fin q =>
            Fin.contractNth (n := p + q) (Fin.natAdd p m) (· * ·) x ⟨p + j, by omega⟩)) =
      (-1 : k) ^ p • ((f fun l : Fin p => x ⟨l, by omega⟩) ⊗ₜ[k]
        B.ρ (Fin.partialProd x ⟨p, by omega⟩) ((-1 : k) ^ ((m : ℕ) + 1) •
          g (Fin.contractNth m (· * ·) fun j : Fin (q + 1) => x ⟨p + j, by omega⟩))) := by
    intro m
    rw [contractNth_prefix_of_le _ x _ (by simp), partialProd_contractNth_of_le _ _ (by omega) (by simp),
      contractNth_suffix _ x _ m rfl (by simp), map_smul, TensorProduct.tmul_smul, smul_smul,
      ← pow_add]
    congr 2
  rw [e0, Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_congr rfl fun m _ => e2 m]
  have hlast : (Fin.contractNth (Fin.last p) (· * ·) fun l : Fin (p + 1) => x ⟨l, by omega⟩) =
      fun l : Fin p => x ⟨l, by omega⟩ := by
    funext l
    rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]
    rfl
  have hT : A.ρ (x ⟨((0 : Fin (p + 1)) : ℕ), by omega⟩)
      (f fun i : Fin p => x ⟨(i.succ : ℕ), by omega⟩) =
      A.ρ (x 0) (f fun i : Fin p => x (⟨i, by omega⟩ : Fin (p + q)).succ) := rfl
  have hG : (fun i : Fin q => x ⟨p + (i.succ : ℕ), by omega⟩) =
      fun j : Fin q => x ⟨p + 1 + j, by omega⟩ := by
    funext j
    congr 1
    ext
    simp only [Fin.val_succ]
    omega
  have hP : B.ρ (Fin.partialProd x ⟨p, by omega⟩) (B.ρ (x ⟨p + ((0 : Fin (q + 1)) : ℕ), by omega⟩)
      (g fun j : Fin q => x ⟨p + 1 + j, by omega⟩)) =
      B.ρ (Fin.partialProd x ⟨p + 1, by omega⟩) (g fun j : Fin q => x ⟨p + 1 + j, by omega⟩) := by
    rw [← Module.End.mul_apply, ← map_mul]
    congr 2
    have := Fin.partialProd_succ x ⟨p, by omega⟩
    simp only [Fin.succ_mk, Fin.castSucc_mk] at this
    rw [this]
    rfl
  rw [hlast, hT, hG, map_add, TensorProduct.tmul_add, smul_add, hP, TensorProduct.add_tmul,
    TensorProduct.add_tmul, ← TensorProduct.smul_tmul', TensorProduct.sum_tmul, map_sum,
    TensorProduct.tmul_sum, Finset.smul_sum, Fin.val_last, pow_succ, mul_neg_one, neg_smul]
  abel
end GroundTheory.GroupCoh
