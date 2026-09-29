-- Prove2me | solution 1 for Module.FaithfullyFlat.exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3d021a70-9b2f-5873-b3ec-936453c994cd

import Mathlib
import Theorems.Thm_Algebra_FormallyUnramified_nonempty_ringHom_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_FaithfullyFlat_exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace Module
p2m_export "Module" "Flat equiv Finite.equiv Finite.of_finite_tensorProduct_of_faithfullyFlat Flat.of_flat_tensorProduct FaithfullyFlat Flat.of_linearEquiv"
namespace FaithfullyFlat
p2m_export "Module.FaithfullyFlat" "trans of_linearEquiv"
p2m_open "Module.FaithfullyFlat Module"

section transl
variable {S : Type*} [CommRing S] {G : Type*} [AddCommGroup G] [Fintype G]

private def transl (u : G → S) : (G → S) →ₗ[S] (G → S) where
  toFun F k := ∑ m, u m * F (k - m)
  map_add' F F' := by ext k; simp [mul_add, Finset.sum_add_distrib]
  map_smul' s F := by ext k; simp [Finset.mul_sum, mul_left_comm]

private theorem transl_apply (u F : G → S) (k : G) : transl u F k = ∑ m, u m * F (k - m) := rfl

private theorem transl_single_zero [DecidableEq G] (u : G → S) (k : G) :
    transl u (Pi.single 0 1) k = u k := by
  rw [transl_apply, Finset.sum_eq_single k]
  · rw [sub_self, Pi.single_eq_same, mul_one]
  · intro m _ hmk
    rw [Pi.single_eq_of_ne (sub_ne_zero.mpr (Ne.symm hmk)), mul_zero]
  · simp

private theorem sum_mul_mul_sum_mul {ι : Type*} [Fintype ι] (u : ι → S) (hu : OrthogonalIdempotents u)
    (F F' : ι → S) : (∑ m, u m * F m) * (∑ m, u m * F' m) = ∑ m, u m * (F m * F' m) := by
  classical
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single m]
  · rw [mul_mul_mul_comm, (hu.idem m).eq]
  · intro m' _ hm'
    rw [mul_mul_mul_comm, hu.ortho (Ne.symm hm'), zero_mul]
  · simp

end transl

section main

variable {A : Type u} [CommRing A] {G : Type v} [AddCommGroup G] [Fintype G]

private theorem exists_subalgebra_mem_iff (e : G → A ⊗[ℤ] A) (he : CompleteOrthogonalIdempotents e)
    (M : Submodule ℤ (G → A))
    (hM : ∀ f : G → A, f ∈ M ↔ ∀ k, ∑ m, e m * (f (k - m) ⊗ₜ[ℤ] 1) = 1 ⊗ₜ[ℤ] f k) :
    ∃ S : Subalgebra ℤ (G → A), ∀ f : G → A, f ∈ S ↔ f ∈ M := by
  have one_mem : (1 : G → A) ∈ M := by
    rw [hM]; intro k
    simp only [Pi.one_apply, ← Finset.sum_mul, he.complete, one_mul]
  have mul_mem : ∀ f g : G → A, f ∈ M → g ∈ M → f * g ∈ M := by
    intro f g hf hg
    rw [hM] at hf hg ⊢
    intro k
    rw [Pi.mul_apply, show (1 : A) ⊗ₜ[ℤ] (f k * g k) = (1 ⊗ₜ[ℤ] f k) * (1 ⊗ₜ[ℤ] g k) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], ← hf k, ← hg k,
      sum_mul_mul_sum_mul e he.toOrthogonalIdempotents]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Pi.mul_apply]
  exact ⟨{ carrier := M
           mul_mem' := fun {a b} ha hb => mul_mem a b ha hb
           one_mem' := one_mem
           add_mem' := fun {a b} ha hb => M.add_mem ha hb
           zero_mem' := M.zero_mem
           algebraMap_mem' := fun n => by
             rw [Algebra.algebraMap_eq_smul_one]
             exact M.smul_mem n one_mem }, fun _ => Iff.rfl⟩

private theorem span_eq_top (S : Subalgebra ℤ (G → A)) (hbcS : IsBaseChange A S.val.toLinearMap) :
    Submodule.span (A ⊗[ℤ] A) (Set.range fun s : S => fun k => (s : G → A) k ⊗ₜ[ℤ] (1 : A)) = ⊤ := by
  classical
  set W := Submodule.span (A ⊗[ℤ] A) (Set.range fun s : S => fun k => (s : G → A) k ⊗ₜ[ℤ] (1 : A))
    with hW

  have h1 : ∀ g : G → A, (fun k => g k ⊗ₜ[ℤ] (1 : A)) ∈ W := by
    intro g
    obtain ⟨t, rfl⟩ := hbcS.equiv.surjective g
    induction t using TensorProduct.induction_on with
    | zero =>
      have : (fun k => (hbcS.equiv (0 : A ⊗[ℤ] S)) k ⊗ₜ[ℤ] (1 : A)) = 0 := by
        funext k; rw [LinearEquiv.map_zero, Pi.zero_apply, TensorProduct.zero_tmul, Pi.zero_apply]
      rw [this]; exact W.zero_mem
    | tmul a s =>
      have : (fun k => (hbcS.equiv (a ⊗ₜ[ℤ] s)) k ⊗ₜ[ℤ] (1 : A)) =
          (a ⊗ₜ[ℤ] (1 : A)) • (fun k => (s : G → A) k ⊗ₜ[ℤ] (1 : A)) := by
        funext k
        rw [IsBaseChange.equiv_tmul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        rfl
      rw [this]
      exact W.smul_mem _ (Submodule.subset_span ⟨s, rfl⟩)
    | add x y hx hy =>
      have : (fun k => (hbcS.equiv (x + y)) k ⊗ₜ[ℤ] (1 : A)) =
          (fun k => hbcS.equiv x k ⊗ₜ[ℤ] (1 : A)) + (fun k => hbcS.equiv y k ⊗ₜ[ℤ] (1 : A)) := by
        funext k; rw [LinearEquiv.map_add, Pi.add_apply, TensorProduct.add_tmul, Pi.add_apply]
      rw [this]; exact W.add_mem hx hy

  have h2 : ∀ (k : G) (x y : A), (Pi.single k (x ⊗ₜ[ℤ] y) : G → A ⊗[ℤ] A) ∈ W := by
    intro k x y
    have : (Pi.single k (x ⊗ₜ[ℤ] y) : G → A ⊗[ℤ] A) =
        ((1 : A) ⊗ₜ[ℤ] y) • (fun j => (Pi.single k x : G → A) j ⊗ₜ[ℤ] (1 : A)) := by
      funext j
      rw [Pi.smul_apply, smul_eq_mul]
      by_cases h : j = k
      · subst h
        rw [Pi.single_eq_same, Pi.single_eq_same, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, TensorProduct.zero_tmul, mul_zero]
    rw [this]; exact W.smul_mem _ (h1 _)

  rw [eq_top_iff]
  rintro F -
  rw [← Finset.univ_sum_single F]
  refine W.sum_mem fun k _ => ?_
  induction F k using TensorProduct.induction_on with
  | zero => rw [Pi.single_zero]; exact W.zero_mem
  | tmul x y => exact h2 k x y
  | add x y hx hy => rw [Pi.single_add]; exact W.add_mem hx hy

private theorem main (faithful : Module.FaithfullyFlat ℤ A)
    (e : G → A ⊗[ℤ] A)
    (S : Subalgebra ℤ (G → A))
    (hS : ∀ f : G → A, f ∈ S ↔ ∀ k, ∑ m, e m * (f (k - m) ⊗ₜ[ℤ] 1) = 1 ⊗ₜ[ℤ] f k)
    (hbcS : IsBaseChange A S.val.toLinearMap) :
    ∃ d : G → A, CompleteOrthogonalIdempotents d ∧ ∀ k, e k = ∑ i, d i ⊗ₜ[ℤ] d (i + k) := by
  classical
  haveI : Nontrivial A := (TensorProduct.lid ℤ A).symm.toEquiv.nontrivial

  have ε_tmul : ∀ (a : A) (s : S), hbcS.equiv (a ⊗ₜ s) = a • (s : G → A) :=
    fun a s => hbcS.equiv_tmul a s
  have ε_mul : ∀ x y : A ⊗[ℤ] S, hbcS.equiv (x * y) = hbcS.equiv x * hbcS.equiv y := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => rw [zero_mul, LinearEquiv.map_zero, zero_mul]
    | add x x' hx hx' => rw [add_mul, LinearEquiv.map_add, LinearEquiv.map_add, hx, hx', add_mul]
    | tmul a s =>
      induction y using TensorProduct.induction_on with
      | zero => rw [mul_zero, LinearEquiv.map_zero, mul_zero]
      | add y y' hy hy' => rw [mul_add, LinearEquiv.map_add, LinearEquiv.map_add, hy, hy', mul_add]
      | tmul a' s' =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, ε_tmul, ε_tmul, ε_tmul, Subalgebra.coe_mul,
          smul_mul_smul_comm]
  have ε_one : hbcS.equiv 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, ε_tmul, one_smul]; rfl
  let ι : (A ⊗[ℤ] S) ≃ₐ[A] (G → A) := AlgEquiv.ofLinearEquiv hbcS.equiv ε_one ε_mul
  have ι_apply : ∀ x, ι x = hbcS.equiv x := fun _ => rfl
  have ι_symm_coe : ∀ s : S, ι.symm (s : G → A) = 1 ⊗ₜ s := fun s => by
    rw [AlgEquiv.symm_apply_eq, ι_apply, ε_tmul, one_smul]

  haveI : Module.Finite A (A ⊗[ℤ] S) := Module.Finite.equiv ι.toLinearEquiv.symm
  haveI : Module.Finite ℤ S := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat A
  haveI : Module.Flat A (A ⊗[ℤ] S) := Module.Flat.of_linearEquiv ι.toLinearEquiv
  haveI : Module.Flat ℤ S := Module.Flat.of_flat_tensorProduct ℤ S A
  haveI : Algebra.FormallyUnramified A (A ⊗[ℤ] S) := Algebra.FormallyUnramified.of_equiv ι.symm
  haveI : Algebra.FormallyUnramified ℤ S :=
    Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat A

  obtain ⟨χ⟩ := @Algebra.FormallyUnramified.nonempty_ringHom_int S _ _
    (by convert ‹Module.Finite ℤ S›) (by convert ‹Module.Flat ℤ S›)
    (by convert ‹Algebra.FormallyUnramified ℤ S›; rfl)

  let χA : S →ₐ[ℤ] A := ((algebraMap ℤ A).comp χ).toIntAlgHom
  let ψ : (G → A) →ₐ[A] A :=
    (Algebra.TensorProduct.lift (AlgHom.id A A) χA fun _ _ => Commute.all _ _).comp ι.symm.toAlgHom
  have hψS : ∀ s : S, ψ s = algebraMap ℤ A (χ s) := by
    intro s
    change Algebra.TensorProduct.lift (AlgHom.id A A) χA (fun _ _ => Commute.all _ _)
      (ι.symm (s : G → A)) = _
    rw [ι_symm_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  set d : G → A := fun k => ψ (Pi.single k 1) with hd_def
  have hd : CompleteOrthogonalIdempotents d :=
    (CompleteOrthogonalIdempotents.single (R := fun _ : G => A)).map ψ.toRingHom
  have hψf : ∀ f : G → A, ψ f = ∑ k, f k * d k := by
    intro f
    conv_lhs => rw [← Finset.univ_sum_single f]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (Pi.single k (f k) : G → A) = algebraMap A (G → A) (f k) * Pi.single k 1 := by
      ext j
      by_cases h : j = k
      · subst h; simp
      · simp [h]
    rw [this, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

  have htrans : ∀ f : G → A, f ∈ S → ∀ h : G, (fun j => f (j + h)) ∈ S := by
    intro f hf h
    rw [hS] at hf ⊢
    intro k
    have := hf (k + h)
    simpa only [add_sub_right_comm] using this
  have hcoef : ∀ (f : G → A) (hf : f ∈ S) (i j : G),
      f j * d i = algebraMap ℤ A (χ ⟨fun l => f (l + (j - i)), htrans f hf (j - i)⟩) * d i := by
    intro f hf i j
    have h1 := hψS ⟨fun l => f (l + (j - i)), htrans f hf (j - i)⟩
    rw [hψf] at h1
    have h2 := congrArg (· * d i) h1
    simp only [Finset.sum_mul] at h2
    rw [Finset.sum_eq_single i] at h2
    · simpa [mul_assoc, (hd.idem i).eq] using h2
    · intro l _ hli
      rw [mul_assoc, hd.ortho hli, mul_zero]
    · simp

  let E : G → A ⊗[ℤ] A := fun m => ∑ i, d i ⊗ₜ[ℤ] d (i + m)
  have hF : ∀ f : G → A, f ∈ S →
      transl e (fun k => f k ⊗ₜ[ℤ] (1 : A)) = transl E (fun k => f k ⊗ₜ[ℤ] (1 : A)) := by
    intro f hf
    ext k
    rw [transl_apply, transl_apply, (hS f).mp hf k]

    set n : G → A := fun h => algebraMap ℤ A (χ ⟨fun l => f (l + h), htrans f hf h⟩) with hn
    have hcoef' : ∀ i j, f j * d i = n (j - i) * d i := fun i j => hcoef f hf i j
    symm
    calc ∑ m, E m * (f (k - m) ⊗ₜ[ℤ] (1 : A))
        = ∑ m, ∑ i, (f (k - m) * d i) ⊗ₜ[ℤ] d (i + m) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [E, Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm (d _) (f _)]
      _ = ∑ m, ∑ i, (n (k - m - i) * d i) ⊗ₜ[ℤ] d (i + m) := by
          simp only [hcoef', sub_sub]
      _ = ∑ i, ∑ m, (n (k - m - i) * d i) ⊗ₜ[ℤ] d (i + m) := Finset.sum_comm
      _ = ∑ i, ∑ j, (n (k - j) * d i) ⊗ₜ[ℤ] d j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Fintype.sum_equiv (Equiv.addLeft i) _ _ (fun m => ?_)
          simp only [Equiv.coe_addLeft]
          congr 3
          abel
      _ = ∑ j, ∑ i, (n (k - j) * d i) ⊗ₜ[ℤ] d j := Finset.sum_comm
      _ = ∑ j, (n (k - j)) ⊗ₜ[ℤ] d j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← TensorProduct.sum_tmul, ← Finset.mul_sum, hd.complete, mul_one]
      _ = ∑ j, (1 : A) ⊗ₜ[ℤ] (n (k - j) * d j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hn]
          simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      _ = (1 : A) ⊗ₜ[ℤ] f k := by
          rw [← TensorProduct.tmul_sum]
          congr 1
          calc ∑ j, n (k - j) * d j = ∑ j, f k * d j := Finset.sum_congr rfl fun j _ => (hcoef' j k).symm
            _ = f k := by rw [← Finset.mul_sum, hd.complete, mul_one]
  have hspan : Submodule.span (A ⊗[ℤ] A)
      (Set.range fun s : S => fun k => (s : G → A) k ⊗ₜ[ℤ] (1 : A)) = ⊤ := span_eq_top S hbcS
  have hEe : transl e = transl E :=
    LinearMap.ext_on_range hspan fun s => hF s s.2
  refine ⟨d, hd, fun k => ?_⟩
  rw [← transl_single_zero e k, hEe, transl_single_zero]

end main

end Module.FaithfullyFlat

open _root_.Module.FaithfullyFlat _root_.P2MW.S_Module_FaithfullyFlat_exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange.Module.FaithfullyFlat in

theorem solution
    (A : Type u) [CommRing A] [Module.FaithfullyFlat ℤ A]
    {G : Type v} [AddCommGroup G] [Fintype G]
    (e : G → A ⊗[ℤ] A) (he : CompleteOrthogonalIdempotents e)
    (M : Submodule ℤ (G → A))
    (hM : ∀ f : G → A, f ∈ M ↔ ∀ k, ∑ m, e m * (f (k - m) ⊗ₜ[ℤ] 1) = 1 ⊗ₜ[ℤ] f k)
    (hbc : IsBaseChange A M.subtype) :
    ∃ d : G → A, CompleteOrthogonalIdempotents d ∧ ∀ k, e k = ∑ i, d i ⊗ₜ[ℤ] d (i - k) := by
  obtain ⟨S, hSM⟩ := exists_subalgebra_mem_iff e he M hM
  have hS : ∀ f : G → A, f ∈ S ↔ ∀ k, ∑ m, e m * (f (k - m) ⊗ₜ[ℤ] 1) = 1 ⊗ₜ[ℤ] f k :=
    fun f => (hSM f).trans (hM f)
  have hbcS : IsBaseChange A S.val.toLinearMap := by
    refine (IsBaseChange.iff_of_equiv_comm (f := M.subtype) (f' := S.val.toLinearMap)
      ({ toFun := fun x => ⟨x.1, (hSM x.1).mpr x.2⟩, invFun := fun x => ⟨x.1, (hSM x.1).mp x.2⟩,
         map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
         left_inv := fun _ => rfl, right_inv := fun _ => rfl } : M ≃ₗ[ℤ] S)
      (LinearEquiv.refl A (G → A)) ?_).mp hbc
    ext x; rfl
  obtain ⟨d, hd, hed⟩ := main ‹_› e S hS hbcS
  refine ⟨fun i => d (-i), ?_, fun k => ?_⟩
  · refine ⟨⟨fun i => hd.idem (-i), fun i j hij => hd.ortho fun h => hij (neg_injective h)⟩, ?_⟩
    rw [← hd.complete]
    exact Fintype.sum_equiv (Equiv.neg G) _ _ (fun k => rfl)
  · rw [hed k]
    exact (Fintype.sum_equiv (Equiv.neg G) _ _ (fun i => by simp [sub_eq_add_neg, add_comm])).symm

end S_Module_FaithfullyFlat_exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange
end P2MW
export P2MW.S_Module_FaithfullyFlat_exists_completeOrthogonalIdempotents_eq_sum_tmul_of_isBaseChange (solution)
