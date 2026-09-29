-- Prove2me | solution 1 for HopfAlgebra.ker_eq_torsionIdeal_of_baseChange_addMonoidAlgebra_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/309fef7b-b935-505e-b57e-9351e75a2801

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_ker_eq_torsionIdeal_of_baseChange_addMonoidAlgebra_of_surjective

set_option autoImplicit false

open scoped TensorProduct

set_option maxHeartbeats 800000

namespace Ws47
namespace MTKER

open AddMonoidAlgebra PDivisibleGroup.Hopf

section GroupAlgebra

variable (A : Type) [CommRing A] {Λ Λ' : Type} [AddCommGroup Λ] [AddCommGroup Λ']

theorem algebraMap_eq_single (a : A) : algebraMap A (AddMonoidAlgebra A Λ') a = single 0 a := by
  simp [AddMonoidAlgebra.coe_algebraMap]

theorem nsmulAlgHom_single (y : Λ') (a : A) :
    ∀ n : ℕ, nsmulAlgHom A (AddMonoidAlgebra A Λ') n (single y a) = single (n • y) a
  | 0 => by
    change (WithConv.ofConv ((WithConv.toConv (AlgHom.id A (AddMonoidAlgebra A Λ')) ^ 0 : WithConv (AddMonoidAlgebra A Λ' →ₐ[A] AddMonoidAlgebra A Λ')))) (single y a) = _
    rw [pow_zero, AlgHom.convOne_apply, counit_single, CommSemiring.counit_apply, zero_nsmul, algebraMap_eq_single]
  | n + 1 => by
    have ih := nsmulAlgHom_single y a n
    change (WithConv.ofConv ((WithConv.toConv (AlgHom.id A (AddMonoidAlgebra A Λ')) ^ (n + 1) : WithConv (AddMonoidAlgebra A Λ' →ₐ[A] AddMonoidAlgebra A Λ')))) (single y a) = _
    rw [pow_succ, AlgHom.convMul_apply, comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
      lsingle_apply, lsingle_apply, Algebra.TensorProduct.lift_tmul]
    change nsmulAlgHom A (AddMonoidAlgebra A Λ') n (single y 1) * single y a = _
    rw [nsmulAlgHom_single y 1 n, single_mul_single, one_mul, succ_nsmul]

theorem augIdeal_eq_span :
    augIdeal A (AddMonoidAlgebra A Λ') = Ideal.span (Set.range fun y : Λ' => single y (1 : A) - 1) := by
  apply le_antisymm
  · intro z hz
    rw [mem_augIdeal_iff] at hz
    have h1 : z = z.coeff.sum (fun y c => single y c) := (AddMonoidAlgebra.sum_coeff_single z).symm
    have h2 : Coalgebra.counit (R := A) z = z.coeff.sum (fun _ c => c) := by
      conv_lhs => rw [h1]
      rw [map_finsuppSum]
      refine Finsupp.sum_congr fun y c => ?_
      rw [counit_single, CommSemiring.counit_apply]
    have h3 : z = z.coeff.sum (fun y c => c • (single y (1 : A) - 1)) + algebraMap A _ (z.coeff.sum (fun _ c => c)) := by
      conv_lhs => rw [h1]
      rw [map_finsuppSum, ← Finsupp.sum_add]
      refine Finsupp.sum_congr fun y c => ?_
      rw [smul_sub, smul_single', mul_one, Algebra.algebraMap_eq_smul_one, sub_add_cancel]
    rw [h3, ← h2, hz, map_zero, add_zero]
    refine Submodule.sum_mem _ fun y _ => ?_
    show z.coeff y • (single y (1 : A) - 1 : AddMonoidAlgebra A Λ') ∈ Ideal.span (Set.range fun y : Λ' => (single y (1 : A) - 1 : AddMonoidAlgebra A Λ'))
    exact Submodule.smul_of_tower_mem _ (z.coeff y) (Ideal.subset_span (Set.mem_range_self y))
  · rw [Ideal.span_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, mem_augIdeal_iff, map_sub, counit_single, CommSemiring.counit_apply, Bialgebra.counit_one, sub_self]

theorem torsionIdeal_eq_span (n : ℕ) :
    torsionIdeal A (AddMonoidAlgebra A Λ') n = Ideal.span (Set.range fun y : Λ' => single (n • y) (1 : A) - 1) := by
  rw [torsionIdeal, augIdeal_eq_span, Ideal.map_span, ← Set.range_comp]
  exact congrArg Ideal.span (congrArg Set.range (funext fun y => by
    simp only [Function.comp_apply, map_sub, nsmulAlgHom_single, map_one]))

theorem ker_mapDomain_eq_span (f : Λ' →+ Λ) (hf : Function.Surjective f) :
    RingHom.ker (mapDomainBialgHom A f) = Ideal.span (Set.range fun x : {x : Λ' // f x = 0} => single (x : Λ') (1 : A) - 1) := by
  classical
  set I : Ideal (AddMonoidAlgebra A Λ') := Ideal.span (Set.range fun x : {x : Λ' // f x = 0} => single (x : Λ') (1 : A) - 1)
    with hI
  apply le_antisymm
  ·
    obtain ⟨s, hs⟩ := hf.hasRightInverse
    have hsingle : ∀ x x' : Λ', f x = f x' → (Ideal.Quotient.mkₐ A I (single x 1) : AddMonoidAlgebra A Λ' ⧸ I) = Ideal.Quotient.mkₐ A I (single x' 1) := by
      intro x x' hxx'
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
      have : single x (1 : A) - single x' 1 = single x' 1 * (single (x - x') 1 - 1) := by
        rw [mul_sub, single_mul_single, mul_one, mul_one, add_sub_cancel]
      rw [this]
      refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨x - x', by rw [map_sub, hxx', sub_self]⟩, rfl⟩)
    let g : Multiplicative Λ →* (AddMonoidAlgebra A Λ' ⧸ I) :=
      { toFun := fun l => Ideal.Quotient.mkₐ A I (single (s (Multiplicative.toAdd l)) 1)
        map_one' := by
          change Ideal.Quotient.mkₐ A I (single (s 0) 1) = 1
          rw [hsingle (s 0) 0 (by rw [hs, map_zero]), ← one_def, map_one]
        map_mul' := fun l l' => by
          change Ideal.Quotient.mkₐ A I (single (s (Multiplicative.toAdd l + Multiplicative.toAdd l')) 1) =
            Ideal.Quotient.mkₐ A I (single (s (Multiplicative.toAdd l)) 1) * Ideal.Quotient.mkₐ A I (single (s (Multiplicative.toAdd l')) 1)
          rw [← map_mul, single_mul_single, mul_one]
          exact hsingle _ _ (by rw [hs, map_add, hs, hs]) }
    let G : AddMonoidAlgebra A Λ →ₐ[A] (AddMonoidAlgebra A Λ' ⧸ I) := AddMonoidAlgebra.lift A _ Λ g

    have hG : ∀ z : AddMonoidAlgebra A Λ', G (mapDomainBialgHom A f z) = Ideal.Quotient.mkₐ A I z := by
      intro z
      induction z using AddMonoidAlgebra.induction_on with
      | of x =>
        rw [AddMonoidAlgebra.of_apply, mapDomainBialgHom_single]
        change G (single (f (Multiplicative.toAdd (Multiplicative.ofAdd x))) 1) = _
        rw [toAdd_ofAdd, AddMonoidAlgebra.lift_single, one_smul]
        exact hsingle (s (f x)) x (hs (f x))
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
      | smul r a ha => rw [map_smul, map_smul, map_smul, ha]
    intro z hz
    rw [RingHom.mem_ker] at hz
    have := hG z
    rw [hz, map_zero, Ideal.Quotient.mkₐ_eq_mk] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
  · rw [Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, mapDomainBialgHom_single, x.2, map_one, ← one_def,
      sub_self]

theorem ker_mapDomain_eq_torsionIdeal (f : Λ' →+ Λ) (hf : Function.Surjective f) (q : ℕ)
    (hfker : ∀ x : Λ', f x = 0 ↔ ∃ y : Λ', x = q • y) :
    RingHom.ker (mapDomainBialgHom A f) = torsionIdeal A (AddMonoidAlgebra A Λ') q := by
  rw [ker_mapDomain_eq_span A f hf, torsionIdeal_eq_span]
  congr 1
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (hfker x).1 x.2
    exact ⟨y, by simp only [hy]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨⟨q • y, (hfker _).2 ⟨y, rfl⟩⟩, rfl⟩

end GroupAlgebra

section BaseChange

variable {R : Type} [CommRing R] (A : Type) [CommRing A] [Algebra R A]
  {C : Type} [CommRing C] [HopfAlgebra R C]

theorem nsmulAlgHom_baseChange_tmul :
    ∀ (n : ℕ) (a : A) (c : C), nsmulAlgHom A (A ⊗[R] C) n (a ⊗ₜ[R] c) = a ⊗ₜ[R] nsmulAlgHom R C n c
  | 0, a, c => by
    rw [nsmulAlgHom_zero_apply, nsmulAlgHom_zero_apply, TensorProduct.counit_tmul,
      CommSemiring.counit_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | n + 1, a, c => by
    have ih := fun (l : C) => nsmulAlgHom_baseChange_tmul n 1 l
    rw [nsmulAlgHom_succ, nsmulAlgHom_succ, AlgHom.convMul_apply, AlgHom.convMul_apply]
    have r := Coalgebra.Repr.arbitrary R c
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← r.eq, TensorProduct.tmul_sum, map_sum, map_sum, map_sum,
      TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lift_tmul]
    change nsmulAlgHom A (A ⊗[R] C) n ((1 : A) ⊗ₜ[R] r.left i) * (a ⊗ₜ[R] r.right i) =
      a ⊗ₜ[R] (nsmulAlgHom R C n (r.left i) * r.right i)
    rw [ih, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem augIdeal_baseChange :
    augIdeal A (A ⊗[R] C) = (augIdeal R C).map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)) := by
  apply le_antisymm
  · intro z hz
    rw [mem_augIdeal_iff] at hz

    let P : A ⊗[R] C →ₗ[R] A ⊗[R] C :=
      LinearMap.lTensor A (LinearMap.id - Algebra.linearMap R C ∘ₗ Coalgebra.counit)
    have hP : ∀ (x : A) (y : C), P (x ⊗ₜ[R] y) = x ⊗ₜ[R] (y - algebraMap R C (Coalgebra.counit (R := R) y)) := by
      intro x y; simp [P, LinearMap.lTensor_tmul, TensorProduct.tmul_sub]
    have hPmem : ∀ w, P w ∈ (augIdeal R C).map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)) := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Ideal.zero_mem _
      | tmul x y =>
        rw [hP]
        have : x ⊗ₜ[R] (y - algebraMap R C (Coalgebra.counit (R := R) y)) =
            (x ⊗ₜ[R] (1 : C)) * ((1 : A) ⊗ₜ[R] (y - algebraMap R C (Coalgebra.counit (R := R) y))) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [this]
        refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
        rw [mem_augIdeal_iff, map_sub, Bialgebra.counit_algebraMap, sub_self]
      | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy

    have hrest : ∀ w : A ⊗[R] C, w - P w = algebraMap A (A ⊗[R] C) (Coalgebra.counit (R := A) w) := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        rw [hP, TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, ← TensorProduct.tmul_sub, sub_sub_cancel,
          Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      | add x y hx hy => rw [map_add, map_add, map_add, ← hx, ← hy]; abel
    have hz' : z = P z := by
      have := hrest z; rw [hz, map_zero, sub_eq_zero] at this; exact this
    rw [hz']; exact hPmem z
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, mem_augIdeal_iff, Algebra.TensorProduct.includeRight_apply, TensorProduct.counit_tmul,
      (mem_augIdeal_iff R C y).1 hy, zero_smul]

theorem torsionIdeal_baseChange (n : ℕ) :
    torsionIdeal A (A ⊗[R] C) n = (torsionIdeal R C n).map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)) := by
  rw [torsionIdeal, torsionIdeal, augIdeal_baseChange]
  change Ideal.map (nsmulAlgHom A (A ⊗[R] C) n).toRingHom (Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)).toRingHom _) =
    Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)).toRingHom (Ideal.map (nsmulAlgHom R C n).toRingHom _)
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext y
  change nsmulAlgHom A (A ⊗[R] C) n ((1 : A) ⊗ₜ[R] y) = (1 : A) ⊗ₜ[R] nsmulAlgHom R C n y
  exact nsmulAlgHom_baseChange_tmul A n 1 y

end BaseChange

section Descent

variable {R : Type} [CommRing R] (A : Type) [CommRing A] [Algebra R A]
  {C : Type} [CommRing C] [Algebra R C]

theorem range_lTensor_subtype_eq (I : Ideal C) :
    LinearMap.range (LinearMap.lTensor A (I.restrictScalars R).subtype) =
      (I.map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C))).restrictScalars R := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul a i =>
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, Submodule.restrictScalars_mem]
      have : a ⊗ₜ[R] (i : C) = (a ⊗ₜ[R] (1 : C)) * ((1 : A) ⊗ₜ[R] (i : C)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ i.2)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  ·
    have hmul : ∀ z w : A ⊗[R] C, w ∈ LinearMap.range (LinearMap.lTensor A (I.restrictScalars R).subtype) →
        z * w ∈ LinearMap.range (LinearMap.lTensor A (I.restrictScalars R).subtype) := by
      intro z w ⟨u, hu⟩
      subst hu
      induction u using TensorProduct.induction_on with
      | zero => rw [map_zero, mul_zero]; exact Submodule.zero_mem _
      | tmul a i =>
        induction z using TensorProduct.induction_on with
        | zero => rw [zero_mul]; exact Submodule.zero_mem _
        | tmul x y =>
          rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, Algebra.TensorProduct.tmul_mul_tmul]
          exact ⟨(x * a) ⊗ₜ[R] ⟨y * i, I.mul_mem_left y i.2⟩, by rw [LinearMap.lTensor_tmul]; rfl⟩
        | add x y hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
      | add x y hx hy => rw [map_add, mul_add]; exact Submodule.add_mem _ hx hy
    intro z hz
    rw [Submodule.restrictScalars_mem] at hz
    have hz' : z ∈ Submodule.span (A ⊗[R] C) (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C) '' I) := by
      rwa [Ideal.map, ← Ideal.submodule_span_eq] at hz
    clear hz
    induction hz' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact ⟨(1 : A) ⊗ₜ[R] ⟨i, hi⟩, by rw [LinearMap.lTensor_tmul]; rfl⟩
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul w x _ hx => rw [smul_eq_mul]; exact hmul w x hx

theorem ideal_eq_of_map_includeRight_eq [Module.FaithfullyFlat R A] (I J : Ideal C)
    (h : I.map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)) =
      J.map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C))) : I = J := by

  suffices key : ∀ I J : Ideal C, I.map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)) =
      J.map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)) → I ≤ J from
    le_antisymm (key I J h) (key J I h.symm)
  intro I J hIJ

  let φ : ↥(I.restrictScalars R) →ₗ[R] C ⧸ (J.restrictScalars R) := (J.restrictScalars R).mkQ ∘ₗ (I.restrictScalars R).subtype
  have hφ : φ = 0 := by
    rw [Module.FaithfullyFlat.zero_iff_lTensor_zero R A]
    apply LinearMap.ext
    intro w
    rw [LinearMap.zero_apply]
    have hw : LinearMap.lTensor A (I.restrictScalars R).subtype w ∈
        LinearMap.range (LinearMap.lTensor A (J.restrictScalars R).subtype) := by
      rw [range_lTensor_subtype_eq, ← hIJ, ← range_lTensor_subtype_eq A I]
      exact ⟨w, rfl⟩
    have hex := lTensor_exact A (LinearMap.exact_subtype_mkQ (J.restrictScalars R)) (Submodule.mkQ_surjective _)
    rw [show LinearMap.lTensor A φ = LinearMap.lTensor A (J.restrictScalars R).mkQ ∘ₗ LinearMap.lTensor A (I.restrictScalars R).subtype
      from LinearMap.lTensor_comp A _ _, LinearMap.comp_apply]
    exact (hex _).2 hw
  intro x hx
  have : φ ⟨x, hx⟩ = 0 := by rw [hφ]; rfl
  simpa [φ] using this

end Descent

section Main

variable {R : Type} [CommRing R] (A : Type) [CommRing A] [Algebra R A]
  {C C' : Type} [CommRing C] [HopfAlgebra R C] [CommRing C'] [HopfAlgebra R C']

theorem ker_baseChange_eq (t : C' →ₐc[R] C) (ht : Function.Surjective t) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id A A) (t : C' →ₐ[R] C)) =
      (RingHom.ker t).map (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C')) := by

  have hex0 : Function.Exact ((RingHom.ker t).restrictScalars R).subtype (t : C' →ₐ[R] C).toLinearMap := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    ext x; rfl
  have hex := lTensor_exact A hex0 ht
  have hker := hex.linearMap_ker_eq
  have hagree : ∀ z : A ⊗[R] C', LinearMap.lTensor A (t : C' →ₐ[R] C).toLinearMap z =
      Algebra.TensorProduct.map (AlgHom.id A A) (t : C' →ₐ[R] C) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a c => rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  apply le_antisymm
  · intro z hz
    have hz' : z ∈ LinearMap.ker (LinearMap.lTensor A (t : C' →ₐ[R] C).toLinearMap) := by
      rw [LinearMap.mem_ker, hagree]; exact hz
    rw [hker] at hz'
    exact (range_lTensor_subtype_eq (R := R) A (RingHom.ker t)).le hz'
  · rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
    rw [RingHom.mem_ker] at hc
    change (1 : A) ⊗ₜ[R] t c = 0
    rw [hc, TensorProduct.tmul_zero]

end Main

end Ws47.MTKER

open Ws47.MTKER PDivisibleGroup.Hopf in
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsDomain R]
    (A : Type) [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]
    (C C' : Type) [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C] [Module.Free R C] [Module.Finite R C]
    [CommRing C'] [HopfAlgebra R C'] [Coalgebra.IsCocomm R C'] [Module.Free R C'] [Module.Finite R C']
    (Λ Λ' : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] [AddCommGroup Λ'] [Fintype Λ'] [DecidableEq Λ']
    (e : A ⊗[R] C ≃ₐc[A] AddMonoidAlgebra A Λ) (e' : A ⊗[R] C' ≃ₐc[A] AddMonoidAlgebra A Λ')
    (v : ℕ) (f : Λ' →+ Λ) (hf : Function.Surjective f) (hfker : ∀ x : Λ', f x = 0 ↔ ∃ y : Λ', x = (p ^ v) • y)
    (t : C' →ₐc[R] C) (ht : Function.Surjective t)
    (hte : ∀ z : A ⊗[R] C', e (Algebra.TensorProduct.map (AlgHom.id A A) (t : C' →ₐ[R] C) z) =
      AddMonoidAlgebra.mapDomainBialgHom A f (e' z)) :
    RingHom.ker t = PDivisibleGroup.Hopf.torsionIdeal R C' (p ^ v) := by
  classical
  apply ideal_eq_of_map_includeRight_eq (R := R) A
  rw [← ker_baseChange_eq A t ht, ← torsionIdeal_baseChange (R := R) A (C := C') (p ^ v)]
  have hG := ker_mapDomain_eq_torsionIdeal A f hf (p ^ v) hfker
  have hT : (torsionIdeal A (A ⊗[R] C') (p ^ v)).map (e' : A ⊗[R] C' →ₐc[A] AddMonoidAlgebra A Λ') =
      torsionIdeal A (AddMonoidAlgebra A Λ') (p ^ v) :=
    map_torsionIdeal_of_surjective (e' : A ⊗[R] C' →ₐc[A] AddMonoidAlgebra A Λ') e'.surjective (p ^ v)
  ext z
  rw [RingHom.mem_ker]
  constructor
  · intro hz
    have h1 : AddMonoidAlgebra.mapDomainBialgHom A f (e' z) = 0 := by rw [← hte, hz, map_zero]
    have h2 : e' z ∈ (torsionIdeal A (A ⊗[R] C') (p ^ v)).map (e' : A ⊗[R] C' →ₐc[A] AddMonoidAlgebra A Λ') := by
      rw [hT, ← hG, RingHom.mem_ker]; exact h1
    obtain ⟨x, hx, hxz⟩ := (Ideal.mem_map_iff_of_surjective (e' : A ⊗[R] C' →ₐc[A] AddMonoidAlgebra A Λ') e'.surjective).1 h2
    have : x = z := e'.injective hxz
    rwa [← this]
  · intro hz
    have h2 : e' z ∈ (torsionIdeal A (A ⊗[R] C') (p ^ v)).map (e' : A ⊗[R] C' →ₐc[A] AddMonoidAlgebra A Λ') :=
      Ideal.mem_map_of_mem _ hz
    rw [hT, ← hG, RingHom.mem_ker] at h2
    have h3 : e (Algebra.TensorProduct.map (AlgHom.id A A) (t : C' →ₐ[R] C) z) = 0 := by rw [hte]; exact h2
    exact e.injective (h3.trans (map_zero e).symm)

end S_HopfAlgebra_ker_eq_torsionIdeal_of_baseChange_addMonoidAlgebra_of_surjective
end P2MW
export P2MW.S_HopfAlgebra_ker_eq_torsionIdeal_of_baseChange_addMonoidAlgebra_of_surjective (solution)
