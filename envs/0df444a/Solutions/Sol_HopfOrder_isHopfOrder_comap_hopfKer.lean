-- Prove2me | solution 1 for HopfOrder.isHopfOrder_comap_hopfKer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c5776d6b-1e2e-551c-9943-a7acced8eef7

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped TensorProduct

namespace HopfOrder
namespace Aux
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable {A : Type*} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

noncomputable def tensorSqHom (S : Subalgebra R A) : (S ⊗[R] S) →ₐ[R] (A ⊗[K] A) :=
  Algebra.TensorProduct.productMap
    (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
    (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)

@[scoped simp]
lemma tensorSqHom_tmul (S : Subalgebra R A) (t t' : S) :
    tensorSqHom (K := K) S (t ⊗ₜ[R] t') = (t : A) ⊗ₜ[K] (t' : A) := by
  simp [tensorSqHom, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]

lemma tensorSqHom_sum_smul_tmul (S : Subalgebra R A) {n : ℕ} (s : Fin n → S)
    (r : Fin n × Fin n → R) :
    tensorSqHom (K := K) S (∑ q, r q • (s q.1 ⊗ₜ[R] s q.2))
      = ∑ q, r q • ((s q.1 : A) ⊗ₜ[K] (s q.2 : A)) := by
  simp only [map_sum, map_smul, tensorSqHom_tmul]

lemma map_val_tensorSqHom_sum_smul_tmul (S : Subalgebra R A) (A₁ : Subalgebra K A) {n : ℕ}
    (γ : Fin n → ↥(S.comap ((A₁.val : ↥A₁ →ₐ[K] A).restrictScalars R)))
    (r : Fin n × Fin n → R) :
    TensorProduct.map (A₁.val : ↥A₁ →ₐ[K] A).toLinearMap (A₁.val : ↥A₁ →ₐ[K] A).toLinearMap
        (tensorSqHom (K := K) (S.comap ((A₁.val : ↥A₁ →ₐ[K] A).restrictScalars R))
          (∑ q, r q • (γ q.1 ⊗ₜ[R] γ q.2)))
      = ∑ q, r q • ((((γ q.1 : ↥A₁) : A)) ⊗ₜ[K] (((γ q.2 : ↥A₁) : A))) := by
  simp only [map_sum, LinearMap.map_smul_of_tower, map_smul, tensorSqHom_tmul, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, Subalgebra.coe_val]

end HopfOrder.Aux
p2m_reactivate "P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder.Aux"
p2m_reactivate "P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder"

namespace HopfOrder
namespace KerAux
open HopfOrder.Aux

variable {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

omit [IsDomain R] in
lemma algebraMap_ne_zero {r : R} (hr : r ≠ 0) : algebraMap R K r ≠ 0 := fun h =>
  hr ((injective_iff_map_eq_zero (algebraMap R K)).mp (IsFractionRing.injective R K) r h)

include K in
lemma isTorsionFree : Module.IsTorsionFree R A := by
  refine Module.IsTorsionFree.mk fun r hr => ?_
  have hr0 : r ≠ 0 := hr.left.ne_zero
  have hK : algebraMap R K r ≠ 0 := algebraMap_ne_zero (K := K) hr0
  intro a b hab
  have hab' : algebraMap R K r • a = algebraMap R K r • b := by
    simpa [IsScalarTower.algebraMap_smul] using hab
  exact smul_right_injective A hK hab'

include K in
lemma free_of_finite [IsPrincipalIdealRing R] (S : Subalgebra R A) [Module.Finite R S] :
    Module.Free R S := by
  haveI : Module.IsTorsionFree R A := isTorsionFree (R := R) (K := K) (A := A)
  haveI : Module.IsTorsionFree R S :=
    Function.Injective.moduleIsTorsionFree (fun s : S => (s : A)) Subtype.coe_injective (fun _ _ => rfl)
  exact Module.free_of_finite_type_torsion_free'

omit [IsDomain R] [IsFractionRing R K] in
lemma algebraMap_smul_mem (S : Subalgebra R A) (r : R) {z : A} (hz : z ∈ S) :
    algebraMap R K r • z ∈ S := by
  rw [IsScalarTower.algebraMap_smul]; exact S.smul_mem hz r

lemma exists_nonzero_smul_mem (S : Subalgebra R A) (hspan : Submodule.span K (S : Set A) = ⊤) (a : A) :
    ∃ r : R, r ≠ 0 ∧ algebraMap R K r • a ∈ S := by
  have ha : a ∈ Submodule.span K (S : Set A) := hspan ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem s hs => exact ⟨1, one_ne_zero, by simpa using hs⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact S.zero_mem⟩
  | add x y _ _ hx hy =>
      obtain ⟨r₁, h₁, e₁⟩ := hx
      obtain ⟨r₂, h₂, e₂⟩ := hy
      refine ⟨r₁ * r₂, mul_ne_zero h₁ h₂, ?_⟩
      rw [smul_add]
      refine S.add_mem ?_ ?_
      · rw [map_mul, mul_comm, mul_smul]; exact algebraMap_smul_mem S r₂ e₁
      · rw [map_mul, mul_smul]; exact algebraMap_smul_mem S r₁ e₂
  | smul k x _ hx =>
      obtain ⟨r, hr, e⟩ := hx
      obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) k
      have hd0 : algebraMap R K d ≠ 0 := algebraMap_ne_zero (K := K) (nonZeroDivisors.ne_zero hd)
      refine ⟨d * r, mul_ne_zero (nonZeroDivisors.ne_zero hd) hr, ?_⟩
      have : algebraMap R K (d * r) * (algebraMap R K n / algebraMap R K d)
          = algebraMap R K n * algebraMap R K r := by
        rw [map_mul]; field_simp
      rw [smul_smul, this, mul_smul]
      exact algebraMap_smul_mem S n e

noncomputable def basisK {ι : Type*} (S : Subalgebra R A) (b : Module.Basis ι R S)
    (hspan : Submodule.span K (S : Set A) = ⊤) : Module.Basis ι K A :=
  Module.Basis.mk (v := fun i => ((b i : S) : A))
    (by
      have hR : LinearIndependent R (fun i => ((b i : S) : A)) :=
        b.linearIndependent.map' S.val.toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
      exact (LinearIndependent.iff_fractionRing R K).mp hR)
    (by
      rw [← hspan, Submodule.span_le]
      intro s hs
      have h1 : (⟨s, hs⟩ : S) ∈ Submodule.span R (Set.range b) := b.mem_span _
      have h2 : s ∈ (Submodule.span R (Set.range b)).map S.val.toLinearMap := ⟨⟨s, hs⟩, h1, rfl⟩
      rw [Submodule.map_span] at h2
      have h3 : S.val.toLinearMap '' Set.range b = Set.range (fun i => ((b i : S) : A)) := by
        ext x
        simp only [Set.mem_image, Set.mem_range]
        constructor
        · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩; exact ⟨b i, ⟨i, rfl⟩, rfl⟩
      rw [h3] at h2
      exact Submodule.span_le_restrictScalars R K _ h2)

omit [IsDomain R] in
@[scoped simp] lemma basisK_apply {ι : Type*} (S : Subalgebra R A) (b : Module.Basis ι R S)
    (hspan : Submodule.span K (S : Set A) = ⊤) (i : ι) : basisK S b hspan i = ((b i : S) : A) :=
  Module.Basis.mk_apply _ _ i

omit [IsDomain R] in

lemma basisK_repr_coe {ι : Type*} (S : Subalgebra R A) (b : Module.Basis ι R S)
    (hspan : Submodule.span K (S : Set A) = ⊤) (s : S) (i : ι) :
    (basisK S b hspan).repr (s : A) i = algebraMap R K (b.repr s i) := by
  classical
  let φ₁ : S →ₗ[R] K := (((basisK S b hspan).coord i).restrictScalars R) ∘ₗ S.val.toLinearMap
  let φ₂ : S →ₗ[R] K := (Algebra.linearMap R K) ∘ₗ (b.coord i)
  have h : φ₁ = φ₂ := by
    refine b.ext fun k => ?_
    have e1 : φ₁ (b k) = (basisK S b hspan).repr (basisK S b hspan k) i := by
      simp [φ₁, basisK_apply]
    have e2 : φ₂ (b k) = algebraMap R K (b.repr (b k) i) := by
      simp [φ₂]
    rw [e1, e2, Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp
  exact congrArg (fun φ : S →ₗ[R] K => φ s) h

lemma basisK_repr_eq_zero_of_mem {ι : Type*} (S : Subalgebra R A) (b : Module.Basis ι R S)
    (hspan : Submodule.span K (S : Set A) = ⊤) (V : Submodule K A) (T : Set ι)
    (hV : ∀ s : S, (s : A) ∈ V → ∀ i, i ∉ T → b.repr s i = 0)
    {a : A} (ha : a ∈ V) {i : ι} (hi : i ∉ T) : (basisK S b hspan).repr a i = 0 := by
  obtain ⟨r, hr, hmem⟩ := exists_nonzero_smul_mem S hspan a
  have h1 : b.repr ⟨_, hmem⟩ i = 0 := hV ⟨_, hmem⟩ (V.smul_mem _ ha) i hi
  have h2 : (basisK S b hspan).repr (algebraMap R K r • a) i = 0 := by
    have h := basisK_repr_coe S b hspan ⟨_, hmem⟩ i
    rw [h1, map_zero] at h
    exact h
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_eq_zero] at h2
  exact h2.resolve_left (algebraMap_ne_zero (K := K) hr)

lemma exists_adapted_basis [IsPrincipalIdealRing R] (S : Subalgebra R A) [Module.Finite R S]
    (V : Submodule K A) :
    ∃ (m n : ℕ) (b : Module.Basis (Fin m) R S) (f : Fin n ↪ Fin m),
      (∀ k, ((b (f k) : S) : A) ∈ V) ∧
      (∀ s : S, (s : A) ∈ V → ∀ i, i ∉ Set.range f → b.repr s i = 0) := by
  classical
  haveI : Module.Free R S := free_of_finite (K := K) S
  let b₀ : Module.Basis (Fin _) R S := (Module.Free.chooseBasis R S).reindex (Fintype.equivFin _)
  let N : Submodule R S := (V.restrictScalars R).comap S.val.toLinearMap
  have hN : ∀ s : S, s ∈ N ↔ (s : A) ∈ V := fun s => Iff.rfl
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm b₀ N
  refine ⟨_, n, snf.bM, snf.f, fun k => ?_,
    fun s hs i hi => snf.repr_eq_zero_of_notMem_range ⟨s, (hN s).mpr hs⟩ hi⟩
  have h1 : ((snf.bN k : N) : S) = snf.a k • snf.bM (snf.f k) := snf.snf k
  have hak : snf.a k ≠ 0 := by
    intro h0
    apply snf.bN.ne_zero k
    rw [← Submodule.coe_eq_zero, h1, h0, zero_smul]
  have hmem : ((snf.a k • snf.bM (snf.f k) : S) : A) ∈ V := by
    rw [← h1]; exact (hN _).mp (snf.bN k).2
  rw [Subalgebra.coe_smul, ← IsScalarTower.algebraMap_smul K (snf.a k)] at hmem
  have h2 := V.smul_mem (algebraMap R K (snf.a k))⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ (algebraMap_ne_zero (K := K) hak), one_smul] at h2

omit [IsDomain R] [IsFractionRing R K] in

lemma tensor_repr_eq_zero {ι : Type*} {M : Type*} [AddCommGroup M] [Module K M]
    (B : Module.Basis ι K A) (g : M →ₗ[K] A) (T : Set ι)
    (hg : ∀ m : M, ∀ i, i ∉ T → B.repr (g m) i = 0)
    (w : M ⊗[K] M) (p : ι × ι) (hp : p.1 ∉ T ∨ p.2 ∉ T) :
    (B.tensorProduct B).repr (TensorProduct.map g g w) p = 0 := by
  obtain ⟨i, j⟩ := p
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [TensorProduct.map_tmul, Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
      rcases hp with h | h
      · rw [hg x _ h, mul_zero]
      · rw [hg y _ h, zero_mul]
  | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, Finsupp.add_apply, h₁, h₂, add_zero]

omit [IsDomain R] [IsFractionRing R K] in

lemma eq_sum_of_repr_eq_zero {M : Type*} [AddCommGroup M] [Module R M] {m n : ℕ}
    (b : Module.Basis (Fin m) R M) (f : Fin n ↪ Fin m) (t : M ⊗[R] M)
    (hvan : ∀ p : Fin m × Fin m, (p.1 ∉ Set.range f ∨ p.2 ∉ Set.range f) →
      (b.tensorProduct b).repr t p = 0) :
    t = ∑ q : Fin n × Fin n,
      (b.tensorProduct b).repr t (f q.1, f q.2) • (b (f q.1) ⊗ₜ[R] b (f q.2)) := by
  classical
  have hz : ∀ p ∈ (Finset.univ : Finset (Fin m × Fin m)), p ∉ Finset.univ.map (f.prodMap f) →
      (b.tensorProduct b).repr t p • (b.tensorProduct b) p = 0 := by
    intro p _ hp
    rw [hvan p ?_, zero_smul]
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := hcon
    exact hp (Finset.mem_map.mpr ⟨(k, l), Finset.mem_univ _, Prod.ext hk hl⟩)
  calc t = ∑ p, (b.tensorProduct b).repr t p • (b.tensorProduct b) p := ((b.tensorProduct b).sum_repr t).symm
    _ = ∑ p ∈ Finset.univ.map (f.prodMap f), (b.tensorProduct b).repr t p • (b.tensorProduct b) p :=
        (Finset.sum_subset (Finset.subset_univ _) hz).symm
    _ = _ := by
        rw [Finset.sum_map]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Function.Embedding.coe_prodMap, Prod.map_apply, Module.Basis.tensorProduct_apply]

omit [IsDomain R] in

lemma repr_tensorSqHom {ι : Type*} (S : Subalgebra R A) (b : Module.Basis ι R S)
    (hspan : Submodule.span K (S : Set A) = ⊤) (t : S ⊗[R] S) (p : ι × ι) :
    ((basisK S b hspan).tensorProduct (basisK S b hspan)).repr (tensorSqHom (K := K) S t) p
      = algebraMap R K ((b.tensorProduct b).repr t p) := by
  obtain ⟨i, j⟩ := p
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul s s' =>
      rw [tensorSqHom_tmul, Module.Basis.tensorProduct_repr_tmul_apply,
        Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, smul_eq_mul, map_mul,
        basisK_repr_coe, basisK_repr_coe]
  | add t₁ t₂ h₁ h₂ =>
      rw [map_add, map_add, Finsupp.add_apply, h₁, h₂, map_add, Finsupp.add_apply, map_add]

end HopfOrder.KerAux
p2m_reactivate "P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder.Aux P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder.KerAux"
p2m_reactivate "P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder.Aux"

namespace HopfOrder
namespace KerHopf
open HopfOrder.Aux HopfOrder.KerAux

theorem comul_mem_range_comap
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    [Coalgebra.IsCocomm K A]
    (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈ (tensorSqHom (K := K) S).range)
    (π : A →ₐc[K] Ā) (c : ↥(HopfAlgebra.hopfKer π)) (hc : (c : A) ∈ S) :
    Coalgebra.comul (R := K) c ∈
      (tensorSqHom (K := K) (S.comap (((HopfAlgebra.hopfKer π).val :
        ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))).range := by
  classical

  obtain ⟨m, n, b, f, hgood, hvanS⟩ :=
    exists_adapted_basis (K := K) S (Subalgebra.toSubmodule (HopfAlgebra.hopfKer π))

  obtain ⟨bK, hbKrepr, hbKvan⟩ : ∃ bK : Module.Basis (Fin m) K A,
      (∀ (t : ↥S ⊗[R] ↥S) (p : Fin m × Fin m),
        (bK.tensorProduct bK).repr (tensorSqHom (K := K) S t) p
          = algebraMap R K ((b.tensorProduct b).repr t p)) ∧
      (∀ (a : ↥(HopfAlgebra.hopfKer π)) (i : Fin m), i ∉ Set.range f → bK.repr (a : A) i = 0) :=
    ⟨basisK S b hspan, repr_tensorSqHom S b hspan, fun a i hi =>
      basisK_repr_eq_zero_of_mem S b hspan (Subalgebra.toSubmodule (HopfAlgebra.hopfKer π))
        (Set.range f) hvanS a.2 hi⟩

  obtain ⟨t, ht⟩ : ∃ t, tensorSqHom (K := K) S t = Coalgebra.comul (R := K) (c : A) :=
    (AlgHom.mem_range _).mp (hcomul _ hc)
  have hvv : TensorProduct.map
      ((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).toLinearMap
      ((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).toLinearMap
        (Coalgebra.comul (R := K) c) = Coalgebra.comul (R := K) (c : A) :=
    HopfAlgebra.map_val_val_comul π c

  have hvanT : ∀ p : Fin m × Fin m, (p.1 ∉ Set.range f ∨ p.2 ∉ Set.range f) →
      (b.tensorProduct b).repr t p = 0 := by
    intro p hp
    have h := hbKrepr t p
    rw [ht, ← hvv, tensor_repr_eq_zero bK _ (Set.range f) (fun x i hi => hbKvan x i hi) _ p hp] at h
    exact (injective_iff_map_eq_zero (algebraMap R K)).mp (IsFractionRing.injective R K) _ h.symm
  have ht_eq := eq_sum_of_repr_eq_zero b f t hvanT

  let γ : Fin n → ↥(S.comap (((HopfAlgebra.hopfKer π).val :
      ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)) :=
    fun k => ⟨⟨((b (f k) : ↥S) : A), hgood k⟩, (Subalgebra.mem_comap _ _ _).mpr (b (f k)).2⟩
  refine (AlgHom.mem_range _).mpr
    ⟨∑ q : Fin n × Fin n, (b.tensorProduct b).repr t (f q.1, f q.2) • (γ q.1 ⊗ₜ[R] γ q.2), ?_⟩

  have hinj : Function.Injective (TensorProduct.map
      ((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).toLinearMap
      ((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).toLinearMap) := by
    have h := HopfAlgebra.HopfKerHopf.ι₂_injective π
    rwa [HopfAlgebra.HopfKerHopf.ι₂_eq_map] at h
  apply hinj
  calc _ = ∑ q : Fin n × Fin n, (b.tensorProduct b).repr t (f q.1, f q.2) •
            ((((γ q.1 : ↥(HopfAlgebra.hopfKer π)) : A)) ⊗ₜ[K] (((γ q.2 : ↥(HopfAlgebra.hopfKer π)) : A))) :=
        map_val_tensorSqHom_sum_smul_tmul S (HopfAlgebra.hopfKer π) γ _
    _ = tensorSqHom (K := K) S (∑ q : Fin n × Fin n,
          (b.tensorProduct b).repr t (f q.1, f q.2) • (b (f q.1) ⊗ₜ[R] b (f q.2))) :=
        (tensorSqHom_sum_smul_tmul S (fun k => b (f k)) _).symm
    _ = tensorSqHom (K := K) S t := by rw [← ht_eq]
    _ = Coalgebra.comul (R := K) (c : A) := ht
    _ = _ := hvv.symm

end HopfOrder.KerHopf
p2m_reactivate "P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder.Aux P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder.KerAux"
p2m_reactivate "P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder.Aux P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.HopfOrder.KerAux"

open HopfOrder.Aux HopfOrder.KerAux in
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    [Coalgebra.IsCocomm K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S)
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (π : A →ₐc[K] Ā) :
    Module.Finite R ↥((S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))) ∧
    Submodule.span K (((S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)) : Subalgebra R ↥(HopfAlgebra.hopfKer π)) : Set ↥(HopfAlgebra.hopfKer π)) = ⊤ ∧
    (∀ x ∈ (S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)), Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : ↥(HopfAlgebra.hopfKer π) →ₐ[K] ↥(HopfAlgebra.hopfKer π) ⊗[K] ↥(HopfAlgebra.hopfKer π)).restrictScalars R).comp ((S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))).val)
          (((Algebra.TensorProduct.includeRight : ↥(HopfAlgebra.hopfKer π) →ₐ[K] ↥(HopfAlgebra.hopfKer π) ⊗[K] ↥(HopfAlgebra.hopfKer π)).restrictScalars R).comp ((S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))).val)).range) ∧
    (∀ x ∈ (S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)), HopfAlgebra.antipode K (A := ↥(HopfAlgebra.hopfKer π)) x ∈ (S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))) ∧
    (∀ x ∈ (S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)), Coalgebra.counit (R := K) (A := ↥(HopfAlgebra.hopfKer π)) x ∈ (algebraMap R K).range) := by
  have hinjK : ∀ {r : R}, r ≠ 0 → algebraMap R K r ≠ 0 := fun hr => algebraMap_ne_zero (K := K) hr
  have hmemC : ∀ (x : ↥(HopfAlgebra.hopfKer π)),
      x ∈ S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)
        ↔ (x : A) ∈ S := fun x => Subalgebra.mem_comap _ _ _
  haveI := hfin
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    let j : ↥(S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))
        →ₗ[R] ↥S :=
      { toFun := fun c => ⟨((c : ↥(HopfAlgebra.hopfKer π)) : A), (hmemC _).mp c.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hj : Function.Injective j := by
      intro c d h
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun s : ↥S => (s : A)) h
    exact Module.Finite.of_injective j hj
  ·
    refine Submodule.eq_top_iff'.mpr fun a => ?_
    obtain ⟨r, hr, hmem⟩ := exists_nonzero_smul_mem S hspan (a : A)
    have hx : (algebraMap R K r • a) ∈
        S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R) := by
      rw [hmemC, Subalgebra.coe_smul]; exact hmem
    have : a = (algebraMap R K r)⁻¹ • (algebraMap R K r • a) := by
      rw [smul_smul, inv_mul_cancel₀ (hinjK hr), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
  ·
    intro c hc
    exact HopfOrder.KerHopf.comul_mem_range_comap S hspan hcomul π c ((hmemC c).mp hc)
  ·
    intro c hc
    rw [hmemC] at hc ⊢
    rw [HopfAlgebra.coe_antipode]
    exact hanti _ hc
  ·
    intro c hc
    rw [HopfAlgebra.counit_coe]
    exact hcounit _ ((hmemC c).mp hc)

end S_HopfOrder_isHopfOrder_comap_hopfKer
end P2MW
export P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer (solution)
