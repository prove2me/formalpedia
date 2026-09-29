-- Prove2me | solution 1 for HopfAlgebra.isHopfGalois_of_isCocomm_of_finiteType_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a5dd50b3-6055-5381-8f25-2f68d2960642

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isHopfGalois_of_isCocomm_of_finiteType_of_surjective

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra
open Set Set.powersetCard

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk sum_antipode_mul_eq_smul sum_mul_antipode_eq_smul coaction coaction_apply hopfKer mem_hopfKer_iff IsHopfGalois isHopfGalois_iff_ker_le_span_of_surjective"
namespace TorsorField
p2m_open "HopfAlgebra"

section Compound

variable {S : Type*} [CommRing S] {N : ℕ} (d : ℕ)

noncomputable abbrev emb (s : powersetCard (Fin N) d) : Fin d ↪o Fin N := ofFinEmbEquiv.symm s

noncomputable def minor (X : Matrix (Fin N) (Fin N) S) (s t : powersetCard (Fin N) d) : S :=
  (X.submatrix (emb d s) (emb d t)).det

noncomputable def compound (X : Matrix (Fin N) (Fin N) S) :
    Matrix (powersetCard (Fin N) d) (powersetCard (Fin N) d) S :=
  Matrix.of fun s t => minor d X s t

theorem compound_apply (X : Matrix (Fin N) (Fin N) S) (s t : powersetCard (Fin N) d) :
    compound d X s t = (X.submatrix (emb d s) (emb d t)).det := rfl

theorem compound_eq_toMatrix (X : Matrix (Fin N) (Fin N) S) :
    compound d X = LinearMap.toMatrix ((Pi.basisFun S (Fin N)).exteriorPower d)
      ((Pi.basisFun S (Fin N)).exteriorPower d) (exteriorPower.map d (Matrix.toLin' X)) := by
  ext s t
  rw [LinearMap.toMatrix_apply, exteriorPower.coe_basis, exteriorPower.map_apply_ιMulti_family,
    exteriorPower.basis_repr_apply, exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti,
    compound_apply, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply, Pi.basisFun_apply,
    Matrix.toLin'_apply, Pi.basisFun_repr]

theorem compound_mul (X Y : Matrix (Fin N) (Fin N) S) :
    compound d (X * Y) = compound d X * compound d Y := by
  let B := (Pi.basisFun S (Fin N)).exteriorPower d
  rw [compound_eq_toMatrix, compound_eq_toMatrix, compound_eq_toMatrix, Matrix.toLin'_mul,
    exteriorPower.map_comp, LinearMap.toMatrix_comp B B B]

theorem compound_one : compound d (1 : Matrix (Fin N) (Fin N) S) = 1 := by
  rw [compound_eq_toMatrix, Matrix.toLin'_one, exteriorPower.map_id, LinearMap.toMatrix_id]

theorem compound_map {S' : Type*} [CommRing S'] (f : S →+* S') (X : Matrix (Fin N) (Fin N) S) :
    compound d (X.map f) = (compound d X).map f := by
  ext s t
  simp only [compound_apply, Matrix.map_apply, Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]

end Compound

section LineTrick

variable {S : Type*} [CommRing S] {d m : ℕ}

noncomputable def low (d m : ℕ) : powersetCard (Fin (d + m)) d := ofFinEmbEquiv (Fin.castAddOrderEmb m)

theorem emb_low : emb d (low d m) = Fin.castAddOrderEmb m := by
  simp [emb, low]

theorem emb_low_apply (j : Fin d) : emb d (low d m) j = Fin.castAdd m j := by
  rw [emb_low]; rfl

theorem mem_low_iff (x : Fin (d + m)) : x ∈ low d m ↔ ∃ j : Fin d, Fin.castAdd m j = x := by
  simp [low, mem_ofFinEmbEquiv_iff_mem_range]

theorem castAdd_ne_natAdd (j : Fin d) (i : Fin m) : Fin.castAdd m j ≠ Fin.natAdd d i := by
  intro h
  have := congrArg Fin.val h
  simp [Fin.val_natAdd] at this
  omega

theorem natAdd_not_mem_low (i : Fin m) : Fin.natAdd d i ∉ low d m := by
  rw [mem_low_iff]
  rintro ⟨j, hj⟩
  exact castAdd_ne_natAdd j i hj

theorem exists_natAdd_mem_of_ne_low {s : powersetCard (Fin (d + m)) d} (hs : s ≠ low d m) :
    ∃ l : Fin d, ∃ i : Fin m, emb d s l = Fin.natAdd d i := by
  obtain ⟨x, hxs, hxl⟩ := (exists_mem_notMem_iff_ne s (low d m)).mp hs
  obtain ⟨l, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s x).mpr hxs
  refine ⟨l, ?_⟩
  induction hx : (ofFinEmbEquiv.symm s l) using Fin.addCases with
  | left j => exact absurd ((mem_low_iff _).mpr ⟨j, rfl⟩) (hx ▸ hxl)
  | right i => exact ⟨i, rfl⟩

theorem det_submatrix_eq_zero_iff_minor {M : ℕ} (X : Matrix (Fin M) (Fin M) S) (σ : Fin d ↪ Fin M)
    (t : powersetCard (Fin M) d) :
    (X.submatrix σ (emb d t)).det = 0 ↔ minor d X (ofFinEmb d (Fin M) σ) t = 0 := by
  set s : powersetCard (Fin M) d := ofFinEmb d (Fin M) σ
  have hmem : ∀ j, σ j ∈ Set.range (emb d s) := fun j => by
    rw [mem_range_ofFinEmbEquiv_symm_iff_mem, mem_ofFinEmb_iff_mem_range]
    exact ⟨j, rfl⟩
  choose τ hτ using hmem
  have hτinj : Function.Injective τ := fun j j' h => σ.injective (by rw [← hτ j, ← hτ j', h])
  let e : Equiv.Perm (Fin d) := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj)
  have hX : X.submatrix σ (emb d t) = (X.submatrix (emb d s) (emb d t)).submatrix e id := by
    ext i j
    simp [Matrix.submatrix_apply, e, hτ]
  rw [hX, ← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.det_permute', Matrix.det_transpose, minor]
  constructor
  · intro h
    have hu : IsUnit ((Equiv.Perm.sign e : ℤ) : S) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h1 | h1 <;> simp [h1]
    exact (hu.mul_right_eq_zero).mp h
  · intro h; rw [h, mul_zero]

theorem lowerLeft_eq_zero (X : Matrix (Fin (d + m)) (Fin (d + m)) S)
    (hunit : IsUnit (minor d X (low d m) (low d m)))
    (hzero : ∀ s, s ≠ low d m → minor d X s (low d m) = 0) (i : Fin m) (j : Fin d) :
    X (Fin.natAdd d i) (Fin.castAdd m j) = 0 := by

  set T : Matrix (Fin d) (Fin d) S := X.submatrix (Fin.castAdd m) (Fin.castAdd m) with hT
  set v : Fin d → S := fun j => X (Fin.natAdd d i) (Fin.castAdd m j) with hv
  have hdetT : T.det = minor d X (low d m) (low d m) := by
    simp only [minor, hT]
    congr 1
    ext a b
    simp [emb_low_apply]

  have hcr : T.transpose.cramer v = 0 := by
    ext l
    rw [Matrix.cramer_transpose_apply, Pi.zero_apply]
    let σ' : Fin d → Fin (d + m) := Function.update (Fin.castAdd m) l (Fin.natAdd d i)
    have hσ'inj : Function.Injective σ' := by
      intro a b hab
      simp only [σ'] at hab
      rcases eq_or_ne a l with ha | ha <;> rcases eq_or_ne b l with hb | hb
      · rw [ha, hb]
      · rw [ha, Function.update_self, Function.update_of_ne hb] at hab
        exact absurd hab.symm (castAdd_ne_natAdd b i)
      · rw [hb, Function.update_self, Function.update_of_ne ha] at hab
        exact absurd hab (castAdd_ne_natAdd a i)
      · rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab
        exact Fin.castAdd_injective _ _ hab
    let σ : Fin d ↪ Fin (d + m) := ⟨σ', hσ'inj⟩
    have hupd : T.updateRow l v = X.submatrix σ (emb d (low d m)) := by
      ext a b
      simp only [Matrix.updateRow_apply, hT, hv, Matrix.submatrix_apply, emb_low_apply, σ,
        Function.Embedding.coeFn_mk, σ']
      split_ifs with h
      · subst h; rw [Function.update_self]
      · rw [Function.update_of_ne h]
    rw [hupd, det_submatrix_eq_zero_iff_minor]
    apply hzero
    intro hs
    have : Fin.natAdd d i ∈ (ofFinEmb d (Fin (d + m)) σ) :=
      (mem_ofFinEmb_iff_mem_range _ _ _ _).mpr ⟨l, by simp [σ, σ']⟩
    rw [hs] at this
    exact natAdd_not_mem_low i this
  have h := Matrix.mulVec_cramer T.transpose v
  rw [hcr, Matrix.mulVec_zero, Matrix.det_transpose] at h
  have hv0 : v = 0 := by
    have := congrArg (fun w => (hdetT ▸ hunit).unit⁻¹.val • w) h
    simp only [smul_zero, smul_smul, IsUnit.val_inv_mul, one_smul] at this
    exact this.symm
  exact congrFun hv0 j

end LineTrick

section Extract

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  {M : Type*} [AddCommGroup M] [Module k M] {ι : Type*} [Fintype ι]

omit [Fintype ι] in

theorem exists_dual_eq_ite [DecidableEq ι] {e : ι → V} (he : LinearIndependent k e) (i : ι) :
    ∃ φ : V →ₗ[k] k, ∀ j, φ (e j) = if j = i then 1 else 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((Finsupp.lapply i).comp (he.repr : _ →ₗ[k] ι →₀ k))
  refine ⟨g, fun j => ?_⟩
  have hmem : e j ∈ Submodule.span k (Set.range e) := Submodule.subset_span ⟨j, rfl⟩
  have := LinearMap.congr_fun hg ⟨e j, hmem⟩
  simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply] at this
  rw [this, he.repr_eq_single j ⟨e j, hmem⟩ rfl, Finsupp.lapply_apply, Finsupp.single_apply]

theorem eq_of_sum_tmul_eq {e : ι → V} (he : LinearIndependent k e) {X Y : ι → M}
    (h : ∑ i, e i ⊗ₜ[k] X i = ∑ i, e i ⊗ₜ[k] Y i) : X = Y := by
  classical
  funext i
  obtain ⟨φ, hφ⟩ := exists_dual_eq_ite he i
  have key := congrArg (fun z => TensorProduct.lid k M (LinearMap.rTensor M φ z)) h
  simp only [map_sum, LinearMap.rTensor_tmul, hφ, TensorProduct.lid_tmul, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at key
  exact key

end Extract

section LocalFiniteness

variable {k : Type*} [Field k] {A : Type*} [AddCommGroup A] [Module k A] [Coalgebra k A]

def cotens (V : Submodule k A) : Submodule k (A ⊗[k] A) :=
  Submodule.span k {z | ∃ v ∈ V, ∃ a : A, z = v ⊗ₜ[k] a}

omit [Coalgebra k A] in
theorem tmul_mem_cotens {V : Submodule k A} {v : A} (hv : v ∈ V) (a : A) : v ⊗ₜ[k] a ∈ cotens V :=
  Submodule.subset_span ⟨v, hv, a, rfl⟩

omit [Coalgebra k A] in
theorem cotens_mono {V W : Submodule k A} (h : V ≤ W) : cotens V ≤ cotens W :=
  Submodule.span_mono fun _ ⟨v, hv, a, hz⟩ => ⟨v, h hv, a, hz⟩

def IsSubcomod (V : Submodule k A) : Prop := ∀ v ∈ V, comul (R := k) v ∈ cotens V

theorem isSubcomod_bot : IsSubcomod (⊥ : Submodule k A) := fun v hv => by
  rw [(Submodule.mem_bot k).mp hv, map_zero]; exact zero_mem _

theorem IsSubcomod.sup {V W : Submodule k A} (hV : IsSubcomod V) (hW : IsSubcomod W) : IsSubcomod (V ⊔ W) := by
  intro v hv
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  exact add_mem (cotens_mono le_sup_left (hV x hx)) (cotens_mono le_sup_right (hW y hy))

theorem isSubcomod_finset_sup {β : Type*} (s : Finset β) (V : β → Submodule k A) (h : ∀ b ∈ s, IsSubcomod (V b)) :
    IsSubcomod (s.sup V) :=
  Finset.sup_induction isSubcomod_bot (fun _ h₁ _ h₂ => h₁.sup h₂) h

theorem exists_finiteDimensional_isSubcomod (x : A) :
    ∃ V : Submodule k A, FiniteDimensional k V ∧ IsSubcomod V ∧ x ∈ V := by
  classical
  let β := Module.Free.chooseBasis k A
  let ιβ := Module.Free.ChooseBasisIndex k A

  let Φ : A ⊗[k] A ≃ₗ[k] (ιβ →₀ A) :=
    (TensorProduct.congr (LinearEquiv.refl k A) β.repr).trans (TensorProduct.finsuppScalarRight k k A ιβ)
  have hΦsymm : ∀ (t : ιβ) (a : A), Φ.symm (Finsupp.single t a) = a ⊗ₜ[k] β t := by
    intro t a
    simp only [Φ, LinearEquiv.trans_symm, LinearEquiv.trans_apply, TensorProduct.finsuppScalarRight_symm_apply_single,
      TensorProduct.congr_symm_tmul, LinearEquiv.refl_symm, LinearEquiv.refl_apply, Module.Basis.repr_symm_single,
      one_smul]

  have hexp : ∀ z : A ⊗[k] A, z = ∑ t ∈ (Φ z).support, (Φ z t) ⊗ₜ[k] β t := by
    intro z
    conv_lhs => rw [← Φ.symm_apply_apply z, ← Finsupp.sum_single (Φ z)]
    rw [Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun t _ => hΦsymm t _
  let F := Φ (comul (R := k) x)
  let V : Submodule k A := Submodule.span k (F '' (F.support : Set ιβ))
  have hFmem : ∀ t ∈ F.support, F t ∈ V := fun t ht => Submodule.subset_span ⟨t, ht, rfl⟩
  refine ⟨V, FiniteDimensional.span_of_finite k ((F.support.finite_toSet).image _), ?_, ?_⟩
  ·

    let κ : ιβ → (A ⊗[k] A) ⊗[k] A →ₗ[k] A ⊗[k] A := fun t =>
      (TensorProduct.rid k (A ⊗[k] A)).toLinearMap ∘ₗ LinearMap.lTensor (A ⊗[k] A) (β.coord t)
    have hκ : ∀ t (w : A ⊗[k] A) (a : A), κ t (w ⊗ₜ[k] a) = (β.coord t a) • w := by
      intro t w a; simp [κ]
    have hgen : ∀ t ∈ F.support, comul (R := k) (F t) ∈ cotens V := by
      intro t ht
      have h1 : κ t (comul.rTensor A (comul (R := k) x)) = comul (F t) := by
        conv_lhs => rw [hexp (comul (R := k) x)]
        simp only [map_sum, LinearMap.rTensor_tmul, hκ, Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_apply]
        simp only [ite_smul, one_smul, zero_smul]
        rw [Finset.sum_ite_eq' F.support t, if_pos ht]
      have h2 : κ t ((TensorProduct.assoc k A A A).symm (comul.lTensor A (comul (R := k) x))) ∈ cotens V := by
        conv => arg 2; rw [hexp (comul (R := k) x)]
        simp only [map_sum, LinearMap.lTensor_tmul]
        refine Submodule.sum_mem _ fun s hs => ?_
        rw [hexp (comul (R := k) (β s)), TensorProduct.tmul_sum, map_sum, map_sum]
        refine Submodule.sum_mem _ fun r _ => ?_
        rw [TensorProduct.assoc_symm_tmul, hκ]
        exact Submodule.smul_mem _ _ (tmul_mem_cotens (hFmem s hs) _)
      rw [Coalgebra.coassoc_symm_apply] at h2
      rwa [h1] at h2
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨t, ht, rfl⟩ := hv
      exact hgen t ht
    | zero => rw [map_zero]; exact zero_mem _
    | add v w _ _ hv hw => rw [map_add]; exact add_mem hv hw
    | smul r v _ hv => rw [map_smul]; exact Submodule.smul_mem _ _ hv
  ·
    have h := Coalgebra.lTensor_counit_comul (R := k) x
    rw [hexp (comul (R := k) x), map_sum] at h
    simp only [LinearMap.lTensor_tmul] at h
    have h' := congrArg (TensorProduct.rid k A) h
    rw [map_sum, TensorProduct.rid_tmul, one_smul] at h'
    rw [← h']
    refine Submodule.sum_mem _ fun t ht => ?_
    rw [TensorProduct.rid_tmul]
    exact Submodule.smul_mem _ _ (hFmem t ht)

theorem exists_matrix_of_isSubcomod {V : Submodule k A} (hV : IsSubcomod V) {n : ℕ}
    (b : Module.Basis (Fin n) k V) :
    ∃ a : Matrix (Fin n) (Fin n) A, ∀ j, comul (R := k) (b j : A) = ∑ i, (b i : A) ⊗ₜ[k] a i j := by
  have key : ∀ z ∈ cotens V, ∃ f : Fin n → A, z = ∑ i, (b i : A) ⊗ₜ[k] f i := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, hv, a, rfl⟩ := hz
      refine ⟨fun i => b.repr ⟨v, hv⟩ i • a, ?_⟩
      have hv' : v = ∑ i, b.repr ⟨v, hv⟩ i • (b i : A) := by
        have h := congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)
        rw [Submodule.coe_sum] at h
        simp only [Submodule.coe_smul] at h
        exact h.symm
      conv_lhs => rw [hv', TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun i _ => by rw [TensorProduct.smul_tmul]
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨f, rfl⟩ := hz
      obtain ⟨g, rfl⟩ := hw
      exact ⟨f + g, by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
    | smul r z _ hz =>
      obtain ⟨f, rfl⟩ := hz
      exact ⟨r • f, by simp [Finset.smul_sum, TensorProduct.tmul_smul]⟩
  choose f hf using key
  exact ⟨Matrix.of fun i j => f _ (hV _ (b j).2) i, fun j => by
    simpa only [Matrix.of_apply] using hf _ (hV _ (b j).2)⟩

end LocalFiniteness

section MulMatrix

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A]

structure IsMulMatrix [Bialgebra R A] {ι : Type*} [Fintype ι] [DecidableEq ι] (c : Matrix ι ι A) : Prop where
  comul_eq : ∀ i j, comul (R := R) (c i j) = ∑ x, c i x ⊗ₜ[R] c x j
  counit_eq : ∀ i j, counit (R := R) (c i j) = (1 : Matrix ι ι R) i j

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section field

variable {k : Type*} [Field k] [Bialgebra k A]

theorem isMulMatrix_of_basis {e : ι → A} (he : LinearIndependent k e) (a : Matrix ι ι A)
    (ha : ∀ j, comul (R := k) (e j) = ∑ i, e i ⊗ₜ[k] a i j) : IsMulMatrix (R := k) a := by
  constructor
  · intro l j

    have h1 : comul.lTensor A (comul (R := k) (e j)) = ∑ i, e i ⊗ₜ[k] comul (R := k) (a i j) := by
      rw [ha, map_sum]; simp only [LinearMap.lTensor_tmul]
    have h2 : TensorProduct.assoc k A A A (comul.rTensor A (comul (R := k) (e j)))
        = ∑ i, e i ⊗ₜ[k] (∑ x, a i x ⊗ₜ[k] a x j) := by
      rw [ha, map_sum, map_sum]
      simp only [LinearMap.rTensor_tmul, ha, TensorProduct.sum_tmul, map_sum, TensorProduct.assoc_tmul]
      rw [Finset.sum_comm]
      simp only [TensorProduct.tmul_sum]
    rw [Coalgebra.coassoc_apply, h1] at h2
    exact congrFun (eq_of_sum_tmul_eq he h2) l
  · intro l j
    have h1 : counit.lTensor A (comul (R := k) (e j)) = ∑ i, e i ⊗ₜ[k] counit (R := k) (a i j) := by
      rw [ha, map_sum]; simp only [LinearMap.lTensor_tmul]
    have h2 : (e j ⊗ₜ[k] (1 : k)) = ∑ i, e i ⊗ₜ[k] (1 : Matrix ι ι k) i j := by
      simp only [Matrix.one_apply, TensorProduct.tmul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Coalgebra.lTensor_counit_comul, h2] at h1
    exact (congrFun (eq_of_sum_tmul_eq he h1) l).symm

end field

variable [HopfAlgebra R A]

noncomputable def IsMulMatrix.repr {c : Matrix ι ι A} (hc : IsMulMatrix (R := R) c) (i j : ι) :
    Coalgebra.Repr R (c i j) ι where
  index := Finset.univ
  left := fun x => c i x
  right := fun x => c x j
  eq := (hc.comul_eq i j).symm

theorem IsMulMatrix.mul_map_antipode {c : Matrix ι ι A} (hc : IsMulMatrix (R := R) c) :
    c * c.map (antipode R) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have := sum_mul_antipode_eq_smul (hc.repr i j)
  simp only [IsMulMatrix.repr] at this
  simp only [Matrix.map_apply, this, hc.counit_eq, Matrix.one_apply, ite_smul, one_smul, zero_smul]

theorem IsMulMatrix.map_antipode_mul {c : Matrix ι ι A} (hc : IsMulMatrix (R := R) c) :
    c.map (antipode R) * c = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have := sum_antipode_mul_eq_smul (hc.repr i j)
  simp only [IsMulMatrix.repr] at this
  simp only [Matrix.map_apply, this, hc.counit_eq, Matrix.one_apply, ite_smul, one_smul, zero_smul]

theorem map_includeLeft_mul_map_includeRight {B : Type*} [CommRing B] [Algebra R B] {κ μ : Type*} [Fintype κ]
    (c : Matrix μ κ A) (d : Matrix κ μ B) (i j : μ) :
    (c.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) *
      d.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)) i j = ∑ x, c i x ⊗ₜ[R] d x j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem map_includeRight_mul_map_includeLeft {B : Type*} [CommRing B] [Algebra R B] {κ μ : Type*} [Fintype κ]
    (d : Matrix μ κ B) (c : Matrix κ μ A) (i j : μ) :
    (d.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) *
      c.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)) i j = ∑ x, c x j ⊗ₜ[R] d i x := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem IsMulMatrix.map_comul {c : Matrix ι ι A} (hc : IsMulMatrix (R := R) c) :
    c.map (Bialgebra.comulAlgHom R A) =
      c.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A) *
        c.map (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) := by
  ext i j
  rw [map_includeLeft_mul_map_includeRight, Matrix.map_apply, Bialgebra.comulAlgHom_apply, hc.comul_eq]

theorem IsMulMatrix.map_counit {c : Matrix ι ι A} (hc : IsMulMatrix (R := R) c) :
    c.map (Bialgebra.counitAlgHom R A) = 1 := by
  ext i j
  rw [Matrix.map_apply, Bialgebra.counitAlgHom_apply, hc.counit_eq]

theorem isMulMatrix_iff (c : Matrix ι ι A) :
    IsMulMatrix (R := R) c ↔
      c.map (Bialgebra.comulAlgHom R A) =
        c.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A) *
          c.map (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) ∧
      c.map (Bialgebra.counitAlgHom R A) = 1 := by
  constructor
  · exact fun hc => ⟨hc.map_comul, hc.map_counit⟩
  · rintro ⟨h1, h2⟩
    constructor
    · intro i j
      have := congrFun (congrFun h1 i) j
      rwa [map_includeLeft_mul_map_includeRight, Matrix.map_apply, Bialgebra.comulAlgHom_apply] at this
    · intro i j
      have := congrFun (congrFun h2 i) j
      rwa [Matrix.map_apply, Bialgebra.counitAlgHom_apply] at this

end MulMatrix

end HopfAlgebra.TorsorField

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk sum_antipode_mul_eq_smul sum_mul_antipode_eq_smul coaction coaction_apply hopfKer mem_hopfKer_iff IsHopfGalois isHopfGalois_iff_ker_le_span_of_surjective"
namespace TorsorField
p2m_open "HopfAlgebra"

section Chevalley

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A]
  {B : Type*} [CommRing B] [Bialgebra k B] (π : A →ₐc[k] B)

theorem exists_chevalley_data :
    ∃ (d m : ℕ) (e : Fin (d + m) → A) (a : Matrix (Fin (d + m)) (Fin (d + m)) A),
      LinearIndependent k e ∧ (∀ j, comul (R := k) (e j) = ∑ i, e i ⊗ₜ[k] a i j) ∧
      (∀ i j, π (a (Fin.natAdd d i) (Fin.castAdd m j)) = 0) ∧
      RingHom.ker (π : A →ₐ[k] B) ≤
        Ideal.span (Set.range fun p : Fin m × Fin d => a (Fin.natAdd d p.1) (Fin.castAdd m p.2)) := by
  classical

  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨G, hG⟩ : (RingHom.ker (π : A →ₐ[k] B)).FG := IsNoetherian.noetherian _

  choose Vx hVfd hVsub hxV using fun x : A => exists_finiteDimensional_isSubcomod (k := k) x
  let V : Submodule k A := G.sup Vx
  haveI : ∀ x, FiniteDimensional k (Vx x) := hVfd
  haveI : FiniteDimensional k V := Submodule.finiteDimensional_finset_sup G Vx
  have hVsubc : IsSubcomod V := isSubcomod_finset_sup G Vx fun x _ => hVsub x
  have hGV : ∀ x ∈ G, x ∈ V := fun x hx => (Finset.le_sup hx : Vx x ≤ V) (hxV x)

  let W : Submodule k V := Submodule.comap V.subtype ((RingHom.ker (π : A →ₐ[k] B)).restrictScalars k)
  have hWmem : ∀ v : V, v ∈ W ↔ π (v : A) = 0 := fun v => Iff.rfl
  obtain ⟨C, hWC⟩ := W.exists_isCompl
  haveI : Module.Free k ↥W := Module.Free.of_divisionRing k ↥W
  haveI : Module.Free k ↥C := Module.Free.of_divisionRing k ↥C
  obtain ⟨d, bW⟩ : (d : ℕ) × Module.Basis (Fin d) k W := ⟨_, Module.finBasis k W⟩
  obtain ⟨m, bC⟩ : (m : ℕ) × Module.Basis (Fin m) k C := ⟨_, Module.finBasis k C⟩
  let bV : Module.Basis (Fin (d + m)) k V :=
    ((bW.prod bC).map (Submodule.prodEquivOfIsCompl W C hWC)).reindex finSumFinEquiv
  have hbV_cast : ∀ j, bV (Fin.castAdd m j) = (bW j : V) := by
    intro j
    simp [bV, Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.prod_apply,
      Submodule.coe_prodEquivOfIsCompl']
  have hbV_nat : ∀ i, bV (Fin.natAdd d i) = (bC i : V) := by
    intro i
    simp [bV, Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.prod_apply,
      Submodule.coe_prodEquivOfIsCompl']
  have he : LinearIndependent k fun i => (bV i : A) := bV.linearIndependent.map' V.subtype V.ker_subtype
  obtain ⟨a, ha⟩ := exists_matrix_of_isSubcomod hVsubc bV

  have hπe : ∀ j, π (bV (Fin.castAdd m j) : A) = 0 := by
    intro j
    rw [← hWmem, hbV_cast]
    exact (bW j).2
  have hεe : ∀ j, counit (R := k) (bV (Fin.castAdd m j) : A) = 0 := by
    intro j
    rw [← CoalgHomClass.counit_comp_apply π, hπe, map_zero]
  refine ⟨d, m, fun i => (bV i : A), a, he, ha, ?_, ?_⟩
  ·
    intro i j
    have hind : LinearIndependent k fun i => π (bV (Fin.natAdd d i) : A) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg

      let u : V := ∑ i, g i • bV (Fin.natAdd d i)
      have huC : u ∈ C := Submodule.sum_mem _ fun i _ => by
        rw [hbV_nat]; exact Submodule.smul_mem _ _ (bC i).2
      have huW : u ∈ W := by
        rw [hWmem]
        have : ((u : V) : A) = ∑ i, g i • (bV (Fin.natAdd d i) : A) := by
          simp only [u, Submodule.coe_sum, Submodule.coe_smul]
        rw [this, map_sum]
        simpa only [map_smul] using hg
      have hu0 : u = 0 := by
        have := Submodule.mem_inf.mpr ⟨huW, huC⟩
        rwa [hWC.inf_eq_bot, Submodule.mem_bot] at this
      have hu' : ∑ i, g i • bC i = 0 := by
        apply Subtype.val_injective
        rw [Submodule.coe_sum]
        simp only [Submodule.coe_smul, ← hbV_nat]
        exact hu0
      exact fun i => Fintype.linearIndependent_iff.mp bC.linearIndependent g hu' i
    have h1 := CoalgHomClass.map_comp_comul_apply π (bV (Fin.castAdd m j) : A)
    rw [hπe, map_zero, ha, map_sum] at h1
    simp only [TensorProduct.map_tmul] at h1
    rw [Fin.sum_univ_add] at h1
    simp only [BialgHom.coe_toLinearMap, hπe, TensorProduct.zero_tmul, Finset.sum_const_zero, zero_add] at h1
    have h2 : ∑ x, π (bV (Fin.natAdd d x) : A) ⊗ₜ[k] π (a (Fin.natAdd d x) (Fin.castAdd m j))
        = ∑ x, π (bV (Fin.natAdd d x) : A) ⊗ₜ[k] (0 : B) := by
      rw [h1]; simp
    exact congrFun (eq_of_sum_tmul_eq hind h2) i
  ·
    rw [← hG, Ideal.span_le]
    intro x hx
    have hxI : x ∈ RingHom.ker (π : A →ₐ[k] B) := by rw [← hG]; exact Ideal.subset_span hx
    have hxW : (⟨x, hGV x hx⟩ : V) ∈ W := hxI

    have hxe : x = ∑ j, bW.repr ⟨_, hxW⟩ j • (bV (Fin.castAdd m j) : A) := by
      have h := congrArg (fun w : W => ((w : V) : A)) (bW.sum_repr ⟨_, hxW⟩)
      dsimp only at h
      rw [Submodule.coe_sum, Submodule.coe_sum] at h
      simp only [Submodule.coe_smul, ← hbV_cast] at h
      exact h.symm
    rw [SetLike.mem_coe, hxe]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ ?_

    have h := Coalgebra.rTensor_counit_comul (R := k) (bV (Fin.castAdd m j) : A)
    rw [ha, map_sum] at h
    simp only [LinearMap.rTensor_tmul] at h
    have h' := congrArg (TensorProduct.lid k A) h
    rw [map_sum, TensorProduct.lid_tmul, one_smul] at h'
    simp only [TensorProduct.lid_tmul] at h'
    rw [← h', Fin.sum_univ_add]
    simp only [hεe, zero_smul, Finset.sum_const_zero, zero_add]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Ideal.subset_span ⟨(i, j), rfl⟩)

end Chevalley

section Weights

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [HopfAlgebra k A]
  {B : Type*} [CommRing B] [Bialgebra k B] (π : A →ₐc[k] B)
  {P : Type*} [Fintype P] [DecidableEq P] {c c' : Matrix P P A} {s₀ : P}

theorem inv_col (hc'c : c' * c = 1) (hcol : ∀ u, u ≠ s₀ → π (c u s₀) = 0) (t : P) :
    π (c' t s₀) * π (c s₀ s₀) = (1 : Matrix P P B) t s₀ := by
  have h := congrArg π (congrFun (congrFun hc'c t) s₀)
  rw [Matrix.mul_apply, map_sum] at h
  simp only [map_mul] at h
  rw [Finset.sum_eq_single s₀ (fun u _ hu => by rw [hcol u hu, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)] at h
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]

theorem chi'_mul_chi (hc'c : c' * c = 1) (hcol : ∀ u, u ≠ s₀ → π (c u s₀) = 0) :
    π (c' s₀ s₀) * π (c s₀ s₀) = 1 := by
  rw [inv_col π hc'c hcol, Matrix.one_apply_eq]

theorem chi_mul_chi' (hc'c : c' * c = 1) (hcol : ∀ u, u ≠ s₀ → π (c u s₀) = 0) :
    π (c s₀ s₀) * π (c' s₀ s₀) = 1 := by
  rw [mul_comm, chi'_mul_chi π hc'c hcol]

theorem inv_col_eq_zero (hc'c : c' * c = 1) (hcol : ∀ u, u ≠ s₀ → π (c u s₀) = 0) (t : P) (ht : t ≠ s₀) :
    π (c' t s₀) = 0 := by
  have h := inv_col π hc'c hcol t
  rw [Matrix.one_apply_ne ht] at h
  calc π (c' t s₀) = π (c' t s₀) * π (c s₀ s₀) * π (c' s₀ s₀) := by rw [mul_assoc, chi_mul_chi' π hc'c hcol, mul_one]
    _ = 0 := by rw [h, zero_mul]

theorem coaction_col (hc : IsMulMatrix (R := k) c) (hcol : ∀ u, u ≠ s₀ → π (c u s₀) = 0) (s : P) :
    coaction π (c s s₀) = c s s₀ ⊗ₜ[k] π (c s₀ s₀) := by
  rw [coaction_apply, hc.comul_eq, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  rw [Finset.sum_eq_single s₀ (fun u _ hu => ?_) (fun h => absurd (Finset.mem_univ _) h)]
  · rfl
  · change c s u ⊗ₜ[k] π (c u s₀) = 0
    rw [hcol u hu, TensorProduct.tmul_zero]

variable [Coalgebra.IsCocomm k A]

theorem map_coaction_eq (hc : IsMulMatrix (R := k) c) :
    c.map (coaction π) = (c.map π).map (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B) *
      c.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B) := by
  ext s t
  rw [map_includeRight_mul_map_includeLeft, Matrix.map_apply, coaction_apply, ← Coalgebra.comm_comul,
    hc.comul_eq, map_sum, map_sum]
  simp only [TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Matrix.map_apply]
  rfl

theorem map_coaction_inv_eq (hc : IsMulMatrix (R := k) c) (hcc' : c * c' = 1) (hc'c : c' * c = 1) :
    c'.map (coaction π) = c'.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B) *
      (c'.map π).map (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B) := by
  set inL : A →ₐ[k] A ⊗[k] B := Algebra.TensorProduct.includeLeft
  set inR : B →ₐ[k] A ⊗[k] B := Algebra.TensorProduct.includeRight
  set ρ : A →ₐ[k] A ⊗[k] B := coaction π
  have h1 : c.map ρ * c'.map ρ = 1 := by
    rw [← Matrix.map_mul, hcc', Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  have hππ : (c'.map π).map inR * (c.map π).map inR = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hc'c, Matrix.map_one _ (map_zero π) (map_one π),
      Matrix.map_one _ (map_zero inR) (map_one inR)]
  have h2 : (c'.map inL * (c'.map π).map inR) * c.map ρ = 1 := by
    rw [map_coaction_eq π hc, Matrix.mul_assoc, ← Matrix.mul_assoc ((c'.map π).map inR), hππ, Matrix.one_mul,
      ← Matrix.map_mul, hc'c, Matrix.map_one _ (map_zero inL) (map_one inL)]
  calc c'.map ρ = (c'.map inL * (c'.map π).map inR) * c.map ρ * c'.map ρ := by rw [h2, Matrix.one_mul]
    _ = c'.map inL * (c'.map π).map inR := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem coaction_inv_col (hc : IsMulMatrix (R := k) c) (hcc' : c * c' = 1) (hc'c : c' * c = 1)
    (hcol : ∀ u, u ≠ s₀ → π (c u s₀) = 0) (t : P) :
    coaction π (c' t s₀) = c' t s₀ ⊗ₜ[k] π (c' s₀ s₀) := by
  have h := congrFun (congrFun (map_coaction_inv_eq π hc hcc' hc'c) t) s₀
  rw [Matrix.map_apply, map_includeLeft_mul_map_includeRight,
    Finset.sum_eq_single s₀ (fun u _ hu => ?_) (fun h => absurd (Finset.mem_univ _) h)] at h
  · exact h
  · rw [Matrix.map_apply, inv_col_eq_zero π hc'c hcol u hu, TensorProduct.tmul_zero]

theorem col_mul_inv_sub_mem (hc : IsMulMatrix (R := k) c) (hcc' : c * c' = 1) (hc'c : c' * c = 1)
    (hcol : ∀ u, u ≠ s₀ → π (c u s₀) = 0) (s : P) :
    c s s₀ * c' s₀ s₀ - algebraMap k A ((1 : Matrix P P k) s s₀) ∈
      {a : A | a ∈ hopfKer π ∧ counit (R := k) a = 0} := by
  constructor
  · refine sub_mem ?_ (Subalgebra.algebraMap_mem _ _)
    rw [mem_hopfKer_iff, map_mul, coaction_col π hc hcol, coaction_inv_col π hc hcc' hc'c hcol,
      Algebra.TensorProduct.tmul_mul_tmul, chi_mul_chi' π hc'c hcol]
  · have hc'ε : c'.map (Bialgebra.counitAlgHom k A) = 1 := by
      have h : c'.map (Bialgebra.counitAlgHom k A) * c.map (Bialgebra.counitAlgHom k A) = 1 := by
        rw [← Matrix.map_mul, hc'c, Matrix.map_one _ (map_zero _) (map_one _)]
      rwa [hc.map_counit, Matrix.mul_one] at h
    have h := congrFun (congrFun hc'ε s₀) s₀
    rw [Matrix.map_apply, Matrix.one_apply_eq, Bialgebra.counitAlgHom_apply] at h
    change counit (R := k) (c s s₀ * c' s₀ s₀ - algebraMap k A ((1 : Matrix P P k) s s₀)) = 0
    rw [map_sub, ← Bialgebra.counitAlgHom_apply, map_mul, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      hc.counit_eq, h, mul_one, Bialgebra.counit_algebraMap, sub_self]

end Weights

section Main

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A]
  [Coalgebra.IsCocomm k A] {B : Type*} [CommRing B] [Bialgebra k B] (π : A →ₐc[k] B)

open Set Set.powersetCard

omit [Algebra.FiniteType k A] [Coalgebra.IsCocomm k A] in
theorem compound_map_algHom {S' : Type*} [CommRing S'] [Algebra k S'] (f : A →ₐ[k] S') {N : ℕ} (d : ℕ)
    (X : Matrix (Fin N) (Fin N) A) : compound d (X.map f) = (compound d X).map f :=
  compound_map d (f : A →+* S') X

theorem ker_le_span_augIdeal_hopfKer :
    RingHom.ker (π : A →ₐ[k] B) ≤ Ideal.span {a : A | a ∈ hopfKer π ∧ counit (R := k) a = 0} := by
  classical
  obtain ⟨d, m, e, a, he, ha, hπa, hIle⟩ := exists_chevalley_data π
  have hmul : IsMulMatrix (R := k) a := isMulMatrix_of_basis he a ha

  set c : Matrix (powersetCard (Fin (d + m)) d) (powersetCard (Fin (d + m)) d) A := compound d a with hcdef
  set c' : Matrix (powersetCard (Fin (d + m)) d) (powersetCard (Fin (d + m)) d) A :=
    compound d (a.map (antipode k)) with hc'def
  have hc : IsMulMatrix (R := k) c := by
    rw [isMulMatrix_iff, hcdef]
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← compound_map_algHom, hmul.map_comul, compound_mul]
      rw [compound_map_algHom, compound_map_algHom]
    · rw [← compound_map_algHom, hmul.map_counit, compound_one]
  have hcc' : c * c' = 1 := by
    rw [hcdef, hc'def, ← compound_mul, hmul.mul_map_antipode, compound_one]
  have hc'c : c' * c = 1 := by
    rw [hcdef, hc'def, ← compound_mul, hmul.map_antipode_mul, compound_one]

  have hcol : ∀ u, u ≠ low d m → π (c u (low d m)) = 0 := by
    intro u hu
    obtain ⟨l, i, hl⟩ := exists_natAdd_mem_of_ne_low hu
    rw [hcdef, compound_apply]
    change (π : A →ₐ[k] B) (Matrix.det _) = 0
    rw [AlgHom.map_det]
    apply Matrix.det_eq_zero_of_row_eq_zero l
    intro j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, hl, emb_low_apply,
      BialgHom.coe_toAlgHom]
    exact hπa i j

  let z : powersetCard (Fin (d + m)) d → A := fun s =>
    c s (low d m) * c' (low d m) (low d m) - algebraMap k A ((1 : Matrix _ _ k) s (low d m))
  have hz : ∀ s, z s ∈ {a : A | a ∈ hopfKer π ∧ counit (R := k) a = 0} := fun s =>
    col_mul_inv_sub_mem π hc hcc' hc'c hcol s
  let 𝔞 : Ideal A := Ideal.span (Set.range z)
  refine le_trans ?_ (Ideal.span_mono (Set.range_subset_iff.mpr hz) : 𝔞 ≤ _)
  refine le_trans hIle (Ideal.span_le.mpr ?_)
  rintro _ ⟨⟨i, j⟩, rfl⟩
  rw [SetLike.mem_coe, ← Ideal.Quotient.eq_zero_iff_mem]

  set g : A →+* A ⧸ 𝔞 := Ideal.Quotient.mk 𝔞 with hgdef
  have hg : ∀ s, g (c s (low d m)) * g (c' (low d m) (low d m)) = (1 : Matrix _ _ (A ⧸ 𝔞)) s (low d m) := by
    intro s
    have h0 : g (z s) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨s, rfl⟩)
    change g (c s (low d m) * c' (low d m) (low d m) - algebraMap k A ((1 : Matrix _ _ k) s (low d m))) = 0 at h0
    rw [map_sub, sub_eq_zero, map_mul] at h0
    rw [h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rw [map_one, map_one]
    · rw [map_zero, map_zero]
  have hunit : IsUnit (g (c (low d m) (low d m))) :=
    IsUnit.of_mul_eq_one (g (c' (low d m) (low d m))) (by rw [hg, Matrix.one_apply_eq])
  have hunit' : IsUnit (g (c' (low d m) (low d m))) :=
    IsUnit.of_mul_eq_one (g (c (low d m) (low d m))) (by rw [mul_comm, hg, Matrix.one_apply_eq])
  have hzero : ∀ s, s ≠ low d m → g (c s (low d m)) = 0 := by
    intro s hs
    have h := hg s
    rw [Matrix.one_apply_ne hs] at h
    exact (hunit'.mul_left_eq_zero).mp h
  have hminor : ∀ s, minor d (a.map g) s (low d m) = g (c s (low d m)) := by
    intro s
    change compound d (a.map g) s (low d m) = g (compound d a s (low d m))
    rw [compound_map, Matrix.map_apply]
  have := lowerLeft_eq_zero (a.map g) (by rw [hminor]; exact hunit)
    (fun s hs => by rw [hminor]; exact hzero s hs) i j
  rwa [Matrix.map_apply] at this

end Main

end HopfAlgebra.TorsorField

open HopfAlgebra.TorsorField in

theorem solution
    (k : Type) [Field k]
    (H : Type) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [Coalgebra.IsCocomm k H]
    (H' : Type) [CommRing H'] [HopfAlgebra k H']
    (qc : H →ₐc[k] H') (hqc : Function.Surjective qc) :
    HopfAlgebra.IsHopfGalois qc :=
  (HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective qc hqc).mpr (ker_le_span_augIdeal_hopfKer qc)

end S_HopfAlgebra_isHopfGalois_of_isCocomm_of_finiteType_of_surjective
end P2MW
export P2MW.S_HopfAlgebra_isHopfGalois_of_isCocomm_of_finiteType_of_surjective (solution)
