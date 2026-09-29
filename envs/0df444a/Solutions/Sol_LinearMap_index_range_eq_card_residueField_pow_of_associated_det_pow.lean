-- Prove2me | solution 1 for LinearMap.index_range_eq_card_residueField_pow_of_associated_det_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/8bc867b3-f90e-5bd2-a2cd-403fff6b8e3e

import Mathlib
import Theorems.Thm_LinearMap_exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_index_range_eq_card_residueField_pow_of_associated_det_pow

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace R4IdxRange

section DVR

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

abbrev spanSub (x : R) : AddSubgroup R := (Ideal.span {x} : Ideal R).toAddSubgroup

theorem mem_spanSub {x y : R} : y ∈ spanSub x ↔ x ∣ y := by
  change y ∈ (Ideal.span {x} : Ideal R) ↔ _
  exact Ideal.mem_span_singleton

theorem spanSub_eq_of_associated {x y : R} (h : Associated x y) : spanSub x = spanSub y := by
  change (Ideal.span {x} : Ideal R).toAddSubgroup = (Ideal.span {y} : Ideal R).toAddSubgroup
  rw [Ideal.span_singleton_eq_span_singleton.2 h]

theorem card_residueField_eq_index {ϖ : R} (hϖ : Irreducible ϖ) :
    Nat.card (IsLocalRing.ResidueField R) = (spanSub ϖ).index := by
  have h : (spanSub ϖ).index = Submodule.cardQuot (IsLocalRing.maximalIdeal R) := by
    rw [Irreducible.maximalIdeal_eq hϖ]; rfl
  rw [h, Submodule.cardQuot_apply]
  rfl

theorem map_mulLeft_spanSub (r x : R) : AddSubgroup.map (AddMonoidHom.mulLeft r) (spanSub x) = spanSub (r * x) := by
  ext y
  simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft, mem_spanSub]
  constructor
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, by ring⟩
  · rintro ⟨w, rfl⟩
    exact ⟨x * w, ⟨w, rfl⟩, by ring⟩

theorem map_mulLeft_top (r : R) : AddSubgroup.map (AddMonoidHom.mulLeft r) ⊤ = spanSub r := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, AddMonoidHom.coe_mulLeft, mem_spanSub]
  constructor
  · rintro ⟨z, rfl⟩; exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩; exact ⟨z, rfl⟩

theorem ker_mulLeft {r : R} (hr : r ≠ 0) : (AddMonoidHom.mulLeft r).ker = ⊥ := by
  rw [AddMonoidHom.ker_eq_bot_iff]
  intro a b h
  exact mul_left_cancel₀ hr h

theorem relIndex_spanSub_pow_succ {ϖ : R} (hϖ : Irreducible ϖ) (k : ℕ) :
    (spanSub (ϖ ^ (k + 1))).relIndex (spanSub (ϖ ^ k)) = Nat.card (IsLocalRing.ResidueField R) := by
  have hk : (ϖ ^ k : R) ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have h1 : spanSub (ϖ ^ (k + 1)) = AddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ k)) (spanSub ϖ) := by
    rw [map_mulLeft_spanSub, pow_succ]
  have h2 : spanSub (ϖ ^ k) = AddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ k)) (⊤ : AddSubgroup R) := by
    rw [map_mulLeft_top]
  rw [h1, h2, AddSubgroup.relIndex_map_map, ker_mulLeft hk, sup_bot_eq, sup_bot_eq, AddSubgroup.relIndex_top_right,
    card_residueField_eq_index hϖ]

theorem index_spanSub_pow {ϖ : R} (hϖ : Irreducible ϖ) (k : ℕ) :
    (spanSub (ϖ ^ k)).index = Nat.card (IsLocalRing.ResidueField R) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, AddSubgroup.index_eq_one]
    ext y
    simp
  | succ k ih =>
    have hle : spanSub (ϖ ^ (k + 1)) ≤ spanSub (ϖ ^ k) := fun y hy => by
      rw [mem_spanSub] at hy ⊢
      exact (pow_dvd_pow ϖ (Nat.le_succ k)).trans hy
    rw [← AddSubgroup.relIndex_mul_index hle, relIndex_spanSub_pow_succ hϖ, ih, pow_succ, mul_comm]

end DVR

section Coordinates

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {n : ℕ}

theorem repr_apply_of_diag (b b' : Module.Basis (Fin n) R M) (f : M →ₗ[R] M) (a : Fin n → R)
    (hfb : ∀ i, f (b i) = a i • b' i) (x : M) (i : Fin n) : b'.repr (f x) i = b.repr x i * a i := by
  have hx : f x = ∑ j, (b.repr x j * a j) • b' j := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hfb, smul_smul]
  rw [hx, b'.repr_sum_self]

theorem mem_range_iff_of_diag (b b' : Module.Basis (Fin n) R M) (f : M →ₗ[R] M) (a : Fin n → R)
    (hfb : ∀ i, f (b i) = a i • b' i) (x : M) : x ∈ LinearMap.range f ↔ ∀ i, a i ∣ b'.repr x i := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨b.repr y i, by rw [repr_apply_of_diag b b' f a hfb, mul_comm]⟩
  · intro h
    choose d hd using h
    refine ⟨∑ i, d i • b i, ?_⟩
    apply b'.ext_elem
    intro i
    rw [repr_apply_of_diag b b' f a hfb, b.repr_sum_self, hd i, mul_comm]

end Coordinates

section Main

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
  (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

theorem main (f : M →ₗ[R] M) (hf : Function.Injective f)
    (ϖ : R) (hϖ : Irreducible ϖ) (m : ℕ) (hdet : Associated (LinearMap.det f) (ϖ ^ m)) :
    (LinearMap.range f).toAddSubgroup.index = Nat.card (IsLocalRing.ResidueField R) ^ m := by
  classical
  set q : ℕ := Nat.card (IsLocalRing.ResidueField R) with hq

  obtain ⟨n, b, b', a, S, hfb, -, -⟩ :=
    LinearMap.exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le R M f hf
      (Module.finrank (IsLocalRing.ResidueField R) (LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R))))
      le_rfl

  have ha0 : ∀ i, a i ≠ 0 := by
    intro i h0
    have : f (b i) = 0 := by rw [hfb, h0, zero_smul]
    exact b.ne_zero i (hf (by rw [this, map_zero]))
  choose e he using fun i => IsDiscreteValuationRing.associated_pow_irreducible (ha0 i) hϖ

  have hdet' : Associated (LinearMap.det f) (∏ i, a i) := by
    have hdiag : LinearMap.toMatrix b b' f = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hfb, map_smul, b'.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
        Matrix.diagonal_apply]
      by_cases h : j = i
      · subst h; simp
      · rw [if_neg h, if_neg (Ne.symm h), smul_zero]
    have hcomp : LinearMap.toMatrix b b f = LinearMap.toMatrix b' b LinearMap.id * LinearMap.toMatrix b b' f := by
      rw [← LinearMap.toMatrix_comp b b' b LinearMap.id f, LinearMap.id_comp]
    have hunitP : IsUnit (LinearMap.toMatrix b' b (LinearMap.id : M →ₗ[R] M)).det := by
      rw [LinearMap.toMatrix_id_eq_basis_toMatrix]
      haveI := Module.Basis.invertibleToMatrix b b'
      exact (Matrix.isUnit_det_of_invertible _)
    obtain ⟨u, hu⟩ := hunitP
    rw [← LinearMap.det_toMatrix b, hcomp, Matrix.det_mul, hdiag, Matrix.det_diagonal, ← hu]
    exact ⟨u⁻¹, by rw [mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩
  have hprod : Associated (∏ i, a i) (ϖ ^ ∑ i, e i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Associated.prod _ (fun i => a i) (fun i => ϖ ^ e i) fun i _ => he i
  have hsum : ∑ i, e i = m := by
    have h1 : Associated (ϖ ^ ∑ i, e i) (ϖ ^ m) := (hdet'.trans hprod).symm.trans hdet
    have h2 : ϖ ^ (∑ i, e i) ∣ ϖ ^ m := h1.dvd
    have h3 : ϖ ^ m ∣ ϖ ^ (∑ i, e i) := h1.symm.dvd
    have := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h2
    have := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h3
    omega

  set φ : M →+ (Fin n → R) := (b'.equivFun : M ≃ₗ[R] (Fin n → R)).toLinearMap.toAddMonoidHom with hφ
  have hφ_apply : ∀ x i, φ x i = b'.repr x i := fun x i => by simp [hφ, Module.Basis.equivFun_apply]
  have hφ_surj : Function.Surjective φ := fun y => ⟨b'.equivFun.symm y, by
    change b'.equivFun (b'.equivFun.symm y) = y; exact LinearEquiv.apply_symm_apply _ _⟩
  set Kpi : AddSubgroup (Fin n → R) := AddSubgroup.pi Set.univ fun i => spanSub (a i) with hKpi
  have hK : (LinearMap.range f).toAddSubgroup = Kpi.comap φ := by
    ext x
    rw [Submodule.mem_toAddSubgroup, mem_range_iff_of_diag b b' f a hfb, AddSubgroup.mem_comap, hKpi,
      AddSubgroup.mem_pi]
    simp only [Set.mem_univ, forall_const, mem_spanSub, hφ_apply]

  have hKidx : Kpi.index = ∏ i : Fin n, q ^ e i := by
    rw [hKpi, AddSubgroup.index_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [spanSub_eq_of_associated (he i)]
    exact index_spanSub_pow hϖ (e i)
  rw [hK, AddSubgroup.index_comap_of_surjective _ hφ_surj, hKidx, Finset.prod_pow_eq_pow_sum, hsum]

end Main

end R4IdxRange

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (hf : Function.Injective f)
    (ϖ : R) (hϖ : Irreducible ϖ) (m : ℕ) (hdet : Associated (LinearMap.det f) (ϖ ^ m)) :
    (LinearMap.range f).toAddSubgroup.index = Nat.card (IsLocalRing.ResidueField R) ^ m :=
  R4IdxRange.main R M f hf ϖ hϖ m hdet

end S_LinearMap_index_range_eq_card_residueField_pow_of_associated_det_pow
end P2MW
export P2MW.S_LinearMap_index_range_eq_card_residueField_pow_of_associated_det_pow (solution)
