-- Prove2me | solution 1 for LinearMap.relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/06ed0827-44e2-5220-a94a-f0d532cb5666

import Mathlib
import Theorems.Thm_LinearMap_exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct

namespace P2mCorankShells

section DVR

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

abbrev spanSub (x : R) : AddSubgroup R := (Ideal.span {x} : Ideal R).toAddSubgroup

theorem mem_spanSub {x y : R} : y ∈ spanSub x ↔ x ∣ y := by
  change y ∈ (Ideal.span {x} : Ideal R) ↔ _
  exact Ideal.mem_span_singleton

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

theorem pow_dvd_mul_iff {ϖ : R} (hϖ : Irreducible ϖ) {a : R} {e : ℕ} (ha : Associated a (ϖ ^ e)) (s : ℕ) (c : R) :
    ϖ ^ s ∣ c * a ↔ ϖ ^ (s - e) ∣ c := by
  rw [(Associated.mul_left c ha).dvd_iff_dvd_right]
  rcases le_or_gt e s with h | h
  · conv_lhs => rw [show s = (s - e) + e by omega, pow_add]
    exact mul_dvd_mul_iff_right (pow_ne_zero _ hϖ.ne_zero)
  · rw [Nat.sub_eq_zero_of_le h.le, pow_zero]
    simp only [one_dvd, iff_true]
    exact (pow_dvd_pow ϖ h.le).trans (dvd_mul_left _ _)

end DVR

section Coordinates

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {n : ℕ}

theorem mem_smul_top_iff (b : Module.Basis (Fin n) R M) (r : R) (x : M) :
    x ∈ (Ideal.span {r} • ⊤ : Submodule R M) ↔ ∀ i, r ∣ b.repr x i := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩ i
    exact ⟨b.repr y i, by rw [map_smul, Finsupp.smul_apply, smul_eq_mul]⟩
  · intro h
    choose d hd using h
    refine ⟨∑ i, d i • b i, Submodule.mem_top, ?_⟩
    rw [Finset.smul_sum]
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← hd i]

theorem repr_apply_of_diag (b b' : Module.Basis (Fin n) R M) (f : M →ₗ[R] M) (a : Fin n → R)
    (hfb : ∀ i, f (b i) = a i • b' i) (x : M) (i : Fin n) : b'.repr (f x) i = b.repr x i * a i := by
  have hx : f x = ∑ j, (b.repr x j * a j) • b' j := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hfb, smul_smul]
  rw [hx, b'.repr_sum_self]

end Coordinates

section Main

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
  (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

theorem card_residueField_pos : 0 < Nat.card (IsLocalRing.ResidueField R) := Nat.card_pos

theorem main (f : M →ₗ[R] M) (hf : Function.Injective f)
    (hker : Module.finrank (IsLocalRing.ResidueField R)
        (LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R))) ≤ 1)
    (ϖ : R) (hϖ : Irreducible ϖ) (m : ℕ) (hdet : Associated (LinearMap.det f) (ϖ ^ m)) (s : ℕ) :
    ((Ideal.span {ϖ ^ s} • ⊤ : Submodule R M).toAddSubgroup).relIndex
        (((Ideal.span {ϖ ^ s} • ⊤ : Submodule R M).comap f).toAddSubgroup) =
      Nat.card (IsLocalRing.ResidueField R) ^ min s m := by
  classical
  set q : ℕ := Nat.card (IsLocalRing.ResidueField R) with hq
  have hqpos : 0 < q := card_residueField_pos R

  obtain ⟨n, b, b', a, S, hfb, hunit, hS⟩ :=
    LinearMap.exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le R M f hf 1 hker

  have ha0 : ∀ i, a i ≠ 0 := by
    intro i h0
    have : f (b i) = 0 := by rw [hfb, h0, zero_smul]
    exact b.ne_zero i (hf (by rw [this, map_zero]))
  choose e he using fun i => IsDiscreteValuationRing.associated_pow_irreducible (ha0 i) hϖ

  have he0 : ∀ i, i ∉ S → e i = 0 := by
    intro i hi
    have hu : IsUnit (ϖ ^ e i) := (he i).isUnit (hunit i hi)
    by_contra hne
    exact hϖ.not_isUnit ((isUnit_pow_iff hne).1 hu)

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

  have hmin : ∏ i, q ^ min s (e i) = q ^ min s m := by
    rcases S.eq_empty_or_nonempty with hS0 | ⟨i₀, hi₀⟩
    · have he0' : ∀ i, e i = 0 := fun i => he0 i (by rw [hS0]; exact Finset.notMem_empty i)
      have hm0 : m = 0 := by rw [← hsum]; exact Finset.sum_eq_zero fun i _ => he0' i
      rw [hm0]
      simp [he0']
    · have hS1 : ∀ i ∈ S, i = i₀ := fun i hi => Finset.card_le_one.1 hS i hi i₀ hi₀
      have he0' : ∀ i, i ≠ i₀ → e i = 0 := fun i hi => he0 i fun h => hi (hS1 i h)
      have hm0 : e i₀ = m := by
        rw [← hsum, Finset.sum_eq_single i₀ (fun i _ hi => he0' i hi) (fun h => absurd (Finset.mem_univ _) h)]
      rw [Finset.prod_eq_single i₀ (fun i _ hi => by rw [he0' i hi, Nat.min_zero, pow_zero])
        (fun h => absurd (Finset.mem_univ _) h), hm0]

  set φ : M →+ (Fin n → R) := (b.equivFun : M ≃ₗ[R] (Fin n → R)).toLinearMap.toAddMonoidHom with hφ
  have hφ_apply : ∀ x i, φ x i = b.repr x i := fun x i => by simp [hφ, Module.Basis.equivFun_apply]
  have hφ_surj : Function.Surjective φ := fun y => ⟨b.equivFun.symm y, by
    change b.equivFun (b.equivFun.symm y) = y; exact LinearEquiv.apply_symm_apply _ _⟩
  set Hpi : AddSubgroup (Fin n → R) := AddSubgroup.pi Set.univ fun _ => spanSub (ϖ ^ s) with hHpi
  set Kpi : AddSubgroup (Fin n → R) := AddSubgroup.pi Set.univ fun i => spanSub (ϖ ^ (s - e i)) with hKpi
  have hH : ((Ideal.span {ϖ ^ s} • ⊤ : Submodule R M).toAddSubgroup) = Hpi.comap φ := by
    ext x
    rw [Submodule.mem_toAddSubgroup, mem_smul_top_iff b, AddSubgroup.mem_comap, hHpi, AddSubgroup.mem_pi]
    simp only [Set.mem_univ, forall_const, mem_spanSub, hφ_apply]
  have hK : (((Ideal.span {ϖ ^ s} • ⊤ : Submodule R M).comap f).toAddSubgroup) = Kpi.comap φ := by
    ext x
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_comap, mem_smul_top_iff b', AddSubgroup.mem_comap, hKpi,
      AddSubgroup.mem_pi]
    simp only [Set.mem_univ, forall_const, mem_spanSub, hφ_apply, repr_apply_of_diag b b' f a hfb]
    exact forall_congr' fun i => pow_dvd_mul_iff hϖ (he i) s _
  have hle : Hpi ≤ Kpi := by
    intro y hy
    rw [hHpi, AddSubgroup.mem_pi] at hy
    rw [hKpi, AddSubgroup.mem_pi]
    intro i hi
    have := hy i hi
    rw [mem_spanSub] at this ⊢
    exact (pow_dvd_pow ϖ (Nat.sub_le s (e i))).trans this

  have hHidx : Hpi.index = ∏ _i : Fin n, q ^ s := by
    rw [hHpi, AddSubgroup.index_pi]
    exact Finset.prod_congr rfl fun i _ => index_spanSub_pow hϖ s
  have hKidx : Kpi.index = ∏ i : Fin n, q ^ (s - e i) := by
    rw [hKpi, AddSubgroup.index_pi]
    exact Finset.prod_congr rfl fun i _ => index_spanSub_pow hϖ (s - e i)
  have hKpos : 0 < ∏ i : Fin n, q ^ (s - e i) := Finset.prod_pos fun i _ => pow_pos hqpos _
  have hrel : Hpi.relIndex Kpi = ∏ i, q ^ min s (e i) := by
    have hmul := AddSubgroup.relIndex_mul_index hle
    rw [hHidx, hKidx] at hmul
    have hsplit : (∏ i : Fin n, q ^ min s (e i)) * ∏ i : Fin n, q ^ (s - e i) = ∏ _i : Fin n, q ^ s := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add]
      congr 1
      omega
    rw [← hsplit] at hmul
    exact Nat.eq_of_mul_eq_mul_right hKpos hmul
  rw [hH, hK, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hφ_surj, hrel, hmin]

end Main

end P2mCorankShells

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (hf : Function.Injective f)
    (hker : Module.finrank (IsLocalRing.ResidueField R)
        (LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R))) ≤ 1)
    (ϖ : R) (hϖ : Irreducible ϖ) (m : ℕ) (hdet : Associated (LinearMap.det f) (ϖ ^ m)) (s : ℕ) :
    ((Ideal.span {ϖ ^ s} • ⊤ : Submodule R M).toAddSubgroup).relIndex
        (((Ideal.span {ϖ ^ s} • ⊤ : Submodule R M).comap f).toAddSubgroup) =
      Nat.card (IsLocalRing.ResidueField R) ^ min s m :=
  P2mCorankShells.main R M f hf hker ϖ hϖ m hdet s

end S_LinearMap_relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one
end P2MW
export P2MW.S_LinearMap_relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one (solution)
