-- Prove2me | solution 1 for MvPolynomial.mem_span_map_of_aeval_X_pow_mem_span_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c2670109-5932-5ba1-808a-ae22785b8ba9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_mem_span_map_of_aeval_X_pow_mem_span_map

set_option autoImplicit false

namespace RelFrobAux

open MvPolynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {σ ι : Type*}

noncomputable def coord (b : Module.Basis ι F K) (j : ι) (g : MvPolynomial σ K) : MvPolynomial σ F :=
  ∑ m ∈ g.support, monomial m (b.repr (g.coeff m) j)

theorem coeff_coord (b : Module.Basis ι F K) (j : ι) (g : MvPolynomial σ K) (m : σ →₀ ℕ) :
    (coord b j g).coeff m = b.repr (g.coeff m) j := by
  classical
  unfold coord
  rw [coeff_sum]
  simp_rw [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · have h0 : g.coeff m = 0 := by simpa [mem_support_iff] using hm
    rw [h0, map_zero, Finsupp.zero_apply]

theorem coord_add (b : Module.Basis ι F K) (j : ι) (g h : MvPolynomial σ K) :
    coord b j (g + h) = coord b j g + coord b j h := by
  ext m
  simp only [coeff_coord, coeff_add, map_add, Finsupp.add_apply]

theorem coord_zero (b : Module.Basis ι F K) (j : ι) : coord b j (0 : MvPolynomial σ K) = 0 := by
  ext m
  simp only [coeff_coord, coeff_zero, map_zero, Finsupp.zero_apply]

noncomputable def coordHom (b : Module.Basis ι F K) (j : ι) : MvPolynomial σ K →+ MvPolynomial σ F where
  toFun := coord b j
  map_zero' := coord_zero b j
  map_add' := coord_add b j

@[scoped simp] theorem coordHom_apply (b : Module.Basis ι F K) (j : ι) (g : MvPolynomial σ K) :
    coordHom b j g = coord (σ := σ) b j g := rfl

theorem coord_sum (b : Module.Basis ι F K) (j : ι) {α : Type*} (s : Finset α) (g : α → MvPolynomial σ K) :
    coord b j (∑ a ∈ s, g a) = ∑ a ∈ s, coord b j (g a) := by
  rw [← coordHom_apply, map_sum]
  rfl

theorem coord_C_mul_map (b : Module.Basis ι F K) (j : ι) (c : K) (w : MvPolynomial σ F) :
    coord b j (C c * map (algebraMap F K) w) = (b.repr c j) • w := by
  ext m
  rw [coeff_coord, coeff_C_mul, coeff_map, coeff_smul, mul_comm c, ← Algebra.smul_def, map_smul,
    Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]

theorem sum_C_mul_map_coord (b : Module.Basis ι F K) (g : MvPolynomial σ K) (J : Finset ι)
    (hJ : ∀ m, (b.repr (g.coeff m)).support ⊆ J) :
    ∑ j ∈ J, C (b j) * map (algebraMap F K) (coord b j g) = g := by
  ext m
  rw [coeff_sum]
  simp_rw [coeff_C_mul, coeff_map, coeff_coord]
  have key := b.linearCombination_repr (g.coeff m)
  rw [Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset (b.repr (g.coeff m)) (hJ m) (fun i a => a • b i)
      (fun j _ => zero_smul _ _)] at key
  exact (Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]).trans key

theorem repr_coeff_support_subset [DecidableEq ι] (b : Module.Basis ι F K) (g : MvPolynomial σ K)
    (m : σ →₀ ℕ) :
    (b.repr (g.coeff m)).support ⊆ g.support.biUnion fun m => (b.repr (g.coeff m)).support := by
  by_cases hm : m ∈ g.support
  · exact Finset.subset_biUnion_of_mem (fun m => (b.repr (g.coeff m)).support) hm
  · have h0 : g.coeff m = 0 := by simpa [mem_support_iff] using hm
    rw [h0, map_zero, Finsupp.support_zero]
    exact Finset.empty_subset _

theorem coord_sum_C_mul_map [DecidableEq ι] (b : Module.Basis ι F K) (J : Finset ι) (w : ι → MvPolynomial σ F)
    (j : ι) (hj : j ∈ J) :
    coord b j (∑ j' ∈ J, C (b j') * map (algebraMap F K) (w j')) = w j := by
  rw [coord_sum]
  simp_rw [coord_C_mul_map, Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' J j]
  exact if_pos hj

theorem aeval_X_pow_map {p : ℕ} [Fact p.Prime] {L : Type*} [CommRing L] [Algebra (ZMod p) L]
    (n : ℕ) (u : MvPolynomial σ (ZMod p)) :
    aeval (fun i => (X i : MvPolynomial σ L) ^ p ^ n) (map (algebraMap (ZMod p) L) u) =
      map (algebraMap (ZMod p) L) (u ^ p ^ n) := by
  induction u using MvPolynomial.induction_on with
  | C c =>
    rw [map_C, ← C_pow, map_C, ZMod.pow_card_pow, aeval_C, algebraMap_eq]
  | add u v hu hv =>
    rw [map_add, map_add, hu, hv, add_pow_char_pow, map_add]
  | mul_X u i hu =>
    rw [map_mul, map_X, map_mul, hu, aeval_X, mul_pow, map_mul, map_pow, map_pow, map_X]

end RelFrobAux
p2m_reactivate "P2MW.S_MvPolynomial_mem_span_map_of_aeval_X_pow_mem_span_map.RelFrobAux"

open RelFrobAux MvPolynomial in
theorem solution
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K] {σ : Type*} (n : ℕ)
    (f : MvPolynomial σ (ZMod p)) (hf : Prime f) (g : MvPolynomial σ K)
    (hg : MvPolynomial.aeval (fun i => (MvPolynomial.X i : MvPolynomial σ K) ^ p ^ n) g ∈
      Ideal.span {MvPolynomial.map (algebraMap (ZMod p) K) f}) :
    g ∈ Ideal.span {MvPolynomial.map (algebraMap (ZMod p) K) f} := by
  classical
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hg

  let b := Module.Basis.ofVectorSpace (ZMod p) K
  let J : Finset (Module.Basis.ofVectorSpaceIndex (ZMod p) K) :=
    (g.support.biUnion fun m => (b.repr (g.coeff m)).support) ∪
      (h.support.biUnion fun m => (b.repr (h.coeff m)).support)
  have hJg : ∀ m, (b.repr (g.coeff m)).support ⊆ J := fun m =>
    (repr_coeff_support_subset b g m).trans Finset.subset_union_left
  have hJh : ∀ m, (b.repr (h.coeff m)).support ⊆ J := fun m =>
    (repr_coeff_support_subset b h m).trans Finset.subset_union_right
  have hg' := sum_C_mul_map_coord b g J hJg
  have hh' := sum_C_mul_map_coord b h J hJh

  have hψg : MvPolynomial.aeval (fun i => (MvPolynomial.X i : MvPolynomial σ K) ^ p ^ n) g =
      ∑ j ∈ J, C (b j) * map (algebraMap (ZMod p) K) ((coord b j g) ^ p ^ n) := by
    conv_lhs => rw [← hg']
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, aeval_C, algebraMap_eq, aeval_X_pow_map]
  have hfh : h * map (algebraMap (ZMod p) K) f =
      ∑ j ∈ J, C (b j) * map (algebraMap (ZMod p) K) (f * coord b j h) := by
    conv_lhs => rw [← hh']
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [_root_.map_mul, mul_assoc, mul_comm (map (algebraMap (ZMod p) K) (coord b j h))]

  have hcoord : ∀ j ∈ J, (coord b j g) ^ p ^ n = f * coord b j h := by
    intro j hj
    have e1 := coord_sum_C_mul_map b J (fun j => (coord b j g) ^ p ^ n) j hj
    have e2 := coord_sum_C_mul_map b J (fun j => f * coord b j h) j hj
    rw [← hψg] at e1
    rw [← hfh, hh] at e2
    exact e1.symm.trans e2

  rw [← hg']
  refine Ideal.sum_mem _ fun j hj => ?_
  obtain ⟨r, hr⟩ := hf.dvd_of_dvd_pow ⟨coord b j h, hcoord j hj⟩
  rw [hr, _root_.map_mul, ← mul_assoc, mul_comm (C (b j)), mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

end S_MvPolynomial_mem_span_map_of_aeval_X_pow_mem_span_map
end P2MW
export P2MW.S_MvPolynomial_mem_span_map_of_aeval_X_pow_mem_span_map (solution)
