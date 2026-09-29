-- Prove2me | solution 1 for MvFormalGroup.Hom.exists_finrank_quotient_span_range_eq_pow_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/be5bbe1f-9c31-5cb6-9b72-77374a54ba79

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Theorems.Thm_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul
import Theorems.Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_Hom_exists_finrank_quotient_span_range_eq_pow_of_finite
p2m_attr_erase "instance" "MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

universe u

noncomputable section

namespace P2mS7DegPow

set_option linter.unusedSectionVars false

open MvPowerSeries MvFormalGroup

section Inverse

variable {k : Type u} [Field k] {d : ℕ}

def lin (C : Matrix (Fin d) (Fin d) k) : Fin d → MvPowerSeries (Fin d) k :=
  fun i => ∑ j, C i j • (X j : MvPowerSeries (Fin d) k)

theorem constantCoeff_lin (C : Matrix (Fin d) (Fin d) k) (i : Fin d) : (lin C i).constantCoeff = 0 := by
  unfold lin
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [smul_eq_C_mul, map_mul, constantCoeff_X, mul_zero]

theorem hasSubst_lin (C : Matrix (Fin d) (Fin d) k) : HasSubst (lin C) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_lin C)

theorem subst_smul_sum {τ : Type*} {F : Fin d → MvPowerSeries τ k} (hF : HasSubst F)
    (C : Matrix (Fin d) (Fin d) k) (G : Fin d → MvPowerSeries (Fin d) k) (i : Fin d) :
    subst F (∑ j, C i j • G j) = ∑ j, C i j • subst F (G j) := by
  rw [← coe_substAlgHom hF, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]

theorem subst_lin {τ : Type*} {F : Fin d → MvPowerSeries τ k} (hF : HasSubst F)
    (C : Matrix (Fin d) (Fin d) k) (i : Fin d) : subst F (lin C i) = ∑ j, C i j • F j := by
  unfold lin
  rw [subst_smul_sum hF]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [subst_X hF]

theorem smul_sum_lin (C D : Matrix (Fin d) (Fin d) k) (i : Fin d) :
    (∑ j, D i j • lin C j) = lin (D * C) i := by
  unfold lin
  simp_rw [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem subst_lin_lin (C D : Matrix (Fin d) (Fin d) k) (i : Fin d) :
    subst (lin C) (lin D i) = lin (D * C) i := by
  rw [subst_lin (hasSubst_lin C), smul_sum_lin]

theorem lin_one : lin (1 : Matrix (Fin d) (Fin d) k) = fun i => (X i : MvPowerSeries (Fin d) k) := by
  funext i
  unfold lin
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem linearPart_smul_sum (C : Matrix (Fin d) (Fin d) k) (G : Fin d → MvPowerSeries (Fin d) k) :
    linearPart (fun i => ∑ j, C i j • G j) = C * linearPart G := by
  ext i l
  simp only [linearPart, Matrix.of_apply, Matrix.mul_apply, map_sum, map_smul, smul_eq_mul]

theorem exists_inverse (ψ : Fin d → MvPowerSeries (Fin d) k) (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hA : IsUnit (linearPart ψ)) :
    ∃ v : Fin d → MvPowerSeries (Fin d) k, (∀ i, (v i).constantCoeff = 0) ∧
      (∀ i, subst ψ (v i) = X i) ∧ (∀ i, subst v (ψ i) = X i) := by
  obtain ⟨⟨A, B, hAB, hBA⟩, hAeq⟩ := hA
  have hAeq' : A = linearPart ψ := hAeq

  let ψt : Fin d → MvPowerSeries (Fin d) k := fun i => ∑ j, B i j • ψ j
  have hψt0 : ∀ i, (ψt i).constantCoeff = 0 := by
    intro i
    show constantCoeff (∑ j, B i j • ψ j) = 0
    rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [smul_eq_C_mul, map_mul, hψ0, mul_zero]
  have hlin : linearPart ψt = 1 := by
    show linearPart (fun i => ∑ j, B i j • ψ j) = 1
    rw [linearPart_smul_sum, ← hAeq', hBA]
  obtain ⟨u, hu0, hu1, hu2⟩ :=
    MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one ψt hψt0 hlin
  have hus := hasSubst_of_constantCoeff_zero hu0
  have hψs := hasSubst_of_constantCoeff_zero hψ0
  refine ⟨fun i => subst (lin B) (u i), fun i => constantCoeff_subst_eq_zero (hasSubst_lin B)
    (constantCoeff_lin B) (hu0 i), fun i => ?_, fun i => ?_⟩
  · rw [subst_comp_subst_apply (hasSubst_lin B) hψs]
    have : (fun j => subst ψ (lin B j)) = ψt := funext fun j => subst_lin hψs B j
    rw [this, hu1]
  ·
    have hS : ∀ j, (∑ l, B j l • subst u (ψ l)) = X j := by
      intro j
      rw [← subst_smul_sum hus, hu2 j]
    have hS' : ∀ i, subst u (ψ i) = lin A i := by
      intro i
      have h1 : (∑ j, A i j • ∑ l, B j l • subst u (ψ l)) = ∑ j, A i j • (X j : MvPowerSeries (Fin d) k) :=
        Finset.sum_congr rfl fun j _ => by rw [hS j]
      have h2 : (∑ j, A i j • ∑ l, B j l • subst u (ψ l)) = subst u (ψ i) := by
        simp_rw [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, hAB]
        rw [Finset.sum_eq_single i]
        · rw [Matrix.one_apply_eq, one_smul]
        · intro l _ hl
          rw [Matrix.one_apply_ne (Ne.symm hl), zero_smul]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      rw [← h2, h1]
      rfl
    have hvs : HasSubst (fun j => subst (lin B) (u j)) := hasSubst_of_constantCoeff_zero fun j =>
      constantCoeff_subst_eq_zero (hasSubst_lin B) (constantCoeff_lin B) (hu0 j)
    rw [← subst_comp_subst_apply hus (hasSubst_lin B), hS', subst_lin_lin, hAB, lin_one]

theorem isUnit_of_rank_eq (A : Matrix (Fin d) (Fin d) k) (h : A.rank = d) : IsUnit A := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  have hr : LinearMap.range A.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact h
  intro y
  have hy : y ∈ LinearMap.range A.mulVecLin := hr ▸ Submodule.mem_top
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx⟩

end Inverse

section Main

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p] {d : ℕ}

private theorem _root_.P2mS7DegPow.finrank_pos {Ψ Φ : MvFormalGroup d k} (ψ : Ψ.Hom Φ)
    (hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries))) :
    0 < Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) := by
  have hne : Ideal.span (Set.range ψ.toPowerSeries) ≠ ⊤ := by
    intro htop
    have hle : Ideal.span (Set.range ψ.toPowerSeries) ≤
        RingHom.ker (constantCoeff : MvPowerSeries (Fin d) k →+* k) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact ψ.constantCoeff_eq_zero i
    rw [htop, top_le_iff] at hle
    have h1 : (1 : MvPowerSeries (Fin d) k) ∈ RingHom.ker (constantCoeff : MvPowerSeries (Fin d) k →+* k) :=
      hle ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  haveI := Ideal.Quotient.nontrivial_iff.mpr hne
  exact Module.finrank_pos

p2m_export "P2mS7DegPow" "finrank_pos"

theorem finrank_eq_one_of_isUnit (ψ : Fin d → MvPowerSeries (Fin d) k)
    (hψ0 : ∀ i, (ψ i).constantCoeff = 0) (hA : IsUnit (linearPart ψ)) :
    Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ)) = 1 := by
  obtain ⟨v, hv0, hψv, -⟩ := exists_inverse ψ hψ0 hA
  have hψs : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  have hker : Ideal.span (Set.range ψ) =
      RingHom.ker (constantCoeff : MvPowerSeries (Fin d) k →+* k) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (RingHom.mem_ker).mpr (hψ0 i)
    · rw [← MvPowerSeries.span_range_X_eq_ker_constantCoeff d, Ideal.span_le]
      rintro _ ⟨i, rfl⟩

      have hvi : v i ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) k)) := by
        rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff d]
        exact (RingHom.mem_ker).mpr (hv0 i)
      have hmap : Ideal.map (substAlgHom hψs).toRingHom
          (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) k))) ≤ Ideal.span (Set.range ψ) := by
        rw [Ideal.map_span, Ideal.span_le]
        rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
        refine Ideal.subset_span ⟨j, ?_⟩
        show ψ j = (substAlgHom hψs) (X j)
        rw [coe_substAlgHom, subst_X hψs]
      have h1 : (substAlgHom hψs).toRingHom (v i) ∈ Ideal.span (Set.range ψ) :=
        hmap (Ideal.mem_map_of_mem _ hvi)
      have h2 : (substAlgHom hψs).toRingHom (v i) = X i := by
        show (substAlgHom hψs) (v i) = X i
        rw [coe_substAlgHom, hψv]
      simpa only [SetLike.mem_coe, h2] using h1
  have hsurj : Function.Surjective (constantCoeff : MvPowerSeries (Fin d) k →+* k) := fun a =>
    ⟨C a, constantCoeff_C a⟩

  let e : (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ)) ≃+* k :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : ∀ y, e (Ideal.Quotient.mk (Ideal.span (Set.range ψ)) y) = constantCoeff y := fun y => rfl
  have helin : ∀ (c : k) (x : MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ)), e (c • x) = c • e x := by
    intro c x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : c • (Ideal.Quotient.mk (Ideal.span (Set.range ψ)) x) = Ideal.Quotient.mk _ (c • x) := rfl
    rw [h1, he, he, smul_eq_C_mul, map_mul, constantCoeff_C, smul_eq_mul]
  let el : (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ)) ≃ₗ[k] k :=
    { toFun := e, invFun := e.symm, map_add' := e.map_add, map_smul' := helin,
      left_inv := e.left_inv, right_inv := e.right_inv }
  rw [el.finrank_eq, Module.finrank_self]

theorem key : ∀ (n : ℕ) (Ψ Φ : MvFormalGroup d k) (_ : Ψ.IsComm) (_ : Φ.IsComm) (ψ : Ψ.Hom Φ),
    Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) →
    Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) ≤ n →
    ∃ h : ℕ, Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) = p ^ h := by
  intro n
  induction n with
  | zero =>
    intro Ψ Φ _ _ ψ hfin hle
    exact absurd hle (not_le.mpr (finrank_pos ψ hfin))
  | succ n ih =>
    intro Ψ Φ hΨ hΦ ψ hfin hle
    haveI := hΨ
    haveI := hΦ
    obtain ⟨Ψ', hΨ', π, ρ, ψ', hψ'π, hρπ, hrank, -, hρfin, hψ'fin, hdegmul⟩ :=
      MvFormalGroup.Hom.exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul p Ψ Φ ψ hfin
    haveI := hΨ'
    set r := (MvFormalGroup.linearPart ψ.toPowerSeries).rank with hr
    by_cases hdr : d - r = 0
    ·
      have hrd : r = d := le_antisymm (hr ▸ Matrix.rank_le_width _) (Nat.sub_eq_zero_iff_le.mp hdr)
      have hunit : IsUnit (MvFormalGroup.linearPart ψ.toPowerSeries) :=
        isUnit_of_rank_eq _ (hr ▸ hrd)
      exact ⟨0, by rw [pow_zero]; exact finrank_eq_one_of_isUnit ψ.toPowerSeries ψ.constantCoeff_eq_zero hunit⟩
    ·
      have hpow : 2 ≤ p ^ (d - r) :=
        le_trans hp.out.two_le (Nat.le_self_pow hdr p)
      have hpos' := finrank_pos ψ' hψ'fin
      have hlt : Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ'.toPowerSeries)) ≤ n := by
        have h1 : 2 * Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ'.toPowerSeries)) ≤
            Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) := by
          rw [hdegmul]
          exact Nat.mul_le_mul_right _ hpow
        omega
      obtain ⟨h', hh'⟩ := ih Ψ' Φ hΨ' hΦ ψ' hψ'fin hlt
      exact ⟨d - r + h', by rw [hdegmul, hh', pow_add]⟩

end Main

end P2mS7DegPow

end

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] {d : ℕ}
    (Ψ Φ : MvFormalGroup d k) [Ψ.IsComm] [Φ.IsComm] (ψ : Ψ.Hom Φ)
    (hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries))) :
    ∃ h : ℕ, Module.finrank k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) = p ^ h :=
  P2mS7DegPow.key (p := p) _ Ψ Φ inferInstance inferInstance ψ hfin le_rfl

end S_MvFormalGroup_Hom_exists_finrank_quotient_span_range_eq_pow_of_finite
end P2MW
export P2MW.S_MvFormalGroup_Hom_exists_finrank_quotient_span_range_eq_pow_of_finite (solution)
