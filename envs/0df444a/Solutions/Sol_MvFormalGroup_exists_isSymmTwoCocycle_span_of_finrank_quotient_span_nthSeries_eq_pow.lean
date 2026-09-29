-- Prove2me | solution 1 for MvFormalGroup.exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f2c78690-5b4f-5d4e-9cf2-befb5af437b6

import Mathlib
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Theorems.Thm_MvFormalGroup_eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow
import Theorems.Thm_MvFormalGroup_exists_isSymmTwoCocycle_rigidified_span_of_finrank_quotient_span_nthSeries_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace P2mFGExtCount

universe u

variable {k : Type u} [CommRing k] {n : ℕ} (F₀ : MvFormalGroup n k)

def coboundaryLin : MvPowerSeries (Fin n) k →ₗ[k] MvPowerSeries (Fin n ⊕ Fin n) k :=
  (substAlgHom F₀.hasSubst_toPowerSeries).toLinearMap -
    (substAlgHom (hasSubst_of_constantCoeff_zero (S := k) (τ := Fin n ⊕ Fin n)
      (a := fun l : Fin n => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k))
      fun l => constantCoeff_X _)).toLinearMap -
    (substAlgHom (hasSubst_of_constantCoeff_zero (S := k) (τ := Fin n ⊕ Fin n)
      (a := fun l : Fin n => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k))
      fun l => constantCoeff_X _)).toLinearMap

theorem coboundaryLin_apply (g : MvPowerSeries (Fin n) k) :
    coboundaryLin F₀ g = F₀.addCoboundary g := by
  simp only [coboundaryLin, LinearMap.sub_apply, AlgHom.toLinearMap_apply, coe_substAlgHom]
  rfl

variable {F₀}

theorem isSymmTwoCocycle_add {Γ₁ Γ₂ : MvPowerSeries (Fin n ⊕ Fin n) k}
    (h₁ : F₀.IsSymmTwoCocycle Γ₁) (h₂ : F₀.IsSymmTwoCocycle Γ₂) :
    F₀.IsSymmTwoCocycle (Γ₁ + Γ₂) := by
  have hA : ∀ l : Fin n, ((X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hB : ∀ l : Fin n, ((X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hC : ∀ l : Fin n, ((X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hFAB := MvFormalGroup.constantCoeff_subst_elim F₀ hA hB
  have hFBC := MvFormalGroup.constantCoeff_subst_elim F₀ hB hC
  refine ⟨by rw [map_add, h₁.constantCoeff_eq_zero, h₂.constantCoeff_eq_zero, add_zero], ?_, ?_⟩
  · rw [subst_add (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> exact constantCoeff_X _)),
      h₁.symm, h₂.symm]
  · rw [subst_add (MvFormalGroup.hasSubst_elim hFAB hC), subst_add (MvFormalGroup.hasSubst_elim hA hB),
      subst_add (MvFormalGroup.hasSubst_elim hA hFBC), subst_add (MvFormalGroup.hasSubst_elim hB hC)]
    have e₁ := h₁.cocycle
    have e₂ := h₂.cocycle
    linear_combination e₁ + e₂

theorem isSymmTwoCocycle_smul (a : k) {Γ : MvPowerSeries (Fin n ⊕ Fin n) k}
    (h : F₀.IsSymmTwoCocycle Γ) : F₀.IsSymmTwoCocycle (a • Γ) := by
  have hA : ∀ l : Fin n, ((X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hB : ∀ l : Fin n, ((X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hC : ∀ l : Fin n, ((X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) k)).constantCoeff = 0 :=
    fun l => constantCoeff_X _
  have hFAB := MvFormalGroup.constantCoeff_subst_elim F₀ hA hB
  have hFBC := MvFormalGroup.constantCoeff_subst_elim F₀ hB hC
  refine ⟨by rw [constantCoeff_smul, h.constantCoeff_eq_zero, smul_zero], ?_, ?_⟩
  · rw [subst_smul (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> exact constantCoeff_X _)),
      h.symm]
  · rw [subst_smul (MvFormalGroup.hasSubst_elim hFAB hC), subst_smul (MvFormalGroup.hasSubst_elim hA hB),
      subst_smul (MvFormalGroup.hasSubst_elim hA hFBC), subst_smul (MvFormalGroup.hasSubst_elim hB hC),
      ← smul_add, ← smul_add, h.cocycle]

theorem isSymmTwoCocycle_sum {ι' : Type*} (s : Finset ι') (c : ι' → k)
    {Γ : ι' → MvPowerSeries (Fin n ⊕ Fin n) k} (h : ∀ m, F₀.IsSymmTwoCocycle (Γ m)) :
    F₀.IsSymmTwoCocycle (∑ m ∈ s, c m • Γ m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MvFormalGroup.IsSymmTwoCocycle.zero F₀
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isSymmTwoCocycle_add (isSymmTwoCocycle_smul (c a) (h a)) ih

end P2mFGExtCount

universe u

open P2mFGExtCount in
theorem solution
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {n : ℕ} (F₀ : MvFormalGroup n k) [F₀.IsComm] (h : ℕ)
    (hh : Module.finrank k (MvPowerSeries (Fin n) k ⧸
      Ideal.span (Set.range (F₀.nthSeries p))) = p ^ h) :
    ∃ (r : ℕ) (Γ : Fin r → MvPowerSeries (Fin n ⊕ Fin n) k),
      r ≤ h - n ∧ (∀ j, F₀.IsSymmTwoCocycle (Γ j)) ∧
      ∀ Γ' : MvPowerSeries (Fin n ⊕ Fin n) k, F₀.IsSymmTwoCocycle Γ' →
        ∃ (c : Fin r → k) (g : MvPowerSeries (Fin n) k), MvPowerSeries.constantCoeff g = 0 ∧
          Γ' = ∑ j, c j • Γ j + F₀.addCoboundary g := by
  classical
  obtain ⟨s, Γv, cv, hs, hΓv, hsp⟩ :=
    MvFormalGroup.exists_isSymmTwoCocycle_rigidified_span_of_finrank_quotient_span_nthSeries_eq_pow
      p F₀ h hh
  have homZero : ∀ f : MvPowerSeries (Fin n) k, MvPowerSeries.constantCoeff f = 0 →
      F₀.addCoboundary f = 0 → f = 0 :=
    fun f hf0 hf =>
      MvFormalGroup.eq_zero_of_addCoboundary_eq_zero_of_finrank_quotient_span_nthSeries_eq_pow
        p F₀ h hh f hf0 hf

  choose a g hg0 hΓl hcl using fun l : Fin n =>
    hsp 0 (Pi.single l 1) (MvFormalGroup.IsSymmTwoCocycle.zero F₀)

  have hΓl' : ∀ l, ∑ j, a l j • Γv j = -F₀.addCoboundary (g l) := fun l =>
    eq_neg_of_add_eq_zero_left (hΓl l).symm

  have hli : LinearIndependent k a := by
    rw [Fintype.linearIndependent_iff]
    intro μ hμ
    set G : MvPowerSeries (Fin n) k := ∑ l, μ l • g l with hGdef
    have hG0 : MvPowerSeries.constantCoeff G = 0 := by
      rw [hGdef, map_sum]
      exact Finset.sum_eq_zero fun l _ => by rw [constantCoeff_smul, hg0 l, smul_zero]
    have hμj : ∀ j, ∑ l, μ l * a l j = 0 := fun j => by
      have := congrFun hμ j
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have hdG : F₀.addCoboundary G = 0 := by
      rw [← coboundaryLin_apply, hGdef, map_sum]
      simp only [map_smul, coboundaryLin_apply]
      have hstep : ∀ l, μ l • F₀.addCoboundary (g l) = -∑ j, (μ l * a l j) • Γv j := by
        intro l
        rw [← neg_neg (F₀.addCoboundary (g l)), ← hΓl' l, smul_neg, Finset.smul_sum]
        simp only [smul_smul]
      simp only [hstep, Finset.sum_neg_distrib]
      rw [Finset.sum_comm, neg_eq_zero]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.sum_smul, hμj j, zero_smul]
    have hG : G = 0 := homZero G hG0 hdG
    intro l'

    have hcoef : MvPowerSeries.coeff (Finsupp.single l' 1) G = μ l' := by
      rw [hGdef, map_sum]
      simp only [coeff_smul]
      have hc : ∀ l, MvPowerSeries.coeff (Finsupp.single l' 1) (g l) =
          (Pi.single l (1 : k) : Fin n → k) l' - ∑ j, a l j * cv j l' := fun l =>
        eq_sub_of_add_eq' (hcl l l').symm
      simp only [hc, mul_sub, Finset.sum_sub_distrib]
      have h1 : ∑ l, μ l * (Pi.single l (1 : k) : Fin n → k) l' = μ l' := by
        simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
      have h2 : ∑ l, μ l * ∑ j, a l j * cv j l' = 0 := by
        simp only [Finset.mul_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← Finset.sum_mul, hμj j, zero_mul]
      rw [h1, h2, sub_zero]
    rw [← hcoef, hG, map_zero]

  set W : Submodule k (Fin s → k) := Submodule.span k (Set.range a) with hW
  have hWrank : Module.finrank k W = n := by
    rw [hW, finrank_span_eq_card hli, Fintype.card_fin]
  set r := Module.finrank k ((Fin s → k) ⧸ W) with hr
  have hrs : r + n = s := by
    have := Submodule.finrank_quotient_add_finrank W
    rw [hWrank, Module.finrank_fin_fun] at this
    exact this
  let bQ := Module.finBasis k ((Fin s → k) ⧸ W)
  choose bl hbl using fun m : Fin r => Submodule.Quotient.mk_surjective W (bQ m)
  refine ⟨r, fun m => ∑ j, bl m j • Γv j, by omega,
    fun m => isSymmTwoCocycle_sum _ _ hΓv, ?_⟩
  intro Γ' hΓ'
  obtain ⟨a', g', hg'0, hdec, -⟩ := hsp Γ' 0 hΓ'

  let ν : Fin r → k := fun m => bQ.repr (Submodule.Quotient.mk (p := W) a') m
  have hq : W.mkQ (a' - ∑ m, ν m • bl m) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul, Submodule.mkQ_apply, hbl]
    rw [bQ.sum_repr]
    exact sub_self _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hW,
    Submodule.mem_span_range_iff_exists_fun] at hq
  obtain ⟨μ, hμ⟩ := hq
  have ha' : a' = ∑ m, ν m • bl m + ∑ l, μ l • a l := by
    rw [hμ]; abel
  refine ⟨ν, g' - ∑ l, μ l • g l, ?_, ?_⟩
  · rw [map_sub, hg'0, map_sum, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun l _ => by rw [constantCoeff_smul, hg0 l, smul_zero]
  · rw [hdec]
    have hcob : F₀.addCoboundary (g' - ∑ l, μ l • g l) =
        F₀.addCoboundary g' - ∑ l, μ l • F₀.addCoboundary (g l) := by
      rw [← coboundaryLin_apply, map_sub, map_sum]
      simp only [map_smul, coboundaryLin_apply]
    rw [hcob]
    have hexp : ∑ j, a' j • Γv j =
        ∑ m, ν m • ∑ j, bl m j • Γv j + ∑ l, μ l • ∑ j, a l j • Γv j := by
      have hcoord : ∀ j, a' j = ∑ m, ν m * bl m j + ∑ l, μ l * a l j := fun j => by
        have := congrFun ha' j
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
      simp only [hcoord, add_smul, Finset.sum_add_distrib, Finset.sum_smul, mul_smul,
        Finset.smul_sum]
      congr 1 <;> exact Finset.sum_comm
    rw [hexp]
    simp only [hΓl', smul_neg, Finset.sum_neg_distrib]
    abel

end

end S_MvFormalGroup_exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow
end P2MW
export P2MW.S_MvFormalGroup_exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow (solution)
