-- Prove2me | solution 1 for MvFormalGroup.exists_isSymmTwoCocycle_rigidified_span_of_finrank_quotient_span_nthSeries_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/5e9d736d-d5df-5932-b5bb-682a3e74727a

import Mathlib
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Theorems.Thm_MvFormalGroup_IsSymmTwoCocycle_addCoboundary_sum_subst_nthSeries_eq_and_exists_eq_addCoboundary_of_mem_span
import Theorems.Thm_MvFormalGroup_exists_add_le_and_forall_exists_sub_sum_smul_mem_span_nthSeries_of_addCoboundary_mem_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_isSymmTwoCocycle_rigidified_span_of_finrank_quotient_span_nthSeries_eq_pow
p2m_attr_erase "instance" "MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace P2mFGRigidExtCount

universe u

section Peel

variable {σ R : Type*} [CommRing R]

theorem mem_span_X_image [DecidableEq σ] (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s = 0) → coeff d f = 0) →
      f ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R)) '' (T : Set σ)) := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext d
      rw [map_zero]
      exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
    rw [h0]
    exact Ideal.zero_mem _
  | @insert s T hs ih =>
    intro f hf

    let f₀ : MvPowerSeries σ R := fun d => if d s = 0 then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s = 0 then coeff d f else 0 := fun d => rfl
    have hdvd : (X s : MvPowerSeries σ R) ∣ f - f₀ := by
      rw [X_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨q, hq⟩ := hdvd
    have hmem₀ : f₀ ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R)) '' (T : Set σ)) := by
      apply ih
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl
    have hsub : Ideal.span ((fun s => (X s : MvPowerSeries σ R)) '' (T : Set σ)) ≤
        Ideal.span ((fun s => (X s : MvPowerSeries σ R)) '' ((insert s T : Finset σ) : Set σ)) := by
      apply Ideal.span_mono
      apply Set.image_mono
      simp
    have hX : (X s : MvPowerSeries σ R) ∈
        Ideal.span ((fun s => (X s : MvPowerSeries σ R)) '' ((insert s T : Finset σ) : Set σ)) :=
      Ideal.subset_span ⟨s, by simp, rfl⟩
    have hf01 : f = f₀ + X s * q := by rw [← hq]; ring
    rw [hf01]
    exact Ideal.add_mem _ (hsub hmem₀) (Ideal.mul_mem_right _ _ hX)

theorem mem_span_range_X_of_constantCoeff [Fintype σ] {f : MvPowerSeries σ R}
    (hf : constantCoeff f = 0) :
    f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  classical
  have h := mem_span_X_image (R := R) (Finset.univ : Finset σ) f (fun d hd => by
    have hd0 : d = 0 := Finsupp.ext fun s => hd s (Finset.mem_univ s)
    rw [hd0, coeff_zero_eq_constantCoeff_apply, hf])
  simpa [Set.image_univ] using h

theorem subst_mem_span_of_constantCoeff [Fintype σ] {τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    subst a f ∈ Ideal.span (Set.range a) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (mem_span_range_X_of_constantCoeff hf)
  rw [← hc, ← coe_substAlgHom ha, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [map_mul, coe_substAlgHom ha, subst_X ha]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨s, rfl⟩)

end Peel

section Cocycles

variable {k : Type u} [CommRing k] {n : ℕ} {F₀ : MvFormalGroup n k}

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

variable (F₀) in

def cocycleSpace : Submodule k (MvPowerSeries (Fin n ⊕ Fin n) k) where
  carrier := {Γ | F₀.IsSymmTwoCocycle Γ}
  zero_mem' := MvFormalGroup.IsSymmTwoCocycle.zero F₀
  add_mem' := fun h₁ h₂ => isSymmTwoCocycle_add h₁ h₂
  smul_mem' := fun a _ h => isSymmTwoCocycle_smul a h

theorem mem_cocycleSpace {Γ : MvPowerSeries (Fin n ⊕ Fin n) k} :
    Γ ∈ cocycleSpace F₀ ↔ F₀.IsSymmTwoCocycle Γ := Iff.rfl

end Cocycles

section Theta

variable {k : Type u} [CommRing k] {n : ℕ} (F₀ : MvFormalGroup n k) (p : ℕ)

theorem hasSubst_nth (i : ℕ) :
    HasSubst (Sum.elim (F₀.nthSeries i) fun l => (X l : MvPowerSeries (Fin n) k)) :=
  MvFormalGroup.hasSubst_elim (MvFormalGroup.constantCoeff_nthSeries F₀ i) fun l => constantCoeff_X l

def theta (Γ : MvPowerSeries (Fin n ⊕ Fin n) k) : MvPowerSeries (Fin n) k :=
  ∑ i ∈ Finset.range p, subst (Sum.elim (F₀.nthSeries i) fun l => (X l : MvPowerSeries (Fin n) k)) Γ

def thetaLin : MvPowerSeries (Fin n ⊕ Fin n) k →ₗ[k] MvPowerSeries (Fin n) k :=
  ∑ i ∈ Finset.range p, (substAlgHom (hasSubst_nth F₀ i)).toLinearMap

theorem thetaLin_apply (Γ : MvPowerSeries (Fin n ⊕ Fin n) k) :
    thetaLin F₀ p Γ = theta F₀ p Γ := by
  simp only [thetaLin, theta, LinearMap.coe_sum, Finset.sum_apply, AlgHom.toLinearMap_apply,
    coe_substAlgHom]

theorem constantCoeff_theta {Γ : MvPowerSeries (Fin n ⊕ Fin n) k} (hΓ : constantCoeff Γ = 0) :
    constantCoeff (theta F₀ p Γ) = 0 := by
  rw [theta, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  exact constantCoeff_subst_eq_zero (hasSubst_nth F₀ i)
    (by rintro (l | l); exacts [MvFormalGroup.constantCoeff_nthSeries F₀ i l, constantCoeff_X l]) hΓ

theorem theta_addCoboundary {g : MvPowerSeries (Fin n) k} (hg : constantCoeff g = 0) :
    theta F₀ p (F₀.addCoboundary g) = subst (F₀.nthSeries p) g - p • g := by
  have hXl : HasSubst (fun l : Fin n => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hXr : HasSubst (fun l : Fin n => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hstep : ∀ i, subst (Sum.elim (F₀.nthSeries i) fun l => (X l : MvPowerSeries (Fin n) k))
      (F₀.addCoboundary g) = subst (F₀.nthSeries (i + 1)) g - subst (F₀.nthSeries i) g - g := by
    intro i
    have hs := hasSubst_nth F₀ i
    unfold MvFormalGroup.addCoboundary
    rw [subst_sub hs, subst_sub hs, subst_comp_subst_apply F₀.hasSubst_toPowerSeries hs,
      subst_comp_subst_apply hXl hs, subst_comp_subst_apply hXr hs]
    have e1 : (fun l : Fin n => subst (Sum.elim (F₀.nthSeries i) fun l => (X l : MvPowerSeries (Fin n) k))
        ((X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k))) = F₀.nthSeries i := by
      funext l; rw [subst_X hs, Sum.elim_inl]
    have e2 : (fun l : Fin n => subst (Sum.elim (F₀.nthSeries i) fun l => (X l : MvPowerSeries (Fin n) k))
        ((X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k))) = X := by
      funext l; rw [subst_X hs, Sum.elim_inr]
    have e3 : (fun s => subst (Sum.elim (F₀.nthSeries i) fun l => (X l : MvPowerSeries (Fin n) k))
        (F₀.toPowerSeries s)) = F₀.nthSeries (i + 1) := by
      rw [MvFormalGroup.nthSeries_succ]
    rw [e1, e2, e3, subst_self]
    rfl
  unfold theta
  simp only [hstep]
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => subst (F₀.nthSeries i) g) p,
    Finset.sum_const, Finset.card_range, MvFormalGroup.nthSeries_zero,
    MvFormalGroup.subst_zero_of_constantCoeff_eq_zero hg, sub_zero]

end Theta

end P2mFGRigidExtCount

universe u

open P2mFGRigidExtCount in
theorem solution
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {n : ℕ} (F₀ : MvFormalGroup n k) [F₀.IsComm] (h : ℕ)
    (hh : Module.finrank k (MvPowerSeries (Fin n) k ⧸
      Ideal.span (Set.range (F₀.nthSeries p))) = p ^ h) :
    ∃ (s : ℕ) (Γ : Fin s → MvPowerSeries (Fin n ⊕ Fin n) k) (c : Fin s → Fin n → k),
      s ≤ h ∧ (∀ j, F₀.IsSymmTwoCocycle (Γ j)) ∧
      ∀ (Γ' : MvPowerSeries (Fin n ⊕ Fin n) k) (c' : Fin n → k), F₀.IsSymmTwoCocycle Γ' →
        ∃ (a : Fin s → k) (g : MvPowerSeries (Fin n) k), MvPowerSeries.constantCoeff g = 0 ∧
          Γ' = ∑ j, a j • Γ j + F₀.addCoboundary g ∧
          ∀ l, c' l = ∑ j, a j * c j l + MvPowerSeries.coeff (Finsupp.single l 1) g := by
  classical

  obtain ⟨s, ψ, hs, -, hspan⟩ :=
    MvFormalGroup.exists_add_le_and_forall_exists_sub_sum_smul_mem_span_nthSeries_of_addCoboundary_mem_span
      p F₀ h hh

  set I : Ideal (MvPowerSeries (Fin n) k) := Ideal.span (Set.range (F₀.nthSeries p)) with hI
  let Ik : Submodule k (MvPowerSeries (Fin n) k) := I.restrictScalars k
  let π : MvPowerSeries (Fin n) k →ₗ[k] MvPowerSeries (Fin n) k ⧸ Ik := Ik.mkQ
  let dbl : Fin n ⊕ Fin n → MvPowerSeries (Fin n ⊕ Fin n) k := Sum.elim
    (fun i => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (F₀.nthSeries p i))
    (fun i => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (F₀.nthSeries p i))
  have hdbl0 : ∀ t, (dbl t).constantCoeff = 0 := by
    rintro (i | i)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
        (fun l => constantCoeff_X _) (MvFormalGroup.constantCoeff_nthSeries F₀ p i)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
        (fun l => constantCoeff_X _) (MvFormalGroup.constantCoeff_nthSeries F₀ p i)
  have hdbl : HasSubst dbl := hasSubst_of_constantCoeff_zero hdbl0

  have hconn : ∀ Γ, F₀.IsSymmTwoCocycle Γ →
      F₀.addCoboundary (theta F₀ p Γ) = subst dbl Γ ∧
      (theta F₀ p Γ ∈ I → ∃ g : MvPowerSeries (Fin n) k, constantCoeff g = 0 ∧
        Γ = F₀.addCoboundary g) := fun Γ hΓ =>
    MvFormalGroup.IsSymmTwoCocycle.addCoboundary_sum_subst_nthSeries_eq_and_exists_eq_addCoboundary_of_mem_span
      p h hh hΓ

  have hθcob : ∀ g : MvPowerSeries (Fin n) k, constantCoeff g = 0 →
      theta F₀ p (F₀.addCoboundary g) ∈ I := by
    intro g hg
    rw [theta_addCoboundary F₀ p hg, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul,
      sub_zero]
    exact subst_mem_span_of_constantCoeff
      (hasSubst_of_constantCoeff_zero (MvFormalGroup.constantCoeff_nthSeries F₀ p)) hg

  let Z : Submodule k (MvPowerSeries (Fin n ⊕ Fin n) k) := cocycleSpace F₀
  let W : Submodule k (MvPowerSeries (Fin n) k ⧸ Ik) := (Z.map (thetaLin F₀ p)).map π
  let W₂ : Submodule k (MvPowerSeries (Fin n) k ⧸ Ik) := Submodule.span k (Set.range fun j => π (ψ j))
  have hWle : W ≤ W₂ := by
    rintro w ⟨y, ⟨Γ, hΓZ, rfl⟩, rfl⟩
    have hΓ : F₀.IsSymmTwoCocycle Γ := hΓZ
    have hprim : F₀.addCoboundary (theta F₀ p Γ) ∈ Ideal.span (Set.range dbl) := by
      rw [(hconn Γ hΓ).1]
      exact subst_mem_span_of_constantCoeff hdbl hΓ.constantCoeff_eq_zero
    obtain ⟨a, ha⟩ := hspan (theta F₀ p Γ) (constantCoeff_theta F₀ p hΓ.constantCoeff_eq_zero) hprim
    have hπ : π (thetaLin F₀ p Γ) = ∑ j, a j • π (ψ j) := by
      rw [thetaLin_apply]
      have h0 : π (theta F₀ p Γ - ∑ j, a j • ψ j) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem]
        exact ha
      rw [map_sub, map_sum, sub_eq_zero] at h0
      simpa only [map_smul] using h0
    rw [hπ]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  haveI : FiniteDimensional k W₂ := FiniteDimensional.span_of_finite k (Set.finite_range _)
  haveI : FiniteDimensional k W := Submodule.finiteDimensional_of_le hWle
  set r := Module.finrank k W with hr
  have hrs : r ≤ s := by
    calc r ≤ Module.finrank k W₂ := Submodule.finrank_mono hWle
      _ ≤ Fintype.card (Fin s) := finrank_range_le_card (R := k) fun j => π (ψ j)
      _ = s := Fintype.card_fin s
  let bW := Module.finBasis k W

  have hlift : ∀ m : Fin r, ∃ Γ : MvPowerSeries (Fin n ⊕ Fin n) k, F₀.IsSymmTwoCocycle Γ ∧
      π (thetaLin F₀ p Γ) = (bW m : MvPowerSeries (Fin n) k ⧸ Ik) := by
    intro m
    obtain ⟨y, ⟨Γ, hΓZ, rfl⟩, hy⟩ := (bW m).2
    exact ⟨Γ, hΓZ, hy⟩
  choose Γm hΓm hΓmπ using hlift

  refine ⟨r + n, Fin.append Γm (fun _ => 0),
    Fin.append (fun _ : Fin r => (0 : Fin n → k)) (fun l : Fin n => Pi.single l 1), by omega, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]; exact hΓm i
    · rw [Fin.append_right]; exact MvFormalGroup.IsSymmTwoCocycle.zero F₀
  intro Γ' c' hΓ'

  have hw' : π (thetaLin F₀ p Γ') ∈ W := ⟨thetaLin F₀ p Γ', ⟨Γ', hΓ', rfl⟩, rfl⟩
  let ν : Fin r →₀ k := bW.repr ⟨π (thetaLin F₀ p Γ'), hw'⟩
  have hsum : ∑ m, ν m • (bW m : MvPowerSeries (Fin n) k ⧸ Ik) = π (thetaLin F₀ p Γ') := by
    have h1 := bW.sum_repr ⟨π (thetaLin F₀ p Γ'), hw'⟩
    have h2 := congrArg (Submodule.subtype W) h1
    rw [map_sum] at h2
    simpa only [map_smul, Submodule.subtype_apply] using h2

  set Δ : MvPowerSeries (Fin n ⊕ Fin n) k := Γ' - ∑ m, ν m • Γm m with hΔ
  have hΔZ : F₀.IsSymmTwoCocycle Δ := by
    have hmem : Δ ∈ Z := by
      refine Submodule.sub_mem _ hΓ' (Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_)
      exact hΓm m
    exact hmem
  have hΔI : theta F₀ p Δ ∈ I := by
    have h0 : π (thetaLin F₀ p Δ) = 0 := by
      rw [hΔ, map_sub, map_sub, map_sum, map_sum, ← hsum]
      simp only [map_smul, hΓmπ, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem,
      thetaLin_apply] at h0
    exact h0
  obtain ⟨g, hg0, hΔg⟩ := (hconn Δ hΔZ).2 hΔI
  refine ⟨Fin.append (fun m => ν m) (fun l => c' l - coeff (Finsupp.single l 1) g), g, hg0, ?_, ?_⟩
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, smul_zero, Finset.sum_const_zero, add_zero]
    rw [← hΔg, hΔ]
    abel
  · intro l
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      zero_add, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    ring

end

end S_MvFormalGroup_exists_isSymmTwoCocycle_rigidified_span_of_finrank_quotient_span_nthSeries_eq_pow
end P2MW
export P2MW.S_MvFormalGroup_exists_isSymmTwoCocycle_rigidified_span_of_finrank_quotient_span_nthSeries_eq_pow (solution)
