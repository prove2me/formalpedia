-- Prove2me | solution 1 for MvPowerSeries.finite_flat_exists_basis_substAlgHom_of_finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/fbbceb8b-e14b-5888-8b26-d4255c6b3a9b

import Mathlib
import Theorems.Thm_Module_Finite_of_isAdicComplete_of_isHausdorff_of_quotient
import Theorems.Thm_Module_Flat_of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient

set_option autoImplicit false

universe u

namespace W2MV
p2m_open "MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.MvPowerSeries"

open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

noncomputable section

namespace MvPowerSeries

section IndexBijection

variable {α β : Type*}

private theorem Finsupp.sumElim_injective2 :
    Function.Injective2 (Finsupp.sumElim : (α →₀ ℕ) → (β →₀ ℕ) → (α ⊕ β →₀ ℕ)) := by
  intro a a' b b' h
  constructor
  · simpa [Finsupp.comapDomain_inl_sumElim] using
      congrArg (fun d => Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn) h
  · simpa [Finsupp.comapDomain_inr_sumElim] using
      congrArg (fun d => Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn) h

private theorem Finsupp.sumElim_eq_zero_iff {a : α →₀ ℕ} {b : β →₀ ℕ} :
    a.sumElim b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    refine Finsupp.sumElim_injective2 (h.trans ?_)
    exact Finsupp.sumElim_zero_zero.symm
  · rintro ⟨rfl, rfl⟩
    exact Finsupp.sumElim_zero_zero

private theorem Finsupp.sumElim_eq_single_inl_iff {a : α →₀ ℕ} {b : β →₀ ℕ} {s : α} {c : ℕ} :
    a.sumElim b = Finsupp.single (Sum.inl s) c ↔ a = Finsupp.single s c ∧ b = 0 := by
  constructor
  · intro h
    refine Finsupp.sumElim_injective2 (h.trans ?_)
    exact (Finsupp.sumElim_single_zero s c).symm
  · rintro ⟨rfl, rfl⟩
    exact Finsupp.sumElim_single_zero s c

private theorem Finsupp.sumElim_eq_single_inr_iff {a : α →₀ ℕ} {b : β →₀ ℕ} {t : β} {c : ℕ} :
    a.sumElim b = Finsupp.single (Sum.inr t) c ↔ a = 0 ∧ b = Finsupp.single t c := by
  constructor
  · intro h
    refine Finsupp.sumElim_injective2 (h.trans ?_)
    exact (Finsupp.sumElim_zero_single t c).symm
  · rintro ⟨rfl, rfl⟩
    exact Finsupp.sumElim_zero_single t c

end IndexBijection

section SumRingEquiv

variable (α β : Type*) {R : Type*} [CommSemiring R]

private def sumToFun (f : MvPowerSeries (α ⊕ β) R) : MvPowerSeries α (MvPowerSeries β R) :=
  fun a => fun b => f (a.sumElim b)

private def sumInvFun (g : MvPowerSeries α (MvPowerSeries β R)) : MvPowerSeries (α ⊕ β) R :=
  fun d => g (d.comapDomain Sum.inl Sum.inl_injective.injOn)
    (d.comapDomain Sum.inr Sum.inr_injective.injOn)

variable {α β}

@[scoped simp]
private theorem coeff_sumToFun (f : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff b (coeff a (sumToFun α β f)) = coeff (a.sumElim b) f :=
  rfl

@[scoped simp]
private theorem coeff_sumInvFun (g : MvPowerSeries α (MvPowerSeries β R)) (d : α ⊕ β →₀ ℕ) :
    coeff d (sumInvFun α β g) =
      coeff (d.comapDomain Sum.inr Sum.inr_injective.injOn)
        (coeff (d.comapDomain Sum.inl Sum.inl_injective.injOn) g) :=
  rfl

private theorem coeff_mul_sumElim [DecidableEq α] [DecidableEq β]
    (f g : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff (a.sumElim b) (f * g) =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal a, ∑ r ∈ Finset.HasAntidiagonal.antidiagonal b,
        coeff (q.1.sumElim r.1) f * coeff (q.2.sumElim r.2) g := by
  classical
  rw [coeff_mul, ← Finsupp.image_sumElim_product_antidiagonal, Finset.sum_image,
    Finset.sum_product]

  rintro ⟨⟨q₁, q₂⟩, ⟨r₁, r₂⟩⟩ - ⟨⟨q₁', q₂'⟩, ⟨r₁', r₂'⟩⟩ - h
  simp only [Prod.mk.injEq] at h ⊢
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨hq₁, hr₁⟩ := Finsupp.sumElim_injective2 h₁
  obtain ⟨hq₂, hr₂⟩ := Finsupp.sumElim_injective2 h₂
  exact ⟨⟨hq₁, hq₂⟩, ⟨hr₁, hr₂⟩⟩

variable (α β) (R) in

private def sumRingEquiv : MvPowerSeries (α ⊕ β) R ≃+* MvPowerSeries α (MvPowerSeries β R) where
  toFun := sumToFun α β
  invFun := sumInvFun α β
  left_inv f := by
    ext d
    rw [show coeff d (sumInvFun α β (sumToFun α β f)) =
        coeff ((d.comapDomain Sum.inl Sum.inl_injective.injOn).sumElim
          (d.comapDomain Sum.inr Sum.inr_injective.injOn)) f from rfl,
      Finsupp.comapDomain_sumElim_comapDomain]
  right_inv g := by
    ext a b
    rw [show coeff b (coeff a (sumToFun α β (sumInvFun α β g))) =
        coeff ((a.sumElim b).comapDomain Sum.inr Sum.inr_injective.injOn)
          (coeff ((a.sumElim b).comapDomain Sum.inl Sum.inl_injective.injOn) g) from rfl,
      Finsupp.comapDomain_inl_sumElim, Finsupp.comapDomain_inr_sumElim]
  map_add' f g := by
    ext a b
    simp only [map_add, coeff_sumToFun]
  map_mul' f g := by
    classical
    ext a b
    rw [coeff_sumToFun, coeff_mul_sumElim]
    rw [show coeff a (sumToFun α β f * sumToFun α β g) =
        ∑ q ∈ Finset.HasAntidiagonal.antidiagonal a, coeff q.1 (sumToFun α β f) * coeff q.2 (sumToFun α β g) from
      coeff_mul (φ := sumToFun α β f) (ψ := sumToFun α β g) (n := a), map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show coeff b (coeff q.1 (sumToFun α β f) * coeff q.2 (sumToFun α β g)) =
        ∑ r ∈ Finset.HasAntidiagonal.antidiagonal b, coeff r.1 (coeff q.1 (sumToFun α β f)) *
          coeff r.2 (coeff q.2 (sumToFun α β g)) from coeff_mul ..]
    exact Finset.sum_congr rfl fun r _ => by rw [coeff_sumToFun, coeff_sumToFun]

@[scoped simp]
private theorem coeff_sumRingEquiv (f : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff b (coeff a (sumRingEquiv α β R f)) = coeff (a.sumElim b) f :=
  rfl

@[scoped simp]
private theorem sumRingEquiv_X_inl (s : α) :
    sumRingEquiv α β R (X (Sum.inl s)) = X s := by
  classical
  ext a b
  rw [coeff_sumRingEquiv, coeff_X, X_def (R := MvPowerSeries β R), coeff_monomial,
    apply_ite (coeff b), coeff_one, coeff_zero]
  simp only [Finsupp.sumElim_eq_single_inl_iff]
  by_cases ha : a = Finsupp.single s 1 <;> by_cases hb : b = (0 : β →₀ ℕ) <;>
    simp [ha, hb]

@[scoped simp]
private theorem sumRingEquiv_X_inr (t : β) :
    sumRingEquiv α β R (X (Sum.inr t)) = C (X t) := by
  classical
  ext a b
  rw [coeff_sumRingEquiv, coeff_X, coeff_C, apply_ite (coeff b), coeff_X, coeff_zero]
  simp only [Finsupp.sumElim_eq_single_inr_iff]
  by_cases ha : a = (0 : α →₀ ℕ) <;> by_cases hb : b = Finsupp.single t 1 <;>
    simp [ha, hb]

@[scoped simp]
private theorem sumRingEquiv_C (r : R) :
    sumRingEquiv α β R (C r) = C (C r) := by
  classical
  ext a b
  rw [coeff_sumRingEquiv, coeff_C, coeff_C, apply_ite (coeff b), coeff_C, coeff_zero]
  simp only [Finsupp.sumElim_eq_zero_iff]
  by_cases ha : a = (0 : α →₀ ℕ) <;> by_cases hb : b = (0 : β →₀ ℕ) <;> simp [ha, hb]

end SumRingEquiv

section FinSucc

variable {R : Type*} [CommSemiring R]

private def finSuccSumEquiv (n : ℕ) : Fin (n + 1) ≃ Unit ⊕ Fin n where
  toFun := Fin.cases (Sum.inl ()) (fun i => Sum.inr i)
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := by
    induction i using Fin.cases <;> simp
  right_inv x := by
    rcases x with ⟨⟩ | i <;> simp

@[scoped simp] private theorem finSuccSumEquiv_zero (n : ℕ) : finSuccSumEquiv n 0 = Sum.inl () := rfl

@[scoped simp] private theorem finSuccSumEquiv_succ (n : ℕ) (i : Fin n) :
    finSuccSumEquiv n i.succ = Sum.inr i := by
  simp [finSuccSumEquiv]

variable (R) in

private def finSuccRingEquiv (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) R ≃+* PowerSeries (MvPowerSeries (Fin n) R) :=
  ((renameEquiv R (finSuccSumEquiv n)).toRingEquiv).trans (sumRingEquiv Unit (Fin n) R)

private theorem finSuccRingEquiv_apply (n : ℕ) (f : MvPowerSeries (Fin (n + 1)) R) :
    finSuccRingEquiv R n f =
      sumRingEquiv Unit (Fin n) R (rename (finSuccSumEquiv n) f) :=
  rfl

@[scoped simp]
private theorem finSuccRingEquiv_X_zero (n : ℕ) :
    finSuccRingEquiv R n (X 0) = PowerSeries.X := by
  rw [finSuccRingEquiv_apply, rename_X]
  exact sumRingEquiv_X_inl ()

@[scoped simp]
private theorem finSuccRingEquiv_X_succ (n : ℕ) (i : Fin n) :
    finSuccRingEquiv R n (X i.succ) = PowerSeries.C (X i) := by
  rw [finSuccRingEquiv_apply, rename_X, finSuccSumEquiv_succ]
  exact sumRingEquiv_X_inr i

@[scoped simp]
private theorem finSuccRingEquiv_C (n : ℕ) (r : R) :
    finSuccRingEquiv R n (C r) = PowerSeries.C (C r) := by
  rw [finSuccRingEquiv_apply, rename_C]
  exact sumRingEquiv_C r

end FinSucc

section IsEmpty

variable (σ : Type*) [IsEmpty σ] (R : Type*) [CommSemiring R]

private def isEmptyRingEquiv : MvPowerSeries σ R ≃+* R :=
  RingEquiv.ofRingHom (constantCoeff (σ := σ) (R := R)) (C (σ := σ) (R := R))
    (by ext r; simp)
    (by classical
        ext f d
        obtain rfl : d = 0 := Subsingleton.eq_zero d
        simp [coeff_C, coeff_zero_eq_constantCoeff])

@[scoped simp]
private theorem isEmptyRingEquiv_apply (f : MvPowerSeries σ R) :
    isEmptyRingEquiv σ R f = constantCoeff f := rfl

@[scoped simp]
private theorem isEmptyRingEquiv_symm_apply (r : R) :
    (isEmptyRingEquiv σ R).symm r = C r := rfl

end IsEmpty

section Noetherian

private theorem isNoetherianRing_fin (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
    exact isNoetherianRing_of_ringEquiv R (isEmptyRingEquiv (Fin 0) R).symm
  | succ n ih =>
    exact isNoetherianRing_of_ringEquiv _ (finSuccRingEquiv R n).symm

end Noetherian

end MvPowerSeries
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries"

end
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries"

end W2MV
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV"

open IsLocalRing PowerSeries RingTheory
open scoped Pointwise

namespace W2PS
namespace PowerSeries

variable {R : Type u} [CommRing R]

private lemma isSMulRegular_X : IsSMulRegular R⟦X⟧ (X : R⟦X⟧) := by
  intro f g h
  simp only [smul_eq_mul] at h
  ext n
  simpa only [coeff_succ_X_mul] using congrArg (coeff (n + 1)) h

private lemma ker_constantCoeff : RingHom.ker (constantCoeff (R := R)) = Ideal.span {(X : R⟦X⟧)} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

private noncomputable def quotSpanXEquiv : (R⟦X⟧ ⧸ Ideal.span {(X : R⟦X⟧)}) ≃+* R :=
  (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)

@[scoped simp]
private lemma quotSpanXEquiv_mk (f : R⟦X⟧) :
    quotSpanXEquiv (Ideal.Quotient.mk _ f) = constantCoeff f := by
  simp only [quotSpanXEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq]
  rfl

private lemma smul_top_eq_span_X :
    (X : R⟦X⟧) • (⊤ : Ideal R⟦X⟧) = Ideal.span {(X : R⟦X⟧)} := by
  rw [← Submodule.ideal_span_singleton_smul]
  simp

section IsLocalRing

variable [IsLocalRing R]

private lemma mem_maximalIdeal_iff {f : R⟦X⟧} :
    f ∈ maximalIdeal R⟦X⟧ ↔ constantCoeff f ∈ maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_iff_constantCoeff]

private lemma X_mem_maximalIdeal : (X : R⟦X⟧) ∈ maximalIdeal R⟦X⟧ := by
  rw [mem_maximalIdeal_iff, constantCoeff_X]
  exact zero_mem _

private lemma C_mem_maximalIdeal {r : R} (hr : r ∈ maximalIdeal R) :
    (C r : R⟦X⟧) ∈ maximalIdeal R⟦X⟧ := by
  rwa [mem_maximalIdeal_iff, constantCoeff_C]

end IsLocalRing
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV"

section KrullDim
variable (R) [IsNoetherianRing R] [IsLocalRing R]

private lemma ringKrullDim_powerSeries : ringKrullDim R⟦X⟧ = ringKrullDim R + 1 := by
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (R := R⟦X⟧) (x := X) isSMulRegular_X X_mem_maximalIdeal
  rw [ringKrullDim_eq_of_ringEquiv (quotSpanXEquiv (R := R))] at h
  exact h.symm

end KrullDim
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV"

section MaximalIdealSpan
variable [IsLocalRing R]

private theorem maximalIdeal_eq_span_image_union_X {S : Set R} (hS : maximalIdeal R = Ideal.span S) :
    maximalIdeal R⟦X⟧ = Ideal.span ((C : R →+* R⟦X⟧) '' S ∪ {(X : R⟦X⟧)}) := by
  apply le_antisymm
  ·
    intro f hf
    have hc : constantCoeff f ∈ maximalIdeal R := mem_maximalIdeal_iff.mp hf

    have h2 : C (constantCoeff f) ∈
        Ideal.span ((C : R →+* R⟦X⟧) '' S ∪ {(X : R⟦X⟧)}) := by
      refine Ideal.span_mono Set.subset_union_left ?_
      rw [← Ideal.map_span]
      exact Ideal.mem_map_of_mem _ (hS ▸ hc)

    have h1 : f - C (constantCoeff f) ∈
        Ideal.span ((C : R →+* R⟦X⟧) '' S ∪ {(X : R⟦X⟧)}) := by
      refine Ideal.span_mono Set.subset_union_right ?_
      rw [← ker_constantCoeff, RingHom.mem_ker, map_sub, constantCoeff_C, sub_self]
    have heq : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
    rw [heq]
    exact add_mem h2 h1
  ·
    rw [Ideal.span_le]
    rintro g (⟨r, hr, rfl⟩ | rfl)
    · exact C_mem_maximalIdeal (by rw [hS]; exact Ideal.subset_span hr)
    · exact X_mem_maximalIdeal

private theorem spanFinrank_maximalIdeal_le_succ [IsNoetherianRing R] :
    (maximalIdeal R⟦X⟧).spanFinrank ≤ (maximalIdeal R).spanFinrank + 1 := by

  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal R))
  have hS : maximalIdeal R = Ideal.span (s : Set R) := by
    rw [← Ideal.submodule_span_eq, hspan]
  rw [maximalIdeal_eq_span_image_union_X hS, ← Ideal.submodule_span_eq]
  refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
    ((s.finite_toSet.image _).union (Set.finite_singleton _))) ?_
  refine le_trans (Set.ncard_union_le _ _) ?_
  rw [Set.ncard_singleton]
  have h1 : ((C : R →+* R⟦X⟧) '' (s : Set R)).ncard ≤ (s : Set R).ncard :=
    Set.ncard_image_le s.finite_toSet
  rw [Set.ncard_coe_finset] at h1
  omega

end MaximalIdealSpan
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV"

private theorem isRegularLocalRing_powerSeries (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing R⟦X⟧ := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [ringKrullDim_powerSeries R, ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)]
  exact_mod_cast spanFinrank_maximalIdeal_le_succ (R := R)

end PowerSeries
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS.PowerSeries"
end W2PS
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS.PowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS"

open IsLocalRing

namespace MvPowerSeries
p2m_export "MvPowerSeries" "X_def coeff_zero_eq_constantCoeff coeff coeff_one rename_C coeff_monomial renameEquiv rename_X X_dvd_iff subst constantCoeff_subst_eq_zero subst_X C X constantCoeff constantCoeff_C hasSubst_of_constantCoeff_zero X_pow_dvd_iff coeff_zero_eq_constantCoeff_apply map coe_substAlgHom algebraMap_apply monomial smul_eq_C_mul coeff_zero coeff_X substAlgHom coeff_mul rename c_eq_algebraMap constantCoeff_X coeff_C ext isUnit_iff_constantCoeff"
namespace SubstFree
p2m_open "MvPowerSeries"

open IsLocalRing

private theorem isRegularLocalRing_fin_field (k : Type u) [Field k] (n : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin n) k) := by
  induction n with
  | zero =>
    haveI : IsRegularLocalRing k := inferInstance
    exact IsRegularLocalRing.of_ringEquiv (W2MV.MvPowerSeries.isEmptyRingEquiv (Fin 0) k).symm
  | succ n ih =>
    haveI := ih
    haveI : IsRegularLocalRing (PowerSeries (MvPowerSeries (Fin n) k)) :=
      W2PS.PowerSeries.isRegularLocalRing_powerSeries _
    exact IsRegularLocalRing.of_ringEquiv (W2MV.MvPowerSeries.finSuccRingEquiv k n).symm

end MvPowerSeries.SubstFree
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS.PowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS"
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS.PowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS"

namespace MvPowerSeries
p2m_export "MvPowerSeries" "X_def coeff_zero_eq_constantCoeff coeff coeff_one rename_C coeff_monomial renameEquiv rename_X X_dvd_iff subst constantCoeff_subst_eq_zero subst_X C X constantCoeff constantCoeff_C hasSubst_of_constantCoeff_zero X_pow_dvd_iff coeff_zero_eq_constantCoeff_apply map coe_substAlgHom algebraMap_apply monomial smul_eq_C_mul coeff_zero coeff_X substAlgHom coeff_mul rename c_eq_algebraMap constantCoeff_X coeff_C ext isUnit_iff_constantCoeff"
namespace SubstFree
p2m_open "MvPowerSeries"

p2m_open "MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.MvPowerSeries"

variable {k : Type u} [Field k] {d : ℕ}

private theorem mem_span_X_pow {σ : Type*} {R : Type*} [CommRing R] [DecidableEq σ] (N : ℕ) (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ e : σ →₀ ℕ, (∀ s ∈ T, e s < N) → coeff e f = 0) →
      f ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    have : f = 0 := by
      ext e
      rw [coeff_zero]
      exact hf e (fun s hs => absurd hs (Finset.notMem_empty s))
    rw [this]
    exact zero_mem _
  | insert s₀ T hs₀ ih =>
    intro f hf
    let f₀ : MvPowerSeries σ R := fun e => if e s₀ < N then coeff e f else 0
    have hf₀ : ∀ e, coeff e f₀ = if e s₀ < N then coeff e f else 0 := fun e => rfl
    have h1 : (X s₀ : MvPowerSeries σ R) ^ N ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hf₀, if_pos hm, sub_self]
    have h2 : f₀ ∈ Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) := by
      refine ih f₀ fun e he => ?_
      rw [hf₀]
      by_cases h : e s₀ < N
      · rw [if_pos h]
        refine hf e fun s hs => ?_
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact h
        · exact he s hs
      · rw [if_neg h]
    have h3 : Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' (T : Set σ)) ≤
        Ideal.span ((fun s => (X s : MvPowerSeries σ R) ^ N) '' ((insert s₀ T : Finset σ) : Set σ)) :=
      Ideal.span_mono (Set.image_mono (by simp))
    obtain ⟨g, hg⟩ := h1
    have : f = f₀ + (X s₀ : MvPowerSeries σ R) ^ N * g := by rw [← hg]; ring
    rw [this]
    refine Ideal.add_mem _ (h3 h2) (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s₀, by simp, rfl⟩))

private theorem mem_span_range_X_of_constantCoeff {R : Type*} [CommRing R] {f : MvPowerSeries (Fin d) R}
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R)) := by
  classical
  have h := mem_span_X_pow 1 Finset.univ f fun e he => by
    have : e = 0 := by
      ext s
      have := he s (Finset.mem_univ s)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [this, coeff_zero_eq_constantCoeff_apply, hf]
  simpa only [pow_one, Finset.coe_univ, Set.image_univ] using h

private theorem constantCoeff_eq_zero_of_mem_span_range_X {R : Type*} [CommRing R] {f : MvPowerSeries (Fin d) R}
    (hf : f ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R))) : constantCoeff f = 0 := by
  have hle : Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R)) ≤
      RingHom.ker (constantCoeff : MvPowerSeries (Fin d) R →+* R) := by
    rw [Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    exact constantCoeff_X s
  exact hle hf

private theorem constantCoeff_substAlgHom {g : Fin d → MvPowerSeries (Fin d) k}
    (hg : ∀ i, constantCoeff (g i) = 0) (x : MvPowerSeries (Fin d) k) :
    constantCoeff (substAlgHom (hasSubst_of_constantCoeff_zero hg) x) = constantCoeff x := by
  have hx : x = algebraMap k (MvPowerSeries (Fin d) k) (constantCoeff x) + (x - C (constantCoeff x)) := by
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]; ring
  have h0 : constantCoeff (x - C (constantCoeff x)) = 0 := by
    rw [map_sub, constantCoeff_C, sub_self]
  conv_lhs => rw [hx]
  rw [map_add, AlgHom.commutes, map_add, coe_substAlgHom,
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hg) hg h0, add_zero,
    MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_C]

end MvPowerSeries.SubstFree
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS.PowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS"
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS.PowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS"

namespace MvPowerSeries
p2m_export "MvPowerSeries" "X_def coeff_zero_eq_constantCoeff coeff coeff_one rename_C coeff_monomial renameEquiv rename_X X_dvd_iff subst constantCoeff_subst_eq_zero subst_X C X constantCoeff constantCoeff_C hasSubst_of_constantCoeff_zero X_pow_dvd_iff coeff_zero_eq_constantCoeff_apply map coe_substAlgHom algebraMap_apply monomial smul_eq_C_mul coeff_zero coeff_X substAlgHom coeff_mul rename c_eq_algebraMap constantCoeff_X coeff_C ext isUnit_iff_constantCoeff"
namespace SubstFree
p2m_open "MvPowerSeries"

p2m_open "MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.MvPowerSeries IsLocalRing"

variable {k : Type u} [Field k] {d : ℕ}

private def Tgt (_φ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k) : Type u := MvPowerSeries (Fin d) k

private noncomputable scoped instance (φ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k) : CommRing (Tgt φ) :=
  inferInstanceAs (CommRing (MvPowerSeries (Fin d) k))

private def toTgt (φ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k) : MvPowerSeries (Fin d) k →+* Tgt φ := φ

private noncomputable scoped instance (φ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k) :
    Algebra (MvPowerSeries (Fin d) k) (Tgt φ) := (toTgt φ).toAlgebra

private theorem algebraMap_Tgt (φ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k)
    (x : MvPowerSeries (Fin d) k) : algebraMap (MvPowerSeries (Fin d) k) (Tgt φ) x = φ x := rfl

private noncomputable def ofT (φ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k) : Tgt φ ≃+* MvPowerSeries (Fin d) k :=
  RingEquiv.refl _

private theorem ofT_algebraMap (φ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k) (r : MvPowerSeries (Fin d) k) :
    ofT φ (algebraMap (MvPowerSeries (Fin d) k) (Tgt φ) r) = φ r := rfl

private theorem ofT_smul (φ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k) (r : MvPowerSeries (Fin d) k)
    (t : Tgt φ) : ofT φ (r • t) = φ r * ofT φ t := by
  rw [Algebra.smul_def, map_mul, ofT_algebraMap]

private theorem ofT_symm_apply (φ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k) (x : MvPowerSeries (Fin d) k) :
    ofT φ ((ofT φ).symm x) = x := rfl

private scoped instance (φ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k) : IsLocalRing (Tgt φ) :=
  inferInstanceAs (IsLocalRing (MvPowerSeries (Fin d) k))

private theorem isRegularLocalRing_Tgt (φ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k) :
    IsRegularLocalRing (Tgt φ) :=
  show IsRegularLocalRing (MvPowerSeries (Fin d) k) from isRegularLocalRing_fin_field k d

end MvPowerSeries.SubstFree
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS.PowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.MvPowerSeries.SubstFree"
p2m_reactivate "P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV.MvPowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2MV P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS.PowerSeries P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.W2PS P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.MvPowerSeries"

theorem solution
    {k : Type u} [Field k] {d : ℕ} (g : Fin d → MvPowerSeries (Fin d) k)
    (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) :
    RingHom.Finite (A := MvPowerSeries (Fin d) k) (B := MvPowerSeries (Fin d) k)
      (MvPowerSeries.substAlgHom (R := k) (MvPowerSeries.hasSubst_of_constantCoeff_zero hg)).toRingHom ∧
    RingHom.Flat (R := MvPowerSeries (Fin d) k) (S := MvPowerSeries (Fin d) k)
      (MvPowerSeries.substAlgHom (R := k) (MvPowerSeries.hasSubst_of_constantCoeff_zero hg)).toRingHom ∧
    ∃ b : Fin (Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) → MvPowerSeries (Fin d) k,
      ∀ x : MvPowerSeries (Fin d) k,
        ∃! c : Fin (Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) →
            MvPowerSeries (Fin d) k,
          x = ∑ i, MvPowerSeries.subst g (c i) * b i := by
  classical

  let φa : MvPowerSeries (Fin d) k →ₐ[k] MvPowerSeries (Fin d) k :=
    MvPowerSeries.substAlgHom (R := k) (MvPowerSeries.hasSubst_of_constantCoeff_zero hg)
  let φ : MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin d) k := φa.toRingHom
  have hφ : ∀ x, φ x = MvPowerSeries.subst g x := fun x => by
    show φa x = _
    rw [MvPowerSeries.coe_substAlgHom]
  have hφX : ∀ i, φ (MvPowerSeries.X i) = g i := fun i => by
    rw [hφ, MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hg)]
  have hφC : ∀ c : k, φ (MvPowerSeries.C c) = MvPowerSeries.C c := fun c => by
    show φa (MvPowerSeries.C c) = _
    rw [MvPowerSeries.c_eq_algebraMap, AlgHom.commutes]
  have hφ0 : ∀ x, MvPowerSeries.constantCoeff (φ x) = MvPowerSeries.constantCoeff x := fun x =>
    MvPowerSeries.SubstFree.constantCoeff_substAlgHom hg x

  let T := MvPowerSeries.SubstFree.Tgt φ
  let e : T ≃+* MvPowerSeries (Fin d) k := MvPowerSeries.SubstFree.ofT φ
  have he_smul : ∀ (r : MvPowerSeries (Fin d) k) (t : T), e (r • t) = φ r * e t :=
    MvPowerSeries.SubstFree.ofT_smul φ
  have he_symm : ∀ x, e (e.symm x) = x := MvPowerSeries.SubstFree.ofT_symm_apply φ

  haveI hregA : IsRegularLocalRing (MvPowerSeries (Fin d) k) :=
    MvPowerSeries.SubstFree.isRegularLocalRing_fin_field k d
  haveI hregT : IsRegularLocalRing T := MvPowerSeries.SubstFree.isRegularLocalRing_Tgt φ

  haveI hloc : IsLocalHom (algebraMap (MvPowerSeries (Fin d) k) T) := by
    refine ⟨fun x hx => ?_⟩
    have hx1 : IsUnit (e (algebraMap (MvPowerSeries (Fin d) k) T x)) := hx.map e
    rw [MvPowerSeries.SubstFree.ofT_algebraMap] at hx1
    have hx' : IsUnit (MvPowerSeries.constantCoeff (φ x)) := MvPowerSeries.isUnit_iff_constantCoeff.mp hx1
    rw [hφ0] at hx'
    exact MvPowerSeries.isUnit_iff_constantCoeff.mpr hx'

  let 𝔫 : Ideal (MvPowerSeries (Fin d) k) := Ideal.span (Set.range MvPowerSeries.X)
  have hrg : (⇑φ) '' Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) k) = Set.range g := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hφX)
  have hmap : Ideal.map (algebraMap (MvPowerSeries (Fin d) k) T) 𝔫 =
      Ideal.comap e (Ideal.span (Set.range g)) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, Ideal.mem_comap, MvPowerSeries.SubstFree.ofT_algebraMap, ← Ideal.mem_comap]
      have : 𝔫 ≤ Ideal.comap φ (Ideal.span (Set.range g)) := by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_span, hrg]
      exact this hr
    · intro t ht
      rw [Ideal.mem_comap] at ht
      have hsurj : ∀ y ∈ Ideal.span (Set.range g), e.symm y ∈ Ideal.map (algebraMap (MvPowerSeries (Fin d) k) T) 𝔫 := by
        intro y hy
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨i, rfl⟩
          rw [← hφX]
          exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
        · rw [map_zero]; exact Ideal.zero_mem _
        · intro a b _ _ ha hb; rw [map_add]; exact Ideal.add_mem _ ha hb
        · intro a b _ hb; rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hb
      have := hsurj (e t) ht
      rwa [RingEquiv.symm_apply_apply] at this
  have hsmul : ∀ (n : ℕ) (t : T),
      t ∈ (𝔫 ^ n • ⊤ : Submodule (MvPowerSeries (Fin d) k) T) ↔
        e t ∈ (Ideal.span (Set.range g) : Ideal (MvPowerSeries (Fin d) k)) ^ n := by
    intro n t
    rw [Ideal.smul_top_eq_map, Ideal.map_pow, hmap, Submodule.restrictScalars_mem, ← Ideal.map_symm,
      ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]
  have hgne : (Ideal.span (Set.range g) : Ideal (MvPowerSeries (Fin d) k)) ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPowerSeries (Fin d) k) ∈ Ideal.span (Set.range g) := htop ▸ Submodule.mem_top
    have hle : Ideal.span (Set.range g) ≤
        RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) k →+* k) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hg i
    have := hle h1
    rw [RingHom.mem_ker, map_one] at this
    exact one_ne_zero this

  haveI hhaus : IsHausdorff 𝔫 T := by
    refine ⟨fun z hz => ?_⟩
    have hz' : ∀ n : ℕ, e z ∈ (Ideal.span (Set.range g) : Ideal _) ^ n := fun n => by
      have h := hz n
      rw [SModEq.sub_mem, sub_zero] at h
      exact (hsmul n z).mp h
    have hmem : e z ∈ ⨅ n : ℕ, (Ideal.span (Set.range g) : Ideal _) ^ n := Ideal.mem_iInf.mpr hz'
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hgne, Ideal.mem_bot] at hmem
    exact e.map_eq_zero_iff.mp hmem

  haveI hfinq : Module.Finite (MvPowerSeries (Fin d) k) (T ⧸ (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T)) := by
    obtain ⟨m, f, hf⟩ :=
      Module.Finite.exists_fin (R := k) (M := MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))
    choose t ht using fun j => Ideal.Quotient.mk_surjective (I := Ideal.span (Set.range g)) (f j)
    rw [Module.finite_def]
    refine ⟨(Finset.univ : Finset (Fin m)).image fun j =>
      Submodule.Quotient.mk (p := (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T)) (e.symm (t j)),
        eq_top_iff.mpr ?_⟩
    rintro y -
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hx : Ideal.Quotient.mk (Ideal.span (Set.range g)) (e x) ∈ Submodule.span k (Set.range f) := by
      rw [hf]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hx
    have hdiff : e x - ∑ j, c j • t j ∈ Ideal.span (Set.range g) := by
      rw [← Ideal.Quotient.eq, map_sum, ← hc]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← ht j]
      simp only [← Ideal.Quotient.mkₐ_eq_mk k, map_smul]
    have hdiff' : x - ∑ j, (MvPowerSeries.C (c j) : MvPowerSeries (Fin d) k) • e.symm (t j) ∈
        (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T) := by
      rw [show (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T) = 𝔫 ^ 1 • ⊤ by rw [pow_one], hsmul 1, pow_one,
        map_sub, map_sum]
      convert hdiff using 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [he_smul, he_symm, hφC, MvPowerSeries.smul_eq_C_mul]
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have hquot : Submodule.Quotient.mk (p := (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T)) x =
        ∑ j, (MvPowerSeries.C (c j) : MvPowerSeries (Fin d) k) •
          Submodule.Quotient.mk (p := (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T)) (e.symm (t j)) := by
      have h0 : (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T).mkQ
          (x - ∑ j, (MvPowerSeries.C (c j) : MvPowerSeries (Fin d) k) • e.symm (t j)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hdiff'
      rw [map_sub, map_sum] at h0
      simp only [map_smul, Submodule.mkQ_apply] at h0
      exact sub_eq_zero.mp h0
    rw [hquot]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  haveI hfinT : Module.Finite (MvPowerSeries (Fin d) k) T :=
    Module.Finite.of_isAdicComplete_of_isHausdorff_of_quotient 𝔫 T hfinq

  haveI hflat : Module.Flat (MvPowerSeries (Fin d) k) T :=
    Module.Flat.of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq
      (MvPowerSeries (Fin d) k) T rfl
  haveI hfree : Module.Free (MvPowerSeries (Fin d) k) T := Module.free_of_flat_of_isLocalRing

  let ι := Module.Free.ChooseBasisIndex (MvPowerSeries (Fin d) k) T
  let b : Module.Basis ι (MvPowerSeries (Fin d) k) T := Module.Free.chooseBasis _ _
  have huniqT : ∀ a a' : ι → MvPowerSeries (Fin d) k, ∑ i, a i • b i = ∑ i, a' i • b i → a = a' := by
    intro a a' h
    have hli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have h0 : ∑ i, (a i - a' i) • b i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
    funext i
    exact sub_eq_zero.mp (hli _ h0 i)
  have hexp : ∀ x : MvPowerSeries (Fin d) k, x = ∑ i, φ (b.repr (e.symm x) i) * e (b i) := by
    intro x
    conv_lhs => rw [← he_symm x, ← b.sum_repr (e.symm x)]
    rw [map_sum]
    simp only [he_smul]
  have huniq : ∀ a a' : ι → MvPowerSeries (Fin d) k,
      ∑ i, φ (a i) * e (b i) = ∑ i, φ (a' i) * e (b i) → a = a' := by
    intro a a' h
    refine huniqT a a' (e.injective ?_)
    rw [map_sum, map_sum]
    simp only [he_smul]
    exact h

  let πg := Ideal.Quotient.mk (Ideal.span (Set.range g))
  have hπC : ∀ c : k, πg (MvPowerSeries.C c) = algebraMap k _ c := fun c => by
    rw [IsScalarTower.algebraMap_apply k (MvPowerSeries (Fin d) k) (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g)),
      Ideal.Quotient.algebraMap_eq, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hφmod : ∀ r, πg (φ r) = algebraMap k _ (MvPowerSeries.constantCoeff r) := by
    intro r
    have hr : r - MvPowerSeries.C (MvPowerSeries.constantCoeff r) ∈ 𝔫 :=
      MvPowerSeries.SubstFree.mem_span_range_X_of_constantCoeff
        (by rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self])
    have h1 : φ r - MvPowerSeries.C (MvPowerSeries.constantCoeff r) ∈ Ideal.span (Set.range g) := by
      rw [← hφC, ← map_sub]
      have h2 := Ideal.mem_map_of_mem φ hr
      rwa [Ideal.map_span, hrg] at h2
    rw [← hπC, eq_comm, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    rw [← Ideal.neg_mem_iff, neg_sub]
    exact h1
  let ev : ι → MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g) := fun i => πg (e (b i))
  have hspan : ⊤ ≤ Submodule.span k (Set.range ev) := by
    rintro y -
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hexp x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_mul, hφmod, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent k ev := by
    rw [Fintype.linearIndependent_iff]
    intro l hl i
    have hz : ∑ i, MvPowerSeries.C (l i) * e (b i) ∈ Ideal.span (Set.range g) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hl]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hπC, ← Algebra.smul_def]
    have hw : ∑ i, (MvPowerSeries.C (l i) : MvPowerSeries (Fin d) k) • b i ∈
        (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T) := by
      rw [show (𝔫 • ⊤ : Submodule (MvPowerSeries (Fin d) k) T) = 𝔫 ^ 1 • ⊤ by rw [pow_one], hsmul 1, pow_one,
        map_sum]
      simp only [he_smul, hφC]
      exact hz
    rw [← b.span_eq, Submodule.mem_ideal_smul_span_iff_exists_sum] at hw
    obtain ⟨a, ha, hsum⟩ := hw
    rw [Finsupp.sum_fintype a (fun i c => c • b i) (fun i => zero_smul (MvPowerSeries (Fin d) k) (b i))] at hsum
    have heq : (⇑a) = fun i => MvPowerSeries.C (l i) := huniqT _ _ hsum
    have hai : MvPowerSeries.C (l i) ∈ 𝔫 := by
      rw [← congrFun heq i]
      exact ha i
    have := MvPowerSeries.SubstFree.constantCoeff_eq_zero_of_mem_span_range_X hai
    rwa [MvPowerSeries.constantCoeff_C] at this
  have hcard : Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g)) = Fintype.card ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk hli hspan)

  let σe : ι ≃ Fin (Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) :=
    Fintype.equivFinOfCardEq hcard.symm
  refine ⟨hfinT, hflat, fun j => e (b (σe.symm j)), fun x => ⟨fun j => b.repr (e.symm x) (σe.symm j), ?_, ?_⟩⟩
  ·
    show x = ∑ j, MvPowerSeries.subst g (b.repr (e.symm x) (σe.symm j)) * e (b (σe.symm j))
    simp only [← hφ]
    rw [Equiv.sum_comp σe.symm (fun i => φ (b.repr (e.symm x) i) * e (b i))]
    exact hexp x
  ·
    intro c' hc'
    simp only [← hφ] at hc'
    have h1 : ∑ i, φ (c' (σe i)) * e (b i) = ∑ i, φ (b.repr (e.symm x) i) * e (b i) := by
      rw [← hexp x, hc', ← Equiv.sum_comp σe.symm (fun i => φ (c' (σe i)) * e (b i))]
      simp only [Equiv.apply_symm_apply]
    have h2 := huniq _ _ h1
    funext j
    have := congrFun h2 (σe.symm j)
    simpa only [Equiv.apply_symm_apply] using this

end S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient
end P2MW
export P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient (solution)
