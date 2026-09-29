-- Prove2me | solution 1 for IsDiscreteValuationRing.iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/bfa91373-7676-5e9d-a2fc-8152b0655822

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupGenerator
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top

set_option autoImplicit false

namespace HerbrandPort

open IsLocalRing IsDiscreteValuationRing Polynomial

namespace FixedPoints

variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]
variable {H : Subgroup G} [H.Normal]

theorem coe_quotientMk_smul_subring (g : G) (x : FixedPoints.subring R H) :
    (((QuotientGroup.mk g : G ⧸ H) • x : FixedPoints.subring R H) : R) = g • (x : R) :=
  rfl

theorem coe_quotientMk_smul_sub_subring (g : G) (x : FixedPoints.subring R H) :
    (((QuotientGroup.mk g : G ⧸ H) • x - x : FixedPoints.subring R H) : R) =
      g • (x : R) - (x : R) :=
  rfl

end FixedPoints

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

variable (R G) in

noncomputable def fixedSubringRamificationDepth (H : Subgroup G) [H.Normal] (σ : G ⧸ H) :
    ℕ∞ :=
  ⨅ x : FixedPoints.subring R H,
    addVal R ((σ • x - x : FixedPoints.subring R H) : R)

theorem fixedSubringRamificationDepth_def (H : Subgroup G) [H.Normal] (σ : G ⧸ H) :
    fixedSubringRamificationDepth R G H σ =
      ⨅ x : FixedPoints.subring R H,
        addVal R ((σ • x - x : FixedPoints.subring R H) : R) :=
  rfl

variable (R G) in

noncomputable def cosetRamificationDepthSum (H : Subgroup G) [Fintype H] (τ₀ : G) : ℕ∞ :=
  ∑ h : H, ramificationDepth R G (τ₀ * (h : G))

theorem cosetRamificationDepthSum_def (H : Subgroup G) [Fintype H] (τ₀ : G) :
    cosetRamificationDepthSum R G H τ₀ =
      ∑ h : H, ramificationDepth R G (τ₀ * (h : G)) :=
  rfl

variable (R G) in

def RamificationDepthCosetLemma (H : Subgroup G) [H.Normal] [Fintype H] : Prop :=
  ∀ τ₀ : G,
    fixedSubringRamificationDepth R G H (QuotientGroup.mk τ₀) =
      cosetRamificationDepthSum R G H τ₀

end IsDiscreteValuationRing

namespace MulSemiringAction

section VanishingPoly

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

variable (R) in

noncomputable def prodXSubSMulSubgroup (H : Subgroup G) [Fintype H] (x : R) : R[X] :=
  ∏ h : H, (X - C ((h : G) • x))

theorem prodXSubSMulSubgroup_def (H : Subgroup G) [Fintype H] (x : R) :
    prodXSubSMulSubgroup R H x = ∏ h : H, (X - C ((h : G) • x)) :=
  rfl

theorem eval_prodXSubSMulSubgroup_self (H : Subgroup G) [Fintype H] (x : R) :
    (prodXSubSMulSubgroup R H x).eval x = 0 := by
  rw [prodXSubSMulSubgroup_def, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ (1 : H)) ?_
  simp

theorem smul_prodXSubSMulSubgroup (H : Subgroup G) [Fintype H] (x : R) (g : G) :
    g • prodXSubSMulSubgroup R H x = ∏ h : H, (X - C ((g * (h : G)) • x)) := by
  rw [prodXSubSMulSubgroup_def, Finset.smul_prod']
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul]

theorem smul_coe_prodXSubSMulSubgroup (H : Subgroup G) [Fintype H] (x : R) (g : H) :
    (g : G) • prodXSubSMulSubgroup R H x = prodXSubSMulSubgroup R H x := by
  rw [smul_prodXSubSMulSubgroup, prodXSubSMulSubgroup_def]
  exact Fintype.prod_bijective (fun h : H => g * h) (Group.mulLeft_bijective g) _ _
    fun h => by rw [Subgroup.coe_mul]

theorem coeff_prodXSubSMulSubgroup_mem (H : Subgroup G) [Fintype H] (x : R) (n : ℕ) :
    (prodXSubSMulSubgroup R H x).coeff n ∈ FixedPoints.subring R H := by
  refine FixedPoints.mem_subring_iff.mpr fun m => ?_
  show (m : G) • (prodXSubSMulSubgroup R H x).coeff n = (prodXSubSMulSubgroup R H x).coeff n
  rw [← Polynomial.coeff_smul, smul_coe_prodXSubSMulSubgroup]

theorem eval_smul_prodXSubSMulSubgroup (H : Subgroup G) [Fintype H] (x : R) (g : G) :
    (g • prodXSubSMulSubgroup R H x).eval x = ∏ h : H, (x - (g * (h : G)) • x) := by
  rw [smul_prodXSubSMulSubgroup, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

theorem prodXSubSMulSubgroup_dvd_of_isRoot {R : Type*} [CommRing R] [IsDomain R]
    {G : Type*} [Group G] [MulSemiringAction G R] {H : Subgroup G} [Fintype H] {x : R}
    (hinj : Function.Injective (fun h : H => (h : G) • x))
    {F : R[X]} (hF : ∀ h : H, F.IsRoot ((h : G) • x)) :
    prodXSubSMulSubgroup R H x ∣ F := by
  classical
  rcases eq_or_ne F 0 with rfl | hF0
  · exact dvd_zero _
  · have hle : (Finset.univ.val.map fun h : H => (h : G) • x) ≤ F.roots := by
      rw [Multiset.le_iff_subset (Finset.univ.nodup.map hinj)]
      intro a ha
      obtain ⟨h, -, rfl⟩ := Multiset.mem_map.mp ha
      exact (Polynomial.mem_roots hF0).mpr (hF h)
    have hkey := (Multiset.prod_X_sub_C_dvd_iff_le_roots hF0
      (Finset.univ.val.map fun h : H => (h : G) • x)).mpr hle
    rw [Multiset.map_map] at hkey
    rw [prodXSubSMulSubgroup_def, Finset.prod_eq_multiset_prod]
    exact hkey

end VanishingPoly

section FixedBase

variable {A R : Type*} [CommSemiring A] [CommRing R] [Algebra A R]
variable {M : Type*} [Monoid M] [MulSemiringAction M R]

theorem smul_map_algebraMap {σ : M}
    (hfix : ∀ a : A, σ • algebraMap A R a = algebraMap A R a) (f : A[X]) :
    σ • f.map (algebraMap A R) = f.map (algebraMap A R) := by
  ext n
  rw [Polynomial.coeff_smul, Polynomial.coeff_map]
  exact hfix _

theorem smul_aeval {σ : M}
    (hfix : ∀ a : A, σ • algebraMap A R a = algebraMap A R a) (f : A[X]) (x : R) :
    σ • (Polynomial.aeval x f : R) = Polynomial.aeval (σ • x) f := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval_map, ← Polynomial.eval_map]
  conv_rhs => rw [← smul_map_algebraMap hfix f]
  rw [Polynomial.smul_eval_smul]

end FixedBase

section Injective

variable {A R : Type*} [CommSemiring A] [CommRing R] [Algebra A R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem injective_subgroup_smul_of_adjoin_singleton_eq_top [FaithfulSMul G R]
    (hGfix : ∀ (σ : G) (a : A), σ • algebraMap A R a = algebraMap A R a)
    {x : R} (hx : Algebra.adjoin A {x} = ⊤) (H : Subgroup G) :
    Function.Injective (fun h : H => (h : G) • x) := by
  intro h h' heq
  have heq' : (h : G) • x = (h' : G) • x := heq
  have hfixx : ((h' : G)⁻¹ * (h : G)) • x = x := by
    rw [mul_smul, heq', inv_smul_smul]
  have hone : (h' : G)⁻¹ * (h : G) = 1 := by
    refine FaithfulSMul.eq_of_smul_eq_smul (α := R) fun r => ?_
    rw [one_smul]
    have hdvd := MulSemiringAction.smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top
      (σ := (h' : G)⁻¹ * (h : G)) (fun a => hGfix _ a) hx r
    rw [hfixx, sub_self, zero_dvd_iff, sub_eq_zero] at hdvd
    exact hdvd
  exact Subtype.ext (inv_mul_eq_one.mp hone).symm

end Injective

section Divisibility

variable {A R : Type*} [CommSemiring A] [CommRing R] [Algebra A R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem smul_sub_dvd_prod_sub_smul {H : Subgroup G} [Fintype H] {y₀ : R}
    (hy : ∀ z ∈ FixedPoints.subring R H, z ∈ Algebra.adjoin A {y₀})
    {τ₀ : G} (hfix : ∀ a : A, τ₀ • algebraMap A R a = algebraMap A R a) (x : R) :
    τ₀ • y₀ - y₀ ∣ ∏ h : H, (x - (τ₀ * (h : G)) • x) := by
  classical
  have hcoeff : ∀ n : ℕ, τ₀ • y₀ - y₀ ∣
      (τ₀ • prodXSubSMulSubgroup R H x - prodXSubSMulSubgroup R H x).coeff n := by
    intro n
    rw [Polynomial.coeff_sub, Polynomial.coeff_smul]
    exact MulSemiringAction.smul_sub_dvd_smul_sub_of_mem_adjoin_singleton hfix
      (hy _ (coeff_prodXSubSMulSubgroup_mem H x n))
  have heval : τ₀ • y₀ - y₀ ∣
      (τ₀ • prodXSubSMulSubgroup R H x - prodXSubSMulSubgroup R H x).eval x := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    exact Finset.dvd_sum fun n _ => (hcoeff n).mul_right _
  rwa [Polynomial.eval_sub, eval_prodXSubSMulSubgroup_self, sub_zero,
    eval_smul_prodXSubSMulSubgroup] at heval

theorem prod_sub_smul_dvd_smul_sub [IsDomain R] [FaithfulSMul G R]
    (hGfix : ∀ (σ : G) (a : A), σ • algebraMap A R a = algebraMap A R a)
    {H : Subgroup G} [Fintype H] {x : R} (hx : Algebra.adjoin A {x} = ⊤)
    {y₀ : R} (hy₀ : y₀ ∈ FixedPoints.subring R H) (τ₀ : G) :
    (∏ h : H, (x - (τ₀ * (h : G)) • x)) ∣ τ₀ • y₀ - y₀ := by
  classical

  have hy₀adj : y₀ ∈ Algebra.adjoin A {x} := hx ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hy₀adj
  obtain ⟨f, hf⟩ := hy₀adj

  have hroot : ∀ h : H,
      (f.map (algebraMap A R) - Polynomial.C y₀).IsRoot ((h : G) • x) := by
    intro h
    have h1 : (f.map (algebraMap A R)).eval ((h : G) • x) = (h : G) • y₀ := by
      rw [← hf, smul_aeval (hGfix (h : G)) f x, Polynomial.aeval_def, ← Polynomial.eval_map]
    have h2 : (h : G) • y₀ = y₀ := hy₀ h
    show (f.map (algebraMap A R) - Polynomial.C y₀).eval ((h : G) • x) = 0
    rw [Polynomial.eval_sub, Polynomial.eval_C, h1, h2, sub_self]

  obtain ⟨q, hq⟩ := prodXSubSMulSubgroup_dvd_of_isRoot
    (injective_subgroup_smul_of_adjoin_singleton_eq_top hGfix hx H) hroot

  have heval : (τ₀ • prodXSubSMulSubgroup R H x).eval x ∣
      (τ₀ • (f.map (algebraMap A R) - Polynomial.C y₀)).eval x :=
    Polynomial.eval_dvd ⟨τ₀ • q, by rw [hq, smul_mul']⟩
  rw [eval_smul_prodXSubSMulSubgroup, smul_sub, Polynomial.smul_C,
    smul_map_algebraMap (hGfix τ₀), Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_map, ← Polynomial.aeval_def, hf,
    show y₀ - τ₀ • y₀ = -(τ₀ • y₀ - y₀) by rw [neg_sub]] at heval
  exact dvd_neg.mp heval

end Divisibility

end MulSemiringAction

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]
variable {A : Type*} [CommSemiring A] [Algebra A R]

theorem addVal_finset_prod {ι : Type*} (s : Finset ι) (f : ι → R) :
    addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) := by
  induction s using Finset.cons_induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, addVal_one]
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, addVal_mul, ih]

theorem fixedSubringRamificationDepth_eq_addVal {H : Subgroup G} [H.Normal]
    {τ₀ : G} (hfix : ∀ a : A, τ₀ • algebraMap A R a = algebraMap A R a)
    {y₀ : R} (hy₀ : y₀ ∈ FixedPoints.subring R H)
    (hy : ∀ z ∈ FixedPoints.subring R H, z ∈ Algebra.adjoin A {y₀}) :
    fixedSubringRamificationDepth R G H (QuotientGroup.mk τ₀) =
      addVal R (τ₀ • y₀ - y₀) := by
  rw [fixedSubringRamificationDepth_def]
  refine le_antisymm (le_trans (iInf_le _ ⟨y₀, hy₀⟩) (le_of_eq ?_)) (le_iInf fun z => ?_)
  · rw [FixedPoints.coe_quotientMk_smul_sub_subring]
  · rw [FixedPoints.coe_quotientMk_smul_sub_subring]
    exact addVal_le_iff_dvd.mpr
      (MulSemiringAction.smul_sub_dvd_smul_sub_of_mem_adjoin_singleton hfix (hy _ z.2))

theorem cosetRamificationDepthSum_eq_addVal {H : Subgroup G} [Fintype H]
    (hGfix : ∀ (σ : G) (a : A), σ • algebraMap A R a = algebraMap A R a)
    {x : R} (hx : Algebra.adjoin A {x} = ⊤) (τ₀ : G) :
    cosetRamificationDepthSum R G H τ₀ =
      addVal R (∏ h : H, (x - (τ₀ * (h : G)) • x)) := by
  rw [cosetRamificationDepthSum_def, addVal_finset_prod]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [ramificationDepth_eq_addVal_of_adjoin_singleton_eq_top
    (fun a => hGfix (τ₀ * (h : G)) a) hx]
  exact (addVal R).map_sub_swap _ _

theorem ramificationDepthCosetLemma_of_monogenic [FaithfulSMul G R]
    {H : Subgroup G} [H.Normal] [Fintype H]
    (hGfix : ∀ (σ : G) (a : A), σ • algebraMap A R a = algebraMap A R a)
    {x : R} (hx : Algebra.adjoin A {x} = ⊤)
    {y₀ : R} (hy₀ : y₀ ∈ FixedPoints.subring R H)
    (hy : ∀ z ∈ FixedPoints.subring R H, z ∈ Algebra.adjoin A {y₀}) :
    RamificationDepthCosetLemma R G H := by
  intro τ₀
  rw [fixedSubringRamificationDepth_eq_addVal (hGfix τ₀) hy₀ hy,
    cosetRamificationDepthSum_eq_addVal hGfix hx τ₀]
  exact le_antisymm
    (addVal_le_iff_dvd.mpr (MulSemiringAction.smul_sub_dvd_prod_sub_smul hy (hGfix τ₀) x))
    (addVal_le_iff_dvd.mpr (MulSemiringAction.prod_sub_smul_dvd_smul_sub hGfix hx hy₀ τ₀))

end IsDiscreteValuationRing

end HerbrandPort

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [FaithfulSMul G R]
    {A : Type*} [CommSemiring A] [Algebra A R]
    (hA : ∀ (σ : G) (a : A), σ • algebraMap A R a = algebraMap A R a)
    {H : Subgroup G} [H.Normal] [Fintype H]
    {x : R} (hx : Algebra.adjoin A {x} = ⊤)
    {y : R} (hy : y ∈ FixedPoints.subring R H)
    (hy' : ∀ z ∈ FixedPoints.subring R H, z ∈ Algebra.adjoin A {y}) (τ : G) :
    (⨅ z : FixedPoints.subring R H,
        IsDiscreteValuationRing.addVal R
          (((QuotientGroup.mk τ : G ⧸ H) • z - z : FixedPoints.subring R H) : R)) =
      ∑ h : H, IsDiscreteValuationRing.ramificationDepth R G (τ * (h : G)) :=
  HerbrandPort.IsDiscreteValuationRing.ramificationDepthCosetLemma_of_monogenic hA hx hy hy' τ

end S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top
end P2MW
export P2MW.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top (solution)
