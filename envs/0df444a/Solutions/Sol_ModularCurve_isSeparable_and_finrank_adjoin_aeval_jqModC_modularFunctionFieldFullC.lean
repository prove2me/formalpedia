-- Prove2me | solution 1 for ModularCurve.isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e23518b8-e925-51d4-bec5-5e3d2b85e9b0

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open Polynomial IntermediateField

namespace LEG1S2SeparatingPoly

section Hahn

variable {Γ : Type*} [LinearOrder Γ] [Zero Γ] {R : Type*} [AddCommMonoid R]

theorem sum_ne_zero_of_order_injOn {ι : Type*} (s : Finset ι) (x : ι → HahnSeries Γ R)
    (h0 : ∃ i ∈ s, x i ≠ 0)
    (hinj : ∀ i ∈ s, ∀ k ∈ s, x i ≠ 0 → x k ≠ 0 → (x i).order = (x k).order → i = k) :
    ∑ i ∈ s, x i ≠ 0 := by
  classical
  set t : Finset ι := s.filter fun i => x i ≠ 0 with ht
  have htne : t.Nonempty := by
    obtain ⟨i, hi, hx⟩ := h0
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hx⟩⟩
  obtain ⟨i₀, hi₀t, hmin⟩ := t.exists_min_image (fun i => (x i).order) htne
  obtain ⟨hi₀s, hx₀⟩ := Finset.mem_filter.mp hi₀t
  intro hsum
  have hcoeff : (∑ i ∈ s, x i).coeff (x i₀).order = (x i₀).coeff (x i₀).order := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_single_of_mem i₀ hi₀s fun i his hine => ?_
    by_cases hxi : x i = 0
    · rw [hxi, HahnSeries.coeff_zero]
    · have hit : i ∈ t := Finset.mem_filter.mpr ⟨his, hxi⟩
      have hle := hmin i hit
      have hne : (x i₀).order ≠ (x i).order := fun h => hine (hinj i his i₀ hi₀s hxi hx₀ h.symm)
      exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_le_of_ne hle hne)
  rw [hsum, HahnSeries.coeff_zero] at hcoeff
  exact hx₀ (HahnSeries.coeff_order_eq_zero.mp hcoeff.symm)

end Hahn

section Orders

p2m_open "ModularCurve~order_jqModC"

variable (K : Type*) [Field K]

local notation "L" => LaurentSeries K

theorem jqModC_ne_zero' : jqModC K ≠ 0 := jqModC_ne_zero_of_nontrivial K

theorem order_jqModC : (jqModC K).order = -1 := by
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) ?_
  · rw [coeff_jqModC_neg_one]; exact one_ne_zero
  · exact (HahnSeries.le_order_iff_forall (jqModC_ne_zero' K)).mpr fun n hn => coeff_jqModC_of_lt K hn

theorem coeff_aeval_laurent (P : K[X]) (x : L) (n : ℤ) :
    (aeval x P).coeff n = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (x ^ i).coeff n := by
  rw [aeval_def, eval₂_eq_sum_range, HahnSeries.coeff_sum]
  simp only [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]

theorem coeff_aeval_jqModC_neg_natDegree (P : K[X]) :
    (aeval (jqModC K) P).coeff (-(P.natDegree : ℤ)) = P.leadingCoeff := by
  rw [coeff_aeval_laurent, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add,
    coeff_jqModC_pow_self, mul_one, leadingCoeff]
  intro i hi
  rw [coeff_jqModC_pow_of_lt K (by simpa using Finset.mem_range.mp hi), mul_zero]

theorem coeff_aeval_jqModC_of_lt (P : K[X]) {n : ℤ} (hn : n < -(P.natDegree : ℤ)) :
    (aeval (jqModC K) P).coeff n = 0 := by
  rw [coeff_aeval_laurent]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [coeff_jqModC_pow_of_lt K (lt_of_lt_of_le hn (by simpa using hi')), mul_zero]

theorem aeval_jqModC_ne_zero {P : K[X]} (hP : P ≠ 0) : aeval (jqModC K) P ≠ 0 := by
  intro h
  have := coeff_aeval_jqModC_neg_natDegree K P
  rw [h, HahnSeries.coeff_zero] at this
  exact leadingCoeff_ne_zero.mpr hP this.symm

theorem order_aeval_jqModC {P : K[X]} (hP : P ≠ 0) :
    (aeval (jqModC K) P).order = -(P.natDegree : ℤ) := by
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) ?_
  · rw [coeff_aeval_jqModC_neg_natDegree]; exact leadingCoeff_ne_zero.mpr hP
  · exact (HahnSeries.le_order_iff_forall (aeval_jqModC_ne_zero K hP)).mpr
      fun n hn => coeff_aeval_jqModC_of_lt K P hn

variable {K}

theorem order_aeval_aeval_jqModC {r : K[X]} (hr : 0 < r.natDegree) {P : K[X]} (hP : P ≠ 0) :
    aeval (aeval (jqModC K) r) P ≠ 0 ∧
      (aeval (aeval (jqModC K) r) P).order = -((r.natDegree : ℤ) * P.natDegree) := by
  have hcomp : P.comp r ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [natDegree_comp, natDegree_zero, mul_eq_zero] at this
    rcases this with h1 | h2
    · rw [natDegree_eq_zero] at h1
      obtain ⟨c, rfl⟩ := h1
      rw [C_comp] at h
      exact hP h
    · omega
  rw [← aeval_comp]
  refine ⟨aeval_jqModC_ne_zero K hcomp, ?_⟩
  rw [order_aeval_jqModC K hcomp, natDegree_comp]
  push_cast
  ring

end Orders

section Level

p2m_open "ModularCurve~order_jqModC"

variable (K : Type*) [Field K] (N : ℕ)

local notation "L" => LaurentSeries K
local notation "FN" => modularFunctionFieldFullC K N

def jF : FN := ⟨jqModC K, jqModC_mem_full K N⟩

@[scoped simp] theorem coe_jF : ((jF K N : FN) : L) = jqModC K := rfl

variable (r : K[X])

def sF : FN := aeval (jF K N) r

theorem coe_sF : ((sF K N r : FN) : L) = aeval (jqModC K) r :=
  (aeval_algHom_apply (modularFunctionFieldFullC K N).val (jF K N) r).symm

def Es : IntermediateField K FN := IntermediateField.adjoin K {sF K N r}

def Ej : IntermediateField K FN := IntermediateField.adjoin K {jF K N}

theorem jF_mem_Ej : jF K N ∈ Ej K N := mem_adjoin_simple_self K _

theorem sF_mem_Ej : sF K N r ∈ Ej K N :=
  (algebra_adjoin_le_adjoin K _) (Polynomial.aeval_mem_adjoin_singleton K (jF K N))

theorem Es_le_Ej : Es K N r ≤ Ej K N :=
  adjoin_simple_le_iff.mpr (sF_mem_Ej K N r)

def sE : Es K N r := ⟨sF K N r, mem_adjoin_simple_self K _⟩

variable {K N r}

theorem coe_coe_aeval_sE (P : K[X]) :
    (((aeval (sE K N r) P : Es K N r) : FN) : L) = aeval (aeval (jqModC K) r) P := by
  have h1 : ((aeval (sE K N r) P : Es K N r) : FN) = aeval (sF K N r) P :=
    (aeval_algHom_apply (Es K N r).val (sE K N r) P).symm
  rw [h1, ← coe_sF]
  exact (aeval_algHom_apply (modularFunctionFieldFullC K N).val (sF K N r) P).symm

theorem dvd_order_of_mem_Es (hr : 0 < r.natDegree) {a : FN} (ha : a ∈ Es K N r) (ha0 : a ≠ 0) :
    (r.natDegree : ℤ) ∣ ((a : FN) : L).order := by
  have ha' : (⟨a, ha⟩ : Es K N r) ∈ (adjoin K {sE K N r} : IntermediateField K (Es K N r)) := by
    have htop : (adjoin K {sE K N r} : IntermediateField K (Es K N r)) = ⊤ := by
      apply IntermediateField.lift_injective
      rw [lift_adjoin_simple, lift_top]
      rfl
    rw [htop]; exact mem_top
  obtain ⟨P, Q, hPQ⟩ := (mem_adjoin_simple_iff K _).mp ha'
  have hPQ' : (a : L) = aeval (aeval (jqModC K) r) P / aeval (aeval (jqModC K) r) Q := by
    have := congrArg (fun z : Es K N r => ((z : FN) : L)) hPQ
    simpa only [IntermediateField.coe_div, coe_coe_aeval_sE] using this
  have ha0' : (a : L) ≠ 0 := fun h => ha0 (by exact_mod_cast h)
  have hP : P ≠ 0 := by
    rintro rfl
    exact ha0' (by rw [hPQ', map_zero, zero_div])
  have hQ : Q ≠ 0 := by
    rintro rfl
    exact ha0' (by rw [hPQ', map_zero, div_zero])
  obtain ⟨hPne, hPord⟩ := order_aeval_aeval_jqModC hr hP
  obtain ⟨hQne, hQord⟩ := order_aeval_aeval_jqModC hr hQ
  have hmul : (a : L) * aeval (aeval (jqModC K) r) Q = aeval (aeval (jqModC K) r) P := by
    rw [hPQ', div_mul_cancel₀ _ hQne]
  have := HahnSeries.order_mul ha0' hQne
  rw [hmul, hPord, hQord] at this
  exact ⟨-(P.natDegree : ℤ) + Q.natDegree, by linarith⟩

theorem linearIndependent_pow_jF (hr : 0 < r.natDegree) :
    LinearIndependent (Es K N r) fun i : Fin r.natDegree => (jF K N : FN) ^ (i : ℕ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  obtain ⟨i₁, hi₁⟩ := not_forall.mp hne

  have hL : ∑ i : Fin r.natDegree, (((c i : Es K N r) : FN) : L) * jqModC K ^ (i : ℕ) = 0 := by
    have := congrArg (fun z : FN => (z : L)) hc
    simpa only [IntermediateField.coe_sum, IntermediateField.smul_def, smul_eq_mul,
      IntermediateField.coe_mul, IntermediateField.coe_pow, coe_jF, IntermediateField.coe_zero]
      using this
  have hj := jqModC_ne_zero' K
  refine sum_ne_zero_of_order_injOn (Finset.univ : Finset (Fin r.natDegree))
    (fun i => (((c i : Es K N r) : FN) : L) * jqModC K ^ (i : ℕ)) ?_ ?_ hL
  · refine ⟨i₁, Finset.mem_univ _, mul_ne_zero ?_ (pow_ne_zero _ hj)⟩
    intro h; apply hi₁; exact_mod_cast h
  · intro i _ k _ hxi hxk hik
    have hci : (((c i : Es K N r) : FN) : L) ≠ 0 := fun h => hxi (by rw [h, zero_mul])
    have hck : (((c k : Es K N r) : FN) : L) ≠ 0 := fun h => hxk (by rw [h, zero_mul])
    rw [HahnSeries.order_mul hci (pow_ne_zero _ hj), HahnSeries.order_mul hck (pow_ne_zero _ hj),
      HahnSeries.order_pow, HahnSeries.order_pow, order_jqModC] at hik
    simp only [nsmul_eq_mul, mul_neg, mul_one] at hik
    have hci0 : ((c i : Es K N r) : FN) ≠ 0 := fun h => hci (by rw [h]; rfl)
    have hck0 : ((c k : Es K N r) : FN) ≠ 0 := fun h => hck (by rw [h]; rfl)
    obtain ⟨mi, hmi⟩ := dvd_order_of_mem_Es hr (c i).2 hci0
    obtain ⟨mk, hmk⟩ := dvd_order_of_mem_Es hr (c k).2 hck0
    rw [hmi, hmk] at hik

    have hi := i.2
    have hk := k.2
    apply Fin.ext
    have ht : (r.natDegree : ℤ) * (mi - mk) = (i : ℕ) - (k : ℕ) := by rw [mul_sub]; linarith
    have h1 : ((i : ℕ) : ℤ) - (k : ℕ) < r.natDegree := by omega
    have h2 : -(r.natDegree : ℤ) < ((i : ℕ) : ℤ) - (k : ℕ) := by omega
    have ht0 : mi - mk = 0 := by
      by_contra ht0
      rcases lt_or_gt_of_ne ht0 with hlt | hgt
      · have : (r.natDegree : ℤ) * (mi - mk) ≤ (r.natDegree : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        linarith
      · have : (r.natDegree : ℤ) * 1 ≤ (r.natDegree : ℤ) * (mi - mk) :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        linarith
    rw [ht0, mul_zero] at ht
    omega

variable (K N r) in

def P0 : (Es K N r)[X] := r.map (algebraMap K (Es K N r)) - C (sE K N r)

theorem aeval_jF_P0 : aeval (jF K N : FN) (P0 K N r) = 0 := by
  rw [P0, map_sub, aeval_map_algebraMap, aeval_C, sub_eq_zero]
  rfl

theorem natDegree_P0 : (P0 K N r).natDegree = r.natDegree := by
  rw [P0, natDegree_sub_C, natDegree_map]

theorem P0_ne_zero (hr : 0 < r.natDegree) : P0 K N r ≠ 0 := by
  intro h
  have := natDegree_P0 (K := K) (N := N) (r := r)
  rw [h, natDegree_zero] at this
  omega

theorem derivative_P0 : derivative (P0 K N r) = (derivative r).map (algebraMap K (Es K N r)) := by
  rw [P0, derivative_sub, derivative_map, derivative_C, sub_zero]

theorem isIntegral_jF (hr : 0 < r.natDegree) : IsIntegral (Es K N r) (jF K N : FN) :=
  isAlgebraic_iff_isIntegral.mp ⟨P0 K N r, P0_ne_zero hr, aeval_jF_P0⟩

theorem finrank_and_isSeparable (hr' : derivative r ≠ 0) :
    let M : IntermediateField (Es K N r) FN := extendScalars (Es_le_Ej K N r)
    Module.finrank (Es K N r) M = r.natDegree ∧ IsSeparable (Es K N r) (jF K N : FN) ∧
      M = adjoin (Es K N r) {(jF K N : FN)} := by
  intro M
  have hr : 0 < r.natDegree := by
    rcases Nat.eq_zero_or_pos r.natDegree with h0 | h0
    · exact absurd (by rw [eq_C_of_natDegree_eq_zero h0, derivative_C]) hr'
    · exact h0
  have hM : M = adjoin (Es K N r) {(jF K N : FN)} := extendScalars_adjoin _
  have hint := isIntegral_jF (K := K) (N := N) hr
  haveI : FiniteDimensional (Es K N r) M := by
    rw [hM]; exact adjoin.finiteDimensional hint

  have hlow : r.natDegree ≤ Module.finrank (Es K N r) M := by
    let b : Fin r.natDegree → M := fun i =>
      ⟨(jF K N : FN) ^ (i : ℕ), (mem_extendScalars _).mpr (pow_mem (jF_mem_Ej K N) _)⟩
    have hb : LinearIndependent (Es K N r) b := by
      refine LinearIndependent.of_comp (M.val.toLinearMap) ?_
      exact linearIndependent_pow_jF hr
    simpa using hb.fintype_card_le_finrank

  have hfin : Module.finrank (Es K N r) M = (minpoly (Es K N r) (jF K N : FN)).natDegree := by
    rw [hM]; exact adjoin.finrank hint
  have hup : (minpoly (Es K N r) (jF K N : FN)).natDegree ≤ r.natDegree := by
    rw [← natDegree_P0 (K := K) (N := N) (r := r)]
    exact natDegree_le_natDegree
      (minpoly.degree_le_of_ne_zero (Es K N r) (jF K N : FN) (P0_ne_zero hr) aeval_jF_P0)
  have hdeg : (minpoly (Es K N r) (jF K N : FN)).natDegree = r.natDegree :=
    le_antisymm hup (hlow.trans hfin.le)
  refine ⟨by rw [hfin, hdeg], ?_, hM⟩

  have hP0eq : P0 K N r = C (P0 K N r).leadingCoeff * minpoly (Es K N r) (jF K N : FN) :=
    eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (minpoly.dvd _ _ aeval_jF_P0) (by rw [natDegree_P0, hdeg])
  have hder : derivative (minpoly (Es K N r) (jF K N : FN)) ≠ 0 := by
    intro h0
    have h1 := congrArg derivative hP0eq
    rw [derivative_C_mul, h0, mul_zero, derivative_P0] at h1
    exact ((Polynomial.map_ne_zero_iff (algebraMap K (Es K N r)).injective).mpr hr') h1
  exact (separable_iff_derivative_ne_zero (minpoly.irreducible hint)).mpr hder

theorem isSeparable_of_baseEquiv {E₀ : IntermediateField K L} (E : IntermediateField K FN)
    (φ : E ≃ₐ[K] E₀) (hφ : ∀ y : E, ((φ y : E₀) : L) = ((y : FN) : L)) (x : FN)
    (hx : IsSeparable E₀ (x : L)) : IsSeparable E x := by
  set μ : E[X] := (minpoly E₀ (x : L)).map (φ.symm : E₀ ≃ₐ[K] E).toAlgHom.toRingHom with hμ
  have hμsep : μ.Separable := Polynomial.Separable.map hx
  have hcomp : ((algebraMap FN L).comp (algebraMap E FN)).comp
      (φ.symm : E₀ ≃ₐ[K] E).toAlgHom.toRingHom = algebraMap E₀ L := by
    refine RingHom.ext fun y => ?_
    show (((φ.symm y : E) : FN) : L) = (y : L)
    rw [← hφ, AlgEquiv.apply_symm_apply]
  have haevalL : ((aeval x μ : FN) : L) = 0 := by
    show algebraMap FN L (aeval x μ) = 0
    rw [aeval_def, hom_eval₂, hμ, eval₂_map, hcomp, ← aeval_def]
    exact minpoly.aeval E₀ (x : L)
  have haeval : aeval x μ = 0 := by exact_mod_cast haevalL
  exact hμsep.of_dvd (minpoly.dvd E x haeval)

variable (K N) in

def gens : Set FN := {x | (x : L) ∈ divisorExpansionsC K N}

theorem adjoin_gens : (adjoin K (gens K N) : IntermediateField K FN) = ⊤ := by
  apply IntermediateField.lift_injective
  refine (lift_adjoin K _ (gens K N)).trans (Eq.trans ?_ (lift_top K (modularFunctionFieldFullC K N)).symm)
  apply le_antisymm
  · exact adjoin_le_iff.mpr (by rintro _ ⟨x, hx, rfl⟩; exact x.2)
  · show adjoin K (divisorExpansionsC K N) ≤ _
    refine adjoin.mono K _ _ fun y hy => ?_
    exact ⟨⟨y, subset_adjoin K _ hy⟩, hy, rfl⟩

theorem isSeparable_Ej [NeZero N] (hN : (N : K) ≠ 0) : Algebra.IsSeparable (Ej K N) FN := by

  have hlift : lift (Ej K N) = adjoin K {jqModC K} := lift_adjoin_simple K _ (jF K N)
  let φ : Ej K N ≃ₐ[K] (adjoin K {jqModC K} : IntermediateField K L) :=
    (liftAlgEquiv (Ej K N)).trans (equivOfEq hlift)
  have hφ : ∀ y : Ej K N, ((φ y : (adjoin K {jqModC K} : IntermediateField K L)) : L) =
      ((y : FN) : L) := fun y => rfl
  have hsepG : ∀ x ∈ gens K N, IsSeparable (Ej K N) x := by
    rintro x ⟨d, hd, hdvd, hx⟩
    have hdK : (d : K) ≠ 0 := by
      obtain ⟨e, rfl⟩ := hdvd
      intro h; apply hN; rw [Nat.cast_mul, h, zero_mul]
    refine isSeparable_of_baseEquiv (Ej K N) φ hφ x ?_
    rw [hx]
    exact isSeparable_jqNModC_of_natCast_ne_zero K d hdK

  have hT : (adjoin (Ej K N) (gens K N) : IntermediateField (Ej K N) FN) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ (adjoin K (gens K N) : IntermediateField K FN) := by
      rw [adjoin_gens]; exact mem_top
    have hle : (adjoin K (gens K N) : IntermediateField K FN) ≤
        restrictScalars K (adjoin (Ej K N) (gens K N)) := by
      rw [restrictScalars_adjoin]
      exact adjoin.mono K _ _ Set.subset_union_right
    exact hle hx
  haveI : Algebra.IsSeparable (Ej K N) (adjoin (Ej K N) (gens K N) : IntermediateField (Ej K N) FN) :=
    (isSeparable_adjoin_iff_isSeparable _ _).mpr hsepG
  haveI : Algebra.IsSeparable (Ej K N) (⊤ : IntermediateField (Ej K N) FN) := by
    rw [← hT]; infer_instance
  exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv (F := Ej K N) (E := FN))

theorem main [NeZero N] (hN : (N : K) ≠ 0) (hr' : derivative r ≠ 0) :
    Algebra.IsSeparable (Es K N r) FN ∧
      Module.finrank (Es K N r) FN = r.natDegree * dedekindPsi N := by
  obtain ⟨hfin, hsep, hM⟩ := finrank_and_isSeparable (K := K) (N := N) (r := r) hr'
  set M : IntermediateField (Es K N r) FN := extendScalars (Es_le_Ej K N r)
  haveI hsepFN : Algebra.IsSeparable (Ej K N) FN := isSeparable_Ej hN
  haveI : Algebra.IsSeparable M FN := hsepFN
  haveI : Algebra.IsSeparable (Es K N r) M := by
    rw [hM]; exact (isSeparable_adjoin_simple_iff_isSeparable _ _).mpr hsep
  refine ⟨Algebra.IsSeparable.trans (Es K N r) M FN, ?_⟩
  have hψ : Module.finrank M FN = dedekindPsi N :=
    finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN
  rw [← Module.finrank_mul_finrank (Es K N r) M FN, hfin, hψ]

end Level

end LEG1S2SeparatingPoly
p2m_reactivate "P2MW.S_ModularCurve_isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC.LEG1S2SeparatingPoly"

theorem solution
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (r : Polynomial K) (hr : Polynomial.derivative r ≠ 0) :
    Algebra.IsSeparable
        (IntermediateField.adjoin K
          ({Polynomial.aeval (⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem_full K N⟩ :
              ModularCurve.modularFunctionFieldFullC K N) r} :
            Set (ModularCurve.modularFunctionFieldFullC K N)))
        (ModularCurve.modularFunctionFieldFullC K N) ∧
    Module.finrank
        (IntermediateField.adjoin K
          ({Polynomial.aeval (⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem_full K N⟩ :
              ModularCurve.modularFunctionFieldFullC K N) r} :
            Set (ModularCurve.modularFunctionFieldFullC K N)))
        (ModularCurve.modularFunctionFieldFullC K N) = r.natDegree * ModularCurve.dedekindPsi N :=
  LEG1S2SeparatingPoly.main hN hr

end
p2m_reactivate "P2MW.S_ModularCurve_isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC.LEG1S2SeparatingPoly"

end S_ModularCurve_isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC
end P2MW
export P2MW.S_ModularCurve_isSeparable_and_finrank_adjoin_aeval_jqModC_modularFunctionFieldFullC (solution)
