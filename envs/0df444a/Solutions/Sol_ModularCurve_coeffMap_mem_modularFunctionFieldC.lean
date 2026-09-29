-- Prove2me | solution 1 for ModularCurve.coeffMap_mem_modularFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f06105b8-2eb6-5d47-841c-4954f27f9a83

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_coeffMap_injective
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_le
import Theorems.Thm_ModularCurve_exists_phiIrreducible
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.FieldTheory.Extension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffMap_mem_modularFunctionFieldC
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_coeffMap_mem_modularFunctionFieldC.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "qExpand qExpand_C qExpand_injective dedekindPsi ModularPolynomialData coeffMap coeffMap_coeff jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem coeffMap_qExpand coeffMap_injective isIntegral_jqNModC_all finrank_adjoin_jqNModC_le exists_phiIrreducible ModularPolynomialData.eval_jqNModC_mul_eq_zero order_jqModC coeff_jqModC_neg_one" end ModularCurve
p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.map_jqNModC {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (N : ℕ) [NeZero N] : coeffMap φ (jqNModC R N) = jqNModC S N := by
  rw [jqNModC, coeffMap_qExpand,
    show coeffMap φ (jqModC R) = (jqModC R).map φ from rfl, map_jqModC, jqNModC]

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.order_le_order_coeffMap {R S : Type*} [CommRing R] [CommRing S]
    (res : R →+* S) (w : LaurentSeries R) (h : coeffMap res w ≠ 0) :
    w.order ≤ (coeffMap res w).order := by
  refine HahnSeries.order_le_of_coeff_ne_zero (g := (coeffMap res w).order) fun hzero => ?_
  exact h (HahnSeries.coeff_order_eq_zero.mp (by rw [coeffMap_coeff, hzero, map_zero]))

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_C qExpand_injective dedekindPsi ModularPolynomialData coeffMap coeffMap_coeff jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem coeffMap_qExpand coeffMap_injective isIntegral_jqNModC_all finrank_adjoin_jqNModC_le exists_phiIrreducible ModularPolynomialData.eval_jqNModC_mul_eq_zero order_jqModC coeff_jqModC_neg_one"
namespace W1
p2m_open "ModularCurve"

variable {L : Type*} [Field L] {O : Subring L}

private def odvd (O : Subring L) (c b : L) : Prop := ∃ o : O, b = c * (o : L)

private theorem odvd_refl (c : L) : odvd O c c := ⟨1, by simp⟩

private theorem odvd_zero (c : L) : odvd O c 0 := ⟨0, by simp⟩

private theorem odvd_trans {a b c : L} (h1 : odvd O a b) (h2 : odvd O b c) : odvd O a c := by
  obtain ⟨o1, rfl⟩ := h1
  obtain ⟨o2, rfl⟩ := h2
  exact ⟨o1 * o2, by push_cast; ring⟩

private theorem odvd_total (hO : ∀ z : L, z ∈ O ∨ z⁻¹ ∈ O) (c b : L) :
    odvd O c b ∨ odvd O b c := by
  rcases eq_or_ne c 0 with rfl | hc
  · rcases eq_or_ne b 0 with rfl | hb
    · exact Or.inl (odvd_refl 0)
    · exact Or.inr (odvd_zero b)
  rcases eq_or_ne b 0 with rfl | hb
  · exact Or.inl (odvd_zero c)
  rcases hO (b / c) with h | h
  · exact Or.inl ⟨⟨b / c, h⟩, by field_simp⟩
  · rw [inv_div] at h
    exact Or.inr ⟨⟨c / b, h⟩, by field_simp⟩

private theorem exists_odvd_min (hO : ∀ z : L, z ∈ O ∨ z⁻¹ ∈ O) :
    ∀ (s : List L), s ≠ [] → ∃ c ∈ s, ∀ b ∈ s, odvd O c b
  | [], h => absurd rfl h
  | [a], _ => ⟨a, List.mem_singleton.mpr rfl, fun b hb => by
      rw [List.mem_singleton.mp hb]; exact odvd_refl a⟩
  | a :: b :: t, _ => by
      obtain ⟨c, hc, hcall⟩ := exists_odvd_min hO (b :: t) (List.cons_ne_nil b t)
      rcases odvd_total hO a c with h | h
      · exact ⟨a, List.mem_cons_self .., fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact odvd_refl z
          · exact odvd_trans h (hcall z hz)⟩
      · exact ⟨c, List.mem_cons_of_mem a hc, fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact h
          · exact hcall z hz⟩

variable {K : Type*} [Field K]

private theorem algebraMap_laurent_eq_C {R : Type*} [CommRing R] (a : R) :
    (algebraMap R (LaurentSeries R)) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply', ← PowerSeries.C_eq_algebraMap, HahnSeries.ofPowerSeries_C]

private theorem coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a : R) :
    coeffMap φ ((algebraMap R (LaurentSeries R)) a) = (algebraMap S (LaurentSeries S)) (φ a) := by
  rw [algebraMap_laurent_eq_C, algebraMap_laurent_eq_C]
  ext k
  rw [coeffMap_coeff,
    show (HahnSeries.C a : LaurentSeries R).coeff k = (HahnSeries.single (0 : ℤ) a).coeff k
      from rfl,
    show (HahnSeries.C (φ a) : LaurentSeries S).coeff k
      = (HahnSeries.single (0 : ℤ) (φ a)).coeff k from rfl]
  rcases eq_or_ne k 0 with rfl | hk
  · rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_same]
  · rw [HahnSeries.coeff_single_of_ne hk, HahnSeries.coeff_single_of_ne hk, map_zero]

private theorem coeffMap_aeval {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (P : Polynomial R) (z : LaurentSeries R) :
    coeffMap φ (Polynomial.aeval z P) = Polynomial.aeval (coeffMap φ z) (P.map φ) := by
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def,
    Polynomial.eval₂_map]
  congr 1
  refine RingHom.ext fun a => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply]
  exact coeffMap_C φ a

private theorem jqModC_ne_zero (K : Type*) [Field K] : jqModC K ≠ 0 := by
  intro h
  have h1 := coeff_jqModC_neg_one K
  rw [h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

private theorem order_jqModC_pow (K : Type*) [Field K] (i : ℕ) :
    (jqModC K ^ i).order = -(i : ℤ) := by
  rw [HahnSeries.order_pow, order_jqModC K, nsmul_eq_mul]
  ring

private theorem leadingCoeff_jqModC (K : Type*) [Field K] : (jqModC K).leadingCoeff = 1 := by
  rw [HahnSeries.leadingCoeff_eq, order_jqModC K]
  exact coeff_jqModC_neg_one K

private theorem leadingCoeff_jqModC_pow (K : Type*) [Field K] (i : ℕ) :
    (jqModC K ^ i).leadingCoeff = 1 := by
  induction i with
  | zero => rw [pow_zero]; exact HahnSeries.leadingCoeff_one
  | succ n ih =>
      rw [pow_succ, HahnSeries.leadingCoeff_mul, ih, leadingCoeff_jqModC, one_mul]

private theorem coeff_jqModC_pow (K : Type*) [Field K] (i : ℕ) :
    (jqModC K ^ i).coeff (-(i : ℤ)) = 1 := by
  have h1 := leadingCoeff_jqModC_pow K i
  rwa [HahnSeries.leadingCoeff_eq, order_jqModC_pow K i] at h1

private theorem coeff_sum {Γ R : Type*} [PartialOrder Γ] [AddCommMonoid R] {ι : Type*}
    (s : Finset ι) (f : ι → HahnSeries Γ R) (k : Γ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, HahnSeries.coeff_zero]
  | cons a t ha ih => rw [Finset.sum_cons, Finset.sum_cons, HahnSeries.coeff_add, ih]

private theorem aeval_jqModC_ne_zero {K : Type*} [Field K] {P : Polynomial K} (hP : P ≠ 0) :
    Polynomial.aeval (jqModC K) P ≠ 0 := by
  have hcf : (Polynomial.aeval (jqModC K) P).coeff (-(P.natDegree : ℤ)) = P.leadingCoeff := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, coeff_sum]
    have h1 : ∀ i ∈ Finset.range (P.natDegree + 1), i ≠ P.natDegree →
        ((algebraMap K (LaurentSeries K)) (P.coeff i) * jqModC K ^ i).coeff
          (-(P.natDegree : ℤ)) = 0 := by
      intro i hi hin
      have hilt : i < P.natDegree :=
        lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
      rw [algebraMap_laurent_eq_C,
        show (HahnSeries.C (P.coeff i) : LaurentSeries K)
          = HahnSeries.single (0 : ℤ) (P.coeff i) from rfl,
        HahnSeries.coeff_single_zero_mul,
        HahnSeries.coeff_eq_zero_of_lt_order
          (by rw [order_jqModC_pow K i]; omega), mul_zero]
    rw [Finset.sum_eq_single P.natDegree h1
        (fun hn' => absurd (Finset.self_mem_range_succ P.natDegree) hn'),
      algebraMap_laurent_eq_C,
      show (HahnSeries.C (P.coeff P.natDegree) : LaurentSeries K)
        = HahnSeries.single (0 : ℤ) (P.coeff P.natDegree) from rfl,
      HahnSeries.coeff_single_zero_mul, coeff_jqModC_pow K P.natDegree, mul_one]
    rfl
  intro h
  rw [h, HahnSeries.coeff_zero] at hcf
  exact Polynomial.leadingCoeff_ne_zero.mpr hP hcf.symm

private def qExpandAlg (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    LaurentSeries K →ₐ[K] LaurentSeries K :=
  { qExpand K N with
    commutes' := fun c => by
      show qExpand K N ((algebraMap K (LaurentSeries K)) c) = (algebraMap K (LaurentSeries K)) c
      rw [algebraMap_laurent_eq_C]
      exact qExpand_C N c }

private theorem aeval_jqNModC_eq_qExpand {K : Type*} [Field K] (N : ℕ) [NeZero N]
    (P : Polynomial K) :
    Polynomial.aeval (jqNModC K N) P = qExpand K N (Polynomial.aeval (jqModC K) P) := by
  show Polynomial.aeval (qExpandAlg K N (jqModC K)) P
    = qExpandAlg K N (Polynomial.aeval (jqModC K) P)
  exact Polynomial.aeval_algHom_apply (qExpandAlg K N) (jqModC K) P

private theorem aeval_jqNModC_ne_zero {K : Type*} [Field K] (N : ℕ) [NeZero N]
    {P : Polynomial K} (hP : P ≠ 0) : Polynomial.aeval (jqNModC K N) P ≠ 0 := by
  rw [aeval_jqNModC_eq_qExpand]
  intro h
  have h2 : qExpand K N (Polynomial.aeval (jqModC K) P) = qExpand K N 0 := by
    rw [h, map_zero]
  exact aeval_jqModC_ne_zero hP (qExpand_injective N h2)

private theorem polys_eq_zero_of_sum_eq_zero {K : Type*} [Field K] (N : ℕ) [NeZero N]
    (hdeg : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        ({jqNModC K N} : Set (LaurentSeries K))) = dedekindPsi N)
    {d : ℕ} (hd : d ≤ dedekindPsi N) (B : Fin d → Polynomial K)
    (hsum : ∑ i : Fin d, Polynomial.aeval (jqModC K) (B i) * jqNModC K N ^ (i : ℕ) = 0) :
    ∀ i, B i = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, hi₀⟩ := hcon
  set Kj := IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) with hKj
  have hα : IsIntegral Kj (jqNModC K N) := isIntegral_jqNModC_all K N
  have hmem : ∀ i : Fin d, Polynomial.aeval (jqModC K) (B i) ∈ Kj := fun i =>
    IntermediateField.algebra_adjoin_le_adjoin K _
      (Polynomial.aeval_mem_adjoin_singleton K (jqModC K))
  set Pm : Polynomial Kj := ∑ i : Fin d,
    Polynomial.monomial (i : ℕ) (⟨Polynomial.aeval (jqModC K) (B i), hmem i⟩ : Kj) with hPm
  have hPmc : ∀ i : Fin d, Pm.coeff (i : ℕ)
      = (⟨Polynomial.aeval (jqModC K) (B i), hmem i⟩ : Kj) := by
    intro i
    rw [hPm, Polynomial.finsetSum_coeff]
    rw [show (∑ b : Fin d, (Polynomial.monomial (b : ℕ)
        (⟨Polynomial.aeval (jqModC K) (B b), hmem b⟩ : Kj)).coeff (i : ℕ))
      = ∑ b : Fin d, if (b : ℕ) = (i : ℕ) then
          (⟨Polynomial.aeval (jqModC K) (B b), hmem b⟩ : Kj) else 0 from
      Finset.sum_congr rfl fun b _ => Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i (fun b _ hb => if_neg (fun h => hb (Fin.ext h)))
      (fun h => absurd (Finset.mem_univ i) h)]
    exact if_pos rfl
  have hPm0 : Pm ≠ 0 := fun h => aeval_jqModC_ne_zero hi₀ (by
    have h1 := hPmc i₀
    rw [h, Polynomial.coeff_zero] at h1
    have h2 : Polynomial.aeval (jqModC K) (B i₀) = ((0 : Kj) : LaurentSeries K) :=
      congrArg Subtype.val h1.symm
    rwa [ZeroMemClass.coe_zero] at h2)
  have haev : Polynomial.aeval (jqNModC K N) Pm = 0 := by
    rw [hPm, map_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hsum
    rw [Polynomial.aeval_monomial]
    congr 1
  have hdegle := minpoly.degree_le_of_ne_zero Kj (jqNModC K N) hPm0 haev
  have hfr : (minpoly Kj (jqNModC K N)).natDegree = dedekindPsi N := by
    rw [← IntermediateField.adjoin.finrank hα]
    exact hdeg
  have hPmdeg : Pm.natDegree < d := by
    refine (Polynomial.natDegree_lt_iff_degree_lt hPm0).mpr ?_
    rw [hPm]
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe d)]
    intro i _
    refine lt_of_le_of_lt (Polynomial.degree_monomial_le _ _) ?_
    exact_mod_cast i.isLt
  have h2 : (minpoly Kj (jqNModC K N)).natDegree ≤ Pm.natDegree :=
    Polynomial.natDegree_le_natDegree hdegle
  omega

private theorem coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    coeffMap φ (jqModC R) = jqModC S := by
  rw [show coeffMap φ (jqModC R) = (jqModC R).map φ from rfl, map_jqModC]

private theorem aeval_jqModC_mem_mffC {K : Type*} [Field K] (N : ℕ) [NeZero N]
    (P : Polynomial K) : Polynomial.aeval (jqModC K) P ∈ modularFunctionFieldC K N := by
  have h1 : Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K))
      ≤ (modularFunctionFieldC K N).toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (jqModC_mem K N))
  exact h1 (Polynomial.aeval_mem_adjoin_singleton K (jqModC K))

private theorem mem_adjoin_jqNModC_of_mem_mffC {L : Type*} [Field L] {N : ℕ} [NeZero N]
    {x : LaurentSeries L} (hx : x ∈ modularFunctionFieldC L N) :
    x ∈ IntermediateField.adjoin
      (IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)))
      ({jqNModC L N} : Set (LaurentSeries L)) := by
  have hle : IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)) ≤
      IntermediateField.adjoin L ({jqModC L, jqNModC L N} : Set (LaurentSeries L)) :=
    IntermediateField.adjoin.mono L _ _
      (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hE := IntermediateField.extendScalars_adjoin hle
  have hcollapse : IntermediateField.adjoin
      (IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)))
      ({jqModC L, jqNModC L N} : Set (LaurentSeries L))
      = IntermediateField.adjoin
        (IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)))
        ({jqNModC L N} : Set (LaurentSeries L)) := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
      (IntermediateField.adjoin.mono _ _ _ ?_)
    · rintro z (rfl | rfl)
      · exact (IntermediateField.adjoin _ _).algebraMap_mem
          (⟨jqModC L, IntermediateField.mem_adjoin_simple_self L (jqModC L)⟩ :
            IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)))
      · exact IntermediateField.subset_adjoin _ _ rfl
    · exact Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)
  rw [modularFunctionFieldC] at hx
  have h2 : x ∈ IntermediateField.extendScalars hle :=
    (IntermediateField.mem_extendScalars _).mpr hx
  rw [hE, hcollapse] at h2
  exact h2

private theorem exists_O_poly {L : Type*} [Field L] {O : Subring L} {c₀ : L} (hc : c₀ ≠ 0)
    {P : Polynomial L} (h : ∀ n, odvd O c₀ (P.coeff n)) :
    ∃ P' : Polynomial O, P'.map O.subtype = Polynomial.C c₀⁻¹ * P := by
  classical
  choose w hw using h
  refine ⟨∑ n ∈ P.support, Polynomial.monomial n (w n), ?_⟩
  ext k
  rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff,
    show (∑ n ∈ P.support, (Polynomial.monomial n (w n)).coeff k)
      = ∑ n ∈ P.support, if n = k then w n else 0 from
      Finset.sum_congr rfl fun n _ => Polynomial.coeff_monomial,
    Finset.sum_ite_eq' P.support k w, Polynomial.coeff_C_mul]
  by_cases hk : k ∈ P.support
  · rw [if_pos hk, hw k, inv_mul_cancel_left₀ hc]
    rfl
  · rw [if_neg hk, Polynomial.notMem_support_iff.mp hk, mul_zero]
    exact map_zero O.subtype

private theorem exists_rep {L : Type*} [Field L] (O : Subring L)
    (hO : ∀ z : L, z ∈ O ∨ z⁻¹ ∈ O) {K : Type*} [Field K] (res : O →+* K) (N : ℕ)
    [NeZero N]
    (hdeg : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        ({jqNModC K N} : Set (LaurentSeries K))) = dedekindPsi N)
    {x : LaurentSeries L} (hx : x ∈ modularFunctionFieldC L N)
    (y : LaurentSeries O) (hy : coeffMap O.subtype y = x) :
    ∃ (d : ℕ) (_ : d ≤ dedekindPsi N) (Dp : Polynomial O) (Ap : Fin d → Polynomial O),
      y * Polynomial.aeval (jqModC O) Dp
          = (∑ i : Fin d, Polynomial.aeval (jqModC O) (Ap i) * jqNModC O N ^ (i : ℕ))
        ∧ Polynomial.map res Dp ≠ 0 := by
  classical
  set Lj := IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)) with hLj
  have hαL : IsIntegral Lj (jqNModC L N) := isIntegral_jqNModC_all L N
  set d := (minpoly Lj (jqNModC L N)).natDegree with hd
  have hdpos : 0 < d := minpoly.natDegree_pos hαL
  obtain ⟨data, -⟩ := ModularCurve.exists_phiIrreducible N
  have hdle : d ≤ dedekindPsi N := by
    rw [hd, ← IntermediateField.adjoin.finrank hαL]
    exact ModularCurve.finrank_adjoin_jqNModC_le L data
  have hxE : x ∈ IntermediateField.adjoin Lj ({jqNModC L N} : Set (LaurentSeries L)) :=
    mem_adjoin_jqNModC_of_mem_mffC hx
  obtain ⟨g₀, hg₀⟩ : ∃ g : Polynomial Lj, Polynomial.aeval (jqNModC L N) g = x := by
    have h1 := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hαL.isAlgebraic
    have h2 : x ∈ Algebra.adjoin Lj ({jqNModC L N} : Set (LaurentSeries L)) := by
      rw [← h1]
      exact hxE
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h2
    obtain ⟨g, hg⟩ := h2
    exact ⟨g, hg⟩
  set g := g₀ %ₘ (minpoly Lj (jqNModC L N)) with hgdef
  have hgx : Polynomial.aeval (jqNModC L N) g = x := by
    have hsplit := Polynomial.modByMonic_add_div g₀ (minpoly Lj (jqNModC L N))
    have h4 := congrArg (Polynomial.aeval (jqNModC L N)) hsplit
    rw [map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at h4
    rw [hgdef, h4]
    exact hg₀
  have hgdeg : g.natDegree < d := by
    rcases eq_or_ne g 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      exact hdpos
    · rw [hd]
      exact Polynomial.natDegree_lt_natDegree h0
        (Polynomial.degree_modByMonic_lt g₀ (minpoly.monic hαL))
  have hxsum : x = ∑ i : Fin d,
      (algebraMap Lj (LaurentSeries L)) (g.coeff (i : ℕ)) * jqNModC L N ^ (i : ℕ) := by
    rw [← hgx, Polynomial.aeval_def,
      Polynomial.eval₂_eq_sum_range' (algebraMap Lj (LaurentSeries L)) hgdeg (jqNModC L N),
      ← Fin.sum_univ_eq_sum_range]
  have hfrac : ∀ i : Fin d, ∃ (r s : Polynomial L),
      Polynomial.aeval (jqModC L) s ≠ 0 ∧
      (algebraMap Lj (LaurentSeries L)) (g.coeff (i : ℕ)) * Polynomial.aeval (jqModC L) s
        = Polynomial.aeval (jqModC L) r := by
    intro i
    have hmem : ((algebraMap Lj (LaurentSeries L)) (g.coeff (i : ℕ)))
        ∈ IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)) := by
      rw [show (algebraMap Lj (LaurentSeries L)) (g.coeff (i : ℕ))
        = ((g.coeff (i : ℕ) : Lj) : LaurentSeries L) from rfl]
      exact (g.coeff (i : ℕ)).2
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff L _).mp hmem
    rcases eq_or_ne ((algebraMap Lj (LaurentSeries L)) (g.coeff (i : ℕ))) 0 with hz | hz
    · exact ⟨0, 1, by rw [map_one]; exact one_ne_zero,
        by rw [hz, map_one, map_zero, zero_mul]⟩
    · have hsevne : Polynomial.aeval (jqModC L) s ≠ 0 := by
        intro h0
        rw [h0, div_zero] at hrs
        exact hz hrs
      refine ⟨r, s, hsevne, ?_⟩
      rw [hrs, div_mul_cancel₀ _ hsevne]
  choose rf sf hsne hseq using hfrac
  set D : Polynomial L := ∏ i : Fin d, sf i with hD
  set A : Fin d → Polynomial L := fun i => rf i * ∏ k ∈ Finset.univ.erase i, sf k with hA
  have hDpoly : D ≠ 0 := by
    rw [hD]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    intro h0
    exact hsne i (by rw [h0, map_zero])
  have hmain : x * Polynomial.aeval (jqModC L) D
      = ∑ i : Fin d, Polynomial.aeval (jqModC L) (A i) * jqNModC L N ^ (i : ℕ) := by
    rw [hxsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsplit : Polynomial.aeval (jqModC L) D
        = Polynomial.aeval (jqModC L) (sf i)
          * Polynomial.aeval (jqModC L) (∏ k ∈ Finset.univ.erase i, sf k) := by
      rw [hD, ← map_mul]
      congr 1
      exact (Finset.mul_prod_erase Finset.univ sf (Finset.mem_univ i)).symm
    calc (algebraMap Lj (LaurentSeries L)) (g.coeff (i : ℕ)) * jqNModC L N ^ (i : ℕ)
          * Polynomial.aeval (jqModC L) D
        = ((algebraMap Lj (LaurentSeries L)) (g.coeff (i : ℕ))
            * Polynomial.aeval (jqModC L) (sf i))
          * (Polynomial.aeval (jqModC L) (∏ k ∈ Finset.univ.erase i, sf k)
            * jqNModC L N ^ (i : ℕ)) := by rw [hsplit]; ring
      _ = Polynomial.aeval (jqModC L) (rf i)
          * (Polynomial.aeval (jqModC L) (∏ k ∈ Finset.univ.erase i, sf k)
            * jqNModC L N ^ (i : ℕ)) := by rw [hseq i]
      _ = Polynomial.aeval (jqModC L) (A i) * jqNModC L N ^ (i : ℕ) := by
          simp only [hA]
          rw [map_mul]
          ring
  set cs : List L := ((List.range (D.natDegree + 1)).map D.coeff)
    ++ (List.finRange d).flatMap
        (fun i => (List.range ((A i).natDegree + 1)).map (A i).coeff) with hcs
  have hcsne : cs ≠ [] := by
    rw [hcs]
    intro h
    have h2 : (List.range (D.natDegree + 1)).map D.coeff = [] :=
      (List.append_eq_nil_iff.mp h).1
    have h3 := List.map_eq_nil_iff.mp h2
    rw [List.range_eq_nil] at h3
    omega
  obtain ⟨c₀, hc₀mem, hc₀all⟩ := exists_odvd_min hO cs hcsne
  have hDleadmem : D.coeff D.natDegree ∈ cs := by
    rw [hcs]
    exact List.mem_append_left _
      (List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_self _)))
  have hc₀ne : c₀ ≠ 0 := by
    intro h0
    obtain ⟨o, ho⟩ := hc₀all _ hDleadmem
    rw [h0, zero_mul] at ho
    exact hDpoly (Polynomial.leadingCoeff_eq_zero.mp ho)
  have hDdvd : ∀ n, odvd O c₀ (D.coeff n) := by
    intro n
    by_cases h : n ≤ D.natDegree
    · refine hc₀all _ ?_
      rw [hcs]
      exact List.mem_append_left _
        (List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le h)))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.not_le.mp h)]
      exact odvd_zero c₀
  have hAdvd : ∀ i n, odvd O c₀ ((A i).coeff n) := by
    intro i n
    by_cases h : n ≤ (A i).natDegree
    · refine hc₀all _ ?_
      rw [hcs]
      refine List.mem_append_right _ ?_
      refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩
      exact List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le h))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.not_le.mp h)]
      exact odvd_zero c₀
  obtain ⟨Dp, hDp⟩ := exists_O_poly hc₀ne hDdvd
  have hApall : ∀ i : Fin d, ∃ P' : Polynomial O,
      P'.map O.subtype = Polynomial.C c₀⁻¹ * A i := fun i => exists_O_poly hc₀ne (hAdvd i)
  choose Ap hAp using hApall
  have hinj : Function.Injective (coeffMap O.subtype) :=
    coeffMap_injective (fun a b h => Subtype.ext h)
  have hOeq : y * Polynomial.aeval (jqModC O) Dp
      = ∑ i : Fin d, Polynomial.aeval (jqModC O) (Ap i) * jqNModC O N ^ (i : ℕ) := by
    apply hinj
    rw [map_mul, map_sum, hy, coeffMap_aeval O.subtype Dp (jqModC O), coeffMap_jqModC, hDp]
    have hterm : ∀ i : Fin d,
        coeffMap O.subtype (Polynomial.aeval (jqModC O) (Ap i) * jqNModC O N ^ (i : ℕ))
          = Polynomial.aeval (jqModC L) (Polynomial.C c₀⁻¹ * A i)
            * jqNModC L N ^ (i : ℕ) := by
      intro i
      rw [map_mul, map_pow, coeffMap_aeval O.subtype (Ap i) (jqModC O), coeffMap_jqModC,
        hAp, ModularCurve.map_jqNModC O.subtype N]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    have hsc : (algebraMap L (LaurentSeries L)) c₀⁻¹ * (x * Polynomial.aeval (jqModC L) D)
        = ∑ i : Fin d, (algebraMap L (LaurentSeries L)) c₀⁻¹
            * (Polynomial.aeval (jqModC L) (A i) * jqNModC L N ^ (i : ℕ)) := by
      rw [hmain, Finset.mul_sum]
    calc x * Polynomial.aeval (jqModC L) (Polynomial.C c₀⁻¹ * D)
        = (algebraMap L (LaurentSeries L)) c₀⁻¹ * (x * Polynomial.aeval (jqModC L) D) := by
          rw [map_mul, Polynomial.aeval_C]
          ring
      _ = ∑ i : Fin d, (algebraMap L (LaurentSeries L)) c₀⁻¹
            * (Polynomial.aeval (jqModC L) (A i) * jqNModC L N ^ (i : ℕ)) := hsc
      _ = ∑ i : Fin d, Polynomial.aeval (jqModC L) (Polynomial.C c₀⁻¹ * A i)
            * jqNModC L N ^ (i : ℕ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_rhs => rw [map_mul, Polynomial.aeval_C]
          ring
  refine ⟨d, hdle, Dp, Ap, hOeq, ?_⟩
  intro hDm0
  have hwitness : ∀ (P : Polynomial L) (Pp : Polynomial O)
      (_ : Pp.map O.subtype = Polynomial.C c₀⁻¹ * P) (n : ℕ) (_ : P.coeff n = c₀),
      Pp.coeff n = 1 := by
    intro P Pp hPp n hn
    have h1 := congrArg (fun Q => Q.coeff n) hPp
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at h1
    rw [hn, inv_mul_cancel₀ hc₀ne] at h1
    exact Subtype.ext h1
  have hred := congrArg (coeffMap res) hOeq
  rw [map_mul, map_sum, coeffMap_aeval res Dp (jqModC O), hDm0, map_zero, mul_zero] at hred
  have hredsum : ∀ i : Fin d,
      coeffMap res (Polynomial.aeval (jqModC O) (Ap i) * jqNModC O N ^ (i : ℕ))
        = Polynomial.aeval (jqModC K) ((Ap i).map res) * jqNModC K N ^ (i : ℕ) := by
    intro i
    rw [map_mul, map_pow, coeffMap_aeval res (Ap i) (jqModC O), coeffMap_jqModC,
      ModularCurve.map_jqNModC res N]
  rw [Finset.sum_congr rfl fun i _ => hredsum i] at hred
  have hall0 := polys_eq_zero_of_sum_eq_zero N hdeg hdle (fun i => (Ap i).map res) hred.symm
  rw [hcs] at hc₀mem
  rcases List.mem_append.mp hc₀mem with hmem | hmem
  · obtain ⟨n, hn, hcoeff⟩ := List.mem_map.mp hmem
    have h1 : Dp.coeff n = 1 := hwitness D Dp hDp n hcoeff
    have h2 := congrArg (fun Q => Q.coeff n) hDm0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h2
    rw [h1, map_one] at h2
    exact one_ne_zero h2
  · obtain ⟨i, hi, hmem2⟩ := List.mem_flatMap.mp hmem
    obtain ⟨n, hn, hcoeff⟩ := List.mem_map.mp hmem2
    have h1 : (Ap i).coeff n = 1 := hwitness (A i) (Ap i) (hAp i) n hcoeff
    have h2 := congrArg (fun Q => Q.coeff n) (hall0 i)
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h2
    rw [h1, map_one] at h2
    exact one_ne_zero h2

private theorem exists_dvd_min_O {L : Type*} [Field L] {O : Subring L} [ValuationRing O] :
    ∀ (s : List O), s ≠ [] → ∃ c ∈ s, ∀ b ∈ s, c ∣ b
  | [], h => absurd rfl h
  | [a], _ => ⟨a, List.mem_singleton.mpr rfl, fun b hb => by
      rw [List.mem_singleton.mp hb]⟩
  | a :: b :: t, _ => by
      obtain ⟨c, hc, hcall⟩ := exists_dvd_min_O (b :: t) (List.cons_ne_nil b t)
      rcases ValuationRing.dvd_total a c with h | h
      · exact ⟨a, List.mem_cons_self .., fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact dvd_rfl
          · exact h.trans (hcall z hz)⟩
      · exact ⟨c, List.mem_cons_of_mem a hc, fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact h
          · exact hcall z hz⟩

private theorem res_eq_zero_of_not_isUnit {L : Type*} [Field L] {O : Subring L}
    [ValuationRing O] {K : Type*} [Field K] (res : O →+* K)
    (hres : Function.Surjective res) {c : O} (hc : ¬ IsUnit c) : res c = 0 := by
  have hker : RingHom.ker res = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective res hres)
  have hmem : c ∈ RingHom.ker res := by
    rw [hker]
    exact (IsLocalRing.mem_maximalIdeal c).mpr (mem_nonunits_iff.mpr hc)
  rwa [RingHom.mem_ker] at hmem

private theorem dvd_coeff_mul {O : Type*} [CommRing O] {c : O} {w v : LaurentSeries O}
    (hw : ∀ k, c ∣ w.coeff k) (k : ℤ) : c ∣ (w * v).coeff k := by
  rw [HahnSeries.coeff_mul]
  exact Finset.dvd_sum fun ij _ => (hw ij.1).mul_right _

private theorem dvd_coeff_aeval {O : Type*} [CommRing O] {c : O} {P : Polynomial O}
    (hP : ∀ n, c ∣ P.coeff n) (z : LaurentSeries O) (k : ℤ) :
    c ∣ (Polynomial.aeval z P).coeff k := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, coeff_sum]
  refine Finset.dvd_sum fun i _ => ?_
  rw [algebraMap_laurent_eq_C,
    show (HahnSeries.C (P.coeff i) : LaurentSeries O)
      = HahnSeries.single (0 : ℤ) (P.coeff i) from rfl,
    HahnSeries.coeff_single_zero_mul]
  exact (hP i).mul_right _

private theorem swap_identity {F : Type*} [Field F] (N : ℕ) [NeZero N]
    (φ : modularFunctionFieldC F N ≃ₐ[F] modularFunctionFieldC F N)
    (hφ1 : φ ⟨jqModC F, jqModC_mem F N⟩ = ⟨jqNModC F N, jqNModC_mem F N⟩)
    (hφ2 : φ ⟨jqNModC F N, jqNModC_mem F N⟩ = ⟨jqModC F, jqModC_mem F N⟩)
    {z : LaurentSeries F} (hz : z ∈ modularFunctionFieldC F N)
    {d : ℕ} (DL : Polynomial F) (AL : Fin d → Polynomial F)
    (hid : z * Polynomial.aeval (jqModC F) DL
      = ∑ i : Fin d, Polynomial.aeval (jqModC F) (AL i) * jqNModC F N ^ (i : ℕ)) :
    ((φ ⟨z, hz⟩ : modularFunctionFieldC F N) : LaurentSeries F)
        * Polynomial.aeval (jqNModC F N) DL
      = ∑ i : Fin d, Polynomial.aeval (jqNModC F N) (AL i) * jqModC F ^ (i : ℕ) := by
  classical
  have hval : ∀ (P : Polynomial F) (pt : modularFunctionFieldC F N),
      ((Polynomial.aeval pt P : modularFunctionFieldC F N) : LaurentSeries F)
        = Polynomial.aeval ((pt : modularFunctionFieldC F N) : LaurentSeries F) P :=
    fun P pt => (Polynomial.aeval_algHom_apply (modularFunctionFieldC F N).val pt P).symm
  have hidS : (⟨z, hz⟩ : modularFunctionFieldC F N)
        * Polynomial.aeval (⟨jqModC F, jqModC_mem F N⟩ : modularFunctionFieldC F N) DL
      = ∑ i : Fin d,
          Polynomial.aeval (⟨jqModC F, jqModC_mem F N⟩ : modularFunctionFieldC F N) (AL i)
            * (⟨jqNModC F N, jqNModC_mem F N⟩ : modularFunctionFieldC F N) ^ (i : ℕ) := by
    refine Subtype.ext ?_
    simp only [MulMemClass.coe_mul, AddSubmonoidClass.coe_finsetSum,
      SubmonoidClass.coe_pow, hval]
    exact hid
  have haev : ∀ P : Polynomial F,
      φ (Polynomial.aeval (⟨jqModC F, jqModC_mem F N⟩ : modularFunctionFieldC F N) P)
        = Polynomial.aeval (⟨jqNModC F N, jqNModC_mem F N⟩ : modularFunctionFieldC F N) P := by
    intro P
    have h3 := Polynomial.aeval_algHom_apply
      (φ : modularFunctionFieldC F N →ₐ[F] modularFunctionFieldC F N)
      (⟨jqModC F, jqModC_mem F N⟩ : modularFunctionFieldC F N) P
    simp only [AlgEquiv.coe_algHom] at h3
    rw [hφ1] at h3
    exact h3.symm
  have h2 := congrArg φ hidS
  rw [map_mul, map_sum, haev DL,
    Finset.sum_congr rfl fun i _ => by rw [map_mul, map_pow, haev (AL i), hφ2]] at h2
  have h4 := congrArg Subtype.val h2
  simp only [MulMemClass.coe_mul, AddSubmonoidClass.coe_finsetSum,
    SubmonoidClass.coe_pow, hval] at h4
  exact h4

private theorem jqNModC_congr' {K : Type*} [Field K] {n m : ℕ} [NeZero n] [NeZero m]
    (h : n = m) : jqNModC K n = jqNModC K m := by
  subst h
  rfl

private theorem isIntegral_adjoin_ring_jqNModC (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    IsIntegral (Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) := by
  classical
  obtain ⟨data, -⟩ := ModularCurve.exists_phiIrreducible N
  have hstub := ModularCurve.ModularPolynomialData.eval_jqNModC_mul_eq_zero data K 1
  rw [jqNModC_one, jqNModC_congr' (one_mul N)] at hstub
  set R := Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K)) with hR
  set jR : R := ⟨jqModC K, Algebra.self_mem_adjoin_singleton K _⟩ with hjR
  refine ⟨data.Φ.map (Polynomial.aeval jR).toRingHom, data.monic.map _, ?_⟩
  have hcomp : (algebraMap R (LaurentSeries K)).comp (Polynomial.aeval jR).toRingHom
      = (Polynomial.aeval (R := ℤ) (jqModC K)).toRingHom := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    rw [RingHom.comp_apply,
      show (Polynomial.aeval jR).toRingHom Polynomial.X = Polynomial.aeval jR Polynomial.X
        from rfl,
      Polynomial.aeval_X,
      show (Polynomial.aeval (R := ℤ) (jqModC K)).toRingHom Polynomial.X
        = Polynomial.aeval (R := ℤ) (jqModC K) Polynomial.X from rfl,
      Polynomial.aeval_X]
    rfl
  rw [Polynomial.eval₂_map, hcomp]
  exact hstub

end ModularCurve.W1

section Stubs

open ModularCurve.W1

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.coeffMap_mem_modularFunctionFieldC {L : Type*} [Field L] (O : Subring L)
    [ValuationRing O] (hO : ∀ z : L, z ∈ O ∨ z⁻¹ ∈ O) {K : Type*} [Field K] (res : O →+* K)
    (N : ℕ) [NeZero N]
    (hdeg : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        ({jqNModC K N} : Set (LaurentSeries K))) = dedekindPsi N)
    {x : LaurentSeries L} (hx : x ∈ modularFunctionFieldC L N)
    (y : LaurentSeries O) (hy : coeffMap O.subtype y = x) :
    coeffMap res y ∈ modularFunctionFieldC K N := by
  obtain ⟨d, hdle, Dp, Ap, hOeq, hDm⟩ := exists_rep O hO res N hdeg hx y hy
  have hred := congrArg (coeffMap res) hOeq
  rw [map_mul, map_sum, coeffMap_aeval res Dp (jqModC O), coeffMap_jqModC] at hred
  have hredsum : ∀ i : Fin d,
      coeffMap res (Polynomial.aeval (jqModC O) (Ap i) * jqNModC O N ^ (i : ℕ))
        = Polynomial.aeval (jqModC K) ((Ap i).map res) * jqNModC K N ^ (i : ℕ) := by
    intro i
    rw [map_mul, map_pow, coeffMap_aeval res (Ap i) (jqModC O), coeffMap_jqModC,
      ModularCurve.map_jqNModC res N]
  rw [Finset.sum_congr rfl fun i _ => hredsum i] at hred
  have hDne : Polynomial.aeval (jqModC K) (Dp.map res) ≠ 0 := aeval_jqModC_ne_zero hDm
  have hstep : coeffMap res y
      = (∑ i : Fin d, Polynomial.aeval (jqModC K) ((Ap i).map res)
          * jqNModC K N ^ (i : ℕ)) / Polynomial.aeval (jqModC K) (Dp.map res) := by
    rw [eq_div_iff hDne]
    exact hred
  rw [hstep]
  refine div_mem ?_ (aeval_jqModC_mem_mffC N _)
  refine sum_mem fun i _ => ?_
  exact mul_mem (aeval_jqModC_mem_mffC N _) (pow_mem (jqNModC_mem K N) _)

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.exists_smul_eq_of_coeffMap_eq_zero {L : Type*} [Field L] (O : Subring L)
    [ValuationRing O] (hO : ∀ z : L, z ∈ O ∨ z⁻¹ ∈ O) {K : Type*} [Field K] (res : O →+* K)
    (hres : Function.Surjective res) (N : ℕ) [NeZero N]
    (hdeg : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        ({jqNModC K N} : Set (LaurentSeries K))) = dedekindPsi N)
    {x : LaurentSeries L} (hx : x ∈ modularFunctionFieldC L N)
    (y : LaurentSeries O) (hy : coeffMap O.subtype y = x) (h0 : coeffMap res y = 0) :
    ∃ (c : O) (y' : LaurentSeries O), res c = 0 ∧ y = c • y' := by
  classical
  rcases eq_or_ne y 0 with rfl | hyne
  · exact ⟨0, 0, map_zero res, by rw [smul_zero]⟩
  obtain ⟨d, hdle, Dp, Ap, hOeq, hDm⟩ := exists_rep O hO res N hdeg hx y hy
  set u : LaurentSeries O := Polynomial.aeval (jqModC O) Dp with hu
  set B : LaurentSeries O :=
    ∑ i : Fin d, Polynomial.aeval (jqModC O) (Ap i) * jqNModC O N ^ (i : ℕ) with hB

  have hredsum : ∀ i : Fin d,
      coeffMap res (Polynomial.aeval (jqModC O) (Ap i) * jqNModC O N ^ (i : ℕ))
        = Polynomial.aeval (jqModC K) ((Ap i).map res) * jqNModC K N ^ (i : ℕ) := by
    intro i
    rw [map_mul, map_pow, coeffMap_aeval res (Ap i) (jqModC O),
      coeffMap_jqModC, ModularCurve.map_jqNModC res N]
  have hall0 : ∀ i : Fin d, (Ap i).map res = 0 := by
    have hred := congrArg (coeffMap res) hOeq
    rw [map_mul, h0, zero_mul, map_sum, Finset.sum_congr rfl fun i _ => hredsum i] at hred
    exact polys_eq_zero_of_sum_eq_zero N hdeg hdle
      (fun i => (Ap i).map res) hred.symm
  have hApker : ∀ (i : Fin d) (n : ℕ), res ((Ap i).coeff n) = 0 := by
    intro i n
    have h1 := congrArg (fun Q => Q.coeff n) (hall0 i)
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using h1

  have hured : coeffMap res u = Polynomial.aeval (jqModC K) (Dp.map res) := by
    rw [hu, coeffMap_aeval res Dp (jqModC O), coeffMap_jqModC]
  have huredne : coeffMap res u ≠ 0 := by
    rw [hured]
    exact aeval_jqModC_ne_zero hDm
  set S : Set ℤ := {k : ℤ | res (u.coeff k) ≠ 0} with hS
  have hSne : S.Nonempty := by
    by_contra hSe
    refine huredne (HahnSeries.ext ?_)
    funext k
    rw [coeffMap_coeff, HahnSeries.coeff_zero]
    by_contra hk
    exact hSe ⟨k, hk⟩
  have hSsub : S ⊆ u.support := fun k hk =>
    Function.mem_support.mpr fun h => hk (by rw [h, map_zero])
  have hSwf : S.IsWF := u.isWF_support.mono hSsub
  set m : ℤ := hSwf.min hSne with hm
  have hmS : m ∈ S := hSwf.min_mem hSne
  have hmsupp : m ∈ u.support := hSsub hmS
  have hmkill : ∀ k, k < m → res (u.coeff k) = 0 := by
    intro k hk
    by_contra hkne
    exact hSwf.not_lt_min hSne (show k ∈ S from hkne) hk
  have hmunit : IsUnit (u.coeff m) := by
    by_contra hnu
    exact hmS (res_eq_zero_of_not_isUnit res hres hnu)

  set ws : List O := (List.range (m - u.order).toNat).map (fun j : ℕ => u.coeff (u.order + (j : ℤ)))
    with hws
  set acs : List O := (List.finRange d).flatMap
    (fun i => (List.range ((Ap i).natDegree + 1)).map (Ap i).coeff) with hacs

  have hune : u ≠ 0 := by
    intro h
    rw [h, map_zero] at huredne
    exact huredne rfl
  have hd1 : 0 < d := by
    by_contra hd0
    have hdz : d = 0 := by omega
    subst hdz
    rw [show B = 0 from by rw [hB]; exact Finset.sum_empty] at hOeq
    exact hyne ((mul_eq_zero.mp hOeq).resolve_right hune)
  have hcsne : acs ≠ [] := by
    rw [hacs]
    intro h
    have h1 : (List.finRange d).flatMap
        (fun i => (List.range ((Ap i).natDegree + 1)).map (Ap i).coeff) = [] := h
    have h2 := List.flatMap_eq_nil_iff.mp h1
    have h3 : (⟨0, hd1⟩ : Fin d) ∈ List.finRange d := List.mem_finRange _
    have h4 := h2 _ h3
    have h5 := List.map_eq_nil_iff.mp h4
    rw [List.range_eq_nil] at h5
    omega
  obtain ⟨c, hcmem, hcall⟩ := exists_dvd_min_O (acs ++ ws)
    (fun h => hcsne (List.append_eq_nil_iff.mp h).1)

  have hcker : res c = 0 := by
    rcases List.mem_append.mp hcmem with h | h
    · rw [hacs] at h
      obtain ⟨i, _, h2⟩ := List.mem_flatMap.mp h
      obtain ⟨n, _, h3⟩ := List.mem_map.mp h2
      rw [← h3]
      exact hApker i n
    · rw [hws] at h
      obtain ⟨j, hj, h2⟩ := List.mem_map.mp h
      rw [← h2]
      refine hmkill _ ?_
      have hj2 := List.mem_range.mp hj
      omega

  have hcB : ∀ k, c ∣ B.coeff k := by
    intro k
    rw [hB, coeff_sum]
    refine Finset.dvd_sum fun i _ => ?_
    refine dvd_coeff_mul (fun k' => ?_) k
    refine dvd_coeff_aeval (fun n => ?_) (jqModC O) k'
    by_cases hn : n ≤ (Ap i).natDegree
    · refine hcall _ (List.mem_append_left _ ?_)
      rw [hacs]
      refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩
      exact List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le hn))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.not_le.mp hn)]
      exact dvd_zero c

  have hcwin : ∀ k, k ∈ u.support → k < m → c ∣ u.coeff k := by
    intro k hk hkm
    refine hcall _ (List.mem_append_right _ ?_)
    rw [hws]
    have hko : u.order ≤ k := HahnSeries.order_le_of_coeff_ne_zero (Function.mem_support.mp hk)
    refine List.mem_map.mpr ⟨(k - u.order).toNat, List.mem_range.mpr ?_, ?_⟩
    · omega
    · have h5 : u.order + (((k - u.order).toNat : ℕ) : ℤ) = k := by omega
      rw [h5]

  have hcy : ∀ n : ℤ, c ∣ y.coeff n := by
    by_contra hcon
    push Not at hcon
    obtain ⟨n₀', hn₀'⟩ := hcon
    set T : Set ℤ := {n : ℤ | ¬ c ∣ y.coeff n} with hT
    have hTne : T.Nonempty := ⟨n₀', hn₀'⟩
    have hTsub : T ⊆ y.support := fun n hn =>
      Function.mem_support.mpr fun h => hn (by rw [h]; exact dvd_zero c)
    have hTwf : T.IsWF := y.isWF_support.mono hTsub
    set n₀ : ℤ := hTwf.min hTne with hn₀
    have hn₀T : n₀ ∈ T := hTwf.min_mem hTne
    have hn₀min : ∀ k, k < n₀ → c ∣ y.coeff k := by
      intro k hk
      by_contra hknd
      exact hTwf.not_lt_min hTne (show k ∈ T from hknd) hk

    have hpair : ((n₀, m) : ℤ × ℤ) ∈ Finset.antidiagonal y.isPWO_support u.isPWO_support
        (n₀ + m) := by
      rw [Finset.mem_antidiagonal]
      exact ⟨hTsub hn₀T, hmsupp, rfl⟩
    have hconv : (y * u).coeff (n₀ + m)
        = y.coeff n₀ * u.coeff m
          + ∑ ij ∈ (Finset.antidiagonal y.isPWO_support u.isPWO_support
              (n₀ + m)).erase (n₀, m), y.coeff ij.1 * u.coeff ij.2 := by
      conv_lhs => rw [HahnSeries.coeff_mul, ← Finset.insert_erase hpair,
        Finset.sum_insert (Finset.notMem_erase _ _)]
    have hrest : c ∣ ∑ ij ∈ (Finset.antidiagonal y.isPWO_support u.isPWO_support
        (n₀ + m)).erase (n₀, m), y.coeff ij.1 * u.coeff ij.2 := by
      refine Finset.dvd_sum fun ij hij => ?_
      have hij2 := Finset.mem_antidiagonal.mp (Finset.mem_of_mem_erase hij)
      have hijne := Finset.ne_of_mem_erase hij
      rcases lt_trichotomy ij.1 n₀ with h | h | h
      · exact (hn₀min ij.1 h).mul_right _
      · exfalso
        refine hijne ?_
        have h2 : ij.2 = m := by omega
        exact Prod.ext h h2
      · have h2 : ij.2 < m := by omega
        exact ((hcwin ij.2 hij2.2.1 h2).mul_left _)
    have hdvd_y : c ∣ y.coeff n₀ * u.coeff m := by
      have h1 : y.coeff n₀ * u.coeff m
          = (y * u).coeff (n₀ + m) - ∑ ij ∈ (Finset.antidiagonal y.isPWO_support
              u.isPWO_support (n₀ + m)).erase (n₀, m), y.coeff ij.1 * u.coeff ij.2 := by
        rw [hconv]
        ring
      rw [h1, hOeq]
      exact dvd_sub (hcB _) hrest
    obtain ⟨v, hv⟩ := hmunit.exists_right_inv
    have h3 : y.coeff n₀ = y.coeff n₀ * u.coeff m * v := by
      rw [mul_assoc, hv, mul_one]
    exact hn₀T (by rw [h3]; exact hdvd_y.mul_right v)

  set w : ℤ → O := fun n => if hn : y.coeff n = 0 then 0 else (hcy n).choose with hw
  have hwspec : ∀ n, y.coeff n = c * w n := by
    intro n
    show y.coeff n = c * (if hn : y.coeff n = 0 then 0 else (hcy n).choose)
    by_cases hn : y.coeff n = 0
    · rw [dif_pos hn, mul_zero, hn]
    · rw [dif_neg hn]
      exact (hcy n).choose_spec
  have hwsub : Function.support w ⊆ y.support := by
    intro n hn
    rw [Function.mem_support] at hn
    refine Function.mem_support.mpr fun h => hn ?_
    show (if hn : y.coeff n = 0 then 0 else (hcy n).choose) = 0
    rw [dif_pos h]
  refine ⟨c, ⟨w, y.isPWO_support'.mono hwsub⟩, hcker, ?_⟩
  ext n
  exact congrArg Subtype.val (hwspec n)

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.coeffMap_swap_eq_algEquiv_coeffMap {L : Type*} [Field L] (O : Subring L)
    [ValuationRing O] (hO : ∀ z : L, z ∈ O ∨ z⁻¹ ∈ O) {K : Type*} [Field K] (res : O →+* K)
    (N : ℕ) [NeZero N]
    (hdeg : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        ({jqNModC K N} : Set (LaurentSeries K))) = dedekindPsi N)
    {x : LaurentSeries L} (hx : x ∈ modularFunctionFieldC L N)
    (σ : modularFunctionFieldC L N ≃ₐ[L] modularFunctionFieldC L N)
    (hσ1 : σ ⟨jqModC L, jqModC_mem L N⟩ = ⟨jqNModC L N, jqNModC_mem L N⟩)
    (hσ2 : σ ⟨jqNModC L N, jqNModC_mem L N⟩ = ⟨jqModC L, jqModC_mem L N⟩)
    (y y' : LaurentSeries O) (hy : coeffMap O.subtype y = x)
    (hy' : coeffMap O.subtype y' = ((σ ⟨x, hx⟩ : modularFunctionFieldC L N) : LaurentSeries L))
    (hmem : coeffMap res y ∈ modularFunctionFieldC K N)
    (τ : modularFunctionFieldC K N ≃ₐ[K] modularFunctionFieldC K N)
    (hτ1 : τ ⟨jqModC K, jqModC_mem K N⟩ = ⟨jqNModC K N, jqNModC_mem K N⟩)
    (hτ2 : τ ⟨jqNModC K N, jqNModC_mem K N⟩ = ⟨jqModC K, jqModC_mem K N⟩) :
    coeffMap res y' = ((τ ⟨coeffMap res y, hmem⟩ : modularFunctionFieldC K N) : LaurentSeries K) := by
  classical
  obtain ⟨d, hdle, Dp, Ap, hOeq, hDm⟩ := exists_rep O hO res N hdeg hx y hy
  have hL := congrArg (coeffMap O.subtype) hOeq
  rw [map_mul, map_sum, hy, coeffMap_aeval O.subtype Dp (jqModC O), coeffMap_jqModC,
    Finset.sum_congr rfl fun i _ => by
      rw [map_mul, map_pow, coeffMap_aeval O.subtype (Ap i) (jqModC O), coeffMap_jqModC,
        ModularCurve.map_jqNModC O.subtype N]] at hL
  have hswapL := swap_identity N σ hσ1 hσ2 hx (Dp.map O.subtype)
    (fun i => (Ap i).map O.subtype) hL
  have hinj : Function.Injective (coeffMap O.subtype) :=
    coeffMap_injective (fun a b h => Subtype.ext h)
  have hOswap : y' * Polynomial.aeval (jqNModC O N) Dp
      = ∑ i : Fin d, Polynomial.aeval (jqNModC O N) (Ap i) * jqModC O ^ (i : ℕ) := by
    apply hinj
    rw [map_mul, map_sum, hy', coeffMap_aeval O.subtype Dp (jqNModC O N),
      show coeffMap O.subtype (jqNModC O N) = jqNModC L N from ModularCurve.map_jqNModC _ N,
      Finset.sum_congr rfl fun i _ => by
        rw [map_mul, map_pow, coeffMap_aeval O.subtype (Ap i) (jqNModC O N),
          show coeffMap O.subtype (jqNModC O N) = jqNModC L N from
            ModularCurve.map_jqNModC _ N,
          coeffMap_jqModC]]
    exact hswapL
  have hred := congrArg (coeffMap res) hOswap
  rw [map_mul, map_sum, coeffMap_aeval res Dp (jqNModC O N),
    show coeffMap res (jqNModC O N) = jqNModC K N from ModularCurve.map_jqNModC res N,
    Finset.sum_congr rfl fun i _ => by
      rw [map_mul, map_pow, coeffMap_aeval res (Ap i) (jqNModC O N),
        show coeffMap res (jqNModC O N) = jqNModC K N from ModularCurve.map_jqNModC res N,
        coeffMap_jqModC]] at hred
  have hredL := congrArg (coeffMap res) hOeq
  rw [map_mul, map_sum, coeffMap_aeval res Dp (jqModC O), coeffMap_jqModC,
    Finset.sum_congr rfl fun i _ => by
      rw [map_mul, map_pow, coeffMap_aeval res (Ap i) (jqModC O), coeffMap_jqModC,
        ModularCurve.map_jqNModC res N]] at hredL
  have hτid := swap_identity N τ hτ1 hτ2 hmem (Dp.map res) (fun i => (Ap i).map res) hredL
  have hZ : Polynomial.aeval (jqNModC K N) (Dp.map res) ≠ 0 := aeval_jqNModC_ne_zero N hDm
  exact mul_right_cancel₀ hZ (hred.trans hτid.symm)

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.isIntegral_adjoin_coeffMap {O : Type*} [CommRing O] {K : Type*}
    [Field K] (res : O →+* K) (N : ℕ) [NeZero N] (Q : Polynomial (Polynomial O))
    (z : LaurentSeries O)
    (hzrep : z = ((Q.map (Polynomial.aeval (jqModC O)).toRingHom).eval (jqNModC O N))) :
    IsIntegral (Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K))) (coeffMap res z) := by
  classical
  subst hzrep
  set R := Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K)) with hR

  have hred : coeffMap res ((Q.map (Polynomial.aeval (jqModC O)).toRingHom).eval
      (jqNModC O N))
      = Q.eval₂ ((Polynomial.aeval (jqModC K)).toRingHom.comp (Polynomial.mapRingHom res))
          (jqNModC K N) := by
    rw [Polynomial.eval_map, Polynomial.hom_eval₂,
      show coeffMap res (jqNModC O N) = jqNModC K N from ModularCurve.map_jqNModC res N]
    congr 1
    refine RingHom.ext fun P => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    rw [show (coeffMap res) ((Polynomial.aeval (jqModC O)).toRingHom P)
        = coeffMap res (Polynomial.aeval (jqModC O) P) from rfl,
      ModularCurve.W1.coeffMap_aeval res P (jqModC O), ModularCurve.W1.coeffMap_jqModC]
    rfl
  rw [hred]

  have hjN : IsIntegral R (jqNModC K N) := ModularCurve.W1.isIntegral_adjoin_ring_jqNModC K N
  refine IsIntegral.of_mem_of_fg (Algebra.adjoin R ({jqNModC K N} : Set (LaurentSeries K)))
    hjN.fg_adjoin_singleton _ ?_
  rw [Polynomial.eval₂_eq_sum_range]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  refine Subalgebra.mul_mem _ ?_
    (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton R _) _)
  have h5 : ((Polynomial.aeval (jqModC K)).toRingHom.comp (Polynomial.mapRingHom res))
      (Q.coeff i) ∈ R := by
    rw [RingHom.comp_apply,
      show (Polynomial.aeval (jqModC K)).toRingHom ((Polynomial.mapRingHom res) (Q.coeff i))
        = Polynomial.aeval (jqModC K) ((Q.coeff i).map res) from rfl]
    exact Polynomial.aeval_mem_adjoin_singleton K (jqModC K)
  exact (Algebra.adjoin R ({jqNModC K N} : Set (LaurentSeries K))).algebraMap_mem
    (⟨_, h5⟩ : R)

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.isIntegral_adjoin_mk_coeffMap {O : Type*} [CommRing O] {K : Type*}
    [Field K] (res : O →+* K) (N : ℕ) [NeZero N] (Q : Polynomial (Polynomial O))
    (z : LaurentSeries O)
    (hzrep : z = ((Q.map (Polynomial.aeval (jqModC O)).toRingHom).eval (jqNModC O N)))
    (hmem : coeffMap res z ∈ modularFunctionFieldC K N) :
    IsIntegral
      (Algebra.adjoin K ({(⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N)} :
        Set (modularFunctionFieldC K N)))
      (⟨coeffMap res z, hmem⟩ : modularFunctionFieldC K N) :=
  AlgebraicCurve.isIntegral_adjoin_intermediateField_mk (modularFunctionFieldC K N)
    (jqModC_mem K N) hmem (ModularCurve.isIntegral_adjoin_coeffMap res N Q z hzrep)

end Stubs

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeffMap_mem_modularFunctionFieldC.ModularCurve in

theorem solution {L : Type*} [Field L] (O : Subring L)
    [ValuationRing O] (hO : ∀ z : L, z ∈ O ∨ z⁻¹ ∈ O) {K : Type*} [Field K] (res : O →+* K)
    (N : ℕ) [NeZero N]
    (hdeg : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        ({jqNModC K N} : Set (LaurentSeries K))) = dedekindPsi N)
    {x : LaurentSeries L} (hx : x ∈ modularFunctionFieldC L N)
    (y : LaurentSeries O) (hy : coeffMap O.subtype y = x) :
    coeffMap res y ∈ modularFunctionFieldC K N :=
  ModularCurve.coeffMap_mem_modularFunctionFieldC O hO res N hdeg hx y hy

#print axioms solution

end S_ModularCurve_coeffMap_mem_modularFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_coeffMap_mem_modularFunctionFieldC (solution)
