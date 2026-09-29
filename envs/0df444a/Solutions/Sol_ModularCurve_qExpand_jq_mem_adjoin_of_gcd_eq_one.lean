-- Prove2me | solution 1 for ModularCurve.qExpand_jq_mem_adjoin_of_gcd_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f7be6fc7-bc70-5abb-bd05-f3654e5aedc9

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq
import Theorems.Thm_ModularCurve_phiIrreducible_all
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_functionFieldGeneration_iff_full_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_jq_mem_adjoin_of_gcd_eq_one
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve Polynomial IntermediateField

namespace W7CGcdDescent

theorem mem_of_unique_common_root {F E Ω : Type*} [Field F] [Field E] [Algebra F E] [Field Ω]
    (φ : E →+* Ω) (L : IntermediateField F E) [CharZero L] (x : E) {ι : Type*} (I : Finset ι)
    (Q : ι → E[X]) (hmonic : ∀ i ∈ I, (Q i).Monic) (hcoeff : ∀ i ∈ I, ∀ n, (Q i).coeff n ∈ L)
    (hroot : ∀ i ∈ I, ((Q i).map φ).IsRoot (φ x)) {i₀ : ι} (hi₀ : i₀ ∈ I)
    (hsplit : ((Q i₀).map φ).Splits)
    (huniq : ∀ y : Ω, (∀ i ∈ I, ((Q i).map φ).IsRoot y) → y = φ x) : x ∈ L := by
  classical

  have hlift : ∀ i ∈ I, ∃ P : L[X], P.map (algebraMap L E) = Q i ∧ P.Monic := by
    intro i hi
    have hmem : Q i ∈ Polynomial.lifts (algebraMap L E) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hcoeff i hi n⟩, rfl⟩
    obtain ⟨P, hP, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hmem (hmonic i hi)
    exact ⟨P, hP, hPm⟩
  choose! P hPmap hPmonic using hlift

  have hrootE : ∀ i ∈ I, Polynomial.aeval x (P i) = 0 := by
    intro i hi
    have h1 : φ (Polynomial.eval x (Q i)) = 0 := by
      rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map]
      exact hroot i hi
    rw [map_eq_zero_iff φ φ.injective] at h1
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hPmap i hi]
    exact h1
  have hint : IsIntegral L x :=
    ⟨P i₀, hPmonic i₀ hi₀, by rw [← Polynomial.aeval_def]; exact hrootE i₀ hi₀⟩
  set m := minpoly L x with hm
  have hdvd : ∀ i ∈ I, m ∣ P i := fun i hi => minpoly.dvd L x (hrootE i hi)
  have hirr : Irreducible m := minpoly.irreducible hint
  have hsep : m.Separable := hirr.separable
  set θ : L →+* Ω := φ.comp (algebraMap L E) with hθ
  have hθmap : ∀ i ∈ I, (P i).map θ = (Q i).map φ := fun i hi => by
    rw [hθ, ← Polynomial.map_map, hPmap i hi]
  have hmsplit : (m.map θ).Splits := by
    have hs : ((P i₀).map θ).Splits := by rw [hθmap i₀ hi₀]; exact hsplit
    refine hs.of_dvd ?_ (Polynomial.map_dvd θ (hdvd i₀ hi₀))
    exact Polynomial.map_monic_ne_zero (hPmonic i₀ hi₀)
  have hdeg : m.natDegree = (m.map θ).roots.card := by
    rw [← hmsplit.natDegree_eq_card_roots, Polynomial.natDegree_map]
  have hnodup : (m.map θ).roots.Nodup := Polynomial.nodup_roots hsep.map
  have hsub : (m.map θ).roots.toFinset ⊆ {φ x} := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero hirr.ne_zero)] at hy
    rw [Finset.mem_singleton]
    refine huniq y fun i hi => ?_
    rw [← hθmap i hi]
    exact hy.dvd (Polynomial.map_dvd θ (hdvd i hi))
  have hcard : (m.map θ).roots.card ≤ 1 := by
    rw [← Multiset.toFinset_card_of_nodup hnodup]
    exact (Finset.card_le_card hsub).trans (Finset.card_singleton _).le
  have hpos : 0 < m.natDegree := minpoly.natDegree_pos hint
  have h1 : m.natDegree = 1 := by omega
  obtain ⟨y, hy⟩ := minpoly.natDegree_eq_one_iff.mp h1
  rw [← hy]
  exact y.2

section Slots

variable (K : Type*) [Field K] [Algebra ℚ K]

noncomputable def sv (a : ℕ) [NeZero a] (u : Kˣ) : LaurentSeries K :=
  qExpand K (a * a) (qTwist u (coeffEmb K jq))

theorem sv_def (a : ℕ) [NeZero a] (u : Kˣ) :
    sv K a u = qExpand K (a * a) (qTwist u (coeffEmb K jq)) := rfl

theorem sv_coeff_neg (a : ℕ) [NeZero a] (u : Kˣ) :
    (sv K a u).coeff (-((a * a : ℕ) : ℤ)) = ((u⁻¹ : Kˣ) : K) := by
  rw [sv_def, show (-((a * a : ℕ) : ℤ)) = ((a * a : ℕ) : ℤ) * (-1) by ring, qExpand_coeff_mul,
    qTwist_coeff, coeffEmb_coeff, coeff_jq_neg_one, map_one, mul_one, zpow_neg, zpow_one]

theorem sv_coeff_of_lt (a : ℕ) [NeZero a] (u : Kˣ) {n : ℤ} (hn : n < -((a * a : ℕ) : ℤ)) :
    (sv K a u).coeff n = 0 := by
  rw [sv_def]
  by_cases hdvd : ((a * a : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hdvd
    have hpos : (0 : ℤ) < ((a * a : ℕ) : ℤ) := by
      have := NeZero.pos (a * a)
      exact_mod_cast this
    have hm : m < -1 := by
      by_contra hle
      push Not at hle
      have : ((a * a : ℕ) : ℤ) * (-1) ≤ ((a * a : ℕ) : ℤ) * m :=
        mul_le_mul_of_nonneg_left hle hpos.le
      omega
    rw [qExpand_coeff_mul, qTwist_coeff, coeffEmb_coeff, coeff_jq_of_lt hm, map_zero, mul_zero]
  · exact qExpand_coeff_of_not_dvd (a * a) _ hdvd

theorem sv_inj {a a' : ℕ} [NeZero a] [NeZero a'] {u u' : Kˣ} (h : sv K a u = sv K a' u') :
    a = a' ∧ u = u' := by
  have haa : a * a = a' * a' := by
    rcases lt_trichotomy (a * a) (a' * a') with hlt | heq | hgt
    · exfalso
      have h1 := sv_coeff_neg K a' u'
      rw [← h, sv_coeff_of_lt K a u (by omega)] at h1
      exact (u'⁻¹).ne_zero h1.symm
    · exact heq
    · exfalso
      have h1 := sv_coeff_neg K a u
      rw [h, sv_coeff_of_lt K a' u' (by omega)] at h1
      exact (u⁻¹).ne_zero h1.symm
  have ha : a = a' := (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp haa
  subst ha
  refine ⟨rfl, ?_⟩
  have h1 := sv_coeff_neg K a u
  rw [h, sv_coeff_neg K a u'] at h1
  exact inv_injective (Units.val_injective h1).symm

theorem sv_one_one : sv K 1 1 = coeffEmb K jq := by
  rw [sv_def, qTwist_one_apply]
  exact qExpand_one_apply _

end Slots

noncomputable abbrev A : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))

noncomputable abbrev K₀ (S : Finset ℕ) : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ
    {x : LaurentSeries ℚ | ∃ (s : ℕ) (_ : NeZero s), s ∈ S ∧ x = qExpand ℚ s jq}

theorem hall (d : ℕ) [NeZero d] :
    Module.finrank A (IntermediateField.adjoin A ({jqN d} : Set (LaurentSeries ℚ)))
        = dedekindPsi d ∧
      modularFunctionField d = modularFunctionFieldFull d := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData d
  exact ⟨ModularCurve.finrank_adjoin_jqN_eq data (ModularCurve.phiIrreducible_all d data),
    ((ModularCurve.functionFieldGeneration_iff_full_eq d).mp
      (ModularCurve.functionFieldGeneration d)).symm⟩

theorem isIntegral_jqN (s : ℕ) [NeZero s] : IsIntegral A (jqN s) := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData s
  refine ⟨data.toAdjoin, data.toAdjoin_monic, ?_⟩
  rw [ModularPolynomialData.toAdjoin, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen]
  exact data.eval_eq_zero

noncomputable def θs (s : ℕ) [NeZero s] : A →+* LaurentSeries ℚ :=
  (qExpand ℚ s).comp (algebraMap A (LaurentSeries ℚ))

theorem θs_apply (s : ℕ) [NeZero s] (c : A) : θs s c = qExpand ℚ s (c : LaurentSeries ℚ) := rfl

theorem θs_mem (S : Finset ℕ) (s : ℕ) [NeZero s] (hs : s ∈ S) (c : A) : θs s c ∈ K₀ S := by
  have h1 : qExpandₐ s (c : LaurentSeries ℚ) ∈ IntermediateField.map (qExpandₐ s) A :=
    (IntermediateField.map_mem_map A (qExpandₐ s)).mpr c.2
  rw [IntermediateField.adjoin_map, Set.image_singleton, qExpandₐ_apply] at h1
  rw [θs_apply]
  have hsub : ({qExpand ℚ s jq} : Set (LaurentSeries ℚ)) ⊆
      {x : LaurentSeries ℚ | ∃ (s : ℕ) (_ : NeZero s), s ∈ S ∧ x = qExpand ℚ s jq} :=
    Set.singleton_subset_iff.mpr ⟨s, inferInstance, hs, rfl⟩
  exact IntermediateField.adjoin.mono ℚ _ _ hsub h1

noncomputable def Qs (s : ℕ) : (LaurentSeries ℚ)[X] :=
  if h : s = 0 then 0 else
    haveI : NeZero s := ⟨h⟩
    (minpoly A (jqN s)).map (θs s)

theorem Qs_eq (s : ℕ) [NeZero s] : Qs s = (minpoly A (jqN s)).map (θs s) := by
  rw [Qs, dif_neg (NeZero.ne s)]

theorem Qs_monic (s : ℕ) [NeZero s] : (Qs s).Monic := by
  rw [Qs_eq]
  exact (minpoly.monic (isIntegral_jqN s)).map _

theorem Qs_coeff_mem (S : Finset ℕ) (s : ℕ) [NeZero s] (hs : s ∈ S) (n : ℕ) :
    (Qs s).coeff n ∈ K₀ S := by
  rw [Qs_eq, Polynomial.coeff_map]
  exact θs_mem S s hs _

theorem neZero_of_dvd {M s : ℕ} [NeZero M] (h : s ∣ M) : NeZero s :=
  ⟨fun hs => NeZero.ne M (Nat.eq_zero_of_zero_dvd (hs ▸ h))⟩

section Factor

variable (K : Type*) [Field K] [Algebra ℚ K] {M : ℕ} [NeZero M] (ζ : Kˣ)
  (hζ : IsPrimitiveRoot (ζ : K) M)
include hζ

omit [Algebra ℚ K] in
theorem isPrimitiveRoot_pow_div (s : ℕ) (hsM : s ∣ M) :
    IsPrimitiveRoot (((ζ ^ (M / s) : Kˣ)) : K) s := by
  rw [Units.val_pow_eq_pow_val]
  exact hζ.pow (NeZero.pos M) (Nat.div_mul_cancel hsM).symm

theorem Qs_map_eq (s : ℕ) [NeZero s] (hsM : s ∣ M) :
    (Qs s).map (coeffEmb K) = ∏ a ∈ s.divisors,
      ∏ b ∈ (Finset.range (s / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (s / a) = 1),
        (X - C (if h : a = 0 then 0 else
          letI : NeZero a := ⟨h⟩
          qExpand K (a * a) (qTwist ((ζ ^ (M / s)) ^ (b * a)) (coeffEmb K jq)))) := by
  rw [Qs_eq, Polynomial.map_map]
  exact ModularCurve.minpoly_jqN_map_eq_prod_slots s (ζ ^ (M / s))
    (isPrimitiveRoot_pow_div K ζ hζ s hsM) (fun d _ => hall d)

theorem exists_slot_of_isRoot (s : ℕ) [NeZero s] (hsM : s ∣ M) {y : LaurentSeries K}
    (hy : ((Qs s).map (coeffEmb K)).IsRoot y) :
    ∃ (a : ℕ) (_ : NeZero a) (b : ℕ), a ∣ s ∧ y = sv K a ((ζ ^ (M / s)) ^ (b * a)) := by
  rw [Qs_map_eq K ζ hζ s hsM, IsRoot, eval_prod, Finset.prod_eq_zero_iff] at hy
  obtain ⟨a, ha, hy⟩ := hy
  rw [eval_prod, Finset.prod_eq_zero_iff] at hy
  obtain ⟨b, -, hy⟩ := hy
  have has : a ∣ s := (Nat.mem_divisors.mp ha).1
  have ha0 : a ≠ 0 := fun h0 => NeZero.ne s (Nat.eq_zero_of_zero_dvd (h0 ▸ has))
  rw [dif_neg ha0, eval_sub, eval_X, eval_C, sub_eq_zero] at hy
  exact ⟨a, ⟨ha0⟩, b, has, hy⟩

theorem isRoot_jq (s : ℕ) [NeZero s] (hsM : s ∣ M) :
    ((Qs s).map (coeffEmb K)).IsRoot (coeffEmb K jq) := by
  rw [Qs_map_eq K ζ hζ s hsM, IsRoot, eval_prod, Finset.prod_eq_zero_iff]
  refine ⟨1, Nat.one_mem_divisors.mpr (NeZero.ne s), ?_⟩
  rw [eval_prod, Finset.prod_eq_zero_iff]
  refine ⟨0, ?_, ?_⟩
  · rw [Finset.mem_filter, Finset.mem_range, Nat.div_one]
    exact ⟨NeZero.pos s, by simp⟩
  · rw [dif_neg one_ne_zero, eval_sub, eval_X, eval_C, sub_eq_zero, zero_mul, pow_zero,
      qTwist_one_apply]
    exact (qExpand_one_apply _).symm

omit hζ in

theorem common_root_unique (hζ : IsPrimitiveRoot (ζ : K) M) (S : Finset ℕ)
    (hSM : ∀ s ∈ S, s ∣ M) (hM : M ∈ S)
    (hgcd : S.gcd id = 1) (y : LaurentSeries K)
    (hy : ∀ s ∈ S, ((Qs s).map (coeffEmb K)).IsRoot y) : y = coeffEmb K jq := by
  have hζu : IsPrimitiveRoot ζ M := IsPrimitiveRoot.coe_units_iff.mp hζ
  obtain ⟨a₀, _, b₀, -, hy₀⟩ := exists_slot_of_isRoot K ζ hζ M dvd_rfl (hy M hM)
  have key : ∀ s ∈ S, a₀ ∣ s ∧ ((ζ ^ (M / M)) ^ (b₀ * a₀)) ^ s = 1 := by
    intro s hs
    haveI : NeZero s := neZero_of_dvd (hSM s hs)
    obtain ⟨a, _, b, has, hys⟩ := exists_slot_of_isRoot K ζ hζ s (hSM s hs) (hy s hs)
    obtain ⟨rfl, hu⟩ := sv_inj K (hy₀.symm.trans hys)
    refine ⟨has, ?_⟩
    rw [hu, ← pow_mul, ← pow_mul, hζu.pow_eq_one_iff_dvd]
    have h : M / s * (b * a₀ * s) = M * (b * a₀) := by
      rw [← mul_assoc, mul_right_comm, Nat.div_mul_cancel (hSM s hs)]
    rw [h]
    exact dvd_mul_right M _
  have ha₀ : a₀ = 1 := by
    have h : a₀ ∣ S.gcd id := Finset.dvd_gcd fun s hs => (key s hs).1
    rw [hgcd] at h
    exact Nat.dvd_one.mp h
  have hu₀ : (ζ ^ (M / M)) ^ (b₀ * a₀) = 1 := by
    have h : orderOf ((ζ ^ (M / M)) ^ (b₀ * a₀)) ∣ S.gcd id :=
      Finset.dvd_gcd fun s hs => orderOf_dvd_iff_pow_eq_one.mpr (key s hs).2
    rw [hgcd, Nat.dvd_one] at h
    exact orderOf_eq_one_iff.mp h
  subst ha₀
  rw [hu₀] at hy₀
  exact hy₀.trans (sv_one_one K)

end Factor

theorem jq_mem_K0 (M : ℕ) [NeZero M] (S : Finset ℕ) (hSM : ∀ s ∈ S, s ∣ M) (hM : M ∈ S)
    (hgcd : S.gcd id = 1) : jq ∈ K₀ S := by
  classical
  obtain ⟨z, hz⟩ : ∃ z : ℂ, IsPrimitiveRoot z M := ⟨_, Complex.isPrimitiveRoot_exp M (NeZero.ne M)⟩
  have hzU : IsUnit z := hz.isUnit (NeZero.ne M)
  set ζ : ℂˣ := hzU.unit with hζdef
  have hζ : IsPrimitiveRoot (ζ : ℂ) M := by rwa [hζdef, hzU.unit_spec]
  haveI : CharZero (K₀ S) := charZero_of_injective_algebraMap (algebraMap ℚ (K₀ S)).injective
  refine mem_of_unique_common_root (F := ℚ) (coeffEmb ℂ) (K₀ S) jq S Qs ?_ ?_ ?_ hM ?_ ?_
  · intro s hs
    haveI : NeZero s := neZero_of_dvd (hSM s hs)
    exact Qs_monic s
  · intro s hs n
    haveI : NeZero s := neZero_of_dvd (hSM s hs)
    exact Qs_coeff_mem S s hs n
  · intro s hs
    haveI : NeZero s := neZero_of_dvd (hSM s hs)
    exact isRoot_jq ℂ ζ hζ s (hSM s hs)
  · rw [Qs_map_eq ℂ ζ hζ M dvd_rfl]
    exact Splits.prod fun a _ => Splits.prod fun b _ => Splits.X_sub_C _
  · exact common_root_unique ℂ ζ hζ S hSM hM hgcd

end W7CGcdDescent

open W7CGcdDescent

theorem solution (M : ℕ) [NeZero M] (S : Finset ℕ)
    (hSM : ∀ s ∈ S, s ∣ M) (hM : M ∈ S) (hgcd : S.gcd id = 1) (d : ℕ) [NeZero d] (hd : d ∣ M) :
    ModularCurve.qExpand ℚ d ModularCurve.jq ∈ IntermediateField.adjoin ℚ
      {x : LaurentSeries ℚ | ∃ (s : ℕ) (_ : NeZero s), s ∈ S ∧ x = ModularCurve.qExpand ℚ s ModularCurve.jq} := by
  have hj : jq ∈ K₀ S := jq_mem_K0 M S hSM hM hgcd
  have hjM : qExpand ℚ M jq ∈ K₀ S :=
    IntermediateField.subset_adjoin ℚ _ ⟨M, inferInstance, hM, rfl⟩
  have hle : modularFunctionField M ≤ K₀ S := by
    rw [modularFunctionField, IntermediateField.adjoin_le_iff]
    rintro x (rfl | rfl)
    exacts [hj, hjM]
  exact hle (ModularCurve.functionFieldGeneration M d hd inferInstance)

end S_ModularCurve_qExpand_jq_mem_adjoin_of_gcd_eq_one
end P2MW
export P2MW.S_ModularCurve_qExpand_jq_mem_adjoin_of_gcd_eq_one (solution)
