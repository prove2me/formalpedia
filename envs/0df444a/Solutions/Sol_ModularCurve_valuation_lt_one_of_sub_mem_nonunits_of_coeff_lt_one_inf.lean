-- Prove2me | solution 1 for ModularCurve.valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/9296ee91-e5cb-5c1e-820d-542e502d377d

import Mathlib
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_PrimCosetReps
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_StarBank_starBank
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket
import Theorems.Thm_ModularCurve_eq_cosetTwoVarPoly_of_forall_isRoot
import Theorems.Thm_ModularCurve_ModularPolynomialData_exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex
import Theorems.Thm_ModularCurve_card_primCosetReps_eq_dedekindPsi
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_coeff_jqModC_pow_of_lt
import Theorems.Thm_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_eq_coeffRed
import Theorems.Thm_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero_inv
import Theorems.Thm_ModularCurve_CharPModel_exists_unique_valueHom
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

namespace ValLtOneInfSol

open ModularCurve Polynomial

section VanishingBelow

variable {K : Type*} [Field K]

def VB (x : LaurentSeries K) (n : ℤ) : Prop := ∀ m : ℤ, m < n → x.coeff m = 0

theorem VB.mono {x : LaurentSeries K} {n n' : ℤ} (h : VB x n) (hle : n' ≤ n) : VB x n' :=
  fun m hm => h m (lt_of_lt_of_le hm hle)

theorem VB_zero (n : ℤ) : VB (0 : LaurentSeries K) n := fun m _ => by simp

theorem VB_one : VB (1 : LaurentSeries K) 0 := by
  intro m hm
  rw [HahnSeries.coeff_one, if_neg hm.ne]

theorem VB.add {x y : LaurentSeries K} {n : ℤ} (hx : VB x n) (hy : VB y n) : VB (x + y) n :=
  fun m hm => by rw [HahnSeries.coeff_add, hx m hm, hy m hm, add_zero]

theorem VB.neg {x : LaurentSeries K} {n : ℤ} (hx : VB x n) : VB (-x) n :=
  fun m hm => by rw [HahnSeries.coeff_neg, hx m hm, neg_zero]

theorem VB.sub {x y : LaurentSeries K} {n : ℤ} (hx : VB x n) (hy : VB y n) : VB (x - y) n := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem VB_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries K) (n : ℤ)
    (h : ∀ i ∈ s, VB (f i) n) : VB (∑ i ∈ s, f i) n := fun m hm => by
  rw [HahnSeries.coeff_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi m hm

theorem VB.mul {x y : LaurentSeries K} {a b : ℤ} (hx : VB x a) (hy : VB y b) :
    VB (x * y) (a + b) := by
  intro m hm
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  obtain ⟨-, -, hsum⟩ := hp
  by_cases hu : p.1 < a
  · rw [hx p.1 hu, zero_mul]
  · have hv : p.2 < b := by omega
    rw [hy p.2 hv, mul_zero]

theorem coeff_mul_of_VB {x y : LaurentSeries K} {a b : ℤ} (hx : VB x a) (hy : VB y b) :
    (x * y).coeff (a + b) = x.coeff a * y.coeff b := by
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_single (a, b)
  · rintro ⟨u, v⟩ hp hne
    rw [Finset.mem_antidiagonal] at hp
    obtain ⟨-, -, hsum⟩ := hp
    dsimp only at hsum ⊢
    by_cases hu : u < a
    · rw [hx u hu, zero_mul]
    · have hne' : u ≠ a ∨ v ≠ b := by
        by_contra h
        push Not at h
        exact hne (Prod.ext h.1 h.2)
      have hv : v < b := by omega
      rw [hy v hv, mul_zero]
  · intro hnot
    rw [Finset.mem_antidiagonal] at hnot
    by_cases hxa : x.coeff a = 0
    · rw [hxa, zero_mul]
    · by_cases hyb : y.coeff b = 0
      · rw [hyb, mul_zero]
      · exact (hnot ⟨(HahnSeries.mem_support _ _).mpr hxa, (HahnSeries.mem_support _ _).mpr hyb,
          rfl⟩).elim

theorem VB.pow {x : LaurentSeries K} {a : ℤ} (hx : VB x a) : ∀ n : ℕ, VB (x ^ n) ((n : ℤ) * a)
  | 0 => by simpa using (VB_one (K := K))
  | n + 1 => by
      have h := (VB.pow hx n).mul hx
      rw [pow_succ]
      convert h using 1
      push_cast; ring

theorem coeff_pow_of_VB {x : LaurentSeries K} {a : ℤ} (hx : VB x a) :
    ∀ n : ℕ, (x ^ n).coeff ((n : ℤ) * a) = (x.coeff a) ^ n
  | 0 => by simp [HahnSeries.coeff_one]
  | n + 1 => by
      rw [pow_succ, pow_succ, show ((n + 1 : ℕ) : ℤ) * a = (n : ℤ) * a + a by push_cast; ring,
        coeff_mul_of_VB (hx.pow n) hx, coeff_pow_of_VB hx n]

theorem VB.twist {x : LaurentSeries K} {n : ℤ} (hx : VB x n) (u : Kˣ) :
    VB (qTwist u x) n := fun m hm => by
  rw [qTwist_coeff, hx m hm, mul_zero]

theorem VB.expand {x : LaurentSeries K} {n : ℤ} (hx : VB x n) (M : ℕ) [NeZero M] :
    VB (qExpand K M x) ((M : ℤ) * n) := fun m hm => by
  by_cases hd : (M : ℤ) ∣ m
  · obtain ⟨m', rfl⟩ := hd
    rw [qExpand_coeff_mul]
    apply hx
    have hM : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    exact lt_of_mul_lt_mul_left hm hM.le
  · exact qExpand_coeff_of_not_dvd M x hd

theorem VB_jqModC : VB (jqModC K) (-1) := fun m hm => by
  have h := coeff_jqModC_pow_of_lt K (b := 1) (m := m) (by simpa using hm)
  simpa using h

theorem VB_cosetConj (N : ℕ) (hN : N ≠ 0) (ζ : Kˣ) (t : ℕ × ℕ × ℕ) (ht : t ∈ primCosetReps N) :
    VB (cosetConj ζ (jqModC K) t) (-((N : ℤ) * N)) := by
  obtain ⟨a, b, d⟩ := t
  obtain ⟨had, -, -⟩ := (mem_primCosetReps hN).mp ht
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hN (by simpa using had.symm)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hN (by simpa using had.symm)
  have haN : a ≤ N := had ▸ Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero hd0)
  haveI : NeZero a := ⟨ha0⟩
  haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero ha0 ha0⟩
  have hEq : cosetConj ζ (jqModC K) (a, b, d) = qExpand K (a * a) (qTwist (ζ ^ (a * b)) (jqModC K)) := by
    rw [cosetConj_eq]; rfl
  rw [hEq]
  have h := ((VB_jqModC (K := K)).twist (ζ ^ (a * b))).expand (a * a)
  refine h.mono ?_
  have : (a : ℤ) * a ≤ (N : ℤ) * N := by
    have := Nat.mul_le_mul haN haN
    exact_mod_cast this
  push_cast
  linarith

def PB (P : Polynomial (LaurentSeries K)) (D : ℕ) (c : ℤ) : Prop :=
  ∀ i : ℕ, VB (P.coeff i) (((i : ℤ) - D) * c)

theorem PB_one (c : ℤ) : PB (1 : Polynomial (LaurentSeries K)) 0 c := by
  intro i
  rw [Polynomial.coeff_one]
  split_ifs with h
  · subst h
    simpa using (VB_one (K := K))
  · exact VB_zero _

theorem PB_X_sub_C {r : LaurentSeries K} {c : ℤ} (hr : VB r (-c)) :
    PB (Polynomial.X - Polynomial.C r) 1 c := by
  intro i
  match i with
  | 0 =>
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub]
      refine hr.neg.mono (le_of_eq ?_)
      push_cast; ring
  | 1 =>
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C_succ, sub_zero]
      simpa using (VB_one (K := K))
  | (n + 2) =>
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_of_ne_one (by omega),
        Polynomial.coeff_C_succ, sub_zero]
      exact VB_zero _

theorem PB.mul {P Q : Polynomial (LaurentSeries K)} {D₁ D₂ : ℕ} {c : ℤ}
    (hP : PB P D₁ c) (hQ : PB Q D₂ c) : PB (P * Q) (D₁ + D₂) c := by
  intro i
  rw [Polynomial.coeff_mul]
  refine VB_sum _ _ _ fun p hp => ?_
  have hpsum : p.1 + p.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have h := (hP p.1).mul (hQ p.2)
  refine h.mono (le_of_eq ?_)
  have : (i : ℤ) = p.1 + p.2 := by exact_mod_cast hpsum.symm
  rw [this]
  push_cast
  ring

theorem PB_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → LaurentSeries K) (c : ℤ)
    (hr : ∀ t ∈ s, VB (r t) (-c)) :
    PB (∏ t ∈ s, (Polynomial.X - Polynomial.C (r t))) s.card c := by
  induction s using Finset.induction_on with
  | empty => simpa using PB_one (K := K) c
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.add_comm]
      exact (PB_X_sub_C (hr a (Finset.mem_insert_self a s))).mul
        (ih fun t ht => hr t (Finset.mem_insert_of_mem ht))

theorem coeff_eval₂_qExpand_jqModC [CharZero K] (N : ℕ) [NeZero N] (c : Polynomial ℤ)
    (hc : c ≠ 0) :
    (Polynomial.eval₂ (Int.castRingHom (LaurentSeries K)) (qExpand K N (jqModC K)) c).coeff
        ((c.natDegree : ℤ) * (-(N : ℤ))) ≠ 0 := by
  set X₀ : LaurentSeries K := qExpand K N (jqModC K) with hX₀
  have hVB : VB X₀ (-(N : ℤ)) := by
    have h := (VB_jqModC (K := K)).expand N
    simpa using h
  have hlead : X₀.coeff (-(N : ℤ)) = 1 := by
    have h : (-(N : ℤ)) = (N : ℤ) * (-1) := by ring
    rw [h, hX₀, qExpand_coeff_mul, coeff_jqModC_neg_one]

  have hterm : ∀ (m : ℕ) (n : ℤ),
      ((Int.castRingHom (LaurentSeries K)) (c.coeff m) * X₀ ^ m).coeff n
        = ((c.coeff m : ℤ) : K) * (X₀ ^ m).coeff n := by
    intro m n
    rw [eq_intCast, ← map_intCast (HahnSeries.C : K →+* LaurentSeries K) (c.coeff m),
      HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  rw [Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_range_succ,
    Finset.sum_eq_zero, zero_add, hterm, coeff_pow_of_VB hVB, hlead, one_pow, mul_one]
  · exact_mod_cast (Polynomial.leadingCoeff_ne_zero.mpr hc)
  · intro m hm
    rw [Finset.mem_range] at hm
    rw [hterm, (hVB.pow m) _ ?_, mul_zero]
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hm' : (m : ℤ) < c.natDegree := by exact_mod_cast hm
    nlinarith

end VanishingBelow

def PhiC (N : ℕ) [NeZero N] (data : ModularPolynomialData N) : Polynomial (LaurentSeries ℂ) :=
  data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ)) (qExpand ℂ N (jqModC ℂ)))

theorem PhiC_coeff (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (i : ℕ) :
    (PhiC N data).coeff i =
      Polynomial.eval₂ (Int.castRingHom (LaurentSeries ℂ)) (qExpand ℂ N (jqModC ℂ))
        (data.Φ.coeff i) := by
  rw [PhiC, Polynomial.coeff_map]
  rfl

theorem PhiC_eq_cosetTwoVarPoly (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    ∃ ζ : ℂˣ, IsPrimitiveRoot ζ N ∧ PhiC N data = cosetTwoVarPoly ζ N (jqModC ℂ) := by
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨ζ, hζ, hroots⟩ :=
    ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex N data
  refine ⟨ζ, hζ, ?_⟩
  have hPmonic : (PhiC N data).Monic := data.monic.map _
  have hPdeg : (PhiC N data).natDegree = (primCosetReps N).card := by
    rw [PhiC, data.monic.natDegree_map, data.natDegree_eq, card_primCosetReps_eq_dedekindPsi N hN]
  have hJ : (jqModC ℂ).coeff (-1) ≠ 0 := by
    rw [coeff_jqModC_neg_one]; exact one_ne_zero
  have hJ' : ∀ m : ℤ, m < -1 → (jqModC ℂ).coeff m = 0 := VB_jqModC
  exact eq_cosetTwoVarPoly_of_forall_isRoot ℂ N hN ζ hζ (jqModC ℂ) hJ hJ' (PhiC N data)
    hPmonic hPdeg hroots

theorem natDegree_coeff_le (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (i : ℕ) :
    (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i) := by
  have hN : N ≠ 0 := NeZero.ne N
  by_cases hci : data.Φ.coeff i = 0
  · rw [hci, Polynomial.natDegree_zero]; exact Nat.zero_le _
  have hiψ : i ≤ dedekindPsi N := by
    by_contra h
    push Not at h
    exact hci (Polynomial.coeff_eq_zero_of_natDegree_lt (data.natDegree_eq ▸ h))

  obtain ⟨ζ, -, hfact⟩ := PhiC_eq_cosetTwoVarPoly N data

  have hPB : PB (cosetTwoVarPoly ζ N (jqModC ℂ)) (dedekindPsi N) ((N : ℤ) * N) := by
    have h := PB_prod (primCosetReps N) (fun t => cosetConj ζ (jqModC ℂ) t) ((N : ℤ) * N)
      (fun t ht => VB_cosetConj N hN ζ t ht)
    rw [card_primCosetReps_eq_dedekindPsi N hN] at h
    exact h

  have hne := coeff_eval₂_qExpand_jqModC (K := ℂ) N (data.Φ.coeff i) hci
  have hle : ¬ ((data.Φ.coeff i).natDegree : ℤ) * (-(N : ℤ))
      < ((i : ℤ) - dedekindPsi N) * ((N : ℤ) * N) := by
    intro hlt
    apply hne
    have h := hPB i _ hlt
    rwa [← hfact, PhiC_coeff] at h
  push Not at hle

  have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hkey : ((data.Φ.coeff i).natDegree : ℤ) ≤ (N : ℤ) * ((dedekindPsi N : ℤ) - i) := by
    nlinarith
  zify [hiψ]
  linarith

section Degree

variable (k : Type*) [Field k]

theorem adjoin_jqModC_le (N : ℕ) [NeZero N] :
    IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)) ≤ modularFunctionFieldC k N :=
  IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem extendScalars_adjoin_jqModC_eq (N : ℕ) [NeZero N] :
    IntermediateField.extendScalars (adjoin_jqModC_le k N) =
      IntermediateField.adjoin (IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)))
        ({jqNModC k N} : Set (LaurentSeries k)) := by
  apply IntermediateField.restrictScalars_injective k
  exact (IntermediateField.extendScalars_restrictScalars _).trans
    (IntermediateField.adjoin_simple_adjoin_simple (F := k) (α := jqModC k)
      (β := jqNModC k N)).symm

theorem relfinrank_eq_dedekindPsi (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (hℓN : ¬ ℓ ∣ N) :
    (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N := by
  have hsock : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∣ N →
      jqNModC k p ∉ IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)) := by
    intro p _ hp
    refine StarBank.starBank (ℓ := ℓ) ?_
    rintro rfl
    exact hℓN hp
  rw [IntermediateField.relfinrank_eq_finrank_of_le (adjoin_jqModC_le k N),
    extendScalars_adjoin_jqModC_eq]
  exact finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket N hsock

end Degree

section PlaceFacts

open AlgebraicCurve IsLocalRing

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (P : Place K F) {u : F} (hu : u ∈ P.toValuationSubring) :
    0 ≤ P.ord u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · simp
  by_cases h : IsUnit (⟨u, hu⟩ : P.toValuationSubring)
  · obtain ⟨w, hw⟩ := h
    have := P.ord_coe_unit w
    rw [hw] at this
    exact this.symm.le
  · exact ((P.mem_maximalIdeal_iff_ord_pos hu0 hu).mp
      ((IsLocalRing.mem_maximalIdeal _).mpr h)).le

theorem mem_of_ord_pos (P : Place K F) {u : F} (hu : 0 < P.ord u) : u ∈ P.toValuationSubring := by
  by_contra h
  have hinv : u⁻¹ ∈ P.toValuationSubring := (P.toValuationSubring.mem_or_inv_mem u).resolve_left h
  have := ord_nonneg_of_mem P hinv
  rw [Place.ord_inv] at this
  omega

theorem mem_nonunits_of_ord_pos (P : Place K F) {u : F} (hu : 0 < P.ord u) :
    u ∈ P.toValuationSubring.nonunits := by
  have hmem := mem_of_ord_pos P hu
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have : (⟨u, hmem⟩ : P.toValuationSubring) ∈ maximalIdeal _ :=
    (P.mem_maximalIdeal_iff_ord_pos hu0 hmem).mpr hu
  exact ValuationSubring.coe_mem_nonunits_iff.mpr this

theorem const_eq_zero_of_mem_nonunits (P : Place K F) {x : K}
    (hx : algebraMap K F x ∈ P.toValuationSubring.nonunits) : x = 0 := by
  by_contra h0
  rw [ValuationSubring.mem_nonunits_iff] at hx
  have h2 : P.toValuationSubring.valuation (algebraMap K F x⁻¹) ≤ 1 :=
    (P.toValuationSubring.valuation_le_one_iff _).mpr (P.algebraMap_mem' _)
  have h := Left.mul_lt_one_of_lt_of_le hx h2
  rw [← map_mul, ← map_mul, mul_inv_cancel₀ h0, map_one, map_one] at h
  exact lt_irrefl _ h

end PlaceFacts

theorem eval₂RingHom_mem {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : S)
    (T : Subring S) (hf : ∀ r, f r ∈ T) (hx : x ∈ T) (q : Polynomial R) :
    Polynomial.eval₂RingHom f x q ∈ T := by
  induction q using Polynomial.induction_on with
  | C a =>
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact hf a
  | add p q hp hq =>
      rw [map_add]
      exact T.add_mem hp hq
  | monomial n a h =>
      rw [pow_succ, ← mul_assoc, map_mul]
      refine T.mul_mem h ?_
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      exact hx

end ValLtOneInfSol

end

open ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction ValuationSubring AlgebraicCurve IsLocalRing Polynomial

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
noncomputable scoped instance ValLtOneInfSol.instQbarIsAlgebraic :
    Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

p2m_reactivate "P2MW.S_ModularCurve_valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf.ValLtOneInfSol"

local notation "Qb" => AlgebraicClosure ℚ

set_option hygiene false in

local notation "FF" => (↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M)))

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
open AlgebraicCurve ModularCurve.CharPModel in
theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M ℓ : ℕ) [NeZero M] [Fact ℓ.Prime]
    (hℓA : A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) < 1) (hlM : ¬ ℓ ∣ M)
    (w : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M)))
    (a₀ : A)
    (hj : 0 < w.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full M (jq_mem M))⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))⁻¹
      - algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
        (a₀ : AlgebraicClosure ℚ)))
    (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
    (hb : ∃ p : Polynomial (affineBaseInf M A), p.Monic ∧
      Polynomial.eval₂ (affineBaseInf M A).subtype b p = 0)
    (hcoeff : ∀ n : ℤ,
      A.valuation ((b : LaurentSeries (AlgebraicClosure ℚ)).coeff n) < 1)
    (a : A)
    (hval : (b - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
      (a : AlgebraicClosure ℚ)) ∈ w.toValuationSubring.nonunits) :
    A.valuation (a : AlgebraicClosure ℚ) < 1 := by

  set k := ResidueField ↥A with hk
  set red : ↥A →+* k := IsLocalRing.residue ↥A with hred
  haveI : CharP k ℓ := by
    refine (CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_
    have hℓmem : ((ℓ : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
      rw [ValuationSubring.valuation_lt_one_iff]
      simpa using hℓA
    have : red (ℓ : ↥A) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hℓmem
    simpa using this
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData M
  have hdeg := ValLtOneInfSol.relfinrank_eq_dedekindPsi k M ℓ hlM
  have hdegX := ValLtOneInfSol.natDegree_coeff_le M data

  have hx : (b : LaurentSeries Qb) ∈ IntermediateField.adjoin Qb {jqModC Qb, jqNModC Qb M} := by
    show (b : LaurentSeries Qb) ∈ modularFunctionFieldC Qb M
    rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero]
    show (b : LaurentSeries Qb) ∈
      IntermediateField.adjoin Qb {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ M ∧ x = jqNModC Qb d}
    rw [← ModularCurve.laurentBaseChange_modularFunctionFieldFull Qb M]
    exact b.2

  have hjBar : ((jBar M : FF) : LaurentSeries Qb) = jqModC Qb := by
    show (jqModC ℚ).map (algebraMap ℚ Qb) = jqModC Qb
    exact map_jqModC (algebraMap ℚ Qb)
  have hjq0 : jqModC Qb ≠ 0 := by
    intro h
    have := congrArg (fun x : LaurentSeries Qb => x.coeff (-1)) h
    simp [coeff_jqModC_neg_one] at this
  set cH : ↥A →+* LaurentSeries Qb := (algebraMap Qb (LaurentSeries Qb)).comp A.subtype with hcH
  set ψ : Polynomial ↥A →+* LaurentSeries Qb :=
    Polynomial.eval₂RingHom cH (jqModC Qb)⁻¹ with hψ
  set φ : Polynomial ↥A →+* FF :=
    Polynomial.eval₂RingHom (constantsHom M A) (jBar M)⁻¹ with hφ
  have hφψ : (algebraMap FF (LaurentSeries Qb)).comp φ = ψ := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [RingHom.comp_apply, hφ, hψ, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, Polynomial.eval₂_C, IntermediateField.algebraMap_apply]
      rfl
    · rw [RingHom.comp_apply, hφ, hψ, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, Polynomial.eval₂_X, IntermediateField.algebraMap_apply, ← hjBar,
        IntermediateField.coe_inv]
  have hφψ' : ∀ q : Polynomial ↥A, ((φ q : FF) : LaurentSeries Qb) = ψ q := fun q => by
    rw [← hφψ, RingHom.comp_apply, IntermediateField.algebraMap_apply]

  have hφmem : ∀ q : Polynomial ↥A, φ q ∈ affineBaseInf M A := fun q =>
    ValLtOneInfSol.eval₂RingHom_mem (constantsHom M A) (jBar M)⁻¹ (affineBaseInf M A)
      (fun r => Subring.subset_closure (Or.inl ⟨r, rfl⟩))
      (Subring.subset_closure (Or.inr rfl)) q
  have hrange : affineBaseInf M A ≤ φ.range := by
    rw [affineBaseInf, Subring.closure_le]
    rintro x (⟨r, rfl⟩ | hx')
    · exact ⟨Polynomial.C r, by rw [hφ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]⟩
    · rw [Set.mem_singleton_iff] at hx'
      subst hx'
      exact ⟨Polynomial.X, by rw [hφ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]⟩

  have hint : ∃ P : Polynomial (Polynomial ↥A), P.Monic ∧
      Polynomial.eval₂ ψ (b : LaurentSeries Qb) P = 0 := by
    obtain ⟨p, hp, hev⟩ := hb
    have hlifts : p.map (affineBaseInf M A).subtype ∈ Polynomial.lifts φ := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨q, hq⟩ := hrange (p.coeff n).2
      exact ⟨q, hq⟩
    obtain ⟨P, hPmap, -, hPmonic⟩ :=
      Polynomial.lifts_and_degree_eq_and_monic hlifts (hp.map _)
    refine ⟨P, hPmonic, ?_⟩
    have hevF : Polynomial.eval₂ φ b P = 0 := by
      rw [← Polynomial.eval_map, hPmap, Polynomial.eval_map]
      exact hev
    have := congrArg (algebraMap FF (LaurentSeries Qb)) hevF
    rw [Polynomial.hom_eval₂, hφψ, map_zero, IntermediateField.algebraMap_apply] at this
    exact this

  set ML : Subring (LaurentSeries Qb) := modularLocalized M A.toSubring red with hML
  have hconst_mem : ∀ r : ↥A, cH r ∈ ML := fun r =>
    subring_le_localizedAtKer _ _ _ _ (constSeries_mem_modularRing M A.toSubring r)
  have hjinv_mem : (jqModC Qb)⁻¹ ∈ ML := by
    refine (mem_localizedAtKer _ _ _ _).mpr
      ⟨1, ⟨jqModC Qb, jqModC_mem_modularRing M A.toSubring⟩, ?_, ?_⟩
    · rw [notMem_redKer_iff, redRes_apply]
      intro h
      have := congrArg (fun x : LaurentSeries k => x.coeff (-1)) h
      simp only [coeffRed_coeff, HahnSeries.coeff_zero] at this
      have hc1 : (⟨((⟨jqModC Qb, jqModC_mem_modularRing M A.toSubring⟩ :
            modularRing M A.toSubring) : LaurentSeries Qb).coeff (-1),
          jqModC_mem_integralCoeffs A.toSubring (-1)⟩ : ↥A.toSubring) = 1 :=
        Subtype.ext (by simp [coeff_jqModC_neg_one])
      rw [hc1, map_one] at this
      exact one_ne_zero this
    · rw [OneMemClass.coe_one]
      exact inv_mul_cancel₀ hjq0
  have hψmem : ∀ q : Polynomial ↥A, ψ q ∈ ML := fun q =>
    ValLtOneInfSol.eval₂RingHom_mem cH (jqModC Qb)⁻¹ ML hconst_mem hjinv_mem q
  set θ : Polynomial ↥A →+* ML := ψ.codRestrict ML hψmem with hθ
  have hbML : (b : LaurentSeries Qb) ∈ ML := by
    obtain ⟨P, hPmonic, hPev⟩ := hint
    refine mem_modularLocalized_of_eval2_monic A red M data hdeg hx (p := P.map θ)
      (hPmonic.map θ) ?_
    have hcomp : ML.subtype.comp θ = ψ := RingHom.ext fun q => rfl
    rw [← hcomp, ← Polynomial.eval₂_map] at hPev
    exact hPev
  set f : ML := ⟨(b : LaurentSeries Qb), hbML⟩ with hf

  have hbA : (b : LaurentSeries Qb) ∈ integralCoeffs A.toSubring := fun n =>
    (A.valuation_le_one_iff _).mp (le_of_lt (hcoeff n))
  have hker : modularRedLocHom M A.toSubring red f = 0 := by
    rw [modularRedLocHom_eq_coeffRed A.toSubring red M f hbA]
    ext n
    rw [coeffRed_coeff, HahnSeries.coeff_zero]
    have hmem : (⟨((b : FF) : LaurentSeries Qb).coeff n, hbA n⟩ : ↥A) ∈ maximalIdeal ↥A := by
      rw [ValuationSubring.valuation_lt_one_iff]
      exact hcoeff n
    exact (IsLocalRing.residue_eq_zero_iff (R := ↥A) _).mpr hmem

  obtain ⟨m, hm, f', ⟨P', hP'monic, hP'ev⟩, hbf⟩ :=
    ModularCurve.CharPModel.exists_eq_const_mul_of_modularRedLocHom_eq_zero_inv M A k red data
      hdeg hdegX f hint hker
  have hmmax : m ∈ maximalIdeal ↥A := (IsLocalRing.residue_eq_zero_iff _).mp hm

  have hjw : (jBar M)⁻¹ - algebraMap Qb FF (a₀ : Qb) ∈ w.toValuationSubring.nonunits :=
    ValLtOneInfSol.mem_nonunits_of_ord_pos w hj
  by_cases hm0 : (m : Qb) = 0
  ·
    have hb0 : b = 0 := by
      apply Subtype.ext
      show (f : LaurentSeries Qb) = ((0 : FF) : LaurentSeries Qb)
      rw [hbf, hm0, map_zero, zero_mul, ZeroMemClass.coe_zero]
    rw [hb0, zero_sub, ← map_neg] at hval
    have := ValLtOneInfSol.const_eq_zero_of_mem_nonunits w hval
    rw [neg_eq_zero] at this
    rw [this, Valuation.map_zero]
    exact zero_lt_one
  ·
    set b' : FF := (algebraMap Qb FF (m : Qb))⁻¹ * b with hb'def
    have halg0 : algebraMap Qb FF (m : Qb) ≠ 0 := (_root_.map_ne_zero _).mpr hm0
    have hbb' : b = algebraMap Qb FF (m : Qb) * b' := by
      rw [hb'def, mul_inv_cancel_left₀ halg0]
    have hb'coe : ((b' : FF) : LaurentSeries Qb) = (f' : LaurentSeries Qb) := by
      have h1 : ((b : FF) : LaurentSeries Qb) = (f : LaurentSeries Qb) := rfl
      have hm0' : algebraMap Qb (LaurentSeries Qb) (m : Qb) ≠ 0 := (_root_.map_ne_zero _).mpr hm0
      have h2 : ((algebraMap Qb FF (m : Qb) : FF) : LaurentSeries Qb)
          = algebraMap Qb (LaurentSeries Qb) (m : Qb) := rfl
      rw [hb'def, MulMemClass.coe_mul, IntermediateField.coe_inv, h2, h1, hbf, ← mul_assoc,
        inv_mul_cancel₀ hm0', one_mul]

    set C : Subring FF :=
      Subring.closure (⇑(algebraMap Qb FF) '' (A : Set Qb) ∪ {(jBar M)⁻¹}) with hCdef
    have hAC : affineBaseInf M A = C := by
      rw [hCdef, affineBaseInf]
      congr 2
      ext x
      constructor
      · rintro ⟨r, rfl⟩
        exact ⟨r, r.2, rfl⟩
      · rintro ⟨r, hr, rfl⟩
        exact ⟨⟨r, hr⟩, rfl⟩
    have hφC : ∀ q : Polynomial ↥A, φ q ∈ C := fun q => hAC ▸ hφmem q
    set φC : Polynomial ↥A →+* C := φ.codRestrict C hφC with hφCdef

    have hb'int : ∃ p : Polynomial C, p.Monic ∧ Polynomial.eval₂ C.subtype (b' : FF) p = 0 := by
      refine ⟨P'.map φC, hP'monic.map φC, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : C.subtype.comp φC = φ := RingHom.ext fun q => rfl
      rw [hcomp]
      apply (algebraMap FF (LaurentSeries Qb)).injective
      rw [Polynomial.hom_eval₂, hφψ, map_zero, IntermediateField.algebraMap_apply, hb'coe]
      exact hP'ev

    set B₀ : Subring FF := (integralClosure (↥C) FF).toSubring with hB₀
    have halgC : algebraMap (↥C) FF = C.subtype := RingHom.ext fun _ => rfl
    have hB₀int : ∀ y : B₀, ∃ p : Polynomial C, p.Monic ∧
        Polynomial.eval₂ C.subtype (y : FF) p = 0 := fun y => by
      obtain ⟨p, hp, hev⟩ := ((mem_integralClosure_iff _ _).mp y.2 : IsIntegral C (y : FF))
      exact ⟨p, hp, halgC ▸ hev⟩
    have hb'B₀ : (b' : FF) ∈ B₀ := by
      rw [hB₀, Subalgebra.mem_toSubring]
      refine (mem_integralClosure_iff _ _).mpr ?_
      obtain ⟨p, hp, hev⟩ := hb'int
      exact ⟨p, hp, halgC ▸ hev⟩
    obtain ⟨χ, hχ, -⟩ :=
      ModularCurve.CharPModel.exists_unique_valueHom A (jBar M)⁻¹ B₀ hB₀int w ⟨a₀, hjw⟩
    set c : ↥A := χ ⟨b', hb'B₀⟩ with hcdef
    have hc : (b' : FF) - algebraMap Qb FF (c : Qb) ∈ w.toValuationSubring.nonunits :=
      hχ ⟨b', hb'B₀⟩

    have hkey : algebraMap Qb FF ((a : Qb) - (m : Qb) * (c : Qb))
        ∈ w.toValuationSubring.nonunits := by
      have hsplit : algebraMap Qb FF ((a : Qb) - (m : Qb) * (c : Qb))
          = algebraMap Qb FF (m : Qb) * ((b' : FF) - algebraMap Qb FF (c : Qb))
            - (b - algebraMap Qb FF (a : Qb)) := by
        rw [hbb', map_sub, map_mul]
        ring
      rw [hsplit, ValuationSubring.mem_nonunits_iff]
      rw [ValuationSubring.mem_nonunits_iff] at hc hval
      refine Valuation.map_sub_lt _ ?_ hval
      rw [Valuation.map_mul, mul_comm]
      have hm1 : w.toValuationSubring.valuation (algebraMap Qb FF (m : Qb)) ≤ 1 :=
        (w.toValuationSubring.valuation_le_one_iff _).mpr (w.algebraMap_mem' _)
      exact Left.mul_lt_one_of_lt_of_le hc hm1
    have hamc : (a : Qb) = ((m * c : ↥A) : Qb) := by
      have := ValLtOneInfSol.const_eq_zero_of_mem_nonunits w hkey
      rw [sub_eq_zero] at this
      rw [this, MulMemClass.coe_mul]
    rw [hamc, ← ValuationSubring.valuation_lt_one_iff]
    exact Ideal.mul_mem_right _ _ hmmax

end S_ModularCurve_valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf
end P2MW
export P2MW.S_ModularCurve_valuation_lt_one_of_sub_mem_nonunits_of_coeff_lt_one_inf (solution)
