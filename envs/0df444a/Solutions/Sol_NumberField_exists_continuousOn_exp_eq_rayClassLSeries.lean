-- Prove2me | solution 1 for NumberField.exists_continuousOn_exp_eq_rayClassLSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1c1a0644-e39c-5ead-855c-a0e0ec3a61d7

import Mathlib
import Definitions.Def_NumberField_CompletedRayL
import Definitions.Def_NumberField_RayCharacterData
import Definitions.Def_FrobeniusDensity_PrimeSums
import Definitions.Def_NumberField_PrimeNormSums
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries

set_option autoImplicit false

noncomputable section

namespace P2mRayEuler

open NumberField IsDedekindDomain Deep.NTSupply Filter Topology NumberField.PrimeNormSum
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [NumberField K] {𝔣 : Ideal (𝓞 K)}
  (χ : NarrowRayClassGroup K 𝔣 →* ℂ)

def chiI (I : Ideal (𝓞 K)) : ℂ := M4aP2.chiIdeal K 𝔣 χ (I : FractionalIdeal (𝓞 K)⁰ K)

theorem coe_ne_zero {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]

theorem chiI_bot : chiI χ ⊥ = 0 := by
  rw [chiI, M4aP2.chiIdeal, dif_neg]
  rw [not_not, FractionalIdeal.coeIdeal_eq_zero]

theorem chiI_of_ne_bot {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    chiI χ I = if hc : Units.mk0 _ (coe_ne_zero hI) ∈ coprimeToModulus K 𝔣 then
      χ (NarrowRayClassGroup.mk K 𝔣 ⟨Units.mk0 _ (coe_ne_zero hI), hc⟩) else 0 := by
  rw [chiI, M4aP2.chiIdeal, dif_pos (coe_ne_zero hI)]

theorem norm_apply_eq_one (g : NarrowRayClassGroup K 𝔣) [Finite (NarrowRayClassGroup K 𝔣)] :
    ‖χ g‖ = 1 :=
  (χ.isOfFinOrder (isOfFinOrder_of_finite g)).norm_eq_one

theorem norm_chiI_le_one (h𝔣 : 𝔣 ≠ ⊥) (I : Ideal (𝓞 K)) : ‖chiI χ I‖ ≤ 1 := by
  haveI : Finite (NarrowRayClassGroup K 𝔣) := Deep.NTSupply.finite K h𝔣
  by_cases hI : I = ⊥
  · rw [hI, chiI_bot, norm_zero]; exact zero_le_one
  · rw [chiI_of_ne_bot χ hI]
    split_ifs
    · rw [norm_apply_eq_one]
    · rw [norm_zero]; exact zero_le_one

theorem chiI_top : chiI χ ⊤ = 1 := by
  rw [chiI_of_ne_bot χ (by simp)]
  have h1 : Units.mk0 ((⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) (coe_ne_zero (by simp)) = 1 :=
    Units.ext (by rw [Units.val_mk0, FractionalIdeal.coeIdeal_top, Units.val_one])
  have hc : Units.mk0 ((⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) (coe_ne_zero (by simp)) ∈
      coprimeToModulus K 𝔣 := by rw [h1]; exact one_mem _
  rw [dif_pos hc]
  have : (⟨Units.mk0 _ (coe_ne_zero (by simp)), hc⟩ : ↥(coprimeToModulus K 𝔣)) = 1 := Subtype.ext h1
  rw [this, map_one, map_one]

theorem mem_coprime_mul_iff {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    Units.mk0 _ (coe_ne_zero (mul_ne_zero hI hJ : I * J ≠ ⊥)) ∈ coprimeToModulus K 𝔣 ↔
      Units.mk0 _ (coe_ne_zero hI) ∈ coprimeToModulus K 𝔣 ∧ Units.mk0 _ (coe_ne_zero hJ) ∈ coprimeToModulus K 𝔣 := by
  simp only [mem_coprimeToModulus_iff, Units.val_mk0]
  have hcount : ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v ((I * J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) +
          FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) := by
    intro v
    rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K v (coe_ne_zero hI) (coe_ne_zero hJ)]
  constructor
  · intro h
    constructor
    · intro v hv
      have h1 := h v hv
      rw [hcount] at h1
      have := FractionalIdeal.count_coe_nonneg K v I
      have := FractionalIdeal.count_coe_nonneg K v J
      omega
    · intro v hv
      have h1 := h v hv
      rw [hcount] at h1
      have := FractionalIdeal.count_coe_nonneg K v I
      have := FractionalIdeal.count_coe_nonneg K v J
      omega
  · rintro ⟨h1, h2⟩ v hv
    rw [hcount, h1 v hv, h2 v hv, add_zero]

theorem chiI_mul {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : chiI χ (I * J) = chiI χ I * chiI χ J := by
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  rw [chiI_of_ne_bot χ hIJ, chiI_of_ne_bot χ hI, chiI_of_ne_bot χ hJ]
  by_cases hc : Units.mk0 _ (coe_ne_zero hIJ) ∈ coprimeToModulus K 𝔣
  · obtain ⟨hcI, hcJ⟩ := (mem_coprime_mul_iff hI hJ).mp hc
    rw [dif_pos hc, dif_pos hcI, dif_pos hcJ, ← map_mul, ← map_mul]
    refine congrArg χ (congrArg (NarrowRayClassGroup.mk K 𝔣) (Subtype.ext (Units.ext ?_)))
    show ((I * J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = (I : FractionalIdeal (𝓞 K)⁰ K) * J
    exact FractionalIdeal.coeIdeal_mul I J
  · rw [dif_neg hc]
    rw [mem_coprime_mul_iff hI hJ, not_and_or] at hc
    rcases hc with h | h
    · rw [dif_neg h, zero_mul]
    · rw [dif_neg h, mul_zero]

def wt (s : ℝ) (I : Ideal (𝓞 K)) : ℝ := (Ideal.absNorm I : ℝ) ^ (-s)

theorem wt_nonneg (s : ℝ) (I : Ideal (𝓞 K)) : 0 ≤ wt s I := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem wt_mul (s : ℝ) (I J : Ideal (𝓞 K)) : wt s (I * J) = wt s I * wt s J := by
  rw [wt, wt, wt, map_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

theorem wt_prime (s : ℝ) (v : HeightOneSpectrum (𝓞 K)) : wt s v.asIdeal = pw K s v := rfl

private def _root_.P2mRayEuler.term (s : ℝ) (I : Ideal (𝓞 K)) : ℂ := chiI χ I * (wt s I : ℂ)

p2m_export "P2mRayEuler" "term"
theorem term_bot (s : ℝ) : term χ s ⊥ = 0 := by rw [term, chiI_bot, zero_mul]

theorem term_top (s : ℝ) : term χ s ⊤ = 1 := by
  rw [term, chiI_top, wt, Ideal.absNorm_top, Nat.cast_one, Real.one_rpow, Complex.ofReal_one, mul_one]

theorem term_mul (s : ℝ) {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    term χ s (I * J) = term χ s I * term χ s J := by
  rw [term, term, term, chiI_mul χ hI hJ, wt_mul, Complex.ofReal_mul]; ring

theorem term_pow (s : ℝ) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (k : ℕ) : term χ s (I ^ k) = term χ s I ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Ideal.one_eq_top, term_top]
  | succ k ih => rw [pow_succ, term_mul χ s (pow_ne_zero _ hI) hI, ih, pow_succ]

private theorem _root_.P2mRayEuler.norm_term_le (h𝔣 : 𝔣 ≠ ⊥) (s : ℝ) (I : Ideal (𝓞 K)) : ‖term χ s I‖ ≤ wt s I := by
  rw [term, norm_mul, Complex.norm_real, Real.norm_of_nonneg (wt_nonneg s I)]
  calc ‖chiI χ I‖ * wt s I ≤ 1 * wt s I := mul_le_mul_of_nonneg_right (norm_chiI_le_one χ h𝔣 I) (wt_nonneg s I)
    _ = wt s I := one_mul _

p2m_export "P2mRayEuler" "norm_term_le"
theorem norm_term_prime_le_half (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    ‖term χ s v.asIdeal‖ ≤ 1 / 2 := by
  refine (norm_term_le χ h𝔣 s _).trans ?_
  rw [wt_prime]
  calc pw K s v ≤ pw K 1 v := pw_antitone hs v
    _ ≤ 1 / 2 := by
      rw [pw, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_one]
      have := two_le_absNorm v
      have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast this
      rw [inv_le_comm₀ (by linarith) (by norm_num), one_div, inv_inv]
      exact h2

theorem summable_wt {s : ℝ} (hs : 1 < s) : Summable (wt (K := K) s) := by
  set e : ℕ → ℝ := fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)
    with he
  have h5 : Summable e := summable_dedekind_terms hs
  have henn : ∀ n, 0 ≤ e n := fun n => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine summable_of_sum_le (fun I => wt_nonneg s I) (c := ∑' n, e n) fun T => ?_
  have hmaps : ∀ I ∈ T, Ideal.absNorm I ∈ T.image Ideal.absNorm := fun I hI => Finset.mem_image_of_mem _ hI
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hstep : ∀ n : ℕ, ∀ S : Finset (Ideal (𝓞 K)),
      (∀ I ∈ S, Ideal.absNorm I = n) → ∑ I ∈ S, wt s I ≤ e n := by
    intro n S hS
    have hterm : ∀ I ∈ S, wt s I = (n : ℝ) ^ (-s) := fun I hI => by rw [wt, hS I hI]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, he]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).to_subtype
    have hle := Nat.card_le_card_of_injective
      (fun I : S => (⟨I.1, hS I.1 I.2⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
      (fun a b h => by
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext h)
    rw [Nat.card_eq_finsetCard] at hle
    exact_mod_cast hle
  calc ∑ n ∈ T.image Ideal.absNorm, ∑ I ∈ T with Ideal.absNorm I = n, wt s I
      ≤ ∑ n ∈ T.image Ideal.absNorm, e n :=
        Finset.sum_le_sum fun n _ => hstep n _ (fun I hI => (Finset.mem_filter.mp hI).2)
    _ ≤ ∑' n, e n := h5.sum_le_tsum _ (fun n _ => henn n)

theorem summable_term (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 < s) : Summable (term χ s) :=
  Summable.of_norm_bounded (summable_wt hs) (norm_term_le χ h𝔣 s)

theorem summable_norm_term (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 < s) : Summable fun I => ‖term χ s I‖ :=
  (summable_wt hs).of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le χ h𝔣 s)

section Bridge

def idealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.zero_eq_bot])⟩

theorem idealUnit_eq (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : idealUnit I hI = Units.mk0 _ (coe_ne_zero hI) :=
  Units.ext (by rw [idealUnit, FractionalIdeal.coe_mk0, Units.val_mk0])

def IsClassOf (C : NarrowRayClassGroup K 𝔣) (I : Ideal (𝓞 K)) : Prop :=
  ∃ hI : I ≠ ⊥, ∃ hc : idealUnit I hI ∈ coprimeToModulus K 𝔣,
    NarrowRayClassGroup.mk K 𝔣 ⟨idealUnit I hI, hc⟩ = C

def classSum [Fintype (NarrowRayClassGroup K 𝔣)] (I : Ideal (𝓞 K)) : ℂ :=
  ∑ C : NarrowRayClassGroup K 𝔣, if IsClassOf C I then χ C else 0

theorem classSum_eq_chiI [Fintype (NarrowRayClassGroup K 𝔣)] (I : Ideal (𝓞 K)) : classSum χ I = chiI χ I := by
  unfold classSum
  by_cases hI : I = ⊥
  · rw [hI, chiI_bot]
    refine Finset.sum_eq_zero fun C _ => ?_
    rw [if_neg]
    rintro ⟨h, -⟩
    exact h rfl
  · rw [chiI_of_ne_bot χ hI]
    by_cases hc : Units.mk0 _ (coe_ne_zero hI) ∈ coprimeToModulus K 𝔣
    · rw [dif_pos hc, ← Finset.sum_filter]
      have hc' : idealUnit I hI ∈ coprimeToModulus K 𝔣 := by rwa [idealUnit_eq]
      have heq : (⟨idealUnit I hI, hc'⟩ : ↥(coprimeToModulus K 𝔣)) = ⟨Units.mk0 _ (coe_ne_zero hI), hc⟩ :=
        Subtype.ext (idealUnit_eq I hI)
      have : Finset.univ.filter (fun C => IsClassOf C I) =
          {NarrowRayClassGroup.mk K 𝔣 ⟨Units.mk0 _ (coe_ne_zero hI), hc⟩} := by
        ext C
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨_, _, h⟩
          rw [← h, ← heq]
        · intro h
          exact ⟨hI, hc', by rw [heq, h]⟩
      rw [this, Finset.sum_singleton]
    · rw [dif_neg hc]
      refine Finset.sum_eq_zero fun C _ => ?_
      rw [if_neg]
      rintro ⟨_, hc', _⟩
      rw [idealUnit_eq] at hc'
      exact hc hc'

def rayZetaEquiv (C : NarrowRayClassGroup K 𝔣) (n : ℕ) :
    {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧
      ∃ hc : FractionalIdeal.mk0 K I ∈ coprimeToModulus K 𝔣,
        NarrowRayClassGroup.mk K 𝔣 ⟨FractionalIdeal.mk0 K I, hc⟩ = C} ≃
    {I : Ideal (𝓞 K) // I ∈ ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset.filter
      fun I => IsClassOf C I)} where
  toFun I := ⟨(I.1 : Ideal (𝓞 K)), by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    refine ⟨I.2.1, ?_⟩
    have hI : (I.1 : Ideal (𝓞 K)) ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact nonZeroDivisors.ne_zero I.1.2
    obtain ⟨hc, hC⟩ := I.2.2
    exact ⟨hI, hc, hC⟩⟩
  invFun I := ⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero (by
      have h := I.2
      rw [Finset.mem_filter] at h
      rw [Ideal.zero_eq_bot]
      exact h.2.1)⟩, by
    have h := I.2
    rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h
    obtain ⟨hn, hI, hc, hC⟩ := h
    exact ⟨hn, hc, hC⟩⟩
  left_inv I := by ext1; rfl
  right_inv I := by ext1; rfl

theorem rayZetaCoeff_eq_card (C : NarrowRayClassGroup K 𝔣) (n : ℕ) :
    M4aTorus.rayZetaCoeff K 𝔣 C n =
      (((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset.filter fun I => IsClassOf C I)).card := by
  rw [M4aTorus.rayZetaCoeff, Nat.card_congr (rayZetaEquiv C n), Nat.card_eq_finsetCard]

theorem sum_mul_rayZetaCoeff_eq [Fintype (NarrowRayClassGroup K 𝔣)] (n : ℕ) :
    ∑ C : NarrowRayClassGroup K 𝔣, χ C * (M4aTorus.rayZetaCoeff K 𝔣 C n : ℂ) =
      ∑ I ∈ (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset, chiI χ I := by
  simp_rw [← classSum_eq_chiI]
  unfold classSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rw [rayZetaCoeff_eq_card, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

variable (K 𝔣) in

def coeff (n : ℕ) : ℂ := ∑ I ∈ (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset, chiI χ I

theorem rayZetaCoeff_le (C : NarrowRayClassGroup K 𝔣) (n : ℕ) :
    M4aTorus.rayZetaCoeff K 𝔣 C n ≤ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
  haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).to_subtype
  refine Nat.card_le_card_of_injective
    (fun I => (⟨(I.1 : Ideal (𝓞 K)), I.2.1⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n})) ?_
  intro I J h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext (Subtype.ext h)

theorem summable_rayZetaCoeff (C : NarrowRayClassGroup K 𝔣) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (M4aTorus.rayZetaCoeff K 𝔣 C n : ℂ)) s := by
  have h := summable_card_absNorm (F := K) hs
  rw [LSeriesSummable, ← summable_norm_iff] at h ⊢
  refine h.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  refine LSeries.norm_term_le s ?_
  simp only [Complex.norm_natCast, Nat.cast_le]
  exact rayZetaCoeff_le C n

theorem rayClassLSeries_eq_LSeries (h𝔣 : 𝔣 ≠ ⊥) {s : ℂ} (hs : 1 < s.re) :
    M4aTorus.rayClassLSeries K 𝔣 χ s = LSeries (coeff K 𝔣 χ) s := by
  haveI : Finite (NarrowRayClassGroup K 𝔣) := Deep.NTSupply.finite K h𝔣
  haveI : Fintype (NarrowRayClassGroup K 𝔣) := Fintype.ofFinite _
  rw [M4aTorus.rayClassLSeries, tsum_fintype]
  have hsum : ∀ C ∈ (Finset.univ : Finset (NarrowRayClassGroup K 𝔣)),
      LSeriesSummable (χ C • fun n ↦ (M4aTorus.rayZetaCoeff K 𝔣 C n : ℂ)) s :=
    fun C _ ↦ (summable_rayZetaCoeff C hs).smul _
  have h1 : ∀ C : NarrowRayClassGroup K 𝔣, χ C * M4aTorus.rayZeta K 𝔣 C s =
      LSeries (χ C • fun n ↦ (M4aTorus.rayZetaCoeff K 𝔣 C n : ℂ)) s := fun C ↦ by
    rw [M4aTorus.rayZeta, LSeries_smul]
  simp_rw [h1]
  rw [← LSeries_sum hsum]
  refine LSeries_congr (fun {n} _ ↦ ?_) s
  rw [Finset.sum_apply, coeff, ← sum_mul_rayZetaCoeff_eq]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rfl

theorem term_LSeries_eq (s : ℝ) (n : ℕ) :
    LSeries.term (coeff K 𝔣 χ) (s : ℂ) n =
      ∑ I ∈ (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset, term χ s I := by
  rw [LSeries.term_def]
  by_cases hn : n = 0
  · rw [if_pos hn]
    symm
    refine Finset.sum_eq_zero fun I hI => ?_
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hn, Ideal.absNorm_eq_zero_iff] at hI
    rw [hI, term_bot]
  · rw [if_neg hn, coeff, Finset.sum_div]
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hI
    rw [term, wt, hI, div_eq_mul_inv, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast,
      Complex.ofReal_neg, Complex.cpow_neg]

theorem rayClassLSeries_eq_tsum (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 < s) :
    M4aTorus.rayClassLSeries K 𝔣 χ s = ∑' I : Ideal (𝓞 K), term χ s I := by
  rw [rayClassLSeries_eq_LSeries χ h𝔣 (by simpa using hs), LSeries]
  have hfib := (summable_term χ h𝔣 hs).hasSum.tsum_fiberwise Ideal.absNorm
  rw [← hfib.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [term_LSeries_eq]
  have hfin : (Ideal.absNorm ⁻¹' {n} : Set (Ideal (𝓞 K))).Finite := Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n
  rw [← Finset.tsum_subtype]
  have hset : ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset : Set (Ideal (𝓞 K))) =
      Ideal.absNorm ⁻¹' {n} := by
    rw [Set.Finite.coe_toFinset]; rfl
  exact (tsum_congr_set_coe (term χ s) hset)

end Bridge

section Euler

open FrobeniusDensity (IsFactoredBy)

def Fac (T : Finset (HeightOneSpectrum (𝓞 K))) : Set (Ideal (𝓞 K)) := {I | IsFactoredBy T I}

theorem mem_Fac {T : Finset (HeightOneSpectrum (𝓞 K))} {I : Ideal (𝓞 K)} :
    I ∈ Fac T ↔ I ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I → v ∈ T := Iff.rfl

theorem top_mem_Fac (T : Finset (HeightOneSpectrum (𝓞 K))) : (⊤ : Ideal (𝓞 K)) ∈ Fac T := by
  refine ⟨by simp, fun v hv => ?_⟩
  exact absurd (Ideal.isUnit_iff.mp (isUnit_of_dvd_one (by rwa [Ideal.one_eq_top]))) v.isPrime.ne_top

theorem eq_top_of_mem_Fac_empty {I : Ideal (𝓞 K)} (hI : I ∈ Fac (∅ : Finset (HeightOneSpectrum (𝓞 K)))) :
    I = ⊤ := by
  by_contra htop
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I htop
  have hpbot : p ≠ ⊥ := by
    rintro rfl
    exact hI.1 (le_bot_iff.mp hIp)
  have := hI.2 ⟨p, hp.isPrime, hpbot⟩ (Ideal.dvd_iff_le.mpr hIp)
  simp at this

def consFactored (v : HeightOneSpectrum (𝓞 K)) {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T)
    (p : ℕ × Fac T) : Fac (T.cons v hv) := by
  refine ⟨v.asIdeal ^ p.1 * p.2.1, mul_ne_zero (pow_ne_zero _ v.ne_bot) p.2.2.1, fun w hw => ?_⟩
  rcases (Prime.dvd_mul w.prime).mp hw with hw | hw
  · have h1 : w.asIdeal ∣ v.asIdeal := w.prime.dvd_of_dvd_pow hw
    have h2 : w = v := HeightOneSpectrum.ext <|
      associated_iff_eq.mp ((Prime.dvd_prime_iff_associated w.prime v.prime).mp h1)
    simp [h2]
  · exact Finset.mem_cons_of_mem (p.2.2.2 w hw)

theorem consFactored_injective (v : HeightOneSpectrum (𝓞 K)) {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T) :
    Function.Injective (consFactored v hv) := by
  have hcount : ∀ (e : ℕ) (J : Fac T),
      Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (v.asIdeal ^ e * J.1)) = e := by
    intro e J
    rw [UniqueFactorizationMonoid.normalizedFactors_mul (pow_ne_zero _ v.ne_bot) J.2.1,
      UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible v.prime.irreducible, Multiset.count_add,
      Multiset.count_nsmul, normalize_eq, Multiset.count_singleton_self, mul_one,
      Multiset.count_eq_zero_of_notMem, add_zero]
    intro hmem
    exact hv (J.2.2 v ((UniqueFactorizationMonoid.mem_normalizedFactors_iff J.2.1).mp hmem).2)
  rintro ⟨e, J⟩ ⟨e', J'⟩ h
  have h' : v.asIdeal ^ e * J.1 = v.asIdeal ^ e' * J'.1 := congrArg Subtype.val h
  have he : e = e' := by rw [← hcount e J, ← hcount e' J', h']
  subst he
  exact Prod.ext rfl (Subtype.ext (mul_left_cancel₀ (pow_ne_zero _ v.ne_bot) h'))

theorem consFactored_surjective (v : HeightOneSpectrum (𝓞 K)) {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T) :
    Function.Surjective (consFactored v hv) := by
  rintro ⟨I, hI0, hIfac⟩
  have hfin : FiniteMultiplicity v.asIdeal I := .of_prime_left v.prime hI0
  obtain ⟨J, hJ, hvJ⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    exact hI0 (by simpa using hJ)
  refine ⟨⟨multiplicity v.asIdeal I, J, hJ0, fun w hw => ?_⟩, Subtype.ext hJ.symm⟩
  have hwI : w.asIdeal ∣ I := hw.trans ((dvd_mul_left J _).trans (dvd_of_eq hJ.symm))
  rcases Finset.mem_cons.mp (hIfac w hwI) with rfl | hmem
  · exact absurd hw hvJ
  · exact hmem

def consFactoredEquiv (v : HeightOneSpectrum (𝓞 K)) {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T) :
    ℕ × Fac T ≃ Fac (T.cons v hv) :=
  Equiv.ofBijective _ ⟨consFactored_injective v hv, consFactored_surjective v hv⟩

theorem norm_term_prime_lt_one (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    ‖term χ s v.asIdeal‖ < 1 :=
  lt_of_le_of_lt (norm_term_prime_le_half χ h𝔣 hs v) (by norm_num)

theorem summable_norm_pow (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    Summable fun k : ℕ => ‖term χ s v.asIdeal ^ k‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_pow_le _ k) ?_
  exact summable_geometric_of_lt_one (norm_nonneg _) (norm_term_prime_lt_one χ h𝔣 hs v)

theorem tsum_Fac_empty (s : ℝ) : ∑' I : Fac (∅ : Finset (HeightOneSpectrum (𝓞 K))), term χ s I = 1 := by
  have huniq : ∀ I : Fac (∅ : Finset (HeightOneSpectrum (𝓞 K))), I = ⟨⊤, top_mem_Fac ∅⟩ :=
    fun I => Subtype.ext (eq_top_of_mem_Fac_empty I.2)
  rw [tsum_eq_single (⟨⊤, top_mem_Fac ∅⟩ : Fac (∅ : Finset (HeightOneSpectrum (𝓞 K))))
    (fun b hb => absurd (huniq b) hb)]
  exact term_top χ s

theorem tsum_Fac_cons (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 < s) (v : HeightOneSpectrum (𝓞 K))
    {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T) :
    ∑' I : Fac (T.cons v hv), term χ s I = (∑' k : ℕ, term χ s v.asIdeal ^ k) * ∑' I : Fac T, term χ s I := by
  have hsumT : Summable fun I : Fac T => ‖term χ s (I : Ideal (𝓞 K))‖ :=
    (summable_norm_term χ h𝔣 hs).subtype _
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_pow χ h𝔣 hs.le v) hsumT,
    ← (consFactoredEquiv v hv).tsum_eq]
  refine tsum_congr fun p => ?_
  show term χ s (v.asIdeal ^ p.1 * p.2.1) = _
  rw [term_mul χ s (pow_ne_zero _ v.ne_bot) p.2.2.1, term_pow χ s v.ne_bot]

theorem tsum_Fac_eq_prod (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 < s) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑' I : Fac T, term χ s I = ∏ v ∈ T, ∑' k : ℕ, term χ s v.asIdeal ^ k := by
  induction T using Finset.cons_induction_on with
  | empty => rw [Finset.prod_empty]; exact tsum_Fac_empty χ s
  | cons v T hv ih => rw [tsum_Fac_cons χ h𝔣 hs v hv, ih, Finset.prod_cons]

def lam (s : ℝ) (v : HeightOneSpectrum (𝓞 K)) : ℂ := -Complex.log (1 - term χ s v.asIdeal)

theorem one_sub_term_ne_zero (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    1 - term χ s v.asIdeal ≠ 0 := by
  intro h
  have := norm_term_prime_lt_one χ h𝔣 hs v
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at this
  exact lt_irrefl _ this

theorem exp_lam (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    Complex.exp (lam χ s v) = ∑' k : ℕ, term χ s v.asIdeal ^ k := by
  rw [lam, Complex.exp_neg, Complex.exp_log (one_sub_term_ne_zero χ h𝔣 hs v),
    (hasSum_geometric_of_norm_lt_one (norm_term_prime_lt_one χ h𝔣 hs v)).tsum_eq]

theorem exp_sum_lam (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 < s) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    Complex.exp (∑ v ∈ T, lam χ s v) = ∑' I : Fac T, term χ s I := by
  rw [Complex.exp_sum, tsum_Fac_eq_prod χ h𝔣 hs T]
  exact Finset.prod_congr rfl fun v _ => exp_lam χ h𝔣 hs.le v

theorem norm_lam_le (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 K)) :
    ‖lam χ s v‖ ≤ 3 / 2 * ‖term χ s v.asIdeal‖ := by
  rw [lam, norm_neg, sub_eq_add_neg]
  have h := Complex.norm_log_one_add_half_le_self (z := -term χ s v.asIdeal)
    (by rw [norm_neg]; exact norm_term_prime_le_half χ h𝔣 hs v)
  rwa [norm_neg] at h

theorem summable_lam (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 < s) : Summable (lam χ s) := by
  refine Summable.of_norm_bounded (g := fun v => 3 / 2 * pw K s v) ((summable_pw hs).mul_left _) fun v => ?_
  refine (norm_lam_le χ h𝔣 hs.le v).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_term_le χ h𝔣 s _) (by norm_num)

def Lam (s : ℝ) : ℂ := ∑' v, lam χ s v

theorem finite_absNorm_le (N : ℕ) : {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal ≤ N}.Finite := by
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) {v | Ideal.absNorm v.asIdeal ≤ N} :=
    fun _ _ _ _ h => HeightOneSpectrum.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine (Set.Finite.biUnion (Set.finite_Iic N) fun n _ => Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset ?_
  rintro _ ⟨v, hv, rfl⟩
  simp only [Set.mem_setOf_eq] at hv
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_Iic]
  exact ⟨_, hv, rfl⟩

theorem finite_ideal_absNorm_le (N : ℕ) : {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ N}.Finite := by
  refine (Set.Finite.biUnion (Set.finite_Iic N) fun n _ => Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset ?_
  intro I hI
  simp only [Set.mem_setOf_eq] at hI
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_Iic]
  exact ⟨_, hI, rfl⟩

def TN (N : ℕ) : Finset (HeightOneSpectrum (𝓞 K)) := (finite_absNorm_le (K := K) N).toFinset

def SN (N : ℕ) : Finset (Ideal (𝓞 K)) := (finite_ideal_absNorm_le (K := K) N).toFinset

theorem tendsto_TN : Tendsto (TN (K := K)) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun M N h v hv => ?_) (fun v => ⟨Ideal.absNorm v.asIdeal, ?_⟩)
  · rw [TN, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv ⊢
    exact hv.trans h
  · rw [TN, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem tendsto_SN : Tendsto (SN (K := K)) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun M N h I hI => ?_) (fun I => ⟨Ideal.absNorm I, ?_⟩)
  · rw [SN, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hI ⊢
    exact hI.trans h
  · rw [SN, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem not_mem_SN_of_not_mem_Fac {N : ℕ} {I : Ideal (𝓞 K)} (hI : I ∉ Fac (TN N)) (hI0 : I ≠ ⊥) :
    I ∉ (SN (K := K) N : Set (Ideal (𝓞 K))) := by
  intro hIS
  apply hI
  refine ⟨hI0, fun v hv => ?_⟩
  rw [TN, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  rw [Finset.mem_coe, SN, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hIS
  refine le_trans ?_ hIS
  refine Nat.le_of_dvd (Nat.pos_of_ne_zero ?_) (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hv))
  rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI0

theorem tendsto_exp_sum_lam (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 < s) :
    Tendsto (fun N => Complex.exp (∑ v ∈ TN N, lam χ s v)) atTop (𝓝 (Complex.exp (Lam χ s))) := by
  have h : HasSum (lam χ s) (Lam χ s) := (summable_lam χ h𝔣 hs).hasSum
  have h' : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) => ∑ v ∈ T, lam χ s v) atTop (𝓝 (Lam χ s)) := h
  exact (h'.comp tendsto_TN).cexp

theorem wt_bot {s : ℝ} (hs : 0 < s) : wt (K := K) s ⊥ = 0 := by
  rw [wt, Ideal.absNorm_bot, Nat.cast_zero, Real.zero_rpow (by linarith)]

theorem tendsto_tsum_Fac (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 < s) :
    Tendsto (fun N => ∑' I : Fac (TN (K := K) N), term χ s I) atTop (𝓝 (∑' I, term χ s I)) := by
  have hst := summable_term χ h𝔣 hs
  have hwt := summable_wt (K := K) hs

  have htail : Tendsto (fun N => ∑' I : {I : Ideal (𝓞 K) // I ∉ SN N}, wt s (I : Ideal (𝓞 K))) atTop (𝓝 0) :=
    (tendsto_tsum_compl_atTop_zero (wt (K := K) s)).comp tendsto_SN
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) htail

  have hsplit := Summable.tsum_add_tsum_compl (s := Fac (TN N)) (f := term χ s) (hst.subtype _) (hst.subtype _)
  have heq : (∑' I : Fac (TN (K := K) N), term χ s I) - ∑' I, term χ s I =
      -∑' I : ↥(Fac (TN (K := K) N))ᶜ, term χ s (I : Ideal (𝓞 K)) := by
    rw [← hsplit]; ring
  rw [heq, norm_neg]
  have h1 : ‖∑' I : ↥(Fac (TN (K := K) N))ᶜ, term χ s (I : Ideal (𝓞 K))‖ ≤
      ∑' I : ↥(Fac (TN (K := K) N))ᶜ, wt s (I : Ideal (𝓞 K)) :=
    tsum_of_norm_bounded ((hwt.subtype _).hasSum) fun I => norm_term_le χ h𝔣 s _
  refine h1.trans ?_
  set B : Set (Ideal (𝓞 K)) := {I | I ∉ SN (K := K) N} with hB
  have hR : (∑' I : {I // I ∉ SN (K := K) N}, wt s (I : Ideal (𝓞 K))) = ∑' I, B.indicator (wt s) I := by
    exact tsum_subtype B (wt s)
  rw [tsum_subtype ((Fac (TN N))ᶜ) (wt s), hR]
  refine Summable.tsum_le_tsum (fun I => ?_) (hwt.indicator _) (hwt.indicator _)
  by_cases hI0 : I = ⊥
  · rw [hI0]
    simp only [Set.indicator, wt_bot (by linarith : (0:ℝ) < s)]
    split_ifs <;> exact le_rfl
  · by_cases hI : I ∈ (Fac (TN N))ᶜ
    · rw [Set.indicator_of_mem hI, Set.indicator_of_mem]
      rw [hB, Set.mem_setOf_eq]
      have := not_mem_SN_of_not_mem_Fac hI hI0
      rwa [Finset.mem_coe] at this
    · rw [Set.indicator_of_notMem hI]
      exact Set.indicator_nonneg (fun _ _ => wt_nonneg s _) _

theorem exp_Lam (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 < s) :
    Complex.exp (Lam χ s) = M4aTorus.rayClassLSeries K 𝔣 χ s := by
  rw [rayClassLSeries_eq_tsum χ h𝔣 hs]
  refine tendsto_nhds_unique ?_ (tendsto_tsum_Fac χ h𝔣 hs)
  have := tendsto_exp_sum_lam χ h𝔣 hs
  refine this.congr fun N => ?_
  exact exp_sum_lam χ h𝔣 hs (TN N)

end Euler

section Cont

theorem continuous_pw (v : HeightOneSpectrum (𝓞 K)) : Continuous fun s : ℝ => pw K s v := by
  unfold pw
  exact (Real.continuous_const_rpow (by have := one_lt_absNorm_real v; positivity)).comp continuous_neg

theorem continuousOn_lam (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    ContinuousOn (fun s : ℝ => lam χ s v) (Set.Ici 1) := by
  have hterm : Continuous fun s : ℝ => term χ s v.asIdeal := by
    unfold term
    refine continuous_const.mul ?_
    rw [show (fun s : ℝ => ((wt s v.asIdeal : ℝ) : ℂ)) = fun s => ((pw K s v : ℝ) : ℂ) from rfl]
    exact Complex.continuous_ofReal.comp (continuous_pw v)
  intro s hs
  have h1 : ContinuousAt (fun s : ℝ => 1 - term χ s v.asIdeal) s := (continuous_const.sub hterm).continuousAt
  have hmem : (1 - term χ s v.asIdeal) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have h2 : (term χ s v.asIdeal).re ≤ 1 / 2 :=
      (Complex.re_le_norm _).trans (norm_term_prime_le_half χ h𝔣 hs v)
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have h3 : ContinuousAt (fun s : ℝ => Complex.log (1 - term χ s v.asIdeal)) s :=
    ContinuousAt.comp (f := fun s : ℝ => 1 - term χ s v.asIdeal) (continuousAt_clog hmem) h1
  exact h3.neg.continuousWithinAt

theorem continuousOn_Lam_Ici (h𝔣 : 𝔣 ≠ ⊥) {s₀ : ℝ} (hs₀ : 1 < s₀) : ContinuousOn (Lam χ) (Set.Ici s₀) := by
  unfold Lam
  refine continuousOn_tsum (u := fun v => 3 / 2 * pw K s₀ v) (fun v => (continuousOn_lam χ h𝔣 v).mono
    (fun s hs => le_trans hs₀.le hs)) ((summable_pw hs₀).mul_left _) fun v s hs => ?_
  have hs1 : 1 ≤ s := le_trans hs₀.le hs
  refine (norm_lam_le χ h𝔣 hs1 v).trans ?_
  refine mul_le_mul_of_nonneg_left ((norm_term_le χ h𝔣 s _).trans ?_) (by norm_num)
  rw [wt_prime]
  exact pw_antitone hs v

theorem continuousOn_Lam (h𝔣 : 𝔣 ≠ ⊥) : ContinuousOn (Lam χ) (Set.Ioi 1) := by
  intro s hs
  rw [Set.mem_Ioi] at hs
  have h := continuousOn_Lam_Ici χ h𝔣 (s₀ := (1 + s) / 2) (by linarith)
  have hat : ContinuousAt (Lam χ) s := h.continuousAt (Ici_mem_nhds (by linarith))
  exact hat.continuousWithinAt

theorem norm_Lam_sub_le (h𝔣 : 𝔣 ≠ ⊥) {s : ℝ} (hs : 1 < s) :
    ‖Lam χ s - ∑' v : HeightOneSpectrum (𝓞 K), term χ s v.asIdeal‖ ≤ ∑' v, pw K 2 v := by
  have hsl := summable_lam χ h𝔣 hs
  have hsterm : Summable fun v : HeightOneSpectrum (𝓞 K) => term χ s v.asIdeal :=
    Summable.of_norm_bounded (summable_pw hs) fun v => norm_term_le χ h𝔣 s _
  rw [Lam, ← hsl.tsum_sub hsterm]
  refine tsum_of_norm_bounded (summable_pw (by norm_num : (1:ℝ) < 2)).hasSum fun v => ?_
  have hz : ‖-term χ s v.asIdeal‖ ≤ 1 / 2 := by rw [norm_neg]; exact norm_term_prime_le_half χ h𝔣 hs.le v
  have h1 : lam χ s v - term χ s v.asIdeal = -(Complex.log (1 + -term χ s v.asIdeal) - -term χ s v.asIdeal) := by
    rw [lam, ← sub_eq_add_neg]; ring
  rw [h1, norm_neg]
  have h2 := Complex.norm_log_one_add_sub_self_le (z := -term χ s v.asIdeal) (by linarith)
  refine h2.trans ?_
  have hn : ‖-term χ s v.asIdeal‖ ≤ pw K s v := by rw [norm_neg]; exact norm_term_le χ h𝔣 s _
  have hn0 : 0 ≤ ‖-term χ s v.asIdeal‖ := norm_nonneg _
  have hinv : (1 - ‖-term χ s v.asIdeal‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc ‖-term χ s v.asIdeal‖ ^ 2 * (1 - ‖-term χ s v.asIdeal‖)⁻¹ / 2
      ≤ ‖-term χ s v.asIdeal‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖-term χ s v.asIdeal‖ ^ 2 := by ring
    _ ≤ pw K s v ^ 2 := by gcongr
    _ ≤ pw K 1 v ^ 2 := by gcongr; exacts [pw_nonneg s v, pw_antitone hs.le v]
    _ = pw K 2 v := by
        rw [pw, pw, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num

theorem term_prime_eq (s : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)) =
      term χ s v.asIdeal := by
  rw [term, chiI, wt, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, Complex.ofReal_neg]

end Cont

theorem main (h𝔣 : 𝔣 ≠ ⊥) :
    ∃ Λ : ℝ → ℂ, ContinuousOn Λ (Set.Ioi 1) ∧
      (∀ s : ℝ, 1 < s → Complex.exp (Λ s) = M4aTorus.rayClassLSeries K 𝔣 χ s) ∧
      (∀ s : ℝ, 1 < s → Summable fun v : HeightOneSpectrum (𝓞 K) =>
          M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) ∧
      ∃ C : ℝ, ∀ s : ℝ, 1 < s →
        ‖Λ s - ∑' v : HeightOneSpectrum (𝓞 K),
            M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))‖ ≤ C := by
  refine ⟨Lam χ, continuousOn_Lam χ h𝔣, fun s hs => exp_Lam χ h𝔣 hs, fun s hs => ?_, ∑' v, pw K 2 v, fun s hs => ?_⟩
  · simp_rw [term_prime_eq]
    exact Summable.of_norm_bounded (summable_pw hs) fun v => norm_term_le χ h𝔣 s _
  · simp_rw [term_prime_eq]
    exact norm_Lam_sub_le χ h𝔣 hs

end P2mRayEuler

end

open NumberField IsDedekindDomain Deep.NTSupply in
open scoped nonZeroDivisors in
theorem solution
    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) :
    ∃ Λ : ℝ → ℂ, ContinuousOn Λ (Set.Ioi 1) ∧
      (∀ s : ℝ, 1 < s → Complex.exp (Λ s) = M4aTorus.rayClassLSeries K 𝔣 χ s) ∧
      (∀ s : ℝ, 1 < s → Summable fun v : HeightOneSpectrum (𝓞 K) =>
          M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) ∧
      ∃ C : ℝ, ∀ s : ℝ, 1 < s →
        ‖Λ s - ∑' v : HeightOneSpectrum (𝓞 K),
            M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))‖ ≤ C :=
  P2mRayEuler.main χ h𝔣

end S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries
end P2MW
export P2MW.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (solution)
