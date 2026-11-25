-- Prove2me | solution 1 for GlobalTheory.GramCount.count_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:10.842482+00:00
-- url     : https://prove2.me/submissions/48fa0094-04f9-42c9-ae3f-2d7ab22e2738

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesWithGramMatrixHenselCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesGramModNilpotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesWithGramMatrixResidueRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizer
import Theorems.Thm_GlobalTheory_GramCount_quotInv_mk
import Theorems.Thm_GlobalTheory_GramCount_quotInv_quotInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_GramCount_Prim_map
import Theorems.Thm_GlobalTheory_GramCount_exists_trace_one
import Theorems.Thm_GlobalTheory_T_card_hermitian_matrices_dvd_sq
import Theorems.Thm_GlobalTheory_T_ncard_primitiveTuplesWithGramMatrix_residueRing
import Theorems.Thm_GlobalTheory_T_ncard_primitive_tuples_gram_mod_nilpotent
import Theorems.Thm_GlobalTheory_T_primitiveTuplesWithGramMatrix_hensel_count
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.GramCount
section Abstract
variable {O : Type} [CommRing O]
private lemma quotient_mk_dvd_mk_iff_dvd (p : O) (j : ℕ) (hj : 1 ≤ j) (u : O) :
    Ideal.Quotient.mk (Ideal.span {p ^ j}) p ∣ Ideal.Quotient.mk (Ideal.span {p ^ j}) u ↔
      p ∣ u := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hv
    obtain ⟨k, hk⟩ := hv
    have hpj : p ^ j = p * p ^ (j - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    exact ⟨w + p ^ (j - 1) * k, by linear_combination hk + k * hpj⟩
  · rintro ⟨w, rfl⟩
    exact ⟨Ideal.Quotient.mk _ w, map_mul _ _ _⟩
end Abstract
end GlobalTheory.GramCount
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.GramCount
variable {O : Type} [CommRing O]
namespace GlobalTheory.GramCount
theorem _root_.solution (c : O →+* O) (hc : ∀ u, c (c u) = u) (ω : O) (hω : IsUnit (ω - c ω))
    (p : O) (hp : c p = p) (hK : ∀ t, c t = t → ¬ p ∣ t → IsUnit t) (q : ℕ) (hq : 2 ≤ q)
    (j : ℕ) (hj : 1 ≤ j) (h1 : Nat.card (O ⧸ Ideal.span {p}) = q ^ 2)
    (h2 : Nat.card (O ⧸ Ideal.span {p ^ j}) = q ^ (2 * j)) (hpj : c (p ^ j) = p ^ j)
    (m n : ℕ) (hmn : 2 * m + 3 ≤ n) (G : Matrix (Fin m) (Fin m) O)
    (hG : ∀ a b, c (G b a) = G a b) (N : ℕ)
    (hN : N = Set.ncard (sols (quotInv c (p ^ j) hpj) n (G.map (Ideal.Quotient.mk _)))) :
    (q : ℝ) ^ (j * (2 * n * m - m ^ 2)) ≤ 2 * N ∧
      (N : ℝ) ≤ 2 * (q : ℝ) ^ (j * (2 * n * m - m ^ 2)) := by
  classical
  have hq0 : 0 < q := by omega

  have hfinA : Finite (O ⧸ Ideal.span {p ^ j}) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; exact pow_ne_zero _ hq0.ne')
  have hfinB : Finite (O ⧸ Ideal.span {p}) :=
    Nat.finite_of_card_ne_zero (by rw [h1]; exact pow_ne_zero _ hq0.ne')
  let _ : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _

  have hle : Ideal.span {p ^ j} ≤ (Ideal.span {p}).comap (RingHom.id O) := by
    rw [Ideal.comap_id, Ideal.span_singleton_le_span_singleton]
    exact dvd_pow_self p (by omega)
  set φ := Ideal.quotientMap (Ideal.span {p}) (RingHom.id O) hle with hφdef
  have hφmk : ∀ u, φ (Ideal.Quotient.mk _ u) = Ideal.Quotient.mk _ u := fun u =>
    Ideal.quotientMap_mk
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨_, hφmk u⟩
  set cA := quotInv c (p ^ j) hpj with hcAdef
  set cB := quotInv c p hp with hcBdef
  have hφc : ∀ u, φ (cA u) = cB (φ u) := by
    intro u
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
    rw [hcAdef, hcBdef, quotInv_mk, hφmk, hφmk, quotInv_mk]
  set pA : O ⧸ Ideal.span {p ^ j} := Ideal.Quotient.mk _ p with hpAdef
  have hker : ∀ u, φ u = 0 ↔ pA ∣ u := by
    intro u
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
    rw [hφmk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hpAdef,
      quotient_mk_dvd_mk_iff_dvd p j hj v]
  have hnil : IsNilpotent pA :=
    ⟨j, by rw [hpAdef, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
           exact Ideal.mem_span_singleton_self _⟩
  have hcA : ∀ u, cA (cA u) = u := quotInv_quotInv c hc _ hpj
  have hcB : ∀ u, cB (cB u) = u := quotInv_quotInv c hc _ hp
  have hωA : IsUnit (Ideal.Quotient.mk (Ideal.span {p ^ j}) ω - cA (Ideal.Quotient.mk _ ω)) := by
    rw [hcAdef, quotInv_mk, ← map_sub]
    exact hω.map _
  have hωB : IsUnit (Ideal.Quotient.mk (Ideal.span {p}) ω - cB (Ideal.Quotient.mk _ ω)) := by
    rw [hcBdef, quotInv_mk, ← map_sub]
    exact hω.map _
  have hpA : cA pA = pA := by rw [hcAdef, hpAdef, quotInv_mk, hp]
  set GA := G.map (Ideal.Quotient.mk (Ideal.span {p ^ j})) with hGAdef
  have hGA : ∀ a b, cA (GA b a) = GA a b := by
    intro a b
    simp only [hGAdef, Matrix.map_apply]
    rw [hcAdef, quotInv_mk, hG]
  have hGB : ∀ a b, cB ((GA.map φ) b a) = (GA.map φ) a b := by
    intro a b
    simp only [Matrix.map_apply]
    rw [← hφc, hGA]

  have hKB : ∀ t, cB t = t → t ≠ 0 → IsUnit t := by
    intro t ht ht0
    obtain ⟨θ, -, hθ, -, -⟩ := exists_trace_one c hc hω
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective t
    have h' : Ideal.Quotient.mk (Ideal.span {p}) (c u) = Ideal.Quotient.mk _ u := by
      rw [hcBdef, quotInv_mk] at ht
      exact ht
    have hv : c (θ * u + c (θ * u)) = θ * u + c (θ * u) := by
      rw [map_add, hc, add_comm]
    have hmk : Ideal.Quotient.mk (Ideal.span {p}) (θ * u + c (θ * u)) =
        Ideal.Quotient.mk _ u := by
      rw [map_mul c, map_add, map_mul, map_mul, h', ← add_mul, ← map_add, hθ, map_one, one_mul]
    have hnd : ¬ p ∣ θ * u + c (θ * u) := by
      intro hd
      apply ht0
      rw [← hmk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact hd
    rw [← hmk]
    exact (hK _ hv hnd).map _
  have hcardB : Fintype.card (O ⧸ Ideal.span {p}) = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact h1

  have h29 := GlobalTheory.T.primitiveTuplesWithGramMatrix_hensel_count cA hcA _ hωA pA hpA hnil m n GA hGA
  have h31 := GlobalTheory.T.ncard_primitive_tuples_gram_mod_nilpotent cA cB hcA pA hnil φ hsurj hφc hker m n GA
  have h33 := GlobalTheory.T.card_hermitian_matrices_dvd_sq cA hcA _ hωA pA hpA m
  have h62 := GlobalTheory.T.ncard_primitiveTuplesWithGramMatrix_residueRing cB hcB _ hωB hKB q hq hcardB m n hmn (GA.map φ) hGB

  have hD : Nat.card {u : O ⧸ Ideal.span {p ^ j} // pA ∣ u} = q ^ (2 * (j - 1)) := by
    have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (φ : (O ⧸ Ideal.span {p ^ j}) →+ (O ⧸ Ideal.span {p})).ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
      (φ : (O ⧸ Ideal.span {p ^ j}) →+ (O ⧸ Ideal.span {p})) hsurj).toEquiv, h1, h2] at hcard
    have hsub : Nat.card ((φ : (O ⧸ Ideal.span {p ^ j}) →+ (O ⧸ Ideal.span {p})).ker) =
        Nat.card {u : O ⧸ Ideal.span {p ^ j} // pA ∣ u} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun u => by
        rw [AddMonoidHom.mem_ker]
        exact hker u)
    rw [hsub] at hcard
    have h2j : q ^ (2 * j) = q ^ 2 * q ^ (2 * (j - 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h2j] at hcard
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos hq0 2) hcard).symm
  rw [hD] at h31 h33

  have hH : Nat.card {H : Matrix (Fin m) (Fin m) (O ⧸ Ideal.span {p ^ j}) //
      (∀ a b, cA (H b a) = H a b) ∧ ∀ a b, pA ∣ H a b} = q ^ ((j - 1) * (m * m)) := by
    apply Nat.pow_left_injective (n := 2) (by norm_num)
    simp only
    rw [h33, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hH, h31] at h29
  have hle2 : m * m ≤ 2 * n * m := by nlinarith
  have hK2 : 2 * n * m - m ^ 2 + m * m = 2 * n * m := by
    rw [sq]
    exact Nat.sub_add_cancel hle2
  have hexp : 2 * (j - 1) * (n * m) =
      (j - 1) * (2 * n * m - m ^ 2) + (j - 1) * (m * m) := by
    rw [← Nat.mul_add, hK2]
    ring
  rw [← pow_mul, hexp, pow_add] at h29
  have hS : Set.ncard (sols cA n GA) =
      q ^ ((j - 1) * (2 * n * m - m ^ 2)) * Set.ncard (sols cB n (GA.map φ)) := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hq0 ((j - 1) * (m * m)))
    rw [h29]
    ring
  have hjK : j * (2 * n * m - m ^ 2) = (j - 1) * (2 * n * m - m ^ 2) + (2 * n * m - m ^ 2) := by
    conv_lhs => rw [← Nat.sub_add_cancel hj]
    ring
  rw [hN, hS, hjK]
  push_cast
  rw [pow_add]
  have hX : (0 : ℝ) ≤ (q : ℝ) ^ ((j - 1) * (2 * n * m - m ^ 2)) := by positivity
  obtain ⟨hlo, hhi⟩ := h62
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo hX]
  · nlinarith [mul_le_mul_of_nonneg_left hhi hX]
end GlobalTheory.GramCount
