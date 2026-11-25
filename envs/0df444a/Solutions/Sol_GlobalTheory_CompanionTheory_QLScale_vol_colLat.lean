-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLScale.vol_colLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:19:01.346217+00:00
-- url     : https://prove2.me/submissions/4a5c3975-223f-4d6e-8676-9017386da93d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinearStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslate
import Theorems.Thm_GlobalTheory_CompanionTheory_QLScale_pi_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_QLScale_res_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_QLScale_q_ne_zero
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_matrix_additive_haar_normalized
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk


section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
namespace GlobalTheory.CompanionTheory.QLScale
open scoped ENNReal
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
section Measure
variable [MeasurableSpace F] [BorelSpace F]
private theorem neg_inv_mul_add_mem_of_residue_eq (hLF : LF 𝒪[F] ϖ nrm q) (y : F) (hy : y * ϖ ∈ 𝒪[F]) (s : 𝒪[F])
    (hs : IsLocalRing.residue 𝒪[F] s = IsLocalRing.residue 𝒪[F] ⟨y * ϖ, hy⟩) :
    -(ϖ⁻¹ * (s : F)) + y ∈ 𝒪[F] := by
  obtain ⟨o, ho, heq⟩ := (res_zero hLF (⟨y * ϖ, hy⟩ - s)).1 (by rw [map_sub, hs, sub_self])
  have hne := hLF.ne
  have heq' : y * ϖ - (s : F) = ϖ * o := by simpa using heq
  have hval : -(ϖ⁻¹ * (s : F)) + y = o := by
    calc -(ϖ⁻¹ * (s : F)) + y = ϖ⁻¹ * (y * ϖ - s) := by
          rw [mul_sub, mul_comm y ϖ, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]; ring
      _ = ϖ⁻¹ * (ϖ * o) := by rw [heq']
      _ = o := by rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hval]
  exact ho
private theorem residue_eq_of_neg_inv_mul_add_mem (hLF : LF 𝒪[F] ϖ nrm q) (y : F) (s t : 𝒪[F])
    (hs : -(ϖ⁻¹ * (s : F)) + y ∈ 𝒪[F]) (ht : -(ϖ⁻¹ * (t : F)) + y ∈ 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] s = IsLocalRing.residue 𝒪[F] t := by
  have hw : ϖ⁻¹ * ((s : F) - t) ∈ 𝒪[F] := by
    have h := sub_mem ht hs
    convert h using 1
    ring
  have h0 : IsLocalRing.residue 𝒪[F] (s - t) = 0 :=
    (res_zero hLF (s - t)).2 ⟨_, hw, by push_cast; rw [← mul_assoc, mul_inv_cancel₀ hLF.ne, one_mul]⟩
  rwa [map_sub, sub_eq_zero] at h0
private theorem mul_mem_of_neg_inv_mul_add_mem (hLF : LF 𝒪[F] ϖ nrm q) (y : F) (s : 𝒪[F])
    (hs : -(ϖ⁻¹ * (s : F)) + y ∈ 𝒪[F]) : y * ϖ ∈ 𝒪[F] := by
  have hne := hLF.ne
  have h := add_mem (mul_mem hs (pi_mem hLF)) s.2
  convert h using 1
  field_simp <;> ring
end Measure
end GlobalTheory.CompanionTheory.QLScale
end
end

set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLScale
open scoped ENNReal
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
variable [MeasurableSpace F] [BorelSpace F]
namespace GlobalTheory.CompanionTheory.QLScale
theorem _root_.solution (hLF : LF O ϖ nrm q) {n m : ℕ} {dx : Measure (Matrix (Fin n) (Fin m) F)}
    (hinv : dx.IsAddLeftInvariant) (h1 : dx (intMat O n m) = 1) (j : Fin m) :
    dx (colLat O ϖ n j) = (q : ℝ≥0∞) ^ n := by
  obtain ⟨hB, hopen, -, -, -, -⟩ := GlobalTheory.T.matrix_additive_haar_normalized hLF n m
  haveI := hB
  haveI := hinv
  obtain rfl : O = 𝒪[F] := hLF.O_eq
  haveI : Finite 𝓀[F] := Nat.finite_of_card_ne_zero (by rw [← hLF.card]; exact q_ne_zero hLF)
  haveI : Fintype 𝓀[F] := Fintype.ofFinite _
  classical
  obtain ⟨s, hs⟩ : ∃ s : 𝓀[F] → 𝒪[F], ∀ r, IsLocalRing.residue 𝒪[F] (s r) = r :=
    ⟨_, Function.surjInv_eq IsLocalRing.residue_surjective⟩
  let E : (Fin n → 𝓀[F]) → Matrix (Fin n) (Fin m) F :=
    fun r i b => if b = j then ϖ⁻¹ * (s (r i) : F) else 0
  let T : (Fin n → 𝓀[F]) → Set (Matrix (Fin n) (Fin m) F) :=
    fun r => (fun x => -E r + x) ⁻¹' intMat 𝒪[F] n m
  have hmemT : ∀ r x, x ∈ T r ↔
      ∀ i b, -(if b = j then ϖ⁻¹ * (s (r i) : F) else 0) + x i b ∈ 𝒪[F] := fun _ _ => Iff.rfl
  have hT : ∀ r, dx (T r) = 1 := fun r => by
    show dx ((fun x => -E r + x) ⁻¹' intMat 𝒪[F] n m) = 1
    rw [measure_preimage_add, h1]
  have hTm : ∀ r, MeasurableSet (T r) := fun r =>
    (hopen.preimage (continuous_const.add continuous_id)).measurableSet
  have hcol : colLat 𝒪[F] ϖ n j = ⋃ r, T r := by
    ext x
    rw [Set.mem_iUnion]
    constructor
    · intro hx
      have hx' : ∀ i b, x i b * (if b = j then ϖ else 1) ∈ 𝒪[F] := hx
      have hxj : ∀ i, x i j * ϖ ∈ 𝒪[F] := fun i => by simpa using hx' i j
      refine ⟨fun i => IsLocalRing.residue 𝒪[F] ⟨x i j * ϖ, hxj i⟩, (hmemT _ x).2 fun i b => ?_⟩
      by_cases hb : b = j
      · rw [hb, if_pos rfl]
        exact neg_inv_mul_add_mem_of_residue_eq hLF (x i j) (hxj i) _ (hs _)
      · rw [if_neg hb, neg_zero, zero_add]
        simpa [hb] using hx' i b
    · rintro ⟨r, hr⟩
      have hr' := (hmemT r x).1 hr
      show ∀ i b, x i b * (if b = j then ϖ else 1) ∈ 𝒪[F]
      intro i b
      by_cases hb : b = j
      · rw [hb, if_pos rfl]
        have h3 := hr' i j
        rw [if_pos rfl] at h3
        exact mul_mem_of_neg_inv_mul_add_mem hLF (x i j) (s (r i)) h3
      · have h3 := hr' i b
        rw [if_neg hb, neg_zero, zero_add] at h3
        rw [if_neg hb, mul_one]
        exact h3
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro r r' hrr'
    refine Set.disjoint_left.2 fun x h h' => hrr' (funext fun i => ?_)
    have h1' := (hmemT r x).1 h i j
    have h2' := (hmemT r' x).1 h' i j
    rw [if_pos rfl] at h1' h2'
    rw [← hs (r i), ← hs (r' i)]
    exact residue_eq_of_neg_inv_mul_add_mem hLF (x i j) _ _ h1' h2'
  rw [hcol, measure_iUnion hdisj hTm]
  simp only [hT, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Nat.cast_pow, ← Nat.card_eq_fintype_card, ← hLF.card]
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, ← hLF.card, Nat.cast_pow]
end GlobalTheory.CompanionTheory.QLScale
