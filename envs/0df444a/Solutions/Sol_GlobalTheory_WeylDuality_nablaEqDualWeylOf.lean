-- Prove2me | solution 1 for GlobalTheory.WeylDuality.nablaEqDualWeylOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:28:12.160851+00:00
-- url     : https://prove2.me/submissions/ba3a1795-453d-408e-9b60-768235e24689

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
import Theorems.Thm_GlobalTheory_WeylDuality_intQ_apply
import Theorems.Thm_GlobalTheory_WeylDuality_applyWord_mem_dualWeyl
import Theorems.Thm_GlobalTheory_WeylDuality_intQ_word
import Theorems.Thm_GlobalTheory_WeylDuality_eval_idFrame_int
import Theorems.Thm_GlobalTheory_WeylDuality_fockQ_hw_pos
import Theorems.Thm_GlobalTheory_WeylDuality_fockB_apply
import Theorems.Thm_GlobalTheory_WeylDuality_mem_bDual
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylIntRat
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace GlobalTheory.WeylDuality
private theorem rowGen_map_intCast {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    Polynomial.map (MvPolynomial.map φ) (rowGen R a b f) = rowGen S a b (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [rowGen]
  | add p q hp hq => rw [map_add, map_add, Polynomial.map_add, hp, hq, map_add]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.map_mul, hp, map_mul, map_mul, map_X]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp
private theorem rowDiv_map_intCast {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (rowDiv R a b k f) = rowDiv S a b k (map φ f) := by
  unfold rowDiv
  rw [← rowGen_map_intCast, Polynomial.coeff_map]
private theorem map_intCast_applyWord {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) ℤ) :
    map (Int.castRingHom ℚ) (applyWord ℤ w f) = applyWord ℚ w (map (Int.castRingHom ℚ) f) := by
  induction w with
  | nil => simp [applyWord]
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    rw [rowDiv_map_intCast, ih]
private theorem fockQ_zero_right {σ : Type} (f : MvPolynomial σ ℚ) : fockQ f 0 = 0 := by
  rw [← fockB_apply, map_zero]
private theorem fockQ_add_right {σ : Type} (f g g' : MvPolynomial σ ℚ) :
    fockQ f (g + g') = fockQ f g + fockQ f g' := by
  rw [← fockB_apply, map_add, fockB_apply, fockB_apply]
private theorem fockQ_smul_right' {σ : Type} (f g : MvPolynomial σ ℚ) (c : ℚ) :
    fockQ f (c • g) = c * fockQ f g := by
  rw [← fockB_apply, map_smul, fockB_apply, smul_eq_mul]
private theorem weight_colW_apply' {r n : ℕ} (e : Fin r × Fin n →₀ ℕ) (s : Fin n) :
    Finsupp.weight (colW r n) e s = ∑ a : Fin r, e (a, s) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [colW, Pi.single_apply]
end GlobalTheory.WeylDuality
end
end

set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution : NablaEqDualWeylOf := by
  intro hCW hHW hAdj hLT r n hn ν hν
  have hc := fockQ_hw_pos hn ν
  ext P
  rw [mem_bDual]
  constructor
  · rintro ⟨F, hF, rfl⟩
    have hFQ : intQ r n F ∈ dualWeyl ℚ r n ν := by
      rw [intQ_apply]
      exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν F hF
    refine ⟨hFQ, ?_⟩
    rintro Q ⟨G, hG, rfl⟩
    unfold weyl at hG
    induction hG using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      refine ⟨eval (idFrame ℤ r n) (applyWord ℤ (transposeWord w) F), ?_⟩
      rw [intQ_word hn ν w, fockQ_symm (intQ r n F), hAdj,
        hHW r n hn ν hν _ (applyWord_mem_dualWeyl ℚ ν _ hFQ), intQ_apply, ← map_intCast_applyWord,
        eval_idFrame_int]
    | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, fockQ_zero_right]
      simp
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      rw [map_add, fockQ_add_right, ha, hb]
      push_cast
      ring
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨c * a, ?_⟩
      have hcx : intQ r n (c • x) = (c : ℚ) • intQ r n x := by
        rw [map_zsmul]
        exact (Int.cast_smul_eq_zsmul ℚ c _).symm
      rw [hcx, fockQ_smul_right', ha]
      push_cast
      ring
  · rintro ⟨hP, hPQ⟩
    have hhom : IsWeightedHomogeneous (colW r n) P ν := by
      unfold dualWeyl at hP
      exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hP).1
    have hint : ∀ w : List (Fin r × Fin r × ℕ),
        ∃ z : ℤ, fockQ (hw ℚ hn ν) (applyWord ℚ w P) = z * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := by
      intro w
      have hmem : applyWord ℚ (transposeWord w) (hw ℚ hn ν) ∈ (weyl ℤ r n hn ν).map (intQ r n) := by
        refine ⟨applyWord ℤ (transposeWord w) (hw ℤ hn ν), ?_, intQ_word hn ν _⟩
        unfold weyl
        exact Submodule.subset_span ⟨_, rfl⟩
      obtain ⟨z, hz⟩ := hPQ _ hmem
      exact ⟨z, by rw [fockQ_symm, hAdj, hz]⟩
    have hcoef : ∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e P = z := by
      intro e he
      by_cases hs : ∀ s : Fin n, ∑ a : Fin r, e (a, s) = ν s
      · obtain ⟨z, hz⟩ := hint (wordOf e)
        refine ⟨z, ?_⟩
        rw [hCW ℚ r n ν P e hhom he hs]
        rw [hHW r n hn ν hν _ (applyWord_mem_dualWeyl ℚ ν _ hP)] at hz
        exact mul_right_cancel₀ hc.ne' hz
      · refine ⟨0, ?_⟩
        by_contra hne
        apply hs
        intro s
        have hwt := hhom (d := e) (by simpa using hne)
        rw [← weight_colW_apply' e s, hwt]
    obtain ⟨Q', hQ'⟩ := hLT r n ν P hP hcoef
    refine ⟨Q', (dualWeylIntRat r n ν Q').mpr ?_, hQ'.symm⟩
    rw [← intQ_apply, ← hQ']
    exact hP
end GlobalTheory.WeylDuality
