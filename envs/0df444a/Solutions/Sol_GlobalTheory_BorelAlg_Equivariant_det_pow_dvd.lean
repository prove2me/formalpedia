-- Prove2me | solution 1 for GlobalTheory.BorelAlg.Equivariant.det_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:35:09.383425+00:00
-- url     : https://prove2.me/submissions/6a811147-082e-414a-9b8f-f47418d88859

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Theorems.Thm_P2M_GlobalTheory_BorelAlg_minor_isRelPrime__ca4173270435
import Theorems.Thm_GlobalTheory_BorelAlg_inj_block
import Theorems.Thm_GlobalTheory_BorelAlg_gen_det_ne_zero
import Theorems.Thm_GlobalTheory_BorelAlg_Equivariant_numer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
variable {ι : Type} (m : ι → ℕ) (L : Type) [Field L]
variable [Fintype ι]
variable {m L} {S : Type} [CommRing S] [Algebra (MvPolynomial (Lt m) L) S]
  [IsLocalization.Away (∏ τ, (gen m L τ).det) S]
namespace GlobalTheory.BorelAlg
namespace Equivariant
theorem _root_.solution {a : ι × ℕ → ℕ} {f : S} (hf : Equivariant m L S a f)
    {P : MvPolynomial (Lt m) L} {N : ℕ}
    (hP : f * algebraMap _ S ((∏ τ, (gen m L τ).det) ^ N) = algebraMap _ S P) (τ₀ : ι) :
    (gen m L τ₀).det ^ N ∣ P := by
  classical
  by_cases h0 : m τ₀ = 0
  · haveI : IsEmpty (Fin (m τ₀)) := by rw [h0]; infer_instance
    rw [Matrix.det_isEmpty, one_pow]; exact one_dvd _
  let l : Fin (m τ₀) := ⟨m τ₀ - 1, by omega⟩
  have hl : ∀ i, i ≤ l := fun i => by
    have := i.2
    simp only [Fin.le_def, l]; omega
  obtain ⟨hM0, hrel⟩ := minor_isRelPrime' (R := L) _ (inj_block m τ₀) l hl
  change ((gen m L τ₀).updateRow l (Pi.single l 1)).det ≠ 0 at hM0
  change IsRelPrime ((gen m L τ₀).updateRow l (Pi.single l 1)).det (gen m L τ₀).det at hrel
  set B := (gen m L τ₀).updateRow l (Pi.single l 1) with hB
  let T := FractionRing (MvPolynomial (Lt m) L)
  let g : MvPolynomial (Lt m) L →+* T := algebraMap _ _
  have hg : Function.Injective g := IsFractionRing.injective _ _
  have hg0 : ∀ {q}, q ≠ 0 → g q ≠ 0 := fun hq h => hq (hg (h.trans (map_zero _).symm))
  let x₀ : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Lt m) L) :=
    Function.update (gen m L) τ₀ B
  have hx₀ : ∀ τ, (x₀ τ).det ≠ 0 := by
    intro τ
    by_cases h : τ = τ₀
    · subst h; simpa [x₀] using hM0
    · simpa [x₀, h] using gen_det_ne_zero m L τ
  let x := fun τ => g.mapMatrix (x₀ τ)
  let y := fun τ => g.mapMatrix (gen m L τ)
  have hxd : ∀ τ, (x τ).det = g (x₀ τ).det := fun τ => (RingHom.map_det _ _).symm
  have hyd : ∀ τ, (y τ).det = g (gen m L τ).det := fun τ => (RingHom.map_det _ _).symm
  have hx : ∀ τ, (x τ).det ≠ 0 := fun τ => hxd τ ▸ hg0 (hx₀ τ)
  have hy : ∀ τ, (y τ).det ≠ 0 := fun τ => hyd τ ▸ hg0 (gen_det_ne_zero m L τ)
  let b := fun τ => y τ * (x τ)⁻¹
  have hxy : ∀ τ, y τ = b τ * x τ := fun τ => by
    simp only [b]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hx τ).isUnit, Matrix.mul_one]
  have hrow : ∀ τ i, y τ i = x τ i → ∀ j, b τ i j = (1 : Matrix _ _ T) i j := by
    intro τ i h j
    rw [← Matrix.mul_nonsing_inv _ (hx τ).isUnit]
    simp only [b, Matrix.mul_apply, h]
  have hne : ∀ τ, τ ≠ τ₀ → y τ = x τ := fun τ h => by simp [x, y, x₀, h]
  have hl' : ∀ i, i ≠ l → y τ₀ i = x τ₀ i := fun i h => by
    ext j; simp [x, y, x₀, B, Matrix.updateRow_ne h]
  have hb : ∀ τ i j, i < j → b τ i j = 0 := by
    intro τ i j hij
    rw [hrow τ i, Matrix.one_apply_ne hij.ne]
    by_cases h : τ = τ₀
    · subst h; exact hl' i (hij.trans_le (hl j)).ne
    · rw [hne τ h]
  have hdetb : (b τ₀).det = b τ₀ l l := by
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hb τ₀ i j hij), Finset.prod_eq_single l]
    · intro i _ hi; rw [hrow _ _ (hl' i hi), Matrix.one_apply_eq]
    · simp
  have hc : (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) = b τ₀ l l ^ a (τ₀, (l : ℕ)) := by
    rw [Finset.prod_eq_single τ₀, Finset.prod_eq_single l]
    · intro i _ hi; rw [hrow _ _ (hl' i hi), Matrix.one_apply_eq, one_pow]
    · simp
    · intro τ _ h
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hrow τ i (by rw [hne τ h]), Matrix.one_apply_eq, one_pow]
    · simp
  have hs : (y τ₀).det = b τ₀ l l * (x τ₀).det := by
    rw [← hdetb, ← Matrix.det_mul, ← hxy]
  have key := hf.numer hP (g.comp C) x y b hx hy hb hxy
  have e1 : eval₂Hom (g.comp C) (fun p : Lt m => y p.1 p.2.1 p.2.2) = g := by
    ext <;> simp [y, gen]
  have e2 : eval₂Hom (g.comp C) (fun p : Lt m => x p.1 p.2.1 p.2.2) =
      g.comp (eval₂Hom C (fun p : Lt m => x₀ p.1 p.2.1 p.2.2)) := by
    ext <;> simp [x]
  have e3 : ∏ τ ∈ Finset.univ.erase τ₀, (y τ).det = ∏ τ ∈ Finset.univ.erase τ₀, (x τ).det :=
    Finset.prod_congr rfl fun τ hτ => by rw [hne τ (Finset.ne_of_mem_erase hτ)]
  have hO : ∏ τ ∈ Finset.univ.erase τ₀, (x τ).det ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => hx τ
  rw [e1, e2, hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ₀),
    ← Finset.mul_prod_erase _ (fun τ => (y τ).det) (Finset.mem_univ τ₀), e3, mul_pow, mul_pow,
    ← mul_assoc, ← mul_assoc] at key
  have key2 := mul_right_cancel₀ (pow_ne_zero N hO) key
  have hxB : (x τ₀).det = g B.det := by rw [hxd]; simp [x₀]
  have k3 : P * B.det ^ (N + a (τ₀, (l : ℕ))) = (gen m L τ₀).det ^ N *
      ((gen m L τ₀).det ^ a (τ₀, (l : ℕ)) *
        eval₂Hom C (fun p : Lt m => x₀ p.1 p.2.1 p.2.2) P) := by
    apply hg
    rw [RingHom.comp_apply] at key2
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, ← hxB, ← hyd, pow_add, ← mul_assoc,
      key2, hs]
    ring
  exact (hrel.symm.pow (m := N) (n := N + a (τ₀, (l : ℕ)))).dvd_of_dvd_mul_right ⟨_, k3⟩
end Equivariant
end GlobalTheory.BorelAlg
