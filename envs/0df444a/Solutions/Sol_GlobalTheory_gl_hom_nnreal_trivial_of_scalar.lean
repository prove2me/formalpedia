-- Prove2me | solution 1 for GlobalTheory.gl_hom_nnreal_trivial_of_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:58:55.949198+00:00
-- url     : https://prove2.me/submissions/e330ee69-b288-41b6-8a64-dca0922ad728

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GlHomNnrealTrivialOfScalarTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
open Matrix
section HomTriv
variable {k : Type} [Field k] {N : ℕ}
private lemma hom_ne_zero (φ : GL (Fin N) k →* NNReal) (g : GL (Fin N) k) : φ g ≠ 0 := by
  intro h
  have := map_mul φ g g⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at this
  exact one_ne_zero this
private lemma diag_perm (φ : GL (Fin N) k →* NNReal) (σ : Equiv.Perm (Fin N))
    (d : Fin N → k) (hd : ∀ m, d m ≠ 0) :
    φ (nonsingInvUnit (diagonal (d ∘ σ))
        (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _ fun m => hd (σ m)))) =
      φ (nonsingInvUnit (diagonal d) (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero d hd))) := by
  set G := nonsingInvUnit (diagonal d) (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero d hd))
  have h1 : (σ.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) k) * σ.symm.toPEquiv.toMatrix = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  have h2 : (σ.symm.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) k) * σ.toPEquiv.toMatrix = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let U : GL (Fin N) k := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, h1, h2⟩
  have hconj : nonsingInvUnit (diagonal (d ∘ σ))
      (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _ fun m => hd (σ m))) = U * G * U⁻¹ := by
    apply Units.ext
    show diagonal (d ∘ σ) = σ.toPEquiv.toMatrix * diagonal d * σ.symm.toPEquiv.toMatrix
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix,
      Equiv.symm_symm]
    exact (submatrix_diagonal_equiv d σ).symm
  rw [hconj, map_mul, map_mul, mul_comm (φ U), mul_assoc, ← map_mul, mul_inv_cancel, map_one,
    mul_one]
end HomTriv
end GlobalTheory
namespace GlobalTheory
open Matrix
section HomTriv2
variable {k : Type} [Field k] {N : ℕ}
private lemma diag_conj_transvection (i j : Fin N) (hij : i ≠ j) (y c : k) :
    diagonal (Pi.mulSingle i y) * transvection i j c =
      transvection i j (y * c) * diagonal (Pi.mulSingle i y) := by
  ext a b
  simp only [diagonal_mul, mul_diagonal, transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Pi.mulSingle_apply]
  by_cases ha : a = i <;> by_cases hb : b = j <;> by_cases hab : a = b <;>
    simp_all [eq_comm] <;> ring
private lemma transvection_trivial (φ : GL (Fin N) k →* NNReal) (hx : ∃ x : k, x ≠ 0 ∧ x ≠ 1)
    (i j : Fin N) (hij : i ≠ j) (c : k) (g : GL (Fin N) k)
    (hg : (g : Matrix (Fin N) (Fin N) k) = transvection i j c) : φ g = 1 := by
  obtain ⟨x, hx0, hx1⟩ := hx
  have hdetT : ∀ c : k, (transvection i j c).det ≠ 0 := fun c => by
    rw [det_transvection_of_ne _ _ hij]; exact one_ne_zero
  let T : k → GL (Fin N) k := fun c => nonsingInvUnit _ (isUnit_iff_ne_zero.mpr (hdetT c))
  have hgT : g = T c := Units.ext hg
  have hmulT : ∀ a b, T a * T b = T (a + b) := fun a b =>
    Units.ext (transvection_mul_transvection_same i j hij a b)
  have hscale : ∀ y : k, y ≠ 0 → ∀ c, φ (T (y * c)) = φ (T c) := by
    intro y hy c
    have hd : ∀ m, (Pi.mulSingle i y : Fin N → k) m ≠ 0 := fun m => by
      by_cases hm : m = i
      · rw [hm, Pi.mulSingle_eq_same]; exact hy
      · rw [Pi.mulSingle_eq_of_ne hm]; exact one_ne_zero
    let D : GL (Fin N) k :=
      nonsingInvUnit (diagonal (Pi.mulSingle i y)) (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _ hd))
    have hc : D * T c = T (y * c) * D := Units.ext (diag_conj_transvection i j hij y c)
    have := congrArg φ hc
    rw [map_mul, map_mul, mul_comm (φ (T (y * c)))] at this
    exact (mul_left_cancel₀ (hom_ne_zero φ D) this).symm
  rw [hgT]
  have key : φ (T c) = φ (T c) * φ (T c) := by
    calc φ (T c) = φ (T (x * c)) := (hscale x hx0 c).symm
      _ = φ (T (c + (x - 1) * c)) := by congr 2; ring
      _ = φ (T c) * φ (T ((x - 1) * c)) := by rw [← hmulT, map_mul]
      _ = φ (T c) * φ (T c) := by rw [hscale (x - 1) (sub_ne_zero.mpr hx1) c]
  have h0 := hom_ne_zero φ (T c)
  exact (mul_right_eq_self₀.mp key.symm).resolve_right h0
end HomTriv2
end GlobalTheory
namespace GlobalTheory
open Matrix
section HomTriv3
variable {k : Type} [Field k] {N : ℕ}
private lemma elemDiag_coe (m : Fin N) (a : kˣ) :
    (elemDiag m a : Matrix (Fin N) (Fin N) k) = diagonal (Pi.mulSingle m (a : k)) := rfl
private lemma prod_elemDiag (d : Fin N → kˣ) :
    ((((List.finRange N).map fun m => elemDiag m (d m)).prod : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) = diagonal (fun t => (d t : k)) := by
  have h1 : ((((List.finRange N).map fun m => elemDiag m (d m)).prod : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) = ((List.finRange N).map
          ((diagonalRingHom (Fin N) k) ∘ fun m => Pi.mulSingle m (d m : k))).prod := by
    rw [show ((List.finRange N).map
        ((diagonalRingHom (Fin N) k) ∘ fun m => Pi.mulSingle m (d m : k))) =
        (List.finRange N).map ((Units.coeHom (Matrix (Fin N) (Fin N) k)) ∘
          fun m => elemDiag m (d m)) from rfl, List.prod_map_hom]
    rfl
  rw [h1, List.prod_map_hom, ← Fin.prod_univ_def, Finset.univ_prod_mulSingle (fun t => (d t : k))]
  rfl
private lemma elemDiag_swap (φ : GL (Fin N) k →* NNReal) (m m' : Fin N) (a : kˣ) :
    φ (elemDiag m a) = φ (elemDiag m' a) := by
  have hcomp : (Pi.mulSingle m' (a : k) : Fin N → k) ∘ (Equiv.swap m m') =
      Pi.mulSingle m (a : k) := by
    funext t
    simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have h := diag_perm φ (Equiv.swap m m') _ (mulSingle_unit_ne_zero m' a)
  have he : elemDiag m a = nonsingInvUnit (diagonal ((Pi.mulSingle m' (a : k) : Fin N → k) ∘
      (Equiv.swap m m'))) (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _
        fun t => mulSingle_unit_ne_zero m' a ((Equiv.swap m m') t))) :=
    Units.ext (by rw [elemDiag_coe]; exact congrArg diagonal hcomp.symm)
  rw [he, h]
  rfl
private lemma elemDiag_trivial (φ : GL (Fin N) k →* NNReal)
    (hφ : ∀ z : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1) (m : Fin N) (a : kˣ) :
    φ (elemDiag m a) = 1 := by
  have hs : Matrix.GeneralLinearGroup.scalar (Fin N) a =
      ((List.finRange N).map fun t => elemDiag t ((fun _ => a) t)).prod := by
    apply Units.ext
    rw [prod_elemDiag]
    simp [Matrix.GeneralLinearGroup.scalar]
  have h1 := hφ a
  rw [hs, map_list_prod, List.map_map, ← Fin.prod_univ_def] at h1
  simp only [Function.comp_apply] at h1
  rw [Finset.prod_congr rfl (fun t _ => elemDiag_swap φ t m a), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at h1
  have hN : N ≠ 0 := by rintro rfl; exact m.elim0
  exact (pow_eq_one_iff_of_nonneg zero_le hN).mp h1
private lemma diagonal_trivial (φ : GL (Fin N) k →* NNReal)
    (hφ : ∀ z : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1) (D : Fin N → k)
    (hD : ∀ t, D t ≠ 0) (g : GL (Fin N) k) (hg : (g : Matrix (Fin N) (Fin N) k) = diagonal D) :
    φ g = 1 := by
  let d : Fin N → kˣ := fun t => Units.mk0 (D t) (hD t)
  have : g = ((List.finRange N).map fun m => elemDiag m (d m)).prod :=
    Units.ext (by rw [prod_elemDiag, hg]; rfl)
  rw [this, map_list_prod, List.map_map, ← Fin.prod_univ_def]
  exact Finset.prod_eq_one fun m _ => elemDiag_trivial φ hφ m (d m)
end HomTriv3
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
open Matrix
variable {k : Type} [Field k] {N : ℕ}
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k], (∃ x : k, x ≠ 0 ∧ x ≠ 1) → ∀ (N : ℕ) (φ : GL (Fin N) k →* NNReal),
      (∀ z : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1) → ∀ g, φ g = 1 := by
  intro k _ hx N φ hφ g
  have hdet : (g : Matrix (Fin N) (Fin N) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ g : GL (Fin N) k, (g : Matrix (Fin N) (Fin N) k) = M → φ g = 1)
    (g : Matrix (Fin N) (Fin N) k) hdet ?_ ?_ ?_ g rfl
  · intro D hD h hh
    rw [det_diagonal] at hD
    exact diagonal_trivial φ hφ D (fun t => (Finset.prod_ne_zero_iff.mp hD) t (Finset.mem_univ t)) h hh
  · intro t h hh
    exact transvection_trivial φ hx t.i t.j t.hij t.c h hh
  · intro A B hA hB hPA hPB h hh
    let uA : GL (Fin N) k := nonsingInvUnit A (isUnit_iff_ne_zero.mpr hA)
    let uB : GL (Fin N) k := nonsingInvUnit B (isUnit_iff_ne_zero.mpr hB)
    have : h = uA * uB := Units.ext hh
    rw [this, map_mul, hPA uA rfl, hPB uB rfl, mul_one]
end GlobalTheory
