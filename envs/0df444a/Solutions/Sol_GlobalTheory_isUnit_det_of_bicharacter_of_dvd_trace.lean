-- Prove2me | solution 1 for GlobalTheory.isUnit_det_of_bicharacter_of_dvd_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:50:13.821038+00:00
-- url     : https://prove2.me/submissions/380a7978-4a62-4d8f-a021-e1219cc75d54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetBicharacterPowFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CardAlgHomReducedTraceSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsUnitDetPairingOfBicharacterOfDvdTrace
import Theorems.Thm_GlobalTheory_det_bicharacter_pow_four
import Theorems.Thm_GlobalTheory_finite_card_trace_algHom_of_isReduced_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped TensorProduct
namespace GlobalTheory
private theorem submatrix_eq_pt_mul_map_mul_transpose {O H K Γ : Type} [CommRing O] [CommRing H] [Algebra O H] [Field K]
    [Algebra O K] {r : ℕ} (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O)
    (pt : Γ → (H →ₐ[O] K)) (X : Γ → Γ → K)
    (hX : ∀ a a', X a a' = ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j))
    (e : Fin r ≃ Γ) :
    (Matrix.of X).submatrix e e = Matrix.of (fun i j => pt (e i) (b j)) * D.map (algebraMap O K) *
      Matrix.transpose (Matrix.of (fun i j => pt (e i) (b j))) := by
  ext i k
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, hX]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring
end GlobalTheory
end

set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O H K Γ : Type) [CommRing O] [IsDomain O] [CommRing H] [Algebra O H] [Field K] [IsAlgClosed K] [Algebra O K] [CommGroup Γ] (r : ℕ) (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (pt : Γ → (H →ₐ[O] K)) (X : Γ → Γ → K) (c : O), Function.Injective (algebraMap O K) → IsReduced (K ⊗[O] H) → Function.Bijective pt → (∀ a a', X a a' = ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j)) → (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → c ≠ 0 → (r : O) = c ^ 2 → (∀ h : H, c ∣ Algebra.trace O H h) → IsUnit D.det := by
  intro O H K Γ _ _ _ _ _ _ _ _ r b D pt X c hinj hred hpt hX hne hm₁ hm₂ hnd hc hr hdvd
  classical
  haveI : Module.Free O H := Module.Free.of_basis b
  haveI : Module.Finite O H := Module.Finite.of_basis b
  obtain ⟨hfin, hcard, htrace⟩ :=
    finite_card_trace_algHom_of_isReduced_baseChange O H K hred
  let E : Γ ≃ (H →ₐ[O] K) := Equiv.ofBijective pt hpt
  haveI : Finite Γ := Finite.of_equiv _ E.symm
  letI : Fintype Γ := Fintype.ofFinite Γ
  letI : Fintype (H →ₐ[O] K) := Fintype.ofFinite _
  have hcardΓ : Fintype.card Γ = r := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr E, hcard, Module.finrank_eq_card_basis b,
      Fintype.card_fin]

  let e : Fin r ≃ Γ := (Fintype.equivFinOfCardEq hcardΓ).symm
  let P : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => pt (e i) (b j)
  let D' : Matrix (Fin r) (Fin r) K := D.map (algebraMap O K)

  have hXP : (Matrix.of X).submatrix e e = P * D' * Matrix.transpose P := submatrix_eq_pt_mul_map_mul_transpose b D pt X hX e

  have hsum : ∀ h : H, algebraMap O K (Algebra.trace O H h) = ∑ i, pt (e i) h := by
    intro h
    rw [htrace h, finsum_eq_sum_of_fintype]
    exact (Fintype.sum_equiv (e.trans E) (fun i => pt (e i) h) (fun ga => ga h)
      fun _ => rfl).symm
  have hdvd' : ∀ h : H, ∃ d, Algebra.trace O H h = c * d := fun h => hdvd h
  choose T hT using hdvd'
  let Tm : Matrix (Fin r) (Fin r) O := Matrix.of fun j k => T (b j * b k)

  have hPP : Matrix.transpose P * P = (algebraMap O K c) • Tm.map (algebraMap O K) := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, P, Matrix.of_apply, Matrix.smul_apply,
      Matrix.map_apply, Tm, smul_eq_mul]
    have hjk : algebraMap O K c * algebraMap O K (T (b j * b k)) =
        algebraMap O K (Algebra.trace O H (b j * b k)) := by
      rw [hT, map_mul]
    rw [hjk, hsum]
    exact Finset.sum_congr rfl fun i _ => (map_mul (pt (e i)) (b j) (b k)).symm
  have hTm : (Tm.map (algebraMap O K)).det = algebraMap O K Tm.det :=
    ((algebraMap O K).map_det Tm).symm
  have hD' : D'.det = algebraMap O K D.det := ((algebraMap O K).map_det D).symm
  have hdetP : P.det ^ 2 = algebraMap O K c ^ r * algebraMap O K Tm.det := by
    have h := congrArg Matrix.det hPP
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin, hTm] at h
    rw [sq, h]
  have h4 := det_bicharacter_pow_four Γ K X hne hm₁ hm₂ hnd
  rw [← Matrix.det_submatrix_equiv_self e (Matrix.of X), hXP, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hcardΓ] at h4
  have hrK : (r : K) = algebraMap O K c ^ 2 := by
    rw [← map_natCast (algebraMap O K) r, hr, map_pow]

  have key : algebraMap O K c ^ (4 * r) * algebraMap O K (Tm.det ^ 4 * D.det ^ 4) =
      algebraMap O K c ^ (4 * r) * 1 := by
    rw [map_mul, map_pow, map_pow, ← hD', mul_one]
    calc algebraMap O K c ^ (4 * r) * (algebraMap O K Tm.det ^ 4 * D'.det ^ 4)
        = (algebraMap O K c ^ r * algebraMap O K Tm.det) ^ 4 * D'.det ^ 4 := by ring
      _ = (P.det ^ 2) ^ 4 * D'.det ^ 4 := by rw [hdetP]
      _ = (P.det * D'.det * P.det) ^ 4 := by ring
      _ = (r : K) ^ (2 * r) := h4
      _ = algebraMap O K c ^ (4 * r) := by
        rw [hrK, ← pow_mul]
        congr 1
        ring
  have hu : algebraMap O K c ^ (4 * r) ≠ 0 :=
    pow_ne_zero _ (by rwa [ne_eq, map_eq_zero_iff _ hinj])
  have h1 := mul_left_cancel₀ hu key
  rw [← map_one (algebraMap O K)] at h1
  have h2 := hinj h1
  exact isUnit_iff_exists_inv.mpr ⟨Tm.det ^ 4 * D.det ^ 3, by linear_combination h2⟩
end GlobalTheory
