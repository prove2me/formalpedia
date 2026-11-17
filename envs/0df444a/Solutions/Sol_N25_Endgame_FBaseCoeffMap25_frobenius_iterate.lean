-- Prove2me | solution 1 for N25.Endgame.FBaseCoeffMap25_frobenius_iterate
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:55.295201+00:00
-- url     : https://prove2.me/submissions/e93d1597-d5dd-4caa-8711-db4290042ca7

import Theorems.Thm_N25_Endgame_coe_qExpFrobeniusModL_pow25
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_N25_intSeriesC_coeffMap25
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_N25_Endgame_qExpand_pow_intRatio25

/-! The power law for iterated q-expansion Frobenius over a finite coefficient field. -/
noncomputable section

namespace N25.Endgame

/-- Finite-field coefficients make the appropriate Frobenius iterate the cardinality power map. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [CharP k p]
    (K : Type*) [Field K] [CharP K p] [Algebra k K]
    (n : ℕ) (hk : Nat.card k = p ^ n) (x : FBase k) :
    (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n) (FBaseCoeffMap25 k K x) =
      FBaseCoeffMap25 k K (x ^ Nat.card k) := by
  dsimp only [FBase, ModularCurve.xHFunctionFieldC] at x ⊢
  let : Fintype k := Fintype.ofFinite k
  let : CharP (LaurentSeries k) p := ModularCurve.charP_laurentSeriesC k p
  let : CharP (LaurentSeries K) p := ModularCurve.charP_laurentSeriesC K p
  have hconst (c : k) : c ^ (p ^ n) = c := by
    rw [← hk, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have h (s : LaurentSeries k) (hs : s ∈ ModularCurve.qExpFunctionFieldC k Γ25) :
      (ModularCurve.qExpand K p ^ n) (ModularCurve.coeffMap (algebraMap k K) s) =
        ModularCurve.coeffMap (algebraMap k K) (s ^ (p ^ n)) := by
    induction hs using IntermediateField.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨w, f, g, a, b, hf, hg, hb, rfl⟩
      have hc : ModularCurve.coeffMap (algebraMap k K)
          (ModularCurve.intSeriesC k a / ModularCurve.intSeriesC k b) =
            ModularCurve.intSeriesC K a / ModularCurve.intSeriesC K b := by
        rw [map_div₀, N25.intSeriesC_coeffMap25, N25.intSeriesC_coeffMap25]
      simp only [map_pow, hc]
      exact qExpand_pow_intRatio25 p K n a b
    | algebraMap c =>
      have hc : (algebraMap k (LaurentSeries k) c) ^ (p ^ n) =
          algebraMap k (LaurentSeries k) c := by rw [← map_pow, hconst]
      rw [hc]
      have hcmap : ModularCurve.coeffMap (algebraMap k K)
          (algebraMap k (LaurentSeries k) c) =
            algebraMap K (LaurentSeries K) (algebraMap k K c) := by
        rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.coeffMap_single,
          ← ModularCurve.algebraMap_laurentSeries_eq_single]
      simp only [hcmap]
      have hcomm :=
        (ModularCurve.qExpandAlgHomC K p ^ n).commutes (algebraMap k K c)
      rw [AlgHom.coe_pow] at hcomm
      have he : ⇑(ModularCurve.qExpandAlgHomC K p) = ⇑(ModularCurve.qExpand K p) :=
        funext (ModularCurve.qExpandAlgHomC_apply K p)
      rw [he] at hcomm
      simpa only [RingHom.coe_pow] using hcomm
    | add z w _ _ hz hw =>
      rw [map_add, map_add, hz, hw, add_pow_char_pow, map_add]
    | mul z w _ _ hz hw =>
      rw [map_mul, map_mul, hz, hw, mul_pow, map_mul]
    | inv z _ hz =>
      rw [map_inv₀, map_inv₀, hz, inv_pow, map_inv₀]
  apply Subtype.ext
  dsimp only [FBaseCoeffMap25]
  rw [coe_qExpFrobeniusModL_pow25]
  change (ModularCurve.qExpand K p ^ n)
    (ModularCurve.coeffMap (algebraMap k K) (x : LaurentSeries k)) =
      ModularCurve.coeffMap (algebraMap k K) ((x : LaurentSeries k) ^ Nat.card k)
  rw [hk]
  exact h _ x.property

end N25.Endgame
