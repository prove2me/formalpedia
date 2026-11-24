-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_euler_weights
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:50:33.984927+00:00
-- url     : https://prove2.me/submissions/206536b8-6226-46ce-ab92-0dfd284e6352

import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Definitions.Def_HodgeComputerSSR_Q5K5Master
import Theorems.Thm_HodgeComputer_Formal_RationalResidues_residue_sum_eq_infinity
import Theorems.Thm_HodgeComputer_Formal_QuadraticCovers_simplePole_residue
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_poly_scaled
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_localQ5_recurrences_K5

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.CoverAlgebra
  SymmetricSexticResidual.CoverResidue SymmetricSexticResidual.Q5WeightsData
  QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators

private abbrev D_all_K5_ne := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_poly_scaled.2.1
private abbrev Q5_K5_eq_scaled := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_poly_scaled.2.2.2.1
private abbrev Q7_K5_eq_scaled := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_poly_scaled.2.2.2.2.1
private abbrev Q5_c5_eq_fac := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_poly_scaled.2.2.2.2.2.1
private abbrev D_all_eq_lc5_mul := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_poly_scaled.2.2.2.2.2.2
private abbrev Q5_Q7_recurrences_K5 := HodgeComputer.SymmetricSexticResidual.Proof.localQ5_recurrences_K5

lemma infinityCoefficient_apply (g : RatFunc CoverL) :
    CrossedRationalResidue.infinityCoefficient g =
      CrossedRationalResidue.residue (0 : CoverL) ((RatFunc.X ^ 2)⁻¹ * reciprocal g) := rfl

-- Euler residue trace on `X^m / Q5_pol` (`m = 0..4`) via `HodgeComputer.Formal.RationalResidues.residue_sum_eq_infinity`!
lemma sum_RQ5_euler_power (m : Fin 5) :
    ∑ r ∈ RQ5, r ^ m.val / (Q5_pol_K5.map ιL_K5).derivative.eval r =
      if m.val = 4 then ιL_K5 (evalSQ_K5 (Q5_c 5))⁻¹ else 0 := by
  set Q5L : CoverL[X] := Q5_pol_K5.map ιL_K5
  have h2893401 : (2893401 : K5) ≠ 0 := by exact_mod_cast (by decide : (2893401 : ℕ) ≠ 0)
  have hQ5L_eq : Q5L = Polynomial.C (ιL_K5 2893401) * k5Params.Q5_z.map ιL_K5 := by
    dsimp only [Q5L]
    rw [← Q5_K5_eq_scaled, Polynomial.map_mul, Polynomial.map_C]
  have hQ5L_ne : Q5L ≠ 0 := by
    rw [hQ5L_eq]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr (map_ne_zero_iff _ ιL_K5.injective |>.mpr h2893401))
      (Polynomial.map_ne_zero Q5_K5_ne_zero)
  have hQ5L_deg : Q5L.natDegree = 5 := by
    rw [hQ5L_eq, Polynomial.natDegree_C_mul (map_ne_zero_iff _ ιL_K5.injective |>.mpr h2893401),
      Polynomial.natDegree_map_eq_of_injective ιL_K5.injective, Q5_K5_natDegree]
  have hQ5L_c5 : Q5L.coeff 5 = ιL_K5 (evalSQ_K5 (Q5_c 5)) := by
    simp only [Q5L, Q5_pol_K5, ← Polynomial.lcoeff_apply]
    simp only [Polynomial.lcoeff_apply, Fin.sum_univ_six]
    simp
  have hQ5L_c5_ne : Q5L.coeff 5 ≠ 0 := by
    rw [← hQ5L_deg]; exact Polynomial.leadingCoeff_ne_zero.mpr hQ5L_ne
  let f : RatFunc CoverL :=
    algebraMap CoverL[X] (RatFunc CoverL) (Polynomial.X ^ m.val) /
    algebraMap CoverL[X] (RatFunc CoverL) Q5L
  have hf_splits : f.denom.Splits := by
    have hdvd : f.denom ∣ Q5L := (RatFunc.denom_dvd hQ5L_ne).mpr ⟨Polynomial.X ^ m.val, rfl⟩
    have hsp : Q5L.Splits := by
      rw [hQ5L_eq]
      exact (Polynomial.Splits.C _).mul Q5_splits_CoverL
    exact hsp.of_dvd hQ5L_ne hdvd
  have houtside : ∀ a ∉ RQ5, CrossedRationalResidue.residue a f = 0 := by
    intro a ha
    have ha_ne : Q5L.eval a ≠ 0 := by
      rw [hQ5L_eq, Polynomial.eval_mul, Polynomial.eval_C]
      refine mul_ne_zero (map_ne_zero_iff _ ιL_K5.injective |>.mpr h2893401) ?_
      intro h0; exact ha (mem_RQ5_iff.mpr h0)
    have hreg : RegularAt a f := ⟨Polynomial.X ^ m.val, Q5L, ha_ne, rfl⟩
    exact hreg.residue_eq_zero
  have hsum_eq := HodgeComputer.Formal.RationalResidues.residue_sum_eq_infinity f hf_splits RQ5 houtside
  have hres_r : ∀ r ∈ RQ5, CrossedRationalResidue.residue r f = r ^ m.val / Q5L.derivative.eval r := by
    intro r hr
    have hr0 : Q5L.eval r = 0 := by
      rw [hQ5L_eq, Polynomial.eval_mul, Polynomial.eval_C, mem_RQ5_iff.mp hr, mul_zero]
    have hrd : Q5L.derivative.eval r ≠ 0 := by
      rw [hQ5L_eq, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
      refine mul_ne_zero (map_ne_zero_iff _ ιL_K5.injective |>.mpr h2893401) ?_
      have hcop := eval_ne_zero_of_isCoprime isCoprime_Q5_Q5_deriv (mem_RQ5_iff.mp hr)
      rwa [← Polynomial.derivative_map] at hcop
    rw [HodgeComputer.Formal.QuadraticCovers.simplePole_residue (Polynomial.X ^ m.val) Q5L r hr0 hrd]
    simp [Polynomial.eval_pow, Polynomial.eval_X]
  rw [Finset.sum_congr rfl hres_r] at hsum_eq
  rw [hsum_eq]
  -- Compute `infinityCoefficient f = residue 0 ((X^2)⁻¹ * reciprocal f)` via reversed polynomial `Q_rev`!
  let Q_rev : CoverL[X] := ∑ j : Fin 6, Polynomial.C (Q5L.coeff (5 - j.val)) * Polynomial.X ^ j.val
  have hQrev_0 : Q_rev.eval 0 = Q5L.coeff 5 := by
    simp [Q_rev, Fin.sum_univ_six]
  have hQrev_0_ne : Q_rev.eval 0 ≠ 0 := by rw [hQrev_0]; exact hQ5L_c5_ne
  have hrec_Q5L : reciprocal (algebraMap CoverL[X] (RatFunc CoverL) Q5L) =
      algebraMap CoverL[X] (RatFunc CoverL) Q_rev / RatFunc.X ^ 5 := by
    rw [reciprocal_polynomial]
    have hQ5L_as : Q5L = ∑ j : Fin 6, Polynomial.C (Q5L.coeff j.val) * Polynomial.X ^ j.val := by
      rw [Fin.sum_univ_eq_sum_range (fun j => Polynomial.C (Q5L.coeff j) * Polynomial.X ^ j)]
      exact Polynomial.as_sum_range_C_mul_X_pow' Q5L (by omega)
    conv_lhs => rw [hQ5L_as]
    simp only [map_sum, map_mul, map_pow, aeval_C, aeval_X,
      show ∀ c : CoverL, algebraMap CoverL (RatFunc CoverL) c = RatFunc.C c from fun _ => rfl,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X, Q_rev]
    rw [Finset.sum_div, Fin.sum_univ_six, Fin.sum_univ_six]
    have hX := CrossedRationalResidue.X_ne_zero (K := CoverL)
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 6).val = 3 from rfl,
      show (4 : Fin 6).val = 4 from rfl, show (5 : Fin 6).val = 5 from rfl,
      Nat.sub_zero, Nat.reduceSub, pow_zero, pow_one, inv_pow, mul_one]
    field_simp [hX]
    ring
  have hrec_Xm : reciprocal (algebraMap CoverL[X] (RatFunc CoverL) (Polynomial.X ^ m.val)) =
      (RatFunc.X ^ m.val)⁻¹ := by
    rw [map_pow, RatFunc.algebraMap_X, map_pow, reciprocal_X, inv_pow]
  have hQrev_ne : algebraMap CoverL[X] (RatFunc CoverL) Q_rev ≠ 0 :=
    polynomialMap_ne_zero (fun h0 => hQrev_0_ne (by simp [h0]))
  have hX := CrossedRationalResidue.X_ne_zero (K := CoverL)
  rw [infinityCoefficient_apply]
  simp only [f, map_div₀, hrec_Xm, hrec_Q5L]
  split_ifs with hm4
  · have hsimp : (RatFunc.X ^ 2)⁻¹ * ((RatFunc.X ^ m.val)⁻¹ /
        (algebraMap CoverL[X] (RatFunc CoverL) Q_rev / RatFunc.X ^ 5)) =
        (algebraMap CoverL[X] (RatFunc CoverL) (1 : CoverL[X]) /
          algebraMap CoverL[X] (RatFunc CoverL) Q_rev) / uniformizer (0 : CoverL) := by
      rw [hm4, uniformizer_zero, map_one]
      field_simp [hX, hQrev_ne]
    rw [hsimp, residue_div_uniformizer, valueAt_div_polynomials 0 1 Q_rev hQrev_0_ne,
      Polynomial.eval_one, hQrev_0, hQ5L_c5, one_div, map_inv₀]
  · have hm3 : m.val ≤ 3 := by omega
    have hsimp : (RatFunc.X ^ 2)⁻¹ * ((RatFunc.X ^ m.val)⁻¹ /
        (algebraMap CoverL[X] (RatFunc CoverL) Q_rev / RatFunc.X ^ 5)) =
        algebraMap CoverL[X] (RatFunc CoverL) (Polynomial.X ^ (3 - m.val)) /
        algebraMap CoverL[X] (RatFunc CoverL) Q_rev := by
      rw [map_pow, RatFunc.algebraMap_X]
      have hpow : (RatFunc.X : RatFunc CoverL) ^ (3 - m.val) * (RatFunc.X ^ 2 * RatFunc.X ^ m.val) = RatFunc.X ^ 5 := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [← hpow]
      field_simp [hX, hQrev_ne]
    rw [hsimp]
    have hreg : RegularAt (0 : CoverL)
        (algebraMap CoverL[X] (RatFunc CoverL) (Polynomial.X ^ (3 - m.val)) /
          algebraMap CoverL[X] (RatFunc CoverL) Q_rev) := ⟨Polynomial.X ^ (3 - m.val), Q_rev, hQrev_0_ne, rfl⟩
    exact hreg.residue_eq_zero

def seqRec5 {K : Type*} [Field K] (c : Fin 6 → K) (init : Fin 5 → K) : ℕ → K
  | 0 => init 0
  | 1 => init 1
  | 2 => init 2
  | 3 => init 3
  | 4 => init 4
  | n + 5 => -(∑ j : Fin 5, c j.castSucc * seqRec5 c init (n + j.val)) / c (Fin.last 5)
termination_by n => n

-- 15-line Bézout proof identifying every `RQ5` power sum `k = 0..12` with `W_K5_scaled k`!
lemma sum_RQ5_power_eq_W_k (k : Fin 13) :
    ∑ r ∈ RQ5, r ^ k.val / ((k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r) =
      ιL_K5 (W_K5_scaled k) := by
  have h2893401 : (2893401 : K5) ≠ 0 := by exact_mod_cast (by decide : (2893401 : ℕ) ≠ 0)
  have h1640 : (1640558367 : K5) ≠ 0 := by exact_mod_cast (by decide : (1640558367 : ℕ) ≠ 0)
  have h2 : (2 : K5) ≠ 0 := by exact_mod_cast (by decide : (2 : ℕ) ≠ 0)
  have hDint : (D_int_all : K5) ≠ 0 :=
    Int.cast_ne_zero.mpr (by unfold D_int_all; decide)
  have hlc5_ne : evalSQ_K5 (Q5_c 5) ≠ 0 := by
    rw [Q5_c5_eq_fac]
    have h112 : (lc5_const : K5) ≠ 0 := by
      unfold lc5_const; push_cast
      exact neg_ne_zero.mpr (by exact_mod_cast (by decide : (112 : ℕ) ≠ 0))
    have hfac : evalSQ_K5 lc5_fac_expr ≠ 0 :=
      left_ne_zero_of_mul (D_all_eq_lc5_mul ▸ D_all_K5_ne)
    exact mul_ne_zero h112 hfac
  set Q5L : CoverL[X] := Q5_pol_K5.map ιL_K5
  set Q7L : CoverL[X] := Q7_pol_K5.map ιL_K5
  have hQ5L_eq : Q5L = Polynomial.C (ιL_K5 2893401) * k5Params.Q5_z.map ιL_K5 := by
    dsimp only [Q5L]
    rw [← Q5_K5_eq_scaled, Polynomial.map_mul, Polynomial.map_C]
  have hQ7L_eq : Polynomial.C (ιL_K5 2) * Q7L = Polynomial.C (ιL_K5 1640558367) * k5Params.Q7_z.map ιL_K5 := by
    dsimp only [Q7L]
    rw [← Polynomial.map_C, ← Polynomial.map_mul, ← Q7_K5_eq_scaled, Polynomial.map_mul, Polynomial.map_C]
  -- First prove for `Q5L`, `Q7L`: `T_pol k = ιL_K5 (W_K5 k)`!
  let T_pol (n : ℕ) : CoverL := ∑ r ∈ RQ5, r ^ n / (Q7L.eval r * Q5L.derivative.eval r)
  have hQ7_ne_r : ∀ r ∈ RQ5, Q7L.eval r ≠ 0 := by
    intro r hr
    have h7 := eval_ne_zero_of_isCoprime isCoprime_Q5_Q7 (mem_RQ5_iff.mp hr)
    intro h0
    have hev := congrArg (fun p : CoverL[X] => p.eval r) hQ7L_eq
    simp only [Polynomial.eval_mul, Polynomial.eval_C, h0, mul_zero] at hev
    exact mul_ne_zero (map_ne_zero_iff _ ιL_K5.injective |>.mpr h1640) h7 hev.symm
  have hdQ5_ne_r : ∀ r ∈ RQ5, Q5L.derivative.eval r ≠ 0 := by
    intro r hr
    rw [hQ5L_eq, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
    refine mul_ne_zero (map_ne_zero_iff _ ιL_K5.injective |>.mpr h2893401) ?_
    have h := eval_ne_zero_of_isCoprime isCoprime_Q5_Q5_deriv (mem_RQ5_iff.mp hr)
    rwa [← Polynomial.derivative_map] at h
  have hT_rec5 : ∀ n : ℕ, ∑ j : Fin 6, ιL_K5 (evalSQ_K5 (Q5_c j)) * T_pol (n + j.val) = 0 := by
    intro n
    simp only [T_pol, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero; intro r hr
    have h1 : ∑ j : Fin 6, ιL_K5 (evalSQ_K5 (Q5_c j)) * (r ^ (n + j.val) / (Q7L.eval r * Q5L.derivative.eval r)) =
        (r ^ n * Q5L.eval r) / (Q7L.eval r * Q5L.derivative.eval r) := by
      have hev5 : Q5L.eval r = ∑ j : Fin 6, ιL_K5 (evalSQ_K5 (Q5_c j)) * r ^ j.val := by
        simp only [Q5L, Q5_pol_K5, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_pow, Polynomial.map_X,
          show ∀ p : CoverL[X], p.eval r = Polynomial.evalRingHom r p from fun _ => rfl, map_sum]
        simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [hev5, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl; intro j _
      rw [pow_add]; ring
    rw [h1, hQ5L_eq, Polynomial.eval_mul, Polynomial.eval_C, mem_RQ5_iff.mp hr]
    simp
  have hT_dual7 : ∀ m : Fin 5,
      ∑ j : Fin 8, ιL_K5 (evalSQ_K5 (Q7_c j)) * T_pol (m.val + j.val) =
        if m.val = 4 then ιL_K5 (evalSQ_K5 (Q5_c 5))⁻¹ else 0 := by
    intro m
    rw [← sum_RQ5_euler_power m]
    simp only [T_pol, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r hr
    have h1 : ∑ j : Fin 8, ιL_K5 (evalSQ_K5 (Q7_c j)) * (r ^ (m.val + j.val) / (Q7L.eval r * Q5L.derivative.eval r)) =
        (r ^ m.val * Q7L.eval r) / (Q7L.eval r * Q5L.derivative.eval r) := by
      have hev7 : Q7L.eval r = ∑ j : Fin 8, ιL_K5 (evalSQ_K5 (Q7_c j)) * r ^ j.val := by
        simp only [Q7L, Q7_pol_K5, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_pow, Polynomial.map_X,
          show ∀ p : CoverL[X], p.eval r = Polynomial.evalRingHom r p from fun _ => rfl, map_sum]
        simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [hev7, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl; intro j _
      rw [pow_add]; ring
    rw [h1]
    have hq7 := hQ7_ne_r r hr
    rw [_root_.mul_comm (r ^ m.val) (Q7L.eval r), mul_div_mul_left _ _ hq7]
  -- Now compare `T_pol` with `W_K5` using `Q5_Q7_recurrences_K5`!
  obtain ⟨hW5, hW7_03, hW7_4⟩ := Q5_Q7_recurrences_K5
  have hW_rec5 (n : Fin 8) :
      ∑ j : Fin 6, ιL_K5 (evalSQ_K5 (Q5_c j)) * ιL_K5 (W_K5 ⟨n.val + j.val, by omega⟩) = 0 := by
    have h := congrArg ιL_K5 (hW5 n)
    simp only [map_sum, map_mul, map_zero] at h
    simp_rw [W_K5, map_div₀, ← mul_div_assoc]
    rw [← Finset.sum_div, h, zero_div]
  have hW_dual7 (m : Fin 5) :
      ∑ j : Fin 8, ιL_K5 (evalSQ_K5 (Q7_c j)) * ιL_K5 (W_K5 ⟨m.val + j.val, by omega⟩) =
        if m.val = 4 then ιL_K5 (evalSQ_K5 (Q5_c 5))⁻¹ else 0 := by
    split_ifs with hm4
    · have h4 : m = 4 := Fin.ext hm4
      clear hm4; subst h4
      have hden_ne : (D_int_all : K5) * evalSQ_K5 D_all_expr ≠ 0 := mul_ne_zero hDint D_all_K5_ne
      have hK : ∑ j : Fin 8, evalSQ_K5 (Q7_c j) * W_K5 ⟨(4 : Fin 5).val + j.val, by omega⟩ = (evalSQ_K5 (Q5_c 5))⁻¹ := by
        simp only [show (4 : Fin 5).val = 4 from rfl]
        simp_rw [W_K5, ← mul_div_assoc]
        rw [← Finset.sum_div, div_eq_iff hden_ne]
        apply mul_left_cancel₀ hlc5_ne
        rw [← mul_assoc, mul_inv_cancel₀ hlc5_ne, one_mul, Q5_c5_eq_fac, D_all_eq_lc5_mul]
        have hW7_4' := hW7_4
        generalize ∑ j : Fin 8, evalSQ_K5 (Q7_c j) * evalSQ_K5 (W_num_expr ⟨4 + j.val, by omega⟩) = S7 at hW7_4' ⊢
        generalize evalSQ_K5 lc5_fac_expr = flc
        generalize evalSQ_K5 D_all_div_lc5_expr = fdl at hW7_4' ⊢
        generalize (D_int_all : K5) = dA at hW7_4' ⊢
        generalize (lc5_const : K5) = c5 at hW7_4' ⊢
        linear_combination flc * hW7_4'
      have hL := congrArg ιL_K5 hK
      simpa only [map_sum, map_mul, map_inv₀] using hL
    · have hm4' : m.val < 4 := by omega
      have h := congrArg ιL_K5 (hW7_03 ⟨m.val, hm4'⟩)
      simp only [map_sum, map_mul, map_zero] at h
      simp_rw [W_K5, map_div₀, ← mul_div_assoc]
      rw [← Finset.sum_div, h, zero_div]
  -- Define `Δ_ext : ℕ → CoverL` extending `T_pol n - ιL_K5 (W_K5 n)` recursively via `Q5`!
  let Δ_ext : ℕ → CoverL :=
    seqRec5 (fun j => ιL_K5 (evalSQ_K5 (Q5_c j))) (fun j => T_pol j.val - ιL_K5 (W_K5 ⟨j.val, by omega⟩))
  have hΔ_rec (n : ℕ) : ∑ j : Fin 6, ιL_K5 (evalSQ_K5 (Q5_c j)) * Δ_ext (n + j.val) = 0 := by
    have hlcL : ιL_K5 (evalSQ_K5 (Q5_c (Fin.last 5))) ≠ 0 := (map_ne_zero_iff _ ιL_K5.injective).mpr hlc5_ne
    have h5 : Δ_ext (n + 5) =
        -(∑ j : Fin 5, ιL_K5 (evalSQ_K5 (Q5_c j.castSucc)) * Δ_ext (n + j.val)) /
          ιL_K5 (evalSQ_K5 (Q5_c (Fin.last 5))) := by
      dsimp only [Δ_ext]; rw [seqRec5]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, h5, mul_div_cancel₀ _ hlcL]
    ring
  have hΔ_eq (n : Fin 13) : Δ_ext n.val = T_pol n.val - ιL_K5 (W_K5 n) := by
    obtain ⟨m, hm⟩ := n
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hlt : m < 5
      · interval_cases m <;> (dsimp only [Δ_ext]; rw [seqRec5]; rfl)
      · have hlcL : ιL_K5 (evalSQ_K5 (Q5_c (Fin.last 5))) ≠ 0 := (map_ne_zero_iff _ ιL_K5.injective).mpr hlc5_ne
        have hm5 : m - 5 < 8 := by omega
        have hr1 := hΔ_rec (m - 5)
        have hr2 := hT_rec5 (m - 5)
        have hr3 := hW_rec5 ⟨m - 5, hm5⟩
        rw [Fin.sum_univ_castSucc] at hr1 hr2 hr3
        simp only [Fin.val_castSucc, Fin.val_last, show m - 5 + 5 = m by omega] at hr1 hr2 hr3
        have hsum_eq : ∑ j : Fin 5, ιL_K5 (evalSQ_K5 (Q5_c j.castSucc)) * Δ_ext (m - 5 + j.val) =
            ∑ j : Fin 5, ιL_K5 (evalSQ_K5 (Q5_c j.castSucc)) *
              (T_pol (m - 5 + j.val) - ιL_K5 (W_K5 ⟨m - 5 + j.val, by omega⟩)) := by
          apply Finset.sum_congr rfl; intro j _
          rw [ih (m - 5 + j.val) (by omega) (by omega)]
        apply mul_left_cancel₀ hlcL
        have hdiff : ∑ j : Fin 5, ιL_K5 (evalSQ_K5 (Q5_c j.castSucc)) *
              (T_pol (m - 5 + j.val) - ιL_K5 (W_K5 ⟨m - 5 + j.val, by omega⟩)) =
            (∑ j : Fin 5, ιL_K5 (evalSQ_K5 (Q5_c j.castSucc)) * T_pol (m - 5 + j.val)) -
            (∑ j : Fin 5, ιL_K5 (evalSQ_K5 (Q5_c j.castSucc)) * ιL_K5 (W_K5 ⟨m - 5 + j.val, by omega⟩)) := by
          rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
        rw [hsum_eq, hdiff] at hr1
        linear_combination hr1 - hr2 + hr3
  -- Linear functional `Λ(P) = ∑ P.coeff n * Δ_ext n`: vanishes on `Q5L * A` and `Q7L * B`!
  let Λ : CoverL[X] → CoverL := fun P => P.sum (fun n c => c * Δ_ext n)
  have hΛ_add (P Q : CoverL[X]) : Λ (P + Q) = Λ P + Λ Q :=
    Polynomial.sum_add_index _ _ _ (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
  have hΛ_C_mul_X (c : CoverL) (n : ℕ) : Λ (Polynomial.C c * Polynomial.X ^ n) = c * Δ_ext n := by
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    exact Polynomial.sum_monomial_index _ _ (zero_mul _)
  have hΛ_Q5 (A : CoverL[X]) : Λ (Q5L * A) = 0 := by
    induction A using Polynomial.induction_on' with
    | add p q hp hq => rw [mul_add, hΛ_add, hp, hq, add_zero]
    | monomial n c =>
      have h1 : Q5L * Polynomial.monomial n c =
          ∑ j : Fin 6, Polynomial.C (c * ιL_K5 (evalSQ_K5 (Q5_c j))) * Polynomial.X ^ (n + j.val) := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp only [Q5L, Q5_pol_K5, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_pow, Polynomial.map_X, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _
        rw [pow_add, map_mul]; ring
      rw [h1]
      have hΛ_sum : ∀ (s : Finset (Fin 6)) (f : Fin 6 → CoverL[X]), Λ (∑ j ∈ s, f j) = ∑ j ∈ s, Λ (f j) := by
        intro s f; classical induction s using Finset.induction_on with
        | empty => simp [Λ]
        | insert a s ha ih => rw [Finset.sum_insert ha, hΛ_add, ih, Finset.sum_insert ha]
      rw [hΛ_sum]
      simp_rw [hΛ_C_mul_X, mul_assoc, ← Finset.mul_sum, hΔ_rec, mul_zero]
  have hΛ_Q7_mon (m : Fin 5) (c : CoverL) : Λ (Q7L * Polynomial.monomial m.val c) = 0 := by
    have h1 : Q7L * Polynomial.monomial m.val c =
        ∑ j : Fin 8, Polynomial.C (c * ιL_K5 (evalSQ_K5 (Q7_c j))) * Polynomial.X ^ (m.val + j.val) := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [Q7L, Q7_pol_K5, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      rw [pow_add, map_mul]; ring
    rw [h1]
    have hΛ_sum : ∀ (s : Finset (Fin 8)) (f : Fin 8 → CoverL[X]), Λ (∑ j ∈ s, f j) = ∑ j ∈ s, Λ (f j) := by
      intro s f; classical induction s using Finset.induction_on with
      | empty => simp [Λ]
      | insert a s ha ih => rw [Finset.sum_insert ha, hΛ_add, ih, Finset.sum_insert ha]
    rw [hΛ_sum]
    simp_rw [hΛ_C_mul_X, mul_assoc, ← Finset.mul_sum]
    have hsum0 : ∑ j : Fin 8, ιL_K5 (evalSQ_K5 (Q7_c j)) * Δ_ext (m.val + j.val) = 0 := by
      have heq : ∀ j : Fin 8, Δ_ext (m.val + j.val) = T_pol (m.val + j.val) - ιL_K5 (W_K5 ⟨m.val + j.val, by omega⟩) :=
        fun j => hΔ_eq ⟨m.val + j.val, by omega⟩
      simp_rw [heq, mul_sub, Finset.sum_sub_distrib, hT_dual7 m, hW_dual7 m, sub_self]
    rw [hsum0, mul_zero]
  have hΛ_Q7 (B : CoverL[X]) : Λ (Q7L * B) = 0 := by
    have hQ5L_ne : Q5L ≠ 0 := by
      rw [hQ5L_eq]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr ((map_ne_zero_iff _ ιL_K5.injective).mpr h2893401))
        (Polynomial.map_ne_zero Q5_K5_ne_zero)
    have hQ5L_deg : Q5L.natDegree = 5 := by
      rw [hQ5L_eq, Polynomial.natDegree_C_mul ((map_ne_zero_iff _ ιL_K5.injective).mpr h2893401),
        Polynomial.natDegree_map_eq_of_injective ιL_K5.injective, Q5_K5_natDegree]
    have hdiv := Polynomial.modByMonic_add_div B (p := Polynomial.C (Q5L.leadingCoeff⁻¹) * Q5L)
    set Q5M := Polynomial.C (Q5L.leadingCoeff⁻¹) * Q5L
    have hM_monic : Q5M.Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hQ5L_ne)]
    have hM_deg : Q5M.natDegree = 5 := by
      rw [Polynomial.natDegree_C_mul (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hQ5L_ne)), hQ5L_deg]
    set rem := B %ₘ Q5M
    set quo := B /ₘ Q5M
    have hB_eq : B = rem + Q5L * (Polynomial.C (Q5L.leadingCoeff⁻¹) * quo) := by
      have h := Polynomial.modByMonic_add_div B Q5M
      rw [← h]; dsimp only [rem, quo, Q5M]; ring
    rw [hB_eq, mul_add, hΛ_add, show Q7L * (Q5L * (Polynomial.C Q5L.leadingCoeff⁻¹ * quo)) =
        Q5L * (Q7L * (Polynomial.C Q5L.leadingCoeff⁻¹ * quo)) by ring, hΛ_Q5, add_zero]
    have hrem_deg : rem.natDegree < 5 := by
      by_cases hr0 : rem = 0
      · simp [hr0]
      · have hlt := Polynomial.degree_modByMonic_lt B hM_monic
        rw [Polynomial.degree_eq_natDegree hr0, Polynomial.degree_eq_natDegree hM_monic.ne_zero, hM_deg] at hlt
        exact WithBot.coe_lt_coe.mp hlt
    have hrem_sum : rem = ∑ m : Fin 5, Polynomial.monomial m.val (rem.coeff m.val) := by
      rw [Fin.sum_univ_eq_sum_range (fun m => Polynomial.monomial m (rem.coeff m))]
      exact Polynomial.as_sum_range' rem 5 hrem_deg
    rw [hrem_sum, Finset.mul_sum]
    have hΛ_sum5 : ∀ (s : Finset (Fin 5)) (f : Fin 5 → CoverL[X]), Λ (∑ m ∈ s, f m) = ∑ m ∈ s, Λ (f m) := by
      intro s f; classical induction s using Finset.induction_on with
      | empty => simp [Λ]
      | insert a s ha ih => rw [Finset.sum_insert ha, hΛ_add, ih, Finset.sum_insert ha]
    rw [hΛ_sum5]
    exact Finset.sum_eq_zero fun m _ => hΛ_Q7_mon m _
  -- Bézout combination from `CoverAlgebra.isCoprime_Q5_Q7`!
  obtain ⟨u, v, huv⟩ := isCoprime_Q5_Q7
  have hbez : (u.map ιL_K5 * Polynomial.C (ιL_K5 2893401)⁻¹) * Q5L +
      (v.map ιL_K5 * Polynomial.C (ιL_K5 1640558367)⁻¹ * Polynomial.C (ιL_K5 2)) * Q7L = 1 := by
    have huvL := congrArg (Polynomial.map ιL_K5) huv
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one] at huvL
    have h5i : Polynomial.C (ιL_K5 2893401)⁻¹ * Q5L = k5Params.Q5_z.map ιL_K5 := by
      rw [hQ5L_eq, ← mul_assoc, ← Polynomial.C_mul,
        inv_mul_cancel₀ ((map_ne_zero_iff _ ιL_K5.injective).mpr h2893401), Polynomial.C_1, one_mul]
    have h7i : Polynomial.C (ιL_K5 1640558367)⁻¹ * Polynomial.C (ιL_K5 2) * Q7L = k5Params.Q7_z.map ιL_K5 := by
      rw [mul_assoc, hQ7L_eq, ← mul_assoc, ← Polynomial.C_mul,
        inv_mul_cancel₀ ((map_ne_zero_iff _ ιL_K5.injective).mpr h1640), Polynomial.C_1, one_mul]
    linear_combination huvL + u.map ιL_K5 * h5i + v.map ιL_K5 * h7i
  have hΔ_zero : Δ_ext k.val = 0 := by
    have h1 : Polynomial.C (1 : CoverL) * Polynomial.X ^ k.val =
        Q5L * (Polynomial.X ^ k.val * (u.map ιL_K5 * Polynomial.C (ιL_K5 2893401)⁻¹)) +
        Q7L * (Polynomial.X ^ k.val * (v.map ιL_K5 * Polynomial.C (ιL_K5 1640558367)⁻¹ * Polynomial.C (ιL_K5 2))) := by
      rw [Polynomial.C_1, one_mul]
      linear_combination -Polynomial.X ^ k.val * hbez
    have hΛ1 := congrArg Λ h1
    rw [hΛ_C_mul_X, one_mul, hΛ_add, hΛ_Q5, hΛ_Q7, add_zero] at hΛ1
    exact hΛ1
  have hTk_eq : T_pol k.val = ιL_K5 (W_K5 k) := sub_eq_zero.mp (hΔ_eq k ▸ hΔ_zero)
  -- Rescale from `(Q5L, Q7L)` back to `(k5Params.Q5_z, k5Params.Q7_z)`!
  have hscale : ∑ r ∈ RQ5, r ^ k.val / ((k5Params.Q7_z.map ιL_K5).eval r * (k5Params.Q5_z.map ιL_K5).derivative.eval r) =
      ιL_K5 (((sc5_den * sc7_den : ℤ) : K5) / ((sc5_num * sc7_num : ℤ) : K5)) * T_pol k.val := by
    simp only [T_pol, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r hr
    have hQ5d : Q5L.derivative.eval r = ιL_K5 2893401 * (k5Params.Q5_z.map ιL_K5).derivative.eval r := by
      rw [hQ5L_eq, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
    have hQ7e : ιL_K5 2 * Q7L.eval r = ιL_K5 1640558367 * (k5Params.Q7_z.map ιL_K5).eval r := by
      have h := congrArg (fun p : CoverL[X] => p.eval r) hQ7L_eq
      simpa only [Polynomial.eval_mul, Polynomial.eval_C] using h
    have hq5d_ne : (k5Params.Q5_z.map ιL_K5).derivative.eval r ≠ 0 := by
      have h := hdQ5_ne_r r hr; rw [hQ5d] at h; exact right_ne_zero_of_mul h
    have hq7e_ne : (k5Params.Q7_z.map ιL_K5).eval r ≠ 0 :=
      eval_ne_zero_of_isCoprime isCoprime_Q5_Q7 (mem_RQ5_iff.mp hr)
    have hq7L_ne := hQ7_ne_r r hr
    have h2L : (ιL_K5 2 : CoverL) ≠ 0 := (map_ne_zero_iff _ ιL_K5.injective).mpr h2
    have h5L : (ιL_K5 2893401 : CoverL) ≠ 0 := (map_ne_zero_iff _ ιL_K5.injective).mpr h2893401
    have h7L : (ιL_K5 1640558367 : CoverL) ≠ 0 := (map_ne_zero_iff _ ιL_K5.injective).mpr h1640
    have hsc : ιL_K5 (((sc5_den * sc7_den : ℤ) : K5) / ((sc5_num * sc7_num : ℤ) : K5)) =
        ιL_K5 2893401 * ιL_K5 1640558367 / ιL_K5 2 := by
      simp only [sc5_num, sc5_den, sc7_num, sc7_den, map_div₀, map_mul, map_ofNat,
        Int.cast_mul, Int.cast_ofNat, one_mul]
    rw [hsc, hQ5d]
    have hq7_div : Q7L.eval r = ιL_K5 1640558367 * (k5Params.Q7_z.map ιL_K5).eval r / ιL_K5 2 := by
      rw [eq_div_iff h2L, _root_.mul_comm, hQ7e]
    rw [hq7_div]
    field_simp [hq5d_ne, hq7e_ne, h2L, h5L, h7L]
  rw [hscale, hTk_eq, ← map_mul, W_K5_scaled]


end SymmetricSexticResidual.LocalResidueQ5

open scoped BigOperators in
theorem solution (k : Fin 13) :
    ∑ r ∈ SymmetricSexticResidual.CoverResidue.RQ5,
      r ^ k.val /
        ((SymmetricSexticResidual.CoverAlgebra.k5Params.Q7_z.map
            SymmetricSexticResidual.CoverResidue.ιL_K5).eval r *
          (SymmetricSexticResidual.CoverAlgebra.k5Params.Q5_z.map
            SymmetricSexticResidual.CoverResidue.ιL_K5).derivative.eval r) =
      SymmetricSexticResidual.CoverResidue.ιL_K5
        (SymmetricSexticResidual.LocalResidueQ5.W_K5_scaled k) :=
  SymmetricSexticResidual.LocalResidueQ5.sum_RQ5_power_eq_W_k k
