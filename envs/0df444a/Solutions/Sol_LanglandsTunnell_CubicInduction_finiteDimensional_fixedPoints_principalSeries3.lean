-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.finiteDimensional_fixedPoints_principalSeries3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e770e8a3-5b94-5bb0-b086-6a1a3fbc9274

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_fixedPoints_principalSeries3

set_option autoImplicit false

open IsDedekindDomain NumberField

open Matrix Rat.HeightOneSpectrum

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 gl3Entry gl3AmbientRightTranslate gl3AmbientRightTranslate_apply localMaximalCompact3 mem_localMaximalCompact3_iff LocalGL3 exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem exists_eq_diagonal3 {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) :
    ∃ a : Fin 3 → (v.adicCompletion ℚ)ˣ, t = diagonal3 v a := by
  have hdet : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det t).ne_zero
  rw [ht, Matrix.det_diagonal] at hdet
  have hd : ∀ i, d i ≠ 0 := fun i h0 => hdet (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  refine ⟨fun i => Units.mk0 (d i) (hd i), Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
  simp only [ht, diagonal3_coe, Units.val_mk0]

private theorem eq_zero_of_forall_mem_localMaximalCompact3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (hK : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, f k = 0) : f = 0 := by
  funext g
  show f g = 0
  obtain ⟨x, y, z, t, d, k, hk, htd, rfl⟩ :=
    exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 v g
  obtain ⟨a, rfl⟩ := exists_eq_diagonal3 htd
  rw [mul_assoc, apply_upperUnipotent3_mul_of_mem_principalSeries3 hf,
    apply_diagonal3_mul_of_mem_principalSeries3 hf, hK k hk, mul_zero]

namespace LevelRepresentatives

private abbrev factPrimeOfPrimes (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

attribute [local instance] factPrimeOfPrimes

variable (v)

private theorem natCast_natGenerator_mem :
    ((natGenerator v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have h : ((natGenerator v : ℕ) : ℤ) ∈ v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) :=
    (natGenerator_dvd_iff v).mp dvd_rfl
  have hmap : (v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))).comap
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) = v.asIdeal :=
    Ideal.comap_map_of_bijective _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).bijective
  rw [← hmap, Ideal.mem_comap, map_natCast]
  exact h

private theorem intValuation_natGenerator_pow_le (n : ℕ) :
    v.intValuation (((natGenerator v : ℕ) : 𝓞 ℚ) ^ n) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [HeightOneSpectrum.intValuation_le_pow_iff_dvd, ← Ideal.span_singleton_pow]
  exact pow_dvd_pow_of_dvd (Ideal.dvd_span_singleton.mpr (natCast_natGenerator_mem v)) n

private theorem valued_sub_le_of_toZModPow_eq (n : ℕ) (x y : v.adicCompletionIntegers ℚ)
    (h : PadicInt.toZModPow n (adicCompletionIntegers.padicIntEquiv v x) =
      PadicInt.toZModPow n (adicCompletionIntegers.padicIntEquiv v y)) :
    Valued.v ((x : v.adicCompletion ℚ) - y) ≤ WithZero.exp (-(n : ℤ)) := by
  set e := adicCompletionIntegers.padicIntEquiv v with he
  have hker : e x - e y ∈ RingHom.ker (PadicInt.toZModPow (p := (primesEquiv v : ℕ)) n) := by
    rw [RingHom.mem_ker, map_sub, h, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨c, hc⟩ := hker
  have hxy : x - y = ((natGenerator v : ℕ) : v.adicCompletionIntegers ℚ) ^ n * e.symm c := by
    apply EquivLike.injective e
    rw [map_sub, map_mul, map_pow, map_natCast, e.apply_symm_apply, hc]
    rfl
  have hcoe := congrArg (fun z : v.adicCompletionIntegers ℚ => (z : v.adicCompletion ℚ)) hxy
  push_cast at hcoe
  have hpow : ((natGenerator v : ℕ) : v.adicCompletion ℚ) ^ n =
      algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (((natGenerator v : ℕ) : 𝓞 ℚ) ^ n) := by
    rw [map_pow, map_natCast]
  have hval : Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (((natGenerator v : ℕ) : 𝓞 ℚ) ^ n)) =
      v.intValuation (((natGenerator v : ℕ) : 𝓞 ℚ) ^ n) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) (v := v) _).trans
      (HeightOneSpectrum.valuation_of_algebraMap (K := ℚ) (v := v) _)
  rw [hcoe, hpow, Valuation.map_mul, hval]
  calc v.intValuation (((natGenerator v : ℕ) : 𝓞 ℚ) ^ n) * Valued.v (e.symm c : v.adicCompletion ℚ)
      ≤ WithZero.exp (-(n : ℤ)) * 1 :=
        mul_le_mul' (intValuation_natGenerator_pow_le v n) (e.symm c).2
    _ = WithZero.exp (-(n : ℤ)) := mul_one _

private theorem valued_mul_apply_le_of_right {C : WithZero (Multiplicative ℤ)}
    {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {i j : Fin 3}
    (ha : ∀ l, Valued.v (a i l) ≤ 1) (hb : ∀ l, Valued.v (b l j) ≤ C) :
    Valued.v ((a * b) i j) ≤ C := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C := fun l => by
    rw [Valuation.map_mul]
    calc Valued.v (a i l) * Valued.v (b l j) ≤ 1 * Valued.v (b l j) := mul_le_mul_left (ha l) _
      _ = Valued.v (b l j) := one_mul _
      _ ≤ C := hb l
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

private def integralEntry (k : {k : LocalGL3 v // k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v}) (i j : Fin 3) :
    v.adicCompletionIntegers ℚ :=
  ⟨gl3Entry v k.1 i j, ((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp k.2).1 i j⟩

private def levelResidue (n : ℕ) (k : {k : LocalGL3 v // k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v}) :
    Fin 3 → Fin 3 → ZMod ((primesEquiv v : ℕ) ^ n) :=
  fun i j => PadicInt.toZModPow n (adicCompletionIntegers.padicIntEquiv v (integralEntry v k i j))

private theorem valued_entry_sub_le_of_levelResidue_eq (n : ℕ)
    (k k' : {k : LocalGL3 v // k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v}) (h : levelResidue v n k = levelResidue v n k')
    (i j : Fin 3) :
    Valued.v (gl3Entry v k.1 i j - gl3Entry v k'.1 i j) ≤ WithZero.exp (-(n : ℤ)) :=
  valued_sub_le_of_toZModPow_eq v n (integralEntry v k i j) (integralEntry v k' i j)
    (by simpa [levelResidue] using congrFun (congrFun h i) j)

private theorem exists_finset_core (n : ℕ) :
    ∃ S : Finset (LocalGL3 v), (∀ s ∈ S, s ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∃ s ∈ S, ∀ i j : Fin 3,
        Valued.v (gl3Entry v (s⁻¹ * k) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ)) := by
  classical
  let rep : (Fin 3 → Fin 3 → ZMod ((primesEquiv v : ℕ) ^ n)) → LocalGL3 v := fun t =>
    if h : ∃ k : {k : LocalGL3 v // k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v}, levelResidue v n k = t then
      h.choose.1 else 1
  have hrep_mem : ∀ t, rep t ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
    intro t
    simp only [rep]
    split_ifs with h
    · exact h.choose.2
    · exact one_mem _
  have hrep_residue : ∀ k : {k : LocalGL3 v // k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v},
      levelResidue v n ⟨rep (levelResidue v n k), hrep_mem _⟩ = levelResidue v n k := by
    intro k
    have h : ∃ k' : {k : LocalGL3 v // k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v},
        levelResidue v n k' = levelResidue v n k := ⟨k, rfl⟩
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hs
    exact hrep_mem t
  · intro k hk
    refine ⟨rep (levelResidue v n ⟨k, hk⟩), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    intro i j
    set s : LocalGL3 v := rep (levelResidue v n ⟨k, hk⟩) with hs_def
    have hs : s ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := hrep_mem _
    have hsmall : ∀ l, Valued.v (((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) -
        (s : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) l j) ≤ WithZero.exp (-(n : ℤ)) := by
      intro l
      rw [Matrix.sub_apply]
      have := valued_entry_sub_le_of_levelResidue_eq v n ⟨k, hk⟩ ⟨s, hs⟩ (hrep_residue ⟨k, hk⟩).symm l j
      simpa [gl3Entry] using this
    have hinv : ∀ l, Valued.v (((s⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i l) ≤ 1 :=
      fun l => ((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hs).2 i l
    have hmat : ((s⁻¹ * k : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        ((s⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
          ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) -
            (s : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by
      rw [Matrix.mul_sub, Units.val_mul, Units.inv_mul]
    have hentry : gl3Entry v (s⁻¹ * k) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
        (((s⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
          ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) -
            (s : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) i j := by
      rw [← hmat, Matrix.sub_apply]
      rfl
    rw [hentry]
    exact valued_mul_apply_le_of_right v hinv hsmall

end LevelRepresentatives

variable (v) in

private theorem exists_finset_forall_mem_localMaximalCompact3 (n : ℕ) :
    ∃ S : Finset (LocalGL3 v), (∀ s ∈ S, s ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∃ s ∈ S, ∀ i j,
        Valued.v (gl3Entry v (s⁻¹ * k) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ)) := by
  exact LevelRepresentatives.exists_finset_core v n

private theorem finiteDimensional_of_le_principalSeries3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} (n : ℕ)
    (W : Submodule ℂ (LocalGL3 v → ℂ)) (hW : W ≤ principalSeries3 v χ)
    (hfix : ∀ f ∈ W, ∀ u : LocalGL3 v,
      (∀ i j, Valued.v (gl3Entry v u i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
        WithZero.exp (-(n : ℤ))) → gl3AmbientRightTranslate (R := ℂ) u f = f) :
    FiniteDimensional ℂ ↥W := by
  obtain ⟨S, hSK, hcov⟩ := exists_finset_forall_mem_localMaximalCompact3 v n
  refine FiniteDimensional.of_injective
    ((LinearMap.funLeft ℂ ℂ fun s : ↥S => (s : LocalGL3 v)).comp W.subtype)
    ((injective_iff_map_eq_zero _).mpr fun f hf0 => ?_)
  have hS : ∀ s ∈ S, (f : LocalGL3 v → ℂ) s = 0 := fun s hs => by
    have h := congr_fun hf0 ⟨s, hs⟩
    simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply, Submodule.coe_subtype,
      Pi.zero_apply, Subtype.coe_mk] using h
  have hK : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, (f : LocalGL3 v → ℂ) k = 0 := fun k hk => by
    obtain ⟨s, hs, hu⟩ := hcov k hk
    have h := congr_fun (hfix f f.2 (s⁻¹ * k) hu) s
    rw [gl3AmbientRightTranslate_apply, mul_inv_cancel_left] at h
    rw [h]
    exact hS s hs
  exact (Submodule.coe_eq_zero (x := f)).mp (eq_zero_of_forall_mem_localMaximalCompact3 (hW f.2) hK)

end LanglandsTunnell.CubicInduction

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_fixedPoints_principalSeries3.LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (n : ℕ) :
    FiniteDimensional ℂ ↥(principalSeries3 v χ ⊓
      ⨅ k ∈ {k : LocalGL3 v | ∀ i j : Fin 3,
          Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
            ≤ WithZero.exp (-(n : ℤ))},
        LinearMap.ker (gl3AmbientRightTranslate (R := ℂ) k - LinearMap.id)) := by
  refine finiteDimensional_of_le_principalSeries3 n _ inf_le_left fun f hf u hu => ?_
  have h := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hf.2 u) hu
  simpa [LinearMap.mem_ker, sub_eq_zero] using h

end

#print axioms solution

end S_LanglandsTunnell_CubicInduction_finiteDimensional_fixedPoints_principalSeries3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_finiteDimensional_fixedPoints_principalSeries3 (solution)
