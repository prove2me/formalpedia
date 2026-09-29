-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/93877e9f-e333-5540-8f67-030399545ddb

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_LocalGL2_iwasawa_decomposition_diag
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow.LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.higherUnitsAt TateLocal.one_mem_higherUnitsAt"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "LocalGL2 diagonal2 diagonal2_coe diagonal2_mul upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff"
namespace PSConductorBound
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem idealBound_pow (b : ℕ) :
    AdelicLevel.idealBound (𝓞 ℚ) (p.asIdeal ^ b) p = WithZero.exp (-(b : ℤ)) := by
  classical
  rw [AdelicLevel.idealBound_of_ne_bot (pow_ne_zero b p.ne_bot), Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr p.ne_bot) (Associates.irreducible_mk.mpr p.irreducible),
    Associates.count_self (Associates.irreducible_mk.mpr p.irreducible), mul_one]

theorem valued_of_mem_higherUnitsAt {b : ℕ} {u : (F)ˣ} (hu : u ∈ higherUnitsAt ℚ p b) :
    Valued.v (u : F) = 1 ∧ Valued.v ((u : F) - 1) ≤ WithZero.exp (-(b : ℤ)) := by
  obtain ⟨hval, hball⟩ := hu
  refine ⟨hval, ?_⟩
  rcases hball with hb | hle
  · subst hb
    simp only [CharP.cast_eq_zero, neg_zero, WithZero.exp_zero]
    calc Valued.v ((u : F) - 1) ≤ max (Valued.v (u : F)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ = 1 := by rw [hval, map_one, max_self]
  · exact hle

theorem inv_mem_higherUnitsAt {b : ℕ} {u : (F)ˣ} (hu : u ∈ higherUnitsAt ℚ p b) :
    u⁻¹ ∈ higherUnitsAt ℚ p b := by
  obtain ⟨hval, hball⟩ := hu
  have hval' : Valued.v ((u⁻¹ : (F)ˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
  refine ⟨hval', ?_⟩
  rcases hball with hb | hle
  · exact Or.inl hb
  · right
    have h : ((u⁻¹ : (F)ˣ) : F) - 1 = -(((u⁻¹ : (F)ˣ) : F) * ((u : F) - 1)) := by
      rw [mul_sub, mul_one, Units.inv_mul, neg_sub]
    rw [h, Valuation.map_neg, map_mul, hval', one_mul]
    exact hle

theorem valued_le_one_of_mem_integralSubgroup {k : G}
    (hk : k ∈ LocalGL2.integralSubgroup O F) (i j : Fin 2) :
    Valued.v ((k : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1 ∧
      Valued.v (((k⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1 := by
  obtain ⟨y, rfl⟩ := hk
  constructor
  · change Valued.v (((y : Matrix (Fin 2) (Fin 2) O) i j : O) : F) ≤ 1
    exact ((y : Matrix (Fin 2) (Fin 2) O) i j).2
  · rw [← map_inv]
    change Valued.v ((((y⁻¹ : GL (Fin 2) O) : Matrix (Fin 2) (Fin 2) O) i j : O) : F) ≤ 1
    exact (((y⁻¹ : GL (Fin 2) O) : Matrix (Fin 2) (Fin 2) O) i j).2

theorem mem_integers_of_mem_integralSubgroup {k : G}
    (hk : k ∈ LocalGL2.integralSubgroup O F) (i j : Fin 2) :
    (k : Matrix (Fin 2) (Fin 2) F) i j ∈ HeightOneSpectrum.adicCompletionIntegers ℚ p ∧
      ((k⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) i j ∈ HeightOneSpectrum.adicCompletionIntegers ℚ p := by
  have h := valued_le_one_of_mem_integralSubgroup p hk i j
  exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h.1,
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h.2⟩

theorem conj_entry_sub (k : G) (d : Fin 2 → (F)ˣ) (i j : Fin 2) :
    ((k⁻¹ * diagonal2 p d * k : G) : Matrix (Fin 2) (Fin 2) F) i j - (1 : Matrix (Fin 2) (Fin 2) F) i j =
      ∑ a : Fin 2, ((k⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) i a * (((d a : F) - 1) *
        (k : Matrix (Fin 2) (Fin 2) F) a j) := by
  have hone : (1 : Matrix (Fin 2) (Fin 2) F) i j =
      ∑ a : Fin 2, ((k⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) i a * (k : Matrix (Fin 2) (Fin 2) F) a j := by
    have h : ((k⁻¹ * k : G) : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [inv_mul_cancel]; rfl
    rw [← h, Units.val_mul, Matrix.mul_apply]
  have hprod : ((k⁻¹ * diagonal2 p d * k : G) : Matrix (Fin 2) (Fin 2) F) i j =
      ∑ a : Fin 2, ((k⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) i a * ((d a : F) *
        (k : Matrix (Fin 2) (Fin 2) F) a j) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [Matrix.mul_apply, diagonal2_coe]
    rw [Finset.sum_eq_single a]
    · rw [Matrix.diagonal_apply_eq]
    · intro c _ hca
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hca), zero_mul]
    · intro h; exact absurd (Finset.mem_univ a) h
  rw [hprod, hone, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem isLocalLevelOne_conj {b : ℕ} {k : G} (hk : k ∈ LocalGL2.integralSubgroup O F)
    (d : Fin 2 → (F)ˣ) (hd : ∀ a, Valued.v ((d a : F) - 1) ≤ WithZero.exp (-(b : ℤ))) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b)
      ((k⁻¹ * diagonal2 p d * k : G) : Matrix (Fin 2) (Fin 2) F) := by
  set M : Matrix (Fin 2) (Fin 2) F := ((k⁻¹ * diagonal2 p d * k : G) : Matrix (Fin 2) (Fin 2) F) with hM

  have key : ∀ i j : Fin 2, Valued.v (M i j - (1 : Matrix (Fin 2) (Fin 2) F) i j) ≤ WithZero.exp (-(b : ℤ)) := by
    intro i j
    rw [hM, conj_entry_sub]
    refine Valuation.map_sum_le _ fun a _ => ?_
    have hk1 := (valued_le_one_of_mem_integralSubgroup p hk a j).1
    have hk2 := (valued_le_one_of_mem_integralSubgroup p hk i a).2
    rw [map_mul, map_mul]
    calc Valued.v (((k⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) i a) *
          (Valued.v ((d a : F) - 1) * Valued.v ((k : Matrix (Fin 2) (Fin 2) F) a j))
        ≤ 1 * (WithZero.exp (-(b : ℤ)) * 1) := mul_le_mul' hk2 (mul_le_mul' (hd a) hk1)
      _ = WithZero.exp (-(b : ℤ)) := by rw [one_mul, mul_one]
  have hexp_le : WithZero.exp (-(b : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  refine ⟨fun i j => ?_, ?_, ?_⟩
  ·
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h := key i j
    have hδ : Valued.v ((1 : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1 := by
      rcases eq_or_ne i j with rfl | hij
      · rw [Matrix.one_apply_eq, map_one]
      · rw [Matrix.one_apply_ne hij, map_zero]; exact zero_le'
    calc Valued.v (M i j) = Valued.v ((M i j - (1 : Matrix (Fin 2) (Fin 2) F) i j) +
          (1 : Matrix (Fin 2) (Fin 2) F) i j) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (M i j - (1 : Matrix (Fin 2) (Fin 2) F) i j))
          (Valued.v ((1 : Matrix (Fin 2) (Fin 2) F) i j)) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le (h.trans hexp_le) hδ
  ·
    rw [idealBound_pow]
    have h := key 1 0
    rwa [Matrix.one_apply_ne (by decide), sub_zero] at h
  ·
    rw [idealBound_pow]
    have h := key 1 1
    rwa [Matrix.one_apply_eq] at h

theorem conj_mem_localLevelOne {b : ℕ} {k : G} (hk : k ∈ LocalGL2.integralSubgroup O F)
    (d : Fin 2 → (F)ˣ) (hd : ∀ a, d a ∈ higherUnitsAt ℚ p b) :
    k⁻¹ * diagonal2 p d * k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  refine ⟨isLocalLevelOne_conj p hk d fun a => (valued_of_mem_higherUnitsAt p (hd a)).2, ?_⟩
  have hinv : (k⁻¹ * diagonal2 p d * k)⁻¹ = k⁻¹ * diagonal2 p d⁻¹ * k := by
    have hdd : diagonal2 p d⁻¹ = (diagonal2 p d)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← diagonal2_mul, inv_mul_cancel]
      rfl
    rw [hdd, mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
  rw [hinv]
  exact isLocalLevelOne_conj p hk d⁻¹ fun a =>
    (valued_of_mem_higherUnitsAt p (inv_mem_higherUnitsAt p (hd a))).2

theorem coe_upperUnipotent2_mul_diagonal2 (z : F) (a₁ a₂ : (F)ˣ) :
    ((upperUnipotent2 p z * diagonal2 p ![a₁, a₂] : G) : Matrix (Fin 2) (Fin 2) F) =
      !![1, z; 0, 1] * !![(a₁ : F), 0; 0, (a₂ : F)] := by
  rw [Units.val_mul, upperUnipotent2_coe, diagonal2_coe]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_apply_ne_zero_of_mem_integralSubgroup {χ : Fin 2 → ((F)ˣ →* ℂˣ)} {f : G → ℂ}
    (hf : f ∈ principalSeries2 p χ) (hf0 : f ≠ 0) :
    ∃ k : G, k ∈ LocalGL2.integralSubgroup O F ∧ f k ≠ 0 := by
  obtain ⟨_, hN, hT⟩ := mem_principalSeries2_iff.mp hf
  obtain ⟨g₀, hg₀⟩ : ∃ g, f g ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (funext h)
  obtain ⟨z, a₁, a₂, k, hk, hg⟩ :=
    LocalGL2.iwasawa_decomposition_diag (HeightOneSpectrum.adicCompletionIntegers ℚ p)
      (HeightOneSpectrum.adicCompletion ℚ p) g₀
  have hg' : g₀ = upperUnipotent2 p z * diagonal2 p ![a₁, a₂] * k := by
    refine Units.ext ?_
    rw [hg, Units.val_mul, coe_upperUnipotent2_mul_diagonal2]
  refine ⟨k, hk, fun hk0 => hg₀ ?_⟩
  rw [hg', mul_assoc, hN, hT, hk0, mul_zero]

theorem norm_eq_one_of_valued_eq_one {u : F} (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, hu, map_one, NNReal.coe_one]

theorem torusChar2_mulSingle (χ : Fin 2 → ((F)ˣ →* ℂˣ)) (i : Fin 2) (u : (F)ˣ) :
    torusChar2 p χ (Pi.mulSingle i u) = ((χ i u : ℂˣ) : ℂ) := by
  unfold torusChar2
  rw [Finset.prod_eq_single i]
  · rw [Pi.mulSingle_eq_same]
  · intro j _ hji
    rw [Pi.mulSingle_eq_of_ne hji, map_one, Units.val_one]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem halfModulus2_mulSingle (i : Fin 2) {u : (F)ˣ} (hu : Valued.v (u : F) = 1) :
    halfModulus2 p (Pi.mulSingle i u) = 1 := by
  have hn : ‖((Pi.mulSingle i u : Fin 2 → (F)ˣ) 0 : F)‖ = 1 ∧
      ‖((Pi.mulSingle i u : Fin 2 → (F)ˣ) 1 : F)‖ = 1 := by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.mulSingle_eq_same, ne_eq, one_ne_zero,
        not_false_eq_true, Pi.mulSingle_eq_of_ne, Units.val_one, norm_one, and_true]
      exact norm_eq_one_of_valued_eq_one p hu
    · simp only [Fin.mk_one, Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true,
        Pi.mulSingle_eq_of_ne, Units.val_one, norm_one, Pi.mulSingle_eq_same, true_and]
      exact norm_eq_one_of_valued_eq_one p hu
  unfold halfModulus2
  rw [hn.1, hn.2, div_one, Real.sqrt_one, Complex.ofReal_one]

end LanglandsTunnell.CubicInduction.PSConductorBound

end

open LanglandsTunnell.CubicInduction.PSConductorBound in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ) (hf0 : f ≠ 0)
    (hfK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b),
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g) :
    ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, χ i u = 1 := by
  obtain ⟨_, _, hT⟩ := mem_principalSeries2_iff.mp hf
  obtain ⟨k, hk, hfk⟩ := exists_apply_ne_zero_of_mem_integralSubgroup p hf hf0
  intro i u hu
  have hval : Valued.v (u : p.adicCompletion ℚ) = 1 := (valued_of_mem_higherUnitsAt p hu).1

  set d : Fin 2 → (p.adicCompletion ℚ)ˣ := Pi.mulSingle i u with hd
  have hdmem : ∀ a, d a ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b := by
    intro a
    rcases eq_or_ne a i with rfl | hai
    · rw [hd, Pi.mulSingle_eq_same]; exact hu
    · rw [hd, Pi.mulSingle_eq_of_ne hai]; exact LanglandsTunnell.TateLocal.one_mem_higherUnitsAt ℚ p b
  have hmem := conj_mem_localLevelOne p hk d hdmem

  have h1 : f (diagonal2 p d * k) = f k := by
    have := hfK _ hmem k
    rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at this

  have h2 : f (diagonal2 p d * k) = ((χ i u : ℂˣ) : ℂ) * f k := by
    rw [hT d k, hd, torusChar2_mulSingle, halfModulus2_mulSingle p i hval, mul_one]
  have h3 : ((χ i u : ℂˣ) : ℂ) = 1 := by
    have h := h1.symm.trans h2
    have h' : (((χ i u : ℂˣ) : ℂ) - 1) * f k = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact sub_eq_zero.mp h''
    · exact absurd h'' hfk
  exact Units.val_eq_one.mp h3

end S_LanglandsTunnell_CubicInduction_forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow (solution)
