-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_principalSeries2_apply_one_eq_zero_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/17291cac-5fa7-515c-8f02-d431725eaa86

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_principalSeries2_apply_one_eq_zero_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

noncomputable section

namespace WsF
namespace PSKit

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => p.adicCompletion ℚ
local notation "G" => GL (Fin 2) (p.adicCompletion ℚ)

variable (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))

set_option quotPrecheck false in
local notation "PS" => ↥(principalSeries2 p θ)
local notation "ρ" => principalSeries2Rep θ

def prof (f : PS) (x : F) : ℂ := (f : G → ℂ) (antidiagonal2 p * upperUnipotent2 p x)

theorem prof_def (f : PS) (x : F) : prof θ f x = (f : G → ℂ) (antidiagonal2 p * upperUnipotent2 p x) := rfl

theorem rep_apply_coe (g h : G) (f : PS) : ((ρ g f : PS) : G → ℂ) h = (f : G → ℂ) (h * g) := rfl
theorem coe_sub' (f g : PS) (h : G) : ((f - g : PS) : G → ℂ) h = (f : G → ℂ) h - (g : G → ℂ) h := rfl
theorem coe_smul' (c : ℂ) (f : PS) (h : G) : ((c • f : PS) : G → ℂ) h = c * (f : G → ℂ) h := rfl

theorem apply_upperUnipotent2_mul (f : PS) (x : F) (g : G) :
    (f : G → ℂ) (upperUnipotent2 p x * g) = (f : G → ℂ) g :=
  (mem_principalSeries2_iff.mp f.2).2.1 x g

theorem apply_diagonal2_mul (f : PS) (a : Fin 2 → Fˣ) (g : G) :
    (f : G → ℂ) (diagonal2 p a * g) = torusChar2 p θ a * halfModulus2 p a * (f : G → ℂ) g :=
  (mem_principalSeries2_iff.mp f.2).2.2 a g

theorem antidiagonal2_upperUnipotent2_diagonal2 (x : F) (a : Fin 2 → Fˣ) :
    antidiagonal2 p * upperUnipotent2 p x * diagonal2 p a =
      diagonal2 p ![a 1, a 0] * (antidiagonal2 p * upperUnipotent2 p (((a 0)⁻¹ : Fˣ) * a 1 * x)) := by
  apply Units.ext
  simp only [Units.val_mul, antidiagonal2_coe, upperUnipotent2_coe, diagonal2_coe]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (a 0).ne_zero, one_mul, mul_comm]

theorem prof_rep_upperUnipotent2 (f : PS) (s x : F) : prof θ (ρ (upperUnipotent2 p s) f) x = prof θ f (x + s) := by
  simp only [prof, rep_apply_coe, mul_assoc, upperUnipotent2_mul]

theorem prof_rep_diagonal2 (f : PS) (a : Fin 2 → Fˣ) (x : F) :
    prof θ (ρ (diagonal2 p a) f) x =
      torusChar2 p θ ![a 1, a 0] * halfModulus2 p ![a 1, a 0] * prof θ f (((a 0)⁻¹ : Fˣ) * a 1 * x) := by
  simp only [prof, rep_apply_coe]
  rw [antidiagonal2_upperUnipotent2_diagonal2, apply_diagonal2_mul]

theorem prof_smul (c : ℂ) (f : PS) (x : F) : prof θ (c • f) x = c * prof θ f x := rfl

theorem apply_one_rep (f : PS) (g : G) : ((ρ g f : PS) : G → ℂ) 1 = (f : G → ℂ) g := by
  rw [rep_apply_coe, one_mul]

theorem apply_upperUnipotent2 (f : PS) (x : F) : (f : G → ℂ) (upperUnipotent2 p x) = (f : G → ℂ) 1 := by
  rw [← mul_one (upperUnipotent2 p x), apply_upperUnipotent2_mul]

theorem apply_diagonal2 (f : PS) (a : Fin 2 → Fˣ) :
    (f : G → ℂ) (diagonal2 p a) = torusChar2 p θ a * halfModulus2 p a * (f : G → ℂ) 1 := by
  rw [← mul_one (diagonal2 p a), apply_diagonal2_mul]

theorem torusChar2_mul_halfModulus2_ne_zero (a : Fin 2 → Fˣ) : torusChar2 p θ a * halfModulus2 p a ≠ 0 :=
  mul_ne_zero (by simp only [torusChar2]; exact Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero _)
    (halfModulus2_ne_zero p a)

theorem exp_mul_le_exp_iff (a b : ℤ) (y : WithZero (Multiplicative ℤ)) :
    WithZero.exp a * y ≤ WithZero.exp b ↔ y ≤ WithZero.exp (b - a) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, y = WithZero.exp k := ⟨WithZero.log y, (WithZero.exp_log hy).symm⟩
    rw [← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]
    omega

theorem isLocallyConstant_of_higherUnitsAt (χ : Fˣ →* ℂˣ) (c : ℕ)
    (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p c, χ u = 1) : IsLocallyConstant χ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u₀

  set ϖ : F := ((uniformizerUnit ℚ p : Fˣ) : F) with hϖ
  have hvϖc : Valued.v (ϖ ^ c) = WithZero.exp (-(c : ℤ)) := by
    rw [map_pow, hϖ, valued_uniformizerUnit, ← WithZero.exp_nsmul]; simp
  have hϖc0 : ϖ ^ c ≠ 0 := pow_ne_zero _ (uniformizerUnit ℚ p).ne_zero
  have hcont : Continuous fun u : Fˣ => ‖(u : F) * ((u₀ : F))⁻¹ - 1‖ :=
    ((Units.continuous_val.mul continuous_const).sub continuous_const).norm
  have hopen : IsOpen {u : Fˣ | ‖(u : F) * ((u₀ : F))⁻¹ - 1‖ < ‖ϖ ^ c‖} :=
    isOpen_lt hcont continuous_const
  have hmem : u₀ ∈ {u : Fˣ | ‖(u : F) * ((u₀ : F))⁻¹ - 1‖ < ‖ϖ ^ c‖} := by
    simp only [Set.mem_setOf_eq, mul_inv_cancel₀ u₀.ne_zero, sub_self, norm_zero]
    exact norm_pos_iff.mpr hϖc0
  filter_upwards [hopen.mem_nhds hmem] with u hu
  have hv : Valued.v ((u : F) * ((u₀ : F))⁻¹ - 1) < WithZero.exp (-(c : ℤ)) := by
    rw [← hvϖc]; exact Valued.toNormedField.norm_lt_iff.mp hu
  have hw : u * u₀⁻¹ ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p c := by
    have hlt1 : Valued.v ((u : F) * ((u₀ : F))⁻¹ - 1) < 1 :=
      hv.trans_le (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_inv_eq_inv_val]
      have := Valuation.map_one_add_of_lt Valued.v hlt1
      rwa [add_sub_cancel] at this
    · rcases Nat.eq_zero_or_pos c with h0 | hpos
      · exact Or.inl h0
      · right; rw [Units.val_mul, Units.val_inv_eq_inv_val]; exact hv.le
  have := hχ _ hw
  rw [map_mul, map_inv, mul_inv_eq_one] at this
  exact this

end WsF.PSKit

end

noncomputable section

namespace WsF
namespace W5b2

open WsF.PSKit

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => p.adicCompletion ℚ
local notation "G" => GL (Fin 2) (p.adicCompletion ℚ)

variable (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))

set_option quotPrecheck false in
local notation "PS" => ↥(principalSeries2 p θ)
local notation "ρ" => principalSeries2Rep θ

theorem cornerEntry2_w0n (x : F) : cornerEntry2 p (antidiagonal2 p * upperUnipotent2 p x) = 1 := by
  simp [cornerEntry2, gl2Entry, antidiagonal2_coe, upperUnipotent2_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem gl2Entry_w0n (x : F) : gl2Entry p (antidiagonal2 p * upperUnipotent2 p x) 1 1 = x := by
  simp [gl2Entry, antidiagonal2_coe, upperUnipotent2_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem gl2Det_w0n (x : F) : gl2Det p (antidiagonal2 p * upperUnipotent2 p x) = gl2Det p (antidiagonal2 p) := by
  simp [gl2Det, antidiagonal2_coe, upperUnipotent2_coe, Matrix.det_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.det_fin_two]

theorem cellValue2_w0n (x : F) :
    cellValue2 p θ (antidiagonal2 p * upperUnipotent2 p x) = cellValue2 p θ (antidiagonal2 p) := by
  simp only [cellValue2, cornerEntry2_w0n, gl2Det_w0n, cornerEntry2_antidiagonal2]

theorem mem_cellCutoff2_w0n_iff (x : F) : antidiagonal2 p * upperUnipotent2 p x ∈ cellCutoff2 p ↔ Valued.v x ≤ 1 := by
  simp only [cellCutoff2, Set.mem_setOf_eq, cornerEntry2_w0n, gl2Entry_w0n, ne_eq, one_ne_zero, not_false_eq_true,
    div_one, true_and]

theorem cornerEntry2_one : cornerEntry2 p (1 : G) = 0 := by
  simp [cornerEntry2, gl2Entry]

theorem main (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1) :
    (∃ φ : ℤ → F → PS,
      (∀ (n : ℤ) (t : F), (φ n t : G → ℂ) 1 = 0) ∧
      (∀ (n : ℤ) (t x : F),
        (φ n t : G → ℂ) (antidiagonal2 p * upperUnipotent2 p x) =
          if Valued.v (x - t) ≤ WithZero.exp (-n) then 1 else 0)) ∧
    ∃ ψ : PS, (ψ : G → ℂ) 1 = 1 := by
  classical
  have hlc : ∀ i, IsLocallyConstant (θ i) := fun i => isLocallyConstant_of_higherUnitsAt (θ i) (c i) (hcθ i)

  let cs : PS := ⟨cellSection2 p θ, cellSection2_mem_principalSeries2 p θ hlc⟩
  set K₀ : ℂ := cellSection2 p θ (antidiagonal2 p) with hK₀
  have hK₀0 : K₀ ≠ 0 := cellSection2_antidiagonal2_ne_zero p θ
  have hK₀' : cellValue2 p θ (antidiagonal2 p) = K₀ := by
    rw [hK₀, cellSection2, Set.indicator_of_mem (antidiagonal2_mem_cellCutoff2 p)]
  have hcs_prof : ∀ x : F, prof θ cs x = if Valued.v x ≤ 1 then K₀ else 0 := by
    intro x
    show cellSection2 p θ (antidiagonal2 p * upperUnipotent2 p x) = _
    by_cases hx : Valued.v x ≤ 1
    · rw [if_pos hx, cellSection2, Set.indicator_of_mem ((mem_cellCutoff2_w0n_iff x).mpr hx), cellValue2_w0n, hK₀']
    · rw [if_neg hx, cellSection2, Set.indicator_of_notMem (fun h => hx ((mem_cellCutoff2_w0n_iff x).mp h))]
  have hcs1 : (cs : G → ℂ) 1 = 0 := by
    show cellSection2 p θ 1 = 0
    rw [cellSection2, Set.indicator_of_notMem]
    intro h
    exact h.1 cornerEntry2_one

  let φ₀ : PS := K₀⁻¹ • cs
  have hφ₀p : ∀ x : F, prof θ φ₀ x = if Valued.v x ≤ 1 then 1 else 0 := by
    intro x; show prof θ (K₀⁻¹ • cs) x = _
    rw [prof_smul, hcs_prof]; split_ifs <;> simp [hK₀0]
  have hφ₀1 : (φ₀ : G → ℂ) 1 = 0 := by show ((K₀⁻¹ • cs : PS) : G → ℂ) 1 = 0; rw [coe_smul', hcs1, mul_zero]

  let ϖ : Fˣ := uniformizerUnit ℚ p
  have hvϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit ℚ p
  let a : ℤ → (Fin 2 → Fˣ) := fun n => ![ϖ ^ n, 1]
  let κ : ℤ → ℂ := fun n => torusChar2 p θ ![(a n) 1, (a n) 0] * halfModulus2 p ![(a n) 1, (a n) 0]
  have hκ : ∀ n, κ n ≠ 0 := fun n => torusChar2_mul_halfModulus2_ne_zero θ _
  let φ : ℤ → F → PS := fun n t => ρ (upperUnipotent2 p (-t)) ((κ n)⁻¹ • ρ (diagonal2 p (a n)) φ₀)
  refine ⟨⟨φ, fun n t => ?_, fun n t x => ?_⟩, ?_⟩
  ·
    show ((ρ (upperUnipotent2 p (-t)) ((κ n)⁻¹ • ρ (diagonal2 p (a n)) φ₀) : PS) : G → ℂ) 1 = 0
    rw [apply_one_rep, apply_upperUnipotent2, coe_smul', apply_one_rep, apply_diagonal2, hφ₀1, mul_zero, mul_zero]
  ·
    show prof θ (ρ (upperUnipotent2 p (-t)) ((κ n)⁻¹ • ρ (diagonal2 p (a n)) φ₀)) x = _
    rw [prof_rep_upperUnipotent2, prof_smul, prof_rep_diagonal2, hφ₀p]
    have e : torusChar2 p θ ![(a n) 1, (a n) 0] * halfModulus2 p ![(a n) 1, (a n) 0] = κ n := rfl
    rw [← mul_assoc, ← mul_assoc]
    simp only [a, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Units.val_one, mul_one, ← sub_eq_add_neg]
    rw [show (κ n)⁻¹ * torusChar2 p θ ![1, ϖ ^ n] * halfModulus2 p ![1, ϖ ^ n] = 1 by
      rw [mul_assoc]; exact inv_mul_cancel₀ (hκ n), one_mul]
    congr 1
    rw [Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, hvϖ,
      ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_zero, exp_mul_le_exp_iff]
    congr 2
    simp only [smul_eq_mul]; ring
  ·
    refine ⟨K₀⁻¹ • ρ (antidiagonal2 p) cs, ?_⟩
    show ((K₀⁻¹ • ρ (antidiagonal2 p) cs : PS) : G → ℂ) 1 = 1
    rw [coe_smul', apply_one_rep]
    exact inv_mul_cancel₀ hK₀0

end WsF.W5b2

end

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1) :
    (∃ φ : ℤ → p.adicCompletion ℚ → ↥(principalSeries2 p θ),
      (∀ (n : ℤ) (t : p.adicCompletion ℚ), (φ n t : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) 1 = 0) ∧
      (∀ (n : ℤ) (t x : p.adicCompletion ℚ),
        (φ n t : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (antidiagonal2 p * upperUnipotent2 p x) =
          if Valued.v (x - t) ≤ WithZero.exp (-n) then 1 else 0)) ∧
    ∃ ψ : ↥(principalSeries2 p θ), (ψ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) 1 = 1 :=
  WsF.W5b2.main θ c hcθ

end S_LanglandsTunnell_CubicInduction_exists_principalSeries2_apply_one_eq_zero_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_principalSeries2_apply_one_eq_zero_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator (solution)
