-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_spherical_mem_principalSeries2_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c5651ca9-a091-5f74-add7-eed594abf026

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries2_of_unramified

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries2_of_unramified.LanglandsTunnell.CubicInduction"

open UnramifiedWhittaker

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "LocalGL2 diagonal2 upperUnipotent2 halfModulus2 torusChar2 principalSeries2 gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry continuous_gl2Det gl2Entry_upperUnipotent2_mul_one gl2Det_upperUnipotent2_mul gl2Entry_diagonal2_mul gl2Det_diagonal2_mul cornerEntry2 continuous_cornerEntry2 cornerEntry2_upperUnipotent2_mul cornerEntry2_diagonal2_mul gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero charExt_units_mul eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
namespace SphSection

variable (v : HeightOneSpectrum (𝓞 ℚ))

def pivot (g : LocalGL2 v) : v.adicCompletion ℚ :=
  if Valued.v (cornerEntry2 v g) ≤ Valued.v (gl2Entry v g 1 1) then gl2Entry v g 1 1 else cornerEntry2 v g

theorem pivot_ne_zero (g : LocalGL2 v) : pivot v g ≠ 0 := by
  unfold pivot
  split_ifs with h
  · intro hd
    have hc : Valued.v (cornerEntry2 v g) ≤ 0 := by rwa [hd, map_zero] at h
    have hc0 : cornerEntry2 v g = 0 := (Valuation.zero_iff _).mp (le_antisymm hc zero_le')
    exact gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero v hc0 hd
  · intro hc
    rw [hc, map_zero] at h
    exact h zero_le'

theorem v_pivot (g : LocalGL2 v) :
    Valued.v (pivot v g) = max (Valued.v (cornerEntry2 v g)) (Valued.v (gl2Entry v g 1 1)) := by
  unfold pivot
  split_ifs with h
  · rw [max_eq_right h]
  · rw [max_eq_left (le_of_not_ge h)]

def sphValue (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL2 v) : ℂ :=
  charExt (χ 0) (gl2Det v g / pivot v g) * charExt (χ 1) (pivot v g) *
    ((Real.sqrt (‖gl2Det v g / pivot v g‖ / ‖pivot v g‖) : ℝ) : ℂ)

theorem pivot_upperUnipotent2_mul (x : v.adicCompletion ℚ) (g : LocalGL2 v) :
    pivot v (upperUnipotent2 v x * g) = pivot v g := by
  simp only [pivot, cornerEntry2_upperUnipotent2_mul]
  have h11 : gl2Entry v (upperUnipotent2 v x * g) 1 1 = gl2Entry v g 1 1 :=
    gl2Entry_upperUnipotent2_mul_one v x g 1
  rw [h11]

theorem sphValue_upperUnipotent2_mul (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (x : v.adicCompletion ℚ)
    (g : LocalGL2 v) : sphValue v χ (upperUnipotent2 v x * g) = sphValue v χ g := by
  simp only [sphValue, pivot_upperUnipotent2_mul, gl2Det_upperUnipotent2_mul]

theorem pivot_diagonal2_mul (a : Fin 2 → (v.adicCompletion ℚ)ˣ) (g : LocalGL2 v) :
    pivot v (diagonal2 v a * g) = (a 1 : v.adicCompletion ℚ) * pivot v g := by
  have h1 : Valued.v (a 1 : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr (a 1).ne_zero
  have hpos : 0 < Valued.v (a 1 : v.adicCompletion ℚ) := lt_of_le_of_ne zero_le' h1.symm
  simp only [pivot, cornerEntry2_diagonal2_mul, gl2Entry_diagonal2_mul, map_mul]
  by_cases h : Valued.v (cornerEntry2 v g) ≤ Valued.v (gl2Entry v g 1 1)
  · rw [if_pos h, if_pos (mul_le_mul_right h _)]
  · rw [if_neg h, if_neg (fun h' => h (le_of_mul_le_mul_left h' hpos))]

theorem sphValue_diagonal2_mul (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 2 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL2 v) :
    sphValue v χ (diagonal2 v a * g) = torusChar2 v χ a * halfModulus2 v a * sphValue v χ g := by
  have h1 : (a 1 : v.adicCompletion ℚ) ≠ 0 := (a 1).ne_zero
  have hdet : gl2Det v (diagonal2 v a * g) / pivot v (diagonal2 v a * g)
      = (a 0 : v.adicCompletion ℚ) * (gl2Det v g / pivot v g) := by
    rw [gl2Det_diagonal2_mul, pivot_diagonal2_mul,
      show (a 0 : v.adicCompletion ℚ) * a 1 * gl2Det v g = (a 1 : v.adicCompletion ℚ) * (a 0 * gl2Det v g) by ring,
      mul_div_mul_left _ _ h1, mul_div_assoc]
  have hmod : ‖(a 0 : v.adicCompletion ℚ) * (gl2Det v g / pivot v g)‖ /
        ‖(a 1 : v.adicCompletion ℚ) * pivot v g‖
      = ‖(a 0 : v.adicCompletion ℚ)‖ / ‖(a 1 : v.adicCompletion ℚ)‖ *
        (‖gl2Det v g / pivot v g‖ / ‖pivot v g‖) := by
    rw [norm_mul, norm_mul]
    ring
  rw [sphValue, sphValue, hdet, pivot_diagonal2_mul, hmod, charExt_units_mul, charExt_units_mul,
    Real.sqrt_mul (div_nonneg (norm_nonneg _) (norm_nonneg _))]
  simp only [torusChar2, halfModulus2, Fin.prod_univ_two]
  push_cast
  ring

theorem entries_le_one_of_mem {k : LocalGL2 v} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    (∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) ∧
    (∀ i j, Valued.v (((k⁻¹ : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) := by
  rw [AdelicDock.mem_localLevelOne_iff] at hk
  obtain ⟨⟨h1, -, -⟩, ⟨h2, -, -⟩⟩ := hk
  exact ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp (h1 i j),
    fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp (h2 i j)⟩

theorem max_bottom_mul_le (g k : LocalGL2 v)
    (hk : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) :
    max (Valued.v (cornerEntry2 v (g * k))) (Valued.v (gl2Entry v (g * k) 1 1)) ≤
      max (Valued.v (cornerEntry2 v g)) (Valued.v (gl2Entry v g 1 1)) := by
  have hrow : ∀ j : Fin 2, gl2Entry v (g * k) 1 j =
      gl2Entry v g 1 0 * (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 j +
      gl2Entry v g 1 1 * (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 j := fun j => by
    simp [gl2Entry, Matrix.mul_apply, Fin.sum_univ_two]
  have hbd : ∀ j : Fin 2, Valued.v (gl2Entry v (g * k) 1 j) ≤
      max (Valued.v (cornerEntry2 v g)) (Valued.v (gl2Entry v g 1 1)) := fun j => by
    rw [hrow j]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [map_mul]
      exact ((mul_le_mul_right (hk 0 j) _).trans_eq (mul_one _)).trans (le_max_left _ _)
    · rw [map_mul]
      exact ((mul_le_mul_right (hk 1 j) _).trans_eq (mul_one _)).trans (le_max_right _ _)
  exact max_le (hbd 0) (hbd 1)

theorem v_pivot_mul_eq {g k : LocalGL2 v} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    Valued.v (pivot v (g * k)) = Valued.v (pivot v g) := by
  obtain ⟨h1, h2⟩ := entries_le_one_of_mem v hk
  rw [v_pivot, v_pivot]
  refine le_antisymm (max_bottom_mul_le v g k h1) ?_
  have := max_bottom_mul_le v (g * k) k⁻¹ h2
  rwa [mul_inv_cancel_right] at this

theorem v_det_eq_one_of_mem {k : LocalGL2 v} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    Valued.v (gl2Det v k) = 1 := by
  obtain ⟨h1, h2⟩ := entries_le_one_of_mem v hk
  have hle : ∀ (m : LocalGL2 v), (∀ i j, Valued.v ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      Valued.v (gl2Det v m) ≤ 1 := fun m hm => by
    rw [gl2Det_eq]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul]
    · exact mul_le_one' (hm 0 0) (hm 1 1)
    · exact mul_le_one' (hm 0 1) (hm 1 0)
  have hk1 := hle k h1
  have hk2 := hle k⁻¹ h2
  have hprod : gl2Det v k * gl2Det v k⁻¹ = 1 := by
    simp only [gl2Det, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hv : Valued.v (gl2Det v k) * Valued.v (gl2Det v k⁻¹) = 1 := by rw [← map_mul, hprod, map_one]
  refine le_antisymm hk1 ?_
  by_contra hlt
  push Not at hlt
  have : Valued.v (gl2Det v k) * Valued.v (gl2Det v k⁻¹) < 1 := mul_lt_one_of_lt_of_le hlt hk2
  rw [hv] at this
  exact lt_irrefl _ this

theorem charExt_eq_of_v_eq (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → χ u = 1)
    {x y : v.adicCompletion ℚ} (hx : x ≠ 0) (hy : y ≠ 0) (h : Valued.v x = Valued.v y) :
    charExt χ x = charExt χ y := by
  have hu : Valued.v (x / y) = 1 := by rw [map_div₀, h, div_self ((Valuation.ne_zero_iff _).mpr hy)]
  have hxy : ((Units.mk0 (x / y) (div_ne_zero hx hy) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y = x := by
    rw [Units.val_mk0, div_mul_cancel₀ _ hy]
  have := charExt_units_mul v χ (Units.mk0 (x / y) (div_ne_zero hx hy)) y
  rw [hxy, hχ _ (by rw [Units.val_mk0]; exact hu), Units.val_one, one_mul] at this
  exact this

theorem sphValue_mul_of_mem (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → χ i u = 1)
    (g k : LocalGL2 v) (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    sphValue v χ (g * k) = sphValue v χ g := by
  have hp := v_pivot_mul_eq v (g := g) hk
  have hdet : Valued.v (gl2Det v (g * k)) = Valued.v (gl2Det v g) := by
    rw [show gl2Det v (g * k) = gl2Det v g * gl2Det v k by simp [gl2Det, Matrix.det_mul], map_mul,
      v_det_eq_one_of_mem v hk, mul_one]
  have hq : Valued.v (gl2Det v (g * k) / pivot v (g * k)) = Valued.v (gl2Det v g / pivot v g) := by
    rw [map_div₀, map_div₀, hp, hdet]
  have hn1 : ‖pivot v (g * k)‖ = ‖pivot v g‖ := by
    rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, hp]
  have hn0 : ‖gl2Det v (g * k) / pivot v (g * k)‖ = ‖gl2Det v g / pivot v g‖ := by
    rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, hq]
  have e0 := charExt_eq_of_v_eq v (χ 0) (hχ 0)
    (div_ne_zero (gl2Det_ne_zero v _) (pivot_ne_zero v _)) (div_ne_zero (gl2Det_ne_zero v _) (pivot_ne_zero v _)) hq
  have e1 := charExt_eq_of_v_eq v (χ 1) (hχ 1) (pivot_ne_zero v _) (pivot_ne_zero v _) hp
  simp only [sphValue, e0, e1, hn0, hn1]

theorem isLocallyConstant_of_unramified (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → χ u = 1) :
    IsLocallyConstant χ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u₀
  have hev : ∀ᶠ u : (v.adicCompletion ℚ)ˣ in nhds u₀, Valued.v (u : v.adicCompletion ℚ) = Valued.v (u₀ : v.adicCompletion ℚ) :=
    (Units.continuous_val.tendsto u₀).eventually (eventually_valued_eq v u₀.ne_zero)
  filter_upwards [hev] with u hu
  have h1 : Valued.v ((u * u₀⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hu,
      mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr u₀.ne_zero)]
  have := hχ _ h1
  rw [map_mul, map_inv, mul_inv_eq_one] at this
  exact this

theorem isLocallyConstant_sphValue (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → χ i u = 1) :
    IsLocallyConstant (sphValue v χ) := by
  have hχ' : ∀ i, IsLocallyConstant (χ i) := fun i => isLocallyConstant_of_unramified v (χ i) (hχ i)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g

  have hcA : ContinuousAt (cornerEntry2 v) g := (continuous_cornerEntry2 v).continuousAt
  have hdA : ContinuousAt (fun h => gl2Entry v h 1 1) g := (continuous_gl2Entry v 1 1).continuousAt
  obtain ⟨p, hpcont, hpg, hev⟩ : ∃ p : LocalGL2 v → v.adicCompletion ℚ, Continuous p ∧ p g = pivot v g ∧
      ∀ᶠ h in nhds g, pivot v h = p h := by
    by_cases hle : Valued.v (cornerEntry2 v g) ≤ Valued.v (gl2Entry v g 1 1)
    · refine ⟨fun h => gl2Entry v h 1 1, continuous_gl2Entry v 1 1, by simp [pivot, hle], ?_⟩
      have hd0 : gl2Entry v g 1 1 ≠ 0 := by
        have := pivot_ne_zero v g; simp only [pivot, if_pos hle] at this; exact this
      have h2 : ∀ᶠ h in nhds g, Valued.v (gl2Entry v h 1 1) = Valued.v (gl2Entry v g 1 1) :=
        hdA.eventually (eventually_valued_eq v hd0)
      by_cases hc0 : cornerEntry2 v g = 0
      · have h1 : ∀ᶠ h in nhds g, Valued.v (cornerEntry2 v h) < Valued.v (gl2Entry v g 1 1) := by
          have ht : Filter.Tendsto (cornerEntry2 v) (nhds g) (nhds 0) := by simpa [hc0] using hcA.tendsto
          exact ht.eventually (eventually_valued_lt v hd0)
        filter_upwards [h1, h2] with h hh1 hh2
        simp only [pivot, if_pos (hh2 ▸ hh1.le)]
      · have h1 : ∀ᶠ h in nhds g, Valued.v (cornerEntry2 v h) = Valued.v (cornerEntry2 v g) :=
          hcA.eventually (eventually_valued_eq v hc0)
        filter_upwards [h1, h2] with h hh1 hh2
        have : Valued.v (cornerEntry2 v h) ≤ Valued.v (gl2Entry v h 1 1) := by rw [hh1, hh2]; exact hle
        simp only [pivot, if_pos this]
    · refine ⟨cornerEntry2 v, continuous_cornerEntry2 v, by simp [pivot, hle], ?_⟩
      have hc0 : cornerEntry2 v g ≠ 0 := by
        have := pivot_ne_zero v g; simp only [pivot, if_neg hle] at this; exact this
      have h1 : ∀ᶠ h in nhds g, Valued.v (cornerEntry2 v h) = Valued.v (cornerEntry2 v g) :=
        hcA.eventually (eventually_valued_eq v hc0)
      by_cases hd0 : gl2Entry v g 1 1 = 0
      · have h2 : ∀ᶠ h in nhds g, Valued.v (gl2Entry v h 1 1) < Valued.v (cornerEntry2 v g) := by
          have ht : Filter.Tendsto (fun h => gl2Entry v h 1 1) (nhds g) (nhds 0) := by simpa [hd0] using hdA.tendsto
          exact ht.eventually (eventually_valued_lt v hc0)
        filter_upwards [h1, h2] with h hh1 hh2
        have : ¬ Valued.v (cornerEntry2 v h) ≤ Valued.v (gl2Entry v h 1 1) := by rw [hh1]; exact not_le.mpr hh2
        simp only [pivot, if_neg this]
      · have h2 : ∀ᶠ h in nhds g, Valued.v (gl2Entry v h 1 1) = Valued.v (gl2Entry v g 1 1) :=
          hdA.eventually (eventually_valued_eq v hd0)
        filter_upwards [h1, h2] with h hh1 hh2
        have : ¬ Valued.v (cornerEntry2 v h) ≤ Valued.v (gl2Entry v h 1 1) := by rw [hh1, hh2]; exact hle
        simp only [pivot, if_neg this]
  have hp0 : p g ≠ 0 := hpg ▸ pivot_ne_zero v g
  have hpA : ContinuousAt p g := hpcont.continuousAt
  have hqA : ContinuousAt (fun h => gl2Det v h / p h) g := ((continuous_gl2Det v).continuousAt).div hpA hp0
  have hq0 : gl2Det v g / p g ≠ 0 := div_ne_zero (gl2Det_ne_zero v g) hp0
  filter_upwards [hev, hqA.eventually (eventually_charExt_eq v (χ 0) (hχ' 0) hq0),
    hpA.eventually (eventually_charExt_eq v (χ 1) (hχ' 1) hp0), hqA.eventually (eventually_norm_eq v hq0),
    hpA.eventually (eventually_norm_eq v hp0)] with h hh e0 e1 n0 n1
  simp only [sphValue, hh, ← hpg, e0, e1, n0, n1]

theorem sphValue_one (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : sphValue v χ 1 = 1 := by
  have hp : pivot v 1 = 1 := by
    simp [pivot, cornerEntry2, gl2Entry]
  have hd : gl2Det v 1 = 1 := by simp [gl2Det]
  have h0 : charExt (χ 0) (1 : v.adicCompletion ℚ) = 1 := by simpa using charExt_coe_units (χ 0) 1
  have h1 : charExt (χ 1) (1 : v.adicCompletion ℚ) = 1 := by simpa using charExt_coe_units (χ 1) 1
  simp [sphValue, hp, hd, h0, h1]

end SphSection

end LanglandsTunnell.CubicInduction

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries2_of_unramified.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SphSection in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → χ i u = 1) :
    ∃ f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ, f ∈ principalSeries2 v χ ∧
      (∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → f (g * k) = f g) ∧
      f 1 = 1 :=
  ⟨sphValue v χ,
    ⟨isLocallyConstant_sphValue v χ hχ, sphValue_upperUnipotent2_mul v χ, sphValue_diagonal2_mul v χ⟩,
    fun k g hk => sphValue_mul_of_mem v χ hχ g k hk, sphValue_one v χ⟩

end
end S_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries2_of_unramified
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries2_of_unramified (solution)
