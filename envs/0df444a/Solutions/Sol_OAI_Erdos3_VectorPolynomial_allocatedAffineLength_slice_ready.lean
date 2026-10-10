-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineLength_slice_ready
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T13:19:17.513904+00:00
-- url     : https://prove2.me/submissions/410046e0-0cfa-4d38-8b62-e66d74c17d63

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B129
import Definitions.Def_OAIErdos3B133
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineLength_ready

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDomainDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeDomainDensity_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < scalarCubeDomainDensity α := inv_pos.mpr (scalarCubeDomain_volumeReal_pos α)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarCubeLatticeGeometry
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem scalarCubeValue_sub_bound {I : Type*} [Fintype I] [DecidableEq I]
    (x y : Option I → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (he : ‖x-y‖ ≤ δ) (t : Finset I) :
    |scalarCubeValue x t - scalarCubeValue y t| ≤ (Fintype.card I + 1 : ℝ)*δ := by
  have hi (i : Option I) : |x i-y i| ≤ δ := (norm_le_pi_norm (x-y) i).trans he
  have hsum : |∑ i ∈ t, (x (some i)-y (some i))| ≤ (t.card : ℝ)*δ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i ∈ t) => hi (some i))
  have hcard : (t.card : ℝ) ≤ Fintype.card I := by exact_mod_cast t.card_le_univ
  have hid : scalarCubeValue x t - scalarCubeValue y t =
      (x none-y none) + ∑ i ∈ t, (x (some i)-y (some i)) := by
    simp only [scalarCubeValue_formula, Finset.sum_sub_distrib]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add (hi none) hsum).trans (by nlinarith))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDensityBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeInnerBox_subset (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeInnerBox I ⊆ scalarCubeDomain I := by
  intro x hx t
  have hr : 0 ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by positivity
  have hn : ‖x-scalarCubeCenter I‖ ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by
    apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro i
    change |x i-scalarCubeCenter I i| ≤ _
    exact abs_le.mpr ⟨by linarith [hx.1 i], by linarith [hx.2 i]⟩
  have hb := scalarCubeValue_sub_bound x (scalarCubeCenter I) hr hn t
  rw [scalarCubeValue_center] at hb
  have he : ((Fintype.card I : ℝ)+1)*(1/(4*((Fintype.card I : ℝ)+1))) = 1/4 := by
    field_simp
  rw [he] at hb
  have ha := abs_le.mp hb
  exact ⟨by linarith [ha.1], by linarith [ha.2]⟩

theorem scalarCubeInnerBox_volume (I : Type*) [Fintype I] :
    volume.real (scalarCubeInnerBox I) = (1/(2*((Fintype.card I : ℝ)+1)))^(Fintype.card I+1) := by
  have hr : 0 ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by positivity
  have ho : (fun i => scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1))) ≤
      (fun i => scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1))) := fun i => by linarith
  have he (i : Option I) : scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1))-
      (scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1))) = 1/(2*((Fintype.card I : ℝ)+1)) := by
    field_simp
    ring
  simp only [measureReal_def, scalarCubeInnerBox, Real.volume_Icc_pi_toReal ho, he,
    Finset.prod_const, Finset.card_univ, Fintype.card_option]

theorem scalarCubeDomainDensity_le_power (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomainDensity I ≤ (2*((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := by
  have hv := measureReal_mono (scalarCubeInnerBox_subset I) (scalarCubeDomain_volume_lt_top I).ne
  rw [scalarCubeInnerBox_volume] at hv
  have hp : 0 < (1/(2*((Fintype.card I : ℝ)+1)))^(Fintype.card I+1) := by positivity
  have hi := one_div_le_one_div_of_le hp hv
  simpa only [scalarCubeDomainDensity, one_div, inv_pow, inv_inv] using hi

theorem scalarCubeDomainDensity_le_exp (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomainDensity I ≤ Real.exp (((Fintype.card I : ℝ)+1)^2) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hb : 2*((Fintype.card I : ℝ)+1) ≤ Real.exp ((Fintype.card I : ℝ)+1) := by
    calc
      _ ≤ Real.exp 1*Real.exp (Fintype.card I) := by gcongr; exact Real.add_one_le_exp _
      _ = _ := by rw [← Real.exp_add, add_comm]
  calc
    _ ≤ (2*((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := scalarCubeDomainDensity_le_power I
    _ ≤ (Real.exp ((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; push_cast; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem progression_slice_endpoint_geometry {L step H : ℕ} (c : ℤ)
    (hL : 0 < L) (hstep : 0 < step) (hH : 2 ≤ H) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hdense : δ * L ≤ ((integerProgressionSupport c (step : ℤ) H).card : ℝ)) :
    let lower := (c : ℝ) / L
    let width := (step : ℝ) * ((H : ℝ) - 1) / L
    0 ≤ lower ∧ δ / 2 ≤ width ∧ |lower| + |width| ≤ 1 ∧
      (step : ℝ) / L ≤ 2 / ((H : ℝ) - 1) := by
  have hbase := hsubset (integerProgressionSupport_point c step H hstep 0 (by omega))
  have hlast := hsubset (integerProgressionSupport_point c step H hstep (H - 1) (by omega))
  have hc : (0 : ℝ) ≤ c := by
    have hh : 0 ≤ c := by simpa using (Finset.mem_Ico.mp hbase).1
    exact_mod_cast hh
  have hh : (c : ℝ) + (step : ℝ) * ((H : ℝ) - 1) < L := by
    have hh := (Finset.mem_Ico.mp hlast).2
    have he : (c : ℝ) + (step : ℝ) * ((H - 1 : ℕ) : ℝ) < L := by exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one] using he
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hstep1 : (1 : ℝ) ≤ step := by exact_mod_cast hstep
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  rw [card_integerProgressionSupport c step H hstep] at hdense
  have hwidth : δ / 2 ≤ (step : ℝ) * ((H : ℝ) - 1) / L := by
    apply (le_div_iff₀ hLp).mpr
    have h1 : (H : ℝ) / 2 ≤ (H : ℝ) - 1 := by linarith
    have h2 : (H : ℝ) - 1 ≤ (step : ℝ) * ((H : ℝ) - 1) := by nlinarith
    nlinarith
  have hw0 : 0 ≤ (step : ℝ) * ((H : ℝ) - 1) / L := (half_pos hδ).le.trans hwidth
  refine ⟨div_nonneg hc hLp.le, hwidth, ?_, ?_⟩
  · rw [abs_of_nonneg (div_nonneg hc hLp.le), abs_of_nonneg hw0, ← add_div]
    exact (div_le_one hLp).mpr hh.le
  · apply (le_div_iff₀ (by linarith : 0 < (H : ℝ) - 1)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hLp).mpr
    linarith

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeProductRiemannBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem scalarCubeRiemannBoundary_le_exp (α : Type*) [Fintype α] [DecidableEq α]
    {D : ℝ} (_hD : 0 ≤ D) (hcard : (Fintype.card α : ℝ) ≤ D) :
    scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) ≤
      Real.exp (scalarCubeRiemannLog D) := by
  let q := Fintype.card α
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h2q : (2 : ℝ) ^ q ≤ Real.exp q := by
    simpa only [← Real.exp_nat_mul, mul_one] using pow_le_pow_left₀ (by norm_num) h2 q
  have h4q : (4 : ℝ) ^ q ≤ Real.exp (2 * q) := by
    simpa only [← Real.exp_nat_mul, mul_comm] using pow_le_pow_left₀ (by norm_num) h4 q
  have hb : scalarCubeGridBoundaryConstant α ≤ Real.exp (4 * q + 2) := by
    simp only [scalarCubeGridBoundaryConstant, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_finset, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    calc
      _ ≤ (Real.exp 1 * Real.exp q) * Real.exp (2 * q) * Real.exp 1 * Real.exp q := by
        gcongr
        exact Real.add_one_le_exp _
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  calc
    _ = scalarCubeGridBoundaryConstant α * scalarCubeDomainDensity α := by
      rw [div_eq_mul_inv]; rfl
    _ ≤ Real.exp (4 * q + 2) * Real.exp (((q : ℝ) + 1) ^ 2) :=
      mul_le_mul hb (scalarCubeDomainDensity_le_exp α)
        (scalarCubeDomainDensity_pos α).le (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp only [scalarCubeRiemannLog]
      have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
      change (q : ℝ) ≤ D at hcard
      nlinarith [sq_nonneg (D - q)]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

theorem progressionSlice_scale_bounds
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    {D E F T δ : ℝ} {S modulus : ℕ} (H step : ι → ℕ) (c : ι → ℤ)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (_hF : 0 ≤ F) (hT : 0 ≤ T)
    (hcard : (Fintype.card ι : ℝ) ≤ D) (hq : (Fintype.card α : ℝ) ≤ D)
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (hm : 0 < modulus) (hmT : (modulus : ℝ) ≤ Real.exp T)
    (hS : Real.exp (progressionSliceLengthLog D E F T) ≤ S)
    (hstep : ∀ j, 0 < step j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ))
    (hdense : ∀ j, δ * S ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ)) :
    (∀ j, 2 ≤ H j) ∧
    (∀ j, (Fintype.card α + 1) * modulus ≤ H j) ∧
    (∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α)) ∧
    (∑ j, (modulus : ℝ) / H j) ≤ Real.exp (-E) ∧
    (∀ j, (step j : ℝ) / S ≤ Real.exp (-E)) := by
  let B := scalarCubeRiemannLog D
  have hB : 0 ≤ B := by dsimp [B, scalarCubeRiemannLog]; positivity
  have hS0 : (0 : ℝ) < S := (Real.exp_pos _).trans_le hS
  have hSpos : 0 < S := by exact_mod_cast hS0
  have hδlow : Real.exp (-F) ≤ δ := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos F) hδ).mpr hδF
  have hHlow (j : ι) : Real.exp (E + T + D + B + 5) ≤ (H j : ℝ) := by
    calc
      _ = Real.exp (-F) * Real.exp (progressionSliceLengthLog D E F T) := by
        rw [← Real.exp_add]; dsimp [progressionSliceLengthLog, B]; congr 1; ring
      _ ≤ δ * S := mul_le_mul hδlow hS (Real.exp_nonneg _) hδ.le
      _ ≤ _ := by simpa only [card_integerProgressionSupport _ _ _ (hstep j)] using hdense j
  have hH2 (j : ι) : 2 ≤ H j := by
    have he : (2 : ℝ) ≤ Real.exp (E + T + D + B + 5) := by
      linarith [Real.add_one_le_exp (E + T + D + B + 5)]
    exact_mod_cast he.trans (hHlow j)
  have hHp (j : ι) : (0 : ℝ) < H j := (Real.exp_pos _).trans_le (hHlow j)
  have hr (j : ι) : (modulus : ℝ) / H j ≤ Real.exp (-(E + D + B + 5)) := by
    calc
      _ ≤ Real.exp T / Real.exp (E + T + D + B + 5) :=
        div_le_div₀ (Real.exp_nonneg _) hmT (Real.exp_pos _) (hHlow j)
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  have hcancel (a : ℝ) : Real.exp a * Real.exp (-(E + D + B + 5)) =
      Real.exp (a - (E + D + B + 5)) := by rw [← Real.exp_add]; rfl
  refine ⟨hH2, ?_, ?_, ?_, ?_⟩
  · intro j
    have hc : (Fintype.card α : ℝ) + 1 ≤ Real.exp D :=
      by linarith [Real.add_one_le_exp D]
    have hratio : ((Fintype.card α : ℝ) + 1) * ((modulus : ℝ) / H j) ≤ 1 := by
      calc
        _ ≤ Real.exp D * Real.exp (-(E + D + B + 5)) :=
          mul_le_mul hc (hr j) (div_nonneg (Nat.cast_nonneg _) (hHp j).le) (Real.exp_nonneg _)
        _ ≤ 1 := by rw [hcancel]; apply Real.exp_le_one_iff.mpr; linarith
    rw [← mul_div_assoc] at hratio
    have hn := (div_le_one (hHp j)).mp hratio
    exact_mod_cast hn
  · intro j
    have hb := scalarCubeRiemannBoundary_le_exp α hD hq
    have hx : (scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α)) *
        ((modulus : ℝ) / H j) < 1 := by
      calc
        _ ≤ Real.exp B * Real.exp (-(E + D + B + 5)) :=
          mul_le_mul hb (hr j) (div_nonneg (Nat.cast_nonneg _) (hHp j).le) (Real.exp_nonneg _)
        _ < 1 := by rw [hcancel]; apply Real.exp_lt_one_iff.mpr; linarith
    apply (div_lt_one (scalarCubeDomain_volumeReal_pos α)).mp
    simpa only [div_mul_eq_mul_div] using hx
  · calc
      _ ≤ ∑ _j : ι, Real.exp (-(E + D + B + 5)) := Finset.sum_le_sum (fun j _ => hr j)
      _ = (Fintype.card ι : ℝ) * Real.exp (-(E + D + B + 5)) := by simp
      _ ≤ Real.exp D * Real.exp (-(E + D + B + 5)) := by
        gcongr
        exact hcard.trans (by linarith [Real.add_one_le_exp D])
      _ ≤ _ := by rw [hcancel]; apply Real.exp_le_exp.mpr; linarith
  · intro j
    have hg := progression_slice_endpoint_geometry (c j) hSpos (hstep j) (hH2 j) hδ
      (hsubset j) (hdense j)
    have hHreal : (2 : ℝ) ≤ H j := by exact_mod_cast hH2 j
    have hmesh : (step j : ℝ) / S ≤ 4 * ((modulus : ℝ) / H j) := by
      apply hg.2.2.2.trans
      apply (div_le_iff₀ (by linarith : 0 < (H j : ℝ) - 1)).mpr
      rw [show 4 * ((modulus : ℝ) / H j) * ((H j : ℝ) - 1) =
        (4 * modulus * ((H j : ℝ) - 1)) / H j by ring]
      apply (le_div_iff₀ (hHp j)).mpr
      have hm1 : (1 : ℝ) ≤ modulus := by exact_mod_cast hm
      have hprod := mul_le_mul_of_nonneg_right hm1 (by linarith : 0 ≤ (H j : ℝ) - 1)
      nlinarith
    calc
      _ ≤ 4 * ((modulus : ℝ) / H j) := hmesh
      _ ≤ Real.exp 3 * Real.exp (-(E + D + B + 5)) := by
        gcongr
        · linarith [Real.add_one_le_exp (3 : ℝ)]
        · exact hr j
      _ ≤ _ := by rw [hcancel]; apply Real.exp_le_exp.mpr; linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype α] [DecidableEq α]
variable (B : D → Type*) (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedPrincipalSides_long (d : LayerSamplerAxis I n)
    (hd : ¬allocatedGridAxis U basis S.value d) (b : B d) (v : Fin (layerSamplerDegree I n d)) :
    allocatedPrincipalSides B U basis S ⟨d, b, v⟩ = S.value := by
  rcases d with ⟨j, d⟩
  cases d with
  | inl i => rfl
  | inr i =>
    change ¬basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1) at hd
    have hactive : S.value^(j.val+1) < basisAxisScale (basis j) i :=
      (Nat.pow_le_pow_right S.positive
        ((layerDegree_le_tailDegree j).trans (Nat.le_succ _))).trans_lt (Nat.lt_of_not_ge hd)
    simp only [allocatedPrincipalSides, layerSamplerSides, heterogeneousSamplerSides,
      layerSamplerDenominators, Sum.elim_inr, layerSamplerDegree,
      integerAxisSideLength, hactive, ↓reduceIte]

local notation "gridAxes" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "degree" => layerSamplerDegree I n

section Law

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

end Law

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PartitionedRegularizationBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem dependentAxis_card_split {D : Type*} [Fintype D] (V : D → Type*)
    [∀ d, Fintype (V d)] (P : D → Prop) [DecidablePred P] :
    Fintype.card (Σ d : {d // P d}, V d.val) +
      Fintype.card (Σ d : {d // ¬P d}, V d.val) = Fintype.card (Σ d, V d) := by
  simp only [Fintype.card_sigma]
  exact Fintype.sum_subtype_add_sum_subtype P (fun d => Fintype.card (V d))

theorem dependentAxis_card_restrict_le {D : Type*} [Fintype D] (V : D → Type*)
    [∀ d, Fintype (V d)] (P : D → Prop) [DecidablePred P] :
    Fintype.card (Σ d : {d // P d}, V d.val) ≤ Fintype.card (Σ d, V d) := by
  have he := dependentAxis_card_split V P
  omega

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

 theorem AllocatedComparisonDimensions.active_tuples {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (partition : LayerSamplerAxis I n → Prop) :
    (Fintype.card (PrincipalTupleIndex (fun a : {a // ¬partition a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)) : ℝ) ≤ D :=
  (Nat.cast_le.mpr (dependentAxis_card_restrict_le
    (fun a => B a × Fin (layerSamplerDegree I n a)) (fun a => ¬partition a))).trans hdim.tuples

 theorem allocatedAffineLength_slice_ready [DecidableEq α]
    {D P Prho Pk target F T δ : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk) (ht : 0 ≤ target)
    (hF : 0 ≤ F) (hT : 0 ≤ T)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (hS : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T) ≤ S.value)
    (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S j : ℤ))
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (modulus : ℕ) (hm : 0 < modulus) (hmT : (modulus : ℝ) ≤ Real.exp T) :
    let grid := allocatedGridAxis (I := I) U basis S.value
    let Tuple := PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    let embed := fun j : Tuple => (⟨j.1.val, j.2⟩ : PrincipalTupleIndex B (layerSamplerDegree I n))
    let E := allocatedAffineReferenceAccuracyLog m D P Prho Pk target
    (∀ j : Tuple, 0 < step (embed j)) →
    (∀ j : Tuple, δ * allocatedPrincipalSides B U basis S (embed j) ≤
      ((integerProgressionSupport (c (embed j)) (step (embed j) : ℤ) (H (embed j))).card : ℝ)) →
    (∀ j : Tuple, 2 ≤ H (embed j)) ∧
    (∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H (embed j)) ∧
    (∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H (embed j)) <
      MeasureTheory.volume.real (scalarCubeDomain α)) ∧
    (∑ j : Tuple, (modulus : ℝ) / H (embed j)) ≤ Real.exp (-E) ∧
    (∀ j : Tuple, (step (embed j) : ℝ) / allocatedPrincipalSides B U basis S (embed j) ≤
      Real.exp (-E)) := by
  intro grid Tuple embed E hstep hdense
  have hlen (j : Tuple) : allocatedPrincipalSides B U basis S (embed j) = S.value :=
    allocatedPrincipalSides_long B U basis S j.1.val j.1.property j.2.1 j.2.2
  have hready := allocatedAffineLength_ready B U basis hdim hP hr hk ht hF hT S hS
  have hE := (allocatedAffineLengthLog_bounds m hdim.nonneg hP hr hk ht hF hT).2.1
  have hslices := progressionSlice_scale_bounds (α := α)
    (fun j : Tuple => H (embed j)) (fun j : Tuple => step (embed j)) (fun j : Tuple => c (embed j))
    hdim.nonneg hE hF hT (hdim.active_tuples B grid) hdim.cube hδ hδF hm hmT hready.2.2 hstep
    (fun j => by simpa only [hlen j] using hsubset (embed j))
    (fun j => by simpa only [hlen j] using hdense j)
  simpa only [hlen] using hslices

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineLength_slice_ready.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedAffineLength_slice_ready.{u_1, u_2, u_3, u_4, u_5, u_6}
