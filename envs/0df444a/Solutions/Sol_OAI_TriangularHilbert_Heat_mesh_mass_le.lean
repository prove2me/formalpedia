-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.mesh_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:01:39.064771+00:00
-- url     : https://prove2.me/submissions/ffd69239-6e97-4faa-9011-3c07f188fc9f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MeshMass.lean:L63-L97
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.mesh_mass_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass

-- ---- from OAI.Analysis.TriangularHilbert.Gaussian ----
namespace OAI

section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TriangularHilbert.Heat

theorem density_eq_gaussianPDFReal {σ : ℝ} (hσ : 0 ≤ σ) :
    density σ = ProbabilityTheory.gaussianPDFReal 0 ⟨σ, hσ⟩ := by
  ext t
  change (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-t^2 / (2*σ)) =
    (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-(t-0)^2 / (2*σ))
  rw [sub_zero]

theorem density_integrable {σ : ℝ} (hσ : 0 ≤ σ) : Integrable (density σ) := by
  rw [density_eq_gaussianPDFReal hσ]
  exact ProbabilityTheory.integrable_gaussianPDFReal 0 _

end TriangularHilbert.Heat
end
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MeshMass ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section

lemma continuous_density (σ : ℝ) : Continuous (density σ) := by
  unfold density
  fun_prop

lemma integral_density {σ : ℝ} (hσ : 0 < σ) : (∫ t, density σ t) = 1 := by
  rw [density_eq_gaussianPDFReal hσ.le]
  apply ProbabilityTheory.integral_gaussianPDFReal_eq_one
  intro he
  have he' : σ = 0 := congrArg (fun r : NNReal => (r : ℝ)) he
  exact hσ.ne' he'

lemma density_cell_le {σ a b : ℝ} (hσ : 0 < σ) (hab : (b-a)^2 ≤ σ) :
    density σ a ≤ meshMassConstant * density (2*σ) b := by
  have hA : 0 < 2*Real.pi*σ := by positivity
  have hB : 0 < 2*Real.pi*(2*σ) := by positivity
  have hsa := Real.sqrt_pos.mpr hA
  have hsb := Real.sqrt_pos.mpr hB
  have hn : Real.sqrt (2*Real.pi*(2*σ)) ≤ 2*Real.sqrt (2*Real.pi*σ) := by
    nlinarith [Real.sq_sqrt hA.le,Real.sq_sqrt hB.le]
  have hn' : (Real.sqrt (2*Real.pi*σ))⁻¹ ≤ 2 * (Real.sqrt (2*Real.pi*(2*σ)))⁻¹ := by
    have hh : 1 / Real.sqrt (2*Real.pi*σ) ≤ 2 / Real.sqrt (2*Real.pi*(2*σ)) :=
      (div_le_div_iff₀ hsa hsb).mpr (by simpa only [one_mul] using hn)
    simpa only [one_div,div_eq_mul_inv,one_mul] using hh
  have hquad : b^2 ≤ 2*a^2+2*σ := by nlinarith [sq_nonneg (b-2*a)]
  have hex : -a^2/(2*σ) ≤ 1/2 + (-b^2/(2*(2*σ))) := by
    apply (mul_le_mul_iff_of_pos_right (show 0 < 4*σ by positivity)).mp
    field_simp
    nlinarith
  unfold density
  calc
    _ ≤ (2 * (Real.sqrt (2*Real.pi*(2*σ)))⁻¹) *
        (Real.exp (1/2) * Real.exp (-b^2/(2*(2*σ)))) :=
      mul_le_mul hn' (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hex)
        (Real.exp_nonneg _) (by positivity)
    _ = _ := by unfold meshMassConstant; ring

lemma mesh_cell_le {h σ : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (c : ℝ) (i : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (i:ℝ) (i+1)) :
    density σ (c+h*i) ≤ meshMassConstant * density (2*σ) (c+h*t) := by
  have hσ0 : 0 < σ := (sq_pos_of_pos hh).trans_le hσ
  apply density_cell_le hσ0
  have hti : 0 ≤ t-i := sub_nonneg.mpr ht.1
  have hti1 : t-i ≤ 1 := by linarith [ht.2]
  have he : c+h*t-(c+h*i) = h*(t-i) := by ring
  rw [he,mul_pow]
  have hs : (t-i)^2 ≤ 1 := by nlinarith
  exact (by nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg h)] : h^2*(t-i)^2 ≤ h^2).trans hσ

lemma mesh_mass_le {h σ : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (c : ℝ) (n : ℕ) :
    (∑ i : Fin n, h*density σ (c+h*i)) ≤ meshMassConstant := by
  have hs : 0 < σ := (sq_pos_of_pos hh).trans_le hσ
  let f : ℝ → ℝ := fun t => h*density (2*σ) (c+h*t)
  have hf : Continuous f := continuous_const.mul ((continuous_density _).comp
    (continuous_const.add (continuous_const.mul continuous_id)))
  have hc (i : ℕ) : h*density σ (c+h*(i:ℝ)) ≤ meshMassConstant * ∫ t in (i:ℝ)..(i+1), f t := by
    have hi := intervalIntegral.integral_mono_on (show (i:ℝ) ≤ i+1 by linarith)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => h*density σ (c+h*i)) volume i (i+1))
      ((continuous_const.mul hf : Continuous (fun t => meshMassConstant * f t)).intervalIntegrable i (i+1))
      (fun t ht => by
        have hb := mul_le_mul_of_nonneg_left (mesh_cell_le hh hσ c i ht) hh.le
        simpa only [Pi.mul_apply,f,mul_assoc,mul_left_comm h meshMassConstant] using hb)
    simpa only [Pi.mul_apply,intervalIntegral.integral_const,add_sub_cancel_left,one_smul,intervalIntegral.integral_const_mul] using hi
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => h*density σ (c+h*i)) n]
  calc
    _ ≤ ∑ i ∈ Finset.range n, meshMassConstant * ∫ t in (i:ℝ)..(i+1), f t := Finset.sum_le_sum (fun i _ => hc i)
    _ = meshMassConstant * ∫ t in (0:ℝ)..n, f t := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [Nat.cast_zero,Nat.cast_add,Nat.cast_one] using
        (intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k:ℝ)) (n := n) (fun i _ => hf.intervalIntegrable _ _))
    _ ≤ meshMassConstant := by
      have hval : (∫ t in (0:ℝ)..n, f t) = ∫ x in c..(c+h*n), density (2*σ) x := by
        unfold f
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left (fun y => density (2*σ) (c+y)) hh.ne']
        rw [intervalIntegral.integral_comp_add_left]
        simp [smul_eq_mul,hh.ne']
      rw [hval]
      have hi : (∫ x in c..(c+h*n), density (2*σ) x) ≤ 1 := by
        rw [intervalIntegral.integral_of_le (by nlinarith [show (0:ℝ) ≤ n by positivity] : c ≤ c+h*n)]
        rw [← integral_density (show 0 < 2*σ by positivity)]
        exact setIntegral_le_integral (density_integrable (by positivity))
          (ae_of_all _ (fun x => density_nonneg (by positivity) x))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hi meshMassConstant_pos.le
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.mesh_mass_le := @_root_.OAI.TriangularHilbert.Heat.mesh_mass_le
