-- Prove2me | solution 2 for OAI.TriangularHilbert.Heat.density_product
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:03:00.851412+00:00
-- url     : https://prove2.me/submissions/3add2501-81ad-4d38-a0df-335f473cf67c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/GaussianConvolution.lean:L23-L40
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.density_product. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass

-- ---- from OAI.Analysis.TriangularHilbert.GaussianConvolution ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a b p : ℝ) :
    density s (a-p)*density t (b-p) =
      density (s+t) (a-b)*density (s*t/(s+t)) (p-(t*a+s*b)/(s+t)) := by
  have hst : s+t ≠ 0 := (add_pos hs ht).ne'
  have hn : Real.sqrt (2*Real.pi*s)*Real.sqrt (2*Real.pi*t) =
      Real.sqrt (2*Real.pi*(s+t))*Real.sqrt (2*Real.pi*(s*t/(s+t))) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi*s),← Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi*(s+t))]
    congr 1
    field_simp
  have he : -(a-p)^2/(2*s) + -(b-p)^2/(2*t) =
      -(a-b)^2/(2*(s+t)) + -(p-(t*a+s*b)/(s+t))^2/(2*(s*t/(s+t))) := by
    field_simp
    ring
  unfold density
  calc
    _ = (Real.sqrt (2*Real.pi*s)*Real.sqrt (2*Real.pi*t))⁻¹ *
        Real.exp (-(a-p)^2/(2*s) + -(b-p)^2/(2*t)) := by rw [mul_inv,Real.exp_add]; ring
    _ = _ := by rw [hn,he,mul_inv,Real.exp_add]; ring

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.density_product := @_root_.OAI.TriangularHilbert.Heat.density_product
