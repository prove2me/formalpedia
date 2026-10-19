-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.errorPairing_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:56:26.249471+00:00
-- url     : https://prove2.me/submissions/3cf95741-1050-489a-9064-219eb0c805eb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/ErrorPairing.lean:L57-L84
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.errorPairing_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing
import Theorems.Thm_OAI_TriangularHilbert_Heat_endpointError_bound
import Theorems.Thm_OAI_TriangularHilbert_Heat_mesh_mass_le
import Theorems.Thm_OAI_TriangularHilbert_Heat_sum_jumpMax_le
import Theorems.Thm_OAI_TriangularHilbert_intInterval_sum_fin
import Theorems.Thm_OAI_TriangularHilbert_intInterval_weighted_le

-- ---- from OAI.Analysis.TriangularHilbert.IntWeak ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma mem_intInterval (m n : ℤ) (r : ℕ) :
    m ∈ intInterval n r ↔ n-(r:ℤ) ≤ m ∧ m ≤ n+r := Finset.mem_Icc

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.IntMax ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma mem_intInterval_iff_dist (m n : ℤ) (r : ℕ) :
    m ∈ intInterval n r ↔ (m-n).natAbs ≤ r := by
  rw [mem_intInterval]
  have he : (m-n).natAbs ≤ r ↔ |m-n| ≤ (r:ℤ) := by
    rw [← Int.natCast_natAbs]
    omega
  rw [he,abs_le]
  constructor <;> intro h <;> constructor <;> omega

lemma intAverage_nonneg (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m) (n : ℤ) (r : ℕ) :
    0 ≤ intAverage D f n r := by
  exact div_nonneg (Finset.sum_nonneg (fun m hm => hf m (Finset.mem_inter.mp hm).1)) (by positivity)

lemma inter_intInterval_of_supportRadius_le (D : Finset ℤ) (n : ℤ) {r : ℕ}
    (hr : supportRadius D n ≤ r) : D ∩ intInterval n r = D := by
  apply Finset.inter_eq_left.mpr
  intro m hm
  rw [mem_intInterval_iff_dist]
  exact (Finset.le_sup hm).trans hr

lemma intAverage_le_intMax (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (n : ℤ) (r : ℕ) : intAverage D f n r ≤ intMax D f n := by
  by_cases hr : r ≤ supportRadius D n
  · exact Finset.le_sup' _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  · have hb : supportRadius D n ≤ r := le_of_lt (lt_of_not_ge hr)
    have hm : intAverage D f n r ≤ intAverage D f n (supportRadius D n) := by
      unfold intAverage
      rw [inter_intInterval_of_supportRadius_le D n hb,
        inter_intInterval_of_supportRadius_le D n le_rfl]
      apply div_le_div_of_nonneg_left (Finset.sum_nonneg hf) (by positivity)
      exact_mod_cast (by omega : 2*supportRadius D n+1 ≤ 2*r+1)
    exact hm.trans (Finset.le_sup' _ (Finset.mem_range.mpr (Nat.lt_succ_self _)))

lemma intMax_nonneg (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m) (n : ℤ) :
    0 ≤ intMax D f n := (intAverage_nonneg D f hf n 0).trans (intAverage_le_intMax D f hf n 0)

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianRadial ----
namespace OAI

section
namespace TriangularHilbert.Heat
open scoped BigOperators
noncomputable section

lemma density_radial_int (σ h : ℝ) (m : ℤ) :
    density σ (h*(m:ℝ)) = density σ (h*(m.natAbs:ℝ)) := by
  have he := congrArg (fun n : ℤ => (n : ℝ)) (Int.natAbs_sq m).symm
  simp only [Int.cast_pow,Int.cast_natCast] at he
  simp only [density,mul_pow,he]

lemma density_radial_descending {σ h : ℝ} (hσ : 0 < σ) (hh : 0 ≤ h) (r : ℕ) :
    h*density σ (h*(r+1:ℕ)) ≤ h*density σ (h*(r:ℝ)) := by
  apply mul_le_mul_of_nonneg_left _ hh
  unfold density
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hr : (0:ℝ) ≤ r := by positivity
  push_cast
  nlinarith [sq_nonneg h]

lemma intInterval_density_mass {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) (N : ℕ) :
    (∑ m ∈ intInterval n N, h*density σ (h*((m-n).natAbs:ℝ))) ≤ meshMassConstant := by
  simp_rw [← density_radial_int]
  rw [intInterval_sum_fin]
  have he (i : Fin (2*N+1)) : h*density σ (h*((n-(N:ℤ)+(i:ℕ)-n:ℤ):ℝ)) =
      h*density σ (-(h*N)+h*i) := by
    congr 2
    push_cast
    ring
  simp_rw [he]
  exact mesh_mass_le hh hσ (-(h*N)) (2*N+1)

lemma gaussian_sum_le_intMax (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) :
    (∑ m ∈ D, f m*(h*density σ (h*((m-n:ℤ):ℝ)))) ≤ meshMassConstant * intMax D f n := by
  have hpos : 0 < σ := (sq_pos_of_pos hh).trans_le hσ
  simp_rw [density_radial_int]
  have hw := intInterval_weighted_le D f hf n (fun r => h*density σ (h*(r:ℝ)))
    (fun r => mul_nonneg hh.le (density_nonneg hpos.le _)) (density_radial_descending hpos hh.le)
  apply hw.trans
  rw [mul_comm meshMassConstant]
  exact mul_le_mul_of_nonneg_left (intInterval_density_mass hh hσ n (supportRadius D n)) (intMax_nonneg D f hf n)
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.FiniteLineMax ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uκ

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma lineExtend_apply (D : Finset ℤ) (f : D → ℝ) (n : D) : lineExtend D f n = f n := by
  simp only [lineExtend,dite_eq_left n.property]

lemma sum_lineExtend (D : Finset ℤ) (f : D → ℝ) (g : ℤ → ℝ) :
    (∑ n ∈ D, lineExtend D f n*g n) = ∑ n : D, f n*g n := by
  rw [← Finset.sum_coe_sort]
  simp only [lineExtend_apply]

lemma lineMax_nonneg (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m) (n : ℤ) :
    0 ≤ lineMax D f n := by
  exact intMax_nonneg D (lineExtend D f) (fun m hm => by simpa only [lineExtend,dite_eq_left hm] using hf ⟨m,hm⟩) n

lemma gaussian_sum_le_lineMax (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) :
    (∑ m : D, f m*(h*Heat.density σ (h*((m-n:ℤ):ℝ)))) ≤ Heat.meshMassConstant*lineMax D f n := by
  have hi := Heat.gaussian_sum_le_intMax D (lineExtend D f)
    (fun m hm => by simpa only [lineExtend,dite_eq_left hm] using hf ⟨m,hm⟩) hh hσ n
  rw [sum_lineExtend] at hi
  exact hi

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.ErrorPairing ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

lemma errorOutput_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) (i j : D) :
    ‖kernelOutput (A 1) (A 2) h (fun m => h*(m:ℤ)) (fun a b => endpointError (r a b)) i j‖ ≤
      envelopeConstant*meshMassConstant*jumpMax D A i j := by
  have hri := hh.trans_le (hr i j)
  have hs : h^2 ≤ 6*(r i j)^2 := by have hr' := hr i j; nlinarith [sq_nonneg (r i j),sq_nonneg h]
  have hed (k : D) : h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ) = h*((((k:ℤ)-(-(i:ℤ)-(j:ℤ))):ℤ):ℝ) := by
    push_cast
    ring
  have h1 := gaussian_sum_le_lineMax D (fun k => ‖A 1 j k‖^2) (fun _ => sq_nonneg _) hh hs (-(i:ℤ)-(j:ℤ))
  have h2 := gaussian_sum_le_lineMax D (fun k => ‖A 2 k i‖^2) (fun _ => sq_nonneg _) hh hs (-(i:ℤ)-(j:ℤ))
  simp_rw [← hed] at h1 h2
  unfold kernelOutput
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k, envelopeConstant*(‖A 1 j k‖^2+‖A 2 k i‖^2)*
        (h*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))) := by
      apply Finset.sum_le_sum
      intro k _
      simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hh.le,Real.norm_eq_abs]
      have hp : ‖A 1 j k‖*‖A 2 k i‖ ≤ ‖A 1 j k‖^2+‖A 2 k i‖^2 := by nlinarith [sq_nonneg (‖A 1 j k‖-‖A 2 k i‖)]
      have hg := endpointError_bound hri (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))
      calc
        _ ≤ h*‖A 1 j k‖*‖A 2 k i‖*(envelopeConstant*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))) := by gcongr
        _ = envelopeConstant*(‖A 1 j k‖*‖A 2 k i‖)*(h*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp envelopeConstant_pos.le)
          (mul_nonneg hh.le (density_nonneg (by positivity) _))
    _ = envelopeConstant*((∑ k, ‖A 1 j k‖^2*(h*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))))+
        (∑ k, ‖A 2 k i‖^2*(h*density (6*(r i j)^2) (h*(i:ℤ)+h*(j:ℤ)+h*(k:ℤ))))) := by
      simp only [mul_assoc,mul_add,add_mul,Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ envelopeConstant*(meshMassConstant*lineMax D (fun k => ‖A 1 j k‖^2) (-(i:ℤ)-(j:ℤ))+
        meshMassConstant*lineMax D (fun k => ‖A 2 k i‖^2) (-(i:ℤ)-(j:ℤ))) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) envelopeConstant_pos.le
    _ ≤ _ := by
      unfold jumpMax
      have h0 := lineMax_nonneg D (fun k => ‖A 0 i k‖^2) (fun _ => sq_nonneg _) (j:ℤ)
      have h3 := lineMax_nonneg D (fun k => ‖A 0 k j‖^2) (fun _ => sq_nonneg _) (i:ℤ)
      have hC := envelopeConstant_pos
      have hM := meshMassConstant_pos
      nlinarith [mul_nonneg (mul_nonneg hC.le hM.le) h0,mul_nonneg (mul_nonneg hC.le hM.le) h3]

lemma errorPairing_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) {h : ℝ} (hh : 0 < h)
    (r : Matrix D D ℝ) (hr : ∀ i j, h ≤ r i j) :
    ‖kernelPairing A h (fun m => h*(m:ℤ)) (fun i j => endpointError (r i j))‖ ≤
      errorPairingConstant*arrayCubic A h := by
  unfold kernelPairing
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i, ∑ j, h^2*‖A 0 i j‖*(envelopeConstant*meshMassConstant*jumpMax D A i j) := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg h)]
      exact mul_le_mul_of_nonneg_left (errorOutput_le D A hh r hr i j) (by positivity)
    _ = envelopeConstant*meshMassConstant*h^2*(∑ i, ∑ j, ‖A 0 i j‖*jumpMax D A i j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ envelopeConstant*meshMassConstant*h^2*(jumpScalarConstant*(∑ v,∑ i,∑ j,‖A v i j‖^3)) :=
      mul_le_mul_of_nonneg_left (sum_jumpMax_le D A) (mul_nonneg (mul_nonneg envelopeConstant_pos.le meshMassConstant_pos.le) (sq_nonneg h))
    _ = _ := by
      unfold errorPairingConstant arrayCubic
      simp only [← Finset.mul_sum]
      ring
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.errorPairing_le := @_root_.OAI.TriangularHilbert.Heat.errorPairing_le
